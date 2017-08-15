#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>
#ifndef NO_BACKTRACE
#include <execinfo.h>
#endif
#include <pthread.h>
#include <stack>
#include <map>

#define DEBUG
#define MAXPATH 1000

// this is what the instrumentation code will pass to the runtime.
// it's type info that has not been associated with a va_list yet.
struct vasan_type_info_tmp
{
	unsigned long id;
	unsigned long arg_count;
	unsigned long*  arg_array;	
};

struct vasan_type_info_full
{
	unsigned int args_ptr;
	struct vasan_type_info_tmp* types;
};

struct tinfo 
{
	void *(*real_start_routine)(void *);
	void *real_start_routine_arg;
};

// only holds the call site info
static thread_local std::stack<struct vasan_type_info_tmp*> vasan_stack;

// maps va_lists onto their call site info
static thread_local std::map<va_list*, struct vasan_type_info_full*> vasan_map;

// protects accesses to global structures
// it's just a simple spinlock as we don't
// expect much contention
static volatile int spinlock = 0;

#ifdef VASAN_STATISTICS
static unsigned long long vararg_calls      = 0;
static unsigned long long vararg_checks     = 0;
static unsigned long long vararg_violations = 0;
#endif

// if set to 1, we log violations but don't terminate
// the program when a violation is triggered
static unsigned char logging_only = 0;

// if set to 1, allow all pointer types to be cast to void* and char*
static unsigned char permissive_void_ptr_checking = 0;

// file we're logging to. can be either stderr or a real file
static FILE* fp = (FILE*)0;

// When set to 1, it's safe to access the global state
static unsigned char vasan_initialized = 0;

/// Thread data for the cleanup handler
static pthread_key_t thread_cleanup_key;

static int (*real_pthread_create) (pthread_t *, const pthread_attr_t *, void *(*)(void*), void *);

static void __vasan_backtrace()
{
#ifndef NO_BACKTRACE
    void *trace[16];
	char **messages = (char **)NULL;
	int i, trace_size = 0;

	trace_size = backtrace(trace, 16);
	messages = backtrace_symbols(trace, trace_size);
	(fprintf)(fp, "Backtrace:\n");
	for (i=0; i<trace_size; ++i)
		(fprintf)(fp, "[%d] %s\n", i, messages[i]);
	free(messages);
#endif
}

static void __vasan_lock()
{
	while(!__sync_bool_compare_and_swap(&spinlock, 0, 1))
		__asm__ __volatile__("rep; nop" ::: "memory");
}

static void __vasan_unlock()
{
	__asm__ __volatile__("" ::: "memory");
	spinlock = 0;
}

/// Thread-specific data destructor
static void thread_cleanup_handler(void *_iter) 
{
	for (auto elem : vasan_map)
		delete elem.second;
}

static void __attribute__((constructor(0)))  __vasan_init()
{
	char path[MAXPATH];

	__vasan_lock();

	if(vasan_initialized)
	{
		__vasan_unlock();
		return;
	}

	// Initialize pthread interceptors for thread allocation
	*(void**)&real_pthread_create = dlsym(RTLD_NEXT, "pthread_create");
	
	// Setup the cleanup handler
	pthread_key_create(&thread_cleanup_key, thread_cleanup_handler);
	
	char *home = getenv("VASAN_ERR_LOG_PATH");
	if (home)
	{
		strcpy(path, home);
		strcat(path, "error.txt");
		fp = fopen(path, "a+");
		logging_only = 1;
	}

	if (!fp)
		fp = stderr;

	char* disabled = getenv("VASAN_NO_ERROR_REPORTING");

	if (disabled && strcmp(disabled, "0"))
		fp = (FILE*)0;

	char* permissive = getenv("VASAN_PERMISSIVE");

	if (permissive && !strcmp(permissive, "1"))
		permissive_void_ptr_checking = 1;

	vasan_initialized = 1;
	__vasan_unlock();
}

static void __attribute__((destructor)) __vasan_fini()
{
#ifdef VASAN_STATISTICS
	fprintf(stderr, "vararg calls: %llu\n", vararg_calls);
	fprintf(stderr, "vararg checks: %llu\n", vararg_checks);
	fprintf(stderr, "vararg violations: %llu\n", vararg_violations);
#endif

	if (fp && fp != stderr)
	{
		fclose(fp);
		fp = (FILE*)0;
	}
}

// CallerSide: Function to push the pointer in the stack
extern "C" void
__vasan_info_push(struct vasan_type_info_tmp *x)
{
#ifdef VASAN_STATISTICS
	__atomic_add_fetch(&vararg_calls, 1, __ATOMIC_RELAXED);
#endif
	vasan_stack.push(x);
}

// We've seen a va_start call.
// Associate the corresponding vasan_type_info_tmp struct with this list
// and store it in the vasan map
extern "C" void
__vasan_vastart(va_list* list)
{
	struct vasan_type_info_tmp* latest = vasan_stack.top();

	if (!latest)
		return;

	auto info = vasan_map.find(list);
	if (info == vasan_map.end())
	    info = vasan_map.insert(std::make_pair(list, new struct vasan_type_info_full)).first;
	
	info->second->args_ptr = 0;
	info->second->types = latest;
}

// This list is no longer going to be used.
// Remove it from the vasan map
extern "C" void
__vasan_vaend(va_list* list)
{
	auto full_info = vasan_map.find(list);
	if (full_info != vasan_map.end())
    {
		delete full_info->second;
		vasan_map.erase(full_info);
    }
}

// Create a copy of another list IN ITS CURRENT STATE!
extern "C" void
__vasan_vacopy(va_list* src, va_list* dst)
{
	auto src_info = vasan_map.find(src);
	auto dst_info = vasan_map.find(dst);

	if (src_info == vasan_map.end())
		return;

	if (dst_info == vasan_map.end())
		dst_info = vasan_map.insert(std::make_pair(dst, new struct vasan_type_info_full)).first;
  
	dst_info->second->args_ptr = src_info->second->args_ptr;
	dst_info->second->types = src_info->second->types;
}

// CallerSide: Function to pop the pointer from the stack
extern "C" void
__vasan_info_pop(int i)
{
	vasan_stack.pop();
}


// New version of the check_index function. You no longer have to figure out
// the index for this one. You just need a list pointer...
extern "C" void
__vasan_check_index_new(va_list* list, unsigned long type)
{
#ifdef VASAN_STATISTICS
	__atomic_add_fetch(&vararg_checks, 1, __ATOMIC_RELAXED);
#endif

	auto info = vasan_map.find(list);
	if (info == vasan_map.end())
		return;

	unsigned long index = info->second->args_ptr;
	
	if (index < info->second->types->arg_count)
	{
		if (type == info->second->types->arg_array[index] ||
            // allow all casts from nullptr to some other ptr type
			(info->second->types->arg_array[index] == 0xDEADBEEF && (type & 1)) ||
			// allow all casts from a ptr type to void*
			(permissive_void_ptr_checking && (info->second->types->arg_array[index] & 1) && (type == 710900085))) 
		{
			// type match
			info->second->args_ptr++;
			return;
		}
		else
		{
#ifdef VASAN_STATISTICS
			__atomic_add_fetch(&vararg_violations, 1, __ATOMIC_RELAXED);
#endif
			if (fp)
			{
				// Temporarily disable recursion so we can safely call fprintf
				(fprintf)(fp, "--------------------------\n");
				(fprintf)(fp, "Error: Type Mismatch \n");
				(fprintf)(fp, "Index is %lu \n", index);
				(fprintf)(fp, "Callee Type : %lu\n", type);
				(fprintf)(fp, "Caller Type : %lu\n", info->second->types->arg_array[index]);
				fflush(fp);
				__vasan_backtrace();

				if (!logging_only)
					exit(-1);
			}
		}
	}
	else
	{
#ifdef VASAN_STATISTICS
		__atomic_add_fetch(&vararg_violations, 1, __ATOMIC_RELAXED);
#endif
		if (fp)
		{
			(fprintf)(fp, "--------------------------\n");
			(fprintf)(fp, "Error: Index greater than Argument Count \n");
			(fprintf)(fp, "Index is %lu \n", index);
			fflush(fp);
			__vasan_backtrace();

			if (!logging_only)
				exit(-1);
		}
	}

	info->second->args_ptr++;
}


static void *thread_start(void *arg) 
{
	struct tinfo *tinfo = (struct tinfo *)arg;

	void *(*start_routine)(void *) = tinfo->real_start_routine;
	void *start_routine_arg = tinfo->real_start_routine_arg;
	free(tinfo);

	__vasan_init();

	// Make sure out thread-specific destructor will be called
	// FIXME: we can do this only any other specific key is set by
	// intercepting the pthread_setspecific function itself
	pthread_setspecific(thread_cleanup_key, (void *)1);

	return start_routine(start_routine_arg);
}

// overrides thread start func
extern "C" int pthread_create (pthread_t *thread, const pthread_attr_t *attr, void *(*start_routine)(void*), void *arg) throw()
{
	struct tinfo* tinfo = (struct tinfo*)malloc(sizeof(struct tinfo));
	tinfo->real_start_routine = start_routine;
	tinfo->real_start_routine_arg = arg;

	if (!real_pthread_create)
	  *(void**)&real_pthread_create = dlsym(RTLD_NEXT, "pthread_create");
	return real_pthread_create(thread, attr, thread_start, tinfo);
}

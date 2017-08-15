#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>
#ifndef NO_BACKTRACE
#include <execinfo.h>
#endif
#include <pthread.h>

#define DEBUG
#define MAXPATH 1000
#define INITIAL_SIZE 1024
#define MAP_MISSING -3  /* No such element */
#define MAP_FULL -2 /* Hashmap is full */
#define MAP_OMEM -1 /* Out of Memory */
#define MAP_OK 0 /* OK */

/*
 * any_t is a pointer.  This allows you to put arbitrary structures in
 * the hashmap.
 */
typedef void *any_t;

/*
 * PFany is a pointer to a function that can take two any_t arguments
 * and return an integer. Returns status code..
 */
typedef int (*PFany)(any_t, any_t);

/*
 * map_t is a pointer to an internally maintained data structure.
 * Clients of this package do not need to know how hashmaps are
 * represented.  They see and manipulate only map_t's. 
 */
typedef any_t map_t;


/* this is what the instrumentation code will pass to the runtime.
 * it's type info that has not been associated with a va_list yet.
 */
struct vasan_type_info_tmp
{
	unsigned long id;
	unsigned long arg_count;
	unsigned long*  arg_array;	
};

struct vasan_type_info_full
{
	va_list* list_ptr;
	unsigned int args_ptr;
	struct vasan_type_info_tmp* types;
};

/* We need to keep keys and values */
typedef struct _hashmap_element{
	int key;
	int in_use;
	any_t data;
} hashmap_element;

/* A hashmap has some maximum size and current size,
 * as well as the data to hold.
 */
typedef struct _hashmap_map{
	int table_size;
	int size;
	hashmap_element *data;
} hashmap_map;

struct stack_elem_t
{
	void* data;
	struct stack_elem_t* next;
};

struct stack_t
{
	struct stack_elem_t* top;
};

struct tinfo 
{
	void *(*real_start_routine)(void *);
	void *real_start_routine_arg;
};

static inline unsigned char __vasan_stack_empty(struct stack_t* stack);
static inline void __vasan_stack_push(struct stack_t* stack, void* data);
static inline void* __vasan_stack_pop(struct stack_t* stack);
static inline void* __vasan_stack_top(struct stack_t* stack);
static inline struct stack_t* __vasan_stack_new();
static inline void __vasan_stack_free(struct stack_t* stack);

/*
 * Return an empty hashmap. Returns NULL if empty.
 */
static inline map_t __vasan_hashmap_new();

/*  
 * Iteratively call f with argument (item, data) for 
 * each element data in the hashmap. The function must
 * return a map status code. If it returns anything other
 * than MAP_OK the traversal is terminated. f must
 * not reenter any hashmap functions, or deadlock may arise.
 */
static inline int __vasan_hashmap_iterate(map_t in, PFany f, any_t item);

/*
 * Add an element to the hashmap. Return MAP_OK or MAP_OMEM.
 */
static inline int __vasan_hashmap_put(map_t in, int key, any_t value);

/*
 * Get an element from the hashmap. Return MAP_OK or MAP_MISSING.
 */
static inline int __vasan_hashmap_get(map_t in, int key, any_t *arg);

/*
 * Remove an element from the hashmap. Return MAP_OK or MAP_MISSING.
 */
static inline int __vasan_hashmap_remove(map_t in, int key);

/*
 * Get any element. Return MAP_OK or MAP_MISSING.
 * remove - should the element be removed from the hashmap
 */
static inline int __vasan_hashmap_get_one(map_t in, any_t *arg, int remove);

/*
 * Free the hashmap
 */
static inline void __vasan_hashmap_free(map_t in);

/*
 * Get the current size of a hashmap
 */
static inline int __vasan_hashmap_length(map_t in);


/* only holds the call site info */
static __thread struct stack_t* vasan_stack;

/* maps va_lists onto their call site info */
static __thread map_t vasan_map;

/* protects accesses to global structures
 * it's just a simple spinlock as we don't
 * expect much contention
 */
static volatile int spinlock = 0;

#ifdef VASAN_STATISTICS
static unsigned long long vararg_calls      = 0;
static unsigned long long vararg_checks     = 0;
static unsigned long long vararg_violations = 0;
#endif

/* if set to 1, we log violations but don't terminate
 * the program when a violation is triggered
 */
static unsigned char logging_only = 0;

/* if set to 1, allow all pointer types to be cast to void* and char* */
static unsigned char permissive_void_ptr_checking = 0;

/* file we're logging to. can be either stderr or a real file */
static FILE* fp = (FILE*)0;

/* When set to 1, it's safe to access the global state */
static unsigned char vasan_initialized = 0;

/* Thread data for the cleanup handler */
static pthread_key_t thread_cleanup_key;

static int (*real_pthread_create) (pthread_t *, const pthread_attr_t *, void *(*)(void*), void *);

int __attribute__((weak)) backtrace(void** buffer, int size)
{
	(fprintf)(fp, "Your standard C library doesn't seem to support backtracing.");
	return 0;
}

char** __attribute__((weak)) backtrace_symbols(void* const* buffer, int size)
{
	return NULL;
}

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

static inline unsigned char __vasan_stack_empty(struct stack_t* stack)
{
	return (stack && stack->top) ? 1 : 0;
}

static inline void __vasan_stack_push(struct stack_t* stack, void* data)
{
	struct stack_elem_t* elem = (struct stack_elem_t*)malloc(sizeof(struct stack_elem_t));
	elem->data = data;
	elem->next = stack->top;
	stack->top = elem;
}

static inline void* __vasan_stack_pop(struct stack_t* stack)
{
	if (stack->top)
	{
		struct stack_elem_t* elem = stack->top;
		void* result = elem->data;
		stack->top = elem->next;
		free(elem);		
		return result;	    
	}

	return (void*)0;
}

static inline void* __vasan_stack_top(struct stack_t* stack)
{
	if (stack->top)
		return stack->top->data;
	return (void*)0;		
}

static inline struct stack_t* __vasan_stack_new()
{
	struct stack_t* result = (struct stack_t*)malloc(sizeof(struct stack_t));
	result->top = (void*)0;
	return result;
}

static inline void __vasan_stack_free(struct stack_t* stack)
{
	while(stack->top)
		(void)__vasan_stack_pop(stack);
	free(stack);
	stack = (struct stack_t*)0;
}

/*
 * Return an empty hashmap, or NULL on failure.
 */
static inline map_t __vasan_hashmap_new() 
{
	hashmap_map* m = (hashmap_map*) malloc(sizeof(hashmap_map));
	if(!m) goto err;

	m->data = (hashmap_element*) calloc(INITIAL_SIZE, sizeof(hashmap_element));
	if(!m->data) goto err;

	m->table_size = INITIAL_SIZE;
	m->size = 0;

	return m;
err:
	if (m)
		__vasan_hashmap_free(m);
	return NULL;
}

/*
 * Hashing function for an integer
 */
static inline unsigned int __vasan_hashmap_hash_int(hashmap_map * m, unsigned int key)
{
	/* Robert Jenkins' 32 bit Mix Function */
	key += (key << 12);
	key ^= (key >> 22);
	key += (key << 4);
	key ^= (key >> 9);
	key += (key << 10);
	key ^= (key >> 2);
	key += (key << 7);
	key ^= (key >> 12);

	/* Knuth's Multiplicative Method */
	key = (key >> 3) * 2654435761;

	return key % m->table_size;
}

/*
 * Return the integer of the location in data
 * to store the point to the item, or MAP_FULL.
 */
static inline int __vasan_hashmap_hash(map_t in, int key)
{
	int curr;
	int i;

	/* Cast the hashmap */
	hashmap_map* m = (hashmap_map *) in;

	/* If full, return immediately */
	if(m->size == m->table_size) return MAP_FULL;

	/* Find the best index */
	curr = __vasan_hashmap_hash_int(m, key);

	/* Linear probling */
	for(i = 0; i< m->table_size; i++){
		if(m->data[curr].in_use == 0)
			return curr;

		if(m->data[curr].key == key && m->data[curr].in_use == 1)
			return curr;

		curr = (curr + 1) % m->table_size;
	}

	return MAP_FULL;
}

/*
 * Doubles the size of the hashmap, and rehashes all the elements
 */
static inline int __vasan_hashmap_rehash(map_t in)
{
	int i;
	int old_size;
	hashmap_element* curr;

	/* Setup the new elements */
	hashmap_map *m = (hashmap_map *) in;
	hashmap_element* temp = (hashmap_element *)
		calloc(2 * m->table_size, sizeof(hashmap_element));
	if(!temp) return MAP_OMEM;

	/* Update the array */
	curr = m->data;
	m->data = temp;

	/* Update the size */
	old_size = m->table_size;
	m->table_size = 2 * m->table_size;
	m->size = 0;

	/* Rehash the elements */
	for(i = 0; i < old_size; i++){
		int status = __vasan_hashmap_put(m, curr[i].key, curr[i].data);
		if (status != MAP_OK)
			return status;
	}

	free(curr);

	return MAP_OK;
}

/* 
 * Add a pointer to the hashmap with some key
 */
static inline int __vasan_hashmap_put(map_t in, int key, any_t value)
{
	int index;
	hashmap_map* m;

	/* Cast the hashmap */
	m = (hashmap_map *) in;

	/* Find a place to put our value */
	index = __vasan_hashmap_hash(in, key);
	while(index == MAP_FULL){
		if (__vasan_hashmap_rehash(in) == MAP_OMEM) {
			return MAP_OMEM;
		}
		index = __vasan_hashmap_hash(in, key);
	}

	/* Set the data */
	m->data[index].data = value;
	m->data[index].key = key;
	m->data[index].in_use = 1;
	m->size++;

	return MAP_OK;
}

/*
 * Get your pointer out of the hashmap with a key
 */
static inline int __vasan_hashmap_get(map_t in, int key, any_t *arg)
{
	int curr;
	int i;
	hashmap_map* m;

	/* Cast the hashmap */
	m = (hashmap_map *) in;

	/* Find data location */
	curr = __vasan_hashmap_hash_int(m, key);

	/* Linear probing, if necessary */
	for(i = 0; i< m->table_size; i++){

		if(m->data[curr].key == key && m->data[curr].in_use == 1){
			*arg = (int *) (m->data[curr].data);
			return MAP_OK;
		}

		curr = (curr + 1) % m->table_size;
	}

	*arg = NULL;

	/* Not found */
	return MAP_MISSING;
}

/*
 * Get a random element from the hashmap
 */
static inline int __vasan_hashmap_get_one(map_t in, any_t *arg, int remove)
{
	int i;
	hashmap_map* m;

	/* Cast the hashmap */
	m = (hashmap_map *) in;

	/* On empty hashmap return immediately */
	if (__vasan_hashmap_length(m) <= 0)
		return MAP_MISSING;

	/* Linear probing */
	for(i = 0; i< m->table_size; i++)
		if(m->data[i].in_use != 0){
			*arg = (any_t) (m->data[i].data);
			if (remove) {
				m->data[i].in_use = 0;
				m->size--;
			}
			return MAP_OK;
		}

	return MAP_OK;
}

/*
 * Iterate the function parameter over each element in the hashmap.  The
 * additional any_t argument is passed to the function as its first
 * argument and the hashmap element is the second.
 */
static inline int __vasan_hashmap_iterate(map_t in, PFany f, any_t item) 
{
	int i;

	/* Cast the hashmap */
	hashmap_map* m = (hashmap_map*) in;

	/* On empty hashmap, return immediately */
	if (__vasan_hashmap_length(m) <= 0)
		return MAP_MISSING;

	/* Linear probing */
	for(i = 0; i< m->table_size; i++)
		if(m->data[i].in_use != 0) {
			any_t data = (any_t) (m->data[i].data);
			int status = f(item, data);
			if (status != MAP_OK) {
				return status;
			}
		}

	return MAP_OK;
}

/*
 * Remove an element with that key from the map
 */
static inline int __vasan_hashmap_remove(map_t in, int key)
{
	int i;
	int curr;
	hashmap_map* m;

	/* Cast the hashmap */
	m = (hashmap_map *) in;

    /* Find key */
	curr = __vasan_hashmap_hash_int(m, key);

	/* Linear probing, if necessary */
	for(i = 0; i< m->table_size; i++){
		if(m->data[curr].key == key && m->data[curr].in_use == 1){
			/* Blank out the fields */
			m->data[curr].in_use = 0;
			m->data[curr].data = NULL;
			m->data[curr].key = 0;

			/* Reduce the size */
			m->size--;
			return MAP_OK;
		}
		curr = (curr + 1) % m->table_size;
	}

	/* Data not found */
	return MAP_MISSING;
}

/* Deallocate the hashmap */
static inline void __vasan_hashmap_free(map_t in)
{
	hashmap_map* m = (hashmap_map*) in;
	free(m->data);
	free(m);
}

/* Return the length of the hashmap */
static inline int __vasan_hashmap_length(map_t in)
{
	hashmap_map* m = (hashmap_map *) in;
	if(m != NULL) return m->size;
	else return 0;
}

/* Thread-specific data destructor */
static void thread_cleanup_handler(void *_iter) 
{
	__vasan_stack_free(vasan_stack);
	__vasan_hashmap_free(vasan_map);
}

static void __attribute__((constructor(0)))  __vasan_init()
{
	char path[MAXPATH];
	char* disabled, *home;

	/* Thread-local state must be initialized for every thread */
	vasan_stack = __vasan_stack_new();
	vasan_map   = __vasan_hashmap_new();

	/* But global state only once.... Make sure it happens safely */
	__vasan_lock();

	if(vasan_initialized)
	{
		__vasan_unlock();
		return;
	}

	/* Initialize pthread interceptors for thread allocation */
	*(void**)&real_pthread_create = dlsym(RTLD_NEXT, "pthread_create");
	
	/* Setup the cleanup handler */
	pthread_key_create(&thread_cleanup_key, thread_cleanup_handler);
	
	home = getenv("VASAN_ERR_LOG_PATH");
	if (home)
	{
		strcpy(path, home);
		strcat(path, "error.txt");
		fp = fopen(path, "a+");
		logging_only = 1;
	}

	if (!fp)
		fp = stderr;

	disabled = getenv("VASAN_NO_ERROR_REPORTING");

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

/* CallerSide: Function to push the pointer in the stack */
void
__vasan_info_push(struct vasan_type_info_tmp *x)
{
#ifdef VASAN_STATISTICS
	__atomic_add_fetch(&vararg_calls, 1, __ATOMIC_RELAXED);
#endif
	__vasan_stack_push(vasan_stack, x);
}

/* We've seen a va_start call.
 * Associate the corresponding vasan_type_info_tmp struct with this list
 * and store it in the vasan map
 */
void
__vasan_vastart(va_list* list)
{
	struct vasan_type_info_tmp* latest = __vasan_stack_top(vasan_stack);
	struct vasan_type_info_full* info;

	if (!latest)
		return;

	if (__vasan_hashmap_get(vasan_map, (unsigned long)list, (any_t*)&info) == MAP_MISSING)
	{
		info = (struct vasan_type_info_full*)malloc(sizeof(struct vasan_type_info_full));
		__vasan_hashmap_put(vasan_map, (unsigned long)list, (any_t*)info);
	}
	
	info->list_ptr = list;
	info->args_ptr = 0;
	info->types = latest;
}

/* This list is no longer going to be used.
 * Remove it from the vasan map
 */
void
__vasan_vaend(va_list* list)
{
	struct vasan_type_info_full* info;
	if (__vasan_hashmap_get(vasan_map, (unsigned long)list, (any_t*)&info) != MAP_MISSING)
	{
		__vasan_hashmap_remove(vasan_map, (unsigned long)list);
		free(info);
	}
}

/* Create a copy of another list IN ITS CURRENT STATE! */
void
__vasan_vacopy(va_list* src, va_list* dst)
{
	struct vasan_type_info_full* src_info, *dst_info;
	if (__vasan_hashmap_get(vasan_map, (unsigned long)src, (any_t*)&src_info) == MAP_MISSING)
		return;
	
	if (__vasan_hashmap_get(vasan_map, (unsigned long)dst, (any_t*)&dst_info) == MAP_MISSING)
	{
		dst_info = (struct vasan_type_info_full*)malloc(sizeof(struct vasan_type_info_full));
		__vasan_hashmap_put(vasan_map, (unsigned long)dst, (any_t*)dst_info);
	}

	dst_info->list_ptr = dst;
	dst_info->args_ptr = src_info->args_ptr;
	dst_info->types = src_info->types;
}

/* CallerSide: Function to pop the pointer from the stack */
void
__vasan_info_pop(int i)
{
	__vasan_stack_pop(vasan_stack);
}


/* New version of the check_index function. You no longer have to figure out
 * the index for this one. You just need a list pointer...
 */
void
__vasan_check_index_new(va_list* list, unsigned long type)
{
#ifdef VASAN_STATISTICS
	__atomic_add_fetch(&vararg_checks, 1, __ATOMIC_RELAXED);
#endif

	struct vasan_type_info_full* info;
	unsigned long index;
	if (__vasan_hashmap_get(vasan_map, (unsigned long)list, (any_t*)&info) == MAP_MISSING)
		return;

	index = info->args_ptr;
	
	if (index < info->types->arg_count)
	{
		if (type == info->types->arg_array[index] ||
            // allow all casts from nullptr to some other ptr type
			((info->types->arg_array[index] == 0xDEADBEEF) && (type & 1)) ||
			// allow all casts from a ptr type to void*
			(permissive_void_ptr_checking && (info->types->arg_array[index] & 1) && (type == 710900085)))
		{
			/* type match */
			info->args_ptr++;
			return;
		}
		else
		{
#ifdef VASAN_STATISTICS
			__atomic_add_fetch(&vararg_violations, 1, __ATOMIC_RELAXED);
#endif
			if (fp)
			{
				(fprintf)(fp, "--------------------------\n");
				(fprintf)(fp, "Error: Type Mismatch \n");
				(fprintf)(fp, "Index is %lu \n", index);
				(fprintf)(fp, "Callee Type : %lu\n", type);
				(fprintf)(fp, "Caller Type : %lu\n", info->types->arg_array[index]);
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

	info->args_ptr++;
}


static void *thread_start(void *arg) 
{
	struct tinfo *tinfo = (struct tinfo *)arg;

	void *(*start_routine)(void *) = tinfo->real_start_routine;
	void *start_routine_arg = tinfo->real_start_routine_arg;
	free(tinfo);

	__vasan_init();

	/* Make sure out thread-specific destructor will be called
	 * FIXME: we can do this only any other specific key is set by
	 * intercepting the pthread_setspecific function itself
     */
	pthread_setspecific(thread_cleanup_key, (void *)1);

	return start_routine(start_routine_arg);
}

/* overrides thread start func */
int pthread_create (pthread_t *thread, const pthread_attr_t *attr, void *(*start_routine)(void*), void *arg) 
{
	struct tinfo* tinfo = (struct tinfo*)malloc(sizeof(struct tinfo));
	tinfo->real_start_routine = start_routine;
	tinfo->real_start_routine_arg = arg;

	if (!real_pthread_create)
	  *(void**)&real_pthread_create = dlsym(RTLD_NEXT, "pthread_create");
	return real_pthread_create(thread, attr, thread_start, tinfo);
}

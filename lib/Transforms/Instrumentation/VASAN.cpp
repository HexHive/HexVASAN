/* -*- Mode:C++; c-file-style: "linux"; c-basic-offset: 2; indent-tabs-mode: nil; -*- */
#include "llvm/ADT/PriorityQueue.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/TableGen/Error.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include <algorithm>

#include <fstream>
#include <iostream>
#include <map>
#include <queue>
#include <stdio.h>
#include <string.h>
#include <string>

std::map<llvm::AllocaInst *, llvm::AllocaInst *> list_map;
std::map<llvm::Value *, long int> variadic_map;
using namespace llvm;
using std::string;

namespace {
unsigned hash(unsigned x) {
  x = ((x >> 16) ^ x) * 0x45d9f3b;
  x = ((x >> 16) ^ x) * 0x45d9f3b;
  x = (x >> 16) ^ x;
  return x;
}
unsigned long res = 0;
  unsigned hashType(Type *T, llvm::LLVMContext& Ctx, bool OuterType=true) {
  unsigned Result = hash(T->getTypeID());

/*
  llvm::errs() << "Callee hashing type: ";
  T->dump();
  llvm::errs() << "Initial hash: " << Result << "\n";
*/

  if (auto *PointerTy = dyn_cast<PointerType>(T)) {
    if (T->getPointerElementType()) {
      if (auto *StructTy = dyn_cast<StructType>(T->getPointerElementType())) {

        Result = hash(T->getPointerElementType()->getTypeID());
        Result = hash(Result ^ StructTy->isPacked());
        Result = hash(Result ^ StructTy->isLiteral());
        Result = hash(Result ^ StructTy->isOpaque());

        for (unsigned int i = 0; i < StructTy->getNumElements(); i++) {
            Result = hash(Result ^ StructTy->getElementType(i)->getTypeID());
        }
        Result = hash(Result ^ StructTy->getTypeID());
        res = Result;
//        printf("Calleeee Pointer 1 %lu \n", res);
        return (Result | 1);
      }
    } else {

      Result = hash(Result ^ PointerTy->getAddressSpace());
      Result = hash(Result ^ PointerTy->getTypeID());
      res = Result;
//      printf("Calleeee Pointer 2 %lu \n", res);
      return (Result | 1);
    }
  }

  if (auto *StructTy = dyn_cast<StructType>(T)) {

    Result = hash(Result ^ StructTy->isPacked());
    Result = hash(Result ^ StructTy->isLiteral());
    Result = hash(Result ^ StructTy->isOpaque());

    for (unsigned int i = 0; i < StructTy->getNumElements(); i++) {
        Result = hash(Result ^ StructTy->getElementType(i)->getTypeID());
    }
    Result = hash(Result ^ StructTy->getTypeID());
    res = Result;
//    printf("Calleeee Struct  %lu \n", res);
    return (Result & (~1));
  }

  if (auto *IntegerTy = dyn_cast<IntegerType>(T))  {
//    llvm::errs() << "Integer type - bitwidth: " << IntegerTy->getBitWidth() << "\n";
    // all integer types are implicitly cast to an equivalent type of at least 32 bits
    if (OuterType)
      Result = hash(Result ^ std::max<unsigned>(32, IntegerTy->getBitWidth()));
    else
      Result = hash(Result ^ IntegerTy->getBitWidth());
  }

  // Treat all floats as doubles
  if (OuterType && T->isFloatTy()) {
    T = Type::getDoubleTy(Ctx);
    Result = hash(T->getTypeID());
  }

  if (auto *FunctionTy = dyn_cast<FunctionType>(T))
    Result = hash(Result ^ FunctionTy->isVarArg());

  if (auto *ArrayTy = dyn_cast<ArrayType>(T))
    Result = hash(Result ^ ArrayTy->getNumElements());

  if (auto *VectorTy = dyn_cast<VectorType>(T))
    Result = hash(Result ^ VectorTy->getNumElements());

  for (Type *SubType : T->subtypes()) {
    Result = hash(Result ^ hashType(SubType, Ctx, false));
  }
  Result = hash(Result ^ T->getTypeID());
  res = Result & (~1);
  if (dyn_cast<PointerType>(T))
    res |= 1;
//  printf("Calleeee end %lu \n", res);
  return res;
}
}

namespace llvm {
struct VASANVisitor : public InstVisitor<VASANVisitor> {
public:
  VASANVisitor(Module &M) : N_M(M) {}

  std::map<Value *, std::set<BasicBlock *> *> checked;

  void instrumentVAArgs();

  void visitCallInst(CallInst &I) {
    Function *ft = I.getCalledFunction();

    if (ft == nullptr)
      return;

    auto ID = ft->getIntrinsicID();
    if (ID != Intrinsic::vastart && 
		ID != Intrinsic::vaend &&
        ID != Intrinsic::vacopy)
      return;

    // Insert a call after the vararg func
    IRBuilder<> B(I.getNextNode());
    Type *VoidTy = Type::getVoidTy(N_M.getContext());
    Type *valistPtr = PointerType::getUnqual(Type::getInt8Ty(N_M.getContext()));

    if (ft->getIntrinsicID() == llvm::Intrinsic::vastart) {
      // The first argument of the call is a bitcast
      // of the va_list struct to i8*
      BitCastInst *listCast = dyn_cast<BitCastInst>(I.getArgOperand(0));
	  Value* listPtr = listCast ? listCast->getOperand(0) : I.getArgOperand(0);

      if (listPtr->getType() != valistPtr)
        listPtr = B.CreateBitCast(listPtr, valistPtr);

      Constant *Func = N_M.getOrInsertFunction("__vasan_vastart", VoidTy,
                                               valistPtr, nullptr);
      B.CreateCall(Func, {listPtr});
    } else if (ft->getIntrinsicID() == llvm::Intrinsic::vacopy) {
      // arg0 of the intrinsic is the dst
      // arg1 of the intrinsic is the src
      // the VASAN runtime does it the other way around

      BitCastInst *dstCast = dyn_cast<BitCastInst>(I.getArgOperand(0));
	  Value* dstPtr = dstCast ? dstCast->getOperand(0) : I.getArgOperand(0);
      BitCastInst *srcCast = dyn_cast<BitCastInst>(I.getArgOperand(1));
	  Value* srcPtr = srcCast ? srcCast->getOperand(0) : I.getArgOperand(1);

      if (srcPtr->getType() != valistPtr)
        srcPtr = B.CreateBitCast(srcPtr, valistPtr);
      if (dstPtr->getType() != valistPtr)
        dstPtr = B.CreateBitCast(dstPtr, valistPtr);

      Constant *Func = N_M.getOrInsertFunction("__vasan_vacopy", VoidTy,
                                               valistPtr, valistPtr, nullptr);
      B.CreateCall(Func, {srcPtr, dstPtr});
    } else if (ft->getIntrinsicID() == llvm::Intrinsic::vaend) {

      BitCastInst *listCast = dyn_cast<BitCastInst>(I.getArgOperand(0));
	  Value* listPtr = listCast ? listCast->getOperand(0) : I.getArgOperand(0);

      if (listPtr->getType() != valistPtr)
        listPtr = B.CreateBitCast(listPtr, valistPtr);

      Constant *Func =
          N_M.getOrInsertFunction("__vasan_vaend", VoidTy, valistPtr, nullptr);
      B.CreateCall(Func, {listPtr});
    }
  }

  template<class InstType> void instrumentVaListReference(InstType& I) {  
    // Trace through the IR to find the phi node that
    // collapses the in_reg and in_mem values
    auto BB = dyn_cast<BasicBlock>(I.getParent());

    if (!BB || !*succ_begin(BB) || !*succ_begin(*succ_begin(BB)))
      return;

    // If this value has already been checked within this basic block
    // then don't test it again
    Type *VoidTy = Type::getVoidTy(N_M.getContext());
    Type *Int64Ty = Type::getInt64Ty(N_M.getContext());
    Type *valistPtr = PointerType::getUnqual(Type::getInt8Ty(N_M.getContext()));
    Value *listPtr = I.getOperand(0);

    auto InstrumentedBBs = checked.find(listPtr);
    if (InstrumentedBBs != checked.end()) {
      auto InstrumentedBB = (*InstrumentedBBs).second->find(BB);
      if (InstrumentedBB != (*InstrumentedBBs).second->end())
        return;
      else
        (*InstrumentedBBs).second->insert(BB);
    } else {
      std::set<BasicBlock *> *newBBs = new std::set<BasicBlock *>;
      newBBs->insert(BB);
      checked.insert(std::make_pair(listPtr, newBBs));
    }

    IRBuilder<> B(&I);
    if (listPtr->getType() != valistPtr)
      listPtr = B.CreateBitCast(listPtr, valistPtr);

    auto CollapseNode = *succ_begin(BB);
    while (!dyn_cast<PHINode>(CollapseNode->begin())) {
      if (!*succ_begin(CollapseNode))
        return;
      CollapseNode = *succ_begin(CollapseNode);
    }
    unsigned long type_hash = 0;

    if (PHINode *phi = dyn_cast<PHINode>(CollapseNode->begin()))
      type_hash = hashType(phi->getType()->getPointerElementType(), N_M.getContext());

    Constant *Func = N_M.getOrInsertFunction("__vasan_check_index_new", VoidTy,
                                             valistPtr, Int64Ty, nullptr);
    B.CreateCall(Func, {listPtr, ConstantInt::get(Int64Ty, type_hash)});

  }

  void visitLoadInst(LoadInst& I) {
    // va_arg calls operating on va_lists that are not stored on the stack
    // start with load instructions.
    auto SrcGEP = dyn_cast<GEPOperator>(I.getOperand(0));

    // We have at least two zero indices at the end.  More indices are
    // possible if the va_list is part of a multilevel struct
    if (!SrcGEP || SrcGEP->getNumIndices() < 2)
      return;

    // Cache the indices. We're going to need them later
    std::vector<unsigned long> Idxs(SrcGEP->getNumIndices());
    unsigned i = 0;
    for (auto Idx = SrcGEP->idx_begin();
         Idx != SrcGEP->idx_end();
         ++Idx)
    {
      if (dyn_cast<ConstantInt>(*Idx))
        Idxs[i++] = dyn_cast<ConstantInt>(*Idx)->getZExtValue();
      else
        Idxs[i++] = (unsigned long) ~0;
    }

    // last two indices must be zero
    if (Idxs[SrcGEP->getNumIndices()-1] || 
        Idxs[SrcGEP->getNumIndices()-2])
      return;

    auto SrcType = dyn_cast<CompositeType>(SrcGEP->getSourceElementType());

    if (!SrcType)
      return;

    auto PointeeType = dyn_cast<CompositeType>(SrcType->getTypeAtIndex((unsigned)0));

    if (!PointeeType)
      return;

    // traverse multilevel structs
    for (i = 2; i < SrcGEP->getNumIndices() - 1; ++i)
    {
      if (Idxs[i] != (unsigned long) ~0)
      {
        PointeeType = dyn_cast<CompositeType>(PointeeType->getTypeAtIndex(Idxs[i]));

        if (!PointeeType)
          return;
      }
    }

    // See if the innermost type is a va_list struct	  
    auto InnerType = dyn_cast<StructType>(PointeeType);
  
    if (!InnerType || 
        !InnerType->hasName() ||
        InnerType->getName() != "struct.__va_list_tag")
      return;

    instrumentVaListReference<LoadInst>(I);
  }

  void visitGetElementPtrInst(GetElementPtrInst &I) {
    // We need to find this instruction: %gp_offset_p = getelementptr
    // inbounds %struct.__va_list_tag, %struct.__va_list_tag*
    // %arraydecay2, i32 0, i32 0
    auto BaseType = dyn_cast<PointerType>(I.getOperand(0)->getType());

    if (!BaseType)
      return;

    auto PointeeType =
        dyn_cast<StructType>(BaseType->getTypeAtIndex((unsigned)0));

    if (!PointeeType || !PointeeType->hasName() ||
        PointeeType->getName() != "struct.__va_list_tag")
      return;

    // Ok. this is a definite va_arg op. now we just need to verify that
    // operands 1 and 2 are null
    auto Index = dyn_cast<ConstantInt>(I.getOperand(1));
    auto Field = dyn_cast<ConstantInt>(I.getOperand(2));

    if (!Index || !Field || Index->getZExtValue() != 0 ||
        (Field->getZExtValue() != 0 && Field->getZExtValue() != 1))
      return;

    instrumentVaListReference<GetElementPtrInst>(I);
  }

  void visitVAArgInstr(VAArgInst &I) {
    // FreeBSD clang emits these afaik
    errs() << "Saw VA Arg Inst: ";
    I.dump();
  }

  Module &N_M;
};
}

namespace {

struct VASAN : public ModulePass {

  static char ID;
  LLVMContext *Context;

  VASAN() : ModulePass(ID) {}

  bool doInitialization(Module &M) { return true; }

  bool doFinalization(Module &M) { return false; }

  uint32_t file_rand = rand();
  std::string file_r = std::to_string(file_rand);

  virtual bool runOnModule(Module &M) {
//    M.dump();
    Context = &M.getContext();
    auto dm = M.getDataLayout();
    srand(time(nullptr));
    std::string file_name;

    for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
      std::ofstream func_va;
      Value *funcptr;

      if (Function *Fnew = dyn_cast<Function>(F)) {
        funcptr = dyn_cast<Value>(Fnew);
      }
      std::string addrtaken = "no";
      std::string definition = "definition";
      if (F->empty()) {
        definition = "declaration";
      } else
        definition = "definition";

      if (F->isVarArg()) {

        /*================================================*/
        uint32_t user_count = 0;
        uint32_t user_call_count = 0;

        for (User *func_users : F->users()) {
          user_count++;

          ConstantExpr *bc = dyn_cast<ConstantExpr>(func_users);
          while (bc != nullptr && bc->isCast() && !bc->user_empty()) {
            func_users = *bc->users().begin();
            bc = dyn_cast<ConstantExpr>(func_users);
          }

          if (dyn_cast<CallInst>(func_users)) {
            user_call_count++;
          }
        }
        if (user_count == user_call_count) {
          addrtaken = "no";
        } else {
          addrtaken = "yes";
        }

        /*================================================*/

        long int unique_id = rand();
        variadic_map.insert(
            std::pair<llvm::Value *, long int>(funcptr, unique_id));
        std::string str;
        llvm::raw_string_ostream rso(str);
        F->getFunctionType()->print(rso);
        std::queue<User *> func_user;
        uint32_t line_no;

        if (MDNode *md = F->getMetadata("dbg")) {
          if (DISubprogram *dl = dyn_cast<DISubprogram>(md)) {
            line_no = dl->getLine();
            file_name = dl->getFilename();
          }
        }

        if (getenv("VASAN_LOG_PATH") != nullptr) {
          char *home = getenv("VASAN_LOG_PATH");

          std::string pathname = home + file_r + "vfunc.csv";

          func_va.open(pathname, std::ios_base::app | std::ios_base::out);

          func_va << unique_id << "\t" << F->getName().str() << "\t"
                  << rso.str() << "\t" << F->getLinkage() << "\t" << file_name
                  << "\t" << line_no;

          func_va << "\t" << addrtaken << "\t" << definition << "\n";
        }
      }
      func_va.close();
    }
    //================csv information ends here
    VASANVisitor V(M);
    V.visit(M);
    //=============================================================
    return false;
  }

  virtual bool runOnFunction(Function &F) { return false; }
};
}
// register pass
char VASAN::ID = 0;

INITIALIZE_PASS(VASAN, "VASAN", "VASAN", false, false)

ModulePass *llvm::createVASANPass() { return new VASAN(); }

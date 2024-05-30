/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <list>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <algorithm>

#include "llvm-c/Core.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/Pass.h"

#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/DenseSet.h>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

namespace
{

  class AFLCoverage : public ModulePass
  {

  public:
    static char ID;
    AFLCoverage() : ModulePass(ID) {}

    bool runOnModule(Module &M) override;

    // StringRef getPassName() const override {
    //  return "American Fuzzy Lop Instrumentation";
    // }
  };

}

int P_edge_num = 0;

char AFLCoverage::ID = 0;

static void getDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line)
{
#ifdef LLVM_OLD_DEBUG_API
  DebugLoc Loc = I->getDebugLoc();
  if (!Loc.isUnknown())
  {
    DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
    DILocation oDILoc = cDILoc.getOrigLocation();

    Line = oDILoc.getLineNumber();
    Filename = oDILoc.getFilename().str();

    if (filename.empty())
    {
      Line = cDILoc.getLineNumber();
      Filename = cDILoc.getFilename().str();
    }
  }
#else
  if (DILocation *Loc = I->getDebugLoc())
  {
    Line = Loc->getLine();
    Filename = Loc->getFilename().str();

    if (Filename.empty())
    {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc)
      {
        Line = oDILoc->getLine();
        Filename = oDILoc->getFilename().str();
      }
    }
  }
#endif /* LLVM_OLD_DEBUG_API */
}

static bool isBlacklisted(const Function *F)
{
  static const SmallVector<std::string, 8> Blacklist = {
      "asan.",
      "llvm.",
      "sancov.",
      "__ubsan_handle_",
      "free",
      "malloc",
      "calloc",
      "realloc"};

  for (auto const &BlacklistFunc : Blacklist)
  {
    if (F->getName().startswith(BlacklistFunc))
    {
      return true;
    }
  }

  return false;
}

bool AFLCoverage::runOnModule(Module &M)
{

  LLVMContext &C = M.getContext();
  LLVMContext *Ctx = nullptr;
  Ctx = &M.getContext();

  IntegerType *Int8Ty = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET"))
  {

    SAYF(cCYA "PDGF-llvm-pass " cBRI VERSION cRST " based on AFL\n");
  }
  else
    be_quiet = 1;

  /* Decide instrumentation ratio */

  char *inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str)
  {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");
  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  int pre_bb_num = 0;
  int none_pre_bb_num = 0;

  std::vector<std::string> basic_blocks;

  const char *outdir = getenv("OUTDIR");
  std::string OutDirectory;
  if (!outdir)
  {
    WARNF("use current directory as 'OUTDIR'\n");
    OutDirectory = ".";
  }
  else
  {
    OutDirectory = outdir;
  }

  std::ifstream targetsfile(OutDirectory + "/premake_results.txt");
  std::string lines;
  int hasfile = 0;
  if (targetsfile)
  {
    while (std::getline(targetsfile, lines))
      basic_blocks.push_back(lines);
    hasfile = 1;
  }
  else
  {
    WARNF("Notice! No targets file found!\n");
  }
  targetsfile.close();

  for (auto &F : M)
  {
    int firstbb = 1;

    for (auto &BB : F)
    {
      bool is_pre = false;

      std::string filename;
      unsigned line;
      std::string bb_name("");

      for (auto &I : BB)
      {
        getDebugLoc(&I, filename, line);

        static const std::string Xlibs("/usr/");
        if (filename.empty() || line == 0 || !filename.compare(0, Xlibs.size(), Xlibs))
          continue;

        if (bb_name.empty())
        {
          std::size_t found = filename.find_last_of("/\\");
          if (found != std::string::npos)
            filename = filename.substr(found + 1);

          bb_name = filename + "," + std::to_string(line);

          std::vector<std::string>::iterator it = std::find(basic_blocks.begin(), basic_blocks.end(), bb_name);
          if (it != basic_blocks.end())
          {
            is_pre = true;
          }

          break;
        }
      }

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      StringRef asmString = "jmp .+2";
      StringRef constraints = "~{dirflag},~{fpsr},~{flags}";
      FunctionType *FTy = FunctionType::get(Type::getVoidTy(*Ctx), false);
      llvm::InlineAsm *IA = llvm::InlineAsm::get(FTy, asmString, constraints, true, false, InlineAsm::AD_ATT);
      ArrayRef<Value *> Args = None;
      llvm::CallInst *Ptr_1 = IRB.CreateCall(IA, Args);
      Ptr_1->addAttribute(AttributeList::FunctionIndex, Attribute::NoUnwind);

      if (AFL_R(100) >= inst_ratio)
        continue;
      if (hasfile && !is_pre)
      {

        StringRef asmString_nop = "nop";
        StringRef constraints_nop = "~{dirflag},~{fpsr},~{flags}";
        FunctionType *FTy_nop = FunctionType::get(Type::getVoidTy(*Ctx), false);
        llvm::InlineAsm *IA_nop = llvm::InlineAsm::get(FTy_nop, asmString_nop, constraints_nop, true, false, InlineAsm::AD_ATT);
        ArrayRef<Value *> Args_nop = None;
        llvm::CallInst *Ptr_2 = IRB.CreateCall(IA_nop, Args_nop);
        Ptr_2->addAttribute(AttributeList::FunctionIndex, Attribute::NoUnwind);

        none_pre_bb_num++;
      }
      else
      {
        pre_bb_num++;
      }

      StringRef asmString_nop = "nop";
      StringRef constraints_nop = "~{dirflag},~{fpsr},~{flags}";
      FunctionType *FTy_nop = FunctionType::get(Type::getVoidTy(*Ctx), false);
      llvm::InlineAsm *IA_nop = llvm::InlineAsm::get(FTy_nop, asmString_nop, constraints_nop, true, false, InlineAsm::AD_ATT);
      ArrayRef<Value *> Args_nop = None;
      llvm::CallInst *Ptr_2 = IRB.CreateCall(IA_nop, Args_nop);
      Ptr_2->addAttribute(AttributeList::FunctionIndex, Attribute::NoUnwind);

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE >> 2);
      if (hasfile && !is_pre)
        cur_loc = cur_loc + (unsigned int)49152;

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;
    }
  }
  OKF("Instrumented as pre bbs: %d, none_pre bbs: %d \n", pre_bb_num, none_pre_bb_num);

  /* Say something nice. */

  if (!be_quiet)
  {

    if (!inst_blocks)
      WARNF("No instrumentation targets found.");
    else
      OKF("Instrumented %u locations (%s mode, ratio %u%%).",
          inst_blocks, getenv("AFL_HARDEN") ? "hardened" : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ? "ASAN/MSAN" : "non-hardened"), inst_ratio);
  }

  return true;
}

static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM)
{

  PM.add(new AFLCoverage());
}

static RegisterStandardPasses RegisterAFLPass(
    // PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);

//===- OptimisticAliasAnalysis.cpp - Stateless Alias Analysis Impl -------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the primary stateless implementation of the
// Alias Analysis interface that implements identities (two different
// globals cannot alias, etc), but does no stateful analysis.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/OptimisticAliasAnalysis.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/PhiValues.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/KnownBits.h"
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <llvm/Support/Debug.h>
#include <utility>
#include <iostream>
#include <string>
#include <fstream>
#include <sstream>
#include <map>

#define DEBUG_TYPE "optimisticaa"

using namespace llvm;

STATISTIC(NumberOfOptimisticAAQueries, "Number of optimisticAA alias calls");
STATISTIC(NumberOfOptimisticAAQueriesUnique, "Number of optimisticAA answers not from cache");
STATISTIC(NumberOfOptimisticDecisions, "Number of optimisticAA NoAlias decisions");
STATISTIC(NumberOfPessimisticDecisions, "Number of optimisticAA MayAlias decisions");

static cl::opt<bool> OptAADumpOptimistic("opt-aa-dump-optimistic", cl::Hidden, cl::init(false));
static cl::opt<bool> OptAADumpPessimistic("opt-aa-dump-pessimistic", cl::Hidden, cl::init(false));
static cl::opt<bool> OptAADumpCached("opt-aa-dump-cached", cl::Hidden, cl::init(false));
static cl::opt<bool> OptAADumpFirst("opt-aa-dump-first", cl::Hidden, cl::init(false));
static cl::opt<std::string> OptAASequence("opt-aa-seq", cl::Hidden, cl::init(""));
static cl::opt<std::string> OptAAProbing("opt-aa-probing", cl::Hidden, cl::desc(""), cl::init(""));
static cl::opt<std::string> OptAATarget("opt-aa-target", cl::Hidden, cl::desc(""), cl::init(""));
unsigned int OptimisticAAResult::currentDecision;

AliasResult OptimisticAAResult::alias(const MemoryLocation &LocA,
                                 const MemoryLocation &LocB,
                                 AAQueryInfo &AAQI) {
  // if no opt-aa-seq is given in the command line, we probably don't want any of this to happen.
  if(OptAASequence.empty()) {
    return AliasResult::MayAlias;
  }

  auto DumpInfo = [&](bool Cached, bool Optimistic){
    if (!(((Cached && OptAADumpCached) || (!Cached && OptAADumpFirst)) && ((Optimistic && OptAADumpOptimistic) || (!Optimistic && OptAADumpPessimistic))))
      return;
    dbgs() << "[ORAQL] " << (Optimistic ? "Optimistic" : "Pessimistic") << " query [Cached " << Cached << "]\n";
    dbgs() << "[ORAQL] - " << *LocA.Ptr << "["<<LocA.Size<<"]\n";
    dbgs() << "[ORAQL] - " << *LocB.Ptr << "["<<LocB.Size<<"]\n";
    const Function *Scope = nullptr;
    auto *PtrAI = dyn_cast<Instruction>(LocA.Ptr);
    auto *PtrBI = dyn_cast<Instruction>(LocB.Ptr);
    auto *PtrAArg = dyn_cast<Argument>(LocA.Ptr);
    auto *PtrBArg = dyn_cast<Argument>(LocB.Ptr);
    if (PtrAI)
      Scope = PtrAI->getFunction();
    else if (PtrBI)
      Scope = PtrBI->getFunction();
    else if (PtrAArg)
      Scope = PtrAArg->getParent();
    else if (PtrBArg)
      Scope = PtrBArg->getParent();
    dbgs() << "[ORAQL] Scope: " << (Scope?  Scope->getName() : "<unknown>") << "\n";
    if (PtrAI)
      dbgs() << "[ORAQL] LocA: " << PtrAI->getDebugLoc() << "\n";
    if (PtrBI)
      dbgs() << "[ORAQL] LocB: " << PtrBI->getDebugLoc() << "\n";
    dbgs() <<"\n";
  };

  NumberOfOptimisticAAQueries++;

  // Check if we have a cached result for this query.
  std::pair<const llvm::Value* const, const llvm::Value* const> pr(LocA.Ptr, LocB.Ptr);
  if (this->decisionCache.find(pr) != this->decisionCache.end()) {
    if(this->decisionCache[pr]) {
      DumpInfo(/* Cached */ true, /* Optimistic */ true);
      return AliasResult::NoAlias;
    }
    DumpInfo(/* Cached */true, /* Optimistic */ false);
    return AliasResult::MayAlias;
  }

  // We must run, and we have nothing in the cache, so the work begins.
  NumberOfOptimisticAAQueriesUnique++;
  currentDecision++;

  if (OptAAProbing.empty() or OptAAProbing == "chunked") {
    // use conventional probing
    if(this->optAAEnabled &&
       (currentDecision-1 >= this->decisions.size() || this->decisions[currentDecision-1] == 1)) {
      NumberOfOptimisticDecisions++;
      DumpInfo(/* Cached */false, /* Optimistic */ true);
      decisionCache[pr] = true;
      return AliasResult::NoAlias;
    }
    NumberOfPessimisticDecisions++;
    DumpInfo(/* Cached */false, /* Optimistic */ false);
    decisionCache[pr] = false;
    return AliasResult::MayAlias;
  }
  else {
    // use fourier probing
    for(auto it=this->decisions.begin(); it!=this->decisions.end(); it=it+2) {
      if(int(currentDecision-1)%(*it)==(*it+1)) {
        NumberOfOptimisticDecisions++;
        DumpInfo(/* Cached */false, /* Optimistic */ true);
        decisionCache[pr] = true;
        return AliasResult::NoAlias;
      }
    }
    NumberOfPessimisticDecisions++;
    DumpInfo(/* Cached */false, /* Optimistic */ false);
    decisionCache[pr] = false;
    return AliasResult::MayAlias;
  }
}

//===----------------------------------------------------------------------===//
// OptimisticAliasAnalysis Pass
//===----------------------------------------------------------------------===//

AnalysisKey OptimisticAA::Key;

OptimisticAAResult OptimisticAA::run(Function &F, FunctionAnalysisManager &AM) {
  return OptimisticAAResult();
}

OptimisticAAWrapperPass::OptimisticAAWrapperPass() : FunctionPass(ID) {
  initializeOptimisticAAWrapperPassPass(*PassRegistry::getPassRegistry());
}

char OptimisticAAWrapperPass::ID = 0;

void OptimisticAAWrapperPass::anchor() {}

INITIALIZE_PASS_BEGIN(OptimisticAAWrapperPass, "optimistic-aa",
                      "Optimistic Alias Analysis", true, true)
INITIALIZE_PASS_END(OptimisticAAWrapperPass, "optimistic-aa",
                    "Optimistic Alias Analysis", true, true)

FunctionPass *llvm::createOptimisticAAWrapperPass() {
  return new OptimisticAAWrapperPass();
}

bool OptimisticAAWrapperPass::runOnFunction(Function &F) {
  Result.reset(new OptimisticAAResult());

  Result->optAAEnabled = true;
  if (!OptAATarget.empty())
    if (!StringRef(F.getParent()->getTargetTriple()).contains(OptAATarget)) {
      Result->optAAEnabled = false;
      return false;
    }

  if(Result->decisions.empty()) {
    std::stringstream iss( OptAASequence );
    int seqItem;
    while ( iss >> seqItem ) {
      Result->decisions.push_back(seqItem);
    }
  }
  return false;
}

void OptimisticAAWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

//OptimisticAAResult llvm::createLegacyPMOptimisticAAResult(Pass &P, Function &F) {
//  return OptimisticAAResult(
//      F.getParent()->getDataLayout(), F,
//      P.getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F),
//      P.getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F));
//}

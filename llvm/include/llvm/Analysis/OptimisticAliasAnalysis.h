//===- OptimisticAliasAnalysis.h - Stateless, local Alias Analysis ---*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// This is the interface for LLVM's primary stateless and local alias analysis.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_OPTIMISTICALIASANALYSIS_H
#define LLVM_ANALYSIS_OPTIMISTICALIASANALYSIS_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include <algorithm>
#include <cstdint>
#include <memory>
#include <utility>

namespace llvm {

struct AAMDNodes;
class APInt;
class AssumptionCache;
class BasicBlock;
class DataLayout;
class DominatorTree;
class Function;
class GEPOperator;
class LoopInfo;
class PHINode;
class SelectInst;
class TargetLibraryInfo;
class PhiValues;
class Value;

/// This is the AA result object for the optimistic alias
/// analysis.
class OptimisticAAResult : public AAResultBase<OptimisticAAResult> {
  friend AAResultBase<OptimisticAAResult>;

public:
  AliasResult alias(const MemoryLocation &LocA, const MemoryLocation &LocB,
                    AAQueryInfo &AAQI);

};

/// Analysis pass providing a never-invalidated alias analysis result.
class OptimisticAA : public AnalysisInfoMixin<OptimisticAA> {
  friend AnalysisInfoMixin<OptimisticAA>;

  static AnalysisKey Key;

public:
  using Result = OptimisticAAResult;

  OptimisticAAResult run(Function &F, FunctionAnalysisManager &AM);
};

/// Legacy wrapper pass to provide the OptimisticAAResult object.
class OptimisticAAWrapperPass : public FunctionPass {
  std::unique_ptr<OptimisticAAResult> Result;

  virtual void anchor();

public:
  static char ID;

  OptimisticAAWrapperPass();

  OptimisticAAResult &getResult() { return *Result; }
  const OptimisticAAResult &getResult() const { return *Result; }

  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
};

FunctionPass *createOptimisticAAWrapperPass();

} // end namespace llvm

#endif // LLVM_ANALYSIS_OPTIMISTICALIASANALYSIS_H

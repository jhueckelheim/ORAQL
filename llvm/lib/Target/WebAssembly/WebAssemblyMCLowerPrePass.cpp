//===-- WebAssemblyMCLowerPrePass.cpp - Prepare for MC lower --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// Some information in MC lowering / asm printing gets generated as
/// instructions get emitted, but may be necessary at the start, such as for
/// .globaltype declarations. This pass collects this information.
///
//===----------------------------------------------------------------------===//

#include "MCTargetDesc/WebAssemblyMCTargetDesc.h"
#include "Utils/WebAssemblyUtilities.h"
#include "WebAssembly.h"
#include "WebAssemblyMachineFunctionInfo.h"
#include "WebAssemblySubtarget.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineModuleInfoImpls.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;

#define DEBUG_TYPE "wasm-mclower-prepass"

namespace {
class WebAssemblyMCLowerPrePass final : public MachineFunctionPass {
  StringRef getPassName() const override {
    return "WebAssembly MC Lower Pre Pass";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    MachineFunctionPass::getAnalysisUsage(AU);
  }

  bool runOnMachineFunction(MachineFunction &MF) override;

public:
  static char ID; // Pass identification, replacement for typeid
  WebAssemblyMCLowerPrePass() : MachineFunctionPass(ID) {}
};
} // end anonymous namespace

char WebAssemblyMCLowerPrePass::ID = 0;
INITIALIZE_PASS(
    WebAssemblyMCLowerPrePass, DEBUG_TYPE,
    "Collects information ahead of time for MC lowering",
    false, false)

FunctionPass *llvm::createWebAssemblyMCLowerPrePass() {
  return new WebAssemblyMCLowerPrePass();
}

bool WebAssemblyMCLowerPrePass::runOnMachineFunction(MachineFunction &MF) {
  LLVM_DEBUG(dbgs() << "********** MC Lower Pre Pass **********\n"
                       "********** Function: "
                    << MF.getName() << '\n');

  MachineModuleInfo &MMI = MF.getMMI();
  MachineModuleInfoWasm &MMIW = MMI.getObjFileInfo<MachineModuleInfoWasm>();

  for (MachineBasicBlock &MBB : MF) {
    for (auto &MI : MBB) {
      // FIXME: what should all be filtered out beyond these?
      if (MI.isDebugInstr() || MI.isInlineAsm())
        continue;
      for (MachineOperand &MO : MI.uses()) {
        if (MO.isSymbol()) {
          MMIW.MachineSymbolsUsed.insert(MO.getSymbolName());
        }
      }
    }
  }

  return true;
}

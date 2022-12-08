// Usage: opt -load-pass-plugin=libUnitProject.so -passes="unit-sccp"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "UnitSCCP.h"

#define DEBUG_TYPE "UnitSCCP"
// Define any statistics here

using namespace llvm;
using namespace cs426;

STATISTIC(IRemove, "Number of instructions removed");
STATISTIC(Beach, "Number of basic blocks unreachable");
STATISTIC(ISimp, "Number of instructions simplified");

/// Main function for running the SCCP optimization
PreservedAnalyses UnitSCCP::run(Function &F, FunctionAnalysisManager &FAM) {
  dbgs() << "UnitSCCP running on " << F.getName() << "\n";

  // Perform the optimization

  // ? Don’t propagate into operation until its block is executable.
  // ? Ignore phi argument if incoming CFG edge not executable
  // ? If variable changes value, add SSA out-edges to SSAQ
  // ? If CFG edge executable, add to FlowQ

  // TODO: Design choice: block SSAOutEdge by executablity of edge or block
  // ? By edge: revisit block if new executable edge
  // ! By block: only revisit instruction on need; may mark constant as bottom?

  init(F);
  while (!FlowQ.empty() || !SSAQ.empty()) {
    while (!FlowQ.empty()) { // Executable
      auto BB = FlowQ.front();
      FlowQ.pop();
      dbgs() << "\nFlowQ: Take Block from Flow queue:" << getSimpleNodeLabel(BB)
             << "\n";
      visitBlock(BB);
      FlowMark[BB] = true;
    }
    while (!SSAQ.empty()) { // Variable Changes
                            // TODO:inq
      Value *V = SSAQ.front();
      SSAQ.pop();
      InSSAQ[V] = false;
      if (auto I = dyn_cast<Instruction>(V)) {
        dbgs() << "\nSSAQ: Take Instruction from SSA queue:" << *I << "\n";
        visitInstruction(I);
      } else {
        assert(false);
      }
    }
  }
  // Set proper preserved analyses
  for (auto v : LatCell) {
    if (auto I = dyn_cast<Instruction>(v.first)) {
      if (v.second.isConstant()) {
        dbgs() << "Found Const: " << *I << " of value " << v.second.info()
               << "\n";
        BasicBlock::iterator ii(I);
        dbgs() << I << v.second.Val << "\n";
        for (auto _ : I->users())
          ISimp++;
        IRemove++;
        ReplaceInstWithValue(I->getParent()->getInstList(), ii, v.second.Val);
      }
    }
  }
  DenseSet<BasicBlock *> V;
  FlowQ.push(&F.getEntryBlock());
  while (!FlowQ.empty()) { // Executable
    auto BB = FlowQ.front();
    FlowQ.pop();
    V.insert(BB);
    if (FlowMark[BB] == false)
      Beach++;
    for (auto SBB : successors(BB)) {
      if (!V.contains(SBB))
        FlowQ.push(SBB);
    }
  }

  dbgs() << "\n\n";
  return PreservedAnalyses();
}
void UnitSCCP::init(Function &F) {
  LatCell.clear();
  ExecFlag.clear();
  FlowMark.clear();
  FlowQ.push(&F.getEntryBlock());
  for (auto &V : F.args()) {
    LatCell[&V] = bottom;
  }
}
void UnitSCCP::visitBlock(BasicBlock *BB) {
  for (auto &I : *BB)
    visitInstruction(&I);
}
void UnitSCCP::visitBranch(BranchInst *I) {
  vector<int> choice;
  if (I->isUnconditional())
    choice = {0};
  else {
    auto LV = getLattice(I->getCondition());
    if (LV.Status == bottom)
      choice = {0, 1};
    else {
      if (LV.Val->isNullValue())
        choice = {1};
      else
        choice = {0};
    }
  }

  for (auto i : choice) {
    auto SuccBB = I->getSuccessor(i);
    Edge E(I->getParent(), SuccBB);
    if (!FlowMark[SuccBB] || !ExecFlag[E]) {
      dbgs() << "visitBr: Mark edge " << edgeInfo(E) << " executable\n";
      // TODO: inq check?
      FlowQ.push(SuccBB);
    }
    ExecFlag[E] = true;
  }
}
void UnitSCCP::visitInstruction(Instruction *I) {
  if (auto Br = dyn_cast<BranchInst>(I)) {
    visitBranch(Br);
    return;
  }

  auto &LV = LatCell[I];
  if (LV.isBottom())
    return;
  LatticeElem ret;
  if (I->isBinaryOp())
    ret = evalBinaryOp(dyn_cast<BinaryOperator>(I));
  else if (I->isUnaryOp())
    ret = evalUnaryOp(dyn_cast<UnaryOperator>(I));
  else if (I->isCast())
    ret = evalCast(dyn_cast<CastInst>(I));
  else {
    switch (I->getOpcode()) {
    case Instruction::ICmp:
    case Instruction::FCmp:
      ret = evalCmp(dyn_cast<CmpInst>(I));
      break;
    case Instruction::Select:
      ret = evalSelect(dyn_cast<SelectInst>(I));
      break;
    case Instruction::GetElementPtr:
      ret = evalGetElementPtr(dyn_cast<GetElementPtrInst>(I));
      break;
    case Instruction::PHI:
      ret = evalPhi(dyn_cast<PHINode>(I));
      break;
    // case Instruction::Ret:
    //   ret = evalRet(dyn_cast<ReturnInst>(I));
    //   break;
    default:
      ret = evalUnsupported(I);
    }
  }
  dbgs() << "visitInstr: Evaluate" << *I << " of value " << LV.info()
         << " with " << ret.info() << "\n";
  if (LV.meet(ret)) {
    dbgs() << "visitInstr: Changing to " << LV.info() << "\n";
    addSSAOutEdges(I);
  }
}
LatticeElem UnitSCCP::evalBinaryOp(BinaryOperator *I) {
  auto LV1 = getLattice(I->getOperand(0)), LV2 = getLattice(I->getOperand(1));
  assert(!LV1.isTop() && !LV2.isTop());
  if (LV1.isBottom() || LV2.isBottom()) {
    return bottom;
  } else {
    return ConstantExpr::get(I->getOpcode(), LV1.Val, LV2.Val);
  }
}
LatticeElem UnitSCCP::evalUnaryOp(UnaryOperator *I) {
  auto LV1 = getLattice(I->getOperand(0));
  if (LV1.isBottom()) {
    return bottom;
  } else {
    return ConstantExpr::get(I->getOpcode(), LV1.Val);
  }
}
LatticeElem UnitSCCP::evalCast(CastInst *I) {
  auto LV1 = getLattice(I->getOperand(0));
  if (LV1.isBottom()) {
    return bottom;
  } else {
    return ConstantExpr::getCast(I->getOpcode(), LV1.Val, I->getType());
  }
}
LatticeElem UnitSCCP::evalCmp(CmpInst *I) {
  auto LV1 = getLattice(I->getOperand(0)), LV2 = getLattice(I->getOperand(1));
  assert(!LV1.isTop() && !LV2.isTop());
  // dbgs() << "CMP: Meeting" << LV1.info() << LV2.info() << "\n";
  if (LV1.isBottom() || LV2.isBottom()) {
    return bottom;
  } else {
    return ConstantExpr::getCompare(I->getPredicate(), LV1.Val, LV2.Val);
  }
}
LatticeElem UnitSCCP::evalSelect(SelectInst *I) {
  auto LVC = getLattice(I->getCondition());
  auto LV1 = getLattice(I->getTrueValue()),
       LV2 = getLattice(I->getFalseValue());
  if (LVC.isBottom())
    return LV1 ^ LV2;
  else {
    if (LVC.Val->isNullValue())
      return LV2;
    if (LVC.Val->isAllOnesValue())
      return LV1;
    assert(false);
  }
}
LatticeElem UnitSCCP::evalGetElementPtr(GetElementPtrInst *I) {
  auto Ptr = getLattice(I->getPointerOperand());
  if (Ptr.isBottom())
    return bottom;
  else {
    vector<Constant *> Idx;
    for (auto &U : I->indices()) {
      auto V = U.get();
      auto LV = getLattice(V);
      if (LV.isBottom()) {
        return bottom;
      }
      Idx.push_back(LV.Val);
    }
    auto AR = makeArrayRef(Idx);
    return ConstantExpr::getGetElementPtr(I->getSourceElementType(), Ptr.Val,
                                          AR);
  }
}
LatticeElem UnitSCCP::evalPhi(PHINode *I) {
  LatticeElem ret;
  for (uint i = 0, n = I->getNumOperands(); i < n; i++) {
    auto V = I->getIncomingValue(i);
    auto PredBB = I->getIncomingBlock(i);
    Edge E(PredBB, I->getParent());
    if (ExecFlag[E]) {
      dbgs() << "PHI: Meeting" << getLattice(V).info() << "\n";
      ret.meet(getLattice(V));
    }
  }
  dbgs() << "PHI: Eval to " << ret.info() << "\n";
  return ret;
}
void UnitSCCP::addSSAOutEdges(Instruction *I) {
  for (auto U : I->users()) {
    if (auto J = dyn_cast<Instruction>(U)) {
      Edge E(I->getParent(), J->getParent());
      if (FlowMark[J->getParent()]) {
        dbgs() << "SSAOut: Push" << *J << " in SSA Queue, due to" << *I << "\n";
        if (!InSSAQ[J]) {
          InSSAQ[J] = true;
          SSAQ.push(J);
        }
      } else {
        dbgs() << "SSAOut: Not push" << *J << " in SSA Queue, due to "
               << edgeInfo(E) << "'s sink not currently executable\n";
      }
    }
  }
}
string LatticeElem::getStatus(const LatticeStatus L) {
  switch (L) {
  case constant:
    return "Constant";
  case top:
    return "Top (may be constant)";
  case bottom:
    return "Bottom (cannot be constant)";
  }
  return "?";
}
string LatticeElem::info() {
  string str;
  raw_string_ostream os(str);
  os << getStatus(Status);
  if (isConstant()) {
    os << " (" << *Val << ")";
  }
  return str;
}
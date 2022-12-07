#ifndef INCLUDE_UNIT_SCCP_H
#define INCLUDE_UNIT_SCCP_H
#include "UnitLoopInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <unordered_map>
#include <utility>

using namespace llvm;
using std::map;
using std::pair;
using std::queue;
using std::set;
using std::stringstream;
using std::vector;

namespace cs426 {
/// Sparse Conditional Constant Propagation Optimization Pass

enum LatticeStatus {
  top, // may be constant
  constant,
  bottom // cannot be constant
};

struct LatticeElem {
  LatticeStatus Status;
  Constant *Val;
  LatticeElem() : Status(top), Val(nullptr) {}
  LatticeElem(Constant *Val) : Status(constant), Val(Val) { assert(Val); }
  LatticeElem(LatticeStatus Status) : Status(Status), Val(nullptr) {}
  bool isTop() const { return Status == top; }
  bool isConstant() const { return Status == constant; }
  bool isBottom() const { return Status == bottom; }
  LatticeElem operator^(const LatticeElem &R) {
    assert(Status != top || R.Status != top);
    if (Status == bottom || R.Status == bottom)
      return bottom;
    if (Status == top)
      return R;
    if (R.Status == top)
      return *this;
    if (Val->isElementWiseEqual(R.Val))
      return R;
    return bottom;
  }
  bool markBottom() {
    if (isBottom())
      return false;
    Status = bottom;
    Val = nullptr;
    return true;
  }
  bool meet(const LatticeElem &R) {
    assert(Status != top || R.Status != top);
    if (Status == bottom || R.Status == bottom)
      return markBottom();

    if (Status == top) {
      *this = R;
      return true;
    }
    if (R.Status == top)
      return false;

    if (Val->isElementWiseEqual(R.Val))
      return false;
    return markBottom();
  }
  string getStatus(const LatticeStatus L);
  string info();
};

struct UnitSCCP : PassInfoMixin<UnitSCCP> {
  // DataLayout *DL;
  using Edge = pair<BasicBlock *, BasicBlock *>;
  queue<BasicBlock *> FlowQ;
  queue<Value *> SSAQ;
  map<Edge, bool> ExecFlag;
  map<BasicBlock *, bool> FlowMark;
  map<Value *, LatticeElem> LatCell;
  map<Value *, bool> InSSAQ;
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
  void init(Function &F);
  void visitBranch(BranchInst *I);
  LatticeElem evalBinaryOp(BinaryOperator *I);
  LatticeElem evalUnaryOp(UnaryOperator *I);
  LatticeElem evalCast(CastInst *I);
  LatticeElem evalCmp(CmpInst *I);
  LatticeElem evalSelect(SelectInst *I);
  LatticeElem evalGetElementPtr(GetElementPtrInst *I);
  LatticeElem evalPhi(PHINode *I);
  LatticeElem evalUnsupported(Instruction *I) { return bottom; }
  LatticeElem evalRet(ReturnInst *I) { return getLattice(I->getOperand(0)); }
  void visitInstruction(Instruction *I);
  void visitBlock(BasicBlock *BB);
  void addSSAOutEdges(Instruction *I);
  LatticeElem getLattice(Value *V) {
    if (auto C = dyn_cast<Constant>(V)) {
      return LatticeElem(C);
    }
    assert(LatCell.count(V));
    return LatCell[V];
  }
  string edgeInfo(Edge E) {
    return "(" + getSimpleNodeLabel(E.first) + "," +
           getSimpleNodeLabel(E.second) + ")";
  }
};
} // namespace cs426

#endif // INCLUDE_UNIT_SCCP_H

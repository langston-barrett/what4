// Vendored from sasi/lib/RangeAnalysis/StridedWrappedRange.cpp
// SASI-PRECISION: removed all LLVM IR-typed dispatch (visit*, filterSigma,
// widening, print, isMoreOrEqualPrecise's WrappedRange cast, the
// StridedWrappedBitwiseShitfs that calls back into transfer functions
// generically), and all DEBUG/dbgs output. The transfer-function math is
// unchanged.

#include "BaseRange.h"
#include "StridedWrappedRange.h"
#include "llvm_stubs.h"

#include <algorithm>
#include <iostream>
#include <iterator>
#include <vector>

using namespace llvm;
using namespace unimelb;

#define EVAL
#define SMART_JOIN

STATISTIC(NumOfOverflows, "Number of overflows");
STATISTIC(NumOfJoins,     "Number of joins");
STATISTIC(NumOfJoinTies,  "Number of join ties");

bool StridedWrappedRange::isBot() const { return __isBottom; }
bool StridedWrappedRange::IsTop() const { return BaseRange::IsTop(); }

void StridedWrappedRange::makeBot() {
  __isBottom = true;
  __isTop    = false;
}

void StridedWrappedRange::makeTop() {
  BaseRange::makeTop();
  this->stride_val = 1;
  __isBottom = false;
}

bool StridedWrappedRange::isIdentical(AbstractValue *V) {
  StridedWrappedRange *S = this;
  StridedWrappedRange *T = cast<StridedWrappedRange>(V);
  return BaseRange::isIdentical(V) && S->stride_val == T->stride_val;
}

bool StridedWrappedRange::isEqual(AbstractValue *V) {
  StridedWrappedRange *S = this;
  StridedWrappedRange *T = cast<StridedWrappedRange>(V);
  return S->lessOrEqual(T) && T->lessOrEqual(S) && S->getStride() == T->getStride();
}

bool StridedWrappedRange::WrappedMember(const APInt &e) const {
  if (isBot()) return false;
  if (IsTop()) return true;

  if (isSingleVal()) {
    assert(getStride() == 0);
    return getLB() == e;
  } else {
    assert(getStride() != 0);
    bool to_ret = false;
    APInt x = getLB();
    APInt y = getUB();

    unsigned long bw = (e.getBitWidth() > x.getBitWidth() ? e.getBitWidth() : x.getBitWidth());
    bw = (bw < y.getBitWidth() ? y.getBitWidth() : bw);

    APInt et((unsigned)bw, e.getZExtValue());
    APInt xt((unsigned)bw, x.getZExtValue());
    APInt yt((unsigned)bw, y.getZExtValue());

    to_ret = SILex_LessOrEqual(et - xt, yt - xt);
    if (to_ret) {
      uint64_t diff_norm = (et - xt).getZExtValue();
      return (diff_norm % getStride()) == 0;
    }
    return to_ret;
  }
}

bool StridedWrappedRange::WrappedlessOrEqual(AbstractValue *V) {
  StridedWrappedRange *S = this;
  StridedWrappedRange *T = cast<StridedWrappedRange>(V);

  if (S->isBot()) return true;
  if (S->IsTop() && T->IsTop()) return true;
  if (S->IsTop()) return false;
  if (T->IsTop()) return true;

  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();
  (void)d;

  if (S->isSingleVal()) return T->WrappedMember(a);
  if (T->isSingleVal()) return false;

  if (T->WrappedMember(a) && T->WrappedMember(b)) {
    if (a == c && b == d && (S->getStride() % T->getStride() == 0)) return true;
    if (!(S->WrappedMember(c)) || !(S->WrappedMember(d))) {
      assert(S->getStride() != 0 && T->getStride() != 0);
      APInt a_u(a.getBitWidth(), a.getZExtValue());
      APInt c_u(c.getBitWidth(), c.getZExtValue());
      return ((((a_u - c_u).getZExtValue() % S->getStride()) == 0)
              && (S->getStride() % T->getStride() == 0));
    }
  }
  return false;
}

bool StridedWrappedRange::lessOrEqual(AbstractValue *V) { return WrappedlessOrEqual(V); }

void StridedWrappedRange::print(raw_ostream &Out) const { BaseRange::print(Out); }

void StridedWrappedRange::join(AbstractValue *V) {
  StridedWrappedRange *R = cast<StridedWrappedRange>(V);
  if (R->isBot()) return;
  if (isBot()) { WrappedRangeAssign(R); return; }

  WrappedJoin(R);
  normalizeTop();
}

void StridedWrappedRange::WrappedJoin(AbstractValue *V) {
  StridedWrappedRange *S = this;
  StridedWrappedRange *T = cast<StridedWrappedRange>(V);

  APInt a = S->getLB();
  APInt b = S->getUB();
  APInt c = T->getLB();
  APInt d = T->getUB();

  NumOfJoins++;

  if (S->isBot()) { WrappedRangeAssign(T); return; }
  if (T->isBot()) return;

  if (S->isSingleVal() && T->isSingleVal()) {
#ifdef SMART_JOIN
    APInt u, l;
    uint64_t si1_card = WCard_mod(a, d);
    uint64_t si2_card = WCard_mod(c, b);
    if (si1_card <= si2_card) { l = a; u = d; }
    else                      { l = c; u = b; }
#else
    APInt u = d, l = a;
#endif
    unsigned long new_stride = (unsigned long)(u - l).getZExtValue();
    setUB(u); setLB(l); setStride(new_stride);
    return;
  }

  StridedWrappedRange S_stride1(*S); S_stride1.AdjustStride();
  StridedWrappedRange T_stride1(*T); T_stride1.AdjustStride();

  if (S->WrappedlessOrEqual(T)) {
    unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
    if (!S->isSingleVal()) new_stride = T->getStride();
    new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)((a - c).getZExtValue()));
    setLB(c); setUB(d); setStride(new_stride);
  } else if (T->WrappedlessOrEqual(S)) {
    unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
    if (!T->isSingleVal()) new_stride = S->getStride();
    new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)((c - a).getZExtValue()));
    setStride(new_stride);
  } else if (T_stride1.WrappedMember(a) && T_stride1.WrappedMember(b) &&
             S_stride1.WrappedMember(c) && S_stride1.WrappedMember(d)) {
    makeTop();
  } else if (S_stride1.WrappedMember(c)) {
    setLB(a); setUB(d);
    unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
    new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)((c - a).getZExtValue()));
    setStride(new_stride);
  } else if (T_stride1.WrappedMember(a)) {
    setLB(c); setUB(b);
    unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
    new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)((a - c).getZExtValue()));
    setStride(new_stride);
  } else {
#ifdef SMART_JOIN
    unsigned long new_stride, new_stride1, new_stride2;
    if (S->isSingleVal())      new_stride = T->getStride();
    else if (T->isSingleVal()) new_stride = S->getStride();
    else new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());

    uint64_t card_c_a = WCard_mod(c, a);
    uint64_t card_a_c = WCard_mod(a, c);

    new_stride1 = UtilFunctions::getGCD(new_stride, (unsigned long)(card_c_a - (uint64_t)1));
    new_stride2 = UtilFunctions::getGCD(new_stride, (unsigned long)(card_a_c - (uint64_t)1));

    StridedWrappedRange si1(*S); si1.setLB(c); si1.setStride(new_stride1);
    StridedWrappedRange si2(*S); si2.setUB(d); si2.setStride(new_stride2);
    uint64_t si1_card = WCard_mod(si1.getLB(), si1.getUB());
    uint64_t si2_card = WCard_mod(si2.getLB(), si2.getUB());
    uint64_t n_val1 = si1_card / ((uint64_t)new_stride1 ? (uint64_t)new_stride1 : 1);
    uint64_t n_val2 = si2_card / ((uint64_t)new_stride2 ? (uint64_t)new_stride2 : 1);
    if (n_val1 <= n_val2) WrappedRangeAssign(&si1);
    else                  WrappedRangeAssign(&si2);
#else
    unsigned long new_stride;
    if (S->isSingleVal())
      new_stride = UtilFunctions::getGCD(T->getStride(), (unsigned long)((c - a).getZExtValue()));
    else if (T->isSingleVal())
      new_stride = UtilFunctions::getGCD(S->getStride(), (unsigned long)((c - a).getZExtValue()));
    else {
      new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());
      uint64_t card_mod = WCard_mod(a, c);
      new_stride = UtilFunctions::getGCD(new_stride, (unsigned long)(card_mod - (uint64_t)1));
    }
    StridedWrappedRange Res(*S);
    Res.setUB(T->getUB());
    Res.setStride(new_stride);
    WrappedRangeAssign(&Res);
#endif
  }

  normalizeTop();
  if (!S->isBot() || !T->isBot()) resetBottomFlag();
}

bool SortWrappedRanges_Compare(StridedWrappedRange *R1, StridedWrappedRange *R2) {
  return SILex_LessOrEqual(R1->getLB(), R2->getLB());
}

void SortWrappedRanges(std::vector<StridedWrappedRange *> &Rs) {
  std::sort(Rs.begin(), Rs.end(), SortWrappedRanges_Compare);
}

StridedWrappedRange Extend(const StridedWrappedRange &R1, const StridedWrappedRange &R2) {
  StridedWrappedRange Res(R1);
  StridedWrappedRange tmp(R2);
  Res.join(&tmp);
  return Res;
}

StridedWrappedRange Bigger(const StridedWrappedRange &R1, const StridedWrappedRange &R2) {
  if (R1.isBot() && !R2.isBot()) return StridedWrappedRange(R2);
  if (R2.isBot() && !R1.isBot()) return StridedWrappedRange(R1);
  if (R2.isBot() && R1.isBot()) return StridedWrappedRange(R1);

  APInt a = R1.getLB(); APInt b = R1.getUB();
  APInt c = R2.getLB(); APInt d = R2.getUB();
  if (SILex_LessOrEqual(StridedWrappedRange::WCard(c, d), StridedWrappedRange::WCard(a, b)))
    return StridedWrappedRange(R1);
  return StridedWrappedRange(R2);
}

StridedWrappedRange ClockWiseGap(const StridedWrappedRange &R1, const StridedWrappedRange &R2) {
  APInt a = R1.getLB(); APInt b = R1.getUB();
  APInt c = R2.getLB(); APInt d = R2.getUB();
  (void)a; (void)d;

  StridedWrappedRange gap(b + 1, c - 1, b.getBitWidth());
  if (R1.isBot() || R2.isBot() || R2.WrappedMember(b) || R1.WrappedMember(c))
    gap.makeBot();
  return gap;
}

StridedWrappedRange WrappedComplement(const StridedWrappedRange &R) {
  StridedWrappedRange C(R);
  if (R.isBot()) { C.makeTop(); return C; }
  if (R.IsTop()) { C.makeBot(); return C; }

  APInt x = C.getLB();
  APInt y = C.getUB();
  C.setLB(y + 1);
  C.setUB(x - 1);
  unsigned long new_dist = (unsigned long)StridedWrappedRange::WCard_mod(C.getLB(), C.getUB());
  new_dist--;
  unsigned long new_stride;
  if (new_dist == 0) new_stride = 0;
  else if (R.getStride() == 0) new_stride = 1;
  else new_stride = UtilFunctions::getGCD(R.getStride(), new_dist);
  C.setStride(new_stride);
  return C;
}

inline bool CrossSouthPole(const APInt &x, const APInt &y) { return y.ult(x); }
inline bool CrossNorthPole(const APInt &x, const APInt &y) { return y.slt(x); }

inline StridedWrappedRange *convertAbsValToWrapped(AbstractValue *V) {
  return cast<StridedWrappedRange>(V);
}

inline AbstractValue *convertPtrValToAbs(StridedWrappedRangePtr V) {
  return cast<AbstractValue>(V.get());
}

void StridedWrappedRange::GeneralizedJoin(std::vector<AbstractValue *> Values) {
  if (Values.size() < 2) return;
  std::vector<StridedWrappedRange *> Rs;
  std::transform(Values.begin(), Values.end(), std::back_inserter(Rs),
                 convertAbsValToWrapped);
  SortWrappedRanges(Rs);

  StridedWrappedRange f(*this); f.makeBot();
  for (auto I = Rs.begin(), E = Rs.end(); I != E; ++I) {
    StridedWrappedRange R(*(*I));
    if (R.IsTop() || CrossSouthPole(R.getLB(), R.getUB())) f = Extend(f, R);
  }

  StridedWrappedRange g(*this); g.makeBot();
  for (auto I = Rs.begin(), E = Rs.end(); I != E; ++I) {
    StridedWrappedRange R(*(*I));
    StridedWrappedRange tmp = ClockWiseGap(f, R);
    g = Bigger(g, tmp);
    f = Extend(f, R);
  }

  StridedWrappedRange Tmp = WrappedComplement(Bigger(g, WrappedComplement(f)));
  this->setLB(Tmp.getLB());
  this->setUB(Tmp.getUB());
}

StridedWrappedRange rotatingGenJoin(std::vector<StridedWrappedRange *> vals, long curr_ind) {
  unsigned long count = 0;
  StridedWrappedRange curr_val(*vals.front());
  curr_val.makeBot();
  while (count < vals.size()) {
    curr_val.WrappedJoin(vals[curr_ind]);
    curr_ind = (curr_ind + 1) % vals.size();
    count++;
  }
  return curr_val;
}

bool StridedWrappedRange::StridedGeneralizedJoin(std::vector<AbstractValue *> Values,
                                                 StridedWrappedRange *result) {
  if (Values.size() < 1) return false;

  if (Values.size() == 1) {
    StridedWrappedRange *R1 = cast<StridedWrappedRange>(Values.front());
    *result = *R1;
    return true;
  }
  if (Values.size() == 2) {
    StridedWrappedRange *R1 = cast<StridedWrappedRange>(Values.front());
    StridedWrappedRange temp(*R1);
    temp.WrappedJoin(Values.back());
    *result = temp;
    return true;
  }

  std::vector<StridedWrappedRange *> Rs;
  std::transform(Values.begin(), Values.end(), std::back_inserter(Rs),
                 convertAbsValToWrapped);
  SortWrappedRanges(Rs);

  StridedWrappedRange f(*(Rs.front())); f.makeBot();

  for (unsigned long i = 0; i < Rs.size(); i++) {
    StridedWrappedRange R = rotatingGenJoin(Rs, i);
    if (i == 0) f = R;
    uint64_t r_vals, f_vals;
    if (R.isSingleVal()) r_vals = 1;
    else r_vals = (WCard_mod(R.getLB(), R.getUB())
                   / (R.getStride() ? (uint64_t)R.getStride() : 1)) + (uint64_t)1;
    if (f.isSingleVal()) f_vals = 1;
    else f_vals = (WCard_mod(f.getLB(), f.getUB())
                   / (f.getStride() ? (uint64_t)f.getStride() : 1)) + (uint64_t)1;
    if (r_vals < f_vals) f = R;
  }

  *result = f;
  return true;
}

void StridedWrappedRange::meet(AbstractValue *V1, AbstractValue *V2) {
  StridedWrappedRange *R1 = cast<StridedWrappedRange>(V1);
  StridedWrappedRange *R2 = cast<StridedWrappedRange>(V2);
  this->makeBot();
  StridedWrappedRange tmp = StridedWrappedMeet(R1, R2);
  this->WrappedJoin(&tmp);
}

std::vector<StridedWrappedRangePtr>
StridedWrappedRange::MultiValueIntersection(StridedWrappedRange *Op1, StridedWrappedRange *Op2) {
  std::vector<StridedWrappedRangePtr> res;
  if (Op1->isBot() || Op2->isBot()) {
    StridedWrappedRange toRet(*Op1); toRet.makeBot();
    res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    return res;
  }
  if (Op1->isSingleVal() && Op2->isSingleVal()) {
    if (Op1->getLB() == Op2->getLB()) {
      APInt lb = Op1->getLB();
      StridedWrappedRange toRet(*Op1);
      toRet.setLB(lb); toRet.setUB(lb); toRet.setStride(0);
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
      return res;
    }
    StridedWrappedRange toRet(*Op1); toRet.makeBot();
    res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    return res;
  }

  if (Op1->isSingleVal()) {
    APInt lb = Op1->getLB();
    if (Op2->getStride() != 0
        && (((Op2->getLB() - lb).getZExtValue() % Op2->getStride()) == 0)
        && Op2->WrappedMember(lb)) {
      StridedWrappedRange toRet(*Op1);
      toRet.setLB(lb); toRet.setUB(lb); toRet.setStride(0);
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
      return res;
    }
    StridedWrappedRange toRet(*Op1); toRet.makeBot();
    res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    return res;
  }
  if (Op2->isSingleVal()) {
    APInt lb = Op2->getLB();
    if (Op1->getStride() != 0
        && (((Op1->getLB() - lb).getZExtValue() % Op1->getStride()) == 0)
        && Op1->WrappedMember(lb)) {
      StridedWrappedRange toRet(*Op2);
      toRet.setLB(lb); toRet.setUB(lb); toRet.setStride(0);
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
      return res;
    }
    StridedWrappedRange toRet(*Op1); toRet.makeBot();
    res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    return res;
  }
  unsigned long new_stride = UtilFunctions::getLCM(Op1->getStride(), Op2->getStride());
  APInt lb1 = Op1->getLB(); APInt ub1 = Op1->getUB();
  APInt lb2 = Op2->getLB(); APInt ub2 = Op2->getUB();
  if (Op1->WrappedlessOrEqual(Op2)) {
    APInt result;
    if (!StridedWrappedRange::minimal_common_integer(Op1, Op2, &result)) {
      StridedWrappedRange toRet(*Op1); toRet.makeBot();
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
      return res;
    }
    unsigned long long_val =
      (unsigned long)((((ub1 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
    APInt newub(ub1.getBitWidth(), long_val);
    StridedWrappedRange toRet(*Op1);
    toRet.setLB(result); toRet.setUB(newub); toRet.setStride(new_stride);
    res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    return res;
  } else if (Op2->WrappedlessOrEqual(Op1)) {
    APInt result;
    if (!StridedWrappedRange::minimal_common_integer(Op1, Op2, &result)) {
      StridedWrappedRange toRet(*Op1); toRet.makeBot();
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
      return res;
    }
    unsigned long long_val =
      (unsigned long)((((ub2 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
    APInt newub(ub2.getBitWidth(), long_val);
    StridedWrappedRange toRet(*Op1);
    toRet.setLB(result); toRet.setUB(newub); toRet.setStride(new_stride);
    res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    return res;
  } else if (Op1->WrappedMember(lb2) && Op1->WrappedMember(ub2)
             && Op2->WrappedMember(lb1) && Op2->WrappedMember(ub1)) {
    APInt result;
    StridedWrappedRange s0(*Op1); s0.setUB(ub2);
    StridedWrappedRange s1(*Op1); s1.setUB(ub1);

    if (!StridedWrappedRange::minimal_common_integer(&s0, Op2, &result)) {
      StridedWrappedRange toRet(*Op1); toRet.makeBot();
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    } else {
      unsigned long long_val =
        (unsigned long)((((ub2 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
      APInt newub(ub2.getBitWidth(), long_val);
      StridedWrappedRange toRet(*Op1);
      toRet.setLB(result); toRet.setUB(newub); toRet.setStride(new_stride);
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    }
    if (!StridedWrappedRange::minimal_common_integer(&s1, Op1, &result)) {
      StridedWrappedRange toRet(*Op1); toRet.makeBot();
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    } else {
      unsigned long long_val =
        (unsigned long)((((ub1 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
      APInt newub(ub1.getBitWidth(), long_val);
      StridedWrappedRange toRet(*Op1);
      toRet.setLB(result); toRet.setUB(newub); toRet.setStride(new_stride);
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    }
    return res;
  } else if (Op1->WrappedMember(lb2)) {
    APInt result;
    if (!StridedWrappedRange::minimal_common_integer(Op2, Op1, &result)) {
      StridedWrappedRange toRet(*Op1); toRet.makeBot();
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
      return res;
    }
    unsigned long long_val =
      (unsigned long)((((ub1 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
    APInt newub(ub1.getBitWidth(), long_val);
    StridedWrappedRange toRet(*Op1);
    toRet.setLB(result); toRet.setUB(newub); toRet.setStride(new_stride);
    res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    return res;
  } else if (Op2->WrappedMember(lb1)) {
    APInt result;
    if (!StridedWrappedRange::minimal_common_integer(Op1, Op2, &result)) {
      StridedWrappedRange toRet(*Op1); toRet.makeBot();
      res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
      return res;
    }
    unsigned long long_val =
      (unsigned long)((((ub2 - result).getZExtValue() / new_stride) * new_stride) + result.getZExtValue());
    APInt newub(ub2.getBitWidth(), long_val);
    StridedWrappedRange toRet(*Op1);
    toRet.setLB(result); toRet.setUB(newub); toRet.setStride(new_stride);
    res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
    return res;
  }
  StridedWrappedRange toRet(*Op1); toRet.makeBot();
  res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(toRet)));
  return res;
}

StridedWrappedRange unimelb::StridedWrappedMeet(StridedWrappedRange *S, StridedWrappedRange *T) {
  APInt a = S->getLB(); APInt b = S->getUB();
  APInt c = T->getLB(); APInt d = T->getUB();

  APInt lb, ub;
  unsigned int width = a.getBitWidth();
  unsigned long new_stride = UtilFunctions::getGCD(S->getStride(), T->getStride());

  if (S->WrappedlessOrEqual(T))      { lb = S->getLB(); ub = S->getUB(); }
  else if (T->WrappedlessOrEqual(S)) { lb = T->getLB(); ub = T->getUB(); }
  else if (T->WrappedMember(a) && T->WrappedMember(b) &&
           S->WrappedMember(c) && S->WrappedMember(d)) {
    if (SILex_LessThan(StridedWrappedRange::WCard(a, b), StridedWrappedRange::WCard(c, d))
        || (StridedWrappedRange::WCard(a, b) == StridedWrappedRange::WCard(c, d) && SILex_LessOrEqual(a, c))) {
      lb = S->getLB(); ub = S->getUB();
    } else { lb = T->getLB(); ub = T->getUB(); }
  } else if (S->WrappedMember(c)) { lb = c; ub = b; }
  else if (T->WrappedMember(a))   { lb = a; ub = d; }
  else {
    StridedWrappedRange Meet(a, b, width);
    Meet.makeBot();
    return Meet;
  }
  StridedWrappedRange Meet(lb, ub, width, new_stride);
  Meet.normalizeTop();
  return Meet;
}

bool IsWrappedOverflow_AddSubSI(const APInt &a, const APInt &b, const APInt &c, const APInt &d) {
  unsigned width = a.getBitWidth();
  APInt tmp1 = StridedWrappedRange::WCard(a, b);
  APInt tmp2 = StridedWrappedRange::WCard(c, d);
  uint64_t n1 = tmp1.getZExtValue();
  uint64_t n2 = tmp2.getZExtValue();
  uint64_t Max = (APInt::getMaxValue(width)).getZExtValue() + 1;
  return (n1 + n2) > Max;
}

std::vector<StridedWrappedRangePtr>
StridedWrappedRange::nsplit(const APInt &x, const APInt &y, unsigned width) {
  APInt NP_lb = APInt::getSignedMaxValue(width);
  APInt NP_ub = APInt::getSignedMinValue(width);
  StridedWrappedRange NP(NP_lb, NP_ub, width);
  StridedWrappedRangePtr s(new StridedWrappedRange(x, y, width));
  std::vector<StridedWrappedRangePtr> res;
  if (!(NP.WrappedlessOrEqual(s.get()))) { res.push_back(s); return res; }
  res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(x, NP_lb, width)));
  res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(NP_ub, y, width)));
  return res;
}

std::vector<StridedWrappedRangePtr>
StridedWrappedRange::strided_nsplit(const APInt &x, const APInt &y, unsigned width, unsigned long orig_stride) {
  APInt NP_lb = APInt::getSignedMaxValue(width);
  APInt NP_ub = APInt::getSignedMinValue(width);
  StridedWrappedRange NP(NP_lb, NP_ub, width);
  StridedWrappedRangePtr s(new StridedWrappedRange(x, y, width, orig_stride));

  bool stradling = false;
  if (!SILex_LessThan(y, NP_ub)) {
    if (SILex_LessThan(y, x))            stradling = true;
    else if (SILex_LessOrEqual(x, NP_lb)) stradling = true;
  } else {
    if (SILex_LessThan(y, x) && SILex_LessOrEqual(x, NP_lb)) stradling = true;
  }

  std::vector<StridedWrappedRangePtr> res;
  if (!stradling) { res.push_back(s); return res; }

  unsigned long step = orig_stride ? orig_stride : 1;
  StridedWrappedRange *s1_obj = new StridedWrappedRange(x, NP_lb, width, orig_stride);
  APInt new_ub = NP_lb - ((NP_lb - x).getZExtValue() % step);
  s1_obj->setUB(new_ub);
  s1_obj->setStride(orig_stride);
  s1_obj->normalizeTop();
  StridedWrappedRangePtr s1(s1_obj);

  s1_obj = new StridedWrappedRange(NP_ub, y, width, orig_stride);
  s1_obj->setStride(orig_stride);
  APInt new_lb = new_ub + step;
  s1_obj->setLB(new_lb);
  s1_obj->normalizeTop();
  StridedWrappedRangePtr s2(s1_obj);

  res.push_back(s1);
  res.push_back(s2);
  return res;
}

std::vector<StridedWrappedRangePtr>
StridedWrappedRange::ssplit(const APInt &x, const APInt &y, unsigned width) {
  APInt SP_lb = APInt::getMaxValue(width);
  APInt SP_ub(width, 0, false);
  StridedWrappedRange SP(SP_lb, SP_ub, width);
  StridedWrappedRangePtr s(new StridedWrappedRange(x, y, width));

  std::vector<StridedWrappedRangePtr> res;
  if (SILex_LessOrEqual(x, y)) { res.push_back(s); return res; }
  res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(x, SP_lb, width)));
  res.push_back(StridedWrappedRangePtr(new StridedWrappedRange(SP_ub, y, width)));
  return res;
}

std::vector<StridedWrappedRangePtr>
StridedWrappedRange::strided_ssplit(const APInt &x, const APInt &y, unsigned width, unsigned long orig_stride) {
  APInt SP_lb = APInt::getMaxValue(width);
  APInt SP_ub(width, 0, false);
  StridedWrappedRange SP(SP_lb, SP_ub, width, 1);
  StridedWrappedRangePtr s(new StridedWrappedRange(x, y, width, orig_stride));

  std::vector<StridedWrappedRangePtr> res;
  if (y.getZExtValue() >= x.getZExtValue()) { res.push_back(s); return res; }

  unsigned long step = orig_stride ? orig_stride : 1;
  StridedWrappedRange *s1_obj = new StridedWrappedRange(x, SP_lb, width, orig_stride);
  APInt new_ub = SP_lb - ((SP_lb - x).getZExtValue() % step);
  s1_obj->setUB(new_ub);
  s1_obj->setStride(orig_stride);
  if (orig_stride == 0 && s1_obj->getLB() != s1_obj->getUB()) s1_obj->setStride(1);
  s1_obj->normalizeTop();
  StridedWrappedRangePtr s1(s1_obj);

  s1_obj = new StridedWrappedRange(SP_ub, y, width, orig_stride);
  APInt new_lb = new_ub + step;
  s1_obj->setLB(new_lb);
  s1_obj->setStride(orig_stride);
  if (orig_stride == 0 && s1_obj->getLB() != s1_obj->getUB()) s1_obj->setStride(1);
  s1_obj->normalizeTop();
  StridedWrappedRangePtr s2(s1_obj);

  res.push_back(s1);
  res.push_back(s2);
  return res;
}

static std::vector<StridedWrappedRangePtr>
psplitsi(const APInt &x, const APInt &y, unsigned width) {
  std::vector<StridedWrappedRangePtr> res;
  std::vector<StridedWrappedRangePtr> s1 = StridedWrappedRange::nsplit(x, y, width);
  for (auto &p : s1) {
    StridedWrappedRange *r = p.get();
    auto s2 = StridedWrappedRange::ssplit(r->getLB(), r->getUB(), r->getLB().getBitWidth());
    res.insert(res.end(), s2.begin(), s2.end());
  }
  return res;
}

static std::vector<StridedWrappedRangePtr>
strided_psplitsi(const APInt &x, const APInt &y, unsigned width, unsigned long orig_stride) {
  std::vector<StridedWrappedRangePtr> res;
  auto s1 = StridedWrappedRange::strided_nsplit(x, y, width, orig_stride);
  for (auto &p : s1) {
    StridedWrappedRange *r = p.get();
    auto s2 = StridedWrappedRange::strided_ssplit(r->getLB(), r->getUB(),
                                                  r->getLB().getBitWidth(),
                                                  r->getStride());
    res.insert(res.end(), s2.begin(), s2.end());
  }
  return res;
}

static std::vector<StridedWrappedRangePtr> purgeZero(StridedWrappedRangePtr RPtr) {
  std::vector<StridedWrappedRangePtr> purgedZeroIntervals;
  StridedWrappedRange *R = RPtr.get();
  unsigned width = R->getLB().getBitWidth();
  APInt Zero_lb(width, 0, false);
  APInt Zero_ub(width, 0, false);
  StridedWrappedRange Zero(Zero_lb, Zero_ub, width, 0);

  if (Zero.lessOrEqual(R)) {
    if (R->getLB() == APInt(width, 0)) {
      if (R->getUB() != APInt(width, 0)) {
        purgedZeroIntervals.push_back(StridedWrappedRangePtr(
          new StridedWrappedRange(R->getLB() + 1, R->getUB(), width, R->getStride())));
      }
    } else {
      if (R->getUB() == APInt(width, 0)) {
        APInt minusOne = APInt::getMaxValue(width);
        purgedZeroIntervals.push_back(StridedWrappedRangePtr(
          new StridedWrappedRange(R->getLB(), minusOne, width, R->getStride())));
      } else {
        APInt plusOne(width, 1, false);
        APInt minusOne = APInt::getMaxValue(width);
        purgedZeroIntervals.push_back(StridedWrappedRangePtr(
          new StridedWrappedRange(R->getLB(), minusOne, width, R->getStride())));
        purgedZeroIntervals.push_back(StridedWrappedRangePtr(
          new StridedWrappedRange(plusOne, R->getUB(), width, R->getStride())));
      }
    }
  } else {
    purgedZeroIntervals.push_back(StridedWrappedRangePtr(new StridedWrappedRange(*R)));
  }
  return purgedZeroIntervals;
}

static std::vector<StridedWrappedRangePtr>
purgeZero(const std::vector<StridedWrappedRangePtr> &Vs) {
  std::vector<StridedWrappedRangePtr> res;
  for (auto &v : Vs) {
    auto p = purgeZero(v);
    res.insert(res.end(), p.begin(), p.end());
  }
  return res;
}

static StridedWrappedRange UnsignedWrappedMult(const StridedWrappedRange *Op1,
                                               const StridedWrappedRange *Op2) {
  StridedWrappedRange Res(*Op1);
  APInt a = Op1->getLB(); APInt b = Op1->getUB();
  APInt c = Op2->getLB(); APInt d = Op2->getUB();
  bool Overflow1, Overflow2;
  APInt lb = a.umul_ov(c, Overflow1);
  APInt ub = b.umul_ov(d, Overflow2);

  if (Overflow1 || Overflow2) {
    NumOfOverflows++;
    Res.makeTop();
    return Res;
  }
  unsigned long new_stride;
  Res.setLB(lb);
  Res.setUB(ub);
  if (Op2->isSingleVal())      new_stride = (unsigned long)(Op1->getStride() * c.getZExtValue());
  else if (Op1->isSingleVal()) new_stride = (unsigned long)(Op2->getStride() * a.getZExtValue());
  else                         new_stride = UtilFunctions::getLCM(Op1->getStride(), Op2->getStride());
  Res.setStride(new_stride);
  return Res;
}

static StridedWrappedRange SignedWrappedMult(const StridedWrappedRange *Op1,
                                             const StridedWrappedRange *Op2) {
  StridedWrappedRange Res(*Op1);
  APInt a = Op1->getLB(); APInt b = Op1->getUB();
  APInt c = Op2->getLB(); APInt d = Op2->getUB();

  bool IsZero_a = IsMSBZeroSI(a);
  bool IsZero_b = IsMSBZeroSI(b);
  bool IsZero_c = IsMSBZeroSI(c);
  bool IsZero_d = IsMSBZeroSI(d);

  unsigned long new_stride;
  if (Op2->isSingleVal()) {
    if (IsZero_c) new_stride = (unsigned long)(Op1->getStride() * c.getZExtValue());
    // SASI-PRECISION: original code casts (stride * sext) directly to ulong,
    // which produces garbage when sext is negative (e.g. width-4 c=15 → -1
    // gives stride * -1 → ULONG_MAX). The stride is a spacing magnitude, so
    // take |sext|.
    else          new_stride = (unsigned long)(Op1->getStride() * (uint64_t)std::abs(c.getSExtValue()));
  } else if (Op1->isSingleVal()) {
    if (IsZero_a) new_stride = (unsigned long)(Op2->getStride() * a.getZExtValue());
    else          new_stride = (unsigned long)(Op2->getStride() * (uint64_t)std::abs(a.getSExtValue()));
  } else {
    new_stride = UtilFunctions::getLCM(Op1->getStride(), Op2->getStride());
  }

  if (IsZero_a && IsZero_b && IsZero_c && IsZero_d) {
    bool O1, O2;
    APInt lb = a.smul_ov(c, O1);
    APInt ub = b.smul_ov(d, O2);
    if (!O1 && !O2) { Res.setLB(lb); Res.setUB(ub); Res.setStride(new_stride); return Res; }
  } else if (!IsZero_a && !IsZero_b && !IsZero_c && !IsZero_d) {
    bool O1, O2;
    APInt lb = b.smul_ov(d, O1);
    APInt ub = a.smul_ov(c, O2);
    if (!O1 && !O2) { Res.setLB(lb); Res.setUB(ub); Res.setStride(new_stride); return Res; }
  } else if (!IsZero_a && !IsZero_b && IsZero_c && IsZero_d) {
    bool O1, O2;
    APInt lb = a.smul_ov(d, O1);
    APInt ub = b.smul_ov(c, O2);
    if (!O1 && !O2) { Res.setLB(lb); Res.setUB(ub); Res.setStride(new_stride); return Res; }
  } else if (IsZero_a && IsZero_b && !IsZero_c && !IsZero_d) {
    bool O1, O2;
    APInt lb = b.smul_ov(c, O1);
    APInt ub = a.smul_ov(d, O2);
    if (!O1 && !O2) { Res.setLB(lb); Res.setUB(ub); Res.setStride(new_stride); return Res; }
  }
  NumOfOverflows++;
  Res.makeTop();
  return Res;
}

bool StridedWrappedRange::minimal_common_integer_splitted(StridedWrappedRange *Op1,
                                                          StridedWrappedRange *Op2,
                                                          APInt *result) {
  unsigned long op1_s, op2_s;
  float x = 0, y = 0;
  APInt op1_l, op2_l, op1_u, op2_u;
  op1_s = Op1->getStride();
  op2_s = Op2->getStride();
  op1_l = Op1->getLB();
  op2_l = Op2->getLB();
  op1_u = Op1->getUB();
  op2_u = Op2->getUB();

  if (Op1->isSingleVal()) {
    if (Op2->isSingleVal()) {
      if (op1_l == op2_l) { *result = op1_l; return true; }
    } else if (op1_l.getZExtValue() >= op2_l.getZExtValue()
               && op1_l.getZExtValue() <= op2_u.getZExtValue()
               && op2_s != 0
               && ((op1_l.getZExtValue() - op2_l.getZExtValue()) % op2_s == 0)) {
      *result = op1_l;
      return true;
    }
    return false;
  }
  if (Op2->isSingleVal()) return StridedWrappedRange::minimal_common_integer_splitted(Op2, Op1, result);

  if (op1_u.getZExtValue() < op2_l.getZExtValue()
      || op2_u.getZExtValue() < op1_l.getZExtValue()) return false;

  if ((op2_l - op1_l).getZExtValue() % UtilFunctions::getGCD(op1_s, op2_s)) return false;

  assert(Op1->getStride() != 0);

  if (UtilFunctions::diophantineNaturalSolution(
          -(long)(op1_l.getZExtValue() - op2_l.getZExtValue()),
          (long)op1_s, -(long)op2_s, &x, &y)) {
    long long_val = ((long)(x * op1_s) + (long)op1_l.getZExtValue());
    APInt first_int(Op1->getWidth(), (uint64_t)long_val);
    if (first_int.uge(op1_l) && first_int.ule(op1_u)
        && first_int.uge(op2_l) && first_int.ule(op2_u)) {
      *result = first_int;
      return true;
    }
  }
  return false;
}

bool StridedWrappedRange::minimal_common_integer(StridedWrappedRange *Op1,
                                                 StridedWrappedRange *Op2,
                                                 APInt *result) {
  std::vector<StridedWrappedRangePtr> op1_ssplitted, op2_ssplitted, temp;
  unsigned long op1_size, op2_size;

  op1_ssplitted = strided_ssplit(Op1->getLB(), Op1->getUB(), Op1->getWidth(), Op1->getStride());
  op2_ssplitted = strided_ssplit(Op2->getLB(), Op2->getUB(), Op1->getWidth(), Op2->getStride());

  if (op1_ssplitted.size() == 1 && op2_ssplitted.size() == 2) {
    temp = op1_ssplitted;
    op1_ssplitted = op2_ssplitted;
    op2_ssplitted = temp;
  }

  op1_size = op1_ssplitted.size();
  op2_size = op2_ssplitted.size();

  if (op1_size == 1 && op2_size == 1)
    return StridedWrappedRange::minimal_common_integer_splitted(Op1, Op2, result);

  APInt int0, int1;
  bool int0_valid, int1_valid;
  if (op1_size == 2 && op2_size == 1) {
    int0_valid = StridedWrappedRange::minimal_common_integer_splitted(
        op1_ssplitted.front().get(), op2_ssplitted.front().get(), &int0);
    int1_valid = StridedWrappedRange::minimal_common_integer_splitted(
        op1_ssplitted.back().get(), op2_ssplitted.front().get(), &int1);
  } else {
    int0_valid = StridedWrappedRange::minimal_common_integer_splitted(
        op1_ssplitted.front().get(), op2_ssplitted.front().get(), &int0);
    int1_valid = StridedWrappedRange::minimal_common_integer_splitted(
        op1_ssplitted.back().get(), op2_ssplitted.back().get(), &int1);
  }
  *result = int0;
  if (!int0_valid) { *result = int1; return int1_valid; }
  return int0_valid;
}

void StridedWrappedRange::WrappedMultiplication(StridedWrappedRange *LHS,
                                                const StridedWrappedRange *Op1,
                                                const StridedWrappedRange *Op2) {
  if (Op1->IsZeroRange() || Op2->IsZeroRange()) {
    LHS->setLB((uint64_t)0);
    LHS->setUB((uint64_t)0);
    LHS->setStride(0);
    return;
  }
  auto s1 = strided_psplitsi(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth(), Op1->getStride());
  auto s2 = strided_psplitsi(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth(), Op2->getStride());

  LHS->makeBot();
  if (Op1->isSingleVal() && Op2->isSingleVal()) {
    LHS->resetBottomFlag();
    LHS->resetTopFlag();
    LHS->setStride(0);
    LHS->setLB(Op1->getLB() * Op2->getLB());
    LHS->setUB(Op1->getUB() * Op2->getUB());
  }

  std::vector<StridedWrappedRangePtr> allranges;
  for (auto &p1 : s1) {
    for (auto &p2 : s2) {
      StridedWrappedRange Tmp1 = UnsignedWrappedMult(p1.get(), p2.get());
      StridedWrappedRange Tmp2 = SignedWrappedMult  (p1.get(), p2.get());
      auto curr_ranges = StridedWrappedRange::MultiValueIntersection(&Tmp1, &Tmp2);
      allranges.insert(allranges.end(), curr_ranges.begin(), curr_ranges.end());
    }
  }
  std::vector<AbstractValue *> Rs;
  std::transform(allranges.begin(), allranges.end(), std::back_inserter(Rs),
                 convertPtrValToAbs);
  StridedWrappedRange result_val(*LHS);
  if (StridedWrappedRange::StridedGeneralizedJoin(Rs, &result_val))
    LHS->WrappedRangeAssign(&result_val);
}

void StridedWrappedRange::AdjustStride() {
  if (!this->IsTop() && !this->isBot()) {
    if (this->getLB() == this->getUB()) this->setStride(0);
    else                                this->setStride(1);
  }
}

static StridedWrappedRange WrappedUnsignedDivision(StridedWrappedRange const *Dividend,
                                                   StridedWrappedRange const *Divisor) {
  StridedWrappedRange Res(*Dividend);
  APInt a = Dividend->getLB(); APInt b = Dividend->getUB();
  APInt c = Divisor ->getLB(); APInt d = Divisor ->getUB();
  Res.setLB(a.udiv(d));
  Res.setUB(b.udiv(c));
  Res.AdjustStride();
  return Res;
}

static StridedWrappedRange WrappedSignedDivision(StridedWrappedRange const *Dividend,
                                                 StridedWrappedRange const *Divisor,
                                                 bool &IsOverflow) {
  IsOverflow = false;
  StridedWrappedRange Res(*Dividend);
  APInt a = Dividend->getLB(); APInt b = Dividend->getUB();
  APInt c = Divisor ->getLB(); APInt d = Divisor ->getUB();

  bool IsZero_a = IsMSBZeroSI(a);
  bool IsZero_c = IsMSBZeroSI(c);

  if (IsZero_a && IsZero_c) {
    bool O1, O2;
    Res.setLB(a.sdiv_ov(d, O1));
    Res.setUB(b.sdiv_ov(c, O2));
    IsOverflow = O1 || O2;
    Res.AdjustStride();
    return Res;
  } else if (!IsZero_a && !IsZero_c) {
    bool O1, O2;
    Res.setLB(b.sdiv_ov(c, O1));
    Res.setUB(a.sdiv_ov(d, O2));
    IsOverflow = O1 || O2;
    Res.AdjustStride();
    return Res;
  } else if (IsZero_a && !IsZero_c) {
    bool O1, O2;
    Res.setLB(b.sdiv_ov(d, O1));
    Res.setUB(a.sdiv_ov(c, O2));
    IsOverflow = O1 || O2;
    Res.AdjustStride();
    return Res;
  } else {
    bool O1, O2;
    Res.setLB(a.sdiv_ov(c, O1));
    Res.setUB(b.sdiv_ov(d, O2));
    IsOverflow = O1 || O2;
    Res.AdjustStride();
    return Res;
  }
}

void StridedWrappedRange::WrappedDivision(StridedWrappedRange *LHS,
                                          const StridedWrappedRange *Dividend,
                                          const StridedWrappedRange *Divisor,
                                          bool IsSignedDiv) {
  if (Dividend->IsZeroRange()) {
    LHS->setLB((uint64_t)0);
    LHS->setUB((uint64_t)0);
    LHS->setStride(0);
    return;
  }
  if (Divisor->IsZeroRange()) { LHS->makeBot(); return; }

  std::vector<AbstractValue *> Rs;
  if (IsSignedDiv) {
    auto s1 = strided_psplitsi(Dividend->getLB(), Dividend->getUB(),
                               Dividend->getLB().getBitWidth(), Dividend->getStride());
    auto s2 = purgeZero(strided_psplitsi(Divisor->getLB(), Divisor->getUB(),
                                         Divisor->getLB().getBitWidth(), Divisor->getStride()));
    LHS->makeBot();
    bool is_top = false;
    for (auto &p1 : s1) {
      if (is_top) break;
      for (auto &p2 : s2) {
        bool IsOverflow;
        StridedWrappedRange Tmp = WrappedSignedDivision(p1.get(), p2.get(), IsOverflow);
        if (IsOverflow) {
          NumOfOverflows++;
          LHS->makeTop();
          is_top = true;
          break;
        }
        Rs.push_back(cast<AbstractValue>(new StridedWrappedRange(Tmp)));
      }
    }
    if (!is_top) {
      StridedWrappedRange result_val(*LHS);
      StridedWrappedRange::StridedGeneralizedJoin(Rs, &result_val);
      LHS->WrappedRangeAssign(&result_val);
    }
  } else {
    auto s1 = strided_ssplit(Dividend->getLB(), Dividend->getUB(),
                             Dividend->getLB().getBitWidth(), Dividend->getStride());
    auto s2 = purgeZero(strided_ssplit(Divisor->getLB(), Divisor->getUB(),
                                       Divisor->getLB().getBitWidth(), Divisor->getStride()));
    LHS->makeBot();
    for (auto &p1 : s1) {
      for (auto &p2 : s2) {
        StridedWrappedRange Tmp = WrappedUnsignedDivision(p1.get(), p2.get());
        Rs.push_back(cast<AbstractValue>(new StridedWrappedRange(Tmp)));
      }
    }
    StridedWrappedRange result_val(*LHS);
    StridedWrappedRange::StridedGeneralizedJoin(Rs, &result_val);
    LHS->WrappedRangeAssign(&result_val);
  }
  for (auto *p : Rs) delete p;
}

void StridedWrappedRange::WrappedRem(StridedWrappedRange *LHS,
                                     const StridedWrappedRange *Dividend,
                                     const StridedWrappedRange *Divisor,
                                     bool IsSignedRem) {
  if (Dividend->IsZeroRange()) {
    LHS->setLB((uint64_t)0);
    LHS->setUB((uint64_t)0);
    LHS->setStride(0);
    return;
  }
  if (Divisor->IsZeroRange()) { LHS->makeBot(); return; }

  std::vector<AbstractValue *> Rs;
  if (IsSignedRem) {
    auto s1 = strided_ssplit(Dividend->getLB(), Dividend->getUB(),
                             Dividend->getLB().getBitWidth(), Dividend->getStride());
    auto s2 = purgeZero(strided_ssplit(Divisor->getLB(), Divisor->getUB(),
                                       Divisor->getLB().getBitWidth(), Divisor->getStride()));
    LHS->makeBot();
    for (auto &p1 : s1) {
      for (auto &p2 : s2) {
        APInt a = p1.get()->getLB();
        APInt b = p1.get()->getUB();
        APInt c = p2.get()->getLB();
        APInt d = p2.get()->getUB();
        (void)b;
        bool IsZero_a = IsMSBZeroSI(a);
        bool IsZero_c = IsMSBZeroSI(c);
        unsigned w = a.getBitWidth();
        APInt lb, ub;
        if (IsZero_a && IsZero_c)        { lb = APInt(w, 0); ub = d - 1; }
        else if (IsZero_a && !IsZero_c)  { lb = APInt(w, 0); ub = -c - 1; }
        else if (!IsZero_a && IsZero_c)  { lb = -d + 1;      ub = APInt(w, 0); }
        else                             { lb = c + 1;       ub = APInt(w, 0); }
        StridedWrappedRange tmp(lb, ub, w, 1);
        Rs.push_back(cast<AbstractValue>(new StridedWrappedRange(tmp)));
      }
    }
  } else {
    auto s1 = strided_ssplit(Dividend->getLB(), Dividend->getUB(),
                             Dividend->getLB().getBitWidth(), Dividend->getStride());
    auto s2 = purgeZero(strided_ssplit(Divisor->getLB(), Divisor->getUB(),
                                       Divisor->getLB().getBitWidth(), Divisor->getStride()));
    LHS->makeBot();
    for (auto &p1 : s1) {
      (void)p1;
      for (auto &p2 : s2) {
        APInt d  = p2.get()->getUB();
        unsigned w = d.getBitWidth();
        APInt lb = APInt(w, 0);
        APInt ub = d - 1;
        StridedWrappedRange tmp(lb, ub, w, 1);
        Rs.push_back(cast<AbstractValue>(new StridedWrappedRange(tmp)));
      }
    }
  }

  StridedWrappedRange result_val(*LHS);
  StridedWrappedRange::StridedGeneralizedJoin(Rs, &result_val);
  LHS->WrappedRangeAssign(&result_val);
  for (auto *p : Rs) delete p;
}

void StridedWrappedRange::WrappedPlus(StridedWrappedRange *LHS,
                                      const StridedWrappedRange *Op1,
                                      const StridedWrappedRange *Op2) {
  if (IsWrappedOverflow_AddSubSI(Op1->getLB(), Op1->getUB(),
                                 Op2->getLB(), Op2->getUB())) {
    NumOfOverflows++;
    LHS->makeTop();
    return;
  }
  LHS->setLB(Op1->getLB() + Op2->getLB());
  LHS->setUB(Op1->getUB() + Op2->getUB());
  unsigned long new_s = UtilFunctions::getGCD(Op1->getStride(), Op2->getStride());
  LHS->setStride(new_s);
}

void StridedWrappedRange::WrappedMinus(StridedWrappedRange *LHS,
                                       const StridedWrappedRange *Op1,
                                       const StridedWrappedRange *Op2) {
  if (IsWrappedOverflow_AddSubSI(Op1->getLB(), Op1->getUB(),
                                 Op2->getLB(), Op2->getUB())) {
    NumOfOverflows++;
    LHS->makeTop();
    return;
  }
  LHS->setLB(Op1->getLB() - Op2->getUB());
  LHS->setUB(Op1->getUB() - Op2->getLB());
  unsigned long new_s = UtilFunctions::getGCD(Op1->getStride(), Op2->getStride());
  LHS->setStride(new_s);
}

StridedWrappedRange StridedWrappedRange::StridedLogicalBitwiseOr(StridedWrappedRange *Op1,
                                                                 StridedWrappedRange *Op2) {
  StridedWrappedRange Result(*Op1);
  auto s1 = strided_ssplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth(), Op1->getStride());
  auto s2 = strided_ssplit(Op2->getLB(), Op2->getUB(), Op2->getLB().getBitWidth(), Op2->getStride());

  Result.makeBot();
  std::vector<AbstractValue *> Rs;

  for (auto &p1 : s1) {
    for (auto &p2 : s2) {
      APInt lb, ub;
      unimelb::unsignedOr(p1.get(), p2.get(), lb, ub);
      StridedWrappedRange Tmp(lb, ub, Op1->getLB().getBitWidth());

      unsigned long s_t, new_stride;
      unsigned long i1_ntz = unimelb::NumContZeros(p1.get()->getStride());
      unsigned long i2_ntz = unimelb::NumContZeros(p2.get()->getStride());

      if      (p1.get()->isSingleVal()) s_t = i2_ntz;
      else if (p2.get()->isSingleVal()) s_t = i1_ntz;
      else                              s_t = (i1_ntz < i2_ntz) ? i1_ntz : i2_ntz;

      if (p1.get()->isSingleVal() && p1.get()->getLB().getZExtValue() == 0)
        new_stride = p2.get()->getStride();
      else if (p2.get()->isSingleVal() && p2.get()->getLB().getZExtValue() == 0)
        new_stride = p1.get()->getStride();
      else
        new_stride = ((unsigned long)1) << s_t;

      if (Tmp.getLB() == Tmp.getUB()) Tmp.setStride(0);
      else                            Tmp.setStride(new_stride);

      Rs.push_back(cast<AbstractValue>(new StridedWrappedRange(Tmp)));
    }
  }
  StridedWrappedRange result_val(Result);
  StridedWrappedRange::StridedGeneralizedJoin(Rs, &result_val);
  Result.WrappedRangeAssign(&result_val);
  for (auto *p : Rs) delete p;
  return Result;
}

StridedWrappedRange StridedWrappedRange::StridedLogicalBitwiseNot(StridedWrappedRange *Op1) {
  StridedWrappedRange Result(*Op1);
  auto s1 = strided_ssplit(Op1->getLB(), Op1->getUB(), Op1->getLB().getBitWidth(), Op1->getStride());

  APInt lb_o = ~(Op1->getUB());
  APInt ub_o = ~(Op1->getLB());
  Result.makeBot();
  std::vector<AbstractValue *> Rs;

  for (auto &p1 : s1) {
    (void)p1;
    APInt lb = lb_o, ub = ub_o;
    StridedWrappedRange Tmp(lb, ub, lb.getBitWidth());
    Tmp.setStride(Op1->getStride());
    Rs.push_back(cast<AbstractValue>(new StridedWrappedRange(Tmp)));
  }
  StridedWrappedRange result_val(Result);
  StridedWrappedRange::StridedGeneralizedJoin(Rs, &result_val);
  Result.WrappedRangeAssign(&result_val);
  for (auto *p : Rs) delete p;
  return Result;
}

void StridedWrappedRange::WrappedLogicalBitwise(StridedWrappedRange *LHS,
                                                StridedWrappedRange *Op1,
                                                StridedWrappedRange *Op2,
                                                unsigned Opcode) {
  StridedWrappedRange temp_result(*Op1);
  LHS->makeBot();
  switch (Opcode) {
  case Instruction::Or: {
    temp_result = StridedWrappedRange::StridedLogicalBitwiseOr(Op1, Op2);
    LHS->WrappedRangeAssign(&temp_result);
    break;
  }
  case Instruction::And: {
    StridedWrappedRange op1_not = StridedWrappedRange::StridedLogicalBitwiseNot(Op1);
    StridedWrappedRange op2_not = StridedWrappedRange::StridedLogicalBitwiseNot(Op2);
    temp_result = StridedWrappedRange::StridedLogicalBitwiseOr(&op1_not, &op2_not);
    temp_result = StridedWrappedRange::StridedLogicalBitwiseNot(&temp_result);
    LHS->WrappedRangeAssign(&temp_result);
    break;
  }
  case Instruction::Xor: {
    StridedWrappedRange op1_not = StridedWrappedRange::StridedLogicalBitwiseNot(Op1);
    StridedWrappedRange op2_not = StridedWrappedRange::StridedLogicalBitwiseNot(Op2);
    StridedWrappedRange first_op  = StridedWrappedRange::StridedLogicalBitwiseOr(&op1_not, Op2);
    first_op = StridedWrappedRange::StridedLogicalBitwiseNot(&first_op);
    StridedWrappedRange second_op = StridedWrappedRange::StridedLogicalBitwiseOr(Op1, &op2_not);
    second_op = StridedWrappedRange::StridedLogicalBitwiseNot(&second_op);
    temp_result = StridedWrappedRange::StridedLogicalBitwiseOr(&first_op, &second_op);
    LHS->WrappedRangeAssign(&temp_result);
    break;
  }
  default:
    llvm_unreachable("Unexpected instruction");
  }
}

StridedWrappedRange StridedWrappedRange::StridedLShr(StridedWrappedRange *Op, uint64_t val) {
  StridedWrappedRange Result(*Op);
  unsigned long ntz;
  Result.makeBot();
  if (val <= Op->getLB().getBitWidth()) {
    StridedWrappedRange temp_result(Op->getLB(), Op->getLB(), Op->getLB().getBitWidth(), 0);
    auto s1 = strided_ssplit(Op->getLB(), Op->getUB(), Op->getLB().getBitWidth(), Op->getStride());
    for (auto &p : s1) {
      APInt lb(p.get()->getLB()), ub(p.get()->getUB());
      APInt unsig_lb(lb.getBitWidth(), lb.getZExtValue(), false);
      APInt unsig_ub(ub.getBitWidth(), ub.getZExtValue(), false);
      APInt new_lb = unsig_lb.lshr((unsigned)val);
      APInt new_ub = unsig_ub.lshr((unsigned)val);
      unsigned long new_stride;
      unsigned long curr_stride = (p.get()->getStride()) >> val;
      ntz = unimelb::NumContZeros(p.get()->getStride());
      if (ntz >= val) new_stride = curr_stride;
      else            new_stride = 1;
      temp_result.setLB(new_lb);
      temp_result.setUB(new_ub);
      temp_result.setStride(new_stride);
      temp_result.normalizeTop();
      Result.join(&temp_result);
    }
  } else {
    Result.makeTop();
  }
  return Result;
}

StridedWrappedRange StridedWrappedRange::StridedAShr(StridedWrappedRange *Op, uint64_t val) {
  StridedWrappedRange Result(*Op);
  unsigned long ntz;
  Result.makeBot();
  if (val <= Op->getLB().getBitWidth()) {
    StridedWrappedRange temp_result(Op->getLB(), Op->getLB(), Op->getLB().getBitWidth(), 0);
    auto s1 = strided_nsplit(Op->getLB(), Op->getUB(), Op->getLB().getBitWidth(), Op->getStride());
    for (auto &p : s1) {
      APInt new_lb = p.get()->getLB().ashr((unsigned)val);
      APInt new_ub = p.get()->getUB().ashr((unsigned)val);
      unsigned long new_stride;
      unsigned long curr_stride = (p.get()->getStride()) >> val;
      ntz = unimelb::NumContZeros(p.get()->getStride());
      if (ntz >= val) new_stride = curr_stride;
      else            new_stride = 1;
      temp_result.setLB(new_lb);
      temp_result.setUB(new_ub);
      temp_result.setStride(new_stride);
      temp_result.normalizeTop();
      Result.join(&temp_result);
    }
  } else {
    Result.makeTop();
  }
  return Result;
}

StridedWrappedRange StridedWrappedRange::StridedShl(StridedWrappedRange *Op, uint64_t val) {
  StridedWrappedRange Result(*Op);
  Result.makeBot();
  if (val <= Op->getLB().getBitWidth()) {
    StridedWrappedRange temp_result(Op->getLB(), Op->getLB(), Op->getLB().getBitWidth(), 0);
    auto s1 = strided_ssplit(Op->getLB(), Op->getUB(), Op->getLB().getBitWidth(), Op->getStride());
    for (auto &p : s1) {
      (void)p;
      APInt new_lb(Op->getLB());
      APInt new_ub(Op->getUB());
      new_lb = new_lb << (unsigned)val;
      new_ub = new_ub << (unsigned)val;
      unsigned long curr_stride = (p.get()->getStride()) << val;
      unsigned long new_stride = (curr_stride > 1) ? curr_stride : 1;
      if (new_lb == new_ub) new_stride = 0;
      temp_result.setLB(new_lb);
      temp_result.setUB(new_ub);
      temp_result.setStride(new_stride);
      temp_result.normalizeTop();
      Result.join(&temp_result);
    }
  } else {
    Result.makeTop();
  }
  return Result;
}

void StridedWrappedRange::StridedWrappedBitwiseShitfs(StridedWrappedRange *LHS,
                                                     StridedWrappedRange *Operand,
                                                     StridedWrappedRange *Shift,
                                                     unsigned Opcode) {
  LHS->makeBot();
  auto s1 = strided_ssplit(Shift->getLB(), Shift->getUB(),
                           Shift->getLB().getBitWidth(), Shift->getStride());
  StridedWrappedRange tmpResult(*Operand);
  for (auto &p : s1) {
    uint64_t lower_val = p.get()->getLB().getZExtValue();
    uint64_t upper_val = p.get()->getUB().getZExtValue();
    unsigned long incr = p.get()->getStride();
    if (!incr) incr += 1;
    while (lower_val <= upper_val) {
      switch (Opcode) {
      case Instruction::Shl:
        tmpResult = StridedWrappedRange::StridedShl (Operand, lower_val);
        LHS->join(&tmpResult); break;
      case Instruction::LShr:
        tmpResult = StridedWrappedRange::StridedLShr(Operand, lower_val);
        LHS->join(&tmpResult); break;
      case Instruction::AShr:
        tmpResult = StridedWrappedRange::StridedAShr(Operand, lower_val);
        LHS->join(&tmpResult); break;
      }
      lower_val += incr;
    }
  }
}

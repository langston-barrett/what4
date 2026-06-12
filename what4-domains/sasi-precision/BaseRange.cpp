// Vendored from sasi/lib/RangeAnalysis/BaseRange.cpp
// SASI-PRECISION: untouched math; removed includes / IR-typed helpers we
// don't ship.

#include "BaseRange.h"

using namespace llvm;
using namespace unimelb;

bool BaseRange::IsTop() const {
  if (isConstant()) return false;
  return __isTop;
}

void BaseRange::makeTop() {
  __isTop = true;
  if (isSigned) {
    setLB(APInt::getSignedMinValue(width));
    setUB(APInt::getSignedMaxValue(width));
  } else {
    setLB(APInt::getMinValue(width));
    setUB(APInt::getMaxValue(width));
  }
  setStride(1);
}

bool BaseRange::isIdentical(AbstractValue *V) {
  BaseRange *B = cast<BaseRange>(V);
  return (__isTop == B->__isTop &&
          getLB() == B->getLB() && getUB() == B->getUB());
}

void BaseRange::printRange(raw_ostream &Out) const {
  (void)Out;
}

void BaseRange::print(raw_ostream &Out) const {
  AbstractValue::print(Out);
  printRange(Out);
}

int64_t minOr_int64t(int64_t a, int64_t b, int64_t c, int64_t d) {
  int64_t m, temp;
  m = 0x80000000;
  while (m != 0) {
    if (~a & c & m) {
      temp = (a | m) & -m;
      if (temp <= b) {
        a = temp;
        break;
      }
    } else if (a & ~c & m) {
      temp = (c | m) & -m;
      if (temp <= d) {
        c = temp;
        break;
      }
    }
    m = m >> 1;
  }
  return a | c;
}

APInt unimelb::minOr(const APInt &a, const APInt &b, const APInt &c, const APInt &d) {
  return APInt(a.getBitWidth(),
               (uint64_t)minOr_int64t(a.getSExtValue(), b.getSExtValue(),
                                      c.getSExtValue(), d.getSExtValue()));
}

int64_t maxOr_int64t(int64_t a, int64_t b, int64_t c, int64_t d) {
  int64_t m, temp;
  m = 0x80000000;
  while (m != 0) {
    if (b & d & m) {
      temp = (b - m) | (m - 1);
      if (temp >= a) {
        b = temp;
        break;
      }
      temp = (d - m) | (m - 1);
      if (temp >= c) {
        d = temp;
        break;
      }
    }
    m = m >> 1;
  }
  return b | d;
}

APInt unimelb::maxOr(const APInt &a, const APInt &b, const APInt &c, const APInt &d) {
  return APInt(a.getBitWidth(),
               (uint64_t)maxOr_int64t(a.getSExtValue(), b.getSExtValue(),
                                      c.getSExtValue(), d.getSExtValue()));
}

APInt unimelb::minAnd(APInt a, const APInt &b, APInt c, const APInt &d) {
  APInt m = APInt::getOneBitSet(a.getBitWidth(), a.getBitWidth() - 1);
  while (m != 0) {
    if ((~a & ~c & m).getBoolValue()) {
      APInt temp = (a | m) & ~m;
      if (temp.ule(b)) { a = temp; break; }
      temp = (c | m) & ~m;
      if (temp.ule(d)) { c = temp; break; }
    }
    m = m.lshr(1);
  }
  return a & c;
}

APInt unimelb::maxAnd(const APInt &a, APInt b, const APInt &c, APInt d) {
  APInt m = APInt::getOneBitSet(a.getBitWidth(), a.getBitWidth() - 1);
  while (m != 0) {
    if ((b & ~d & m).getBoolValue()) {
      APInt temp = (b & ~m) | (m - 1);
      if (temp.uge(a)) { b = temp; break; }
    } else if ((~b & d & m).getBoolValue()) {
      APInt temp = (d & ~m) | (m - 1);
      if (temp.uge(c)) { d = temp; break; }
    }
    m = m.lshr(1);
  }
  return b & d;
}

APInt unimelb::minXor(const APInt &a, const APInt &b, const APInt &c, const APInt &d) {
  return (unimelb::minAnd(a, b, ~d, ~c) | unimelb::minAnd(~b, ~a, c, d));
}

APInt unimelb::maxXor(const APInt &a, const APInt &b, const APInt &c, const APInt &d) {
  return (unimelb::maxOr(APInt::getNullValue(a.getBitWidth()),
                         unimelb::maxAnd(a, b, ~d, ~c),
                         APInt::getNullValue(a.getBitWidth()),
                         unimelb::maxAnd(~b, ~a, c, d)));
}

void unimelb::unsignedOr(BaseRange *Op1, BaseRange *Op2, APInt &lb, APInt &ub) {
  APInt a = Op1->getLB();
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();
  APInt d = Op2->getUB();
  lb = unimelb::minOr(a, b, c, d);
  ub = unimelb::maxOr(a, b, c, d);
}

void unimelb::unsignedAnd(BaseRange *Op1, BaseRange *Op2, APInt &lb, APInt &ub) {
  APInt a = Op1->getLB();
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();
  APInt d = Op2->getUB();
  lb = unimelb::minAnd(a, b, c, d);
  ub = unimelb::maxAnd(a, b, c, d);
}

void unimelb::unsignedXor(BaseRange *Op1, BaseRange *Op2, APInt &lb, APInt &ub) {
  APInt a = Op1->getLB();
  APInt b = Op1->getUB();
  APInt c = Op2->getLB();
  APInt d = Op2->getUB();
  lb = unimelb::minXor(a, b, c, d);
  ub = unimelb::maxXor(a, b, c, d);
}

unsigned long unimelb::NumContZeros(unsigned long val) {
  if (val == 0) return 0;
  unsigned long y = (~val) & (val - 1);
  unsigned count = 0;
  while (y) { count++; y >>= 1; }
  return count;
}

unsigned long unimelb::NumOnes(unsigned long val) {
  unsigned count = 0;
  while (val) { count++; val = val & (val - 1); }
  return count;
}

// Vendored from sasi/include/StridedWrappedRange.h
// SASI-PRECISION: replaced llvm/* includes with llvm_stubs.h, removed
// Value*-taking and TBool-taking constructors and the visit*/filterSigma
// dispatch glue (we never invoke any of those). Math is unchanged.

#ifndef SASI_PRECISION_STRIDED_WRAPPED_RANGE_H
#define SASI_PRECISION_STRIDED_WRAPPED_RANGE_H

#include "AbstractValue.h"
#include "BaseRange.h"
#include "llvm_stubs.h"

#include <memory>
#include <vector>

#define __SIGNED false
#define round(x) ((x)>=0?(long)((x)+0.5):(long)((x)-0.5))

namespace unimelb {

  class StridedWrappedRange;
  typedef std::shared_ptr<StridedWrappedRange> StridedWrappedRangePtr;

  class UtilFunctions {
  public:
    static uint64_t getGCD(uint64_t a, uint64_t b) {
      if (b == 0) return a;
      return UtilFunctions::getGCD(b, a % b);
    }

    static unsigned long getLCM(unsigned long a, unsigned long b) {
      if (a == 0 || b == 0) return 0;
      return (uint64_t)((uint64_t)a * (uint64_t)b) / UtilFunctions::getGCD(a, b);
    }

    static unsigned long getExtendedGCD(unsigned long a, unsigned long b,
                                        unsigned long *x, unsigned long *y) {
      unsigned long x0, y0, d;
      if (b == 0) { *x = 1; *y = 0; return a; }
      d = UtilFunctions::getExtendedGCD(b, a % b, &x0, &y0);
      *x = y0;
      *y = x0 - ((a / b) * y0);
      return d;
    }

    static bool get_intersection(float a, float b, int a_dir, int b_dir,
                                 float *lb, float *ub) {
      if (a_dir == 2 && b_dir == 2) {
        *lb = (a > b) ? a : b;
        *ub = 1.0f / 0.0f;
        return true;
      }
      if (a_dir == 1 && b_dir == 2) {
        if (a > b) { *lb = b; *ub = a; return true; }
        return false;
      }
      if (a_dir == 2 && b_dir == 1) {
        if (b > a) { *lb = a; *ub = b; return true; }
        return false;
      }
      if (a_dir == 1 && b_dir == 1) {
        *ub = (a < b) ? a : b;
        *lb = -1.0f / 0.0f;
        return true;
      }
      return false;
    }

    static bool diophantineNaturalSolution(long c, long a, long b,
                                           float *solx, float *soly) {
      long d, x0, y0;
      uint64_t tmp_g;
      tmp_g = UtilFunctions::getGCD((uint64_t)b, (uint64_t)c);
      d = UtilFunctions::getGCD(a, tmp_g);
      a = a / d;
      b = b / d;
      c = c / d;
      if (c == 0) { *solx = 0; *soly = 0; return true; }
      d = UtilFunctions::getExtendedGCD((unsigned long)a, (unsigned long)b,
                                        (unsigned long *)&x0,
                                        (unsigned long *)&y0);
      if (((int64_t)c) % d == 0) {
        float t0, t1, t, lb, ub;
        int t0_dir, t1_dir;
        t0 = ((-c * x0) * 1.0f) / b;
        t1 = (( c * y0) * 1.0f) / a;
        t0_dir = (b < 0) ? 1 : 2;
        t1_dir = (a < 0) ? 2 : 1;
        if (UtilFunctions::get_intersection(t0, t1, t0_dir, t1_dir, &lb, &ub)) {
          float lb_abs = lb < 0 ? -lb : lb;
          float ub_abs = ub < 0 ? -ub : ub;
          float pos_inf =  1.0f / 0.0f;
          float neg_inf = -1.0f / 0.0f;
          if (lb <= 0 && ub >= 0) {
            t = lb;
            if (ub_abs < lb_abs) t = ub;
          } else if (lb == pos_inf || lb == neg_inf) {
            t = ub;
          } else if (ub == pos_inf || ub == neg_inf) {
            t = lb;
          } else {
            t = lb;
            if (ub_abs < lb_abs) t = ub;
          }
          *solx = c * x0 + b * t;
          *soly = c * y0 - a * t;
        } else {
          return false;
        }
        return true;
      }
      return false;
    }
  };

  class StridedWrappedRange : public BaseRange {
  public:
    virtual BaseId getValueID() const { return StridedWrappedRangeId; }

    StridedWrappedRange(APInt lb, APInt ub, unsigned Width)
      : BaseRange(lb, ub, Width, __SIGNED, false),
        __isBottom(false),
        CounterWideningCannotDoubling(0) {}

    StridedWrappedRange(APInt lb, APInt ub, unsigned Width, unsigned long new_stride)
      : BaseRange(lb, ub, Width, __SIGNED, false),
        __isBottom(false),
        CounterWideningCannotDoubling(0) {
      if (lb == ub) setStride(0);
      else          setStride(new_stride);
    }

    StridedWrappedRange(const StridedWrappedRange &other) : BaseRange(other) {
      __isBottom = other.__isBottom;
      CounterWideningCannotDoubling = other.CounterWideningCannotDoubling;
    }

    ~StridedWrappedRange() {}

    static inline APInt WCard(const APInt &x, const APInt &y) {
      if (x == y + 1) return APInt::getMaxValue(x.getBitWidth());
      return (y - x) + 1;
    }

    static inline uint64_t WCard_mod(const APInt &x, const APInt &y) {
      int64_t x_s = x.getSExtValue();
      int64_t y_s = y.getSExtValue();
      y_s = (int64_t)(y_s + 1);
      if (x_s == y_s) {
        uint64_t val_n = APInt::getMaxValue(x.getBitWidth()).getZExtValue();
        return val_n + (uint64_t)1;
      } else {
        APInt ret_val = WCard(x, y);
        if (ret_val == APInt::getMaxValue(x.getBitWidth()))
          return ret_val.getZExtValue();
        return ret_val.getZExtValue();
      }
    }

    inline void normalizeTop() {
      if (isBot()) return;
      if (IsTop()) { setStride(1); return; }

      if (getStride() == 0 && getLB() != getUB()) setStride(1);

      APInt tLB(getWidth() + 1, LB.getZExtValue());
      APInt tUB(getWidth() + 1, UB.getZExtValue());

      if (((tLB == tUB + 1) || (getLB() == (getUB() + 1))) && (getStride() <= 1))
        makeTop();
      else if (LB == UB)
        setStride(0);
    }

    inline void normalize() {
      if (IsTop()) return;
      if (isBot()) return;
      normalizeTop();
    }

    inline uint64_t Cardinality() const {
      if (isBot()) return 0;
      unsigned long curr_str = getStride();
      APInt x = getLB();
      APInt y = getUB();
      if (IsTop() || (x == y + 1)) {
        APInt card = APInt::getMaxValue(width);
        if (curr_str == 0) return card.getZExtValue() + 1;
        return (card.getZExtValue() + 1) / curr_str;
      }
      APInt card = (y - x + 1);
      if (curr_str == 0) return card.getZExtValue();
      return card.getZExtValue() / curr_str;
    }

    virtual bool isGammaSingleton() const {
      if (isBot() || IsTop()) return false;
      APInt card = StridedWrappedRange::WCard(getLB(), getUB());
      return card == 1;
    }

    inline bool isSingleVal() const {
      if (IsTop() || isBot()) return false;
      return getLB().getZExtValue() == getUB().getZExtValue();
    }

    inline bool IsRangeTooBig(const APInt &lb, const APInt &ub) {
      APInt card = StridedWrappedRange::WCard(lb, ub);
      uint64_t n = card.getZExtValue();
      unsigned w = lb.getBitWidth();
      uint64_t Max = (APInt::getMaxValue(w)).getZExtValue() + 1;
      return n >= Max;
    }

    inline void convertWidenBoundsToWrappedRange(const APInt &lb, const APInt &ub) {
      if (IsRangeTooBig(lb, ub)) makeTop();
      else { setLB(lb); setUB(ub); }
    }

    StridedWrappedRange *clone() { return new StridedWrappedRange(*this); }

    static inline bool classof(const StridedWrappedRange *) { return true; }
    static inline bool classof(const BaseRange *V) {
      return V->getValueID() == StridedWrappedRangeId;
    }
    static inline bool classof(const AbstractValue *V) {
      return V->getValueID() == StridedWrappedRangeId;
    }

    virtual bool isBot() const;
    virtual bool IsTop() const;
    virtual void makeBot();
    virtual void makeTop();
    virtual void print(raw_ostream &Out) const;
    void AdjustStride();

    inline void WrappedRangeAssign(StridedWrappedRange *other) {
      BaseRange::RangeAssign(other);
      __isBottom = other->__isBottom;
    }

    static std::vector<StridedWrappedRangePtr> ssplit(const APInt &, const APInt &, unsigned);
    static std::vector<StridedWrappedRangePtr> strided_ssplit(const APInt &, const APInt &, unsigned, unsigned long);
    static std::vector<StridedWrappedRangePtr> nsplit(const APInt &, const APInt &, unsigned);
    static std::vector<StridedWrappedRangePtr> strided_nsplit(const APInt &, const APInt &, unsigned, unsigned long);

    static bool minimal_common_integer(StridedWrappedRange *Op1, StridedWrappedRange *Op2, APInt *result);
    static bool minimal_common_integer_splitted(StridedWrappedRange *Op1, StridedWrappedRange *Op2, APInt *result);
    static std::vector<StridedWrappedRangePtr> MultiValueIntersection(StridedWrappedRange *Op1, StridedWrappedRange *Op2);
    static bool StridedGeneralizedJoin(std::vector<AbstractValue *> Values, StridedWrappedRange *result);

    static StridedWrappedRange StridedLogicalBitwiseOr(StridedWrappedRange *Op1, StridedWrappedRange *Op2);
    static StridedWrappedRange StridedLogicalBitwiseNot(StridedWrappedRange *Op1);

    static StridedWrappedRange StridedShl (StridedWrappedRange *Op, uint64_t val);
    static StridedWrappedRange StridedAShr(StridedWrappedRange *Op, uint64_t val);
    static StridedWrappedRange StridedLShr(StridedWrappedRange *Op, uint64_t val);

    bool WrappedMember(const APInt &) const;

    virtual bool hasNoZero() const {
      APInt zero(width, 0);
      return !this->isBot() && !this->WrappedMember(zero);
    }

    bool WrappedlessOrEqual(AbstractValue *);
    virtual bool lessOrEqual(AbstractValue *);
    virtual void WrappedJoin(AbstractValue *);
    virtual void join(AbstractValue *);
    virtual void GeneralizedJoin(std::vector<AbstractValue *>);
    virtual void meet(AbstractValue *, AbstractValue *);
    virtual bool isEqual(AbstractValue *);

    virtual bool isIdentical(AbstractValue *V);

    void WrappedPlus(StridedWrappedRange *,
                     const StridedWrappedRange *, const StridedWrappedRange *);
    void WrappedMinus(StridedWrappedRange *,
                      const StridedWrappedRange *, const StridedWrappedRange *);
    void WrappedMultiplication(StridedWrappedRange *,
                               const StridedWrappedRange *, const StridedWrappedRange *);
    void WrappedDivision(StridedWrappedRange *,
                         const StridedWrappedRange *, const StridedWrappedRange *, bool);
    void WrappedRem(StridedWrappedRange *,
                    const StridedWrappedRange *, const StridedWrappedRange *, bool);

    void WrappedLogicalBitwise(StridedWrappedRange *,
                               StridedWrappedRange *, StridedWrappedRange *,
                               unsigned);

    void StridedWrappedBitwiseShitfs(StridedWrappedRange *,
                                     StridedWrappedRange *, StridedWrappedRange *,
                                     unsigned);

  private:
    bool __isBottom;
    unsigned int CounterWideningCannotDoubling;

    inline void resetBottomFlag() { __isBottom = false; }

    void Binary_WrappedJoin(StridedWrappedRange *R1, StridedWrappedRange *R2);
  };

  inline raw_ostream &operator<<(raw_ostream &o, StridedWrappedRange r) {
    (void)r;
    return o;
  }

  StridedWrappedRange StridedWrappedMeet(StridedWrappedRange *, StridedWrappedRange *);

  inline bool IsMSBOneSI (const APInt &x) { return  x.isNegative(); }
  inline bool IsMSBZeroSI(const APInt &x) { return !x.isNegative(); }

  inline bool SILex_LessThan(const APInt &x, const APInt &y) {
    bool a = !x.isNegative();
    bool b = !y.isNegative();
    if (!a &&  b) return false;
    if ( a && !b) return true;
    if (!a && !b) return x.slt(y);
    return x.ult(y);
  }

  inline bool SILex_LessOrEqual(const APInt &x, const APInt &y) {
    bool a = !x.isNegative();
    bool b = !y.isNegative();
    if (!a &&  b) return false;
    if ( a && !b) return true;
    if (!a && !b) return x.sle(y);
    return x.ule(y);
  }

  inline APInt Lex_maxSI(const APInt &x, const APInt &y) {
    return SILex_LessOrEqual(x, y) ? y : x;
  }

  inline StridedWrappedRange
  simkSmallerInterval(const APInt &x, const APInt &y, unsigned width_) {
    StridedWrappedRange R1(x, x, width_);
    StridedWrappedRange R2(y, y, width_);
    R1.join(&R2);
    return R1;
  }

}

#endif

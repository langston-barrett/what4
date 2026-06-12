// Vendored from sasi/include/BaseRange.h
// SASI-PRECISION: replaced llvm/* includes with llvm_stubs.h, removed
// LLVM-IR-typed constructors and helpers (checkCastingOp, checkOpWithShift,
// bridge_*) that we never call. Bitwise helper free-functions stay because
// StridedWrappedRange uses them.

#ifndef SASI_PRECISION_BASE_RANGE_H
#define SASI_PRECISION_BASE_RANGE_H

#include "AbstractValue.h"
#include "llvm_stubs.h"

using namespace llvm;

namespace unimelb {

  class BaseRange : public AbstractValue {
  protected:
    APInt LB, UB;
    unsigned width;
    bool isSigned;
    bool __isTop;
    unsigned long stride_val;
  public:
    // Constructor for APInt's only — the only one we use.
    BaseRange(APInt lb, APInt ub, unsigned Width, bool IsSigned, bool isLattice)
      : AbstractValue(isLattice), __isTop(false) {
      isSigned = IsSigned;
      width = Width;
      setLB(lb);
      setUB(ub);
      if (lb == ub) setStride(0);
      else          setStride(1);
    }

    BaseRange(const BaseRange &I) : AbstractValue(I) {
      width    = I.width;
      isSigned = I.isSigned;
      setLB(I.LB);
      setUB(I.UB);
      __isTop = I.__isTop;
      setStride(I.getStride());
    }

    unsigned long getStride() const { return stride_val; }
    void setStride(unsigned long new_stride) { stride_val = new_stride; }

    virtual ~BaseRange() {}

    inline const APInt &getUB() const { return UB; }
    inline const APInt &getLB() const { return LB; }

    inline unsigned getWidth() { return width; }
    inline bool IsSigned() const { return isSigned; }

    inline bool IsConstantRange() const {
      if (isBot()) return false;
      if (IsTop()) return false;
      return LB == UB;
    }
    inline bool IsZeroRange() const { return (LB == UB && LB == APInt(width, 0)); }

    inline APInt getMaxValue() {
      return isSigned ? APInt::getSignedMaxValue(width) : APInt::getMaxValue(width);
    }
    inline APInt getMinValue() {
      return isSigned ? APInt::getSignedMinValue(width) : APInt::getMinValue(width);
    }

    static inline bool IsSignedCompInst(unsigned Opcode) {
      switch (Opcode) {
      case ICmpInst::ICMP_SLE:
      case ICmpInst::ICMP_SLT:
      case ICmpInst::ICMP_SGE:
      case ICmpInst::ICMP_SGT:
        return true;
      default:
        return false;
      }
    }

    virtual inline void setLB(APInt lb)    { LB = lb; }
    virtual inline void setUB(APInt ub)    { UB = ub; }
    virtual inline void setLB(uint64_t lb) { LB = APInt(width, lb); }
    virtual inline void setUB(uint64_t ub) { UB = APInt(width, ub); }

    inline void setSign(bool IsSigned_) { isSigned = IsSigned_; }

    virtual bool hasNoZero() const { return false; }

    inline void RangeAssign(BaseRange *V) {
      setLB(V->getLB());
      setUB(V->getUB());
      __isTop = V->IsTop();
      setStride(V->getStride());
    }

    inline void resetTopFlag() { __isTop = false; }

    virtual bool IsTop() const;
    virtual void makeTop();
    virtual void print(raw_ostream &) const;

    virtual bool isIdentical(AbstractValue *V);

    void printRange(raw_ostream &) const;

    static APInt smin(const APInt &x, const APInt &y) { return x.slt(y) ? x : y; }
    static APInt smax(const APInt &x, const APInt &y) { return x.sgt(y) ? x : y; }
    static APInt umin(const APInt &x, const APInt &y) { return x.ult(y) ? x : y; }
    static APInt umax(const APInt &x, const APInt &y) { return x.ugt(y) ? x : y; }
  };

  // Bitwise helpers that StridedWrappedRange relies on.
  APInt minOr (const APInt&, const APInt&, const APInt&, const APInt&);
  APInt maxOr (const APInt&, const APInt&, const APInt&, const APInt&);
  APInt minAnd(APInt, const APInt&, APInt, const APInt&);
  APInt maxAnd(const APInt&, APInt, const APInt&, APInt);
  APInt minXor(const APInt&, const APInt&, const APInt&, const APInt&);
  APInt maxXor(const APInt&, const APInt&, const APInt&, const APInt&);

  void unsignedOr (BaseRange *, BaseRange *, APInt &lb, APInt &ub);
  void unsignedAnd(BaseRange *, BaseRange *, APInt &lb, APInt &ub);
  void unsignedXor(BaseRange *, BaseRange *, APInt &lb, APInt &ub);

  unsigned long NumContZeros(unsigned long val);
  unsigned long NumOnes(unsigned long val);

}

#endif

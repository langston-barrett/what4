// Minimal LLVM stubs for the standalone sasi-precision build.
//
// We vendor sasi's StridedWrappedRange transfer functions verbatim. Those
// functions touch:
//
//   * `llvm::APInt`        — pervasive in the math.
//   * IR types             — only in dispatch glue we delete or never call.
//   * `cast<T>` / `dyn_cast<T>` / `llvm_unreachable`
//   * `STATISTIC` / `DEBUG` / `dbgs()` / `raw_ostream`
//
// This header replaces the `llvm/...` includes with a header-only shim:
// a width-tagged uint64_t APInt that supports the small surface the .cpp
// uses, plus empty stubs / passthroughs for the rest.

#ifndef SASI_PRECISION_LLVM_STUBS_H
#define SASI_PRECISION_LLVM_STUBS_H

#include <cassert>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>

namespace llvm {

class APInt {
public:
  APInt() : bw_(0), val_(0) {}

  APInt(unsigned width, uint64_t v, bool /*isSigned*/ = false)
    : bw_(width), val_(maskTo(v, width)) {}

  // Allow implicit assignment from uint64_t (used widely with setLB/setUB).
  APInt &operator=(uint64_t v) {
    val_ = maskTo(v, bw_);
    return *this;
  }

  unsigned getBitWidth() const { return bw_; }

  uint64_t getZExtValue() const { return val_; }

  int64_t getSExtValue() const {
    if (bw_ == 0) return 0;
    if (bw_ >= 64) return static_cast<int64_t>(val_);
    uint64_t signBit = 1ull << (bw_ - 1);
    if (val_ & signBit)
      return static_cast<int64_t>(val_) - static_cast<int64_t>(1ull << bw_);
    return static_cast<int64_t>(val_);
  }

  bool getBoolValue() const { return val_ != 0; }

  std::string toString(unsigned /*radix*/, bool isSigned) const {
    std::ostringstream os;
    if (isSigned) os << getSExtValue();
    else os << getZExtValue();
    return os.str();
  }

  static APInt getMaxValue(unsigned width) {
    return APInt(width, mask(width));
  }
  static APInt getMinValue(unsigned width) {
    return APInt(width, 0);
  }
  static APInt getSignedMaxValue(unsigned width) {
    if (width == 0) return APInt(0, 0);
    return APInt(width, mask(width) >> 1);
  }
  static APInt getSignedMinValue(unsigned width) {
    if (width == 0) return APInt(0, 0);
    return APInt(width, 1ull << (width - 1));
  }
  static APInt getNullValue(unsigned width) {
    return APInt(width, 0);
  }
  static APInt getOneBitSet(unsigned width, unsigned bit) {
    return APInt(width, 1ull << bit);
  }

  // Width predicates.
  bool isMaxValue() const { return val_ == mask(bw_); }
  bool isMinValue() const { return val_ == 0; }
  bool isMaxSignedValue() const { return val_ == (mask(bw_) >> 1); }
  bool isMinSignedValue() const { return bw_ != 0 && val_ == (1ull << (bw_ - 1)); }
  bool isNegative() const {
    if (bw_ == 0) return false;
    return (val_ >> (bw_ - 1)) & 1ull;
  }

  // Arithmetic.
  APInt operator+(const APInt &o) const { return APInt(bw_, val_ + o.val_); }
  APInt operator-(const APInt &o) const { return APInt(bw_, val_ - o.val_); }
  APInt operator*(const APInt &o) const { return APInt(bw_, val_ * o.val_); }

  APInt operator+(uint64_t k) const { return APInt(bw_, val_ + k); }
  APInt operator-(uint64_t k) const { return APInt(bw_, val_ - k); }

  APInt operator-() const { return APInt(bw_, (~val_ + 1ull) & mask(bw_)); }

  APInt &operator+=(const APInt &o) { val_ = maskTo(val_ + o.val_, bw_); return *this; }
  APInt &operator-=(const APInt &o) { val_ = maskTo(val_ - o.val_, bw_); return *this; }

  APInt udiv(const APInt &o) const {
    assert(o.val_ != 0);
    return APInt(bw_, val_ / o.val_);
  }
  APInt urem(const APInt &o) const {
    assert(o.val_ != 0);
    return APInt(bw_, val_ % o.val_);
  }
  APInt sdiv(const APInt &o) const { bool _; return sdiv_ov(o, _); }

  APInt sdiv_ov(const APInt &o, bool &overflow) const {
    overflow = false;
    int64_t a = getSExtValue();
    int64_t b = o.getSExtValue();
    assert(b != 0);
    // INT_MIN / -1 overflows.
    if (bw_ != 0 && a == static_cast<int64_t>(1ull << (bw_ - 1)) - (1ll << bw_)
        && b == -1) {
      overflow = true;
    }
    int64_t r = a / b;
    return APInt(bw_, static_cast<uint64_t>(r));
  }

  APInt umul_ov(const APInt &o, bool &overflow) const {
    __uint128_t prod = static_cast<__uint128_t>(val_) * static_cast<__uint128_t>(o.val_);
    __uint128_t cap = (bw_ == 0) ? 0 : (__uint128_t{1} << bw_);
    overflow = (bw_ != 0 && prod >= cap);
    return APInt(bw_, static_cast<uint64_t>(prod));
  }

  APInt smul_ov(const APInt &o, bool &overflow) const {
    int64_t a = getSExtValue();
    int64_t b = o.getSExtValue();
    __int128_t prod = static_cast<__int128_t>(a) * static_cast<__int128_t>(b);
    if (bw_ == 0) { overflow = false; return APInt(0, 0); }
    __int128_t hi = static_cast<__int128_t>(1) << (bw_ - 1);
    overflow = (prod >= hi || prod < -hi);
    return APInt(bw_, static_cast<uint64_t>(prod));
  }

  // Bitwise.
  APInt operator~() const { return APInt(bw_, ~val_); }
  APInt operator&(const APInt &o) const { return APInt(bw_, val_ & o.val_); }
  APInt operator|(const APInt &o) const { return APInt(bw_, val_ | o.val_); }
  APInt operator^(const APInt &o) const { return APInt(bw_, val_ ^ o.val_); }

  APInt operator<<(unsigned n) const {
    if (n >= bw_) return APInt(bw_, 0);
    return APInt(bw_, val_ << n);
  }
  APInt shl(unsigned n) const { return *this << n; }

  APInt lshr(unsigned n) const {
    if (n >= bw_) return APInt(bw_, 0);
    return APInt(bw_, val_ >> n);
  }

  APInt ashr(unsigned n) const {
    if (bw_ == 0) return *this;
    if (n >= bw_) n = bw_ - 1;
    int64_t s = getSExtValue();
    int64_t r = s >> n;
    return APInt(bw_, static_cast<uint64_t>(r));
  }

  // Comparisons.
  bool operator==(const APInt &o) const { return val_ == o.val_; }
  bool operator!=(const APInt &o) const { return val_ != o.val_; }
  bool operator==(uint64_t k) const { return val_ == maskTo(k, bw_); }
  bool operator!=(uint64_t k) const { return val_ != maskTo(k, bw_); }

  bool ult(const APInt &o) const { return val_ < o.val_; }
  bool ule(const APInt &o) const { return val_ <= o.val_; }
  bool ugt(const APInt &o) const { return val_ > o.val_; }
  bool uge(const APInt &o) const { return val_ >= o.val_; }
  bool ult(uint64_t k) const { return val_ < maskTo(k, bw_); }
  bool ule(uint64_t k) const { return val_ <= maskTo(k, bw_); }
  bool ugt(uint64_t k) const { return val_ > maskTo(k, bw_); }
  bool uge(uint64_t k) const { return val_ >= maskTo(k, bw_); }

  bool slt(const APInt &o) const { return getSExtValue() < o.getSExtValue(); }
  bool sle(const APInt &o) const { return getSExtValue() <= o.getSExtValue(); }
  bool sgt(const APInt &o) const { return getSExtValue() > o.getSExtValue(); }
  bool sge(const APInt &o) const { return getSExtValue() >= o.getSExtValue(); }
  bool slt(uint64_t k) const { return getSExtValue() < static_cast<int64_t>(k); }

private:
  unsigned bw_;
  uint64_t val_;

  static uint64_t mask(unsigned bw) {
    if (bw == 0) return 0;
    if (bw >= 64) return ~uint64_t{0};
    return (uint64_t{1} << bw) - 1;
  }
  static uint64_t maskTo(uint64_t v, unsigned bw) { return v & mask(bw); }
};

// Stub IR types: we never invoke methods on these, only carry them as
// pointer parameters in vendored signatures we don't call.
class Value;
class BasicBlock;
class Function;
class Module;
class Type;
class TBool;
class ConstantInt;

class Instruction {
public:
  enum BinaryOps {
    Add, Sub, Mul, UDiv, SDiv, URem, SRem,
    And, Or, Xor,
    Shl, LShr, AShr,
    Trunc, SExt, ZExt
  };
};

class ICmpInst {
public:
  enum Predicate {
    ICMP_EQ, ICMP_NE,
    ICMP_ULT, ICMP_ULE, ICMP_UGT, ICMP_UGE,
    ICMP_SLT, ICMP_SLE, ICMP_SGT, ICMP_SGE
  };
};

// raw_ostream stub — eats everything.
class raw_ostream {
public:
  template <typename T> raw_ostream &operator<<(const T &) { return *this; }
};
inline raw_ostream &dbgs() { static raw_ostream s; return s; }
inline raw_ostream &errs() { static raw_ostream s; return s; }
inline raw_ostream &outs() { static raw_ostream s; return s; }

// cast / dyn_cast — identity at our scale; every cast in the .cpp is
// from an `AbstractValue*` that *is* a `StridedWrappedRange*`.
template <typename T, typename U> T *cast(U *v) { return static_cast<T *>(v); }
template <typename T, typename U> T *dyn_cast(U *v) { return static_cast<T *>(v); }

[[noreturn]] inline void llvm_unreachable_internal(const char *msg = "") {
  std::cerr << "llvm_unreachable: " << msg << "\n";
  std::abort();
}

} // namespace llvm

// Macros used in sasi: redefine to no-ops where appropriate.
#ifndef llvm_unreachable
#define llvm_unreachable(msg) ::llvm::llvm_unreachable_internal(msg)
#endif

#define DEBUG(X) do { } while (0)
#define DEBUG_TYPE(x)
#define STATISTIC(NAME, DESC) static unsigned long NAME = 0

#endif // SASI_PRECISION_LLVM_STUBS_H

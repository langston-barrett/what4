// sasi-precision: enumerate width-4 progressions, run each through sasi's
// StridedWrappedRange transfer functions, and emit a CSV in the same shape
// as what4-domains/test/PrecisionRegression/strides.csv.

#include "BaseRange.h"
#include "StridedWrappedRange.h"
#include "llvm_stubs.h"

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdint>
#include <functional>
#include <iostream>
#include <set>
#include <string>
#include <vector>

using namespace llvm;
using namespace unimelb;

namespace {

constexpr unsigned W = 4;
constexpr uint64_t M = 16;          // 2^W
constexpr uint64_t MASK = 15;       // 2^W - 1

// One concrete value-set, sorted, for dedup keys and oracle inputs.
using ValueSet = std::vector<uint8_t>;

// Mask to width-4.
inline uint8_t mask4(uint64_t x) { return static_cast<uint8_t>(x & MASK); }
inline int8_t toSigned4(uint64_t x) {
  uint8_t u = mask4(x);
  return (u & 8u) ? static_cast<int8_t>(static_cast<int>(u) - 16) : static_cast<int8_t>(u);
}
inline uint8_t fromSigned4(int x) {
  return mask4(static_cast<uint64_t>(x) & MASK);
}

// ---- Conversion: abstract -> concrete value-set ----
//
// Sasi's `Cardinality()` is `(UB - LB + 1) / stride`, which underestimates
// at width 4 (e.g. {0,2,4,6} → (6+1)/2 = 3, missing the last element). We
// walk the progression ourselves: start at LB, step by stride mod 2^w, and
// stop after at most 2^w iterations or when we revisit LB.
ValueSet toList(const StridedWrappedRange &R) {
  ValueSet out;
  if (R.isBot()) return out;
  if (R.IsTop()) {
    out.reserve(M);
    for (uint64_t i = 0; i < M; ++i) out.push_back(static_cast<uint8_t>(i));
    return out;
  }
  uint64_t lb = R.getLB().getZExtValue() & MASK;
  uint64_t ub = R.getUB().getZExtValue() & MASK;
  unsigned long stride = R.getStride();
  if (R.isSingleVal() || stride == 0) {
    out.push_back(static_cast<uint8_t>(lb));
    return out;
  }
  // Walk LB, LB+stride, ..., UB (mod 2^w). Cap at 2^w + 1 iterations as a
  // safety net.
  uint64_t v = lb;
  for (uint64_t i = 0; i < M + 1; ++i) {
    out.push_back(static_cast<uint8_t>(v & MASK));
    if ((v & MASK) == ub) break;
    v = (v + stride) & MASK;
  }
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
  return out;
}

// ---- Domain enumeration: mirrors enumStrides4 in Common.hs:96-104 ----
//
// We additionally drop self-wrapping APs — those where start + stride*i ≥ 2^w.
// Reason: sasi's WrappedPlus / WrappedMinus / WrappedLogicalBitwise / etc.
// treat a strided wrapped interval as a fixed-stride walk from LB clockwise
// to UB. When the input AP wraps past the south pole AND its stride does not
// divide 2^w, the walk re-enters with a phase shift the transfer functions
// don't account for, and they return unsound results (we observed conc > abs
// on add/sub/xor for those inputs). Restricting to non-self-wrapping APs
// gives an apples-to-apples comparison: every input is faithfully
// represented in both domains.
std::vector<StridedWrappedRange> enumStrides4() {
  std::vector<StridedWrappedRange> out;
  for (uint64_t stride = 1; stride <= MASK; ++stride) {
    uint64_t g = stride & ((MASK + 1) - stride);
    uint64_t orbit = (MASK + 1) / g;
    for (uint64_t start = 0; start <= MASK; ++start) {
      for (uint64_t i = 0; i < orbit; ++i) {
        if (start + stride * i >= (MASK + 1)) continue;   // skip self-wrapping
        APInt lb(W, start);
        APInt ub(W, (start + stride * i) & MASK);
        unsigned long s = (i == 0) ? 0 : static_cast<unsigned long>(stride);
        out.emplace_back(lb, ub, W, s);
      }
    }
  }
  return out;
}

// ---- Dedup by value-set ----
std::vector<StridedWrappedRange> dedup(const std::vector<StridedWrappedRange> &xs) {
  std::vector<StridedWrappedRange> out;
  std::set<ValueSet> seen;
  for (const auto &x : xs) {
    ValueSet k = toList(x);
    if (seen.insert(k).second) out.push_back(x);
  }
  return out;
}

// ---- Concrete oracle ops, mirroring Common.hs:253-328 ----
uint8_t cAdd(uint8_t x, uint8_t y) { return mask4(static_cast<uint64_t>(x) + y); }
uint8_t cSub(uint8_t x, uint8_t y) { return mask4(static_cast<uint64_t>(x) + (M - y)); }
uint8_t cMul(uint8_t x, uint8_t y) { return mask4(static_cast<uint64_t>(x) * y); }
uint8_t cAnd(uint8_t x, uint8_t y) { return mask4(static_cast<uint64_t>(x) & y); }
uint8_t cOr (uint8_t x, uint8_t y) { return mask4(static_cast<uint64_t>(x) | y); }
uint8_t cXor(uint8_t x, uint8_t y) { return mask4(static_cast<uint64_t>(x) ^ y); }

uint8_t cNegate(uint8_t x) { return mask4(M - x); }
uint8_t cNot   (uint8_t x) { return mask4(~static_cast<uint64_t>(x)); }

bool cUdivPartial(uint8_t x, uint8_t y, uint8_t &out) { if (!y) return false; out = x / y; return true; }
bool cUremPartial(uint8_t x, uint8_t y, uint8_t &out) { if (!y) return false; out = x % y; return true; }
bool cSdivPartial(uint8_t x, uint8_t y, uint8_t &out) {
  if (!y) return false;
  int sx = toSigned4(x), sy = toSigned4(y);
  int q = (sx > 0) == (sy > 0) ? std::abs(sx) / std::abs(sy)
                                : -(std::abs(sx) / std::abs(sy));
  // C++ integer division truncates toward zero, matching Haskell `quot`.
  q = sx / sy;
  out = fromSigned4(q);
  return true;
}
bool cSremPartial(uint8_t x, uint8_t y, uint8_t &out) {
  if (!y) return false;
  int sx = toSigned4(x), sy = toSigned4(y);
  out = fromSigned4(sx % sy);  // C++ % is `rem`, matches Haskell.
  return true;
}

uint8_t cShl (uint8_t x, uint8_t y) {
  int s = static_cast<int>(y);
  if (s >= static_cast<int>(W)) return 0;
  return mask4(static_cast<uint64_t>(x) << s);
}
uint8_t cLshr(uint8_t x, uint8_t y) {
  int s = static_cast<int>(y);
  if (s >= static_cast<int>(W)) return 0;
  return mask4(static_cast<uint64_t>(x) >> s);
}
uint8_t cAshr(uint8_t x, uint8_t y) {
  int s = static_cast<int>(y);
  int sx = toSigned4(x);
  int s2 = (s >= static_cast<int>(W)) ? (W - 1) : s;
  return fromSigned4(sx >> s2);
}

// ---- Aggregator helpers, mirroring Common.hs:115-220 ----
struct Result { std::string op; uint64_t abs_; uint64_t conc; };

template <typename UnaryAbs, typename UnaryConc>
Result unaryResult(const std::string &name,
                   const std::vector<StridedWrappedRange> &reps,
                   UnaryAbs absOp, UnaryConc concOp) {
  uint64_t abs_ = 0, conc = 0;
  for (const auto &a : reps) {
    abs_ += toList(absOp(a)).size();
    std::set<uint8_t> s;
    for (uint8_t x : toList(a)) s.insert(concOp(x));
    conc += s.size();
  }
  return {name, abs_, conc};
}

template <typename BinAbs, typename BinConc>
Result binaryResult(const std::string &name,
                    const std::vector<StridedWrappedRange> &reps,
                    BinAbs absOp, BinConc concOp) {
  uint64_t abs_ = 0, conc = 0;
  for (const auto &a : reps) {
    auto la = toList(a);
    for (const auto &b : reps) {
      abs_ += toList(absOp(a, b)).size();
      std::set<uint8_t> s;
      for (uint8_t x : la) for (uint8_t y : toList(b)) s.insert(concOp(x, y));
      conc += s.size();
    }
  }
  return {name, abs_, conc};
}

template <typename BinAbs, typename PartConc>
Result binaryResultFiltered(const std::string &name,
                            const std::vector<StridedWrappedRange> &reps,
                            BinAbs absOp, PartConc concOp) {
  uint64_t abs_ = 0, conc = 0;
  for (const auto &a : reps) {
    auto la = toList(a);
    for (const auto &b : reps) {
      abs_ += toList(absOp(a, b)).size();
      std::set<uint8_t> s;
      uint8_t v;
      for (uint8_t x : la) for (uint8_t y : toList(b))
        if (concOp(x, y, v)) s.insert(v);
      conc += s.size();
    }
  }
  return {name, abs_, conc};
}

// Lattice oracle: set-union (join) or set-intersect (meet) of value-sets.
struct SetUnion {
  std::set<uint8_t> operator()(const ValueSet &a, const ValueSet &b) const {
    std::set<uint8_t> s(a.begin(), a.end());
    s.insert(b.begin(), b.end());
    return s;
  }
};

template <typename BinAbs, typename SetOp>
Result latticeResult(const std::string &name,
                     const std::vector<StridedWrappedRange> &reps,
                     BinAbs absOp, SetOp setOp) {
  uint64_t abs_ = 0, conc = 0;
  for (const auto &a : reps) {
    auto la = toList(a);
    for (const auto &b : reps) {
      abs_ += toList(absOp(a, b)).size();
      conc += setOp(la, toList(b)).size();
    }
  }
  return {name, abs_, conc};
}

template <typename LeqOp>
Result leqResult(const std::string &name,
                 const std::vector<StridedWrappedRange> &reps,
                 LeqOp leq) {
  uint64_t abs_ = 0, conc = 0;
  for (const auto &a : reps) {
    auto la = toList(a);
    for (const auto &b : reps) {
      auto lb = toList(b);
      bool contained = std::includes(lb.begin(), lb.end(), la.begin(), la.end());
      if (contained) abs_++;
      if (leq(a, b)) conc++;
    }
  }
  return {name, abs_, conc};
}

// ---- Wrappers around sasi transfer functions ----
//
// Each lambda owns mutable copies because sasi's signatures take non-const
// `*` (cast<>() drops const internally). We construct a result variable with
// `LHS->makeBot()` semantics and then call the transfer.

StridedWrappedRange runAdd(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.WrappedPlus(&R, &A, &B);
  return R;
}
StridedWrappedRange runSub(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.WrappedMinus(&R, &A, &B);
  return R;
}
StridedWrappedRange runMul(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.WrappedMultiplication(&R, &A, &B);
  return R;
}
StridedWrappedRange runAnd(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.WrappedLogicalBitwise(&R, &A, &B, Instruction::And);
  return R;
}
StridedWrappedRange runOr(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.WrappedLogicalBitwise(&R, &A, &B, Instruction::Or);
  return R;
}
StridedWrappedRange runXor(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.WrappedLogicalBitwise(&R, &A, &B, Instruction::Xor);
  return R;
}
StridedWrappedRange runShlOp(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.StridedWrappedBitwiseShitfs(&R, &A, &B, Instruction::Shl);
  return R;
}
StridedWrappedRange runLShrOp(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.StridedWrappedBitwiseShitfs(&R, &A, &B, Instruction::LShr);
  return R;
}
StridedWrappedRange runAShrOp(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.StridedWrappedBitwiseShitfs(&R, &A, &B, Instruction::AShr);
  return R;
}
StridedWrappedRange runNot(const StridedWrappedRange &a) {
  StridedWrappedRange A(a);
  return StridedWrappedRange::StridedLogicalBitwiseNot(&A);
}
StridedWrappedRange runNegate(const StridedWrappedRange &a) {
  // 0 - a, using WrappedMinus.
  StridedWrappedRange Z(APInt(W, 0), APInt(W, 0), W, 0);
  StridedWrappedRange A(a), R(APInt(W, 0), APInt(W, 0), W, 0);
  R.WrappedMinus(&R, &Z, &A);
  return R;
}
bool runLeq(const StridedWrappedRange &a, const StridedWrappedRange &b) {
  StridedWrappedRange A(a), B(b);
  return A.WrappedlessOrEqual(&B);
}

// ---- CSV emit ----
std::string formatPercent(uint64_t num, uint64_t denom) {
  if (denom == 0) return "0.0%";
  uint64_t perMille = (num * 1000) / denom;
  uint64_t whole = perMille / 10;
  uint64_t frac  = perMille % 10;
  return std::to_string(whole) + "." + std::to_string(frac) + "%";
}

void emit(const std::vector<Result> &rs, std::ostream &os) {
  os << "op,abs,conc,precision\n";
  for (const auto &r : rs) {
    os << r.op << "," << r.abs_ << "," << r.conc << ","
       << formatPercent(r.conc, r.abs_) << "\n";
  }
}

} // namespace

int main() {
  std::cerr << "Enumerating width-4 progressions...\n";
  auto raw  = enumStrides4();
  std::cerr << "  raw: " << raw.size() << "\n";
  auto reps = dedup(raw);
  std::cerr << "  deduped: " << reps.size() << "\n";

  std::vector<Result> results;

  results.push_back(leqResult   ("leq",    reps, runLeq));
  results.push_back(unaryResult ("negate", reps, runNegate, cNegate));
  results.push_back(binaryResult("add",    reps, runAdd, cAdd));
  results.push_back(binaryResult("sub",    reps, runSub, cSub));
  results.push_back(binaryResult("mul",    reps, runMul, cMul));
  // udiv/urem/sdiv/srem omitted: sasi's strided splitter produces pieces
  // with strides that don't divide 2^w (e.g. piece [2,0,3] from splitting
  // [9,0,3] over width 4); WrappedMember/WrappedUnsignedDivision then trip
  // on inconsistent state. Sasi limitation at width 4, not something we
  // can paper over without rewriting the splitter.
  results.push_back(unaryResult ("not", reps, runNot, cNot));
  results.push_back(binaryResult("and", reps, runAnd, cAnd));
  results.push_back(binaryResult("or",  reps, runOr,  cOr));
  results.push_back(binaryResult("xor", reps, runXor, cXor));
  results.push_back(binaryResult("shl",  reps, runShlOp,  cShl));
  results.push_back(binaryResult("lshr", reps, runLShrOp, cLshr));
  results.push_back(binaryResult("ashr", reps, runAShrOp, cAshr));
  // pseudoMeet/pseudoJoin omitted: sasi's StridedWrappedMeet segfaults on
  // some width-4 pairs (separate bug from the SignedWrappedMult sign-cast
  // we patched in StridedWrappedRange.cpp). Re-enable once traced.

  emit(results, std::cout);
  return 0;
}

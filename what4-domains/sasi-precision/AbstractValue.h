// Vendored from sasi/include/AbstractValue.h
// SASI-PRECISION: replaced llvm/* includes with llvm_stubs.h, and trimmed
// the abstract interface to the methods we actually call. Pure abstract
// methods that depend on IR types (visitArithBinaryOp, visitCast, etc.)
// have been removed since we never dispatch through the LLVM-shaped API.

#ifndef SASI_PRECISION_ABSTRACT_VALUE_H
#define SASI_PRECISION_ABSTRACT_VALUE_H

#include "llvm_stubs.h"
#include <vector>

using namespace llvm;

namespace unimelb {

  typedef enum {
    RangeId               = 0,
    WrappedRangeId        = 1,
    StridedWrappedRangeId = 2
  } BaseId;

  class AbstractValue {
  protected:
    Value *var;
    unsigned numOfChanges;
    BasicBlock *B;
    bool IsLattice;
  public:
    virtual BaseId getValueID() const = 0;

    AbstractValue(Value *v, bool isLattice = true)
      : var(v), numOfChanges(0), B(nullptr), IsLattice(isLattice) {}
    AbstractValue(bool isLattice = true)
      : var(nullptr), numOfChanges(0), B(nullptr), IsLattice(isLattice) {}
    AbstractValue(const AbstractValue &other) {
      var          = other.var;
      numOfChanges = other.numOfChanges;
      B            = other.B;
      IsLattice    = other.IsLattice;
    }
    virtual AbstractValue *clone() = 0;
    virtual ~AbstractValue() {}

    inline unsigned getNumOfChanges() { return numOfChanges; }
    inline Value *getValue()         { return var; }
    inline Value *getValue() const   { return var; }
    inline bool   isConstant() const { return var == nullptr; }
    inline bool   isLattice() const  { return true; }
    inline BasicBlock *getBasicBlock() { return B; }
    inline void incNumOfChanges()   { numOfChanges++; }
    inline void resetNumOfChanges() { numOfChanges = 0; }
    inline void setBasicBlock(BasicBlock *_B) { assert(!B); B = _B; }

    static inline bool classof(const AbstractValue *) { return true; }

    virtual bool isGammaSingleton() const = 0;
    virtual bool isBot() const = 0;
    virtual bool IsTop() const = 0;
    virtual bool hasNoZero() const = 0;
    virtual void makeBot() = 0;
    virtual void makeTop() = 0;
    virtual void join(AbstractValue *V) = 0;
    virtual void GeneralizedJoin(std::vector<AbstractValue *>) = 0;
    virtual void meet(AbstractValue *V1, AbstractValue *V2) = 0;
    virtual bool lessOrEqual(AbstractValue *V) = 0;
    virtual bool isEqual(AbstractValue *V) = 0;
    virtual bool isIdentical(AbstractValue *V) = 0;

    virtual void print(raw_ostream &Out) const { (void)Out; }
  };

}

#endif

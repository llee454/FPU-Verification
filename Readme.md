Readme
======

This package contains a Coq development that verifies that the "rem"
register in Hauser's algorithm for taking the square root of binary
floating point numbers is large enough to store intermediate values
without a loss of precision.

Hauser's algorithm computes both sqrt and division operations, So,
this package presents proofs that his register allocations are
correct for both operations. In addition, when computing square
roots, we must distinguish between the case when exponents are even
and odd. Accordingly, we provide separate proofs covering these
two cases.

See [docs] for informal proofs and background information. See
[verification] for formal proofs.

Organization
------------

* docs
  Documentation explaining the models used to model Hauser's
  algorithm and informal correctness proffs.
* models
  "Deep Specification" models of Hausers algorithm written.
* verfication
  Formal proofs

Approach
--------

We follow a four part process to verify that the registers
allocated by Hauser's algorithm are sufficiently large to store
all intermediate values computed during square root and division
operations:

1. Deep Specification
   Directly model Hauser's Chisel algorithm.
2. Abstract Model
   Identify a set of mathematical recurrence relations that model
   the variables used within Hauser's Chisel algorithm. We ensure
   that their is an bijective mapping from the values computed within
   our equations and the variables defined by Hauser's algorithm.
3. Constraint Translation
   Translate the properties that we want to prove about Hauser's
   algorithm into constraints applying to the values of our abstract
   model. Specifically, we identify an upper bound for our `error`
   value that must be satisfied for Hauser's register allocations
   to be correct.
4. Formal Verification
   Write formal proofs verifying that our model satisfies these
   constraints (and by extension, that Hauser's algorithm satisfies
   the corresponding constraints).

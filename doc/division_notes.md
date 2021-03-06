Our Abstract Binary Floating Point Division Algorithm
=====================================================

Our abstract floating point binary division algorithm accepts two
floating point binary numbers: `a` and `b`; and iteratively generates
an approximations of `a/b`.

By definition the quotient, `q`, of `a` and `b` is the number such that `q * b + r = a`, and `0 <= r < b`.

We assume that `a` and `b` have the form: `1.a0a1...an` and `1.b0b1...bn`, where `ak` and `bk` represent arbitrary bit values.

Our model iteratively generates an approximation, `approx n` for `a/b`. Initially, this approximation equals 0. With each iteration, we either append a 1 or a 0 onto the previous approximation. We determine whether or not we will append a 1, by checking whether or not doing so causes us to overshoot `a`.

Let `approx n` denote the approximation generated by the n-th iteration. Let `bit n` denote the bit append onto our approximation in the n-th iteration. Lastly, let `error n` denote the discrepancy between the product `b * approx n` and `a`.

With these definitions, we can characterize the algorithm using the following set of recurrence relations:

```
approx 0 = 0
approx (n + 1) = approx (n) + bit (n)/2^n

bit (n) = 0 \/ bit (n) = 1

error (n) = a - b * approx (n)
0 <= error (n)
```

From these equations and constraints, we can derive the formula for `bit (n)`:

```
bit (n)
  := if b * (approx (n) + 1/2^n) <= a
       then 1
       else 0
```

We can also derive a recurrence relation for `error (n)` the eliminates any reference to `a`:

```
error (n + 1) = a - b * approx (n + 1)
              = a - b * (approx (n) + bit (n)/2^n)
              = a - b * approx (n) - b * bit (n)/2^n
              = error (n) - b * bit (n)/2^n
```

Corollaries
-----------

```
             0 <= error (n)
               <= a - b * approx (n)
b * approx (n) <= a
    approx (n) <= a/b
    approx (n) <= 2

bit (n) = 1 -> b * approx (n) + 1/2^n <= a
                           approx (n) <= 1/b * (a - 1/2^n)
                           approx (n) <= 2 - 1/2^n

bit (n) = 0 -> a < b * (approx (n) + 1/2^n)
               a/b - 1/2^n < approx (n)

0 <= approx (n) <= approx (n+1) <= a/b < approx (n) + 2/2^n
n = 0:
  a/b < approx (0) + 2/2^0
  a/b < 2
  holds because a < 2, and b >= 1.
n + 1:
  given: a/b < approx (n) + 2/2^n
  goal: a/b < approx (n + 1) + 2/2^(n + 1)
            < approx (n) + bit (n)/2^n + 1/2^n
  bit (n) = 0:
    holds by bit (n) = 0 rule, which asserts that a/b < approx (n) + 1/2^n
  bit (n) = 1:
    goal: a/b < approx (n) + 1/2^n + 1/2^n
              < approx (n) + 2/2^n
    assumption.
  
approx (n) <= 1/2^n * (2^(n + 1) - 1)

a/b < approx (n) + 2/2^n
a < b * approx (n) + b * 2/2^n
a - b * approx (n) < b * 2/2^n
error (n) < b * 2/2^n
          < 2 * 2/2^n
          < 4/2^n
```

Proving that the rem Register is Sufficiently Wide
--------------------------------------------------

Our algorithm is a reference model for Hauser's floating point division algorithm. Murali, has provided a model of Hauser's algorithm along with a mapping between te variables defined in his reference algorithm and Hauser's.

Murali asked me to verify that the number of bits associated with Hauser's rem register is sufficient to hold any intermediate value without a loss of precision.

Hauser allocated two extra bits beyond those used by `a` and `b`. This means that his register is sufficient provided that it does not store a value greater than 4.

Mapping this constraint onto our model, we find that it is equivalent to requiring that: `forall n : nat, error (n) < 8/2^n`

Proof
-----

```
a/b < approx (n) + 2/2^n
n = 0:
  a/b < approx (0) + 2/2^0
  a/b < 2
  holds because a < 2, and b >= 1.
n + 1:
  given: a/b < approx (n) + 2/2^n
  goal: a/b < approx (n + 1) + 2/2^(n + 1)
            < approx (n) + bit (n)/2^n + 1/2^n
  bit (n) = 0:
    holds by bit (n) = 0 rule, which asserts that a/b < approx (n) + 1/2^n
  bit (n) = 1:
    goal: a/b < approx (n) + 1/2^n + 1/2^n
              < approx (n) + 2/2^n
    assumption.
```

```
a/b < approx (n) + 2/2^n
a < b * approx (n) + b * 2/2^n
a - b * approx (n) < b * 2/2^n
error (n) < b * 2/2^n
          < 2 * 2/2^n
          < 4/2^n
```

Proving that the Algorithm is Correct
------------------------------------------

To prove that the algorithm is correct, we must show that it converges to the true quotient. To do this, we can use a fundamental result from real analysis which states that any bounded monotonically increasing sequence converges to its bound.

This theorem is represented by Coq's `Un_cv` predicate.

```
Definition Un_cv
  := fun (Un : nat -> R) (l : R)
      => forall eps : R,
           (eps > 0)%R ->
           exists N : nat, forall n : nat, n >= N -> (R_dist (Un n) l < eps)%R
  : (nat -> R) -> R -> Prop
```

The correctness statement for the division algorithm is:

```
Theorem spec_is_correct : Un_cv approx (a/b).
```

expanding this goal gives:

```
forall eps : R, eps > 0 ->
  exists n : nat, (forall m : nat, n <= m -> R_dist (approx n) (a/b) < eps).
```

This means that, given a value for `eps` we must return a value for `n` such that `Rabs (approx n - a/b)) < eps`.

We know that:

```
         error n < 4/2^n
a - b * approx n < 4/2^n
  a/b - approx n < 1/b * 4/2^n
|approx n - a/b| < 1/b * 4/2^n
```

From this, we can easily derive a value for `n` such that `|approx n - a/b| < eps`. To do so, simply equate `eps = 1/b * 4/2^n` and solve for n. Doing so gives:

```
          eps = 1/b * 4/2^n
2^n * b * eps = 4
          2^n = 4/(b * eps)
            n = log2 (4) - log2 (b * eps)
            n = 2 - log2 (b) - log2 (eps)
```

The Remainder Register Width Proof Sketch
=========================================

The square root operation is applied to numbers written in binary scientific notation. All numbers are represented using two numbers: a mantissa and an exponent.

given a number: a = mantissa * 2^exponent, we take the square root as follows: sqrt (mantissa) * 2^(exponent/2).

When the exponent is odd - i.e. exists k, exponent = 2 * k + 1 - this calculation produces the following result: sqrt (mantissa) * 2^k * sqrt(2) = sqrt(2 * mantissa) * 2^k.

Consequently, we distinguish between two cases: when exponent is an even number and when exponent is an odd number.

We use a normalized representation where mantissa always has the form 1.bbb... where the b's denote arbitrary bits. We exclude that case where the number being rooted is 0.

Our algorithm
-------------

Our algorithm essentially generates an approximation value for the square root of mantissa, denoted `a`, by iteratively adding bits to the end of an approximation, denoted `approx`. In each iteration, we check to see whether or not we can append a 1 to the current approximation. If we can, we append a 1 and continue. Otherwise we append a 0 and continue.

Our algorithm can be summarized by the following recurrence equations:

```
a = approx (n)^2 + error (n)

approx (0) = 0
approx (n + 1) = approx (n) + b (n)/2^n

0 <= error (n)
b (n) in {0, 1}
```

From these equations, we can derive the equation for `b (n)`:

```
b (n) := if 1/2^n*(2*approx (n) + 1/2^n) <= error (n)
           then 1
           else 0
```

We can then derive the equation for `error (n)`:

```
error (0) = a
error (n + 1) = error (n) - b (n)/2^n*(2*approx (n) + b (n)/2^n)
```

Because `a` has the form 1.bbb..., we can assume:

```
1 <= a < 2
```

From these equations, we can derive the following corollaries:

```
0 <= approx (n) < 2
forall n : nat, b (n) = 0 -> error (n) < 1/2^n*(2*approx (n) + 1/2^n)
forall n : nat, b (n) = 1 -> 1/2^n*(2*approx (n) + 1/2^n) <= error (n)
```

A Lower Bound Constraint for Approx (n) and an Upper Bound Constraint on A
--------------------------------------------------------------------------

The following lemma establishes an important lower bound constraint for `approx (n)`.

```
Lemma approx_lower_bound : forall n : nat, a < (approx (n) + 2/2^n)^2
```

We proceed using a proof by induction. When n = 0, substitution gives:

```
a < (approx (0) + 2/2^0)^2
a < 4
```

In the inductive step, we have to prove: forall n : nat, a < (approx (n) + 2/2^n)^2 -> a < (approx (n + 1) + 1/2^n)^2.
Expanding our goal gives:

```
a < (approx (n) + b (n)/2^n + 1/2^n)^2
```

We proceed by case analysis. `b (n)` either equals 0 or 1.

### b (n) = 0

When b (n) = 0, our goal becomes: `a < (approx (n) + 1/2^n)^2`.

Our proof is as follows:

```
a = approx (n)^2 + error (n)
a < approx (n)^2 + 1/2^n*(2*approx (n) + 1/2^n)    because error (n) < ... when b (n) = 0.
a < (approx (n) + 1/2^n)^2
```

### b (n) = 1

When b (n) = 1, our goal becomes: `a < (approx (n) + 1/2^n + 1/2^n)^2`

But this is equivalent to, `a < (approx (n) + 2/2^n)^2`, which is identical to the inductive hypothesis.

Qed.

A Constant Upper Bound Constraint on Error (n)
----------------------------------------------

We can demonstrate that `forall n: nat, error (n) < 4`, we will need this upper bound when proving our primary theorem below.

Again we proceed using proof by induction. 

### n = 0

Our goal is: `error (0) < 4`. 

Our proof is:

```
error (0) = a - approx (0)^2
error (0) < 2 - 0
error (0) < 2
and 2 <= 4
```

### n + 1

Our goal is: `forall n : nat, error (n) < 4 -> error (n + 1) < 4`. This follows immediately because `forall n : nat, error (n + 1) <= error (n)`. Here we expand `error (n + 1)`:

```
error (n + 1) = error (n) - b (n)/2^n*(2*approx (n) + b (n)/2^n)
error (n + 1) < 4 - 0   maximizing the rhs using the inductive hypothesis and b (n) = 0
error (n + 1) < 4
and 4 <= 4
```

A Scaling Upper Bound Constraint for Error (n)
----------------------------------------------

We will also use the following tight upper bound for `error (n)`

```
a < (approx (n) + 2/2^n)^2
a < approx (n)^2 + 4/2^n*(approx (n) + 1/2^n)
a - approx (n)^2 < 4/2^n*(approx (n) + 1/2^n)
error (n) < 4/2^n*(approx (n) + 1/2^n)
```

Proving that the Rem Register Width is Sufficient for Numbers with Even Exponents
---------------------------------------------------------------------------------

To prove that the number of bits allocated to the Rem Register is sufficient to hold the error values generated for numbers with even exponents, we have to verify that:
`forall n : nat, error (n) < 8/2^n`.

We can prove the following upper bound in this case:

```
approx (n)^2 = a - error (n)
approx (n)^2 < 2 - 0  maximizing the rhs.
approx (n) < 2^(1/2)
```

We can substitute this upper bound into our scaling upper bound for error (n):

```
error (n) < 4/2^n*(approx (n) + 1/2^n)
error (n) < 4/2^n*(2^(1/2) + 1/2^n)
```

Now this upper bound is less than 8/2^n for all n > 0, but fails when n = 0.

Fortunately, for n = 0, we can simply using the constant upper bound for error (0).

This completes the proof.

Proving that the Rem Register width is Sufficient for Numbers with Odd Exponents
--------------------------------------------------------------------------------

When the exponent is odd, we have to store a larger value in the error register. As noted above, the value stored is `2a` rather than `a`. 

The fundamental equations become:

```
2*a = approx (n)^2 + error (n)

approx (0) = 0
approx (n + 1) = approx (n) + b (n)/2^n

0 <= error (n)
b (n) in {0, 1}
```

The derived equations become:

```
b (n) := if 1/2^n*(2*approx (n) + 1/2^n) <= error (n)
           then 1
           else 0

error (0) = 2*a
error (n + 1) = error (n) - b (n)/2^n*(2*approx (n) + b (n)/2^n)

0 <= approx (n) < 2
forall n : nat, b (n) = 0 -> error (n) < 1/2^n*(2*approx (n) + 1/2^n)
forall n : nat, b (n) = 1 -> 1/2^n*(2*approx (n) + 1/2^n) <= error (n)
```

The lemmas proved above hold. To derive them we need only substitute `2*a` for `a` in the original proofs.

```
forall n : nat, 2*a < (approx (n) + 2/2^n)^2
forall n : nat, error (n) < 4
forall n : nat, error (n) < 4/2^n*(approx (n) + 1/2^n)
```

also, we need an upper bound for `approx n`. The largest possible value for `approx n` is achieved by always append a 1 to our approximation. But, no matter how many 1s we append we never exceed 2.

```
Axiom limit : forall n : nat, approx n + 1/2^n < 2.
```

Note: `limit` can be proved in a straightforward manner, but we omit this proof here. Now, as in the even exponents case, we proceed using direct calculation with two upper bounds.

```
error (n) < (4/2^n) * (approx n + 1/2^n)
by error_upper_bound_approx

error n < (4/2^n)*(2 - 1/2^n + 1/2^n).
subst approx_n_upper_bound

error n < (4/2^n)*2
error n < 8/2^n
```

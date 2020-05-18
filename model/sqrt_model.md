Square Root Algorithms
======================

Binary Number Representation
----------------------------

The standard recursive binary square root algorithm accepts a binary number written in decimal notation.

We require that the number have the form: `x = [a0 a1 ... an . b0 b1 .. bm]`, where `x = a0 * 2^n + a1 * 2^n-1 + ... + an * 2^0 + b0 * 2^-1 + b1 * 2^-2 + ... + bm * 2^-m`.

We also require that the number of bits in front of the decimal point, `n`, and the number of bits after the decimal point, `m`, be even numbers.

If `x` can be written such that `n` or `m` is odd, we simply prepend or append a 0.

For example `x = 110.011 = 1*2^2 + 1*2^1 + 0*2^0 + 0*2^-1 + 1*2^-2 + 1*2^3`.

To use the standard algorithm, we need to prepend and append 0's and rewrite `x` as `0110.0110`.

We need the number of bits before and after the decimal point to be even because the standard algorithm recurses over `x` processing bits in pairs.

The Rationale Behind the Standard Algorithm
-------------------------------------------

Given a binary number, `x`, the standard algorithm recursively computes an approximation, `approx`, while trying to minimize the error between `x` and `approx^2` with each iteration.

Symbolically, the standard algorithm computes a value, approx, where `x - approx^2 = error`, and tries to minimize error with each iteration.

We recurse over `x`. At the beginning of each iteration, `n`, we draw the 2 most significant bits from `x` that we have not yet processed.

Let:

* `error (n)` denote the error during the n-th iteration
* `approx (n)` denote the approximation computed by the n-th iteration
* `a (n)` denotes the value of the n-th bit in `x`
* `x (n)` the portion of x iterated over so far.
* `b (n)` the bit computed for our approximation in the n-th iteration

In each iteration we extend our approximation by a single bit.

```
approx (0)     = 0
approx (n + 1) = 2 * approx (n) + b (n)
```

In each iteration we process two additional bits from `x`. If we let `x (n)` represent the bits processed so far, this means we shift the previous amount 2 bits and add the next 2 bits.

```
x (0) = 2 * a (0) + a (1)
x (n + 1) = 4 * x (n) + 2 * a (2 * n) + a (2 * n + 1)
```

Our error is simply: `error (n) = x (n) - approx (n)^2`

From the requirement that the error is always positive, we can derive the equation that tells us whether or not the n-th bit in our approximation should be 1 or 0.

```
                                                        0 &lt;= x (n + 1) - approx (n + 1)^2
                                         approx (n + 1)^2 &lt;= x (n + 1)
                                                      ... &lt;= 4 * x (n) + 2 * a (2 * n) + a (2 * n + 1)
                               (2 * approx (n) + b (n))^2 &lt;= ...
4 * approx (n)^2 + 2 * (2 * approx (n)) * b (n) + b (n)^2 &lt;= ...
                         4 * approx (n) * b (n) + b (n)^2 &lt;= (4 * x (n) - 4 * approx (n)^2) * 2 * a (2 * n) + a (2 * n + 1)
                                                      ... &lt;= 4 * error (n) * 2 * a (2 * n) + a (2 * n + 1)
                         b (n) * (4 * approx (n) + b (n)) &lt;= ...
                                       4 * approx (n) + 1 &lt;= 4 * error (n) * 2 * a (2 * n) + a (2 * n + 1)
```

because `b (n)` is either 1 or 0, we are only concerned with confirming that this condition is satisfied when `b (n)` is 1. This leads to:

what's more we can calculate the equation for error (n + 1) in terms of error (n)

```
error (0) = 2 * a (0) + a (1)
error (n + 1) = x (n + 1) - approx (n + 1)^2
          ... = 4 * x (n) + 2 * a (2 * n) + a (2 * n + 1) - (2 * approx (n) + b (n))^2
          ... = 4 * x (n) + ... - (4 * approx (n)^2 + 4 * approx (n) * b (n) + b (n)^2)
          ... = 4 * (x (n) - approx (n)^2) + ... - (4 * approx (n) * b (n) + b (n)^2)
error (n + 1) = (4 * error (n) + 2 * a (2 * n) + a (2 * n + 1)) - (b (n) * (4 * approx (n) + b (n)))
```

The Standard Algorithm
----------------------

Putting these equations together, we can derive the standard algorithm.

```
bsqrt_aux (n, m, x, err, approx)
  := if n = m
       then approx
       else block ([bn, approxn, errn],
         bn      : if 4 * decodeR (approx) + 1 &lt;=
                      4 * err + 2 * x [(2 * m) + 1] + x [(2 * m + 1) + 1]
                     then 1
                     else 0,
         approxn : encodeR (2 * decodeR (approx) + bn),
         errn    : (4 * err + 2 * x [(2 * m) + 1] + x [(2 * m + 1) + 1]) -
                   (bn * (4 * decodeR (approx) + bn)),
         bsqrt_aux (n, m + 1, x, errn, approxn));

bsqrt (x)
  := bsqrt_aux (length (x)/2, 0, x, 0, []);
```

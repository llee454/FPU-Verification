Square Root Algorithms
======================


Binary Number Representation
----------------------------

Hauser's binary square root algorithm accepts a binary number written in decimal notation.

It requires that the number have the form: `x = [a0 a1 ... an . b0 b1 .. bm]`, where `x = a0 * 2^n + a1 * 2^n-1 + ... + an * 2^0 + b0 * 2^-1 + b1 * 2^-2 + ... + bm * 2^-m`.

For example `x = 10.011 = 1*2^1 + 0*2^0 + 0*2^-1 + 1*2^-2 + 1*2^3`.

We pass the `x` to Hauser's algorithm using scientific notation. That is, we express `x` using two numbers, a mantissa and an exponent. The example above would be expressed as: `1.0011 * 2^-1`.

When we compute the square root of `x`, we get an expression like `sqrt (mantissa * 2^exp) = sqrt (mantissa) * sqrt (2^exp) = sqrt (mantissa) * 2^(exp / 2)`, which means that we perform two operations: we compute the square root of the mantissa and we divide the exponent in half. 

If the exponent is even, we can compute the new exponent by simply shifting the binary string that represents the exponent 1 bit to the right.

If the exponent is odd however, we cannot do this without, effectively rounding the result of the division.

To circumvent this problem, we shift the mantissa by left by 1 bit if the exponent is odd. This is equivalent to adding 1 to the exponent. The resulting number has the form `1b.bbb * 2^e` where e is now an even exponent.

Once we perform this transformation, we can compute the new exponent by simply right shifting the exponent.

Now, whenever we perform this transformation, the mantissa always has the form `1b.bbb` - i.e. its equivalent to `2 * a` where `a` was the original mantissa for `x`.

To compute the new exponent, we simply shift the binary string that represents the exponent right by 1 bit. 

To compute the new mantissa, we perform a recurisive algorithm in which we start with a bit string that is all 0s, and then iteratively try to set each successive bit to 1.

The Rationale Behind the Standard Algorithm
-------------------------------------------

Given a binary number, `x`, the algorithm recursively computes an approximation, `approx`, while trying to minimize the error between `x` and `approx^2` with each iteration.

Symbolically, the algorithm computes a value, approx, where `x - approx^2 = error`, and tries to minimize error with each iteration.

We recurse over `x`. At the beginning of each iteration, `n`, we draw the 2 most significant bits from `x` that we have not yet processed.

Let:

1. `error (n)` denote the error during the n-th iteration
2. `approx (n)` denote the approximation computed by the n-th iteration
3. `a (n)` denotes the value of the n-th bit in `x`
4. `x (n)` the portion of x iterated over so far.
5. `b (n)` the bit computed for our approximation in the n-th iteration

In each iteration we extend our approximation by a single bit.

```
approx (0)     = 0
approx (n + 1) = 2 * approx (n) + b (n)
```

In each iteration we process two additional bits from x. If we let `x (n)` represent the bits processed so far, this means we shift the previous amount 2 bits and add the next 2 bits.

```
x (0) = 2 * a (0) + a (1)
x (n + 1) = 4 * x (n) + 2 * a (2 * n) + a (2 * n + 1)
```

Our error is simply:

```
error (n) = x (n) - approx (n)^2
```

From the requirement that the error is always positive, we can derive the equation that tells us whether or not the n-th bit in our approximation should be 1 or 0.
```
                                                        0 <= error (n + 1)
                                                        0 <= x (n + 1) - approx (n + 1)^2
                                         approx (n + 1)^2 <= x (n + 1)
                                                      ... <= 4 * x (n) + 2 * a (2 * n) + a (2 * n + 1)
                               (2 * approx (n) + b (n))^2 <= ...
4 * approx (n)^2 + 2 * (2 * approx (n)) * b (n) + b (n)^2 <= ...
                         4 * approx (n) * b (n) + b (n)^2 <= (4 * x (n) - 4 * approx (n)^2) * 2 * a (2 * n) + a (2 * n + 1)
                                                      ... <= 4 * error (n) * 2 * a (2 * n) + a (2 * n + 1)
                         b (n) * (4 * approx (n) + b (n)) <= ...
                                       4 * approx (n) + 1 <= 4 * error (n) * 2 * a (2 * n) + a (2 * n + 1)
```
because b (n) is either 1 or 0, we are only concerned with confirming that this condition is satisfied when b (n) is 1. This leads to:


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
         bn      : if 4 * decodeR (approx) + 1 <=
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

Division Readme
===============

The Division module defines a function that implements floating
point division.

For simplicity, we only consider positive floating point numbers. We
follow IEE 754 in representing floating point numbers using a scheme
analogous to scientific notation. In our scheme, every floating
point number is represented like 1.0101 * 2^(10). We represent these
numbers as pairs of bit vectors. The first bit vector represents
the significant digits - 10101 in our example. The second bit vector
represents the bits in the exponent - 10 in our example.

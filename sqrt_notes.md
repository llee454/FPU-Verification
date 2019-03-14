== Goal ==

rem (n) = error (n) * 2^n/2 < 4

forall n : nat, error (n) < 8/2^n

== Definitions and Relations ==

1 <= a < 2

a = approx (n)^2 + error (n)

error (n + 1) = error (n) - (b (n)/2^n) * (2 * approx (n) + b (n)/2^n)

a < (approx (n) + 2/2^n)^2
intuitively, because adding 2/2^n flips a bit that was a 0 in approx (n). That bit was 0 precisely to ensure that approx (n)^2 was less than a.

a < (approx (n) + 2/2^n)^2
a < approx (n)^2 + 4/2^n * (approx (n) + 1/2^n)
a - approx (n)^2 < 4/2^n * (approx (n) + 1/2^n)
error (n) < 4/2^n * (approx (n) + 1/2^n)
0 <= error (n) < 4/2^n * (approx (n) + 1/2^n)

approx (n)^2 = a - error (n)
approx (n)^2 < 2 - 0
approx (n) < 2^(1/2)
0 <= approx (n) < 2^(1/2)

subst the upper bound for approx (n) into the bounds for error (n) gives:

0 <= error (n) < (2^(5/2) + 4/2^n)/2^n = (5.656854249492383+4/2^n)/2^n

8/2^(n + 1) = 8/(2*2^n) = 4/2^n

== Proof ==

We can prove that the goal holds for n = 0 using my proof that error (n) < 4 for n = 0.

For all n > 0, direct calculation using error (n) < (5.656854249492383+4/2^n)/2^n gives it.

clearly this holds for n = 0 and n = 1 (I already have a proof that forall n, error (n) < 4.

So the goal is:

forall n : nat, error (n) < 8/2^n -> error (n + 1) < 4/2^n

lets expand error (n + 1). Our goal is:

error (n) - ((b (n)/2^n) * (2 * approx (n) + b (n)/2^n)) < 4/2^n

In what follows we will attempt maximize the lhs of this equation and show that it cannot exceed the rhs.

To do this we will attempt to establish upper bounds for error (n) and lower bounds for approx (n) and show that when these bounds are substituted, the lhs is less than the rhs.

== Case Analysis on b (n) ==

when b (n) = 0: error (n) < 1/2^n * (2 approx (n) + 1/2^n).

when b (n) = 1: 1/2^n * (2 approx (n) + 1/2^n) <= error (n).

=== b (n) = 0 ===

when b (n) = 0: error (n) < 1/2^n * (2 * approx (n) + 1/2^n).

1/2^n * (2 * approx (n) + 1/2^n) - ((b n/2^n) * (2 * approx (n) + b (n)/2^n))
1/2^n * (2 * approx (n) + 1/2^n)

now when we maximize the equation by substituting approx (n) = 2, we get:

4/2^n + 1/4^n which is not less than 4/2^n.

So we need a stronger (lower) upper bound for approx (n).

Substituting 2^(1/2) for approx (n) gives:

(1/2^n + 2^(3/2))/2^n < 4/2^n;
1/2^n + 2^(3/2) < 4;
1/2^n + 2.82842712474619 < 4

This is maximized when n = 0, giving:

3.82842712474619 < 4

which holds.

==== b (n) = 1 ====

Our goal is to prove that:

error (n) - (1/2^n) * (2 * approx (n) + 1/2^n)) < 4/2^n

Again we maximize error (n), minimize the second term in the lhs, and show that the result is less than 4/2^n.

lets use error (n) = 4/2^n * (approx (n) + 1/2^n) and approx (n) = 0.

4/2^n * (approx (n) + 1/2^n) - (1/2^n) * (2 * approx (n) + 1/2^n)) < 4/2^n
(3/2^n)/2^n < 4/2^n;
3/2^n < 4

which holds.

== Conclusion ==

This proves that forall n, error (n), 8/2^n.

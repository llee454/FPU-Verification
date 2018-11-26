(*
  This file proves that the width used by the rem register in
  Hausner's implementation if large enough to store any intermediate
  value that may result while computing the quotient of two
  floating point binary numbers.

  Coq is ill-suited to algebraic manipulations. Whenever, we have
  relied on an algebraic transformation that we could not verify simply
  using Coq, we have placed the associated equation in a conjecture
  and verified it using Maxima - an open source CAS similar to
  Maple and Mathematica.  Maxima can solve simple equations and
  inequalities.

  Whenever we have marked a conjecture as "verified"
  using Maxima, we have used Maxima to prove that the equation or
  inequality holds. On the other hand, whenever we have marked a
  conjecture as "tested" using Maxima, we have verified that it
  holds over a range of numerical examples.
*)

Require Import base.
Require Import Reals.
Require Import Fourier.

Open Scope R_scope.

(** Represents the dividend. *)
Parameter a : R.

(** Represents the divisor. *)
Parameter b : R.

(**
  Asserts the lower and upper bounds on the
  dividend and divisor.

  These follow because both [a] and [b], have
  the form: 1.b0b1...bn.
*)
Axiom a_lower_bound : 1 <= a.
Axiom a_upper_bound : a < 2.
Axiom b_lower_bound : 1 <= b.
Axiom b_upper_bound : b < 2.

(**
  Accepts a natural number, [n], and returns the
  bit append onto our quotient approximation in
  the n-th iteration.
*)
Parameter bit : nat -> R.

(**
  Accepts a natural number, [n], and returns
  the quotient approximation generated in the
  n-th iteration.
*)
Parameter approx : nat -> R.

Axiom bit_0 : forall n : nat, a < b * (approx n + 1/2^n) -> bit n = 0.

Axiom bit_1 : forall n : nat, b * (approx n + 1/2^n) <= a -> bit n = 1.

(**
  Asserts that [bit n] always returns a binary
  digit - i.e. a bit.
*)
Lemma bit_is_bit
  : forall n : nat, bit n = 0 \/ bit n = 1.
Proof
  fun n
    => or_ind
        (fun H : a < b * (approx n + 1/2^n)
          => or_introl (bit n = 1) (bit_0 n H))
        (fun H : b * (approx n + 1/2^n) <= a
          => or_intror (bit n = 0) (bit_1 n H))
        (Rlt_or_le a (b * (approx n + 1/2^n))).

(**
  Asserts that the initial quotient approximation
  is 0.
*)
Axiom approx_0 : approx 0 = 0.

(**
  Asserts that each quotient approximation is
  produced by appending a bit onto the end of
  the previous approximation.
*)
Axiom approx_Sn : forall n : nat, approx (S n) = approx n + bit n/2^n.

(**
  Accepts a natural number, [n], and returns
  a measure of the error between the current
  quotient approximation and the true value.
*)
Parameter error : nat -> R.

(** Represents the error equation. *)
Axiom error_n : forall n : nat, error n = a - b * approx n.

(** Asserts that the error is always positive. *)
Axiom error_is_pos : forall n : nat, 0 <= error n.

Lemma bit_0_inv
  : forall n : nat, bit n = 0 -> a < b * (approx n + 1/2^n).
Proof
  fun n H
    => or_ind
         (fun H0 : a < b * (approx n + 1/2^n)
           => H0)
         (fun H0 : b * (approx n + 1/2^n) <= a
           => False_ind _
                (R1_neq_R0 (H || X = 0 @X by <- bit_1 n H0)))
         (Rlt_or_le a (b * (approx n + 1/2^n))).

Lemma bit_1_inv
  : forall n : nat, bit n = 1 -> b * (approx n + 1/2^n) <= a.
Proof
  fun n H
    => or_ind
         (fun H0 : a < b * (approx n + 1/2^n)
           => False_ind _
                (R1_neq_R0 (eq_sym (H || X = 1 @X by <- bit_0 n H0))))
         (fun H0 : b * (approx n + 1/2^n) <= a
           => H0)
         (Rlt_or_le a (b * (approx n + 1/2^n))).

Conjecture approx_lower_bound_aux_0 : 0 <= 0 + 2.

(* TODO: verify *)
Conjecture approx_lower_bound_aux_1
  : forall n : nat, bit n = 0 -> b * (approx n + 1/2^n) < b * (approx (S n) + 2/2^(S n)).

Conjecture approx_lower_bound_aux_2
  : forall n : nat, approx n + 1/2^n + 1/2^n = approx n + 2/2^n.

Conjecture approx_lower_bound_aux_3
  : forall n : nat, 2/2^(S n) = 1/2^n.

Lemma approx_lower_bound 
  :  forall n : nat, a < b * (approx n + 2/2^n).
Proof
  nat_ind _
    (Rlt_le_trans a 2 (b * (0 + 2))
      a_upper_bound 
      (Rle_trans 2 (1 * (0 + 2)) (b * (0 + 2))
        (ltac:(fourier) : 2 <= 1 * (0 + 2))
        (Rmult_le_compat_r (0 + 2) 1 b
          approx_lower_bound_aux_0
          b_lower_bound))
      || a < b * (X + 2) @X by approx_0
      || a < b * (approx 0 + X) @X by (ltac:(field) : 2/2^0 = 2))
    (fun n (H : a < b * (approx n + 2/2^n))
      => or_ind
           (fun H0 : bit n = 0
             => Rlt_trans a (b * (approx n + 1/2^n)) (b * (approx (S n) + 2/2^(S n)))
                  (bit_0_inv n H0)
                  (approx_lower_bound_aux_1 n H0))
           (fun H0 : bit n = 1
             => H
                || a < b * X @X by approx_lower_bound_aux_2 n
                || a < b * (approx n + X/2^n + 1/2^n) @X by H0
                || a < b * (X + 1/2^n) @X by approx_Sn n
                || a < b * (approx (S n) + X) @X by approx_lower_bound_aux_3 n)
           (bit_is_bit n)).

Conjecture error_upper_bound_aux_0 : forall n : nat, 0 < 2/2^n.

Conjecture error_upper_bound_aux_1 : forall n : nat, 4/2^n = 2 * (2/2^n).

Theorem error_upper_bound
  :  forall n : nat, error n < 4/2^n.
Proof
  fun n
    => Rlt_trans
         (error n) (b * (2/2^n)) (2 * (2/2^n))
         (Rplus_lt_compat_r
           (- (b * approx n)) a (b * approx n + b * (2/2^n))
           (approx_lower_bound n
             || a < X @X by <- Rmult_plus_distr_l b (approx n) (2/2^n))
           || X < b * approx n + b * (2/2^n) - b * approx n @X by error_n n
           || error n < X @X by (ltac:(ring) : b * approx n - b * approx n + b * (2/2^n) = b * approx n + b * (2/2^n) - b * approx n)
           || error n < X + b * (2/2^n) @X by <- Rplus_opp_r (b * approx n)
           || error n < X @X by <- Rplus_0_l (b * (2/2^n)))
         (Rmult_lt_compat_r (2/2^n) b 2
           (error_upper_bound_aux_0 n)
            b_upper_bound) 
         || error n < X @X by error_upper_bound_aux_1 n.

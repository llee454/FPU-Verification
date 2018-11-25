(*
  This file proves that the width used by the
  rem register in Hausner's implementation if
  large enough to store any intermediate value
  that may result while computing the square
  root of a floating point binary number having
  an even exponent.

  Coq is ill-suited to algebraic
  manipulations. Whenever, we have relied on
  an algebraic transformation that we could
  not verify simply using Coq, we have placed
  the associated equation in a conjecture and
  verified it using Maxima - an open source CAS
  similar to Maple and Mathematica.

  Maxima can solve simple equations and
  inequalities. Whenever we have marked a
  conjecture as "verified" using Maxima, we
  have used Maxima to prove that the equation or
  inequality holds. On the other hand, whenever
  we have marked a conjecture as "tested" using
  Maxima, we have verified that it holds over
  a range of numerical examples.
*)

Require Import base.
Require Import Reals.
Require Import Fourier.

Open Scope R_scope.

(**
  Represents the mantissa of the number that we
  are computing the square root of.
*)
Parameter a : R.

(**
  We require that [a] correspond to a binary
  floating point number of the form 1.b1b2...bn,
  where bi represents an arbitrary bit. For
  example: 1.01011.

  Accordingly, the smallest possible value
  that [a] can represent is 1. The largest is
  infinitesimally less than 2.
*)
Axiom a_lower_bound : 1 <= a. 
Axiom a_upper_bound : a < 2.

(**
  Accepts a natural number, [n], and returns the
  value of the n-th bit in our approximation of
  the square root of [a].
*)
Parameter b : nat -> R.

(** Asserts that b returns a binary value. *)
Axiom b_is_bit : forall n : nat, {b n = 0}+{b n = 1}.

(**
  Accepts a natural number, [n], and returns our
  n-th approximation of the square root of [a].
*)
Parameter approx : nat -> R.

(**
  Asserts that our initial approximation of the
  square root of [a] is 0.
*)
Axiom approx_0 : approx 0 = 0.

(**
  Asserts that we generate the n-th approximation
  by appending the n-th bit onto our previous
  approximation.
*)
Axiom approx_Sn : forall n : nat, approx (S n) = approx n + (b n)/(2^n).

(**
  Accepts a natural number, [n], and returns
  the difference between [a] and the square of
  our n-th approximation.
*)
Parameter error : nat -> R.

(** Asserts that the error is always positive. *)
Axiom error_is_positive : forall n : nat, 0 <= error (n).

(**
  Asserts the relationship between [a], our
  approximation for the square root of [a],
  and the discrepancy between the square of our
  approximation and [a].
*)
Axiom murali : forall n : nat, 2*a = (approx n)^2 + error n.

(**
*)
Conjecture two_a_lt_4 : 2*a < 4.

(**
  Proves that the discrepancy between the square
  of our initial approximation and [a] equals
  [a].
*)
Lemma error_0
  :  error 0 = 2*a.
Proof
  eq_sym
    (murali 0
      || 2*a = (X)^2 + error 0 @X by <- approx_0
      || 2*a = X + error 0 @X by <- Rmult_0_l (0 * 1)
      || 2*a = X @X by <- Rplus_0_l (error 0)).
 
(**
*)
Conjecture error_0_lt_4 : error 0 < 4.

(**
  Represents [error] in terms of [a] and
  [approx].
*)
Lemma error_n 
  :  forall n : nat, 2*a - (approx n)^2 = error n.
Proof
  fun n
    => Rplus_eq_compat_r (- (approx n)^2) (2*a) ((approx n)^2 + (error n)) (murali n)
         || 2*a - (approx n)^2 = X                @X by <- Rplus_assoc ((approx n)^2) (error n) (- (approx n)^2)
         || 2*a - (approx n)^2 = (approx n)^2 + X @X by <- Rplus_comm (error n) (- (approx n)^2)
         || 2*a - (approx n)^2 = X                @X by Rplus_assoc ((approx n)^2) (- (approx n)^2) (error n)
         || 2*a - (approx n)^2 = X + error n      @X by <- Rplus_opp_r ((approx n)^2)
         || 2*a - (approx n)^2 = X                @X by <- Rplus_0_l (error n).

(**
  Provides an algebraic expansion for [error].

  note:
  error (S n) = error n - (b n)/(2^n) * (2 * approx n + (b n)/(2^n))
  error (S n) = error n - (b n)/(2^n) * (approx n + approx n + (b n)/(2^n))
  error (S n) = error n - (b n)/(2^n) * (approx n + approx (S n))
*)
Conjecture error_Sn
  :  forall n : nat, error (S n) = error n - (b n)/(2^n) * (2 * approx n + (b n)/(2^n)).
(*
Proof
  fun n
    => eq_sym (error_n (S n))
        || error (S n) = a - X^2 @X by approx_Sn n
        || error (S n) = a - (approx n + b n/2^n) * X @X Rmult_1_r (approx n + b n/2^n)
        || error (S n) = a - X @X by Rmult_plus_distr_l (approx n + b n/2^n) (approx n) (b n/2^n)
        || error (S n) = a - X ((approx n + b n/2^n) * b n/2^n) @X by Rmult_plus_distr_r (approx n) (b n/2^n) (approx n)
*)

(*
  Asserts bounds for [error] and [approx] based
  on the value of a given bit.
*)
Axiom b_0 : forall n : nat, b n = 0 -> error n < 1/2^n * (2 * approx n + 1/2^n).
Axiom b_1 : forall n : nat, b n = 1 -> 1/2^n * (2 * approx n + 1/2^n) <= error n.


(*
  Proves that every bit is greater than or equal
  to 0.
*)
Lemma b_lower_bound
  :  forall n : nat, 0 <= b n.
Proof
  fun n
    => sumbool_ind
         (fun _ => 0 <= b n)
         (fun H : b n = 0
           => Req_le_sym 0 (b n) H)
         (fun H : b n = 1
           => Rle_0_1 || 0 <= X @X by H)
         (b_is_bit n).

(**
  Proves that [approx] is always positive.
*)
Lemma approx_is_positive
  :  forall n : nat, 0 <= approx n.
Proof
  nat_ind _
    (Req_le_sym 0 (approx 0) approx_0)
    (fun n (H : 0 <= approx n)
      => Rle_trans 0
           (approx n + 0)
           (approx n + (b n)/(2^n))
           (H || 0 <= X @X by Rplus_0_r (approx n))
           (Rplus_le_compat_l
             (approx n)
             0
             ((b n)/(2^n))
             ((Rmult_le_compat_r
               (/(2^n))
               0
               (b n)
               (Rlt_le 0 (/(2^n))
                 (Rinv_0_lt_compat (2^n)
                    (pow_lt 2 n Rlt_0_2)))
               (b_lower_bound n))
               || X <= (b n)/(2^n) @X by <- Rmult_0_l (/(2^n)))
             )
         || 0 <= X @X by (approx_Sn n)).

Conjecture two_n_nonzero : forall n : nat, 2 ^ n <> 0.

(**
  Expresses the square of [approx] in terms of
  [a] and [error].
*)
Lemma approx_n_sqr
  :  forall n : nat, 2*a - error n = (approx n)^2.
Proof.
  (induction n).
    (rewrite error_0).
    (rewrite approx_0).
    ring.

    (rewrite (approx_Sn n)).
    (rewrite <- (error_n (S n))).
    (rewrite (approx_Sn n)).
    field.
    exact (two_n_nonzero n).

Qed.

(**
  Represents the [approx] in terms of [a] and
  [error].
*)
Lemma approx_n
  :  forall n : nat, sqrt (2*a - error n) = approx n.
Proof
  fun n
    => f_equal sqrt (approx_n_sqr n)
         || sqrt (2*a - error n) = X @X by <- sqrt_pow2 (approx n) (approx_is_positive n).

(**
*)
Lemma approx_sqr_is_positive_alt
  :  forall n : nat, 0 <= 2*a - error n.
Proof
  fun n
    => pow_le (approx n) 2 (approx_is_positive n)
         || 0 <= X @X by approx_n_sqr n.

(**
  Asserts a weak constant upper bound for
  [approx].

  approx n = sqrt(2*a - error n) < sqrt(4)
*)
Conjecture approx_upper_bound
  :  forall n : nat, approx n < sqrt 4.

(**
  This upper bound results from approx always appending a 1 each n.

  verified with Maxima
  load("solve_rec")$
  solve_rec(f[n+1]=1+2*f[n],f[n]);
  maxapprox(n):=(2^n+2^n-1)/2^n;
  sum(1/2^m,m,0,n);
*)
Conjecture approx_n_upper_bound
  :  forall n : nat, approx n <= 1/2^n * (2^(n + 1) - 1);

Lemma a_upper_bound_0
  : forall n : nat, approx n + 1/2^n + 1/2^n = approx n + 2/2^n.
Proof.
  intro.
  field.
  exact (two_n_nonzero n).
Qed.

Lemma a_upper_bound_1
  : forall n : nat, 2/2^(S n) = 1/2^n.
Proof.
  intro.
  (simpl).
  field.
  exact (two_n_nonzero n).
Qed.

(*
  (approx n + 1/2^n)^2 <= (approx (S n) + 2/2^(S n))^2
                       <= (approx (S n) + 1/2^n)^2
                       <= (approx n + b n/2^n + 1/2^n)^2
  b n = 0
                       <= (approx n + 1/2^n)^2
                       reflexivity
  b n = 1
                       <= (approx n + 1/2^n + 1/2^n)^2
                       trivial 

  load(ineq);
  assume(0<approx(n));
  assume(0<approx(n+1));
  assume(approx(n)<approx(n+1));
  is((approx(n)+1/2^n)^2<=(approx(n+1)+2/2^(n+1))^2);
*)
Theorem a_upper_bound_2
  : forall n : nat, (approx n + 1/2^n)^2 <= (approx (S n) + 2/2^(S n))^2.
Proof.
  intro.
  (rewrite (approx_Sn n)).
  (induction (b_is_bit n)).
   (rewrite a0).
   (assert (0 / 2 ^ n = 0)).
    field.
    exact (two_n_nonzero n).
    (rewrite H).
    (rewrite a_upper_bound_1).
    (rewrite (Rplus_assoc (approx n) 0 (1 / 2 ^ n))).
    (rewrite (Rplus_0_l (1 / 2 ^ n))).
    (apply (Req_le ((approx n + 1 / 2 ^ n) ^ 2))).
    reflexivity.
   (rewrite b0).
   (simpl).
   (rewrite (Rmult_1_r (approx n + 1 / 2 ^ n))).
   (rewrite (Rmult_1_r (approx n + 1 / 2 ^ n + 2 / (2 * 2 ^ n)))).
   (apply Rlt_le).
   (assert (approx n + 1 / 2 ^ n < approx n + 1 / 2 ^ n + 2 / (2 * 2 ^ n))).
    (rewrite (Rplus_assoc (approx n) (1 / 2 ^ n) (2 / (2 * 2 ^ n)))).
    (apply
      (Rplus_lt_compat_l (approx n) (1 / 2 ^ n) (1 / 2 ^ n + 2 / (2 * 2 ^ n)))).
    (rewrite <- (Rplus_0_r (1 / 2 ^ n))  at 1).
    (apply (Rplus_lt_compat_l (1 / 2 ^ n) 0 (2 / (2 * 2 ^ n)))).
    (simpl).
    (apply Rlt_mult_inv_pos).
     fourier.
     (apply Rmult_lt_0_compat).
      fourier.
      (apply pow_lt).
      fourier.
    (assert (0 <= approx n + 1 / 2 ^ n)).
     (apply Rplus_le_le_0_compat).
      (apply (approx_is_positive n)).
      (apply (Rle_mult_inv_pos 1 (2 ^ n))).
       fourier.
       (apply (pow_lt 2 n)).
       fourier.
     (assert (0 <= approx n + 1 / 2 ^ n + 2 / (2 * 2 ^ n))).
      (apply Rplus_le_le_0_compat).
       (apply H0).
       (apply (Rle_mult_inv_pos 2 (2 * 2 ^ n))).
        fourier.
        (apply Rmult_lt_0_compat).
         fourier.
         (apply (pow_lt 2 n)).
         fourier.
      (apply
        (Rmult_le_0_lt_compat (approx n + 1 / 2 ^ n)
           (approx n + 1 / 2 ^ n + 2 / (2 * 2 ^ n)) 
           (approx n + 1 / 2 ^ n) (approx n + 1 / 2 ^ n + 2 / (2 * 2 ^ n)) H0
           H0 H H)).
Qed.

(*
  n = 0:
  2*a < (0 + 2/2^0)^2
  2*a < 4

  Sn:
  2*a < (approx (S n) + 2/2^(S n))^2
  2*a < (approx n + b n/2^n + 1/2^n)^2

    b n = 0:
    2*a < (approx n + 1/2^n)^2
    (approx n)^2 + error n < (approx n + 1/2^n)^2
                           < (approx n)^2 + 1/2^n * (2 * approx n + 1/2^n)
                   error n < 1/2^n * (2 * approx n + 1/2^n)
    by b_0 

    b n = 1:
    2*a < (approx n + 1/2^n + 1/2^n)^2
    2*a < (approx n + 2/2^n)^2
    hypothesis
*)
Theorem a_upper_bound_approx
  :  forall n : nat, 2*a < (approx n + 2/2^n)^2.
Proof nat_ind _
       (two_a_lt_4
         || 2*a < X @X by (ltac:(field) : (0 + 2/2^0)^2 = 4)
         || 2*a < (X + 2/2^0)^2 @X by approx_0)
       (fun n (H : 2*a < (approx n + 2/2^n)^2)
         => sumbool_ind
              (fun _ => 2*a < (approx (S n) + 2/2^(S n))^2)
              (fun H0 : b n = 0
                => Rlt_le_trans
                     (2*a)
                     ((approx n + 1/2^n)^2)
                     ((approx (S n) + 2/2^(S n))^2)
                     (Rle_lt_trans
                       (2*a)
                       ((approx n)^2 + error n)
                       ((approx n)^2 + 1/2^n*(2*approx (n) + 1/2^n))
                       (Req_le
                         (2*a)
                         ((approx n)^2 + error n)
                         (murali n))
                       (Rplus_lt_compat_l
                         ((approx n)^2)
                         (error n)
                         (1/2^n*(2*approx (n) + 1/2^n))
                         (b_0 n H0))
                       || 2*a < X @X by (ltac:(ring) : ((approx (n) + 1/2^n)^2) = (approx (n)^2 + 1/2^n*(2*approx (n) + 1/2^n))))
                     (a_upper_bound_2 n))
              (fun H0 : b n = 1
                => let H1
                     :  approx (S n) = approx n + 1/2^n
                     := approx_Sn n
                          || approx (S n) = approx n + (X/2^n) @X by <- H0 in
                   H
                   || 2*a < X^2 @X by a_upper_bound_0 n
                   || 2*a < (X + 1/2^n)^2 @X by H1
                   || 2*a < (approx (S n) + X)^2 @X by a_upper_bound_1 n)
              (b_is_bit n)).

(**
*)
Conjecture error_upper_bound_const_0
  : forall n : nat, - ((b n)/(2^n) * (2 * approx n + (b n)/(2^n))) <= 0.

(** Proves that [error] is always less than 4. *)
Theorem error_upper_bound_const
  :  forall n : nat, error n < 4.
Proof
  nat_ind _
    error_0_lt_4
    (fun n (H : error n < 4)
      => Rlt_le_trans
           (error (S n))
           (4 - ((b n)/(2^n) * (2 * approx n + (b n)/(2^n))))
           (4 + 0)
           ((Rplus_lt_compat_r
             (- ((b n)/(2^n) * (2 * approx n + (b n)/(2^n))))
             (error n)
             4
             H)
             || X < 4 - ((b n)/(2^n) * (2 * approx n + (b n)/(2^n))) @X by error_Sn n)
           (Rplus_le_compat_l
             4
             (- ((b n)/(2^n) * (2 * approx n + (b n)/(2^n))))
             0
             (error_upper_bound_const_0 n))
         || error (S n) < X @X by <- Rplus_0_r 4).

Axiom error_upper_bound_approx_0
  :  forall n : nat, (approx n)^2 + (4/2^n)*(approx n + 1/2^n) = (approx n + 2/2^n)^2.

(**
  Proves a significant constraint on [error]
  and [approx].
*)
Theorem error_upper_bound_approx
  :  forall n : nat, error n < (4/2^n)*(approx n + 1/2^n).
Proof
  fun n
    => Rplus_lt_compat_r
         (- ((approx n)^2))
         (2*a)
         ((4/2^n)*(approx n + 1/2^n) + (approx n)^2)
         (a_upper_bound_approx n 
           || 2*a < X @X by error_upper_bound_approx_0 n
           || 2*a < X @X by <- Rplus_comm ((approx n)^2) ((4/2^n)*(approx n + 1/2^n)))
       || X < ((4/2^n)*(approx n + 1/2^n) + (approx n)^2) - ((approx n)^2) @X by <- error_n n
       || error n < X                              @X by <- Rplus_assoc ((4/2^n)*(approx n + 1/2^n)) ((approx n)^2) (- ((approx n)^2))
       || error n < (4/2^n)*(approx n + 1/2^n) + X @X by <- Rplus_opp_r ((approx n)^2)
       || error n < X                              @X by <- Rplus_0_r ((4/2^n)*(approx n + 1/2^n)).

(**
  TODO: Verify.

  load(ineq);
  assume(approx(n)<sqrt(4));
  assume(0<n);
  is((approx(n)+1/2^n)<(sqrt(4)+1/2^n));
  
*)
Conjecture rem_register_even_exp_0
  : forall n : nat, (4/2^n)*(approx n + 1/2^n) < (4/2^n)*(2 + 1/2^n).


Conjecture rem_register_even_exp_1
  : forall n : nat, 0 <= 4 - 8 / (2 * (2 * 2 ^ n)).

Conjecture rem_register_even_exp_2
  : forall n : nat, 0 <= 2 * 2 - error (S n).
(*

(induction n).
 (apply (Rlt_trans (error 0) 4 (8 / 1))).
  (apply error_upper_bound_const).

  fourier.

 (induction n).
  (apply (Rlt_le_trans (error 1) 4 (8 / 2 ^ 1))).
   (apply error_upper_bound_const).

   (simpl).
   fourier.

  (assert (approx (S (S n)) < sqrt (4 - 2 / 2 ^ n))).
   (rewrite <- (approx_n (S (S n)))).
   replace (2 / 2 ^ n) with 8 / 2 ^ S (S n).
    (apply sqrt_lt_1).
     (apply (approx_sqr_is_positive_alt (S (S n)))).

     (simpl).
     admit.

     (apply Rplus_lt_compat).
      (apply two_a_lt_4).

      (apply Ropp_lt_contravar).


(** TODO: Verify. 
  Is equivalent to:

  4/2^(n+2) * (2 + 1/2^(n+2)) < 8/2^(n+2)
  1/2^n * (2 + 1/2^(n + 2)) < 2/2^n
  2 + 1/2^(n + 2) < 2

  This argument fails. There is never a value of n where the lhs is less than the rhs.


  1/2^(n+1) + sqrt(2) < 2
  1/2^(n+1) + sqrt(2) < 1/2^(n+1) + 1.5 <= 2
                        1/2^(n+1)       <= 2 - 1.5
                        1/2^(n+1)       <= 1/2
  
*)
Conjecture rem_register_even_exp_1
  :  forall n : nat, (4/2^(S n))*(2 + 1/2^(S n)) < 8/2^(S n).

(**
  Proves that the width used to store
  intermediate error values is large enough to
  accomodate every possible value without a loss
  of precision.
*)
Theorem rem_register_even_exp
  :  forall n : nat, error n < 8/2^n.
Proof
  nat_ind _
    (Rlt_trans
      (error 0)
      4
      (8/2^0)
      (error_upper_bound_const 0)
      ((ltac:(fourier) : 4 < 8)
        || 4 < X @X by (ltac:(field) : 8/2^0 = 8)))
    (fun n (H : error n < 8/2^n)
      => Rlt_trans
           (error (S n))
           ((4/2^(S n))*(approx (S n) + 1/2^(S n)))
           (8/2^(S n))
           (error_upper_bound_approx (S n))
           (Rlt_trans
             ((4/2^(S n))*(approx (S n) + 1/2^(S n)))
             ((4/2^(S n))*(sqrt 2 + 1/2^(S n)))
             (8/2^(S n))
             (rem_register_even_exp_0 (S n))
             (rem_register_even_exp_1 n))).

*)

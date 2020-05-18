(*
  This file proves that the width used by the
  rem register in Hausner's implementation if
  large enough to store any intermediate value
  that may result while computing the square
  root of a floating point binary number having
  an even exponent.
*)

Require Import base.
Require Import aux.
Require Import Reals.
Require Import micromega.Lra.

Open Scope R_scope.

Axiom lt_sqrt_div_3_2 : sqrt 2 < 3 / 2.

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
Axiom spec : forall n : nat, a = (approx n)^2 + error n.

(**
  Proves that the discrepancy between the square
  of our initial approximation and [a] equals
  [a].
*)
Lemma error_0
  :  error 0 = a.
Proof.
  exact
    (eq_sym
      (spec 0
        || a = (X)^2 + error 0 @X by <- approx_0
        || a = X + error 0 @X by <- Rmult_0_l (0 * 1)
        || a = X @X by <- Rplus_0_l (error 0))).
Qed.
 
(**
  Represents [error] in terms of [a] and
  [approx].
*)
Lemma error_n 
  :  forall n : nat, a - (approx n)^2 = error n.
Proof.
  exact
    (fun n
      => Rplus_eq_compat_r (- (approx n)^2) a ((approx n)^2 + (error n)) (spec n)
           || a - (approx n)^2 = X                @X by <- Rplus_assoc ((approx n)^2) (error n) (- (approx n)^2)
           || a - (approx n)^2 = (approx n)^2 + X @X by <- Rplus_comm (error n) (- (approx n)^2)
           || a - (approx n)^2 = X                @X by Rplus_assoc ((approx n)^2) (- (approx n)^2) (error n)
           || a - (approx n)^2 = X + error n      @X by <- Rplus_opp_r ((approx n)^2)
           || a - (approx n)^2 = X                @X by <- Rplus_0_l (error n)).
Qed.

(**
  Provides an algebraic expansion for [error].
*)
Lemma error_Sn
  :  forall n : nat, error (S n) = error n - (b n)/(2^n) * (2 * approx n + (b n)/(2^n)).
Proof.
  exact
    (fun n =>
      eq_sym (error_n (S n))
      || error (S n) = a - X^2 @X by <- approx_Sn n
      || _ = a - (approx n + b n/2^n) * X @X by <- Rmult_1_r (approx n + b n/2^n)
      || _ = _ - X @X by <- Rmult_plus_distr_r (approx n) ((b n)/(2^n)) (approx n + b n/2^n)
      || _ = _ - (X + _) @X by <- Rmult_plus_distr_l (approx n) (approx n) (b n/2^n)
      || _ = _ - (_ + X) @X by <- Rmult_plus_distr_l (b n/2^n) (approx n) (b n/2^n)
      || _ = _ - ((X + _) + _) @X by pow2 (approx n)
      || _ = _ - X @X by Rplus_assoc ((approx n)^2 + approx n * (b n/2^n)) (b n/2^n * approx n) ((b n/2^n) * (b n/2^n))
      || _ = _ - (X + _) @X by <- Rplus_assoc ((approx n)^2) (approx n * (b n/2^n)) (b n/2^n * approx n)
      || _ = _ - (_ + (_ + X) + _) @X by <- Rmult_comm (b n/2^n) (approx n)
      || _ = _ - (_ + X + _) @X by double (approx n * (b n/2^n))
      || _ = _ - X @X by <- Rplus_assoc ((approx n)^2) (2 * ((approx n) * (b n/2^n))) ((b n/2^n)*(b n/2^n))
      || _ = _ + X @X by <- Ropp_plus_distr ((approx n)^2) (2 * (approx n * (b n/2^n)) + (b n/2^n)*(b n/2^n))
      || _ = X @X by Rplus_assoc a (- (approx n)^2) (- (2*(approx n * (b n/2^n)) + (b n/2^n)*(b n/2^n)))
      || _ = X + _ @X by <- error_n n
      || _ = _ - (X + _) @X by Rmult_assoc 2 (approx n) (b n/2^n)
      || _ = _ - X @X by Rmult_plus_distr_r (2 * (approx n)) (b n/2^n) (b n/2^n)
      || _ = _ - X @X by <- Rmult_comm (2 * approx n + b n/2^n) (b n/2^n)).
Qed.

(*
  In each iteration [n], we try to append a 1
  bit onto [approx]. If the result is larger than
  [a], we append a 0 instead.
*)
Axiom bn : forall n : nat, (approx n + 1/2^n)^2 > a <-> b n = 0.

(*
  Asserts bounds for [error] and [approx] based
  on the value of a given bit.

  a < (approx (n) + 1/2^n)^2
  approx (n)^2 + error (n) < (apporx (n) + 1/2^n)^2
  approx (n)^2 + error (n) < approx (n)^2 + 1/2^n (2 approx (n) + 1/2^n)
  error (n) < approx (n)^2 + 1/2^n (2 approx (n) + 1/2^n)
*)
Lemma b_0 : forall n : nat, b n = 0 -> error n < 1/2^n * (2 * approx n + 1/2^n).
Proof.
  exact
    (fun n H =>
      Rplus_lt_compat_l
        (- (approx n)^2)
        ((approx n)^2 + error n)
        ((approx n)^2 + (1/2^n * (2 * approx n + 1/2^n)))
        (Rgt_lt _ _ (proj2 (bn n) H)
          || X < (approx n + 1/2^n)^2 @X by <- spec n
          || _ < X @X by <- sqr_expand (approx n) (1/2^n))
      || X < _ @X by Rplus_assoc (- (approx n)^2) ((approx n)^2) (error n)
      || _ < X @X by Rplus_assoc (- (approx n)^2) ((approx n)^2) (1/2^n * (2 * approx n + 1/2^n))
      || X + _ < _ @X by <- Rplus_opp_l ((approx n)^2)
      || X < _ @X by <- Rplus_0_l (error n)
      || _ < X + _ @X by <- Rplus_opp_l ((approx n)^2)
      || _ < X @X by <- Rplus_0_l _).
Qed.

(*
  0 <= error (n + 1)
  0 <= error (n) + b (n)/2^n (2 approx (n) + b (n)/2^n)
  b (n)/2^n (2 approx (n) + b (n)/2^n) <= error (n)
*)
Lemma b_1 : forall n : nat, b n = 1 -> 1/2^n * (2 * approx n + 1/2^n) <= error n.
Proof.
  exact
    (fun n H =>
      Rplus_le_compat_r
        (b n/2^n * (2 * approx n + b n/2^n)) 0
        (error n - b n/2^n * (2 * approx n + b n/2^n))
        (error_is_positive (S n)
         || 0 <= X @X by <- error_Sn n)
      || X <= _ @X by <- Rplus_0_l (b n/2^n * (2 * approx n + b n/2^n))
      || _ <= X @X by <-
        Rplus_assoc (error n)
          (- (b n/2^n * (2 * approx n + b n/2^n)))
          (b n/2^n * (2 * approx n + b n/2^n))
      || _ <= _ + X @X by <- Rplus_opp_l (b n / 2 ^ n * (2 * approx n + b n / 2 ^ n))
      || _ <= X @X by <- Rplus_0_r (error n)
      || X @X by ltac:(rewrite H; reflexivity)).
Qed.

(*
  Proves that every bit is greater than or equal
  to 0.
*)
Lemma b_lower_bound
  :  forall n : nat, 0 <= b n.
Proof.
  exact
    (fun n
      => sumbool_ind
           (fun _ => 0 <= b n)
           (fun H : b n = 0
             => Req_le_sym 0 (b n) H)
           (fun H : b n = 1
             => Rle_0_1 || 0 <= X @X by H)
           (b_is_bit n)).
Qed.

(**
  Proves that [approx] is always positive.
*)
Lemma approx_is_positive
  :  forall n : nat, 0 <= approx n.
Proof.
  exact
    (nat_ind _
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
           || 0 <= X @X by (approx_Sn n))).
Qed.

(**
  Expresses the square of [approx] in terms of
  [a] and [error].
*)
Lemma approx_n_sqr
  :  forall n : nat, a - error n = (approx n)^2.
Proof.
  exact
    (fun n
      => Rplus_eq_compat_r (- error n) a ((approx n)^2 + error n) (spec n)
           || a - error n = X                @X by <- Rplus_assoc ((approx n)^2) (error n) (- (error n))
           || a - error n = (approx n)^2 + X @X by <- Rplus_opp_r (error n)
           || a - error n = X                @X by <- Rplus_0_r ((approx n)^2)).
Qed.

(**
  Represents the [approx] in terms of [a] and
  [error].
*)
Lemma approx_n
  :  forall n : nat, sqrt (a - error n) = approx n.
Proof.
  exact
    (fun n
      => f_equal sqrt (approx_n_sqr n)
           || sqrt (a - error n) = X @X by <- sqrt_pow2 (approx n) (approx_is_positive n)).
Qed.

Lemma approx_sqr_is_positive_alt
  :  forall n : nat, 0 <= a - error n.
Proof.
  exact
    (fun n
      => pow_le (approx n) 2 (approx_is_positive n)
           || 0 <= X @X by approx_n_sqr n).
Qed.

Lemma approx_sqr_is_positive : forall n : nat, 0 <= (approx n)^2.
Proof.
  intro n.
  apply (pow_le (approx n) 2 (approx_is_positive n)).
Qed.

Lemma error_upper_bound_a : forall n : nat, error n <= a.
Proof.
  intro n.
  apply (le_eq ((approx n)^2) (error n) a (approx_sqr_is_positive n)).
  exact (eq_sym (spec n)).
Qed.

(**
  Asserts a weak constant upper bound for
  [approx].

  approx n = sqrt(a - error n) < sqrt(2)
*)
Lemma approx_upper_bound
  :  forall n : nat, approx n < sqrt 2.
Proof.
  intro n.
  rewrite <- (sqrt_square (approx n) (approx_is_positive n)).
  rewrite <- (pow2 (approx n)).
  apply (sqrt_lt_1_alt ((approx n)^2) 2).
  split.
  + exact (approx_sqr_is_positive n).
  + refine (Rle_lt_trans ((approx n)^2) a 2 _ a_upper_bound).
    apply (le_eq_comm ((approx n)^2) (error n) a (error_is_positive n) (eq_sym (spec n))).
Qed.

Lemma a_upper_bound_0
  : forall n : nat, approx n + 1/2^n + 1/2^n = approx n + 2/2^n.
Proof.
  intro n.
  rewrite (Rplus_assoc (approx n) (1/2^n) (1/2^n)).
  unfold Rdiv.
  rewrite <- (Rmult_plus_distr_r 1 1 (/2^n)).
  reflexivity.
Qed.

Lemma a_upper_bound_1
  : forall n : nat, 2/2^(S n) = 1/2^n.
Proof.
  intro n.
  simpl.
  unfold Rdiv.
  rewrite (Rinv_mult_distr 2 (2^n) neq_2_0 (pow_nonzero 2 n neq_2_0)).
  rewrite <- (Rmult_assoc 2 (/2) (/2^n)).
  rewrite (Rinv_r_simpl_r 2 (/2^n) neq_2_0).
  exact (eq_sym (Rmult_1_l (/2^n))).
Qed.

Lemma b_is_positive : forall n : nat, 0 <= b n.
Proof.
  intro n.
  destruct (b_is_bit n) as [H|H]; rewrite H.
  + exact (Rle_refl 0).  
  + exact Rle_0_1.
Qed.

(* Proves that [approx] is monotonically increasing. *)
Lemma approx_inc : forall n : nat, approx n <= approx (S n).
Proof.
  intro n.
  exact
    (le_eq_comm (approx n) (b n/2^n) (approx (S n))
      (Rle_mult_inv_pos (b n) (2^n) (b_is_positive n) (pow_lt 2 n Rlt_0_2))
      (eq_sym (approx_Sn n))).
Qed.

(*
  (approx n + 1/2^n)^2 <= (approx (S n) + 1/2^n)^2
                       <= (approx n + b n/2^n + 1/2^n)^2
  b n = 0
                       <= (approx n + 1/2^n)^2
                       reflexivity
  b n = 1
                       <= (approx n + 1/2^n + 1/2^n)^2
                       trivial 
*)
Lemma a_upper_bound_2
  : forall n : nat, (approx n + 1/2^n)^2 <= (approx (S n) + 2/2^(S n))^2.
Proof.
  intro n.
  rewrite (a_upper_bound_1 n).
  rewrite (approx_Sn n).
  destruct (b_is_bit n) as [H|H]; rewrite H.
  + unfold Rdiv; rewrite (Rmult_0_l (/2^n)); rewrite (Rplus_0_r (approx n));
    exact (Rle_refl ((approx n + 1/2^n)^2)).
  + rewrite (a_upper_bound_0 n).
    apply (pow_incr (approx n + 1/2^n) (approx n + 2/2^n) 2).
    split.
    - apply (Rplus_le_le_0_compat (approx n) (1/2^n)).
      * exact (approx_is_positive n).
      * exact (Rle_mult_inv_pos 1 (2^n) Rle_0_1 (pow_lt 2 n Rlt_0_2)).
    - apply (Rplus_le_compat_l (approx n) (1/2^n) (2/2^n)).
      unfold Rdiv.
      apply (Rmult_le_compat_r (/2^n) 1 2).
      * rewrite <- (Rmult_1_l (/2^n)).
        exact (Rle_mult_inv_pos 1 (2^n) Rle_0_1 (pow_lt 2 n Rlt_0_2)).
      * exact (le_1_2).
Qed.

Theorem a_upper_bound_approx
  :  forall n : nat, a < (approx n + 2/2^n)^2.
Proof.
  exact
    (nat_ind _
      ((Rlt_trans a 2 4
        a_upper_bound
        (ltac:(lra)))
        || a < X @X by (ltac:(field) : (0 + 2/2^0)^2 = 4)
        || a < (X + 2/2^0)^2 @X by approx_0)
      (fun n (H : a < (approx n + 2/2^n)^2)
        => sumbool_ind
             (fun _ => a < (approx (S n) + 2/2^(S n))^2)
             (fun H0 : b n = 0
               => Rlt_le_trans a
                    ((approx n + 1/2^n)^2)
                    ((approx (S n) + 2/2^(S n))^2)
                    (Rle_lt_trans a
                      ((approx n)^2 + error n)
                      ((approx n)^2 + 1/2^n*(2*approx (n) + 1/2^n))
                      (Req_le a
                        ((approx n)^2 + error n)
                        (spec n))
                      (Rplus_lt_compat_l
                        ((approx n)^2)
                        (error n)
                        (1/2^n*(2*approx (n) + 1/2^n))
                        (b_0 n H0))
                      || a < X @X by (ltac:(ring) : ((approx (n) + 1/2^n)^2) = (approx (n)^2 + 1/2^n*(2*approx (n) + 1/2^n))))
                    (a_upper_bound_2 n))
             (fun H0 : b n = 1
               => let H1
                    :  approx (S n) = approx n + 1/2^n
                    := approx_Sn n
                         || approx (S n) = approx n + (X/2^n) @X by <- H0 in
                  H
                  || a < X^2 @X by a_upper_bound_0 n
                  || a < (X + 1/2^n)^2 @X by H1
                  || a < (approx (S n) + X)^2 @X by a_upper_bound_1 n)
             (b_is_bit n))).
Qed.

Lemma error_Sn_plus
  :  forall n : nat, error (S n) + (b n/2^n) * (2 * approx n + (b n/2^n)) = error n.
Proof.
  intro n.
  rewrite (error_Sn n).
  unfold Rminus.
  rewrite
    (Rplus_assoc
      (error n)
      (- ((b n/2^n) * (2 * approx n + (b n/2^n))))
         ((b n/2^n) * (2 * approx n + (b n/2^n)))).
  rewrite (Rplus_opp_l ((b n/2^n) * (2 * approx n + (b n/2^n)))).
  exact (Rplus_0_r (error n)).
Qed.

Lemma error_upper_bound_const_0
  : forall n : nat, - ((b n)/(2^n) * (2 * approx n + (b n)/(2^n))) <= 0.
Proof.
  intro n.
  apply (Rle_minus_0 ((b n/2^n) * (2 * approx n + (b n/2^n)))).
  destruct (b_is_bit n) as [H|H]; rewrite H; unfold Rdiv.
  + rewrite (Rmult_0_l (/2^n)).
    rewrite (Rmult_0_l (2 * approx n + 0)).
    exact (Rle_refl 0).
  + rewrite (Rmult_1_l (/2^n)).
    apply (Rmult_le_pos (/2^n) (2 * approx n + /2^n) (Rle_inv_2n n)).
    refine (Rplus_le_le_0_compat (2 * approx n) (/2^n) _ (Rle_inv_2n n)).
    exact (Rmult_le_pos 2 (approx n) le_0_2 (approx_is_positive n)).
Qed.

(** Proves that [error] is always less than 4. *)
Theorem error_upper_bound_const
  :  forall n : nat, error n < 4.
Proof.
  exact
    (nat_ind _
      (Rlt_trans
        (error 0) 2 4
        (a_upper_bound
          || X < 2 @X by error_0)
        (ltac:(lra) : 2 < 4))
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
           || error (S n) < X @X by <- Rplus_0_r 4)).
Qed.

Lemma error_upper_bound_approx_0
  :  forall n : nat, (approx n)^2 + (4/2^n)*(approx n + 1/2^n) = (approx n + 2/2^n)^2.
Proof.
  intro n.
  rewrite (sqr_expand (approx n) (2/2^n)).
  unfold Rdiv.
  rewrite <- (Rmult_1_r 2) at 6.
  rewrite (Rmult_assoc 2 1 (/2^n)).
  rewrite <- (Rmult_plus_distr_l 2 (approx n) (1 * /2^n)).
  rewrite (Rmult_assoc 2 (/2^n) _).
  rewrite <- (Rmult_assoc (/2^n) 2 (approx n + (1 * /2^n))).
  rewrite (Rmult_comm (/2^n) 2).
  rewrite (Rmult_assoc 2 (/2^n) (approx n + (1 * /2^n))).
  rewrite <- (Rmult_assoc 2 2 (/2^n * (approx n + (1 * /2^n)))).
  rewrite eq_2_2_4.
  rewrite <- (Rmult_assoc 4 (/2^n) (approx n + 1 * /2^n)).
  reflexivity.
Qed.

(**
  Proves a significant constraint on [error]
  and [approx].
*)
Theorem error_upper_bound_approx
  :  forall n : nat, error n < (4/2^n)*(approx n + 1/2^n).
Proof.
  exact
    (fun n
      => Rplus_lt_compat_r
           (- ((approx n)^2))
           a
           ((4/2^n)*(approx n + 1/2^n) + (approx n)^2)
           (a_upper_bound_approx n 
             || a < X @X by error_upper_bound_approx_0 n
             || a < X @X by <- Rplus_comm ((approx n)^2) ((4/2^n)*(approx n + 1/2^n)))
         || X < ((4/2^n)*(approx n + 1/2^n) + (approx n)^2) - ((approx n)^2) @X by <- error_n n
         || error n < X                              @X by <- Rplus_assoc ((4/2^n)*(approx n + 1/2^n)) ((approx n)^2) (- ((approx n)^2))
         || error n < (4/2^n)*(approx n + 1/2^n) + X @X by <- Rplus_opp_r ((approx n)^2)
         || error n < X                              @X by <- Rplus_0_r ((4/2^n)*(approx n + 1/2^n))).
Qed.

Lemma rem_register_even_exp_0
  :  forall n : nat, (4/2^n)*(approx n + 1/2^n) < (4/2^n)*(sqrt 2 + 1/2^n).
Proof.
  intro n.
  apply (Rmult_lt_compat_l (4/2^n) (approx n + 1/2^n) (sqrt 2 + 1/2^n)).
  + unfold Rdiv.
    apply (Rlt_mult_inv_pos 4 (2^n) lt_0_4 (pow_lt 2 n Rlt_0_2)).
  + apply (Rplus_lt_compat_r (1/2^n) (approx n) (sqrt 2) (approx_upper_bound n)).
Qed.
    

(**
  Is equivalent to:
  1/2^(n+1) + sqrt(2) < 2
  1/2^(n+1) + sqrt(2) < 1/2^(n+1) + 1.5 <= 2
                        1/2^(n+1)       <= 2 - 1.5
                        1/2^(n+1)       <= 1/2
  
*)
Lemma rem_register_even_exp_1
  :  forall n : nat, (4/2^(S n))*(sqrt 2 + 1/2^(S n)) < 8/2^(S n).
Proof.
  intro n.
  unfold Rdiv.
  simpl.
  rewrite (Rinv_mult_distr 2 (2^n) neq_2_0 (pow_nonzero 2 n neq_2_0)).
  rewrite <- (Rmult_assoc 4 (/2) (/2^n)). fold (Rdiv 4 2). rewrite div_eq_4_2.
  rewrite <- (Rmult_assoc 8 (/2) (/2^n)). fold (Rdiv 8 2). rewrite div_eq_8_2.
  rewrite (Rmult_assoc 2 (/2^n) (sqrt 2 + 1 * (/2 * /2^n))).
  rewrite (Rmult_comm (/2^n) (sqrt 2 + 1 * (/2 * /2^n))).
  rewrite <- (Rmult_assoc 2 (sqrt 2 + 1 * (/2 * /2^n)) (/2^n)).
  apply (Rmult_lt_compat_r (/2^n) (2 * (sqrt 2 + 1 * (/2 * /2^n))) 4).
  + exact (Rlt_inv_2n n).
  + rewrite <- eq_2_2_4.
    apply (Rmult_lt_compat_l 2 (sqrt 2 + 1 * (/2 * /2^n)) 2).
    - exact lt_0_2.
    - refine
        (Rlt_le_trans
          (sqrt 2 + 1 * (/2 * /2^n))
          (3/2 + 1 * (/2 * /2^n))
          2 _ _). 
      * apply (Rplus_lt_compat_r (1 * (/2 * /2^n))).
        exact (lt_sqrt_div_3_2).
      * rewrite (Rmult_1_l (/2 * /2^n)).
        rewrite <- (Rmult_1_l (/2)).
        unfold Rdiv.
        induction n as [m|m].
        ** rewrite (pow_O 2).
           rewrite Rinv_1.
           rewrite (Rmult_1_r (1 * /2)).
           rewrite <- (Rmult_plus_distr_r 3 1 (/2)).
           rewrite eq_3_1_4.
           fold (Rdiv 4 2).
           rewrite div_eq_4_2.
           exact (Rle_refl 2).
        ** simpl.
           apply
             (Rle_trans
               (3 * / 2 + 1 * / 2 * / (2 * 2 ^ m))
               (3 * / 2 + 1 * / 2 * / 2 ^ m)
               2).
           *** apply
                 (Rplus_le_compat_l
                   (3*/2)
                   (1 * /2 * /(2 * 2^m))
                   (1 * /2 * /2^m)).
               rewrite (Rmult_1_l (/2)).
               apply (Rmult_le_compat_l (/2) (/(2 * 2 ^ m)) (/2^m)).
               apply (neq_inv_2_0).
               rewrite (Rinv_mult_distr 2 (2^m) neq_2_0 (pow_nonzero 2 m neq_2_0)).
               rewrite <- (Rmult_1_l (/2^m)) at 2.
               refine (Rmult_le_compat_r (/2^m) (/2) 1 (Rle_inv_2n m) _).
               apply (Rmult_le_reg_l 2 (/2) 1).
               **** exact lt_0_2.
               **** rewrite (Rinv_r 2); [rewrite (Rmult_1_r 2); exact le_1_2|exact neq_2_0].
           *** assumption.
Qed.
  
(**
  Proves that the width used to store
  intermediate error values is large enough to
  accomodate every possible value without a loss
  of precision.
*)
Theorem rem_register_even_exp
  :  forall n : nat, error n < 8/2^n.
Proof.
  exact
    (nat_ind _
      (Rlt_trans
        (error 0)
        4
        (8/2^0)
        (error_upper_bound_const 0)
        ((ltac:(lra) : 4 < 8)
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
               (rem_register_even_exp_1 n)))).
Qed.

(*
  This file proves that the width used by the
  rem register in Hausner's implementation if
  large enough to store any intermediate value
  that may result while computing the square
  root of a floating point binary number having
  an odd exponent.
*)

Require Import base.
Require Import aux.
Require Import Reals.
Require Import micromega.Lra.

Open Scope R_scope.

(**
  Represents the mantissa of the number that we
  are computing the square root of.

  Note: in this development we are considering the case where the
  exponent of the number is odd. To simplify our calculations, we
  multiply the mantissa, [a], by 2 and subtract 1 from the exponent
  to produce an even exponent. Consequently, we compute the sqrt of
  [2 a] not [a]. [approx] will represent our approximation for the
  square root of [2 a].
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
  n-th approximation of the square root of [2 a].

  Note: see note for [a].
*)
Fixpoint approx (n : nat) : R :=
  match n with
  | 0 => 0
  | S m => approx m + (b m/2^m)
  end.

(**
  Accepts a natural number, [n], and returns
  the difference between [2 a] and the square of
  our n-th approximation.
*)
Parameter error : nat -> R.

(** Asserts that the error is always positive. *)
Axiom error_is_positive : forall n : nat, 0 <= error (n).

(**
  Asserts the relationship between [2 a], our
  approximation for the square root of [2 a],
  and the discrepancy between the square of our
  approximation and [2 a].
*)
Axiom spec : forall n : nat, 2*a = (approx n)^2 + error n.

(*
  The upper bound for approx where we [append] a 1 bit every
  iteration.
*)
Fixpoint approx_ub_strict (n : nat) : R :=
  match n with
  | 0 => 0
  | S m => approx_ub_strict m + 1/(2^m)
  end.

(*
  Prove that the upper bound for approx converges to 2, but is
  always 2/2^n less than 2.
*)
Lemma approx_ub_strict_eqn : forall n : nat, approx_ub_strict n + 2/2^n = 2.
Proof.
  induction n as [|m Hm]; unfold approx_ub_strict.
  + lra.
  + fold (approx_ub_strict m).
    rewrite Rplus_assoc.
    rewrite eq_2_2n.
    rewrite eq_1_2n.
    assumption.
Qed.
    
(*
  Verifies that approx_ub_strict is in fact an upper bound for
  approx.
*)
Lemma approx_ub_strict_is_ub : forall n : nat, approx n <= approx_ub_strict n.
Proof.
  induction n as [|m Hm]; unfold approx_ub_strict.
  + unfold approx.
    lra.
  + unfold approx. 
    fold (approx_ub_strict m).
    destruct (b_is_bit m) as [Hb|Hb]; rewrite Hb.
    - apply (Rplus_le_compat (approx m) (approx_ub_strict m) (0/2^m) (1/2^m)).
      * assumption.
      * unfold Rdiv.
        rewrite (Rmult_0_l (/2^m)).
        apply (Rle_mult_inv_pos 1 (2^m) (ltac:(lra) : 0 <= 1) (pow_lt 2 m lt_0_2)).
    - apply (Rplus_le_compat_r (1/2^m) (approx m) (approx_ub_strict m)).
      assumption.
Qed.

(*
  Approx has the form b0.b1 b2... which is
  always less than 2 no matter how many bits
  you append.
*)
Lemma limit : forall n : nat, approx n + 1/2^n < 2.
Proof.
  intro n.
  rewrite <- (approx_ub_strict_eqn n) at 2.
  apply (Rplus_le_lt_compat (approx n) (approx_ub_strict n) (1/2^n) (2/2^n)).
  + exact (approx_ub_strict_is_ub n).
  + unfold Rdiv.
    apply (Rmult_lt_compat_r (/2^n) 1 2 (Rlt_inv_2n n)).
    lra.
Qed.

Lemma approx_ub : forall n : nat, approx n < 2 - 1/2^n.
Proof.
  intro n.
  apply (Rplus_lt_reg_r (1/2^n) (approx n) (2 - 1/2^n)).
  unfold Rminus.
  rewrite (Rplus_assoc 2 (- (1/2^n)) (1/2^n)).
  rewrite (Rplus_opp_l (1/2^n)).
  rewrite (Rplus_0_r 2).
  exact (limit n).
Qed.

Lemma two_a_lt_4
  : 2*a < 4.
Proof.
  exact
    (Rmult_lt_compat_l 2 a 2
      (ltac:(lra) : 0 < 2)
      a_upper_bound
    || 2 * a < X @X by (ltac:(ring) : (2*2) = 4)).
Qed.

(**
  Proves that the discrepancy between the square
  of our initial approximation and [2 a] equals
  [2 a].
*)
Lemma error_0
  :  error 0 = 2 * a.
Proof.
  apply eq_sym.
  rewrite <- (Rplus_0_l (error 0)).
  rewrite <- (Rmult_0_l (0 * 1)).
  exact (spec 0).
Qed.

Lemma error_n 
  :  forall n : nat, 2*a - (approx n)^2 = error n.
Proof.
  intro n.
  rewrite <- (Rplus_0_l (error n)).
  rewrite <- (Rplus_opp_r ((approx n)^2)).
  rewrite (Rplus_assoc ((approx n)^2) (- (approx n)^2) (error n)).
  rewrite <- (Rplus_comm (error n) (- (approx n)^2)).
  rewrite <- (Rplus_assoc ((approx n)^2) (error n) (- (approx n)^2)).
  exact (Rplus_eq_compat_r (- (approx n)^2) (2*a) ((approx n)^2 + (error n)) (spec n)).
Qed.

(**
  Provides an algebraic expansion for [error].

  note:
  error (S n) = error n - (b n)/(2^n) * (2 * approx n + (b n)/(2^n))
  error (S n) = error n - (b n)/(2^n) * (approx n + approx n + (b n)/(2^n))
  error (S n) = error n - (b n)/(2^n) * (approx n + approx (S n))
*)
Lemma error_Sn
  :  forall n : nat, error (S n) = error n - (b n)/(2^n) * (2 * approx n + (b n)/(2^n)).
Proof.
  intro n.
  rewrite <- (error_n (S n)).
  unfold approx.
  fold (approx n).
  rewrite (sqr_expand (approx n) (b n/2^n)).
  unfold Rminus.
  rewrite (Ropp_plus_distr ((approx n)^2) (b n/2^n * (2 * approx n + b n/2^n))).
  rewrite <- (Rplus_assoc (2 * a) (- (approx n)^2) (- (b n/2^n * (2 * approx n + b n/2^n)))).
  exact
    (Rplus_eq_compat_r
      (- (b n/2^n * (2 * approx n + b n/2^n)))
      (2 * a + - (approx n)^2)
      (error n)
      (error_n n)).
Qed.

(*
  In each iteration [n], we try to append a 1
  bit onto [approx]. If the result is larger than
  [2 a], we append a 0 instead.
*)
Axiom bn : forall n : nat, (approx n + 1/2^n)^2 > 2 * a <-> b n = 0.

(*
  Asserts bounds for [error] and [approx] based
  on the value of a given bit.

  2 a < (approx (n) + 1/2^n)^2
  approx (n)^2 + error (n) < (apporx (n) + 1/2^n)^2
  approx (n)^2 + error (n) < approx (n)^2 + 1/2^n (2 approx (n) + 1/2^n)
  error (n) < approx (n)^2 + 1/2^n (2 approx (n) + 1/2^n)
*)
Lemma b_0 : forall n : nat, b n = 0 -> error n < 1/2^n * (2 * approx n + 1/2^n).
Proof.
  intros n H.
  apply (Rplus_lt_reg_l ((approx n)^2) (error n) (1/2^n * (2 * approx n + 1/2^n))).
  rewrite <- (sqr_expand (approx n) (1/2^n)).
  rewrite <- (spec n).
  exact (Rlt_gt (2 * a) ((approx n + 1/2^n)^2) (proj2 (bn n) H)).
Qed.

(*
  0 <= error (n + 1)
  0 <= error (n) - b (n)/2^n (2 approx (n) + b (n)/2^n)
  b (n)/2^n (2 approx (n) + b (n)/2^n) <= error (n)
*)
Lemma b_1 : forall n : nat, b n = 1 -> 1/2^n * (2 * approx n + 1/2^n) <= error n.
Proof.
  intros n H.
  rewrite <- H.
  apply
    (Rplus_le_reg_r
      (- (b n/2^n * (2 * approx n + b n/2^n)))
      (b n/2^n * (2 * approx n + b n/2^n))
      (error n)).
  rewrite (Rplus_opp_r (b n/2^n * (2 * approx n + b n/2^n))).
  fold (Rminus (error n) (b n/2^n * (2 * approx n + b n/2^n))).
  rewrite <- (error_Sn n).
  exact (error_is_positive (S n)).
Qed.
  
(*
  Proves that every bit is greater than or equal
  to 0.
*)
Lemma b_lower_bound
  :  forall n : nat, 0 <= b n.
Proof.
  intro n.
  destruct (b_is_bit n) as [H|H].
  + exact (Req_le_sym 0 (b n) H).
  + rewrite H.
    exact (Rle_0_1).
Qed.

(**
  Proves that [approx] is always positive.
*)
Lemma approx_is_positive
  :  forall n : nat, 0 <= approx n.
Proof.
  induction n as [|m H].
  + exact (Req_le_sym 0 (approx 0) eq_refl).
  + unfold approx.
    fold (approx m).
    apply (Rle_trans 0 (approx m + 0) (approx m + (b m)/(2^m))).
    - rewrite (Rplus_0_r (approx m)); assumption.
    - apply (Rplus_le_compat_l (approx m) 0 ((b m)/(2^m))).
      rewrite <- (Rmult_0_l (/2^m)).
      apply (Rmult_le_compat_r (/2^m) 0 (b m)).
      * exact (Rlt_le 0 (/(2^m)) (Rinv_0_lt_compat (2^m) (pow_lt 2 m Rlt_0_2))).
      * exact (b_lower_bound m).
Qed.

(* Proves that [approx] is monotonically increasing. *)
Lemma approx_inc : forall n : nat, approx n <= approx (S n).
Proof.
  intro n.
  unfold approx.
  fold (approx n).
  destruct (b_is_bit n) as [Hb|Hb]; rewrite Hb.
  + lra.
  + rewrite <- (Rplus_0_r (approx n)) at 1.
    apply (Rplus_le_compat_l (approx n) 0 (1/2^n)).
    unfold Rdiv.
    exact (Rle_mult_inv_pos 1 (2^n) ltac:(lra) (pow_lt 2 n lt_0_2)).
Qed.

Lemma a_upper_bound_2
  : forall n : nat, (approx n + 1/2^n)^2 <= (approx (S n) + 2/2^(S n))^2.
Proof.
  intro n.
  apply (pow_incr (approx n + 1/2^n) (approx (S n) + 2/2^(S n)) 2).
  split.
  apply (Rplus_le_le_0_compat (approx n) (1/2^n) (approx_is_positive n) (le_0_1_2n n)).
  + rewrite (eq_2_2n n).
    apply (Rplus_le_compat_r (1/2^n) (approx n) (approx (S n))).
    exact (approx_inc n).
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
Proof.
  induction n as [|m Hm].
  + unfold approx.
    rewrite (Rplus_0_l (2/2^0)).
    unfold Rdiv.
    simpl.
    rewrite (RMicromega.Rinv_1 2).
    rewrite (Rmult_1_r 2).
    exact (Rmult_lt_compat_l 2 a 2 lt_0_2 a_upper_bound).
  + destruct (b_is_bit m) as [Hb|Hb].
    - apply (Rlt_le_trans
        (2*a)
        ((approx m + 1/2^m)^2)
        ((approx (S m) + 2/2^(S m))^2)).
      * assert ((approx m + 1/2^m)^2 = (approx m)^2 + 1/2^m*(2*approx m + 1/2^m)) as H.
        ** lra.
        ** rewrite H.
           exact (Rle_lt_trans
             (2*a)
             ((approx m)^2 + error m)
             ((approx m)^2 + 1/2^m*(2*(approx m) + 1/2^m))
             (Req_le
               (2*a)
               ((approx m)^2 + error m)
               (spec m))
             (Rplus_lt_compat_l
               ((approx m)^2)
               (error m)
               (1/2^m*(2*(approx m) + 1/2^m))
               (b_0 m Hb))).
      * exact (a_upper_bound_2 m).
    - rewrite (eq_2_2n m).
      unfold approx.
      fold (approx m).
      rewrite Hb.
      rewrite (Rplus_assoc (approx m) (1/2^m) (1/2^m)).
      rewrite (eq_1_2n m).
      assumption.
Qed.

Lemma error_upper_bound_approx_0
  :  forall n : nat, (approx n)^2 + (4/2^n)*(approx n + 1/2^n) = (approx n + 2/2^n)^2.
Proof.
  intro n.
  rewrite (sqr_expand (approx n) (2/2^n)).
  unfold Rdiv.
  rewrite <- (Rmult_plus_distr_l 2 (approx n) (/2^n)).
  rewrite (Rmult_assoc 2 (/2^n) (2 * (approx n + /2^n))).
  rewrite <- (Rmult_assoc (/2^n) 2 (approx n + /2^n)).
  rewrite (Rmult_comm (/2^n) 2).
  rewrite (Rmult_assoc 2 (/2^n) (approx n + /2^n)).
  rewrite <- (Rmult_assoc 2 2 (/2^n * (approx n + /2^n))).
  rewrite eq_2_2_4.
  rewrite (Rmult_1_l (/2^n)).
  rewrite (Rmult_assoc 4 (/2^n) (approx n + /2^n)).
  reflexivity.
Qed.

(**
  Proves a significant constraint on [error]
  and [approx].
*)
Theorem error_upper_bound_approx
  :  forall n : nat, error n < (4/2^n)*(approx n + 1/2^n).
Proof.
  intro n.
  rewrite <- (Rplus_0_r ((4/2^n)*(approx n + 1/2^n))).
  rewrite <- (Rplus_opp_r ((approx n)^2)).
  rewrite <- (Rplus_assoc ((4/2^n)*(approx n + 1/2^n)) ((approx n)^2) (- ((approx n)^2))).
  rewrite <- (error_n n).
  apply (Rplus_lt_compat_r
    (- ((approx n)^2))
    (2*a)
    ((4/2^n)*(approx n + 1/2^n) + (approx n)^2)).
   rewrite <- (Rplus_comm ((approx n)^2) ((4/2^n)*(approx n + 1/2^n))).
   rewrite (error_upper_bound_approx_0 n).
   exact (a_upper_bound_approx n).
Qed.

(*
  error n < (4/2^n)*(approx n + 1/2^n).
  error n < (4/2^n)*(2 - 1/2^n + 1/2^n).
  error n < (4/2^n)*2
  error n < 8/2^n
*)
Theorem rem_register_odd_exp :
  forall n : nat, error n < 8/2^n.
Proof.
  intro n.
  unfold Rdiv.
  rewrite <- Rmult_4_2.
  rewrite (Rmult_assoc 4 2 (/2^n)).
  rewrite (Rmult_comm 2 (/2^n)).
  rewrite <- (Rmult_assoc 4 (/2^n) 2).
  rewrite <- (Rplus_0_r 2) at 2.
  rewrite <- (Rplus_opp_l (1/2^n)).
  rewrite <- (Rplus_assoc 2 (-(1/2^n)) (1/2^n)).
  fold (Rminus 2 (1/2^n)).
  rewrite <- (Rdiv_4_2).
  apply (Rlt_trans (error n)
    (4/2^n * (approx n + 1/2^n))
    (4/2^n * (2 - 1/2^n + 1/2^n))).
  + exact (error_upper_bound_approx n).
  + apply (Rmult_lt_compat_l
      (4/2^n)
      (approx n + 1/2^n)
      (2 - 1/2^n + 1/2^n)
      (ltac:(
        unfold Rdiv;
        exact (Rmult_lt_0_compat 4 (/2^n) lt_0_4 (Rlt_inv_2n n))))).
    exact (Rplus_lt_compat_r 
      (1/2^n)
      (approx n)
      (2 - 1/2^n)
      (approx_ub n)).
Qed.
 
Close Scope R_scope.

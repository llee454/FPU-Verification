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
  multiply the mantissa, [a], by 2 and subtract  1 from the exponent
  to produce aneven exponent. Consequently, we compute the sqrt of
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
Parameter approx : nat -> R.

(**
  Asserts that our initial approximation of the
  square root of [2 a] is 0.
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
    unfold Rdiv.
    unfold pow at 2.
    fold pow.
    rewrite (Rinv_mult_distr 2 (2^m) neq_2_0 (pow_nonzero 2 m neq_2_0)).
    rewrite <- (Rmult_assoc 2 (/2) (/2^m)).
    rewrite (Rinv_r 2 neq_2_0).
    assert (2/2^m = 1 * /2^m + 1 * /2^m) as H.
    - lra.
    - rewrite <- H.
      assumption.
Qed.
    
(*
  Verifies that approx_ub_strict is in fact an upper bound for
  approx.
*)
Lemma approx_ub_strict_is_ub : forall n : nat, approx n <= approx_ub_strict n.
Proof.
  induction n as [|m Hm]; unfold approx_ub_strict.
  + rewrite approx_0.
    lra.
  + rewrite approx_Sn.
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
  exact
    (eq_sym
      (spec 0
        || 2 * a = (X)^2 + error 0 @X by <- approx_0
        || 2 * a = X + error 0 @X by <- Rmult_0_l (0 * 1)
        || 2 * a = X @X by <- Rplus_0_l (error 0))).
Qed.

Lemma error_n 
  :  forall n : nat, 2*a - (approx n)^2 = error n.
Proof.
  exact
    (fun n
      => Rplus_eq_compat_r (- (approx n)^2) (2*a) ((approx n)^2 + (error n)) (spec n)
           || 2*a - (approx n)^2 = X                @X by <- Rplus_assoc ((approx n)^2) (error n) (- (approx n)^2)
           || 2*a - (approx n)^2 = (approx n)^2 + X @X by <- Rplus_comm (error n) (- (approx n)^2)
           || 2*a - (approx n)^2 = X                @X by Rplus_assoc ((approx n)^2) (- (approx n)^2) (error n)
           || 2*a - (approx n)^2 = X + error n      @X by <- Rplus_opp_r ((approx n)^2)
           || 2*a - (approx n)^2 = X                @X by <- Rplus_0_l (error n)).
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
  rewrite (approx_Sn n).
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

Lemma a_upper_bound_0
  : forall n : nat, approx n + 1/2^n + 1/2^n = approx n + 2/2^n.
Proof.
  intro.
  field.
  exact (pow_nonzero 2 n neq_2_0).
Qed.

Lemma a_upper_bound_1
  : forall n : nat, 2/2^(S n) = 1/2^n.
Proof.
  intro.
  (simpl).
  field.
  exact (pow_nonzero 2 n neq_2_0).
Qed.

(*
  Establishes an important upper bound on approx n.

  (approx n + 1/2^n)^2 <= (approx (S n) + 2/2^(S n))^2
                       <= (approx (S n) + 1/2^n)^2
                       <= (approx n + b n/2^n + 1/2^n)^2
  b n = 0
                       <= (approx n + 1/2^n)^2
                       reflexivity
  b n = 1
                       <= (approx n + 1/2^n + 1/2^n)^2
                       trivial 
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
    exact (pow_nonzero 2 n neq_2_0).
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
     lra.
     (apply Rmult_lt_0_compat).
      lra.
      (apply pow_lt).
      lra.
    (assert (0 <= approx n + 1 / 2 ^ n)).
     (apply Rplus_le_le_0_compat).
      (apply (approx_is_positive n)).
      (apply (Rle_mult_inv_pos 1 (2 ^ n))).
       lra.
       (apply (pow_lt 2 n)).
       lra.
     (assert (0 <= approx n + 1 / 2 ^ n + 2 / (2 * 2 ^ n))).
      (apply Rplus_le_le_0_compat).
       (apply H0).
       (apply (Rle_mult_inv_pos 2 (2 * 2 ^ n))).
        lra.
        (apply Rmult_lt_0_compat).
         lra.
         (apply (pow_lt 2 n)).
         lra.
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
Proof.
  exact
    (nat_ind _
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
                        (spec n))
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
             (b_is_bit n))).
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
  exact
    (fun n
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
         || error n < X                              @X by <- Rplus_0_r ((4/2^n)*(approx n + 1/2^n))).
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

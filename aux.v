(* A collection of auxiliary results about reals. *)
Require Import Reals.
Require Import micromega.Lra.

Open Scope R_scope.

Lemma neq_2_0 : 2 <> 0. Proof. lra. Qed.
Lemma le_1_2 : 1 <= 2. Proof. lra. Qed.
Lemma le_0_2 : 0 <= 2. Proof. lra. Qed.
Lemma lt_0_2 : 0 < 2. Proof. lra. Qed.
Lemma eq_2_2_4 : 2 * 2 = 4. Proof. lra. Qed.
Lemma lt_0_4 : 0 < 4. Proof. lra. Qed.
Lemma div_eq_4_2 : 4 / 2 = 2. Proof. lra. Qed.
Lemma div_eq_8_2 : 8 / 2 = 4. Proof. lra. Qed.
Lemma eq_3_1_4 : 3 + 1 = 4. Proof. lra. Qed.

Lemma neq_inv_2_0 : 0 <= /2.
Proof.
  apply (Rlt_le 0 (/2)).
  exact (pos_half_prf).
Qed.

Lemma le_eq : forall x y z : R, 0 <= x -> x + y = z -> y <= z.
Proof.
  intros x y z Hx H.
  rewrite <- H.
  rewrite <- (Rplus_0_l y) at 1.
  apply (Rplus_le_compat_r y 0 x Hx).
Qed.

Lemma le_eq_comm : forall x y z : R, 0 <= y -> x + y = z -> x <= z.
Proof.
  intros x y z Hy H.
  rewrite (Rplus_comm x y) in H.
  exact (le_eq y x z Hy H).
Qed.

Lemma Rle_minus_0 : forall x : R, 0 <= x -> - x <= 0.
Proof.
  intros x H.
  apply (le_eq x (- x) 0 H (Rplus_opp_r x)).
Qed.

Lemma Rle_inv_2n : forall n : nat, 0 <= /2^n.
Proof.
  intro n.
  rewrite <- (Rmult_1_l (/2^n)).
  exact (Rle_mult_inv_pos 1 (2^n) Rle_0_1 (pow_lt 2 n Rlt_0_2)).
Qed.

Lemma Rlt_inv_2n : forall n : nat, 0 < /2^n.
Proof.
  intro n.
  rewrite <- (Rmult_1_l (/2^n)).
  exact (Rlt_mult_inv_pos 1 (2^n) Rlt_0_1 (pow_lt 2 n Rlt_0_2)).
Qed.

Lemma pow2 : forall n : R, n^2 = n * n.
Proof.
  intro n.
  simpl.
  rewrite (Rmult_1_r n).
  reflexivity.
Qed.

Close Scope R_scope.

(* A collection of auxiliary results about reals. *)
Require Import base.
Require Import Reals.
Require Import micromega.Lra.

Open Scope R_scope.

Lemma neq_2_0 : 2 <> 0. Proof. lra. Qed.
Lemma le_1_2 : 1 <= 2. Proof. lra. Qed.
Lemma le_0_2 : 0 <= 2. Proof. lra. Qed.
Lemma le_0_4 : 0 <= 4. Proof. lra. Qed.
Lemma lt_0_2 : 0 < 2. Proof. lra. Qed.
Lemma eq_2_2_4 : 2 * 2 = 4. Proof. lra. Qed.
Lemma lt_0_4 : 0 < 4. Proof. lra. Qed.
Lemma div_eq_4_2 : 4 / 2 = 2. Proof. lra. Qed.
Lemma div_eq_8_2 : 8 / 2 = 4. Proof. lra. Qed.
Lemma eq_3_1_4 : 3 + 1 = 4. Proof. lra. Qed.
Lemma Rmult_4_2 : 4 * 2 = 8. Proof. lra. Qed.

Lemma Rminus_2_1 : 2 + - (1) = 1. Proof. lra. Qed.

Lemma Rdiv_4_2 : forall n : nat, 4/2^n = 4 * /2^n.
Proof.
  intro n.
  unfold Rdiv.
  reflexivity.
Qed.

Lemma Rdiv_expand : forall n : nat, 1/2^n = 1 * /2^n.
Proof.
  intro n.
  unfold Rdiv.
  reflexivity.
Qed.

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

Lemma sqr_expand : forall a b : R, (a + b)^2 = a^2 + b * (2 * a + b).
Proof.
  exact
    (fun a b =>
      eq_refl ((a + b)^2)
      || _ = (a + b) * X @X by <- Rmult_1_r (a + b)
      || _ = X @X by <- Rmult_plus_distr_r a b (a + b)
      || _ = X + _ @X by <- Rmult_plus_distr_l a a b
      || _ = X + _ + _ @X by pow2 a
      || _ = _ + _ + X @X by <- Rmult_plus_distr_l b a b
      || _ = X @X by <- Rplus_assoc (a^2) (a * b) (b * a + b * b)
      || _ = _ + X @X by Rplus_assoc (a * b) (b * a) (b * b)
      || _ = _ + (_ + X + _) @X by Rmult_comm a b
      || _ = _ + (X + _) @X by double (a * b)
      || _ = _ + (X + _) @X by Rmult_assoc 2 a b
      || _ = _ + X @X by Rmult_plus_distr_r (2 * a) b b
      || _ = _ + X @X by <- Rmult_comm (2 * a + b) b).
Qed.

Close Scope R_scope.

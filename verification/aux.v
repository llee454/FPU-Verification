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

Lemma eq_2_2n
  : forall n : nat, 2/2^(S n) = 1/2^n.
Proof.
  intro n.
  unfold Rdiv.
  unfold pow.
  fold pow.
  rewrite (Rinv_mult_distr 2 (2^n) neq_2_0 (pow_nonzero 2 n neq_2_0)).
  rewrite <- (Rmult_assoc 2 (/2) (/2^n)).
  rewrite (Rinv_r 2 neq_2_0).
  reflexivity.
Qed.

Lemma eq_1_2n
  : forall n : nat, 1/2^n + 1/2^n = 2/2^n.
Proof.
  intro n.
  unfold Rdiv.
  lra.
Qed.

Lemma le_0_1_2n : forall n : nat, 0 <= 1/2^n.
Proof.
  intro n.
  unfold Rdiv.
  exact (Rle_mult_inv_pos 1 (2^n) ltac:(lra) (pow_lt 2 n Rlt_0_2)).
Qed.

Lemma lt_0_1_2n : forall n : nat, 0 < 1/2^n.
Proof.
  intro n.
  unfold Rdiv.
  exact (Rlt_mult_inv_pos 1 (2^n) ltac:(lra) (pow_lt 2 n Rlt_0_2)).
Qed.

Lemma ln_pow : forall (x : R), 0 < x -> forall (n : nat), ln (x^n) = (INR n)*(ln x).
Proof.
  intros x Hx.
  induction n as [|m Hm].
  + simpl.
    rewrite ln_1.
    exact (eq_sym (Rmult_0_l (ln x))).
  + unfold pow.
    fold pow.
    rewrite (ln_mult x (x^m) Hx (pow_lt x m Hx)).
    rewrite Hm.
    rewrite <- (Rmult_1_l (ln x)) at 1.
    rewrite <- (Rmult_plus_distr_r 1 (INR m) (ln x)).
    rewrite (Rplus_comm 1 (INR m)).
    destruct m as [m|m]; simpl.
    - lra.
    - reflexivity.
Qed.

Definition Rlog x y := (ln y)/(ln x).

Definition Rlog2 x := Rlog 2 x.

Infix "^R" := Rpower (at level 30, right associativity) : R_scope.

Lemma ln_neq_0 : forall x : R, x <> 1 -> 0 < x -> ln x <> 0.
Proof.
  intros x Hneq_x_1 Hlt_0_x.
  rewrite <- ln_1.
  intro H.
  assert (x = 1) as H0.
  + exact (ln_inv x 1 Hlt_0_x (ltac:(lra) : 0 < 1) H).
  + contradiction.
Qed.

Lemma exp_neq_0 : forall x : R, exp x <> 0.
Proof.
  intro x.
  exact (not_eq_sym (Rlt_not_eq 0 (exp x) (exp_pos x))).
Qed.

Lemma Rpower_Rlog : forall x y : R, x <> 1 -> 0 < x -> 0 < y -> x ^R (Rlog x y) = y.
Proof.
  intros x y H_neq_x_1 H_lt_0_x H_lt_0_y.
  unfold Rpower.
  unfold Rlog.
  unfold Rdiv.
  rewrite (Rmult_assoc (ln y) (/ln x) (ln x)).
  rewrite (Rinv_l (ln x) (ln_neq_0 x H_neq_x_1 H_lt_0_x)).
  rewrite (Rmult_1_r (ln y)).
  exact (exp_ln y H_lt_0_y).
Qed.
    
Lemma ln_Rpower : forall x y : R, ln (x ^R y) = y * ln x.
Proof.
  intros x y.
  unfold Rpower.
  rewrite (ln_exp (y * ln x)).
  reflexivity.
Qed.

Lemma Rlog_pow : forall (x : R) (n : nat), x <> 1 -> 0 < x -> Rlog x (x^n) = INR n.
Proof.
  intros x n H_neq_x_1 H_lt_0_x.
  rewrite <- (Rpower_pow n x H_lt_0_x).
  unfold Rpower.
  unfold Rlog.
  rewrite (ln_exp (INR n * ln x)).
  unfold Rdiv.
  rewrite (Rmult_assoc (INR n) (ln x) (/ln x)).
  rewrite (Rinv_r (ln x) (ln_neq_0 x H_neq_x_1 H_lt_0_x)).
  exact (Rmult_1_r (INR n)).
Qed.

Lemma Rpower_nonzero : forall (x : R) (n : nat), 0 < x -> x ^R INR n <> 0.
Proof.
  intros x n H.
  rewrite (Rpower_pow n x H).
  exact (pow_nonzero x n (not_eq_sym (Rlt_not_eq 0 x H))).
Qed.

Close Scope R_scope.

(*
*)

Require Import base.
Require Import Reals.
Require Import Fourier.

Open Scope R_scope.

Section sqrt.

Parameter a : R.

Hypothesis a_lower_bound : 1 <= a. 

Hypothesis a_upper_bound : a < 2.

Parameter b : nat -> R.

Axiom b_is_bit : forall n : nat, {b n = 0}+{b n = 1}.

Parameter approx : nat -> R.

Axiom approx_0 : approx 0 = 0.

Axiom approx_n : forall n : nat, approx (S n) = approx n + (b n)/(2^n).

Parameter error : nat -> R.

Axiom error_is_positive : forall n : nat, 0 <= error (n).

Axiom murali : forall n : nat, a = (approx n)^2 + error n.

Definition error_0
  :  error 0 = a
  := eq_sym
       (murali 0
         || a = (X)^2 + error 0 @X by <- approx_0
         || a = X + error 0 @X by <- Rmult_0_l (0 * 1)
         || a = X @X by <- Rplus_0_l (error 0)).
     
Definition error_n 
  :  forall n : nat, a - (approx n)^2 = error n
  := fun n
       => Rplus_eq_compat_r (- (approx n)^2) a ((approx n)^2 + (error n)) (murali n)
            || a - (approx n)^2 = X @X by <- Rplus_assoc ((approx n)^2) (error n) (- (approx n)^2)
            || a - (approx n)^2 = (approx n)^2 + X @X by <- Rplus_comm (error n) (- (approx n)^2)
            || a - (approx n)^2 = X @X by Rplus_assoc ((approx n)^2) (- (approx n)^2) (error n)
            || a - (approx n)^2 = X + error n @X by <- Rplus_opp_r ((approx n)^2)
            || a - (approx n)^2 = X @X by <- Rplus_0_l (error n).

Definition theorem_0
  :  error 0 < 4
  := let H  : a < 2 := a_upper_bound in
     let H0 : error 0 = a := error_0 in
     ltac:(fourier).

Definition theorem_n_0
  :  forall n : nat, (approx n + (b n / 2^n))^2 = (approx n)^2 + (b n / 2^n) * (2 * approx n + (b n / 2^n))
  := fun n
       => ltac:(ring).

Definition b_lower_bound
  :  forall n : nat, 0 <= b n
  := fun n
       => sumbool_ind
            (fun _ => 0 <= b n)
            (fun H : b n = 0
              => Req_le_sym 0 (b n) H)
            (fun H : b n = 1
              => Rle_0_1 || 0 <= X @X by H)
            (b_is_bit n).

Axiom theorem_n_1_2 : forall n : nat, 0 <= approx n.

Axiom theorem_n_1
  :  forall n : nat, 0 < (b n / 2^n) * (2 * approx n + (b n / 2^n)).

Definition theorem_n
  :  forall n : nat, error n < 4/2^n -> error (S n) < 4
  := fun n H
       =>
          let H0
            :  error n - ((b n / 2^n) * (2 * approx n + (b n / 2^n))) = error (S n)
            := error_n (S n)
               || a - (X)^2 = error (S n) @X by <- approx_n n
               || a - X     = error (S n) @X by <- theorem_n_0 n
               || a + X     = error (S n) @X by <- Ropp_plus_distr ((approx n)^2) ((b n / 2^n) * (2 * approx n + (b n / 2^n)))
               || X         = error (S n) @X by Rplus_assoc a (- ((approx n)^2)) (- ((b n / 2^n) * (2 * approx n + (b n / 2^n))))
               || X - (b n / 2^n) * (2 * approx n + (b n / 2^n)) = error (S n) @X by <- error_n n
          in
          let H1
            :  error n - ((b n / 2^n) * (2 * approx n + (b n / 2^n))) < 4 - ((b n / 2^n) * (2 * approx n + (b n / 2^n)))
            := Rplus_lt_compat_r (- ((b n / 2^n) * (2 * approx n + (b n / 2^n))))
               (error n) 4 H
          in
          let H2
            :  error (S n) < 4 - ((b n / 2^n) * (2 * approx n + (b n / 2^n)))
            := H1
               || X < 4 - ((b n / 2^n) * (2 * approx n + (b n / 2^n))) @X by <- H0
          in
          let H3
            :  4 - ((b n / 2^n) * (2 * approx n + (b n / 2^n))) < 4
            := tech_Rgt_minus 4 ((b n / 2^n) * (2 * approx n + (b n / 2^n))) (theorem_n_1 n)
          in
          let H4
            :  error (S n) < 4
            := Rlt_trans (error (S n)) (4 - ((b n / 2^n) * (2 * approx n + (b n / 2^n)))) 4
                 H2 H3
          in H4.
          
Definition theorem
  :  forall n : nat, error n < 4
  := nat_ind _
       theorem_0
       theorem_n.

End sqrt.

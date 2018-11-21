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

Axiom a_upper_bound_mod : 2*a < 4.

Parameter b : nat -> R.

Axiom b_is_bit : forall n : nat, {b n = 0}+{b n = 1}.

Parameter approx : nat -> R.

Axiom approx_0 : approx 0 = 0.

Axiom approx_n : forall n : nat, approx (S n) = approx n + (b n)/(2^n).

Parameter error : nat -> R.

Axiom error_is_positive : forall n : nat, 0 <= error (n).

Axiom murali : forall n : nat, 2*a = (approx n)^2 + error n.

Definition error_0
  :  error 0 = 2*a
  := eq_sym
       (murali 0
         || 2*a = (X)^2 + error 0 @X by <- approx_0
         || 2*a = X + error 0 @X by <- Rmult_0_l (0 * 1)
         || 2*a = X @X by <- Rplus_0_l (error 0)).
     
Definition error_n 
  :  forall n : nat, 2*a - (approx n)^2 = error n
  := fun n
       => Rplus_eq_compat_r (- (approx n)^2) (2*a) ((approx n)^2 + (error n)) (murali n)
            || 2*a - (approx n)^2 = X @X by <- Rplus_assoc ((approx n)^2) (error n) (- (approx n)^2)
            || 2*a - (approx n)^2 = (approx n)^2 + X @X by <- Rplus_comm (error n) (- (approx n)^2)
            || 2*a - (approx n)^2 = X @X by Rplus_assoc ((approx n)^2) (- (approx n)^2) (error n)
            || 2*a - (approx n)^2 = X + error n @X by <- Rplus_opp_r ((approx n)^2)
            || 2*a - (approx n)^2 = X @X by <- Rplus_0_l (error n).

Axiom error_Sn : forall n : nat, error (S n) = error n - (b n)/(2^n) * (2 * approx n + (b n)/(2^n)).

Axiom theorem_0 : error 0 < 8/2^(0).

Axiom b_0 : forall n : nat, b n = 0 -> error n < 1/2^n * (2 * approx n + 1/2^n).

Axiom b_1 : forall n : nat, b n = 1 -> 1/2^n * (2 * approx n + 1/2^n) <= error n.

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

Axiom approx_upper_bound : forall n : nat, approx n < sqrt 4.

Definition approx_lower_bound
  :  forall n : nat, 0 <= approx n
  := nat_ind _
       (Req_le_sym 0 (approx 0) approx_0)
       (fun n (H : 0 <= approx n)
         => (* 0 <= approx (S n)
               0 <= approx n + (b n)/(2^n)
               0 <= approx n + 0 <= approx n + (b n)/(2^n)
               0 <= approx n *)
            Rle_trans 0
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
            || 0 <= X @X by (approx_n n)).

(* verified using Maxima *)
Axiom a_upper_bound_0
  : forall n : nat, approx n + 1/2^n + 1/2^n = approx n + 2/2^n.

(* verified using Maxima *)
Axiom a_upper_bound_1
  : forall n : nat, 2/2^(S n) = 1/2^n.

Axiom a_upper_bound_2
  : forall n : nat, (approx n + 1/2^n)^2 <= (approx (S n) + 2/2^(S n))^2.

Theorem a_upper_bound_approx
  :  forall n : nat, 2*a < (approx n + 2/2^n)^2.
Proof nat_ind _
       (a_upper_bound_mod
         || 2*a < X @X by (ltac:(field) : (0 + 2/2^0)^2 = 4)
         || 2*a < (X + 2/2^0)^2 @X by approx_0)
       (fun n (H : 2*a < (approx n + 2/2^n)^2)
         => sumbool_ind
              (fun _ => 2*a < (approx (S n) + 2/2^(S n))^2)
              (fun H0 : b n = 0
                => Rlt_le_trans (2*a)
                     ((approx n + 1/2^n)^2)
                     ((approx (S n) + 2/2^(S n))^2)
                     (Rle_lt_trans (2*a)
                       ((approx n)^2 + error n)
                       ((approx n)^2 + 1/2^n*(2*approx (n) + 1/2^n))
                       (Req_le (2*a)
                         ((approx n)^2 + error n)
                         (murali n))
                       (Rplus_lt_compat_l
                         ((approx n)^2)
                         (error n)
                         (1/2^n*(2*approx (n) + 1/2^n))
                         (b_0 n H0))
                       || (2*a) < X @X by (ltac:(ring) : ((approx (n) + 1/2^n)^2) = (approx (n)^2 + 1/2^n*(2*approx (n) + 1/2^n))))
                     (a_upper_bound_2 n))
              (fun H0 : b n = 1
                => let H1
                     :  approx (S n) = approx n + 1/2^n
                     := approx_n n
                          || approx (S n) = approx n + (X/2^n) @X by <- H0 in
                   H
                   || (2*a) < X^2 @X by a_upper_bound_0 n
                   || (2*a) < (X + 1/2^n)^2 @X by H1
                   || (2*a) < (approx (S n) + X)^2 @X by a_upper_bound_1 n)
              (b_is_bit n)).

Axiom error_upper_bound_const_0
  : forall n : nat, - ((b n)/(2^n) * (2 * approx n + (b n)/(2^n))) <= 0.

Definition error_upper_bound_const
  :  forall n : nat, error n < 4
  := nat_ind _
       (a_upper_bound_mod
         || X < 4 @X by error_0)
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

(* verified using Maxima *)
Axiom error_upper_bound_approx_0
  :  forall n : nat, (approx n)^2 + (4/2^n)*(approx n + 1/2^n) = (approx n + 2/2^n)^2.

Definition error_upper_bound_approx
  :  forall n : nat, error n < (4/2^n)*(approx n + 1/2^n)
  := fun n
       => Rplus_lt_compat_r
            (- ((approx n)^2))
            (2*a)
            ((4/2^n)*(approx n + 1/2^n) + (approx n)^2)
            (a_upper_bound_approx n 
              || 2*a < X @X by error_upper_bound_approx_0 n
              || 2*a < X @X by <- Rplus_comm ((approx n)^2) ((4/2^n)*(approx n + 1/2^n)))
          || X < ((4/2^n)*(approx n + 1/2^n) + (approx n)^2) - ((approx n)^2) @X by <- error_n n
          || error n < X @X by <- Rplus_assoc ((4/2^n)*(approx n + 1/2^n)) ((approx n)^2) (- ((approx n)^2))
          || error n < (4/2^n)*(approx n + 1/2^n) + X @X by <- Rplus_opp_r ((approx n)^2)
          || error n < X @X by <- Rplus_0_r ((4/2^n)*(approx n + 1/2^n)).

Axiom rem_register_even_exp_0
  : forall n : nat, (4/2^n)*(approx n + 1/2^n) < (4/2^n)*(sqrt 2 + 1/2^n).

(* verified using Maxima *)
Axiom rem_register_even_exp_1
  : forall n : nat, (4/2^(S (S n)))*(sqrt 2 + 1/2^(S (S n))) < 8/2^(S (S n)).

Axiom rem_register_even_exp_2
  : 4 = 8/2^(S 0).

Definition rem_register_even_exp
  :  forall n : nat, error n < 8/2^n
  := nat_ind _
       (Rlt_trans
         (error 0)
         4
         (8/2^0)
         (error_upper_bound_const 0)
         ((ltac:(fourier) : 4 < 8)
           || 4 < X @X by (ltac:(field) : 8/2^0 = 8)))
       (nat_ind
         (fun n => error n < 8/2^n -> error (S n) < 8/2^(S n))
         (fun _
           => error_upper_bound_const (S 0)
                || error (S 0) < X @X by <- rem_register_even_exp_2)
         (fun n _ _
           => Rlt_trans
                (error (S (S n)))
                ((4/2^(S (S n)))*(approx (S (S n)) + 1/2^(S (S n))))
                (8/2^(S (S n)))
                (error_upper_bound_approx (S (S n)))
                (Rlt_trans
                  ((4/2^(S (S n)))*(approx (S (S n)) + 1/2^(S (S n))))
                  ((4/2^(S (S n)))*(sqrt 2 + 1/2^(S (S n))))
                  (8/2^(S (S n)))
                  (rem_register_even_exp_0 (S (S n)))
                  (rem_register_even_exp_1 n)))).

End sqrt.

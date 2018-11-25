(**
  The Division module defines a function that implements floating
  point division.

  For simplicity, we only consider positive floating point numbers. We
  follow IEE 754 in representing floating point numbers using a scheme
  analogous to scientific notation. In our scheme, every floating
  point number is represented like 1.0101 * 2^(10). We represent these
  numbers as pairs of bit vectors. The first bit vector represents
  the significant digits - 10101 in our example. The second bit vector
  represents the bits in the exponent - 10 in our example.
*)

Require Import Vector.
Require Import PeanoNat.
Require Import Streams.
Require Import Eqdep.
Import VectorNotations.

Open Scope vector_scope.

(** Represents bits - i.e. binary digits. *)
Inductive bit_type : Set := bO | bI.

(** Accepts a bit and returns true iff it is 0. *)
Definition bit_is_zero (b : bit_type) : bool
  := match b with
       | b0 => true
       end.

(**
  Represents binary number widths - i.e. the
  number of bits used to represent binary
  numbers.
*)
Definition width_type : Set := {n : nat | 0 < n}.

(**
  Accepts a natural number [n] and a proof that
  [n] is greater than 0 and returns a binary
  string width.
*)
Definition width (n : nat) (H : 0 < n) := exist (fun n => 0 < n) n H.

Arguments width [n] H.

(**
  Accepts a binary number width and returns the
  equivalent natural number.
*)
Definition width_nat (w : width_type) : nat := proj1_sig w.

(**
  Accepts a binary number width and returns the
  next largest width.
*)
Definition width_S (w : width_type) : width_type
  := width (Nat.lt_lt_succ_r 0 (width_nat w) (proj2_sig w)).

(**
  Represents the 1 bit width, which is the base
  case for most recursions.
*)
Definition width_1 : width_type := width Nat.lt_0_1.

(**
  Represents bit numbers represented by a given
  number of bits.

  Note: [x0, x1, ..., xn] represents
  x0 + 2 x1 + ... + 2^n xn.
*)
Definition binary_type
  :  width_type -> Set
  := fun n => Vector.t bit_type (width_nat n).

(**
Definition binary_type_conv
  :  forall (n : nat) (H : 0 < n) (x : binary_type (width H)) (H0 : 0 < n),
     binary_type (width H0)
  := 
*)

(** Represents a one bit binary number. *)
Definition binary_singleton (x : bit_type) : binary_type width_1 := [x].

(**
*)
Definition binary_type_rec
  :  forall (P : forall w : width_type, binary_type w -> Set),
     (forall x : bit_type, P width_1 [x]) ->
     (forall (x0 : bit_type) (n : nat) (H : 0 < n) (xs : Vector.t bit_type n), P (width H) xs -> P (width_S (width H)) (x0 :: xs)) ->
     forall (w : width_type) (x : binary_type w), P w x
  := fun P f1 fn w
       => Vector.t_rect bit_type
            (fun (n : nat) (xs : Vector.t bit_type n) => forall (H : 0 < n), P (width H) xs)
            (fun H : 0 < 0 => False_rec _ (Nat.lt_irrefl 0 H))
            (fun (x0 : bit_type) (n : nat)
              => Vector.t_rect bit_type
                   (fun (m : nat) (xs : Vector.t bit_type m) => forall (H : 0 < S m), P (width H) (x0 :: xs))
                   (* case where n = 1 *)
                   (fun H0 : 0 < 1
                     => f1 x0 : P width_1 [x0]
                              (* : P (width H0) [x0] *))
                   (* case where n > 1 *)
                   (fun x1 m xs g (_ : 0 < n)
                     => fn x0 (S m) (Nat.lt_0_succ 0 m) (x1 :: xs) g))
            (width_nat w)
            (proj2_sig w).
                          

(**
  Accepts a binary number and returns true iff
  it is 0 - i.e. all of its bits equal 0.
*)
Definition binary_is_zero
  :  forall n : width_type, binary_type n -> bool
  := sig_rect
       (fun n => binary_type n -> bool)
       (fun n (H : 0 < n)
         => Vector.t_rect bit_type
              (fun m => binary_type m -> bool)
              true (* contradictory case *)
              (fun m
                => bit_type_rect
                     (fun _ => binary_type m -> (binary_type m -> bool) -> bool)
                     (fun xs f => f xs)
                     false)
              n).
(*

  := fun n
       => binary_type_rec
            (fun m => binary_type m -> bool) 
            (fun _
              => 


  := fun _ => Forall (fun b : bit_type => is_true (bit_is_zero b)).

(**
*)
Definition binary_type_compare
  :  forall (n : nat) (x : binary_type n),
            (m : nat) (y : binary_type m),
       comparison
  := binary_type_rec
       (fun n => binary_type n -> forall m, binary_type m -> comparison)
       (binary_type_rec _
         Eq
         (fun m y0 

(**
  Accepts two bit vectors [x] and [y] and returns
  true iff [x] equals [y].
*)
Axiom binary_number_eq_dec : forall (n : nat) (x y : binary_type n), {x = y} + {x <> y}.


(**
  Accepts two bit vectors [x] and [y] and returns
  true iff [x] is less than or equal to [y].
*)
Axiom binary_number_leb : forall (n : nat) (x : binary_type n) (m : nat) (y : binary_type m), bool. 


(**
*)
Axiom binary_number_sub
  :  forall (n : nat) (x : binary_type n)
            (m : nat) (y : binary_type m),
            
     
(**
*)
Definition binary_number_div_aux (n : nat) (x : binary_type n) 
  :  forall m : nat, binary_type m -> 
     forall rn : nat, binary_type rn ->
     binary_number m * binary_number rn
  := Vector.t_rect bit_type
       (fun m => binary_type m -> binary_number m * binary_number rn)
       ([], r)
       (fun m y0 ys (f : binary_type m -> forall rn : nat, binary_type rn -> binary_number m * binary_number rn)
         rn r
         => let z
              : binary_number (S rn)
              := shiftin y0 r in
            if binary_number_leb n x (S rn) z
              then let (q, s) := f ys z in
                   (1 :: q, s)
              else let (q, s) := f ys 
       
(*
  := Vector.t_rect bit_type
       (fun m
         => sumbool_rect _
              (fun _ => binary_number n -> binary_number n)
              (fun _ => unit)
              (Nat.eq_dec n m))
       (Vector.t_rect bit_type
         (fun m
           => sumbool_rect _
                (fun _ => binary_number 0)
                (fun _ => unit)
                (Nat.eq_dec 0 m))
         []
         tt)
       (fun b0 m bs (f : binary_number m -> binary_number m)
         => Vector.t_rect bit_type
              (fun o
                => sumbool_rect _
                     (S m = o -> binary_number (S m))
                     (_ -> unit)
                     (Nat.eq_dec (S m) o))
              (fun H : S m = 0
                => False_rec _ (Nat.neq_succ_0 m H))
              (fun c0 o cs (_ : binary_number o) (H : S m = S o)
                => let H0 : m = o := eq_add_S m o H in
 *)                  
       

(**
  Represents floating point numbers.

  Accepts two arguments: mantissa, the number of
  significan bits in the numbers; and exponent,
  the number of bits used to specify exponents.
*)
Inductive float_type (mantissa : nat) (exponent : nat)
  := float : binary_type mantissa -> binary_type exponent -> float_type mantissa exponent.

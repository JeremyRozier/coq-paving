Require Import Bool.
Require Export ZArith.
Require Import Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From mathcomp Require Import seq path fintype.
From mathcomp Require Import fingraph.


(** * Definitions *)

(** We define colors as natural numbers, and we set a few
    names to make things a bit more readable. *)
Inductive color := Color: nat -> color.

(** The equality of colors is of course decidable. *)

Definition color_eqb : color -> color -> bool.
Proof.
  intros t u. destruct t, u.
  exact (Nat.eqb n n0).
Defined.

Definition Black := Color 0.
Definition White := Color 1.
Definition Red   := Color 2.
Definition Green := Color 3.
Definition Blue  := Color 4.
(* etc... *)


(* Since we restrict ourselves to one dimensional tiles,
   tiles will only have two sides. *)

Inductive side := Right | Left .

Record tile := {
    right  : color;
    left  : color;
  }.

(* A cell is just one place on the 1-dimensional line,
defined by its coordinate. *)

Inductive cell:= C : Z  -> cell.


(* So far, we say that colors are compatible if equal,
 but this might not be general enough afterwards. *)

Definition compatible_color : color -> color -> bool:=
  color_eqb.

Transparent compatible_color.
Hint Unfold compatible_color.

Definition compatible_right : tile -> tile -> bool:=
(* to do *) fun _ _ => true.

Definition compatible_left : tile -> tile -> bool:=
(* to do *) fun _ _ => true.


(* A configuration is a map associating to any cell
a tile. *)

Definition configuration := cell -> tile.

Infix "=z=":=Z.eqb (at level 75).


(** To make things more comfortable afterwards, we define the 
the notion of neighbourhood for cells, by means of a function
that maps to cell c₁ c₂ to the side of c₁ through which they are
in contact, None otherwise. *)

Definition neighbour: cell -> cell -> option side:=
 fun c d =>
    match c with
    | C xc =>
        match d with
        | C xd  =>
            if  (xd =z= Z.pred xc)
            then Some Left
            else
              if (xd =z= Z.succ xc) 
              then Some Right
              else None
        end
    end.


(** This is a mathcomp trick, we define an inductive specifying 
the previous function, together with a lemma that will allow us
to reason by case distinction on the neighbourhood of a cell
while having the right hypothesis automatically put in the context. *)

Inductive neighbour_spec: cell -> cell-> option side -> Type:=
|Neighbour_left (z1 z2:Z) (p:z2 = Z.pred z1): neighbour_spec (C z1) (C z2) (Some Left)
|Neighbour_right z1 z2 (p: z2 = Z.succ z1): neighbour_spec (C z1) (C z2) (Some Right)
|Neighbour_none z1 z2 (p:z2<>Z.pred z1) (q:z2<>Z.succ z1): neighbour_spec (C z1) (C z2) None.


Lemma neighbourP:
  forall c1 c2, neighbour_spec c1 c2 (neighbour c1 c2).
Proof.
  intros c1 c2.
  induction c1,c2.
  unfold neighbour.
  pose (b:= z0 =z= Z.pred z).
  assert ((z0 =z= Z.pred z) = b) by reflexivity.
  induction b;rewrite H.
  - apply Z.eqb_eq in H. now  apply Neighbour_left.
  - pose (b:= z0 =z= Z.succ z).
  assert ((z0 =z= Z.succ z) = b) by reflexivity.
  induction b;rewrite H0.
    + apply Z.eqb_eq in H0. now  apply Neighbour_right.
    + apply Z.eqb_neq in H,H0. now apply Neighbour_none.
Qed.


                                                      

Definition compatible: configuration -> cell -> cell -> bool:=
  fun T c d => (* to do *)true .


Definition tiling T:Prop:= (* to do *) True.

Definition periodic (T:configuration):Prop:=
(* to do *)True.




(* Should be useful in the future to deal with finite part
of a tiling/configuration. *)

Definition pattern := cell -> option tile.

Definition view:= cell -> bool.

Definition conf_from_view : configuration -> view -> pattern:=
  fun T view c => if view c then Some (T c) else None. 



(******************************)
(*  Example 1: one black tile *)
(******************************)


Definition allblack:tile:=
  @Build_tile Black Black.

Definition T_allblack:configuration := fun _ => allblack.


Proposition allblack_tiling : tiling T_allblack.
Proof.
  (* to do *)
Qed.  



(******************************)
(*  Example 2 - two tiles     *)
(*   - black / white          *)
(*   - white / black          *)
(******************************)


Definition bw:tile:=
  @Build_tile Black White.
Definition wb:tile:=
  @Build_tile White Black.

(* Note : la même magie pour se simplifier la vie *)
 
Inductive even_spec: Z -> bool->  Type:=
|  Even z (p:Z.even z=true) (q:Z.odd z=false) : even_spec z true
|  Odd z (p:Z.even z = false) (q:Z.odd z=true) : even_spec z false.

Lemma evenP: forall z, even_spec z (Z.even z).
Proof.
  intros.
  pose (b:=Z.even z).
  assert (Z.even z=b) by reflexivity.
  induction b.
  - rewrite H; apply (Even z H). now rewrite <- Z.negb_even, H.
  - rewrite H; apply (Odd z H).  now rewrite <- Z.negb_even, H.
Qed.


Definition alternating:configuration := (* to do, on pourra s'aider de Z.even ! *).



Proposition alternating_tiling : tiling alternating.
Proof.
  (* to do *)
Qed.  

Proposition alternating_periodic : periodic alternating.
Proof.
  (* to do *)
Qed.  

        

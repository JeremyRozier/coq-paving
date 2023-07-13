Require Import Bool.
Require Export ZArith.
Require Import Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From mathcomp Require Import seq. (* path fintype. *)
(* From mathcomp Require Import fingraph. *)


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

Inductive side := North | West | East | South .

Record tile := {
    north  : color;
    west  : color;
    east : color;
    south : color;
}.

(* A cell is just one place on the 1-dimensional line,
defined by its coordinate. *)

Inductive cell:= C : Z -> Z -> cell.


(* So far, we say that colors are compatible if equal,
 but this might not be general enough afterwards. *)

Definition compatible_color : color -> color -> bool:=
  color_eqb.

Transparent compatible_color.
Hint Unfold compatible_color.

Definition compatible_north : tile -> tile -> bool:=
fun tile1 tile2 => color_eqb (@north tile1) (@south tile2).


Definition compatible_west : tile -> tile -> bool:=
fun tile1 tile2 => color_eqb (@west tile1) (@east tile2).

Definition compatible_east : tile -> tile -> bool:=
fun tile1 tile2 => color_eqb (@east tile1) (@west tile2).


Definition compatible_south : tile -> tile -> bool:=
fun tile1 tile2 => color_eqb (@south tile1) (@north tile2).

Definition configuration := cell -> tile.

Infix "=z=":=Z.eqb (at level 75).


Definition neighbour: cell -> cell -> option side:=
 fun c d =>
    match c with
    | C xc yc =>
        match d with
        | C xd yd =>
            if  (xd =z= Z.pred xc) && (yd =z= yc)
              then Some West
            else
              if (xd =z= Z.succ xc) && (yd =z= yc)
                then Some East
            else
              if (xd =z= xc) && (yd =z= Z.pred yc)
                then Some South
            else
              if (xd =z= xc) && (yd =z= Z.succ yc)
                then Some North
            else
              None
        end
    end.

Inductive neighbour_spec: cell -> cell-> option side -> Type:=
|Neighbour_west (x1 y1 x2 y2:Z) (p:x2 = Z.pred x1) (q:y2 = y1): neighbour_spec (C x1 y1) (C x2  y2) (Some West)
|Neighbour_east x1 y1 x2 y2     (p:x2 = Z.succ x1) (q:y2 = y1): neighbour_spec (C x1 y1) (C x2 y2) (Some East)
|Neighbour_south x1 y1 x2 y2 (p:x2 = x1) (q:y2 = Z.pred y1): neighbour_spec (C x1 y1) (C x2 y2) (Some South)
|Neighbour_north x1 y1 x2 y2 (p:x2 = x1) (q:y2 = Z.pred y1): neighbour_spec (C x1 y1) (C x2 y2) (Some North)
|Neighbour_none x1 y1 x2 y2 (p:x2<>Z.pred x1) (q:x2<>Z.succ x1) (r:y2<>Z.pred y1) (s:y2<>Z.succ y1): neighbour_spec (C x1 y1) (C x2 y2) None.


Lemma neighbourP:
  forall c1 c2, neighbour_spec c1 c2 (neighbour c1 c2).
Proof.
  intros c1 c2.
  induction c1,c2.
  unfold neighbour.
  pose (b:= z0 =z= Z.pred z).
  assert ((z0 =z= Z.pred z) = b) by reflexivity.
  induction b.
  rewrite H.
  - apply Z.eqb_eq in H. now  apply Neighbour_left.
  - pose (b:= z0 =z= Z.succ z).
  assert ((z0 =z= Z.succ z) = b) by reflexivity.
  induction b;rewrite H0.
    + apply Z.eqb_eq in H0. now  apply Neighbour_right.
    + apply Z.eqb_neq in H,H0. now apply Neighbour_none.
Qed.



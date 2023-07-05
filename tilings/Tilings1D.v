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

Inductive side := Right | Left .

Record tile := {
    left  : color;
    right  : color;
  }.

Check @right.

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
fun tile1 tile2 => color_eqb (@right tile1) (@left tile2).


Definition compatible_left : tile -> tile -> bool:=
fun tile1 tile2 => color_eqb (@left tile1) (@right tile2).



(* A configuration is a map associating to any cell
a tile. *)

Definition configuration := cell -> tile.

Infix "=z=":=Z.eqb (at level 75).


(** To make things more comfortable afterwards, we define the 
the notion of neighbourhood for cells, by means of a function
that maps to cell c\u2081 c\u2082 to the side of c\u2081 through which they are
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
|Neighbour_left (z1 z2:Z) (p:z2 = Z.pred z1)             : neighbour_spec (C z1) (C z2) (Some Left)
|Neighbour_right z1 z2 (p: z2 = Z.succ z1)               : neighbour_spec (C z1) (C z2) (Some Right)
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
fun T c d =>
match neighbour c d with
| Some Right => compatible_right (T c) (T d)
| Some Left => compatible_left (T c) (T d)
| None => true
end. 
 
Definition tiling (T:configuration):Prop:=
  forall c d, compatible T c d.
(*forall m : Z, compatible_right (T (C m)) (T (C (m+1))).
*)
Definition periodic (T:configuration):Prop:=
exists (n:nat), forall z, T (C z) = T (C (z + Z.of_nat n)).

Definition weakly_periodic (T:configuration):Prop:=
exists (n s:nat), forall z, Z.le (Z.of_nat s) z -> T (C z) = T (C (z + Z.of_nat n)).

Definition not_weakly_periodic (T:configuration): Prop :=
forall (n s:nat), exists z,  Z.le (Z.of_nat s) z /\ T (C z) <> T (C (z + Z.of_nat n)).

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
unfold tiling.
unfold compatible.
intros c d.
case: neighbourP;intros.
- unfold T_allblack, compatible_left.
simpl.
reflexivity.
- now compute.
- trivial.
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


(* Note : la m\u00eame magie pour se simplifier la vie *)
 
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

Check Z.even 4.

Definition alternating:configuration := fun c: cell => 
match c with
|C z => if (Z.even z) then bw else wb
end.

Proposition alternating_right_compatible:
  forall c d, neighbour c d = some Right
  -> compatible_right (alternating c) (alternating d).
Proof.
intros m n H.
admit.
Admitted.

Proposition color_eqb_sym:
  (forall c d, color_eqb c d = color_eqb d c).
Admitted.


Proposition compatible_right_left (T:configuration):
  forall c d, (compatible_right (T c) (T d)
<->
compatible_left (T d) (T c)).
Proof.
unfold compatible_left,compatible_right;
split;intros;rewrite color_eqb_sym;trivial.
Qed.
Print neighbour.


Proposition compatible_right_tiling T:
  (forall z1 z2, z2 = Z.succ z1 
    -> compatible_right (T (C z1)) (T (C z2)))
->
(tiling T).
Proof.
intros H c d.
unfold compatible.
case:neighbourP;intros.
apply compatible_right_left.
apply H.
rewrite p.
now rewrite Z.succ_pred.
now apply H.
trivial.
Qed.



Proposition alternating_tiling : tiling alternating.
Proof.
unfold tiling, alternating.
intros m n.
unfold compatible.
case:neighbourP;intros.
assert (H:=evenP z1);
induction H;
rewrite p Z.even_pred q;now simpl.
assert (H:=evenP z1);
induction H;
rewrite p Z.even_succ q;now simpl.
trivial.
Qed.

Proposition alternating_periodic : periodic alternating.
Proof.
unfold periodic.
unfold alternating.
exists 2.
intros.
rewrite Z.even_add.
case:evenP;intros.
-now simpl.
-now simpl.
Qed.

(******************************)
(*  Example 3 - three tiles   *)
(*   - black / white
     - black / black          *)
(*   - white / black          *)
(******************************)
Search "leq".
Search "log".

Check Z.abs.
Check Z.log2.
Check Z.div.
Check Z.pow(Z.log2(Z.abs(_))).

Search nat "pow".
Definition is_pow_2_nat (n:nat) := Nat.eqb (Nat.pow 2 (Nat.log2 (n))) n.

Search  Z.geb.


Definition aperiodic_increasing:configuration := fun c: cell => 
match c with
|C z => if (z <=? 1)%Z then allblack else let n:=Z.to_nat z in
   if is_pow_2_nat(n) then bw else if (is_pow_2_nat(n - 1)) then wb else allblack
end.

Lemma is_pow_2_nat_equiv: forall n:nat, is_pow_2_nat(n) <-> exists m:nat, n = Nat.pow 2 m.
  intros n;split;[intros H |intros (m,Hm)].
  exists (Nat.log2 n);  now apply Nat.eqb_eq in H.
  rewrite Hm. unfold is_pow_2_nat.
  apply Nat.eqb_eq. f_equal. rewrite Nat.log2_pow2;lia.
Qed.  

Lemma is_pow_2_succ:
  forall n, (1 < n) -> is_pow_2_nat n -> is_pow_2_nat (S n) = false.
Proof.
  intros n Hn Pow.
  rewrite Nat.eqb_neq; intro Eq.
  apply Nat.eqb_eq in Pow.
  assert (H:=Nat.log2_succ_le n).
  pose m:=Nat.log2 n. 
  destruct (le_lt_eq_dec _ _ H) as [H1|H1];fold m in H1,Pow.
  - assert (Nat.log2 n.+1 <= m)%coq_nat by lia.
  assert (m <=Nat.log2 n.+1)%coq_nat.
  apply Nat.log2_le_mono;lia.
  assert (Hm: m =Nat.log2 n.+1) by lia.
  rewrite -Hm in Eq. rewrite Pow in Eq. lia.
  - rewrite H1 in Eq.
  rewrite Nat.pow_succ_r in Eq;try lia.
  rewrite Pow in Eq. simpl in Eq.
  rewrite -add1n in Eq.
  assert ( n = 1 ).
  replace n with ((n + (n + 0)%coq_nat)%coq_nat - n).
  rewrite Eq.
  apply Nat.add_sub_eq_l. 
  rewrite Nat.add_comm. reflexivity.
  rewrite Nat.add_0_r.
  now apply Nat.add_sub_eq_l. 
  rewrite H0 in Hn. inversion Hn.
Qed.


Lemma is_pow_2_nat_succ:
  forall z : Z, (1 < z)%Z -> is_pow_2_nat (Z.to_nat z) ->
           is_pow_2_nat (Z.to_nat (Z.succ z)) = false.
Proof.
  intros z Hz Pow.
  replace (Z.to_nat (Z.succ z)) with ((Z.to_nat z).+1).
  apply is_pow_2_succ;trivial.
  case:ltP;intros;trivial.
  exfalso;apply n.
  replace 1 with (Z.to_nat 1) by reflexivity.
  apply Z2Nat.inj_lt;lia.
  rewrite Z2Nat.inj_succ;trivial.
  lia.
Qed.

     
Lemma is_pow2_nat_succ_moins:
  forall z: Z, is_pow_2_nat (Z.to_nat z) -> is_pow_2_nat(Z.to_nat (Z.succ z) -1) = true.
Admitted.

Lemma not_is_pow2_nat_succ_moins:
  forall z: Z, is_pow_2_nat (Z.to_nat z) = false -> is_pow_2_nat(Z.to_nat (Z.succ z) -1) = false.
Admitted.

Proposition aperiodic_increasing_tiling : tiling aperiodic_increasing.
Proof.
apply compatible_right_tiling.
intros z1 z2 H.
unfold aperiodic_increasing.
case:ifP;intros.
case:ifP;intros.
1:{
unfold compatible_right.
now simpl.
}
1:{
rewrite H.
rewrite H in n.
case:ifP;intros.
1:{
unfold compatible_right.
now simpl.
}
case:ifP;intros.
unfold compatible_right.
simpl.
apply Z.leb_le in i.
apply Z.leb_gt in n.
admit.
admit.
}
case:ifP.
1:{
intro H0.
rewrite H.
assert ((Z.succ z1 <=? 1 )%Z = false).
apply Z.leb_gt.
apply Z.leb_gt in n.
lia.
rewrite H1.
apply Z.leb_gt in n.
(* assert ((1 < z1)%Z /\ is_pow_2_nat (Z.to_nat z1)). *)
(* split. *)
(* exact n. *)
(* exact H0. *)
assert (H2:=is_pow_2_nat_succ _ n H0).
rewrite H2.
apply is_pow2_nat_succ_moins in H0.
now rewrite H0.
} 
intro H0.
case:ifP;intros.
rewrite H.
assert ((Z.succ z1 <=? 1)%Z = false).
apply Z.leb_gt.
apply Z.leb_gt in n.
lia.
rewrite H1.
case:ifP;intros.
now simpl.
apply not_is_pow2_nat_succ_moins in H0.
now rewrite H0.
rewrite H.
assert ((Z.succ z1 <=? 1)%Z = false).
apply Z.leb_gt.
apply Z.leb_gt in n.
lia.
rewrite H1.
case:ifP;intros.
now simpl.
apply not_is_pow2_nat_succ_moins in H0.
now rewrite H0.
Admitted.

Lemma nat_le_power : forall s n:nat, (Z.of_nat s <= 2 ^ (Z.of_nat (n + s) + 1))%Z.
Admitted.

Check Nat.pow.

Lemma aperiodic_increasing_not_period: forall n s:nat, is_pow_2_nat (Z.to_nat (2 ^ (Z.of_nat (n + s) + 1) + Z.of_nat n)) = false.
Admitted.

Lemma power_not_le_1: forall n s: nat, (2 ^ (Z.of_nat (n + s) + 1) <=? 1)%Z = false.
Admitted.

Lemma power_of_2: forall n s : nat, is_pow_2_nat (Z.to_nat (2 ^ (Z.of_nat (n + s) + 1))) = true.
Admitted.

Lemma power_not_le_1_n: forall n s:nat, (2 ^ (Z.of_nat (n + s) + 1) + Z.of_nat n <=? 1)%Z = false.
Admitted.

Proposition aperiodic_increasing_aperiodic : not_weakly_periodic aperiodic_increasing.
Proof.
unfold not_weakly_periodic.
unfold aperiodic_increasing.
intros.
exists (Z.pow 2 (Z.of_nat (n + s) + 1%Z)).
split.
1:{
apply nat_le_power.
}
rewrite power_not_le_1.
rewrite power_of_2.
rewrite power_not_le_1_n.
rewrite aperiodic_increasing_not_period.
now case:ifP;intros.
Qed.

(* Formalization oriented graphs *)

Print nat.




Definition edge := fun t1 t2: tile => compatible_right t1 t2.


(* Inductive path : list tile -> Prop :=  *)
(* |Path_two_tiles: forall (t1 t2 : tile), edge t1 t2 -> path (t1::t2::nil) *)
(* |Path_more: forall (t1 t2 : tile) (list_t:list tile), edge t1 t2 -> path (t2::list_t) -> path (t1::t2::list_t). *)

(* Definition cycle := fun (list_t : list tile) => match list_t with *)
(* |nil => False *)
(* |cons t xs => path (list_t ++ (t::nil)) *)
(* end. *)


(* J'ai l\u00e9g\u00e8rement modifi\u00e9 ta seconde version, le but \u00e9tant que la propri\u00e9t\u00e9 
path contienne aussi l'information de o\u00f9 \u00e0 o\u00f9. Comme \u00e7a, on peut tout simplement
dire qu'un cycle est juste un chemin depuis un sommet vers lui-m\u00eame. 

Et j'ai remplac\u00e9 list par seq, mais c'est quasiment pareil, c'est plut\u00f4t en pr\u00e9vision
de futures extensions possibles pour rester bas\u00e9s sur certaines librairies.*)

Inductive path: seq tile -> tile -> tile -> Prop :=
|path_two: forall t1 t2, edge t1 t2 -> path (t1::t2::nil) t1 t2
|path_cons: forall t1 t2 t3 p, edge t1 t2 -> path p t2 t3 -> path (t1::p) t1 t3.

Definition cycle p x:=path p x x.


(* Remarque qu'ici on pourrait aussi travailler en version bool\u00e9enne, 
je ne sais pas si ce sera utile par la suite, mais c'est tout \u00e0 fait possible:
- la relation "edge" est d\u00e9cidable,
- la propri\u00e9t\u00e9 "path p x y" l'est si "edge" l'est 
- la propri\u00e9t\u00e9 "cycle p x" l'est si "path" l'est 
 *)

Print cycle.

Fixpoint nb_edges (l: seq tile) : Z :=
match l with
| nil => -1
| _ :: xs => Z.succ (nb_edges xs)
end.

(*Print list.*)

Print nat.
(*Fixpoint fonction p x c := match p with 
|nil => x
|cons y p2 => match c with 
  |C z => if (z mod (Z.of_nat (nb_edges p)) =z= (Z.of_nat (nb_edges p2))) then y else fonction p2 x c 
  end
end.*)


Fixpoint nth (l : seq tile) (n : nat) default: tile :=
match l with
| nil => default
| cons x xs => match n with
 | O => x
 | S m => nth xs m default
 end
end.


Lemma path_compatible_right:
    forall p z x y, path p x y  -> (z < nb_edges p)%Z ->
             compatible_right (nth p (Z.to_nat z) x) (nth p (Z.abs_nat(Z.succ z)) x).
Admitted.

Lemma cycle_length: forall c x, cycle c x -> nth c 0 = nth c (Z.abs_nat (nb_edges c)).
Admitted.

Lemma nb_edges_cycle_pos: forall c x, cycle c x -> (nb_edges c > 0)%Z.
Admitted.



Lemma mod_bound:
  forall (a:Z) (z:Z), (z>0)%Z -> (0%Z <= (a mod z)%Z < z)%Z.
Proof.
  intros a z Hz.
  assert (Bla:=Z_div_mod a z Hz ) .
  pose (D:= Z.div_eucl a z).
  assert (D = Z.div_eucl a z) by reflexivity.
  destruct D as (q,r).
  unfold Z.modulo. rewrite -H.
  rewrite -H in Bla;now destruct Bla as (_,Eq).
Qed.



(*Definition tiling_cycle x p (H:cycle p x):configuration
  := fun (c:cell)=> fonction p x c.*)

Definition tiling_cycle x p (H:cycle p x):configuration
  := fun (c:cell)=> match c with 
|C z => nth p (Z.abs_nat(z mod nb_edges p)) x
end.


Lemma tiling_cycle_tiling : forall x p H, tiling (tiling_cycle x p H).
Proof.
intros.
apply compatible_right_tiling;intros.
unfold tiling_cycle;intros.
rewrite H0.
pose proof H as H1.
pose proof H as H2.
apply cycle_length in H1.
apply nb_edges_cycle_pos in H2.
pose (z3 := z1 mod nb_edges p).



Require Import Bool.
Require Export ZArith.
Require Import Psatz.
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

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

Record Tile := {
    left  : color;
    right  : color;
  }.


(* Technical definition to get a finite type based on a set
   of tiles using SSReflect structures. *)

Definition tile_eq : Tile -> Tile -> bool:=
  fun t u => color_eqb t.(left) u.(left) && color_eqb t.(right) u.(right).

Lemma tile_eq_reflect x y:
  reflect (x=y) (tile_eq x y).
Proof.
  pose (b:=tile_eq x y).
  assert (tile_eq x y = b) by reflexivity.
  destruct b;rewrite H;
  destruct x, y;unfold tile_eq in H;simpl in *;
  unfold color_eqb in H;
    induction right0, left0, right1, left1.
  - apply andb_prop in H;destruct H.
    apply Nat.eqb_eq in H,H0;
    subst;now apply ReflectT.
  - apply andb_false_elim in H.
    destruct H as [ H | H];
    apply Nat.eqb_neq in H;
    apply ReflectF;
    intro; now inversion H0.
Qed.

Definition tile_eqMixin := Equality.Mixin tile_eq_reflect.
Definition tile_eqType : eqType := Equality.Pack tile_eqMixin.

Canonical tile_eqType.

Section Tilings.
  Parameter (Tiles : Finite.class_of Tile).
  Canonical tile:=@Finite.Pack Tile Tiles.
  
 
  (* A cell is just one place on the 1-dimensional line,
defi ned by its coordinate. *)
  
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
      the  notion of neighbourhood for cells, by means of a function
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

  Definition pattern := cell -> option tile.

  Definition view:= cell -> bool.

  Definition conf_from_view : configuration -> view -> pattern:=
    fun T view c => if view c then Some (T c) else None. 

 
  Definition period := {n : nat & (n > 0)%coq_nat}.
  Definition period_to_nat : period -> nat.
    intros p. destruct p. exact x.
  Defined.
  Coercion period_to_nat: period >-> nat.

  Definition makeperiod n (H:(n>0)%coq_nat):period:=existT _ n H.


  Definition periodic (T:configuration):Prop:=
    exists (n:period), forall z, T (C z) = T (C (z + Z.of_nat n)).

  Definition ultimately_periodic (T:configuration):Prop:=
    exists (n:period) (s:nat), forall z, Z.le (Z.of_nat s) z -> T (C z) = T (C (z + Z.of_nat n)).

  Definition not_ultimately_periodic (T:configuration): Prop :=
    forall (n:period) (s:nat), exists z,  Z.le (Z.of_nat s) z /\ T (C z) <> T (C (z + Z.of_nat n)).

  (* Should be useful in the future to deal with finite part
     of a tiling/configuration. *)

  (** * Properties *)

  
  Proposition color_eqb_sym:
    (forall c d, color_eqb c d = color_eqb d c).
    intros. unfold color_eqb;destruct c,d;simpl.
    apply Nat.eqb_sym.
  Qed.

  Proposition compatible_right_left (T:configuration):
    forall c d, (compatible_right (T c) (T d)
            <->
              compatible_left (T d) (T c)).
  Proof.
    unfold compatible_left,compatible_right;
      split;intros;rewrite color_eqb_sym;trivial.
  Qed.



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




  
  (** * The associated oriented graphs *)

  Definition edge := fun t1 t2: tile => compatible_right t1 t2.

  Inductive path: seq tile -> tile -> tile -> Prop :=
  |path_two: forall t1 t2, edge t1 t2 -> path (t1::t2::nil) t1 t2
  |path_cons: forall t1 t2 t3 p, edge t1 t2 -> path p t2 t3 -> path (t1::p) t1 t3.

  Definition cycle p x:=path p x x.

    Fixpoint nb_edges (l: seq tile) : Z :=
    match l with
    | nil => -1
    | _ :: xs => Z.succ (nb_edges xs)
    end.

  
  Lemma nb_edges_path_pos: forall p x y, path p x y-> (nb_edges p > 0)%Z.
  Proof.
  Admitted.

  Fixpoint nth (l : seq tile) (n : nat) default: tile :=
    match l with
    | nil => default
    | cons x xs => match n with
                  | O => x
                  | S m => nth xs m default
                  end
    end.


  Lemma path_compatible_right:
    forall p n x y, path p x y -> n < Z.abs_nat(nb_edges p) ->
               compatible_right (nth p n x) (nth p (S n) x).
  Proof.
    intros.
    (* TODO : J\u00e9r\u00e9my *)
  Admitted.


  Lemma path_fst: forall p x y d, path p x y -> nth p 0 d = x.
  Proof.
    intros p x y d P.
    now inversion P;subst;simpl.
  Qed.


  
  Lemma path_last: forall p x y d, path p x y -> nth p (Z.abs_nat (nb_edges p)) d = y.
  Proof.
    intros p x y d P.
    induction P.
    - simpl. reflexivity.
    - simpl.
      assert (Z.abs_nat (Z.succ (nb_edges p))= S (Z.abs_nat ((nb_edges p)))).
      {apply Zabs2Nat.inj_succ. assert (Nb:=nb_edges_path_pos p t2 t3 P). 
       lia.
      }
      rewrite H0. exact IHP.
  Qed.

  Lemma cycle_length: forall c x d, cycle c x -> nth c 0 d = nth c (Z.abs_nat (nb_edges c)) d.
    intros c x d Cyc.
    rewrite (path_fst c x x d Cyc).
    now rewrite (path_last c x x d Cyc).
  Qed.

  Lemma nb_edges_cycle_pos: forall c x, cycle c x -> (nb_edges c > 0)%Z.
    intros. apply (nb_edges_path_pos c x x H).
  Qed.  




  Lemma succ_mod_0: forall n z, (n>0)%Z -> (Z.succ z mod n)%Z = 0%Z ->
                           (z mod n)%Z = (Z.pred (n)).
  Proof.
    intros n z Hn H.
    assert (n<>0)%Z by lia.
    assert (Bla:=Z.div_eucl_eq (Z.succ z) n H0).
    unfold Z.modulo in H.
    pose (D:= Z.div_eucl (Z.succ z) n).
    assert (D = Z.div_eucl (Z.succ z) n) by reflexivity.
    destruct D as (q,r).
    rewrite -H1 in Bla,H.
    rewrite H in Bla.
    rewrite (Zpred_succ z) Bla.
    replace (Z.pred (n * q + 0)) with (Z.pred n + Z.pred q * n)%Z by lia.
    rewrite Z_mod_plus_full.
    apply Z.mod_small.
    split;lia.
  Qed.



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



  Lemma cycle_cases: forall (z n : Z), (n>0)%Z ->
                                  (Z.succ z mod n = 0)%Z \/ 
                                    (Z.succ z mod n = Z.succ (z mod n))%Z.
  Proof.
    intros.
    assert (Hn:(n<>0)%Z) by lia.
    assert (Eq:=Z_div_mod z n H ).
    pose (D:= Z.div_eucl z n).
    assert (D = Z.div_eucl z n) by reflexivity.
    destruct D as (q,r).
    rewrite -H0 in Eq.
    destruct Eq as (Eq,Bound).
    subst.
    destruct (Z.eq_dec r (n-1)).
    left. rewrite e.
    replace (Z.succ (n * q + (n - 1))) with (n * (q + 1))%Z by lia.
    symmetry.
    apply Z.mod_unique_pos with (q:=(q+1)%Z);lia.
    right.
    assert (r+1 <n)%Z by lia.
    replace (Z.succ (n * q + r)) with (n * q + (r+1))%Z by lia.
    replace (((n * q + (r + 1)) mod n)%Z) with (r+1)%Z.
    replace ((n * q + r) mod n)%Z with r.
    lia.
    apply Z.mod_unique_pos with (q:=q);[lia|reflexivity].
    apply Z.mod_unique_pos with (q:=q);[lia|reflexivity].
  Qed.


  Definition tiling_cycle x p (H:cycle p x):configuration
    := fun (c:cell)=> match c with 
                   |C z => nth p (Z.abs_nat(z mod nb_edges p)) x
                   end.

  Lemma geq_ge : forall z k : Z, (z > k)%Z -> (z >= k)%Z.
  Proof.
    lia.
  Qed.

  Lemma tiling_cycle_tiling : forall x p H, tiling (tiling_cycle x p H).
  Proof.
    intros.
    apply compatible_right_tiling;intros.
    unfold tiling_cycle;intros.
    rewrite H0.
    pose proof H as H1.
    pose proof H as H2.
    apply cycle_length with (d:=x) in H1.
    apply nb_edges_cycle_pos in H2.
    destruct (cycle_cases z1 (nb_edges p)).
    1:{
      apply H2.
    }
    1:{
      rewrite H3.
      rewrite H1.
      pose proof H2 as H4.
      apply succ_mod_0 with (z := z1) in H2.
      2:{
        now rewrite H3.
      }
      rewrite H2.
      rewrite Zabs2Nat.inj_pred.
      1:{ 
        replace (Z.abs_nat (nb_edges p)) with ((Z.abs_nat (nb_edges p)).-1.+1).
        1:{
          {apply path_compatible_right with (y:=x);unfold cycle in H.
           apply H.
           admit.   (* TODO : J\u00e9r\u00e9my *)
          }
        }
        admit.   (* TODO : J\u00e9r\u00e9my *)
      }
  Admitted.
  (*apply path_compatible_right with (y:=x).
1:{
unfold cycle in H.
apply H.
}
lia.
}
rewrite H3.
apply path_compatible_right with (y:=x).
1:{
unfold cycle in H.
apply H.
}
apply mod_bound.
apply H2.
Qed.
   *)

  Lemma periodic_cycle_tiling : forall x p H, periodic (tiling_cycle x p H).
  Proof.
    intros.
    unfold periodic.
    assert (Nb:=nb_edges_cycle_pos p x H).
    assert ((0 < (Z.abs_nat(nb_edges p)))%coq_nat).
    { rewrite <- Zabs2Nat.inj_0. apply Zabs_nat_lt. lia. }
    exists (makeperiod (Z.abs_nat(nb_edges p)) H0).
    intros.
    unfold tiling_cycle;intros.
    rewrite Nat2Z.inj_abs_nat.
    apply nb_edges_cycle_pos in H.
    pose proof H as H1.
    apply geq_ge in H.
    apply Z.ge_le_iff in H.
    apply Z.abs_eq_iff in H.
    rewrite H.
    apply Z_mod_plus with (a := z) (b := 1%Z) (c := nb_edges p) in H1.
    rewrite Z.mul_1_l in H1.
    now rewrite H1.
  Admitted. 



  (** * The graph associated to any tiling admits a cycle *)
  
  Axiom tilings_repeat: forall c, tiling c -> exists s n, (0 < n) /\ c (C (Z.of_nat s)) = c (C (Z.of_nat (s+n))).
    (* Pigeonhole principle *)

  Lemma tiling_exists_cycle : forall c, tiling c -> exists p x, cycle p x.
  Admitted.

End Tilings.








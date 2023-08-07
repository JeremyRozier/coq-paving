Require Import tilings1D.
Require Import Bool.
Require Export ZArith.
Require Import Psatz.
From mathcomp Require Import all_ssreflect.



(******************************)
(*  Example 1: one black tile *)
(******************************)

Definition allblack:Tile:=
  @Build_Tile Black Black.

 
Definition T_allblack:configuration := fun _ => allblack.


Proposition allblack_tiling : tiling T_allblack.
Proof.
unfold tiling.
unfold compatible.
intros c d.
case:neighbourP;intros.
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
  @Build_Tile Black White.
Definition wb:tile:=
  @Build_Tile White Black.


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
  Check neighbourP.
  assert (N:=neighbourP m n).
  rewrite H in N. inversion N;subst.
  unfold alternating.
  now case:evenP;intros;rewrite Z.even_succ q.
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


Ltac ex_period n:= 
  assert (Hperiod:(n>0)%coq_nat) by lia;
  exists (makeperiod n Hperiod);simpl;try clear Hperiod.


Proposition alternating_periodic : periodic alternating.
Proof.
unfold periodic.
unfold alternating.
ex_period 2.
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
Definition is_pow_2_nat (n:nat) := Nat.eqb (Nat.pow 2 (Nat.log2 (n))) n.



Definition aperiodic_increasing:configuration := fun c: cell => 
match c with
|C z => if (z <=? 1)%Z then allblack else let n:=Z.to_nat z in
   if is_pow_2_nat(n) then bw else if (is_pow_2_nat(n - 1)) then wb else allblack
end.

Lemma is_pow_2_nat_equiv: forall n:nat, is_pow_2_nat(n)
 <-> exists m:nat, n = Nat.pow 2 m.
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


Lemma to_nat_succ_sub:
  forall z:Z, (0<=z)%Z -> Z.to_nat (Z.succ z) -1 = Z.to_nat z.
Proof.
  intros.
  rewrite Z2Nat.inj_succ;try assumption.
  now rewrite subSS subn0.
Qed.


Lemma is_pow2_nat_succ_moins:
  forall z: Z, (0<=z)%Z -> is_pow_2_nat (Z.to_nat z) ->
 is_pow_2_nat(Z.to_nat (Z.succ z) -1) = true.
Proof.
  intros;now rewrite to_nat_succ_sub.
Qed.

Lemma not_is_pow2_nat_succ_moins:
  forall z: Z, (0<=z)%Z -> is_pow_2_nat (Z.to_nat z) = false ->
 is_pow_2_nat(Z.to_nat (Z.succ z) -1) = false.
Proof.
  intros;now rewrite to_nat_succ_sub.
Qed.


Proposition aperiodic_increasing_tiling : tiling aperiodic_increasing.
Proof.
apply compatible_right_tiling.
intros z1 z2 H; subst.
unfold aperiodic_increasing,compatible_right.
repeat case:ifP;intros H H1;intros;simpl;trivial;
  try (apply Z.leb_gt in n).
{
  apply Z.leb_le in i.
  (* Gr\u00e2ce \u00e0 i et n on peut obtenir z1=1 *)
  replace z1 with 1%Z in * by lia;simpl in *.
  rewrite -H1.
  (* ici on peut juste calculer, on aurait aussi pu mettre "now" 
   au d\u00e9but de la commande suivante. *)
  compute. reflexivity.
}
{
  assert ((Z.succ z1 <=? 1 )%Z = false).
  apply Z.leb_gt.
  apply Z.leb_gt in n.
  lia.
  now rewrite -H0.
}
{ now rewrite -(is_pow_2_nat_succ _ n i). }
{ rewrite -H. now apply is_pow2_nat_succ_moins;try lia. }
now rewrite -(not_is_pow2_nat_succ_moins _ _ n0);try lia.
now rewrite -(not_is_pow2_nat_succ_moins _ _ n1);try lia.
Qed.



Lemma nat_lt_power : forall s n:nat, ( s < 2 ^ ((n + s) + 1)).
Proof.
  intros s n.
  apply leq_trans with (2^s).
  - now apply ltn_expl.
  - apply leq_pexp2l;try reflexivity.
    apply leq_trans with (n+s);[apply leq_addl|apply leq_addr].
Qed.


Lemma nat_le_power : forall s n:nat, ( s <= 2 ^ ((n + s) + 1)).
Proof.
 intros s n.
 now apply ltnW,nat_lt_power.
Qed.



Lemma expn_is_pow: forall n, Nat.pow 2 n = expn 2 n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite expnS.
    do 2 rewrite mulSn; rewrite mul0n.
    now rewrite IHn.
Qed.

Lemma Z_le_power : forall s n:nat, (Z.of_nat n <=Z.pow 2 (Z.of_nat ((s + n) + 1)))%Z.
Proof.
  intros.
  replace (2%Z) with (Z.of_nat 2) by reflexivity.
  rewrite <- Nat2Z.inj_pow.
  apply inj_le.
  apply (elimT leP).
  eapply leq_trans;[apply (nat_le_power n s)|].
  now rewrite expn_is_pow.
Qed.


Lemma between_not_pow:
  forall p n, 2^n < p -> p< 2^(n.+1) -> is_pow_2_nat p = false.
Proof.
  intros p n H1 H2.
  pose (b:= is_pow_2_nat p).
  assert (IsPow:is_pow_2_nat p=b) by reflexivity.
  destruct b;try now rewrite IsPow.
  exfalso.
  apply is_pow_2_nat_equiv in IsPow.
  destruct IsPow as (m,Hm).
  rewrite Hm in H1,H2.
  rewrite expn_is_pow in H1,H2.
  apply (@ltn_pexp2l 2) in H1,H2;try reflexivity.
  apply (elimT leP) in H1,H2.
  lia.
Qed.
  

Lemma power_not_le_1: forall n s: nat, (2 ^ (Z.of_nat (n + s + 1)) <=? 1)%Z = false.
Proof.
intros.
apply Z.leb_gt.
do 2 rewrite Nat2Z.inj_add.
assert ((0 <= Z.of_nat n + Z.of_nat s + 1)%Z).
-lia.
apply Z.log2_lt_cancel.
apply Z.log2_pow2 in H.
rewrite H.
simpl.
lia.
Qed.


Lemma power_of_2: forall n s : nat,
    is_pow_2_nat (Z.to_nat (2 ^ (Z.of_nat (n + s + 1)))) = true.
Proof.
intros.
apply is_pow_2_nat_equiv.
exists (Z.to_nat((Z.of_nat(n + s + 1))%Z)).
rewrite Z2Nat.inj_pow.
reflexivity.
lia.
lia.
Qed.

Lemma power_not_le_1_n: forall n s:nat, 
    (2 ^ (Z.of_nat (n + s + 1)) + Z.of_nat n <=? 1)%Z = false.
  (* devrait \u00eatre simple *)
intros.
apply Z.leb_gt.
do 2 rewrite Nat2Z.inj_add.
assert ((0 <= Z.of_nat n + Z.of_nat s + 1)%Z).
-lia.
apply Z.log2_lt_cancel.
apply Z.log2_pow2 in H.
(*TODO*)
Admitted.

Lemma not_pow_aux:
  forall n s:nat, n>0 -> is_pow_2_nat (Z.to_nat (2 ^ (Z.of_nat (n + s + 1)) + Z.of_nat n)) = false.
Proof.
  intros.
  rewrite Z2Nat.inj_add;try lia.
  rewrite Z2Nat.inj_pow;try lia.
  rewrite expn_is_pow;do 2 rewrite Nat2Z.id.
  apply (between_not_pow _ ((n + s + 1))).
  { rewrite <- (addn0 (2 ^ (n + s + 1))) at 1. 
    now rewrite ltn_add2l. }
  { rewrite expnS.
    do 2 rewrite mulSn; rewrite mul0n;rewrite addn0.
    rewrite ltn_add2l. replace (n+s+1) with (s+n+1).
    apply nat_lt_power.
    f_equal;now rewrite addnC.
  }
Qed.



Proposition aperiodic_increasing_aperiodic : not_ultimately_periodic aperiodic_increasing.
Proof.
unfold not_ultimately_periodic.
unfold aperiodic_increasing.
intros.
exists ((2 ^ (Z.of_nat (n + s + 1)))%Z).
split.
1:{
  apply (Z_le_power n s).
}
rewrite power_not_le_1.
rewrite power_of_2.
rewrite power_not_le_1_n.
rewrite not_pow_aux.
now case:ifP;intros.
destruct n as (n,Hn);simpl.
apply (introT leP). lia.
Qed.

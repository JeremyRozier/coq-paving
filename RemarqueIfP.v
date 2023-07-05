
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.

Goal
  forall b c (bla bli blo:nat),
    (if b then bla else if c then bli else blo)
  = ( if c then if b then bla else bli else if b then bla else blo).
Proof.
  intros.
  case:ifP;intros.
  (* c'est le premier ifP qui est sélectionné, et dans ce cas 
  c'est en fait équivalent à :

  case (ifP b bla (if c then bli else blo));intros.

  ou

  assert,(H:=ifP b bla (if c then bli else blo).
    case H;intros.      
   *)
  case:ifP;intros.
  (* le second *)
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

(* Remarque que quand le raisonnement par cas sur ifP est fait,
ça fait aussi du même coup un raisonnement par cas sur le booléen
correspondant, donc ça simplifie considérablement le but puisque les
autres "if" portant sur le même booléen sont automatiquement réduits.*)

Goal
  forall b c (bla bli blo:nat),
    (if b then bla else if c then bli else blo)
  = ( if c then if b then bla else bli else if b then bla else blo).
Proof.
  intros.
  case (ifP c bli blo);intros.
  reflexivity.
  reflexivity.
Qed.


(* Dernière remarque, dans ce cas simplifié, on n'a même pas vraiment
besoin de ifP, mais juste de raisonner par cas sur les booléens. Ça
ne marche pas toujours, mais c'est bien de le garder en tête. *)

Goal
  forall b c (bla bli blo:nat),
    (if b then bla else if c then bli else blo)
  = ( if c then if b then bla else bli else if b then bla else blo).
Proof.
  intros.
  case b;case c;reflexivity.
Qed.

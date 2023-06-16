(*** Introduction à Coq : formules, entiers et listes ***)

(* Pour avoir les raccourcis comme il faut dans coqide :
- Lancer "coqide" dans un terminal
- Edit > Preferences > Shortcuts > Modifiers for Navigation Menu
- Changer vers <alt> (selon les versions:
  - Taper Alt+W dans le champ, ou,
  - Laisser le bouton <alt> seul enfonçé)
- Cliquer sur OK
- Quitter coqide
- Relancer coqide *)

(* Les exercices sont issus de TP que j'ai donné accompagnant un cours, 
normalement ça devrait être auto-suffisant mais il pourrait rester quelques
références à d'autres documents, ce n'est pas vital de les avoir a priori.

Attention, les exercices ne sont pas forcément rangé par difficulté croissante,
il y a un mix de 2 TPs, et le début du 2ème est plus simple que la fin du premier. *)

(*** Logique Simple ***)

(* Les deux tactiques centrales de Coq sont :

  [intro]
    L'équivalent de "soit x" et de "supposons que..."  dans les maths
    informelles, [intro] introduit un nouvel objet (entité sur
    laquelle on raisonne, ou hypothèse) dans le contexte.
    On peut nommer l'objet que l'on introduit, avec [intro x] ou
    [intro H], par exemple.
    La variante [intros] fait [intro] autant que possible, en
    choisissant (plus ou moins arbitrairement) des noms pour les
    hypothèses ainsi créées.
    
  [apply H]
    Permet d'invoquer l'hypothèse nommée H. *)

Lemma trivial1 : forall P : Prop, P -> P.
intro P. intro H. apply H. Qed.

(* À vous de jouer maintenant !
Prouvez les lemmes suivants en utilisant uniquement intro et apply*)

Lemma trivial2 : forall P Q : Prop, (P -> Q) -> P -> Q.
  intro P.
  intro Q.
  intro H.
  apply H.
Qed.


(* [intros H1 H2 H3] est un raccourci pour [intro H1. intro H2. intro H3.]. *)
(*    Vous pouvez maintenant l'utiliser. *)

Lemma trivial3 : forall P Q R : Prop,
  (P -> Q -> R) -> (P -> Q) -> P -> R.
  intros P Q R H0 H1 H2.
  apply H0.
  apply H2.
  apply H1.
  apply H2.
Qed.


(* Une dernière chose à propose de apply. Observez la preuve suivante, 
que vous pourriez avoir écrite sans difficulté. *)

Lemma trivial4: forall P, (forall x, P x) -> P 2.
  intros P H.
  apply H.
Qed.


(* À la deuxième ligne, on a appliqué l'hypothèse (H: forall x, P x) 
pour en déduire (P 2), qui ne coïncide pourtant pas avec l'hypothèse. 
En réalité, ce que Coq a fait pour vous, c'est qu'il a deviné que vous
vouliez appliquez l'hypothèse H dans le cas particulier où x vaut 2. 
C'est à dire: *)

Lemma trivial4': forall P, (forall x, P x) -> P 2.
  intros P H.
  Check (H 2).
  apply (H 2).
Qed.


(* Autrement dit, on peut (et même parfois on doit) préciser les arguments
 d'une hypothèse quand on l'applique.
Après avoir médité sur cette idée, prouver le lemme suivant: *)
Lemma apply1: forall (P : nat -> Prop), (forall x y, P x -> P y) -> P 2 -> P 3. 
  intros A B C.
  Check (B 2,3).
  apply (B 2,3).
  apply C.
Qed.



(* Pour chaque connecteur logique, Coq fournit une tactique pour l'utiliser
quand il est en hypothèse et une tactique pour le "construire" quand
il est en but. Voici ce qui a été vu en cours pour la conjonction et
l'existentielle :

    connecteur    | pour utiliser |  pour construire
  ----------------|---------------|---------------------
      P /\ Q      |  destruct H.  |  split.
  exists x:nat, P |  destruct H.  |  exists 17.
*)

(* La disjonction est notée \/ en Coq.
   Pour prouver un but de la forme A \/ B, on dispose des deux tactiques "left." et "right.".
   Devinez ce qui se passe lorsque l'on a une hypothèse de la forme "H : A\/B"
   dans le but courant, et que l'on fait [destruct H].
   Vérifiez que vous avez deviné juste en prouvant les lemmes suivants. *)

Set Implicit Arguments. 

Lemma conj1: forall P Q : Prop, P /\ Q -> P.
intros P Q H.
destruct H.
apply H.
Qed.

Lemma conj2: forall P Q : Prop, P -> Q -> P /\ Q. (* Pourquoi ça split l'hypothèse *)
intros P Q H.
split.
apply H.
apply H0.
Qed.

Definition bla: forall A B:Prop, A -> B -> A /\ B
 := fun A B H H' => conj H H'.
Check bla.

Check conj2.

Check conj2.
Print conj2.

Lemma or1 : forall P Q : Prop, P -> P \/ Q.
intros P Q.
left.
apply H.
Qed.

Print or1.
Print or_introl.

Lemma or2 : forall P Q R : Prop,
  P \/ Q -> (P -> R) -> (Q -> R) -> R.
  intros P Q R A B C.
  destruct A as [H |H].
  - apply (B H).
  - apply (C H).
Qed.

Print or2.

(* Prouvez maintenant le lemme suivant.
   Vous aurez besoin pour cela des tactiques suivantes pour travailler sur les expressions entières : 

    [reflexivity] 
      Permet de prouver un but de la forme "a = a". Cette tactique peut aussi s'utiliser pour 
      d'autres relations reflexive.

    [simpl]
      Permet de simplifier une expression dans le but. On verra plus formellement plus tard 
      comment ça marche, mais pour l'instant vous pouvez voir ça comme une tactique permettant 
      de réécrire par exemple "2*2" en "4".  
*)
Lemma echauffement_or : forall x, (x=2 \/ x=4) -> exists y, x=2*y /\ (y=1 \/ y=2).
intros A B.
destruct B.
exists 1.
split.
simpl.
apply H.
left.
reflexivity.
exists 2.
split.
simpl.
apply H.
right.
reflexivity.
Qed.

(* Retour sur la curryfication *)
(* Devinez l'énoncé du lemme suivant, et prouvez-le *)
Definition curry3 : forall A B C D, 
((A/\B/\C) -> D) -> A -> B -> C -> D
:=
fun A B C D H a b c =>
  H (conj a (conj b c)).

Lemma curry4 : forall A B C D, ((A/\B/\C) -> D) -> A -> B -> C -> D.
Proof.
  intros A B C D H a b c.
  apply H.
  split.
  apply a.
  split.
  apply b.
  apply c.
Qed.




(*** Arithmétique Simple sur les Entiers ***)

(* Inspirez-vous des définitions de plusnat et pred vues en cours 
pour définir la soustraction sur les naturels, qui satisfera la propriété n-(n+k)=0 *)



Print nat.

Fixpoint minus (n m:nat) : nat 
:=
match n,m with 
  | _,0 => n
  | 0, S b => 0
  | S a, S b => minus a b
end.

Print minus.
(* Prouvez le lemme suivant. Vous aurez besoin de la tactique suivante:
    [case n]
    Permet de séparer une preuve sur n en deux : d'abord le cas "n = 0", puis le cas "n = S n0". *)

Lemma minus_zero : forall n, minus n 0 = n.
Proof.
  intro n.
  case n.
  -compute.
  reflexivity. 
  -intro n2.
  compute.
  reflexivity.


Qed.

(* Vous aurez besoin de la tactique suivante pour le prochain lemme : 
    
    [induction n]
    Permet de faire une preuve par récurrence sur l'entier n (ou une induction sur n). 
    Il vous faudra alors, comme en maths, prouver le cas "n=0" puis le cas "S n" en supposant la propriété vraie
pour n *)

(* Formellement, le principe d'induction est résumé par la formule suivante en Coq : *)
Check nat_ind.

(* Notez la différence avec la tactique [case] précédente. *)
Check nat_case.

(* Indice supplémentaire : Maintenant que vous avez prouvé le lemme "minus_zero", vous pouvez maintenant 
écrire [apply minus_zero] pour utiliser ce lemme. *)

Lemma plus_minus : forall n k, (minus (n + k) n) = k.
Proof.
  intros n k.
  induction n.
  -cbn.
  apply minus_zero.
  -simpl.
  apply IHn.


Qed.
Print plus_minus.

(*** Ordres et relations  ***)

(** Pour vous montrer qu'avec Coq on peut aussi faire des mathématiques,
on va chercher ici à prouver quelques résultats très simples sur les ordres. 
Pour commencer, on se donne un objet X fixé (la carrière de l'ensemble ordonné
que l'on va considérer, et l'on définit ce qu'est une relation sur X, à savoir
une proposition portant sur deux éléments de X. *)

Parameter X : Set.
Definition relation:= X -> X -> Prop.

(** Obversez qu'ici, les relations sont définies commes des fonctions.
On pourrait par exemple définir la relation d'ordre sur les entiers 
en utilisant le fait que n≤m ssi n-m = 0 : *)

Definition leq n m:=  n - m = 0.

(** On vérifie que leq a bien le bon type.*)
Check leq.

(** Alternativement, on peut utiliser (comme en OCaml) le mot-clé [fun] 
à travers la structure:

     Definition f:= fun x y z => ...

pour définir des fonctions. La définition précédente est ainsi équivalente à:
*)

Definition leq':=fun n m => n-m = 0.


(** Comme vous le savez sûrement déjà, un ordre est une relation réflexive,
 anti-symétrique et transitive. Définissez ici ces différentes notions. *)

Definition reflexive (R:relation):= forall n : X, R n n.

Definition antisymmetric (R:relation):= forall n m : X, R n m -> ~(R m n).

Definition transitive (R:relation):=forall n m p : X, (R n m) /\ (R m p) -> R n p.

Definition order (R:relation):= reflexive R /\ antisymmetric R /\ transitive R.


(** Dans la suite, si vous avez besoin de déplier une définition, vous
pouvez utiliser la tactique:
    [unfold f]
qui permet de remplacer dans le but le nom "f" définit plus haut par son 
expression. De même, vous pouvez déplier une opération dans l'une des 
hypothèses du contexte en utilisant:
    [unfold f in H]
*)


(** Pour commencer, on va montrer que l'ordre inversé (i.e. la relation 
"retournée") définit lui-même un ordre. 
Définissez ici ce qu'est le retournée d'une relation. *)

(*JE SUIS COINCÉ*)
Definition reverse (R:relation):= fun x y => (x <> y -> ~R x y) \/ (x = y -> R x x).
Print reverse.

(** On peut maintenant montrer que si une relation est 
(réflexive|anti-symétrique|transitive) sa relation inverse l'est aussi. *)


Lemma rev_refl (R:relation): reflexive R -> reflexive (reverse R).
intro H.
unfold reflexive.
intro n.
unfold reverse.
right.
unfold reflexive in H.
intro H1.
apply H.
Qed.

(*JE SUIS COINCÉ*)
Lemma rev_antisym (R:relation): antisymmetric R -> antisymmetric (reverse R).
intro H0.
unfold antisymmetric in H0.
unfold antisymmetric.
intros n m H1.
unfold reverse in H1.
unfold reverse.
unfold not.
intro H2.


Qed.


Lemma rev_trans (R:relation): transitive R -> transitive (reverse R).
  [...]  
Qed.


(** On peut maintenant facilement montrer qu'un ordre inversé est 
lui-même un ordre. *)

Lemma rev_order (R:relation):  order R -> order (reverse R).
  [...]  
Qed.




(*** Fonctions sur les listes ***)

(* Une "incantation" pour avoir accès à la bibliothèque Coq traitant des listes *)
Require Export List.

(* Coq connaît les listes polymorphes : les "listes de A", pour un type A quelconque
  (liste de naturels, de booléens, de listes de naturels, de fonctions de type nat -> nat, ..) *)
Print list.

(* Pour faciliter les choses, on va fixer ici un type de listes *)
Parameter A : Set.

(* Ainsi, quand vous déclarez un type de listes, utilisez "list A" *)

(* Définissez une fonction "rev" qui renvoie le retournement de son argument, 
en utilisant la fonction "++" qui permet de concatener deux listes, 
puis prouvez que c'est une involution, en s'aidant de ces lemmes intermédiaires. *)

Fixpoint rev (l:list A) : list A := 
  match l with 
    | nil => nil
    | a :: m => rev(m) ++ (a::nil)
  end.
(* Encore une fois, on peut utiliser le principe d'induction sur les listes [induction l] *)
Check list_ind.


(* On vous donne également quelques lemmes intérmédiaires en Coq *)
Check app_nil_end.
Check app_assoc.

(* Prouvez maintenant les lemmes suivants. Vous aurez besoin encore d'une nouvelle tactique :
    [rewrite H] 
    Si H est une hypothèse de la forme "a = b", [rewrite H] remplace dans le but toutes les 
    occurences de "a" par "b". Inversement, nous avons aussi:
    [rewrite <- H]
    Si H est une hypothèse de la forme "a = b", [rewrite H] remplace dans le but toutes les 
    occurences de "b" par "a". *)

Lemma rev_concat : forall xs ys, rev (xs ++ ys) = rev ys ++ rev xs.
intros xs ys.
induction xs.
-simpl.
apply app_nil_end.
-simpl.
rewrite app_assoc.
now rewrite IHxs.
Qed.



Lemma rev_singleton : 
  forall xs x, rev (xs ++ (x :: nil)) = x :: rev xs.
intros xs x.
rewrite rev_concat.
simpl.
reflexivity.
Qed.

Lemma rev_involution : forall l, rev (rev l) = l.
intro l.
induction l.
-reflexivity.
-simpl.
now rewrite rev_singleton,IHl.
Qed.

(* Ce n'est pas très économique de retourner des listes en appelant à
chaque fois "++". Trouver une solution plus rapide puis prouver
l'équivalence des deux. *)
Fixpoint rev2_aux (l acc:list A) : list A := 
  match l with 
    | nil => acc
    | a :: m => rev2_aux m (a::acc)
  end.

  Definition revopt l:= rev2_aux l nil.



(* N'hésitez pas à prouver des lemmes intérmédiaires, surtout si vous utilisez des 
fonctions auxiliaires... *)

(* [...] 

Lemma revopt_correct : forall l, revopt l = rev l.
[...]
Qed.
*)

(* Voyez avec votre chargé de TP si vous avez programmé la version "optimisée" de rev. 
dans le cas contraire, introduisez rev' et montrez que les deux fonctions coïncident *)

(*
[...]
*)

(* Utiliser List.fold_left pour donner une définition alternative de la fonction qui 
  calcule la longueur d'une liste *)
Check List.fold_left.

Definition fold_length (l : list A) : nat :=
0.

(* ?? *)

(* Définissez une fonction perms : nat -> list (list nat) telle que perms k 
  renvoie la liste de toutes les permutations de la liste [0;..;k] 
  Prouvez ensuite des tas de propriétés intéressantes de perms.
  Bonne Chance ! *)

  


(*** Loqique, booléens, propositions et IMP ***)

(* Négation *)
(* On peut voir le faux, noté False, comme un connecteur logique, qui
peut être inséré dans le "tableau" où figuraient la conjonction et
l'existentielle: 

    connecteur    | pour utiliser |  pour construire
  ----------------|---------------|---------------------
      P /\ Q      |  destruct H.  |  split.
      P \/ Q      |  destruct H.  |  left. / right.
  exists x:nat, P |  destruct H.  |  exists 17.
      False       |  destruct H.  |

Devinez :
- pourquoi il n'y a pas de tactique dans la colonne "pour construire" de ce tableau.
- ce que fait "destruct H." si H est une hypothèse qui dit False. *)

(* A vous de jouer : prouvez les lemmes suivants *)

Lemma ex_falso: forall P : Prop, False -> P.
intro P.
intro H.
destruct H.
Qed.

(* Si l'on a A:Prop, alors ~A, la négation de A, est une notation pour "A -> False". *)
(* Si la notation vous perturbe, vous pouvez toujours utiliser la tactique [unfold not.] *)

Lemma not_not : forall P : Prop, P -> ~~P.
intros P H N.
apply (N H).
Qed.


Lemma morgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
intros P Q H1 H2.
destruct H1;destruct H2 as [HP HQ] ;apply H;[exact HP|exact HQ].
Qed.

Lemma morgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
intros P Q H1 H2.
destruct H1.
destruct H2.
-apply H.
exact H1.
-apply H0.
exact H1.
Qed.


(* Pour la prochaine preuve, vous aurez besoin d'une nouvelle tactique : 
  [inversion H.]
Formellement, lorsque l'on appelle [inversion H], Coq essaye de 
trouver les conditions nécessaires pour que l'hypothèse H soit vérifiée.
Coq fait aussi quelques simplifications lorsque l'on utilise inversion : si H est fausse, alors 
il termine automatiquement la preuve, si H implique une égalité entre 2 expressions, il fait 
parfois automatiquement le remplacement. 
Essayez cette tactique sur les prochains lemmes pour comprendre comment elle marche en pratique  *)

Lemma zero_un : ~(0=1).

intro H.
inversion H.
Qed.
(*Notez que "x <> y" est un raccourci de "x = y -> False".*)

(* Un autre exemple d'application de la tactique inversion, indépendamment de la négation *)
Lemma S_out :  forall n m : nat, S n = S m -> n = m.
intros n m H.
inversion H.
reflexivity.
Qed.


(* Dans le même style, les différents constructeurs d'un type inductif ne peuvent pas renvoyer la même valeur.
Revenons sur la tentative de définition  des entiers avec le successeur ET le prédécesseur, vue en cours. *)
Inductive t : Set :=
  Ze : t | Pr : t -> t | Su : t -> t.

Lemma S_et_P : forall x y, Su x = Pr y -> False.
intros x y H.
inversion H.
Qed.

(** Food for thought : à méditer après ce TP, ou si par hasard vous avez fini 
le reste avant la fin. Avec la syntaxe au-dessus, il est évident que le 
"prédécesseur" du "successeur" de "zéro" et "zéro" ne définissent pas le même
 objet: *)

Lemma PSZ: Pr (Su Ze) = Ze -> False.
  intros H. inversion H.
Qed.

Require Export ZArith.

(** Sauriez-vous montrer la même chose en remplaçant "zéro" par un x (de type t)
quelconque ? 
On insiste sur le fait que cette question est plutôt pour emmener à la maison 
que pour pendant le TP. Nous serons par ailleurs ravis de recevoir des mails 
si vous avez des questions là-dessus.
Un indice : souvenez-vous de vos cours de maths, où vous avez sûrement été déjà 
amené.e.s à prouver des résultats plus forts et plus généraux pour parvenir à
vos fins. 
Si besoin, vous pourrez vous servir de la tactique [omega] (chargée avec la 
librairie ZArith au-dessus, pour résoudre de buts arithmétiques (notamment 
obtenir faux à partir d'une hypothèse évidemment fausse comme x < x ou 2 < 0), 
et vous pouvez aussi invoquer la tactique [Search bla] pour chercher des lemmes
contenant "bla", comme dans: *)

Search "<" "S".



(*Lemma inj_PS: forall x, Pr (Su x) = x -> False.
[...]
Qed.*)




(** * Les booléens et les propositions **)

(* Il y a en Coq deux moyens d'exprimer des affirmations logiques, avec des booléens (le type bool) ou
des propositions (le type prop *)
Check True. 
Check False.
Check true.
Check false.

(*Un booléen est soit "true" soit "false". Ainsi, si on définit la fonction "and" suivante : *)

Definition Booland a b := match a,b with 
  | true,true => true
  | true,false => false
  | false,true => false
  | false,false => false
end.

(* Et qu'on l'évalue, on obtient soit true, soit false *)

Eval compute in (Booland false true).
Eval compute in (Booland true true).


(* Il est important de garder à l'esprit que ceci est spécifique au type "bool".
En effet, un objet de type "Prop" n'est pas quelque chose que l'on peut 
simplifier soit en True soit en False, mais plutôt un énoncé dont on peut 
avoir une preuve (preuve que l'on peut construire en Coq à l'aide de tactiques).
*)


Eval compute in (False /\ True).

(* On va travailler un peu sur ces différences dans un exemple *) 
(* On donne deux moyens de prouver qu'un entier est pair. *)

Definition not a := match a with 
  |false => true
  |true => false
end.

Fixpoint evenb n := match n with 
  | 0 => true
  | S n' => not (evenb n')
end.

Definition even_bool n := evenb n = true.

(* Prouvez que 42 est pair avec cette définition *)

Lemma even_42_bool : even_bool 42.
unfold even_bool.
simpl.
reflexivity.
Qed.

(* Une seconde définition avec une fonction "double" *)

Fixpoint double n := match n with 
  |0 => 0
  |S n' => S (S (double n'))
end.

Definition even_prop n := exists k, n = double k.

(* Prouvez une nouvelle fois que 42 est pair *)

Lemma even_42_prop : even_prop 42.
unfold even_prop.
exists 21.
simpl.
reflexivity.
Qed.

(* Et maintenant, on va prouvez que finalement, ces deux définitions sont équivalentes *)
(* On aura besoin pour cela de lemmes auxiliaires, prouvez les. *)
(* Indice : Vous pouvez utiliser la tactique [case a] quand "a" est un booléen pour traiter les deux cas "true" et "false".
Cela ne modifiera que dans l'objectif.*)

Lemma Not_invol : forall a, not (not a) = a.
intro a.
case a.
-simpl.
reflexivity.
-simpl.
reflexivity.
Qed.

Lemma Not_false : forall a, not a = false -> a = true.
intros a H.
destruct a.
-reflexivity.
-inversion H.
Qed.

Lemma Not_true : forall a, not a = true -> a = false. 
intros a H.
destruct a.
-inversion H.
-reflexivity.
Qed.

Lemma evenb_double : forall k, even_bool (double k).
intro k.
unfold even_bool.
induction k.
-simpl.
reflexivity.
-simpl.
rewrite IHk.
simpl.
reflexivity.
Qed.



(*Tentez de prouver que la définition booléenne implique la définition propositionnelle*)
Lemma even_bool_to_prop : forall n, even_bool n -> even_prop n.
intros n H.
induction n.
-unfold even_prop.
exists 0.
simpl.
reflexivity.
-unfold even_prop.
unfold even_bool in H.
unfold even_bool, even_prop in IHn.
unfold evenb in H, IHn.
Abort.


(* Dans certains cas, on aura besoin d'une hypothèse d'induction plus forte que ce l'on souhaite prouver.
Note : Comme l'hypothèse d'induction 'est' notre objectif, "intro H. induction x" donnera une hypothèse d'induction
plus faible que "induction x" puis "intro H" dans les sous-cas.*)
(* Comprenez et completez la preuve à trous suivante: *)

Lemma evenb_double_conv : forall n, 
(evenb n = true -> exists k, n = double k) /\ (evenb n = false -> exists k, n = S (double k)).
induction n.
-split.
intro H.
exists 0.
simpl.
reflexivity.
intro H.
inversion H.
-simpl. 
destruct IHn. 
split.
intros. destruct H0.
apply Not_true.
apply H1.
rewrite H0.
exists (S x).
simpl.
reflexivity.
intros. destruct H.
apply Not_false.
apply H1.
rewrite H.
exists x.
reflexivity.
Qed.

(* On peut maintenant prouver l'équivalence entre les deux *)
Lemma even_bool_prop : forall n, even_prop n <-> even_bool n.
intro n.
unfold even_prop, even_bool.
-split.
intro H.
destruct H.
rewrite H.
apply evenb_double.
intro H.
apply evenb_double_conv.
apply H.
Qed.

(* Sur cet exemple, vous avez normalement constaté qu'il est plus difficile de travailler sur 
les preuves avec les booléens que les propositions.
En effet, on est passé assez facilement des propositions aux booléens (evenb_double) mais l'inverse était plus compliqué. *)

(* En revanche, sur la preuve que 42 est paire, sur les booléens il n'y a presque rien à faire, mais pour les propositions, 
il faut au minimum donner l'entier correspondant à l'existentiel... *)
(* Ou bien, si on ne veut pas donner l'entier, on peut faire la preuve suivante... *)

Lemma even_42_prop_bis : even_prop 42.
apply even_bool_prop. reflexivity. Qed.

(* Sur cet exemple, on ne gagne pas vraiment à utiliser cette preuve. Mais sur certains cas, il peut être utile de connaitre cette 
technique. Un exemple extreme serait la preuve en Coq du théorème des 4 couleurs, 
dans laquelle ce procédé est utilisé pour qu'une preuve qui aurait eu besoin d'une analyse de centaines de cas soit 
capturé par un calcul sur les booléens. *)

(* Un exemple plus simple serait le suivant. Prouvez ce lemme *)

Lemma not_even_1001 : ~(even_bool 1001).
intro H.
inversion H.
Qed.

(* Et celui-ci ? Voyez-vous le problème ?*)

Lemma not_even_1001_bis : ~(even_prop 1001).
intro H.
apply even_bool_prop in H.
inversion H.
Qed.



(* Petit bonus : La fin de cette partie permet de vous familiariser d'avantager aux équivalences bool/Prop.
Il n'est pas nécessaire de la faire en TP, particulièrement si vous avez l'impression d'être en retard.*)
(* Si Coq râle, n'hésitez à commenter les parties non faites *)

(* Prouvez le lemme suivant *)

(*JE SUIS COINCÉ*)
Lemma andb_true_iff : forall a b, Booland a b = true <-> (a = true /\ b = true).
intros a b.
split.
-intro H.
split.
case a.
reflexivity.
Qed.

(* Définissez la fonction "Boolor" pour les booléens *)

Definition Boolor a b := .

(* Prouvez comme ci-dessus l'équivalence avec \/ *)

[...]

(* Fin du bonus. *)

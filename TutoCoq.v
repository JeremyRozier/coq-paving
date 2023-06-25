(*** Introduction \u00e0 Coq : formules, entiers et listes ***)

(* Pour avoir les raccourcis comme il faut dans coqide :
- Lancer "coqide" dans un terminal
- Edit > Preferences > Shortcuts > Modifiers for Navigation Menu
- Changer vers <alt> (selon les versions:
  - Taper Alt+W dans le champ, ou,
  - Laisser le bouton <alt> seul enfon\u00e7\u00e9)
- Cliquer sur OK
- Quitter coqide
- Relancer coqide *)

(* Les exercices sont issus de TP que j'ai donn\u00e9 accompagnant un cours, 
normalement \u00e7a devrait \u00eatre auto-suffisant mais il pourrait rester quelques
r\u00e9f\u00e9rences \u00e0 d'autres documents, ce n'est pas vital de les avoir a priori.

Attention, les exercices ne sont pas forc\u00e9ment rang\u00e9 par difficult\u00e9 croissante,
il y a un mix de 2 TPs, et le d\u00e9but du 2\u00e8me est plus simple que la fin du premier. *)

(*** Logique Simple ***)

(* Les deux tactiques centrales de Coq sont :

  [intro]
    L'\u00e9quivalent de "soit x" et de "supposons que..."  dans les maths
    informelles, [intro] introduit un nouvel objet (entit\u00e9 sur
    laquelle on raisonne, ou hypoth\u00e8se) dans le contexte.
    On peut nommer l'objet que l'on introduit, avec [intro x] ou
    [intro H], par exemple.
    La variante [intros] fait [intro] autant que possible, en
    choisissant (plus ou moins arbitrairement) des noms pour les
    hypoth\u00e8ses ainsi cr\u00e9\u00e9es.
    
  [apply H]
    Permet d'invoquer l'hypoth\u00e8se nomm\u00e9e H. *)

    Lemma trivial1 : forall P : Prop, P -> P.
    intro P. intro H. apply H. Qed.
    
    (* \u00c0 vous de jouer maintenant !
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
    
    
    (* Une derni\u00e8re chose \u00e0 propose de apply. Observez la preuve suivante, 
    que vous pourriez avoir \u00e9crite sans difficult\u00e9. *)
    
    Lemma trivial4: forall P, (forall x, P x) -> P 2.
      intros P H.
      apply H.
    Qed.
    
    
    (* \u00c0 la deuxi\u00e8me ligne, on a appliqu\u00e9 l'hypoth\u00e8se (H: forall x, P x) 
    pour en d\u00e9duire (P 2), qui ne co\u00efncide pourtant pas avec l'hypoth\u00e8se. 
    En r\u00e9alit\u00e9, ce que Coq a fait pour vous, c'est qu'il a devin\u00e9 que vous
    vouliez appliquez l'hypoth\u00e8se H dans le cas particulier o\u00f9 x vaut 2. 
    C'est \u00e0 dire: *)
    
    Lemma trivial4': forall P, (forall x, P x) -> P 2.
      intros P H.
      Check (H 2).
      apply (H 2).
    Qed.
    
    
    (* Autrement dit, on peut (et m\u00eame parfois on doit) pr\u00e9ciser les arguments
     d'une hypoth\u00e8se quand on l'applique.
    Apr\u00e8s avoir m\u00e9dit\u00e9 sur cette id\u00e9e, prouver le lemme suivant: *)
    Lemma apply1: forall (P : nat -> Prop), (forall x y, P x -> P y) -> P 2 -> P 3. 
      intros A B C.
      Check (B 2,3).
      apply (B 2,3).
      apply C.
    Qed.
    
    
    
    (* Pour chaque connecteur logique, Coq fournit une tactique pour l'utiliser
    quand il est en hypoth\u00e8se et une tactique pour le "construire" quand
    il est en but. Voici ce qui a \u00e9t\u00e9 vu en cours pour la conjonction et
    l'existentielle :
    
        connecteur    | pour utiliser |  pour construire
      ----------------|---------------|---------------------
          P /\ Q      |  destruct H.  |  split.
      exists x:nat, P |  destruct H.  |  exists 17.
    *)
    
    (* La disjonction est not\u00e9e \/ en Coq.
       Pour prouver un but de la forme A \/ B, on dispose des deux tactiques "left." et "right.".
       Devinez ce qui se passe lorsque l'on a une hypoth\u00e8se de la forme "H : A\/B"
       dans le but courant, et que l'on fait [destruct H].
       V\u00e9rifiez que vous avez devin\u00e9 juste en prouvant les lemmes suivants. *)
    
    Set Implicit Arguments. 
    
    Lemma conj1: forall P Q : Prop, P /\ Q -> P.
    intros P Q H.
    destruct H.
    apply H.
    Qed.
    
    Lemma conj2: forall P Q : Prop, P -> Q -> P /\ Q. (* Pourquoi \u00e7a split l'hypoth\u00e8se *)
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
       Vous aurez besoin pour cela des tactiques suivantes pour travailler sur les expressions enti\u00e8res : 
    
        [reflexivity] 
          Permet de prouver un but de la forme "a = a". Cette tactique peut aussi s'utiliser pour 
          d'autres relations reflexive.
    
        [simpl]
          Permet de simplifier une expression dans le but. On verra plus formellement plus tard 
          comment \u00e7a marche, mais pour l'instant vous pouvez voir \u00e7a comme une tactique permettant 
          de r\u00e9\u00e9crire par exemple "2*2" en "4".  
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
    (* Devinez l'\u00e9nonc\u00e9 du lemme suivant, et prouvez-le *)
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
    
    
    
    
    (*** Arithm\u00e9tique Simple sur les Entiers ***)
    
    (* Inspirez-vous des d\u00e9finitions de plusnat et pred vues en cours 
    pour d\u00e9finir la soustraction sur les naturels, qui satisfera la propri\u00e9t\u00e9 n-(n+k)=0 *)
    
    
    
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
        Permet de s\u00e9parer une preuve sur n en deux : d'abord le cas "n = 0", puis le cas "n = S n0". *)
    
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
        Permet de faire une preuve par r\u00e9currence sur l'entier n (ou une induction sur n). 
        Il vous faudra alors, comme en maths, prouver le cas "n=0" puis le cas "S n" en supposant la propri\u00e9t\u00e9 vraie
    pour n *)
    
    (* Formellement, le principe d'induction est r\u00e9sum\u00e9 par la formule suivante en Coq : *)
    Check nat_ind.
    
    (* Notez la diff\u00e9rence avec la tactique [case] pr\u00e9c\u00e9dente. *)
    Check nat_case.
    
    (* Indice suppl\u00e9mentaire : Maintenant que vous avez prouv\u00e9 le lemme "minus_zero", vous pouvez maintenant 
    \u00e9crire [apply minus_zero] pour utiliser ce lemme. *)
    
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
    
    (** Pour vous montrer qu'avec Coq on peut aussi faire des math\u00e9matiques,
    on va chercher ici \u00e0 prouver quelques r\u00e9sultats tr\u00e8s simples sur les ordres. 
    Pour commencer, on se donne un objet X fix\u00e9 (la carri\u00e8re de l'ensemble ordonn\u00e9
    que l'on va consid\u00e9rer, et l'on d\u00e9finit ce qu'est une relation sur X, \u00e0 savoir
    une proposition portant sur deux \u00e9l\u00e9ments de X. *)
    
    Parameter X : Set.
    Definition relation:= X -> X -> Prop.
    
    (** Obversez qu'ici, les relations sont d\u00e9finies commes des fonctions.
    On pourrait par exemple d\u00e9finir la relation d'ordre sur les entiers 
    en utilisant le fait que n\u2264m ssi n-m = 0 : *)
    
    Definition leq n m:=  n - m = 0.
    
    (** On v\u00e9rifie que leq a bien le bon type.*)
    Check leq.
    
    (** Alternativement, on peut utiliser (comme en OCaml) le mot-cl\u00e9 [fun] 
    \u00e0 travers la structure:
    
         Definition f:= fun x y z => ...
    
    pour d\u00e9finir des fonctions. La d\u00e9finition pr\u00e9c\u00e9dente est ainsi \u00e9quivalente \u00e0:
    *)
    
    Definition leq':=fun n m => n-m = 0.
    
    
    (** Comme vous le savez s\u00fbrement d\u00e9j\u00e0, un ordre est une relation r\u00e9flexive,
     anti-sym\u00e9trique et transitive. D\u00e9finissez ici ces diff\u00e9rentes notions. *)
    
    Definition reflexive (R:relation):= forall n : X, R n n.
    
    Definition antisymmetric (R:relation):= forall n m : X, R n m -> ~(R m n).
    
    Definition transitive (R:relation):=forall n m p : X, (R n m) /\ (R m p) -> R n p.
    
    Definition order (R:relation):= reflexive R /\ antisymmetric R /\ transitive R.
    
    
    (** Dans la suite, si vous avez besoin de d\u00e9plier une d\u00e9finition, vous
    pouvez utiliser la tactique:
        [unfold f]
    qui permet de remplacer dans le but le nom "f" d\u00e9finit plus haut par son 
    expression. De m\u00eame, vous pouvez d\u00e9plier une op\u00e9ration dans l'une des 
    hypoth\u00e8ses du contexte en utilisant:
        [unfold f in H]
    *)
    
    
    (** Pour commencer, on va montrer que l'ordre invers\u00e9 (i.e. la relation 
    "retourn\u00e9e") d\u00e9finit lui-m\u00eame un ordre. 
    D\u00e9finissez ici ce qu'est le retourn\u00e9e d'une relation. *)
    
    (*JE SUIS COINC\u00c9*)
    
    (* Definition reverse (R:relation):= fun x y => (x <> y -> ~R x y) \/ (x = y -> R x x). *)
    (* Print reverse. *)
    
    (* C'est normal, l\u00e0 tu as d\u00e9finies quelque chose d'assez surprenant. Ce qu'on entend
    par ordre invers\u00e9e ou relation retourn\u00e9e pour une relation R, c'est juste la relation R'
    telle que R' x y = R y x. *)
    
    Definition reverse (R:relation) := fun x y => R y x.
    
    (** On peut maintenant montrer que si une relation est 
    (r\u00e9flexive|anti-sym\u00e9trique|transitive) sa relation inverse l'est aussi. *)
    
    
    Lemma rev_refl (R:relation): reflexive R -> reflexive (reverse R).
    intro H.
    unfold reflexive.
    intro n.
    unfold reverse.
    apply H.
    Qed.
    
    (*JE SUIS COINC\u00c9*)
    Lemma rev_antisym (R:relation): antisymmetric R -> antisymmetric (reverse R).
    intro H0.
    unfold antisymmetric in H0.
    unfold antisymmetric.
    unfold reverse.
    intros n m H1 H2.
    Admitted.

  

    
    
    Lemma rev_trans (R:relation): transitive R -> transitive (reverse R).
    Admitted.
    
    (** On peut maintenant facilement montrer qu'un ordre invers\u00e9 est 
    lui-m\u00eame un ordre. *)
    
    Lemma rev_order (R:relation):  order R -> order (reverse R).
    Admitted.
    
    
    
    (*** Fonctions sur les listes ***)
    
    (* Une "incantation" pour avoir acc\u00e8s \u00e0 la biblioth\u00e8que Coq traitant des listes *)
    Require Export List.
    
    (* Coq conna\u00eet les listes polymorphes : les "listes de A", pour un type A quelconque
      (liste de naturels, de bool\u00e9ens, de listes de naturels, de fonctions de type nat -> nat, ..) *)
    Print list.
    
    (* Pour faciliter les choses, on va fixer ici un type de listes *)
    Parameter A : Set.
    
    (* Ainsi, quand vous d\u00e9clarez un type de listes, utilisez "list A" *)
    
    (* D\u00e9finissez une fonction "rev" qui renvoie le retournement de son argument, 
    en utilisant la fonction "++" qui permet de concatener deux listes, 
    puis prouvez que c'est une involution, en s'aidant de ces lemmes interm\u00e9diaires. *)
    
    Fixpoint rev (l:list A) : list A := 
      match l with 
        | nil => nil
        | a :: m => rev(m) ++ (a::nil)
      end.
    (* Encore une fois, on peut utiliser le principe d'induction sur les listes [induction l] *)
    Check list_ind.
    
    
    (* On vous donne \u00e9galement quelques lemmes int\u00e9rm\u00e9diaires en Coq *)
    Check app_nil_end.
    Check app_assoc.
    
    (* Prouvez maintenant les lemmes suivants. Vous aurez besoin encore d'une nouvelle tactique :
        [rewrite H] 
        Si H est une hypoth\u00e8se de la forme "a = b", [rewrite H] remplace dans le but toutes les 
        occurences de "a" par "b". Inversement, nous avons aussi:
        [rewrite <- H]
        Si H est une hypoth\u00e8se de la forme "a = b", [rewrite H] remplace dans le but toutes les 
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
    
    (* Ce n'est pas tr\u00e8s \u00e9conomique de retourner des listes en appelant \u00e0
    chaque fois "++". Trouver une solution plus rapide puis prouver
    l'\u00e9quivalence des deux. *)
    Fixpoint rev2_aux (l acc:list A) : list A := 
      match l with 
        | nil => acc
        | a :: m => rev2_aux m (a::acc)
      end.
    
      Definition revopt l:= rev2_aux l nil.
    
    
    
    (* N'h\u00e9sitez pas \u00e0 prouver des lemmes int\u00e9rm\u00e9diaires, surtout si vous utilisez des 
    fonctions auxiliaires... *)
    
    (* [...] 
    
    Lemma revopt_correct : forall l, revopt l = rev l.
    [...]
    Qed.
    *)
    
    (* Voyez avec votre charg\u00e9 de TP si vous avez programm\u00e9 la version "optimis\u00e9e" de rev. 
    dans le cas contraire, introduisez rev' et montrez que les deux fonctions co\u00efncident *)
    
    (*
    [...]
    *)
    
    (* Utiliser List.fold_left pour donner une d\u00e9finition alternative de la fonction qui 
      calcule la longueur d'une liste *)
    Check List.fold_left.
    
    Definition fold_length (l : list A) : nat :=
    0.
    
    (* ?? *)
    
    (* D\u00e9finissez une fonction perms : nat -> list (list nat) telle que perms k 
      renvoie la liste de toutes les permutations de la liste [0;..;k] 
      Prouvez ensuite des tas de propri\u00e9t\u00e9s int\u00e9ressantes de perms.
      Bonne Chance ! *)
    
      
    
    
    (*** Loqique, bool\u00e9ens, propositions et IMP ***)
    
    (* N\u00e9gation *)
    (* On peut voir le faux, not\u00e9 False, comme un connecteur logique, qui
    peut \u00eatre ins\u00e9r\u00e9 dans le "tableau" o\u00f9 figuraient la conjonction et
    l'existentielle: 
    
        connecteur    | pour utiliser |  pour construire
      ----------------|---------------|---------------------
          P /\ Q      |  destruct H.  |  split.
          P \/ Q      |  destruct H.  |  left. / right.
      exists x:nat, P |  destruct H.  |  exists 17.
          False       |  destruct H.  |
    
    Devinez :
    - pourquoi il n'y a pas de tactique dans la colonne "pour construire" de ce tableau.
    - ce que fait "destruct H." si H est une hypoth\u00e8se qui dit False. *)
    
    (* A vous de jouer : prouvez les lemmes suivants *)
    
    Lemma ex_falso: forall P : Prop, False -> P.
    intro P.
    intro H.
    destruct H.
    Qed.
    
    (* Si l'on a A:Prop, alors ~A, la n\u00e9gation de A, est une notation pour "A -> False". *)
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
    trouver les conditions n\u00e9cessaires pour que l'hypoth\u00e8se H soit v\u00e9rifi\u00e9e.
    Coq fait aussi quelques simplifications lorsque l'on utilise inversion : si H est fausse, alors 
    il termine automatiquement la preuve, si H implique une \u00e9galit\u00e9 entre 2 expressions, il fait 
    parfois automatiquement le remplacement. 
    Essayez cette tactique sur les prochains lemmes pour comprendre comment elle marche en pratique  *)
    
    Lemma zero_un : ~(0=1).
    
    intro H.
    inversion H.
    Qed.
    (*Notez que "x <> y" est un raccourci de "x = y -> False".*)
    
    (* Un autre exemple d'application de la tactique inversion, ind\u00e9pendamment de la n\u00e9gation *)
    Lemma S_out :  forall n m : nat, S n = S m -> n = m.
    intros n m H.
    inversion H.
    reflexivity.
    Qed.
    
    
    (* Dans le m\u00eame style, les diff\u00e9rents constructeurs d'un type inductif ne peuvent pas renvoyer la m\u00eame valeur.
    Revenons sur la tentative de d\u00e9finition  des entiers avec le successeur ET le pr\u00e9d\u00e9cesseur, vue en cours. *)
    Inductive t : Set :=
      Ze : t | Pr : t -> t | Su : t -> t.
    
    Lemma S_et_P : forall x y, Su x = Pr y -> False.
    intros x y H.
    inversion H.
    Qed.
    
    (** Food for thought : \u00e0 m\u00e9diter apr\u00e8s ce TP, ou si par hasard vous avez fini 
    le reste avant la fin. Avec la syntaxe au-dessus, il est \u00e9vident que le 
    "pr\u00e9d\u00e9cesseur" du "successeur" de "z\u00e9ro" et "z\u00e9ro" ne d\u00e9finissent pas le m\u00eame
     objet: *)
    
    Lemma PSZ: Pr (Su Ze) = Ze -> False.
      intros H. inversion H.
    Qed.
    
    Require Export ZArith.
    
    (** Sauriez-vous montrer la m\u00eame chose en rempla\u00e7ant "z\u00e9ro" par un x (de type t)
    quelconque ? 
    On insiste sur le fait que cette question est plut\u00f4t pour emmener \u00e0 la maison 
    que pour pendant le TP. Nous serons par ailleurs ravis de recevoir des mails 
    si vous avez des questions l\u00e0-dessus.
    Un indice : souvenez-vous de vos cours de maths, o\u00f9 vous avez s\u00fbrement \u00e9t\u00e9 d\u00e9j\u00e0 
    amen\u00e9.e.s \u00e0 prouver des r\u00e9sultats plus forts et plus g\u00e9n\u00e9raux pour parvenir \u00e0
    vos fins. 
    Si besoin, vous pourrez vous servir de la tactique [omega] (charg\u00e9e avec la 
    librairie ZArith au-dessus, pour r\u00e9soudre de buts arithm\u00e9tiques (notamment 
    obtenir faux \u00e0 partir d'une hypoth\u00e8se \u00e9videmment fausse comme x < x ou 2 < 0), 
    et vous pouvez aussi invoquer la tactique [Search bla] pour chercher des lemmes
    contenant "bla", comme dans: *)
    
    Search "<" "S".
    
    
    
    (*Lemma inj_PS: forall x, Pr (Su x) = x -> False.
    [...]
    Qed.*)
    
    
    
    
    (** * Les bool\u00e9ens et les propositions **)
    
    (* Il y a en Coq deux moyens d'exprimer des affirmations logiques, avec des bool\u00e9ens (le type bool) ou
    des propositions (le type prop *)
    Check True. 
    Check False.
    Check true.
    Check false.
    
    (*Un bool\u00e9en est soit "true" soit "false". Ainsi, si on d\u00e9finit la fonction "and" suivante : *)
    
    Definition Booland a b := match a,b with 
      | true,true => true
      | true,false => false
      | false,true => false
      | false,false => false
    end.
    
    (* Et qu'on l'\u00e9value, on obtient soit true, soit false *)
    
    Eval compute in (Booland false true).
    Eval compute in (Booland true true).
    
    
    (* Il est important de garder \u00e0 l'esprit que ceci est sp\u00e9cifique au type "bool".
    En effet, un objet de type "Prop" n'est pas quelque chose que l'on peut 
    simplifier soit en True soit en False, mais plut\u00f4t un \u00e9nonc\u00e9 dont on peut 
    avoir une preuve (preuve que l'on peut construire en Coq \u00e0 l'aide de tactiques).
    *)
    
    
    Eval compute in (False /\ True).
    
    (* On va travailler un peu sur ces diff\u00e9rences dans un exemple *) 
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
    
    (* Prouvez que 42 est pair avec cette d\u00e9finition *)
    
    Lemma even_42_bool : even_bool 42.
    unfold even_bool.
    simpl.
    reflexivity.
    Qed.
    
    (* Une seconde d\u00e9finition avec une fonction "double" *)
    
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
    
    (* Et maintenant, on va prouvez que finalement, ces deux d\u00e9finitions sont \u00e9quivalentes *)
    (* On aura besoin pour cela de lemmes auxiliaires, prouvez les. *)
    (* Indice : Vous pouvez utiliser la tactique [case a] quand "a" est un bool\u00e9en pour traiter les deux cas "true" et "false".
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
    
    
    
    (*Tentez de prouver que la d\u00e9finition bool\u00e9enne implique la d\u00e9finition propositionnelle*)
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
    
    
    (* Dans certains cas, on aura besoin d'une hypoth\u00e8se d'induction plus forte que ce l'on souhaite prouver.
    Note : Comme l'hypoth\u00e8se d'induction 'est' notre objectif, "intro H. induction x" donnera une hypoth\u00e8se d'induction
    plus faible que "induction x" puis "intro H" dans les sous-cas.*)
    (* Comprenez et completez la preuve \u00e0 trous suivante: *)
    
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
    
    (* On peut maintenant prouver l'\u00e9quivalence entre les deux *)
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
    
    (* Sur cet exemple, vous avez normalement constat\u00e9 qu'il est plus difficile de travailler sur 
    les preuves avec les bool\u00e9ens que les propositions.
    En effet, on est pass\u00e9 assez facilement des propositions aux bool\u00e9ens (evenb_double) mais l'inverse \u00e9tait plus compliqu\u00e9. *)
    
    (* En revanche, sur la preuve que 42 est paire, sur les bool\u00e9ens il n'y a presque rien \u00e0 faire, mais pour les propositions, 
    il faut au minimum donner l'entier correspondant \u00e0 l'existentiel... *)
    (* Ou bien, si on ne veut pas donner l'entier, on peut faire la preuve suivante... *)
    
    Lemma even_42_prop_bis : even_prop 42.
    apply even_bool_prop. reflexivity. Qed.
    
    (* Sur cet exemple, on ne gagne pas vraiment \u00e0 utiliser cette preuve. Mais sur certains cas, il peut \u00eatre utile de connaitre cette 
    technique. Un exemple extreme serait la preuve en Coq du th\u00e9or\u00e8me des 4 couleurs, 
    dans laquelle ce proc\u00e9d\u00e9 est utilis\u00e9 pour qu'une preuve qui aurait eu besoin d'une analyse de centaines de cas soit 
    captur\u00e9 par un calcul sur les bool\u00e9ens. *)
    
    (* Un exemple plus simple serait le suivant. Prouvez ce lemme *)
    
    Lemma not_even_1001 : ~(even_bool 1001).
    intro H.
    inversion H.
    Qed.
    
    (* Et celui-ci ? Voyez-vous le probl\u00e8me ?*)
    
    Lemma not_even_1001_bis : ~(even_prop 1001).
    intro H.
    apply even_bool_prop in H.
    inversion H.
    Qed.
    
    
    
    (* Petit bonus : La fin de cette partie permet de vous familiariser d'avantager aux \u00e9quivalences bool/Prop.
    Il n'est pas n\u00e9cessaire de la faire en TP, particuli\u00e8rement si vous avez l'impression d'\u00eatre en retard.*)
    (* Si Coq r\u00e2le, n'h\u00e9sitez \u00e0 commenter les parties non faites *)
    
    (* Prouvez le lemme suivant *)
    
    (*JE SUIS COINC\u00c9*)
    Lemma andb_true_iff : forall a b, Booland a b = true <-> (a = true /\ b = true).
    intros a b.
    split.
    -intro H.
    split.
    destruct a.
    reflexivity.
    rewrite <- H.
    case b.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    destruct b.
    reflexivity.
    rewrite <- H.
    case a.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    -intro H.
    destruct H.
    rewrite H. rewrite H0.
    simpl.
    reflexivity.
    Qed.
    
    (* D\u00e9finissez la fonction "Boolor" pour les bool\u00e9ens *)
    
    Definition Boolor a b := match a, b with
    |true,_ => true
    |_,true => true
    |false, false => false
    end.
    
    (* Prouvez comme ci-dessus l'\u00e9quivalence avec \/ *)
    
    Lemma orb_true_iff : forall a b, Boolor a b = true <-> (a = true \/ b = true).
    Proof.
    intros a b. (* Introduce variables a and b *)
    split.
    -intro H. 
    +destruct a. 
    left.
    reflexivity. 
    destruct b.
    right.
    reflexivity.
    left.
    simpl in H.
    inversion H.
    -intro H.
    destruct H.
    rewrite H.
    simpl.
    reflexivity.
    rewrite H.
    case a.
    +simpl.
    reflexivity.
    +simpl.
    reflexivity.
    Qed.
    
    
    
    (* Fin du bonus. *)
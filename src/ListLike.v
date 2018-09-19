Require Import Coq.Program.Tactics.

Class ListLike (L : Type -> Type) : Type :=
  {
    (* constructors *)
    ll_nil : forall {A}, L A;
    ll_cons : forall {A}, A -> L A -> L A;

    (* eliminators *)
    list_like_rec :
      forall {A : Type} (P : L A -> Set),
        P ll_nil -> (forall (a : A) (l : L A), P l -> P (ll_cons a l)) -> forall l : L A, P l;
    list_like_rect :
      forall {A : Type} (P : L A -> Type),
        P ll_nil -> (forall (a : A) (l : L A), P l -> P (ll_cons a l)) -> forall l : L A, P l;
    list_like_ind :
      forall {A : Type} (P : L A -> Prop),
        P ll_nil -> (forall (a : A) (l : L A), P l -> P (ll_cons a l)) -> forall l : L A, P l;

    (* laws *)
    rec_invar_nil : forall {A : Type} {P : L A -> Set}
                      (case_nil : P ll_nil)
                      (case_cons : forall (a : A) (l : L A), P l -> P (ll_cons a l)),
        list_like_rec P case_nil case_cons ll_nil = case_nil;
    rec_invar_cons : forall {A : Type} {P : L A -> Set}
                      (case_nil : P ll_nil)
                      (case_cons : forall (a : A) (l : L A), P l -> P (ll_cons a l)),
        forall (a : A) {l : L A},
          list_like_rec P case_nil case_cons (ll_cons a l) =
          case_cons a l (list_like_rec P case_nil case_cons l);

    rect_invar_nil : forall {A : Type} {P : L A -> Type}
                       (case_nil : P ll_nil)
                       (case_cons : forall (a : A) (l : L A), P l -> P (ll_cons a l)),
        list_like_rect P case_nil case_cons ll_nil = case_nil;
    rect_invar_cons : forall {A : Type} {P : L A -> Type}
                        (case_nil : P ll_nil)
                        (case_cons : forall (a : A) (l : L A), P l -> P (ll_cons a l)),
        forall (a : A) {l : L A},
          list_like_rect P case_nil case_cons (ll_cons a l) =
          case_cons a l (list_like_rect P case_nil case_cons l);

    (* there is no need for ind_invar_nil and ind_invar_cons as equality is
     *  not defined for propositions. *)
  }.

Create HintDb listlike discriminated.
Hint Rewrite -> @rec_invar_nil @rec_invar_cons : listlike.
Hint Rewrite -> @rect_invar_nil @rect_invar_cons : listlike.

Notation Monoidal := ListLike.

Local Ltac calc := autorewrite with listlike in *; trivial. 

Section Functions.
  
  Local Notation "[]" := ll_nil.
  Local Notation "x :: xs" := (ll_cons x xs).
  
  Context {L} `{LL : ListLike L}.

  Ltac ind l := induction l using list_like_rect.

  Definition InjectivityContra {A} :=
    @list_like_rect L _ A (fun _ => Prop) False (fun _ _ _ => True).    

  Lemma injective_cons_nil : forall A (a : A) l,
      a :: l <> [].
  Proof.
    intros. intro Contra.
    assert (InjectivityContra (a :: l) = InjectivityContra []) by (rewrite Contra; trivial).
    unfold InjectivityContra in H. calc.
    rewrite <- H. trivial.
  Qed.

  Definition InjectivityCons {A} a l1 :=
    @list_like_rect L _ A (fun _ => Prop) False (fun b l2 _ => a = b /\ l1 = l2).
  
  Lemma injective_cons : forall A (a b : A) l1 l2,
      a :: l1 = b :: l2 ->
      a = b /\ l1 = l2.
  Proof.
    intros.
    assert (InjectivityCons a l1 (a :: l1) = InjectivityCons a l1 (b :: l2))
      by (rewrite H; trivial).
    unfold InjectivityCons in H0. calc.
    rewrite <- H0. auto.
  Qed.
  
  Definition map {A B} (f : A -> B) (l : L A) : L B.
  Proof.
    ind l.
    - exact [].
    - exact (f a :: IHl).
  Defined.
  
  Definition filter {A} (f : A -> bool) (l : L A) : L A.
  Proof.
    ind l.
    - exact [].
    - refine (if f a then _ else _).
      + exact (a :: IHl).
      + exact IHl.
  Defined.
  
  Definition fold_right {A B} (f : A -> B -> B) (b : B) (l : L A) : B.
  Proof.
    ind l.
    - exact b.
    - exact (f a IHl).
  Defined.

  Definition fold_left {A B} (f : B -> A -> B) (b : B) (l : L A) : B.
  Proof.
    revert b. ind l.
    - intros. exact b.
    - intros. exact (IHl (f b a)).
  Defined.

  Context {A : Type}.

  Definition app (l1 l2 : L A) : L A := fold_right ll_cons l2 l1.
  Local Notation "l1 ++ l2" := (app l1 l2).

  Definition concat (ls : L (L A)) : L A := fold_right app [] ls.

  Definition length (l : L A) : nat := fold_right (fun _ n => S n) O l.

  Definition tails (l : L A) : L (L A).
  Proof.
    ind l.
    - exact ([] :: []).
    - exact (l :: IHl).
  Defined.

  Definition nth (l : L A) (n : nat) : option A.
  Proof.
    ind l.
    - exact None.
    - destruct n.
      + exact (Some a).
      + exact IHl.
  Defined.

  Definition rev (l : L A) : L A.
  Proof.
    ind l.
    - exact [].
    - exact (IHl ++ a :: []).
  Defined.

  Lemma map_nil : forall B (f : A -> B),
      map f [] = [].
  Proof.
    intros. unfold map; calc.
  Qed.
  
  Lemma map_cons : forall B (f : A -> B) a l,
      map f (a :: l) = f a :: map f l.
  Proof.
    intros. unfold map; calc.
  Qed.

  Lemma fold_right_nil : forall B (f : A -> B -> B) (b : B),
      fold_right f b [] = b.
  Proof using.
    intros. unfold fold_right. calc.
  Qed.
  Hint Rewrite -> @fold_right_nil : listlike.

  Lemma fold_right_cons : forall B (f : A -> B -> B) (b : B) (a : A) (l : L A),
      fold_right f b (a :: l) = f a (fold_right f b l).
  Proof using.
    intros. unfold fold_right. calc.
  Qed.
  Hint Rewrite -> @fold_right_cons : listlike.

  Lemma fold_left_nil : forall B (f : B -> A -> B) (b : B),
      fold_left f b [] = b.
  Proof using.
    intros. unfold fold_left. calc.
  Qed.
  Hint Rewrite -> @fold_left_nil : listlike.

  Lemma fold_left_cons : forall B (f : B -> A -> B) (b : B) (a : A) (l : L A),
      fold_left f b (a :: l) = fold_left f (f b a) l.
  Proof using.
    intros. unfold fold_left. calc.
  Qed.
  Hint Rewrite -> @fold_left_cons : listlike.
  
  Lemma app_id_l : forall (l : L A), [] ++ l = l.
  Proof using.
    intros. unfold app. calc.
  Qed.
  Hint Rewrite -> app_id_l : listlike.
  
  Lemma app_id_r : forall (l : L A), l ++ [] = l.
  Proof using.
    intros. ind l.
    - calc.
    - unfold app. calc. f_equal.
      apply IHl.
  Qed.
  Hint Rewrite -> app_id_r : listlike.

  Lemma app_cons : forall (a : A) (l1 l2 : L A), (a :: l1) ++ l2 = a :: (l1 ++ l2).
  Proof using.
    intros. unfold app. calc.
  Qed.
  Hint Rewrite -> @app_cons : listlike.

  Lemma app_assoc : forall l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    ind l1; intros; calc.
    rewrite IHl1. trivial.
  Qed.

  Lemma app_inv : forall l1 l2, l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
  Proof.
    intros. ind l1; calc.
    - auto.
    - exfalso. revert H. apply injective_cons_nil.
  Qed.
  
  Lemma length_nil : length (@ll_nil _ _ A) = 0.
  Proof using.
    intros. unfold length. calc.
  Qed.
  Hint Rewrite -> length_nil : listlike.

  Lemma length_cons : forall (h : A) l, length (h :: l) = S (length l).
  Proof using.
    intros. unfold length. calc.
  Qed.
  Hint Rewrite -> @length_cons : listlike.
  
  Lemma app_length : forall (l1 l2 : L A),
      length (l1 ++ l2) = length l1 + length l2.
  Proof using.
    intros. ind l1; calc.
    simpl. f_equal. apply IHl1.
  Qed.
  Hint Rewrite -> app_length : listlike.
  
  Lemma rev_cons : forall a l, rev (a :: l) = rev l ++ a :: [].
  Proof.
    intros. unfold rev. calc.
  Qed.
  
  Lemma rev_app : forall l1 l2, rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros; ind l1; calc.
    - unfold rev; calc.
    - unfold rev. calc.
      lazymatch goal with
        |- ?G => change G with (rev (l ++ l2) ++ a :: [] = rev l2 ++ rev l ++ a :: [])
      end.
      rewrite IHl1. rewrite app_assoc.
      trivial.
  Qed.
  
  Lemma rev_involutive : forall l, rev (rev l) = l.
  Proof.
    intros; ind l.
    - unfold rev; calc.
    - replace (a :: l) with ((a :: []) ++ l) by calc.
      do 2 rewrite rev_app. rewrite IHl.
      f_equal. unfold rev; calc.
  Qed.
  
End Functions.

Module Notations.
  
  Notation "[]" := ll_nil.
  Notation "x :: xs" := (ll_cons x xs) (at level 60, right associativity).
  Notation "l1 ++ l2" := (app l1 l2) (at level 60, right associativity).
  Notation "[ x .. z ]" := (ll_cons x .. (ll_cons z ll_nil) .. ).
  
End Notations.

Module Automations.

  Ltac ind l := induction l using list_like_ind || induction l using list_like_rect.
  Ltac list_inv :=
    repeat match goal with
           | H : ll_cons _ _ = ll_nil |- _ => exfalso; revert H; apply injective_cons_nil
           | H : ll_nil = ll_cons _ _ |- _ => symmetry in H
           | H : ll_cons _ _ = ll_cons _ _ |- _ =>
             apply injective_cons in H; destruct H as [? ?]; subst
           end.
  
  Hint Rewrite -> @fold_right_nil : listlike.
  Hint Rewrite -> @fold_right_cons : listlike.
  Hint Rewrite -> @app_id_l : listlike.
  Hint Rewrite -> @app_id_r : listlike.
  Hint Rewrite -> @app_cons : listlike.
  Hint Rewrite -> @length_nil @length_cons : listlike.
  Hint Rewrite -> @app_length : listlike.
  Hint Rewrite -> @map_nil @map_cons : listlike.
  Hint Rewrite -> @fold_left_nil @fold_left_cons : listlike.
  
End Automations.
  
Section Predicates.
  Import Notations.
  Import Automations.
  
  Context {L} `{LL : ListLike L}.
  Context {A : Type}.
  
  Inductive All (P : A -> Prop) : L A -> Prop :=
  | All_nil : All P []
  | All_cons : forall {x xs}, P x -> All P xs -> All P (x :: xs).

  Inductive Any (P : A -> Prop) : L A -> Prop :=
  | Any_found : forall {h tl}, P h -> Any P (h :: tl)
  | Any_prep : forall {h tl}, Any P tl -> Any P (h :: tl).

  Inductive AllTails (P : A -> L A -> Prop) : L A -> Prop :=
  | AT_nil : AllTails P []
  | AT_cons : forall {x xs}, P x xs -> AllTails P xs -> AllTails P (x :: xs).
  
  Definition In x := Any (fun y => x = y).
  Definition Uniq := AllTails (fun x xs => ~ (In x xs)).

  Lemma All_map_iff : forall P l f,
      All P (map f l) <-> All (fun x => P (f x)) l.
  Proof.
    intros. split.
    - intros. ind l; calc.
      + constructor.
      + inversion H; list_inv.
        subst. constructor; auto.

    - induction 1; calc.
      + constructor.
      + constructor; auto.
  Qed.

  Lemma All_forall_iff : forall P l, All P l <-> (forall x, In x l -> P x).
  Proof.
    intros; split.
    - induction 1; intros; unfold In in *.
      + inversion H; list_inv.
      + inversion H1; list_inv; auto.

    - ind l; intros.
      + constructor.
      + constructor.
        * apply H. constructor. trivial.
        * apply IHl. intros. apply H.
          apply Any_prep. apply H0.
  Qed.

  Lemma Any_map_iff : forall P l f,
      Any P (map f l) <-> Any (fun x => P (f x)) l.
  Proof.
    intros. split.
    - ind l; intros; calc.
      + inversion H; list_inv.
      + inversion H; list_inv.
        constructor; auto.
        apply Any_prep. intuition.
        
    - induction 1; calc.
      + constructor; trivial.
      + apply Any_prep. trivial.
  Qed.

  Lemma Any_exist_iff : forall P l,
      Any P l <-> exists x, In x l /\ P x.
  Proof.
    intros; split.
    - induction 1.
      + exists h. split; trivial.
        apply Any_found. trivial.
      + destruct IHAny. destruct_conjs. exists x.
        split; trivial.
        apply Any_prep; trivial.

    - intros. destruct H. destruct_conjs.
      ind l; unfold In in *.
      + inversion H; list_inv.
      + inversion H; list_inv.
        * constructor; trivial.
        * apply Any_prep. auto.
  Qed.

  Lemma Any_app_iff : forall P l1 l2,
      Any P (l1 ++ l2) <-> Any P l1 \/ Any P l2.
  Proof.
    intros; split.
    - ind l1; intros; calc.
      + auto.
      + inversion H; list_inv.
        * left; constructor. trivial.
        * destruct IHl1; trivial.
          -- left; apply Any_prep; trivial.
          -- auto.

    - intros. ind l1.
      + destruct H.
        * inversion H; list_inv.
        * calc.
      + destruct H; calc.
        * inversion H; list_inv.
          -- constructor; trivial.
          -- apply Any_prep; firstorder.
        * apply Any_prep. firstorder.
  Qed.       
          
End Predicates.

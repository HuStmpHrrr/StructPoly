Require Import Coq.Program.Tactics.
Require Import PeanoNat.

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

Class MonoList L : Type :=
  {
    elem : Type;
    
    (* constructors *)
    ml_nil : L;
    ml_cons : elem -> L -> L;

    (* eliminators *)
    mono_list_rec :
      forall (P : L -> Set),
        P ml_nil -> (forall (a : elem) (l : L), P l -> P (ml_cons a l)) -> forall l : L, P l;
    mono_list_rect :
      forall (P : L -> Type),
        P ml_nil -> (forall (a : elem) (l : L), P l -> P (ml_cons a l)) -> forall l : L, P l;
    mono_list_ind :
      forall (P : L -> Prop),
        P ml_nil -> (forall (a : elem) (l : L), P l -> P (ml_cons a l)) -> forall l : L, P l;

    (* laws *)
    ml_rec_invar_nil : forall {P : L -> Set}
                         (case_nil : P ml_nil)
                         (case_cons : forall (a : elem) (l : L), P l -> P (ml_cons a l)),
        mono_list_rec P case_nil case_cons ml_nil = case_nil;
    ml_rec_invar_cons : forall {P : L -> Set}
                          (case_nil : P ml_nil)
                          (case_cons : forall (a : elem) (l : L), P l -> P (ml_cons a l)),
        forall (a : elem) {l : L},
          mono_list_rec P case_nil case_cons (ml_cons a l) =
          case_cons a l (mono_list_rec P case_nil case_cons l);

    ml_rect_invar_nil : forall {P : L -> Type}
                          (case_nil : P ml_nil)
                          (case_cons : forall (a : elem) (l : L), P l -> P (ml_cons a l)),
        mono_list_rect P case_nil case_cons ml_nil = case_nil;
    ml_rect_invar_cons : forall {P : L -> Type}
                           (case_nil : P ml_nil)
                           (case_cons : forall (a : elem) (l : L), P l -> P (ml_cons a l)),
        forall (a : elem) {l : L},
          mono_list_rect P case_nil case_cons (ml_cons a l) =
          case_cons a l (mono_list_rect P case_nil case_cons l);    
  }.

Hint Rewrite -> @ml_rec_invar_nil @ml_rec_invar_cons : listlike.
Hint Rewrite -> @ml_rect_invar_nil @ml_rect_invar_cons : listlike.

Instance MonoIsList {L} {A} `(isList : ListLike L) : MonoList (L A) :=
  {
    elem := A;
    ml_nil := ll_nil;
    ml_cons := ll_cons;

    mono_list_rec := list_like_rec;
    mono_list_rect := list_like_rect;
    mono_list_ind := list_like_ind
  }.
Proof.
  all:intros.
  - apply rec_invar_nil.
  - apply rec_invar_cons.
  - apply rect_invar_nil.
  - apply rect_invar_cons.
Defined.

Section Injectivity.
  Local Notation "[]" := ml_nil.
  Local Notation "x :: xs" := (ml_cons x xs).
  
  Context {L} `{ML : MonoList L}.

  Definition InjectivityContra :=
    @mono_list_rect L _ (fun _ => Prop) False (fun _ _ _ => True).    

  Lemma injective_cons_nil : forall (a : elem) l,
      a :: l <> [].
  Proof.
    intros. intro Contra.
    assert (InjectivityContra (a :: l) = InjectivityContra []) by (rewrite Contra; trivial).
    unfold InjectivityContra in H. calc.
    rewrite <- H. trivial.
  Qed.

  Definition InjectivityCons a l1 :=
    @mono_list_rect L _ (fun _ => Prop) False (fun b l2 _ => a = b /\ l1 = l2).
  
  Lemma injective_cons : forall (a b : elem) l1 l2,
      a :: l1 = b :: l2 ->
      a = b /\ l1 = l2.
  Proof.
    intros.
    assert (InjectivityCons a l1 (a :: l1) = InjectivityCons a l1 (b :: l2))
      by (rewrite H; trivial).
    unfold InjectivityCons in H0. calc.
    rewrite <- H0. auto.
  Qed.

End Injectivity.

Section MonoFunctions.

  Local Notation "[]" := ml_nil.
  Local Notation "x :: xs" := (ml_cons x xs).
  
  Context {L} `{ML : MonoList L}.

  Ltac ind l := induction l using mono_list_rect.

  Definition fold_right {B} (f : elem -> B -> B) (b : B) (l : L) : B.
  Proof.
    ind l.
    - exact b.
    - exact (f a IHl).
  Defined.

  Definition fold_left {B} (f : B -> elem -> B) (b : B) (l : L) : B.
  Proof.
    revert b. ind l.
    - intros. exact b.
    - intros. exact (IHl (f b a)).
  Defined.

  Definition app (l1 l2 : L) : L := fold_right ml_cons l2 l1.
  Local Notation "l1 ++ l2" := (app l1 l2).

  Definition length (l : L) : nat := fold_right (fun _ n => S n) O l.

  Definition nth (l : L) (n : nat) : option elem.
  Proof.
    ind l.
    - exact None.
    - destruct n.
      + exact (Some a).
      + exact IHl.
  Defined.

  Definition rev (l : L) : L.
  Proof.
    ind l.
    - exact [].
    - exact (IHl ++ a :: []).
  Defined.
  
  Lemma fold_right_nil : forall B (f : elem -> B -> B) (b : B),
      fold_right f b [] = b.
  Proof using.
    intros. unfold fold_right. calc.
  Qed.
  Hint Rewrite -> @fold_right_nil : listlike.

  Lemma fold_right_cons : forall B (f : elem -> B -> B) (b : B) (a : elem) (l : L),
      fold_right f b (a :: l) = f a (fold_right f b l).
  Proof using.
    intros. unfold fold_right. calc.
  Qed.
  Hint Rewrite -> @fold_right_cons : listlike.

  Lemma fold_left_nil : forall B (f : B -> elem -> B) (b : B),
      fold_left f b [] = b.
  Proof using.
    intros. unfold fold_left. calc.
  Qed.
  Hint Rewrite -> @fold_left_nil : listlike.

  Lemma fold_left_cons : forall B (f : B -> elem -> B) (b : B) (a : elem) (l : L),
      fold_left f b (a :: l) = fold_left f (f b a) l.
  Proof using.
    intros. unfold fold_left. calc.
  Qed.
  Hint Rewrite -> @fold_left_cons : listlike.
  
  Lemma app_nil_l : forall (l : L), [] ++ l = l.
  Proof using.
    intros. unfold app. calc.
  Qed.
  Hint Rewrite -> app_nil_l : listlike.
  
  Lemma app_nil_r : forall (l : L), l ++ [] = l.
  Proof using.
    intros. ind l.
    - calc.
    - unfold app. calc. f_equal.
      apply IHl.
  Qed.
  Hint Rewrite -> app_nil_r : listlike.

  Lemma app_cons : forall (a : elem) (l1 l2 : L), (a :: l1) ++ l2 = a :: (l1 ++ l2).
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
  
  Lemma length_nil : length (@ml_nil _ _) = 0.
  Proof using.
    intros. unfold length. calc.
  Qed.
  Hint Rewrite -> length_nil : listlike.

  Lemma length_cons : forall (h : elem) l, length (h :: l) = S (length l).
  Proof using.
    intros. unfold length. calc.
  Qed.
  Hint Rewrite -> @length_cons : listlike.
  
  Lemma app_length : forall (l1 l2 : L),
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

  Lemma rev_length : forall l, length (rev l) = length l.
  Proof.
    intros; ind l; unfold rev; calc.
    rewrite Nat.add_comm. simpl. f_equal.
    rewrite <- IHl. reflexivity.
  Qed.      

End MonoFunctions.

Module TermNotations.

  Notation "[]" := ml_nil : ll_scope.
  Notation "x :: xs" := (ml_cons x xs) (at level 60, right associativity) : ll_scope.
  Notation "l1 ++ l2" := (app l1 l2) (at level 60, right associativity) : ll_scope.
  Notation "[ x .. z ]" := (ml_cons x .. (ml_cons z ml_nil) .. ) : ll_scope.

  Open Scope ll_scope.
  
End TermNotations.

Module BasicAutomations.

  Ltac ind l :=
    induction l using mono_list_ind || induction l using mono_list_rect.

  Ltac fold_ll :=
    repeat match goal with
           | H : context[ll_cons ?x ?xs] |- _ =>
             change (ll_cons x xs) with (ml_cons x xs) in H
           | |- context[ll_cons ?x ?xs] =>
             change (ll_cons x xs) with (ml_cons x xs)
           | H : context [@ll_nil ?L _ ?A] |- _ =>
             change (@ll_nil L _ A) with (@ml_nil (L A) _) in H
           | |- context [@ll_nil ?L _ ?A] =>
             change (@ll_nil L _ A) with (@ml_nil (L A) _)
           end.
  
  Ltac list_inv :=
    repeat (fold_ll;
            match goal with
            | H : ml_cons _ _ = ml_nil |- _ =>
              exfalso; eapply injective_cons_nil; apply H
            | H : ml_nil = ml_cons _ _ |- _ => symmetry in H
            | H : ml_cons _ _ = ml_cons _ _ |- _ =>
              apply injective_cons in H; destruct H as [? ?]
            end); subst.
  
  Hint Rewrite -> @fold_right_nil : listlike.
  Hint Rewrite -> @fold_right_cons : listlike.
  Hint Rewrite -> @app_nil_l : listlike.
  Hint Rewrite -> @app_nil_r : listlike.
  Hint Rewrite -> @app_cons : listlike.
  Hint Rewrite -> @length_nil @length_cons : listlike.
  Hint Rewrite -> @app_length : listlike.
  Hint Rewrite -> @fold_left_nil @fold_left_cons : listlike.
  
End BasicAutomations.

Section MonoPredicates.
  Import TermNotations.
  Import BasicAutomations.
    
  Context {L} `{ML : MonoList L}.
  
  Inductive All (P : elem -> Prop) : L -> Prop :=
  | All_nil : All P ml_nil
  | All_cons : forall {x xs}, P x -> All P xs -> All P (x :: xs).
  
  Inductive Any (P : elem -> Prop) : L -> Prop :=
  | Any_found : forall {h tl}, P h -> Any P (h :: tl)
  | Any_prep : forall {h tl}, Any P tl -> Any P (h :: tl).

  Inductive AllTails (P : elem -> L -> Prop) : L -> Prop :=
  | AT_nil : AllTails P []
  | AT_cons : forall {x xs}, P x xs -> AllTails P xs -> AllTails P (x :: xs).

  Hint Constructors All Any AllTails.
  
  Definition In x := Any (fun y => x = y).
  Definition Uniq := AllTails (fun x xs => ~ (In x xs)).

  Hint Transparent In Uniq.

  Lemma All_forall_iff : forall P l, All P l <-> (forall x, In x l -> P x).
  Proof.
    intros; split.
    - induction 1; intros; unfold In in *.
      + inversion H; list_inv.
      + inversion H1; list_inv; auto.

    - ind l; intros; auto.
      constructor.
      + apply H. constructor. trivial.
      + apply IHl. intros. apply H.
        apply Any_prep. apply H0.
  Qed.

  Lemma All_app_iff : forall P l1 l2,
      All P (l1 ++ l2) <-> All P l1 /\ All P l2.
  Proof.
    intros; split.
    - ind l1; intros; calc.
      + auto.
      + inversion H; list_inv.
        destruct IHl1; auto.

    - intros; destruct_conjs. ind l1; calc.
      inversion H; list_inv.
      auto.
  Qed.

  Lemma Any_exist_iff : forall P l,
      Any P l <-> exists x, In x l /\ P x.
  Proof.
    intros; split.
    - induction 1.
      + exists h. split; auto.
        apply Any_found. trivial.
      + destruct IHAny. destruct_conjs. exists x.
        split; trivial. 
        apply Any_prep; trivial.

    - intros. destruct H. destruct_conjs.
      ind l; unfold In in *.
      + inversion H; list_inv.
      + inversion H; list_inv; auto.
  Qed.

  Lemma Any_app_iff : forall P l1 l2,
      Any P (l1 ++ l2) <-> Any P l1 \/ Any P l2.
  Proof.
    intros; split.
    - ind l1; intros; calc.
      + auto.
      + inversion H; list_inv.
        * left; auto. 
        * destruct IHl1; auto.

    - intros. ind l1.
      + destruct H.
        * inversion H; list_inv.
        * calc.
      + destruct H; calc; auto.
        inversion H; list_inv; auto.
  Qed.

  Definition In_dec : (forall (x y : elem), {x = y} + {x <> y}) ->
                      forall x l, {In x l} + {~In x l}.
  Proof.
    intro Eqdec. intros.
    ind l.
    - right. intro Contra. inversion Contra; list_inv.
    - destruct (Eqdec x a).
      + subst. left. constructor; auto.
      + destruct IHl.
        * left. apply Any_prep; trivial.
        * right. intro Contra.
          inversion Contra; list_inv.
          congruence.
          intuition.
  Defined.
  
End MonoPredicates.

Section Functions.
  Import TermNotations.
  Import BasicAutomations.
  
  Context {L} `{LL : ListLike L}.
  
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

  Context {A : Type}.
  
  Definition concat (ls : L (L A)) : L A.
  Proof.
    refine (fold_right _ [] ls).
    simpl. apply app.
  Defined.
  
  Definition tails (l : L A) : L (L A).
  Proof.
    ind l.
    - refine (_ :: []). simpl. exact [].
    - exact (l :: IHl).
  Defined.
  
  Lemma map_nil : forall B (f : A -> B),
      map f [] = [].
  Proof.
    intros. unfold map; calc.
  Qed.
  
  Lemma map_cons : forall B (f : A -> B) a l,
      map f (a :: l) = f a :: map f l.
  Proof.
    intros. unfold map; simpl; calc.
  Qed.
  
End Functions.

Module MoreAutomations.

  Hint Rewrite -> @map_nil @map_cons : listlike.

End MoreAutomations.

Section Predicates.
  Import TermNotations.
  Import BasicAutomations.
  Import MoreAutomations.
  
  Context {L} `{LL : ListLike L}.

  Hint Constructors All Any.
  
  Lemma All_map_iff : forall A B P l (f : A -> B),
    All P (map f l) <-> All (fun x => P (f x)) l.
  Proof.
    intros. split.
    - intros. ind l; calc.
      inversion H; list_inv.
      auto.

    - induction 1; calc. auto.
  Qed.

  Lemma Any_map_iff : forall A B P l (f : A -> B),
      Any P (map f l) <-> Any (fun x => P (f x)) l.
  Proof.
    intros. split.
    - ind l; intros; calc.
      + inversion H; list_inv.
      + inversion H; list_inv; auto.
        
    - induction 1; calc; auto.
  Qed.

End Predicates.
Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Pointed.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.
Require Crypto.Util.Option.
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.Tactics.BreakMatch.
Require Export Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Crypto.Util.Tactics.SplitInContext.
Import ListNotations.
Local Open Scope list_scope.

Scheme Equality for list.

Definition list_case
           {A} (P : list A -> Type) (N : P nil) (C : forall x xs, P (cons x xs))
           (ls : list A)
  : P ls
  := match ls return P ls with
     | nil => N
     | cons x xs => C x xs
     end.

Definition list_case_nodep
           {A} (P : Type) (N : P) (C : A -> list A -> P)
           (ls : list A)
  : P
  := match ls with
     | nil => N
     | cons x xs => C x xs
     end.


Global Instance list_rect_Proper_dep_gen {A P} (RP : forall x : list A, P x -> P x -> Prop)
  : Proper (RP nil ==> forall_relation (fun x => forall_relation (fun xs => RP xs ==> RP (cons x xs))) ==> forall_relation RP) (@list_rect A P) | 10.
Proof.
  cbv [forall_relation respectful]; intros N N' HN C C' HC ls.
  induction ls as [|l ls IHls]; cbn [list_rect];
    repeat first [ apply IHls | apply HC | apply HN | progress intros | reflexivity ].
Qed.
Global Instance list_rect_Proper_dep {A P} : Proper (eq ==> forall_relation (fun _ => forall_relation (fun _ => forall_relation (fun _ => eq))) ==> forall_relation (fun _ => eq)) (@list_rect A P) | 1.
Proof.
  cbv [forall_relation respectful Proper]; intros; eapply (@list_rect_Proper_dep_gen A P (fun _ => eq)); cbv [forall_relation respectful]; intros; subst; eauto.
Qed.
Global Instance list_rect_arrow_Proper_dep {A P Q} : Proper ((eq ==> eq) ==> forall_relation (fun _ => forall_relation (fun _ => (eq ==> eq) ==> (eq ==> eq))) ==> forall_relation (fun _ => eq ==> eq)) (@list_rect A (fun x => P x -> Q x)) | 10.
Proof.
  cbv [forall_relation respectful Proper]; intros; eapply (@list_rect_Proper_dep_gen A (fun x => P x -> Q x) (fun _ => eq ==> eq)%signature); intros; subst; eauto.
Qed.
Global Instance list_case_Proper_dep {A P} : Proper (eq ==> forall_relation (fun _ => forall_relation (fun _ => eq)) ==> forall_relation (fun _ => eq)) (@list_case A P) | 1.
Proof.
  cbv [forall_relation]; intros N N' ? C C' HC ls; subst N'; revert N; destruct ls; eauto.
Qed.
Global Instance list_rect_Proper_gen {A P} R
  : Proper (R ==> (eq ==> eq ==> R ==> R) ==> eq ==> R) (@list_rect A (fun _ => P)) | 10.
Proof. repeat intro; subst; apply (@list_rect_Proper_dep_gen A (fun _ => P) (fun _ => R)); cbv [forall_relation respectful] in *; eauto. Qed.
Global Instance list_rect_Proper {A P} : Proper (eq ==> pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq)) ==> eq ==> eq) (@list_rect A (fun _ => P)).
Proof. repeat intro; subst; apply (@list_rect_Proper_dep A (fun _ => P)); eauto. Qed.
Global Instance list_rect_arrow_Proper {A P Q}
  : Proper ((eq ==> eq) ==> (eq ==> eq ==> (eq ==> eq) ==> eq ==> eq) ==> eq ==> eq ==> eq)
           (@list_rect A (fun _ => P -> Q)) | 10.
Proof. eapply list_rect_Proper_gen. Qed.
Global Instance list_case_Proper {A P} : Proper (eq ==> pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq) (@list_case A (fun _ => P)).
Proof. repeat intro; subst; apply (@list_case_Proper_dep A (fun _ => P)); eauto. Qed.

Create HintDb distr_length discriminated.
Create HintDb simpl_set_nth discriminated.
Create HintDb simpl_update_nth discriminated.
Create HintDb simpl_nth_default discriminated.
Create HintDb simpl_nth_error discriminated.
Create HintDb simpl_firstn discriminated.
Create HintDb simpl_skipn discriminated.
Create HintDb simpl_fold_right discriminated.
Create HintDb simpl_fold_left discriminated.
Create HintDb simpl_sum_firstn discriminated.
Create HintDb push_map discriminated.
Create HintDb push_combine discriminated.
Create HintDb push_flat_map discriminated.
Create HintDb push_rev discriminated.
Create HintDb push_fold_right discriminated.
Create HintDb push_fold_left discriminated.
Create HintDb push_partition discriminated.
Create HintDb pull_nth_error discriminated.
Create HintDb push_nth_error discriminated.
Create HintDb pull_nth_default discriminated.
Create HintDb push_nth_default discriminated.
Create HintDb pull_firstn discriminated.
Create HintDb push_firstn discriminated.
Create HintDb pull_skipn discriminated.
Create HintDb push_skipn discriminated.
Create HintDb push_sum discriminated.
Create HintDb pull_update_nth discriminated.
Create HintDb push_update_nth discriminated.
Create HintDb znonzero discriminated.

#[global]
Hint Rewrite
  @app_length
  @rev_length
  @map_length
  @seq_length
  @fold_left_length
  @split_length_l
  @split_length_r
  @firstn_length
  @combine_length
  @prod_length
  : distr_length.

#[global]
Hint Rewrite
     rev_involutive
  : push_rev.

Global Hint Extern 1 => progress autorewrite with distr_length in * : distr_length.
Ltac distr_length := autorewrite with distr_length in *;
  try solve [simpl in *; intros; (idtac + exfalso); lia].

Module Export List.
  Local Set Implicit Arguments.
  Import ListNotations.
  (** From the 8.6 Standard Library *)

  Section Elts.
    Variable A : Type.

    (** Results about [nth_error] *)

    Lemma nth_error_In l n (x : A) : nth_error l n = Some x -> In x l.
    Proof using Type.
      revert n. induction l as [|a l IH]; intros [|n]; simpl; try easy.
      - injection 1; auto.
      - eauto.
    Qed.
  End Elts.

  Section Map.
    Variables (A : Type) (B : Type).
    Variable f : A -> B.

    Lemma map_nil : forall A B (f : A -> B), map f nil = nil.
    Proof using Type. reflexivity. Qed.
    Lemma map_cons (x:A)(l:list A) : map f (x::l) = (f x) :: (map f l).
    Proof using Type.
      reflexivity.
    Qed.
    Lemma map_repeat x n : map f (List.repeat x n) = List.repeat (f x) n.
    Proof using Type. induction n; simpl List.repeat; simpl map; congruence. Qed.
  End Map.
#[global]
  Hint Rewrite @map_cons @map_nil @map_repeat : push_map.
#[global]
  Hint Rewrite @map_app : push_map.

  Section FlatMap.
    Lemma flat_map_nil {A B} (f:A->list B) : List.flat_map f (@nil A) = nil.
    Proof. reflexivity. Qed.
    Lemma flat_map_cons {A B} (f:A->list B) x xs :
      (List.flat_map f (x::xs) = (f x++List.flat_map f xs))%list.
    Proof. reflexivity. Qed.
  End FlatMap.
#[global]
  Hint Rewrite @flat_map_cons @flat_map_nil : push_flat_map.

  Lemma rev_cons {A} x ls : @rev A (x :: ls) = rev ls ++ [x]. Proof. reflexivity. Qed.
#[global]
  Hint Rewrite @rev_cons : list.

  Section FoldRight.
    Context {A B} (f:B->A->A).
    Lemma fold_right_nil : forall {A B} (f:B->A->A) a,
        List.fold_right f a nil = a.
    Proof using Type. reflexivity. Qed.
    Lemma fold_right_cons : forall a b bs,
      fold_right f a (b::bs) = f b (fold_right f a bs).
    Proof using Type. reflexivity. Qed.
    Lemma fold_right_snoc a x ls:
      @fold_right A B f a (ls ++ [x]) = fold_right f (f x a) ls.
    Proof using Type.
      rewrite <-(rev_involutive ls), <-rev_cons.
      rewrite !fold_left_rev_right; reflexivity.
    Qed.
  End FoldRight.
#[global]
  Hint Rewrite @fold_right_nil @fold_right_cons @fold_right_snoc : simpl_fold_right push_fold_right.

  Section Partition.
    Lemma partition_nil {A} (f:A->_) : partition f nil = (nil, nil).
    Proof. reflexivity.                                         Qed.
    Lemma partition_cons {A} (f:A->_) x xs : partition f (x::xs) =
                                             if f x
                                             then (x :: (fst (partition f xs)), (snd (partition f xs)))
                                             else ((fst (partition f xs)), x :: (snd (partition f xs))).
    Proof. cbv [partition]; break_match; reflexivity.           Qed.
  End Partition.
#[global]
  Hint Rewrite @partition_nil @partition_cons : push_partition.

  Lemma in_seq len start n :
    In n (seq start len) <-> start <= n < start+len.
  Proof.
   revert start. induction len as [|len IHlen]; simpl; intros.
   - rewrite <- plus_n_O. split;[easy|].
     intros (H,H'). apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H H')).
   - rewrite IHlen, <- plus_n_Sm; simpl; split.
     * intros [H|H]; subst; intuition auto with arith.
     * intros (H,H'). destruct (Lt.le_lt_or_eq _ _ H); intuition.
  Qed.

  Section Facts.

    Variable A : Type.

    Theorem length_zero_iff_nil (l : list A):
      length l = 0 <-> l=[].
    Proof using Type.
      split; [now destruct l | now intros ->].
    Qed.
  End Facts.

  Section Cutting.

    Variable A : Type.

    Local Notation firstn := (@firstn A).

    Lemma firstn_nil n: firstn n [] = [].
    Proof using Type. induction n; now simpl. Qed.

    Lemma firstn_cons n a l: firstn (S n) (a::l) = a :: (firstn n l).
    Proof using Type. now simpl. Qed.

    Lemma firstn_all l: firstn (length l) l = l.
    Proof using Type. induction l as [| ? ? H]; simpl; [reflexivity | now rewrite H]. Qed.

    Lemma firstn_all2 n: forall (l:list A), (length l) <= n -> firstn n l = l.
    Proof using Type. induction n as [|k iHk].
           - intro l. inversion 1 as [H1|?].
             rewrite (length_zero_iff_nil l) in H1. subst. now simpl.
           - destruct l as [|x xs]; simpl.
             * now reflexivity.
             * simpl. intro H. apply Peano.le_S_n in H. f_equal. apply iHk, H.
    Qed.

    Lemma firstn_O l: firstn 0 l = [].
    Proof using Type. now simpl. Qed.

    Lemma firstn_le_length n: forall l:list A, length (firstn n l) <= n.
    Proof using Type.
      induction n as [|k iHk]; simpl; [auto | destruct l as [|x xs]; simpl].
      - auto with arith.
      - apply le_n_S, iHk.
    Qed.

    Lemma firstn_length_le: forall l:list A, forall n:nat,
          n <= length l -> length (firstn n l) = n.
    Proof using Type. induction l as [|x xs Hrec].
           - simpl. intros n H. apply le_n_0_eq in H. rewrite <- H. now simpl.
           - destruct n as [|n].
             * now simpl.
             * simpl. intro H. apply le_S_n in H. now rewrite (Hrec n H).
    Qed.

    Lemma firstn_app n:
      forall l1 l2,
        firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2).
    Proof using Type. induction n as [|k iHk]; intros l1 l2.
           - now simpl.
           - destruct l1 as [|x xs].
             * unfold List.firstn at 2, length. now rewrite 2!app_nil_l, <- minus_n_O.
             * rewrite <- app_comm_cons. simpl. f_equal. apply iHk.
    Qed.

    Lemma firstn_app_2 n:
      forall l1 l2,
        firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2.
    Proof using Type. induction n as [| k iHk];intros l1 l2.
           - unfold List.firstn at 2. rewrite <- plus_n_O, app_nil_r.
             rewrite firstn_app. rewrite <- minus_diag_reverse.
             unfold List.firstn at 2. rewrite app_nil_r. apply firstn_all.
           - destruct l2 as [|x xs].
             * simpl. rewrite app_nil_r. apply firstn_all2. auto with arith.
             * rewrite firstn_app. assert (H0 : (length l1 + S k - length l1) = S k).
               auto with arith.
               rewrite H0, firstn_all2; [reflexivity | auto with arith].
    Qed.

    Lemma firstn_firstn:
      forall l:list A,
      forall i j : nat,
        firstn i (firstn j l) = firstn (min i j) l.
    Proof using Type. induction l as [|x xs Hl].
           - intros. simpl. now rewrite ?firstn_nil.
           - destruct i.
             * intro. now simpl.
             * destruct j.
             + now simpl.
             + simpl. f_equal. apply Hl.
    Qed.

  End Cutting.

  Lemma fold_right_rev_left A B (f : B -> A -> B) (l : list A) (i : B)
    : fold_left f (rev l) i = fold_right (fun x y => f y x) i l.
  Proof.
    now rewrite <- fold_left_rev_right, rev_involutive.
  Qed.


  Section FoldLeft.
    Context {A B} (f:A->B->A).
    Lemma fold_left_nil : forall {A B} (f:A->B->A) a,
        List.fold_left f nil a = a.
    Proof using Type. reflexivity. Qed.
    Lemma fold_left_cons : forall a b bs,
      fold_left f (b::bs) a = fold_left f bs (f a b).
    Proof using Type. reflexivity. Qed.
    Lemma fold_left_snoc a x ls:
      @fold_left A B f (ls ++ [x]) a = f (fold_left f ls a) x.
    Proof using Type.
      rewrite <-(rev_involutive ls), <-rev_cons.
      rewrite !fold_right_rev_left; reflexivity.
    Qed.
  End FoldLeft.
#[global]
  Hint Rewrite @fold_left_nil @fold_left_cons @fold_left_snoc : simpl_fold_left push_fold_left.

  (** new operations *)
  Definition enumerate {A} (ls : list A) : list (nat * A)
    := combine (seq 0 (length ls)) ls.
End List.

#[global]
Hint Rewrite @firstn_skipn : simpl_firstn.
#[global]
Hint Rewrite @firstn_skipn : simpl_skipn.
#[global]
Hint Rewrite @firstn_nil @firstn_cons @List.firstn_all @firstn_O @firstn_app_2 @List.firstn_firstn : push_firstn.
#[global]
Hint Rewrite @firstn_nil @firstn_cons @List.firstn_all @firstn_O @firstn_app_2 @List.firstn_firstn : simpl_firstn.
#[global]
Hint Rewrite @firstn_app : push_firstn.
#[global]
Hint Rewrite <- @firstn_cons @firstn_app @List.firstn_firstn : pull_firstn.
#[global]
Hint Rewrite @firstn_all2 @removelast_firstn @firstn_removelast using lia : push_firstn.
#[global]
Hint Rewrite @firstn_all2 @removelast_firstn @firstn_removelast using lia : simpl_firstn.

Local Arguments value / _ _.
Local Arguments error / _.

Definition list_beq_hetero {A B} (f : A -> B -> bool)
  := fix list_beq_hetero (l1 : list A) (l2 : list B) : bool
       := match l1, l2 with
          | [], [] => true
          | [], _ | _, [] => false
          | x :: xs, y :: ys => f x y && list_beq_hetero xs ys
          end%bool.

Definition sum_firstn l n := fold_right Z.add 0%Z (firstn n l).

Definition sum xs := sum_firstn xs (length xs).

Section map2.
  Context {A B C}
          (f : A -> B -> C).

  Fixpoint map2 (la : list A) (lb : list B) : list C :=
    match la, lb with
    | nil, _ => nil
    | _, nil => nil
    | a :: la', b :: lb'
      => f a b :: map2 la' lb'
    end.
End map2.

(* xs[n] := f xs[n] *)
Fixpoint update_nth {T} n f (xs:list T) {struct n} :=
        match n with
        | O => match xs with
                                 | nil => nil
                                 | x'::xs' => f x'::xs'
                                 end
        | S n' =>  match xs with
                                 | nil => nil
                                 | x'::xs' => x'::update_nth n' f xs'
                                 end
  end.

(* xs[n] := x *)
Definition set_nth {T} n x (xs:list T)
  := update_nth n (fun _ => x) xs.

Definition splice_nth {T} n (x:T) xs := firstn n xs ++ x :: skipn (S n) xs.
#[global]
Hint Unfold splice_nth : core.

Fixpoint take_while {T} (f : T -> bool) (ls : list T) : list T
  := match ls with
     | nil => nil
     | cons x xs => if f x then x :: @take_while T f xs else nil
     end.

Fixpoint drop_while {T} (f : T -> bool) (ls : list T) : list T
  := match ls with
     | nil => nil
     | cons x xs => if f x then @drop_while T f xs else x :: xs
     end.
Ltac boring :=
  simpl; intuition auto with zarith datatypes;
  repeat match goal with
           | [ H : _ |- _ ] => rewrite H; clear H
           | [ |- context[match ?pf with end] ] => solve [ case pf ]
           | _ => progress autounfold in *
           | _ => progress autorewrite with core
           | _ => progress simpl in *
           | _ => progress intuition auto with zarith datatypes
         end; eauto.

Ltac boring_list :=
  repeat match goal with
         | _ => progress boring
         | _ => progress autorewrite with distr_length simpl_nth_default simpl_update_nth simpl_set_nth simpl_nth_error in *
         end.

Section Relations.
  Fixpoint list_eq {A B} eq (x : list A) (y : list B) :=
    match x, y with
    | [], [] => True
    | [], _ | _, [] => False
    | x :: xs, y :: ys => eq x y /\ list_eq eq xs ys
    end.

  Local Ltac t :=
    repeat first [ progress cbn in *
                 | progress break_match
                 | intro
                 | intuition congruence
                 | progress destruct_head'_and
                 | solve [ apply reflexivity
                         | apply symmetry; eassumption
                         | eapply transitivity; eassumption
                         | eauto ] ].

  Fixpoint list_eq_refl {T} {R} {Reflexive_R:@Reflexive T R} (ls : list T) : list_eq R ls ls.
  Proof. destruct ls; cbn; repeat split; auto. Defined.
  Global Instance Reflexive_list_eq {T} {R} {Reflexive_R:@Reflexive T R}
    : Reflexive (list_eq R) | 1
    := list_eq_refl.

  Lemma list_eq_sym {A B} {R1 R2 : _ -> _ -> Prop} (HR : forall v1 v2, R1 v1 v2 -> R2 v2 v1)
    : forall v1 v2, @list_eq A B R1 v1 v2 -> list_eq R2 v2 v1.
  Proof. induction v1; t. Qed.

  Lemma list_eq_trans {A B C} {R1 R2 R3 : _ -> _ -> Prop}
        (HR : forall v1 v2 v3, R1 v1 v2 -> R2 v2 v3 -> R3 v1 v3)
    : forall v1 v2 v3, @list_eq A B R1 v1 v2 -> @list_eq B C R2 v2 v3 -> @list_eq A C R3 v1 v3.
  Proof. induction v1; t. Qed.

  Global Instance Transitive_list_eq {T} {R} {Transitive_R:@Transitive T R}
    : Transitive (list_eq R) | 1 := list_eq_trans Transitive_R.

  Global Instance Symmetric_list_eq {T} {R} {Symmetric_R:@Symmetric T R}
    : Symmetric (list_eq R) | 1 := list_eq_sym Symmetric_R.

  Global Instance Equivalence_list_eq {T} {R} {Equivalence_R:@Equivalence T R}
    : Equivalence (list_eq R). Proof. split; exact _. Qed.
End Relations.

Definition list_leq_to_eq {A} {x y : list A} : x = y -> list_eq eq x y.
Proof. destruct 1; reflexivity. Defined.

Fixpoint list_eq_to_leq {A} {x y : list A} {struct x} : list_eq eq x y -> x = y.
Proof.
  destruct x, y; cbn; try reflexivity; destruct 1; try apply f_equal2; eauto.
Defined.

Lemma list_leq_to_eq_refl {A x} : @list_leq_to_eq A x x eq_refl = reflexivity _.
Proof. destruct x; cbn; reflexivity. Qed.

Lemma list_eq_to_leq_refl {A x} : @list_eq_to_leq A x x (reflexivity _) = eq_refl.
Proof.
  induction x as [|x xs IH]; cbn; rewrite ?IH; try reflexivity.
Qed.

Lemma list_leq_to_eq_to_leq {A x y} v : @list_eq_to_leq A x y (@list_leq_to_eq A x y v) = v.
Proof.
  now subst; rewrite list_leq_to_eq_refl, list_eq_to_leq_refl.
Qed.

Lemma list_eq_to_leq_to_eq {A x y} v : @list_leq_to_eq A x y (@list_eq_to_leq A x y v) = v.
Proof.
  revert y v.
  induction x as [|x xs IH], y as [|y ys]; try specialize (IH ys); cbn.
  1-3: intro H; destruct H; reflexivity.
  intro H; destruct H as [? H]; subst; specialize (IH H).
  cbv [list_leq_to_eq] in *; subst.
  break_innermost_match_hyps; subst; reflexivity.
Qed.

Lemma UIP_nil {A} (p q : @nil A = @nil A) : p = q.
Proof.
  rewrite <- (list_leq_to_eq_to_leq p), <- (list_leq_to_eq_to_leq q); simpl; reflexivity.
Qed.

Lemma invert_list_eq {A x y} (p : @list_eq A A eq x y) : { pf : x = y | list_leq_to_eq pf = p }.
Proof. eexists; apply list_eq_to_leq_to_eq. Qed.

Lemma invert_eq_list {A x y} (p : x = y) : { pf : @list_eq A A eq x y | list_eq_to_leq pf = p }.
Proof. eexists; apply list_leq_to_eq_to_leq. Qed.

Ltac destr_list_eq H :=
  lazymatch type of H with
  | True => first [ clear H | destruct H ]
  | False => destruct H
  | _ = _ /\ _
    => let H' := fresh in
       destruct H as [H' H];
       destr_list_eq H
  | list_eq eq _ _
    => first [ apply list_eq_to_leq in H
             | let H' := fresh in
               rename H into H';
               destruct (invert_list_eq H') as [H ?]; subst H' ]
  end.
Ltac inversion_list_step :=
  match goal with
  | [ H : nil = nil |- _ ] => clear H
  | [ H : cons _ _ = nil |- _ ] => solve [ inversion H ]
  | [ H : nil = cons _ _ |- _ ] => solve [ inversion H ]
  | [ H : nil = nil |- _ ]
    => assert (eq_refl = H) by apply UIP_nil; subst H
  | [ H : cons _ _ = cons _ _ |- _ ]
    => apply list_leq_to_eq in H; cbn [list_eq] in H;
       destr_list_eq H
  | [ H : cons _ _ = cons _ _ |- _ ]
    => let H' := fresh in
       rename H into H';
       destruct (invert_eq_list H') as [H ?]; subst H';
       cbn [list_eq] in H; destr_list_eq H
  end.

Ltac inversion_list := repeat inversion_list_step.

Lemma list_bl_hetero {A B} {AB_beq : A -> B -> bool} {AB_R : A -> B -> Prop}
      (AB_bl : forall x y, AB_beq x y = true -> AB_R x y)
  : forall {x y},
    list_beq_hetero AB_beq x y = true -> list_eq AB_R x y.
Proof using Type.
  induction x, y; cbn in *; eauto; try congruence.
  rewrite Bool.andb_true_iff; intuition eauto.
Qed.

Lemma list_lb_hetero {A B} {AB_beq : A -> B -> bool} {AB_R : A -> B -> Prop}
      (AB_lb : forall x y, AB_R x y -> AB_beq x y = true)
  : forall {x y},
    list_eq AB_R x y -> list_beq_hetero AB_beq x y = true.
Proof using Type.
  induction x, y; cbn in *; rewrite ?Bool.andb_true_iff; intuition (congruence || eauto).
Qed.

Lemma list_beq_hetero_uniform {A : Type} A_beq {x y}
  : list_beq_hetero A_beq x y = @list_beq A A_beq x y.
Proof. destruct x, y; cbn; reflexivity. Qed.

Lemma list_bl_hetero_eq {A}
      {A_beq : A -> A -> bool}
      (A_bl : forall x y, A_beq x y = true -> x = y)
      {x y}
  : list_beq_hetero A_beq x y = true -> x = y.
Proof using Type. rewrite list_beq_hetero_uniform; now apply internal_list_dec_bl. Qed.

Lemma list_lb_hetero_eq {A}
      {A_beq : A -> A -> bool}
      (A_lb : forall x y, x = y -> A_beq x y = true)
      {x y}
  : x = y -> list_beq_hetero A_beq x y = true.
Proof using Type. rewrite list_beq_hetero_uniform; now apply internal_list_dec_lb. Qed.

Lemma eqlistA_bl {A eqA} {R : relation A}
      (H : forall x y : A, eqA x y = true -> R x y)
  : forall x y, list_beq A eqA x y = true -> eqlistA R x y.
Proof.
  induction x, y; cbn; auto; try discriminate; constructor.
  all: rewrite Bool.andb_true_iff in *; destruct_head'_and; eauto.
Qed.

Lemma eqlistA_lb {A eqA} {R : relation A}
      (H : forall x y : A, R x y -> eqA x y = true)
  : forall x y, eqlistA R x y -> list_beq A eqA x y = true.
Proof.
  induction x, y; cbn; auto; try discriminate; inversion 1; subst.
  all: rewrite Bool.andb_true_iff; eauto.
Qed.

Lemma nth_default_cons : forall {T} (x u0 : T) us, nth_default x (u0 :: us) 0 = u0.
Proof. auto. Qed.

#[global]
Hint Rewrite @nth_default_cons : simpl_nth_default.
#[global]
Hint Rewrite @nth_default_cons : push_nth_default.

Lemma nth_default_cons_S : forall {A} us (u0 : A) n d,
  nth_default d (u0 :: us) (S n) = nth_default d us n.
Proof. boring. Qed.

#[global]
Hint Rewrite @nth_default_cons_S : simpl_nth_default.
#[global]
Hint Rewrite @nth_default_cons_S : push_nth_default.

Lemma nth_default_nil : forall {T} n (d : T), nth_default d nil n = d.
Proof. induction n; boring. Qed.

#[global]
Hint Rewrite @nth_default_nil : simpl_nth_default.
#[global]
Hint Rewrite @nth_default_nil : push_nth_default.

Lemma nth_error_nil_error : forall {A} n, nth_error (@nil A) n = None.
Proof. induction n; boring. Qed.

#[global]
Hint Rewrite @nth_error_nil_error : simpl_nth_error.

Ltac nth_tac' :=
  intros; simpl in *; unfold error,value in *; repeat progress (match goal with
    | [  |- context[nth_error nil ?n] ] => rewrite nth_error_nil_error
    | [ H: ?x = Some _  |- context[match ?x with Some _ => ?a | None => ?a end ] ] => destruct x
    | [ H: ?x = None _  |- context[match ?x with Some _ => ?a | None => ?a end ] ] => destruct x
    | [  |- context[match ?x with Some _ => ?a | None => ?a end ] ] => destruct x
    | [  |- context[match nth_error ?xs ?i with Some _ => _ | None => _ end ] ] => case_eq (nth_error xs i); intros
    | [ |- context[(if lt_dec ?a ?b then _ else _) = _] ] => destruct (lt_dec a b)
    | [ |- context[_ = (if lt_dec ?a ?b then _ else _)] ] => destruct (lt_dec a b)
    | [ H: context[(if lt_dec ?a ?b then _ else _) = _] |- _ ] => destruct (lt_dec a b)
    | [ H: context[_ = (if lt_dec ?a ?b then _ else _)] |- _ ] => destruct (lt_dec a b)
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ H: Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
    | [ H: None = Some _  |- _ ] => inversion H
    | [ H: Some _ = None |- _ ] => inversion H
    | [ |- Some _ = Some _ ] => apply f_equal
  end); eauto; try (autorewrite with list in *); try lia; eauto.
Lemma nth_error_map {A B f n l}
  : nth_error (@map A B f l) n = option_map f (nth_error l n).
Proof. revert n; induction l, n; nth_tac'. Qed.
Lemma nth_error_map_ex : forall A B (f:A->B) i xs y,
  nth_error (map f xs) i = Some y ->
  exists x, nth_error xs i = Some x /\ f x = y.
Proof. intros *; rewrite nth_error_map; edestruct nth_error; nth_tac'. Qed.

Lemma nth_error_seq : forall i start len,
  nth_error (seq start len) i =
  if lt_dec i len
  then Some (start + i)
  else None.
  induction i as [|? IHi]; destruct len; nth_tac'; erewrite IHi; nth_tac'.
Qed.

Lemma nth_error_error_length : forall A i (xs:list A), nth_error xs i = None ->
  i >= length xs.
Proof.
  induction i as [|? IHi]; destruct xs; nth_tac'; try match goal with H : _ |- _ => specialize (IHi _ H) end; lia.
Qed.

Lemma nth_error_value_length : forall A i (xs:list A) x, nth_error xs i = Some x ->
  i < length xs.
Proof.
  induction i as [|? IHi]; destruct xs; nth_tac'; try match goal with H : _ |- _ => specialize (IHi _ _ H) end; lia.
Qed.

Lemma nth_error_length_error : forall A i (xs:list A),
  i >= length xs ->
  nth_error xs i = None.
Proof.
  induction i as [|? IHi]; destruct xs; nth_tac'; rewrite IHi by lia; auto.
Qed.
Global Hint Resolve nth_error_length_error : core.
#[global]
Hint Rewrite @nth_error_length_error using lia : simpl_nth_error.

Lemma map_nth_default : forall (A B : Type) (f : A -> B) n x y l,
  (n < length l) -> nth_default y (map f l) n = f (nth_default x l n).
Proof.
  intros A B f n x y l H.
  unfold nth_default.
  erewrite map_nth_error.
  reflexivity.
  nth_tac'.
  let H0 := match goal with H0 : _ = None |- _ => H0 end in
  pose proof (nth_error_error_length A n l H0).
  lia.
Qed.

#[global]
Hint Rewrite @map_nth_default using lia : push_nth_default.

Ltac nth_tac :=
  repeat progress (try nth_tac'; try (match goal with
    | [ H: nth_error (map _ _) _ = Some _ |- _ ] => destruct (nth_error_map_ex _ _ _ _ _ _ H); clear H
    | [ H: nth_error (seq _ _) _ = Some _ |- _ ] => rewrite nth_error_seq in H
    | [H: nth_error _ _ = None |- _ ] => specialize (nth_error_error_length _ _ _ H); intro; clear H
  end)).

Lemma app_cons_app_app : forall T xs (y:T) ys, xs ++ y :: ys = (xs ++ (y::nil)) ++ ys.
Proof. induction xs; boring. Qed.

Lemma unfold_set_nth {T} n x
  : forall xs,
    @set_nth T n x xs
    = match n with
      | O => match xs with
             | nil => nil
             | x'::xs' => x::xs'
             end
      | S n' =>  match xs with
                 | nil => nil
                 | x'::xs' => x'::set_nth n' x xs'
                 end
      end.
Proof.
  induction n; destruct xs; reflexivity.
Qed.

Lemma simpl_set_nth_0 {T} x
  : forall xs,
    @set_nth T 0 x xs
    = match xs with
      | nil => nil
      | x'::xs' => x::xs'
      end.
Proof. intro; rewrite unfold_set_nth; reflexivity. Qed.

Lemma simpl_set_nth_S {T} x n
  : forall xs,
    @set_nth T (S n) x xs
    = match xs with
      | nil => nil
      | x'::xs' => x'::set_nth n x xs'
      end.
Proof. intro; rewrite unfold_set_nth; reflexivity. Qed.

#[global]
Hint Rewrite @simpl_set_nth_S @simpl_set_nth_0 : simpl_set_nth.

Lemma update_nth_ext {T} f g n
  : forall xs, (forall x, nth_error xs n = Some x -> f x = g x)
               -> @update_nth T n f xs = @update_nth T n g xs.
Proof.
  induction n as [|n IHn]; destruct xs; simpl; intros H;
    try rewrite IHn; try rewrite H;
      try congruence; trivial.
Qed.

Global Instance update_nth_Proper {T}
  : Proper (eq ==> pointwise_relation _ eq ==> eq ==> eq) (@update_nth T).
Proof. repeat intro; subst; apply update_nth_ext; trivial. Qed.

Global Instance update_nth_Proper_eq {A} : Proper (eq ==> (eq ==> eq) ==> eq ==> eq) (@update_nth A) | 1.
Proof. repeat intro; subst; apply update_nth_Proper; repeat intro; eauto. Qed.

Lemma update_nth_id_eq_specific {T} f n
  : forall (xs : list T) (H : forall x, nth_error xs n = Some x -> f x = x),
    update_nth n f xs = xs.
Proof.
  induction n as [|n IHn]; destruct xs; simpl; intros H;
    try rewrite IHn; try rewrite H; unfold value in *;
      try congruence; assumption.
Qed.

#[global]
Hint Rewrite @update_nth_id_eq_specific using congruence : simpl_update_nth.

Lemma update_nth_id_eq : forall {T} f (H : forall x, f x = x) n (xs : list T),
    update_nth n f xs = xs.
Proof. intros; apply update_nth_id_eq_specific; trivial. Qed.

#[global]
Hint Rewrite @update_nth_id_eq using congruence : simpl_update_nth.

Lemma update_nth_id : forall {T} n (xs : list T),
    update_nth n (fun x => x) xs = xs.
Proof. intros; apply update_nth_id_eq; trivial. Qed.

#[global]
Hint Rewrite @update_nth_id : simpl_update_nth.

Lemma nth_update_nth : forall m {T} (xs:list T) (n:nat) (f:T -> T),
  nth_error (update_nth m f xs) n =
  if eq_nat_dec n m
  then option_map f (nth_error xs n)
  else nth_error xs n.
Proof.
  induction m as [|? IHm].
  { destruct n, xs; auto. }
  { destruct xs, n; intros; simpl; auto;
      [ | rewrite IHm ]; clear IHm;
        edestruct eq_nat_dec; reflexivity. }
Qed.

#[global]
Hint Rewrite @nth_update_nth : push_nth_error.
#[global]
Hint Rewrite <- @nth_update_nth : pull_nth_error.

Lemma length_update_nth : forall {T} i f (xs:list T), length (update_nth i f xs) = length xs.
Proof.
  induction i, xs; boring.
Qed.

#[global]
Hint Rewrite @length_update_nth : distr_length.

Lemma nth_set_nth : forall m {T} (xs:list T) (n:nat) x,
  nth_error (set_nth m x xs) n =
  if eq_nat_dec n m
  then (if lt_dec n (length xs) then Some x else None)
  else nth_error xs n.
Proof.
  intros m T xs n x; unfold set_nth; rewrite nth_update_nth.
  destruct (nth_error xs n) eqn:?, (lt_dec n (length xs)) as [p|p];
    rewrite <- nth_error_Some in p;
    solve [ reflexivity
          | exfalso; apply p; congruence ].
Qed.

#[global]
Hint Rewrite @nth_set_nth : push_nth_error.

Lemma length_set_nth : forall {T} i x (xs:list T), length (set_nth i x xs) = length xs.
Proof. intros; apply length_update_nth. Qed.

#[global]
Hint Rewrite @length_set_nth : distr_length.

Lemma nth_error_length_exists_value : forall {A} (i : nat) (xs : list A),
  (i < length xs)%nat -> exists x, nth_error xs i = Some x.
Proof.
  induction i, xs; boring; try lia.
Qed.

Lemma nth_error_length_not_error : forall {A} (i : nat) (xs : list A),
  nth_error xs i = None -> (i < length xs)%nat -> False.
Proof.
  intros A i xs H H0.
  destruct (nth_error_length_exists_value i xs); intuition; congruence.
Qed.

Lemma nth_error_value_eq_nth_default : forall {T} i (x : T) xs,
  nth_error xs i = Some x -> forall d, nth_default d xs i = x.
Proof.
  unfold nth_default; boring.
Qed.

#[global]
Hint Rewrite @nth_error_value_eq_nth_default using eassumption : simpl_nth_default.

Lemma skipn0 : forall {T} (xs:list T), skipn 0 xs = xs.
Proof. auto. Qed.

Lemma destruct_repeat : forall {A} xs y, (forall x : A, In x xs -> x = y) ->
  xs = nil \/ exists xs', xs = y :: xs' /\ (forall x : A, In x xs' -> x = y).
Proof.
  destruct xs as [|? xs]; intros; try tauto.
  right.
  exists xs; split.
  + f_equal; auto using in_eq.
  + intros; auto using in_cons.
Qed.

Lemma splice_nth_equiv_update_nth : forall {T} n f d (xs:list T),
  splice_nth n (f (nth_default d xs n)) xs =
  if lt_dec n (length xs)
  then update_nth n f xs
  else xs ++ (f d)::nil.
Proof.
  induction n, xs; boring_list; break_match; auto; lia.
Qed.

Lemma splice_nth_equiv_update_nth_update : forall {T} n f d (xs:list T),
  n < length xs ->
  splice_nth n (f (nth_default d xs n)) xs = update_nth n f xs.
Proof.
  intros.
  rewrite splice_nth_equiv_update_nth; break_match; auto; lia.
Qed.

Lemma splice_nth_equiv_update_nth_snoc : forall {T} n f d (xs:list T),
  n >= length xs ->
  splice_nth n (f (nth_default d xs n)) xs = xs ++ (f d)::nil.
Proof.
  intros.
  rewrite splice_nth_equiv_update_nth; break_match; auto; lia.
Qed.

Definition IMPOSSIBLE {T} : list T. exact nil. Qed.

Ltac remove_nth_error :=
  repeat match goal with
         | _ => exfalso; solve [ eauto using @nth_error_length_not_error ]
         | [ |- context[match nth_error ?ls ?n with _ => _ end] ]
           => destruct (nth_error ls n) eqn:?
         end.

Lemma update_nth_equiv_splice_nth: forall {T} n f (xs:list T),
  update_nth n f xs =
  if lt_dec n (length xs)
  then match nth_error xs n with
       | Some v => splice_nth n (f v) xs
       | None => IMPOSSIBLE
       end
  else xs.
Proof.
  induction n as [|? IHn]; destruct xs; intros;
    autorewrite with simpl_update_nth simpl_nth_default in *; simpl in *;
      try (erewrite IHn; clear IHn); auto.
  repeat break_match; remove_nth_error; try reflexivity; try lia.
Qed.

Lemma splice_nth_equiv_set_nth : forall {T} n x (xs:list T),
  splice_nth n x xs =
  if lt_dec n (length xs)
  then set_nth n x xs
  else xs ++ x::nil.
Proof. intros T n x xs; rewrite splice_nth_equiv_update_nth with (f := fun _ => x); auto. Qed.

Lemma splice_nth_equiv_set_nth_set : forall {T} n x (xs:list T),
  n < length xs ->
  splice_nth n x xs = set_nth n x xs.
Proof. intros T n x xs H; rewrite splice_nth_equiv_update_nth_update with (f := fun _ => x); auto. Qed.

Lemma splice_nth_equiv_set_nth_snoc : forall {T} n x (xs:list T),
  n >= length xs ->
  splice_nth n x xs = xs ++ x::nil.
Proof. intros T n x xs H; rewrite splice_nth_equiv_update_nth_snoc with (f := fun _ => x); auto. Qed.

Lemma set_nth_equiv_splice_nth: forall {T} n x (xs:list T),
  set_nth n x xs =
  if lt_dec n (length xs)
  then splice_nth n x xs
  else xs.
Proof.
  intros T n x xs; unfold set_nth; rewrite update_nth_equiv_splice_nth with (f := fun _ => x); auto.
  repeat break_match; remove_nth_error; trivial.
Qed.

Lemma combine_update_nth : forall {A B} n f g (xs:list A) (ys:list B),
  combine (update_nth n f xs) (update_nth n g ys) =
  update_nth n (fun xy => (f (fst xy), g (snd xy))) (combine xs ys).
Proof.
  induction n as [|? IHn]; destruct xs, ys; simpl; try rewrite IHn; reflexivity.
Qed.

(* grumble, grumble, [rewrite] is bad at inferring the identity function, and constant functions *)
Ltac rewrite_rev_combine_update_nth :=
  let lem := match goal with
             | [ |- context[update_nth ?n (fun xy => (@?f xy, @?g xy)) (combine ?xs ?ys)] ]
               => let f := match (eval cbv [fst] in (fun y x => f (x, y))) with
                           | fun _ => ?f => f
                           end in
                  let g := match (eval cbv [snd] in (fun x y => g (x, y))) with
                           | fun _ => ?g => g
                           end in
                  constr:(@combine_update_nth _ _ n f g xs ys)
             end in
  rewrite <- lem.

Lemma combine_update_nth_l : forall {A B} n (f : A -> A) xs (ys:list B),
  combine (update_nth n f xs) ys =
  update_nth n (fun xy => (f (fst xy), snd xy)) (combine xs ys).
Proof.
  intros ??? f xs ys.
  etransitivity; [ | apply combine_update_nth with (g := fun x => x) ].
  rewrite update_nth_id; reflexivity.
Qed.

Lemma combine_update_nth_r : forall {A B} n (g : B -> B) (xs:list A) (ys:list B),
  combine xs (update_nth n g ys) =
  update_nth n (fun xy => (fst xy, g (snd xy))) (combine xs ys).
Proof.
  intros ??? g xs ys.
  etransitivity; [ | apply combine_update_nth with (f := fun x => x) ].
  rewrite update_nth_id; reflexivity.
Qed.

Lemma combine_set_nth : forall {A B} n (x:A) xs (ys:list B),
  combine (set_nth n x xs) ys =
    match nth_error ys n with
    | None => combine xs ys
    | Some y => set_nth n (x,y) (combine xs ys)
    end.
Proof.
  intros A B n x xs ys; unfold set_nth; rewrite combine_update_nth_l.
  nth_tac;
    [ repeat rewrite_rev_combine_update_nth; apply f_equal2
    | assert (nth_error (combine xs ys) n = None)
      by (apply nth_error_None; rewrite combine_length; lia * ) ];
    autorewrite with simpl_update_nth; reflexivity.
Qed.

Lemma nth_error_value_In : forall {T} n xs (x:T),
  nth_error xs n = Some x -> In x xs.
Proof.
  induction n; destruct xs; nth_tac.
Qed.

Lemma In_nth_error_value : forall {T} xs (x:T),
  In x xs -> exists n, nth_error xs n = Some x.
Proof.
  induction xs as [|?? IHxs]; nth_tac; destruct_head or; subst.
  - exists 0; reflexivity.
  - edestruct IHxs as [x0]; eauto. exists (S x0). eauto.
Qed.

Lemma nth_value_index : forall {T} i xs (x:T),
  nth_error xs i = Some x -> In i (seq 0 (length xs)).
Proof.
  induction i as [|? IHi]; destruct xs; nth_tac; right.
  rewrite <- seq_shift; apply in_map; eapply IHi; eauto.
Qed.

Lemma nth_error_app : forall {T} n (xs ys:list T), nth_error (xs ++ ys) n =
  if lt_dec n (length xs)
  then nth_error xs n
  else nth_error ys (n - length xs).
Proof.
  induction n as [|n IHn]; destruct xs as [|? xs]; nth_tac;
    rewrite IHn; destruct (lt_dec n (length xs)); trivial; lia.
Qed.

Lemma nth_default_app : forall {T} n x (xs ys:list T), nth_default x (xs ++ ys) n =
  if lt_dec n (length xs)
  then nth_default x xs n
  else nth_default x ys (n - length xs).
Proof.
  intros T n x xs ys.
  unfold nth_default.
  rewrite nth_error_app.
  destruct (lt_dec n (length xs)); auto.
Qed.

#[global]
Hint Rewrite @nth_default_app : push_nth_default.

Lemma combine_truncate_r : forall {A B} (xs : list A) (ys : list B),
  combine xs ys = combine xs (firstn (length xs) ys).
Proof.
  induction xs; destruct ys; boring.
Qed.

Lemma combine_truncate_l : forall {A B} (xs : list A) (ys : list B),
  combine xs ys = combine (firstn (length ys) xs) ys.
Proof.
  induction xs; destruct ys; boring.
Qed.

Lemma combine_app_samelength : forall {A B} (xs xs':list A) (ys ys':list B),
  length xs = length ys ->
  combine (xs ++ xs') (ys ++ ys') = combine xs ys ++ combine xs' ys'.
Proof.
  induction xs, xs', ys, ys'; boring; lia.
Qed.

Lemma map_fst_combine {A B} (xs:list A) (ys:list B) : List.map fst (List.combine xs ys) = List.firstn (length ys) xs.
Proof.
  revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
Qed.

Lemma map_snd_combine {A B} (xs:list A) (ys:list B) : List.map snd (List.combine xs ys) = List.firstn (length xs) ys.
Proof.
  revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
Qed.
#[global]
Hint Rewrite @map_fst_combine @map_snd_combine : push_map.

Lemma skipn_nil : forall {A} n, skipn n nil = @nil A.
Proof. destruct n; auto. Qed.

#[global]
Hint Rewrite @skipn_nil : simpl_skipn.
#[global]
Hint Rewrite @skipn_nil : push_skipn.

Lemma skipn_0 : forall {A} xs, @skipn A 0 xs = xs.
Proof. reflexivity. Qed.

#[global]
Hint Rewrite @skipn_0 : simpl_skipn.
#[global]
Hint Rewrite @skipn_0 : push_skipn.

Lemma skipn_cons_S : forall {A} n x xs, @skipn A (S n) (x::xs) = @skipn A n xs.
Proof. reflexivity. Qed.

#[global]
Hint Rewrite @skipn_cons_S : simpl_skipn.
#[global]
Hint Rewrite @skipn_cons_S : push_skipn.

Lemma skipn_app : forall {A} n (xs ys : list A),
  skipn n (xs ++ ys) = skipn n xs ++ skipn (n - length xs) ys.
Proof.
  induction n, xs, ys; boring.
Qed.

#[global]
Hint Rewrite @skipn_app : push_skipn.

Lemma skipn_skipn {A} n1 n2 (ls : list A)
  : skipn n2 (skipn n1 ls) = skipn (n1 + n2) ls.
Proof.
  revert n2 ls; induction n1, ls;
    simpl; autorewrite with simpl_skipn;
      boring.
Qed.

#[global]
Hint Rewrite @skipn_skipn : simpl_skipn.
#[global]
Hint Rewrite <- @skipn_skipn : push_skipn.
#[global]
Hint Rewrite @skipn_skipn : pull_skipn.

Lemma skipn_firstn {A} (ls : list A) n m
  : skipn n (firstn m ls) = firstn (m - n) (skipn n ls).
Proof.
  revert n m; induction ls, m, n; simpl; autorewrite with simpl_skipn simpl_firstn; boring_list.
Qed.
Lemma firstn_skipn_add {A} (ls : list A) n m
  : firstn n (skipn m ls) = skipn m (firstn (m + n) ls).
Proof.
  revert n m; induction ls, m; simpl; autorewrite with simpl_skipn simpl_firstn; boring_list.
Qed.
Lemma firstn_skipn_add' {A} (ls : list A) n m
  : firstn n (skipn m ls) = skipn m (firstn (n + m) ls).
Proof. rewrite firstn_skipn_add; do 2 f_equal; auto with arith. Qed.
#[global]
Hint Rewrite <- @firstn_skipn_add @firstn_skipn_add' : simpl_firstn.
#[global]
Hint Rewrite <- @firstn_skipn_add @firstn_skipn_add' : simpl_skipn.

Lemma firstn_app_inleft : forall {A} n (xs ys : list A), (n <= length xs)%nat ->
  firstn n (xs ++ ys) = firstn n xs.
Proof.
  induction n, xs, ys; boring; try lia.
Qed.

#[global]
Hint Rewrite @firstn_app_inleft using solve [ distr_length ] : simpl_firstn.
#[global]
Hint Rewrite @firstn_app_inleft using solve [ distr_length ] : push_firstn.

Lemma skipn_app_inleft : forall {A} n (xs ys : list A), (n <= length xs)%nat ->
  skipn n (xs ++ ys) = skipn n xs ++ ys.
Proof.
  induction n, xs, ys; boring; try lia.
Qed.

#[global]
Hint Rewrite @skipn_app_inleft using solve [ distr_length ] : push_skipn.

Lemma firstn_map : forall {A B} (f : A -> B) n (xs : list A), firstn n (map f xs) = map f (firstn n xs).
Proof. induction n, xs; boring. Qed.

#[global]
Hint Rewrite @firstn_map : push_firstn.
#[global]
Hint Rewrite <- @firstn_map : pull_firstn.

Lemma skipn_map : forall {A B} (f : A -> B) n (xs : list A), skipn n (map f xs) = map f (skipn n xs).
Proof. induction n, xs; boring. Qed.

#[global]
Hint Rewrite @skipn_map : push_skipn.
#[global]
Hint Rewrite <- @skipn_map : pull_skipn.

Lemma firstn_all : forall {A} n (xs:list A), n = length xs -> firstn n xs = xs.
Proof.
  induction n, xs; boring; lia.
Qed.

#[global]
Hint Rewrite @firstn_all using solve [ distr_length ] : simpl_firstn.
#[global]
Hint Rewrite @firstn_all using solve [ distr_length ] : push_firstn.

Lemma skipn_all : forall {T} n (xs:list T),
  (n >= length xs)%nat ->
  skipn n xs = nil.
Proof.
  induction n, xs; boring; lia.
Qed.

#[global]
Hint Rewrite @skipn_all using solve [ distr_length ] : simpl_skipn.
#[global]
Hint Rewrite @skipn_all using solve [ distr_length ] : push_skipn.

Lemma firstn_app_sharp : forall {A} n (l l': list A),
  length l = n ->
  firstn n (l ++ l') = l.
Proof.
  intros.
  rewrite firstn_app_inleft; auto using firstn_all; lia.
Qed.

#[global]
Hint Rewrite @firstn_app_sharp using solve [ distr_length ] : simpl_firstn.
#[global]
Hint Rewrite @firstn_app_sharp using solve [ distr_length ] : push_firstn.

Lemma skipn_app_sharp : forall {A} n (l l': list A),
  length l = n ->
  skipn n (l ++ l') = l'.
Proof.
  intros.
  rewrite skipn_app_inleft; try rewrite skipn_all; auto; lia.
Qed.

#[global]
Hint Rewrite @skipn_app_sharp using solve [ distr_length ] : simpl_skipn.
#[global]
Hint Rewrite @skipn_app_sharp using solve [ distr_length ] : push_skipn.

Lemma skipn_length : forall {A} n (xs : list A),
  length (skipn n xs) = (length xs - n)%nat.
Proof.
  induction n, xs; boring.
Qed.

#[global]
Hint Rewrite @skipn_length : distr_length.

Lemma length_cons : forall {T} (x:T) xs, length (x::xs) = S (length xs).
  reflexivity.
Qed.

#[global]
Hint Rewrite @length_cons : distr_length.

Lemma length_cons_full {T} n (x:list T) (t:T) (H: length (t :: x) = S n)
  : length x = n.
Proof. distr_length. Qed.

Lemma cons_length : forall A (xs : list A) a, length (a :: xs) = S (length xs).
Proof.
  auto.
Qed.

Lemma length0_nil : forall {A} (xs : list A), length xs = 0%nat -> xs = nil.
Proof.
  induction xs; boring; discriminate.
Qed.

Lemma length_tl {A} ls : length (@tl A ls) = (length ls - 1)%nat.
Proof. destruct ls; cbn [tl length]; lia. Qed.
#[global]
Hint Rewrite @length_tl : distr_length.

Lemma length_snoc {A : Type} (l : list A) a : length (l ++ [a]) = S (length l).
Proof. simpl_list; boring. Qed.

#[global]
Hint Rewrite @length_snoc : distr_length.

Lemma combine_cons : forall {A B} a b (xs:list A) (ys:list B),
  combine (a :: xs) (b :: ys) = (a,b) :: combine xs ys.
Proof. reflexivity. Qed.
#[global]
Hint Rewrite @combine_cons : push_combine.

Lemma firstn_combine : forall {A B} n (xs:list A) (ys:list B),
  firstn n (combine xs ys) = combine (firstn n xs) (firstn n ys).
Proof.
  induction n, xs, ys; boring.
Qed.

#[global]
Hint Rewrite @firstn_combine : push_firstn.
#[global]
Hint Rewrite <- @firstn_combine : pull_firstn.

Lemma combine_nil_r : forall {A B} (xs:list A),
  combine xs (@nil B) = nil.
Proof.
  induction xs; boring.
Qed.
#[global]
Hint Rewrite @combine_nil_r : push_combine.

Lemma combine_snoc {A B} xs : forall ys x y,
    length xs = length ys ->
    @combine A B (xs ++ (x :: nil)) (ys ++ (y :: nil)) = combine xs ys ++ ((x, y) :: nil).
Proof.
  induction xs; intros; destruct ys; distr_length; cbn;
    try rewrite IHxs by lia; reflexivity.
Qed.
#[global]
Hint Rewrite @combine_snoc using (solve [distr_length]) : push_combine.

Lemma skipn_combine : forall {A B} n (xs:list A) (ys:list B),
  skipn n (combine xs ys) = combine (skipn n xs) (skipn n ys).
Proof.
  induction n, xs, ys; boring.
  rewrite combine_nil_r; reflexivity.
Qed.

#[global]
Hint Rewrite @skipn_combine : push_skipn.
#[global]
Hint Rewrite <- @skipn_combine : pull_skipn.

Lemma break_list_last: forall {T} (xs:list T),
  xs = nil \/ exists xs' y, xs = xs' ++ y :: nil.
Proof.
  destruct xs using rev_ind; auto.
  right; do 2 eexists; auto.
Qed.

Lemma break_list_first: forall {T} (xs:list T),
  xs = nil \/ exists x xs', xs = x :: xs'.
Proof.
  destruct xs; auto.
  right; do 2 eexists; auto.
Qed.

Lemma list012 : forall {T} (xs:list T),
  xs = nil
  \/ (exists x, xs = x::nil)
  \/ (exists x xs' y, xs = x::xs'++y::nil).
Proof.
  destruct xs as [|? xs]; auto.
  right.
  destruct xs using rev_ind. {
    left; eexists; auto.
  } {
    right; repeat eexists; auto.
  }
Qed.

Lemma nil_length0 : forall {T}, length (@nil T) = 0%nat.
Proof.
  auto.
Qed.

#[global]
Hint Rewrite @nil_length0 : distr_length.

Lemma nth_error_Some_nth_default : forall {T} i x (l : list T), (i < length l)%nat ->
  nth_error l i = Some (nth_default x l i).
Proof.
  intros ? ? ? ? i_lt_length.
  destruct (nth_error_length_exists_value _ _ i_lt_length) as [k nth_err_k].
  unfold nth_default.
  rewrite nth_err_k.
  reflexivity.
Qed.

Lemma update_nth_cons : forall {T} f (u0 : T) us, update_nth 0 f (u0 :: us) = (f u0) :: us.
Proof. reflexivity. Qed.

#[global]
Hint Rewrite @update_nth_cons : simpl_update_nth.

Lemma set_nth_cons : forall {T} (x u0 : T) us, set_nth 0 x (u0 :: us) = x :: us.
Proof. intros; apply update_nth_cons. Qed.

#[global]
Hint Rewrite @set_nth_cons : simpl_set_nth.

Lemma cons_update_nth : forall {T} n f (y : T) us,
  y :: update_nth n f us = update_nth (S n) f (y :: us).
Proof.
  induction n; boring.
Qed.

#[global]
Hint Rewrite <- @cons_update_nth : simpl_update_nth.

Lemma update_nth_nil : forall {T} n f, update_nth n f (@nil T) = @nil T.
Proof.
  induction n; boring.
Qed.

#[global]
Hint Rewrite @update_nth_nil : simpl_update_nth.

Lemma cons_set_nth : forall {T} n (x y : T) us,
  y :: set_nth n x us = set_nth (S n) x (y :: us).
Proof. intros; apply cons_update_nth. Qed.

#[global]
Hint Rewrite <- @cons_set_nth : simpl_set_nth.

Lemma set_nth_nil : forall {T} n (x : T), set_nth n x nil = nil.
Proof. intros; apply update_nth_nil. Qed.

#[global]
Hint Rewrite @set_nth_nil : simpl_set_nth.

Lemma skipn_nth_default : forall {T} n us (d : T), (n < length us)%nat ->
 skipn n us = nth_default d us n :: skipn (S n) us.
Proof.
  induction n as [|n IHn]; destruct us as [|? us]; intros d H; nth_tac.
  rewrite (IHn us d) at 1 by lia.
  nth_tac.
Qed.

Lemma nth_default_out_of_bounds : forall {T} n us (d : T), (n >= length us)%nat ->
  nth_default d us n = d.
Proof.
  induction n as [|n IHn]; unfold nth_default; nth_tac;
    let us' := match goal with us : list _ |- _ => us end in
    destruct us' as [|? us]; nth_tac.
  assert (n >= length us)%nat by lia.
  pose proof (nth_error_length_error _ n us).
  specialize_by_assumption.
  rewrite_hyp * in *.
  congruence.
Qed.

#[global]
Hint Rewrite @nth_default_out_of_bounds using lia : simpl_nth_default.

Ltac nth_error_inbounds :=
  match goal with
  | [ |- context[match nth_error ?xs ?i with Some _ => _ | None => _ end ] ] =>
    case_eq (nth_error xs i);
    match goal with
      | [ |- forall _, nth_error xs i = Some _ -> _ ] =>
          let x := fresh "x" in
          let H := fresh "H" in
          intros x H;
          repeat progress erewrite H;
          repeat progress erewrite (nth_error_value_eq_nth_default i xs x); auto
      | [ |- nth_error xs i = None -> _ ] =>
          let H := fresh "H" in
          intros H;
          destruct (nth_error_length_not_error _ _ H);
          try solve [distr_length]
    end;
    idtac
  end.
Ltac set_nth_inbounds :=
  match goal with
  | [ |- context[set_nth ?i ?x ?xs] ] =>
    rewrite (set_nth_equiv_splice_nth i x xs);
    destruct (lt_dec i (length xs));
    match goal with
    | [ H : ~ (i < (length xs))%nat |- _ ] => destruct H
    | [ H :   (i < (length xs))%nat |- _ ] => try solve [distr_length]
    end
  end.
Ltac update_nth_inbounds :=
  match goal with
  | [ |- context[update_nth ?i ?f ?xs] ] =>
    rewrite (update_nth_equiv_splice_nth i f xs);
    destruct (lt_dec i (length xs));
    match goal with
    | [ H : ~ (i < (length xs))%nat |- _ ] => destruct H
    | [ H :   (i < (length xs))%nat |- _ ] => remove_nth_error; try solve [distr_length]
    end
  end.

Ltac nth_inbounds := nth_error_inbounds || set_nth_inbounds || update_nth_inbounds.

Definition nth_dep {A} (ls : list A) (n : nat) (pf : n < length ls) : A.
Proof.
  refine (match nth_error ls n as v return nth_error ls n = v -> A with
          | Some v => fun _ => v
          | None => fun bad => match _ : False with end
          end eq_refl).
  apply (proj1 (@nth_error_None _ _ _)) in bad; instantiate; generalize dependent (length ls); clear.
  abstract (intros; lia).
Defined.

Lemma nth_error_nth_dep {A} ls n pf : nth_error ls n = Some (@nth_dep A ls n pf).
Proof.
  unfold nth_dep.
  generalize dependent (@nth_error_None A ls n).
  edestruct nth_error; boring.
Qed.

Lemma nth_default_nth_dep {A} d ls n pf : nth_default d ls n = @nth_dep A ls n pf.
Proof.
  unfold nth_dep.
  generalize dependent (@nth_error_None A ls n).
  destruct (nth_error ls n) eqn:?; boring.
  erewrite nth_error_value_eq_nth_default by eassumption; reflexivity.
Qed.

Lemma nth_default_in_bounds : forall {T} (d' d : T) n us, (n < length us)%nat ->
  nth_default d us n = nth_default d' us n.
Proof.
  intros; now unshelve erewrite !nth_default_nth_dep.
Qed.

Global Hint Resolve nth_default_in_bounds : simpl_nth_default.

Lemma cons_eq_head : forall {T} (x y:T) xs ys, x::xs = y::ys -> x=y.
Proof.
  intros; congruence.
Qed.
Lemma cons_eq_tail : forall {T} (x y:T) xs ys, x::xs = y::ys -> xs=ys.
Proof.
  intros; congruence.
Qed.

Lemma map_nth_default_always {A B} (f : A -> B) (n : nat) (x : A) (l : list A)
  : nth_default (f x) (map f l) n = f (nth_default x l n).
Proof.
  revert n; induction l; simpl; intro n; destruct n; [ try reflexivity.. ].
  nth_tac.
Qed.

#[global]
Hint Rewrite @map_nth_default_always : push_nth_default.

Lemma map_S_seq {A} (f:nat->A) len : forall start,
  List.map (fun i => f (S i)) (seq start len) = List.map f (seq (S start) len).
Proof. induction len as [|len IHlen]; intros; simpl; rewrite ?IHlen; reflexivity. Qed.

Lemma seq_snoc len : forall start, seq start (S len) = seq start len ++ ((start + len)%nat :: nil).
Proof.
  induction len; intros.
  { cbv [seq app]. autorewrite with natsimplify; reflexivity. }
  { remember (S len); simpl seq.
      rewrite (IHlen (S start)); subst; simpl seq.
      rewrite Nat.add_succ_r; reflexivity. }
Qed.

Lemma seq_len_0 a : seq a 0 = nil. Proof. reflexivity. Qed.
Lemma seq_add start a b : seq start (a + b) = seq start a ++ seq (start + a) b.
Proof.
  revert start b; induction a as [|a IHa]; cbn; intros start b.
  { f_equal; lia. }
  { rewrite IHa; do 3 f_equal; lia. }
Qed.

Lemma map_seq_ext {A} (f g : nat -> A) (n m k : nat)
      (H : forall i : nat, n <= i <= m + k -> f i = g (i + (m - n))%nat)
      (Hnm : n <= m) :
  map f (seq n k) = map g (seq m k).
Proof.
  generalize dependent m; generalize dependent n; induction k as [|k IHk]; intros; simpl.
  - reflexivity.
  - simpl; rewrite H by lia; replace (n + (m - n))%nat with m by lia.
    rewrite (IHk (S n) (S m)); [reflexivity| |lia].
    intros; rewrite Nat.sub_succ; apply H; lia. Qed.

Lemma map_seq_pred n m :
  seq n m = map (fun i => (i - 1)%nat) (seq (S n) m).
Proof. rewrite <- map_id at 1; apply map_seq_ext; intros; lia. Qed.

Lemma map_seq_succ n m :
  seq (S n) m = map (fun i => (i + 1)%nat) (seq n m).
Proof. rewrite <- map_id at 1; symmetry; apply map_seq_ext; intros; lia. Qed.

Lemma fold_right_and_Truth_forall_In_iff : forall {T} (l : list T) (P : T -> Prop) (Tr : Prop),
    (Tr /\ forall x, In x l -> P x) <-> fold_right and Tr (map P l).
Proof.
  induction l as [|?? IHl]; intros; simpl; try tauto.
  rewrite <- IHl by assumption.
  intuition (subst; auto).
Qed.

Lemma fold_right_and_True_forall_In_iff : forall {T} (l : list T) (P : T -> Prop),
  (forall x, In x l -> P x) <-> fold_right and True (map P l).
Proof.
  intros; rewrite <- fold_right_and_Truth_forall_In_iff; tauto.
Qed.

Lemma fold_right_invariant : forall {A B} P (f: A -> B -> B) l x,
  P x -> (forall y, In y l -> forall z, P z -> P (f y z)) ->
  P (fold_right f x l).
Proof.
  induction l as [|a l IHl]; intros ? ? step; auto.
  simpl.
  apply step; try apply in_eq.
  apply IHl; auto.
  intros y in_y_l.
  apply (in_cons a) in in_y_l.
  auto.
Qed.

Lemma fold_left_and_Truth_forall_In_iff : forall {T} (l : list T) (P : T -> Prop) (Tr : Prop),
    (Tr /\ forall x, In x l -> P x) <-> fold_left and (map P l) Tr.
Proof.
  induction l as [|?? IHl]; intros; simpl; try tauto.
  rewrite <- IHl.
  intuition (subst; auto).
Qed.

Lemma fold_left_and_True_forall_In_iff : forall {T} (l : list T) (P : T -> Prop),
  (forall x, In x l -> P x) <-> fold_left and (map P l) True.
Proof.
  intros; rewrite <- fold_left_and_Truth_forall_In_iff; tauto.
Qed.

Lemma fold_left_invariant : forall {A B} P (f: B -> A -> B) l x,
  P x -> (forall y, In y l -> forall z, P z -> P (f z y)) ->
  P (fold_left f l x).
Proof.
  pose proof in_rev.
  split_iff.
  intros; rewrite <- fold_left_rev_right; eapply fold_right_invariant;
    eauto.
Qed.

Lemma In_firstn : forall {T} n l (x : T), In x (firstn n l) -> In x l.
Proof.
  induction n; destruct l; boring.
Qed.

Lemma In_skipn : forall {T} n l (x : T), In x (skipn n l) -> In x l.
Proof.
  induction n; destruct l; boring.
Qed.

Lemma In_firstn_skipn_split {T} n (x : T)
  : forall l, In x l <-> In x (firstn n l) \/ In x (skipn n l).
Proof.
  intro l; split; revert l; induction n; destruct l; boring.
  match goal with
  | [ IH : forall l, In ?x l -> _ \/ _, H' : In ?x ?ls |- _ ]
    => destruct (IH _ H')
  end; auto.
Qed.

Lemma firstn_firstn_min : forall {A} m n (l : list A),
    firstn n (firstn m l) = firstn (min n m) l.
Proof.
  induction m as [|? IHm]; destruct n; intros l; try lia; auto.
  destruct l; auto.
  simpl.
  f_equal.
  apply IHm; lia.
Qed.

Lemma firstn_firstn : forall {A} m n (l : list A), (n <= m)%nat ->
  firstn n (firstn m l) = firstn n l.
Proof.
  intros A m n l H; rewrite firstn_firstn_min.
  apply Min.min_case_strong; intro; [ reflexivity | ].
  assert (n = m) by lia; subst; reflexivity.
Qed.

#[global]
Hint Rewrite @firstn_firstn using lia : push_firstn.

Lemma firstn_succ : forall {A} (d : A) n l, (n < length l)%nat ->
  firstn (S n) l = (firstn n l) ++ nth_default d l n :: nil.
Proof.
  intros A d; induction n as [|? IHn]; destruct l; rewrite ?(@nil_length0 A); intros; try lia.
  + rewrite nth_default_cons; auto.
  + simpl.
    rewrite nth_default_cons_S.
    rewrite <-IHn by (rewrite cons_length in *; lia).
    reflexivity.
Qed.

Lemma firstn_seq k a b
  : firstn k (seq a b) = seq a (min k b).
Proof.
  revert k a; induction b as [|? IHb], k; simpl; try reflexivity.
  intros; rewrite IHb; reflexivity.
Qed.
#[global]
Hint Rewrite @firstn_seq : push_firstn.

Lemma skipn_seq k a b
  : skipn k (seq a b) = seq (k + a) (b - k).
Proof.
  revert k a; induction b as [|? IHb], k; simpl; try reflexivity.
  intros; rewrite IHb; simpl; f_equal; lia.
Qed.

Lemma update_nth_out_of_bounds : forall {A} n f xs, n >= length xs -> @update_nth A n f xs = xs.
Proof.
  induction n as [|n IHn]; destruct xs; simpl; try congruence; try lia; intros.
  rewrite IHn by lia; reflexivity.
Qed.

#[global]
Hint Rewrite @update_nth_out_of_bounds using lia : simpl_update_nth.


Lemma update_nth_nth_default_full : forall {A} (d:A) n f l i,
  nth_default d (update_nth n f l) i =
  if lt_dec i (length l) then
    if (eq_nat_dec i n) then f (nth_default d l i)
    else nth_default d l i
  else d.
Proof.
  induction n as [|n IHn]; (destruct l; simpl in *; [ intros i **; destruct i; simpl; try reflexivity; lia | ]);
    intros i **; repeat break_match; subst; try destruct i;
      repeat first [ progress break_match
                   | progress subst
                   | progress boring
                   | progress autorewrite with simpl_nth_default
                   | lia ].
Qed.

#[global]
Hint Rewrite @update_nth_nth_default_full : push_nth_default.

Lemma update_nth_nth_default : forall {A} (d:A) n f l i, (0 <= i < length l)%nat ->
  nth_default d (update_nth n f l) i =
  if (eq_nat_dec i n) then f (nth_default d l i) else nth_default d l i.
Proof. intros; rewrite update_nth_nth_default_full; repeat break_match; boring. Qed.

#[global]
Hint Rewrite @update_nth_nth_default using (lia || distr_length; lia) : push_nth_default.

Lemma set_nth_nth_default_full : forall {A} (d:A) n v l i,
  nth_default d (set_nth n v l) i =
  if lt_dec i (length l) then
    if (eq_nat_dec i n) then v
    else nth_default d l i
  else d.
Proof. intros; apply update_nth_nth_default_full; assumption. Qed.

#[global]
Hint Rewrite @set_nth_nth_default_full : push_nth_default.

Lemma set_nth_nth_default : forall {A} (d:A) n x l i, (0 <= i < length l)%nat ->
  nth_default d (set_nth n x l) i =
  if (eq_nat_dec i n) then x else nth_default d l i.
Proof. intros; apply update_nth_nth_default; assumption. Qed.

#[global]
Hint Rewrite @set_nth_nth_default using (lia || distr_length; lia) : push_nth_default.

Lemma nth_default_preserves_properties : forall {A} (P : A -> Prop) l n d,
  (forall x, In x l -> P x) -> P d -> P (nth_default d l n).
Proof.
  intros A P l n d H H0; rewrite nth_default_eq.
  destruct (nth_in_or_default n l d); auto.
  congruence.
Qed.

Lemma nth_default_preserves_properties_length_dep :
  forall {A} (P : A -> Prop) l n d,
  (forall x, In x l -> n < (length l) -> P x) -> ((~ n < length l) -> P d) -> P (nth_default d l n).
Proof.
  intros A P l n d H H0.
  destruct (lt_dec n (length l)).
  + rewrite nth_default_eq; auto using nth_In.
  + rewrite nth_default_out_of_bounds by lia.
    auto.
Qed.

Lemma nth_error_first : forall {T} (a b : T) l,
  nth_error (a :: l) 0 = Some b -> a = b.
Proof.
  intros; simpl in *.
  unfold value in *.
  congruence.
Qed.

Lemma nth_error_exists_first : forall {T} l (x : T) (H : nth_error l 0 = Some x),
  exists l', l = x :: l'.
Proof.
  induction l; try discriminate; intros x H; eexists.
  apply nth_error_first in H.
  subst; eauto.
Qed.

Lemma list_elementwise_eq : forall {T} (l1 l2 : list T),
  (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  induction l1, l2; intros H; try reflexivity;
    pose proof (H 0%nat) as Hfirst; simpl in Hfirst; inversion Hfirst.
  f_equal.
  apply IHl1.
  intros i; specialize (H (S i)).
  boring.
Qed.

Lemma sum_firstn_all_succ : forall n l, (length l <= n)%nat ->
  sum_firstn l (S n) = sum_firstn l n.
Proof.
  unfold sum_firstn; intros.
  autorewrite with push_firstn; reflexivity.
Qed.

#[global]
Hint Rewrite @sum_firstn_all_succ using lia : simpl_sum_firstn.

Lemma sum_firstn_all : forall n l, (length l <= n)%nat ->
  sum_firstn l n = sum_firstn l (length l).
Proof.
  unfold sum_firstn; intros.
  autorewrite with push_firstn; reflexivity.
Qed.

#[global]
Hint Rewrite @sum_firstn_all using lia : simpl_sum_firstn.

Lemma sum_firstn_succ_default : forall l i,
  sum_firstn l (S i) = (nth_default 0 l i + sum_firstn l i)%Z.
Proof.
  unfold sum_firstn; induction l as [|a l IHl], i;
    intros; autorewrite with simpl_nth_default simpl_firstn simpl_fold_right in *;
      try reflexivity.
  rewrite IHl; lia.
Qed.

#[global]
Hint Rewrite @sum_firstn_succ_default : simpl_sum_firstn.

Lemma sum_firstn_0 : forall xs,
  sum_firstn xs 0 = 0%Z.
Proof.
  destruct xs; reflexivity.
Qed.

#[global]
Hint Rewrite @sum_firstn_0 : simpl_sum_firstn.

Lemma sum_firstn_succ : forall l i x,
  nth_error l i = Some x ->
  sum_firstn l (S i) = (x + sum_firstn l i)%Z.
Proof.
  intros; rewrite sum_firstn_succ_default.
  erewrite nth_error_value_eq_nth_default by eassumption; reflexivity.
Qed.

#[global]
Hint Rewrite @sum_firstn_succ using congruence : simpl_sum_firstn.

Lemma sum_firstn_succ_cons : forall x xs i,
  sum_firstn (x :: xs) (S i) = (x + sum_firstn xs i)%Z.
Proof.
  unfold sum_firstn; simpl; reflexivity.
Qed.

#[global]
Hint Rewrite @sum_firstn_succ_cons : simpl_sum_firstn.

Lemma sum_firstn_nil : forall i,
  sum_firstn nil i = 0%Z.
Proof. destruct i; reflexivity. Qed.

#[global]
Hint Rewrite @sum_firstn_nil : simpl_sum_firstn.

Lemma sum_firstn_succ_default_rev : forall l i,
  sum_firstn l i = (sum_firstn l (S i) - nth_default 0 l i)%Z.
Proof.
  intros; rewrite sum_firstn_succ_default; lia.
Qed.

Lemma sum_firstn_succ_rev : forall l i x,
  nth_error l i = Some x ->
  sum_firstn l i = (sum_firstn l (S i) - x)%Z.
Proof.
  intros; erewrite sum_firstn_succ by eassumption; lia.
Qed.

Lemma sum_firstn_nonnegative : forall n l, (forall x, In x l -> 0 <= x)%Z
                                       -> (0 <= sum_firstn l n)%Z.
Proof.
  induction n as [|n IHn]; destruct l as [|? l]; autorewrite with simpl_sum_firstn; simpl; try lia.
  { specialize (IHn l).
    destruct n; simpl; autorewrite with simpl_sum_firstn simpl_nth_default in *;
      intuition auto with zarith. }
Qed.

Global Hint Resolve sum_firstn_nonnegative : znonzero.

Lemma sum_firstn_app : forall xs ys n,
  sum_firstn (xs ++ ys) n = (sum_firstn xs n + sum_firstn ys (n - length xs))%Z.
Proof.
  induction xs as [|a xs IHxs]; simpl.
  { intros ys n; autorewrite with simpl_sum_firstn; simpl.
    f_equal; lia. }
  { intros ys [|n]; autorewrite with simpl_sum_firstn; simpl; [ reflexivity | ].
    rewrite IHxs; lia. }
Qed.

Lemma sum_firstn_app_sum : forall xs ys n,
  sum_firstn (xs ++ ys) (length xs + n) = (sum_firstn xs (length xs) + sum_firstn ys n)%Z.
Proof.
  intros; rewrite sum_firstn_app; autorewrite with simpl_sum_firstn.
  do 2 f_equal; lia.
Qed.
#[global]
Hint Rewrite @sum_firstn_app_sum : simpl_sum_firstn.

Lemma sum_cons xs x : sum (x :: xs) = (x + sum xs)%Z.
Proof. reflexivity. Qed.
#[global]
Hint Rewrite sum_cons : push_sum.

Lemma sum_nil : sum nil = 0%Z.
Proof. reflexivity. Qed.
#[global]
Hint Rewrite sum_nil : push_sum.

Lemma sum_app x y : sum (x ++ y) = (sum x + sum y)%Z.
Proof. induction x; rewrite ?app_nil_l, <-?app_comm_cons; autorewrite with push_sum; lia. Qed.
#[global]
Hint Rewrite sum_app : push_sum.

Lemma sum_rev x : sum (rev x) = sum x.
Proof. induction x; cbn [rev]; autorewrite with push_sum; lia. Qed.
#[global]
Hint Rewrite sum_rev : push_sum.

Lemma nth_error_skipn : forall {A} n (l : list A) m,
nth_error (skipn n l) m = nth_error l (n + m).
Proof.
induction n as [|n IHn]; destruct l; boring.
apply nth_error_nil_error.
Qed.
#[global]
Hint Rewrite @nth_error_skipn : push_nth_error.

Lemma nth_default_skipn : forall {A} (l : list A) d n m, nth_default d (skipn n l) m = nth_default d l (n + m).
Proof.
cbv [nth_default]; intros.
rewrite nth_error_skipn.
reflexivity.
Qed.
#[global]
Hint Rewrite @nth_default_skipn : push_nth_default.

Lemma sum_firstn_skipn : forall l n m, sum_firstn l (n + m) = (sum_firstn l n + sum_firstn (skipn n l) m)%Z.
Proof.
induction m; intros.
+ rewrite sum_firstn_0. autorewrite with natsimplify. lia.
+ rewrite <-plus_n_Sm, !sum_firstn_succ_default.
    rewrite nth_default_skipn.
    lia.
Qed.

Lemma nth_default_seq_inbounds d s n i (H:(i < n)%nat) :
  List.nth_default d (List.seq s n) i = (s+i)%nat.
Proof.
  progress cbv [List.nth_default].
  rewrite nth_error_seq.
  break_innermost_match; solve [ trivial | lia ].
Qed.
#[global]
Hint Rewrite @nth_default_seq_inbounds using lia : push_nth_default.

Lemma sum_firstn_prefix_le' : forall l n m, (forall x, In x l -> (0 <= x)%Z) ->
                                            (sum_firstn l n <= sum_firstn l (n + m))%Z.
Proof.
intros l n m H.
rewrite sum_firstn_skipn.
pose proof (sum_firstn_nonnegative m (skipn n l)) as Hskipn_nonneg.
match type of Hskipn_nonneg with
  ?P -> _ => assert P as Q; [ | specialize (Hskipn_nonneg Q); lia ] end.
intros x HIn_skipn.
apply In_skipn in HIn_skipn.
auto.
Qed.

Lemma sum_firstn_prefix_le : forall l n m, (forall x, In x l -> (0 <= x)%Z) ->
                                            (n <= m)%nat ->
                                            (sum_firstn l n <= sum_firstn l m)%Z.
Proof.
intros l n m H H0.
replace m with (n + (m - n))%nat by lia.
auto using sum_firstn_prefix_le'.
Qed.

Lemma sum_firstn_pos_lt_succ : forall l n m, (forall x, In x l -> (0 <= x)%Z) ->
                                        (n < length l)%nat ->
                                        (sum_firstn l n < sum_firstn l (S m))%Z ->
                                        (n <= m)%nat.
Proof.
intros l n m H H0 H1.
destruct (le_dec n m); auto.
replace n with (m + (n - m))%nat in H1 by lia.
rewrite sum_firstn_skipn in H1.
rewrite sum_firstn_succ_default in *.
match goal with H : (?a + ?b < ?c + ?a)%Z |- _ => assert (H2 : (b < c)%Z) by lia end.
destruct (lt_dec m (length l)). {
    rewrite skipn_nth_default with (d := 0%Z) in H2 by assumption.
    replace (n - m)%nat with (S (n - S m))%nat in H2 by lia.
    rewrite sum_firstn_succ_cons in H2.
    pose proof (sum_firstn_nonnegative (n - S m) (skipn (S m) l)) as H3.
    match type of H3 with
      ?P -> _ => assert P as Q; [ | specialize (H3 Q); lia ] end.
    intros ? A.
    apply In_skipn in A.
    apply H in A.
    lia.
} {
    rewrite skipn_all, nth_default_out_of_bounds in H2 by lia.
    rewrite sum_firstn_nil in H2; lia.
}
Qed.

Definition NotSum {T} (xs : list T) (v : nat) := True.

Ltac NotSum :=
  lazymatch goal with
  | [ |- NotSum ?xs (length ?xs + _)%nat ] => fail
  | [ |- NotSum _ _ ] => exact I
  end.

Lemma sum_firstn_app_hint : forall xs ys n, NotSum xs n ->
  sum_firstn (xs ++ ys) n = (sum_firstn xs n + sum_firstn ys (n - length xs))%Z.
Proof. auto using sum_firstn_app. Qed.

#[global]
Hint Rewrite sum_firstn_app_hint using solve [ NotSum ] : simpl_sum_firstn.


Lemma nth_default_map2 : forall {A B C} (f : A -> B -> C) ls1 ls2 i d d1 d2,
  nth_default d (map2 f ls1 ls2) i =
    if lt_dec i (min (length ls1) (length ls2))
    then f (nth_default d1 ls1 i) (nth_default d2 ls2 i)
    else d.
Proof.
  induction ls1 as [|a ls1 IHls1], ls2.
  + cbv [map2 length min].
    intros.
    break_match; try lia.
    apply nth_default_nil.
  + cbv [map2 length min].
    intros.
    break_match; try lia.
    apply nth_default_nil.
  + cbv [map2 length min].
    intros.
    break_match; try lia.
    apply nth_default_nil.
  + simpl.
    destruct i.
    - intros. rewrite !nth_default_cons.
      break_match; auto; lia.
    - intros d d1 d2. rewrite !nth_default_cons_S.
      rewrite IHls1 with (d1 := d1) (d2 := d2).
      repeat break_match; auto; lia.
Qed.

Lemma map2_cons : forall A B C (f : A -> B -> C) ls1 ls2 a b,
  map2 f (a :: ls1) (b :: ls2) = f a b :: map2 f ls1 ls2.
Proof.
  reflexivity.
Qed.

Lemma map2_nil_l : forall A B C (f : A -> B -> C) ls2,
  map2 f nil ls2 = nil.
Proof.
  reflexivity.
Qed.

Lemma map2_nil_r : forall A B C (f : A -> B -> C) ls1,
  map2 f ls1 nil = nil.
Proof.
  destruct ls1; reflexivity.
Qed.
Local Hint Resolve map2_nil_r map2_nil_l : core.

Ltac simpl_list_lengths := repeat match goal with
                                  | H : context[length (@nil ?A)] |- _ => rewrite (@nil_length0 A) in H
                                  | H : context[length (_ :: _)] |- _ => rewrite length_cons in H
                                  | |- context[length (@nil ?A)] => rewrite (@nil_length0 A)
                                  | |- context[length (_ :: _)] => rewrite length_cons
                                  end.

Section OpaqueMap2.
  Local Opaque map2.

  Lemma map2_length : forall A B C (f : A -> B -> C) ls1 ls2,
      length (map2 f ls1 ls2) = min (length ls1) (length ls2).
  Proof.
    induction ls1 as [|a ls1 IHls1], ls2; intros; try solve [cbv; auto].
    rewrite map2_cons, !length_cons, IHls1.
    auto.
  Qed.
  Hint Rewrite @map2_length : distr_length.


  Lemma map2_app : forall A B C (f : A -> B -> C) ls1 ls2 ls1' ls2',
      (length ls1 = length ls2) ->
      map2 f (ls1 ++ ls1') (ls2 ++ ls2') = map2 f ls1 ls2 ++ map2 f ls1' ls2'.
  Proof.
    induction ls1 as [|a ls1 IHls1], ls2; intros; rewrite ?map2_nil_r, ?app_nil_l; try congruence;
      simpl_list_lengths; try lia.
    rewrite <-!app_comm_cons, !map2_cons.
    rewrite IHls1; auto.
  Qed.
End OpaqueMap2.
#[global]
Hint Rewrite @map2_length : distr_length.

Lemma firstn_update_nth {A}
  : forall f m n (xs : list A), firstn m (update_nth n f xs) = update_nth n f (firstn m xs).
Proof.
  induction m; destruct n, xs;
    autorewrite with simpl_firstn simpl_update_nth;
    congruence.
Qed.

#[global]
Hint Rewrite @firstn_update_nth : push_firstn.
#[global]
Hint Rewrite @firstn_update_nth : pull_update_nth.
#[global]
Hint Rewrite <- @firstn_update_nth : pull_firstn.
#[global]
Hint Rewrite <- @firstn_update_nth : push_update_nth.

Global Instance fold_right_Proper {A B} : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq ==> eq) (@fold_right A B) | 1.
Proof.
  cbv [pointwise_relation]; intros f g Hfg x y ? ls ls' ?; subst y ls'; revert x.
  induction ls as [|l ls IHls]; cbn [fold_right]; intro; rewrite ?IHls, ?Hfg; reflexivity.
Qed.
Global Instance fold_right_Proper_eq {A B} : Proper ((eq ==> eq ==> eq) ==> eq ==> eq ==> eq) (@fold_right A B) | 1.
Proof. cbv [respectful]; repeat intro; subst; apply fold_right_Proper; repeat intro; eauto. Qed.

Global Instance fold_left_Proper {A B} : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq ==> eq) (@fold_left A B) | 1.
Proof.
  repeat intro; rewrite <- !fold_left_rev_right; apply fold_right_Proper; cbv [pointwise_relation] in *; eauto; congruence.
Qed.
Global Instance fold_left_Proper_eq {A B} : Proper ((eq ==> eq ==> eq) ==> eq ==> eq ==> eq) (@fold_left A B) | 1.
Proof. cbv [respectful]; repeat intro; subst; apply fold_left_Proper; repeat intro; eauto. Qed.

Require Import Coq.Lists.SetoidList.
Global Instance Proper_nth_default : forall A eq,
  Proper (eq==>eqlistA eq==>Logic.eq==>eq) (nth_default (A:=A)).
Proof.
  intros A ee x y H; subst; induction 1.
  + repeat intro; rewrite !nth_default_nil; assumption.
  + intros x1 y0 H2; subst; destruct y0; rewrite ?nth_default_cons, ?nth_default_cons_S; auto.
Qed.

Lemma fold_right_andb_true_map_iff A (ls : list A) f
  : List.fold_right andb true (List.map f ls) = true <-> forall i, List.In i ls -> f i = true.
Proof.
  induction ls as [|a ls IHls]; simpl; [ | rewrite Bool.andb_true_iff, IHls ]; try tauto.
  intuition (congruence || eauto).
Qed.

Lemma fold_right_andb_true_iff_fold_right_and_True (ls : list bool)
  : List.fold_right andb true ls = true <-> List.fold_right and True (List.map (fun b => b = true) ls).
Proof.
  rewrite <- (map_id ls) at 1.
  rewrite fold_right_andb_true_map_iff, fold_right_and_True_forall_In_iff; reflexivity.
Qed.

Lemma fold_left_andb_true_map_iff A (ls : list A) f
  : List.fold_left andb (List.map f ls) true = true <-> forall i, List.In i ls -> f i = true.
Proof.
  rewrite <- fold_left_rev_right, <- map_rev; setoid_rewrite Bool.andb_comm.
  rewrite fold_right_andb_true_map_iff.
  setoid_rewrite <- in_rev; reflexivity.
Qed.

Lemma fold_left_andb_true_iff_fold_left_and_True (ls : list bool)
  : List.fold_left andb ls true = true <-> List.fold_left and (List.map (fun b => b = true) ls) True.
Proof.
  rewrite <- (map_id ls) at 1.
  rewrite fold_left_andb_true_map_iff, fold_left_and_True_forall_In_iff; reflexivity.
Qed.

Lemma fold_right_andb_truth_map_iff A (ls : list A) f t
  : List.fold_right andb t (List.map f ls) = true <-> (t = true /\ forall i, List.In i ls -> f i = true).
Proof.
  induction ls as [|a ls IHls]; simpl; [ | rewrite Bool.andb_true_iff, IHls ]; try tauto.
  intuition (congruence || eauto).
Qed.

Lemma fold_right_andb_truth_iff_fold_right_and_Truth (ls : list bool) t
  : List.fold_right andb t ls = true <-> List.fold_right and (t = true) (List.map (fun b => b = true) ls).
Proof.
  rewrite <- (map_id ls) at 1.
  rewrite fold_right_andb_truth_map_iff, fold_right_and_Truth_forall_In_iff; reflexivity.
Qed.

Lemma fold_left_andb_truth_map_iff A (ls : list A) f t
  : List.fold_left andb (List.map f ls) t = true <-> (t = true /\ forall i, List.In i ls -> f i = true).
Proof.
  rewrite <- fold_left_rev_right, <- map_rev; setoid_rewrite Bool.andb_comm.
  rewrite fold_right_andb_truth_map_iff.
  setoid_rewrite <- in_rev; reflexivity.
Qed.

Lemma fold_left_andb_truth_iff_fold_left_and_Truth (ls : list bool) t
  : List.fold_left andb ls t = true <-> List.fold_left and (List.map (fun b => b = true) ls) (t = true).
Proof.
  rewrite <- (map_id ls) at 1.
  rewrite fold_left_andb_truth_map_iff, fold_left_and_Truth_forall_In_iff; reflexivity.
Qed.

Lemma Forall2_forall_iff : forall {A B} (R : A -> B -> Prop) (xs : list A) (ys : list B) d1 d2, length xs = length ys ->
  (Forall2 R xs ys <-> (forall i, (i < length xs)%nat -> R (nth_default d1 xs i) (nth_default d2 ys i))).
Proof.
  intros A B R xs ys d1 d2 H; split; [ intros H0 i H1 | intros H0 ].

  + revert xs ys H H0 H1.
    induction i as [|i IHi]; intros xs ys H H0 H1; destruct H0; distr_length; autorewrite with push_nth_default; auto.
    eapply IHi; auto. lia.
  + revert xs ys H H0; induction xs as [|a xs IHxs]; intros ys H H0; destruct ys; distr_length; econstructor.
    - specialize (H0 0%nat).
      autorewrite with push_nth_default in *; auto.
      apply H0; lia.
    - apply IHxs; try lia.
      intros i H1.
      specialize (H0 (S i)).
      autorewrite with push_nth_default in *; auto.
      apply H0; lia.
Qed.

Lemma Forall2_forall_iff' : forall {A} R (xs ys : list A) d, length xs = length ys ->
  (Forall2 R xs ys <-> (forall i, (i < length xs)%nat -> R (nth_default d xs i) (nth_default d ys i))).
Proof. intros; apply Forall2_forall_iff; assumption. Qed.

Lemma nth_default_firstn : forall {A} (d : A) l i n,
  nth_default d (firstn n l) i = if le_dec n (length l)
                                 then if lt_dec i n then nth_default d l i else d
                                 else nth_default d l i.
Proof.
  intros A d l i; induction n as [|n IHn]; break_match; autorewrite with push_nth_default; auto; try lia.
  + rewrite (firstn_succ d) by lia.
    autorewrite with push_nth_default; repeat (break_match_hyps; break_match; distr_length);
      rewrite Min.min_l in * by lia; try lia.
    - apply IHn; lia.
    - replace i with n in * by lia.
      rewrite Nat.sub_diag.
      autorewrite with push_nth_default; auto.
  + rewrite nth_default_out_of_bounds; break_match_hyps; distr_length; auto; lia.
  + rewrite firstn_all2 by lia.
    auto.
Qed.
#[global]
Hint Rewrite @nth_default_firstn : push_nth_default.

Lemma nth_error_repeat {T} x n i v : nth_error (@repeat T x n) i = Some v -> v = x.
Proof.
  revert n x v; induction i as [|i IHi]; destruct n; simpl in *; eauto; congruence.
Qed.

#[global]
Hint Rewrite repeat_length : distr_length.

Lemma repeat_spec_iff : forall {A} (ls : list A) x n,
    (length ls = n /\ forall y, In y ls -> y = x) <-> ls = repeat x n.
Proof.
  intros A ls x n; split; [ revert A ls x n | intro; subst; eauto using repeat_length, repeat_spec ].
  induction ls as [|a ls IHls], n; simpl; intros; intuition try congruence.
  f_equal; auto.
Qed.

Lemma repeat_spec_eq : forall {A} (ls : list A) x n,
    length ls = n
    -> (forall y, In y ls -> y = x)
    -> ls = repeat x n.
Proof.
  intros; apply repeat_spec_iff; auto.
Qed.

Lemma tl_repeat {A} x n : tl (@repeat A x n) = repeat x (pred n).
Proof. destruct n; reflexivity. Qed.

Lemma firstn_repeat : forall {A} x n k, firstn k (@repeat A x n) = repeat x (min k n).
Proof. induction n, k; boring. Qed.

#[global]
Hint Rewrite @firstn_repeat : push_firstn.

Lemma skipn_repeat : forall {A} x n k, skipn k (@repeat A x n) = repeat x (n - k).
Proof. induction n, k; boring. Qed.

#[global]
Hint Rewrite @skipn_repeat : push_skipn.

Global Instance Proper_map {A B} {RA RB} {Equivalence_RB:Equivalence RB}
  : Proper ((RA==>RB) ==> eqlistA RA ==> eqlistA RB) (@List.map A B).
Proof.
  repeat intro.
  match goal with [H:eqlistA _ _ _ |- _ ] => induction H end; [reflexivity|].
  cbv [respectful] in *; econstructor; eauto.
Qed.

Lemma pointwise_map {A B} : Proper ((pointwise_relation _ eq) ==> eq ==> eq) (@List.map A B).
Proof.
  repeat intro; cbv [pointwise_relation] in *; subst.
  match goal with [H:list _ |- _ ] => induction H as [|? IH IHIH] end; [reflexivity|].
  simpl. rewrite IHIH. congruence.
Qed.

Lemma map_map2 {A B C D} (f:A -> B -> C) (g:C -> D) (xs:list A) (ys:list B) : List.map g (map2 f xs ys) = map2 (fun (a : A) (b : B) => g (f a b)) xs ys.
Proof.
  revert ys; induction xs as [|a xs IHxs]; intros ys; [reflexivity|].
  destruct ys; [reflexivity|].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma map2_fst {A B C} (f:A -> C) (xs:list A) : forall (ys:list B), length xs = length ys ->
  map2 (fun (a : A) (_ : B) => f a) xs ys = List.map f xs.
Proof.
  induction xs as [|a xs IHxs]; intros ys **; [reflexivity|].
  destruct ys; [simpl in *; discriminate|].
  simpl. rewrite IHxs by eauto. reflexivity.
Qed.

Lemma map2_flip {A B C} (f:A -> B -> C) (xs:list A) : forall (ys: list B),
   map2 (fun b a => f a b) ys xs = map2 f xs ys.
Proof.
  induction xs as [|a xs IHxs]; destruct ys; try reflexivity; [].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma map2_snd {A B C} (f:B -> C) (xs:list A) : forall (ys:list B), length xs = length ys ->
  map2 (fun (_ : A) (b : B) => f b) xs ys = List.map f ys.
Proof. intros. rewrite map2_flip. eauto using map2_fst. Qed.

Lemma map2_map {A B C A' B'} (f:A -> B -> C) (g:A' -> A) (h:B' -> B) (xs:list A') (ys:list B')
  : map2 f (List.map g xs) (List.map h ys) = map2 (fun a b => f (g a) (h b)) xs ys.
Proof.
  revert ys; induction xs as [|a xs IHxs]; destruct ys; intros; try reflexivity; [].
  simpl. rewrite IHxs. reflexivity.
Qed.

Definition expand_list_helper {A} (default : A) (ls : list A) (n : nat) (idx : nat) : list A
  := nat_rect
       (fun _ => nat -> list A)
       (fun _ => nil)
       (fun n' rec_call idx
        => cons (List.nth_default default ls idx) (rec_call (S idx)))
       n
       idx.
Definition expand_list {A} (default : A) (ls : list A) (n : nat) : list A
  := expand_list_helper default ls n 0.

Lemma expand_list_helper_correct {A} (default : A) (ls : list A) (n idx : nat) (H : (idx + n <= length ls)%nat)
  : expand_list_helper default ls n idx
    = List.firstn n (List.skipn idx ls).
Proof.
  cbv [expand_list_helper]; revert idx H.
  induction n as [|n IHn]; cbn; intros.
  { reflexivity. }
  { rewrite IHn by lia.
    erewrite (@skipn_nth_default _ idx ls) by lia.
    reflexivity. }
Qed.

Lemma expand_list_correct (n : nat) {A} (default : A) (ls : list A) (H : List.length ls = n)
  : expand_list default ls n = ls.
Proof.
  subst; cbv [expand_list]; rewrite expand_list_helper_correct by reflexivity.
  rewrite skipn_0, firstn_all; reflexivity.
Qed.

Ltac expand_lists _ :=
  let default_for A :=
      match goal with
      | _ => (eval lazy in (_ : pointed A))
      | _ => constr_fail_with ltac:(fun _ => idtac "Warning: could not infer a default value for list type" A)
      end in
  let T := lazymatch goal with |- _ = _ :> ?T => T end in
  let v := fresh in
  evar (v : T); transitivity v;
  [ subst v
  | repeat match goal with
           | [ H : @List.length ?A ?f = ?n |- context[?f] ]
             => let v := default_for A in
                rewrite <- (@expand_list_correct n A v f H);
                clear H
           end;
    lazymatch goal with
    | [ H : List.length ?f = _ |- context[?f] ]
      => fail 0 "Could not expand list" f
    | _ => idtac
    end;
    subst v; reflexivity ].

Lemma single_list_rect_to_match A (P:list A -> Type) (Pnil: P nil) (PS: forall a tl, P (a :: tl)) ls :
  @list_rect A P Pnil (fun a tl _ => PS a tl) ls = match ls with
                                                   | cons a tl => PS a tl
                                                   | nil => Pnil
                                                   end.
Proof. destruct ls; reflexivity. Qed.

Lemma partition_app A (f : A -> bool) (a b : list A)
  : partition f (a ++ b) = (fst (partition f a) ++ fst (partition f b),
                            snd (partition f a) ++ snd (partition f b)).
Proof.
  revert b; induction a, b; cbn; rewrite ?app_nil_r; eta_expand; try reflexivity.
  rewrite !IHa; cbn; break_match; reflexivity.
Qed.

Lemma flat_map_map A B C (f : A -> B) (g : B -> list C) (xs : list A)
  : flat_map g (map f xs) = flat_map (fun x => g (f x)) xs.
Proof. induction xs; cbn; congruence. Qed.
Lemma flat_map_singleton A B (f : A -> B) (xs : list A)
  : flat_map (fun x => cons (f x) nil) xs = map f xs.
Proof. induction xs; cbn; congruence. Qed.
Lemma flat_map_ext A B (f g : A -> list B) xs (H : forall x, In x xs -> f x = g x)
  : flat_map f xs = flat_map g xs.
Proof. induction xs; cbn in *; [ reflexivity | rewrite IHxs; f_equal ]; intros; intuition auto. Qed.
Global Instance flat_map_Proper A B : Proper (pointwise_relation _ eq ==> eq ==> eq) (@flat_map A B).
Proof. repeat intro; subst; apply flat_map_ext; auto. Qed.

Global Instance map_Proper_eq {A B} : Proper ((eq ==> eq) ==> eq ==> eq) (@List.map A B) | 1.
Proof. repeat intro; subst; apply pointwise_map; repeat intro; eauto. Qed.
Global Instance flat_map_Proper_eq {A B} : Proper ((eq ==> eq) ==> eq ==> eq) (@List.flat_map A B) | 1.
Proof. repeat intro; subst; apply flat_map_Proper; repeat intro; eauto. Qed.
Global Instance partition_Proper {A} : Proper (pointwise_relation _ eq ==> eq ==> eq) (@List.partition A).
Proof.
  cbv [pointwise_relation]; intros f g Hfg ls ls' ?; subst ls'.
  induction ls as [|l ls IHls]; cbn [partition]; rewrite ?IHls, ?Hfg; reflexivity.
Qed.
Global Instance partition_Proper_eq {A} : Proper ((eq ==> eq) ==> eq ==> eq) (@List.partition A) | 1.
Proof. repeat intro; subst; apply partition_Proper; repeat intro; eauto. Qed.

Lemma partition_map A B (f : B -> bool) (g : A -> B) xs
  : partition f (map g xs) = (map g (fst (partition (fun x => f (g x)) xs)),
                              map g (snd (partition (fun x => f (g x)) xs))).
Proof. induction xs; cbn; [ | rewrite !IHxs ]; break_match; reflexivity. Qed.
Lemma map_fst_partition A B (f : B -> bool) (g : A -> B) xs
  : map g (fst (partition (fun x => f (g x)) xs)) = fst (partition f (map g xs)).
Proof. rewrite partition_map; reflexivity. Qed.
Lemma map_snd_partition A B (f : B -> bool) (g : A -> B) xs
  : map g (snd (partition (fun x => f (g x)) xs)) = snd (partition f (map g xs)).
Proof. rewrite partition_map; reflexivity. Qed.
Lemma partition_In A (f:A -> bool) xs : forall x, @In A x xs <-> @In A x (if f x then fst (partition f xs) else snd (partition f xs)).
Proof.
  intro x; destruct (f x) eqn:?; split; intros; repeat apply conj; revert dependent x;
    (induction xs as [|x' xs IHxs]; cbn; [ | destruct (f x') eqn:?, (partition f xs) ]; cbn in *; subst; intuition (subst; auto));
    congruence.
Qed.
Lemma fst_partition_In A f xs : forall x, @In A x (fst (partition f xs)) <-> f x = true /\ @In A x xs.
Proof.
  intro x; split; intros; repeat apply conj; revert dependent x;
    (induction xs as [|x' xs IHxs]; cbn; [ | destruct (f x') eqn:?, (partition f xs) ]; cbn in *; subst; intuition (subst; auto));
    congruence.
Qed.
Lemma snd_partition_In A f xs : forall x, @In A x (snd (partition f xs)) <-> f x = false /\ @In A x xs.
Proof.
  intro x; split; intros; repeat apply conj; revert dependent x;
    (induction xs as [|x' xs IHxs]; cbn; [ | destruct (f x') eqn:?, (partition f xs) ]; cbn in *; subst; intuition (subst; auto));
    congruence.
Qed.

Lemma list_rect_map A B P (f : A -> B) N C ls
  : @list_rect B P N C (map f ls) = @list_rect A (fun ls => P (map f ls)) N (fun x xs rest => C (f x) (map f xs) rest) ls.
Proof. induction ls as [|x xs IHxs]; cbn; [ | rewrite IHxs ]; reflexivity. Qed.
Lemma flat_map_app A B (f : A -> list B) xs ys
  : flat_map f (xs ++ ys) = flat_map f xs ++ flat_map f ys.
Proof. induction xs as [|x xs IHxs]; cbn; rewrite ?IHxs, <- ?app_assoc; reflexivity. Qed.
#[global]
Hint Rewrite flat_map_app : push_flat_map.
Lemma map_flat_map A B C (f : A -> list B) (g : B -> C) xs
  : map g (flat_map f xs) = flat_map (fun x => map g (f x)) xs.
Proof. induction xs as [|x xs IHxs]; cbn; rewrite ?map_app; congruence. Qed.

Lemma flat_map_rev A B (f : A -> list B) xs
  : flat_map f (rev xs) = rev (flat_map (fun x => rev (f x)) xs).
Proof.
  induction xs as [|x xs IHxs]; cbn; autorewrite with push_flat_map; rewrite ?rev_app_distr, ?IHxs, ?rev_involutive, ?app_nil_r; reflexivity.
Qed.
#[global]
Hint Rewrite flat_map_rev : push_flat_map.

Lemma rev_flat_map A B (f : A -> list B) xs
  : rev (flat_map f xs) = flat_map (fun x => rev (f x)) (rev xs).
Proof. rewrite flat_map_rev; setoid_rewrite rev_involutive; reflexivity. Qed.
#[global]
Hint Rewrite rev_flat_map : push_rev.

Lemma combine_map_map A B C D (f : A -> B) (g : C -> D) xs ys
  : combine (map f xs) (map g ys) = map (fun ab => (f (fst ab), g (snd ab))) (combine xs ys).
Proof. revert ys; induction xs, ys; cbn; congruence. Qed.
Lemma combine_map_l A B C (f : A -> B) xs ys
  : @combine B C (map f xs) ys = map (fun ab => (f (fst ab), snd ab)) (combine xs ys).
Proof. rewrite <- combine_map_map with (f:=f) (g:=fun x => x), map_id; reflexivity. Qed.
Lemma combine_map_r A B C (f : B -> C) xs ys
  : @combine A C xs (map f ys) = map (fun ab => (fst ab, f (snd ab))) (combine xs ys).
Proof. rewrite <- combine_map_map with (g:=f) (f:=fun x => x), map_id; reflexivity. Qed.
Lemma combine_same A xs
  : @combine A A xs xs = map (fun x => (x, x)) xs.
Proof. induction xs; cbn; congruence. Qed.
Lemma if_singleton A (b:bool) (x y : A) : (if b then x::nil else y::nil) = (if b then x else y)::nil.
Proof. now case b. Qed.
Lemma flat_map_if_In A B (b : A -> bool) (f g : A -> list B) xs (b' : bool)
  : (forall v, In v xs -> b v = b') -> flat_map (fun x => if b x then f x else g x) xs = if b' then flat_map f xs else flat_map g xs.
Proof. induction xs as [|x xs IHxs]; cbn; [ | intro H; rewrite IHxs, H by eauto ]; case b'; reflexivity. Qed.
Lemma flat_map_if_In_sumbool A B X Y (b : forall a : A, sumbool (X a) (Y a)) (f g : A -> list B) xs (b' : bool)
  : (forall v, In v xs -> (if b v then true else false) = b') -> flat_map (fun x => if b x then f x else g x) xs = if b' then flat_map f xs else flat_map g xs.
Proof.
  intro H; erewrite <- flat_map_if_In by refine H.
  apply flat_map_Proper; [ intro | reflexivity ]; break_innermost_match; reflexivity.
Qed.
Lemma map_if_In A B (b : A -> bool) (f g : A -> B) xs (b' : bool)
  : (forall v, In v xs -> b v = b') -> map (fun x => if b x then f x else g x) xs = if b' then map f xs else map g xs.
Proof. induction xs as [|x xs IHxs]; cbn; [ | intro H; rewrite IHxs, H by eauto ]; case b'; reflexivity. Qed.
Lemma map_if_In_sumbool A B X Y (b : forall a : A, sumbool (X a) (Y a)) (f g : A -> B) xs (b' : bool)
  : (forall v, In v xs -> (if b v then true else false) = b') -> map (fun x => if b x then f x else g x) xs = if b' then map f xs else map g xs.
Proof.
  intro H; erewrite <- map_if_In by refine H.
  apply map_ext_in; intro; break_innermost_match; reflexivity.
Qed.
Lemma fold_right_map A B C (f : A -> B) xs (F : _ -> _ -> C) v
  : fold_right F v (map f xs) = fold_right (fun x y => F (f x) y) v xs.
Proof. revert v; induction xs; cbn; intros; congruence. Qed.
Lemma fold_right_flat_map A B C (f : A -> list B) xs (F : _ -> _ -> C) v
  : fold_right F v (flat_map f xs) = fold_right (fun x y => fold_right F y (f x)) v xs.
Proof. revert v; induction xs; cbn; intros; rewrite ?fold_right_app; congruence. Qed.

Lemma fold_right_ext_in A B f g v xs : (forall x y, List.In x xs -> f x y = g x y) -> @fold_right A B f v xs = fold_right g v xs.
Proof. induction xs; cbn; intro H; rewrite ?H, ?IHxs; auto. Qed.
Lemma fold_right_ext A B f g v xs : (forall x y, f x y = g x y) -> @fold_right A B f v xs = fold_right g v xs.
Proof. intros; apply fold_right_ext_in; eauto. Qed.

Lemma fold_right_id_ext A B f v xs : (forall x y, f x y = y) -> @fold_right A B f v xs = v.
Proof. induction xs; cbn; intro H; rewrite ?H; auto. Qed.
Lemma fold_left_map A B C f f' l a
  : @fold_left A B f (@List.map C _ f' l) a = fold_left (fun x y => f x (f' y)) l a.
Proof. revert a; induction l; cbn [List.map List.fold_left]; auto. Qed.
Lemma fold_left_flat_map A B C (f : A -> list B) xs (F : _ -> _ -> C) v
  : fold_left F (flat_map f xs) v = fold_left (fun x y => fold_left F (f y) x) xs v.
Proof. revert v; induction xs; cbn; intros; rewrite ?fold_left_app; congruence. Qed.

Lemma fold_left_ext_in A B f g v xs : (forall x y, List.In y xs -> f x y = g x y) -> @fold_left A B f xs v = fold_left g xs v.
Proof. intros; rewrite <- !fold_left_rev_right; apply fold_right_ext_in; intros *; rewrite <- in_rev; eauto. Qed.
Lemma fold_left_ext A B f g v xs : (forall x y, f x y = g x y) -> @fold_left A B f v xs = fold_left g v xs.
Proof. intros; apply fold_left_ext_in; eauto. Qed.

Lemma fold_left_id_ext A B f v xs : (forall x y, f x y = x) -> @fold_left A B f xs v = v.
Proof. induction xs; cbn; intro H; rewrite ?H; auto. Qed.
Lemma nth_error_repeat_alt {A} (v : A) n i
  : nth_error (repeat v n) i = if dec (i < n)%nat then Some v else None.
Proof.
  revert i; induction n as [|n IHn], i; cbn; try reflexivity.
  cbn [nth_error]; rewrite IHn; do 2 edestruct dec; try reflexivity; lia.
Qed.
Lemma nth_default_repeat A (v:A) n (d:A) i : nth_default d (repeat v n) i = if dec (i < n)%nat then v else d.
Proof.
  cbv [nth_default]; rewrite nth_error_repeat_alt; now break_innermost_match.
Qed.
#[global]
Hint Rewrite nth_default_repeat : push_nth_default simpl_nth_default.
Lemma fold_right_if_dec_eq_seq A start len i f (x v : A)
  : ((start <= i < start + len)%nat -> f i v = x)
    -> (forall j v, (i <> j)%nat -> f j v = v)
    -> fold_right f v (seq start len) = if dec (start <= i < start + len)%nat then x else v.
Proof.
  revert start v; induction len as [|len IHlen]; intros start v H H'; [ | rewrite seq_snoc, fold_right_app; cbn [fold_right] ].
  { edestruct dec; try reflexivity; lia. }
  { destruct (dec (i = (start + len)%nat)); subst; [ | rewrite H' by lia ];
      rewrite IHlen; eauto; intros; clear IHlen;
        repeat match goal with
               | _ => reflexivity
               | _ => lia
               | _ => progress subst
               | _ => progress specialize_by lia
               | [ H : context[dec ?P] |- _ ] => destruct (dec P)
               | [ |- context[dec ?P] ] => destruct (dec P)
               | [ H : f _ _ = _ |- _ ] => rewrite H
               | [ H : forall j, f j ?v = _ |- context[f _ ?v] ] => rewrite H
               end. }
Qed.

Lemma fold_left_if_dec_eq_seq A start len i f (x v : A)
  : ((start <= i < start + len)%nat -> f v i = x)
    -> (forall j v, (i <> j)%nat -> f v j = v)
    -> fold_left f (seq start len) v = if dec (start <= i < start + len)%nat then x else v.
Proof.
  revert start v; induction len as [|len IHlen]; intros start v H H'; [ | rewrite seq_snoc, fold_left_app; cbn [fold_left] ].
  { edestruct dec; try reflexivity; lia. }
  { destruct (dec (i = (start + len)%nat)); subst; [ | rewrite H' by lia ];
      rewrite IHlen; eauto; intros; clear IHlen;
        repeat match goal with
               | _ => reflexivity
               | _ => lia
               | _ => progress subst
               | _ => progress specialize_by lia
               | [ H : context[dec ?P] |- _ ] => destruct (dec P)
               | [ |- context[dec ?P] ] => destruct (dec P)
               | [ H : f _ _ = _ |- _ ] => rewrite H
               | [ H : forall j, f j ?v = _ |- context[f _ ?v] ] => rewrite H
               end. }
Qed.

Lemma fold_left_push A (x y : A) (f : A -> A -> A)
      (f_assoc : forall x y z, f (f x y) z = f x (f y z))
      ls
  : f x (fold_left f ls y) = fold_left f ls (f x y).
Proof.
  revert x y; induction ls as [|l ls IHls]; cbn; [ reflexivity | ].
  intros; rewrite IHls; f_equal; auto.
Qed.

Lemma fold_right_push A (x y : A) (f : A -> A -> A)
      (f_assoc : forall x y z, f (f x y) z = f x (f y z))
      ls
  : f (fold_right f x ls) y = fold_right f (f x y) ls.
Proof.
  rewrite <- (rev_involutive ls), !fold_left_rev_right, fold_left_push with (f:=fun x y => f y x); auto.
Qed.

Lemma nth_error_combine {A B} n (ls1 : list A) (ls2 : list B)
  : nth_error (combine ls1 ls2) n = match nth_error ls1 n, nth_error ls2 n with
                                    | Some v1, Some v2 => Some (v1, v2)
                                    | _, _ => None
                                    end.
Proof.
  revert ls2 n; induction ls1 as [|l1 ls1 IHls1], ls2, n; cbn [combine nth_error]; try reflexivity; auto.
  edestruct nth_error; reflexivity.
Qed.

Lemma combine_repeat {A B} (a : A) (b : B) n : combine (repeat a n) (repeat b n) = repeat (a, b) n.
Proof. induction n; cbn; congruence. Qed.

Lemma combine_rev_rev_samelength {A B} ls1 ls2 : length ls1 = length ls2 -> @combine A B (rev ls1) (rev ls2) = rev (combine ls1 ls2).
Proof.
  revert ls2; induction ls1 as [|? ? IHls1], ls2; cbn in *; try congruence; intros.
  rewrite combine_app_samelength, IHls1 by (rewrite ?rev_length; congruence); cbn [combine].
  reflexivity.
Qed.

Lemma map_nth_default_seq {A} (d:A) n ls
  : length ls = n -> List.map (List.nth_default d ls) (List.seq 0 n) = ls.
Proof.
  intro; subst.
  rewrite <- (List.rev_involutive ls); generalize (List.rev ls); clear ls; intro ls.
  rewrite List.rev_length.
  induction ls; cbn [length List.rev]; [ reflexivity | ].
  rewrite seq_snoc, List.map_app.
  apply f_equal2; [ | cbn; rewrite nth_default_app, List.rev_length, Nat.sub_diag ];
    [ etransitivity; [ | eassumption ]; apply List.map_ext_in; intro; rewrite Lists.List.in_seq;
      rewrite nth_default_app, List.rev_length; intros
    | ].
  all: edestruct lt_dec; try (exfalso; lia).
  all: reflexivity.
Qed.

Lemma nth_error_firstn A ls n i
  : List.nth_error (@List.firstn A n ls) i = if lt_dec i n then List.nth_error ls i else None.
Proof.
  revert ls i; induction n, ls, i; cbn; try reflexivity; destruct lt_dec; try reflexivity; rewrite IHn.
  all: destruct lt_dec; try reflexivity; lia.
Qed.

Lemma nth_error_rev A n ls : List.nth_error (@List.rev A ls) n = if lt_dec n (length ls) then List.nth_error ls (length ls - S n) else None.
Proof.
  destruct lt_dec; [ | rewrite nth_error_length_error; rewrite ?List.rev_length; try reflexivity; lia ].
  revert dependent n; induction ls as [|x xs IHxs]; cbn [length List.rev]; try reflexivity; intros; try lia.
  { rewrite nth_error_app, List.rev_length, Nat.sub_succ.
    destruct lt_dec.
    { rewrite IHxs by lia.
      rewrite <- (Nat.succ_pred_pos (length xs - n)) by lia.
      cbn [List.nth_error].
      f_equal; lia. }
    { assert (n = length xs) by lia; subst.
      rewrite Nat.sub_diag.
      reflexivity. } }
Qed.

Lemma concat_fold_right_app A ls
  : @List.concat A ls = List.fold_right (@List.app A) nil ls.
Proof. induction ls; cbn; eauto. Qed.

Lemma map_update_nth_ext {A B n} f1 f2 f3 ls1 ls2
  : map f3 ls1 = ls2
    -> (forall x, List.In x ls1 -> f3 (f2 x) = f1 (f3 x))
    -> map f3 (@update_nth A n f2 ls1) = @update_nth B n f1 ls2.
Proof.
  revert ls1 ls2; induction n as [|n IHn], ls1 as [|x1 xs1], ls2 as [|x2 xs2]; cbn; intros H0 H1; try discriminate; try reflexivity.
  all: inversion H0; clear H0; subst.
  all: f_equal; eauto using or_introl.
Qed.

Lemma push_f_list_rect {P P'} (f : P -> P') {A} Pnil Pcons Pcons' ls
      (Hcons : forall x xs rec, f (Pcons x xs rec)
                                = Pcons' x xs (f rec))
  : f (list_rect (fun _ : list A => P) Pnil Pcons ls)
    = list_rect
        (fun _ => _)
        (f Pnil)
        Pcons'
        ls.
Proof.
  induction ls as [|x xs IHxs]; cbn [list_rect]; [ reflexivity | ].
  rewrite Hcons, IHxs; reflexivity.
Qed.

Lemma eq_app_list_rect {A} (ls1 ls2 : list A)
  : List.app ls1 ls2 = list_rect _ ls2 (fun x _ rec => x :: rec) ls1.
Proof. revert ls2; induction ls1, ls2; cbn; f_equal; eauto. Qed.
Lemma eq_flat_map_list_rect {A B} f (ls : list A)
  : @flat_map A B f ls = list_rect _ nil (fun x _ rec => f x ++ rec) ls.
Proof. induction ls; cbn; eauto. Qed.
Lemma eq_partition_list_rect {A} f (ls : list A)
  : @partition A f ls = list_rect _ (nil, nil) (fun x _ '(a, b) => bool_rect (fun _ => _) (x :: a, b) (a, x :: b) (f x)) ls.
Proof. induction ls; cbn; eauto. Qed.
Lemma eq_fold_right_list_rect {A B} f v (ls : list _)
  : @fold_right A B f v ls = list_rect _ v (fun x _ rec => f x rec) ls.
Proof. induction ls; cbn; eauto. Qed.
Lemma eq_fold_left_list_rect {A B} f v (ls : list _)
  : @fold_left A B f ls v = list_rect _ (fun v => v) (fun x _ rec v => rec (f v x)) ls v.
Proof. revert f v; induction ls; cbn; eauto. Qed.
Lemma eq_map_list_rect {A B} f (ls : list _)
  : @List.map A B f ls = list_rect _ nil (fun x _ rec => f x :: rec) ls.
Proof. induction ls; cbn; eauto. Qed.
Lemma eq_flat_map_fold_right {A B} f (ls : list A)
  : @flat_map A B f ls = fold_right (fun x y => f x ++ y) nil ls.
Proof. induction ls; cbn; eauto. Qed.
Lemma eq_flat_map_fold_left_gen {A B} f (ls : list A) ls'
  : fold_left (fun x y => x ++ f y) ls ls' = ls' ++ @flat_map A B f ls.
Proof. revert ls'; induction ls; cbn; intros; rewrite ?app_nil_r, ?IHls, ?app_assoc; eauto. Qed.
Lemma eq_flat_map_fold_left {A B} f (ls : list A)
  : @flat_map A B f ls = fold_left (fun x y => x ++ f y) ls nil.
Proof. rewrite eq_flat_map_fold_left_gen; reflexivity. Qed.

Lemma map_repeat {A B} (f : A -> B) v k
  : List.map f (List.repeat v k) = List.repeat (f v) k.
Proof. induction k; cbn; f_equal; assumption. Qed.
Lemma map_const {A B} (v : B) (ls : list A)
  : List.map (fun _ => v) ls = List.repeat v (List.length ls).
Proof. induction ls; cbn; f_equal; assumption. Qed.

Lemma Forall2_rev {A B R ls1 ls2}
  : @List.Forall2 A B R ls1 ls2
    -> List.Forall2 R (rev ls1) (rev ls2).
Proof using Type.
  induction 1; cbn [rev]; [ constructor | ].
  apply Forall2_app; auto.
Qed.

Lemma Forall2_update_nth {A B f g n R ls1 ls2}
  : @List.Forall2 A B R ls1 ls2
    -> (forall v1, nth_error ls1 n = Some v1 -> forall v2, nth_error ls2 n = Some v2 -> R v1 v2 -> R (f v1) (g v2))
    -> @List.Forall2 A B R (update_nth n f ls1) (update_nth n g ls2).
Proof using Type.
  intro H; revert n; induction H, n; cbn [nth_error update_nth].
  all: repeat first [ progress intros
                    | progress specialize_by_assumption
                    | assumption
                    | match goal with
                      | [ |- List.Forall2 _ _ _ ] => constructor
                      | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
                      | [ IH : forall n : nat, _, H : forall v1, nth_error ?l ?n = Some v1 -> _ |- _ ] => specialize (IH n H)
                      end ].
Qed.

Fixpoint remove_duplicates' {A} (beq : A -> A -> bool) (ls : list A) : list A
  := match ls with
     | nil => nil
     | cons x xs => if existsb (beq x) xs
                    then @remove_duplicates' A beq xs
                    else x :: @remove_duplicates' A beq xs
     end.
Definition remove_duplicates {A} (beq : A -> A -> bool) (ls : list A) : list A
  := List.rev (remove_duplicates' beq (List.rev ls)).
Fixpoint find_duplicates' {A} (beq : A -> A -> bool) (ls : list A) : list A
  := match ls with
     | nil => nil
     | cons x xs => if existsb (beq x) xs
                    then x :: @find_duplicates' A beq xs
                    else @find_duplicates' A beq xs
     end.
Definition find_duplicates {A} (beq : A -> A -> bool) (ls : list A) : list A
  := remove_duplicates beq (find_duplicates' beq ls).

Lemma InA_remove_duplicates'
      {A} (A_beq : A -> A -> bool)
      (R : A -> A -> Prop)
      {R_Transitive : Transitive R}
      (A_bl : forall x y, A_beq x y = true -> R x y)
      (ls : list A)
  : forall x, InA R x (remove_duplicates' A_beq ls) <-> InA R x ls.
Proof using Type.
  induction ls as [|x xs IHxs]; intro y; [ reflexivity | ].
  cbn [remove_duplicates']; break_innermost_match;
    rewrite ?InA_cons, IHxs; [ | reflexivity ].
  split; [ now auto | ].
  intros [?|?]; subst; auto; [].
  rewrite existsb_exists in *.
  destruct_head'_ex; destruct_head'_and.
  match goal with H : _ |- _ => apply A_bl in H end.
  rewrite InA_alt.
  eexists; split; [ | eassumption ].
  etransitivity; eassumption.
Qed.

Lemma InA_remove_duplicates
      {A} (A_beq : A -> A -> bool)
      (R : A -> A -> Prop)
      {R_Transitive : Transitive R}
      (A_bl : forall x y, A_beq x y = true -> R x y)
      (ls : list A)
  : forall x, InA R x (remove_duplicates A_beq ls) <-> InA R x ls.
Proof using Type.
  cbv [remove_duplicates]; intro.
  rewrite InA_rev, InA_remove_duplicates', InA_rev; auto; reflexivity.
Qed.

Lemma InA_eq_In_iff {A} x ls
  : InA eq x ls <-> @List.In A x ls.
Proof using Type.
  rewrite InA_alt.
  repeat first [ progress destruct_head'_and
               | progress destruct_head'_ex
               | progress subst
               | solve [ eauto ]
               | apply conj
               | progress intros ].
Qed.

Lemma NoDupA_eq_NoDup {A} ls
  : @NoDupA A eq ls <-> NoDup ls.
Proof using Type.
  split; intro H; induction H; constructor; eauto;
    (idtac + rewrite <- InA_eq_In_iff + rewrite InA_eq_In_iff); assumption.
Qed.

Lemma in_remove_duplicates'
      {A} (A_beq : A -> A -> bool) (A_bl : forall x y, A_beq x y = true -> x = y)
      (ls : list A)
  : forall x, List.In x (remove_duplicates' A_beq ls) <-> List.In x ls.
Proof using Type.
  intro x; rewrite <- !InA_eq_In_iff; apply InA_remove_duplicates'; eauto; exact _.
Qed.

Lemma in_remove_duplicates
      {A} (A_beq : A -> A -> bool) (A_bl : forall x y, A_beq x y = true -> x = y)
      (ls : list A)
  : forall x, List.In x (remove_duplicates A_beq ls) <-> List.In x ls.
Proof using Type.
  intro x; rewrite <- !InA_eq_In_iff; apply InA_remove_duplicates; eauto; exact _.
Qed.

Lemma NoDupA_remove_duplicates' {A} (A_beq : A -> A -> bool)
      (R : A -> A -> Prop)
      {R_Transitive : Transitive R}
      (A_lb : forall x y, A_beq x y = true -> R x y)
      (A_bl : forall x y, R x y -> A_beq x y = true)
      (ls : list A)
  : NoDupA R (remove_duplicates' A_beq ls).
Proof using Type.
  induction ls as [|x xs IHxs]; [ now constructor | ].
  cbn [remove_duplicates']; break_innermost_match; [ assumption | constructor; auto ]; [].
  intro H'.
  cut (false = true); [ discriminate | ].
  match goal with H : _ = false |- _ => rewrite <- H end.
  rewrite existsb_exists in *.
  rewrite InA_remove_duplicates' in H' by eauto.
  rewrite InA_alt in H'.
  destruct_head'_ex; destruct_head'_and.
  eauto.
Qed.

Lemma NoDupA_remove_duplicates {A} (A_beq : A -> A -> bool)
      (R : A -> A -> Prop)
      {R_Equivalence : Equivalence R}
      (A_lb : forall x y, A_beq x y = true -> R x y)
      (A_bl : forall x y, R x y -> A_beq x y = true)
      (ls : list A)
  : NoDupA R (remove_duplicates A_beq ls).
Proof using Type.
  cbv [remove_duplicates].
  apply NoDupA_rev; [ assumption | ].
  apply NoDupA_remove_duplicates'; auto; exact _.
Qed.

Lemma NoDup_remove_duplicates' {A} (A_beq : A -> A -> bool)
      (R : A -> A -> Prop)
      (A_lb : forall x y, A_beq x y = true -> x = y)
      (A_bl : forall x y, x = y -> A_beq x y = true)
      (ls : list A)
  : NoDup (remove_duplicates' A_beq ls).
Proof using Type.
  apply NoDupA_eq_NoDup, NoDupA_remove_duplicates'; auto; exact _.
Qed.

Lemma NoDup_remove_duplicates {A} (A_beq : A -> A -> bool)
      (A_lb : forall x y, A_beq x y = true -> x = y)
      (A_bl : forall x y, x = y -> A_beq x y = true)
      (ls : list A)
  : NoDup (remove_duplicates A_beq ls).
Proof using Type.
  apply NoDupA_eq_NoDup, NoDupA_remove_duplicates; auto; exact _.
Qed.

Lemma remove_duplicates'_eq_NoDupA {A} (A_beq : A -> A -> bool)
      (R : A -> A -> Prop)
      (A_lb : forall x y, A_beq x y = true -> R x y)
      (ls : list A)
  : NoDupA R ls -> remove_duplicates' A_beq ls = ls.
Proof using Type.
  intro H; induction H as [|x xs H0 H1 IHxs]; [ reflexivity | ].
  cbn [remove_duplicates'].
  rewrite IHxs.
  repeat first [ break_innermost_match_step
               | reflexivity
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | progress rewrite existsb_exists in *
               | progress rewrite InA_alt in *
               | match goal with
                 | [ H : ~(exists x, and _ _) |- _ ]
                   => specialize (fun x H0 H1 => H (ex_intro _ x (conj H0 H1)))
                 end
               | solve [ exfalso; eauto ] ].
Qed.

Lemma remove_duplicates_eq_NoDupA {A} (A_beq : A -> A -> bool)
      (R : A -> A -> Prop)
      {R_equiv : Equivalence R}
      (A_lb : forall x y, A_beq x y = true -> R x y)
      (ls : list A)
  : NoDupA R ls -> remove_duplicates A_beq ls = ls.
Proof using Type.
  cbv [remove_duplicates]; intro.
  erewrite remove_duplicates'_eq_NoDupA by (eauto + apply NoDupA_rev; eauto).
  rewrite rev_involutive; reflexivity.
Qed.

Lemma remove_duplicates'_eq_NoDup {A} (A_beq : A -> A -> bool)
      (A_lb : forall x y, A_beq x y = true -> x = y)
      (ls : list A)
  : NoDup ls -> remove_duplicates' A_beq ls = ls.
Proof using Type.
  intro H; apply remove_duplicates'_eq_NoDupA with (R:=eq); eauto.
  now apply NoDupA_eq_NoDup.
Qed.

Lemma remove_duplicates_eq_NoDup {A} (A_beq : A -> A -> bool)
      (A_lb : forall x y, A_beq x y = true -> x = y)
      (ls : list A)
  : NoDup ls -> remove_duplicates A_beq ls = ls.
Proof using Type.
  intro H; apply remove_duplicates_eq_NoDupA with (R:=eq); eauto; try exact _.
  now apply NoDupA_eq_NoDup.
Qed.

Lemma eq_repeat_nat_rect {A} x n
  : @List.repeat A x n
    = nat_rect _ nil (fun k repeat_k => x :: repeat_k) n.
Proof using Type. induction n; cbn; f_equal; assumption. Qed.

Lemma eq_firstn_nat_rect {A} n ls
  : @List.firstn A n ls
    = nat_rect
        _
        (fun _ => nil)
        (fun n' firstn_n' ls
         => match ls with
            | nil => nil
            | cons x xs => x :: firstn_n' xs
            end)
        n ls.
Proof using Type. revert ls; induction n, ls; cbn; f_equal; auto. Qed.

Lemma eq_skipn_nat_rect {A} n ls
  : @List.skipn A n ls
    = nat_rect
        _
        (fun ls => ls)
        (fun n' skipn_n' ls
         => match ls with
            | nil => nil
            | cons x xs => skipn_n' xs
            end)
        n ls.
Proof using Type. revert ls; induction n, ls; cbn; f_equal; auto. Qed.

Lemma eq_combine_list_rect {A B} xs ys
  : @List.combine A B xs ys
    = list_rect
        _
        (fun _ => nil)
        (fun x xs combine_xs ys
         => match ys with
            | nil => nil
            | y :: ys => (x, y) :: combine_xs ys
            end)
        xs ys.
Proof using Type. revert ys; induction xs, ys; cbn; f_equal; auto. Qed.

Lemma eq_length_list_rect {A} xs
  : @List.length A xs
    = (list_rect _)
        0%nat
        (fun _ xs length_xs => S length_xs)
        xs.
Proof using Type. induction xs; cbn; f_equal; auto. Qed.

Lemma eq_rev_list_rect {A} xs
  : @List.rev A xs
    = (list_rect _)
        nil
        (fun x xs rev_xs => rev_xs ++ [x])
        xs.
Proof using Type. induction xs; cbn; f_equal; auto. Qed.

Lemma eq_update_nth_nat_rect {A} n f xs
  : @update_nth A n f xs
    = (nat_rect _)
        (fun xs => match xs with
                   | nil => nil
                   | x' :: xs' => f x' :: xs'
                   end)
        (fun n' update_nth_n' xs
         => match xs with
            | nil => nil
            | x' :: xs' => x' :: update_nth_n' xs'
            end)
        n
        xs.
Proof using Type. revert xs; induction n, xs; cbn; f_equal; auto. Qed.

Lemma flat_map_const_nil {A B} ls : @flat_map A B (fun _ => nil) ls = nil.
Proof using Type. induction ls; cbn; auto. Qed.

Lemma Forall_map_iff {A B} (f : A -> B) ls P
  : Forall P (List.map f ls) <-> Forall (fun x => P (f x)) ls.
Proof.
  induction ls as [|?? IH]; cbn [List.map]; split; intro H; inversion_clear H; constructor; split_iff; auto.
Qed.

Lemma ForallOrdPairs_map_iff {A B} (f : A -> B) ls P
  : ForallOrdPairs P (List.map f ls) <-> ForallOrdPairs (fun x y => P (f x) (f y)) ls.
Proof.
  pose proof (@Forall_map_iff A B f) as HF.
  induction ls as [|?? IH]; cbn [List.map]; split; intro H; inversion_clear H; constructor; split_iff; auto.
Qed.

Lemma HdRel_map_iff {A B} (f : A -> B) R x xs
  : HdRel R (f x) (List.map f xs) <-> HdRel (fun x y => R (f x) (f y)) x xs.
Proof.
  destruct xs; split; intro H; inversion_clear H; constructor; auto.
Qed.

Lemma Sorted_map_iff {A B} (f : A -> B) R ls
  : Sorted R (List.map f ls) <-> Sorted (fun x y => R (f x) (f y)) ls.
Proof.
  induction ls as [|?? IH]; cbn [List.map]; split; intro H; inversion_clear H;
    constructor; split_iff; auto; now apply HdRel_map_iff.
Qed.

Lemma In_nth_error_iff {A l x}
  : In x l <-> exists n : nat, @nth_error A l n = Some x.
Proof.
  split; [ now apply In_nth_error | intros [? ?]; eapply nth_error_In; eassumption ].
Qed.

Lemma fold_right_fun_apply {A B C} (ls : list B) (f : B -> C -> (A -> C)) init x
  : fold_right (fun b F a => f b (F a) a) init ls x = fold_right (fun b c => f b c x) (init x) ls.
Proof. induction ls as [|?? IH]; cbn; now f_equal. Qed.

Ltac make_fold_right_fun_apply ty :=
  multimatch ty with
  | context[@fold_right ?AC ?B ?f ?init ?ls ?x]
    => let fv := fresh in
       let b := fresh "b" in
       let F := fresh "F" in
       let a := fresh "a" in
       let f := lazymatch
             constr:(
               fun b F a
               => match f b F a return _ with
                  | fv
                    => ltac:(let fv := (eval cbv [fv] in fv) in
                             lazymatch (eval pattern a, (F a), b in fv) with
                             | ?f _ _ _ => refine (fun x y z => f z y x)
                             end)
                  end) with
           | fun _ _ _ => ?f => (eval cbv beta in f)
           | ?f => idtac "failed to eliminate the functional dependencies of" f;
                   fail 0 "failed to eliminate the functional dependencies of" f
           end in
       constr:(@fold_right_fun_apply _ _ _ ls f init x)
  end.

Ltac rewrite_fold_right_fun_apply :=
  match goal with
  | [ H : ?T |- _ ] => let pf := make_fold_right_fun_apply T in
                       rewrite pf in H
  | [ |- ?T ] => let pf := make_fold_right_fun_apply T in
                 rewrite pf
  end.

Lemma fold_left_fun_apply {A B C} (ls : list B) (f : C -> B -> (A -> C)) init x
  : fold_left (fun F b a => f (F a) b a) ls init x = fold_left (fun b c => f b c x) ls (init x).
Proof. rewrite <- !fold_left_rev_right; now rewrite_fold_right_fun_apply. Qed.

Ltac make_fold_left_fun_apply ty :=
  multimatch ty with
  | context[@fold_left ?AC ?B ?f ?ls ?init ?x]
    => let fv := fresh in
       let b := fresh "b" in
       let F := fresh "F" in
       let a := fresh "a" in
       let f := lazymatch
             constr:(
               fun F b a
               => match f F b a return _ with
                  | fv
                    => ltac:(let fv := (eval cbv [fv] in fv) in
                             lazymatch (eval pattern a, b, (F a) in fv) with
                             | ?f _ _ _ => refine (fun x y z => f z y x)
                             end)
                  end) with
           | fun _ _ _ => ?f => (eval cbv beta in f)
           | ?f => idtac "failed to eliminate the functional dependencies of" f;
                   fail 0 "failed to eliminate the functional dependencies of" f
           end in
       constr:(@fold_left_fun_apply _ _ _ ls f init x)
  end.

Ltac rewrite_fold_left_fun_apply :=
  match goal with
  | [ H : ?T |- _ ] => let pf := make_fold_left_fun_apply T in
                       rewrite pf in H
  | [ |- ?T ] => let pf := make_fold_left_fun_apply T in
                 rewrite pf
  end.

Definition span_cps' {A} (f : A -> bool) {T} (k : list A * list A -> T)
  := fix span_cps' (ls : list A) (prefix : list A) : T
    := match ls with
       | nil => k (List.rev prefix, ls)
       | x :: xs => if f x then span_cps' xs (x :: prefix) else k (List.rev prefix, ls)
       end.

Definition span_cps {A} (f : A -> bool) (ls : list A) {T} (k : list A * list A -> T) : T
  := span_cps' f k ls [].

Definition span {A} (f : A -> bool) (ls : list A) : list A * list A
  := span_cps f ls id.
Definition takeWhile {A} (f : A -> bool) (ls : list A) : list A := fst (span f ls).
Definition dropWhile {A} (f : A -> bool) (ls : list A) : list A := snd (span f ls).

Lemma span_cps'_id A f xs T k prefix
  : @span_cps' A f T k xs prefix = k (List.rev prefix ++ fst (span f xs), snd (span f xs)).
Proof.
  revert T k prefix; induction xs as [|?? IH]; intros; cbn; try (rewrite !IH; clear IH); cbv [id]; break_innermost_match; cbn [List.rev fst snd List.app]; rewrite ?List.app_nil_l, ?List.app_nil_r, <- ?List.app_assoc; try reflexivity.
Qed.

Lemma span_cps_id A f xs T k
  : @span_cps A f xs T k = k (span f xs).
Proof. cbv [span_cps]; rewrite span_cps'_id; destruct span; reflexivity. Qed.

Lemma span_nil A f : @span A f nil = (nil, nil).
Proof. reflexivity. Qed.
Lemma span_cons A f x xs : @span A f (x :: xs) = if f x then let '(xs, ys) := span f xs in (x :: xs, ys) else (nil, x :: xs).
Proof. cbv [span span_cps]; cbn; rewrite !span_cps'_id; cbv [id]; reflexivity. Qed.

Lemma span_app {A} f xs
  : fst (@span A f xs) ++ snd (@span A f xs) = xs.
Proof. induction xs; rewrite ?span_nil, ?span_cons; break_innermost_match; boring. Qed.

Lemma takeWhile_app_dropWhile {A} f xs
  : @takeWhile A f xs ++ @dropWhile A f xs = xs.
Proof. apply span_app. Qed.

Lemma filter_fst_span {A} f xs
  : filter f (fst (@span A f xs)) = fst (@span A f xs).
Proof. induction xs; rewrite ?span_nil, ?span_cons; break_innermost_match; boring. Qed.

Lemma filter_takeWhile {A} f xs
  : filter f (@takeWhile A f xs) = @takeWhile A f xs.
Proof. apply filter_fst_span. Qed.

Lemma hd_not_snd_span {A} f xs x
      (H : nth_error (snd (@span A f xs)) 0 = Some x)
  : f x = false.
Proof.
  induction xs.
  all: repeat first [ rewrite !span_nil in *
                    | rewrite !span_cons in *
                    | progress cbn in *
                    | progress cbv [fst snd] in *
                    | congruence
                    | solve [ auto ]
                    | break_innermost_match_hyps_step ].
Qed.


Definition groupBy' {A} (f : A -> A -> bool)
  := fix groupBy' (ls : list A) (prefix : list A) : list (list A)
    := match ls with
       | [] => []
       | x :: xs => span_cps'
                      (f x) (fun '(xs, ys)
                             => (x :: xs) :: match ys with
                                             | [] => []
                                             | _ => groupBy' ys []
                                             end)
                      xs prefix
       end.
Definition groupBy {A} (f : A -> A -> bool) (ls : list A) : list (list A)
  := groupBy' f ls [].

Definition span_cps'_rect A (f : A -> bool) T (k : list A * list A -> T)
           (P : list A -> list A -> T -> Type)
           (Pnil : forall prefix, P nil prefix (k (List.rev prefix, nil)))
           (Pcons_true : forall x xs prefix rv, f x = true -> P xs (x :: prefix) rv -> P (x :: xs) prefix rv)
           (Pcons_false : forall x ls prefix xs, f x = false -> ls = x :: xs -> P ls prefix (k (List.rev prefix, ls)))
  : forall (ls : list A) (prefix : list A), P ls prefix (@span_cps' A f T k ls prefix).
Proof.
  fix span_cps'_rect 1.
  intro ls.
  case_eq ls; [ | intros x xs ]; intros H prefix; cbn [span_cps'].
  { apply Pnil. }
  { destruct (f x) eqn:H'.
    { apply Pcons_true; [ apply H' | apply span_cps'_rect ]. }
    { generalize (Pcons_false x ls prefix xs H' H).
      clear -H; subst ls; exact id. } }
Defined.

Fixpoint concat_groupBy' {A f} ls prefix {struct ls}
  : match ls with
    | nil => List.concat (@groupBy' A f ls prefix) = nil
    | x :: xs
      => List.concat (@groupBy' A f ls prefix) = x :: List.rev prefix ++ xs
    end.
Proof.
  specialize (concat_groupBy' A f).
  destruct ls as [|x xs].
  { reflexivity. }
  { cbn [groupBy'].
    apply span_cps'_rect; cbn [concat List.rev List.app]; clear xs prefix.
    { intros; rewrite ?List.app_nil_l, ?List.app_nil_r; split; reflexivity. }
    { intros *; rewrite ?app_comm_cons, <- ?List.app_assoc; cbn [List.app]; trivial. }
    { intros x' ls xs' prefix' H H'.
      specialize (concat_groupBy' ls); cbv beta iota in *.
      subst ls.
      rewrite concat_groupBy'; cbn.
      reflexivity. } }
Qed.

Lemma concat_groupBy A f ls
  : List.concat (@groupBy A f ls) = ls.
Proof.
  cbv [groupBy]; destruct ls as [|x xs]; [ reflexivity | apply (concat_groupBy' (x :: xs)) ].
Qed.

Lemma eq_filter_nil_Forall_iff {A} f (xs : list A)
  : filter f xs = nil <-> Forall (fun x => f x = false) xs.
Proof. induction xs; cbn; break_innermost_match; boring; inversion_list; inversion_one_head Forall; congruence. Qed.

Definition is_nil {A} (x : list A) : bool
  := match x with
     | nil => true
     | _ => false
     end.

Lemma is_nil_eq_nil_iff {A x} : @is_nil A x = true <-> x = nil.
Proof. destruct x; cbv; split; congruence. Qed.

Lemma find_none_iff {A} (f : A -> bool) (xs : list A) : find f xs = None <-> forall x, In x xs -> f x = false.
Proof.
  split; try apply find_none.
  pose proof (find_some f xs) as H.
  edestruct find; [ specialize (H _ eq_refl) | reflexivity ].
  destruct H as [H1 H2].
  intro H'; specialize (H' _ H1); congruence.
Qed.

Lemma find_none_iff_nth_error {A} (f : A -> bool) (xs : list A) : find f xs = None <-> forall n a, nth_error xs n = Some a -> f a = false.
Proof.
  rewrite find_none_iff.
  setoid_rewrite In_nth_error_iff.
  intuition (destruct_head'_ex; eauto).
Qed.

Lemma find_some_iff {A} (f : A -> bool) (xs : list A) x
  : find f xs = Some x
    <-> exists n, nth_error xs n = Some x /\ f x = true /\ forall n', n' < n -> forall a, nth_error xs n' = Some a -> f a = false.
Proof.
  induction xs as [|y xs IHxs]; cbn [find].
  all: repeat first [ apply conj
                    | progress intros
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress Option.inversion_option
                    | progress break_innermost_match_hyps
                    | progress subst
                    | progress cbn in *
                    | assumption
                    | exists 0; cbn; repeat split; try assumption; (idtac + (intros; exfalso)); lia
                    | progress break_innermost_match
                    | reflexivity
                    | congruence
                    | match goal with
                      | [ H : nth_error nil ?i = _ |- _ ] => is_var i; destruct i
                      | [ H : nth_error (cons _ _) ?i = _ |- _ ] => is_var i; destruct i
                      | [ H : ?T <-> _, H' : ?T |- _ ] => destruct H as [H _]; specialize (H H')
                      | [ H : S ?x < S ?y |- _ ] => assert (x < y) by lia; clear H
                      | [ H : forall a, Some _ = Some a -> _ |- _ ] => specialize (H _ eq_refl)
                      | [ H : forall a, Some a = Some _ -> _ |- _ ] => specialize (H _ eq_refl)
                      | [ H : forall n, n < S ?v -> @?P n |- _ ]
                        => assert (forall n, n < v -> P (S n)) by (intros ? ?; apply H; lia);
                           specialize (H 0 ltac:(lia))
                      end
                    | eexists (S _); cbn; repeat apply conj; [ eassumption | .. ]; try assumption; intros [|?]
                    | progress split_iff
                    | solve [ eauto with nocore ]
                    | progress specialize_by eauto ].
Qed.

Section find_index.
  Context {A} (f : A -> bool).

  Definition find_index (xs : list A) : option nat
    := option_map (@fst _ _) (find (fun v => f (snd v)) (enumerate xs)).

  Lemma find_index_none_iff xs
    : find_index xs = None <-> forall i a, nth_error xs i = Some a -> f a = false.
  Proof using Type.
    cbv [find_index enumerate].
    edestruct find eqn:H; cbn; [ split; [ congruence | ] | split; [ intros _ | reflexivity ] ].
    { rewrite find_some_iff in H.
      destruct H as [n H]; intro H'; specialize (H' n).
      rewrite nth_error_combine, nth_error_seq in H.
      break_innermost_match_hyps; destruct_head'_and; Option.inversion_option; subst; cbn in *.
      specialize (H' _ eq_refl); congruence. }
    { rewrite find_none_iff_nth_error in H.
      intros n a; specialize (H n (n, a)).
      rewrite nth_error_combine, nth_error_seq in H.
      edestruct lt_dec; [ | rewrite nth_error_length_error by lia; congruence ].
      edestruct nth_error eqn:?; intros; Option.inversion_option; subst; specialize (H eq_refl); assumption. }
  Qed.

  Lemma find_index_some_iff xs n
    : find_index xs = Some n
      <-> ((exists x, nth_error xs n = Some x /\ f x = true) /\ forall n', n' < n -> forall a, nth_error xs n' = Some a -> f a = false).
  Proof using Type.
    cbv [find_index enumerate].
    edestruct find eqn:H; cbn; [ | split; [ congruence | ] ].
    { rewrite find_some_iff in H.
      destruct H as [n' H].
      rewrite nth_error_combine, nth_error_seq in H.
      setoid_rewrite nth_error_combine in H.
      setoid_rewrite nth_error_seq in H.
      break_innermost_match_hyps; split; intro H'; destruct_head'_and; Option.inversion_option; subst; cbn in *.
      all: repeat apply conj; eauto.
      { let H := match goal with H : forall n, n < _ -> _ |- _ => H end in
        intros i H' a' H''; specialize (H i H' (i, a'));
          rewrite H'' in H;
          break_innermost_match_hyps; [ specialize (H eq_refl); assumption | ].
        rewrite nth_error_length_error in H'' by lia; congruence. }
      { match goal with |- Some ?n = Some ?m => destruct (lt_eq_lt_dec n m) end; destruct_head' sumbool; subst; try reflexivity.
        all: match goal with H : forall n', n' < _ -> _ |- _ => specialize (H _ ltac:(eassumption)) end.
        { match goal with H : forall a, nth_error _ _ = Some _ -> _ |- _ => specialize (H _ ltac:(eassumption)); congruence end. }
        { destruct_head'_ex; destruct_head'_and.
          break_innermost_match_hyps; try congruence; try lia.
          Option.inversion_option; subst.
          match goal with H : forall x, Some _ = Some x -> _ |- _ => specialize (H _ eq_refl) end.
          cbn in *.
          congruence. } } }
    { rewrite find_none_iff_nth_error in H.
      intros [ [a [H0 H1]] ?]; specialize (H n (n, a)).
      rewrite nth_error_combine, nth_error_seq, H0 in H.
      break_innermost_match_hyps; [ | rewrite nth_error_length_error in H0 by lia; congruence ].
      specialize (H eq_refl); cbn in *.
      congruence. }
  Qed.
End find_index.

Lemma fold_left_id {A B} init ls
  : @fold_left A B (fun x _ => x) ls init = init.
Proof.
  revert init; induction ls as [|x xs IHxs]; cbn [fold_left]; eauto.
Qed.

Lemma fold_left_cons {B} init ls
  : @fold_left _ B (fun xs x => cons x xs) ls init = List.rev ls ++ init.
Proof.
  revert init; induction ls as [|x xs IHxs]; cbn [fold_left List.rev];
    intros; rewrite ?IHxs, ?List.app_nil_l, ?List.app_nil_r, <- ?List.app_assoc;
    cbn [List.app]; reflexivity.
Qed.

Lemma map_swap_combine {A B} ls1 ls2
  : List.map (fun xy => (snd xy, fst xy)) (List.combine ls2 ls1)
    = @List.combine A B ls1 ls2.
Proof.
  revert ls2; induction ls1 as [|x xs IHxs], ls2 as [|y ys]; cbn [List.combine List.map fst snd]; congruence.
Qed.

Lemma fold_right_higher_order A B C f a ls (F : _ -> C)
  : fold_right (fun x acc a => acc (f x a)) F ls a
    = F (@fold_right A B f a (List.rev ls)).
Proof.
  revert F a; induction ls; cbn; try reflexivity; intros.
  rewrite IHls, fold_right_app; cbn.
  reflexivity.
Qed.

Lemma fold_right_rev_higher_order A B f a ls
  : @fold_right A B f a (List.rev ls)
    = fold_right (fun x acc a => acc (f x a)) id ls a.
Proof. symmetry; apply fold_right_higher_order. Qed.

Lemma fold_left_higher_order A B C f a ls (F : _ -> C)
  : fold_left (fun acc x a => acc (f a x)) ls F a
    = F (@fold_left A B f (List.rev ls) a).
Proof.
  revert F a; induction ls; cbn; try reflexivity; intros.
  rewrite IHls, fold_left_app; cbn.
  reflexivity.
Qed.

Lemma fold_left_rev_higher_order A B f a ls
  : @fold_left A B f (List.rev ls) a
    = fold_left (fun acc x a => acc (f a x)) ls id a.
Proof. symmetry; apply fold_left_higher_order. Qed.

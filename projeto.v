(** * Projeto de LC1 - 2024-2 (30 pontos)  *)

(*
Nome e matrícula dos participantes:
1.
2.
3.
*)

(* begin hide *)
Require Import Arith.
Require Import List.
Require Import Lia.
Require Import Permutation.
(* end hide *)

(** ** Introdução  *)
(** Esta é a introdução ... *)

(** * Ordenação por Inserção binária *)

Require Import List Arith Lia.
Require Import Permutation.
Require Import Recdef.
Require Import Sorting.

Inductive ord: list nat -> Prop :=
| ord_nil: ord nil
| ord_one: forall h, ord (h::nil)
| ord_all: forall x y l, x <= y -> ord (y::l) -> ord (x::y::l).

Function binsert x l {measure length l} :=
  match l with
  | nil => x::nil
  | h::nil => if (x <=? h) then x::h::nil else h::x::nil
  | h::tl => let mid := length l / 2 in
             let l1 := firstn mid l in
             let l2 := skipn mid l in
             let ec := hd 99 l2 in
             if (x =? ec) then l1 ++ x::l2
             else if (x <? ec) then (binsert x l1) ++ l2 else l1++(binsert x l2)
  end.
Proof.
  - intros. rewrite firstn_length_le.
    + simpl length. apply Nat.div_lt.
      * lia.
      * auto.
    + apply Nat.lt_le_incl. simpl length. apply Nat.div_lt.
      * lia.
      * auto.
  - intros. rewrite skipn_length. apply Nat.sub_lt.
    + apply Nat.lt_le_incl. simpl length. apply Nat.div_lt.
      * lia.
      * auto.
    + simpl length. apply Nat.div_str_pos. split.
      * auto.
      * lia.
Defined.

Definition le_all x l := forall y, In y l -> x <= y.

Lemma ord_le_all: forall l a, ord(l) -> le_all a l -> ord(a :: l).
Proof.
  induction l.
    - intros. apply ord_one.
    - intros. apply ord_all.
      + unfold le_all in *. apply H0. apply in_eq.
      + assumption.
Qed.

Lemma ord_snd: forall l x y, ord (x::y::l) -> ord (x::l).
Proof.
  induction l.
  - intros x y H. apply ord_one.
  - intros x y H. inversion H; subst. inversion H4; subst. apply ord_all.
    +  apply Nat.le_trans with y; assumption.
    + assumption.
Qed. 

Lemma ord_all_le: forall l a, ord(a :: l) -> le_all a l.
Proof.
  induction l.
  - intros a H. unfold le_all. intros y H'. inversion H'.
  - intros a' H. unfold le_all in *. intros y H'. apply in_inv in H'. destruct H'.
    + subst.  inversion H; subst. assumption.
    + apply IHl.
      * apply ord_snd in H; assumption.
      * assumption.
Qed.

Lemma ord_cons: forall l a, ord l -> le_all a l -> ord (a::l).
Proof.
  induction l.
  - intros. apply ord_one.
  - intros. apply ord_le_all in H0. assumption. assumption. 
Qed.

Lemma ord_tail: forall l a, ord (a::l) -> ord l.
Proof.
  induction l.
  - intros a H. apply ord_nil.
  - intros a' H. inversion H; subst. assumption.
Qed.

Lemma le_all_concat: forall l l' x, le_all x l -> le_all x l' -> le_all x (l++l').
Proof.
  intros l l1 a H H1. unfold le_all in *. intros. apply in_app_or in H0. destruct H0.
  - apply H. assumption.
  - apply H1. assumption.
Qed.

Lemma hd_in: forall l (y: nat), length l > 0 -> In (hd y l) l.
Proof.
  induction l.
  - intros y H. simpl in H. inversion H.
  - intros y H. simpl in *. left. reflexivity.
Qed.

Lemma app_le_all: forall l1 l2 a, le_all a (l1++l2) -> (le_all a l1 /\ le_all a l2).
Proof.
  intros l1 l2 a H. unfold le_all in *. split.
  - intros y HIn. apply H. apply in_or_app. left; assumption.
  - intros y Hin. apply H. apply in_or_app. right; assumption.
Qed.

Lemma le_all_cons: forall l a x, x <= a -> le_all x l -> le_all x (a::l).
Proof.
  intros l a x Hle H. unfold le_all in *. intros y Hin. apply in_inv in Hin. destruct Hin.
  - subst. assumption.
  - apply H; assumption.
Qed.

Lemma ord_concatenacao: forall l l' x, ord(l++l') -> length(l') > 0  -> x = hd 99 l' -> ord(l++(x::l')).
Proof.
  induction l.
  - intros l' x y H1 H2. simpl in *. apply ord_cons.
    + assumption.
    + generalize dependent l'. intro l'; case l'.
      * intros H1 H2 H3. simpl in *. inversion H2.
      * intros n l H1 H2 H3. simpl in H3. subst. apply ord_all_le in H1.  unfold le_all in *. intros y' H. apply in_inv in H. destruct H.
        ** subst. auto.
        ** apply H1. assumption.
  - intros l2 x H1 H2 H3. simpl in *. apply ord_cons.
    + apply IHl. apply ord_tail in H1. assumption. assumption. assumption.
    + apply le_all_concat.
      * apply ord_all_le in H1. apply app_le_all in H1. destruct H1. assumption.
      * apply ord_all_le in H1. apply app_le_all in H1. destruct H1. apply le_all_cons. unfold le_all in H0. 
      apply H0. rewrite H3. apply hd_in. assumption. assumption.  
Qed.

Lemma skipn_length_gt_O: forall h: nat, forall tl: list nat, length (skipn (length (h :: tl) / 2) (h :: tl)) > 0.
Proof.
  intros. rewrite skipn_length. apply Nat.lt_add_lt_sub_r. rewrite Nat.add_0_l. apply Nat.div_lt.
  - simpl. lia.
  - lia.
Qed.

Lemma le_all_perm_sorted: forall l1 l2, (forall x, In x l1 -> le_all x l2) -> ord l1 -> ord l2 -> ord (l1++l2).
Proof.
  induction l1.
  - intros l2 H1 H2 H3. simpl. assumption.
  - intros l2 H1 H2 H3. simpl. apply ord_cons.
    + apply IHl1.
      * intros x H. apply H1. apply in_cons. assumption.
      * apply ord_tail in H2. assumption.
      * assumption.
    + simpl le_all. intros y H. apply in_app_or in H. destruct H. 
      * apply ord_all_le in H2. unfold le_all in H2. apply H2. assumption.
      * unfold le_all in H1. apply H1.
        ** apply in_eq.
        ** assumption.
Qed.

Lemma le_all_perm_le_all: forall l l' x, le_all x l -> Permutation l l' -> le_all x l'.
Proof.
  intros l l' x H1 H2. induction H2.
  - assumption.
  - unfold le_all in *. intros y H. apply in_inv in H. destruct H. 
    + subst. apply H1. apply in_eq.  
    + apply IHPermutation.
      * intros y' H'. apply H1. apply in_cons. assumption.
      * assumption.
  - unfold le_all in *. intros y' H'. apply in_inv in H'. destruct H'.
    + subst. apply H1. apply in_cons. apply in_eq.
    + apply in_inv in H. destruct H.
      * subst. apply H1. apply in_eq.
      *  apply H1. repeat apply in_cons. assumption.
  - apply IHPermutation2. apply IHPermutation1. assumption.
Qed.

Lemma le_all_hd_le: forall x y l, length l > 0 -> le_all x l -> x <= hd y l.
Proof.
  induction l.
  - intros. simpl in H. inversion H.
  - intros. simpl. unfold le_all in *. destruct H0 with a.
    + apply in_eq.
    + lia.
    + lia.
Qed.

Lemma sorted_in_le_all: forall l1 l2 x, ord(l1++l2) -> In x l1 -> le_all x l2.
Proof.
  induction l1.
  - intros l2 x H1 H2. inversion H2.
  - intros l2 x H1 H2. simpl in *. destruct H2.
    + subst. apply ord_all_le in H1. apply app_le_all in H1. destruct H1. assumption.
    + apply IHl1.
      * apply ord_tail in H1. assumption.
      * assumption.
Qed.

Lemma ord_firstn_one: forall n l x, ord (x::l) -> ord (x::firstn n l).
Proof.
  intro n. induction n. intro l. destruct l.
  - simpl. intro. auto.
  - simpl. intros. apply ord_one.
  - destruct l.
    + simpl. intros. apply ord_one.
    + simpl. intros. apply ord_all.
      * inversion H. exact H2.
      * apply IHn. inversion H. exact H4.
Qed.

Lemma ord_firstn: forall l n, ord l -> ord (firstn n l).
Proof.
  intro l. destruct l. intro n. destruct n.
  - simpl. auto.
  - simpl. intro. apply ord_nil.
  - intro. destruct n0.
    + simpl. intro. apply ord_nil.
    + simpl. apply ord_firstn_one.
Qed.

Lemma ord_skipn: forall l n, ord l -> ord (skipn n l).
Proof.
  intro l. induction l. intro n. destruct n.
  - simpl. auto.
  - simpl. auto.
  - destruct n.
    + rewrite skipn_O. auto.
    + simpl. intro. apply IHl. inversion H.
      * apply ord_nil.
      * assumption.
Qed.

Lemma le_all_app: forall l1 l2 a, le_all a l1 -> le_all a l2 -> le_all a (l1++l2).
Proof.
  intros l1 l2 a H1 H2. unfold le_all in *. intros y H. apply in_app_or in H. destruct H.
  - apply H1; assumption.
  - apply H2; assumption.
Qed.

Lemma length_ord_le_all: forall l x y, length l > 0 -> ord l -> x <= hd y l -> le_all x l.
Proof.
  induction l.
  - intros x y H1 H2 H3. simpl in H1. inversion H1.
  - intros x y H1 H2 H3. simpl in H3. apply le_all_cons.
    + assumption.
    + apply ord_all_le in H2. clear H1 IHl. unfold le_all in *. intros y' HIn. apply Nat.le_trans with a.
      * assumption.
      * apply H2. assumption.
Qed.


Lemma in_perm_in: forall l l' (x: nat), In x l -> Permutation l l' -> In x l'.
Proof.
  intros l l' x H1 H2. induction H2.
  - assumption.
  - apply in_inv in H1. destruct H1.
    + subst. apply in_eq.
    + apply in_cons. apply IHPermutation. assumption.
  - apply in_inv in H1. destruct H1.
    + subst. apply in_cons. apply in_eq.
    + apply in_inv in H. destruct H.
      * subst. apply in_eq.
      * repeat apply in_cons. assumption.
  - apply IHPermutation2. apply IHPermutation1. assumption.
Qed.


Lemma ord_app: forall l1 l2 x y, ord (l1++l2) -> length l2 > 0 -> x = hd y l2 -> ord (l1++x::l2).
Proof.
  induction l1.
  - intros l2 x y H1 H2 H3. simpl in *. apply ord_cons.
    + assumption.
    + generalize dependent l2. intro l2; case l2.
      * intros H1 H2 H3. simpl in *. inversion H2.
      * intros n l H1 H2 H3. simpl in H3. subst. apply ord_all_le in H1.  unfold le_all in *. intros y' H. apply in_inv in H. destruct H.
        ** subst. auto.
        ** apply H1. assumption.
  - intros l2 x y H1 H2 H3. simpl in *. apply ord_cons.
    + apply IHl1 with y.
      * apply ord_tail in H1. assumption.
      * assumption.
      * assumption.
    + apply le_all_app.
      * apply ord_all_le in H1. apply app_le_all in H1. destruct  H1. assumption.
      * apply ord_all_le in H1. apply app_le_all in H1. destruct H1. apply le_all_cons.
        ** unfold le_all in H0. apply H0. rewrite H3. apply hd_in; assumption.
        ** assumption.
Qed.

Lemma ord_app_perm: forall l1 l1' l2, (forall x, In x l1 -> le_all x l2)  -> Permutation l1 l1' -> ord l1' -> ord l2 -> ord (l1'++l2).
Proof.
  intros l1 l1' l2 H1 H2 H3 H4. apply le_all_perm_sorted.
  - intros x H. apply H1. apply in_perm_in with l1'.
    + assumption.
    + apply Permutation_sym. assumption.
  - assumption.
  - assumption.
Qed.

Lemma binsert_perm: forall l x, Permutation (x::l) (binsert x l).
Proof.
  intros l x. functional induction (binsert x l).
  - apply Permutation_refl.
  - apply Permutation_refl.
  - apply perm_swap.
  - apply Permutation_cons_app. rewrite firstn_skipn. apply Permutation_refl.
  - apply perm_trans with ( (x :: firstn (length (h :: tl) / 2) (h :: tl)) ++ (skipn (length (h :: tl) / 2) (h :: tl))). 
    + simpl. apply perm_skip. rewrite firstn_skipn. apply Permutation_refl.
    + apply Permutation_app_tail. assumption.
  - apply perm_trans with ( (firstn (length (h :: tl) / 2) (h :: tl)) ++ (x :: skipn (length (h :: tl) / 2) (h :: tl))).
    + apply Permutation_cons_app. rewrite firstn_skipn. apply Permutation_refl.
    + apply Permutation_app_head. assumption. 
Qed.


Lemma binsert_sorted: forall l x, ord l -> ord (binsert x l).
Proof.
  intros l x H. functional induction (binsert x l).
  (*Caso em que binsert x na lista vazia*)
  - apply ord_one.
  (*Caso em que binsert x na lista unitária e x < h*)
  - apply ord_all.
    + apply leb_complete. assumption.
    + assumption.
  (*Caso em que binsert x na lista unitária e h < x*)
  - apply ord_all.
    + apply leb_complete_conv in e0. apply Nat.lt_le_incl. assumption.
    + apply ord_one.
  (*Caso em que x é o primeiro elemento da segunda metade da lista l *)
  - apply ord_app with 99.
    (*provar que l1 ++ l2- ou seja, l' - está ordenado*)
    + pose proof firstn_skipn. specialize (H0 nat (length (h :: x :: tl) / 2) (h :: x :: tl)). rewrite firstn_skipn. assumption.
    (*provar que o  tamanho da segunda metade da lista é maior do que 0*)
    + rewrite skipn_length. simpl length. unfold gt. apply Nat.lt_add_lt_sub_r. rewrite Nat.add_0_l. apply Nat.div_lt.
      * lia.
      * auto.
    (*provar que x é igual ao primeiro elemento da segunda metade da lista*)
    + apply Nat.eqb_eq. assumption.
  (*Caso em que binsere x na primeira metade da lista l*)
  - apply ord_app_perm with (x::firstn (length (h :: tl) / 2) (h :: tl)).
    + intros. apply in_inv in H0. destruct H0. 
      ** subst. apply length_ord_le_all with 99.
        *** rewrite skipn_length. simpl length. unfold gt. apply Nat.lt_add_lt_sub_r. rewrite Nat.add_0_l. apply Nat.div_lt.
          **** lia. 
          **** auto.
        *** apply ord_skipn. assumption. 
        *** apply Nat.ltb_lt in e1. lia.
      ** apply length_ord_le_all with 99. 
        rewrite skipn_length. simpl length. unfold gt. apply Nat.lt_add_lt_sub_r. 
        rewrite Nat.add_0_l. apply Nat.div_lt. lia. auto. 
        *** apply ord_skipn. assumption. 
        *** apply le_all_hd_le. apply skipn_length_gt_O. apply sorted_in_le_all with (firstn (length (h :: tl) / 2) (h :: tl)).
        rewrite firstn_skipn. assumption. assumption.
    + apply binsert_perm. 
    + apply IHl0. apply ord_firstn. assumption. 
    + apply ord_skipn. assumption. 
  - apply le_all_perm_sorted.
    + intros. apply le_all_perm_le_all with (x::skipn (length (h :: tl) / 2) (h :: tl)). 
        * apply le_all_cons.
          ** apply Nat.le_trans with (hd 99 (skipn (length (h :: tl) / 2) (h :: tl))).
            *** apply le_all_hd_le.
              **** apply skipn_length_gt_O.
              **** apply sorted_in_le_all with (firstn (length (h :: tl) / 2) (h :: tl)).
                ***** rewrite firstn_skipn. exact H.
                ***** exact H0.
            *** apply Nat.ltb_nlt in e1. lia.
          ** apply sorted_in_le_all with (firstn (length (h :: tl) / 2) (h :: tl)).
            *** rewrite firstn_skipn. exact H.
            *** exact H0.
        * apply binsert_perm. 
    + apply ord_firstn. assumption.
    + apply IHl0. apply ord_skipn. assumption.
Qed.

Theorem binsert_preserva: forall l x, (ord l -> ord (binsert x  l)) /\ Permutation (x::l) (binsert x l).
Proof.
  intro l. split.
  - apply binsert_sorted.
  - apply binsert_perm.
Qed.

Fixpoint binsertion_sort (l: list nat) :=
  match l with
  | nil => nil
  | h::l' => binsert h (binsertion_sort l')
  end.


Lemma binsertion_sort_sorts: forall l, ord (binsertion_sort l).
Proof.
  induction l as [|h l'].
  - simpl. apply ord_nil.
  - simpl. apply binsert_sorted. assumption.
Qed.

Lemma perm_binsert: forall l l' x, Permutation l l' -> Permutation (binsert x l) (binsert x l').
Proof.
  intros l l' x H. apply perm_trans with (x::l').
  - apply Permutation_sym. apply perm_trans with (x::l).
    + apply perm_skip. apply Permutation_sym. exact H.
    + apply binsert_perm.
  - apply binsert_perm.
Qed.

Theorem binsertion_sort_correct: forall l,
  ord (binsertion_sort l) /\ Permutation l (binsertion_sort l).
Proof.
  induction l.
  - split.
    + simpl. apply ord_nil.
    + simpl. apply Permutation_refl.
  - destruct IHl as [Hord Hperm]. split.
    + simpl. apply binsert_sorted. assumption.
    + simpl.
      apply perm_trans with (a :: binsertion_sort l).
      * apply perm_skip. assumption.  (* Permutation (a::l) (a::binsertion_sort l) *)
      * apply binsert_perm.  (* Permutation (a::binsertion_sort l) (binsert a (binsertion_sort l)) *)
Qed.

Lemma ord_to_sorted: forall l, ord l -> Sorted le l.
Proof.
  induction 1; try constructor; auto.
Qed.

Theorem binsertion_sort_correct_spec: forall l,
  Sorted le (binsertion_sort l) /\ Permutation l (binsertion_sort l).
Proof.
  intro l.
  destruct (binsertion_sort_correct l) as [Hord Hperm].
  split.
  - apply ord_to_sorted. exact Hord.
  - exact Hperm.
Qed.

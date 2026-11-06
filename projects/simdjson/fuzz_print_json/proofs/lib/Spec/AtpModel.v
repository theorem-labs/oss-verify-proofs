(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim SjModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SEP : list Z := [10; 126; 126; 10].

Fixpoint starts_with (p l : list Z) : bool :=
  match p, l with
  | [], _ => true
  | _ :: _, [] => false
  | a :: p', b :: l' => (a =? b) && starts_with p' l'
  end.

Fixpoint find_sep (l : list Z) : option nat :=
  match l with
  | [] => None
  | _ :: l' => if starts_with SEP l then Some O
               else match find_sep l' with Some i => Some (S i) | None => None end
  end.

Fixpoint split_go (fuel : nat) (all : list Z) : list (list Z) :=
  match fuel with
  | O => [all]
  | S f => match find_sep all with
           | None => [all]
           | Some pos => firstn pos all :: split_go f (skipn (pos + 4) all)
           end
  end.

Definition atp_parts (d : list Z) : list (list Z) :=
  match d with [] => [] | _ => split_go (S (length d)) d end.

Definition atp_P (d : list Z) : nat := Nat.max (length (atp_parts d)) 2.

Definition atp_s0 (d : list Z) : list Z := nth 0 (atp_parts d) [].
Definition atp_ptr (d : list Z) : list Z := nth 1 (atp_parts d) [].

Definition atp_doc (d : list Z) : list Z :=
  if zlength (atp_s0 d) <=? SJ_PADMAX then atp_s0 d else [].

Fixpoint segs_go (l cur : list Z) : list (list Z) :=
  match l with
  | [] => [rev cur]
  | c :: l' => if c =? 47 then rev cur :: segs_go l' [] else segs_go l' (c :: cur)
  end.
Definition ptr_segs (p : list Z) : list (list Z) :=
  match p with c :: rest => if c =? 47 then segs_go rest [] else [] | [] => [] end.

Definition has_tilde (k : list Z) : bool := existsb (fun c => c =? 126) k.

Definition SSO_MAX : Z := 22.
Definition str_sz (L : Z) : Z := if L =? 23 then 26 else Z.lor L 7 + 1.

Definition vcap_next (cap size : Z) : Z := Z.max (2 * cap) (size + 1).
Definition VELT : Z := 16.

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable d : list Z.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition newnt (n : Z) : M ptr :=
  r <- lib_malloc ops n ;;
  match r with Some p => ret ops p | None => unreachable ops end.

Definition del (p : ptr) : M unit := lib_free ops (Some p).

Definition vec : Type := (Z * Z * option ptr)%type.
Definition vec0 : vec := (0, 0, None).

Definition vpush (v : vec) : M vec :=
  let '(cap, size, blk) := v in
  if size <? cap then ret ops (cap, size + 1, blk)
  else let cap' := vcap_next cap size in
       b <- newnt (VELT * cap') ;;
       (match blk with Some b0 => del b0 | None => ret ops tt end) ;;;
       ret ops (cap', size + 1, Some b).

Fixpoint vpushes (n : nat) (v : vec) : M vec :=
  match n with
  | O => ret ops v
  | S n' => v' <- vpush v ;; vpushes n' v'
  end.

Definition vfree (v : vec) : M unit :=
  match v with (_, _, Some b) => del b | _ => ret ops tt end.

Definition seg_alloc (z : Z) (k : list Z) : bool :=
  (z =? 2) && has_tilde k && (SSO_MAX <? zlength k).

Fixpoint atp_walk (segs : list (list Z)) : M unit :=
  match segs with
  | [] => ret ops tt
  | k :: rest =>
      z <- cho ops ;;
      if z =? 0 then ret ops tt
      else (if seg_alloc z k then p <- newnt (str_sz (zlength k)) ;; del p else ret ops tt) ;;;
           atp_walk rest
  end.

Definition fuzz_one_with (rc : option Z) : M Z :=
  let len0 := zlength (atp_s0 d) in
  let L := zlength (atp_doc d) in
  v <- vpushes (atp_P d) vec0 ;;
  cpo <- (if len0 <=? SJ_PADMAX then p <- newnt (SJ_COPY len0) ;; ret ops (Some p) else ret ops None) ;;
  sb <- newnt (SJ_SBUF L) ;;
  tp <- newnt (SJ_TAPE L) ;;
  im <- newnt SJ_IMPL ;;
  ix <- newnt (SJ_IDX L) ;;
  oc <- newnt SJ_OC ;;
  ia <- newnt SJ_IA ;;
  (match rc with Some c => r <- newnt c ;; del r | None => ret ops tt end) ;;;
  (match cpo with Some p => del p | None => ret ops tt end) ;;;
  ok <- cho ops ;;
  (if ok =? 0 then ret ops tt else atp_walk (ptr_segs (atp_ptr d))) ;;;
  del sb ;;; del tp ;;; del ia ;;; del oc ;;; del ix ;;; del im ;;;
  vfree v ;;;
  ret ops 0.

Definition fuzz_one : M Z := fuzz_one_with (sj_root_copy (atp_doc d)).

Fixpoint run_calls (n : nat) (rc : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      rc' <- fuzz_one ;;
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;
      run_calls n' rc'
  end.

Definition target_run (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in

  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2
  | Some owned =>
      rc <- run_calls calls 0 ;;
      lib_free ops owned ;;;
      ret ops (if rc =? 0 then 0 else 1)
  end.

End Target.

Lemma split_go_nonnil : forall fuel all, split_go fuel all <> [].
Proof. intros [|f] all; cbn; [discriminate|]. destruct (find_sep all); discriminate. Qed.

Lemma atp_parts_nil : atp_parts [] = [].
Proof. reflexivity. Qed.

Lemma atp_P_ge2 : forall d, (2 <= atp_P d)%nat.
Proof. intros d. unfold atp_P. lia. Qed.

Lemma starts_with_len : forall p l, starts_with p l = true -> (length p <= length l)%nat.
Proof.
  induction p as [|a p IH]; intros [|b l] H; cbn in *; try lia; try discriminate.
  apply andb_prop in H. destruct H as [_ H]. apply IH in H. lia.
Qed.

Lemma find_sep_unfold : forall c l,
  find_sep (c :: l) = if starts_with SEP (c :: l) then Some O else match find_sep l with Some i => Some (S i) | None => None end.
Proof. reflexivity. Qed.

Lemma find_sep_spec : forall l i, find_sep l = Some i -> (i + 4 <= length l)%nat.
Proof.
  induction l as [|c l IH]; intros i H; [discriminate|].
  rewrite find_sep_unfold in H. destruct (starts_with SEP (c :: l)) eqn:E.
  - inversion H; subst. apply starts_with_len in E. cbn [SEP length] in E. cbn. lia.
  - destruct (find_sep l) as [j|]; [|discriminate]. inversion H; subst. specialize (IH j eq_refl). cbn. lia.
Qed.

Lemma split_go_len : forall fuel all p, In p (split_go fuel all) -> (length p <= length all)%nat.
Proof.
  induction fuel as [|f IH]; intros all p H; cbn in H.
  - destruct H as [<-|[]]. lia.
  - destruct (find_sep all) as [pos|] eqn:E.
    + destruct H as [<-|H].
      * rewrite length_firstn. lia.
      * specialize (IH _ _ H). rewrite length_skipn in IH. lia.
    + destruct H as [<-|[]]. lia.
Qed.

Lemma atp_parts_len : forall d p, In p (atp_parts d) -> (length p <= length d)%nat.
Proof. intros d p. unfold atp_parts. destruct d; [intros []|]. apply split_go_len. Qed.

Lemma nth_In_or_default {A} : forall (l : list A) n dft, nth n l dft = dft \/ In (nth n l dft) l.
Proof. induction l as [|x l IH]; intros [|n] dft; cbn; auto. destruct (IH n dft); auto. Qed.

Lemma atp_s0_len : forall d, zlength (atp_s0 d) <= zlength d.
Proof.
  intros d. unfold atp_s0, zlength. destruct (nth_In_or_default (atp_parts d) 0 []) as [->|H]; [cbn; lia|].
  apply atp_parts_len in H. lia.
Qed.

Lemma atp_ptr_len : forall d, zlength (atp_ptr d) <= zlength d.
Proof.
  intros d. unfold atp_ptr, zlength. destruct (nth_In_or_default (atp_parts d) 1 []) as [->|H]; [cbn; lia|].
  apply atp_parts_len in H. lia.
Qed.

Lemma atp_doc_len : forall d, zlength (atp_doc d) <= zlength d /\ zlength (atp_doc d) <= SJ_PADMAX.
Proof.
  intros d. unfold atp_doc. pose proof (atp_s0_len d). destruct (Z.leb_spec (zlength (atp_s0 d)) SJ_PADMAX); [lia|].
  unfold zlength in *. cbn. unfold SJ_PADMAX. lia.
Qed.

Lemma split_go_count : forall fuel all, (4 * (length (split_go fuel all) - 1) <= length all)%nat.
Proof.
  induction fuel as [|f IH]; intros all; cbn; [lia|].
  destruct (find_sep all) as [pos|] eqn:E; cbn; [|lia].
  pose proof (find_sep_spec _ _ E). specialize (IH (skipn (pos + 4) all)). rewrite length_skipn in IH.
  pose proof (split_go_nonnil f (skipn (pos + 4) all)). destruct (split_go f (skipn (pos + 4) all)); [congruence|]. cbn in *. lia.
Qed.

Lemma atp_P_bound : forall d, (4 * (atp_P d - 1) <= length d + 4)%nat.
Proof.
  intros d. unfold atp_P, atp_parts. destruct d as [|c d']; [cbn; lia|].
  pose proof (split_go_count (S (length (c :: d'))) (c :: d')). lia.
Qed.

Lemma segs_go_len : forall l cur k, In k (segs_go l cur) -> (length k <= length l + length cur)%nat.
Proof.
  induction l as [|c l IH]; intros cur k H; cbn in H.
  - destruct H as [<-|[]]. rewrite length_rev. lia.
  - destruct (c =? 47).
    + destruct H as [<-|H]; [rewrite length_rev; cbn; lia|]. specialize (IH _ _ H). cbn in *. lia.
    + specialize (IH _ _ H). cbn in *. lia.
Qed.

Lemma ptr_segs_len : forall p k, In k (ptr_segs p) -> (length k <= length p)%nat.
Proof.
  intros p k. unfold ptr_segs. destruct p as [|c rest]; [intros []|]. destruct (c =? 47); [|intros []].
  intros H. pose proof (segs_go_len rest [] k H). cbn in *. lia.
Qed.

Lemma land7_range : forall L, 0 <= L -> 0 <= Z.land L 7 <= 7.
Proof.
  intros L HL. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (Z.ones 3) with (2^3 - 1).
  pose proof (Z.mod_pos_bound L (2^3) ltac:(lia)). lia.
Qed.

Lemma str_sz_bound : forall L, 0 <= L -> L + 1 <= str_sz L <= L + 8.
Proof.
  intros L HL. unfold str_sz. destruct (Z.eqb_spec L 23); [lia|].
  pose proof (Z.add_lor_land L 7). pose proof (land7_range L HL). lia.
Qed.

Definition sep_at (l : list Z) (i : nat) : Prop := firstn 4 (skipn i l) = SEP.

Lemma starts_with_SEP : forall l, starts_with SEP l = true <-> firstn 4 l = SEP.
Proof.
  intros l. unfold SEP. destruct l as [|a [|b [|c [|e l]]]].
  1-4: cbn -[Z.eqb]; split; intros H; try discriminate; repeat rewrite Bool.andb_false_r in H; discriminate.
  cbn -[Z.eqb]. rewrite Bool.andb_true_r.
  destruct (Z.eqb_spec 10 a), (Z.eqb_spec 126 b), (Z.eqb_spec 126 c), (Z.eqb_spec 10 e); cbn; split; intros H;
    try discriminate; subst; try reflexivity; inversion H; subst; contradiction.
Qed.

Lemma find_sep_Some : forall l i, find_sep l = Some i <-> sep_at l i /\ forall j, (j < i)%nat -> ~ sep_at l j.
Proof.
  unfold sep_at. induction l as [|c l IH]; intros i.
  - cbn. split; [discriminate|]. intros [H _]. destruct i; cbn in H; discriminate.
  - rewrite find_sep_unfold. destruct (starts_with SEP (c :: l)) eqn:E.
    + apply starts_with_SEP in E. split.
      * intros H; inversion H; subst. split; [exact E| intros j Hj; lia].
      * intros [Hi Hmin]. destruct i as [|i]; [reflexivity|]. exfalso. apply (Hmin O); [lia| exact E].
    + assert (E' : firstn 4 (c :: l) <> SEP) by (intros X; apply (proj2 (starts_with_SEP _)) in X; congruence).
      destruct (find_sep l) as [j|] eqn:F; rewrite <- F in IH.
      * split.
        -- intros H; inversion H; subst. destruct (proj1 (IH j) F) as [Hj Hmin]. split; [exact Hj|].
           intros [|j'] Hj'; [exact E'|]. cbn. apply Hmin. lia.
        -- intros [Hi Hmin]. destruct i as [|i]; [exfalso; exact (E' Hi)|]. f_equal.
           assert (find_sep l = Some i); [|congruence]. apply (proj2 (IH i)). split; [exact Hi|].
           intros j' Hj'. exact (Hmin (S j') ltac:(lia)).
      * split; [discriminate|]. intros [Hi Hmin]. destruct i as [|i]; [exfalso; exact (E' Hi)|]. exfalso.
        assert (X : find_sep l = Some i); [|congruence]. apply (proj2 (IH i)). split; [exact Hi|].
        intros j' Hj'. exact (Hmin (S j') ltac:(lia)).
Qed.

Lemma find_sep_None : forall l, find_sep l = None <-> forall i, ~ sep_at l i.
Proof.
  intros l. split.
  - intros H i Hi. revert l H Hi. induction i as [|i IH]; intros l H Hi.
    + destruct l as [|c l]; [unfold sep_at in Hi; cbn in Hi; discriminate|].
      rewrite find_sep_unfold in H. unfold sep_at in Hi. cbn [skipn] in Hi.
      apply (proj2 (starts_with_SEP _)) in Hi. rewrite Hi in H. discriminate.
    + destruct l as [|c l]; [unfold sep_at in Hi; cbn in Hi; discriminate|].
      rewrite find_sep_unfold in H. destruct (starts_with SEP (c :: l)); [discriminate|].
      destruct (find_sep l) eqn:F; [discriminate|]. unfold sep_at in Hi. cbn [skipn] in Hi. exact (IH l F Hi).
  - intros H. destruct (find_sep l) as [i|] eqn:F; [|reflexivity]. exfalso. apply (H i). exact (proj1 (proj1 (find_sep_Some l i) F)).
Qed.

Definition parts_of (all : list Z) : list (list Z) := split_go (S (length all)) all.

Lemma split_go_enough : forall f g all, (length all < 4 * f)%nat -> (length all < 4 * g)%nat -> split_go f all = split_go g all.
Proof.
  induction f as [|f IH]; intros g all Hf Hg; [lia|]. destruct g as [|g]; [lia|]. cbn.
  destruct (find_sep all) as [pos|] eqn:E; [|reflexivity]. f_equal.
  pose proof (find_sep_spec _ _ E). apply IH; rewrite length_skipn; lia.
Qed.

Lemma parts_of_unfold : forall all,
  parts_of all = match find_sep all with
                 | None => [all]
                 | Some pos => firstn pos all :: parts_of (skipn (pos + 4) all)
                 end.
Proof.
  intros all. unfold parts_of at 1. cbn [split_go]. destruct (find_sep all) as [pos|] eqn:E; [|reflexivity]. f_equal.
  unfold parts_of. pose proof (find_sep_spec _ _ E). apply split_go_enough; rewrite ?length_skipn; lia.
Qed.

Lemma atp_parts_eq : forall d, atp_parts d = match d with [] => [] | _ => parts_of d end.
Proof. intros [|c d]; reflexivity. Qed.

Fixpoint take_seg (l : list Z) : list Z := match l with [] => [] | c :: l' => if c =? 47 then [] else c :: take_seg l' end.
Fixpoint drop_seg (l : list Z) : list Z := match l with [] => [] | c :: l' => if c =? 47 then c :: l' else drop_seg l' end.

Lemma take_drop_seg : forall l, l = take_seg l ++ drop_seg l.
Proof. induction l as [|c l IH]; cbn; [reflexivity|]. destruct (c =? 47); cbn; [reflexivity|]. f_equal. exact IH. Qed.

Lemma take_seg_no_slash : forall l, ~ In 47 (take_seg l).
Proof.
  induction l as [|c l IH]; cbn; [tauto|]. destruct (Z.eqb_spec c 47); cbn; [tauto|]. intros [H|H]; [lia| exact (IH H)].
Qed.

Lemma drop_seg_shape : forall l, drop_seg l = [] \/ exists l', drop_seg l = 47 :: l'.
Proof.
  induction l as [|c l IH]; cbn; [left; reflexivity|]. destruct (Z.eqb_spec c 47); [right; subst; eexists; reflexivity| exact IH].
Qed.

Lemma segs_go_acc : forall l cur, segs_go l cur = match segs_go l [] with [] => [] | k :: ks => (rev cur ++ k) :: ks end.
Proof.
  induction l as [|c l IH]; intros cur; cbn; [rewrite app_nil_r; reflexivity|].
  destruct (c =? 47); [rewrite app_nil_r; reflexivity|].
  rewrite (IH [c]), (IH (c :: cur)). destruct (segs_go l []) as [|k ks]; [reflexivity|]. cbn. rewrite <- app_assoc. reflexivity.
Qed.

Lemma segs_go_unfold : forall l, segs_go l [] = take_seg l :: match drop_seg l with [] => [] | _ :: l' => segs_go l' [] end.
Proof.
  induction l as [|c l IH]; cbn; [reflexivity|]. destruct (c =? 47); [reflexivity|].
  rewrite segs_go_acc. rewrite IH. cbn. reflexivity.
Qed.

Lemma ptr_segs_unfold : forall rest,
  ptr_segs (47 :: rest) = take_seg rest :: match drop_seg rest with [] => [] | l' => ptr_segs l' end.
Proof.
  intros rest. unfold ptr_segs at 1. cbn [Z.eqb Pos.eqb]. rewrite segs_go_unfold.
  destruct (drop_seg_shape rest) as [->|[l' ->]]; [reflexivity|]. unfold ptr_segs. cbn [Z.eqb Pos.eqb]. reflexivity.
Qed.

Lemma ptr_segs_not_slash : forall p, match p with [] => True | c :: _ => c <> 47 end -> ptr_segs p = [].
Proof. intros [|c p] H; [reflexivity|]. unfold ptr_segs. destruct (Z.eqb_spec c 47); [lia| reflexivity]. Qed.

Lemma ptr_segs_join : forall p, match p with 47 :: _ => True | _ => False end ->
  concat (map (fun k => 47 :: k) (ptr_segs p)) = p.
Proof.
  intros p. remember (length p) as n eqn:En. revert p En.
  induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf); intros p En Hp.
  destruct p as [|c rest]; [destruct Hp|]. destruct c as [|q|q]; try destruct Hp.
  do 6 (try (destruct q; try destruct Hp)).
  rewrite ptr_segs_unfold. cbn [map concat]. cbn [app]. f_equal.
  rewrite (take_drop_seg rest) at 3. f_equal.
  destruct (drop_seg_shape rest) as [E|[l' E]]; rewrite E; [reflexivity|].
  apply (IHn (S (length l'))); [| reflexivity| exact I].
  subst n. pose proof (take_drop_seg rest) as X. rewrite E in X.
  assert (HL : length rest = (length (take_seg rest) + S (length l'))%nat) by (rewrite X at 1; rewrite length_app; reflexivity).
  cbn [length]. lia.
Qed.

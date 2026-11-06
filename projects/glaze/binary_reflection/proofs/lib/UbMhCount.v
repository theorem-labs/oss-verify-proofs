(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhCountSpec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition junk_in (st : mst) (Jl : list (Z * Z)) : Prop :=
  forall x k o, is_group st x -> 0 <= k <= g_lastidx st x -> s_slot st x k = SJunk o -> In (x, k) Jl.

Definition top_groups (st : mst) : list Z :=
  List.filter (fun g => match s_kind st g with GTop => true | GNest _ _ _ => false end) (s_groups st).

(* [comment removed for export] *)
Definition COUNT_GROUPS `{RN : mh_run} : Prop :=
  forall st L Jl, WF st L -> junk_in st Jl ->
    Z.of_nat (length (s_groups st)) <= 9 * (Z.of_nat (length L) + 48 + Z.of_nat (length Jl))
    /\ Z.of_nat (length (top_groups st)) <= Z.of_nat (length L) + 48 + Z.of_nat (length Jl).

(* [comment removed for export] *)
Definition COUNT_AREAS `{RN : mh_run} : Prop :=
  forall st L, WF st L -> s_flist st = [] -> c_avail_cnt (s_ctx st) = 0 ->
    101 * Z.of_nat (length (s_areas st)) <= Z.of_nat (length (s_groups st)) + Z.of_nat (length (s_limbo st)).

(* [comment removed for export] *)
Definition COUNT_REGIONS `{RN : mh_run} : Prop :=
  forall st L, WF st L ->
    Z.of_nat (length (s_regions st)) <= Z.of_nat (length (top_groups st)) + 2 * AREAMAX + 2.

End UbMhCountSpec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv UbMhCountSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_map_on {A B} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  intros Hinj Hnd. induction Hnd as [|a l Hn Hnd IH]; cbn; constructor.
  - intros Hin. apply in_map_iff in Hin as [y [Hy Hyl]].
    assert (y = a) by (apply Hinj; cbn; auto). subst. contradiction.
  - apply IH. intros x y Hx Hy. apply Hinj; cbn; auto.
Qed.

Lemma NoDup_list_prod {A B} (l : list A) (l' : list B) :
  List.NoDup l -> List.NoDup l' -> List.NoDup (list_prod l l').
Proof.
  intros Hl Hl'. induction Hl as [|a l Hn Hl IH]; cbn; [constructor|].
  apply NoDup_app.
  - apply NoDup_map_on; [|exact Hl']. intros x y _ _ H. congruence.
  - exact IH.
  - intros [x y] Hin Hin'. apply in_map_iff in Hin as [y' [Heq _]]. inversion Heq; subst.
    apply in_prod_iff in Hin' as [Hx _]. contradiction.
Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).

Lemma in_zseq n k : In k (zseq n) <-> 0 <= k < Z.of_nat n.
Proof.
  unfold zseq. rewrite in_map_iff. split.
  - intros [x [<- Hx]]. apply in_seq in Hx. lia.
  - intros Hk. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia.
Qed.

Lemma length_zseq n : length (zseq n) = n.
Proof. unfold zseq. now rewrite length_map, length_seq. Qed.

Lemma NoDup_zseq n : List.NoDup (zseq n).
Proof.
  unfold zseq. apply NoDup_map_on; [|apply seq_NoDup]. intros x y _ _ H. lia.
Qed.

Lemma length_flat_map_const {A B} (f : A -> list B) (c : nat) (l : list A) :
  (forall x, In x l -> length (f x) = c) -> length (flat_map f l) = (c * length l)%nat.
Proof.
  induction l as [|a l IH]; cbn; intros H; [lia|].
  rewrite length_app, (H a) by auto. rewrite IH by auto. lia.
Qed.

(* [comment removed for export] *)
Definition zsum {A} (f : A -> Z) (l : list A) : Z := fold_right (fun x acc => f x + acc) 0 l.

Lemma zsum_cons {A} (f : A -> Z) a l : zsum f (a :: l) = f a + zsum f l.
Proof. reflexivity. Qed.

Lemma zsum_nil {A} (f : A -> Z) : zsum f [] = 0.
Proof. reflexivity. Qed.

Lemma zsum_app {A} (f : A -> Z) l1 l2 : zsum f (l1 ++ l2) = zsum f l1 + zsum f l2.
Proof. induction l1 as [|a l1 IH]; [rewrite zsum_nil; cbn [app]; lia|]. cbn [app]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_perm {A} (f : A -> Z) l1 l2 : Permutation l1 l2 -> zsum f l1 = zsum f l2.
Proof.
  induction 1; rewrite ?zsum_cons; lia.
Qed.

Lemma zsum_map {A B} (g : A -> B) (f : B -> Z) l : zsum f (map g l) = zsum (fun x => f (g x)) l.
Proof. induction l as [|a l IH]; [reflexivity|]. cbn [map]. rewrite !zsum_cons, IH. reflexivity. Qed.

Lemma zsum_le_pointwise {A} (f g : A -> Z) l :
  (forall x, In x l -> f x <= g x) -> zsum f l <= zsum g l.
Proof.
  induction l as [|a l IH]; intros H; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons.
  assert (f a <= g a) by (apply H; cbn; auto). assert (zsum f l <= zsum g l) by (apply IH; intros; apply H; cbn; auto). lia.
Qed.

Lemma zsum_nonneg {A} (f : A -> Z) l : (forall x, In x l -> 0 <= f x) -> 0 <= zsum f l.
Proof.
  induction l as [|a l IH]; intros H; [rewrite zsum_nil; lia|]. rewrite zsum_cons.
  assert (0 <= f a) by (apply H; cbn; auto). assert (0 <= zsum f l) by (apply IH; intros; apply H; cbn; auto). lia.
Qed.

Lemma zsum_const {A} (c : Z) (l : list A) : zsum (fun _ => c) l = c * Z.of_nat (length l).
Proof. induction l as [|a l IH]; [rewrite zsum_nil; cbn; lia|]. rewrite zsum_cons, IH. cbn [length]. lia. Qed.

Lemma zsum_filter_split {A} (p : A -> bool) (f : A -> Z) l :
  zsum f l = zsum f (List.filter p l) + zsum f (List.filter (fun x => negb (p x)) l).
Proof.
  induction l as [|a l IH]; [reflexivity|]. rewrite zsum_cons. cbn [List.filter negb].
  destruct (p a); cbn [negb]; rewrite !zsum_cons; lia.
Qed.

(* [comment removed for export] *)
Lemma zsum_incl_nodup {A} (f : A -> Z) (l l' : list A) :
  List.NoDup l -> incl l l' -> (forall y, In y l' -> 0 <= f y) -> zsum f l <= zsum f l'.
Proof.
  intros Hnd. revert l'. induction Hnd as [|a l Hn Hnd IH]; intros l' Hincl Hpos.
  - rewrite zsum_nil. apply zsum_nonneg. exact Hpos.
  - rewrite zsum_cons.
    destruct (in_split a l') as [l1 [l2 ->]]; [apply Hincl; cbn; auto|].
    rewrite zsum_app, zsum_cons.
    assert (Hi : incl l (l1 ++ l2)).
    { intros x Hx. assert (Hx' : In x (l1 ++ a :: l2)) by (apply Hincl; cbn; auto).
      apply in_app_iff in Hx'. apply in_app_iff. destruct Hx' as [?|[<-|?]]; auto. contradiction. }
    assert (zsum f l <= zsum f (l1 ++ l2)).
    { apply IH; [exact Hi|]. intros y Hy. apply Hpos. apply in_app_iff in Hy. apply in_app_iff. cbn. tauto. }
    rewrite zsum_app in H. lia.
Qed.

(* [comment removed for export] *)
Lemma fold_regions_zsum (rs : list region) :
  fold_right (fun r acc => match rg_kind r with RGroup _ => rg_len r + acc | _ => acc end) 0 rs
  = zsum rg_len (List.filter (fun r => match rg_kind r with RGroup _ => true | _ => false end) rs).
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. cbn [fold_right List.filter]. rewrite IH.
  destruct (rg_kind r); reflexivity.
Qed.

Lemma fold_L_zsum (L : list (Z * Z)) :
  fold_right (fun b acc => snd b + MBLK + acc) 0 L = zsum (fun b => snd b + MBLK) L.
Proof. induction L as [|b L IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. reflexivity. Qed.

Lemma Nat_iter_fix {A} (f : A -> A) (x : A) n : f x = x -> Nat.iter n f x = x.
Proof. intros H. induction n as [|n IH]; [reflexivity|]. rewrite Nat.iter_succ, IH. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Count.
  Context {RN : mh_run}.
Variable st : mst.
Variable L : list (Z * Z).
Hypothesis HWF : WF st L.

Let groups := s_groups st.
Let regions := s_regions st.

#[local] Notation glast m := (g_lastidx st m).
#[local] Notation gslot m i := (s_slot st m i).
#[local] Notation gsc m := (g_sc st m).

Lemma HG : wf_groups st L. Proof. destruct HWF as (_ & _ & _ & H & _). exact H. Qed.

Lemma HLv : wf_live st L. Proof. destruct HWF as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HR : wf_regions st. Proof. destruct HWF as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HA : wf_areas st. Proof. destruct HWF as (_ & H & _). exact H. Qed.
Lemma HC : wf_ctx st. Proof. destruct HWF as (H & _). exact H. Qed.
Lemma HWG : forall m, is_group st m -> wf_group st L m.
Proof. intros m Hm. exact (wG_each st L HG m Hm). Qed.

Lemma Gnd : List.NoDup groups. Proof. apply NoDup_ListNoDup. exact (wG_nodup st L HG). Qed.
Lemma Rnd : List.NoDup regions. Proof. apply NoDup_ListNoDup. exact (wr_nodup st HR). Qed.
Lemma Areas_nd : List.NoDup (s_areas st). Proof. apply NoDup_ListNoDup. exact (wa_nodup st HA). Qed.

Lemma glast_nonneg m : 0 <= glast m.
Proof. unfold g_lastidx, w_lastidx. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition idxs (m : Z) : list Z := zseq (S (Z.to_nat (glast m))).

Lemma in_idxs m k : In k (idxs m) <-> 0 <= k <= glast m.
Proof. unfold idxs. rewrite in_zseq. pose proof (glast_nonneg m). lia. Qed.

Lemma idxs_first m : exists l, idxs m = 0 :: l.
Proof. unfold idxs, zseq. cbn. eexists. reflexivity. Qed.

Definition is_user_b (s : slot_st) : bool := match s with SUser _ _ _ _ => true | _ => false end.
Definition is_junk_b (s : slot_st) : bool := match s with SJunk _ => true | _ => false end.
Definition is_host_b (s : slot_st) : bool := match s with SHost _ _ => true | _ => false end.
Definition is_free_b (s : slot_st) : bool := match s with SAvail | SFreed => true | _ => false end.

Definition has_user (m : Z) : bool := existsb (fun k => is_user_b (gslot m k)) (idxs m).
Definition has_junk (m : Z) : bool := existsb (fun k => is_junk_b (gslot m k)) (idxs m).
Definition all_free (m : Z) : bool := forallb (fun k => is_free_b (gslot m k)) (idxs m).
Definition terminal (m : Z) : bool := has_user m || has_junk m || all_free m.

(* [comment removed for export] *)
Definition user_of (m : Z) : option (Z * Z) :=
  match find (fun k => is_user_b (gslot m k)) (idxs m) with
  | Some k => match gslot m k with SUser p n _ _ => Some (p, n) | _ => None end
  | None => None
  end.

(* [comment removed for export] *)
Definition first_child (m : Z) : option Z :=
  match find (fun k => is_host_b (gslot m k)) (idxs m) with
  | Some k => match gslot m k with SHost c _ => Some c | _ => None end
  | None => None
  end.

Definition host (m : Z) : Z := match s_kind st m with GTop => m | GNest hm _ _ => hm end.

Lemma user_of_some m p n :
  user_of m = Some (p, n) -> exists k off res, 0 <= k <= glast m /\ gslot m k = SUser p n off res.
Proof.
  unfold user_of. destruct (find _ _) as [k|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hk _]. apply in_idxs in Hk.
  destruct (gslot m k) eqn:Hs; try discriminate. intros H. injection H as <- <-.
  exists k, off, res. auto.
Qed.

Lemma has_user_user_of m : has_user m = true -> exists p n, user_of m = Some (p, n).
Proof.
  unfold has_user, user_of. intros H. apply existsb_exists in H as [k [Hk Hu]].
  destruct (find _ _) as [k'|] eqn:Hf.
  - apply find_some in Hf as [_ Hu']. destruct (gslot m k'); try discriminate. eauto.
  - pose proof (find_none _ _ Hf k Hk) as Hn. cbn in Hn. rewrite Hu in Hn. discriminate.
Qed.


Lemma has_junk_slot m : has_junk m = true -> exists k off, 0 <= k <= glast m /\ gslot m k = SJunk off.
Proof.
  unfold has_junk. intros H. apply existsb_exists in H as [k [Hk Hj]]. apply in_idxs in Hk.
  destruct (gslot m k) eqn:Hs; try discriminate. eauto.
Qed.

Lemma all_free_slots m : all_free m = true -> forall k, 0 <= k <= glast m -> gslot m k = SAvail \/ gslot m k = SFreed.
Proof.
  unfold all_free. intros H k Hk.
  pose proof (proj1 (forallb_forall _ _) H k (proj2 (in_idxs m k) Hk)) as Hs. cbn in Hs.
  destruct (gslot m k); try discriminate; auto.
Qed.

(* [comment removed for export] *)
Lemma nonterminal_child m :
  is_group st m -> terminal m = false ->
  exists c, first_child m = Some c /\ is_group st c /\ exists i off, s_kind st c = GNest m i off.
Proof.
  intros Hg Ht. unfold terminal in Ht.
  apply orb_false_iff in Ht as [Ht Hfree]. apply orb_false_iff in Ht as [Huser Hjunk].
  (* [comment removed for export] *)
  assert (Hex : exists k, In k (idxs m) /\ is_host_b (gslot m k) = true).
  { unfold all_free in Hfree.
    destruct (existsb (fun k => is_host_b (gslot m k)) (idxs m)) eqn:He.
    - apply existsb_exists in He as [k Hk]. exists k. exact Hk.
    - exfalso.
      assert (forallb (fun k => is_free_b (gslot m k)) (idxs m) = true); [|congruence].
      apply forallb_forall. intros k Hk.
      assert (Hu : is_user_b (gslot m k) = false).
      { destruct (is_user_b (gslot m k)) eqn:E; [|reflexivity]. exfalso.
        assert (existsb (fun k => is_user_b (gslot m k)) (idxs m) = true); [apply existsb_exists; eauto|].
        unfold has_user in Huser. congruence. }
      assert (Hj : is_junk_b (gslot m k) = false).
      { destruct (is_junk_b (gslot m k)) eqn:E; [|reflexivity]. exfalso.
        assert (existsb (fun k => is_junk_b (gslot m k)) (idxs m) = true); [apply existsb_exists; eauto|].
        unfold has_junk in Hjunk. congruence. }
      assert (Hh : is_host_b (gslot m k) = false).
      { destruct (is_host_b (gslot m k)) eqn:E; [|reflexivity]. exfalso.
        assert (existsb (fun k => is_host_b (gslot m k)) (idxs m) = true); [apply existsb_exists; eauto|].
        congruence. }
      destruct (gslot m k); cbn in *; congruence. }
  unfold first_child. destruct (find _ _) as [k|] eqn:Hf.
  - apply find_some in Hf as [Hk Hh]. apply in_idxs in Hk.
    destruct (gslot m k) as [| |p n off res|c off|off] eqn:Hs; try discriminate.
    exists c. split; [reflexivity|].
    pose proof (wg_slots st L m (HWG m Hg) k Hk) as Hwf. rewrite Hs in Hwf. cbn in Hwf.
    destruct Hwf as (_ & Hgc & _ & Hkind & _). split; [exact Hgc|]. eauto.
  - exfalso. destruct Hex as [k [Hk Hh]]. pose proof (find_none _ _ Hf k Hk) as Hn. cbn in Hn. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint updepth (k : nat) (m : Z) : Prop :=
  match k with
  | O => True
  | S k' => match s_kind st m with GTop => False | GNest hm _ _ => updepth k' hm end
  end.

Lemma updepth_le_depth : forall k f m, nest_depth_le st f m -> updepth k m -> (k <= f)%nat.
Proof.
  induction k as [|k IH]; intros f m Hd Hu; [lia|].
  cbn in Hu. destruct f as [|f].
  - cbn in Hd. destruct (s_kind st m); [contradiction|]. contradiction.
  - cbn in Hd. destruct (s_kind st m) as [|hm hi hoff]; [contradiction|].
    specialize (IH f hm Hd Hu). lia.
Qed.

(* [comment removed for export] *)
Fixpoint term (f : nat) (m : Z) : Z :=
  if terminal m then m
  else match f with
       | O => m
       | S f' => match first_child m with Some c => term f' c | None => m end
       end.

Lemma term_terminal_id f m : terminal m = true -> term f m = m.
Proof. intros H. destruct f; cbn; rewrite H; reflexivity. Qed.

Lemma term_spec : forall f m k,
  is_group st m -> updepth k m -> (k + f = 8)%nat ->
  is_group st (term f m) /\ terminal (term f m) = true /\
  exists d, (d <= f)%nat /\ Nat.iter d host (term f m) = m.
Proof.
  induction f as [|f IH]; intros m k Hg Hu Hkf.
  - cbn. destruct (terminal m) eqn:Ht.
    + split; [exact Hg|]. split; [exact Ht|]. exists O. split; [lia|reflexivity].
    + exfalso. destruct (nonterminal_child m Hg Ht) as (c & _ & Hgc & i & off & Hkind).
      assert (Hu' : updepth (S k) c) by (cbn; rewrite Hkind; exact Hu).
      pose proof (updepth_le_depth (S k) 8 c (wg_depth st L c (HWG c Hgc)) Hu'). lia.
  - cbn. destruct (terminal m) eqn:Ht.
    + split; [exact Hg|]. split; [exact Ht|]. exists O. split; [lia|reflexivity].
    + destruct (nonterminal_child m Hg Ht) as (c & Hfc & Hgc & i & off & Hkind). rewrite Hfc.
      assert (Hu' : updepth (S k) c) by (cbn; rewrite Hkind; exact Hu).
      destruct (IH c (S k) Hgc Hu' ltac:(lia)) as (Hgt & Htt & d & Hd & Hit).
      split; [exact Hgt|]. split; [exact Htt|]. exists (S d). split; [lia|].
      rewrite Nat.iter_succ, Hit. unfold host. rewrite Hkind. reflexivity.
Qed.

Definition T8 (m : Z) : Z := term 8 m.

Lemma T8_spec m : is_group st m ->
  is_group st (T8 m) /\ terminal (T8 m) = true /\ exists d, (d <= 8)%nat /\ Nat.iter d host (T8 m) = m.
Proof. intros Hg. apply (term_spec 8 m 0 Hg I eq_refl). Qed.

Lemma host_top m : s_kind st m = GTop -> host m = m.
Proof. intros H. unfold host. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma top_iter8 m : is_group st m -> s_kind st m = GTop -> Nat.iter 8 host (T8 m) = m.
Proof.
  intros Hg Htop. destruct (T8_spec m Hg) as (_ & _ & d & Hd & Hit).
  replace 8%nat with ((8 - d) + d)%nat by lia. rewrite Nat.iter_add, Hit.
  apply Nat_iter_fix. apply host_top. exact Htop.
Qed.

Lemma T8_inj_top m1 m2 :
  is_group st m1 -> is_group st m2 -> s_kind st m1 = GTop -> s_kind st m2 = GTop ->
  T8 m1 = T8 m2 -> m1 = m2.
Proof.
  intros H1 H2 T1 T2 Heq. rewrite <- (top_iter8 m1 H1 T1), <- (top_iter8 m2 H2 T2), Heq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition terms : list Z := List.filter terminal groups.

Lemma NoDup_terms : List.NoDup terms.
Proof. unfold terms. apply NoDup_filter. exact Gnd. Qed.

(* [comment removed for export] *)
Definition has_ptr (m p : Z) : bool :=
  existsb (fun k => match gslot m k with SUser p' _ _ _ => Z.eqb p' p | _ => false end) (idxs m).
Definition owner (b : Z * Z) : Z :=
  match find (fun m => has_ptr m (fst b)) groups with Some m => m | None => 0 end.

Lemma has_ptr_slot m p : has_ptr m p = true -> exists k n off res, 0 <= k <= glast m /\ gslot m k = SUser p n off res.
Proof.
  unfold has_ptr. intros H. apply existsb_exists in H as [k [Hk Hs]]. apply in_idxs in Hk.
  destruct (gslot m k) as [| |p' n off res| |] eqn:E; try discriminate. apply Z.eqb_eq in Hs. subst.
  exists k, n, off, res. auto.
Qed.

Lemma owner_eq m k p n off res :
  is_group st m -> 0 <= k <= glast m -> gslot m k = SUser p n off res -> owner (p, n) = m.
Proof.
  intros Hg Hk Hs. unfold owner. cbn [fst]. destruct (find _ _) as [m'|] eqn:Hf.
  - apply find_some in Hf as [Hm' Hp]. apply has_ptr_slot in Hp as (k' & n' & off' & res' & Hk' & Hs').
    destruct (wL_fun st L HLv m' k' m k p n' n off' off res' res Hm' Hg Hk' Hk Hs' Hs) as [-> _]. reflexivity.
  - exfalso. pose proof (find_none _ _ Hf m Hg) as Hn. cbn [fst] in Hn.
    assert (has_ptr m p = true); [|congruence]. unfold has_ptr. apply existsb_exists.
    exists k. split; [apply in_idxs; lia|]. rewrite Hs. apply Z.eqb_refl.
Qed.

(* [comment removed for export] *)
Definition ffrep (sc : Z) : Z :=
  match find (fun m => Z.eqb (gsc m) sc && all_free m) groups with Some m => m | None => 0 end.
Definition heads48 : list Z := map ffrep (zseq 48).

Lemma ffrep_eq t : is_group st t -> all_free t = true -> ffrep (gsc t) = t.
Proof.
  intros Hg Hf. unfold ffrep. destruct (find _ _) as [m'|] eqn:Hfd.
  - apply find_some in Hfd as [Hm' Hb]. apply andb_true_iff in Hb as [Hsc Hff]. apply Z.eqb_eq in Hsc.
    exact (wG_oneff st L HG m' t Hm' Hg (all_free_slots m' Hff) (all_free_slots t Hf) Hsc).
  - exfalso. pose proof (find_none _ _ Hfd t Hg) as Hn. cbv beta in Hn. rewrite Z.eqb_refl in Hn. rewrite Hf in Hn. discriminate Hn.
Qed.

(* [comment removed for export] *)
Lemma terminal_cases (Jl : list (Z * Z)) t :
  junk_in st Jl -> is_group st t -> terminal t = true ->
  In t (map owner L ++ map fst Jl ++ heads48).
Proof.
  intros HJ Hg Ht. unfold terminal in Ht. apply orb_true_iff in Ht as [Ht|Hfree].
  - apply orb_true_iff in Ht as [Hu|Hj].
    + apply has_user_user_of in Hu as (p & n & Huo).
      destruct (user_of_some _ _ _ Huo) as (k & off & res & Hk & Hs).
      apply in_app_iff. left. apply in_map_iff. exists (p, n). split.
      * apply (owner_eq t k p n off res Hg Hk Hs).
      * pose proof (wg_slots st L t (HWG t Hg) k Hk) as Hwf. rewrite Hs in Hwf. cbn in Hwf. tauto.
    + apply has_junk_slot in Hj as (k & off & Hk & Hs).
      apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (t, k). split; [reflexivity|].
      exact (HJ t k off Hg Hk Hs).
  - pose proof (wg_fullfree st L t (HWG t Hg) (all_free_slots t Hfree)) as (_ & Hsc & Hhd).
    apply in_app_iff. right. apply in_app_iff. right. unfold heads48. apply in_map_iff.
    exists (gsc t). split; [exact (ffrep_eq t Hg Hfree)|]. apply in_zseq.
    pose proof (Z.mod_pos_bound (g_W st t / 64) 64). unfold g_sc, w_sizeclass in *. lia.
Qed.

Lemma length_terms (Jl : list (Z * Z)) :
  junk_in st Jl -> (length terms <= length L + 48 + length Jl)%nat.
Proof.
  intros HJ.
  assert (Hincl : incl terms (map owner L ++ map fst Jl ++ heads48)).
  { intros t Ht. unfold terms in Ht. apply filter_In in Ht as [Hg Ht]. apply (terminal_cases Jl t HJ Hg Ht). }
  pose proof (NoDup_incl_length NoDup_terms Hincl) as Hlen.
  rewrite !length_app, !length_map in Hlen. unfold heads48 in Hlen. rewrite length_map, length_zseq in Hlen. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition anc9 (t : Z) : list Z := map (fun d => Nat.iter d host t) (seq 0 9).

Lemma groups_incl_anc : incl groups (flat_map anc9 terms).
Proof.
  intros m Hm. apply in_flat_map. destruct (T8_spec m Hm) as (Hgt & Htt & d & Hd & Hit).
  exists (T8 m). split.
  - unfold terms. apply filter_In. split; assumption.
  - unfold anc9. apply in_map_iff. exists d. split; [exact Hit|]. apply in_seq. lia.
Qed.

Lemma top_incl : incl (top_groups st) (map (fun t => Nat.iter 8 host t) terms).
Proof.
  intros m Hm. unfold top_groups in Hm. apply filter_In in Hm as [Hg Hk].
  destruct (s_kind st m) eqn:Htop; [|discriminate].
  apply in_map_iff. exists (T8 m). split; [apply top_iter8; assumption|].
  destruct (T8_spec m Hg) as (Hgt & Htt & _). unfold terms. apply filter_In. split; assumption.
Qed.

Theorem count_groups_st (Jl : list (Z * Z)) : junk_in st Jl ->
  Z.of_nat (length (s_groups st)) <= 9 * (Z.of_nat (length L) + 48 + Z.of_nat (length Jl))
  /\ Z.of_nat (length (top_groups st)) <= Z.of_nat (length L) + 48 + Z.of_nat (length Jl).
Proof.
  intros HJ. pose proof (length_terms Jl HJ) as HT.
  pose proof (NoDup_incl_length Gnd groups_incl_anc) as H1.
  rewrite (length_flat_map_const anc9 9) in H1 by (intros; unfold anc9; now rewrite length_map, length_seq).
  assert (Hnt : List.NoDup (top_groups st)) by (unfold top_groups; apply NoDup_filter; exact Gnd).
  pose proof (NoDup_incl_length Hnt top_incl) as H2. rewrite length_map in H2.
  change (s_groups st) with groups. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition all_metas : list Z :=
  map (fun ak => meta_addr (fst ak) (snd ak)) (list_prod (s_areas st) (zseq (Z.to_nat NSLOTS))).

Lemma length_all_metas : length all_metas = (101 * length (s_areas st))%nat.
Proof. unfold all_metas. rewrite length_map, length_prod, length_zseq. unfold NSLOTS. cbn. lia. Qed.

Lemma NoDup_all_metas : List.NoDup all_metas.
Proof.
  unfold all_metas. apply NoDup_map_on.
  - intros [a k] [a' k'] Hin Hin' Heq. cbn in Heq.
    apply in_prod_iff in Hin as [Ha Hk]. apply in_prod_iff in Hin' as [Ha' Hk'].
    apply in_zseq in Hk. apply in_zseq in Hk'. unfold NSLOTS in *.
    destruct (wa_rng st HA a Ha) as (Hma & _). destruct (wa_rng st HA a' Ha') as (Hma' & _).
    unfold meta_addr, AREA_HDR, META_SZ in Heq.
    assert (a = a').
    { assert (Hd : (a - a') mod 4096 = 0).
      { rewrite Zminus_mod, Hma, Hma'. reflexivity. }
      assert (Hr : -4096 < a - a' < 4096) by lia.
      apply Z.mod_divide in Hd; [|lia]. destruct Hd as [q Hq].
      assert (q = 0) by nia. subst q. lia. }
    subst a'. f_equal. lia.
  - apply NoDup_list_prod; [exact Areas_nd | apply NoDup_zseq].
Qed.

Theorem count_areas_st : s_flist st = [] -> c_avail_cnt (s_ctx st) = 0 ->
  101 * Z.of_nat (length (s_areas st)) <= Z.of_nat (length (s_groups st)) + Z.of_nat (length (s_limbo st)).
Proof.
  intros Hfl Hav.
  assert (Hincl : incl all_metas (s_groups st ++ s_limbo st)).
  { intros m Hm. unfold all_metas in Hm. apply in_map_iff in Hm as [[a k] [<- Hin]]. cbn.
    apply in_prod_iff in Hin as [Ha Hk]. apply in_zseq in Hk.
    assert (HU : metaU st (meta_addr a k)).
    { unfold metaU, is_meta_of. exists a, k. repeat split; auto; unfold NSLOTS in *; lia. }
    apply in_app_iff. destruct (in_dec Z.eq_dec (meta_addr a k) (s_groups st)) as [Hg|Hng]; [left; exact Hg|right].
    apply (wG_meta_other st L HG); [exact HU|exact Hng| |].
    - unfold in_flist. rewrite Hfl. cbn. tauto.
    - unfold fresh. rewrite Hav. lia. }
  pose proof (NoDup_incl_length NoDup_all_metas Hincl) as Hlen.
  rewrite length_all_metas, length_app in Hlen. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition isBrk (r : region) : bool := match rg_kind r with RBrk => true | _ => false end.
Definition isMeta (r : region) : bool := match rg_kind r with RMeta _ => true | _ => false end.
Definition isGrp (r : region) : bool := match rg_kind r with RGroup _ => true | _ => false end.

Definition regof (m : Z) : region := RG (g_mem st m) (4096 * g_maplen st m) (RGroup m).

Lemma length_regions_split :
  (length regions = length (List.filter isBrk regions) + length (List.filter isMeta regions) + length (List.filter isGrp regions))%nat.
Proof.
  clearbody regions. induction regions as [|r rs IH]; [reflexivity|].
  cbn [length List.filter]. destruct r as [b len [|e|m]]; cbn [isBrk isMeta isGrp rg_kind length]; rewrite IH; lia.
Qed.

Lemma length_meta_regions : Z.of_nat (length (List.filter isMeta regions)) <= AREAMAX + 1.
Proof.
  pose proof (wr_meta_cnt st HR) as H1. pose proof (wc_shift st HC) as H2. pose proof (wa_cnt st HA) as H3.
  change (s_regions st) with regions in H1. unfold isMeta. cbn in *. lia.
Qed.

Lemma length_brk_regions : Z.of_nat (length (List.filter isBrk regions)) <= AREAMAX.
Proof.
  pose proof (wr_brk st HR) as H1. pose proof (wa_cnt st HA) as H3. change (s_regions st) with regions in H1.
  destruct (s_brk st) as [|b0 b|g].
  - assert (List.filter isBrk regions = []) as ->.
    { destruct (List.filter isBrk regions) as [|r rs] eqn:E; [reflexivity|]. exfalso.
      assert (Hin : In r (List.filter isBrk regions)) by (rewrite E; cbn; auto).
      apply filter_In in Hin as [Hin Hb]. destruct r as [bb ll [| |]]; try discriminate. exact (H1 bb ll Hin). }
    cbn. unfold AREAMAX. lia.
  - destruct H1 as (_ & H1 & _). unfold isBrk. lia.
  - destruct H1 as (H1 & _). unfold isBrk. lia.
Qed.

Lemma grp_regions_incl : incl (List.filter isGrp regions) (map regof (top_groups st)).
Proof.
  intros r Hr. apply filter_In in Hr as [Hin Hk]. destruct r as [b len [| |m]]; try discriminate.
  destruct (wG_regions st L HG b len m Hin) as (Hg & Htop & -> & ->).
  apply in_map_iff. exists m. split; [reflexivity|]. unfold top_groups. apply filter_In. rewrite Htop. split; [exact Hg|reflexivity].
Qed.

Lemma length_grp_regions : (length (List.filter isGrp regions) <= length (top_groups st))%nat.
Proof.
  pose proof (NoDup_incl_length (NoDup_filter isGrp Rnd) grp_regions_incl) as H.
  rewrite length_map in H. exact H.
Qed.

Theorem count_regions_st :
  Z.of_nat (length (s_regions st)) <= Z.of_nat (length (top_groups st)) + 2 * AREAMAX + 2.
Proof.
  change (s_regions st) with regions. rewrite length_regions_split.
  pose proof length_meta_regions. pose proof length_brk_regions. pose proof length_grp_regions. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma grp_regions_perm : Permutation (List.filter isGrp regions) (map regof (top_groups st)).
Proof.
  apply NoDup_Permutation.
  - apply NoDup_filter. exact Rnd.
  - apply NoDup_map_on.
    + intros x y _ _ H. unfold regof in H. congruence.
    + unfold top_groups. apply NoDup_filter. exact Gnd.
  - intros r. split; [apply grp_regions_incl|].
    intros Hr. apply in_map_iff in Hr as [m [<- Hm]]. unfold top_groups in Hm. apply filter_In in Hm as [Hg Hk].
    pose proof (wg_kind st L m (HWG m Hg)) as Hkind. destruct (s_kind st m); [|discriminate].
    destruct Hkind as (_ & Hin & _). apply filter_In. split; [exact Hin|reflexivity].
Qed.

(* [comment removed for export] *)
Definition charge (m : Z) : Z :=
  match user_of (T8 m) with Some b => snd b + MBLK | None => GRPMAX end.

Definition blk_of (m : Z) : Z * Z := match user_of (T8 m) with Some b => b | None => (0, 0) end.
Definition hasU (m : Z) : bool := match user_of (T8 m) with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition no_junk63 : Prop :=
  forall m off, is_group st m -> gsc m = 63 -> gslot m 0 <> SJunk off.

Lemma user_n_nonneg m p n : is_group st m -> user_of m = Some (p, n) -> 0 <= n /\ In (p, n) L.
Proof.
  intros Hg Hu. destruct (user_of_some _ _ _ Hu) as (k & off & res & Hk & Hs).
  pose proof (wg_slots st L m (HWG m Hg) k Hk) as Hwf. rewrite Hs in Hwf. cbn in Hwf. tauto.
Qed.

Lemma len_le_charge m : no_junk63 ->
  is_group st m -> s_kind st m = GTop -> rg_len (regof m) <= charge m.
Proof.
  intros H63 Hg Htop. cbn.
  pose proof (wg_kind st L m (HWG m Hg)) as Hkind. rewrite Htop in Hkind. destruct Hkind as (Hml & Hin & _).
  destruct (T8_spec m Hg) as (Hgt & Htt & _).
  assert (Hch : GRPMAX <= charge m).
  { unfold charge. destruct (user_of (T8 m)) as [[p n]|] eqn:Hu; [|lia].
    destruct (user_n_nonneg _ _ _ Hgt Hu) as [Hn _]. cbn. unfold MBLK, GRPMAX. lia. }
  destruct (wg_sc st L m (HWG m Hg)) as [Hsc|(Hsc & Hlast & _)].
  - pose proof (wr_grp_bound st HR _ _ _ Hin Hsc). lia.
  - destruct (wr_grp63 st HR _ _ _ Hin Hsc) as [(p & n & off & res & Hs & Hlen)|(off & Hs)].
    + (* [comment removed for export] *)
      assert (Hterm : terminal m = true).
      { unfold terminal. replace (has_user m) with true; [reflexivity|]. symmetry.
        unfold has_user. apply existsb_exists. exists 0. split; [apply in_idxs; pose proof (glast_nonneg m); lia|].
        rewrite Hs. reflexivity. }
      assert (HT : T8 m = m) by (unfold T8; apply term_terminal_id; exact Hterm).
      unfold charge. rewrite HT.
      assert (Hu : user_of m = Some (p, n)).
      { unfold user_of. destruct (idxs_first m) as [l Hl]. rewrite Hl. cbn. rewrite Hs. cbn. rewrite Hs. reflexivity. }
      rewrite Hu. cbn. unfold MBLK. lia.
    + exfalso. exact (H63 m off Hg Hsc Hs).
Qed.

Lemma top_props m : In m (top_groups st) -> is_group st m /\ s_kind st m = GTop.
Proof.
  intros Hm. unfold top_groups in Hm. apply filter_In in Hm as [Hg Hk].
  destruct (s_kind st m); [auto|discriminate].
Qed.

Theorem count_bytes_st (Jl : list (Z * Z)) : junk_in st Jl -> no_junk63 ->
  fold_right (fun r acc => match rg_kind r with RGroup _ => rg_len r + acc | _ => acc end) 0 (s_regions st)
    <= fold_right (fun b acc => snd b + MBLK + acc) 0 L + (48 + Z.of_nat (length Jl)) * GRPMAX.
Proof.
  intros HJ H63. rewrite fold_regions_zsum, fold_L_zsum. change (s_regions st) with regions.
  fold isGrp. rewrite (zsum_perm _ _ _ grp_regions_perm), zsum_map.
  (* [comment removed for export] *)
  transitivity (zsum charge (top_groups st)).
  { apply zsum_le_pointwise. intros m Hm. destruct (top_props m Hm) as [Hg Ht]. apply (len_le_charge m H63 Hg Ht). }
  (* [comment removed for export] *)
  rewrite (zsum_filter_split hasU).
  set (TU := List.filter hasU (top_groups st)). set (TN := List.filter (fun x => negb (hasU x)) (top_groups st)).
  assert (HnT : List.NoDup (top_groups st)) by (unfold top_groups; apply NoDup_filter; exact Gnd).
  (* [comment removed for export] *)
  assert (HU : zsum charge TU <= zsum (fun b => snd b + MBLK) L).
  { transitivity (zsum (fun m => snd (blk_of m) + MBLK) TU).
    { apply zsum_le_pointwise. intros m Hm. apply filter_In in Hm as [_ Hh]. unfold hasU in Hh.
      unfold charge, blk_of. destruct (user_of (T8 m)); [lia|discriminate]. }
    rewrite <- (zsum_map blk_of (fun b => snd b + MBLK)).
    apply zsum_incl_nodup.
    - apply NoDup_map_on; [|apply NoDup_filter; exact HnT].
      intros x y Hx Hy Heq. apply filter_In in Hx as [Hx Hhx]. apply filter_In in Hy as [Hy Hhy].
      destruct (top_props x Hx) as [Hgx Htx]. destruct (top_props y Hy) as [Hgy Hty].
      apply (T8_inj_top x y Hgx Hgy Htx Hty).
      unfold hasU, blk_of in *.
      destruct (user_of (T8 x)) as [[px nx]|] eqn:Ex; [|discriminate].
      destruct (user_of (T8 y)) as [[py ny]|] eqn:Ey; [|discriminate]. subst.
      destruct (T8_spec x Hgx) as (Hgtx & _). destruct (T8_spec y Hgy) as (Hgty & _).
      injection Heq as Hp Hn. subst.
      destruct (user_of_some _ _ _ Ex) as (kx & ox & rx & Hkx & Hsx).
      destruct (user_of_some _ _ _ Ey) as (ky & oy & ry & Hky & Hsy).
      exact (proj1 (wL_fun st L HLv _ _ _ _ _ _ _ _ _ _ _ Hgtx Hgty Hkx Hky Hsx Hsy)).
    - intros b Hb. apply in_map_iff in Hb as [m [<- Hm]]. apply filter_In in Hm as [Hm Hh].
      destruct (top_props m Hm) as [Hg _]. destruct (T8_spec m Hg) as (Hgt & _).
      unfold hasU, blk_of in *. destruct (user_of (T8 m)) as [[p n]|] eqn:E; [|discriminate].
      exact (proj2 (user_n_nonneg _ _ _ Hgt E)).
    - intros [p n] Hin. cbn. destruct (wL_in st L HLv p n Hin) as (m & i & off & res & Hg & Hi & Hs).
      pose proof (wg_slots st L m (HWG m Hg) i Hi) as Hwf. rewrite Hs in Hwf. cbn in Hwf. unfold MBLK. lia. }
  (* [comment removed for export] *)
  assert (HN : zsum charge TN <= (48 + Z.of_nat (length Jl)) * GRPMAX).
  { transitivity (zsum (fun _ => GRPMAX) TN).
    { apply zsum_le_pointwise. intros m Hm. apply filter_In in Hm as [_ Hh]. unfold hasU in Hh.
      unfold charge. destruct (user_of (T8 m)); [discriminate|lia]. }
    rewrite zsum_const.
    assert (Hlen : (length TN <= length Jl + 48)%nat).
    { assert (Hincl : incl (map T8 TN) (map fst Jl ++ heads48)).
      { intros t Ht. apply in_map_iff in Ht as [m [<- Hm]]. apply filter_In in Hm as [Hm Hh].
        destruct (top_props m Hm) as [Hg _]. destruct (T8_spec m Hg) as (Hgt & Htt & _).
        pose proof (terminal_cases Jl (T8 m) HJ Hgt Htt) as Hc. apply in_app_iff in Hc as [Hc|Hc]; [|exact Hc].
        exfalso. apply in_map_iff in Hc as [[p n] [Ho Hin]].
        (* [comment removed for export] *)
        unfold hasU in Hh. destruct (user_of (T8 m)) eqn:E; [discriminate|].
        unfold terminal in Htt.
        destruct (has_user (T8 m)) eqn:Eu.
        - apply has_user_user_of in Eu as (p' & n' & E'). congruence.
        - (* [comment removed for export] *)
          destruct (wL_in st L HLv p n Hin) as (m' & i & off & res & Hg' & Hi & Hs').
          pose proof (owner_eq m' i p n off res Hg' Hi Hs') as Ho'. rewrite Ho' in Ho. subst m'.
          assert (has_user (T8 m) = true); [|congruence].
          unfold has_user. apply existsb_exists. exists i. split; [apply in_idxs; lia|]. rewrite Hs'. reflexivity. }
      assert (Hnd : List.NoDup (map T8 TN)).
      { apply NoDup_map_on; [|apply NoDup_filter; exact HnT].
        intros x y Hx Hy. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
        destruct (top_props x Hx) as [Hgx Htx]. destruct (top_props y Hy) as [Hgy Hty].
        apply (T8_inj_top x y Hgx Hgy Htx Hty). }
      pose proof (NoDup_incl_length Hnd Hincl) as Hl.
      rewrite length_map, length_app, length_map in Hl. unfold heads48 in Hl. rewrite length_map, length_zseq in Hl. lia. }
    unfold GRPMAX. nia. }
  lia.
Qed.

End Count.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem count_groups `{RN : mh_run} : COUNT_GROUPS.
Proof. intros st L Jl HWF HJ. exact (count_groups_st st L HWF Jl HJ). Qed.

Theorem count_areas `{RN : mh_run} : COUNT_AREAS.
Proof. intros st L HWF Hfl Hav. exact (count_areas_st st L HWF Hfl Hav). Qed.

Theorem count_regions `{RN : mh_run} : COUNT_REGIONS.
Proof. intros st L HWF. exact (count_regions_st st L HWF). Qed.

(* [comment removed for export] *)
Theorem count_bytes_no_junk63 `{RN : mh_run} : forall st L Jl, WF st L -> junk_in st Jl -> no_junk63 st ->
    fold_right (fun r acc => match rg_kind r with RGroup _ => rg_len r + acc | _ => acc end) 0 (s_regions st)
      <= fold_right (fun b acc => snd b + MBLK + acc) 0 L + (48 + Z.of_nat (length Jl)) * GRPMAX.
Proof. intros st L Jl HWF HJ H63. exact (count_bytes_st st L HWF Jl HJ H63). Qed.


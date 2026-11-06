(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_Ext2S8 MI_GeomS8 KStepS8 MI_Pres4S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Bits.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Bridge Require Import BrResS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8 HeEmptyS8 HeWNtfS8 HeMetaS8 HeWSlotS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMRES.
Context {RUNp : RunP}.

Definition csz (n : Z) : Z := Z.max (2 ^ 20) (mmap_len (n + IB + UNIT)).

Fixpoint anc (f : nat) (st : mstate) (s : aptr) : list aptr :=
  match f with
  | O => []
  | S f' =>
    match s_slots st !! s with
    | None => []
    | Some (m, _) => let b := gbase (MR st m) in b :: (if m_maplen (MR st m) =? 0 then anc f' st b else [])
    end
  end.

Lemma gok_fsub_res {X st LS m b ai} : group_ok X st LS m b ai -> fsub (fmask (MR st m)) (mask_upto (m_last_idx (MR st m))).
Proof.
  intros GO i Hi T. pose proof (g_masks _ _ _ _ _ _ GO) as (A0 & F0 & Ab & Fb & _ & _). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold fmask in T. rewrite Z.lor_spec in T. apply Bool.orb_true_iff in T as [T|T].
  - pose proof (Ab i Hi T). rewrite testbit_mask_upto by lia. apply Z.leb_le. lia.
  - pose proof (Fb i Hi T). rewrite testbit_mask_upto by lia. apply Z.leb_le. lia.
Qed.

Lemma anc_length f st s : (length (anc f st s) <= f)%nat.
Proof.
  revert s. induction f as [|f IH]; intros s; cbn; [lia|].
  destruct (s_slots st !! s) as [[m i]|]; cbn; [| lia]. destruct (m_maplen (MR st m) =? 0); cbn; [pose proof (IH (gbase (MR st m))); lia| lia].
Qed.

Section ST.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVC x0 st L BL LS.
Hypothesis E : EINV st.

Let IM : inv_M x0 st LS := proj1 (proj2 (proj2 INV)).
Let IG : inv_G x0 st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S x0 st BL := proj2 (proj2 (proj2 (proj2 (proj2 INV)))).

Lemma hosts_base b m : hosts st b m -> gbase (MR st m) = b.
Proof. intros H. exact (hosts_gbase x0 st LS IM b m H). Qed.

Lemma anc_extend f : forall s0 b' m' m i, In b' (anc f st s0) -> hosts st b' m' -> m_maplen (MR st m') = 0 ->
  s_slots st !! b' = Some (m, i) -> In (gbase (MR st m)) (anc (S f) st s0).
Proof.
  induction f as [|f IH]; intros s0 b' m' m i Hin Hb' ML Hsl; [destruct Hin|].
  cbn [anc] in Hin. cbn [anc].
  destruct (s_slots st !! s0) as [[m0 i0]|] eqn:E0; [| destruct Hin].
  destruct Hin as [Eb|Hin].
  -
    destruct (is_valid _ _ _ IS s0 m0 i0 E0) as ([b0 Hb0] & _ & _).
    rewrite (hosts_base b0 m0 Hb0) in Eb |- *. subst b0.
    pose proof (hosts_fun st b' m0 m' Hb0 Hb') as ->. rewrite ML, Z.eqb_refl.
    right. cbn [anc]. rewrite Hsl. left. reflexivity.
  - destruct (m_maplen (MR st m0) =? 0); [| destruct Hin].
    right. exact (IH (gbase (MR st m0)) b' m' m i Hin Hb' ML Hsl).
Qed.

Lemma anc_rid f : forall s b, In b (anc f st s) -> fst b = fst s.
Proof.
  induction f as [|f IH]; intros s b Hin; [destruct Hin|]. cbn [anc] in Hin.
  destruct (s_slots st !! s) as [[m i]|] eqn:E0; [| destruct Hin].
  destruct (is_valid _ _ _ IS s m i E0) as ([b0 Hb0] & _ & Es). rewrite (hosts_base b0 m Hb0) in Hin.
  assert (Fs : fst s = fst b0) by (rewrite Es, (slot_start'_eq x0 st LS IM m b0 i Hb0); reflexivity).
  destruct Hin as [<-|Hin]; [symmetry; exact Fs|].
  destruct (m_maplen (MR st m) =? 0); [| destruct Hin]. rewrite Fs. exact (IH b0 b Hin).
Qed.

Lemma bits_upto (a : Z) : forall n : nat, (forall i, 0 <= i < Z.of_nat n -> Z.testbit a i = true) \/ (exists i, 0 <= i < Z.of_nat n /\ Z.testbit a i = false).
Proof.
  induction n as [|n IH]; [left; intros; lia|].
  destruct IH as [ALL|(i & Hi & F)]; [| right; exists i; split; [lia| exact F]].
  destruct (Z.testbit a (Z.of_nat n)) eqn:T; [| right; exists (Z.of_nat n); split; [lia| exact T]].
  left. intros i Hi. destruct (Z.eq_dec i (Z.of_nat n)) as [->|NE]; [exact T| apply ALL; lia].
Qed.

Lemma nonempty_slot b m ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> ~ gempty st m ->
  exists i, 0 <= i <= m_last_idx (MR st m) /\ Z.testbit (fmask (MR st m)) i = false.
Proof.
  intros Hb NE. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO. pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (gok_fsub_res GO) as FS.
  destruct (bits_upto (fmask (MR st m)) (Z.to_nat (m_last_idx (MR st m) + 1))) as [ALL|(i & Hi & F)].
  - exfalso. apply NE. unfold gempty. apply Z.bits_inj'. intros j Hj. rewrite testbit_mask_upto by lia.
    destruct (Z.leb_spec j (m_last_idx (MR st m))) as [Hle|Hgt].
    + apply ALL. rewrite Z2Nat.id by lia. lia.
    + destruct (Z.testbit (fmask (MR st m)) j) eqn:T; [| reflexivity]. exfalso.
      pose proof (FS j Hj T) as T'. rewrite testbit_mask_upto in T' by lia. apply Z.leb_le in T'. lia.
  - exists i. rewrite Z2Nat.id in Hi by lia. split; [lia| exact F].
Qed.

Lemma inuse_slot b m ai i : s_groups st !! b = Some (mkGhdr (Some m) ai) -> 0 <= i <= m_last_idx (MR st m) ->
  Z.testbit (fmask (MR st m)) i = false ->
  let s := slot_start' (MR st m) i in
  In s (map bslot BL) \/ (exists m' ai', s_groups st !! s = Some (mkGhdr (Some m') ai') /\ m_maplen (MR st m') = 0
                            /\ m_sizeclass (MR st m') < m_sizeclass (MR st m) /\ m_sizeclass (MR st m) < 48).
Proof.
  intros Hb Hi F. cbv zeta. set (s := slot_start' (MR st m) i).
  pose proof (is_part _ _ _ IS b m ai i Hb Hi) as P. cbv zeta in P. fold s in P. destruct P as (P & _).
  unfold fmask in F. rewrite Z.lor_spec in F. apply Bool.orb_false_iff in F as [Fa Ff]. unfold tbit in P.
  destruct P as [P|[P|[P|[P|P]]]]; [rewrite Fa in P; discriminate| rewrite Ff in P; discriminate| left; exact P| | cbn in P; discriminate].
  right. destruct (s_groups st !! s) as [[[m'|] ai']|] eqn:Hs; [| exfalso; exact (ig_nometa _ _ _ IG _ _ Hs)| exfalso; exact (P eq_refl)].
  exists m', ai'. split; [reflexivity|]. pose proof (ig_ok _ _ _ IG _ _ _ Hs) as GO'.
  assert (Ss : 0 < snd s).
  { pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO. pose proof (g_align _ _ _ _ _ _ GO) as [A0 _].
    unfold s. rewrite (slot_start'_eq x0 st LS IM m b i (ex_intro _ ai Hb)). cbn [snd]. unfold sstart.
    rewrite (hosts_base b m (ex_intro _ ai Hb)). pose proof (stride_ge x0 st LS IG b m (ex_intro _ ai Hb)) as SG. unfold UNIT in *. nia. }
  assert (ML : m_maplen (MR st m') = 0).
  { destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [E0|NE0]; [exact E0|]. exfalso. destruct (g_top _ _ _ _ _ _ GO' NE0) as [S0 _]. lia. }
  split; [exact ML|]. destruct (g_nest _ _ _ _ _ _ GO' ML) as (p & ip & Hsl & _ & _ & CL & _).
  pose proof (is_total _ _ _ IS b m i (ex_intro _ ai Hb) Hi) as T. fold s in T. rewrite T in Hsl. injection Hsl as <- <-. lia.
Qed.

Lemma ne_on_chain k : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> ~ gempty st m ->
  m_sizeclass (MR st m) <= Z.of_nat k -> exists blk, In blk BL /\ forall f, (k < f)%nat -> In b (anc f st (bslot blk)).
Proof.
  induction k as [|k IH]; intros b m ai Hb NE Hc.
  - destruct (nonempty_slot b m ai Hb NE) as (i & Hi & F).
    destruct (inuse_slot b m ai i Hb Hi F) as [Hin|(m' & ai' & Hs & ML & CL & _)].
    + apply in_map_iff in Hin as (blk & Eb & Hin). exists blk. split; [exact Hin|]. intros f Hf. destruct f as [|f]; [lia|].
      cbn [anc]. rewrite Eb, (is_total _ _ _ IS b m i (ex_intro _ ai Hb) Hi), (hosts_base b m (ex_intro _ ai Hb)). left. reflexivity.
    + exfalso. pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hs)). lia.
  - destruct (nonempty_slot b m ai Hb NE) as (i & Hi & F).
    destruct (inuse_slot b m ai i Hb Hi F) as [Hin|(m' & ai' & Hs & ML & CL & _)].
    + apply in_map_iff in Hin as (blk & Eb & Hin). exists blk. split; [exact Hin|]. intros f Hf. destruct f as [|f]; [lia|].
      cbn [anc]. rewrite Eb, (is_total _ _ _ IS b m i (ex_intro _ ai Hb) Hi), (hosts_base b m (ex_intro _ ai Hb)). left. reflexivity.
    + assert (NE' : ~ gempty st m') by (intros G; destruct (e_top _ E _ m' (ex_intro _ ai' Hs) G) as [NZ _]; exact (NZ ML)).
      destruct (IH _ m' ai' Hs NE' ltac:(lia)) as (blk & Hblk & CH). exists blk. split; [exact Hblk|].
      intros f Hf. destruct f as [|f]; [lia|].
      rewrite <- (hosts_base b m (ex_intro _ ai Hb)).
      apply (anc_extend f (bslot blk) (slot_start' (MR st m) i) m' m i); [apply CH; lia| exists ai'; exact Hs| exact ML|].
      exact (is_total _ _ _ IS b m i (ex_intro _ ai Hb) Hi).
Qed.

Definition GL : list (aptr * ghdr) := map_to_list (s_groups st).
Definition gm (bh : aptr * ghdr) : aptr := default (0%N, 0) (g_meta (snd bh)).
Definition ne_b (bh : aptr * ghdr) : bool := negb (fmask (MR st (gm bh)) =? mask_upto (m_last_idx (MR st (gm bh)))).

Lemma GL_in b h : In (b, h) GL <-> s_groups st !! b = Some h.
Proof. unfold GL. rewrite <- elem_of_map_to_list. symmetry. apply list_elem_of_In. Qed.

Lemma GL_meta b h : In (b, h) GL -> exists ai, h = mkGhdr (Some (gm (b, h))) ai.
Proof.
  intros Hin. apply GL_in in Hin. destruct h as [[m|] ai]; [exists ai; reflexivity| exfalso; exact (ig_nometa _ _ _ IG _ _ Hin)].
Qed.

Lemma GL_nodup : NoDup (map fst GL).
Proof. unfold GL. exact (NoDup_fst_map_to_list _). Qed.

Lemma ngrp_GL : ngrp st = Z.of_nat (length GL).
Proof. unfold ngrp, GL. rewrite length_map_to_list. reflexivity. Qed.

Lemma nodup_incl_length {A} (l k : list A) : NoDup l -> (forall x, In x l -> In x k) -> (length l <= length k)%nat.
Proof.
  intros ND SUB. apply submseteq_length. apply NoDup_submseteq; [exact ND|].
  intros x Hx. apply list_elem_of_In. apply SUB. apply list_elem_of_In. exact Hx.
Qed.

Lemma NoDup_map_fst_filter {A B} (P : A * B -> bool) (l : list (A * B)) : NoDup (map fst l) -> NoDup (map fst (List.filter P l)).
Proof.
  induction l as [|x l IH]; intros ND; cbn; [constructor|]. cbn in ND. apply NoDup_cons in ND as [Nx ND].
  destruct (P x); [| apply IH; exact ND]. cbn. apply NoDup_cons. split; [| apply IH; exact ND].
  intros Hin. apply Nx. apply list_elem_of_In. apply list_elem_of_In in Hin. apply in_map_iff in Hin as (y & <- & Hy).
  apply filter_In in Hy as [Hy _]. apply in_map_iff. exists y. auto.
Qed.

Lemma length_flat_map_le {A B} (g : A -> list B) (l : list A) n : (forall x, length (g x) <= n)%nat -> (length (flat_map g l) <= n * length l)%nat.
Proof. intros H. induction l as [|x l IH]; cbn; [lia|]. rewrite length_app. pose proof (H x). lia. Qed.

Lemma ne_groups_bound : (length (List.filter ne_b GL) <= 64 * length BL)%nat.
Proof.
  transitivity (length (map fst (List.filter ne_b GL))); [rewrite length_map; lia|].
  transitivity (length (flat_map (fun blk => anc 64 st (bslot blk)) BL)); [| apply length_flat_map_le; intros; apply anc_length].
  apply nodup_incl_length; [exact (NoDup_map_fst_filter _ _ GL_nodup)|].
  intros b Hin. apply in_map_iff in Hin as ([b' h] & Eb & Hin). cbn in Eb. subst b'. apply filter_In in Hin as [Hin NEb].
  apply GL_in in Hin. destruct h as [[m|] ai]; [| exfalso; exact (ig_nometa _ _ _ IG _ _ Hin)].
  unfold ne_b in NEb. cbn [gm fst snd g_meta default] in NEb. apply Bool.negb_true_iff, Z.eqb_neq in NEb.
  pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hin)) as SC.
  destruct (ne_on_chain 63 b m ai Hin NEb ltac:(lia)) as (blk & Hblk & CH).
  apply in_flat_map. exists blk. split; [exact Hblk|]. apply CH. lia.
Qed.

Lemma e_groups_bound : (length (List.filter (fun bh => negb (ne_b bh)) GL) <= 32)%nat.
Proof.
  set (EL := List.filter (fun bh => negb (ne_b bh)) GL).
  assert (FACTS : forall b h, In (b, h) EL -> exists ai, s_groups st !! b = Some (mkGhdr (Some (gm (b, h))) ai) /\ gempty st (gm (b, h))
                    /\ 7 <= m_sizeclass (MR st (gm (b, h))) <= 38).
  { intros b h Hin. apply filter_In in Hin as [Hin Eb]. apply GL_in in Hin. destruct h as [[m|] ai]; [| exfalso; exact (ig_nometa _ _ _ IG _ _ Hin)].
    exists ai. unfold ne_b in Eb. cbn [gm fst snd g_meta default] in Eb |- *. rewrite Bool.negb_involutive in Eb. apply Z.eqb_eq in Eb.
    assert (G : gempty st m) by exact Eb.
    split; [exact Hin|]. split; [exact G|]. exact (proj2 (e_top _ E b m (ex_intro _ ai Hin) G)). }
  transitivity (length (map (fun bh => Z.to_nat (m_sizeclass (MR st (gm bh)) - 7)) EL)); [rewrite length_map; lia|].
  transitivity (length (seq 0 32)); [| rewrite length_seq; lia].
  apply nodup_incl_length.
  - assert (ND : NoDup (map fst EL)) by exact (NoDup_map_fst_filter _ _ GL_nodup).
    assert (INJ : forall b1 h1 b2 h2, In (b1, h1) EL -> In (b2, h2) EL -> m_sizeclass (MR st (gm (b1, h1))) = m_sizeclass (MR st (gm (b2, h2))) -> b1 = b2).
    { intros b1 h1 b2 h2 H1 H2 Ec. destruct (FACTS b1 h1 H1) as (a1 & G1 & E1 & _). destruct (FACTS b2 h2 H2) as (a2 & G2 & E2 & _).
      exact (e_uniq _ E b1 _ b2 _ (ex_intro _ a1 G1) (ex_intro _ a2 G2) E1 E2 Ec). }
    clearbody EL. induction EL as [|[b h] EL IH]; cbn; [constructor|].
    cbn in ND. apply NoDup_cons in ND as [Nb ND]. apply NoDup_cons. split.
    + intros Hin. apply list_elem_of_In in Hin. apply in_map_iff in Hin as ([b2 h2] & Ec & H2). apply Nb. apply list_elem_of_In.
      destruct (FACTS b h ltac:(left; reflexivity)) as (_ & _ & _ & R1). destruct (FACTS b2 h2 ltac:(right; exact H2)) as (_ & _ & _ & R2).
      rewrite (INJ b h b2 h2 ltac:(left; reflexivity) ltac:(right; exact H2) ltac:(lia)). apply in_map_iff. exists (b2, h2). auto.
    + apply IH; [intros; apply FACTS; right; assumption| exact ND| intros; eapply INJ; [right| right|]; eassumption].
  - intros x Hin. apply in_map_iff in Hin as ([b h] & <- & Hin). destruct (FACTS b h Hin) as (_ & _ & _ & R). apply in_seq. lia.
Qed.

Theorem ngrp_bound : ngrp st <= 64 * Z.of_nat (length BL) + 32.
Proof.
  rewrite ngrp_GL, <- (filter_length ne_b GL). pose proof ne_groups_bound. pose proof e_groups_bound. lia.
Qed.

Theorem nmeta_le_ngrp : (forall m, s_metas st !! m <> None -> m_mem (MR st m) <> None) -> nmeta st <= ngrp st.
Proof.
  intros ALL. unfold nmeta. rewrite ngrp_GL, <- length_map_to_list.
  set (ML := map_to_list (s_metas st)).
  assert (HM : forall m r, In (m, r) ML -> MR st m = r /\ exists b, m_mem r = Some b /\ hosts st b m).
  { intros m r Hin. unfold ML in Hin. apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
    assert (Er : MR st m = r) by (unfold MR, get_meta_rec; rewrite Hin; reflexivity). split; [exact Er|].
    destruct (m_mem r) as [b|] eqn:Em.
    - exists b. split; [reflexivity|]. destruct (im_group _ _ _ IM m b ltac:(rewrite Er; exact Em)) as [H|[]]. exact H.
    - exfalso. apply (ALL m); [rewrite Hin; discriminate| rewrite Er; exact Em]. }
  apply Nat2Z.inj_le.
  transitivity (length (map (fun mr : aptr * meta => gbase (snd mr)) ML)); [rewrite length_map; lia|].
  transitivity (length (map fst GL)); [| rewrite length_map; lia].
  apply nodup_incl_length.
  - assert (ND : NoDup (map fst ML)) by (unfold ML; exact (NoDup_fst_map_to_list _)).
    assert (INJ : forall m1 r1 m2 r2, In (m1, r1) ML -> In (m2, r2) ML -> gbase r1 = gbase r2 -> m1 = m2).
    { intros m1 r1 m2 r2 H1 H2 Eg. destruct (HM _ _ H1) as (E1 & b1 & M1 & B1). destruct (HM _ _ H2) as (E2 & b2 & M2 & B2).
      unfold gbase in Eg. rewrite M1, M2 in Eg. cbn in Eg. subst b2. exact (hosts_fun st b1 m1 m2 B1 B2). }
    clearbody ML. induction ML as [|[m r] ML IH]; cbn; [constructor|]. cbn in ND. apply NoDup_cons in ND as [Nm ND]. apply NoDup_cons. split.
    + intros Hin. apply list_elem_of_In in Hin. apply in_map_iff in Hin as ([m2 r2] & Eg & H2). cbn in Eg. apply Nm. apply list_elem_of_In.
      rewrite (INJ m r m2 r2 ltac:(left; reflexivity) ltac:(right; exact H2) (eq_sym Eg)). apply in_map_iff. exists (m2, r2). auto.
    + apply IH; [intros; apply HM; right; assumption| exact ND| intros; eapply INJ; [right| right|]; eassumption].
  - intros b Hin. apply in_map_iff in Hin as ([m r] & <- & Hin). destruct (HM _ _ Hin) as (Er & b & Mb & Hb). cbn [snd].
    unfold gbase. rewrite Mb. cbn [default]. destruct Hb as [ai Hb]. apply in_map_iff. exists (b, mkGhdr (Some m) ai). split; [reflexivity|].
    apply GL_in. exact Hb.
Qed.

Definition RL : list (N * region) := map_to_list (s_regions st).
Definition GR : list (N * region) := List.filter is_greg RL.

Definition te_b (kr : N * region) : bool :=
  match s_groups st !! (fst kr, 0) with
  | Some (mkGhdr (Some m) _) => fmask (MR st m) =? mask_upto (m_last_idx (MR st m))
  | _ => false
  end.

Lemma RL_nodup : NoDup (map fst RL).
Proof. unfold RL. exact (NoDup_fst_map_to_list _). Qed.

Lemma ngreg_GR : ngreg st = Z.of_nat (length GR).
Proof. reflexivity. Qed.

Lemma GR_top rid r : In (rid, r) GR -> s_regions st !! rid = Some r /\ r_kind r = RKGroup
  /\ exists m ai, s_groups st !! (rid, 0) = Some (mkGhdr (Some m) ai) /\ m_maplen (MR st m) <> 0.
Proof.
  intros Hin. apply filter_In in Hin as [Hin Hk]. unfold RL in Hin. apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
  unfold is_greg in Hk. cbn [snd] in Hk. destruct (r_kind r) eqn:Ek; try discriminate.
  split; [exact Hin|]. split; [reflexivity|].
  destruct (ig_top _ _ _ IG rid r Hin Ek ltac:(discriminate)) as (m & [ai Hm] & ML). exists m, ai. auto.
Qed.

Lemma anc_tail_small f : forall s b0 rest b m', anc f st s = b0 :: rest -> In b rest -> hosts st b m' -> m_sizeclass (MR st m') < 48.
Proof.
  induction f as [|f IH]; intros s b0 rest b m' Ea Hin Hb; [discriminate|]. cbn [anc] in Ea.
  destruct (s_slots st !! s) as [[m0 i0]|] eqn:E0; [| discriminate]. injection Ea as Eb0 Er. subst rest.
  destruct (Z.eqb_spec (m_maplen (MR st m0)) 0) as [ML|ML]; [| destruct Hin].
  destruct (is_valid _ _ _ IS s m0 i0 E0) as ([c0 Hc0] & _ & _). rewrite (hosts_base c0 m0 Hc0) in Eb0, Hin. subst c0.
  destruct (hosts_ok x0 st LS IG b0 m0 Hc0) as (a0 & G0 & GO0).
  destruct (g_nest _ _ _ _ _ _ GO0 ML) as (p & ip & Hsl & _ & _ & CL & _).
  destruct f as [|f']; [destruct Hin|]. cbn [anc] in Hin. rewrite Hsl in Hin.
  destruct (is_valid _ _ _ IS b0 p ip Hsl) as ([c1 Hc1] & _ & _). rewrite (hosts_base c1 p Hc1) in Hin.
  destruct Hin as [<-|Hin].
  - pose proof (hosts_fun st c1 p m' Hc1 Hb) as <-. lia.
  - apply (IH b0 c1 (if m_maplen (MR st p) =? 0 then anc f' st c1 else []) b m'); [| | exact Hb].
    + cbn [anc]. rewrite Hsl, (hosts_base c1 p Hc1). reflexivity.
    + destruct (m_maplen (MR st p) =? 0); [exact Hin| destruct Hin].
Qed.

Lemma anc_head f s b0 rest : anc f st s = b0 :: rest -> exists m0 i0, s_slots st !! s = Some (m0, i0) /\ b0 = gbase (MR st m0).
Proof.
  destruct f as [|f]; cbn [anc]; [discriminate|]. destruct (s_slots st !! s) as [[m0 i0]|]; [| discriminate].
  intros Ea. injection Ea as <- _. exists m0, i0. split; reflexivity.
Qed.

Variable SZ : list (aptr * Z).
Hypothesis L63H : L63 st SZ.
Hypothesis SZP : Permutation (map fst SZ) (map bslot BL).

Lemma mmap_len_round x : mmap_len x = round_up_pg x.
Proof. rewrite round_up_pg_eq. reflexivity. Qed.

Lemma csz_ge n : 2 ^ 20 <= csz n.
Proof. unfold csz. lia. Qed.

Lemma small_top_region rid r m ai : s_regions st !! rid = Some r -> s_groups st !! (rid, 0) = Some (mkGhdr (Some m) ai) ->
  m_maplen (MR st m) <> 0 -> m_sizeclass (MR st m) < 48 -> mmap_len (r_len r) <= 2 ^ 20.
Proof.
  intros Hr Hm ML SC. pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO.
  destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r' & Hr' & _ & Hlen & _). cbn [fst] in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
  destruct (g_sc _ _ _ _ _ _ GO) as [[_ MLB]|[SC' _]]; [| lia].
  rewrite mmap_len_round, <- Hlen. lia.
Qed.

Lemma ne_region_block rid r : In (rid, r) GR -> te_b (rid, r) = false ->
  exists e, In e SZ /\ fst (fst e) = rid /\ mmap_len (r_len r) <= csz (snd e).
Proof.
  intros Hin Te. destruct (GR_top rid r Hin) as (Hr & Hk & m & ai & Hm & ML).
  unfold te_b in Te. cbn [fst] in Te. rewrite Hm in Te. apply Z.eqb_neq in Te.
  pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hm)) as SC.
  destruct (ne_on_chain 63 (rid, 0) m ai Hm Te ltac:(lia)) as (blk & Hblk & CH). specialize (CH 64%nat ltac:(lia)).
  pose proof (anc_rid 64 (bslot blk) (rid, 0) CH) as Erid. cbn [fst] in Erid.
  assert (HinS : In (bslot blk) (map fst SZ)) by (apply (Permutation_in _ (Permutation_sym SZP)); apply in_map_iff; exists blk; auto).
  apply in_map_iff in HinS as ([c n] & Ec & HinS). cbn in Ec. subst c.
  exists (bslot blk, n). split; [exact HinS|]. split; [cbn; symmetry; exact Erid|]. cbn [snd].
  destruct SC as [[SC _]|(SC & LI0 & _)].
  - pose proof (small_top_region rid r m ai Hr Hm ML ltac:(lia)). pose proof (csz_ge n). lia.
  -
    destruct (anc 64 st (bslot blk)) as [|b0 rest] eqn:Ea; [destruct CH|].
    assert (Eb0 : b0 = (rid, 0)).
    { destruct CH as [E0|Hin']; [exact E0|]. exfalso. pose proof (anc_tail_small 64 (bslot blk) b0 rest (rid, 0) m Ea Hin' (ex_intro _ ai Hm)). lia. }
    subst b0. destruct (anc_head 64 (bslot blk) _ _ Ea) as (m0 & i0 & E0 & Eg).
    destruct (is_valid _ _ _ IS _ m0 i0 E0) as ([c0 Hc0] & Hi0 & Es). rewrite (hosts_base c0 m0 Hc0) in Eg. subst c0.
    pose proof (hosts_fun st (rid, 0) m0 m Hc0 (ex_intro _ ai Hm)) as ->.
    destruct (L63H (bslot blk) n m i0 HinS E0 SC) as (r2 & Hr2 & _ & Hl2). rewrite <- Erid in Hr2. rewrite Hr in Hr2. injection Hr2 as <-.
    rewrite Hl2. unfold csz. lia.
Qed.

Lemma zsum_filter_split {A} (w : A -> Z) (f : A -> bool) (l : list A) :
  zsum (map w l) = zsum (map w (List.filter f l)) + zsum (map w (List.filter (fun x => negb (f x)) l)).
Proof. induction l as [|x l IH]; cbn [map List.filter]; [reflexivity|]. destruct (f x); cbn [negb map]; rewrite !zsum_cons; lia. Qed.

Lemma zsum_le_const {A} (w : A -> Z) (c : Z) (l : list A) : 0 <= c -> (forall x, In x l -> w x <= c) -> zsum (map w l) <= c * Z.of_nat (length l).
Proof.
  intros Hc H. induction l as [|x l IH]; cbn [map length]; [cbn; lia|]. rewrite zsum_cons. pose proof (H x ltac:(left; reflexivity)).
  specialize (IH ltac:(intros; apply H; right; assumption)). lia.
Qed.

Lemma zsum_nonneg {A} (w : A -> Z) (l : list A) : (forall x, In x l -> 0 <= w x) -> 0 <= zsum (map w l).
Proof.
  intros H. induction l as [|x l IH]; cbn [map]; [cbn; lia|]. rewrite zsum_cons. pose proof (H x ltac:(left; reflexivity)).
  specialize (IH ltac:(intros; apply H; right; assumption)). lia.
Qed.

Lemma zsum_rel_inj {A B} (R : A -> B -> Prop) (w : A -> Z) (g : B -> Z) :
  forall (l1 : list A) (l2 : list B), NoDup l1 -> (forall b, In b l2 -> 0 <= g b) ->
  (forall a, In a l1 -> exists b, In b l2 /\ R a b /\ w a <= g b) ->
  (forall a a' b, In a l1 -> In a' l1 -> R a b -> R a' b -> a = a') ->
  zsum (map w l1) <= zsum (map g l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 ND G0 EX INJ; cbn [map].
  - change (zsum []) with 0. exact (zsum_nonneg g l2 G0).
  - rewrite zsum_cons. apply NoDup_cons in ND as [Na ND].
    destruct (EX a ltac:(left; reflexivity)) as (b & Hb & Rab & Wab).
    apply in_split in Hb as (l2a & l2b & ->).
    assert (P : Permutation (map g (l2a ++ b :: l2b)) (g b :: map g (l2a ++ l2b))).
    { rewrite !map_app. cbn. apply Permutation_sym. apply Permutation_middle. }
    rewrite (zsum_perm _ _ P), zsum_cons.
    enough (zsum (map w l1) <= zsum (map g (l2a ++ l2b))) by lia.
    apply IH; [exact ND| intros b' Hb'; apply G0; apply in_app_iff in Hb' as [?|?]; apply in_app_iff; [left| right; right]; assumption| |].
    + intros a' Ha'. destruct (EX a' ltac:(right; exact Ha')) as (b' & Hb' & Ra'b' & Wa'b'). exists b'. split; [| auto].
      apply in_app_iff in Hb' as [H|[<-|H]]; [apply in_app_iff; left; exact H| | apply in_app_iff; right; exact H].
      exfalso. pose proof (INJ a a' b ltac:(left; reflexivity) ltac:(right; exact Ha') Rab Ra'b') as <-. apply Na. apply list_elem_of_In. exact Ha'.
    + intros a1 a2 b' H1 H2. apply INJ; right; assumption.
Qed.

Lemma e_regions_bound : (length (List.filter te_b GR) <= 32)%nat.
Proof.
  set (EL := List.filter te_b GR).
  assert (FACTS : forall rid r, In (rid, r) EL -> exists m ai, s_groups st !! (rid, 0) = Some (mkGhdr (Some m) ai) /\ gempty st m /\ 7 <= m_sizeclass (MR st m) <= 38).
  { intros rid r Hin. apply filter_In in Hin as [Hin Te]. destruct (GR_top rid r Hin) as (Hr & _ & m & ai & Hm & ML).
    unfold te_b in Te. cbn [fst] in Te. rewrite Hm in Te. apply Z.eqb_eq in Te. exists m, ai. split; [exact Hm|]. split; [exact Te|].
    exact (proj2 (e_top _ E _ m (ex_intro _ ai Hm) Te)). }
  assert (ND : NoDup (map fst EL)) by exact (NoDup_map_fst_filter _ _ (NoDup_map_fst_filter _ _ RL_nodup)).
  transitivity (length (map (fun kr : N * region => match s_groups st !! (fst kr, 0) with Some (mkGhdr (Some m) _) => Z.to_nat (m_sizeclass (MR st m) - 7) | _ => 0%nat end) EL)); [rewrite length_map; lia|].
  transitivity (length (seq 0 32)); [| rewrite length_seq; lia].
  apply nodup_incl_length.
  + assert (INJ : forall k1 r1 k2 r2 m1 a1 m2 a2, In (k1, r1) EL -> In (k2, r2) EL ->
              s_groups st !! (k1, 0) = Some (mkGhdr (Some m1) a1) -> s_groups st !! (k2, 0) = Some (mkGhdr (Some m2) a2) ->
              m_sizeclass (MR st m1) = m_sizeclass (MR st m2) -> k1 = k2).
    { intros k1 r1 k2 r2 m1 a1 m2 a2 H1 H2 G1 G2 Ec.
      destruct (FACTS k1 r1 H1) as (m1' & a1' & G1' & E1 & _). rewrite G1 in G1'. injection G1' as <- <-.
      destruct (FACTS k2 r2 H2) as (m2' & a2' & G2' & E2 & _). rewrite G2 in G2'. injection G2' as <- <-.
      pose proof (e_uniq _ E (k1, 0) m1 (k2, 0) m2 (ex_intro _ a1 G1) (ex_intro _ a2 G2) E1 E2 Ec) as Ek. injection Ek as Ek'. exact Ek'. }
    clearbody EL. induction EL as [|[k r] EL IH]; cbn [map]; [constructor|].
    cbn in ND. apply NoDup_cons in ND as [Nk ND]. apply NoDup_cons. split.
    * intros Hin. apply list_elem_of_In in Hin. apply in_map_iff in Hin as ([k2 r2] & Ec & H2). apply Nk. apply list_elem_of_In.
      destruct (FACTS k r ltac:(left; reflexivity)) as (m1 & a1 & G1 & _ & R1). destruct (FACTS k2 r2 ltac:(right; exact H2)) as (m2 & a2 & G2 & _ & R2).
      cbn [fst] in Ec. rewrite G1, G2 in Ec.
      rewrite (INJ k r k2 r2 m1 a1 m2 a2 ltac:(left; reflexivity) ltac:(right; exact H2) G1 G2 ltac:(lia)). apply in_map_iff. exists (k2, r2). auto.
    * apply IH; [intros rid' r' Hin'; exact (FACTS rid' r' (or_intror Hin'))| exact ND| intros; eapply INJ; [right| right| | |]; eassumption].
  + intros x Hin. apply in_map_iff in Hin as ([k r] & <- & Hin). destruct (FACTS k r Hin) as (m & a & G & _ & R). cbn [fst]. rewrite G. apply in_seq. lia.
Qed.

Definition wgr (kr : N * region) : Z := mmap_len (r_len (snd kr)).

Theorem group_bytes_bound : zsum (map wgr GR) <= zsum (map (fun e => csz (snd e)) SZ) + 32 * 2 ^ 20.
Proof.
  rewrite (zsum_filter_split wgr te_b GR).
  assert (TE : zsum (map wgr (List.filter te_b GR)) <= 2 ^ 20 * 32).
  { transitivity (2 ^ 20 * Z.of_nat (length (List.filter te_b GR))).
    - apply zsum_le_const; [lia|]. intros [rid r] Hin. apply filter_In in Hin as [Hin Te]. destruct (GR_top rid r Hin) as (Hr & _ & m & ai & Hm & ML).
      unfold te_b in Te. cbn [fst] in Te. rewrite Hm in Te. apply Z.eqb_eq in Te.
      pose proof (e_top _ E _ m (ex_intro _ ai Hm) Te) as [_ SC]. unfold wgr. cbn [snd]. exact (small_top_region rid r m ai Hr Hm ML ltac:(lia)).
    - pose proof e_regions_bound. nia. }
  assert (TN : zsum (map wgr (List.filter (fun x => negb (te_b x)) GR)) <= zsum (map (fun e => csz (snd e)) SZ)).
  { apply (zsum_rel_inj (fun kr e => fst (fst e) = fst kr)).
    - apply (NoDup_fmap_1 fst). exact (NoDup_map_fst_filter _ _ (NoDup_map_fst_filter _ _ RL_nodup)).
    - intros e _. cbn beta. etransitivity; [| exact (csz_ge (snd e))]. apply Z.pow_nonneg. lia.
    - intros [rid r] Hin. apply filter_In in Hin as [Hin Te]. apply Bool.negb_true_iff in Te.
      destruct (ne_region_block rid r Hin Te) as (e & He & Ef & W). exists e. split; [exact He|]. split; [exact Ef| exact W].
    - intros [k1 r1] [k2 r2] e H1 H2 E1 E2. cbn [fst] in E1, E2. subst k1 k2.
      apply filter_In in H1 as [H1 _]. apply filter_In in H2 as [H2 _]. apply filter_In in H1 as [H1 _]. apply filter_In in H2 as [H2 _].
      unfold RL in H1, H2. apply list_elem_of_In in H1. apply list_elem_of_In in H2. apply elem_of_map_to_list in H1. apply elem_of_map_to_list in H2.
      rewrite H1 in H2. injection H2 as ->. reflexivity. }
  lia.
Qed.

Theorem group_regions_bound : ngreg st <= Z.of_nat (length BL) + 32.
Proof.
  rewrite ngreg_GR, <- (filter_length te_b GR).
  enough ((length (List.filter te_b GR) <= 32)%nat /\ (length (List.filter (fun x => negb (te_b x)) GR) <= length BL)%nat) by lia.
  split; [exact e_regions_bound|].
  - transitivity (length (map (fun kr : N * region => fst kr) (List.filter (fun x => negb (te_b x)) GR))); [rewrite length_map; lia|].
    transitivity (length (map (fun blk => fst (bslot blk)) BL)); [| rewrite length_map; lia].
    apply nodup_incl_length; [exact (NoDup_map_fst_filter _ _ (NoDup_map_fst_filter _ _ RL_nodup))|].
    intros rid Hin. apply in_map_iff in Hin as ([rid' r] & E0 & Hin). cbn in E0. subst rid'.
    apply filter_In in Hin as [Hin Te]. apply Bool.negb_true_iff in Te.
    destruct (ne_region_block rid r Hin Te) as ([c n] & He & Ef & _). cbn in Ef. subst rid.
    assert (Hc : In c (map bslot BL)) by (apply (Permutation_in _ SZP); apply in_map_iff; exists (c, n); auto).
    apply in_map_iff in Hc as (blk & <- & Hblk). apply in_map_iff. exists blk. auto.
Qed.

End ST.

Definition wbrk (r : region) : Z := match r_kind r with RKBrk => 2 * r_len r | _ => 0 end.
Definition wgrp (r : region) : Z := match r_kind r with RKGroup => mmap_len (r_len r) | _ => 0 end.

Lemma wreg_split r : wreg r = wgrp r + metalen r + wbrk r.
Proof. unfold wreg, wgrp, metalen, wbrk. destruct (r_kind r); lia. Qed.

Lemma zsum_map_add {A} (f g : A -> Z) l : zsum (map (fun x => f x + g x) l) = zsum (map f l) + zsum (map g l).
Proof. induction l as [|x l IH]; cbn [map]; [reflexivity|]. rewrite !zsum_cons. lia. Qed.

Lemma zsum_map_ext {A} (f g : A -> Z) l : (forall x, In x l -> f x = g x) -> zsum (map f l) = zsum (map g l).
Proof. intros H. induction l as [|x l IH]; cbn [map]; [reflexivity|]. rewrite !zsum_cons, (H x ltac:(left; reflexivity)), IH; [reflexivity|]. intros; apply H; right; assumption. Qed.

Lemma zsum_filter_zero {A} (w : A -> Z) (f : A -> bool) l : (forall x, In x l -> f x = false -> w x = 0) ->
  zsum (map w l) = zsum (map w (List.filter f l)).
Proof.
  intros H. rewrite (zsum_filter_split w f l).
  enough (zsum (map w (List.filter (fun x => negb (f x)) l)) = 0) by lia.
  transitivity (zsum (map (fun _ => 0) (List.filter (fun x => negb (f x)) l))).
  - apply zsum_map_ext. intros x Hx. apply filter_In in Hx as [Hx Hf]. apply H; [exact Hx|]. destruct (f x); [discriminate| reflexivity].
  - induction (List.filter _ l) as [|y k IH]; cbn [map]; [reflexivity| rewrite zsum_cons; lia].
Qed.

Section BOUNDS.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (SZ : list (aptr * Z)).
Hypothesis INV : INVC x0 st L BL LS.
Hypothesis E : EINV st.
Hypothesis L63H : L63 st SZ.
Hypothesis SZP : Permutation (map fst SZ) (map bslot BL).
Hypothesis MA : MARITH st.
Let CU : CURI st := CURI_of _ _ _ _ _ INV.

Lemma brk_regions_bound : zsum (map (fun kr : N * region => wbrk (snd kr)) (RL st)) <= 2 * PGSZ * (1 + nareas st).
Proof.
  set (isbrk := fun kr : N * region => match r_kind (snd kr) with RKBrk => true | _ => false end).
  rewrite (zsum_filter_zero _ isbrk); [| intros [rid r] _ Hf; unfold isbrk, wbrk in *; cbn [snd] in *; destruct (r_kind r); try discriminate; reflexivity].
  assert (IN : forall rid r, In (rid, r) (List.filter isbrk (RL st)) -> s_regions st !! rid = Some r /\ r_kind r = RKBrk).
  { intros rid r Hin. apply filter_In in Hin as [Hin Hb]. unfold RL in Hin. apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
    split; [exact Hin|]. unfold isbrk in Hb. cbn [snd] in Hb. destruct (r_kind r); try discriminate; reflexivity. }
  assert (LEN : (length (List.filter isbrk (RL st)) <= 1)%nat).
  { pose proof (NoDup_map_fst_filter isbrk _ (RL_nodup st)) as ND.
    destruct (List.filter isbrk (RL st)) as [|[k1 r1] [|[k2 r2] rest]] eqn:EF; cbn; [lia| lia|]. exfalso.
    destruct (IN k1 r1 ltac:(left; reflexivity)) as [H1 K1]. destruct (IN k2 r2 ltac:(right; left; reflexivity)) as [H2 K2].
    pose proof (cu_brk1 _ CU k1 k2 r1 r2 H1 H2 K1 K2) as ->. cbn in ND. apply NoDup_cons in ND as [N1 _]. apply N1. left. }
  pose proof (nareas_nonneg := Nat2Z.is_nonneg (size (s_areas st))). fold (nareas st) in nareas_nonneg.
  transitivity (2 * PGSZ * (1 + nareas st) * Z.of_nat (length (List.filter isbrk (RL st)))); [| unfold PGSZ; nia].
  apply zsum_le_const; [unfold PGSZ; nia|]. intros [rid r] Hin. destruct (IN rid r Hin) as [Hr Hk]. cbn [snd]. unfold wbrk. rewrite Hk.
  pose proof (ma_brki _ MA rid r Hr Hk). lia.
Qed.

Theorem Phi_bound : Phi st <= zsum (map (fun e => csz (snd e)) SZ) + 32 * 2 ^ 20 + PGSZ * (6 * nareas st + 8).
Proof.
  rewrite Phi_regsum. unfold regsum.
  rewrite (zsum_map_ext _ (fun kr : N * region => (wgrp (snd kr) + metalen (snd kr)) + wbrk (snd kr))) by (intros; apply wreg_split).
  rewrite !zsum_map_add. fold (RL st). change (zsum (map (fun x : N * region => metalen (snd x)) (RL st))) with (regsum metalen st).
  pose proof (ma_mbi _ MA) as MB. pose proof (ma_shi _ MA) as SH. pose proof brk_regions_bound as BB.
  assert (GB : zsum (map (fun x : N * region => wgrp (snd x)) (RL st)) <= zsum (map (fun e => csz (snd e)) SZ) + 32 * 2 ^ 20).
  { rewrite (zsum_filter_zero _ is_greg); [| intros [rid r] _ Hf; unfold is_greg, wgrp in *; cbn [snd] in *; destruct (r_kind r); try discriminate; reflexivity].
    fold (GR st). rewrite (zsum_map_ext _ (wgr)); [exact (group_bytes_bound st L BL LS INV E SZ L63H SZP)|].
    intros [rid r] Hin. destruct (GR_top st L BL LS INV rid r Hin) as (_ & Hk & _). unfold wgrp, wgr. cbn [snd]. rewrite Hk. reflexivity. }
  assert (BD : brk_dead_w st <= 2 * PGSZ) by (unfold brk_dead_w; destruct (c_brk (s_ctx st)); unfold PGSZ; lia).
  unfold PGSZ in *. nia.
Qed.

Theorem Psi_bound : Psi st <= Z.of_nat (length BL) + 32 + 4 * nareas st.
Proof. unfold Psi. pose proof (group_regions_bound st L BL LS INV E SZ L63H SZP). lia. Qed.

Theorem pot_bound : pot st <= NSLOTS * (2 + 2 * nareas st).
Proof.
  unfold pot, am_pot. pose proof (ma_shi _ MA) as SH. pose proof (cu_avail _ CU) as [[A0 _] _]. pose proof (cu_cursor _ CU) as [C0 _].
  unfold NSLOTS in *. nia.
Qed.

Theorem nareas_bound : NSLOTS * nareas st <= nmeta st + NSLOTS.
Proof. pose proof (ma_cnti _ MA). pose proof (cu_avail _ CU) as [[_ A1] _]. lia. Qed.

End BOUNDS.

Definition CM (K : Z) : Z := 64 * (K + 32) + 32.

Record RES (cs : mstate) (SZ : list (aptr * Z)) (K : Z) : Prop := mkRES {
  rs_einv : EINV cs;
  rs_nlk : NLK cs;
  rs_l63 : L63 cs SZ;
  rs_marith : MARITH cs;
  rs_nmeta : nmeta cs <= CM K
}.

End HMRES.

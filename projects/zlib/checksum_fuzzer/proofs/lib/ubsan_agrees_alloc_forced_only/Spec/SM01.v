(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require PropExec.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require MState.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require KInv.
From stdpp Require gmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_Inv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_List.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_Ext.
From Stdlib Require Wf_nat.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Mem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Exec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module KStep.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool. From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import MState. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode.
Import SM09. Import SM09.Prelim. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv.
Import ListNotations.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).


Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
  intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
  assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
  intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
  pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
  pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
  pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
  nia.
Qed.

Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. apply mmap_len_bound. assumption. Qed.

Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.

Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.

Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. rewrite alloc_ceiling_val. lia. Qed.
Lemma alloc_ceiling_lo_lt : alloc_ceiling_lo <= alloc_ceiling.
Proof. rewrite alloc_ceiling_val, alloc_ceiling_lo_val. lia. Qed.
Lemma alloc_top_lt64 : forall h, alloc_top h < 2^64 - 2^23.
Proof. intros h. unfold alloc_top, stack_max_size. pose proof (bv_unsigned_in_range 64 (vm_init_sp h)) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
End KStep.

Module MI_Arith.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc.
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma size_classes_length : length size_classes = 48%nat.
Proof. reflexivity. Qed.

Lemma size_classes_bounds : Forall (fun x => 1 <= x <= 8191) size_classes.
Proof.
  apply Forall_forall. intros x Hx. unfold size_classes in Hx.
  repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
Qed.

Lemma size_class_bound sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  apply (Forall_forall (fun x => 1 <= x <= 8191) size_classes); [apply size_classes_bounds|].
  apply nth_In. rewrite size_classes_length. lia.
Qed.

Lemma mask_upto_nonneg k : 0 <= k -> 0 <= mask_upto k.
Proof. intros. unfold mask_upto. assert (0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

Lemma testbit_mask_upto k i : 0 <= k -> 0 <= i -> Z.testbit (mask_upto k) i = (i <=? k).
Proof.
  intros Hk Hi. unfold mask_upto. replace (2 ^ (k + 1) - 1) with (Z.pred (2 ^ (k + 1))) by lia.
  rewrite <- Z.ones_equiv. destruct (Z.leb_spec i k).
  - apply Z.ones_spec_low. lia.
  - apply Z.ones_spec_high. lia.
Qed.

Lemma testbit_bit i j : 0 <= i -> 0 <= j -> Z.testbit (bit i) j = (i =? j).
Proof.
  intros Hi Hj. unfold bit. destruct (Z.eqb_spec i j) as [<-|NE].
  - apply Z.pow2_bits_true. exact Hi.
  - apply Z.pow2_bits_false. lia.
Qed.

Lemma bits_below_bound n a : 0 <= a -> 0 <= n -> (forall i, 0 <= i -> Z.testbit a i = true -> i < n) -> a < 2 ^ n.
Proof.
  intros Ha Hn Hb. destruct (Z.lt_ge_cases a (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
  assert (Hl : n <= Z.log2 a) by (apply Z.log2_le_pow2; lia).
  assert (Ht : Z.testbit a (Z.log2 a) = true) by (apply Z.bit_log2; lia).
  specialize (Hb (Z.log2 a) ltac:(apply Z.log2_nonneg) Ht). lia.
Qed.

Lemma testbit_false_above n a i : 0 <= a < 2 ^ n -> n <= i -> Z.testbit a i = false.
Proof.
  intros Ha Hi. destruct (Z.eq_dec a 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
  apply (Z.lt_le_trans _ (2 ^ n)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
End MI_Arith.

Module MI_Ext2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Inv. Import SM08.MI_Kit. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_List. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Ext.
Import ListNotations.
Local Open Scope Z_scope.

Section EXT2.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).

Lemma inv_M_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> inv_M X st LS -> inv_M X st' LS.
Proof.
  intros HM HG I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

Lemma inv_L_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> (forall h, get_head st' h = get_head st h) ->
  inv_L st LS -> inv_L st' LS.
Proof.
  intros HM HG HE I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

Lemma group_ok_ext m b ai : s_metas st' = s_metas st -> s_slots st' = s_slots st ->
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> fst b = rid -> s_regions st' !! rid = Some r) ->
  group_ok X st LS m b ai -> group_ok X st' LS m b ai.
Proof.
  intros HM HS HR I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HS; try assumption.
  - intros Hml. destruct (G13 Hml) as (H0 & r & Hr & Hk & E1 & E2). split; [exact H0|]. exists r. split; [| auto]. apply HR; auto.
  - intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

Lemma inv_S_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> s_slots st' = s_slots st ->
  inv_S X st BL -> inv_S X st' BL.
Proof.
  intros HM HG HS I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
Qed.
End EXT2.
End MI_Ext2.

Module MI_Geom.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia. From Stdlib Require Import Wf_nat.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Inv. Import SM08. Import SM08.MI_Kit. Import MI_Arith.
Import ListNotations.
Local Open Scope Z_scope.

Section GEOM.
Variable X : extras.
Variable st : mstate.
Variable L : mled.
Variable BL : list blk.
Variable LS : lhead -> list aptr.
Hypothesis IM : inv_M X st LS.
Hypothesis IG : inv_G X st LS.
Hypothesis IS : inv_S X st BL.
Local Notation R := (MR st).


Lemma hosts_gbase b m : hosts st b m -> gbase (R m) = b.
Proof.
  intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst.
  unfold gbase, MR. rewrite Hmem. reflexivity.
Qed.

Lemma hosts_mem b m : hosts st b m -> m_mem (R m) = Some b.
Proof.
  intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst. exact Hmem.
Qed.

Lemma hosts_inj b1 b2 m : hosts st b1 m -> hosts st b2 m -> b1 = b2.
Proof. intros H1 H2. pose proof (hosts_mem _ _ H1). pose proof (hosts_mem _ _ H2). congruence. Qed.

Lemma hosts_fun b m1 m2 : hosts st b m1 -> hosts st b m2 -> m1 = m2.
Proof. intros [a1 H1] [a2 H2]. rewrite H1 in H2. inversion H2. reflexivity. Qed.

Lemma hosts_ok b m : hosts st b m -> exists ai, s_groups st !! b = Some (mkGhdr (Some m) ai) /\ group_ok X st LS m b ai.
Proof. intros [ai H]. exists ai. split; [exact H|]. exact (ig_ok _ _ _ IG _ _ _ H). Qed.

Lemma live_hosts m : live_group st m -> exists b, hosts st b m.
Proof. intros H. exact H. Qed.

Lemma slot_start'_eq m b i : hosts st b m -> slot_start' (R m) i = (fst b, sstart (R m) i).
Proof. intros H. rewrite slot_start'_sstart. rewrite (hosts_gbase _ _ H). reflexivity. Qed.

Lemma stride_cases b m : hosts st b m ->
  get_stride (R m) = UNIT * size_class (m_sizeclass (R m)) /\ 0 <= m_sizeclass (R m) < 48
  \/ get_stride (R m) = m_maplen (R m) * 4096 - UNIT /\ m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0.
Proof.
  intros H. destruct (hosts_ok _ _ H) as (ai & Hg & GO). unfold get_stride.
  destruct (Z.eqb_spec (m_last_idx (R m)) 0) as [E|NE]; cbn.
  - destruct (Z.eqb_spec (m_maplen (R m)) 0) as [E2|NE2]; cbn.
    + left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
    + right. auto.
  - left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
Qed.

Lemma stride_ge b m : hosts st b m -> UNIT <= get_stride (R m) /\ get_stride (R m) mod UNIT = 0.
Proof.
  intros H. destruct (stride_cases _ _ H) as [[E Hsc]|(E & _ & NZ)]; rewrite E.
  - pose proof (size_class_bound _ Hsc). unfold UNIT. split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT. split; [lia|].
    replace (m_maplen (R m) * 4096 - 16) with ((m_maplen (R m) * 256 - 1) * 16) by lia. apply Z_mod_mult.
Qed.


Lemma sstart_mono b m i j : hosts st b m -> i <= j -> sstart (R m) i <= sstart (R m) j.
Proof. intros H Hij. unfold sstart. destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. Qed.

Lemma sstart_succ m i : sstart (R m) (i + 1) = sstart (R m) i + get_stride (R m).
Proof. unfold sstart. lia. Qed.

Lemma sstart_lt b m i j : hosts st b m -> i < j -> sstart (R m) i + get_stride (R m) <= sstart (R m) j.
Proof. intros H Hij. rewrite <- sstart_succ. apply (sstart_mono _ _ _ _ H). lia. Qed.

Lemma sstart0 b m : hosts st b m -> sstart (R m) 0 = snd b + UNIT.
Proof. intros H. unfold sstart. rewrite (hosts_gbase _ _ H). lia. Qed.

Lemma gend_eq m : gend (R m) = sstart (R m) (m_last_idx (R m) + 1).
Proof. reflexivity. Qed.


Definition child (c p : aptr) (i : Z) : Prop :=
  exists b, hosts st b c /\ m_maplen (R c) = 0 /\ s_slots st !! b = Some (p, i).

Inductive anc : aptr -> aptr -> Z -> aptr -> Prop :=
| anc_child c p i : child c p i -> anc c p i c
| anc_step m c j c' p i : anc m c j c' -> child c p i -> anc m p i c.

Lemma child_facts c p i : child c p i ->
  exists bc bp, hosts st bc c /\ hosts st bp p /\ fst bc = fst bp /\ 0 <= i <= m_last_idx (R p)
    /\ bc = (fst bp, sstart (R p) i)
    /\ sstart (R p) i = snd bc /\ gend (R c) <= sstart (R p) (i + 1)
    /\ m_sizeclass (R c) < m_sizeclass (R p) < 48.
Proof.
  intros (bc & Hc & Hml & Hsl).
  destruct (is_valid _ _ _ IS _ _ _ Hsl) as (Hlive & Hi & Hs).
  destruct Hlive as [bp Hp].
  destruct (hosts_ok _ _ Hc) as (ai & Hg & GO).
  destruct (g_nest _ _ _ _ _ _ GO Hml) as (p' & i' & Hsl' & Hfst & Hend & Hsc & Hstr).
  rewrite Hsl in Hsl'. inversion Hsl'; subst p' i'.
  exists bc, bp. rewrite (slot_start'_eq _ _ _ Hp) in Hs.
  repeat split; auto; try lia.
  - rewrite Hs. reflexivity.
  - rewrite Hs. reflexivity.
  - rewrite sstart_succ. exact Hend.
Qed.

Lemma anc_facts m p i c : anc m p i c ->
  exists bm bp, hosts st bm m /\ hosts st bp p /\ fst bm = fst bp /\ 0 <= i <= m_last_idx (R p)
    /\ child c p i /\ (m = c \/ exists j c', anc m c j c')
    /\ sstart (R p) i <= snd bm /\ gend (R m) <= sstart (R p) (i + 1)
    /\ m_sizeclass (R m) < m_sizeclass (R p) < 48.
Proof.
  induction 1 as [c p i Hch|m c j c' p i Ha IH Hch].
  - destruct (child_facts _ _ _ Hch) as (bc & bp & Hc & Hp & Hfst & Hi & Hbc & Hs & Hend & Hsc).
    exists bc, bp. repeat split; auto; lia.
  - destruct IH as (bm & bc & Hm & Hc & Hfst & Hj & Hch' & _ & Hs & Hend & Hsc).
    destruct (child_facts _ _ _ Hch) as (bc' & bp & Hc' & Hp & Hfst' & Hi & Hbc & Hs' & Hend' & Hsc').
    pose proof (hosts_inj _ _ _ Hc Hc') as E.
    pose proof (sstart0 _ _ Hc). pose proof (sstart_mono _ _ 0 j Hc ltac:(lia)).
    pose proof (sstart_mono _ _ (j + 1) (m_last_idx (R c) + 1) Hc ltac:(lia)). rewrite <- gend_eq in *.
    subst bc bc'. cbn [fst snd] in *.
    exists bm, bp. split; [exact Hm|]. split; [exact Hp|]. split; [congruence|]. split; [exact Hi|].
    split; [exact Hch|]. split; [right; eauto|].
    unfold UNIT in *. repeat split; lia.
Qed.

Lemma anc_irrefl m i c : anc m m i c -> False.
Proof. intros H. destruct (anc_facts _ _ _ _ H) as (? & ? & _ & _ & _ & _ & _ & _ & _ & _ & Hsc). lia. Qed.

Lemma anc_trans m q j c' p i c : anc m q j c' -> anc q p i c -> anc m p i c.
Proof.
  intros H1 H2. revert m j c' H1. induction H2 as [q p i Hch|q c j2 c2 p i Ha IH Hch]; intros m j' c' H1.
  - eapply anc_step; eauto.
  - eapply anc_step; [| exact Hch]. eapply IH. exact H1.
Qed.

Lemma child_unique c1 c2 p i : child c1 p i -> child c2 p i -> c1 = c2.
Proof.
  intros H1 H2.
  destruct (child_facts _ _ _ H1) as (b1 & bp & Hc1 & Hp & _ & _ & Hb1 & _).
  destruct (child_facts _ _ _ H2) as (b2 & bp' & Hc2 & Hp' & _ & _ & Hb2 & _).
  pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. subst b1 b2. exact (hosts_fun _ _ _ Hc1 Hc2).
Qed.

Lemma top_chain m bm : hosts st bm m -> m_maplen (R m) = 0 ->
  exists t i c bt, anc m t i c /\ hosts st bt t /\ m_maplen (R t) <> 0 /\ fst bt = fst bm.
Proof.
  intros Hm Hml.
  remember (Z.to_nat (48 - m_sizeclass (R m))) as n eqn:En.
  revert m bm Hm Hml En. induction n as [n IH] using lt_wf_ind; intros m bm Hm Hml En.
  assert (Hch : exists p i, child m p i).
  { destruct (hosts_ok _ _ Hm) as (ai & Hg & GO). destruct (g_nest _ _ _ _ _ _ GO Hml) as (p & i & Hsl & _). exists p, i. exists bm. auto. }
  destruct Hch as (p & i & Hch).
  destruct (child_facts _ _ _ Hch) as (bc & bp & Hc & Hp & Hfst & Hi & Hbc & _ & _ & Hsc).
  pose proof (hosts_inj _ _ _ Hm Hc). subst bc bm. cbn [fst snd] in *.
  destruct (Z.eq_dec (m_maplen (R p)) 0) as [Hml'|Hml'].
  - destruct (IH (Z.to_nat (48 - m_sizeclass (R p))) ltac:(lia) p bp Hp Hml' eq_refl) as (t & j & c & bt & Ha & Ht & Htop & Hfst').
    exists t, j, c, bt. split; [| repeat split; auto; congruence]. eapply anc_trans; [apply anc_child; exact Hch| exact Ha].
  - exists p, i, m, bp. repeat split; auto. apply anc_child. exact Hch.
Qed.

Lemma top_at0 t bt : hosts st bt t -> m_maplen (R t) <> 0 -> snd bt = 0.
Proof. intros Ht Hml. destruct (hosts_ok _ _ Ht) as (ai & _ & GO). destruct (g_top _ _ _ _ _ _ GO Hml) as [H0 _]. exact H0. Qed.

Lemma top_unique t1 t2 b1 b2 : hosts st b1 t1 -> hosts st b2 t2 -> m_maplen (R t1) <> 0 -> m_maplen (R t2) <> 0 ->
  fst b1 = fst b2 -> t1 = t2.
Proof.
  intros H1 H2 M1 M2 Hf. pose proof (top_at0 _ _ H1 M1). pose proof (top_at0 _ _ H2 M2).
  assert (b1 = b2) by (destruct b1, b2; cbn in *; congruence). subst b2. exact (hosts_fun _ _ _ H1 H2).
Qed.

Lemma anc_not_top m p i c bm : anc m p i c -> hosts st bm m -> 0 < snd bm.
Proof.
  intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & Hi & _ & _ & Hs & _).
  pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
  destruct (hosts_ok _ _ Hp) as (ai & _ & GO). pose proof (g_align _ _ _ _ _ _ GO) as [H0 _].
  pose proof (sstart0 _ _ Hp). pose proof (sstart_mono _ _ 0 i Hp ltac:(lia)). unfold UNIT in *. lia.
Qed.

Lemma dichotomy m1 m2 b1 b2 : hosts st b1 m1 -> hosts st b2 m2 -> fst b1 = fst b2 -> m1 <> m2 ->
  (exists i c, anc m1 m2 i c) \/ (exists i c, anc m2 m1 i c)
  \/ (exists p i1 i2 c1 c2, i1 <> i2 /\ anc m1 p i1 c1 /\ anc m2 p i2 c2).
Proof.
  remember (Z.to_nat (48 - m_sizeclass (R m1)) + Z.to_nat (48 - m_sizeclass (R m2)))%nat as n eqn:En.
  revert m1 m2 b1 b2 En. induction n as [n IH] using lt_wf_ind; intros m1 m2 b1 b2 En H1 H2 Hf NE.
  destruct (Z.eq_dec (m_maplen (R m1)) 0) as [M1|M1]; destruct (Z.eq_dec (m_maplen (R m2)) 0) as [M2|M2].
  -
    destruct (hosts_ok _ _ H1) as (a1 & _ & G1). destruct (g_nest _ _ _ _ _ _ G1 M1) as (p1 & i1 & S1 & _).
    destruct (hosts_ok _ _ H2) as (a2 & _ & G2). destruct (g_nest _ _ _ _ _ _ G2 M2) as (p2 & i2 & S2 & _).
    assert (C1 : child m1 p1 i1) by (exists b1; auto). assert (C2 : child m2 p2 i2) by (exists b2; auto).
    destruct (child_facts _ _ _ C1) as (bc1 & bp1 & Hc1 & Hp1 & Hf1 & Hi1 & Hb1 & _ & _ & Hsc1).
    destruct (child_facts _ _ _ C2) as (bc2 & bp2 & Hc2 & Hp2 & Hf2 & Hi2 & Hb2 & _ & _ & Hsc2).
    pose proof (hosts_inj _ _ _ H1 Hc1); subst bc1. pose proof (hosts_inj _ _ _ H2 Hc2); subst bc2.
    destruct (aptr_eq_dec p1 m2) as [->|N1]; [left; exists i1, m1; apply anc_child; exact C1|].
    destruct (aptr_eq_dec p2 m1) as [->|N2]; [right; left; exists i2, m2; apply anc_child; exact C2|].
    destruct (aptr_eq_dec p1 p2) as [->|N3].
    + pose proof (hosts_inj _ _ _ Hp1 Hp2); subst bp2.
      destruct (Z.eq_dec i1 i2) as [->|Ni].
      * exfalso. apply NE. exact (child_unique _ _ _ _ C1 C2).
      * right; right. exists p2, i1, i2, m1, m2. split; [exact Ni|]. split; apply anc_child; assumption.
    + assert (Hf' : fst bp1 = fst bp2) by congruence.
      destruct (IH (Z.to_nat (48 - m_sizeclass (R p1)) + Z.to_nat (48 - m_sizeclass (R p2)))%nat ltac:(lia) p1 p2 bp1 bp2 eq_refl Hp1 Hp2 Hf' N3)
        as [(j & c & Ha)|[(j & c & Ha)|(p & j1 & j2 & c1 & c2 & Nj & Ha1 & Ha2)]].
      *
        destruct (Z.eq_dec j i2) as [->|Nj].
        -- destruct (anc_facts _ _ _ _ Ha) as (_ & _ & _ & _ & _ & _ & Cc & Hor & _).
           pose proof (child_unique _ _ _ _ Cc C2); subst c.
           destruct Hor as [->|(j' & c' & Ha')]; [contradiction|].
           left. exists j', c'. eapply anc_trans; [apply anc_child; exact C1| exact Ha'].
        -- right; right. exists p2, j, i2, c, m2. split; [exact Nj|]. split; [| apply anc_child; exact C2].
           eapply anc_trans; [apply anc_child; exact C1| exact Ha].
      * destruct (Z.eq_dec j i1) as [->|Nj].
        -- destruct (anc_facts _ _ _ _ Ha) as (_ & _ & _ & _ & _ & _ & Cc & Hor & _).
           pose proof (child_unique _ _ _ _ Cc C1); subst c.
           destruct Hor as [->|(j' & c' & Ha')]; [congruence|].
           right; left. exists j', c'. eapply anc_trans; [apply anc_child; exact C2| exact Ha'].
        -- right; right. exists p1, i1, j, m1, c. split; [congruence|]. split; [apply anc_child; exact C1|].
           eapply anc_trans; [apply anc_child; exact C2| exact Ha].
      * right; right. exists p, j1, j2, c1, c2. split; [exact Nj|]. split.
        -- eapply anc_trans; [apply anc_child; exact C1| exact Ha1].
        -- eapply anc_trans; [apply anc_child; exact C2| exact Ha2].
  -
    destruct (top_chain _ _ H1 M1) as (t & i & c & bt & Ha & Ht & Mt & Hft).
    assert (t = m2) by (eapply top_unique; eauto; congruence). subst t. left. exists i, c. exact Ha.
  - destruct (top_chain _ _ H2 M2) as (t & i & c & bt & Ha & Ht & Mt & Hft).
    assert (t = m1) by (eapply top_unique; eauto; congruence). subst t. right; left. exists i, c. exact Ha.
  - exfalso. apply NE. eapply top_unique; eauto.
Qed.


Lemma last_idx_nonneg b m : hosts st b m -> 0 <= m_last_idx (R m).
Proof. intros H. destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). lia. Qed.

Lemma anc_box m p j c bm : anc m p j c -> hosts st bm m ->
  sstart (R p) j <= snd bm /\ gend (R m) <= sstart (R p) (j + 1)
  /\ sstart (R p) j + 16 <= sstart (R m) 0.
Proof.
  intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & _ & _ & _ & Hs & He & _).
  pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (sstart0 _ _ Hm). unfold UNIT in *. lia.
Qed.

Lemma anc_hostslot m p j c : anc m p j c -> exists bp, hosts st bp p /\ s_groups st !! (fst bp, sstart (R p) j) <> None.
Proof.
  intros Ha. destruct (anc_facts _ _ _ _ Ha) as (bm & bp & Hm & Hp & _ & _ & Hch & _).
  destruct (child_facts _ _ _ Hch) as (bc & bp' & Hc & Hp' & _ & _ & Hbc & _).
  pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. exists bp. split; [exact Hp|].
  rewrite <- Hbc. destruct Hc as [ai Hc]. rewrite Hc. discriminate.
Qed.

Lemma sst_lt b m i j : hosts st b m -> i < j -> sstart (R m) i + 16 <= sstart (R m) j.
Proof. intros H Hij. pose proof (sstart_lt _ _ i j H Hij). destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. lia. Qed.

Lemma gend_ge b m : hosts st b m -> snd b + 32 <= gend (R m).
Proof.
  intros H. rewrite gend_eq. pose proof (sstart0 _ _ H). pose proof (sst_lt _ _ 0 (m_last_idx (R m) + 1) H ltac:(pose proof (last_idx_nonneg _ _ H); lia)).
  unfold UNIT in *. lia.
Qed.

Section SEP.
  Variables (m : aptr) (bm : aptr) (i : Z).
  Hypothesis Hm : hosts st bm m.
  Hypothesis Hi : 0 <= i <= m_last_idx (R m).
  Hypothesis NH : s_groups st !! (fst bm, sstart (R m) i) = None.

  Lemma sep_no_anc m2 c : anc m2 m i c -> False.
  Proof. intros Ha. destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne). pose proof (hosts_inj _ _ _ Hm Hp); subst bp. exact (Hne NH). Qed.

  Let S0m := sstart0 _ _ Hm.
  Let Lm := sst_lt _ _ i (i + 1) Hm ltac:(lia).

  Lemma sep_hdr0 m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) + 1 ->
    (m2 <> m \/ i2 <> i) ->
    sstart (R m2) i2 <= sstart (R m) i \/ sstart (R m) (i + 1) <= sstart (R m2) i2.
  Proof.
    intros H2 Hf Hi2 NE. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - destruct NE as [|NEi]; [congruence|].
      destruct (Z.lt_ge_cases i2 i).
      + left. apply (sstart_mono _ _ _ _ Hm). lia.
      + right. apply (sstart_mono _ _ _ _ Hm). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ i2 j H2 ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.

  Lemma sep_h3 m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) ->
    (m2 <> m \/ i2 <> i) ->
    sstart (R m2) i2 + 16 <= sstart (R m) i \/ sstart (R m) (i + 1) <= sstart (R m2) i2.
  Proof.
    intros H2 Hf Hi2 NE. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - destruct NE as [|NEi]; [congruence|].
      destruct (Z.lt_ge_cases i2 i).
      + left. apply (sst_lt _ _ _ _ Hm). lia.
      + right. apply (sstart_mono _ _ _ _ Hm). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sst_lt _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ i2 j H2 ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sst_lt _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.

  Lemma sep_ghdr m2 b2 : hosts st b2 m2 -> fst b2 = fst bm ->
    snd b2 + 16 <= sstart (R m) i \/ sstart (R m) (i + 1) <= snd b2 + 4.
  Proof.
    intros H2 Hf. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - left. pose proof (hosts_inj _ _ _ Hm H2); subst b2. pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2. pose proof (gend_ge _ _ H2) as G2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + left. destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3).
        pose proof (sstart_mono _ _ 0 j H2 ltac:(lia)). pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.

  Lemma sep_ext m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) ->
    (m2 <> m \/ i2 <> i) -> s_groups st !! (fst b2, sstart (R m2) i2) = None ->
    sstart (R m2) (i2 + 1) <= sstart (R m) i \/ sstart (R m) (i + 1) <= sstart (R m2) i2.
  Proof.
    intros H2 Hf Hi2 NE NH2. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - destruct NE as [|NEi]; [congruence|].
      destruct (Z.lt_ge_cases i2 i).
      + left. apply (sstart_mono _ _ _ _ Hm). lia.
      + right. apply (sstart_mono _ _ _ _ Hm). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ (i2 + 1) (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (Z.eq_dec j i2) as [->|Nj].
        { exfalso. destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne). pose proof (hosts_inj _ _ _ H2 Hp); subst bp. exact (Hne NH2). }
        destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (i2 + 1) j H2 ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ (i2 + 1) (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.
End SEP.

End GEOM.
End MI_Geom.

Module MI_Pres1.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Inv. Import SM08.MI_Kit. Import MI_Arith. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_List. Import MI_Geom. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Ext.
Import ListNotations.
Local Open Scope Z_scope.

Lemma slot_key_inj X st BL (IS : inv_S X st BL) b1 m1 b2 m2 i1 i2 :
  hosts st b1 m1 -> hosts st b2 m2 -> 0 <= i1 <= m_last_idx (MR st m1) -> 0 <= i2 <= m_last_idx (MR st m2) ->
  slot_start' (MR st m1) i1 = slot_start' (MR st m2) i2 -> m1 = m2 /\ i1 = i2.
Proof.
  intros H1 H2 R1 R2 E.
  pose proof (is_total _ _ _ IS _ _ _ H1 R1) as T1. pose proof (is_total _ _ _ IS _ _ _ H2 R2) as T2.
  rewrite E in T1. rewrite T1 in T2. inversion T2. auto.
Qed.

Lemma one5_E_irrel (A B C D E E' : Prop) : one5 A B C D E -> ~ E -> ~ E' -> one5 A B C D E'.
Proof.
  unfold one5. intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) NE NE'.
  split; [destruct H0 as [a|[b|[c|[d|e]]]]; [left; exact a| right; left; exact b| right; right; left; exact c| right; right; right; left; exact d| exfalso; exact (NE e)]|].
  repeat split; try assumption; intros [? ?]; apply NE'; assumption.
Qed.

Section MASK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g b : aptr) (ai : Z) (A' F' : Z) (pend' : option aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! b = Some (mkGhdr (Some g) ai).

Let X' := mkX (x_idle X) (x_zomb X) pend' (x_orph X) (x_fresh X).
Let f := fun r : meta => m_set_avail A' (m_set_freed F' r).
Let st' := upd_meta g f st.
Local Notation R := (MR st).
Local Notation R' := (MR st').

Hypothesis C_masks : 0 <= A' /\ 0 <= F'
  /\ (forall i, 0 <= i -> tbit A' i = true -> i <= ai)
  /\ (forall i, 0 <= i -> tbit F' i = true -> i <= m_last_idx (R g))
  /\ (forall i, 0 <= i -> tbit A' i = true -> tbit F' i = true -> False)
  /\ (forall i, ai < i <= m_last_idx (R g) -> tbit F' i = true).
Hypothesis C_part : forall i, 0 <= i <= m_last_idx (R g) ->
  let s := slot_start' (R g) i in
  one5 (tbit A' i = true) (tbit F' i = true) (In s (map bslot BL)) (s_groups st !! s <> None) (pend' = Some s).
Hypothesis C_pend : pend' = x_pend X \/
  ((forall s, x_pend X = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)
   /\ (forall s, pend' = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)).
Hypothesis C_rest : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> A' = 0 /\ F' <> 0.
Hypothesis C_unlisted : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> ~ in_list LS g -> A' = 0 /\ F' = 0.
Hypothesis C_under : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> get_stride (R g) < UNIT * size_class (m_sizeclass (R g)) -> A' = 0 /\ F' = 0.

Lemma R'_eq x : R' x = if aptr_eqb x g then f (R g) else R x.
Proof. unfold st', MR. apply get_meta_rec_upd. Qed.
Lemma R'_other x : x <> g -> R' x = R x.
Proof. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma R'_g : R' g = f (R g).
Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
Lemma fR_mem : m_mem (f (R g)) = m_mem (R g). Proof. reflexivity. Qed.
Lemma fR_prev : m_prev (f (R g)) = m_prev (R g). Proof. reflexivity. Qed.
Lemma fR_next : m_next (f (R g)) = m_next (R g). Proof. reflexivity. Qed.
Lemma fR_last : m_last_idx (f (R g)) = m_last_idx (R g). Proof. reflexivity. Qed.
Lemma fR_freeable : m_freeable (f (R g)) = m_freeable (R g). Proof. reflexivity. Qed.
Lemma fR_sc : m_sizeclass (f (R g)) = m_sizeclass (R g). Proof. reflexivity. Qed.
Lemma fR_maplen : m_maplen (f (R g)) = m_maplen (R g). Proof. reflexivity. Qed.
Lemma fR_avail : m_avail (f (R g)) = A'. Proof. reflexivity. Qed.
Lemma fR_freed : m_freed (f (R g)) = F'. Proof. reflexivity. Qed.
Lemma fR_stride : get_stride (f (R g)) = get_stride (R g). Proof. reflexivity. Qed.
Lemma fR_gbase : gbase (f (R g)) = gbase (R g). Proof. reflexivity. Qed.
Lemma fR_sstart i : sstart (f (R g)) i = sstart (R g) i. Proof. reflexivity. Qed.
Lemma fR_slot_start' i : slot_start' (f (R g)) i = slot_start' (R g) i. Proof. reflexivity. Qed.
Lemma fR_gend : gend (f (R g)) = gend (R g). Proof. reflexivity. Qed.
Lemma fR_cnt : cnt_of (f (R g)) = cnt_of (R g). Proof. reflexivity. Qed.

Lemma R'_mem x : m_mem (R' x) = m_mem (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_prev x : m_prev (R' x) = m_prev (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_next x : m_next (R' x) = m_next (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_last x : m_last_idx (R' x) = m_last_idx (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_freeable x : m_freeable (R' x) = m_freeable (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sc x : m_sizeclass (R' x) = m_sizeclass (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_maplen x : m_maplen (R' x) = m_maplen (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_stride x : get_stride (R' x) = get_stride (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_gbase x : gbase (R' x) = gbase (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sstart x i : sstart (R' x) i = sstart (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_slot_start' x i : slot_start' (R' x) i = slot_start' (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_gend x : gend (R' x) = gend (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_cnt x : cnt_of (R' x) = cnt_of (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_avail_other x : x <> g -> m_avail (R' x) = m_avail (R x). Proof. intros; rewrite R'_other; auto. Qed.
Lemma R'_freed_other x : x <> g -> m_freed (R' x) = m_freed (R x). Proof. intros; rewrite R'_other; auto. Qed.

Lemma st'_groups : s_groups st' = s_groups st. Proof. reflexivity. Qed.
Lemma st'_slots : s_slots st' = s_slots st. Proof. reflexivity. Qed.
Lemma st'_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
Lemma st'_ctx : s_ctx st' = s_ctx st. Proof. reflexivity. Qed.
Lemma st'_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
Lemma st'_shadow : s_shadow st' = s_shadow st. Proof. reflexivity. Qed.
Lemma hosts' bb m : hosts st' bb m <-> hosts st bb m. Proof. apply hosts_ext. reflexivity. Qed.
Lemma live' m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. reflexivity. Qed.
Lemma keys' x : s_metas st' !! x <> None <-> s_metas st !! x <> None \/ x = g.
Proof.
  unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
  split; [auto| intros _; discriminate].
Qed.

Lemma g_hosts : hosts st b g. Proof. exists ai. exact Hg. Qed.

Theorem INVL_mask_change : INVL X' st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof IM as IM0. pose proof IG as IG0. pose proof IS as IS0.
  assert (Gpres : s_metas st !! g <> None).
  { exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)). }
  assert (HD : forall m, live_group st m -> m <> g -> True) by auto.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - destruct IR; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_groups; try assumption.
  - destruct IA; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_areas; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply keys' in K.
      destruct K as [K| ->].
      * destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
      * destruct (s_metas st !! g) as [mr0|] eqn:E; [| congruence]. exact (ia_metas g mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
      * apply K. apply Hk. exact Hk2.
      * apply Gpres. rewrite <- K. apply Hk. exact Hk2.
    + intros sc Hsc. unfold usage, ctx. rewrite st'_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
      unfold gcnt. rewrite st'_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
      rewrite R'_sc, R'_cnt. reflexivity.
  - destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts). congruence.
      * apply M1. exact Hm.
    + intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
    + intros bb h Hb. rewrite st'_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
    + intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| exact E].
      exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
    + intros z Hz. destruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, st'_groups. repeat split; auto. exists bb. auto.
  - destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
    + intros h. unfold st'. rewrite get_head_upd_meta. apply L1.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
    + exact L3.
    + exact L4.
    + intros m. rewrite R'_next, R'_prev. apply L5.
    + intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
      exfalso. pose proof (L6 g Hm) as Z0. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
    + intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
    + exact L9.
  - destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros m bb aim Hm. rewrite st'_groups in Hm. pose proof (G1 m bb aim Hm) as GO.
      destruct (aptr_eqb_spec m g) as [->|NE].
      *
        pose proof (hosts_inj _ _ _ IM0 _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
        rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
        destruct GO; constructor; rewrite ?R'_g, ?fR_last, ?fR_sc, ?fR_maplen, ?fR_freeable, ?fR_avail, ?fR_freed, ?fR_stride, ?fR_gend, ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; exact g_present).
        all: try exact C_masks.
        all: try (intros NF Hp; apply g_partial; [exact NF| exact Hp]).
        all: try (intros NF Hsc NI; apply C_unlisted; assumption).
        all: try (intros NF sc Hm Hh; apply (C_rest NF sc Hm Hh)).
        all: try (intros NF Hsc Hs; apply C_under; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: match goal with |- ?g => idtac "REMAINS-G" g end.
      * destruct GO; constructor; rewrite ?(R'_other m NE), ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: match goal with |- ?g => idtac "REMAINS-O" g end.
    + intros bb aim H. rewrite st'_groups in H. eapply G2. exact H.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st'_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite hosts', R'_maplen. auto.
    + intros bb h H. rewrite st'_groups in H. rewrite st'_regions. eapply G5. exact H.
  - destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
    + intros s m i H. rewrite st'_slots in H. destruct (S1 s m i H) as (? & ? & ?). rewrite live', R'_last, R'_slot_start'. auto.
    + intros bb m i Hb Hi. rewrite st'_slots, R'_slot_start'. apply (S2 bb); [apply hosts'; exact Hb| rewrite <- R'_last; exact Hi].
    + intros bb m aim i Hb Hi. rewrite st'_groups in Hb. rewrite R'_last in Hi. rewrite R'_slot_start', st'_groups.
      rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite fR_avail, fR_freed. apply C_part. exact Hi.
      *
        pose proof (S3 bb m aim i Hb Hi) as P. cbn zeta in P |- *.
        destruct C_pend as [EP|[C_pend_old C_pend_new]]; [unfold X'; cbn [x_pend]; rewrite EP; exact P|].
        assert (NP1 : forall s, x_pend X = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_old _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (NP2 : forall s, pend' = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_new _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (O1 : ~ (x_pend X = Some (slot_start' (R m) i))) by (intros E; exact (NP1 _ E eq_refl)).
        assert (O2 : ~ (pend' = Some (slot_start' (R m) i))) by (intros E; exact (NP2 _ E eq_refl)).
        exact (one5_E_irrel _ _ _ _ _ _ P O1 O2).
    + intros s Hs. rewrite st'_slots. destruct C_pend as [EP|[_ C_pend_new]].
      * apply S4. rewrite <- EP. unfold X' in Hs. exact Hs.
      * destruct (C_pend_new _ Hs) as (j & Hj & ->). rewrite (S2 b g j g_hosts Hj). discriminate.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite st'_slots, R'_stride. auto.
  - apply (inv_SH_view st st'); try reflexivity; try assumption.
    + apply R'_gbase. + apply R'_stride. + apply R'_last. + apply R'_maplen.
Qed.
End MASK.
End MI_Pres1.

Module MI_Shadow.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. Import SM08.MI_Kit.
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition hl_ticks (hl : list (Z * N)) (t : N) : Prop := forall ch, In ch hl -> (snd ch <= t)%N.

Lemma stale_hav_add_some cov t hl b tk :
  hl_ticks hl t ->
  stale (hav_add cov t hl) b (Some tk) = ((b <? cov) && (tk <? t)%N) || stale hl b (Some tk).
Proof.
  intros Ht. unfold hav_add, stale. cbn [existsb fst snd].
  destruct ((b <? cov) && (tk <? t)%N) eqn:E; cbn [orb]; [reflexivity|].
  induction hl as [|[c h] hl IH]; [reflexivity|].
  assert (Hh : (h <= t)%N) by (apply (Ht (c, h)); left; reflexivity).
  assert (IH' : existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) (filter (fun ch : Z * N => cov <? fst ch) hl)
                = existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) hl).
  { apply IH. intros ch Hin. apply Ht. right. exact Hin. }
  rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd].
  - rewrite IH'. reflexivity.
  - rewrite IH'. destruct ((b <? c) && (tk <? h)%N) eqn:E2; cbn; [|reflexivity].
    exfalso. apply Bool.andb_true_iff in E2 as [E2 E3]. apply Z.ltb_lt in E2. apply N.ltb_lt in E3.
    assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
    apply Bool.andb_false_iff in E as [E|E]; [apply Z.ltb_ge in E; lia| apply N.ltb_ge in E; lia].
Qed.

Lemma stale_hav_add_none cov t hl b :
  stale (hav_add cov t hl) b None = (b <? cov) || stale hl b None.
Proof.
  unfold hav_add, stale. cbn [existsb fst snd]. rewrite Bool.andb_true_r.
  destruct (b <? cov) eqn:E; cbn [orb]; [reflexivity|].
  induction hl as [|[c h] hl IH]; [reflexivity|].
  rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd]; rewrite ?Bool.andb_true_r.
  - rewrite IH. reflexivity.
  - rewrite IH. destruct (Z.ltb_spec b c); cbn; [|reflexivity]. exfalso.
    assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
    apply Z.ltb_ge in E. lia.
Qed.


Lemma havoc_units_lookup x y t h u :
  let u0 := x / 16 in let u1 := (y - 1) / 16 in
  let lastcov := (if y mod 16 =? 0 then 16 else y mod 16) in
  (havoc_units x y t h) !! u =
    if (u0 <=? u) && (u <=? u1) then Some (hav_add (if u =? u1 then lastcov else 16) t (default [] (h !! u))) else h !! u.
Proof.
  cbn zeta. unfold havoc_units.
  set (u0 := x / 16). set (u1 := (y - 1) / 16). set (lastcov := if y mod 16 =? 0 then 16 else y mod 16).
  set (F := fun acc : Z * gmap Z (list (Z * N)) => let (u2, h0) := acc in (u2 + 1, <[u2 := hav_add (if u2 =? u1 then lastcov else 16) t (default [] (h0 !! u2))]> h0)).
  destruct (Z.lt_ge_cases (u1 - u0 + 1) 0) as [Hneg|Hnn].
  -
    destruct (u1 - u0 + 1) eqn:E; try lia. cbn.
    destruct (Z.leb_spec u0 u), (Z.leb_spec u u1); cbn; try reflexivity. lia.
  - assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (u0, h) in fst r = u0 + n /\
              forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v).
    { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = u0 + n /\ forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v)); [| | exact Hn].
      - cbn. split; [lia|]. intros v. destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + 0)); cbn; try reflexivity. lia.
      - intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
        destruct (Z.eq_dec v (u0 + k)) as [->|NE].
        + rewrite lookup_insert_eq. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + (k + 1))); cbn; try lia.
          f_equal. f_equal. rewrite IH. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + k)); cbn; try lia. reflexivity.
        + rewrite lookup_insert_ne by congruence. rewrite IH.
          destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + k)), (Z.ltb_spec v (u0 + (k + 1))); cbn; try reflexivity; lia. }
    destruct (GEN (u1 - u0 + 1) Hnn) as [_ G]. rewrite G.
    destruct (Z.leb_spec u0 u), (Z.ltb_spec u (u0 + (u1 - u0 + 1))), (Z.leb_spec u u1); cbn; try reflexivity; lia.
Qed.

Lemma havoc_pages_lookup p0 p1 t h pg :
  (havoc_pages p0 p1 t h) !! pg = if (p0 <=? pg) && (pg <? p1) then Some t else h !! pg.
Proof.
  unfold havoc_pages.
  set (F := fun acc : Z * gmap Z N => let (pg0, h0) := acc in (pg0 + 1, <[pg0 := t]> h0)).
  destruct (Z.lt_ge_cases (p1 - p0) 0) as [Hneg|Hnn].
  - destruct (p1 - p0) eqn:E; try lia. cbn. destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg p1); cbn; try reflexivity. lia.
  - assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (p0, h) in fst r = p0 + n /\
              forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v).
    { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = p0 + n /\ forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v)); [| | exact Hn].
      - cbn. split; [lia|]. intros v. destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + 0)); cbn; try reflexivity. lia.
      - intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
        destruct (Z.eq_dec v (p0 + k)) as [->|NE].
        + rewrite lookup_insert_eq. destruct (Z.leb_spec p0 (p0 + k)), (Z.ltb_spec (p0 + k) (p0 + (k + 1))); cbn; try lia. reflexivity.
        + rewrite lookup_insert_ne by congruence. rewrite IH.
          destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + k)), (Z.ltb_spec v (p0 + (k + 1))); cbn; try reflexivity; lia. }
    destruct (GEN (p1 - p0) Hnn) as [_ G]. rewrite G.
    destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg (p0 + (p1 - p0))), (Z.ltb_spec pg p1); cbn; try reflexivity; lia.
Qed.


Lemma div16_mono a b : a <= b -> a / 16 <= b / 16.
Proof. intros. apply Z.div_le_mono; lia. Qed.

Lemma havoc_units_in x y t h o tko :
  x mod 16 = 0 -> x <= o < y ->
  match tko with Some tk => (tk < t)%N | None => True end ->
  stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = true.
Proof.
  intros Hx Ho Htk. rewrite havoc_units_lookup.
  assert (U0 : x / 16 <= o / 16) by (apply div16_mono; lia).
  assert (U1 : o / 16 <= (y - 1) / 16) by (apply div16_mono; lia).
  destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); try lia. cbn [andb default].
  cbn [default id]. unfold hav_add, stale. cbn [existsb fst snd].
  match goal with |- (?a && ?b) || _ = true => enough (E : a && b = true) by (rewrite E; reflexivity) end.
  apply Bool.andb_true_iff. split.
  - apply Z.ltb_lt. destruct (Z.eqb_spec (o / 16) ((y - 1) / 16)) as [E|NE].
    + destruct (Z.eqb_spec (y mod 16) 0) as [Ey|Ny].
      * pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
      *
        pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)).
        pose proof (Z.div_mod y 16 ltac:(lia)).
        pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
        assert (y / 16 = (y - 1) / 16 \/ y / 16 = (y - 1) / 16 + 1) by (pose proof (div16_mono (y - 1) y ltac:(lia)); pose proof (div16_mono y (y - 1 + 16) ltac:(lia)); rewrite <- Z.div_add in * by lia; nia).
        lia.
    + pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct tko as [tk|]; [apply N.ltb_lt; exact Htk| reflexivity].
Qed.

Lemma havoc_units_out x y t h o tko :
  x mod 16 = 0 -> ~ (x <= o < y) ->
  match tko with Some tk => hl_ticks (default [] (h !! (o / 16))) t | None => True end ->
  stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = stale (default [] (h !! (o / 16))) (o mod 16) tko.
Proof.
  intros Hx Ho Htk. rewrite havoc_units_lookup.
  destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); cbn [andb]; try reflexivity.
  cbn [default id].
  assert (Hoy : y <= o).
  { destruct (Z.lt_ge_cases o x); [|lia]. exfalso.
    pose proof (Z.div_mod x 16 ltac:(lia)). pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.mod_pos_bound o 16 ltac:(lia)). nia. }
  assert (E : o / 16 = (y - 1) / 16) by (pose proof (div16_mono (y - 1) o ltac:(lia)); lia).
  rewrite E, Z.eqb_refl.
  pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)). pose proof (Z.div_mod y 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
  assert (Ny : y mod 16 <> 0 /\ y mod 16 <= o mod 16) by nia.
  destruct (Z.eqb_spec (y mod 16) 0) as [|_]; [lia|].
  destruct tko as [tk|].
  - rewrite stale_hav_add_some by (rewrite <- E; exact Htk). destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
  - rewrite stale_hav_add_none. destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
Qed.

Lemma hav_add_ticks cov t hl : hl_ticks hl t -> hl_ticks (hav_add cov t hl) t.
Proof.
  intros H ch Hin. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
  apply H. apply list_elem_of_In. apply list_elem_of_In in Hin. apply list_elem_of_filter in Hin. tauto.
Qed.

Lemma havoc_units_ticks x y t h :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) ->
  forall u hl, havoc_units x y t h !! u = Some hl -> hl_ticks hl t.
Proof.
  intros Hh u hl. rewrite havoc_units_lookup. destruct (_ && _).
  - intros E. inversion E. subst. apply hav_add_ticks. destruct (h !! u) as [hl0|] eqn:E0; cbn; [eapply Hh; exact E0| intros ? []].
  - apply Hh.
Qed.

Lemma havoc_units_default_ticks x y t h o :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (havoc_units x y t h !! o)) t.
Proof.
  intros Hh. destruct (havoc_units x y t h !! o) as [hl|] eqn:E; cbn; [eapply havoc_units_ticks; eauto| intros ? []].
Qed.

Lemma default_ticks (h : gmap Z (list (Z * N))) t o :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (h !! o)) t.
Proof. intros Hh. destruct (h !! o) as [hl|] eqn:E; cbn; [eapply Hh; eauto| intros ? []]. Qed.

Section HAVOC.
Variables (p : aptr) (n : Z) (st : mstate).
Hypothesis Al : snd p mod 16 = 0.
Hypothesis Hn : 0 < n.
Let sh := get_shadow st (fst p).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).
Let a := snd p.
Let b := snd p + n.
Let t := s_tick st.
Let fp := (a + 4095) / 4096.
Let lp := b / 4096.

Lemma havoc_shadow :
  get_shadow (havoc p n st) (fst p) =
    mkShadow (r_cells sh)
      (if fp <? lp then
         (if lp * 4096 <? b then havoc_units (lp * 4096) b t (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh)
          else (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh))
       else havoc_units a b t (r_hav sh))
      (if fp <? lp then havoc_pages fp lp t (r_havp sh) else r_havp sh).
Proof.
  unfold havoc. destruct (Z.leb_spec n 0); [lia|]. rewrite get_shadow_upd_shadow, N.eqb_refl.
  subst sh a b t fp lp. destruct (_ <? _); [|reflexivity]. destruct (_ <? _); destruct (_ <? _); reflexivity.
Qed.

Lemma havoc_other_region rid : rid <> fst p -> get_shadow (havoc p n st) rid = get_shadow st rid.
Proof.
  intros NE. unfold havoc. destruct (n <=? 0); [reflexivity|]. rewrite get_shadow_upd_shadow.
  destruct (N.eqb_spec rid (fst p)); [congruence| reflexivity].
Qed.

Lemma fp_ge : a <= fp * 4096.
Proof. subst fp. pose proof (Z.div_mod (a + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (a + 4095) 4096 ltac:(lia)). lia. Qed.
Lemma lp_le : lp * 4096 <= b.
Proof. subst lp. pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)). lia. Qed.
Lemma fp_al : (fp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.
Lemma lp_al : (lp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.

Lemma havoc_stale_out o tko :
  ~ (a <= o < b) ->
  match tko with Some tk => True | None => True end ->
  let sh' := get_shadow (havoc p n st) (fst p) in
  stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko
  = stale_pg (r_havp sh !! (o / 4096)) tko || stale (default [] (r_hav sh !! (o / 16))) (o mod 16) tko.
Proof.
  intros Ho _. rewrite havoc_shadow. cbn [r_hav r_havp].
  pose proof fp_ge. pose proof lp_le.
  assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
            match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
  { intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
  destruct (Z.ltb_spec fp lp).
  - f_equal.
    + rewrite havoc_pages_lookup. destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); cbn [andb]; try reflexivity.
      exfalso. apply Ho. pose proof (Z.div_mod o 4096 ltac:(lia)). pose proof (Z.mod_pos_bound o 4096 ltac:(lia)). nia.
    + destruct (Z.ltb_spec (lp * 4096) b); destruct (Z.ltb_spec a (fp * 4096)).
      * rewrite havoc_units_out; [| apply lp_al| lia| apply TKo; apply havoc_units_ticks; exact TK].
        rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
      * rewrite havoc_units_out; [reflexivity| apply lp_al| lia| apply TKo; exact TK].
      * rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
      * reflexivity.
  - f_equal. rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
Qed.

Lemma havoc_stale_in o tko :
  a <= o < b ->
  match tko with Some tk => (tk < t)%N | None => True end ->
  let sh' := get_shadow (havoc p n st) (fst p) in
  stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko = true.
Proof.
  intros Ho Htk. rewrite havoc_shadow. cbn [r_hav r_havp].
  pose proof fp_ge. pose proof lp_le.
  assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
            match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
  { intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
  apply Bool.orb_true_iff.
  destruct (Z.ltb_spec fp lp).
  - destruct (Z.lt_ge_cases o (fp * 4096)) as [Hhead|Hnh].
    + right. destruct (Z.ltb_spec a (fp * 4096)); [|lia].
      destruct (Z.ltb_spec (lp * 4096) b).
      * rewrite havoc_units_out; [| apply lp_al| nia| apply TKo; apply havoc_units_ticks; exact TK].
        apply havoc_units_in; [exact Al| lia| exact Htk].
      * apply havoc_units_in; [exact Al| lia| exact Htk].
    + destruct (Z.lt_ge_cases o (lp * 4096)) as [Hmid|Htail].
      * left. rewrite havoc_pages_lookup.
        assert (fp <= o / 4096 < lp).
        { split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]. }
        destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); try lia. cbn [andb].
        destruct tko as [tk|]; cbn; [apply N.ltb_lt; exact Htk| reflexivity].
      * right. destruct (Z.ltb_spec (lp * 4096) b); [|lia].
        apply havoc_units_in; [apply lp_al| lia| exact Htk].
  - right. apply havoc_units_in; [exact Al| lia| exact Htk].
Qed.

Lemma cell_read_havoc_out q :
  ~ (fst q = fst p /\ a <= snd q < b) ->
  cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. destruct (N.eq_dec (fst q) (fst p)) as [E|NE].
  - rewrite E. assert (Ho : ~ (a <= snd q < b)) by tauto.
    unfold cell_read. pose proof (havoc_stale_out (snd q)) as SO. cbn zeta in SO.
    replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
    subst sh. destruct (r_cells (get_shadow st (fst p)) !! snd q) as [[v tk]|].
    + rewrite (SO (Some tk) Ho I). reflexivity.
    + rewrite (SO None Ho I). reflexivity.
  - rewrite havoc_other_region by exact NE. reflexivity.
Qed.

Lemma cell_read_havoc_in q :
  fst q = fst p -> a <= snd q < b ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < t)%N) ->
  exists h, cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = Unknown h.
Proof.
  intros E Ho Htk. rewrite E. unfold cell_read.
  replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
  pose proof (havoc_stale_in (snd q)) as SI. cbn zeta in SI.
  destruct (r_cells sh !! snd q) as [[v tk]|] eqn:Ec.
  - rewrite (SI (Some tk) Ho (Htk v tk eq_refl)). eauto.
  - rewrite (SI None Ho I). eauto.
Qed.

Lemma havoc_cells rid : r_cells (get_shadow (havoc p n st) rid) = r_cells (get_shadow st rid).
Proof.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [rewrite havoc_shadow; reflexivity| rewrite havoc_other_region by exact NE; reflexivity].
Qed.

Lemma havoc_ticks rid :
  (forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl t) ->
  (forall pg tk, r_havp (get_shadow st rid) !! pg = Some tk -> (tk <= t)%N) ->
  (forall u hl, r_hav (get_shadow (havoc p n st) rid) !! u = Some hl -> hl_ticks hl t)
  /\ (forall pg tk, r_havp (get_shadow (havoc p n st) rid) !! pg = Some tk -> (tk <= t)%N).
Proof.
  intros H1 H2. destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite havoc_other_region by exact NE; auto].
  rewrite havoc_shadow. cbn [r_hav r_havp]. split.
  - destruct (fp <? lp); [| apply havoc_units_ticks; exact TK].
    destruct (lp * 4096 <? b); destruct (a <? fp * 4096); repeat apply havoc_units_ticks; exact TK.
  - destruct (fp <? lp); [| exact H2]. intros pg tk. rewrite havoc_pages_lookup. destruct (_ && _); [| apply H2].
    intros X. inversion X. lia.
Qed.
End HAVOC.


Section HDR.
Variables (bp : aptr) (st : mstate).
Hypothesis Al : snd bp mod 16 = 0.
Let sh := get_shadow st (fst bp).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).

Lemma hdr_havoc_shadow :
  get_shadow (hdr_havoc bp st) (fst bp) =
  mkShadow (r_cells sh) (<[snd bp / 16 := hav_add 12 (s_tick st) (default [] (r_hav sh !! (snd bp / 16)))]> (r_hav sh)) (r_havp sh).
Proof. unfold hdr_havoc. rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity. Qed.

Lemma hdr_havoc_other_region rid : rid <> fst bp -> get_shadow (hdr_havoc bp st) rid = get_shadow st rid.
Proof. intros NE. unfold hdr_havoc. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst bp)); [congruence| reflexivity]. Qed.

Lemma cell_read_hdr_havoc_out q :
  ~ (fst q = fst bp /\ snd bp <= snd q < snd bp + 12) ->
  cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. destruct (N.eq_dec (fst q) (fst bp)) as [E|NE]; [| rewrite hdr_havoc_other_region by exact NE; reflexivity].
  rewrite E. rewrite hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
  destruct (Z.eq_dec (snd q / 16) (snd bp / 16)) as [Eu|Nu].
  - rewrite Eu, lookup_insert_eq. cbn [default id].
    assert (Hb : 12 <= snd q mod 16).
    { pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (snd q) 16 ltac:(lia)).
      assert (~ (snd bp <= snd q < snd bp + 12)) by tauto. nia. }
    destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|].
    + rewrite stale_hav_add_some by (apply default_ticks; exact TK). destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [andb orb]. rewrite <- Eu. reflexivity.
    + rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [orb]. rewrite <- Eu. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma cell_read_hdr_havoc_in q :
  fst q = fst bp -> snd bp <= snd q < snd bp + 12 ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < s_tick st)%N) ->
  exists h, cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = Unknown h.
Proof.
  intros E Ho Htk. rewrite E, hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
  assert (Eu : snd q / 16 = snd bp / 16).
  { pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). symmetry. apply Z.div_unique with (r := snd q - snd bp); lia. }
  rewrite Eu, lookup_insert_eq. cbn [default id].
  assert (Hb : snd q mod 16 < 12).
  { pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). nia. }
  destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|] eqn:Ec.
  - unfold hav_add, stale. cbn [existsb fst snd].
    destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. rewrite (proj2 (N.ltb_lt _ _)) by (eapply Htk; reflexivity).
    cbn [andb orb]. rewrite Bool.orb_true_r. eauto.
  - rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. cbn [orb]. rewrite Bool.orb_true_r. eauto.
Qed.

Lemma hdr_havoc_cells rid : r_cells (get_shadow (hdr_havoc bp st) rid) = r_cells (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [rewrite hdr_havoc_shadow; reflexivity| rewrite hdr_havoc_other_region by exact NE; reflexivity]. Qed.

Lemma hdr_havoc_ticks rid :
  (forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl (s_tick st)) ->
  (forall u hl, r_hav (get_shadow (hdr_havoc bp st) rid) !! u = Some hl -> hl_ticks hl (s_tick st))
  /\ r_havp (get_shadow (hdr_havoc bp st) rid) = r_havp (get_shadow st rid).
Proof.
  intros H1. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [| rewrite hdr_havoc_other_region by exact NE; auto].
  rewrite hdr_havoc_shadow. cbn [r_hav r_havp]. split; [| reflexivity].
  intros u hl. destruct (Z.eq_dec u (snd bp / 16)) as [->|Nu].
  - rewrite lookup_insert_eq. intros X. inversion X. subst. apply hav_add_ticks. apply default_ticks. exact TK.
  - rewrite lookup_insert_ne by congruence. apply H1.
Qed.
End HDR.
End MI_Shadow.

Module MI_Pres2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Inv. Import SM08.MI_Kit. Import MI_Arith. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_List. Import MI_Geom. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Ext. Import MI_Shadow. Import MI_Pres1.
Import ListNotations.
Local Open Scope Z_scope.

Definition inT (rid : N) (lo hi : Z) (q : aptr) : Prop := fst q = rid /\ lo <= snd q < hi.

Section WRITE_T.
Variables (X : extras) (st st' : mstate) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis IM : inv_M X st LS.
Hypothesis IG : inv_G X st LS.
Hypothesis IS : inv_S X st BL.
Hypothesis ISH : inv_SH st BL.
Variables (m bm : aptr) (i : Z).
Hypothesis Hm : hosts st bm m.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st m).
Hypothesis NH : s_groups st !! (fst bm, sstart (MR st m) i) = None.
Hypothesis NB : forall k, In k BL -> bslot k <> (fst bm, sstart (MR st m) i).
Let lo := sstart (MR st m) i - 3.
Let hi := sstart (MR st m) (i + 1) - 4.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall q, ~ inT (fst bm) lo hi q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

Local Notation R := (MR st).

Lemma known_out q v : ~ inT (fst bm) lo hi q -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite RD by exact Hq. exact K. Qed.
Lemma unknown_out q : ~ inT (fst bm) lo hi q -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite RD by exact Hq. exact K. Qed.

Lemma not_inT_lo q : snd q < lo -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [H1 _]]. lia. Qed.
Lemma not_inT_hi q : hi <= snd q -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [_ H2]]. lia. Qed.
Lemma not_inT_rid q : fst q <> fst bm -> ~ inT (fst bm) lo hi q.
Proof. intros H [H1 _]. exact (H H1). Qed.

Theorem inv_SH_write_T : inv_SH st' BL.
Proof.
  pose proof (ce_metas _ _ CE) as HMe. pose proof (ce_groups _ _ CE) as HG. pose proof (ce_slots _ _ CE) as HS. pose proof (ce_regions _ _ CE) as HR.
  pose proof (MR_ext st st' HMe) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct ISH as [D1 D2 D3 D4 D5 D6]. constructor.
  - intros rid sh H. rewrite HR. eapply DOM. exact H.
  - intros rid sh H. rewrite TK. eapply TKS. exact H.
  -
    intros b2 m2 i2 Hb2 Hi2. apply HE in Hb2. rewrite ME in Hi2 |- *.
    apply known_out; [| exact (D3 b2 m2 i2 Hb2 Hi2)].
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
    unfold cnt_of in Hi2.
    destruct (aptr_eq_dec m2 m) as [Em|NEm]; [destruct (Z.eq_dec i2 i) as [Ei|NEi]|].
    + subst m2 i2. apply not_inT_lo. subst lo hi. cbn. unfold IB. lia.
    + destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_intror NEi)) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
    + destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_introl NEm)) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
  -
    intros b2 m2 o Hb2 Ho. apply HE in Hb2. apply unknown_out; [| exact (D4 b2 m2 o Hb2 Ho)].
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
    destruct (sep_ghdr _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 Hb2 Ef) as [A|A];
      [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
  -
    intros b2 m2 p2 i2 Hb2 Hml Hs. apply HE in Hb2. rewrite ME in Hml. rewrite HS in Hs. rewrite !ME.
    destruct (D5 b2 m2 p2 i2 Hb2 Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp2 Hp2] & Hi2 & Eb2).
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp2) in Eb2.
    assert (OUT : forall d, 1 <= d <= 3 -> ~ inT (fst bm) lo hi (fst b2, snd b2 - d)).
    { intros d Hd. subst b2. cbn [fst snd].
      destruct (N.eq_dec (fst bp2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
      assert (NE : p2 <> m \/ i2 <> i).
      { destruct (aptr_eq_dec p2 m) as [->|]; [right| left; assumption]. intros ->.
        pose proof (hosts_inj _ _ _ IM _ _ _ Hp2 Hm). subst bp2. destruct Hb2 as [ai2 Hb2]. rewrite Hb2 in NH. discriminate. }
      destruct (sep_h3 _ _ _ _ IM IG IS m bm i Hm Hi NH p2 bp2 i2 Hp2 Ef Hi2 NE) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
    split; [exists v3; split; [apply known_out; [apply (OUT 3); lia| exact K3]| auto]|].
    split; [apply known_out; [apply (OUT 2); lia| exact K2]|].
    split; [apply known_out; [apply (OUT 1); lia| exact K1]| exact Q].
  -
    intros k m2 i2 Hk Hs. rewrite HS in Hs. rewrite !ME.
    destruct (D6 k m2 i2 Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b2 Hb2] & Hi2 & Ek).
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb2) in Ek.
    destruct (is_blocks _ _ _ IS k Hk) as (m2' & i2' & Hs' & Hoff & Hsz & Hfit). rewrite Hs in Hs'. inversion Hs'. subst m2' i2'. clear Hs'.
    pose proof (stride_ge _ _ _ IG _ _ Hb2) as [SG _].
    assert (NH2 : s_groups st !! (fst b2, sstart (R m2) i2) = None).
    { destruct Hb2 as [ai2 Hb2']. pose proof (is_part _ _ _ IS _ _ _ _ Hb2' Hi2) as P. cbn zeta in P.
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai2 Hb2')) in P.
      unfold one5 in P. destruct (s_groups st !! (fst b2, sstart (R m2) i2)) eqn:E; [| reflexivity]. exfalso.
      assert (U : In (fst b2, sstart (R m2) i2) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
      assert (H : s_groups st !! (fst b2, sstart (R m2) i2) <> None) by congruence. tauto. }
    assert (NE : m2 <> m \/ i2 <> i).
    { destruct (aptr_eq_dec m2 m) as [->|]; [right| left; assumption]. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hb2 Hm). subst b2. exact (NB k Hk Ek). }
    assert (OUT : forall o, sstart (R m2) i2 - 4 <= o < sstart (R m2) (i2 + 1) - 4 -> ~ inT (fst bm) lo hi (fst (bslot k), o)).
    { intros o Ho. rewrite Ek. cbn [fst].
      destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
      destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 NE NH2) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
    assert (Esnd : snd (bslot k) = sstart (R m2) i2) by (rewrite Ek; reflexivity).
    rewrite sstart_succ in OUT. unfold UNIT, IB in *.
    split; [apply known_out; [apply OUT; lia| exact A1]|].
    split; [apply known_out; [apply OUT; lia| exact A2]|].
    split; [apply known_out; [apply OUT; lia| exact A3]|].
    split; [apply known_out; [apply OUT; lia| exact A4]|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6).
      repeat split; try (apply known_out; [apply OUT; lia| assumption]). exact B6.
    + split; [intros Hr; apply known_out; [apply OUT; lia| apply A7; exact Hr]|].
      intros a Ha. apply unknown_out; [apply OUT; lia| apply A8; exact Ha].
Qed.
End WRITE_T.


Lemma inv_R_X X X' st L : x_orph X' = x_orph X -> inv_R X st L -> inv_R X' st L.
Proof. intros E I. destruct I; constructor; try assumption. rewrite E. assumption. Qed.
Lemma inv_M_X X X' st LS : x_idle X' = x_idle X -> x_zomb X' = x_zomb X -> inv_M X st LS -> inv_M X' st LS.
Proof. intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; assumption. Qed.
Lemma group_ok_X X X' st LS m b ai : x_fresh X' = x_fresh X -> group_ok X st LS m b ai -> group_ok X' st LS m b ai.
Proof. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.
Lemma inv_G_X X X' st LS : x_fresh X' = x_fresh X -> x_orph X' = x_orph X -> inv_G X st LS -> inv_G X' st LS.
Proof.
  intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; try assumption.
  intros. eapply group_ok_X; [exact E1|]. eauto.
Qed.

Lemma inv_SH_incl st BL BL' : (forall k, In k BL' -> In k BL) -> inv_SH st BL -> inv_SH st BL'.
Proof. intros Hsub I. destruct I; constructor; try assumption. intros k m i Hk Hs. apply ish_blk; [apply Hsub; exact Hk| exact Hs]. Qed.


Lemma bl_remove_split BL k : NoDup (map bslot BL) -> In k BL ->
  exists l1 l2, BL = l1 ++ k :: l2 /\ bl_remove (bslot k) BL = l1 ++ l2 /\ ~ In (bslot k) (map bslot l1) /\ ~ In (bslot k) (map bslot l2).
Proof.
  induction BL as [|b BL IH]; intros ND Hin; [destruct Hin|].
  cbn in ND. apply NoDup_cons in ND as [N1 N2].
  destruct Hin as [<-|Hin].
  - exists [], BL. cbn. rewrite aptr_eqb_refl. repeat split; auto. intros H. apply N1. apply list_elem_of_In. exact H.
  - destruct (IH N2 Hin) as (l1 & l2 & E1 & E2 & M1 & M2).
    assert (NE : bslot b <> bslot k).
    { intros E. apply N1. rewrite E. apply list_elem_of_In. apply in_map. exact Hin. }
    exists (b :: l1), l2. cbn. rewrite (aptr_eqb_neq (bslot b) (bslot k)) by exact NE. rewrite E1, E2 at 1. rewrite <- E1.
    repeat split; auto. cbn. intros [H|H]; [exact (NE H)| exact (M1 H)].
Qed.


Section REMOVE_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (k : blk).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis NP : x_pend X = None.
Let X' := mkX (x_idle X) (x_zomb X) (Some (bslot k)) (x_orph X) (x_fresh X).
Let BL' := bl_remove (bslot k) BL.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! (bslot k) = Some (m, i) ->
  forall q, ~ inT (fst (bslot k)) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

Theorem INVL_remove_block : INVL X' st' L BL' LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & Hoff & Hsz & Hfit).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
  destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
  assert (SUB : forall k', In k' BL' -> In k' BL /\ bslot k' <> bslot k).
  { intros k' H. subst BL'. rewrite EBL' in H. rewrite EBL. apply in_app_iff in H. split.
    - apply in_app_iff. cbn. tauto.
    - intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H. }
  assert (IS' : inv_S X' st BL').
  { destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    - exact S1.
    - exact S2.
    - intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
      rewrite NP in P.
      assert (MEMk : In (slot_start' (MR st m2) i2) (map bslot BL) <->
                     In (slot_start' (MR st m2) i2) (map bslot BL') \/ slot_start' (MR st m2) i2 = bslot k).
      { subst BL'. rewrite EBL' , EBL. rewrite !map_app. cbn. rewrite !in_app_iff. cbn. intuition congruence. }
      assert (NOTk : In (slot_start' (MR st m2) i2) (map bslot BL') -> slot_start' (MR st m2) i2 <> bslot k).
      { intros H E. subst BL'. rewrite EBL' in H. rewrite map_app, in_app_iff in H. rewrite E in H. tauto. }
      unfold one5 in P |- *.
      assert (D : @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2)) <-> slot_start' (MR st m2) i2 = bslot k) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
      assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
      set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
      set (U' := In (slot_start' (MR st m2) i2) (map bslot BL')) in *.
      set (E := slot_start' (MR st m2) i2 = bslot k) in *.
      set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
      set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
      set (P5 := @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2))) in *.
      set (Q5 := None = Some (slot_start' (MR st m2) i2)) in *.
      fold P5. fold Q5 in P. clearbody U U' E A F Hh P5 Q5. clear - P MEMk NOTk D N5; tauto.
    - intros s Hs'. cbn in Hs'. inversion Hs'. subst s. rewrite Hs. discriminate.
    - subst BL'. rewrite EBL'. pose proof S5 as ND. rewrite EBL in ND. rewrite !map_app in ND |- *. cbn in ND.
      apply NoDup_app in ND as (A1 & A2 & A3). apply NoDup_cons in A3 as [_ A3].
      apply NoDup_app. split; [exact A1|]. split; [| exact A3]. intros x Hx Hx2. apply (A2 x Hx). right. exact Hx2.
    - intros k' Hk'. apply S6. apply SUB. exact Hk'. }
  assert (ISH' : inv_SH st' BL').
  { eapply (inv_SH_write_T X' st st' BL' LS (inv_M_X X X' st LS eq_refl eq_refl IM) (inv_G_X X X' st LS eq_refl eq_refl IG) IS'); try eassumption.
    - apply (inv_SH_incl st BL). { intros k' H. apply SUB. exact H. } exact ISH.
    -
      destruct Hm as [ai Hm']. pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P.
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')) in P. unfold one5 in P.
      destruct (s_groups st !! (fst bm, sstart (MR st m) i)) eqn:E; [| reflexivity]. exfalso.
      assert (U : In (fst bm, sstart (MR st m) i) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
      assert (H : s_groups st !! (fst bm, sstart (MR st m) i) <> None) by congruence. tauto.
    - intros k' Hk' E. destruct (SUB k' Hk') as [_ NE]. apply NE. rewrite E, Ek. reflexivity.
    - intros q Hq. apply (RD m i Hs). rewrite Ek. exact Hq. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
  - apply (inv_A_ctrl st st' CE). exact IA.
  - apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ctrl st st' LS CE). exact IL.
  - apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
  - apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
  - exact ISH'.
Qed.

Lemma remove_block_members k' : In k' BL' <-> In k' BL /\ bslot k' <> bslot k.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
  subst BL'. rewrite EBL', EBL. rewrite !in_app_iff. cbn. split.
  - intros H. split; [tauto|]. intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H.
  - intros [[H|[<-|H]] NE]; [tauto| congruence| tauto].
Qed.
End REMOVE_BLOCK.


Definition blk_shadow_ok (st : mstate) (k : blk) (m : aptr) (i : Z) : Prop :=
  let rid := fst (bslot k) in
  let p := snd (bslot k) + UNIT * boff k in
  let e := snd (bslot k) + get_stride (MR st m) - IB in
  let res := e - p - bsize k in
  let q := (p - snd (gbase (MR st m)) - UNIT) / UNIT in
  known st (rid, p - 4) 0
  /\ known st (rid, p - 3) (i + 32 * Z.min res 5)
  /\ known st (rid, p - 2) (byte_of q 0) /\ known st (rid, p - 1) (byte_of q 1) /\ 0 <= q < 2^16
  /\ (5 <= res -> known st (rid, e - 4) (byte_of res 0) /\ known st (rid, e - 3) (byte_of res 1)
                /\ known st (rid, e - 2) (byte_of res 2) /\ known st (rid, e - 1) (byte_of res 3)
                /\ known st (rid, e - 5) 0 /\ res < 2^32)
  /\ (0 < res -> known st (rid, e - res) 0)
  /\ (forall a, p <= a < p + bsize k -> unknown st (rid, a)).

Lemma inv_SH_cons st BL k m i :
  inv_SH st BL -> s_slots st !! (bslot k) = Some (m, i) -> blk_shadow_ok st k m i -> inv_SH st (k :: BL).
Proof.
  intros I Hs Hk. destruct I; constructor; try assumption.
  intros k' m' i' [<-|Hk'] Hs'.
  - rewrite Hs in Hs'. inversion Hs'. subst. exact Hk.
  - apply ish_blk; assumption.
Qed.

Section ADD_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Let k : blk := ((c, off), n).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = Some c.
Let X' := mkX (x_idle X) (x_zomb X) None (x_orph X) (x_fresh X).
Let BL' := k :: BL.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! c = Some (m, i) ->
  forall q, ~ inT (fst c) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).
Hypothesis BLK : forall m i, s_slots st !! c = Some (m, i) ->
  0 <= off <= 255 /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB /\ blk_shadow_ok st' k m i.

Theorem INVL_add_block : INVL X' st' L BL' LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (s_slots st !! c) as [[m i]|] eqn:Hs. 2:{ exfalso. exact (is_pend _ _ _ IS c HP Hs). }
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
  destruct (BLK m i eq_refl) as (Hoff & Hn & Hfit & SHK).
  destruct Hm as [ai Hm'].
  pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P0. cbn zeta in P0.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')), <- Ek, HP in P0.
  assert (NU : ~ In c (map bslot BL)) by (unfold one5 in P0; tauto).
  assert (NH : s_groups st !! c = None).
  { destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. unfold one5 in P0. tauto. }
  assert (IS' : inv_S X' st BL').
  { destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    - exact S1.
    - exact S2.
    - intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
      rewrite HP in P. subst BL'.
      assert (EQm : In (slot_start' (MR st m2) i2) (map bslot (k :: BL)) <-> c = slot_start' (MR st m2) i2 \/ In (slot_start' (MR st m2) i2) (map bslot BL)) by (cbn; tauto).
      unfold one5 in P |- *. rewrite EQm.
      assert (D : @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2)) <-> c = slot_start' (MR st m2) i2) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
      assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
      assert (NU' : c = slot_start' (MR st m2) i2 -> ~ In (slot_start' (MR st m2) i2) (map bslot BL)) by (intros <-; exact NU).
      set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
      set (E := c = slot_start' (MR st m2) i2) in *.
      set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
      set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
      set (P5 := @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2))) in *.
      set (Q5 := @eq (option aptr) None (Some (slot_start' (MR st m2) i2))) in *.
      clearbody U E A F Hh P5 Q5. clear - P D N5; tauto.
    - intros s Hs'. cbn in Hs'. discriminate.
    - subst BL'. cbn. apply NoDup_cons. split; [| exact S5]. intros H. apply NU. apply list_elem_of_In. exact H.
    - intros k' [<-|Hk']; [| apply S6; exact Hk'].
      exists m, i. cbn. auto. }
  assert (ISH' : inv_SH st' BL').
  { apply (inv_SH_cons st' BL k m i).
    - eapply (inv_SH_write_T X st st' BL LS IM IG IS); try eassumption.
      + exists ai. exact Hm'.
      + rewrite <- Ek. exact NH.
      + intros k' Hk' E. apply NU. rewrite Ek, <- E. apply in_map. exact Hk'.
      + intros q Hq. apply (RD m i eq_refl). rewrite Ek. exact Hq.
    - rewrite (ce_slots _ _ CE). exact Hs.
    - exact SHK. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
  - apply (inv_A_ctrl st st' CE). exact IA.
  - apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ctrl st st' LS CE). exact IL.
  - apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
  - apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
  - exact ISH'.
Qed.
End ADD_BLOCK.
End MI_Pres2.

Module MI_Tree.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Definition rejects {R} (t : M R) : Prop :=
  match t with SVis (EUndef _) _ => True | _ => False end.

Definition is_peek (e : ev) : bool := match e with EPeek _ _ _ => true | _ => false end.
Definition is_undef (e : ev) : bool := match e with EUndef _ => true | _ => false end.

Lemma rejects_inv {R} (t : M R) : rejects t -> exists w k, t = SVis (EUndef w) k.
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; try tauto. intros _. eauto. Qed.

Lemma rejects_bind {R S} (t : M R) (f : R -> M S) : rejects t -> rejects (sbind t f).
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; tauto. Qed.

Fixpoint ftree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> ftree L (k v) Post
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a)
  end.

Fixpoint ptree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => False
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ptree (event_post L e a) (k a) Post else rejects (k a)
  end.

Ltac case_ans :=
  match goal with
  | |- context [if answer_ok ?L ?e ?a then _ else _] => destruct (answer_ok L e a) eqn:?
  | H : context [if answer_ok ?L ?e ?a then _ else _] |- _ => destruct (answer_ok L e a) eqn:?
  end.

Lemma ftree_ret {R} L (r : R) Post : Post L r -> ftree L (SRet r) Post.
Proof. intros H. exact H. Qed.

Lemma ftree_vis {R} L e (k : Z -> M R) Post :
  is_peek e = false -> is_undef e = false ->
  event_pre L e ->
  (forall a, answer_ok L e a = true -> ftree (event_post L e a) (k a) Post) ->
  (forall a, answer_ok L e a = false -> rejects (k a)) ->
  ftree L (SVis e k) Post.
Proof.
  intros Hp Hu He Hk Hr. destruct e; cbn in Hp, Hu; try discriminate; cbn [ftree]; split; auto;
  intros a; case_ans; auto.
Qed.

Lemma ftree_peek {R} L p c h (k : Z -> M R) Post :
  (forall v, 0 <= v < 256 -> ftree L (k v) Post) -> ftree L (SVis (EPeek p c h) k) Post.
Proof. intros H. exact H. Qed.

Lemma ftree_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ftree L t Post -> ftree L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

Lemma ftree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
  ftree L t Post -> (forall L' r, Post L' r -> ftree L' (f r) Q) -> ftree L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk).
    + intros v Hv. apply IH; [apply H; exact Hv| exact Hf].
    + destruct H.
Qed.

Lemma rejects_bad_answer {R} (b : M R) : rejects (bad_answer b).
Proof. exact I. Qed.

Lemma ftree_guard {R} L tag (c : bool) (k bail : M R) Post :
  c = true -> ftree L k Post -> ftree L (guard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

Lemma ftree_guard_inv {R} L tag (c : bool) (k bail : M R) Post :
  ftree L (guard tag c k bail) Post -> c = true /\ ftree L k Post.
Proof. unfold guard. destruct c; cbn; [auto| intros H; destruct H]. Qed.

Lemma ptree_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ptree L t Post -> ptree L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]); exact H.
Qed.

Lemma ptree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
  ptree L t Post -> (forall L' r, Post L' r -> ptree L' (f r) Q) -> ptree L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk); exact H.
Qed.

Lemma ptree_ctree_ok {R} : forall (t : M R) L Post, ptree L t Post -> ctree_ok L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [ftree ptree follow sbind] in *; [exact H|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros z Hz; specialize (Hk z); rewrite Hz in Hk; apply IH; exact Hk);
    destruct H.
Qed.

Lemma ptree_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L (P1 : mled -> R1 -> Prop) (P2 : mled -> R2 -> Prop),
  (forall L' r1 r2, RR r1 r2 -> P1 L' r1 -> P2 L' r2) ->
  ptree L t1 P1 -> ptree L t2 P2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L P1 P2 HP H; cbn [ftree ptree follow sbind] in *.
  - eapply HP; eauto.
  - destruct e; try exact H. all: destruct H as [He H]; split; [exact He|]; intros a; specialize (H a);
      case_ans; [eapply IH; eauto|].
    all: specialize (Hk a); destruct (rejects_inv _ H) as (w & k' & E); rewrite E in Hk; inversion Hk; subst; exact I.
Qed.

Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma ftree_prun {R} : forall (t : M R) L Post o,
  ftree L t Post -> ptree L (prun pans pupd o t) (fun L' x => Post L' (snd x)).
Proof.
  induction t as [r|e k IH]; intros L Post o H; cbn [ftree ptree follow sbind] in *.
  - exact H.
  - unfold prun. destruct e; cbn [eruns psel];
      try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
           case_ans; [apply IH; exact Hk|];
           destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E; exact I).
    + apply IH. apply H. apply Hpans.
    + destruct H.
Qed.
End PRUN.

Lemma ptree_follow {R} : forall (t : M R) L Post ans r,
  ptree L t Post -> follow t ans = Some r -> exists L', cpath L t L' r /\ Post L' r.
Proof.
  induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ftree ptree follow sbind] in *.
  - inversion Hf; subst. exists L. split; [constructor| exact H].
  - destruct e; try (destruct H; fail); try contradiction.
    all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
      specialize (Hk a); case_ans;
      [ destruct (IH a _ _ _ _ Hk Hf) as (L' & Hp & HP); exists L'; split; [econstructor; eauto| exact HP]
      | destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

Lemma ptree_cpath {R} : forall (t : M R) L Post L' r,
  ptree L t Post -> cpath L t L' r -> Post L' r.
Proof.
  induction t as [r0|e k IH]; intros L Post L' r H Hp; cbn [ftree ptree follow sbind] in *.
  - inversion Hp; subst. exact H.
  - inversion Hp; subst. destruct e; try contradiction.
    all: destruct H as [He Hk];
      match goal with Ha : answer_ok _ _ ?z = true |- _ => specialize (Hk z); rewrite Ha in Hk; eapply IH; eauto end.
Qed.

Lemma strel_cpath {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L L' r2, cpath L t2 L' r2 -> exists r1, cpath L t1 L' r1 /\ RR r1 r2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L L' r Hp.
  - inversion Hp; subst. exists r1. split; [constructor| exact Hr].
  - inversion Hp; subst.
    match goal with Hc : cpath _ (k2 ?z) _ _ |- _ =>
      destruct (IH z _ _ _ Hc) as (r1 & Hp1 & Hr1); exists r1; split; [econstructor; eauto| exact Hr1] end.
Qed.

Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall ans,
  match follow t1 ans, follow t2 ans with
  | Some r1, Some r2 => RR r1 r2
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans; cbn.
  - exact Hr.
  - destruct e; destruct ans; cbn; auto; apply IH.
Qed.
End MI_Tree.

Module MI_Read.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. Import MI_Tree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Inv. Import SM08.MI_Kit. Import MI_Arith.
Import ListNotations.
Local Open Scope Z_scope.


Lemma rd8_known {R} st q v (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

Lemma known_at st rid o v rid' o' :
  known st (rid, o) v -> o' = o -> rid' = rid -> cell_read (get_shadow st rid') o' = Known v.
Proof. intros H -> ->. exact H. Qed.

Lemma rd8_ftree {R} L st q (k : Z -> M R) Post :
  (forall v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 256 -> ftree L (k v) Post) ->
  ftree L (rd8 st q k) Post.
Proof.
  intros Hk H. unfold rd8. destruct (cell_read _ _) as [v|h] eqn:E.
  - apply H. apply Hk. reflexivity.
  - cbn [ftree]. intros v Hv. unfold peek_answer_ok.
    destruct (Z.leb_spec 0 v), (Z.ltb_spec v 256); cbn [andb]; try lia. apply H. lia.
Qed.

Lemma rd16_ftree {R} L st q (k : Z -> M R) Post :
  (forall q' v, cell_read (get_shadow st (fst q')) (snd q') = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 65536 -> ftree L (k v) Post) ->
  ftree L (rd16 st q k) Post.
Proof.
  intros Hk H. unfold rd16. apply rd8_ftree; [apply Hk|]. intros b0 H0. apply rd8_ftree; [apply Hk|]. intros b1 H1. apply H. lia.
Qed.

Lemma known_byte st rid o v :
  (forall sh o' v' t, s_shadow st !! rid = Some sh -> r_cells sh !! o' = Some (v', t) -> 0 <= v' < 256) ->
  cell_read (get_shadow st rid) o = Known v -> 0 <= v < 256.
Proof.
  intros Hc H. unfold cell_read, get_shadow in H. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn [default id] in H.
  - destruct (r_cells sh !! o) as [[v' t]|] eqn:E2.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. subst. eapply Hc; eauto.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. lia.
  - rewrite !lookup_empty in H. cbn in H. inversion H. lia.
Qed.


Lemma land_255 x : 0 <= x -> Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma byte_of_0 x : 0 <= x -> byte_of x 0 = x mod 256.
Proof. intros. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r. apply land_255. lia. Qed.
Lemma byte_of_1 x : 0 <= x -> byte_of x 1 = (x / 256) mod 256.
Proof. intros. unfold byte_of. replace (8 * 1) with 8 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_2 x : 0 <= x -> byte_of x 2 = (x / 65536) mod 256.
Proof. intros. unfold byte_of. replace (8 * 2) with 16 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_3 x : 0 <= x -> byte_of x 3 = (x / 16777216) mod 256.
Proof. intros. unfold byte_of. replace (8 * 3) with 24 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. apply land_255. apply Z.div_pos; lia. Qed.

Lemma byte_of_range x k : 0 <= x -> 0 <= k -> 0 <= byte_of x k < 256.
Proof.
  intros. unfold byte_of. rewrite land_255 by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]).
  apply Z.mod_pos_bound. lia.
Qed.

Lemma u16_bytes q : 0 <= q < 2^16 -> byte_of q 0 + 256 * byte_of q 1 = q.
Proof. intros. rewrite byte_of_0, byte_of_1 by lia. rewrite (Z.mod_small (q / 256)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). pose proof (Z.div_mod q 256 ltac:(lia)). lia. Qed.

Lemma u32_bytes r : 0 <= r < 2^32 ->
  byte_of r 0 + 256 * byte_of r 1 + 65536 * byte_of r 2 + 16777216 * byte_of r 3 = r.
Proof.
  intros. rewrite byte_of_0, byte_of_1, byte_of_2, byte_of_3 by lia.
  pose proof (Z.div_mod r 256 ltac:(lia)) as E1.
  pose proof (Z.div_mod (r / 256) 256 ltac:(lia)) as E2. rewrite (Z.div_div r 256 256) in E2 by lia. change (256 * 256) with 65536 in E2.
  pose proof (Z.div_mod (r / 65536) 256 ltac:(lia)) as E3. rewrite (Z.div_div r 65536 256) in E3 by lia. change (65536 * 256) with 16777216 in E3.
  rewrite (Z.mod_small (r / 16777216)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  lia.
Qed.

Lemma land31_idx i r : 0 <= i <= 31 -> 0 <= r -> Z.land (i + 32 * r) 31 = i.
Proof.
  intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (i + r * 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma shiftr5_res i r : 0 <= i <= 31 -> 0 <= r -> Z.shiftr (i + 32 * r) 5 = r.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (r * 32 + i) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.


Lemma area_of_mslot a k : snd a mod PGSZ = 0 -> 0 <= k < NSLOTS -> area_of (mslot a k) = a.
Proof.
  intros Ha Hk. unfold area_of, mslot, aadd, AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. destruct a as [r o]; cbn in *. f_equal.
  rewrite <- Zplus_mod_idemp_l, Ha. cbn [Z.add]. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mod_pg_mod16 x : x mod PGSZ = 0 -> x mod 16 = 0.
Proof. intros H. unfold PGSZ in H. pose proof (Z.div_mod x 4096 ltac:(lia)). rewrite H in H0.
  rewrite H0. replace (4096 * (x / 4096) + 0) with ((256 * (x / 4096)) * 16) by lia. apply Z_mod_mult. Qed.

Lemma mslot_mod8 a k : snd a mod PGSZ = 0 -> snd (mslot a k) mod 8 = 0.
Proof.
  intros Ha. unfold mslot, aadd, AREA_HDR, META_SIZE. cbn [snd].
  pose proof (Z.div_mod (snd a) 4096 ltac:(lia)). unfold PGSZ in Ha. rewrite Ha in H.
  rewrite H. replace (4096 * (snd a / 4096) + 0 + (24 + 40 * k)) with ((512 * (snd a / 4096) + 3 + 5 * k) * 8) by lia. apply Z_mod_mult.
Qed.
End MI_Read.

Module Monad.

From Stdlib Require Import ZArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import MState. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Mem. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Exec. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes.
Import ListNotations.
Import ITree.Exc.

Section Monad.
Context {St : Type}.

Definition M (A : Type) : Type := St -> itree node (exc (A * St)).

Definition mret {A} (a : A) : M A := fun s => Ret (Ok (a, s)).
Definition mbind {A B} (m : M A) (f : A -> M B) : M B :=
  fun s => ebind (m s) (fun p => f (fst p) (snd p)).
Definition munr {A} : M A := fun _ => Ret Unr.
Definition mget : M St := fun s => Ret (Ok (s, s)).
Definition mput (s : St) : M unit := fun _ => Ret (Ok (tt, s)).
Definition mupd (f : St -> St) : M unit := fun s => Ret (Ok (tt, f s)).
Definition msys {A} (n : node) (dec : resp -> option A) : M A :=
  fun s => enode n (fun r => match dec r with Some a => Some (a, s) | None => None end).
Definition mwhen (b : bool) (m : M unit) : M unit := if b then m else mret tt.
Definition massert (b : bool) : M unit := if b then mret tt else munr.

Fixpoint mloop {X R} (fuel : nat) (body : X -> M (X + R)) (x : X) : M R :=
  match fuel with
  | O => munr
  | S fuel' => mbind (body x) (fun s => match s with
                                        | inl x' => mloop fuel' body x'
                                        | inr r => mret r
                                        end)
  end.

Lemma mbind_mret : forall {A B} (a : A) (f : A -> M B) s, mbind (mret a) f s = f a s.
Proof. reflexivity. Qed.
Lemma mbind_munr : forall {A B} (f : A -> M B) s, mbind (munr (A:=A)) f s = Ret Unr.
Proof. reflexivity. Qed.

Section Machine.
Variable segs : list Segment.

Definition implM {A} (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
  impl segs (at_node segs) (c s) (epost (fun p => Q (fst p) (snd p))) ms.

Lemma implM_ret : forall {A} (a : A) s Q ms, evt segs (Q a s) ms -> implM (mret a) s Q ms.
Proof. intros A a s Q ms H. unfold implM, mret. apply impl_ret_ok. exact H. Qed.

Lemma implM_unr : forall {A} s (Q : A -> St -> machine_state -> Prop) ms, implM munr s Q ms.
Proof. intros. unfold implM, munr. apply impl_ret_unr. Qed.

Lemma implM_bind : forall {A B} (m : M A) (f : A -> M B) s Q1 Q ms,
  implM m s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implM (f a) s' Q ms') ->
  implM (mbind m f) s Q ms.
Proof.
  intros A B m f s Q1 Q ms Hm Hf. unfold implM, mbind in *.
  eapply impl_ebind; [exact Hm|]. intros [a s'] ms' H. cbn in *. apply Hf. exact H.
Qed.

Lemma implM_mono : forall {A} (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  implM m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implM m s Q' ms.
Proof.
  intros A m s Q Q' ms H HQ. unfold implM in *. eapply impl_epost_mono; [exact H|].
  intros [a s'] ms'; cbn; auto.
Qed.

Lemma implM_sys : forall {A} n (dec : resp -> option A) s Q ms,
  evt segs (fun ms1 => at_node segs n ms1 /\
                       forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms ->
  implM (msys n dec) s Q ms.
Proof.
  intros A n dec s Q ms H. unfold implM, msys. apply impl_enode.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp [a s'] E. cbn. specialize (Hk rsp).
  destruct (dec rsp) as [a'|]; [|discriminate]. inversion E; subst. apply Hk. reflexivity.
Qed.

Lemma implM_get : forall s Q ms, evt segs (Q s s) ms -> implM mget s Q ms.
Proof. intros. unfold implM, mget. apply impl_ret_ok. exact H. Qed.
Lemma implM_put : forall s s' Q ms, evt segs (Q tt s') ms -> implM (mput s') s Q ms.
Proof. intros. unfold implM, mput. apply impl_ret_ok. exact H. Qed.
Lemma implM_upd : forall f s Q ms, evt segs (Q tt (f s)) ms -> implM (mupd f) s Q ms.
Proof. intros. unfold implM, mupd. apply impl_ret_ok. exact H. Qed.

Lemma implM_evt : forall {A} (c : M A) s Q P ms,
  evt segs P ms -> (forall ms', P ms' -> implM c s Q ms') -> implM c s Q ms.
Proof. intros A c s Q P ms H K. unfold implM in *. eapply impl_evt; eauto. Qed.

Lemma implM_loop_S : forall {X R} fuel (body : X -> M (X + R)) x s Q ms,
  implM (body x) s (fun r s' ms' => match r with
                                   | inl x' => implM (mloop fuel body x') s' Q ms'
                                   | inr v => evt segs (Q v s') ms'
                                   end) ms ->
  implM (mloop (S fuel) body x) s Q ms.
Proof.
  intros X R fuel body x s Q ms H. cbn [mloop]. eapply implM_bind; [exact H|].
  intros [x'|v] s' ms' H'; cbn in H'.
  - exact H'.
  - apply implM_ret. exact H'.
Qed.

End Machine.
End Monad.

Arguments M St A : clear implicits.

Declare Scope mspec_scope.
Notation "x <- m ;; k" := (mbind m (fun x => k)) (at level 100, m at next level, right associativity) : mspec_scope.
Notation "m ;;; k" := (mbind m (fun _ => k)) (at level 100, right associativity) : mspec_scope.
Notation "' p <- m ;; k" := (mbind m (fun x => let 'p := x in k)) (at level 100, p pattern, m at next level, right associativity) : mspec_scope.
End Monad.

Module MSafe.
From Stdlib Require Import ZArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes.
Import Monad.
Import ListNotations.
Import ITree.Exc.


Fixpoint twf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> twf (k rsp) mo' P
  end.

Lemma twf_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twf t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twf t mo P'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
Qed.

Lemma twf_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twf t mo (fun a mo1 => twf (f a) mo1 P) -> twf (ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.

Lemma twf_tsafe : forall {R} (t : itree node R) mo P, twf t mo P -> tsafe nstep nsafe t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact I|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH. eapply Hk; eauto.
Qed.

Lemma twf_tpath : forall {R} (t : itree node R) mo P tr r mo',
  twf t mo P -> tpath nstep t mo tr r mo' -> P r mo'.
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo P tr r mo' H Hp; cbn in *.
  - destruct Hp as (<- & -> & ->). exact H.
  - destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    eapply IH; [eapply Hk; exact Hst| exact Hp].
Qed.

Definition etwf {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twf t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwf_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwf t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwf t mo Q'.
Proof.
  intros A t mo Q Q' H HQ. unfold etwf in *. eapply twf_mono; [exact H|].
  intros [|a] mo1; cbn; auto.
Qed.

Lemma etwf_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
  etwf t mo (fun a mo1 => etwf (f a) mo1 Q) -> etwf (ebind t f) mo Q.
Proof.
  intros A B t f mo Q H. unfold etwf, ebind in *. apply twf_bind.
  eapply twf_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [destruct Ha| exact Ha].
Qed.

Lemma etwf_ret : forall {A} (a : A) mo (Q : A -> Model -> Prop), Q a mo -> etwf (Ret (Ok a)) mo Q.
Proof. intros A a mo Q H. exact H. Qed.

Lemma etwf_enode : forall {A} n (pl : resp -> option A) mo (Q : A -> Model -> Prop),
  nsafe n mo ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, pl rsp = Some a /\ Q a mo') ->
  etwf (enode n pl) mo Q.
Proof.
  intros A n pl mo Q Hs Hk. unfold etwf, enode. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

Lemma etwf_leaves : forall {A} (t : itree node (exc A)) mo,
  etwf t mo (fun _ _ => False) -> leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof.
  intros A t mo H. split.
  - intros tr r mo' Hp. pose proof (twf_tpath t mo _ tr r mo' H Hp) as HP. destruct r; exact HP.
  - eapply twf_tsafe. exact H.
Qed.


Section MSpec.
Context {St : Type}.

Definition assn : Type := St -> Model -> Prop.

Definition mspec {A} (P : assn) (m : M St A) (Q : A -> assn) : Prop :=
  forall s mo, P s mo -> etwf (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspec_ret {A} (a : A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo -> Q a s mo) -> mspec P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspec_bind {A B} (m : M St A) (f : A -> M St B) (P : assn) (Q1 : A -> assn) (Q : B -> assn) :
  mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind. apply etwf_ebind.
  eapply etwf_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

Lemma mspec_conseq {A} (m : M St A) (P P' : assn) (Q Q' : A -> assn) :
  mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. eapply etwf_mono; [exact (Hm s mo (HP _ _ HP'))|].
  intros [a s1] mo1; cbn; auto.
Qed.

Lemma mspec_pre {A} (m : M St A) (P P' : assn) (Q : A -> assn) :
  mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> mspec P' m Q.
Proof. intros Hm HP. eapply mspec_conseq; eauto. Qed.

Lemma mspec_post {A} (m : M St A) (P : assn) (Q Q' : A -> assn) :
  mspec P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P m Q'.
Proof. intros Hm HQ. eapply mspec_conseq; eauto. Qed.

Lemma mspec_munr {A} (Q : A -> assn) : mspec (fun _ _ => False) munr Q.
Proof. intros s mo []. Qed.

Lemma mspec_false {A} (m : M St A) (Q : A -> assn) : mspec (fun _ _ => False) m Q.
Proof. intros s mo []. Qed.

Lemma mspec_get (P : assn) : mspec P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

Lemma mspec_put (P : assn) (s1 : St) : mspec P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspec_upd (P : assn) (f : St -> St) : mspec P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspec_upd' (P : assn) (Q : unit -> assn) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspec P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspec_sys {A} (n : node) (dec : resp -> option A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
  mspec P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

Lemma mspec_if {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  (b = true -> mspec P m1 Q) -> (b = false -> mspec P m2 Q) -> mspec P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

Lemma mspec_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  mspec (fun s mo => P s mo /\ b = true) m1 Q -> mspec (fun s mo => P s mo /\ b = false) m2 Q ->
  mspec P (if b then m1 else m2) Q.
Proof. intros H1 H2 s mo HP. destruct b; [apply H1|apply H2]; auto. Qed.

Lemma mspec_exI {A X} (P : X -> assn) (m : M St A) (Q : A -> assn) :
  (forall x, mspec (P x) m Q) -> mspec (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.

Lemma mspec_pure {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
  (phi -> mspec P m Q) -> mspec (fun s mo => P s mo /\ phi) m Q.
Proof. intros H s mo [HP Hphi]. exact (H Hphi s mo HP). Qed.

Lemma mspec_pure_l {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
  (phi -> mspec P m Q) -> mspec (fun s mo => phi /\ P s mo) m Q.
Proof. intros H s mo [Hphi HP]. exact (H Hphi s mo HP). Qed.

Lemma mspec_pointwise {A} (P : assn) (m : M St A) (Q : A -> assn) :
  (forall s mo, P s mo -> mspec (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspec P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

Lemma mspec_when (b : bool) (m : M St unit) (P : assn) (Q : unit -> assn) :
  (b = true -> mspec P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspec P (mwhen b m) Q.
Proof. intros H1 H2. unfold mwhen. destruct b; [apply H1; reflexivity|]. apply mspec_ret. apply H2. reflexivity. Qed.

Lemma mspec_loop {X R} (body : X -> M St (X + R)) (I : X -> assn) (Q : R -> assn) (meas : X -> nat) :
  (forall x, mspec (I x) (body x)
     (fun r s mo => match r with
                    | inl x' => I x' s mo /\ (meas x' < meas x)%nat
                    | inr v => Q v s mo
                    end)) ->
  forall fuel x, (meas x < fuel)%nat -> mspec (I x) (mloop fuel body x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x Hf; [lia|].
  cbn [mloop]. eapply mspec_bind; [apply Hb|].
  intros [x'|v]; cbn.
  - intros s mo [HI Hm]. apply (IH x'); [lia| exact HI].
  - apply mspec_ret. auto.
Qed.

Lemma mspec_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn) (Q : B -> assn) :
  mspec P m (fun _ => R) -> (forall a, mspec R (f a) Q) -> mspec P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspec_bind; [exact Hm|]. intros a. apply Hf. Qed.

Lemma mspec_program {A} (P : assn) (m : M St A) s mo :
  mspec P m (fun _ _ _ => False) -> P s mo ->
  forall {B} (f : A * St -> itree node (exc B)),
  leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
  intros Hm HP B f. apply etwf_leaves. apply etwf_ebind.
  eapply etwf_mono; [exact (Hm s mo HP)|]. intros [a s'] mo' [].
Qed.

End MSpec.

Arguments assn St : clear implicits.
Arguments mspec {St A} P m Q.
End MSafe.

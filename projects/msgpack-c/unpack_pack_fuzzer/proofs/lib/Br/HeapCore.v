(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Frame Step Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog A_MallocBlocks A_MallocHINV A_MallocFacts_A A_Malloc_iface A_MallocFacts_inv2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition rpub (a : Z) : Prop :=
  (RNEED_LOCKS <= a < RNEED_LOCKS + 1) \/ (RPAGE_SIZE <= a < RPAGE_SIZE + 8)
  \/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RSSP_GUARD <= a < RSSP_GUARD + 8).

Definition PUBS (m : mem) : Prop :=
  rw_cells rsegs m RNEED_LOCKS [C1 (b8 0)]
  /\ rw_cells rsegs m RPAGE_SIZE [C8 (wz 4096)]
  /\ rw_cells rsegs m RGOT_SSP [C8 (wz RSSP_GUARD)]
  /\ rw_cells rsegs m RSSP_GUARD [C8 (wz ssp_canary)].

Definition rmrep_core (st : mstate) (m : mem) : Prop :=
  rregions_wf st /\ rmrep_ctx st m /\ rw_cells rsegs m RMLOCK [C4 (wz 0)]
  /\ rmrep_areas st m /\ rmrep_groups st m /\ rmrep_shadow st m.

Lemma rmrep_split : forall st m, rmrep st m <-> rmrep_core st m /\ PUBS m.
Proof.
  intros st m. unfold rmrep, rmrep_core, PUBS, rmrep_globals. tauto.
Qed.

Definition RHEAP_core (s : PState) (LB : list block) (m : mem) : Prop :=
  exists st LB0, Permutation LB0 LB /\ strip st = ps_m s /\ rmrep_core st m
                 /\ HINV_from ref_reserved st (ps_brk s) LB0.

Lemma RHEAP_split : forall s LB m, RHEAP s LB m <-> RHEAP_core s LB m /\ PUBS m.
Proof.
  intros s LB m. unfold RHEAP, RHEAP_core. split.
  - intros (st & LB0 & HP & Hs & MR & HI). apply rmrep_split in MR as [MC PU]. split; [| exact PU]. exists st, LB0. auto.
  - intros [(st & LB0 & HP & Hs & MC & HI) PU]. exists st, LB0. split; [exact HP|]. split; [exact Hs|]. split; [| exact HI].
    apply rmrep_split. auto.
Qed.

Lemma RHEAP_core_perm : forall s LB LB' m, RHEAP_core s LB m -> Permutation LB LB' -> RHEAP_core s LB' m.
Proof.
  intros s LB LB' m (st & LB0 & HP & H) P. exists st, LB0. split; [| exact H]. eapply Permutation_trans; eassumption.
Qed.

Definition rcorefoot (st : mstate) (a : Z) : Prop :=
  (RCTX <= a < RCTX + 928) \/ (RMLOCK <= a < RMLOCK + 4)
  \/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

Lemma rcorefoot_rrepfoot : forall st a, rcorefoot st a -> rrepfoot st a.
Proof.
  intros st a [H|[H|[H|[H|H]]]].
  - apply rrepfoot_ctx; exact H.
  - apply rrepfoot_mlock; exact H.
  - destruct H as (ak & ar & H1 & H2). eapply rrepfoot_area; eauto.
  - destruct H as (b & gh & H1 & H2). eapply rrepfoot_group; eauto.
  - destruct H as (rid & r & v & H1 & H2 & H3 & H4). eapply rrepfoot_known; eauto.
Qed.

Lemma wmono_of_dom : forall m m',
  (forall x : word, m x <> None -> m' x <> None) -> wmono rsegs m m'.
Proof.
  intros m m' H x. unfold wview. destruct (m x) eqn:E1.
  - intros _. specialize (H x ltac:(rewrite E1; discriminate)). destruct (m' x); [discriminate| exfalso; apply H; reflexivity].
  - destruct (m' x); [intros; discriminate| intros X; exact X].
Qed.

Lemma rmrep_core_transport : forall st m m',
  rmrep_core st m ->
  (forall a, 0 <= a < 2^64 -> rcorefoot st a -> m' (wa a) = m (wa a)) ->
  wmono rsegs m m' ->
  rmrep_core st m'.
Proof.
  intros st m m' (WF & CX & ML & AR & GR & SH) AG WM.
  assert (AGR : forall A n, (forall a, A <= a < A + n -> rcorefoot st a) -> 0 <= A -> A + n <= 2^64 -> agree_on m m' A n).
  { intros A n HF HA HB a Ha. apply AG; [lia|]. apply HF. exact Ha. }
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rcorefoot st a) -> rw_cells rsegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; eauto. apply AGR; [exact HP| lia| lia]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
    pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. left. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. apply AGR; rewrite ?L1 in *; try lia. intros a Ha. left. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. apply AGR; rewrite ?L2 in *; try lia. intros a Ha. left. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. apply AGR; rewrite ?L3 in *; try lia. intros a Ha. left. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. apply AGR; rewrite ?L4 in *; try lia. intros a Ha. left. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. left. cbn in Ha. unfold RCTX in *. lia.
  - apply TC; [exact ML |]. intros a Ha. right; left. cbn in Ha. unfold RMLOCK in *. lia.
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. do 2 right; left. exists ak, ar. split; [exact Ha| lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. do 2 right; left. exists ak, ar. split; [exact Ha| lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. do 2 right; left. exists ak, ar. split; [exact Ha| lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. do 3 right; left. exists b, gh. split; [exact Hb| lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      pose proof Bt as (B0 & B1 & _). cbn in B1.
      eapply rbytes_at_agree; [exact Bt|]. apply AGR; cbn; try lia. intros a Ha.
      do 4 right. exists rid, r, v. split; [exact Hr|]. split; [exact Hk|]. split; [lia|].
      replace (a - r_base r) with o by lia. exact Hc.
Qed.

Definition RIMG_LO : Z := 0x10000.
Definition RIMG_HI : Z := 0x88000.

Lemma RIMG_HI_reserved_top : reserved_top (segments_reserved rsegs) = RIMG_HI.
Proof. vm_compute. reflexivity. Qed.

Definition rclient_img (a : Z) : Prop := RIMG_LO <= a < RIMG_HI /\ ~ (RMLOCK <= a < RCTX + 936).

Lemma rcorefoot_where : forall st a, rregions_wf st -> rcorefoot st a ->
  a < alloc_ceiling /\ (RMLOCK <= a < RCTX + 928 \/ a < RIMG_LO \/ RIMG_HI <= a).
Proof.
  intros st a WF RF. pose proof WF as (_ & WR & _).
  destruct RF as [R1|[R2|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|(q & rq & v & Hq & Kq & Rq & Cq)]]]];
    pose_ceil; unfold RCTX, RMLOCK, RIMG_LO, RIMG_HI in *.
  - lia. - lia.
  - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. pose_ceil.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. pose_ceil.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. pose_ceil. lia.
Qed.

Lemma rcorefoot_not_block : forall st LB0 m a blk,
  MFACTS_g (resv:=ref_reserved) st LB0 -> rmrep_core st m -> In blk LB0 -> rcorefoot st a ->
  ~ (blk_addr blk <= a < blk_addr blk + blk_size blk).
Proof.
  intros st LB0 m a blk MF MC INb RF Ha. pose proof MC as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (MR' : exists r, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
            /\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)).
  {
    pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk INb) as [BS BR BZ].
    destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
    destruct BR as (r & Hr & Hk).
    pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
    pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
    destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
    change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
    exists r. split; [exact Hr|]. split; [exact Hk|].
    pose proof (round_up_pg_ge (r_len r)) as RU.
    rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
    unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
    assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    rewrite Esnd in EA. lia. }
  destruct MR' as (r & Hr & Hk & LOB & HIB).
  destruct (WR _ _ Hr) as (RB0 & _ & _ & RC & RFr). pose proof (rreserved_disjoint1 _ _ RFr) as DI.
  pose proof (round_up_pg_ge (r_len r)) as RU.
  destruct RF as [R1|[R2|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|(q & rq & v & Hq & Kq & Rq & Cq)]]]].
  - unfold RCTX in R1. assert (0 < round_up_pg (r_len r)) by lia. destruct (DI ltac:(lia)); lia.
  - unfold RMLOCK in R2. destruct (DI ltac:(lia)); lia.
  - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
    assert (NEr : fst ak <> fst (blk_slot blk)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
    pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
    destruct (DJ _ _ _ _ Hra Hr NEr); lia.
  - destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
    destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NEr].
    + rewrite E, Hr in Hrb. inversion Hrb; subst rb.
      pose proof (mf_hdr_clear _ _ MF b' gh blk r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
    + pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
  - destruct (N.eq_dec q (fst (blk_slot blk))) as [->|NEr].
    + rewrite Hr in Hq. inversion Hq; subst rq.
      destruct (mf_blk_unknown _ _ MF blk r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
    + pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
Qed.

Lemma core_block_inside : forall st LB0 (m : mem) blk,
  MFACTS_g (resv:=ref_reserved) st LB0 -> In blk LB0 ->
  exists r, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
            /\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r).
Proof.
  intros st LB0 m blk MF INb.
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk INb) as [BS BR BZ].
  destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
  destruct BR as (r & Hr & Hk).
  pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  exists r. split; [exact Hr|]. split; [exact Hk|].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA. lia.
Qed.

Lemma RHEAP_core_blocks_disjoint : forall s LB m b1 b2,
  RHEAP_core s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros s LB m b1 b2 (st & LB0 & HP & _ & MC & [_ AR]) I1 I2 NE. pose proof (A_MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I1]).
  assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I2]).
  destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
  - exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
    clear -ND IN1 IN2 ES. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
    destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
    + exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
    + exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
  - destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
    + exact (mf_blocks_disjoint _ _ MF b1 b2 IN1 IN2 EF NS).
    + destruct (core_block_inside st LB0 m b1 MF IN1) as (r1 & Hr1 & Hk1 & LO1 & HI1).
      destruct (core_block_inside st LB0 m b2 MF IN2) as (r2 & Hr2 & Hk2 & LO2 & HI2).
      pose proof MC as (WF & _). pose proof WF as (_ & _ & DJ & _).
      pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
      destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

Lemma RHEAP_core_nodup : forall s LB m, RHEAP_core s LB m -> List.NoDup (map blk_id LB).
Proof.
  intros s LB m (st & LB0 & HP & _ & _ & [_ AR]). pose proof (mf_nodup _ _ (A_MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
  inversion ND; subst. constructor; [|apply IH; assumption].
  intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
  unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

Lemma nodup_map_neq : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> x <> y -> f x <> f y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy NE; [destruct Hx|].
  cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hx as [->|Hx], Hy as [->|Hy].
  - exfalso; apply NE; reflexivity.
  - intros E. apply NI. rewrite E. apply in_map. exact Hy.
  - intros E. apply NI. rewrite <- E. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

Lemma RHEAP_core_blocks_disjoint_addr : forall s LB m b1 b2 a,
  RHEAP_core s LB m -> In b1 LB -> In b2 LB -> blk_addr b1 <> blk_addr b2 ->
  blk_addr b1 <= a < blk_addr b1 + blk_size b1 -> ~ (blk_addr b2 <= a < blk_addr b2 + blk_size b2).
Proof.
  intros s LB m b1 b2 a RC I1 I2 NE H1 H2.
  assert (NEb : b1 <> b2) by (intros ->; apply NE; reflexivity).
  pose proof (nodup_map_neq blk_id LB b1 b2 (RHEAP_core_nodup s LB m RC) I1 I2 NEb) as NI.
  destruct (RHEAP_core_blocks_disjoint s LB m b1 b2 RC I1 I2 NI); lia.
Qed.

Lemma RHEAP_core_frame : forall s LB m m',
  RHEAP_core s LB m ->
  (forall a, 0 <= a < 2^64 -> a < alloc_ceiling ->
     ~ (exists blk, In blk LB /\ blk_addr blk <= a < blk_addr blk + blk_size blk) -> ~ rclient_img a ->
     m' (wa a) = m (wa a)) ->
  (forall x : word, m x <> None -> m' x <> None) ->
  RHEAP_core s LB m'.
Proof.
  intros s LB m m' (st & LB0 & HP & Hst & MC & HI) AG DOM. exists st, LB0. split; [exact HP|]. split; [exact Hst|]. split; [| exact HI].
  destruct HI as [_ AR]. pose proof (A_MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  pose proof MC as (WF & _).
  eapply rmrep_core_transport; [exact MC| | apply wmono_of_dom; exact DOM].
  intros a Ha RF. destruct (rcorefoot_where st a WF RF) as [AC AW]. apply AG; [exact Ha| exact AC| |].
  - intros (blk & Hblk & R). apply (rcorefoot_not_block st LB0 m a blk MF MC); [| exact RF| exact R].
    eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hblk].
  - intros [I1 I2]. unfold RIMG_LO, RIMG_HI, RMLOCK, RCTX in *. lia.
Qed.

Lemma pos_aligned_4096 : forall x, 0 < x -> x mod 4096 = 0 -> 4096 <= x.
Proof. intros x Hx Hm. Z.div_mod_to_equations. lia. Qed.

Lemma RHEAP_core_block_range : forall s LB m b, RHEAP_core s LB m -> In b LB ->
  4096 <= blk_addr b /\ 0 <= blk_size b /\ blk_addr b + blk_size b <= alloc_ceiling
  /\ (blk_addr b + blk_size b <= RIMG_LO \/ RIMG_HI <= blk_addr b)
  /\ forall a, blk_addr b <= a < blk_addr b + blk_size b -> m (wa a) <> None.
Proof.
  intros s LB m b (st & LB0 & HP & Hst & MC & HI) Hb.
  destruct HI as [_ AR]. pose proof (A_MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
  pose proof MC as (WF & _ & _ & _ & _ & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b INb) as [BS BR BZ].
  destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
  destruct BR as (r & Hr & Hk).
  pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bm & Hm & Efst & Esnd & _).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g bm Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot b) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA.
  destruct (WR _ _ Hr) as (RB0 & RAL & RL0 & RC & RFr). pose proof (rreserved_disjoint1 _ _ RFr) as DI.
  pose proof (pos_aligned_4096 _ RB0 RAL) as R4096.
  unfold RIMG_LO, RIMG_HI. split; [lia|]. split; [lia|]. split; [lia|]. split; [destruct (DI ltac:(lia)); lia|].
  intros a Ha. destruct (SH _ _ Hr Hk) as [HWr _]. destruct HWr as (_ & _ & HW).
  specialize (HW (a - r_base r) ltac:(lia)). replace (r_base r + (a - r_base r)) with a in HW by lia.
  unfold wview in HW. intros E. rewrite E in HW.
  pose_ceil. rewrite ref_find_segment_none in HW; [exact (HW eq_refl)| lia|].
  unfold wa. rewrite unsigned_lit by lia. destruct (DI ltac:(lia)); lia.
Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_inv2.
Import F_syscalls.TwinB RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition rpub (a : Z) : Prop :=
  (RNEED_LOCKS <= a < RNEED_LOCKS + 1) \/ (RPAGE_SIZE <= a < RPAGE_SIZE + 8)
  \/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RSSP_GUARD <= a < RSSP_GUARD + 8).

Definition PUBS (m : mem) : Prop :=
  rw_cells rsegs m RNEED_LOCKS [C1 (b8 0)]
  /\ rw_cells rsegs m RPAGE_SIZE [C8 (wz 4096)]
  /\ rw_cells rsegs m RGOT_SSP [C8 (wz RSSP_GUARD)]
  /\ rw_cells rsegs m RSSP_GUARD [C8 (wz ssp_canary)].

Definition rmrep_core (st : mstate) (m : mem) : Prop :=
  rregions_wf st /\ rmrep_ctx st m /\ rw_cells rsegs m RMLOCK [C4 (wz 0)]
  /\ rmrep_areas st m /\ rmrep_groups st m /\ rmrep_shadow st m.

Lemma rmrep_split : forall st m, rmrep st m <-> rmrep_core st m /\ PUBS m.
Proof.
  intros st m. unfold rmrep, rmrep_core, PUBS, rmrep_globals. tauto.
Qed.

Definition RHEAP_core (s : PState) (LB : list block) (m : mem) : Prop :=
  exists st LB0, Permutation LB0 LB /\ strip st = ps_m s /\ rmrep_core st m
                 /\ HINV_from ref_reserved st (ps_brk s) LB0.

Lemma RHEAP_split : forall s LB m, RHEAP s LB m <-> RHEAP_core s LB m /\ PUBS m.
Proof.
  intros s LB m. unfold RHEAP, RHEAP_core. split.
  - intros (st & LB0 & HP & Hs & MR & HI). apply rmrep_split in MR as [MC PU]. split; [| exact PU]. exists st, LB0. auto.
  - intros [(st & LB0 & HP & Hs & MC & HI) PU]. exists st, LB0. split; [exact HP|]. split; [exact Hs|]. split; [| exact HI].
    apply rmrep_split. auto.
Qed.

Lemma RHEAP_core_perm : forall s LB LB' m, RHEAP_core s LB m -> Permutation LB LB' -> RHEAP_core s LB' m.
Proof.
  intros s LB LB' m (st & LB0 & HP & H) P. exists st, LB0. split; [| exact H]. eapply Permutation_trans; eassumption.
Qed.

Definition rcorefoot (st : mstate) (a : Z) : Prop :=
  (RCTX <= a < RCTX + 928) \/ (RMLOCK <= a < RMLOCK + 4)
  \/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

Lemma rcorefoot_rrepfoot : forall st a, rcorefoot st a -> rrepfoot st a.
Proof.
  intros st a [H|[H|[H|[H|H]]]].
  - apply rrepfoot_ctx; exact H.
  - apply rrepfoot_mlock; exact H.
  - destruct H as (ak & ar & H1 & H2). eapply rrepfoot_area; eauto.
  - destruct H as (b & gh & H1 & H2). eapply rrepfoot_group; eauto.
  - destruct H as (rid & r & v & H1 & H2 & H3 & H4). eapply rrepfoot_known; eauto.
Qed.

Lemma wmono_of_dom : forall m m',
  (forall x : word, m x <> None -> m' x <> None) -> wmono rsegs m m'.
Proof.
  intros m m' H x. unfold wview. destruct (m x) eqn:E1.
  - intros _. specialize (H x ltac:(rewrite E1; discriminate)). destruct (m' x); [discriminate| exfalso; apply H; reflexivity].
  - destruct (m' x); [intros; discriminate| intros X; exact X].
Qed.

Lemma rmrep_core_transport : forall st m m',
  rmrep_core st m ->
  (forall a, 0 <= a < 2^64 -> rcorefoot st a -> m' (wa a) = m (wa a)) ->
  wmono rsegs m m' ->
  rmrep_core st m'.
Proof.
  intros st m m' (WF & CX & ML & AR & GR & SH) AG WM.
  assert (AGR : forall A n, (forall a, A <= a < A + n -> rcorefoot st a) -> 0 <= A -> A + n <= 2^64 -> agree_on m m' A n).
  { intros A n HF HA HB a Ha. apply AG; [lia|]. apply HF. exact Ha. }
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rcorefoot st a) -> rw_cells rsegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; eauto. apply AGR; [exact HP| lia| lia]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
    pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. left. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. apply AGR; rewrite ?L1 in *; try lia. intros a Ha. left. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. apply AGR; rewrite ?L2 in *; try lia. intros a Ha. left. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. apply AGR; rewrite ?L3 in *; try lia. intros a Ha. left. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. apply AGR; rewrite ?L4 in *; try lia. intros a Ha. left. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. left. cbn in Ha. unfold RCTX in *. lia.
  - apply TC; [exact ML |]. intros a Ha. right; left. cbn in Ha. unfold RMLOCK in *. lia.
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. do 2 right; left. exists ak, ar. split; [exact Ha| lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. do 2 right; left. exists ak, ar. split; [exact Ha| lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. do 2 right; left. exists ak, ar. split; [exact Ha| lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. do 3 right; left. exists b, gh. split; [exact Hb| lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      pose proof Bt as (B0 & B1 & _). cbn in B1.
      eapply rbytes_at_agree; [exact Bt|]. apply AGR; cbn; try lia. intros a Ha.
      do 4 right. exists rid, r, v. split; [exact Hr|]. split; [exact Hk|]. split; [lia|].
      replace (a - r_base r) with o by lia. exact Hc.
Qed.

Definition RIMG_LO : Z := 0x10000.
Definition RIMG_HI : Z := 0x8a000.

Lemma RIMG_HI_reserved_top : reserved_top (segments_reserved rsegs) = RIMG_HI.
Proof. vm_compute. reflexivity. Qed.

Definition rclient_img (a : Z) : Prop := RIMG_LO <= a < RIMG_HI /\ ~ (RMLOCK <= a < RCTX + 936).

Lemma rcorefoot_where : forall st a, rregions_wf st -> rcorefoot st a ->
  a < alloc_ceiling /\ (RMLOCK <= a < RCTX + 928 \/ a < RIMG_LO \/ RIMG_HI <= a).
Proof.
  intros st a WF RF. pose proof WF as (_ & WR & _).
  destruct RF as [R1|[R2|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|(q & rq & v & Hq & Kq & Rq & Cq)]]]];
    pose_ceil; unfold RCTX, RMLOCK, RIMG_LO, RIMG_HI in *.
  - lia. - lia.
  - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. pose_ceil.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. pose_ceil.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. pose_ceil. lia.
Qed.

Lemma rcorefoot_not_block : forall st LB0 m a blk,
  MFACTS_g (resv:=ref_reserved) st LB0 -> rmrep_core st m -> In blk LB0 -> rcorefoot st a ->
  ~ (blk_addr blk <= a < blk_addr blk + blk_size blk).
Proof.
  intros st LB0 m a blk MF MC INb RF Ha. pose proof MC as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (MR' : exists r, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
            /\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)).
  {
    pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk INb) as [BS BR BZ].
    destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
    destruct BR as (r & Hr & Hk).
    pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
    pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
    destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
    change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
    exists r. split; [exact Hr|]. split; [exact Hk|].
    pose proof (round_up_pg_ge (r_len r)) as RU.
    rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
    unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
    assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    rewrite Esnd in EA. lia. }
  destruct MR' as (r & Hr & Hk & LOB & HIB).
  destruct (WR _ _ Hr) as (RB0 & _ & _ & RC & RFr). pose proof (rreserved_disjoint1 _ _ RFr) as DI.
  pose proof (round_up_pg_ge (r_len r)) as RU.
  destruct RF as [R1|[R2|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|(q & rq & v & Hq & Kq & Rq & Cq)]]]].
  - unfold RCTX in R1. assert (0 < round_up_pg (r_len r)) by lia. destruct (DI ltac:(lia)); lia.
  - unfold RMLOCK in R2. destruct (DI ltac:(lia)); lia.
  - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
    assert (NEr : fst ak <> fst (blk_slot blk)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
    pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
    destruct (DJ _ _ _ _ Hra Hr NEr); lia.
  - destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
    destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NEr].
    + rewrite E, Hr in Hrb. inversion Hrb; subst rb.
      pose proof (mf_hdr_clear _ _ MF b' gh blk r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
    + pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
  - destruct (N.eq_dec q (fst (blk_slot blk))) as [->|NEr].
    + rewrite Hr in Hq. inversion Hq; subst rq.
      destruct (mf_blk_unknown _ _ MF blk r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
    + pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
Qed.

Lemma core_block_inside : forall st LB0 (m : mem) blk,
  MFACTS_g (resv:=ref_reserved) st LB0 -> In blk LB0 ->
  exists r, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
            /\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r).
Proof.
  intros st LB0 m blk MF INb.
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk INb) as [BS BR BZ].
  destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
  destruct BR as (r & Hr & Hk).
  pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  exists r. split; [exact Hr|]. split; [exact Hk|].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA. lia.
Qed.

Lemma RHEAP_core_blocks_disjoint : forall s LB m b1 b2,
  RHEAP_core s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros s LB m b1 b2 (st & LB0 & HP & _ & MC & [_ AR]) I1 I2 NE. pose proof (A_MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I1]).
  assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I2]).
  destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
  - exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
    clear -ND IN1 IN2 ES. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
    destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
    + exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
    + exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
  - destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
    + exact (mf_blocks_disjoint _ _ MF b1 b2 IN1 IN2 EF NS).
    + destruct (core_block_inside st LB0 m b1 MF IN1) as (r1 & Hr1 & Hk1 & LO1 & HI1).
      destruct (core_block_inside st LB0 m b2 MF IN2) as (r2 & Hr2 & Hk2 & LO2 & HI2).
      pose proof MC as (WF & _). pose proof WF as (_ & _ & DJ & _).
      pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
      destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

Lemma RHEAP_core_nodup : forall s LB m, RHEAP_core s LB m -> List.NoDup (map blk_id LB).
Proof.
  intros s LB m (st & LB0 & HP & _ & _ & [_ AR]). pose proof (mf_nodup _ _ (A_MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
  inversion ND; subst. constructor; [|apply IH; assumption].
  intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
  unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

Lemma nodup_map_neq : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> x <> y -> f x <> f y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy NE; [destruct Hx|].
  cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hx as [->|Hx], Hy as [->|Hy].
  - exfalso; apply NE; reflexivity.
  - intros E. apply NI. rewrite E. apply in_map. exact Hy.
  - intros E. apply NI. rewrite <- E. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

Lemma RHEAP_core_blocks_disjoint_addr : forall s LB m b1 b2 a,
  RHEAP_core s LB m -> In b1 LB -> In b2 LB -> blk_addr b1 <> blk_addr b2 ->
  blk_addr b1 <= a < blk_addr b1 + blk_size b1 -> ~ (blk_addr b2 <= a < blk_addr b2 + blk_size b2).
Proof.
  intros s LB m b1 b2 a RC I1 I2 NE H1 H2.
  assert (NEb : b1 <> b2) by (intros ->; apply NE; reflexivity).
  pose proof (nodup_map_neq blk_id LB b1 b2 (RHEAP_core_nodup s LB m RC) I1 I2 NEb) as NI.
  destruct (RHEAP_core_blocks_disjoint s LB m b1 b2 RC I1 I2 NI); lia.
Qed.

Lemma RHEAP_core_frame : forall s LB m m',
  RHEAP_core s LB m ->
  (forall a, 0 <= a < 2^64 -> a < alloc_ceiling ->
     ~ (exists blk, In blk LB /\ blk_addr blk <= a < blk_addr blk + blk_size blk) -> ~ rclient_img a ->
     m' (wa a) = m (wa a)) ->
  (forall x : word, m x <> None -> m' x <> None) ->
  RHEAP_core s LB m'.
Proof.
  intros s LB m m' (st & LB0 & HP & Hst & MC & HI) AG DOM. exists st, LB0. split; [exact HP|]. split; [exact Hst|]. split; [| exact HI].
  destruct HI as [_ AR]. pose proof (A_MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  pose proof MC as (WF & _).
  eapply rmrep_core_transport; [exact MC| | apply wmono_of_dom; exact DOM].
  intros a Ha RF. destruct (rcorefoot_where st a WF RF) as [AC AW]. apply AG; [exact Ha| exact AC| |].
  - intros (blk & Hblk & R). apply (rcorefoot_not_block st LB0 m a blk MF MC); [| exact RF| exact R].
    eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hblk].
  - intros [I1 I2]. unfold RIMG_LO, RIMG_HI, RMLOCK, RCTX in *. lia.
Qed.

Lemma pos_aligned_4096 : forall x, 0 < x -> x mod 4096 = 0 -> 4096 <= x.
Proof. intros x Hx Hm. Z.div_mod_to_equations. lia. Qed.

Lemma RHEAP_core_block_range : forall s LB m b, RHEAP_core s LB m -> In b LB ->
  4096 <= blk_addr b /\ 0 <= blk_size b /\ blk_addr b + blk_size b <= alloc_ceiling
  /\ (blk_addr b + blk_size b <= RIMG_LO \/ RIMG_HI <= blk_addr b)
  /\ forall a, blk_addr b <= a < blk_addr b + blk_size b -> m (wa a) <> None.
Proof.
  intros s LB m b (st & LB0 & HP & Hst & MC & HI) Hb.
  destruct HI as [_ AR]. pose proof (A_MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
  pose proof MC as (WF & _ & _ & _ & _ & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b INb) as [BS BR BZ].
  destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
  destruct BR as (r & Hr & Hk).
  pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bm & Hm & Efst & Esnd & _).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g bm Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot b) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA.
  destruct (WR _ _ Hr) as (RB0 & RAL & RL0 & RC & RFr). pose proof (rreserved_disjoint1 _ _ RFr) as DI.
  pose proof (pos_aligned_4096 _ RB0 RAL) as R4096.
  unfold RIMG_LO, RIMG_HI. split; [lia|]. split; [lia|]. split; [lia|]. split; [destruct (DI ltac:(lia)); lia|].
  intros a Ha. destruct (SH _ _ Hr Hk) as [HWr _]. destruct HWr as (_ & _ & HW).
  specialize (HW (a - r_base r) ltac:(lia)). replace (r_base r + (a - r_base r)) with a in HW by lia.
  unfold wview in HW. intros E. rewrite E in HW.
  pose_ceil. rewrite ref_find_segment_none in HW; [exact (HW eq_refl)| lia|].
  unfold wa. rewrite unsigned_lit by lia. destruct (DI ltac:(lia)); lia.
Qed.

End CEIL.
End TwinB.

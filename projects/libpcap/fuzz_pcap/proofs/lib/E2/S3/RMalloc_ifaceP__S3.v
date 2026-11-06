(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBase.
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_P__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_small.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocCls__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_bigw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_mm_syscalls__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free_K__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module RMalloc_ifaceP.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_P__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.F_malloc_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.Malloc_ifaceP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rregion_addr_facts : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (0 < round_up_pg (r_len r) -> (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x55000 <= r_base r)
                                   /\ (r_base r + round_up_pg (r_len r) <= the_tb \/ the_tb + 4096 <= r_base r)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  split; [|split; [exact RBAL| split; [exact RBC| intros Hn; split; [exact (rreserved_disjoint1 _ _ RFr Hn)| exact (rreserved_tls _ _ RFr Hn)]]]].
  clear RFr. Z.div_mod_to_equations. lia.
Qed.

Lemma rblock_inside st LB m blk :
  MFACTS_g (resv:=ref_reserved) st LB -> rmrep st m -> In blk LB ->
  exists r g idx, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
    /\ (s_slots st) !! (blk_slot blk) = Some (g, idx)
    /\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
    /\ 0 <= blk_size blk
    /\ 4096 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x55000 <= r_base r)
        /\ (r_base r + round_up_pg (r_len r) <= the_tb \/ the_tb + 4096 <= r_base r)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MF MR IN.
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
  destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
  destruct BR as (r & Hr & Hk).
  pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof (rregion_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1).
  exists r, g, idx. split; [exact Hr|]. split; [exact Hk|]. split; [exact SL|].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA. ceil_facts.
  assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.

Lemma RHEAP_blocks_nodup_proof : RHEAP_blocks_nodup_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m (LB0 & HP & _ & [_ AR] & _). set (st := ps_m s) in *. pose proof (mf_nodup _ _ (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
  inversion ND; subst. constructor; [|apply IH; assumption].
  intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
  unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

Lemma RHEAP_block_range_b : forall s LB m b, RHEAP s LB m -> In b LB ->
  rblock_range (blk_addr b) (blk_size b) /\ blk_addr b = conc (ps_m s) (blk_ptr b).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m b (LB0 & HP & MR & [_ AR] & _) HIN. set (st := ps_m s) in *. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
  destruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)). rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
  pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bb & Hm & Efst & Esnd & IDX).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
  pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF).
  unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
  assert (32 <= round_up_pg (r_len r)) by nia.
  (* [comment removed for export] *)
  assert (EP : blk_addr b = conc st (blk_ptr b)).
  { destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL & INV & _ & _ & _ & CR).
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.Forall2_In_l _ _ _ _ CR IN0) as (k & HkB & (C1 & C2 & C3 & C4)).
    unfold blk_ptr. rewrite C3, C1, C4. symmetry. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.conc_aadd.
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.blk_region _ _ _ _ _ k INV HkB) as (rk & Hrk & _). exists rk. exact Hrk. }
  split; [| exact EP].
  unfold rblock_range. ceil_facts. split; [lia|]. split; [|lia].
  rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
  replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
    with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
  apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.

Lemma RHEAP_block_range_proof : RHEAP_block_range_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m p A n HR HIN. destruct (RHEAP_block_range_b s LB m (p, A, n) HR HIN) as [BR EP].
  cbn [blk_addr blk_size blk_ptr blk_slot blk_id fst snd] in BR, EP. split; [exact BR|]. destruct p; cbn in EP |- *. exact EP.
Qed.

Lemma RHEAP_blocks_disjoint_proof : RHEAP_blocks_disjoint_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m b1 b2 (LB0 & HP & MR & [_ AR] & _) I1 I2 NE. set (st := ps_m s) in *. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
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
    + destruct (rblock_inside st LB0 m b1 MF MR IN1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _).
      destruct (rblock_inside st LB0 m b2 MF MR IN2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _).
      pose proof MR as (WF & _). pose proof WF as (_ & _ & DJ & _).
      pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
      destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rrepfoot_where st m a : rmrep st m -> rrepfoot st a ->
  a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38
                        \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
                        \/ ((a < 0x10000 \/ 0x55000 <= a) /\ (a < the_tb \/ the_tb + 4096 <= a))).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
    unfold RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; ceil_facts.
  - lia. - lia. - lia. - lia.
  - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. pose proof (rreserved_tls _ _ RFa) as DT. ceil_facts.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. pose proof (rreserved_tls _ _ RFb) as DT. ceil_facts.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. pose proof (rreserved_tls _ _ RFq) as DT. ceil_facts. lia.
  - lia. - lia.
Qed.

Lemma RHEAP_frame_proof : RHEAP_frame_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m m' W (LB0 & HP & MR & HI & REPL) MU WM FW. set (st := ps_m s) in *. exists LB0. split; [exact HP|].
  destruct HI as [BLK AR]. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof the_tb_facts as TBF0.
  split; [| split; [split; [exact BLK| exact AR]|]].
  2:{ (* [comment removed for export] *)
      eapply rw_cells_transport; [exact REPL| exact MU| exact WM|]. eapply Forall_disjoint_from; [exact FW|]. intros lo hi CW.
      unfold rclient_write_ok in CW. cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in CW |- *. unfold RMREPLACED.
      change (Z.of_nat 4) with 4.
      destruct CW as [CW|[CW|[(b & Hb & B1 & B2)|CW]]].
      - unfold RCTX in *; ceil_facts. lia.
      - unfold RMLOCK, RLIBC, RCTX, RGOT_SSP, RSSP_GUARD in *. lia.
      - assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
        destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
        unfold RCTX in *. lia.
      - unfold RCTX in *. lia. }
  eapply (rmrep_transport_unowned st m m' W MR MU WM).
  intros lo hi a Hin Ha RF.
  pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
  destruct (rrepfoot_where st m a MR RF) as [AC AW].
  pose proof the_tb_facts as TBF.
  destruct CW as [CW|[CW|[(b & Hb & B1 & B2)|CW]]]; cbn [fst snd] in *.
  - ceil_facts. lia.
  - unfold RMLOCK, RLIBC, RCTX, RGOT_SSP, RSSP_GUARD in *; ceil_facts. lia.
  - (* [comment removed for export] *)
    assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
    destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    + unfold RCTX in R1. lia.
    + unfold RMLOCK in R2. lia.
    + unfold RNEED_LOCKS in R3. lia.
    + unfold RPAGE_SIZE in R4'. lia.
    + destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
      destruct (DJ _ _ _ _ Hra Hr NEr); lia.
    + destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
      * pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
    + destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
      * rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
      * pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
    + unfold RGOT_SSP in R8. lia.
    + unfold RSSP_GUARD in R9. lia.
  - (* [comment removed for export] *) unfold RMLOCK, RLIBC, RCTX, RGOT_SSP, RSSP_GUARD in *; ceil_facts. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma u64arr_of_rw_cells' : forall m A n bs k, rw_cells ssegs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
  u64arr ssegs m A (repeat (wz 0) k).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells ssegs m A cs);
  [ apply (rw_cells_recast ssegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 ssegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Lemma bytes_at_zero_sub : forall m A N A' K,
  bytes_at ssegs m A (repeat (Z_to_bv 8 0) N) -> A <= A' -> A' + Z.of_nat K <= A + Z.of_nat N ->
  bytes_at ssegs m A' (repeat (Z_to_bv 8 0) K).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m A N A' K (B0 & B1 & BB) H1 H2. rewrite repeat_length in B1, BB. split; [lia|]. rewrite repeat_length. split; [lia|].
  intros i Hi. replace (A' + Z.of_nat i) with (A + Z.of_nat (Z.to_nat (A' - A) + i)) by lia.
  rewrite (BB (Z.to_nat (A' - A) + i)%nat ltac:(lia)).
  rewrite !nth_error_repeat by lia. reflexivity.
Qed.

Lemma wr_at_sub' : forall m a n a' n', wr_at ssegs m a n -> a <= a' -> a' + n' <= a + n -> wr_at ssegs m a' n'.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m a n a' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma rctx_zero_chunk : forall m A cs,
  bytes_at ssegs m RCTX (repeat (Z_to_bv 8 0) 928) -> wr_at ssegs m RCTX 928 ->
  RCTX <= A -> A + Z.of_nat (cells_size cs) <= RCTX + 928 ->
  cells_wf cs -> cells_bytes cs = repeat (Z_to_bv 8 0) (cells_size cs) ->
  rw_cells ssegs m A cs.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m A cs HB HW H1 H2 Hwf Hbs. split; [split; [exact Hwf|]|].
  - rewrite Hbs. eapply bytes_at_zero_sub; [exact HB| lia| cbn [Z.of_nat]; lia].
  - eapply wr_at_sub'; [exact HW| lia| lia].
Qed.

Lemma RHEAP_init_proof : RHEAP_init_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s m Hm Hbrk (ML & CB0 & CW0 & NL & PS & GOT & GUARD & MREPL).
  set (st0 := minit msecret ref_reserved).
  assert (CXH : rw_cells ssegs m 0x53da0 (ctx_head_cells st0)).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXA : rw_cells ssegs m (0x53da0 + 80) [CB 384 (u64s (repeat (wz 0) 48))]).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXU : rw_cells ssegs m (0x53da0 + 464) [CB 384 (u64s (repeat (wz 0) 48))]).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXS : rw_cells ssegs m (0x53da0 + 848) [CB 32 (zeros 32)]).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXB : rw_cells ssegs m (0x53da0 + 880) [CB 32 (zeros 32)]).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXT : rw_cells ssegs m (0x53da0 + 912) (ctx_tail_cells st0)).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  unfold RHEAP, RHEAPm. rewrite Hm, Hbrk. fold st0.
  exists []. split; [apply Permutation_refl|].
  split.
  2:{ split; [apply HINV_from_init| exact MREPL]. }
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) split; [reflexivity|]. split; [intros rid r H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? ? ? H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
    intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
  - unfold rmrep_ctx, RCTX. split; [exact CXH|]. split; [|split; [|split; [|split]]].
    + replace (actives st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXA| reflexivity| reflexivity].
    + replace (usages st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXU| reflexivity| reflexivity].
    + replace (unmap_seqs st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells ssegs m _ 32). exact CXS.
    + replace (bouncess st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells ssegs m _ 32). exact CXB.
    + exact CXT.
  - unfold rmrep_globals. split; [exact ML|]. split; [exact NL|]. split; [exact PS|]. split; [exact GOT| exact GUARD].
  - intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.F_malloc_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.Malloc_ifaceP.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rregion_addr_facts : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (0 < round_up_pg (r_len r) -> (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x56000 <= r_base r)
                                   /\ (r_base r + round_up_pg (r_len r) <= the_tb \/ the_tb + 4096 <= r_base r)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  split; [|split; [exact RBAL| split; [exact RBC| intros Hn; split; [exact (rreserved_disjoint1 _ _ RFr Hn)| exact (rreserved_tls _ _ RFr Hn)]]]].
  clear RFr. Z.div_mod_to_equations. lia.
Qed.

Lemma rblock_inside st LB m blk :
  MFACTS_g (resv:=ref_reserved) st LB -> rmrep st m -> In blk LB ->
  exists r g idx, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
    /\ (s_slots st) !! (blk_slot blk) = Some (g, idx)
    /\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
    /\ 0 <= blk_size blk
    /\ 4096 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x56000 <= r_base r)
        /\ (r_base r + round_up_pg (r_len r) <= the_tb \/ the_tb + 4096 <= r_base r)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MF MR IN.
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
  destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
  destruct BR as (r & Hr & Hk).
  pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof (rregion_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1).
  exists r, g, idx. split; [exact Hr|]. split; [exact Hk|]. split; [exact SL|].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA. ceil_facts.
  assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.

Lemma RHEAP_blocks_nodup_proof : RHEAP_blocks_nodup_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m (LB0 & HP & _ & [_ AR] & _). set (st := ps_m s) in *. pose proof (mf_nodup _ _ (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
  inversion ND; subst. constructor; [|apply IH; assumption].
  intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
  unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

Lemma RHEAP_block_range_b : forall s LB m b, RHEAP s LB m -> In b LB ->
  rblock_range (blk_addr b) (blk_size b) /\ blk_addr b = conc (ps_m s) (blk_ptr b).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m b (LB0 & HP & MR & [_ AR] & _) HIN. set (st := ps_m s) in *. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
  destruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)). rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
  pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bb & Hm & Efst & Esnd & IDX).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
  pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF).
  unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
  assert (32 <= round_up_pg (r_len r)) by nia.
  (* [comment removed for export] *)
  assert (EP : blk_addr b = conc st (blk_ptr b)).
  { destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL & INV & _ & _ & _ & CR).
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.Forall2_In_l _ _ _ _ CR IN0) as (k & HkB & (C1 & C2 & C3 & C4)).
    unfold blk_ptr. rewrite C3, C1, C4. symmetry. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.conc_aadd.
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.blk_region _ _ _ _ _ k INV HkB) as (rk & Hrk & _). exists rk. exact Hrk. }
  split; [| exact EP].
  unfold rblock_range. ceil_facts. split; [lia|]. split; [|lia].
  rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
  replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
    with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
  apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.

Lemma RHEAP_block_range_proof : RHEAP_block_range_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m p A n HR HIN. destruct (RHEAP_block_range_b s LB m (p, A, n) HR HIN) as [BR EP].
  cbn [blk_addr blk_size blk_ptr blk_slot blk_id fst snd] in BR, EP. split; [exact BR|]. destruct p; cbn in EP |- *. exact EP.
Qed.

Lemma RHEAP_blocks_disjoint_proof : RHEAP_blocks_disjoint_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m b1 b2 (LB0 & HP & MR & [_ AR] & _) I1 I2 NE. set (st := ps_m s) in *. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
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
    + destruct (rblock_inside st LB0 m b1 MF MR IN1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _).
      destruct (rblock_inside st LB0 m b2 MF MR IN2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _).
      pose proof MR as (WF & _). pose proof WF as (_ & _ & DJ & _).
      pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
      destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rrepfoot_where st m a : rmrep st m -> rrepfoot st a ->
  a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38
                        \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
                        \/ ((a < 0x10000 \/ 0x56000 <= a) /\ (a < the_tb \/ the_tb + 4096 <= a))).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
    unfold RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; ceil_facts.
  - lia. - lia. - lia. - lia.
  - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. pose proof (rreserved_tls _ _ RFa) as DT. ceil_facts.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. pose proof (rreserved_tls _ _ RFb) as DT. ceil_facts.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. pose proof (rreserved_tls _ _ RFq) as DT. ceil_facts. lia.
  - lia. - lia.
Qed.

Lemma RHEAP_frame_proof : RHEAP_frame_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s LB m m' W (LB0 & HP & MR & HI & REPL) MU WM FW. set (st := ps_m s) in *. exists LB0. split; [exact HP|].
  destruct HI as [BLK AR]. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof the_tb_facts as TBF0.
  split; [| split; [split; [exact BLK| exact AR]|]].
  2:{ (* [comment removed for export] *)
      eapply rw_cells_transport; [exact REPL| exact MU| exact WM|]. eapply Forall_disjoint_from; [exact FW|]. intros lo hi CW.
      unfold rclient_write_ok in CW. cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in CW |- *. unfold RMREPLACED.
      change (Z.of_nat 4) with 4.
      destruct CW as [CW|[CW|[(b & Hb & B1 & B2)|CW]]].
      - unfold RCTX in *; ceil_facts. lia.
      - unfold RMLOCK, RLIBC, RCTX, RGOT_SSP, RSSP_GUARD in *. lia.
      - assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
        destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
        unfold RCTX in *. lia.
      - unfold RCTX in *. lia. }
  eapply (rmrep_transport_unowned st m m' W MR MU WM).
  intros lo hi a Hin Ha RF.
  pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
  destruct (rrepfoot_where st m a MR RF) as [AC AW].
  pose proof the_tb_facts as TBF.
  destruct CW as [CW|[CW|[(b & Hb & B1 & B2)|CW]]]; cbn [fst snd] in *.
  - ceil_facts. lia.
  - unfold RMLOCK, RLIBC, RCTX, RGOT_SSP, RSSP_GUARD in *; ceil_facts. lia.
  - (* [comment removed for export] *)
    assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
    destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    + unfold RCTX in R1. lia.
    + unfold RMLOCK in R2. lia.
    + unfold RNEED_LOCKS in R3. lia.
    + unfold RPAGE_SIZE in R4'. lia.
    + destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
      destruct (DJ _ _ _ _ Hra Hr NEr); lia.
    + destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
      * pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
    + destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
      * rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
      * pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
    + unfold RGOT_SSP in R8. lia.
    + unfold RSSP_GUARD in R9. lia.
  - (* [comment removed for export] *) unfold RMLOCK, RLIBC, RCTX, RGOT_SSP, RSSP_GUARD in *; ceil_facts. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma u64arr_of_rw_cells' : forall m A n bs k, rw_cells usegs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
  u64arr usegs m A (repeat (wz 0) k).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Lemma bytes_at_zero_sub : forall m A N A' K,
  bytes_at usegs m A (repeat (Z_to_bv 8 0) N) -> A <= A' -> A' + Z.of_nat K <= A + Z.of_nat N ->
  bytes_at usegs m A' (repeat (Z_to_bv 8 0) K).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m A N A' K (B0 & B1 & BB) H1 H2. rewrite repeat_length in B1, BB. split; [lia|]. rewrite repeat_length. split; [lia|].
  intros i Hi. replace (A' + Z.of_nat i) with (A + Z.of_nat (Z.to_nat (A' - A) + i)) by lia.
  rewrite (BB (Z.to_nat (A' - A) + i)%nat ltac:(lia)).
  rewrite !nth_error_repeat by lia. reflexivity.
Qed.

Lemma wr_at_sub' : forall m a n a' n', wr_at usegs m a n -> a <= a' -> a' + n' <= a + n -> wr_at usegs m a' n'.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m a n a' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma rctx_zero_chunk : forall m A cs,
  bytes_at usegs m RCTX (repeat (Z_to_bv 8 0) 928) -> wr_at usegs m RCTX 928 ->
  RCTX <= A -> A + Z.of_nat (cells_size cs) <= RCTX + 928 ->
  cells_wf cs -> cells_bytes cs = repeat (Z_to_bv 8 0) (cells_size cs) ->
  rw_cells usegs m A cs.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m A cs HB HW H1 H2 Hwf Hbs. split; [split; [exact Hwf|]|].
  - rewrite Hbs. eapply bytes_at_zero_sub; [exact HB| lia| cbn [Z.of_nat]; lia].
  - eapply wr_at_sub'; [exact HW| lia| lia].
Qed.

Lemma RHEAP_init_proof : RHEAP_init_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros s m Hm Hbrk (ML & CB0 & CW0 & NL & PS & GOT & GUARD & MREPL).
  set (st0 := minit msecret ref_reserved).
  assert (CXH : rw_cells usegs m 0x54560 (ctx_head_cells st0)).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXA : rw_cells usegs m (0x54560 + 80) [CB 384 (u64s (repeat (wz 0) 48))]).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXU : rw_cells usegs m (0x54560 + 464) [CB 384 (u64s (repeat (wz 0) 48))]).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXS : rw_cells usegs m (0x54560 + 848) [CB 32 (zeros 32)]).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXB : rw_cells usegs m (0x54560 + 880) [CB 32 (zeros 32)]).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  assert (CXT : rw_cells usegs m (0x54560 + 912) (ctx_tail_cells st0)).
  { eapply rctx_zero_chunk; [exact CB0| exact CW0| unfold RCTX; lia| unfold RCTX; cbn; lia| cbn; repeat split; exact I| vm_compute; reflexivity]. }
  unfold RHEAP, RHEAPm. rewrite Hm, Hbrk. fold st0.
  exists []. split; [apply Permutation_refl|].
  split.
  2:{ split; [apply HINV_from_init| exact MREPL]. }
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) split; [reflexivity|]. split; [intros rid r H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? ? ? H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
    intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
  - unfold rmrep_ctx, RCTX. split; [exact CXH|]. split; [|split; [|split; [|split]]].
    + replace (actives st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXA| reflexivity| reflexivity].
    + replace (usages st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXU| reflexivity| reflexivity].
    + replace (unmap_seqs st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells usegs m _ 32). exact CXS.
    + replace (bouncess st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells usegs m _ 32). exact CXB.
    + exact CXT.
  - unfold rmrep_globals. split; [exact ML|]. split; [exact NL|]. split; [exact PS|]. split; [exact GOT| exact GUARD].
  - intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.

End PORT.

End WithCeil.
End TwB.
End RMalloc_ifaceP.

(* [comment removed for export] *)
Module RF_malloc_top.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.F_malloc_top.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_small. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RMalloc_ifaceP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rheap_pres_of_fp st st' LB lo sp m m' :
  RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
  rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
  rheap_pres LB sp m m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
  destruct Hc as [Hsp | [(Himg & Hns & HnE) | [(blk & Hin & Hblk) | [Htls Hne]]]].
  4:{ (* [comment removed for export] *)
      pose proof the_tb_facts as TBF. pose proof MR as (WFt & _). pose proof MR' as (WFt' & _).
      pose proof WFt as (_ & WRt & _). pose proof WFt' as (_ & WRt' & _).
      destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB0 & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]];
        unfold RCTX in *; ceil_facts.
      - lia.
      - exact (Hne H).
      - lia.
      - destruct (WRt' _ _ Hrx) as (_ & _ & _ & _ & RF). pose proof (lr_lo_ge rx). pose proof (round_up_pg_ge (r_len rx)).
        pose proof (rreserved_tls _ _ RF). lia.
      - destruct (WRt' _ _ Hrx) as (_ & _ & _ & _ & RF). pose proof (lr_lo_ge rx). pose proof (round_up_pg_ge (r_len rx)).
        pose proof (rreserved_tls _ _ RF). lia.
      - destruct (WRt _ _ Hr') as (_ & _ & _ & _ & RF). pose proof (lr_lo_ge r'). pose proof (round_up_pg_ge (r_len r')).
        pose proof (rreserved_tls _ _ RF). lia.
      - destruct (WRt _ _ Hr') as (_ & _ & _ & _ & RF). pose proof (lr_lo_ge r'). pose proof (round_up_pg_ge (r_len r')).
        pose proof (rreserved_tls _ _ RF). pose proof (rgroup_conc st b' gh WFt Hg') as (rb & Hrb & Cb & _). rewrite Hr' in Hrb. inversion Hrb; subst rb. lia.
      - destruct FRESH as [FC FR]. pose proof WFt as (RS & _). unfold live_ranges in FR. rewrite RS in FR.
        pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; unfold ref_reserved; cbn; right; right; right; right; left; reflexivity)). lia. }
  - destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); ceil_facts; lia.
  - pose proof the_tb_facts. destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg) as [HX|HX]; [apply Hns; unfold ralloc_static, RLIBC, RCTX, RMLOCK in *; lia| exact (HnE HX)].
  - destruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    ceil_facts.
    pose proof MR' as (WF' & _). pose proof WF' as (_ & WR' & DISJ' & _).
    pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
    destruct REL as [RREG _ _]. destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1).
    pose proof (round_up_pg_mono _ _ L1) as RL1.
    pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
    destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB1 & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
    + lia.
    + (* [comment removed for export] *) lia.
    + unfold RCTX in H. lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
      destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
      pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB1) as [_ HB].
        destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
        rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ruser_chunk st' m' (p : aptr) r n :
  rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
  16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
  exists junk, rw_cells ssegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR Hr Hk P0 PN N0.
  pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH (fst p) r Hr Hk) as [HW _].
  pose proof (rregion_addr_facts st' m' (fst p) r MR Hr) as (R4 & _ & RC & RI). ceil_facts.
  rewrite (conc_region' st' p r Hr).
  assert (W : wr_at ssegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
  destruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
  exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
  split; [exact L| exact I].
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rfinQ (m : mem) (st : mstate) (s : PState)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (n lo B : Z)
    (res : mstate * optr) (s' : PState) (msf : machine_state) : Prop :=
  exists (m' : mem) (errv' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    msf = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (oconc (fst res) (snd res))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rmrep (fst res) m' /\ mrel st (fst res) /\ brk_link_ps (fst res) s'
    /\ rpres_except (rmalloc_fp st (fst res) lo (bv_unsigned sp)) m m'
    /\ ps_m s' = ps_m s /\ ps_rest s' = ps_rest s
    /\ match snd res with
       | None => errv' = Z_to_bv 64 ENOMEM
       | Some p => rblock_range (conc (fst res) p) n /\ exists junk, rw_cells ssegs m' (conc (fst res) p) [CB (Z.to_nat n) junk]
       end.

(* [comment removed for export] *)
Lemma rmalloc_implT : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  let st := ps_m s in
  rmrep st m -> brk_link_ps st s -> RAREACH st LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] -> mem_inv ssegs m -> tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplT m (malloc st n) s
         (fun res s' msf => rfinQ m st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo B res s' msf /\ leaf_of m (malloc st n) res)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom ssegs)).
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
  intros until errv. intros st MR BL AR AUXB SB ST CLO LO ERR MI TP HA N.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| ceil_facts; lia]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  apply (rimplT_reach m (malloc st n)). unfold malloc. fold st.
  eapply rimplT_bind.
  { exact (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
             m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)). }
  intros [st2 r] s' ms'' CQ. cbn [rcoreQ] in CQ.
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    ceil_facts.
    eapply rimplT_mono.
    { exact (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                MR2 TK2 UA2 MI2 ST2 ltac:(ceil_facts; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO). }
    intros [st' p'] s'' msf [-> EP]. unfold renf_post in EP.
    destruct EP as (st'_ & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF).
    inversion ER; subst st'_ p'. clear ER.
    destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    unfold rfinQ. cbn [fst snd oconc]. exists m', errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite (rerrno_addr tp TP). pose proof the_tb_facts.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)).
             intros a Ha [X|X]; subst lo_s hi_s; lia. }
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split; [exact MR'|]. split; [exact MRELf|].
    split. { unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2. }
    split; [exact PEf|]. split; [exact PSM|]. split; [exact PSF|].
    split. { unfold rblock_range; ceil_facts. rewrite EA. pose proof the_tb_facts.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
    exists ujunk. exact UCH.
  - (* [comment removed for export] *)
    destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & EEN2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO).
    cbv beta iota. apply rimplT_ret. apply evt_done.
    unfold rfinQ. cbn [fst snd oconc]. exists m1, errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split; [exact MR2|]. split; [exact MREL|]. split; [exact BL2|]. split; [exact PE2|]. split; [exact PSM|]. split; [exact PSF| exact EEN2].
Qed.

Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| ceil_facts; lia]).
  destruct HEAP as (LB0 & HPERM & MR & [BLK AR] & REPL). rename LB into LBc. rename LB0 into LB.
  set (st := ps_m s) in *.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  (* [comment removed for export] *)
  eapply (implM_evt ssegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom ssegs))).
  { unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  (* [comment removed for export] *)
  eapply (rraw_malloc_bridge s n m (fun res s' msf => rfinQ m st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo B res s' msf
                                                     /\ leaf_of m (malloc st n) res)).
  { exact (rmalloc_implT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
             MR BL AR AUXB SB ST CLO LO ERR MI TP HA N). }
  (* [comment removed for export] *)
  intros st' p s' msf [FQ LEAF]. unfold rfinQ in FQ. cbn [fst snd] in FQ.
  destruct FQ as (m' & errv' & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI' & ST' & ERR' & AUX' & MR' & MREL & BL' & PEf & PSM & PSR & RES).
  pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MREL PEf CLO ltac:(lia)) as HPf.
  assert (REPL' : rw_cells ssegs m' RMREPLACED [C4 (Z_to_bv 64 0)]).
  { eapply rpres_except_rw_cells; [exact PEf| exact REPL|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha Hfp.
    pose proof the_tb_facts.
    destruct (rmalloc_fp_image st st' lo (bv_unsigned sp) m m' a MR MR' Hfp CLO ltac:(unfold RMREPLACED, RCTX in Ha; lia)); unfold RMREPLACED, RCTX in *; lia. }
  unfold rmalloc_post. do 15 eexists. exists m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
  split. { rewrite ps_rest_set_m. exact PSR. }
  (* [comment removed for export] *)
  destruct LEAF as (l0 & ans & l1 & FF). unfold lrun in FF.
  destruct (strel_follow _ _ _ (malloc_control pans_l pupd_l pans_l_range st n l0) ans (l1, (st', p)) FF) as ([cst c] & FC & [Hcst Hpc]).
  cbn [fst snd] in Hcst, Hpc. fold (lrun l0 (malloc st n)) in FF.
  destruct p as [pf|].
  - (* [comment removed for export] *)
    destruct RES as [BR [junk UCH]].
    destruct c as [c|]; [| destruct Hpc]. destruct Hpc as [Efst [off Eoff]].
    assert (Epf : pf = aadd c (UNIT * off)) by (destruct pf, c; unfold aadd; cbn in Efst, Eoff |- *; subst; reflexivity).
    exists c, off, (conc st' pf), junk.
    split; [exact Epf|]. split; [reflexivity|]. split; [rewrite ps_m_set_m; reflexivity|]. split; [exact BR|].
    split; [| exact UCH].
    unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
    eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact MR'|]. split; [| exact REPL']. split.
    + apply (proj1 (brk_link_ps_iff st' s')). exact BL'.
    + eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_some _ _ _ st LB n l0 l1 ans st' pf cst c off AR ltac:(lia) FF FC Epf).
  - (* [comment removed for export] *)
    destruct c as [c|]; [destruct Hpc|].
    split; [reflexivity|]. split; [exact RES|].
    unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
    exists LB. split; [exact HPERM|]. split; [exact MR'|]. split; [| exact REPL']. split.
    + apply (proj1 (brk_link_ps_iff st' s')). exact BL'.
    + eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_none _ _ _ st LB n l0 l1 ans st' AR ltac:(lia) FF).
Qed.
End TOPLEVEL.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.F_malloc_top.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_enf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_entry.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_join.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RMalloc_ifaceP.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rheap_pres_of_fp st st' LB lo sp m m' :
  RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
  rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
  rheap_pres LB sp m m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
  destruct Hc as [Hsp | [(Himg & Hns & HnE) | [(blk & Hin & Hblk) | [Htls Hne]]]].
  4:{ (* [comment removed for export] *)
      pose proof the_tb_facts as TBF. pose proof MR as (WFt & _). pose proof MR' as (WFt' & _).
      pose proof WFt as (_ & WRt & _). pose proof WFt' as (_ & WRt' & _).
      destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB0 & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]];
        unfold RCTX in *; ceil_facts.
      - lia.
      - exact (Hne H).
      - lia.
      - destruct (WRt' _ _ Hrx) as (_ & _ & _ & _ & RF). pose proof (lr_lo_ge rx). pose proof (round_up_pg_ge (r_len rx)).
        pose proof (rreserved_tls _ _ RF). lia.
      - destruct (WRt' _ _ Hrx) as (_ & _ & _ & _ & RF). pose proof (lr_lo_ge rx). pose proof (round_up_pg_ge (r_len rx)).
        pose proof (rreserved_tls _ _ RF). lia.
      - destruct (WRt _ _ Hr') as (_ & _ & _ & _ & RF). pose proof (lr_lo_ge r'). pose proof (round_up_pg_ge (r_len r')).
        pose proof (rreserved_tls _ _ RF). lia.
      - destruct (WRt _ _ Hr') as (_ & _ & _ & _ & RF). pose proof (lr_lo_ge r'). pose proof (round_up_pg_ge (r_len r')).
        pose proof (rreserved_tls _ _ RF). pose proof (rgroup_conc st b' gh WFt Hg') as (rb & Hrb & Cb & _). rewrite Hr' in Hrb. inversion Hrb; subst rb. lia.
      - destruct FRESH as [FC FR]. pose proof WFt as (RS & _). unfold live_ranges in FR. rewrite RS in FR.
        pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; unfold ref_reserved; cbn; right; right; right; right; left; reflexivity)). lia. }
  - destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); ceil_facts; lia.
  - pose proof the_tb_facts. destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg) as [HX|HX]; [apply Hns; unfold ralloc_static, RLIBC, RCTX, RMLOCK in *; lia| exact (HnE HX)].
  - destruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    ceil_facts.
    pose proof MR' as (WF' & _). pose proof WF' as (_ & WR' & DISJ' & _).
    pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
    destruct REL as [RREG _ _]. destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1).
    pose proof (round_up_pg_mono _ _ L1) as RL1.
    pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
    destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB1 & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
    + lia.
    + (* [comment removed for export] *) lia.
    + unfold RCTX in H. lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
      destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
      pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB1) as [_ HB].
        destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
        rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ruser_chunk st' m' (p : aptr) r n :
  rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
  16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
  exists junk, rw_cells usegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR Hr Hk P0 PN N0.
  pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH (fst p) r Hr Hk) as [HW _].
  pose proof (rregion_addr_facts st' m' (fst p) r MR Hr) as (R4 & _ & RC & RI). ceil_facts.
  rewrite (conc_region' st' p r Hr).
  assert (W : wr_at usegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
  destruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
  exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
  split; [exact L| exact I].
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rfinQ (m : mem) (st : mstate) (s : PState)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (n lo B : Z)
    (res : mstate * optr) (s' : PState) (msf : machine_state) : Prop :=
  exists (m' : mem) (errv' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    msf = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (oconc (fst res) (snd res))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rmrep (fst res) m' /\ mrel st (fst res) /\ brk_link_ps (fst res) s'
    /\ rpres_except (rmalloc_fp st (fst res) lo (bv_unsigned sp)) m m'
    /\ ps_m s' = ps_m s /\ ps_rest s' = ps_rest s
    /\ match snd res with
       | None => errv' = Z_to_bv 64 ENOMEM
       | Some p => rblock_range (conc (fst res) p) n /\ exists junk, rw_cells usegs m' (conc (fst res) p) [CB (Z.to_nat n) junk]
       end.

(* [comment removed for export] *)
Lemma rmalloc_implT : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  let st := ps_m s in
  rmrep st m -> brk_link_ps st s -> RAREACH st LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplT m (malloc st n) s
         (fun res s' msf => rfinQ m st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo B res s' msf /\ leaf_of m (malloc st n) res)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
  intros until errv. intros st MR BL AR AUXB SB ST CLO LO ERR MI TP HA N.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| ceil_facts; lia]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  apply (rimplT_reach m (malloc st n)). unfold malloc. fold st.
  eapply rimplT_bind.
  { exact (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
             m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)). }
  intros [st2 r] s' ms'' CQ. cbn [rcoreQ] in CQ.
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    ceil_facts.
    eapply rimplT_mono.
    { exact (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                MR2 TK2 UA2 MI2 ST2 ltac:(ceil_facts; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO). }
    intros [st' p'] s'' msf [-> EP]. unfold renf_post in EP.
    destruct EP as (st'_ & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF).
    inversion ER; subst st'_ p'. clear ER.
    destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    unfold rfinQ. cbn [fst snd oconc]. exists m', errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite (rerrno_addr tp TP). pose proof the_tb_facts.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)).
             intros a Ha [X|X]; subst lo_s hi_s; lia. }
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split; [exact MR'|]. split; [exact MRELf|].
    split. { unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2. }
    split; [exact PEf|]. split; [exact PSM|]. split; [exact PSF|].
    split. { unfold rblock_range; ceil_facts. rewrite EA. pose proof the_tb_facts.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
    exists ujunk. exact UCH.
  - (* [comment removed for export] *)
    destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & EEN2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO).
    cbv beta iota. apply rimplT_ret. apply evt_done.
    unfold rfinQ. cbn [fst snd oconc]. exists m1, errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split; [exact MR2|]. split; [exact MREL|]. split; [exact BL2|]. split; [exact PE2|]. split; [exact PSM|]. split; [exact PSF| exact EEN2].
Qed.

Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| ceil_facts; lia]).
  destruct HEAP as (LB0 & HPERM & MR & [BLK AR] & REPL). rename LB into LBc. rename LB0 into LB.
  set (st := ps_m s) in *.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  (* [comment removed for export] *)
  eapply (implM_evt usegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs))).
  { unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  (* [comment removed for export] *)
  eapply (rraw_malloc_bridge s n m (fun res s' msf => rfinQ m st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo B res s' msf
                                                     /\ leaf_of m (malloc st n) res)).
  { exact (rmalloc_implT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
             MR BL AR AUXB SB ST CLO LO ERR MI TP HA N). }
  (* [comment removed for export] *)
  intros st' p s' msf [FQ LEAF]. unfold rfinQ in FQ. cbn [fst snd] in FQ.
  destruct FQ as (m' & errv' & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI' & ST' & ERR' & AUX' & MR' & MREL & BL' & PEf & PSM & PSR & RES).
  pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MREL PEf CLO ltac:(lia)) as HPf.
  assert (REPL' : rw_cells usegs m' RMREPLACED [C4 (Z_to_bv 64 0)]).
  { eapply rpres_except_rw_cells; [exact PEf| exact REPL|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha Hfp.
    pose proof the_tb_facts.
    destruct (rmalloc_fp_image st st' lo (bv_unsigned sp) m m' a MR MR' Hfp CLO ltac:(unfold RMREPLACED, RCTX in Ha; lia)); unfold RMREPLACED, RCTX in *; lia. }
  unfold rmalloc_post. do 15 eexists. exists m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
  split. { rewrite ps_rest_set_m. exact PSR. }
  (* [comment removed for export] *)
  destruct LEAF as (l0 & ans & l1 & FF). unfold lrun in FF.
  destruct (strel_follow _ _ _ (malloc_control pans_l pupd_l pans_l_range st n l0) ans (l1, (st', p)) FF) as ([cst c] & FC & [Hcst Hpc]).
  cbn [fst snd] in Hcst, Hpc. fold (lrun l0 (malloc st n)) in FF.
  destruct p as [pf|].
  - (* [comment removed for export] *)
    destruct RES as [BR [junk UCH]].
    destruct c as [c|]; [| destruct Hpc]. destruct Hpc as [Efst [off Eoff]].
    assert (Epf : pf = aadd c (UNIT * off)) by (destruct pf, c; unfold aadd; cbn in Efst, Eoff |- *; subst; reflexivity).
    exists c, off, (conc st' pf), junk.
    split; [exact Epf|]. split; [reflexivity|]. split; [rewrite ps_m_set_m; reflexivity|]. split; [exact BR|].
    split; [| exact UCH].
    unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
    eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact MR'|]. split; [| exact REPL']. split.
    + apply (proj1 (brk_link_ps_iff st' s')). exact BL'.
    + eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_some _ _ _ st LB n l0 l1 ans st' pf cst c off AR ltac:(lia) FF FC Epf).
  - (* [comment removed for export] *)
    destruct c as [c|]; [destruct Hpc|].
    split; [reflexivity|]. split; [exact RES|].
    unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
    exists LB. split; [exact HPERM|]. split; [exact MR'|]. split; [| exact REPL']. split.
    + apply (proj1 (brk_link_ps_iff st' s')). exact BL'.
    + eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_none _ _ _ st LB n l0 l1 ans st' AR ltac:(lia) FF).
Qed.
End TOPLEVEL.

End PORT.

End WithCeil.
End TwB.
End RF_malloc_top.

(* [comment removed for export] *)
Module RF_calloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocTreeB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_callocA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RMalloc_ifaceP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocCls__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocCls__MA.MallocCls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rcalloc_pro_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (cnt sz lo : Z) : machine_state -> Prop :=
  fun ms' => exists (a2v : word) (m1 : mem) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x186a4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (sz * cnt)) (Z_to_bv 64 (sz * cnt)) (Z_to_bv 64 sz)
                  a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m1 (seg_rom ssegs)
    /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
    /\ stk ssegs m1 lo (bv_unsigned sp + -32)
    /\ rw_cells ssegs m1 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra].

Lemma rcalloc_prologue : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem) (cnt sz lo : Z),
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv ssegs m ->
  a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> cnt * sz <= RCALLOC_MAX ->
  evt ssegs (rcalloc_pro_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cnt sz lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until lo. intros ST CLO LO MI A0 A1 Hc Hs Hmax. unfold RCALLOC_MAX in Hmax.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. ceil_facts.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl ssegs m) as WM.
  subst a0 a1. unfold RCALLOC_SYM.
  st1. carve_frame 32%nat ST. st1. st1. st1.
  st1. if_cases K1; zify_cond K1.
  - st1. st1. st1. st1. finish. exact FR.
  - st1. st1. if_cases K2; zify_cond K2.
    + st1. st1. st1. st1. finish. exact FR.
    + exfalso. apply K2. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rcalloc_none_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (ret_pc ra) fc None m (seg_rom ssegs).

Lemma rcalloc_tail_none : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem) (junk : list byte) (s1v : word) lo,
  rw_cells ssegs m (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] -> stk ssegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 ->
  evt ssegs (fun ms' => rcalloc_none_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ms' /\ stk ssegs m lo (bv_unsigned sp))
      (MS (mkR (Z_to_bv 64 0x186a4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x186a4) fc None m (seg_rom ssegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until lo. intros FR ST SP32.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  st1. if_cases K; zify_cond K. 2:{ exfalso. unfold wz in K. rewrite ?unsigned_lit in K by lia. lia. }
  st1. st1. st1. st1. st1. st1.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [| exact ST]. unfold rcalloc_none_post.
  reflexivity.
Qed.

Definition rcalloc_some_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
    /\ stk ssegs m' lo (bv_unsigned sp).

Lemma rcalloc_tail_some : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
    (junk : list byte) (bjunk : list byte) (A n lo : Z),
  rw_cells ssegs m (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] -> stk ssegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 ->
  mem_inv ssegs m -> alloc_ceiling <= lo ->
  rw_cells ssegs m RMREPLACED [C4 (Z_to_bv 64 0)] ->
  rw_cells ssegs m A [CB (Z.to_nat n) bjunk] ->
  0 < A -> A + n <= alloc_ceiling -> 0 <= n < 4096 ->
  (forall (ra' sp' x0 x1 x2 s0' s1' y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
     evt ssegs (rallzerop_post ra' sp' gp tp x0 x1 x2 s0' s1' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 y7 F fc m)
         (MS (mkR ra' sp' gp tp x0 x1 x2 s0' s1' (wz A) y1 y2 y3 y4 y5 y6 y7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
             F (Z_to_bv 64 rallzerop_entry) fc None m (seg_rom ssegs))) ->
  evt ssegs (rcalloc_some_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A n lo)
      (MS (mkR (Z_to_bv 64 0x186a4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (wz n) (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x186a4) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until lo. intros FR ST SP32 MI CLO REPL BLK A0 AN HN ALLZ.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. pose proof AN as AN'. ceil_facts.
  unfold RMREPLACED, RCTX in REPL. change (0x53da0 + 928) with 0x54140 in REPL.
  st1. if_cases K; zify_cond K. { exfalso. unfold wz in K. rewrite ?unsigned_lit in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
  (* [comment removed for export] *)
  st1. st1.
  eapply evt_cut; [apply ALLZ|]. intros ms' (z1 & z2 & z3 & z4 & z5 & z6 & ->).
  replace (ret_pc (Z_to_bv 64 0x18784)) with (Z_to_bv 64 0x18784) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K3; zify_cond K3. { exfalso. unfold wz in K3. rewrite ?unsigned_lit in K3 by lia. lia. }
  st1. st1. st1. if_cases K4; zify_cond K4.
  2:{ exfalso. unfold wz in K4. rewrite ?unsigned_lit in K4 by lia. rewrite ?Z.shiftr_div_pow2 in K4 by lia. change (2 ^ 12) with 4096 in K4. rewrite ?Z.div_small in K4 by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  release_frame FR ST (bv_unsigned sp).
  eapply evt_mono.
  { eapply (memset_spec ra sp gp tp _ _ _ s0 s1 (wz A) (Z_to_bv 64 0) (wz n)); [| exact MI].
    unfold wz. rewrite !unsigned_lit by lia. exact BLK. }
  intros ms' PM. unfold memset_post in PM.
  destruct PM as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & CH).
  unfold wz in MU, CH |- *. rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in CH by lia.
  unfold rcalloc_some_post. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  change (0 mod 256) with 0 in CH. split; [exact CH|].
  eapply stk_transport; [exact ST| exact MU| exact WM|]. cbn. intros x Hx. left. destruct ST as (_ & _ & _). ceil_facts. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rcfinQ (m m1 : mem) (st : mstate) (s : PState)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (n lo B : Z)
    (res : mstate * optr) (s' : PState) (msf : machine_state) : Prop :=
  exists (mM m' : mem) (errv' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    msf = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (oconc (fst res) (snd res))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rmrep (fst res) mM /\ mrel st (fst res) /\ brk_link_ps (fst res) s'
    /\ rpres_except (rmalloc_fp st (fst res) lo (bv_unsigned sp - 32)) m1 mM
    /\ rw_cells ssegs mM RMREPLACED [C4 (Z_to_bv 64 0)]
    /\ ps_m s' = ps_m s /\ ps_rest s' = ps_rest s
    /\ match snd res with
       | None => m' = mM /\ errv' = Z_to_bv 64 ENOMEM
       | Some p => rblock_range (conc (fst res) p) n
                   /\ munch [(conc (fst res) p, conc (fst res) p + n)]%Z mM m' /\ wmono ssegs mM m'
                   /\ rw_cells ssegs m' (conc (fst res) p) [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
       end.

Lemma rcalloc_implT : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (junk : list byte) (s : PState) (LB : list block) (cnt sz lo B : Z) (errv : word),
  let st := ps_m s in
  let n := sz * cnt in
  rmrep st m1 -> brk_link_ps st s -> RAREACH st LB ->
  rauxv_ok m1 B -> bv_unsigned sp <= B ->
  stk ssegs m1 lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells ssegs m1 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] ->
  rw_cells ssegs m1 (errno_addr tp) [C4 errv] -> mem_inv ssegs m1 -> tp = Z_to_bv 64 RATP ->
  rw_cells ssegs m1 RMREPLACED [C4 (Z_to_bv 64 0)] ->
  0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= n <= RCALLOC_MAX ->
  rimplT m (sbind (malloc st n) (fun x__ => match x__ with (st1, p) =>
            match p with
            | None => ret (st1, None)
            | Some q => is_allzero st1 q (fun _ => ret (st1, Some q)) (ret (st1, Some q))
            end end)) s
         (fun res s' msf => rcfinQ m m1 st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo B res s' msf /\ leaf_of m (malloc st n) res)
         (MS (mkR (Z_to_bv 64 0x186a4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) (Z_to_bv 64 n) a1
                  a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m1 (seg_rom ssegs)).
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
  intros until errv. intros st n MR BL AR AUXB SB ST CLO LO FR ERR MI TP REPL Hc Hs Hn. unfold RCALLOC_STACK in LO. unfold RCALLOC_MAX in Hn.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0. change (bv_modulus 64) with (2^64) in SPR0.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  pose proof CLO as CLOv. ceil_facts.
  eapply rimplT_bind.
  { eapply (rmalloc_implT as_pre as_inv RAS AS_PRE RBIG (Z_to_bv 64 0x186a4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 s LB n lo B errv
              MR BL AR AUXB); [rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST| exact CLO| rewrite unsigned_lit by lia; lia| exact ERR| exact MI| exact TP| reflexivity| lia]. }
  intros [st1 r] s' msf [FQ LEAF1]. unfold rfinQ in FQ. cbn [fst snd] in FQ.
  destruct FQ as (mM & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI1 & ST1 & ERR1 & AUX1 & MR1 & MREL & BL1 & PE1 & PSM & PSR & RES).
  rewrite !unsigned_lit in ST1 by lia. rewrite !unsigned_lit in PE1 by lia. replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in PE1 by lia.
  replace (ret_pc (Z_to_bv 64 0x186a4)) with (Z_to_bv 64 0x186a4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (FR1 : rw_cells ssegs mM (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE1| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha Hfp.
    destruct (rmalloc_fp_cases st st1 lo (bv_unsigned sp - 32) m1 mM a MR MR1 Hfp); ceil_facts; lia. }
  assert (REPL1 : rw_cells ssegs mM RMREPLACED [C4 (Z_to_bv 64 0)]).
  { eapply rpres_except_rw_cells; [exact PE1| exact REPL|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha Hfp.
    pose proof the_tb_facts.
    destruct (rmalloc_fp_image st st1 lo (bv_unsigned sp - 32) m1 mM a MR MR1 Hfp CLO ltac:(unfold RMREPLACED, RCTX in Ha; lia)); unfold RMREPLACED, RCTX in *; lia. }
  destruct r as [pf|].
  - (* [comment removed for export] *)
    destruct RES as [BR [bjunk UCH]].
    (* [comment removed for export] *)
    destruct LEAF1 as (l0 & ans & l1 & FF).
    destruct (MallocTree.strel_follow _ _ _ (malloc_control pans_l pupd_l pans_l_range st n l0) ans (l1, (st1, Some pf)) FF) as ([cst c] & FC & [Hcst Hpc]).
    cbn [fst snd] in Hcst, Hpc.
    destruct c as [c|]; [| destruct Hpc]. destruct Hpc as [Efst [off Eoff]].
    assert (Epf : pf = aadd c (UNIT * off)) by (destruct pf, c; unfold aadd; cbn in Efst, Eoff |- *; subst; reflexivity).
    pose proof (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_some _ _ _ st LB n l0 l1 ans st1 pf cst c off AR ltac:(lia) FF FC Epf) as AR1.
    set (blk := ((c, off), conc st1 pf, n) : block) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR1) as C1.
    (* [comment removed for export] *)
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _ & _ & _ & CR0).
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree.ptree_follow _ _ _ _ (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree.ftree_prun pans_l pupd_l pans_l_range _ _ _ l0 (malloc_ft_cls st L BLl LS n INV ltac:(unfold MMAP_THRESHOLD; lia))) FF) as (L' & _ & CLS).
    cbn [fst snd] in CLS. destruct CLS as (c' & off' & g & idx & sc & LS' & Epf' & Hoff' & INV' & SLc & SCg & SCREL & STRc).
    pose proof (size_to_class_le26 n ltac:(lia)) as SC26.
    assert (SC27 : 0 <= sc <= 27) by (pose proof (proj1 (size_to_class_ok n ltac:(unfold MMAP_THRESHOLD; lia))); lia).
    (* [comment removed for export] *)
    pose proof (ci_ticks _ _ C1) as TK.
    pose proof (KINV_of_CINV _ _ C1) as K0.
    pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C1) blk ltac:(left; reflexivity)) as BK.
    pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C1) blk ltac:(left; reflexivity)) as BC.
    destruct BK as [(g' & i & b & SL & HB & FB & I & NFR & (off2 & O0 & OA & OS & OK & HK)) NG SZ].
    cbn [blk blk_slot blk_addr blk_size blk_id fst snd] in SL, HB, FB, I, NFR, O0, OA, OS, OK, HK, NG, SZ.
    (* [comment removed for export] *)
    assert (Ec : c' = c).
    { pose proof INV' as (_ & _ & _ & _ & _ & IS' & _).
      destruct (is_valid _ _ _ IS' c g' i SL) as (LGg & Hi & Esl).
      destruct HB as [ai0 Hgh0].
      pose proof (is_part _ _ _ IS' b g' ai0 i Hgh0 Hi) as P5. cbv zeta in P5. rewrite <- Esl in P5.
      destruct P5 as (OR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      destruct OR5 as [X|[X|[X|[X|X]]]].
      - exfalso. apply NFR. right. exact X.
      - exfalso. apply NFR. left. exact X.
      - cbn [map bslot fst] in X. destruct X as [X|X]; [exact X|]. exfalso.
        pose proof (ci_nodup _ _ C1) as ND. cbn [map blk blk_slot blk_id fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI.
        clear - X CR0. revert X. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks.CORR in CR0. induction CR0 as [|b0 k0 LB0 BL0 [E0 _] _ IH]; cbn; [tauto|]. intros [X|X]; [left; rewrite E0; exact X| right; exact (IH X)].
      - exfalso. exact (X NG).
      - exfalso. cbn in X. discriminate X. }
    subst c'.
    assert (off' = off) as -> by (rewrite Epf in Epf'; unfold aadd in Epf'; destruct c as [c1 c2]; cbn in Epf'; inversion Epf'; unfold UNIT in *; lia).
    clear Epf' Hoff'.
    rewrite SLc in SL. assert (g' = g /\ i = idx) as [-> ->] by (inversion SL; auto). clear SL.
    assert (off2 = off) as ->.
    { rewrite Epf, conc_aadd in OA; [unfold UNIT in OA; lia|]. destruct (ci_gmetas _ _ C1 b g HB) as [_ _ _ _ _ _ _ _ _ GR _ _]. destruct GR as (r0 & Hr0 & _). rewrite FB in Hr0. eauto. }
    pose proof (ci_gmetas _ _ C1 b g HB) as GO.
    destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
    pose proof MR1 as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
    destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
    destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
    cbn [blk blk_slot blk_addr blk_size fst snd] in Hr0, A16, AEND, AL, UNK, HD, BB.
    rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
    destruct HK as (hb3 & lo8 & hi & C3 & V31 & C2 & C1' & OFF). cbn [aadd fst snd] in C3, C2, C1', OFF.
    assert (Fp : fst pf = fst b) by (rewrite Epf; cbn; symmetry; exact FB).
    assert (Cp : conc st1 pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
    assert (Cc : conc st1 c = r_base r + snd c) by (apply conc_region'; rewrite <- FB; exact Hr).
    assert (Sp : snd pf = snd c + 16 * off) by (rewrite Epf; unfold UNIT; cbn; lia).
    destruct (ki_slts _ _ _ K0 _ _ _ SLc) as (GMg & Ec & _).
    assert (Sc : snd c = snd b + 16 + get_stride (get_meta_rec st1 g) * idx).
    { rewrite Ec. rewrite (slot_start'_mem _ b idx (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
    pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
    assert (SI0 : 0 <= get_stride (get_meta_rec st1 g) * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
    assert (SIL : get_stride (get_meta_rec st1 g) * (idx + 1) <= get_stride (get_meta_rec st1 g) * (m_last_idx (get_meta_rec st1 g) + 1)).
    { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
    unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
    assert (P16m : snd pf mod 16 = 0).
    { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st1 g) * idx) in *.
      assert (SIM : si mod 16 = 0) by (subst si; unfold UNIT in SM; rewrite Z.mul_mod, SM, Z.mul_0_l by lia; reflexivity).
      unfold UNIT, IB in *. clear - SIM B16 O0. Z.div_mod_to_equations. lia. }
    assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
    { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st1 g) * idx) in *. set (stq := get_stride (get_meta_rec st1 g)) in *.
      unfold UNIT, IB in *.
      assert (16 * off + 16 <= stq) by (clear - OS SZ SM O0 S16; Z.div_mod_to_equations; lia).
      rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
    assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
    { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
    destruct HB as [ai Hgh].
    (* [comment removed for export] *)
    assert (OK' : cell_read (get_shadow st1 (fst pf)) (snd pf + -4) = Known 0) by (rewrite Fp, FB; replace (snd pf + -4) with (snd c + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    assert (C3p : cell_read (get_shadow st1 (fst pf)) (snd pf + -3) = Known hb3) by (rewrite Fp, FB; replace (snd pf + -3) with (snd c + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    assert (C2p : cell_read (get_shadow st1 (fst pf)) (snd pf + -2) = Known lo8) by (rewrite Fp, FB; replace (snd pf + -2) with (snd c + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    assert (C1p : cell_read (get_shadow st1 (fst pf)) (snd pf + -2 + 1) = Known hi) by (rewrite Fp, FB; replace (snd pf + -2 + 1) with (snd c + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1').
    (* [comment removed for export] *)
    unfold is_allzero, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16; [peek_known| peek_known|]. apply rimplT_rd8; [peek_known|]. cbv zeta. apply rimplT_rd8; [peek_known|].
    rewrite (rdv_known m st1 (aadd pf (-4)) 0) by (cbn [aadd fst snd]; exact OK').
    rewrite (rdv_known m st1 (aadd pf (-3)) hb3) by (cbn [aadd fst snd]; exact C3p).
    rewrite (rdv_known m st1 (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; exact C2p).
    rewrite (rdv_known m st1 (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; exact C1p).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st1 !! area_of g) as [ar|] eqn:AR1e; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    apply rimplT_ret.
    (* [comment removed for export] *)
    pose proof (go_sc _ _ _ GO) as GSC.
    eapply evt_mono.
    { eapply (rcalloc_tail_some ra sp gp tp u0 u1 u2 s0 s1 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc mM junk bjunk (conc st1 pf) n lo);
        [exact FR1| exact ST1| lia| exact MI1| exact CLO| exact REPL1| exact UCH| | | |].
      - destruct BR as (BR0 & _). exact BR0.
      - destruct BR as (_ & _ & _ & BRC & _). exact BRC.
      - lia.
      - (* [comment removed for export] *)
        intros.
        eapply (rallzerop_spec _ _ gp tp _ _ _ _ _ (wz (conc st1 pf)) _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mM st1 pf r g (mkGhdr (Some g) ai) ar hb3 lo8 hi);
          first [exact MR1 | exact MI1 | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        + rewrite Fp. exact Hr.
        + unfold wz. rewrite Cp. apply unsigned_lit. ceil_facts. pose proof (round_up_pg_ge (r_len r)). lia.
        + exact P16m.
        + rewrite Sp, Sc. lia.
        + rewrite Sp. unfold UNIT in *. lia.
        + exact PHI.
        + replace (snd pf - 4) with (snd pf + -4) by lia. exact OK'.
        + replace (snd pf - 3) with (snd pf + -3) by lia. exact C3p.
        + replace (snd pf - 2) with (snd pf + -2) by lia. exact C2p.
        + replace (snd pf - 1) with (snd pf + -2 + 1) by lia. exact C1p.
        + exact Hgh.
        + reflexivity.
        + exact (go_slot _ _ _ GO).
        + destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
        + exact (go_mem _ _ _ GO).
        + exact AR1e.
        + exact G15.
        + exact (go_avail _ _ _ GO).
        + exact (go_freed _ _ _ GO).
        + exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        + clear - LI. lia.
        + rewrite (go_freeable _ _ _ GO). clear. lia.
        + clear - GSC. lia.
        + pose proof (go_maplen _ _ _ GO). clear - H. lia.
        + exact G12.
        + exact G13.
        + exact G14.
        + unfold MI_Inv.MR in SCg. lia.
        + assert (Hsc : (m_sizeclass (get_meta_rec st1 g) <? 48) = true) by (apply Z.ltb_lt; unfold MI_Inv.MR in SCg; lia).
          rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b]. apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        + intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st1 g)) 0) as [Eml|_]; [exfalso; exact (Hml Eml)|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st1 g) * 4096) with (m_maplen (get_meta_rec st1 g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        + (* [comment removed for export] *)
          intros Hml Hli. unfold MI_Inv.MR in SCg, STRc. rewrite SCg. specialize (STRc ltac:(lia)).
          unfold get_stride in STRc. rewrite (proj2 (Z.eqb_eq _ _) Hli) in STRc. replace (m_maplen (get_meta_rec st1 g) =? 0) with false in STRc by (symmetry; apply Z.eqb_neq; exact Hml).
          cbn [andb negb] in STRc. unfold UNIT in STRc. lia. }
    (* [comment removed for export] *)
    intros msf SPo. unfold rcalloc_some_post in SPo.
    destruct SPo as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & MUz & WMz & MI' & CHz & ST').
    split; [| exists l0, ans, l1; exact FF].
    unfold rcfinQ. cbn [fst snd oconc]. exists mM, m', errv1. do 14 eexists.
    destruct BR as (BR0 & BR16 & BRn & BRC & BRI & BRT).
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rw_cells_transport; [exact ERR1| exact MUz| exact WMz|]. cbn. rewrite (rerrno_addr tp TP). pose proof the_tb_facts. ceil_facts. lia. }
    split. { eapply (auxv_ok_frame ssegs RAUXV_CELL mM m' B); [exact AUX1| exact MUz| exact WMz|]. constructor; [| constructor]. cbn. clear - BRC BRI SB LO CLOv. unfold RAUXV_CELL in *; ceil_facts. lia. }
    split; [exact MR1|]. split; [exact MREL|]. split; [exact BL1|]. split; [exact PE1|]. split; [exact REPL1|]. split; [exact PSM|]. split; [exact PSR|].
    split; [exact (conj BR0 (conj BR16 (conj BRn (conj BRC (conj BRI BRT)))))|]. split; [exact MUz|]. split; [exact WMz| exact CHz].
  - (* [comment removed for export] *)
    cbv beta iota. apply rimplT_ret.
    eapply evt_mono.
    { eapply (rcalloc_tail_none ra sp gp tp u0 u1 u2 s0 s1 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc mM junk (Z_to_bv 64 n) lo FR1 ST1 ltac:(lia)). }
    intros msf [-> ST']. split; [| exact LEAF1].
    unfold rcfinQ. cbn [fst snd oconc]. exists mM, mM, errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST'|]. split; [exact ERR1|]. split; [exact AUX1|].
    split; [exact MR1|]. split; [exact MREL|]. split; [exact BL1|]. split; [exact PE1|]. split; [exact REPL1|]. split; [exact PSM|]. split; [exact PSR| split; [reflexivity| exact RES]].
Qed.

(* [comment removed for export] *)
Theorem rcalloc_spec_proof : rcalloc_stmt.
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA0 HA1 Hc Hs Hmax.
  pose proof LO as LO'. unfold RCALLOC_STACK in LO'. pose proof Hmax as Hmax'. unfold RCALLOC_MAX in Hmax'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0. change (bv_modulus 64) with (2^64) in SPR0.
  pose proof CLO as CLOv. ceil_facts.
  destruct HEAP as (LB0 & HPERM & MR & [BLK AR] & REPL). rename LB into LBc. rename LB0 into LB.
  set (st := ps_m s) in *.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  assert (Hn : 0 <= sz * cnt <= RCALLOC_MAX) by (unfold RCALLOC_MAX; nia).
  replace (cnt * sz) with (sz * cnt) by lia.
  (* [comment removed for export] *)
  eapply (raw_calloc_bridge ssegs s cnt sz m (fun res s' msf =>
            exists m1, munch [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m m1 /\ wmono ssegs m m1 /\ rmrep st m1 /\
              rcfinQ m m1 st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (sz * cnt) lo B res s' msf /\ leaf_of m (malloc st (sz * cnt)) res)).
  { unfold calloc. fold st.
    replace (negb (sz =? 0) && (SIZE_MAX / sz <? cnt)) with false.
    2:{ symmetry. destruct (Z.eqb_spec sz 0); cbn [negb andb]; [reflexivity|]. apply Z.ltb_ge. apply Z.div_le_lower_bound; [lia|]. unfold SIZE_MAX. nia. }
    replace (cnt * sz) with (sz * cnt) by lia.
    (* [comment removed for export] *)
    eapply rimplT_evt.
    { eapply (rcalloc_prologue ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cnt sz lo ST CLO ltac:(lia) MI HA0 HA1 Hc Hs Hmax). }
    intros ms1 (a2v & m1 & junk & -> & MUs & WM & MI1 & ST1 & FR).
    assert (MR1 : rmrep st m1).
    { eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]. intros l h [E1|[]]; inversion E1; subst; ceil_facts; lia. }
    assert (ERR1 : rw_cells ssegs m1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MUs| exact WM|]. cbn. rewrite (rerrno_addr tp TP). pose proof the_tb_facts. lia. }
    assert (REPL1 : rw_cells ssegs m1 RMREPLACED [C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact REPL| exact MUs| exact WM|]. cbn. unfold RMREPLACED, RCTX. lia. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply (auxv_ok_frame ssegs RAUXV_CELL m m1 B); [exact AUXB| exact MUs| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    eapply rimplT_mono.
    { exact (rcalloc_implT ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 sz) a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1 junk s LB cnt sz lo B errv
               MR1 BL AR AUX1 SB ST1 CLO LO FR ERR1 MI1 TP REPL1 Hc Hs Hn). }
    intros res s' msf [FQ LF]. exists m1. split; [exact MUs|]. split; [exact WM|]. split; [exact MR1|]. split; [exact FQ| exact LF]. }
  (* [comment removed for export] *)
  intros st' p s' msf (m1 & MUs & WM & MR1 & FQ & LEAF). unfold rcfinQ in FQ. cbn [fst snd] in FQ.
  destruct FQ as (mM & m' & errv' & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI' & ST' & ERR' & AUX' & MR' & MREL & BL' & PEf & REPL' & PSM & PSR & RES).
  (* [comment removed for export] *)
  assert (HP0 : rheap_pres LB (bv_unsigned sp) m m1).
  { intros x Hx Hcx. split; [| apply WM]. apply MUs. rewrite wa_unsigned by lia. cbn.
    destruct Hcx as [X|[[X _]|[(b & Hb & Xb)|[X _]]]].
    - lia.
    - lia.
    - destruct (rblock_inside st LB m b MF MR Hb) as (r & g & idx & _ & _ & _ & LOB & HIB & _ & _ & RC & _). ceil_facts. lia.
    - pose proof the_tb_facts. lia. }
  pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp - 32) m1 mM MF MR1 MR' MREL PEf CLO ltac:(lia)) as HPf.
  assert (HP1 : rheap_pres LBc (bv_unsigned sp) m mM).
  { eapply rheap_pres_trans; [| eapply (rheap_pres_weaken LB LBc (bv_unsigned sp - 32)); [exact HPf| lia| exact HIN]].
    eapply rheap_pres_weaken; [exact HP0| lia| exact HIN]. }
  unfold rcalloc_post.
  destruct LEAF as (l0 & ans & l1 & FF). unfold lrun in FF.
  destruct (MallocTree.strel_follow _ _ _ (malloc_control pans_l pupd_l pans_l_range st (sz * cnt) l0) ans (l1, (st', p)) FF) as ([cst c] & FC & [Hcst Hpc]).
  cbn [fst snd] in Hcst, Hpc. fold (lrun l0 (malloc st (sz * cnt))) in FF.
  destruct p as [pf|].
  - (* [comment removed for export] *)
    destruct RES as (BR & MUz & WMz & CHz).
    destruct c as [c|]; [| destruct Hpc]. destruct Hpc as [Efst [off Eoff]].
    assert (Epf : pf = aadd c (UNIT * off)) by (destruct pf, c; unfold aadd; cbn in Efst, Eoff |- *; subst; reflexivity).
    set (blk := ((c, off), conc st' pf, sz * cnt) : block).
    assert (HEAP1 : RHEAP (set_m st' s') (blk :: LBc) mM).
    { unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
      exists (blk :: LB). split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact MR'|]. split; [| exact REPL']. split.
      + apply (proj1 (brk_link_ps_iff st' s')). exact BL'.
      + eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_some _ _ _ st LB (sz * cnt) l0 l1 ans st' pf cst c off AR ltac:(lia) FF FC Epf). }
    destruct BR as (BR0 & BR16 & BRn & BRC & BRI & BRT).
    assert (HP2 : rheap_pres LBc (bv_unsigned sp) mM m').
    { intros x Hx Hcx. split; [| apply WMz]. apply MUz. rewrite wa_unsigned by lia. cbn.
      destruct Hcx as [X|[[X _]|[(b & Hb & Xb)|[X _]]]].
      - ceil_facts. lia.
      - lia.
      - destruct (RHEAP_blocks_disjoint_proof (set_m st' s') (blk :: LBc) mM blk b HEAP1 ltac:(left; reflexivity) ltac:(right; exact Hb)) as [D|D].
        + cbn [blk blk_id fst]. intros E.
          pose proof (RHEAP_blocks_nodup_proof (set_m st' s') (blk :: LBc) mM HEAP1) as ND. cbn [map blk blk_id fst] in ND.
          apply List.NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. rewrite E. apply in_map. exact Hb.
        + cbn [blk blk_addr blk_size fst snd] in D. lia.
        + cbn [blk blk_addr blk_size fst snd] in D. lia.
      - lia. }
    exists u0, u1, u2, (wz (conc st' pf)), v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m', errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply rheap_pres_trans; [exact HP1| exact HP2]|].
    split; [rewrite ps_rest_set_m; exact PSR|].
    exists c, off, (conc st' pf).
    split; [exact Epf|]. split; [reflexivity|]. split; [rewrite ps_m_set_m; reflexivity|].
    split; [exact (conj BR0 (conj BR16 (conj BRn (conj BRC (conj BRI BRT)))))|].
    split; [| exact CHz].
    eapply (RHEAP_frame_proof (set_m st' s') (blk :: LBc) mM m'); [exact HEAP1| exact MUz| exact WMz|].
    constructor; [| constructor]. right. right. left. exists blk. split; [left; reflexivity|]. cbn [blk blk_addr blk_size fst snd]. lia.
  - (* [comment removed for export] *)
    destruct c as [c|]; [destruct Hpc|]. destruct RES as [-> EEN].
    exists u0, u1, u2, (wz 0), v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, mM, errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [exact HP1|]. split; [rewrite ps_rest_set_m; exact PSR|].
    split; [reflexivity|]. split; [exact EEN|].
    unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
    exists LB. split; [exact HPERM|]. split; [exact MR'|]. split; [| exact REPL']. split.
    + apply (proj1 (brk_link_ps_iff st' s')). exact BL'.
    + eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_none _ _ _ st LB (sz * cnt) l0 l1 ans st' AR ltac:(lia) FF).
Qed.

End TOPLEVEL.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocTreeB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_join.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_callocA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RMalloc_ifaceP.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocCls__MA.MallocCls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rcalloc_pro_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (cnt sz lo : Z) : machine_state -> Prop :=
  fun ms' => exists (a2v : word) (m1 : mem) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x18e64) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (sz * cnt)) (Z_to_bv 64 (sz * cnt)) (Z_to_bv 64 sz)
                  a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m1 (seg_rom usegs)
    /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
    /\ stk usegs m1 lo (bv_unsigned sp + -32)
    /\ rw_cells usegs m1 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra].

Definition rcalloc_prologue__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem) (cnt sz lo : Z),
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
  a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> cnt * sz <= RCALLOC_MAX ->
  evt usegs (rcalloc_pro_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cnt sz lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cnt sz lo : ltac2:(SecDiet.SzSec.tyM 'rcalloc_prologue__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rcalloc_prologue__body : ltac2:(SecDiet.SzSec.bodyP 'rcalloc_prologue__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros ST CLO LO MI A0 A1 Hc Hs Hmax. unfold RCALLOC_MAX in Hmax.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. ceil_facts.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl usegs m) as WM.
  subst a0 a1. unfold RCALLOC_SYM.
  st1. carve_frame 32%nat ST. st1. st1. st1.
  st1. if_cases K1; zify_cond K1.
  - st1. st1. st1. st1. finish. exact FR.
  - st1. st1. if_cases K2; zify_cond K2.
    + st1. st1. st1. st1. finish. exact FR.
    + exfalso. apply K2. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. nia.
Qed.
End Sz1.
Lemma rcalloc_prologue : ltac:(let t := eval cbv delta [rcalloc_prologue__stmt] in rcalloc_prologue__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cnt sz lo. ltac2:(SecDiet.SzSec.closeP 'rcalloc_prologue__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rcalloc_none_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (ret_pc ra) fc None m (seg_rom usegs).

Definition rcalloc_tail_none__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem) (junk : list byte) (s1v : word) lo,
  rw_cells usegs m (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] -> stk usegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 ->
  evt usegs (fun ms' => rcalloc_none_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ms' /\ stk usegs m lo (bv_unsigned sp))
      (MS (mkR (Z_to_bv 64 0x18e64) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18e64) fc None m (seg_rom usegs)).
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk s1v lo : ltac2:(SecDiet.SzSec.tyM 'rcalloc_tail_none__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rcalloc_tail_none__body : ltac2:(SecDiet.SzSec.bodyP 'rcalloc_tail_none__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
 intros FR ST SP32.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  st1. if_cases K; zify_cond K. 2:{ exfalso. unfold wz in K. rewrite ?unsigned_lit in K by lia. lia. }
  st1. st1. st1. st1. st1. st1.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [| exact ST]. unfold rcalloc_none_post.
  reflexivity.
Qed.
End Sz2.
Lemma rcalloc_tail_none : ltac:(let t := eval cbv delta [rcalloc_tail_none__stmt] in rcalloc_tail_none__stmt in exact t).
Proof using MSECV TB. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk s1v lo. ltac2:(SecDiet.SzSec.closeP 'rcalloc_tail_none__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rcalloc_some_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
    /\ stk usegs m' lo (bv_unsigned sp).

Definition rcalloc_tail_some__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
    (junk : list byte) (bjunk : list byte) (A n lo : Z),
  rw_cells usegs m (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] -> stk usegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 ->
  mem_inv usegs m -> alloc_ceiling <= lo ->
  rw_cells usegs m RMREPLACED [C4 (Z_to_bv 64 0)] ->
  rw_cells usegs m A [CB (Z.to_nat n) bjunk] ->
  0 < A -> A + n <= alloc_ceiling -> 0 <= n < 4096 ->
  (forall (ra' sp' x0 x1 x2 s0' s1' y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
     evt usegs (rallzerop_post ra' sp' gp tp x0 x1 x2 s0' s1' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 y7 F fc m)
         (MS (mkR ra' sp' gp tp x0 x1 x2 s0' s1' (wz A) y1 y2 y3 y4 y5 y6 y7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
             F (Z_to_bv 64 rallzerop_entry) fc None m (seg_rom usegs))) ->
  evt usegs (rcalloc_some_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A n lo)
      (MS (mkR (Z_to_bv 64 0x18e64) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (wz n) (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18e64) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk bjunk A n lo : ltac2:(SecDiet.SzSec.tyM 'rcalloc_tail_some__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rcalloc_tail_some__body : ltac2:(SecDiet.SzSec.bodyP 'rcalloc_tail_some__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros FR ST SP32 MI CLO REPL BLK A0 AN HN ALLZ.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. pose proof AN as AN'. ceil_facts.
  unfold RMREPLACED, RCTX in REPL. change (0x54560 + 928) with 0x54900 in REPL.
  st1. if_cases K; zify_cond K. { exfalso. unfold wz in K. rewrite ?unsigned_lit in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
  (* [comment removed for export] *)
  st1. st1.
  eapply evt_cut; [apply ALLZ|]. intros ms' (z1 & z2 & z3 & z4 & z5 & z6 & ->).
  replace (ret_pc (Z_to_bv 64 0x18f44)) with (Z_to_bv 64 0x18f44) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K3; zify_cond K3. { exfalso. unfold wz in K3. rewrite ?unsigned_lit in K3 by lia. lia. }
  st1. st1. st1. if_cases K4; zify_cond K4.
  2:{ exfalso. unfold wz in K4. rewrite ?unsigned_lit in K4 by lia. rewrite ?Z.shiftr_div_pow2 in K4 by lia. change (2 ^ 12) with 4096 in K4. rewrite ?Z.div_small in K4 by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  release_frame FR ST (bv_unsigned sp).
  eapply evt_mono.
  { eapply (memset_spec ra sp gp tp _ _ _ s0 s1 (wz A) (Z_to_bv 64 0) (wz n)); [| exact MI].
    unfold wz. rewrite !unsigned_lit by lia. exact BLK. }
  intros ms' PM. unfold memset_post in PM.
  destruct PM as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & CH).
  unfold wz in MU, CH |- *. rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in CH by lia.
  unfold rcalloc_some_post. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  change (0 mod 256) with 0 in CH. split; [exact CH|].
  eapply stk_transport; [exact ST| exact MU| exact WM|]. cbn. intros x Hx. left. destruct ST as (_ & _ & _). ceil_facts. lia.
Qed.
End Sz3.
Lemma rcalloc_tail_some : ltac:(let t := eval cbv delta [rcalloc_tail_some__stmt] in rcalloc_tail_some__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk bjunk A n lo. ltac2:(SecDiet.SzSec.closeP 'rcalloc_tail_some__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rcfinQ (m m1 : mem) (st : mstate) (s : PState)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (n lo B : Z)
    (res : mstate * optr) (s' : PState) (msf : machine_state) : Prop :=
  exists (mM m' : mem) (errv' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    msf = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (oconc (fst res) (snd res))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rmrep (fst res) mM /\ mrel st (fst res) /\ brk_link_ps (fst res) s'
    /\ rpres_except (rmalloc_fp st (fst res) lo (bv_unsigned sp - 32)) m1 mM
    /\ rw_cells usegs mM RMREPLACED [C4 (Z_to_bv 64 0)]
    /\ ps_m s' = ps_m s /\ ps_rest s' = ps_rest s
    /\ match snd res with
       | None => m' = mM /\ errv' = Z_to_bv 64 ENOMEM
       | Some p => rblock_range (conc (fst res) p) n
                   /\ munch [(conc (fst res) p, conc (fst res) p + n)]%Z mM m' /\ wmono usegs mM m'
                   /\ rw_cells usegs m' (conc (fst res) p) [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
       end.

Definition rcalloc_implT__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (junk : list byte) (s : PState) (LB : list block) (cnt sz lo B : Z) (errv : word),
  let st := ps_m s in
  let n := sz * cnt in
  rmrep st m1 -> brk_link_ps st s -> RAREACH st LB ->
  rauxv_ok m1 B -> bv_unsigned sp <= B ->
  stk usegs m1 lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
  rw_cells usegs m1 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] ->
  rw_cells usegs m1 (errno_addr tp) [C4 errv] -> mem_inv usegs m1 -> tp = Z_to_bv 64 RATP ->
  rw_cells usegs m1 RMREPLACED [C4 (Z_to_bv 64 0)] ->
  0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= n <= RCALLOC_MAX ->
  rimplT m (sbind (malloc st n) (fun x__ => match x__ with (st1, p) =>
            match p with
            | None => ret (st1, None)
            | Some q => is_allzero st1 q (fun _ => ret (st1, Some q)) (ret (st1, Some q))
            end end)) s
         (fun res s' msf => rcfinQ m m1 st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo B res s' msf /\ leaf_of m (malloc st n) res)
         (MS (mkR (Z_to_bv 64 0x18e64) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) (Z_to_bv 64 n) a1
                  a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m1 (seg_rom usegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1 junk s LB cnt sz lo B errv : ltac2:(SecDiet.SzSec.tyM 'rcalloc_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rcalloc_implT__body : ltac2:(SecDiet.SzSec.bodyP 'rcalloc_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
 intros st n MR BL AR AUXB SB ST CLO LO FR ERR MI TP REPL Hc Hs Hn. unfold RCALLOC_STACK in LO. unfold RCALLOC_MAX in Hn.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0. change (bv_modulus 64) with (2^64) in SPR0.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  pose proof CLO as CLOv. ceil_facts.
  eapply rimplT_bind.
  { eapply (rmalloc_implT as_pre as_inv RAS AS_PRE RBIG (Z_to_bv 64 0x18e64) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 s LB n lo B errv
              MR BL AR AUXB); [rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST| exact CLO| rewrite unsigned_lit by lia; lia| exact ERR| exact MI| exact TP| reflexivity| lia]. }
  intros [st1 r] s' msf [FQ LEAF1]. unfold rfinQ in FQ. cbn [fst snd] in FQ.
  destruct FQ as (mM & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI1 & ST1 & ERR1 & AUX1 & MR1 & MREL & BL1 & PE1 & PSM & PSR & RES).
  rewrite !unsigned_lit in ST1 by lia. rewrite !unsigned_lit in PE1 by lia. replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in PE1 by lia.
  replace (ret_pc (Z_to_bv 64 0x18e64)) with (Z_to_bv 64 0x18e64) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (FR1 : rw_cells usegs mM (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE1| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha Hfp.
    destruct (rmalloc_fp_cases st st1 lo (bv_unsigned sp - 32) m1 mM a MR MR1 Hfp); ceil_facts; lia. }
  assert (REPL1 : rw_cells usegs mM RMREPLACED [C4 (Z_to_bv 64 0)]).
  { eapply rpres_except_rw_cells; [exact PE1| exact REPL|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha Hfp.
    pose proof the_tb_facts.
    destruct (rmalloc_fp_image st st1 lo (bv_unsigned sp - 32) m1 mM a MR MR1 Hfp CLO ltac:(unfold RMREPLACED, RCTX in Ha; lia)); unfold RMREPLACED, RCTX in *; lia. }
  destruct r as [pf|].
  - (* [comment removed for export] *)
    destruct RES as [BR [bjunk UCH]].
    (* [comment removed for export] *)
    destruct LEAF1 as (l0 & ans & l1 & FF).
    destruct (MallocTree.strel_follow _ _ _ (malloc_control pans_l pupd_l pans_l_range st n l0) ans (l1, (st1, Some pf)) FF) as ([cst c] & FC & [Hcst Hpc]).
    cbn [fst snd] in Hcst, Hpc.
    destruct c as [c|]; [| destruct Hpc]. destruct Hpc as [Efst [off Eoff]].
    assert (Epf : pf = aadd c (UNIT * off)) by (destruct pf, c; unfold aadd; cbn in Efst, Eoff |- *; subst; reflexivity).
    pose proof (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_some _ _ _ st LB n l0 l1 ans st1 pf cst c off AR ltac:(lia) FF FC Epf) as AR1.
    set (blk := ((c, off), conc st1 pf, n) : block) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR1) as C1.
    (* [comment removed for export] *)
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _ & _ & _ & CR0).
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree.ptree_follow _ _ _ _ (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree.ftree_prun pans_l pupd_l pans_l_range _ _ _ l0 (malloc_ft_cls st L BLl LS n INV ltac:(unfold MMAP_THRESHOLD; lia))) FF) as (L' & _ & CLS).
    cbn [fst snd] in CLS. destruct CLS as (c' & off' & g & idx & sc & LS' & Epf' & Hoff' & INV' & SLc & SCg & SCREL & STRc).
    pose proof (size_to_class_le26 n ltac:(lia)) as SC26.
    assert (SC27 : 0 <= sc <= 27) by (pose proof (proj1 (size_to_class_ok n ltac:(unfold MMAP_THRESHOLD; lia))); lia).
    (* [comment removed for export] *)
    pose proof (ci_ticks _ _ C1) as TK.
    pose proof (KINV_of_CINV _ _ C1) as K0.
    pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C1) blk ltac:(left; reflexivity)) as BK.
    pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C1) blk ltac:(left; reflexivity)) as BC.
    destruct BK as [(g' & i & b & SL & HB & FB & I & NFR & (off2 & O0 & OA & OS & OK & HK)) NG SZ].
    cbn [blk blk_slot blk_addr blk_size blk_id fst snd] in SL, HB, FB, I, NFR, O0, OA, OS, OK, HK, NG, SZ.
    (* [comment removed for export] *)
    assert (Ec : c' = c).
    { pose proof INV' as (_ & _ & _ & _ & _ & IS' & _).
      destruct (is_valid _ _ _ IS' c g' i SL) as (LGg & Hi & Esl).
      destruct HB as [ai0 Hgh0].
      pose proof (is_part _ _ _ IS' b g' ai0 i Hgh0 Hi) as P5. cbv zeta in P5. rewrite <- Esl in P5.
      destruct P5 as (OR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      destruct OR5 as [X|[X|[X|[X|X]]]].
      - exfalso. apply NFR. right. exact X.
      - exfalso. apply NFR. left. exact X.
      - cbn [map bslot fst] in X. destruct X as [X|X]; [exact X|]. exfalso.
        pose proof (ci_nodup _ _ C1) as ND. cbn [map blk blk_slot blk_id fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI.
        clear - X CR0. revert X. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks.CORR in CR0. induction CR0 as [|b0 k0 LB0 BL0 [E0 _] _ IH]; cbn; [tauto|]. intros [X|X]; [left; rewrite E0; exact X| right; exact (IH X)].
      - exfalso. exact (X NG).
      - exfalso. cbn in X. discriminate X. }
    subst c'.
    assert (off' = off) as -> by (rewrite Epf in Epf'; unfold aadd in Epf'; destruct c as [c1 c2]; cbn in Epf'; inversion Epf'; unfold UNIT in *; lia).
    clear Epf' Hoff'.
    rewrite SLc in SL. assert (g' = g /\ i = idx) as [-> ->] by (inversion SL; auto). clear SL.
    assert (off2 = off) as ->.
    { rewrite Epf, conc_aadd in OA; [unfold UNIT in OA; lia|]. destruct (ci_gmetas _ _ C1 b g HB) as [_ _ _ _ _ _ _ _ _ GR _ _]. destruct GR as (r0 & Hr0 & _). rewrite FB in Hr0. eauto. }
    pose proof (ci_gmetas _ _ C1 b g HB) as GO.
    destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
    pose proof MR1 as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
    destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
    destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
    cbn [blk blk_slot blk_addr blk_size fst snd] in Hr0, A16, AEND, AL, UNK, HD, BB.
    rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
    destruct HK as (hb3 & lo8 & hi & C3 & V31 & C2 & C1' & OFF). cbn [aadd fst snd] in C3, C2, C1', OFF.
    assert (Fp : fst pf = fst b) by (rewrite Epf; cbn; symmetry; exact FB).
    assert (Cp : conc st1 pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
    assert (Cc : conc st1 c = r_base r + snd c) by (apply conc_region'; rewrite <- FB; exact Hr).
    assert (Sp : snd pf = snd c + 16 * off) by (rewrite Epf; unfold UNIT; cbn; lia).
    destruct (ki_slts _ _ _ K0 _ _ _ SLc) as (GMg & Ec & _).
    assert (Sc : snd c = snd b + 16 + get_stride (get_meta_rec st1 g) * idx).
    { rewrite Ec. rewrite (slot_start'_mem _ b idx (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
    pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
    assert (SI0 : 0 <= get_stride (get_meta_rec st1 g) * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
    assert (SIL : get_stride (get_meta_rec st1 g) * (idx + 1) <= get_stride (get_meta_rec st1 g) * (m_last_idx (get_meta_rec st1 g) + 1)).
    { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
    unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
    assert (P16m : snd pf mod 16 = 0).
    { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st1 g) * idx) in *.
      assert (SIM : si mod 16 = 0) by (subst si; unfold UNIT in SM; rewrite Z.mul_mod, SM, Z.mul_0_l by lia; reflexivity).
      unfold UNIT, IB in *. clear - SIM B16 O0. Z.div_mod_to_equations. lia. }
    assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
    { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st1 g) * idx) in *. set (stq := get_stride (get_meta_rec st1 g)) in *.
      unfold UNIT, IB in *.
      assert (16 * off + 16 <= stq) by (clear - OS SZ SM O0 S16; Z.div_mod_to_equations; lia).
      rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
    assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
    { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
    destruct HB as [ai Hgh].
    (* [comment removed for export] *)
    assert (OK' : cell_read (get_shadow st1 (fst pf)) (snd pf + -4) = Known 0) by (rewrite Fp, FB; replace (snd pf + -4) with (snd c + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    assert (C3p : cell_read (get_shadow st1 (fst pf)) (snd pf + -3) = Known hb3) by (rewrite Fp, FB; replace (snd pf + -3) with (snd c + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    assert (C2p : cell_read (get_shadow st1 (fst pf)) (snd pf + -2) = Known lo8) by (rewrite Fp, FB; replace (snd pf + -2) with (snd c + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    assert (C1p : cell_read (get_shadow st1 (fst pf)) (snd pf + -2 + 1) = Known hi) by (rewrite Fp, FB; replace (snd pf + -2 + 1) with (snd c + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1').
    (* [comment removed for export] *)
    unfold is_allzero, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16; [peek_known| peek_known|]. apply rimplT_rd8; [peek_known|]. cbv zeta. apply rimplT_rd8; [peek_known|].
    rewrite (rdv_known m st1 (aadd pf (-4)) 0) by (cbn [aadd fst snd]; exact OK').
    rewrite (rdv_known m st1 (aadd pf (-3)) hb3) by (cbn [aadd fst snd]; exact C3p).
    rewrite (rdv_known m st1 (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; exact C2p).
    rewrite (rdv_known m st1 (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; exact C1p).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st1 !! area_of g) as [ar|] eqn:AR1e; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    apply rimplT_ret.
    (* [comment removed for export] *)
    pose proof (go_sc _ _ _ GO) as GSC.
    eapply evt_mono.
    { eapply (rcalloc_tail_some ra sp gp tp u0 u1 u2 s0 s1 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc mM junk bjunk (conc st1 pf) n lo);
        [exact FR1| exact ST1| lia| exact MI1| exact CLO| exact REPL1| exact UCH| | | |].
      - destruct BR as (BR0 & _). exact BR0.
      - destruct BR as (_ & _ & _ & BRC & _). exact BRC.
      - lia.
      - (* [comment removed for export] *)
        intros.
        eapply (rallzerop_spec _ _ gp tp _ _ _ _ _ (wz (conc st1 pf)) _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mM st1 pf r g (mkGhdr (Some g) ai) ar hb3 lo8 hi);
          first [exact MR1 | exact MI1 | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        + rewrite Fp. exact Hr.
        + unfold wz. rewrite Cp. apply unsigned_lit. ceil_facts. pose proof (round_up_pg_ge (r_len r)). lia.
        + exact P16m.
        + rewrite Sp, Sc. lia.
        + rewrite Sp. unfold UNIT in *. lia.
        + exact PHI.
        + replace (snd pf - 4) with (snd pf + -4) by lia. exact OK'.
        + replace (snd pf - 3) with (snd pf + -3) by lia. exact C3p.
        + replace (snd pf - 2) with (snd pf + -2) by lia. exact C2p.
        + replace (snd pf - 1) with (snd pf + -2 + 1) by lia. exact C1p.
        + exact Hgh.
        + reflexivity.
        + exact (go_slot _ _ _ GO).
        + destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
        + exact (go_mem _ _ _ GO).
        + exact AR1e.
        + exact G15.
        + exact (go_avail _ _ _ GO).
        + exact (go_freed _ _ _ GO).
        + exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        + clear - LI. lia.
        + rewrite (go_freeable _ _ _ GO). clear. lia.
        + clear - GSC. lia.
        + pose proof (go_maplen _ _ _ GO). clear - H. lia.
        + exact G12.
        + exact G13.
        + exact G14.
        + unfold MI_Inv.MR in SCg. lia.
        + assert (Hsc : (m_sizeclass (get_meta_rec st1 g) <? 48) = true) by (apply Z.ltb_lt; unfold MI_Inv.MR in SCg; lia).
          rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b]. apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        + intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st1 g)) 0) as [Eml|_]; [exfalso; exact (Hml Eml)|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st1 g) * 4096) with (m_maplen (get_meta_rec st1 g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        + (* [comment removed for export] *)
          intros Hml Hli. unfold MI_Inv.MR in SCg, STRc. rewrite SCg. specialize (STRc ltac:(lia)).
          unfold get_stride in STRc. rewrite (proj2 (Z.eqb_eq _ _) Hli) in STRc. replace (m_maplen (get_meta_rec st1 g) =? 0) with false in STRc by (symmetry; apply Z.eqb_neq; exact Hml).
          cbn [andb negb] in STRc. unfold UNIT in STRc. lia. }
    (* [comment removed for export] *)
    intros msf SPo. unfold rcalloc_some_post in SPo.
    destruct SPo as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & MUz & WMz & MI' & CHz & ST').
    split; [| exists l0, ans, l1; exact FF].
    unfold rcfinQ. cbn [fst snd oconc]. exists mM, m', errv1. do 14 eexists.
    destruct BR as (BR0 & BR16 & BRn & BRC & BRI & BRT).
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rw_cells_transport; [exact ERR1| exact MUz| exact WMz|]. cbn. rewrite (rerrno_addr tp TP). pose proof the_tb_facts. ceil_facts. lia. }
    split. { eapply (auxv_ok_frame usegs RAUXV_CELL mM m' B); [exact AUX1| exact MUz| exact WMz|]. constructor; [| constructor]. cbn. clear - BRC BRI SB LO CLOv. unfold RAUXV_CELL in *; ceil_facts. lia. }
    split; [exact MR1|]. split; [exact MREL|]. split; [exact BL1|]. split; [exact PE1|]. split; [exact REPL1|]. split; [exact PSM|]. split; [exact PSR|].
    split; [exact (conj BR0 (conj BR16 (conj BRn (conj BRC (conj BRI BRT)))))|]. split; [exact MUz|]. split; [exact WMz| exact CHz].
  - (* [comment removed for export] *)
    cbv beta iota. apply rimplT_ret.
    eapply evt_mono.
    { eapply (rcalloc_tail_none ra sp gp tp u0 u1 u2 s0 s1 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc mM junk (Z_to_bv 64 n) lo FR1 ST1 ltac:(lia)). }
    intros msf [-> ST']. split; [| exact LEAF1].
    unfold rcfinQ. cbn [fst snd oconc]. exists mM, mM, errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST'|]. split; [exact ERR1|]. split; [exact AUX1|].
    split; [exact MR1|]. split; [exact MREL|]. split; [exact BL1|]. split; [exact PE1|]. split; [exact REPL1|]. split; [exact PSM|]. split; [exact PSR| split; [reflexivity| exact RES]].
Qed.
End Sz4.
Lemma rcalloc_implT : ltac:(let t := eval cbv delta [rcalloc_implT__stmt] in rcalloc_implT__stmt in exact t).
Proof using AS_PRE RAS RBIG. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1 junk s LB cnt sz lo B errv. ltac2:(SecDiet.SzSec.closeP 'rcalloc_implT__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rcalloc_spec_proof__stmt : Prop := rcalloc_stmt.
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv : ltac2:(SecDiet.SzSec.tyM 'rcalloc_spec_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rcalloc_spec_proof__body : ltac2:(SecDiet.SzSec.bodyP 'rcalloc_spec_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA0 HA1 Hc Hs Hmax.
  pose proof LO as LO'. unfold RCALLOC_STACK in LO'. pose proof Hmax as Hmax'. unfold RCALLOC_MAX in Hmax'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0. change (bv_modulus 64) with (2^64) in SPR0.
  pose proof CLO as CLOv. ceil_facts.
  destruct HEAP as (LB0 & HPERM & MR & [BLK AR] & REPL). rename LB into LBc. rename LB0 into LB.
  set (st := ps_m s) in *.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  assert (Hn : 0 <= sz * cnt <= RCALLOC_MAX) by (unfold RCALLOC_MAX; nia).
  replace (cnt * sz) with (sz * cnt) by lia.
  (* [comment removed for export] *)
  eapply (raw_calloc_bridge usegs s cnt sz m (fun res s' msf =>
            exists m1, munch [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m m1 /\ wmono usegs m m1 /\ rmrep st m1 /\
              rcfinQ m m1 st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (sz * cnt) lo B res s' msf /\ leaf_of m (malloc st (sz * cnt)) res)).
  { unfold calloc. fold st.
    replace (negb (sz =? 0) && (SIZE_MAX / sz <? cnt)) with false.
    2:{ symmetry. destruct (Z.eqb_spec sz 0); cbn [negb andb]; [reflexivity|]. apply Z.ltb_ge. apply Z.div_le_lower_bound; [lia|]. unfold SIZE_MAX. nia. }
    replace (cnt * sz) with (sz * cnt) by lia.
    (* [comment removed for export] *)
    eapply rimplT_evt.
    { eapply (rcalloc_prologue ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cnt sz lo ST CLO ltac:(lia) MI HA0 HA1 Hc Hs Hmax). }
    intros ms1 (a2v & m1 & junk & -> & MUs & WM & MI1 & ST1 & FR).
    assert (MR1 : rmrep st m1).
    { eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]. intros l h [E1|[]]; inversion E1; subst; ceil_facts; lia. }
    assert (ERR1 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MUs| exact WM|]. cbn. rewrite (rerrno_addr tp TP). pose proof the_tb_facts. lia. }
    assert (REPL1 : rw_cells usegs m1 RMREPLACED [C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact REPL| exact MUs| exact WM|]. cbn. unfold RMREPLACED, RCTX. lia. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply (auxv_ok_frame usegs RAUXV_CELL m m1 B); [exact AUXB| exact MUs| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    eapply rimplT_mono.
    { exact (rcalloc_implT ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 sz) a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1 junk s LB cnt sz lo B errv
               MR1 BL AR AUX1 SB ST1 CLO LO FR ERR1 MI1 TP REPL1 Hc Hs Hn). }
    intros res s' msf [FQ LF]. exists m1. split; [exact MUs|]. split; [exact WM|]. split; [exact MR1|]. split; [exact FQ| exact LF]. }
  (* [comment removed for export] *)
  intros st' p s' msf (m1 & MUs & WM & MR1 & FQ & LEAF). unfold rcfinQ in FQ. cbn [fst snd] in FQ.
  destruct FQ as (mM & m' & errv' & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI' & ST' & ERR' & AUX' & MR' & MREL & BL' & PEf & REPL' & PSM & PSR & RES).
  (* [comment removed for export] *)
  assert (HP0 : rheap_pres LB (bv_unsigned sp) m m1).
  { intros x Hx Hcx. split; [| apply WM]. apply MUs. rewrite wa_unsigned by lia. cbn.
    destruct Hcx as [X|[[X _]|[(b & Hb & Xb)|[X _]]]].
    - lia.
    - lia.
    - destruct (rblock_inside st LB m b MF MR Hb) as (r & g & idx & _ & _ & _ & LOB & HIB & _ & _ & RC & _). ceil_facts. lia.
    - pose proof the_tb_facts. lia. }
  pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp - 32) m1 mM MF MR1 MR' MREL PEf CLO ltac:(lia)) as HPf.
  assert (HP1 : rheap_pres LBc (bv_unsigned sp) m mM).
  { eapply rheap_pres_trans; [| eapply (rheap_pres_weaken LB LBc (bv_unsigned sp - 32)); [exact HPf| lia| exact HIN]].
    eapply rheap_pres_weaken; [exact HP0| lia| exact HIN]. }
  unfold rcalloc_post.
  destruct LEAF as (l0 & ans & l1 & FF). unfold lrun in FF.
  destruct (MallocTree.strel_follow _ _ _ (malloc_control pans_l pupd_l pans_l_range st (sz * cnt) l0) ans (l1, (st', p)) FF) as ([cst c] & FC & [Hcst Hpc]).
  cbn [fst snd] in Hcst, Hpc. fold (lrun l0 (malloc st (sz * cnt))) in FF.
  destruct p as [pf|].
  - (* [comment removed for export] *)
    destruct RES as (BR & MUz & WMz & CHz).
    destruct c as [c|]; [| destruct Hpc]. destruct Hpc as [Efst [off Eoff]].
    assert (Epf : pf = aadd c (UNIT * off)) by (destruct pf, c; unfold aadd; cbn in Efst, Eoff |- *; subst; reflexivity).
    set (blk := ((c, off), conc st' pf, sz * cnt) : block).
    assert (HEAP1 : RHEAP (set_m st' s') (blk :: LBc) mM).
    { unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
      exists (blk :: LB). split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact MR'|]. split; [| exact REPL']. split.
      + apply (proj1 (brk_link_ps_iff st' s')). exact BL'.
      + eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_some _ _ _ st LB (sz * cnt) l0 l1 ans st' pf cst c off AR ltac:(lia) FF FC Epf). }
    destruct BR as (BR0 & BR16 & BRn & BRC & BRI & BRT).
    assert (HP2 : rheap_pres LBc (bv_unsigned sp) mM m').
    { intros x Hx Hcx. split; [| apply WMz]. apply MUz. rewrite wa_unsigned by lia. cbn.
      destruct Hcx as [X|[[X _]|[(b & Hb & Xb)|[X _]]]].
      - ceil_facts. lia.
      - lia.
      - destruct (RHEAP_blocks_disjoint_proof (set_m st' s') (blk :: LBc) mM blk b HEAP1 ltac:(left; reflexivity) ltac:(right; exact Hb)) as [D|D].
        + cbn [blk blk_id fst]. intros E.
          pose proof (RHEAP_blocks_nodup_proof (set_m st' s') (blk :: LBc) mM HEAP1) as ND. cbn [map blk blk_id fst] in ND.
          apply List.NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. rewrite E. apply in_map. exact Hb.
        + cbn [blk blk_addr blk_size fst snd] in D. lia.
        + cbn [blk blk_addr blk_size fst snd] in D. lia.
      - lia. }
    exists u0, u1, u2, (wz (conc st' pf)), v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m', errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [eapply rheap_pres_trans; [exact HP1| exact HP2]|].
    split; [rewrite ps_rest_set_m; exact PSR|].
    exists c, off, (conc st' pf).
    split; [exact Epf|]. split; [reflexivity|]. split; [rewrite ps_m_set_m; reflexivity|].
    split; [exact (conj BR0 (conj BR16 (conj BRn (conj BRC (conj BRI BRT)))))|].
    split; [| exact CHz].
    eapply (RHEAP_frame_proof (set_m st' s') (blk :: LBc) mM m'); [exact HEAP1| exact MUz| exact WMz|].
    constructor; [| constructor]. right. right. left. exists blk. split; [left; reflexivity|]. cbn [blk blk_addr blk_size fst snd]. lia.
  - (* [comment removed for export] *)
    destruct c as [c|]; [destruct Hpc|]. destruct RES as [-> EEN].
    exists u0, u1, u2, (wz 0), v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, mM, errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [exact HP1|]. split; [rewrite ps_rest_set_m; exact PSR|].
    split; [reflexivity|]. split; [exact EEN|].
    unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
    exists LB. split; [exact HPERM|]. split; [exact MR'|]. split; [| exact REPL']. split.
    + apply (proj1 (brk_link_ps_iff st' s')). exact BL'.
    + eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_none _ _ _ st LB (sz * cnt) l0 l1 ans st' AR ltac:(lia) FF).
Qed.
End Sz5.
Theorem rcalloc_spec_proof : ltac:(let t := eval cbv delta [rcalloc_spec_proof__stmt] in rcalloc_spec_proof__stmt in exact t).
Proof using AS_PRE RAS RBIG. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB cnt sz lo B errv. ltac2:(SecDiet.SzSec.closeP 'rcalloc_spec_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End TOPLEVEL.

End PORT.

End WithCeil.
End TwB.
End RF_calloc.

(* [comment removed for export] *)
Module RF_malloc_big.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_bigw. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_bigw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_malloc_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_mm_syscalls__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_small. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free_K__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_malloc_bigw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rmrep_ext : forall st st' m,
  rmrep st m ->
  s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
  s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
  s_reserved st' = s_reserved st ->
  rmrep st' m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st st' m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof using CEILV G0 MSECV. pin_using (fun (CEILV G0 MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
  rewrite G0. reflexivity.
Qed.

Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof using CEILV MSECV n rid. pin_using (fun (CEILV MSECV n rid : unit) => tt). ceil_facts. msec_facts.
  intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof using CEILV MSECV c st3. pin_using (fun (CEILV MSECV c st3 : unit) => tt). ceil_facts. msec_facts. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof using CEILV MSECV c n rid. pin_using (fun (CEILV MSECV c n rid : unit) => tt). ceil_facts. msec_facts.
  intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma rbf_regions : s_regions stF = s_regions st3. Proof using CEILV MSECV g n rid. pin_using (fun (CEILV MSECV g n rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_areas : s_areas stF = s_areas st3. Proof using CEILV MSECV g n rid. pin_using (fun (CEILV MSECV g n rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_reserved : s_reserved stF = s_reserved st3. Proof using CEILV MSECV g n rid. pin_using (fun (CEILV MSECV g n rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_next : s_next_rid stF = s_next_rid st3. Proof using CEILV MSECV g n rid. pin_using (fun (CEILV MSECV g n rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof using CEILV GN MSECV n. pin_using (fun (CEILV GN MSECV n : unit) => tt). ceil_facts. msec_facts.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite GN. reflexivity.
Qed.
Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof using CEILV MSECV c n. pin_using (fun (CEILV MSECV c n : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_shadow q : get_shadow stF q = get_shadow stM q.
Proof using CEILV MSECV c g n rid st3. pin_using (fun (CEILV MSECV c g n rid st3 : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof using CEILV MSECV g n. pin_using (fun (CEILV MSECV g n : unit) => tt). ceil_facts. msec_facts.
  intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma rbf_ctx : ctx stF = ctx stM.
Proof using CEILV HC MSECV g n rid. pin_using (fun (CEILV HC MSECV g n rid : unit) => tt). ceil_facts. msec_facts. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof using CEILV HC MSECV stM. pin_using (fun (CEILV HC MSECV stM : unit) => tt). ceil_facts. msec_facts. rewrite rbf_ctx. reflexivity. Qed.

Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof using G0 GN HC n. pin_using (fun (G0 GN HC n : unit) => tt). ceil_facts. msec_facts.
  intros MR. eapply (rmrep_ext stM stF m MR); try reflexivity.
  - exact rbf_ctx.
  - intros q. destruct (decide (q = g)) as [->|NE]; [rewrite rbf_meta, rbm_meta; reflexivity| rewrite rbf_meta_other, rbm_meta_other by exact NE; reflexivity].
  - rewrite rbf_groups, rbm_groups. reflexivity.
Qed.

Lemma rticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof using CEILV MSECV c g n rid st3. pin_using (fun (CEILV MSECV c g n rid st3 : unit) => tt). ceil_facts. msec_facts. intros H; exact H. Qed.

(* [comment removed for export] *)
Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof using MSECV NR TLSFACTS. pin_using (fun (MSECV NR TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
  replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
  cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof using CEILV MSECV n. pin_using (fun (CEILV MSECV n : unit) => tt). ceil_facts. msec_facts.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
  unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rerrno_norm : RATP + -164 = RERRNO. Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. lia. Qed.

Lemma rreserved_tlsU : forall b n, ranges_free ref_reserved b n = true -> b + n <= the_tb \/ the_tb + 4096 <= b.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros b n H. unfold ranges_free, ref_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

Lemma rrepfoot_where2 st m a : rmrep st m -> rrepfoot st a ->
  a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38
                        \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
                        \/ ((a < 0x10000 \/ 0x55000 <= a) /\ (a < the_tb \/ the_tb + 4096 <= a))).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
    unfold RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; ceil_facts.
  - lia. - lia. - lia. - lia.
  - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. pose proof (rreserved_tls _ _ RFa) as DT. ceil_facts.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. pose proof (rreserved_tls _ _ RFb) as DT. ceil_facts.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. pose proof (rreserved_tls _ _ RFq) as DT. ceil_facts. lia.
  - lia. - lia.
Qed.

(* [comment removed for export] *)
Lemma rwrapper_munch_keeps st m m' (spv lo : Z) :
  rmrep st m -> munch [(spv - 80, spv); (RERRNO, RERRNO + 4)] m m' -> wmono ssegs m m' -> alloc_ceiling <= spv - 80 ->
  rmrep st m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR MU WM HS. eapply (rmrep_transport_unowned st m m' _ MR MU WM).
  intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; unfold RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; ceil_facts; lia.
Qed.

Lemma rpres_except_of_munch_nw C W m m' :
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. unfold wview. rewrite E. auto.
Qed.

(* [comment removed for export] *)
Lemma rfp_below_ceiling K st3 stx m lo spv a :
  rmrep st3 m -> spv <= a -> alloc_ceiling <= a -> ~ (ralloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try lia.
  - unfold RCTX in *; ceil_facts. lia.
  - pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR q rq Hq) as (_ & _ & _ & RC & _). lia.
Qed.

Lemma rbig_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros Hn. rewrite rbf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

Lemma rregion_facts_hi : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  r_base r + round_up_pg (r_len r) <= 0x23000 \/ 0x55000 <= r_base r.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  destruct (rreserved_disjoint _ _ RFr) as (_ & _ & _ & D). exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop :=
  forall st LB t xa n, RAREACH st LB -> MMAP_THRESHOLD <= n < 2^32 ->
  mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
  ram_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).


Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv4.areach_ampre_proof _ _ AR)|].
  unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.

Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.

Lemma rbig_spec : rbig_stmt.
Proof using AM AMP. pin_using (fun (AM AMP : unit) => tt). ceil_facts. msec_facts.
  pose proof AMP as AMP_BIG. unfold rAMP_BIG in AMP_BIG.
  intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
  intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RAM_STACK in LO. unfold MMAP_THRESHOLD in NR.
  rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).
  (* [comment removed for export] *)
  riprefixT. ceil_facts. subst tp. rewrite RATP_unsigned in ERR1. pose proof the_tb_facts. rewrite ?rerrno_norm in *.
  unfold RMLOCK.
  step. step. step. step. step. step. step. step. step.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST1 | rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; exact ERR1 | exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
    | reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | ceil_facts; lia
    | rewrite SP'; rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; lia | rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; lia ]. }
  intros ans ms' PO.
  assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (RERRNO, RERRNO + 4)] m1 m2 -> wmono ssegs m1 m2 ->
            rw_cells ssegs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ rmrep st1 m2 /\ rauxv_ok m2 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
  { intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM| cbn; lia].
    - eapply (rwrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| exact WM| ceil_facts; lia].
      eapply munch_weaken; [|exact MU]. intros y; cbn; lia.
    - eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. unfold RAUXV_CELL.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    - eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch; [exact MU| exact WM|].
      intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. exact HX.
    - eapply unk_agree_munch; [exact UA1| exact MU| |].
      + intros rid r Hr Hk. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. ceil_facts. cbn.
        pose proof MR1 as ((_ & WRt & _) & _). destruct (WRt _ _ Hr) as (_ & _ & _ & _ & RFt). pose proof (rreserved_tlsU _ _ RFt). lia.
      + intros rid r Hr. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). ceil_facts. lia. }
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & [He HEN]).
    cbn [mmap_val]. destruct (mmap_answer_ok_err (live_ranges st1) (n + IB + UNIT) e He) as [-> ->]. cbn [negb].
    apply rimplT_ret.
    rewrite ?RATP_unsigned in MU2. rewrite SP' in ST2. rewrite ?RATP_unsigned in ERR2. pose proof the_tb_facts. rewrite ?rerrno_norm in *.
    destruct (FRAME m2 MU2 WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
    replace (ret_pc (Z_to_bv 64 0x192f4)) with (Z_to_bv 64 0x192f4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    eapply evt_cut. { eapply rbig_fail1_walk; [exact FR2| exact ST2| lia| lia]. }
    intros ms'' [-> ST3]. apply evt_done. cbn [rcoreQ].
    exists m2, (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e)). do 14 eexists. split; [reflexivity|].
    split; [exact MR2|]. split; [exact TK1|]. split; [exact MI2|]. split; [exact ST3|].
    split; [rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; exact ERR2|]. split; [rewrite HEN; reflexivity|]. split; [exact AUX2|]. split; [exact PE2|].
    split; [apply mrel_same; reflexivity|]. split; [exact BL|]. repeat split; reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & AOK).
    cbn [mmap_val].
    destruct (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
    2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    destruct (mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
    rewrite ?RATP_unsigned in MU2. rewrite SP' in ST2. rewrite ?RATP_unsigned in ERR2. pose proof the_tb_facts. rewrite ?rerrno_norm in *.
    destruct (FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
    assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by reflexivity.
    pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) st1).
    { eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
    set (L := mmap_len (n + IB + UNIT)).
    assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
    pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
    unfold F_mm_syscalls.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
    assert (ELm : mmap_len (n + IB + UNIT) = L) by reflexivity. clearbody L. ceil_facts. unfold IB, UNIT in LG.
    set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    (* [comment removed for export] *)
    assert (TLSx : forall y, the_tb <= y < the_tb + 4096 -> ~ (xa <= y < xa + L)).
    { intros y Hy. pose proof MR1 as ((RS1 & _) & _). unfold live_ranges in XRF. rewrite RS1 in XRF.
      pose proof (ranges_free_In _ _ _ _ _ XRF ltac:(apply in_or_app; left; unfold ref_reserved; cbn; do 4 right; left; reflexivity)). lia. }
    assert (TLSe0 : ~ (xa <= RERRNO < xa + L)) by (apply TLSx; lia). assert (TLSe3 : ~ (xa <= RERRNO + 3 < xa + L)) by (apply TLSx; lia).
    assert (MRz : rmrep st2 mz).
    { rewrite Est2. eapply (rmrep_new_region st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
        rewrite <- ?EL; [ceil_facts; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    fold mz in ST2 |- *.
    (* [comment removed for export] *)
    pose proof MR1 as (WF1 & _). pose proof WF1 as (RS1 & WR1 & _).
    assert (XI : xa + L <= 0x10000 \/ 0x55000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa L = true).
      { apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS1. exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv ssegs mz).
    { unfold mz. apply (mem_inv_zeros ssegs m2 xa L); try (keep_hyps CEILV n xa L CEILM__ NR X0 XC LG; lia); [exact MI2|]. intros w Hw. apply ref_ro_addr_false. lia. }
    assert (FRz : rw_cells ssegs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
    { eapply rrw_cells_agree; [exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (TKz : ticks_ok st2) by (rewrite Est2; exact TK1).
    assert (UAz : unk_agree st2 o mz).
    { eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
      rewrite Est2 in Hq. destruct (rnr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
      - right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (rnr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
        unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
      - left. split; [exact Hq1|]. split; [rewrite Est2; apply rnr_shadow|]. split; [intros off X; exact X|].
        intros off h Ho Hc NG. destruct (WR1 q r Hq1) as (B0 & _ & _ & BC & _). ceil_facts.
        pose proof (rnr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; exact XRF) q r Hq1) as D.
        pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; (keep_hyps CEILV xa r off CEILM__ Ho B0 BC TB L q D H1; lia). }
    (* [comment removed for export] *)
    riprefixT.
    replace (ret_pc (Z_to_bv 64 0x192f4)) with (Z_to_bv 64 0x192f4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (mf_ctx _ _ MF) as FC. destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
    change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
    eapply evt_cut.
    { eapply (rbig_seq_walk sp gp (Z_to_bv 64 RATP)) with (st := st2) (lo := lo);
        [exact MRz| rewrite Est2; exact FC4| rewrite unsigned_lit by lia; lia| exact FRz| exact ST2| lia| ceil_facts; lia| exact MIz]. }
    intros ms1 (wa0 & wa1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MR3).
    apply evt_done.
    (* [comment removed for export] *)
    assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono ssegs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono ssegs m2 xa L); try lia; exact Hw).
    assert (AUXz : rauxv_ok mz (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUX2| exact MUz| exact WMz|]. unfold RAUXV_CELL. constructor; [cbn; (keep_hyps CEILV TB sp lo xa L CLO LO XC XI; lia)| constructor]. }
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUXz| exact MU3| exact WM3|]. unfold RAUXV_CELL, RCTX.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
    assert (ERRz : rw_cells ssegs mz (RERRNO) [C4 errv]).
    { eapply rrw_cells_agree; [exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; (keep_hyps CEILV TB xa L a CEILM__ H0 Ha n NR LG TLSe0 TLSe3; lia). }
    assert (ERR3 : rw_cells ssegs m3 (RERRNO) [C4 errv]).
    { eapply rw_cells_transport; [exact ERRz| exact MU3| exact WM3|]. unfold RCTX. cbn. lia. }
    assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply rnr_conc; exact Hq).
    assert (BL2 : brk_link_ps (step_seq st2) s).
    { eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | exact BL].
      intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      apply Hconc2. cbn. destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
    assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); exact TKz).
    eapply AM.
    { apply (AMP_BIG st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| exact VOK| exact ISE]. }
    { exact MR3. }
    { exact TK2'. }
    { exact BL2. }
    { rewrite SP'. eapply rauxv_ok_weaken; [exact AUX3| ceil_facts; lia]. }
    { rewrite SP'. exact ST3. }
    { ceil_facts; lia. }
    { rewrite SP'. unfold RAM_STACK. lia. }
    { rewrite RATP_unsigned. pose proof the_tb_facts. rewrite ?rerrno_norm in *. exact ERR3. }
    { exact MI3. }
    { reflexivity. }
    intros st3 mo s' ms' PO3 BL3.
    destruct PO3 as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & ENO4 & AUX4 & PE4 & MR4 & TK4 & PSM & PSF & PSO & REL).
    rewrite SP' in ST4, AUX4, PE4. rewrite RATP_unsigned in ERR4. pose proof the_tb_facts. rewrite ?rerrno_norm in *.
    replace (ret_pc (Z_to_bv 64 0x193e8)) with (Z_to_bv 64 0x193e8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells ssegs m4 (bv_unsigned sp + -48) cs) end.
    { eapply rpres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. cbn in Ha. eapply (rfp_below_ceiling _ st3 _ m4); [exact MR4| lia| ceil_facts; lia]. }
    assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply rnr_lookup_new). }
    assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { destruct (amr_regions _ _ _ REL rid _ RR2) as (r' & Hr' & K' & B' & L' & G'). rewrite Hr'. f_equal. apply G'. reflexivity. }
    assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; exact PT1).
    assert (PT3 : ptrs_in (fun q => q <> rid) st3).
    { apply (amr_ptrs _ _ _ REL); [|exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
    pose proof MR4 as (WF4 & _ & (ML4 & _) & _). pose proof WF4 as (RS4 & WR4 & DJ4 & _).
    assert (RS3 : s_reserved st3 = ref_reserved) by exact RS4.
    (* [comment removed for export] *)
    assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
              (forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a) ->
              rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m4).
    { intros stF RSF HFP.
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
        do 4 right. split; [ceil_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. cbn. unfold RCTX in *.
        split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; unfold RCTX; lia| right; right; left; unfold RCTX; lia]. }
      eapply rpres_except_mono; [exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
      do 4 right. eapply (fresh_addr_anti st (step_seq st2)); [| |exact X].
      { transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
      intros q rq Hq. exists rq. split; [|repeat split; auto; lia].
      transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      rewrite Est2, rnr_lookup_old; [exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
    destruct mo as [g|].
    + (* [comment removed for export] *)
      apply rimplT_ret.
      destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
      pose proof (rmeta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)).
      set (G := conc st3 g) in *.
      assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; ceil_facts; lia).
      assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
      { intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
        destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
      { intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
        destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (SHN3 : (s_shadow st3) !! rid = None).
      { rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. exact FRs. }
      assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
      { rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. reflexivity. }
      eapply evt_cut.
      { eapply (rbig_succ_walk st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:(ceil_facts; lia) sp gp (Z_to_bv 64 RATP));
          [exact HG| exact FR4| exact ST4| lia| exact MI4]. }
      intros ms5 (a0' & a1' & m7 & -> & MU7 & WM7 & MI7 & ST7 & FR7 & MR7 & TK7).
      apply evt_done. cbn [rcoreQ].
      set (stF := big_final st3 g rid n).
      rewrite (rbf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
      change (pw st3 (Some g)) with (pw stF (Some g)).
      exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. do 17 eexists.
      split; [reflexivity|].
      assert (MRF : rmrep stF m7) by (apply (rmrep_big_final st3 g rid n _ G0 (GN3 0) HC3); exact MR7).
      split; [exact MRF|].
      split; [exact TK7|].
      assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite rbig_stride by lia; rewrite <- EL; reflexivity).
      assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
      { intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
      split.
      { (* [comment removed for export] *)
        assert (UA3 : unk_agree (step_seq st2) o m3).
        { eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
          assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; exact Hq).
          split; [exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          intros off h Ho Hc NG. pose proof MRz as (WFz & _). pose proof WFz as (_ & WRz & _).
          destruct (WRz q r Hq2) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). ceil_facts.
          apply MU3. rewrite wa_unsigned by lia. cbn. unfold RCTX. (keep_hyps CEILV TB xa L st3 g r off Ho D; lia). }
        assert (UA4 : unk_agree st3 o m4).
        { eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
          assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
          { destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
            - destruct (amr_regions _ _ _ REL q r2 E) as (r' & Hr' & K' & _ & _ & G'). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. exact Hk.
            - exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
          split; [exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; exact (amr_groups _ _ _ REL)|].
          intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). ceil_facts.
          refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
          intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
          - lia.
          - pose proof (rreserved_tls _ _ RFq) as DT. pose proof (lr_lo_ge r). pose proof (round_up_pg_ge (r_len r)). specialize (DT ltac:(lia)). (keep_hyps CEILV TB xa L st3 g r off Ho X DT; lia).
          - unfold RCTX in X. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). (keep_hyps CEILV TB xa L st3 g r off Ho X D; lia).
          - assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; exact Hk).
            pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
          - pose proof (fresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). (keep_hyps CEILV TB xa L st3 g r off Ho Y H2; lia). }
        eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
        destruct (N.eq_dec q rid) as [->|NE].
        - right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
          change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
          rewrite cell_read_hh0 in Hc by (exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
          exists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
        - left. split; [exact Hq|]. split; [apply rbf_shadow_other; exact NE|].
          split. { intros off (b & gh & Hb & Hf & Ho). exists b, gh. split; [|auto]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)).
                   rewrite lookup_insert_ne; [exact Hb|]. intros <-. cbn in Hf. congruence. }
          intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). ceil_facts.
          pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
          apply MU7; rewrite wa_unsigned by (keep_hyps CEILV xa st3 g r off CEILM__ Ho B0 BC; lia); cbn; unfold RCTX; (keep_hyps CEILV TB n xa L st3 g q r off NR LG Ho D H2 H3 H4; lia). }
      split; [exact MI7|]. split; [exact ST7|]. split; [exact FR7|].
      assert (ERR8 : rw_cells ssegs m7 (RERRNO) [C4 errv4]).
      { eapply rw_cells_transport; [exact ERR4| exact MU7| exact WM7|]. cbn. unfold RCTX.
        assert (TBI8 : 0x339d0 <= the_tb /\ the_tb + 4096 <= 0x53aa0) by (pose proof the_tb_facts as TBX8; destruct TBX8 as (TBX8a & TBX8b & TBX8c & [TBX8d|TBX8d]); lia).
        (keep_hyps CEILV TB n xa L st3 g XA H1 GI2 TBI8 XI LG NR; lia). }
      split; [rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; exact ERR8|].
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [exact Hq| split; [exact Kq| exact Xa]]. }
      assert (PE18 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m7).
      { eapply rpres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_trans.
        { eapply rpres_except_of_munch; [exact MU7| exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
          - left. right; right; right. exists ridg, rg. split; [exact Hrg|]. split; [exact Krg|]. lia.
          - do 4 right. split; [ceil_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia].
          - left. right; right; left. unfold RCTX in *. lia. }
        apply rpres_except_refl. }
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [exact MR0| exact MRF| exact AUX1| exact PE18| ceil_facts; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
          exists r'. split; [|repeat split; auto]. exact Hr'.
        - change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE18]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      rewrite (rbf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
      split. { intros a Ha. do 4 right. split; [ceil_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      split. { unfold u32. Z.div_mod_to_equations. lia. }
      assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by (keep_hyps CEILV n xa st3 g NR; lia); Z.div_mod_to_equations; (keep_hyps CEILV TB n xa L st3 g q r NR H2 H3; lia)).
      pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
      assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; (keep_hyps CEILV TB n xa L st3 g q r H2 H3; lia)).
      rewrite <- big_ml_eq in RU by lia.
      split.
      { (* [comment removed for export] *) constructor; rewrite ?(rbf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
        - reflexivity.
        - exact RR3.
        - reflexivity.
        - lia.
        - reflexivity.
        - lia.
        - lia.
        - rewrite <- EL. lia.
        - lia.
        - rewrite RU. Z.div_mod_to_equations. lia.
        - lia.
        - lia.
        - lia.
        - intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (rbf_groups st3 g rid n (GN3 0)) in Hb'.
          destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
          rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
        - change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
          rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        - intros off Ho Hfit. Z.div_mod_to_equations. lia.
        - unfold stF. rewrite rbf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
        - exact MSL.
        - lia.
        - lia.
        - lia.
        - lia.
        - right. repeat split; lia. }
      split. { intros _. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
               cbn [fst snd]. rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      split; [exact MRELF|].
      split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| exact BL3]. }
      repeat split; assumption.
    + (* [comment removed for export] *)
      cbn [pw oconc].
      riprefixT.
      eapply evt_cut.
      { apply rbig_fail2a_walk. exact ML4. }
      intros ms2 ->. apply evt_done.
      eapply rimplT_munmap.
      { eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
          [ rewrite unsigned_lit by (keep_hyps CEILV sp lo xa CEILF__ CLO LO SPR; lia); exact ST4 | rewrite unsigned_lit by (keep_hyps CEILV TB xa L TLSFACTS CEILM__; lia); rewrite ?rerrno_norm; exact ERR4 | exact MI4 | reflexivity | unfold IB, UNIT; f_equal; (keep_hyps CEILV n xa; lia)
          | (keep_hyps CEILV xa X0; lia) | rewrite ELm; (keep_hyps CEILV xa L CEILM__ XC; lia) | unfold IB, UNIT; (keep_hyps CEILV n xa NR; lia) | rewrite unsigned_lit by (keep_hyps CEILV sp lo xa CEILF__ CLO LO SPR; lia); (keep_hyps CEILV sp lo xa LO; lia)
          | rewrite unsigned_lit by (keep_hyps CEILV TB xa L TLSFACTS CEILM__; lia); rewrite unsigned_lit by (keep_hyps CEILV sp lo xa CEILF__ CLO LO SPR; lia); (keep_hyps CEILV TB sp lo xa L TLSFACTS CLO LO; lia) | rewrite ELm; left; ceil_facts; (keep_hyps CEILV lo xa L CLO XC; lia)
          | rewrite ELm, unsigned_lit by (keep_hyps CEILV TB xa L TLSFACTS CEILM__; lia); (keep_hyps CEILV TB n xa L NR LG TLSe0 TLSe3; lia) | rewrite unsigned_lit by (keep_hyps CEILV TB xa L TLSFACTS CEILM__; lia); (keep_hyps CEILV TB xa L TLSFACTS; lia) ]. }
      intros ans2 ms3 PM. unfold rmunmap_post in PM.
      destruct PM as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He6).
      rewrite (munmap_answer_ok_range ans2 (rg_err_range _ ans2 He6)). apply rimplT_ret.
      rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by (keep_hyps CEILV TB xa L TLSFACTS CEILM__; lia).
      replace (ret_pc (Z_to_bv 64 0x194c0)) with (Z_to_bv 64 0x194c0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells ssegs m6 (bv_unsigned sp + -48) cs) end.
      { eapply rrw_cells_agree; [exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. ceil_facts. (keep_hyps CEILV TB sp lo xa L a CLO LO XC H1 Ha; lia). }
      eapply evt_cut. { eapply rbig_fail2b_walk; [exact FR6| exact ST6| lia| lia]. }
      intros ms4 [-> ST7]. apply evt_done. cbn [rcoreQ].
      set (stF := drop_region rid st3).
      assert (MRF : rmrep stF m6).
      { eapply (rmrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
        rewrite <- EL in Hout.
        assert (A1 : a < alloc_ceiling /\ (a + 1 <= RERRNO \/ RERRNO + 4 <= a) /\ (a < xa \/ xa + L <= a)).
        { destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
            [unfold RMLOCK in *; ceil_facts; (keep_hyps CEILV TB xa L a CEILF__ H1 Hout X; lia)| unfold RLIBC in *; ceil_facts; (keep_hyps CEILV TB xa L a CEILF__ H1 Hout X; lia)| unfold RGOT_SSP in *; ceil_facts; (keep_hyps CEILV TB xa L a CEILF__ H1 Hout X; lia)| unfold RSSP_GUARD in *; ceil_facts; (keep_hyps CEILV TB xa L a CEILF__ H1 Hout X; lia)|].
          destruct (WR4 q rq Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). pose proof (lr_lo_ge rq).
          pose proof (rreserved_tlsU _ _ RFq). pose proof (round_up_pg_ge (r_len rq)).
          split; [lia|]. split; [(keep_hyps CEILV TB xa L a rq Xa H2 H3; lia)|].
          destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
          destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
        ceil_facts.
        apply MU6; rewrite wa_unsigned by (keep_hyps CEILV xa a Ha; lia); cbn; (keep_hyps CEILV TB sp lo xa L a CLO LO A1; lia). }
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [|split; [exact Kq|exact Xa]].
        unfold stF. rewrite rdr_lookup_old; [exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
      assert (PE16 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m6).
      { eapply rpres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_of_munch_nw; [exact MU6|]. intros a Ha NC. cbn.
        split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; lia|].
        do 4 right. split; [ceil_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      exists m6, (F_mm_syscalls.rg_errno ans2 errv4). do 14 eexists. split; [reflexivity|].
      split; [exact MRF|]. split; [apply rticks_ok_drop_region; exact TK4|]. split; [exact MI6|]. split; [exact ST7|].
      split; [rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; exact ERR6|].
      split; [destruct ans2 as [e6|d6]; cbn [F_mm_syscalls.rg_errno]; [cbn in He6; rewrite (proj2 He6); reflexivity| exact (ENO4 eq_refl)]|].
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [exact MR0| exact MRF| exact AUX1| exact PE16| ceil_facts; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
          exists r'. split; [|repeat split; auto]. unfold stF. rewrite rdr_lookup_old by exact NE. exact Hr'.
        - unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
          change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE16]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      split; [exact MRELF|].
      split.
      { eapply (brk_link_ps_ext st3); [reflexivity| | exact BL3]. intros rb ob Hb. unfold stF. apply rdr_conc. cbn.
        destruct PT3 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
      repeat split; assumption.
Qed.
End BIG.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_bigw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_malloc_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_enf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_entry.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_join.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_malloc_bigw.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rmrep_ext : forall st st' m,
  rmrep st m ->
  s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
  s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
  s_reserved st' = s_reserved st ->
  rmrep st' m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st st' m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof using CEILV G0 MSECV. pin_using (fun (CEILV G0 MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
  rewrite G0. reflexivity.
Qed.

Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof using CEILV MSECV n rid. pin_using (fun (CEILV MSECV n rid : unit) => tt). ceil_facts. msec_facts.
  intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof using CEILV MSECV c st3. pin_using (fun (CEILV MSECV c st3 : unit) => tt). ceil_facts. msec_facts. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof using CEILV MSECV c n rid. pin_using (fun (CEILV MSECV c n rid : unit) => tt). ceil_facts. msec_facts.
  intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma rbf_regions : s_regions stF = s_regions st3. Proof using CEILV MSECV g n rid. pin_using (fun (CEILV MSECV g n rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_areas : s_areas stF = s_areas st3. Proof using CEILV MSECV g n rid. pin_using (fun (CEILV MSECV g n rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_reserved : s_reserved stF = s_reserved st3. Proof using CEILV MSECV g n rid. pin_using (fun (CEILV MSECV g n rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_next : s_next_rid stF = s_next_rid st3. Proof using CEILV MSECV g n rid. pin_using (fun (CEILV MSECV g n rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof using CEILV GN MSECV n. pin_using (fun (CEILV GN MSECV n : unit) => tt). ceil_facts. msec_facts.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite GN. reflexivity.
Qed.
Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof using CEILV MSECV c n. pin_using (fun (CEILV MSECV c n : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_shadow q : get_shadow stF q = get_shadow stM q.
Proof using CEILV MSECV c g n rid st3. pin_using (fun (CEILV MSECV c g n rid st3 : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof using CEILV MSECV g n. pin_using (fun (CEILV MSECV g n : unit) => tt). ceil_facts. msec_facts.
  intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma rbf_ctx : ctx stF = ctx stM.
Proof using CEILV HC MSECV g n rid. pin_using (fun (CEILV HC MSECV g n rid : unit) => tt). ceil_facts. msec_facts. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof using CEILV HC MSECV stM. pin_using (fun (CEILV HC MSECV stM : unit) => tt). ceil_facts. msec_facts. rewrite rbf_ctx. reflexivity. Qed.

Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof using G0 GN HC n. pin_using (fun (G0 GN HC n : unit) => tt). ceil_facts. msec_facts.
  intros MR. eapply (rmrep_ext stM stF m MR); try reflexivity.
  - exact rbf_ctx.
  - intros q. destruct (decide (q = g)) as [->|NE]; [rewrite rbf_meta, rbm_meta; reflexivity| rewrite rbf_meta_other, rbm_meta_other by exact NE; reflexivity].
  - rewrite rbf_groups, rbm_groups. reflexivity.
Qed.

Lemma rticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof using CEILV MSECV c g n rid st3. pin_using (fun (CEILV MSECV c g n rid st3 : unit) => tt). ceil_facts. msec_facts. intros H; exact H. Qed.

(* [comment removed for export] *)
Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof using MSECV NR TLSFACTS. pin_using (fun (MSECV NR TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
  replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
  cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof using CEILV MSECV n. pin_using (fun (CEILV MSECV n : unit) => tt). ceil_facts. msec_facts.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
  unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rerrno_norm : RATP + -164 = RERRNO. Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts. lia. Qed.

Lemma rreserved_tlsU : forall b n, ranges_free ref_reserved b n = true -> b + n <= the_tb \/ the_tb + 4096 <= b.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros b n H. unfold ranges_free, ref_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

Lemma rrepfoot_where2 st m a : rmrep st m -> rrepfoot st a ->
  a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38
                        \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
                        \/ ((a < 0x10000 \/ 0x56000 <= a) /\ (a < the_tb \/ the_tb + 4096 <= a))).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
    unfold RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; ceil_facts.
  - lia. - lia. - lia. - lia.
  - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. pose proof (rreserved_tls _ _ RFa) as DT. ceil_facts.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. pose proof (rreserved_tls _ _ RFb) as DT. ceil_facts.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. pose proof (rreserved_tls _ _ RFq) as DT. ceil_facts. lia.
  - lia. - lia.
Qed.

(* [comment removed for export] *)
Lemma rwrapper_munch_keeps st m m' (spv lo : Z) :
  rmrep st m -> munch [(spv - 80, spv); (RERRNO, RERRNO + 4)] m m' -> wmono usegs m m' -> alloc_ceiling <= spv - 80 ->
  rmrep st m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR MU WM HS. eapply (rmrep_transport_unowned st m m' _ MR MU WM).
  intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; unfold RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; ceil_facts; lia.
Qed.

Lemma rpres_except_of_munch_nw C W m m' :
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. unfold wview. rewrite E. auto.
Qed.

(* [comment removed for export] *)
Lemma rfp_below_ceiling K st3 stx m lo spv a :
  rmrep st3 m -> spv <= a -> alloc_ceiling <= a -> ~ (ralloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try lia.
  - unfold RCTX in *; ceil_facts. lia.
  - pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR q rq Hq) as (_ & _ & _ & RC & _). lia.
Qed.

Lemma rbig_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros Hn. rewrite rbf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

Lemma rregion_facts_hi : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  r_base r + round_up_pg (r_len r) <= 0x23000 \/ 0x56000 <= r_base r.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  destruct (rreserved_disjoint _ _ RFr) as (_ & _ & _ & D). exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop :=
  forall st LB t xa n, RAREACH st LB -> MMAP_THRESHOLD <= n < 2^32 ->
  mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
  ram_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).


Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv4.areach_ampre_proof _ _ AR)|].
  unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.

Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.

Lemma rbig_spec : rbig_stmt.
Proof using AM AMP. pin_using (fun (AM AMP : unit) => tt). ceil_facts. msec_facts.
  pose proof AMP as AMP_BIG. unfold rAMP_BIG in AMP_BIG.
  intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
  intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RAM_STACK in LO. unfold MMAP_THRESHOLD in NR.
  rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).
  (* [comment removed for export] *)
  riprefixT. ceil_facts. subst tp. rewrite RATP_unsigned in ERR1. pose proof the_tb_facts. rewrite ?rerrno_norm in *.
  unfold RMLOCK.
  step. step. step. step. step. step. step. step. step.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST1 | rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; exact ERR1 | exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
    | reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | ceil_facts; lia
    | rewrite SP'; rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; lia | rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; lia ]. }
  intros ans ms' PO.
  assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (RERRNO, RERRNO + 4)] m1 m2 -> wmono usegs m1 m2 ->
            rw_cells usegs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ rmrep st1 m2 /\ rauxv_ok m2 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
  { intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM| cbn; lia].
    - eapply (rwrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| exact WM| ceil_facts; lia].
      eapply munch_weaken; [|exact MU]. intros y; cbn; lia.
    - eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. unfold RAUXV_CELL.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    - eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch; [exact MU| exact WM|].
      intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. exact HX.
    - eapply unk_agree_munch; [exact UA1| exact MU| |].
      + intros rid r Hr Hk. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. ceil_facts. cbn.
        pose proof MR1 as ((_ & WRt & _) & _). destruct (WRt _ _ Hr) as (_ & _ & _ & _ & RFt). pose proof (rreserved_tlsU _ _ RFt). lia.
      + intros rid r Hr. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). ceil_facts. lia. }
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & [He HEN]).
    cbn [mmap_val]. destruct (mmap_answer_ok_err (live_ranges st1) (n + IB + UNIT) e He) as [-> ->]. cbn [negb].
    apply rimplT_ret.
    rewrite ?RATP_unsigned in MU2. rewrite SP' in ST2. rewrite ?RATP_unsigned in ERR2. pose proof the_tb_facts. rewrite ?rerrno_norm in *.
    destruct (FRAME m2 MU2 WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
    replace (ret_pc (Z_to_bv 64 0x19ab4)) with (Z_to_bv 64 0x19ab4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    eapply evt_cut. { eapply rbig_fail1_walk; [exact FR2| exact ST2| lia| lia]. }
    intros ms'' [-> ST3]. apply evt_done. cbn [rcoreQ].
    exists m2, (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e)). do 14 eexists. split; [reflexivity|].
    split; [exact MR2|]. split; [exact TK1|]. split; [exact MI2|]. split; [exact ST3|].
    split; [rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; exact ERR2|]. split; [rewrite HEN; reflexivity|]. split; [exact AUX2|]. split; [exact PE2|].
    split; [apply mrel_same; reflexivity|]. split; [exact BL|]. repeat split; reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & AOK).
    cbn [mmap_val].
    destruct (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
    2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    destruct (mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
    rewrite ?RATP_unsigned in MU2. rewrite SP' in ST2. rewrite ?RATP_unsigned in ERR2. pose proof the_tb_facts. rewrite ?rerrno_norm in *.
    destruct (FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
    assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by reflexivity.
    pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) st1).
    { eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
    set (L := mmap_len (n + IB + UNIT)).
    assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
    pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
    unfold F_mm_syscalls.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
    assert (ELm : mmap_len (n + IB + UNIT) = L) by reflexivity. clearbody L. ceil_facts. unfold IB, UNIT in LG.
    set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    (* [comment removed for export] *)
    assert (TLSx : forall y, the_tb <= y < the_tb + 4096 -> ~ (xa <= y < xa + L)).
    { intros y Hy. pose proof MR1 as ((RS1 & _) & _). unfold live_ranges in XRF. rewrite RS1 in XRF.
      pose proof (ranges_free_In _ _ _ _ _ XRF ltac:(apply in_or_app; left; unfold ref_reserved; cbn; do 4 right; left; reflexivity)). lia. }
    assert (TLSe0 : ~ (xa <= RERRNO < xa + L)) by (apply TLSx; lia). assert (TLSe3 : ~ (xa <= RERRNO + 3 < xa + L)) by (apply TLSx; lia).
    assert (MRz : rmrep st2 mz).
    { rewrite Est2. eapply (rmrep_new_region st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
        rewrite <- ?EL; [ceil_facts; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    fold mz in ST2 |- *.
    (* [comment removed for export] *)
    pose proof MR1 as (WF1 & _). pose proof WF1 as (RS1 & WR1 & _).
    assert (XI : xa + L <= 0x10000 \/ 0x56000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa L = true).
      { apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS1. exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv usegs mz).
    { unfold mz. apply (mem_inv_zeros usegs m2 xa L); try lia; [exact MI2|]. intros w Hw. apply ref_ro_addr_false. lia. }
    assert (FRz : rw_cells usegs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
    { eapply rrw_cells_agree; [exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (TKz : ticks_ok st2) by (rewrite Est2; exact TK1).
    assert (UAz : unk_agree st2 o mz).
    { eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
      rewrite Est2 in Hq. destruct (rnr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
      - right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (rnr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
        unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
      - left. split; [exact Hq1|]. split; [rewrite Est2; apply rnr_shadow|]. split; [intros off X; exact X|].
        intros off h Ho Hc NG. destruct (WR1 q r Hq1) as (B0 & _ & _ & BC & _). ceil_facts.
        pose proof (rnr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; exact XRF) q r Hq1) as D.
        pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; (keep_hyps CEILV xa r off CEILM__ Ho B0 BC TB L q D H1; lia). }
    (* [comment removed for export] *)
    riprefixT.
    replace (ret_pc (Z_to_bv 64 0x19ab4)) with (Z_to_bv 64 0x19ab4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (mf_ctx _ _ MF) as FC. destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
    change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
    eapply evt_cut.
    { eapply (rbig_seq_walk sp gp (Z_to_bv 64 RATP)) with (st := st2) (lo := lo);
        [exact MRz| rewrite Est2; exact FC4| rewrite unsigned_lit by lia; lia| exact FRz| exact ST2| lia| ceil_facts; lia| exact MIz]. }
    intros ms1 (wa0 & wa1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MR3).
    apply evt_done.
    (* [comment removed for export] *)
    assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono usegs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono usegs m2 xa L); try lia; exact Hw).
    assert (AUXz : rauxv_ok mz (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUX2| exact MUz| exact WMz|]. unfold RAUXV_CELL. constructor; [cbn; (keep_hyps CEILV TB sp lo xa L CLO LO XC XI; lia)| constructor]. }
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUXz| exact MU3| exact WM3|]. unfold RAUXV_CELL, RCTX.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
    assert (ERRz : rw_cells usegs mz (RERRNO) [C4 errv]).
    { eapply rrw_cells_agree; [exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; (keep_hyps CEILV TB xa L a CEILM__ H0 Ha n NR LG TLSe0 TLSe3; lia). }
    assert (ERR3 : rw_cells usegs m3 (RERRNO) [C4 errv]).
    { eapply rw_cells_transport; [exact ERRz| exact MU3| exact WM3|]. unfold RCTX. cbn. lia. }
    assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply rnr_conc; exact Hq).
    assert (BL2 : brk_link_ps (step_seq st2) s).
    { eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | exact BL].
      intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      apply Hconc2. cbn. destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
    assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); exact TKz).
    eapply AM.
    { apply (AMP_BIG st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| exact VOK| exact ISE]. }
    { exact MR3. }
    { exact TK2'. }
    { exact BL2. }
    { rewrite SP'. eapply rauxv_ok_weaken; [exact AUX3| ceil_facts; lia]. }
    { rewrite SP'. exact ST3. }
    { ceil_facts; lia. }
    { rewrite SP'. unfold RAM_STACK. lia. }
    { rewrite RATP_unsigned. pose proof the_tb_facts. rewrite ?rerrno_norm in *. exact ERR3. }
    { exact MI3. }
    { reflexivity. }
    intros st3 mo s' ms' PO3 BL3.
    destruct PO3 as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & ENO4 & AUX4 & PE4 & MR4 & TK4 & PSM & PSF & PSO & REL).
    rewrite SP' in ST4, AUX4, PE4. rewrite RATP_unsigned in ERR4. pose proof the_tb_facts. rewrite ?rerrno_norm in *.
    replace (ret_pc (Z_to_bv 64 0x19ba8)) with (Z_to_bv 64 0x19ba8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -48) cs) end.
    { eapply rpres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. cbn in Ha. eapply (rfp_below_ceiling _ st3 _ m4); [exact MR4| lia| ceil_facts; lia]. }
    assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply rnr_lookup_new). }
    assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { destruct (amr_regions _ _ _ REL rid _ RR2) as (r' & Hr' & K' & B' & L' & G'). rewrite Hr'. f_equal. apply G'. reflexivity. }
    assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; exact PT1).
    assert (PT3 : ptrs_in (fun q => q <> rid) st3).
    { apply (amr_ptrs _ _ _ REL); [|exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
    pose proof MR4 as (WF4 & _ & (ML4 & _) & _). pose proof WF4 as (RS4 & WR4 & DJ4 & _).
    assert (RS3 : s_reserved st3 = ref_reserved) by exact RS4.
    (* [comment removed for export] *)
    assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
              (forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a) ->
              rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m4).
    { intros stF RSF HFP.
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
        do 4 right. split; [ceil_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. cbn. unfold RCTX in *.
        split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; unfold RCTX; lia| right; right; left; unfold RCTX; lia]. }
      eapply rpres_except_mono; [exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
      do 4 right. eapply (fresh_addr_anti st (step_seq st2)); [| |exact X].
      { transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
      intros q rq Hq. exists rq. split; [|repeat split; auto; lia].
      transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      rewrite Est2, rnr_lookup_old; [exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
    destruct mo as [g|].
    + (* [comment removed for export] *)
      apply rimplT_ret.
      destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
      pose proof (rmeta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)).
      set (G := conc st3 g) in *.
      assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; ceil_facts; lia).
      assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
      { intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
        destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
      { intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
        destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (SHN3 : (s_shadow st3) !! rid = None).
      { rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. exact FRs. }
      assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
      { rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. reflexivity. }
      eapply evt_cut.
      { eapply (rbig_succ_walk st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:(ceil_facts; lia) sp gp (Z_to_bv 64 RATP));
          [exact HG| exact FR4| exact ST4| lia| exact MI4]. }
      intros ms5 (a0' & a1' & m7 & -> & MU7 & WM7 & MI7 & ST7 & FR7 & MR7 & TK7).
      apply evt_done. cbn [rcoreQ].
      set (stF := big_final st3 g rid n).
      rewrite (rbf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
      change (pw st3 (Some g)) with (pw stF (Some g)).
      exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. do 17 eexists.
      split; [reflexivity|].
      assert (MRF : rmrep stF m7) by (apply (rmrep_big_final st3 g rid n _ G0 (GN3 0) HC3); exact MR7).
      split; [exact MRF|].
      split; [exact TK7|].
      assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite rbig_stride by lia; rewrite <- EL; reflexivity).
      assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
      { intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
      split.
      { (* [comment removed for export] *)
        assert (UA3 : unk_agree (step_seq st2) o m3).
        { eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
          assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; exact Hq).
          split; [exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          intros off h Ho Hc NG. pose proof MRz as (WFz & _). pose proof WFz as (_ & WRz & _).
          destruct (WRz q r Hq2) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). ceil_facts.
          apply MU3. rewrite wa_unsigned by lia. cbn. unfold RCTX. (keep_hyps CEILV TB xa L st3 g r off Ho D; lia). }
        assert (UA4 : unk_agree st3 o m4).
        { eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
          assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
          { destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
            - destruct (amr_regions _ _ _ REL q r2 E) as (r' & Hr' & K' & _ & _ & G'). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. exact Hk.
            - exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
          split; [exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; exact (amr_groups _ _ _ REL)|].
          intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). ceil_facts.
          refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
          intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
          - lia.
          - pose proof (rreserved_tls _ _ RFq) as DT. pose proof (lr_lo_ge r). pose proof (round_up_pg_ge (r_len r)). specialize (DT ltac:(lia)). (keep_hyps CEILV TB xa L st3 g r off Ho X DT; lia).
          - unfold RCTX in X. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). (keep_hyps CEILV TB xa L st3 g r off Ho X D; lia).
          - assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; exact Hk).
            pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
          - pose proof (fresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). (keep_hyps CEILV TB xa L st3 g r off Ho Y H2; lia). }
        eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
        destruct (N.eq_dec q rid) as [->|NE].
        - right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
          change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
          rewrite cell_read_hh0 in Hc by (exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
          exists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
        - left. split; [exact Hq|]. split; [apply rbf_shadow_other; exact NE|].
          split. { intros off (b & gh & Hb & Hf & Ho). exists b, gh. split; [|auto]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)).
                   rewrite lookup_insert_ne; [exact Hb|]. intros <-. cbn in Hf. congruence. }
          intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). ceil_facts.
          pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
          apply MU7; rewrite wa_unsigned by (keep_hyps CEILV xa st3 g r off CEILM__ Ho B0 BC; lia); cbn; unfold RCTX; (keep_hyps CEILV TB n xa L st3 g q r off NR LG Ho D H2 H3 H4; lia). }
      split; [exact MI7|]. split; [exact ST7|]. split; [exact FR7|].
      assert (ERR8 : rw_cells usegs m7 (RERRNO) [C4 errv4]).
      { eapply rw_cells_transport; [exact ERR4| exact MU7| exact WM7|]. cbn. unfold RCTX.
        assert (TBI8 : 0x34190 <= the_tb /\ the_tb + 4096 <= 0x54260) by (pose proof the_tb_facts as TBX8; destruct TBX8 as (TBX8a & TBX8b & TBX8c & [TBX8d|TBX8d]); lia).
        (keep_hyps CEILV TB n xa L st3 g XA H1 GI2 TBI8 XI LG NR; lia). }
      split; [rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; exact ERR8|].
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [exact Hq| split; [exact Kq| exact Xa]]. }
      assert (PE18 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m7).
      { eapply rpres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_trans.
        { eapply rpres_except_of_munch; [exact MU7| exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
          - left. right; right; right. exists ridg, rg. split; [exact Hrg|]. split; [exact Krg|]. lia.
          - do 4 right. split; [ceil_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia].
          - left. right; right; left. unfold RCTX in *. lia. }
        apply rpres_except_refl. }
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [exact MR0| exact MRF| exact AUX1| exact PE18| ceil_facts; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
          exists r'. split; [|repeat split; auto]. exact Hr'.
        - change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE18]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      rewrite (rbf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
      split. { intros a Ha. do 4 right. split; [ceil_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      split. { unfold u32. Z.div_mod_to_equations. lia. }
      assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by (keep_hyps CEILV n xa st3 g NR; lia); Z.div_mod_to_equations; (keep_hyps CEILV TB n xa L st3 g q r NR H2 H3; lia)).
      pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
      assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; (keep_hyps CEILV TB n xa L st3 g q r H2 H3; lia)).
      rewrite <- big_ml_eq in RU by lia.
      split.
      { (* [comment removed for export] *) constructor; rewrite ?(rbf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
        - reflexivity.
        - exact RR3.
        - reflexivity.
        - lia.
        - reflexivity.
        - lia.
        - lia.
        - rewrite <- EL. lia.
        - lia.
        - rewrite RU. Z.div_mod_to_equations. lia.
        - lia.
        - lia.
        - lia.
        - intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (rbf_groups st3 g rid n (GN3 0)) in Hb'.
          destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
          rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
        - change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
          rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        - intros off Ho Hfit. Z.div_mod_to_equations. lia.
        - unfold stF. rewrite rbf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
        - exact MSL.
        - lia.
        - lia.
        - lia.
        - lia.
        - right. repeat split; lia. }
      split. { intros _. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
               cbn [fst snd]. rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      split; [exact MRELF|].
      split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| exact BL3]. }
      repeat split; assumption.
    + (* [comment removed for export] *)
      cbn [pw oconc].
      riprefixT.
      eapply evt_cut.
      { apply rbig_fail2a_walk. exact ML4. }
      intros ms2 ->. apply evt_done.
      eapply rimplT_munmap.
      { eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
          [ rewrite unsigned_lit by (keep_hyps CEILV sp lo xa CEILF__ CLO LO SPR; lia); exact ST4 | rewrite unsigned_lit by (keep_hyps CEILV TB xa L TLSFACTS CEILM__; lia); rewrite ?rerrno_norm; exact ERR4 | exact MI4 | reflexivity | unfold IB, UNIT; f_equal; (keep_hyps CEILV n xa; lia)
          | (keep_hyps CEILV xa X0; lia) | rewrite ELm; (keep_hyps CEILV xa L CEILM__ XC; lia) | unfold IB, UNIT; (keep_hyps CEILV n xa NR; lia) | rewrite unsigned_lit by (keep_hyps CEILV sp lo xa CEILF__ CLO LO SPR; lia); (keep_hyps CEILV sp lo xa LO; lia)
          | rewrite unsigned_lit by (keep_hyps CEILV TB xa L TLSFACTS CEILM__; lia); rewrite unsigned_lit by (keep_hyps CEILV sp lo xa CEILF__ CLO LO SPR; lia); (keep_hyps CEILV TB sp lo xa L TLSFACTS CLO LO; lia) | rewrite ELm; left; ceil_facts; (keep_hyps CEILV lo xa L CLO XC; lia)
          | rewrite ELm, unsigned_lit by (keep_hyps CEILV TB xa L TLSFACTS CEILM__; lia); (keep_hyps CEILV TB n xa L NR LG TLSe0 TLSe3; lia) | rewrite unsigned_lit by (keep_hyps CEILV TB xa L TLSFACTS CEILM__; lia); (keep_hyps CEILV TB xa L TLSFACTS; lia) ]. }
      intros ans2 ms3 PM. unfold rmunmap_post in PM.
      destruct PM as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He6).
      rewrite (munmap_answer_ok_range ans2 (rg_err_range _ ans2 He6)). apply rimplT_ret.
      rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by lia.
      replace (ret_pc (Z_to_bv 64 0x19c80)) with (Z_to_bv 64 0x19c80) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -48) cs) end.
      { eapply rrw_cells_agree; [exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. ceil_facts. (keep_hyps CEILV TB sp lo xa L a CLO LO XC H1 Ha; lia). }
      eapply evt_cut. { eapply rbig_fail2b_walk; [exact FR6| exact ST6| lia| lia]. }
      intros ms4 [-> ST7]. apply evt_done. cbn [rcoreQ].
      set (stF := drop_region rid st3).
      assert (MRF : rmrep stF m6).
      { eapply (rmrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
        rewrite <- EL in Hout.
        assert (A1 : a < alloc_ceiling /\ (a + 1 <= RERRNO \/ RERRNO + 4 <= a) /\ (a < xa \/ xa + L <= a)).
        { destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
            [unfold RMLOCK in *; ceil_facts; (keep_hyps CEILV TB xa L a CEILF__ H1 Hout X; lia)| unfold RLIBC in *; ceil_facts; (keep_hyps CEILV TB xa L a CEILF__ H1 Hout X; lia)| unfold RGOT_SSP in *; ceil_facts; (keep_hyps CEILV TB xa L a CEILF__ H1 Hout X; lia)| unfold RSSP_GUARD in *; ceil_facts; (keep_hyps CEILV TB xa L a CEILF__ H1 Hout X; lia)|].
          destruct (WR4 q rq Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). pose proof (lr_lo_ge rq).
          pose proof (rreserved_tlsU _ _ RFq). pose proof (round_up_pg_ge (r_len rq)).
          split; [lia|]. split; [(keep_hyps CEILV TB xa L a rq Xa H2 H3; lia)|].
          destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
          destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
        ceil_facts.
        apply MU6; rewrite wa_unsigned by (keep_hyps CEILV xa a Ha; lia); cbn; (keep_hyps CEILV TB sp lo xa L a CLO LO A1; lia). }
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [|split; [exact Kq|exact Xa]].
        unfold stF. rewrite rdr_lookup_old; [exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
      assert (PE16 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m6).
      { eapply rpres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_of_munch_nw; [exact MU6|]. intros a Ha NC. cbn.
        split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; lia|].
        do 4 right. split; [ceil_facts; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      exists m6, (F_mm_syscalls.rg_errno ans2 errv4). do 14 eexists. split; [reflexivity|].
      split; [exact MRF|]. split; [apply rticks_ok_drop_region; exact TK4|]. split; [exact MI6|]. split; [exact ST7|].
      split; [rewrite RATP_unsigned; pose proof the_tb_facts; rewrite ?rerrno_norm in *; exact ERR6|].
      split; [destruct ans2 as [e6|d6]; cbn [F_mm_syscalls.rg_errno]; [cbn in He6; rewrite (proj2 He6); reflexivity| exact (ENO4 eq_refl)]|].
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [exact MR0| exact MRF| exact AUX1| exact PE16| ceil_facts; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
          exists r'. split; [|repeat split; auto]. unfold stF. rewrite rdr_lookup_old by exact NE. exact Hr'.
        - unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
          change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE16]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      split; [exact MRELF|].
      split.
      { eapply (brk_link_ps_ext st3); [reflexivity| | exact BL3]. intros rb ob Hb. unfold stF. apply rdr_conc. cbn.
        destruct PT3 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
      repeat split; assumption.
Qed.
End BIG.

End PORT.

End WithCeil.
End TwB.
End RF_malloc_big.

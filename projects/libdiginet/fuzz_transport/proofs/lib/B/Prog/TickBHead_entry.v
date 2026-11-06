(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 513 of its 626 lines of code are new or changed and 1026 lines of the source are left out. *)
(* TickBHead_entry: Lemma tbh_entry : tbh_call_at -> transport_diginet_session_tick_cg_holds_stmt. The walk of
   diginet_session_tick on fuzz_transport.asan-ubsan (0x8909c = transportb_sigma TB_diginet_session_tick,
   AF_diginet_session_tick = 0x7dfc of lib/B/Prog/DgnTransportBList.v) from the entry to its call of
   __asan_set_shadow_f8 (+0x13c), whose state the head's own cut tbh_call_at (lib/B/Prog/TickBHead_mid.v) takes.
   rule 24: proves no function (a segment of a piece of the walk of diginet_session_tick).
   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []); the runs are the
   position-abstract runs of lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x:
     run 1a  +0x000 .. +0x044  the frame (`addi sp, sp, -192`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into s1
                               (a run to +0x048);
     run 1b  +0x048 .. +0x06c  now at s1 + 56, the flag word through its GOT word (1, so `beqz a2` is not taken), s8 =
                               the shadow base, s4 = s, a0 = 0x700, up to `jal __asan_stack_malloc_5`;
     +0x070                    the class-5 stack malloc: the statement's astack_malloc_realizes premise through
                               lib/A/Prog/TransportGFrame.v gx_stack_malloc_at (the frame F in a0, 4096 <= F);
     run 2a  +0x074 .. +0x0d8  s2 = s11 = F (`bnez s2` taken: the real-stack arm is not reached), the frame word at
                               s1 + 64, the frame's 24-byte header, s3 = the frame's shadow address (a run to +0x0dc);
     run 2b  +0x0dc .. +0x138  the frame's shadow bytes 0 .. 19, s6 = s3 + 20, a1 = 186, a0 = s6, up to
                               `jal __asan_set_shadow_f8`.
   Each run starts from a symbolic state built from the registers the run before left (the valuation
   lib/B/Prog/TickBHead_kit.v slh_EB). What the call keeps (acall_kept_g) runs from the entry to the stack malloc's
   return (lib/A/Prog/TransportGCg.v dk_kept_step_g, then dk_kept_trans_g with the call's acall_kept) and from there
   over the written ranges (dk_kept_own_g: the slot s1 + 64 in the call's window, the frame's header and its shadow
   bytes in the own frame). No byte of G is written. The record's premises give tick_laws (with
   lib/B/Prog/DgnTransportBCg.v G_HARNESS_gx_ok / G_HARNESS_gx_noerrno) and tick_callees (all ten contracts). Image
   A's twin: lib/A/Prog/TickHead_entry.v. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg TickCutB TickBHead_mid.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TickBHead_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require SlostHead.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module SLH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.SlostHead.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition TBH_B0 : Z * Z := (0, 0).

(* run 1a, +0x000 .. +0x048: the stack region below the entry sp. *)
Definition tbh_facts1 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_tbh1 : sstate := mkSS AF_diginet_session_tick sr_atoms [stack_region TICK_FRAME] None tbh_facts1.
Definition TBH_C1 : Z := AF_diginet_session_tick + 0x48.

(* run 1b, +0x048 .. +0x070: s1 (atom 9) is the realigned sp; the run writes now at s1 + 56 and reads the four image
   cells of TickBHead_kit.v slh_img_regionsB (the flag word's GOT word and cell, the shadow base's GOT word and
   cell). *)
Definition tbh_rg_now : YP09.region := YP09.mkRegion (Some 9%nat) 56 64 56 64 [].
Definition tbh_facts2 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_tbh2 : sstate := mkSS TBH_C1 sr_atoms (tbh_rg_now :: slh_img_regionsB) None tbh_facts2.

(* run 2a, +0x074 .. +0x0dc: after the stack malloc, the frame F in a0 (atom 10); the run writes the slot s1 + 64 and
   the frame's 24-byte header. s8 (atom 24) is the shadow base. *)
Definition TBH_C2 : Z := AF_diginet_session_tick + 0x74.
Definition TBH_C3 : Z := AF_diginet_session_tick + 0xdc.
Definition tbh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 64 72 64 72 [].
Definition tbh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition tbh_facts3 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_tbh3 : sstate := mkSS TBH_C2 sr_atoms [tbh_rg_slot; tbh_rg_hdr] None tbh_facts3.

(* run 2b, +0x0dc .. +0x13c: s3 (atom 19) is the frame's shadow address; the run writes its shadow bytes 0 .. 19. *)
Definition tbh_rg_sh : YP09.region := YP09.mkRegion (Some 19%nat) 0 20 0 20 [].
Definition tbh_facts4 : facts := mkFacts [(19%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_tbh4 : sstate := mkSS TBH_C3 sr_atoms [tbh_rg_sh] None tbh_facts4.

Section th. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma tbh_vals : BASE + AF_diginet_session_tick = transportb_sigma TB_diginet_session_tick.
Proof. vm_compute. reflexivity. Qed.

(* The entry state of run 1a (the saves go into the stack region). *)
Lemma tbh_entry1 : forall (W : world segs) regs mem,
  (forall a, spZ regs - TICK_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (slh_EB regs) ss_tbh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_tick)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_tbh1.
  assert (Usp : bv_unsigned (ew (slh_EB regs) 2) = spZ regs)
    by (rewrite (slh_ew_regB regs 2 2%bv eq_refl); reflexivity).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold TICK_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold tbh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The entry state of run 1b: the slot s1 + 56 and the four image cells. *)
Lemma tbh_entry2 : forall ly S (W : world segs) regs mem md spv,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 9 = w64 spv -> 2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  (forall a, spv + 56 <= a < spv + 64 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (slh_EB regs) ss_tbh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TBH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md spv HCELLS HAR R9 Hsp Hsp32 Hpres.
  rewrite restrict_mkst_fx. unfold ss_tbh2.
  assert (U9 : bv_unsigned (ew (slh_EB regs) 9) = spv)
    by (rewrite (slh_ew_regB regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (E32 : ew (slh_EB regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply slh_ew_32B.
  destruct (slh_img_okB B ly S W mem md (slh_EB regs) HCELLS HAR
    (slh_ew_objB regs 1 ltac:(lia)) (slh_ew_objB regs 95 ltac:(lia))
    (slh_ew_objB regs 0 ltac:(lia)) (slh_ew_objB regs 96 ltac:(lia)) E32) as [HRs HPd].
  destruct slh_valsB as (V1 & V95 & V0 & V96).
  assert (VB : forall n v0, ew (slh_EB regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (slh_EB regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold tbh_rg_now, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold slh_img_regionsB in *. apply pairwise_disjoint_of_extents.
    unfold tbh_rg_now, got_regionP, bcell_regionP, slh_got_uarB, slh_uar_cellB, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (slh_ew_objB regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (slh_ew_objB regs 95 ltac:(lia)))
      by (rewrite V95; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (slh_ew_objB regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) (slh_ew_objB regs 96 ltac:(lia)))
      by (rewrite V96; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95, V0, V96. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
  - unfold tbh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2a: the slot s1 + 64 and the frame's header. *)
Lemma tbh_entry3 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 2048 <= spv -> F mod 64 = 0 ->
  (forall a, spv + 64 <= a < spv + 72 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (slh_EB regs) ss_tbh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TBH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R24 Hsp Hsp32 HF0 HFs HF64 Hpslot Hpframe.
  rewrite restrict_mkst_fx. unfold ss_tbh3.
  assert (U2 : bv_unsigned (ew (slh_EB regs) 2) = spv)
    by (rewrite (slh_ew_regB regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (slh_EB regs) 9) = spv)
    by (rewrite (slh_ew_regB regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (slh_EB regs) 10) = F)
    by (rewrite (slh_ew_regB regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew (slh_EB regs) 24) = SHADOW_OFF)
    by (rewrite (slh_ew_regB regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (slh_EB regs) 32) = SHADOW_OFF)
    by (rewrite (slh_ew_32B regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [tbh_rg_slot tbh_rg_hdr YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold tbh_rg_slot, tbh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold tbh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U24, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2b: the frame's shadow bytes 0 .. 19. *)
Lemma tbh_entry4 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 19 = w64 SH -> SHADOW_OFF <= SH -> SH + 20 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 20 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (slh_EB regs) ss_tbh4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TBH_C3)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R19 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_tbh4.
  assert (U19 : bv_unsigned (ew (slh_EB regs) 19) = SH)
    by (rewrite (slh_ew_regB regs 19 19%bv eq_refl), R19; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold tbh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold tbh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold tbh_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* The walk from the entry to the call of __asan_set_shadow_f8, then the head's call cut. *)
Lemma tbh_entry : tbh_call_at B MT -> @transport_diginet_session_tick_cg_holds_stmt fx rc B MT.
Proof.
intros CALL.
unfold transport_diginet_session_tick_cg_holds_stmt.
intros HPCS HCELLS HTC HGU HGNE0 HROU HRNE LAWS MTL MTF SMP FFL ASM0 SSF8 IOS0 SST0 AI0 NT0 SFR0 SS000 SD0 TK0.
unfold transport_diginet_session_tick_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Hnow Htw Hfn Hm HTF HROM HAP HI1 HI2 HQB HI4 HNB HI5a HI5b Hcnt Hcnt0 Hcnt2 Hev.
(* HQB (S_queued Bw <= QUEUE_MAX) and HNB (g_ncmd Bw <= CMDS_MAX): premises of the statement that no piece needs (the
   cuts carry invariants (2) and (4) without them). *)
clear HQB HNB.
pose proof (G_HARNESS_gx_ok B HGU) as HGX.
pose proof (G_HARNESS_gx_noerrno B HGNE0) as HGNE.
pose proof (ASM0 fx) as ASM.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : TICK_STK = ltac:(let v := eval vm_compute in TICK_STK in exact v)) by reflexivity.
assert (FF : TICK_FRAME = 192) by reflexivity.
assert (CS : TICK_S = 6157888) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - TICK_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (tbh_entry1 W regs memc Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (slh_EB regs)) by apply slh_env_imgB.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (slh_EB regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (slh_EB regs) 2) = spZ regs)
  by (rewrite (slh_ew_regB regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_tick)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1a, +0x000 .. +0x048 *)
paj_run_to_tok RUNTO HS HJ SHOK TBH_B0 TBH_C1.
{ tbh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
set (sp1 := 32 * ((spZ regs + -192) / 32)).
destruct (can_sp1_facts (spZ regs + -192) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by (clear - Hsp1r; lia).
assert (E2' : ew (slh_EB regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (slh_ew_regB regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
tbh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (slh_EB regs) 2 (spZ regs) (-192) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
tbh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (slh_ew_regB regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
tbh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (slh_ew_regB regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
tbh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
tbh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (slh_EB regs) 2 (spZ regs) (-192) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
tbh_reg HS (10%bv : bv 5) (w64 TICK_S) R10
  ltac:(cbn [sv_denot]; rewrite (slh_ew_regB regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
tbh_reg HS (11%bv : bv 5) (w64 now) R11
  ltac:(cbn [sv_denot]; rewrite (slh_ew_regB regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
tbh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) SLH.slh_saved -> -104 <= o <= -8).
{ intros o r0 Hin. unfold SLH.slh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) SLH.slh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. unfold SLH.slh_saved in Hin.
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r0))
    ltac:(tbh_u64 (YK11.getr regs r0))).
  apply (can_field_of_region (slh_EB regs) _ 2 (spZ regs) _ (-192) 0 (-192) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r0)) 0) (bv_unsigned (YK11.getr regs r0)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (slh_ew_regB regs (Z.to_nat (bv_unsigned r0)) r0 ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; tbh_u64 (YK11.getr regs r0)
  | cbn; lia ]. }
clear HRsk.
(* run 1b, +0x048 .. +0x070, from a state built from the registers *)
pmkst HS.
set (ms1 := ms) in *. clearbody ms1. clear HS SHOK.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
pose proof (tbh_entry2 lyc Sc W (ms_regs ms1) (ms_mem ms1) _ sp1 HCELLS HAR1 R9 ltac:(lia) Hsp1al
  ltac:(intros a Ha; apply (slh_jpresB B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia)) as HS.
clear HEI.
assert (HEI : img_env VAL A_LIM (slh_EB (ms_regs ms1))) by apply slh_env_imgB.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (slh_EB (ms_regs ms1)) (mrestrict (w_H W) (ms_mem ms1)))
  by constructor.
assert (U9b : bv_unsigned (ew (slh_EB (ms_regs ms1)) 9) = sp1)
  by (rewrite (slh_ew_regB (ms_regs ms1) 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TBH_C1)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK TBH_B0.
{ tbh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9b in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1b, HFr into HFr1b, HG into HG1b.
(* the registers at the call of __asan_stack_malloc_5 *)
lazymatch type of HS with context [restrict _ ?m] => set (msM := m) in *; clearbody msM end.
tbh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 32368)) Q1 ltac:(apply codeptr_val; exact HEI).
tbh_kreg HS (ms_regs ms1) (2%bv : bv 5) 2%nat R2 Q2. tbh_kreg HS (ms_regs ms1) (3%bv : bv 5) 3%nat R3 Q3.
tbh_kreg HS (ms_regs ms1) (4%bv : bv 5) 4%nat R4 Q4. tbh_kreg HS (ms_regs ms1) (8%bv : bv 5) 8%nat R8 Q8.
tbh_kreg HS (ms_regs ms1) (9%bv : bv 5) 9%nat R9 Q9.
tbh_reg HS (20%bv : bv 5) (w64 TICK_S) Q20
  ltac:(cbn [sv_denot]; rewrite (slh_ew_regB (ms_regs ms1) 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10).
tbh_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) Q24
  ltac:(cbn [sv_denot]; first [reflexivity | rewrite (slh_ew_32B (ms_regs ms1)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]).
(* now, at s1 + 56 *)
tbh_region HS 0%nat HRnow.
assert (HNOW1 : rdword (aview segs (w_H W) (ms_mem msM)) (sp1 + 56) = Some now).
{ apply (YF0x.val_mem_rdword (w_H W) (ms_mem msM) (sp1 + 56) now ltac:(lia)).
  apply (can_field_of_region (slh_EB (ms_regs ms1)) _ 9 sp1 _ 56 64 56 64 56 8%N (SOff 11 0) now HRnow U9b);
  [tbh_in | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (slh_ew_regB (ms_regs ms1) 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact R11. }
clear HRnow.
(* run 1b wrote the slot s1 + 56 only *)
assert (K1b : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 56 <= a < sp1 + 64) ->
  aview segs (w_H W) (ms_mem msM) a = aview segs (w_H W) (ms_mem ms1) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 56 <= x < sp1 + 64) HFr1b); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9b in Hx; lia |]).
  destruct Hin. }
(* run 1a wrote [sp - 192, sp) only *)
assert (K1a : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 192 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
assert (HSV1 : forall (o : Z) (r : bv 5), In (o, r) SLH.slh_saved ->
  rdword (aview segs (w_H W) (ms_mem msM)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. pose proof (HSVo o r0 Hin) as Ho. rewrite <- (HSV o r0 Hin).
  apply rdword_ext. intros i Hi. apply K1b; lia. }
(* +0x070: the class-5 stack malloc, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_malloc_5)) mm rom) mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low SMP TICK_CID ASM
    ltac:(unfold TICK_CID; lia) TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 32368)) HJ) end.
  - unfold spZ at 1. rewrite Q2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - exact Hcnt. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ TICK_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ TICK_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ TICK_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh.
change (fs_frame_bytes TICK_CID) with 2048 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc TICK_CID pos) in *.
rewrite Zplus_minus in HK1.
(* the thirteen saved words and now, kept by the class-5 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) SLH.slh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. pose proof (HSVo o r0 Hin) as Ho.
  rewrite <- (HSV1 o r0 Hin). unfold rdword.
  rewrite !(proj1 HK1) by lia. reflexivity. }
assert (HNOW2 : rdword (aview segs (w_H W) mem2) (sp1 + 56) = Some now).
{ rewrite <- HNOW1. unfold rdword. rewrite !(proj1 HK1) by lia. reflexivity. }
assert (P2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs msM) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact Q2]).
assert (P3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs msM) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact Q3]).
assert (P4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs msM) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact Q4]).
assert (P8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs msM) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact Q8]).
assert (P9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs msM) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact Q9]).
assert (P20 : YK11.getr regs2 20 = w64 TICK_S)
  by (transitivity (YK11.getr (ms_regs msM) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact Q20]).
assert (P24 : YK11.getr regs2 24 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs msM) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact Q24]).
clear HS.
set (memT := ms_mem msM) in *. set (regsT := ms_regs msM) in *. clearbody memT regsT. clear msM.
(* +0x074 .. +0x0dc: s2 = s11 = F, the slot s1 + 64, the frame's header, s3 = the frame's shadow address. *)
pose proof (tbh_entry3 W regs2 mem2 F sp1 P2 P9 Ha0 P24 ltac:(lia) Hsp1al HF0 ltac:(lia) HF64
  ltac:(intros a Ha; apply (slh_jpresB B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia)
  ltac:(intros a Ha; apply Hfpres; lia)) as HS.
clear HEI.
assert (HEI : img_env VAL A_LIM (slh_EB regs2)) by apply slh_env_imgB.
clear SHOK.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (slh_EB regs2) (mrestrict (w_H W) mem2)) by constructor.
assert (U9c : bv_unsigned (ew (slh_EB regs2) 9) = sp1)
  by (rewrite (slh_ew_regB regs2 9 9%bv eq_refl), P9; apply unsigned_lit_small; lia).
assert (U10c : bv_unsigned (ew (slh_EB regs2) 10) = F)
  by (rewrite (slh_ew_regB regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TBH_C2)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_to_tok RUNTO HS HJ SHOK TBH_B0 TBH_C3.
{ tbh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9c in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ TICK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10c in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes TICK_CID) with 2048.
  change (frame_addr lyc TICK_CID pos) with F. lia. }
rename HF into HF2a, HFr into HFr2a, HG into HG2a.
lazymatch type of HS with context [restrict _ ?m] => set (ms2a := m) in *; clearbody ms2a end.
match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
(* the registers at +0x0dc *)
assert (EF10 : ew (slh_EB regs2) 10 = Z_to_bv 64 F) by (rewrite (slh_ew_regB regs2 10 10%bv eq_refl); exact Ha0).
assert (EF24 : ew (slh_EB regs2) 24 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (slh_ew_regB regs2 24 24%bv eq_refl); exact P24).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
tbh_reg HS (19%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T19
  ltac:(exact (can_denot_shadow (slh_EB regs2) 10 24 F SHADOW_OFF EF10 EF24 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
tbh_kreg HS regs2 (2%bv : bv 5) 2%nat P2 T2. tbh_kreg HS regs2 (3%bv : bv 5) 3%nat P3 T3.
tbh_kreg HS regs2 (4%bv : bv 5) 4%nat P4 T4. tbh_kreg HS regs2 (8%bv : bv 5) 8%nat P8 T8.
tbh_kreg HS regs2 (9%bv : bv 5) 9%nat P9 T9. tbh_kreg HS regs2 (20%bv : bv 5) 20%nat P20 T20.
tbh_kreg HS regs2 (24%bv : bv 5) 24%nat P24 T24.
tbh_reg HS (18%bv : bv 5) (w64 F) T18
  ltac:(cbn [sv_denot]; rewrite (slh_ew_regB regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
tbh_reg HS (27%bv : bv 5) (w64 F) T27
  ltac:(cbn [sv_denot]; rewrite (slh_ew_regB regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
(* run 2a wrote the slot s1 + 64 and the frame's header only *)
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 64 <= a < sp1 + 72 \/ F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms2a) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 64 <= x < sp1 + 72 \/ F <= x < F + 24) HFr2a);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9c, ?U10c in Hx;
    first [left; lia | right; lia] |]).
  destruct Hin. }
pose proof HG2a as G2a. clear HF2a HFr2a HG2a.
(* +0x0dc .. +0x13c: the frame's shadow bytes 0 .. 19, s6, a1, a0, up to the call of __asan_set_shadow_f8. *)
pmkst HS.
clear HS.
pose proof (tbh_entry4 W (ms_regs ms2a) (ms_mem ms2a) (SHADOW_OFF + F / 8) T19
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
clear HEI.
assert (HEI : img_env VAL A_LIM (slh_EB (ms_regs ms2a))) by apply slh_env_imgB.
clear SHOK.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (slh_EB (ms_regs ms2a)) (mrestrict (w_H W) (ms_mem ms2a)))
  by constructor.
assert (U19 : bv_unsigned (ew (slh_EB (ms_regs ms2a)) 19) = SHADOW_OFF + F / 8)
  by (rewrite (slh_ew_regB (ms_regs ms2a) 19 19%bv eq_refl), T19; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TBH_C3)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK TBH_B0.
{ tbh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ TICK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes TICK_CID / 8) with 256.
  change (frame_addr lyc TICK_CID pos) with F. unfold shadow_addr. lia. }
rename HF into HF2b, HFr into HFr2b, HG into HG2b.
lazymatch type of HS with context [restrict _ ?m] => set (msC := m) in *; clearbody msC end.
(* run 2b wrote the frame's shadow bytes 0 .. 19 only *)
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) ->
  aview segs (w_H W) (ms_mem msC) a = aview segs (w_H W) (ms_mem ms2a) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 20) HFr2b);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U19 in Hx; lia |]).
  destruct Hin. }
pose proof HG2b as G2b. clear HF2b HFr2b HG2b.
(* the registers at the call *)
tbh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + TBH_RET)) V1 ltac:(apply codeptr_val; exact HEI).
tbh_reg HS (10%bv : bv 5) (w64 (SHADOW_OFF + F / 8 + 20)) V10
  ltac:(cbn [sv_denot]; rewrite U19; reflexivity).
tbh_reg HS (11%bv : bv 5) (w64 186) V11 ltac:(reflexivity).
tbh_reg HS (22%bv : bv 5) (w64 (SHADOW_OFF + F / 8 + 20)) V22
  ltac:(cbn [sv_denot]; rewrite U19; reflexivity).
tbh_kreg HS (ms_regs ms2a) (2%bv : bv 5) 2%nat T2 V2. tbh_kreg HS (ms_regs ms2a) (3%bv : bv 5) 3%nat T3 V3.
tbh_kreg HS (ms_regs ms2a) (4%bv : bv 5) 4%nat T4 V4. tbh_kreg HS (ms_regs ms2a) (8%bv : bv 5) 8%nat T8 V8.
tbh_kreg HS (ms_regs ms2a) (9%bv : bv 5) 9%nat T9 V9. tbh_kreg HS (ms_regs ms2a) (18%bv : bv 5) 18%nat T18 V18.
tbh_kreg HS (ms_regs ms2a) (19%bv : bv 5) 19%nat T19 V19. tbh_kreg HS (ms_regs ms2a) (20%bv : bv 5) 20%nat T20 V20.
tbh_kreg HS (ms_regs ms2a) (24%bv : bv 5) 24%nat T24 V24. tbh_kreg HS (ms_regs ms2a) (27%bv : bv 5) 27%nat T27 V27.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_set_shadow_f8)) mm rom) mdx) Q);
  set (mdC := mdx) in * end.
clear HS SHOK.
set (memC := ms_mem msC) in *.
(* ---- what the call keeps, from the entry memory memc to the memory at the call ---- *)
assert (Hwin : forall a, spZ regs - TICK_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 208 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. rewrite (K1b a Ha ltac:(lia)). exact (K1a a Ha ltac:(lia)). }
assert (GT : forall a, apresent (w_H W) memc a -> apresent (w_H W) memT a).
{ intros a Ha. apply (apresent_grows _ _ _ a HG1b). exact (apresent_grows _ _ _ a HG1 Ha). }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memT (spZ regs - TICK_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc memT
    (spZ regs - TICK_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 208 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - exact GT.
  - intros a Ha _. lia.
  - intros b m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W mem2 (spZ regs - TICK_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W memT W mem2 (spZ regs - TICK_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS_B W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS_B W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS_B lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
(* every byte outside the three written ranges is the one the stack malloc left *)
assert (KFC : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp1 + 64 <= a < sp1 + 72 \/ F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) ->
  aview segs (w_H W) memC a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros [X | X]; apply Hn; tauto)). }
assert (GFC : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) memC a).
{ intros a Ha. apply (apresent_grows _ _ _ a G2b). exact (apresent_grows _ _ _ a G2a Ha). }
assert (NGF : forall a, F <= a < F + 2048 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ TICK_CID pos a HAR2 Hin2 ltac:(change (fs_frame_bytes TICK_CID) with 2048; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (KGC : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memC (spZ regs - TICK_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_own_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc S2 W memc mdc mem2 md2 mem2 memC
    (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F (flag_addr lyc TICK_CID pos) (fun _ => False)
    (fun a => sp1 + 64 <= a < sp1 + 72 \/ F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GFC].
  - intros a [X | [X | X]].
    + left. lia.
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes TICK_CID) with 2048. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
  - intros a Ha Hn. exact (KFC a Ha Hn). }
assert (GXC : gx_kept segs TG.G_HARNESS_B W memc W memC).
{ intros a Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (KFC a ltac:(lia) ltac:(intros [X | [X | X]];
    [exact (NGH a ltac:(unfold SHADOW_OFF; lia) Hg) | exact (NGF a ltac:(lia) Hg)
    | exact (NGH a ltac:(unfold SHADOW_OFF in *; lia) Hg)])).
  exact (GK2 a Hg). }
(* the thirteen saved words, the frame's last word and now, at memC *)
assert (HSVC : forall (o : Z) (r : bv 5), In (o, r) SLH.slh_saved ->
  rdword (aview segs (w_H W) memC) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. pose proof (HSVo o r0 Hin) as Ho. rewrite <- (HSV2 o r0 Hin).
  apply rdword_ext. intros i Hi. apply KFC; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HFWC : Forall (fun o : Z * Z => rdword (aview segs (w_H W) memC) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) TICK_SAVED).
{ unfold TICK_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSVC (- o) (Z_to_bv 5 r)); unfold SLH.slh_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
assert (HFLC : rdword (aview segs (w_H W) memC) (F + TICK_FBYTES - 8) = Some (flag_addr lyc TICK_CID pos)).
{ rewrite <- Hflag. unfold TICK_FBYTES. apply rdword_ext. intros i Hi. apply KFC; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  intros [X | [X | X]]; [lia | lia |].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HNOWC : rdword (aview segs (w_H W) memC) (sp1 + 56) = Some now).
{ rewrite <- HNOW2. apply rdword_ext. intros i Hi. apply KFC; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  intros [X | [X | X]]; [lia | lia | unfold SHADOW_OFF in *; lia]. }
(* the class-5 frame changed the allocator state's st_fs only *)
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
(* the record facts, the callee contracts and the caller's facts, as the cuts state them *)
assert (HLAWS : tick_laws B MT)
  by exact (conj HPCS (conj HCELLS (conj HTC (conj HGU (conj HGNE0 (conj HROU (conj HRNE (conj LAWS (conj MTL
    (conj MTF (conj SMP (conj FFL (conj HGX HGNE))))))))))))).
assert (HCALLEES : tick_callees B MT)
  by exact (conj ASM0 (conj SSF8 (conj IOS0 (conj SST0 (conj AI0 (conj NT0 (conj SFR0 (conj SS000
    (conj SD0 TK0))))))))).
assert (HFIX : tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F).
{ unfold tick_fix.
  refine (conj HJe (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj Hsp16 (conj Hlo (conj Hhi
    (conj Hnow (conj Htw (conj Hfn (conj Hm (conj HTF (conj HROM (conj HAP
    (conj (conj HI1 (conj HI2 (conj HI4 (conj HI5a HI5b)))) (conj Hcnt (conj Hcnt0 (conj Hcnt2 (conj Hev
    (conj _ (conj eq_refl (conj HF0 (conj HF64 (conj HFc HFapp))))))))))))))))))))))))))).
  unfold sp1, TICK_FRAME. replace (spZ regs - 192) with (spZ regs + -192) by lia. reflexivity. }
assert (MID : tbh_mid B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now pos sp1 F S2 memC mdC (ms_regs msC)).
{ refine (conj HJ (conj Hfrs2 (conj Eab2 (conj HMO (conj KGC (conj GXC (conj HFWC (conj HFLC (conj HNOWC _))))))))).
  unfold tbh_regs, tick_regs_base.
  refine (conj (conj V2 (conj _ (conj _ (conj V8 (conj V9 (conj V18 V27)))))) (conj V19 (conj V20 (conj V22 V24)))).
  - rewrite V3. symmetry. exact Hgp.
  - rewrite V4. symmetry. exact Htp. }
exact (CALL HLAWS HCALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2
  memC mdC (ms_regs msC) HFIX MID V10 V11 V1).
Qed.
End th.

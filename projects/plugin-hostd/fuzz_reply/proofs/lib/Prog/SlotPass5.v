(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 613 of its 658 lines of code are new or changed and 1184 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/SlotPass9G.v, with its module paths and module names changed; 102 of its 129 lines of code are new or changed and 631 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
  YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09
  YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import
  Img0 Contract ContractT FrameAPI SlotKept SlotPack AllocPack MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadQ SlotWalk snprintf_c
  check_no_loss_read_c check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept
  send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c
  gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep ListRep CheckRep HarnessTr RelayRunT RelayRunF
  source_reset_c check_no_loss_c check_shape_ends_c check_shape_done_c drain_b_c op_add_c SlotInv SlotSteps SlotRes
  SlotReads KindB HarnessGlue HarnessFrame SlotHead SlotHeadP SlotEntry RelayCap SlotExitScanAux
  relay_instance_gone_b_c relay_remove_b_c ListStep ListTr SlotPass2Run SlotPass2Check SlotPass5Run SlotPass5Loop
  SlotPass5Check SlotPass1w SlotPass5T SlotPass5S SlotPass5L2 SlotEntryRun SlotExitFinAux printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotPass5L1 SlotPass5C SlotRI3 SlotP5Res3
  SlotP5Res3Full SlotPass5V SlotPass5G.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p5_glue : forall B API LS SH SK ra empty rc fx j E CS RI t k c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_no_loss_read_contract ->
  J2 (rc := rc) B (API rc) E RI t k c ->
  SR (ms_segs B) c (p5_s24 (rc := rc) B (API rc) E RI t k).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t k c HF CNR HJ.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  pose proof (proj1 (proj1 PRE)) as LP.
  destruct LP as (_ & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC.
  assert (SPB : 0 <= slot_sp E /\ slot_sp E + 32 < 2 ^ 64).
  { clear - SPLO SPHI AC. unfold slot_sp, SLOT_FRAME in *. unfold SLOT_STACK in SPLO. lia. }
  destruct HJ as (fx' & regs & L & A & mem & md & es & hj & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out &
    N & Lss & kss & ob & Pb & slack & -> & HR & CORE & HPLEN & HOS & HNO & HOBL & HP0 & HPA & HFZ & HTT & HKK & HNN &
    HNFD & HN4 & RD).
  pose proof CORE as CORE0. unfold l2_core, l2_body in CORE0. destruct CORE0 as (HMR & _).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HR as HR0. unfold RG2 in HR0.
  destruct HR0 as ((B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + k)) by exact R8.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 (slot_sp E + 32)) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 0x30fc0) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 DIV10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (ss_n E - k)) by exact R23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 (slot_sp E + 16)) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 4) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (G_S + 4)) by exact F26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4)) by exact F27.
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply (p5_loop1 CNR (slot_sp E)); [exact (proj1 SPB)|exact (proj2 SPB)|exact RD]. }
  intros ms1 (can1 & (x1' & x10' & ->) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  rewrite <- SEG. apply SR_ret.
  exists fx', cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, N, Lss, kss, ob, Pb, slack.
  split; [exact HFZ|]. split; [exact HTT|]. split; [exact HKK|]. split; [exact HNN|]. split; [exact HNFD|].
  split; [exact HN4|]. split; [exact HPLEN|]. split; [exact HP0|]. split; [exact HPA|]. split; [exact HOS|].
  split; [exact HNO|]. split; [exact HOBL|].
  exists L, A, R1, mem, md, es, hj.
  split; [reflexivity|].
  split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X1|exact CORE].
Qed.

Lemma MI_op5 : forall B API LS SH SK ra empty rc fx j E CS t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  snprintf_contract -> check_no_loss_read_contract -> check_bounded_contract -> check_shape_done_contract ->
  p5c_res3_full -> l2_res_nl3 -> l2_res_se3 ->
  p5v_cnt_S -> p5v_ncs_S -> p5v_wt_S -> p5v_pend_S -> p5v_ekc_S -> p5v_ekb_S -> p5v_old_S -> p5v_out_S ->
  p5v_chain_S ->
  gone_partial_S rc B (API rc) ->
  (forall fx0 : FPState, @check_no_loss_contract fx0 rc B (API rc) pack3_form) ->
  (forall fx0 : FPState, @check_shape_ends_contract fx0 rc B (API rc) pack3_form) ->
  walk_at (ss_pl E) (t + 1) (if K <? ss_n E then K + 1 else K) ->
  MI (rc := rc) B (API rc) E RI3_reply t K 0x13ddc
    (fun _ hj no regs => no = 0 /\ disp_src 5 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (fun c' => exists k', LI (rc := rc) B (API rc) E RI3_reply (t + 1) k' c').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS t K s c HF SNP CNR CB CSD HRES HRNL HRSE V1 V2 V3 V4 V5 V6 V7 V8 V9
    HGP HCNL HCSE HW HM.
  eapply SR_bind; [exact (p5_start B API LS SH SK ra empty rc fx j E CS RI3_reply t K s c HF SNP RI3_mono HM)|].
  intros c1 (k' & HK' & HJ1).
  assert (HWk : walk_at (ss_pl E) (t + 1) k').
  { destruct HK' as [(HKn & HEq)|(HKn & HEq)]; rewrite HEq.
    - rewrite (proj2 (Z.ltb_lt K (ss_n E)) HKn) in HW. exact HW.
    - rewrite (proj2 (Z.ltb_ge K (ss_n E)) ltac:(lia)) in HW. exact HW. }
  eapply SR_bind;
    [exact (p5_call HRES V1 V2 V3 V4 V5 V6 V7 V8 V9 B API LS SH SK ra empty rc fx j E CS t k' c1 HF HGP HJ1)|].
  intros c2 HJ2.
  eapply SR_bind; [exact (p5_glue B API LS SH SK ra empty rc fx j E CS RI3_reply t k' c2 HF CNR HJ2)|].
  intros c3 H24.
  eapply SR_bind; [exact (p5_loop2 B API LS SH SK ra empty rc fx j E CS t k' c3 HF HCNL HCSE HRNL HRSE H24)|].
  intros c4 HJ4.
  exact (p5_tail B API LS SH SK ra empty rc fx j E CS RI3_reply t k' c4 HF CB CSD RI3_mono HWk HJ4).
Qed.

Theorem pass5_holds : snprintf_contract -> check_no_loss_read_contract -> check_bounded_contract ->
  check_shape_done_contract -> p5c_res3_full -> l2_res_nl3 -> l2_res_se3 ->
  p5v_cnt_S -> p5v_ncs_S -> p5v_wt_S -> p5v_pend_S -> p5v_ekc_S -> p5v_ekb_S -> p5v_old_S -> p5v_out_S ->
  p5v_chain_S ->
  (forall B API LS SH SK ra empty rc, frame_facts B API LS SH SK ra empty -> gone_partial_S rc B (API rc)) ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @check_no_loss_contract fx rc B (API rc) pack3_form /\ @check_shape_ends_contract fx rc B (API rc) pack3_form) ->
  pass_ok RI3_reply 5.
Proof.
  intros SNP CNR CB CSD HRES HRNL HRSE V1 V2 V3 V4 V5 V6 V7 V8 V9 HGP HCT B API LS SH SK ra empty rc fx j E CS HF t k c
    HL Ht Hk Hop.
  cbv beta in Hop.
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI3_reply t k c HF RI3_mono HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 5) with 0x13ddc in HM. change (disp_k E 5 k) with (k + 1) in HM.
  assert (HW5 : walk_at (ss_pl E) (t + 1) (if k + 1 <? ss_n E then k + 1 + 1 else k + 1)).
  { replace (k + 1 + 1) with (k + 2) by lia.
    exact (walk_one E t k 5 (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop
      (or_introl eq_refl)). }
  assert (FF : frame_facts B API LS SH SK ra empty) by exact (proj1 HF).
  exact (MI_op5 B API LS SH SK ra empty rc fx j E CS t (k + 1) s c' HF SNP CNR CB CSD HRES HRNL HRSE
    V1 V2 V3 V4 V5 V6 V7 V8 V9 (HGP B API LS SH SK ra empty rc FF)
    (fun fx0 => proj1 (HCT B API LS SH SK ra empty rc fx0 FF))
    (fun fx0 => proj2 (HCT B API LS SH SK ra empty rc fx0 FF))
    HW5 HM).
Qed.

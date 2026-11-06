(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its module paths and module names changed; 57 of its 110 lines of code are new or changed and 611 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv SlotSteps SlotHead SlotHeadP SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotHeadQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition RG4 (E : sstart) (t k : Z) : list rentry -> list (hsrc * nat) -> Z -> bvmap 5 word -> Prop :=
  fun _ _ no regs => tail_regs E t k regs /\ getr regs 10 = Z_to_bv 64 no.

Definition J4 {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) (E : sstart) (RI : res_inv) (t k : Z)
    (c : config) : Prop :=
  MI (rc := rc) B API E RI t k 0x14050 (RG4 E t k) c.

Lemma p5t_nout : forall segs m (mx nout cap out : word),
  rw_cells segs m G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] ->
  bytes_at segs m check_shape_done_c.G_NOUT (le8 nout).
Proof.
  intros segs m mx nout cap out ((_ & BY) & _). cbn [cells_bytes cbytes] in BY.
  rewrite !bytes_at_app, !length_le8 in BY. destruct BY as (_ & B1 & _).
  replace check_shape_done_c.G_NOUT with (G_OUTV + Z.of_nat 8) by (unfold check_shape_done_c.G_NOUT, G_OUTV; lia).
  exact B1.
Qed.

Lemma p5t_run : check_shape_done_contract -> forall
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bytes_at rsegs m check_shape_done_c.G_NOUT (le8 x10) ->
  evt rsegs (fun ms => exists a1 : word,
      ms = MS (mkR (Z_to_bv 64 0x14054) x2 x3 x4 x5 x6 x7 x8 x9 x10 a1 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
                   x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m (seg_rom rsegs))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x14050) fc None m (seg_rom rsegs)).
Proof.
  intros CSD x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m HN.
  step.
  eapply evt_cut; [eapply CSD; exact HN|].
  intros ms (a1 & ->). rewrite ret_pc_even by lia.
  step. apply evt_done. eexists. reflexivity.
Qed.

Lemma p5_tail : forall B API LS SH SK ra empty rc fx j E CS RI t k c,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  check_bounded_contract -> check_shape_done_contract -> RI_mono RI -> walk_at (ss_pl E) (t + 1) k ->
  J4 (rc := rc) B (API rc) E RI t k c ->
  SR (ms_segs B) c (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t k c HF CB CSD RIM HW HM.
  pose proof (proj1 (proj1 HF)) as SEG.
  unfold J4 in HM.
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (0x14050 =? TAIL_CHECK) || (0x14050 =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HR as (((B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22) & HA0).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GOV & _).
  assert (NB : bytes_at rsegs mem check_shape_done_c.G_NOUT (le8 nout)).
  { rewrite <- SEG. exact (p5t_nout _ _ _ _ _ _ GOV). }
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + k)) by exact R8.
  assert (E10 : reg_get regs 10 = nout).
  { transitivity (Z_to_bv 64 (bv_unsigned nout)); [exact HA0|apply Z_to_bv_bv_unsigned]. }
  assert (E19 : reg_get regs 19 = Z_to_bv 64 (slot_sp E + 32)) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 DIV10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (ss_n E - k)) by exact R23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 (slot_sp E + 16)) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 4) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (G_S + 4)) by exact F26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4)) by exact F27.
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E10, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply (p5t_run CSD). exact NB. }
  intros ms1 (can1 & (a1 & ->) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  rewrite <- SEG.
  eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t k (fun _ _ _ r => tail_regs E t k r));
    [exact HF|exact CB|intros; assumption|exact HW|]|intros c' HC; exists k; exact HC].
  exists fx', L, A, R1, mem, md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es, hj.
  split; [rewrite ?SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
  split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X1|].
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
  split; [exact HRO|]. split; [exact HIK|]. split; [exact HST|]. split; [exact HDK|]. split; [exact HGL|].
  split; [(revert Hnfd; cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia)|].
  split; [exact HOUT|].
  split; [eapply relay_at_t; [exact HREL|cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|].
  split; [exact Hes|]. split; [exact Hcost|]. exact HRI.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 229 of its 265 lines of code are new or changed and 539 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/U/Prog/SegCF/SegSlotCF.v, with its module names changed; 31 of its 55 lines of code are new or changed and 241 lines of the source are left out. *)
(* The cut-free lifts of the evt statements of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput's three evt-only segments
   (UBSan): U/Prog/SegEvt.v's evt_M01 (K13984 -> K139e4 at f = 0), evt_L02 (K13aac f -> K13c34 f) and evt_V01 (K13e90
   -> K141ec), the statements the U walks of M01, L02 and V01 prove, are used unchanged: an evt over segconf's code
   from a state with U/SlotFR's frame, which the CF frame gives (SlotInvCF.FR_u_of_cf: the agreement room
   128 <= sb_cap <= CAP_AG is stronger than the halts room). The CF slot closes the exit cut by the CF copy of
   Tac_seg.b1_seg_hb (SegCF/Tac_seg.v: FR across the run by the CF Tac_b1.b1_fr_hb; for V01, whose evt is a
   Tac_seg.seg_evt_e with the errno cell in its write set, b1_seg_hb_e over b1_fr_hb_e) as U/Prog/SegEvt.v's lifts do:
   - S_M01_cf_of_evt, S_L02_cf_of_evt, S_V01_cf_of_evt: the CF segment statements StmtsCF.S_M01, S_L02, S_V01 from
     the evt statements, under SlotInvCF.frame_facts_cf.
   The evt statements carry no frame facts of their own: at segconf's concrete instance the U walks' statements
   (frame_facts_ubsan at the halts shape -> K_<seg> -> evt_<seg>) give them (SlotTopCF.v).
   Segment lemma: the cut-free slot's lifts of the walks' evt statements. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv SegEvt SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegCF Require Import StmtsCF Tac_seg.
Import ListNotations.
Open Scope Z_scope.

Section LiftCF.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.

Lemma S_M01_cf_of_evt : (forall fx' : FPState, evt_M01 (fx:=fx') B APIf ra empty CP) -> S_M01 B APIf ra empty CP.
Proof.
  intros EVT H138e8 g c (bc & bm & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPre).
  refine (b1_seg_hb (fx:=fx') B APIf ra empty FF g (hb_cm bc bm) [(bc, C_SIZE)] L A regs mem md
           (Z_to_bv 64 0x13984) 0x139e4 (cp_K139e4 CP (g_in g) (g_p g) (g_S g) 0 bc bm) _ HF HP _
           (EVT fx' g bc bm L A regs mem md (FR_u_of_cf B APIf ra empty g _ L A regs mem md HF) HP HPre Hfrm) _ _).
  - intros x [<-|[]]. right. left. reflexivity.
  - intros ms HQ. exact HQ.
  - intros c' HC'. apply (H138e8 g c'). split; [lia | exists bc, bm; exact HC'].
Qed.

Lemma S_L02_cf_of_evt : (forall fx' : FPState, evt_L02 (fx:=fx') B APIf ra empty CP) -> S_L02 B APIf ra empty CP.
Proof.
  intros EVT f Had8 g c (bc & bm & t & nt & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPre).
  refine (b1_seg_hb (fx:=fx') B APIf ra empty FF g (hb_tcm bc bm t nt) (hb_tcm bc bm t nt) L A regs mem md
           (Z_to_bv 64 0x13aac) 0x13c34 (cp_K13c34 CP (g_in g) (g_p g) (g_S g) f bc bm t nt) _ HF HP _
           (EVT fx' g f bc bm t nt L A regs mem md (FR_u_of_cf B APIf ra empty g _ L A regs mem md HF) HP HPre Hfrm)
           _ _).
  - intros x Hx. exact Hx.
  - intros ms HQ. exact HQ.
  - intros c' HC'. apply (Had8 g c'). exists bc, bm, t, nt. exact HC'.
Qed.

Lemma S_V01_cf_of_evt : (forall fx' : FPState, evt_V01 (fx:=fx') B APIf ra empty CP) -> S_V01 B APIf ra empty CP.
Proof.
  intros EVT Hf40 g c (bc & bm & tab & ntab & mt & nmt & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPre).
  refine (b1_seg_hb_e (fx:=fx') B APIf ra empty FF g (hb_end bc bm tab ntab mt nmt) [(mt, nmt); (tab, ntab)]
           L A regs mem md (Z_to_bv 64 0x13e90) 0x141ec (cp_K141ec CP (g_in g) (g_p g) (g_S g) bc bm tab ntab mt nmt)
           _ HF HP _
           (EVT fx' g bc bm tab ntab mt nmt L A regs mem md (FR_u_of_cf B APIf ra empty g _ L A regs mem md HF)
              HP HPre Hfrm) _ _).
  - intros x [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity].
  - intros ms HQ. exact HQ.
  - intros c' HC'. apply (Hf40 g c'). exists bc, bm, tab, ntab, mt, nmt. exact HC'.
Qed.

End LiftCF.

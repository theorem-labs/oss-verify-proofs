(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 259 of its 298 lines of code are new or changed and 535 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Prog/SegSlot.v, with its module names changed; 74 of its 107 lines of code are new or changed and 265 lines of the source are left out. *)
(* The evt statements of the three evt-only segments of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain) and their
   lifts to the segment statements of Prog/LLVMFuzzerTestOneInput_c.v:
   - evt_M01 (K138a4 -> K138e8 at f = 0; writes the stack window and c: reac_segconf_init),
     evt_L02 (K13984 f -> K13ad8 f; writes the window, text, m, c and longl's written bytes),
     evt_V01 (K13cac -> K13f40; writes the window, mt, tab and the errno cell): each a Tac_seg.seg_evt (evt_V01: a
     Tac_seg.seg_evt_e, whose write set adds the errno cell [ERRNO_CELL, ERRNO_CELL + 4): reac_segconf_declared's
     reac_declared_vlan_split calls strtol, which writes errno and puts its value back) from the cut predicate of its
     entry cut to the cut predicate of its exit cut, over the cut's live harness blocks. These are what the walks of
     M01, L02 and V01 prove (an evt over segconf's code and its evt callees, with FR as the frame premise);
   - S_M01_of_evt, S_L02_of_evt, S_V01_of_evt: the slot lifts them to S_M01, S_L02, S_V01 (Tac_seg.b1_seg_evt, for V01
     b1_seg_evt_e: FR across the run by Tac_b1.b1_fr_hb / b1_fr_hb_e, the exit cut closed at the run's FP state);
   - seg_M01_of_evt, seg_L02_of_evt, seg_V01_of_evt: the same as the segment statements of SegEnd.v, for every
     instance that satisfies frame_facts_plain, from the evt statements under the segment's evt contracts K_<seg>.
   The other five segments (E01, L01, L03, M02, X01) end or start at allocator calls; their walks prove S_<seg>
   directly with the slot's steps (Tac_b1.b1_malloc_call, b1_calloc_call, Tac_b8.b8_free_call, b8_post_FR), as
   reac-pw/fuzz_role's and reac-pw/fuzz_pin's E01 and X01 do.
   Segment lemma: the statements the segment walks prove and the slot's lifts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c SegEnd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_seg.
Import ListNotations.
Open Scope Z_scope.

Section Evt.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.

(* M01, K138a4 -> K138e8 at f = 0 (0x138a4 .. 0x138e4: the NULL tests of c and m, reac_segconf_init(c)). *)
Definition evt_M01 : Prop := forall g bc bm,
  seg_evt B APIf ra empty g (hb_cm bc bm) [(bc, C_SIZE)] 0x138a4 0x138e8
    (cp_K138a4 CP (g_in g) (g_p g) (g_S g) bc bm) (cp_K138e8 CP (g_in g) (g_p g) (g_S g) 0 bc bm).

(* L02, K13984 f -> K13ad8 f (0x13984 .. 0x13ad4: memcpy, the label, m_file and the reader's parse). *)
Definition evt_L02 : Prop := forall g f bc bm t nt,
  seg_evt B APIf ra empty g (hb_tcm bc bm t nt) (hb_tcm bc bm t nt) 0x13984 0x13ad8
    (cp_K13984 CP (g_in g) (g_p g) (g_S g) f bc bm t nt) (cp_K13ad8 CP (g_in g) (g_p g) (g_S g) f bc bm t nt).

(* V01, K13cac -> K13f40 (0x13cac .. 0x13f3c: the guard, "enp1s0", m_declared, reac_segconf_declared,
   check_declared); its write set holds the errno cell too (seg_evt_e). *)
Definition evt_V01 : Prop := forall g bc bm tab ntab mt nmt,
  seg_evt_e B APIf ra empty g (hb_end bc bm tab ntab mt nmt) [(mt, nmt); (tab, ntab)] 0x13cac 0x13f40
    (cp_K13cac CP (g_in g) (g_p g) (g_S g) bc bm tab ntab mt nmt)
    (cp_K13f40 CP (g_in g) (g_p g) (g_S g) bc bm tab ntab mt nmt).

End Evt.

Section Lift.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.

Lemma S_M01_of_evt : (forall fx' : FPState, evt_M01 (fx:=fx') B APIf ra empty CP) -> S_M01 B APIf ra empty CP.
Proof.
  intros EVT H138e8 g c (bc & bm & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPre).
  apply (b1_seg_evt (fx:=fx') B APIf ra empty FF g (hb_cm bc bm) [(bc, C_SIZE)] 0x138a4 0x138e8 _ _
           L A regs mem md (EVT fx' g bc bm)).
  - intros x [<-|[]]. right. left. reflexivity.
  - exact HF.
  - exact HP.
  - exact HPre.
  - exact Hfrm.
  - intros c' HC'. apply (H138e8 g c'). split; [lia | exists bc, bm; exact HC'].
Qed.

Lemma S_L02_of_evt : (forall fx' : FPState, evt_L02 (fx:=fx') B APIf ra empty CP) -> S_L02 B APIf ra empty CP.
Proof.
  intros EVT f Had8 g c (bc & bm & t & nt & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPre).
  apply (b1_seg_evt (fx:=fx') B APIf ra empty FF g (hb_tcm bc bm t nt) (hb_tcm bc bm t nt) 0x13984 0x13ad8 _ _
           L A regs mem md (EVT fx' g f bc bm t nt)).
  - intros x Hx. exact Hx.
  - exact HF.
  - exact HP.
  - exact HPre.
  - exact Hfrm.
  - intros c' HC'. apply (Had8 g c'). exists bc, bm, t, nt. exact HC'.
Qed.

Lemma S_V01_of_evt : (forall fx' : FPState, evt_V01 (fx:=fx') B APIf ra empty CP) -> S_V01 B APIf ra empty CP.
Proof.
  intros EVT Hf40 g c (bc & bm & tab & ntab & mt & nmt & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPre).
  apply (b1_seg_evt_e (fx:=fx') B APIf ra empty FF g (hb_end bc bm tab ntab mt nmt) [(mt, nmt); (tab, ntab)]
           0x13cac 0x13f40 _ _ L A regs mem md (EVT fx' g bc bm tab ntab mt nmt)).
  - intros x [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity].
  - exact HF.
  - exact HP.
  - exact HPre.
  - exact Hfrm.
  - intros c' HC'. apply (Hf40 g c'). exists bc, bm, tab, ntab, mt, nmt. exact HC'.
Qed.

End Lift.

(* The segment statements of SegEnd.v from the evt statements, for every instance that satisfies the frame facts. *)
Section Stmts.
Variable CP : cut_preds.
Variables K_M01 K_L02 K_V01 : Prop.

Theorem seg_M01_of_evt :
  (forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
     (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
   frame_facts_plain B APIf LS SH SK ra empty -> K_M01 -> evt_M01 B APIf ra empty CP) ->
  seg_M01_stmt CP K_M01.
Proof.
  intros EVT fx rc B APIf LS SH SK ra empty FF K.
  apply (S_M01_of_evt B APIf ra empty CP FF). intros fx'. exact (EVT fx' rc B APIf LS SH SK ra empty FF K).
Qed.

Theorem seg_L02_of_evt :
  (forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
     (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
   frame_facts_plain B APIf LS SH SK ra empty -> K_L02 -> evt_L02 B APIf ra empty CP) ->
  seg_L02_stmt CP K_L02.
Proof.
  intros EVT fx rc B APIf LS SH SK ra empty FF K.
  apply (S_L02_of_evt B APIf ra empty CP FF). intros fx'. exact (EVT fx' rc B APIf LS SH SK ra empty FF K).
Qed.

Theorem seg_V01_of_evt :
  (forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
     (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
   frame_facts_plain B APIf LS SH SK ra empty -> K_V01 -> evt_V01 B APIf ra empty CP) ->
  seg_V01_stmt CP K_V01.
Proof.
  intros EVT fx rc B APIf LS SH SK ra empty FF K.
  apply (S_V01_of_evt B APIf ra empty CP FF). intros fx'. exact (EVT fx' rc B APIf LS SH SK ra empty FF K).
Qed.

End Stmts.

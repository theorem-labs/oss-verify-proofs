(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 223 of its 256 lines of code are new or changed and 541 lines of the source are left out. *)
(* Segment X01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): [0x13f40, 0x13f9c], the
   four frees and the epilogue. K13f40 -> RET (Prog/LLVMFuzzerTestOneInput_c.v's S_X01 at Seg/SegWalkMainA.v's CPseg).
   The cut is at its own FP state (Tac_b8.b8_cut_open): every step below runs at it. P_K13f40 (Prog/seg_cuts.v) gives
   s4 = mt, s3 = tab, s0 = m, s1 = c. Each free is of the head block of hb (SlotInv.hb_end = [mt; tab; m; c]) through
   Tac_b8.b8_free_call with hb1 = [] (free at 0x16a3c = frame_facts_plain's ms_free), and the callee-saved registers
   s3, s0, s1 survive each free (its regs_preserved):
     0x13f40 `mv a0,s4`, 0x13f44 `jal free` (ra 0x13f48): free(mt), hb -> [tab; m; c];
     0x13f48 `mv a0,s3`, 0x13f4c `jal free` (ra 0x13f50): free(tab), hb -> [m; c];
     0x13f50 `mv a0,s0`, 0x13f54 `jal free` (ra 0x13f58): free(m), hb -> [c];
     0x13f58 `mv a0,s1`, 0x13f5c `jal free` (ra 0x13f60): free(c), hb -> [].
   Then 0x13f60 `mv a0,zero`, the thirteen restores ra, s0 .. s11 from [sp + 0x68, sp + 0xd0) = the saved bytes FR
   keeps at S - 104 (0x13f64 .. 0x13f94), 0x13f98 `addi sp,sp,0xd0`, 0x13f9c `ret`: Post by Tac_b8.b8_post_FR at the
   cut's FP state (FR with hb = [], a0 = 0; sp, gp, tp from FR, s0 .. s11 from the saved bytes; RES_END by resb_end).
   Template: reac-pw/fuzz_role's Prog/Seg/X01.v (commit cb8205fb6109; two frees there), with
   segconf's pcs, its four frees and frame 208.
   Part of the proof of LLVMFuzzerTestOneInput (segment X01 of its walk); no released proof of fuzz_segconf's
   LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c SegEnd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_slot Tac_b8 SegWalkMainA.
Import ListNotations.
Open Scope Z_scope.

(* 0x13f40 `mv a0,s4`; 0x13f44 `jal free`. *)
Lemma kX01a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13f48) x2 x3 x4 x5 x6 x7 x8 x9 x20 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x16a3c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13f40) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x13f48 `mv a0,s3`; 0x13f4c `jal free`. *)
Lemma kX01b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13f50) x2 x3 x4 x5 x6 x7 x8 x9 x19 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x16a3c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13f48) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x13f50 `mv a0,s0`; 0x13f54 `jal free`. *)
Lemma kX01c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13f58) x2 x3 x4 x5 x6 x7 x8 x9 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x16a3c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13f50) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x13f58 `mv a0,s1`; 0x13f5c `jal free`. *)
Lemma kX01d : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13f60) x2 x3 x4 x5 x6 x7 x8 x9 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x16a3c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13f58) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x13f60 `mv a0,zero`; the restores of ra, s0 .. s11 from [sp + 0x68, sp + 0xd0); `addi sp,sp,0xd0`; `ret`. *)
Lemma kX01e : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z)
    (r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : word),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 208 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 0xc8)) 8 = Some (le8 r1) ->
  ov_read_bytes rsegs m (wa (sp0 + 0xc0)) 8 = Some (le8 r8) ->
  ov_read_bytes rsegs m (wa (sp0 + 0xb8)) 8 = Some (le8 r9) ->
  ov_read_bytes rsegs m (wa (sp0 + 0xb0)) 8 = Some (le8 r18) ->
  ov_read_bytes rsegs m (wa (sp0 + 0xa8)) 8 = Some (le8 r19) ->
  ov_read_bytes rsegs m (wa (sp0 + 0xa0)) 8 = Some (le8 r20) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x98)) 8 = Some (le8 r21) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x90)) 8 = Some (le8 r22) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x88)) 8 = Some (le8 r23) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x80)) 8 = Some (le8 r24) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x78)) 8 = Some (le8 r25) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x70)) 8 = Some (le8 r26) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x68)) 8 = Some (le8 r27) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR r1 (Z_to_bv 64 (sp0 + 208)) x3 x4 x5 x6 x7 r8 r9 (Z_to_bv 64 0) x11 x12 x13 x14 x15
                           x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 x28 x29 x30 x31) F (ret_pc r1) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13f60) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 E2 H0 H1
    R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
  subst x2.
  do 16 step.
  apply evt_done. reflexivity.
Qed.

Section X01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.

(* The saved bytes at S - 104: s11, s10, .., s2, s1, s0, ra. *)
Lemma x01_saved_split : forall g mem, bytes_at rsegs mem (g_S g - SLOT_SAVE) (saved_bytes ra g) ->
  bytes_at rsegs mem (g_S g - 104) (le8 (getr (g_regs g) 27)) /\
  bytes_at rsegs mem (g_S g - 96) (le8 (getr (g_regs g) 26)) /\
  bytes_at rsegs mem (g_S g - 88) (le8 (getr (g_regs g) 25)) /\
  bytes_at rsegs mem (g_S g - 80) (le8 (getr (g_regs g) 24)) /\
  bytes_at rsegs mem (g_S g - 72) (le8 (getr (g_regs g) 23)) /\
  bytes_at rsegs mem (g_S g - 64) (le8 (getr (g_regs g) 22)) /\
  bytes_at rsegs mem (g_S g - 56) (le8 (getr (g_regs g) 21)) /\
  bytes_at rsegs mem (g_S g - 48) (le8 (getr (g_regs g) 20)) /\
  bytes_at rsegs mem (g_S g - 40) (le8 (getr (g_regs g) 19)) /\
  bytes_at rsegs mem (g_S g - 32) (le8 (getr (g_regs g) 18)) /\
  bytes_at rsegs mem (g_S g - 24) (le8 (getr (g_regs g) 9)) /\
  bytes_at rsegs mem (g_S g - 16) (le8 (getr (g_regs g) 8)) /\
  bytes_at rsegs mem (g_S g - 8) (le8 (Z_to_bv 64 ra)).
Proof.
  intros g mem H. unfold saved_bytes, SLOT_SAVE in H.
  repeat (apply bytes_at_app in H; destruct H as [?H H]; rewrite length_le8 in H).
  repeat match goal with |- _ /\ _ => split end;
    match goal with H : bytes_at _ _ ?a (le8 ?v) |- bytes_at _ _ ?b (le8 ?v) => replace b with a by lia; exact H end.
Qed.

Lemma seg_X01 : S_X01 B APIf ra empty CPseg.
Proof.
  intros g c (bc & bm & tab & ntab & mt & nmt & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros fx' L A regs mem md Hfrm HF HP HPc.
  destruct HPc as (_ & _ & H20 & H19 & H8 & H9).
  unfold hb_end, hb_tab, hb_cm in HF, HP.
  (* free(mt): the head of [mt; tab; m; c]. *)
  assert (Hin : In (mt, nmt) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kX01a | intros regs_c HG].
  rewrite <- Ep in HF, HP.
  apply (b8_free_call B APIf ra empty FF g [] [(tab, ntab); (bm, M_SIZE); (bc, C_SIZE)] L A regs mem md regs_c
    p nmt).
  - exact HF.
  - exact HP.
  - exact Hp.
  - b8rg HG.
  - b8rg HG.
  - b8rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG. transitivity (getr regs 20); [reflexivity|]. rewrite Ep. exact H20.
  - intros L1 A1 regs1 mem1 md1 HF1 HP1 RP1 _ _.
    replace (getr regs_c 1) with (Z_to_bv 64 0x13f48) by (rewrite HG; reflexivity).
    cbn [app] in HF1, HP1.
    assert (E19 : getr regs1 19 = Z_to_bv 64 tab).
    { etransitivity; [exact (RP1 19 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact H19. }
    assert (E8 : getr regs1 8 = Z_to_bv 64 bm).
    { etransitivity; [exact (RP1 8 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact H8. }
    assert (E9 : getr regs1 9 = Z_to_bv 64 bc).
    { etransitivity; [exact (RP1 9 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact H9. }
    clear H20 H19 H8 H9.
    (* free(tab): the head of [tab; m; c]. *)
    assert (Hin2 : In (tab, ntab) (blocks L1 A1))
      by (apply (Permutation_in _ (Permutation_sym HP1)); left; reflexivity).
    destruct (b8_in_blocks L1 A1 _ _ Hin2) as (p2 & Hp2 & Ep2).
    eapply (b8_run_to B APIf ra empty FF); [exact HF1 | unfold rmk; apply kX01b | intros regs_c2 HG2].
    rewrite <- Ep2 in HF1, HP1.
    apply (b8_free_call B APIf ra empty FF g [] [(bm, M_SIZE); (bc, C_SIZE)] L1 A1 regs1 mem1 md1 regs_c2 p2 ntab).
    + exact HF1.
    + exact HP1.
    + exact Hp2.
    + b8rg HG2.
    + b8rg HG2.
    + b8rg HG2.
    + rewrite HG2. apply ret_ok_even. reflexivity.
    + rewrite HG2. transitivity (getr regs1 19); [reflexivity|]. rewrite Ep2. exact E19.
    + intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 _ _.
      replace (getr regs_c2 1) with (Z_to_bv 64 0x13f50) by (rewrite HG2; reflexivity).
      cbn [app] in HF2, HP2.
      assert (E8' : getr regs2 8 = Z_to_bv 64 bm).
      { etransitivity; [exact (RP2 8 ltac:(unfold callee_saved; lia))|]. rewrite HG2. exact E8. }
      assert (E9' : getr regs2 9 = Z_to_bv 64 bc).
      { etransitivity; [exact (RP2 9 ltac:(unfold callee_saved; lia))|]. rewrite HG2. exact E9. }
      clear E19 E8 E9.
      (* free(m): the head of [m; c]. *)
      assert (Hin3 : In (bm, M_SIZE) (blocks L2 A2))
        by (apply (Permutation_in _ (Permutation_sym HP2)); left; reflexivity).
      destruct (b8_in_blocks L2 A2 _ _ Hin3) as (p3 & Hp3 & Ep3).
      eapply (b8_run_to B APIf ra empty FF); [exact HF2 | unfold rmk; apply kX01c | intros regs_c3 HG3].
      rewrite <- Ep3 in HF2, HP2.
      apply (b8_free_call B APIf ra empty FF g [] [(bc, C_SIZE)] L2 A2 regs2 mem2 md2 regs_c3 p3 M_SIZE).
      * exact HF2.
      * exact HP2.
      * exact Hp3.
      * b8rg HG3.
      * b8rg HG3.
      * b8rg HG3.
      * rewrite HG3. apply ret_ok_even. reflexivity.
      * rewrite HG3. transitivity (getr regs2 8); [reflexivity|]. rewrite Ep3. exact E8'.
      * intros L3 A3 regs3 mem3 md3 HF3 HP3 RP3 _ _.
        replace (getr regs_c3 1) with (Z_to_bv 64 0x13f58) by (rewrite HG3; reflexivity).
        cbn [app] in HF3, HP3.
        assert (E9'' : getr regs3 9 = Z_to_bv 64 bc).
        { etransitivity; [exact (RP3 9 ltac:(unfold callee_saved; lia))|]. rewrite HG3. exact E9'. }
        clear E8' E9'.
        (* free(c): the last block. *)
        assert (Hin4 : In (bc, C_SIZE) (blocks L3 A3))
          by (apply (Permutation_in _ (Permutation_sym HP3)); left; reflexivity).
        destruct (b8_in_blocks L3 A3 _ _ Hin4) as (p4 & Hp4 & Ep4).
        eapply (b8_run_to B APIf ra empty FF); [exact HF3 | unfold rmk; apply kX01d | intros regs_c4 HG4].
        rewrite <- Ep4 in HF3, HP3.
        apply (b8_free_call B APIf ra empty FF g [] [] L3 A3 regs3 mem3 md3 regs_c4 p4 C_SIZE).
        -- exact HF3.
        -- exact HP3.
        -- exact Hp4.
        -- b8rg HG4.
        -- b8rg HG4.
        -- b8rg HG4.
        -- rewrite HG4. apply ret_ok_even. reflexivity.
        -- rewrite HG4. transitivity (getr regs3 9); [reflexivity|]. rewrite Ep4. exact E9''.
        -- intros L4 A4 regs4 mem4 md4 HF4 HP4 _ _ _.
           replace (getr regs_c4 1) with (Z_to_bv 64 0x13f60) by (rewrite HG4; reflexivity).
           cbn [app] in HF4, HP4.
           (* The epilogue. *)
           pose proof HF4 as (HGV & Hsp & Hgp & Htp & HSV & _).
           pose proof (b8_GV_S B empty g HGV) as (_ & HS).
           pose proof alloc_ceiling_value as HAC.
           destruct (x01_saved_split g mem4 HSV)
             as (B27 & B26 & B25 & B24 & B23 & B22 & B21 & B20 & B19 & B18 & B9 & B8 & B1).
           unfold fsp, SLOT_FRAME in Hsp. unfold SLOT_K, SLOT_STACK in HS.
           eapply (b8_run_to B APIf ra empty FF); [exact HF4 | | intros regs5 HG5].
           ++ unfold rmk. eapply kX01e with (sp0 := g_S g - 208).
              ** exact Hsp.
              ** lia.
              ** lia.
              ** replace (g_S g - 208 + 0xc8) with (g_S g - 8) by lia. apply b8_bytes_le8. exact B1.
              ** replace (g_S g - 208 + 0xc0) with (g_S g - 16) by lia. apply b8_bytes_le8. exact B8.
              ** replace (g_S g - 208 + 0xb8) with (g_S g - 24) by lia. apply b8_bytes_le8. exact B9.
              ** replace (g_S g - 208 + 0xb0) with (g_S g - 32) by lia. apply b8_bytes_le8. exact B18.
              ** replace (g_S g - 208 + 0xa8) with (g_S g - 40) by lia. apply b8_bytes_le8. exact B19.
              ** replace (g_S g - 208 + 0xa0) with (g_S g - 48) by lia. apply b8_bytes_le8. exact B20.
              ** replace (g_S g - 208 + 0x98) with (g_S g - 56) by lia. apply b8_bytes_le8. exact B21.
              ** replace (g_S g - 208 + 0x90) with (g_S g - 64) by lia. apply b8_bytes_le8. exact B22.
              ** replace (g_S g - 208 + 0x88) with (g_S g - 72) by lia. apply b8_bytes_le8. exact B23.
              ** replace (g_S g - 208 + 0x80) with (g_S g - 80) by lia. apply b8_bytes_le8. exact B24.
              ** replace (g_S g - 208 + 0x78) with (g_S g - 88) by lia. apply b8_bytes_le8. exact B25.
              ** replace (g_S g - 208 + 0x70) with (g_S g - 96) by lia. apply b8_bytes_le8. exact B26.
              ** replace (g_S g - 208 + 0x68) with (g_S g - 104) by lia. apply b8_bytes_le8. exact B27.
           ++ rewrite (b8_ret_pc_ra ra (b8_ra B APIf ra empty FF)). apply SR_ret.
              apply (b8_post_FR B APIf ra empty FF g L4 A4 regs4 regs5 mem4 md4 Hfrm HF4 HP4).
              ** b8rg HG5.
              ** intros r Hr. unfold callee_saved in Hr.
                 assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                   r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
                 destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
                   rewrite HG5; try reflexivity.
                 --- destruct HGV as (_ & _ & _ & _ & _ & _ & _ & E2 & _).
                     transitivity (Z_to_bv 64 (g_S g)); [|symmetry; exact E2].
                     transitivity (Z_to_bv 64 (g_S g - 208 + 208)); [reflexivity | f_equal; lia].
                 --- exact Hgp.
                 --- exact Htp.
Qed.

End X01.

Theorem seg_X01_holds : seg_X01_stmt CPseg.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF.
  exact (seg_X01 B APIf ra empty FF).
Qed.

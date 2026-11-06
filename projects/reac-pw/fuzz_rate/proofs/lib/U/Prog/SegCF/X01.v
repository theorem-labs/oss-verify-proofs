(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 197 of its 226 lines of code are new or changed and 546 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/X01.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_role's U/Prog/SegCF/X01.v, as libreac/fuzz_ctrl's released
   U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg -> SegCF, the
   segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the allocator
   contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Segment X01 of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (UBSan): [0x14660, 0x146b4], the three frees and the
   epilogue. K14660 -> RET (U/Prog/LLVMFuzzerTestOneInput_c.v's S_X01).
   The plain segment (lib/Prog/Seg/X01.v) with the UBSan numbers: the frame is 592 bytes, free is 0x1693c (=
   frame_facts_cf's ms_free). 0x14660 `mv a0,s4`, 0x14664 `jal free` (ra 0x14668) frees the buf block (the head
   of hb_buf) through Tac_b8.b8_free_call; 0x14668 `mv a0,s3`, 0x1466c `jal free` (ra 0x14670) frees the pod block
   (the head of [(pod, g_len g); (pp, 19744)]); 0x14670 `ld a0,0xd8(sp)`, 0x14674 `jal free` (ra 0x14678) frees the
   pp block (one-block free), leaving FR with hb = []. pp comes from the frame cell sp + 0xd8 of K14660: the two
   frees before keep every byte from the frame's sp up (b8_free_call's continuation; Tac_b8.b8_ba_above). Then
   0x14678 `mv a0,zero`, the thirteen restores ra, s0 .. s11 from the saved bytes at S - 104 (0x1467c .. 0x146ac),
   0x146b0 `addi sp,sp,0x250`, 0x146b4 `ret`: Post by Tac_b8.b8_post_FR at the cut's FP state. No trap is reached in
   this stretch.
   Adapted from reac-pw/fuzz_role's U/Prog/Seg/X01.v (two frees there).
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0 Contract FrameAPI KindBGlue SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import Tac_slot Tac_b8.
Import ListNotations.
Open Scope Z_scope.

(* 0x14660 `mv a0,s4`; 0x14664 `jal free`. *)
Lemma kX01a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x14668) x2 x3 x4 x5 x6 x7 x8 x9 x20 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1693c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x14660) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x14668 `mv a0,s3`; 0x1466c `jal free`. *)
Lemma kX01c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x14670) x2 x3 x4 x5 x6 x7 x8 x9 x19 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1693c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x14668) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x14670 `ld a0,0xd8(sp)`; 0x14674 `jal free`. *)
Lemma kX01e : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z)
    (v : word),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 592 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 0xd8)) 8 = Some (le8 v) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x14678) x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1693c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x14670) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 v E2 H0 H1 RV.
  subst x2.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x14678 `mv a0,zero`; the restores of ra, s0 .. s11 from [sp + 0x1e8, sp + 0x250); `addi sp,sp,0x250`; `ret`. *)
Lemma kX01b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z)
    (r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : word),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 592 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x248)) 8 = Some (le8 r1) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x240)) 8 = Some (le8 r8) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x238)) 8 = Some (le8 r9) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x230)) 8 = Some (le8 r18) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x228)) 8 = Some (le8 r19) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x220)) 8 = Some (le8 r20) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x218)) 8 = Some (le8 r21) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x210)) 8 = Some (le8 r22) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x208)) 8 = Some (le8 r23) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x200)) 8 = Some (le8 r24) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1f8)) 8 = Some (le8 r25) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1f0)) 8 = Some (le8 r26) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1e8)) 8 = Some (le8 r27) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR r1 (Z_to_bv 64 (sp0 + 592)) x3 x4 x5 x6 x7 r8 r9 (Z_to_bv 64 0) x11 x12 x13 x14 x15
                           x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 x28 x29 x30 x31) F (ret_pc r1) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x14678) fc None m ro).
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
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.
Hypothesis FREE : free_contract_cf B (APIf rc).

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

Lemma seg_X01 : S_X01 B APIf ra empty.
Proof.
  pose proof FREE as HFREE.
  pose proof (b8_segs B APIf ra empty FF) as ES.
  intros g c (pp & pod & cb & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros fx' L A regs mem md Hfrm HF HP (H20 & H19 & HC80).
  unfold hb_buf in HF, HP.
  (* free(buf): the head block (cb, g_bl g). *)
  assert (Hin : In (cb, g_bl g) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kX01a | intros regs_c HG].
  rewrite <- Ep in HF, HP.
  apply (b8_free_call B APIf ra empty FF g [] [(pod, g_len g); (pp, POD_PROPS)] L A regs mem md regs_c p (g_bl g)).
  - exact HF.
  - exact HP.
  - exact Hp.
  - b8rg HG.
  - b8rg HG.
  - b8rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG. transitivity (getr regs 20); [reflexivity|]. rewrite Ep. exact H20.
  - intros L' A' regs' mem' md' HF' HP' RP' HK'.
    replace (getr regs_c 1) with (Z_to_bv 64 0x14668) by (rewrite HG; reflexivity).
    cbn [app] in HF', HP'.
    rewrite ES in HK'.
    assert (C1 : bytes_at rsegs mem' (fsp g + 0xd8) (le8 (Z_to_bv 64 pp))).
    { apply (b8_ba_above mem mem' (g_S g - 592) _ _ HC80); [unfold fsp, SLOT_FRAME; lia | exact HK']. }
    (* free(pod): the head block (pod, g_len g) of [(pod, g_len g); (pp, 19744)]. *)
    assert (Hin2 : In (pod, g_len g) (blocks L' A'))
      by (apply (Permutation_in _ (Permutation_sym HP')); left; reflexivity).
    destruct (b8_in_blocks L' A' _ _ Hin2) as (p2 & Hp2 & Ep2).
    assert (E19 : getr regs' 19 = Z_to_bv 64 pod).
    { etransitivity; [exact (RP' 19 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact H19. }
    eapply (b8_run_to B APIf ra empty FF); [exact HF' | unfold rmk; apply kX01c | intros regs_c2 HG2].
    rewrite <- Ep2 in HF', HP'.
    apply (b8_free_call B APIf ra empty FF g [] [(pp, POD_PROPS)] L' A' regs' mem' md' regs_c2 p2 (g_len g)).
    + exact HF'.
    + exact HP'.
    + exact Hp2.
    + b8rg HG2.
    + b8rg HG2.
    + b8rg HG2.
    + rewrite HG2. apply ret_ok_even. reflexivity.
    + rewrite HG2. transitivity (getr regs' 19); [reflexivity|]. rewrite Ep2. exact E19.
    + intros L'' A'' regs'' mem'' md'' HF'' HP'' RP'' HK''.
      replace (getr regs_c2 1) with (Z_to_bv 64 0x14670) by (rewrite HG2; reflexivity).
      cbn [app] in HF'', HP''.
      rewrite ES in HK''.
      assert (C2 : bytes_at rsegs mem'' (fsp g + 0xd8) (le8 (Z_to_bv 64 pp))).
      { apply (b8_ba_above mem' mem'' (g_S g - 592) _ _ C1); [unfold fsp, SLOT_FRAME; lia | exact HK'']. }
      (* free(pp): pp reloaded from the cell sp + 0xd8; the one-block free. *)
      assert (Hin3 : In (pp, POD_PROPS) (blocks L'' A''))
        by (apply (Permutation_in _ (Permutation_sym HP'')); left; reflexivity).
      destruct (b8_in_blocks L'' A'' _ _ Hin3) as (p3 & Hp3 & Ep3).
      pose proof HF'' as (HGV0 & Hsp0 & _).
      pose proof (b8_GV_S B empty g HGV0) as (_ & HS).
      pose proof alloc_ceiling_value as HAC.
      unfold fsp, SLOT_FRAME in Hsp0, C2. unfold SLOT_K, SLOT_STACK in HS.
      eapply (b8_run_to B APIf ra empty FF); [exact HF'' | | intros regs_c3 HG3].
      { unfold rmk. eapply kX01e with (sp0 := g_S g - 592) (v := Z_to_bv 64 pp).
        - exact Hsp0.
        - lia.
        - lia.
        - apply b8_bytes_le8. exact C2. }
      rewrite <- Ep3 in HF'', HP''.
      apply (b8_free_call B APIf ra empty FF g [] [] L'' A'' regs'' mem'' md'' regs_c3 p3 POD_PROPS).
      * exact HF''.
      * exact HP''.
      * exact Hp3.
      * b8rg HG3.
      * b8rg HG3.
      * b8rg HG3.
      * rewrite HG3. apply ret_ok_even. reflexivity.
      * rewrite HG3. transitivity (Z_to_bv 64 pp); [reflexivity|]. rewrite Ep3. reflexivity.
      * intros L3 A3 regs3 mem3 md3 HF3 HP3 RP3 _.
        replace (getr regs_c3 1) with (Z_to_bv 64 0x14678) by (rewrite HG3; reflexivity).
        pose proof HF3 as (HGV & Hsp & Hgp & Htp & HSV & _).
        destruct (x01_saved_split g mem3 HSV)
          as (B27 & B26 & B25 & B24 & B23 & B22 & B21 & B20 & B19 & B18 & B9 & B8 & B1).
        unfold fsp, SLOT_FRAME in Hsp.
        eapply (b8_run_to B APIf ra empty FF); [exact HF3 | | intros regs4 HG4].
        -- unfold rmk. eapply kX01b with (sp0 := g_S g - 592).
           ++ exact Hsp.
           ++ lia.
           ++ lia.
           ++ replace (g_S g - 592 + 0x248) with (g_S g - 8) by lia. apply b8_bytes_le8. exact B1.
           ++ replace (g_S g - 592 + 0x240) with (g_S g - 16) by lia. apply b8_bytes_le8. exact B8.
           ++ replace (g_S g - 592 + 0x238) with (g_S g - 24) by lia. apply b8_bytes_le8. exact B9.
           ++ replace (g_S g - 592 + 0x230) with (g_S g - 32) by lia. apply b8_bytes_le8. exact B18.
           ++ replace (g_S g - 592 + 0x228) with (g_S g - 40) by lia. apply b8_bytes_le8. exact B19.
           ++ replace (g_S g - 592 + 0x220) with (g_S g - 48) by lia. apply b8_bytes_le8. exact B20.
           ++ replace (g_S g - 592 + 0x218) with (g_S g - 56) by lia. apply b8_bytes_le8. exact B21.
           ++ replace (g_S g - 592 + 0x210) with (g_S g - 64) by lia. apply b8_bytes_le8. exact B22.
           ++ replace (g_S g - 592 + 0x208) with (g_S g - 72) by lia. apply b8_bytes_le8. exact B23.
           ++ replace (g_S g - 592 + 0x200) with (g_S g - 80) by lia. apply b8_bytes_le8. exact B24.
           ++ replace (g_S g - 592 + 0x1f8) with (g_S g - 88) by lia. apply b8_bytes_le8. exact B25.
           ++ replace (g_S g - 592 + 0x1f0) with (g_S g - 96) by lia. apply b8_bytes_le8. exact B26.
           ++ replace (g_S g - 592 + 0x1e8) with (g_S g - 104) by lia. apply b8_bytes_le8. exact B27.
        -- rewrite (b8_ret_pc_ra ra (b8_ra B APIf ra empty FF)). apply SR_ret.
           apply (b8_post_FR B APIf ra empty g L3 A3 regs3 regs4 mem3 md3 Hfrm HF3 HP3).
           ++ b8rg HG4.
           ++ intros r Hr. unfold callee_saved in Hr.
              assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
              destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; rewrite HG4;
                try reflexivity.
              ** destruct HGV as (_ & _ & _ & _ & _ & _ & _ & E2 & _).
                 transitivity (Z_to_bv 64 (g_S g)); [|symmetry; exact E2].
                 transitivity (Z_to_bv 64 (g_S g - 592 + 592)); [reflexivity | f_equal; lia].
              ** exact Hgp.
              ** exact Htp.
Qed.

End X01.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 292 of its 327 lines of code are new or changed and 540 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/X01.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_role's U/Prog/SegCF/X01.v, as libreac/fuzz_ctrl's
   released U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg ->
   SegCF, the segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the
   allocator contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Segment X01 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan): [0x1482c, 0x14898], the four frees and the
   epilogue. K1482c -> RET (U/Prog/LLVMFuzzerTestOneInput_c.v's S_X01).
   reac-pw/fuzz_role's U/Prog/Seg/X01.v with headamp's numbers: the frame is 608 bytes, free is 0x167fc, and four
   blocks are freed, each the head of hb, through Tac_b8.b8_free_call (hb1 = []):
   0x1482c `mv a0,s7`, 0x14830 `jal free` (ra 0x14834) frees first; 0x14834 `mv a0,s3`, 0x14838 `jal free`
   (ra 0x1483c) frees out; 0x1483c `mv a0,s1`, 0x14840 `jal free` (ra 0x14844) frees pod; 0x14844 `ld a0,0x70(sp)`
   reads pp from its frame cell (each free keeps the bytes from sp up), 0x14848 `jal free` (ra 0x1484c) frees pp,
   leaving FR with hb = []. Then 0x1484c `mv a0,zero`, the thirteen restores ra, s0 .. s11 from the saved bytes at
   S - 104 (0x14850 .. 0x14880), the four `fld` of fs0 .. fs3 from [S - 136, S - 104) (0x14884 .. 0x14890; those
   cells lie in FR's stack window, so they read some bytes), 0x14894 `addi sp,sp,0x260`, 0x14898 `ret`. The `fld`
   write the FP registers, so the epilogue runs by Tac_slot.sl_run_fp on the normalized memory (it writes no byte;
   FR carries over by sl_fr_run with an empty write set) and Post closes by Tac_b8.b8_post_FR at the FP state the
   run ends at (fcsr unchanged, so rounding mode 0). No trap is reached in this stretch. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Cells.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0 Contract FrameAPI KindBGlue SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF Require Import Tac_slot Tac_b8.
Import ListNotations.
Open Scope Z_scope.

(* 0x1482c `mv a0,s7`; 0x14830 `jal free`. *)
Lemma kX01a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x14834) x2 x3 x4 x5 x6 x7 x8 x9 x23 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x167fc) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x1482c) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x14834 `mv a0,s3`; 0x14838 `jal free`. *)
Lemma kX01c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1483c) x2 x3 x4 x5 x6 x7 x8 x9 x19 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x167fc) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x14834) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x1483c `mv a0,s1`; 0x14840 `jal free`. *)
Lemma kX01d : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x14844) x2 x3 x4 x5 x6 x7 x8 x9 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x167fc) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x1483c) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x14844 `ld a0,0x70(sp)`; 0x14848 `jal free`. *)
Lemma kX01e : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z) (v : word),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 608 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x70)) 8 = Some (le8 v) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1484c) x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x167fc) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x14844) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 v E2 H0 H1 RV.
  subst x2.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x1484c `mv a0,zero`; the restores of ra, s0 .. s11 from [sp + 0x1f8, sp + 0x260); the `fld` of fs0 .. fs3 from
   [sp + 0x1d8, sp + 0x1f8); `addi sp,sp,0x260`; `ret`. The FP registers end as the `fld` leave them. *)
Lemma kX01b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z)
    (r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : word) (f0 f1 f2 f3 : list byte),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 608 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x258)) 8 = Some (le8 r1) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x250)) 8 = Some (le8 r8) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x248)) 8 = Some (le8 r9) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x240)) 8 = Some (le8 r18) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x238)) 8 = Some (le8 r19) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x230)) 8 = Some (le8 r20) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x228)) 8 = Some (le8 r21) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x220)) 8 = Some (le8 r22) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x218)) 8 = Some (le8 r23) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x210)) 8 = Some (le8 r24) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x208)) 8 = Some (le8 r25) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x200)) 8 = Some (le8 r26) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1f8)) 8 = Some (le8 r27) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1f0)) 8 = Some f0 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1e8)) 8 = Some f1 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1e0)) 8 = Some f2 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1d8)) 8 = Some f3 ->
  Exec.evt rsegs
    (fun ms' => exists F' : bvmap 5 word,
       ms' = MS (mkR r1 (Z_to_bv 64 (sp0 + 608)) x3 x4 x5 x6 x7 r8 r9 (Z_to_bv 64 0) x11 x12 x13 x14 x15
                     x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 x28 x29 x30 x31) F' (ret_pc r1) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x1484c) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 f0 f1 f2 f3 E2 H0 H1
    R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 Q0 Q1 Q2 Q3.
  subst x2.
  do 20 step.
  apply evt_done. eexists. reflexivity.
Qed.

(* An 8-byte cell of a stack region reads some bytes. *)
Lemma x01_rd8 : forall m lo hi a, Frame.stk rsegs m lo hi -> lo <= a -> a + 8 <= hi ->
  exists bs, ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m lo hi a ST H1 H2.
  destruct (sl_rw_of_stk m lo hi a 8 ST H1 ltac:(lia)) as (bs & HRW).
  exists bs. pose proof HRW as [[[Hl _] _] _]. cbn [Cells.cells_wf Cells.cell_wf] in Hl.
  pose proof (b8_bytes_ovr rsegs m a bs (sl_rw_bytes m a 8 bs HRW)) as HR. rewrite Hl in HR. exact HR.
Qed.

(* Thirteen 8-byte cells at a, a + 8, .., a + 96 (the saved s11, s10, .., s2, s1, s0, ra at a = S - 104). *)
Lemma x01_saved_split : forall mem a (r27 r26 r25 r24 r23 r22 r21 r20 r19 r18 r9 r8 r1 : word),
  bytes_at rsegs mem a (le8 r27 ++ le8 r26 ++ le8 r25 ++ le8 r24 ++ le8 r23 ++ le8 r22 ++ le8 r21 ++ le8 r20 ++
                        le8 r19 ++ le8 r18 ++ le8 r9 ++ le8 r8 ++ le8 r1) ->
  bytes_at rsegs mem a (le8 r27) /\ bytes_at rsegs mem (a + 8) (le8 r26) /\
  bytes_at rsegs mem (a + 16) (le8 r25) /\ bytes_at rsegs mem (a + 24) (le8 r24) /\
  bytes_at rsegs mem (a + 32) (le8 r23) /\ bytes_at rsegs mem (a + 40) (le8 r22) /\
  bytes_at rsegs mem (a + 48) (le8 r21) /\ bytes_at rsegs mem (a + 56) (le8 r20) /\
  bytes_at rsegs mem (a + 64) (le8 r19) /\ bytes_at rsegs mem (a + 72) (le8 r18) /\
  bytes_at rsegs mem (a + 80) (le8 r9) /\ bytes_at rsegs mem (a + 88) (le8 r8) /\
  bytes_at rsegs mem (a + 96) (le8 r1).
Proof.
  intros mem a r27 r26 r25 r24 r23 r22 r21 r20 r19 r18 r9 r8 r1 H.
  repeat (apply bytes_at_app in H; destruct H as [?H H]; rewrite length_le8 in H).
  repeat match goal with |- _ /\ _ => split end;
    match goal with H : bytes_at _ _ ?x (le8 ?v) |- bytes_at _ _ ?y (le8 ?v) => replace y with x by lia; exact H end.
Qed.

(* An 8-byte cell at sp + 0x70 across a run that keeps every byte from sp up (a free). *)
Lemma x01_c70 : forall sp mem mem' v, 0 <= sp -> sp + 0x78 <= 2 ^ 64 ->
  bytes_at rsegs mem (sp + 0x70) (le8 v) ->
  (forall a, sp <= a < 2 ^ 64 -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  bytes_at rsegs mem' (sp + 0x70) (le8 v).
Proof.
  intros sp mem mem' v H0 H1 HB HK.
  apply (b8_ba_mbyte mem); [exact HB|]. intros i Hi. rewrite length_le8 in Hi. apply HK. lia.
Qed.

Section X01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.
Hypothesis FREE : free_contract_cf B (APIf rc).

Lemma seg_X01 : S_X01 B APIf ra empty.
Proof using fx rc B APIf LS SH SK ra empty FF FREE.
  intros g c (pp & pod & out & first & nf & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros fx' L A regs mem md Hfrm HF HP (H23 & H19 & H9 & HC70).
  unfold hb_first, hb_out, hb_pod in HF, HP.
  destruct (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp0 & _ & HSK0 & HS47).
  pose proof alloc_ceiling_value as HAC.
  pose proof (b8_segs B APIf ra empty FF) as SEGS0.
  assert (Hfsp : 0 <= fsp g /\ fsp g + 0x78 <= 2 ^ 64) by (unfold fsp, SLOT_FRAME; lia).
  (* free(first) *)
  assert (Hin : In (first, nf) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kX01a | intros regs_c HG].
  rewrite <- Ep in HF, HP.
  apply (b8_free_call B APIf ra empty FF g [] [(out, OUT_LEN (g_cap g)); (pod, g_len g); (pp, POD_PROPS)]
           L A regs mem md regs_c p nf).
  - exact HF.
  - exact HP.
  - exact Hp.
  - b8rg HG.
  - b8rg HG.
  - b8rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG. transitivity (getr regs 23); [reflexivity|]. rewrite Ep. exact H23.
  - intros L1 A1 regs1 mem1 md1 HF1 HP1 RP1 HK1.
    replace (getr regs_c 1) with (Z_to_bv 64 0x14834) by (rewrite HG; reflexivity).
    cbn [app] in HF1, HP1.
    assert (E19 : getr regs1 19 = Z_to_bv 64 out).
    { etransitivity; [exact (RP1 19 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact H19. }
    assert (E9 : getr regs1 9 = Z_to_bv 64 pod).
    { etransitivity; [exact (RP1 9 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact H9. }
    pose proof (x01_c70 (fsp g) mem mem1 _ (proj1 Hfsp) (proj2 Hfsp) HC70
                  ltac:(rewrite <- SEGS0; exact HK1)) as HC70a.
    (* free(out) *)
    assert (Hin2 : In (out, OUT_LEN (g_cap g)) (blocks L1 A1))
      by (apply (Permutation_in _ (Permutation_sym HP1)); left; reflexivity).
    destruct (b8_in_blocks L1 A1 _ _ Hin2) as (p2 & Hp2 & Ep2).
    eapply (b8_run_to B APIf ra empty FF); [exact HF1 | unfold rmk; apply kX01c | intros regs_c2 HG2].
    rewrite <- Ep2 in HF1, HP1.
    apply (b8_free_call B APIf ra empty FF g [] [(pod, g_len g); (pp, POD_PROPS)]
             L1 A1 regs1 mem1 md1 regs_c2 p2 (OUT_LEN (g_cap g))).
    + exact HF1.
    + exact HP1.
    + exact Hp2.
    + b8rg HG2.
    + b8rg HG2.
    + b8rg HG2.
    + rewrite HG2. apply ret_ok_even. reflexivity.
    + rewrite HG2. transitivity (getr regs1 19); [reflexivity|]. rewrite Ep2. exact E19.
    + intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 HK2.
      replace (getr regs_c2 1) with (Z_to_bv 64 0x1483c) by (rewrite HG2; reflexivity).
      cbn [app] in HF2, HP2.
      assert (E9b : getr regs2 9 = Z_to_bv 64 pod).
      { etransitivity; [exact (RP2 9 ltac:(unfold callee_saved; lia))|]. rewrite HG2. exact E9. }
      pose proof (x01_c70 (fsp g) mem1 mem2 _ (proj1 Hfsp) (proj2 Hfsp) HC70a
                    ltac:(rewrite <- SEGS0; exact HK2)) as HC70b.
      (* free(pod) *)
      assert (Hin3 : In (pod, g_len g) (blocks L2 A2))
        by (apply (Permutation_in _ (Permutation_sym HP2)); left; reflexivity).
      destruct (b8_in_blocks L2 A2 _ _ Hin3) as (p3 & Hp3 & Ep3).
      eapply (b8_run_to B APIf ra empty FF); [exact HF2 | unfold rmk; apply kX01d | intros regs_c3 HG3].
      rewrite <- Ep3 in HF2, HP2.
      apply (b8_free_call B APIf ra empty FF g [] [(pp, POD_PROPS)]
               L2 A2 regs2 mem2 md2 regs_c3 p3 (g_len g)).
      * exact HF2.
      * exact HP2.
      * exact Hp3.
      * b8rg HG3.
      * b8rg HG3.
      * b8rg HG3.
      * rewrite HG3. apply ret_ok_even. reflexivity.
      * rewrite HG3. transitivity (getr regs2 9); [reflexivity|]. rewrite Ep3. exact E9b.
      * intros L3 A3 regs3 mem3 md3 HF3 HP3 RP3 HK3.
        replace (getr regs_c3 1) with (Z_to_bv 64 0x14844) by (rewrite HG3; reflexivity).
        cbn [app] in HF3, HP3.
        pose proof (x01_c70 (fsp g) mem2 mem3 _ (proj1 Hfsp) (proj2 Hfsp) HC70b
                      ltac:(rewrite <- SEGS0; exact HK3)) as HC70c.
        destruct (b8_FR_sp B APIf ra empty g _ L3 A3 regs3 mem3 md3 HF3) as (Hsp3 & _).
        (* `ld a0,0x70(sp)`, free(pp) *)
        assert (Hin4 : In (pp, POD_PROPS) (blocks L3 A3))
          by (apply (Permutation_in _ (Permutation_sym HP3)); left; reflexivity).
        destruct (b8_in_blocks L3 A3 _ _ Hin4) as (p4 & Hp4 & Ep4).
        eapply (b8_run_to B APIf ra empty FF); [exact HF3 | | intros regs_c4 HG4].
        { unfold rmk. eapply kX01e with (sp0 := g_S g - 608).
          - exact Hsp3.
          - lia.
          - lia.
          - unfold fsp, SLOT_FRAME in HC70c. replace (g_S g - 608 + 0x70) with (g_S g - 608 + 112) by lia.
            apply b8_bytes_le8. exact HC70c. }
        rewrite <- Ep4 in HF3, HP3.
        apply (b8_free_call B APIf ra empty FF g [] [] L3 A3 regs3 mem3 md3 regs_c4 p4 POD_PROPS).
        -- exact HF3.
        -- exact HP3.
        -- exact Hp4.
        -- b8rg HG4.
        -- b8rg HG4.
        -- b8rg HG4.
        -- rewrite HG4. apply ret_ok_even. reflexivity.
        -- rewrite HG4, Ep4. reflexivity.
        -- intros L4 A4 regs4 mem4 md4 HF4 HP4 RP4 HK4.
           replace (getr regs_c4 1) with (Z_to_bv 64 0x1484c) by (rewrite HG4; reflexivity).
           cbn [app] in HF4, HP4.
           (* the epilogue *)
           pose proof HF4 as (HGV & Hsp & Hgp & Htp & HSV & _ & _ & _ & HM4 & _).
           pose proof (b8_GV_S B empty g HGV) as (_ & HS).
           unfold saved_bytes, SLOT_SAVE in HSV.
           destruct (x01_saved_split mem4 (g_S g - 104) _ _ _ _ _ _ _ _ _ _ _ _ _ HSV)
             as (B27 & B26 & B25 & B24 & B23 & B22 & B21 & B20 & B19 & B18 & B9 & B8 & B1).
           destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HF4) as (_ & _ & _ & _ & HMI).
           pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HF4) as STn.
           destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM4) as (Hh & Hl & _).
           pose proof (sl_segs B APIf ra empty FF) as SEGS.
           unfold fsp, SLOT_FRAME in Hsp. unfold SLOT_K, SLOT_STACK in HS, STn.
           destruct (x01_rd8 _ _ _ (g_S g - 608 + 0x1f0) STn ltac:(lia) ltac:(lia)) as (f0 & Q0).
           destruct (x01_rd8 _ _ _ (g_S g - 608 + 0x1e8) STn ltac:(lia) ltac:(lia)) as (f1 & Q1).
           destruct (x01_rd8 _ _ _ (g_S g - 608 + 0x1e0) STn ltac:(lia) ltac:(lia)) as (f2 & Q2).
           destruct (x01_rd8 _ _ _ (g_S g - 608 + 0x1d8) STn ltac:(lia) ltac:(lia)) as (f3 & Q3).
           rewrite SEGS.
           eapply (sl_run_fp regs4 (Z_to_bv 64 0x1484c) mem4 md4 _ (Post B APIf ra g) Hh Hl HMI).
           ++ rewrite sl_mkR_of. eapply kX01b with (sp0 := g_S g - 608).
              ** exact Hsp.
              ** lia.
              ** lia.
              ** replace (g_S g - 608 + 0x258) with (g_S g - 104 + 96) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B1).
              ** replace (g_S g - 608 + 0x250) with (g_S g - 104 + 88) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B8).
              ** replace (g_S g - 608 + 0x248) with (g_S g - 104 + 80) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B9).
              ** replace (g_S g - 608 + 0x240) with (g_S g - 104 + 72) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B18).
              ** replace (g_S g - 608 + 0x238) with (g_S g - 104 + 64) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B19).
              ** replace (g_S g - 608 + 0x230) with (g_S g - 104 + 56) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B20).
              ** replace (g_S g - 608 + 0x228) with (g_S g - 104 + 48) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B21).
              ** replace (g_S g - 608 + 0x220) with (g_S g - 104 + 40) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B22).
              ** replace (g_S g - 608 + 0x218) with (g_S g - 104 + 32) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B23).
              ** replace (g_S g - 608 + 0x210) with (g_S g - 104 + 24) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B24).
              ** replace (g_S g - 608 + 0x208) with (g_S g - 104 + 16) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B25).
              ** replace (g_S g - 608 + 0x200) with (g_S g - 104 + 8) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B26).
              ** replace (g_S g - 608 + 0x1f8) with (g_S g - 104) by lia. apply b8_bytes_le8.
                 exact (bytes_at_normalize rsegs mem4 _ _ HMI B27).
              ** exact Q0.
              ** exact Q1.
              ** exact Q2.
              ** exact Q3.
           ++ intros ms (F1 & ->). do 5 eexists. reflexivity.
           ++ intros R F' pc' fc' m0' (F1 & HQ) regs' m' Hx Hrel Hsame.
              injection HQ; intros; subst.
              rewrite (b8_ret_pc_ra ra (b8_ra B APIf ra empty FF)).
              pose proof (mem_rel_normalize rsegs mem4 HMI) as HR0.
              assert (HF5 : FR B APIf ra empty g [] L4 A4 regs4 m' md4).
              { apply (sl_fr_run B APIf ra empty FF g [] L4 A4 regs4 mem4 md4 regs4 m' [] HF4 HP4).
                - exact (munch_rel rsegs [] mem4 (normalize rsegs mem4) m' (normalize rsegs mem4) HR0 Hrel Hsame
                           (munch_refl [] (normalize rsegs mem4))).
                - exact (wmono_rel rsegs mem4 (normalize rsegs mem4) m' (normalize rsegs mem4) HR0 Hrel Hsame
                           (wmono_refl rsegs (normalize rsegs mem4))).
                - exact (ro_agree_same rsegs mem4 m' HMI Hsame).
                - intros x _ Hx'. exfalso. apply Hx'. exact I.
                - reflexivity.
                - reflexivity.
                - reflexivity. }
              rewrite <- SEGS. apply SR_ret.
              apply (b8_post_FR B APIf ra empty g L4 A4 regs4 regs' m' md4).
              ** exact Hfrm.
              ** exact HF5.
              ** exact HP4.
              ** rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
              ** intros r Hr. unfold callee_saved in Hr.
                 assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                   r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
                 destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
                   rewrite (sl_getr_eqv _ _ _ Hx); try reflexivity.
                 --- destruct HGV as (_ & _ & _ & _ & _ & _ & _ & E2 & _).
                     transitivity (Z_to_bv 64 (g_S g)); [|symmetry; exact E2].
                     transitivity (Z_to_bv 64 (g_S g - 608 + 608)); [reflexivity | f_equal; lia].
                 --- exact Hgp.
                 --- exact Htp.
Qed.

End X01.

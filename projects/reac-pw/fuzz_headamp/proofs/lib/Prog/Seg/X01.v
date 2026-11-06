(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 249 of its 285 lines of code are new or changed and 538 lines of the source are left out. *)
(* Segment X01 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (plain): [0x141b4, 0x1421c], the four frees and the
   epilogue. K141b4 -> RET (Prog/LLVMFuzzerTestOneInput_c.v's S_X01).
   The cut is at its own FP state (Tac_b8.b8_cut_open): the frees run at it. Each free goes through
   Tac_b8.b8_free_call with hb1 = [] (free at 0x162fc = frame_facts_plain's ms_free), taking the head block of the
   cut's list hb_first g first nf out pod pp: 0x141b4 `mv a0,s7`, 0x141b8 `jal free` (ra 0x141bc), the first block;
   0x141bc `mv a0,s3`, 0x141c0 `jal free` (ra 0x141c4), the out block; 0x141c4 `mv a0,s1`, 0x141c8 `jal free`
   (ra 0x141cc), the pod block; 0x141cc `ld a0,0x58(sp)`, 0x141d0 `jal free` (ra 0x141d4), the pp block, whose address
   the frame cell sp + 0x58 holds (each free keeps the bytes from sp up, b8_free_call's last clause; the s registers by
   its callee-saved clause). That leaves FR with hb = []. Then 0x141d4 `mv a0,zero`, the thirteen restores ra, s0 ..
   s11 from the saved bytes at S - 104 (0x141d8 .. 0x14208), the three `fld` of fs0, fs1, fs2 from sp + 0x1c0,
   0x1b8, 0x1b0 (0x1420c .. 0x14214), 0x14218 `addi sp,sp,0x230`, 0x1421c `ret`. The `fld` write the FP registers,
   so this run ends at FP registers of its own (x01_run_fp: the straight-run lemma Tac_b8.b8_run_to with the final FP
   registers left free; fcsr is kept: a load accrues no flag); Post then holds by Tac_b8.b8_post_FR at that FP state
   (rounding mode 0 from CUTST). The `fld` read the 24 bytes at [S - 128, S - 104), present by FR's stack window.
   The callee-saved registers: sp, gp, tp from FR, s0 .. s11 from the saved bytes.
   Adapted from reac-pw/fuzz_role's Prog/Seg/X01.v (two frees, no FP restore), itself from reac-pw/fuzz_pin's
   Prog/Seg/X01.v (libreac/fuzz_ctrl's released Seg/C05.v and Seg/X02.v, origin/ossv/recipes 25e3d17bdb50). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import Tac_slot Tac_b8 SegFacts.
Import ListNotations.
Open Scope Z_scope.

(* 0x141b4 `mv a0,s7`; 0x141b8 `jal free`. *)
Lemma kX01a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x141bc) x2 x3 x4 x5 x6 x7 x8 x9 x23 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x162fc) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x141b4) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x141bc `mv a0,s3`; 0x141c0 `jal free`. *)
Lemma kX01b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x141c4) x2 x3 x4 x5 x6 x7 x8 x9 x19 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x162fc) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x141bc) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x141c4 `mv a0,s1`; 0x141c8 `jal free`. *)
Lemma kX01c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x141cc) x2 x3 x4 x5 x6 x7 x8 x9 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x162fc) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x141c4) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x141cc `ld a0,0x58(sp)`; 0x141d0 `jal free`. *)
Lemma kX01d : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z) (v : word),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 0x60 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x58)) 8 = Some (le8 v) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x141d4) x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x162fc) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x141cc) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 v E2 H0 H1 RV.
  subst x2.
  step. step. apply evt_done. reflexivity.
Qed.

(* 0x141d4 `mv a0,zero`; the restores of ra, s0 .. s11 from [sp + 0x1c8, sp + 0x230); the fld of fs0, fs1, fs2 from
   sp + 0x1c0, 0x1b8, 0x1b0; `addi sp,sp,0x230`; `ret`. The FP registers at the end are left free. *)
Lemma kX01e : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z)
    (r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : word) (f8 f9 f18 : list byte),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 560 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x228)) 8 = Some (le8 r1) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x220)) 8 = Some (le8 r8) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x218)) 8 = Some (le8 r9) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x210)) 8 = Some (le8 r18) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x208)) 8 = Some (le8 r19) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x200)) 8 = Some (le8 r20) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1f8)) 8 = Some (le8 r21) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1f0)) 8 = Some (le8 r22) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1e8)) 8 = Some (le8 r23) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1e0)) 8 = Some (le8 r24) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1d8)) 8 = Some (le8 r25) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1d0)) 8 = Some (le8 r26) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1c8)) 8 = Some (le8 r27) ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1c0)) 8 = Some f8 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1b8)) 8 = Some f9 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x1b0)) 8 = Some f18 ->
  Exec.evt rsegs
    (fun ms' => exists F', ms' = MS (mkR r1 (Z_to_bv 64 (sp0 + 560)) x3 x4 x5 x6 x7 r8 r9 (Z_to_bv 64 0) x11 x12 x13
                                     x14 x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 x28 x29 x30 x31)
                                 F' (ret_pc r1) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x141d4) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 f8 f9 f18 E2 H0 H1
    R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 Q8 Q9 Q18.
  subst x2.
  do 19 step.
  apply evt_done. eexists. reflexivity.
Qed.

(* Eight bytes of the stack window are readable. *)
Lemma x01_rd8 : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 8 <= hi ->
  exists bs, ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m lo hi a ST H1 H2. pose proof ST as (H0 & _ & _).
  destruct (stk_bytes rsegs m a (a + 8) (b8_stk_sub _ _ _ _ _ _ ST H1 H2 ltac:(lia)) ltac:(lia)) as (bs & Hl & Hb).
  exists bs. pose proof (b8_bytes_ovr rsegs m a bs Hb) as E. rewrite Hl in E.
  replace (Z.to_nat (a + 8 - a)) with 8%nat in E by lia. exact E.
Qed.

(* A straight run whose final FP registers are left free (Tac_b8.b8_run_to's run, by KindBGlue.kb_run's proof): the
   continuation runs at the FP state with those registers and the final fcsr. *)
Section X01Run.
Context {fx : FPState}.

Lemma x01_run_fp : forall regs pc mem md R' pc' fc' mem' (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs (fun ms => exists F', ms = MState.MS R' F' pc' fc' None mem' (seg_rom rsegs))
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall F' regs', (forall r, getr regs' r = getr R' r) ->
     SR rsegs (mkCfg (@mkst (mkFP F' fc') regs' pc' mem' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md R' pc' fc' mem' P Hh Hl HE HK.
  eapply (evt_SR_canon rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (F' & ->) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc'' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  eapply HK. apply kb_getr_eqv. exact HR.
Qed.

End X01Run.

Section X01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis FREE : free_contract B (APIf rc).

Lemma seg_X01 : S_X01 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF FREE.
  pose proof FREE as HFREE.
  unfold S_X01. intros g c (pp & pb & ob & fb & nf & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HF HP (H23 & H19 & H9 & HC58).
  unfold hb_first, hb_out, hb_pod in HF, HP.
  pose proof (b8_segs B APIf ra empty FF) as SEGS.
  pose proof HF as (HGV0 & _).
  pose proof (b8_GV_S B empty g HGV0) as (_ & HS0).
  pose proof alloc_ceiling_value as HAC.
  unfold SLOT_K, SLOT_STACK in HS0.
  (* free(first) at 0x141b8: the head block (first, nf). *)
  assert (Hin1 : In (fb, nf) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_in_blocks L A _ _ Hin1) as (p1 & Hp1 & Ep1).
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kX01a | intros regs_c1 HG1].
  rewrite <- Ep1 in HF, HP.
  apply (b8_free_call B APIf ra empty FF g [] [(ob, OUT_LEN (g_cap g)); (pb, g_len g); (pp, POD_PROPS)]
           L A regs mem md regs_c1 p1 nf).
  { exact HF. }
  { exact HP. }
  { exact Hp1. }
  { b8rg HG1. }
  { b8rg HG1. }
  { b8rg HG1. }
  { rewrite HG1. apply ret_ok_even. reflexivity. }
  { rewrite HG1. transitivity (getr regs 23); [reflexivity|]. rewrite Ep1. exact H23. }
  intros L1 A1 regs1 mem1 md1 HF1 HP1 RP1 HK1.
  replace (getr regs_c1 1) with (Z_to_bv 64 0x141bc) by (rewrite HG1; reflexivity).
  cbn [app] in HF1, HP1.
  assert (E19 : getr regs1 19 = Z_to_bv 64 ob).
  { etransitivity; [exact (RP1 19 ltac:(unfold callee_saved; lia))|]. rewrite HG1. exact H19. }
  assert (E9 : getr regs1 9 = Z_to_bv 64 pb).
  { etransitivity; [exact (RP1 9 ltac:(unfold callee_saved; lia))|]. rewrite HG1. exact H9. }
  (* free(out) at 0x141c0. *)
  assert (Hin2 : In (ob, OUT_LEN (g_cap g)) (blocks L1 A1))
    by (apply (Permutation_in _ (Permutation_sym HP1)); left; reflexivity).
  destruct (b8_in_blocks L1 A1 _ _ Hin2) as (p2 & Hp2 & Ep2).
  eapply (b8_run_to B APIf ra empty FF); [exact HF1 | unfold rmk; apply kX01b | intros regs_c2 HG2].
  rewrite <- Ep2 in HF1, HP1.
  apply (b8_free_call B APIf ra empty FF g [] [(pb, g_len g); (pp, POD_PROPS)]
           L1 A1 regs1 mem1 md1 regs_c2 p2 (OUT_LEN (g_cap g))).
  { exact HF1. }
  { exact HP1. }
  { exact Hp2. }
  { b8rg HG2. }
  { b8rg HG2. }
  { b8rg HG2. }
  { rewrite HG2. apply ret_ok_even. reflexivity. }
  { rewrite HG2. transitivity (getr regs1 19); [reflexivity|]. rewrite Ep2. exact E19. }
  intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 HK2.
  replace (getr regs_c2 1) with (Z_to_bv 64 0x141c4) by (rewrite HG2; reflexivity).
  cbn [app] in HF2, HP2.
  assert (E9' : getr regs2 9 = Z_to_bv 64 pb).
  { etransitivity; [exact (RP2 9 ltac:(unfold callee_saved; lia))|]. rewrite HG2. exact E9. }
  (* free(pod) at 0x141c8. *)
  assert (Hin3 : In (pb, g_len g) (blocks L2 A2))
    by (apply (Permutation_in _ (Permutation_sym HP2)); left; reflexivity).
  destruct (b8_in_blocks L2 A2 _ _ Hin3) as (p3 & Hp3 & Ep3).
  eapply (b8_run_to B APIf ra empty FF); [exact HF2 | unfold rmk; apply kX01c | intros regs_c3 HG3].
  rewrite <- Ep3 in HF2, HP2.
  apply (b8_free_call B APIf ra empty FF g [] [(pp, POD_PROPS)] L2 A2 regs2 mem2 md2 regs_c3 p3 (g_len g)).
  { exact HF2. }
  { exact HP2. }
  { exact Hp3. }
  { b8rg HG3. }
  { b8rg HG3. }
  { b8rg HG3. }
  { rewrite HG3. apply ret_ok_even. reflexivity. }
  { rewrite HG3. transitivity (getr regs2 9); [reflexivity|]. rewrite Ep3. exact E9'. }
  intros L3 A3 regs3 mem3 md3 HF3 HP3 RP3 HK3.
  replace (getr regs_c3 1) with (Z_to_bv 64 0x141cc) by (rewrite HG3; reflexivity).
  cbn [app] in HF3, HP3.
  (* free(pp) at 0x141d0, pp read from the frame cell sp + 0x58, which the three frees kept. *)
  rewrite SEGS in HK1, HK2, HK3.
  assert (HC58' : bytes_at rsegs mem3 (g_S g - 560 + 0x58) (le8 (Z_to_bv 64 pp))).
  { apply (b8_ba_mbyte mem mem3 _ _ HC58). intros i Hi. rewrite length_le8 in Hi.
    unfold fsp, SLOT_FRAME. rewrite HK3, HK2, HK1 by lia. reflexivity. }
  assert (Hin4 : In (pp, POD_PROPS) (blocks L3 A3))
    by (apply (Permutation_in _ (Permutation_sym HP3)); left; reflexivity).
  destruct (b8_in_blocks L3 A3 _ _ Hin4) as (p4 & Hp4 & Ep4).
  pose proof HF3 as (_ & Hsp3 & _).
  unfold fsp, SLOT_FRAME in Hsp3.
  eapply (b8_run_to B APIf ra empty FF); [exact HF3 | | intros regs_c4 HG4].
  { unfold rmk. eapply kX01d with (sp0 := g_S g - 560).
    - exact Hsp3.
    - lia.
    - lia.
    - apply b8_bytes_le8. exact HC58'. }
  rewrite <- Ep4 in HF3, HP3.
  apply (b8_free_call B APIf ra empty FF g [] [] L3 A3 regs3 mem3 md3 regs_c4 p4 POD_PROPS).
  { exact HF3. }
  { exact HP3. }
  { exact Hp4. }
  { b8rg HG4. }
  { b8rg HG4. }
  { b8rg HG4. }
  { rewrite HG4. apply ret_ok_even. reflexivity. }
  { rewrite HG4, Ep4. reflexivity. }
  intros L4 A4 regs4 mem4 md4 HF4 HP4 RP4 HK4.
  replace (getr regs_c4 1) with (Z_to_bv 64 0x141d4) by (rewrite HG4; reflexivity).
  cbn [app] in HF4, HP4.
  (* The epilogue: the restores and the fld from the frame, by x01_run_fp. *)
  pose proof HF4 as (HGV & Hsp & Hgp & Htp & HSV & HSTK & _ & _ & HM4 & _).
  destruct (sf_saved_split mem4 (g_S g) _ _ _ _ _ _ _ _ _ _ _ _ _ HSV)
    as (B27 & B26 & B25 & B24 & B23 & B22 & B21 & B20 & B19 & B18 & B9 & B8 & B1).
  unfold fsp, SLOT_FRAME in Hsp. unfold SLOT_K, SLOT_STACK in HSTK.
  destruct (x01_rd8 mem4 _ _ (g_S g - 112) HSTK ltac:(lia) ltac:(lia)) as (f8 & Q8).
  destruct (x01_rd8 mem4 _ _ (g_S g - 120) HSTK ltac:(lia) ltac:(lia)) as (f9 & Q9).
  destruct (x01_rd8 mem4 _ _ (g_S g - 128) HSTK ltac:(lia) ltac:(lia)) as (f18 & Q18).
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM4) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (x01_run_fp regs4 (Z_to_bv 64 0x141d4) mem4 md4 _ _ _ _ _ Hh Hl).
  { unfold rmk. eapply kX01e with (sp0 := g_S g - 560).
    - exact Hsp.
    - lia.
    - lia.
    - replace (g_S g - 560 + 0x228) with (g_S g - 8) by lia. apply b8_bytes_le8. exact B1.
    - replace (g_S g - 560 + 0x220) with (g_S g - 16) by lia. apply b8_bytes_le8. exact B8.
    - replace (g_S g - 560 + 0x218) with (g_S g - 24) by lia. apply b8_bytes_le8. exact B9.
    - replace (g_S g - 560 + 0x210) with (g_S g - 32) by lia. apply b8_bytes_le8. exact B18.
    - replace (g_S g - 560 + 0x208) with (g_S g - 40) by lia. apply b8_bytes_le8. exact B19.
    - replace (g_S g - 560 + 0x200) with (g_S g - 48) by lia. apply b8_bytes_le8. exact B20.
    - replace (g_S g - 560 + 0x1f8) with (g_S g - 56) by lia. apply b8_bytes_le8. exact B21.
    - replace (g_S g - 560 + 0x1f0) with (g_S g - 64) by lia. apply b8_bytes_le8. exact B22.
    - replace (g_S g - 560 + 0x1e8) with (g_S g - 72) by lia. apply b8_bytes_le8. exact B23.
    - replace (g_S g - 560 + 0x1e0) with (g_S g - 80) by lia. apply b8_bytes_le8. exact B24.
    - replace (g_S g - 560 + 0x1d8) with (g_S g - 88) by lia. apply b8_bytes_le8. exact B25.
    - replace (g_S g - 560 + 0x1d0) with (g_S g - 96) by lia. apply b8_bytes_le8. exact B26.
    - replace (g_S g - 560 + 0x1c8) with (g_S g - 104) by lia. apply b8_bytes_le8. exact B27.
    - replace (g_S g - 560 + 0x1c0) with (g_S g - 112) by lia. exact Q8.
    - replace (g_S g - 560 + 0x1b8) with (g_S g - 120) by lia. exact Q9.
    - replace (g_S g - 560 + 0x1b0) with (g_S g - 128) by lia. exact Q18. }
  intros F' regs5 HG5.
  rewrite <- SEGS.
  rewrite (b8_ret_pc_ra ra (b8_ra B APIf ra empty FF)). apply SR_ret.
  eapply (b8_post_FR B APIf ra empty g L4 A4 regs4 regs5 mem4 md4).
  - exact Hfrm.
  - exact HF4.
  - exact HP4.
  - b8rg HG5.
  - intros r Hr. unfold callee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; rewrite HG5;
      try reflexivity.
    + destruct HGV as (_ & _ & _ & _ & _ & _ & _ & E2 & _).
      transitivity (Z_to_bv 64 (g_S g)); [|symmetry; exact E2].
      transitivity (Z_to_bv 64 (g_S g - 560 + 560)); [reflexivity | f_equal; lia].
    + exact Hgp.
    + exact Htp.
Qed.

End X01.

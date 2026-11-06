(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 74 of its 94 lines of code are new or changed and 554 lines of the source are left out. *)
(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f = pinned 3776ca44d75c):
   K13cac -> K13f40 (0x13cac .. 0x13f3c and the -1 exit 0x13fa0 .. 0x13fac of the plain binary),
   as SegEvt.evt_V01 (a Tac_seg.seg_evt_e: the write set holds the errno cell) at CPseg
   (Prog/Seg/SegWalkMainA.v) and its lift SegEnd.seg_V01_stmt CPseg MainB.K_V01 (SegEvt.seg_V01_of_evt).
   The run is assembled from the pieces of Prog/Seg/V01_Inv.v: V01_Env (the cut state K13cac and the frame FR give
   HEAD's premises on the normalized memory), V01_Head (the guard, "enp1s0", the loop set-up), V01_Loop (the loop of
   the inline m_declared, with V01_Split (strrchr, V01_Dig's digit loop, V01_Par's parent loop) and V01_Add
   (V01_Dup's duplicate loop, the append)), V01_Tail (reac_segconf_declared, check_declared). At K13f40 only the
   registers matter (seg_cuts.P_K13f40: s4 = mt, s3 = tab, s0 = m, s1 = c); the run writes inside
   seg_We g [(mt, nmt); (tab, ntab)] and touches no FP state (every callee keeps F and fcsr).
   Part of the proof of LLVMFuzzerTestOneInput: this file is segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import memset_c memcpy_c strrchr_c strcmp_c
  reac_segconf_declared_c check_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c
  SegEnd SegEvt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_seg SegWalkMainA
  MainB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import V01_Inv V01_Env V01_Head V01_Dig V01_Par
  V01_Split V01_Dup V01_Add V01_Loop V01_Tail.
Import ListNotations.
Open Scope Z_scope.

(* seg_We's write set holds v01_We's. *)
Lemma v01_sub_We : forall inp g tab ntab mt nmt, ntab = TAB_N inp -> nmt = MT_N inp ->
  sub_fp (v01_We inp (g_S g) tab mt) (seg_We g [(mt, nmt); (tab, ntab)]).
Proof.
  intros inp g tab ntab mt nmt -> ->. intros x Hx.
  unfold seg_We, seg_W, v01_We, v01_W, ERRNO_CELL, V01_ERRNO, SLOT_K, SLOT_STACK in *.
  cbn [map fst snd Frame.outside] in *. tauto.
Qed.

Section V01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis KV : MainB.K_V01.

Lemma v01_evt : evt_V01 B APIf ra empty CPseg.
Proof.
  destruct KV as (HMS & HMC & HSR & HSC & HDC & HCD).
  unfold evt_V01, seg_evt_e. intros g bc bm tab ntab mt nmt L A regs mem md HFR HP HPre Hfrm.
  unfold CPseg in HPre |- *. cbn [cp_K13cac cp_K13f40] in HPre |- *.
  destruct (v01_env B APIf ra empty FF g bc bm tab ntab mt nmt L A regs mem md HFR HP HPre)
    as (GEO & BASE & PRE & Htp).
  pose proof HPre as (Hntab & Hnmt & (H8 & H26 & _) & H10 & H19 & H20 & H22 & _).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & _ & _ & _ & _).
  unfold rgz in H8, H26, H10, H19, H20, H22.
  unfold fsp, SLOT_FRAME in Hsp.
  rewrite sl_mkR_of. rewrite Hsp, H8, H26, H10, H19, H20, H22.
  set (inp := g_in g) in *. set (S := g_S g) in *. set (m0 := normalize rsegs mem) in *.
  set (Qf := fun ms : machine_state => exists R F' fc' m', ms = MState.MS R F' (Z_to_bv 64 0x13f40) fc' None m'
                 (seg_rom rsegs) /\ frm_zero fc' /\
               Frame.munch (seg_We g [(mt, nmt); (tab, ntab)]) m0 m' /\ Frame.wmono rsegs m0 m' /\
               YK11.getr R 2 = Z_to_bv 64 (S - 208) /\ YK11.getr R 3 = YK11.getr regs 3 /\
               YK11.getr R 4 = YK11.getr regs 4 /\
               (forall regs' m, Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m m' ->
                  P_K13f40 inp (g_p g) S bc bm tab ntab mt nmt regs' m)).
  change (Exec.evt rsegs Qf (vst 0x13cac (getr regs 1) (Z_to_bv 64 (S - 208)) (getr regs 3) (getr regs 4)
    (getr regs 5) (getr regs 6) (getr regs 7) (Z_to_bv 64 bm) (getr regs 9) (Z_to_bv 64 mt) (getr regs 11)
    (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
    (Z_to_bv 64 tab) (Z_to_bv 64 (seg_cap inp + 1)) (getr regs 21) (Z_to_bv 64 (seg_cap inp)) (getr regs 23)
    (getr regs 24) (getr regs 25) (Z_to_bv 64 (bm + MC_N)) (getr regs 27) (getr regs 28) (getr regs 29)
    (getr regs 30) (getr regs 31) fp_regs fp_csr m0)).
  assert (KE : K_end inp S bc bm tab mt m0 (getr regs 3) (getr regs 4) fp_regs fp_csr Qf).
  { intros ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m' MU WM MI.
    unfold Qf, v01_end_st, vst.
    eexists _, fp_regs, fp_csr, m'. split; [reflexivity|]. split; [exact Hfrm|].
    split; [exact (munch_weaken _ _ _ _ (v01_sub_We inp g tab ntab mt nmt Hntab Hnmt) MU)|].
    split; [exact WM|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros regs' m Hx Hrel. unfold P_K13f40, rgz.
    rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [exact Hntab|]. split; [exact Hnmt|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | reflexivity]. }
  assert (KT : K_tail inp S bc bm tab mt m0 (getr regs 3) (getr regs 4) fp_regs fp_csr Qf)
    by exact (v01_tail HDC HCD inp S bc bm tab mt m0 (getr regs 3) (getr regs 4) fp_regs fp_csr Qf GEO BASE Htp KE).
  assert (KL : K_loop inp S bc bm tab mt m0 (getr regs 3) (getr regs 4) fp_regs fp_csr Qf)
    by exact (v01_loop (v01_split HSR HMC v01_dig v01_par) (v01_add HMC (v01_dup HSC))
                inp S bc bm tab mt m0 (getr regs 3) (getr regs 4) fp_regs fp_csr Qf GEO BASE KT).
  exact (v01_head HMS HMC inp S bc bm tab mt m0 (getr regs 3) (getr regs 4) fp_regs fp_csr Qf
           (getr regs 1) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 9) (getr regs 11) (getr regs 12)
           (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 21)
           (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
           (getr regs 31) GEO BASE PRE KL KT).
Qed.

End V01.

Theorem evt_V01_holds : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> MainB.K_V01 -> evt_V01 B APIf ra empty CPseg.
Proof. intros fx rc B APIf LS SH SK ra empty FF KV. exact (v01_evt B APIf ra empty FF KV). Qed.

Theorem seg_V01 : SegEnd.seg_V01_stmt SegWalkMainA.CPseg MainB.K_V01.
Proof. apply seg_V01_of_evt. exact evt_V01_holds. Qed.

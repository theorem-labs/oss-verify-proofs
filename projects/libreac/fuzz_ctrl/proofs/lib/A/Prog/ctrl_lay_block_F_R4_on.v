(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_ctrl_classify_box_frameLib.v, with its module paths, module names, addresses and numbers changed; 4015 of its 4198 lines of code are new or changed and 806 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/ctrl_lay_blockF_on.v, with its module paths, addresses and numbers changed; 20 of its 69 lines of code are new or changed and 4149 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): ROUTE (C) twin of region R4's run (0x858f4, after the class-1 flag
   release, -> ret).  A Theorem Labs lane (a Theorem Labs lane), brief
   (a working note, not in this delivery).  rule 24: no function proved.  This file proves no
   function (kind: segment lemma).

   lay_tail_F_R4_on is lay_tail_F_R4 (ctrl_lay_block_F_R4.v (at head lib/A/Prog/ctrl_lay_block_F_R4.v:73-101; written on a working branch 63a02bb46d7)) in
   the route (C) form of record (a Theorem Labs lane's ASSIGN.md (a working note, not in this delivery; its form frozen by a Theorem Labs lane 09:38Z) and the 10:34Z amendment):
   - PRE: lay_tail_F_R4's universal premise `shadow_rw m'` (F_R4.v:81) is DROPPED.  R = the shadow bytes the run reads
     or stores through that premise = NONE (measured below), so there is no region predicate and no _sub lemma.
   - POST: the post Q's `shadow_rw m'` conjunct (ctrl_lay_block.v, at head :509) becomes the transport
     `forall P, shadow_rw_on P m0 -> shadow_rw_on P m'` from the region's START memory m0 to its END memory m'
     (lay_Q_on m0 below; the twin takes m0 := its pre memory).  The end memory is the start memory (the post's
     `ms_mem s = m'`, F_R4.v:84), so the transport is the identity.

   R DERIVATION (for the auditor a Theorem Labs lane), against the source:
   - a Theorem Labs lane's consumer table shadow-rw-consumers-A.md row 420 (a working note, not in this delivery): "lay_tail_F_R4
     premise `shadow_rw m'` (ctrl_lay_block_F_R4.v:81) into post Q (ctrl_lay_block.v:491) ... none (epilogue makes no
     shadow access)" (the row's ctrl_lay_block.v:491 is Q's `shadow_rw m'` conjunct, at head lib/A/Prog/ctrl_lay_block.v:509; Definition Q is at head :498).  CHECKED: in lay_tail_F_R4's proof the premise is the intro name SR (F_R4.v:90) and its only use
     is `exact SR` (F_R4.v:99), the post's own shadow_rw conjunct.  The 16 steps (F_R4.v:95) are the `j` and
     lay_tail's 12 restores from the SAVES cells at [S - 96, S) (rw_cells, F_R4.v:76), `addi sp` and `ret`: no
     instruction touches a shadow byte (the footprint premise is rng (S - 96) 96 only, F_R4.v:75).
   So R4 reads no shadow byte and stores none: premise dropped.

   DIFF AGAINST ctrl_lay_block_F_R4.v (instruction proofs VERBATIM): Section K8R -> K8R_on; lay_tail_F_R4 ->
   lay_tail_F_R4_on; premise `shadow_rw m' ->` removed (intro name SR removed); post `Q` -> `lay_Q_on m'`;
   `unfold ctrl_lay_block.Q` -> `unfold lay_Q_on`; `exact SR` -> `exact (fun P H => H)`.
   RE-PROVED HELPERS: none.  NEW DEFINITION: lay_Q_on = Section L's Q (ctrl_lay_block.v, at head :498-512) with its
   `shadow_rw m'` conjunct (at head :509) replaced by the transport from m0.

   PROVENANCE: as ctrl_lay_block_F_R4.v (image root (internal path), ELF
   sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd, FACTS of record ed6b6b7b0ab). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ctrl_lay_block_F_common.
(* The skeleton's Require list, repeated in its order (Import is not transitive; lib.Lib ExecF StepF LAST, so StepF's
   step / if_false / finish / store_done shadow the evt engine's). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth
  RcSynthLib RcLay RcLayLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c reac_box_model_block_c ctrl_lay_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ctrl_lay_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF.
(* route (C): the region-restricted shadow_rw (a Theorem Labs lane's leaf) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Local Open Scope Z_scope.

Section K8R_on.
  (* Section L's Variables (ctrl_lay_block.v :404-405), minus `ob`, which neither SAVES, LAY nor Q mentions. *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr tb mb nb gb : list byte).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.
  Local Notation SP2 := ((S - 128) / 32 * 32).

  Local Notation SAVES := (ctrl_lay_block.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
  Local Notation LAY := (ctrl_lay_block.LAY md g fr tb mb nb gb).

  (* Section L's HHM (:450). *)
  Hypothesis HHM : HIGHMEM_BEG <= S - K.

  (* Section L's Q (ctrl_lay_block.v:480-494), verbatim, except its `shadow_rw m'` conjunct (:491): the route (C)
     post, every shadow region present at the region's start memory m0 is present at the end memory m'. *)
  Definition lay_Q_on (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch ([(p + 18, p + 50); (S - K, S)] ++ fp_w [0%nat; 1%nat] FS ++
             [(shadow_addr (S - K), shadow_addr S)]) m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' (S - K) S /\
      rw_cells rsegs m' (p + 18) [CB 32 LAY] /\
      asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m0 -> shadow_rw_on P m') /\
      addressable m' (S - K) K /\
      fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
      ctrl_lay_block_tls m' (bv_unsigned tp) FS (S - K) S.

  Lemma lay_tail_F_R4_on : forall (RNG : footprint) (m' : word -> option byte)
      (xra xsp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    rng RNG (S - 96) 96 ->
    rw_cells rsegs m' (bv_unsigned sp + -96) SAVES ->
    munch ([(p + 18, p + 50); (S - K, S)] ++ fp_w [0%nat; 1%nat] FS ++
           [(shadow_addr (S - K), shadow_addr S)]) m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - K) S ->
    rw_cells rsegs m' (p + 18) [CB 32 LAY] ->
    asan_cells m' -> addressable m' (S - K) K ->
    fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) ->
    ctrl_lay_block_tls m' (bv_unsigned tp) FS (S - K) S ->
    evtF rsegs RNG (fun s => lay_Q_on m' s /\ ms_mem s = m')
      (MS (mkR xra xsp gp tp x5 x6 x7 sp (Z_to_bv 64 SP2) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x858f4) fc None m' (seg_rom rsegs)).
  Proof.
    intros RNG m' xra xsp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30
      x31 RWIN FR MU WM MI ST BK AC AW FP TL.
    unfold ctrl_lay_block.SAVES in FR. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (SPlo : 2 ^ 32 <= S < 2 ^ 64)
      by (pose proof HHM; pose proof Rsp; unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in *; lia).
    (* 0x858f4 j 85928, then lay_tail's own 15 steps. *)
    do 16 step.
    apply evtF_done. split; [| reflexivity]. unfold lay_Q_on. cbv beta.
    do 15 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact BK|]. split; [exact AC|]. split; [exact (fun P H => H)|]. split; [exact AW|].
    split; [exact FP | exact TL].
  Qed.
End K8R_on.

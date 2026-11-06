(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 99 of its 112 lines of code are new or changed and 235 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block_F_1.v; 36 of its 74 lines of code are new or changed and 74 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): region R1 of the cgif glue (entry 0x855f4 -> the cut 0x85668).
   A Theorem Labs lane.  Re-base plan
   ctrl_lay_block-rebase.md section 3 R1 and section 5 (a working note, not in this delivery).

   R1's run is stretch k = 1 (ctrl_lay_block_F_1.v ctrl_lay_block_F_1), applied by the glue as it is with Section L's
   memory m := normalize memc (no copy: its post already states its exact write set, munch [(S - K, S)],
   ctrl_lay_block_F_1.v:86).  The stretch stops BEFORE the `jal 3d72c <__asan_stack_malloc_1>` at 0x85668; the glue's
   cut rule (YC85.v aj_stack_malloc_atS) starts at the callee's entry with ra = the return address.  This file gives
   that one instruction:
   - lay_F_R1_jal: ctrl_lay_block.v ly_pro_go :2792, the second `step` of that line (it takes the jal).  One `step`,
     no data access, memory unchanged; ra := 0x8566c, pc := ASAN_STACK_MALLOC_1 = 0x3d72c (asan_stack_malloc_c.v:9).
   No Section L helper is used or re-proved.

   ROUTE (a) CONDITIONS (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z, via a Theorem Labs lane); re-based copy allowed by a Theorem Labs lane 23:53Z
   (instruction proofs verbatim, re-proved helpers named: none):
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and
      no new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk.  No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell.  The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes.
   4. Every _F carries provenance in its header and goes to the auditor a Theorem Labs lane
      who signs it against its proved run before it counts.
   5. A StepF "footprint: access <a> width <n> not covered by any [rng] hypothesis" error means STOP and report
      it: never widen the footprint to make it pass.

   PROVENANCE.
   - image root (internal path)
     -> (internal path)
   - ELF sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd
   - compare: fuzz_ctrl.objdump.txt (a working note, not in this delivery), ctrl_lay_block 0x855f4 .. 0x85988
   - FACTS of record ed6b6b7b0ab (origin/regen/libreac-v190-on-338), PAU (internal path)
   - re-run from ctrl_lay_block.v at a working branch d69f7c708f6 (same text at 9d33dba1444). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* stretch k = 1, Required qualified (the region run below composes it with the jal) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_lay_block_F_1.
Import ListNotations.
Open Scope Z_scope.

Lemma lay_F_R1_jal : forall (RNG : ExecF.footprint)
    (xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
     x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mg : word -> option byte),
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8566c) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                              x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 ASAN_STACK_MALLOC_1) fc None mg (seg_rom rsegs))
    (MS (mkR xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x85668) fc None mg (seg_rom rsegs)).
Proof.
  intros RNG xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc mg.
  step.
  apply ExecF.evtF_done. unfold ASAN_STACK_MALLOC_1. reflexivity.
Qed.

(* ---- the region's whole run: stretch k = 1 (ctrl_lay_block_F_1.v ctrl_lay_block_F_1) then lay_F_R1_jal, from the
   entry 0x855f4 to the callee's entry 0x3d72c with ra = 0x8566c.  The glue lifts this ONE run with Section L's
   memory m := normalize memc.  Pure composition (ExecF.evtF_cut); the post is k = 1's (lay_F_pre_smalloc,
   ctrl_lay_block_F_1.v:78-87) with ra and pc moved by the jal. ---- *)
Section K1R.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g : Z).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.
  Local Notation SP2 := ((S - 128) / 32 * 32).

  (* k = 1's hypotheses (ctrl_lay_block_F_1.v:66-70 = ctrl_lay_block.v :415 ST0, :446 MI0, :448 AC0, :450 HHM,
     :451 HAE), exactly their types. *)
  Hypothesis ST0 : stk rsegs m (S - K) S.
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis HHM : HIGHMEM_BEG <= S - K.
  Hypothesis HAE : S <= APPMEM_END.

  Definition lay_F_R1_post : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (mg : word -> option byte),
      ms' = MS (mkR (Z_to_bv 64 0x8566c) (Z_to_bv 64 SP2) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                    (Z_to_bv 64 96) a1' a2' (Z_to_bv 64 g) a4' a5' a6' a7'
                    s2 (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 md) (Z_to_bv 64 p) s8 s9
                    (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
               F (Z_to_bv 64 ASAN_STACK_MALLOC_1) fc None mg (seg_rom rsegs) /\
      munch [(S - K, S)] m mg /\ wmono rsegs m mg /\ rd_mono m mg /\ mem_inv rsegs mg /\
      rw_cells rsegs mg (S - 96) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).

  Lemma lay_F_R1_run : forall (RNG : ExecF.footprint),
    ExecF.rng RNG (S - K) K -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG GOT_UAR 8 -> ExecF.rng RNG UAR 4 ->
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ExecF.evtF rsegs RNG lay_F_R1_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m (seg_rom rsegs)).
  Proof.
    intros RNG R1 R2 R3 R4 R5 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6.
    eapply ExecF.evtF_cut.
    { exact (ctrl_lay_block_F_1.ctrl_lay_block_F_1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g
               ST0 MI0 AC0 HHM HAE RNG R1 R2 R3 R4 R5 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m eq_refl). }
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mg & -> &
                MU & WM & RM & MI & FR).
    eapply ExecF.evtF_cut; [apply lay_F_R1_jal |].
    intros ms2 ->. apply ExecF.evtF_done. unfold lay_F_R1_post.
    exists t0', t1', t2', a1', a2', a4', a5', a6', a7', t3', t4', t5', t6', mg.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI | exact FR].
  Qed.
End K1R.

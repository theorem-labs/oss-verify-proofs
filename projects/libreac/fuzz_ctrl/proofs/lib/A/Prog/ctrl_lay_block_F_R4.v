(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its addresses and numbers changed; 20 of its 55 lines of code are new or changed and 3818 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): RE-BASED copy of stretch k = 8 for region R4 of the cgif glue
   (0x858f4, after the class-1 flag release, -> ret).  A Theorem Labs lane.  Re-base plan
   R4 (ctrl_lay_block-rebase.md section 3 and section 5 (a working note, not in this delivery)).

   WHY A COPY.  lay_tail_F (ctrl_lay_block_F_8.v:91-119) is applied by the glue with Section L's memory
   m := normalize m3 (the memory after the release); its premises at that base come from AR (plan, R4 table).  Its
   post Q (ctrl_lay_block.v:480-494) hides the final memory behind an existential with LC's coarse munch set, which
   contains bytes that are not awr (plan section 4).  The run only loads (the twelve restores) and jumps, so the final
   memory IS m'.  This copy states that, so the glue's journal step (ProgWorld.v ajournal_of_fsteps :963) takes the
   empty write set.

   DIFF AGAINST ctrl_lay_block_F_8.v (not in this delivery; for the auditor a Theorem Labs lane; instruction proofs VERBATIM): Section K8 -> K8R;
   lay_tail_F -> lay_tail_F_R4; the post `Q` -> `fun s => Q s /\ ms_mem s = m'`; after `apply evtF_done.` the
   proof adds `split; [| reflexivity].` for the new conjunct, the rest is verbatim.  lay_tail_of_F is not copied.
   No Section L helper is re-proved.

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
   - copied from ctrl_lay_block_F_8.v (not in this delivery) (a working branch ac3e4b54a3a, merged 9d33dba1444), itself
     lay_tail (ctrl_lay_block.v (at head lib/A/Prog/ctrl_lay_block.v:905-936; from a working branch d69f7c708f6)) moved back one instruction. *)
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
Import ListNotations.
Open Scope Z_scope.

Section K8R.
  (* Section L's Variables (ctrl_lay_block.v :404-405), minus `ob`, which neither SAVES, LAY nor Q mentions. *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr tb mb nb gb : list byte).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.
  Local Notation SP2 := ((S - 128) / 32 * 32).

  Local Notation SAVES := (ctrl_lay_block.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
  Local Notation LAY := (ctrl_lay_block.LAY md g fr tb mb nb gb).
  Local Notation Q :=
    (ctrl_lay_block.Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g FS fr tb mb nb gb).

  (* Section L's HHM (:450). *)
  Hypothesis HHM : HIGHMEM_BEG <= S - K.

  Lemma lay_tail_F_R4 : forall (RNG : footprint) (m' : word -> option byte)
      (xra xsp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    rng RNG (S - 96) 96 ->
    rw_cells rsegs m' (bv_unsigned sp + -96) SAVES ->
    munch ([(p + 18, p + 50); (S - K, S)] ++ fp_w [0%nat; 1%nat] FS ++
           [(shadow_addr (S - K), shadow_addr S)]) m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - K) S ->
    rw_cells rsegs m' (p + 18) [CB 32 LAY] ->
    asan_cells m' -> shadow_rw m' -> addressable m' (S - K) K ->
    fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) ->
    ctrl_lay_block_tls m' (bv_unsigned tp) FS (S - K) S ->
    evtF rsegs RNG (fun s => Q s /\ ms_mem s = m')
      (MS (mkR xra xsp gp tp x5 x6 x7 sp (Z_to_bv 64 SP2) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x858f4) fc None m' (seg_rom rsegs)).
  Proof.
    intros RNG m' xra xsp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30
      x31 RWIN FR MU WM MI ST BK AC SR AW FP TL.
    unfold ctrl_lay_block.SAVES in FR. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (SPlo : 2 ^ 32 <= S < 2 ^ 64)
      by (pose proof HHM; pose proof Rsp; unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in *; lia).
    (* 0x858f4 j 85928, then lay_tail's own 15 steps. *)
    do 16 step.
    apply evtF_done. split; [| reflexivity]. unfold ctrl_lay_block.Q. cbv beta.
    do 15 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact BK|]. split; [exact AC|]. split; [exact SR|]. split; [exact AW|].
    split; [exact FP | exact TL].
  Qed.
End K8R.

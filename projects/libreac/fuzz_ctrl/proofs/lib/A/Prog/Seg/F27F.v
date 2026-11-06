(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 186 of its 223 lines of code are new or changed and 359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F27.v, with its module paths and module names changed; 583 of its 701 lines of code are new or changed and 105 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F27.v c521acaf7acb (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F_bounded re-derives the extracted run at ExecF.RNG_all, and each <r>_of_F_bounded_shape
   proves that the bounded corollary is the extracted statement plus address-bound premises and nothing else.
   There is NO <r>_of_F_verbatim pin in this file, because F27.v states NO run lemma: its two runs are the
   `Tac_slot.sl_run` argument inside the one Hat proof seg_F27 (F27.v:139, the two arms at :165 and :229), so there
   is no F27.<r> constant to pin against. This is the case Seg/F5F.v (a Theorem Labs lane, 96b9daa01771) reports the same way;
   reported here to the lead and to the auditor a Theorem Labs lane.
   Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of the two inline runs of seg_F27 (F27.v:139), 0x82604 -> 0x8265c (the r = 0 arm,
   F27.v:165-191) and 0x82604 -> 0x82750 (the r <> 0 arm, F27.v:229-255). Each statement is exactly the evt fact
   seg_F27's script hands to Tac_slot.sl_run for that arm: the same start state
   `MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82604) fp_csr None mem (seg_rom rsegs)`, the same post predicate
   K, and the carried facts the script uses, with the ghost terms abstracted to plain variables
   (t_rp -> 0 / -1, t_unk -> u / -1, [A+136] -> fr + 128, [A+176] -> fr + 64, the three ports words -> -7).
   Each run is re-stepped with lib.Lib StepF as an ExecF.evtF under a universally quantified footprint RNG, with the
   same script, and one ExecF.rng premise per region the run reads. Both arms are read-only (no store, no call, no
   instrumented check), so no premise names a shadow byte and mem' = mem in both posts.
   Three name changes, as Seg/F5F.v and Seg/F10F.v make them (same term after delta, no new reasoning):
   f27F_mkR_of_expand is F27.f27_mkR_of_expand over lib.Lib's mkR (the register map StepF reads), f27F_slti0 is
   F27.f27_slti0 over lib.Lib's PropExec.v_slti (the one the StepF step puts in the goal), and the read premises are
   delta-unfolded from ULMem.wa, which lib.Lib's solve_load does not unfold. F27.v itself is unchanged outside comments. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot B7Cuts F27.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow the UL engine's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr (the register read of rg and of the sl_run post-state), as F27.v does. *)
Import YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module ULMemF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module F27UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.

(* The UL engine's evt from the lib.Lib one: both are msteps of `ms_svc_pending ms = None /\ step = MachineOk ms'`
   (Seg/F10F.v f10F_ul_of_lib). Tac_slot.sl_run takes the UL form, this file's old form gives the lib.Lib one. *)
Lemma f27F_ul_of_lib : forall Q ms, LE.evt rsegs Q ms -> F27UE.evt rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [clear HQ|exact HQ].
  induction H as [s|s s1 s2 Hs _ IH]; [apply F27UE.msteps_refl|].
  eapply F27UE.msteps_cons; [exact Hs | exact IH].
Qed.
Section RunF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

(* F27.f27_mkR_of_expand with lib.Lib's mkR (the register map StepF reads). *)
Lemma f27F_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  LFr.mkR (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 1)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 5)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 6)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 7)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 10)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 11)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 12)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 13)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 14)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 15)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 16)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 17)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 20)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 25)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 27)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 28)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 29)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 30)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* F27.f27_slti0 over lib.Lib's PropExec.v_slti: `slti a1,s4,0` with s4 = u >= 0 gives 0. *)
Lemma f27F_slti0 : forall u, 0 <= u < 2 ^ 63 -> LPE.v_slti (Z_to_bv 64 u) 0 = Z_to_bv 64 0.
Proof. exact f27_slti0. Qed.

(* ---- The r = 0 arm (F27.v:165-191): 0x82604 -> 0x8265c. The run reads one cell, the spill [s1 + 136]. ---- *)
Lemma f27_r0_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (A1 fr phi u : Z)
    (RNG : footprint),
  rg regs 25 0 -> rg regs 20 u -> rg regs 10 u -> rg regs 9 A1 -> rg regs 22 (phi + 18) ->
  0 <= u < 2 ^ 63 ->
  ov_read_bytes rsegs mem (ULMemF.wa (A1 + 136)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 128))) ->
  rng RNG (A1 + 136) 8 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x8265c /\ mem' = mem /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 20 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 20 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 7 = Z_to_bv 64 (fr + 128) /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 10 = Z_to_bv 64 (phi + 26) /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 14 = Z_to_bv 64 (phi + 26) /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 15 = Z_to_bv 64 12 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 11 = Z_to_bv 64 0 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 12 = Z_to_bv 64 0 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 13 = Z_to_bv 64 0 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 16 = Z_to_bv 64 0))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82604) fp_csr None mem
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros regs mem A1 fr phi u RNG Hs9 Hs4 Ha0 H91 H22 Hu63 RD136 R136.
  cbv beta delta [ULMemF.wa] in RD136.
  rewrite f27F_mkR_of_expand.
  f27_slot Hs9. f27_slot Hs4. f27_slot Ha0. f27_slot H91. f27_slot H22.
  (* 0x82604 bne a0,s4: both counts are u, not taken *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    f27_br false ltac:(rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.bv_eqb_refl; reflexivity).
  (* 0x82608 seqz a0,s9 ; 0x8260c slti a1,s4,0 ; 0x82610 li a2,-7 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
  (* 0x82614 beq a0,a1: seqz r = 1, slti u = 0, not taken *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    f27_br false ltac:(rewrite (f27F_slti0 u Hu63); vm_compute; reflexivity).
  (* 0x82618 ld t2,136(s1) = fr + 128 ; 0x8261c beqz s9: r = 0, taken to 0x82640 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. f27_brc true.
  (* 0x82640-0x82658: li a6,0 ; li a3,0 ; li a1,0 ; li a2,0 ; addi a4,s6,8 ; li a5,12 ; mv a0,a4 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.finish.
    all: OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.simp_regs; try reflexivity; try (f_equal; lia).
Qed.

(* ---- The r <> 0 arm (F27.v:229-255): 0x82604 -> 0x82750. The run reads the two spills [s1 + 136] and
   [s1 + 176] and the three ports words at fr + 128 / fr + 132 / fr + 136 (plain lw, no instrumented check). ---- *)
Lemma f27_rm_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (A1 fr : Z) (RNG : footprint),
  rg regs 25 (-1) -> rg regs 20 (-1) -> rg regs 10 (-1) -> rg regs 9 A1 ->
  ov_read_bytes rsegs mem (ULMemF.wa (A1 + 136)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 128))) ->
  ov_read_bytes rsegs mem (ULMemF.wa (A1 + 176)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) ->
  ov_read_bytes rsegs mem (ULMemF.wa (fr + 128)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
  ov_read_bytes rsegs mem (ULMemF.wa (fr + 132)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
  ov_read_bytes rsegs mem (ULMemF.wa (fr + 136)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
  rng RNG (A1 + 136) 8 -> rng RNG (A1 + 176) 8 ->
  rng RNG (fr + 128) 4 -> rng RNG (fr + 132) 4 -> rng RNG (fr + 136) 4 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x82750 /\ mem' = mem /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 25 = Z_to_bv 64 (fr + 64)))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82604) fp_csr None mem
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros regs mem A1 fr RNG Hs9 Hs4 Ha0 H91 RD136 RD176 RD0 RD4 RD8 R136 R176 RP0 RP4 RP8.
  cbv beta delta [ULMemF.wa] in RD136, RD176, RD0, RD4, RD8.
  rewrite f27F_mkR_of_expand.
  f27_slot Hs9. f27_slot Hs4. f27_slot Ha0. f27_slot H91.
  (* 0x82604 bne a0,s4: both -1, not taken *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. f27_brc false.
  (* seqz a0,s9 = 0 ; slti a1,s4,0 = 1 ; li a2,-7 ; 0x82614 beq a0,a1 not taken *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. f27_brc false.
  (* 0x82618 ld t2,136(s1) = fr + 128 ; 0x8261c beqz s9 (= -1) not taken *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. f27_brc false.
  (* 0x82620 lw a0,0(t2) = -7 ; 0x82624 ld s9,176(s1) = fr + 64 ; 0x82628 bne a0,a2 not taken *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. f27_brc false.
  (* 0x8262c lw a0,4(t2) = -7 ; 0x82630 bne a0,a2 not taken *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. f27_brc false.
  (* 0x82634 lw a0,8(t2) = -7 ; 0x82638 bne a0,a2 not taken *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. f27_brc false.
  (* 0x8263c j 82750 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.finish.
    all: OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.simp_regs; try reflexivity; try (f_equal; lia).
Qed.

(* ---- The extracted runs at ExecF.RNG_all. seg_F27 states no bound on the spill base A1 or on the frame base fr
   (it carries only `rg regs 9 A1` and the loaded values), so ExecF.rng_all cannot be applied to the rng premises
   from the run's own premises. Per the lane rule these corollaries are the `_bounded` form: the extracted
   statement with exactly `0 <= lo` and `lo + len <= 2 ^ 64` for the regions the run reads, inserted after the
   run's premises, and no verbatim pin. ---- *)
Lemma f27_r0_run_of_F_bounded : forall (regs : bvmap 5 word) (mem : word -> option byte) (A1 fr phi u : Z),
  rg regs 25 0 -> rg regs 20 u -> rg regs 10 u -> rg regs 9 A1 -> rg regs 22 (phi + 18) ->
  0 <= u < 2 ^ 63 ->
  ov_read_bytes rsegs mem (ULMemF.wa (A1 + 136)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 128))) ->
  0 <= A1 + 136 -> A1 + 136 + 8 <= 2 ^ 64 ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x8265c /\ mem' = mem /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 20 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 20 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 7 = Z_to_bv 64 (fr + 128) /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 10 = Z_to_bv 64 (phi + 26) /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 14 = Z_to_bv 64 (phi + 26) /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 15 = Z_to_bv 64 12 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 11 = Z_to_bv 64 0 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 12 = Z_to_bv 64 0 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 13 = Z_to_bv 64 0 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 16 = Z_to_bv 64 0))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82604) fp_csr None mem
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros regs mem A1 fr phi u Hs9 Hs4 Ha0 H91 H22 Hu63 RD136 B0 B1.
  eapply evtF_evt, (f27_r0_run_F regs mem A1 fr phi u RNG_all); try assumption.
  apply rng_all; lia.
Qed.

Lemma f27_rm_run_of_F_bounded : forall (regs : bvmap 5 word) (mem : word -> option byte) (A1 fr : Z),
  rg regs 25 (-1) -> rg regs 20 (-1) -> rg regs 10 (-1) -> rg regs 9 A1 ->
  ov_read_bytes rsegs mem (ULMemF.wa (A1 + 136)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 128))) ->
  ov_read_bytes rsegs mem (ULMemF.wa (A1 + 176)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) ->
  ov_read_bytes rsegs mem (ULMemF.wa (fr + 128)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
  ov_read_bytes rsegs mem (ULMemF.wa (fr + 132)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
  ov_read_bytes rsegs mem (ULMemF.wa (fr + 136)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
  0 <= A1 + 136 -> A1 + 136 + 8 <= 2 ^ 64 ->
  0 <= A1 + 176 -> A1 + 176 + 8 <= 2 ^ 64 ->
  0 <= fr + 128 -> fr + 128 + 4 <= 2 ^ 64 ->
  0 <= fr + 132 -> fr + 132 + 4 <= 2 ^ 64 ->
  0 <= fr + 136 -> fr + 136 + 4 <= 2 ^ 64 ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x82750 /\ mem' = mem /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 25 = Z_to_bv 64 (fr + 64)))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82604) fp_csr None mem
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros regs mem A1 fr Hs9 Hs4 Ha0 H91 RD136 RD176 RD0 RD4 RD8
    B0 B1 B2 B3 B4 B5 B6 B7 B8 B9.
  eapply evtF_evt, (f27_rm_run_F regs mem A1 fr RNG_all); try assumption;
    apply rng_all; lia.
Qed.

(* The shape checks: each bounded corollary is the extracted run's statement plus its bound premises, and nothing
   else -- from the extracted statement (at RNG_all) the bounded one follows by dropping them. *)
Lemma f27_r0_run_of_F_bounded_shape :
  (forall (regs : bvmap 5 word) (mem : word -> option byte) (A1 fr phi u : Z),
   rg regs 25 0 -> rg regs 20 u -> rg regs 10 u -> rg regs 9 A1 -> rg regs 22 (phi + 18) ->
   0 <= u < 2 ^ 63 ->
   ov_read_bytes rsegs mem (ULMemF.wa (A1 + 136)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 128))) ->
   LE.evt rsegs
     (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
        (pc' = Z_to_bv 64 0x8265c /\ mem' = mem /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 20 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 20 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 7 = Z_to_bv 64 (fr + 128) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 10 = Z_to_bv 64 (phi + 26) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 14 = Z_to_bv 64 (phi + 26) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 15 = Z_to_bv 64 12 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 11 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 12 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 13 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 16 = Z_to_bv 64 0))
     (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82604) fp_csr None mem
     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs))) ->
  (forall (regs : bvmap 5 word) (mem : word -> option byte) (A1 fr phi u : Z),
   rg regs 25 0 -> rg regs 20 u -> rg regs 10 u -> rg regs 9 A1 -> rg regs 22 (phi + 18) ->
   0 <= u < 2 ^ 63 ->
   ov_read_bytes rsegs mem (ULMemF.wa (A1 + 136)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 128))) ->
   0 <= A1 + 136 -> A1 + 136 + 8 <= 2 ^ 64 ->
   LE.evt rsegs
     (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
        (pc' = Z_to_bv 64 0x8265c /\ mem' = mem /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 20 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 20 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 7 = Z_to_bv 64 (fr + 128) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 10 = Z_to_bv 64 (phi + 26) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 14 = Z_to_bv 64 (phi + 26) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 15 = Z_to_bv 64 12 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 11 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 12 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 13 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 16 = Z_to_bv 64 0))
     (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82604) fp_csr None mem
       (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs))).
Proof.
  intros H. intros. eapply H; eassumption.
Qed.

Lemma f27_rm_run_of_F_bounded_shape :
  (forall (regs : bvmap 5 word) (mem : word -> option byte) (A1 fr : Z),
   rg regs 25 (-1) -> rg regs 20 (-1) -> rg regs 10 (-1) -> rg regs 9 A1 ->
   ov_read_bytes rsegs mem (ULMemF.wa (A1 + 136)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 128))) ->
   ov_read_bytes rsegs mem (ULMemF.wa (A1 + 176)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) ->
   ov_read_bytes rsegs mem (ULMemF.wa (fr + 128)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
   ov_read_bytes rsegs mem (ULMemF.wa (fr + 132)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
   ov_read_bytes rsegs mem (ULMemF.wa (fr + 136)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
   LE.evt rsegs
     (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
        (pc' = Z_to_bv 64 0x82750 /\ mem' = mem /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 25 = Z_to_bv 64 (fr + 64)))
     (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82604) fp_csr None mem
     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs))) ->
  (forall (regs : bvmap 5 word) (mem : word -> option byte) (A1 fr : Z),
   rg regs 25 (-1) -> rg regs 20 (-1) -> rg regs 10 (-1) -> rg regs 9 A1 ->
   ov_read_bytes rsegs mem (ULMemF.wa (A1 + 136)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 128))) ->
   ov_read_bytes rsegs mem (ULMemF.wa (A1 + 176)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) ->
   ov_read_bytes rsegs mem (ULMemF.wa (fr + 128)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
   ov_read_bytes rsegs mem (ULMemF.wa (fr + 132)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
   ov_read_bytes rsegs mem (ULMemF.wa (fr + 136)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (-7))) ->
   0 <= A1 + 136 -> A1 + 136 + 8 <= 2 ^ 64 ->
   0 <= A1 + 176 -> A1 + 176 + 8 <= 2 ^ 64 ->
   0 <= fr + 128 -> fr + 128 + 4 <= 2 ^ 64 ->
   0 <= fr + 132 -> fr + 132 + 4 <= 2 ^ 64 ->
   0 <= fr + 136 -> fr + 136 + 4 <= 2 ^ 64 ->
   LE.evt rsegs
     (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
        (pc' = Z_to_bv 64 0x82750 /\ mem' = mem /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 25 = Z_to_bv 64 (fr + 64)))
     (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82604) fp_csr None mem
       (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs))).
Proof.
  intros H. intros. eapply H; eassumption.
Qed.

End RunF.

(* ---- The compiled source tie (a Theorem Labs lane 04:24Z, auditor a Theorem Labs lane's condition). This file has no constr_eq pin,
   so the tie is this lemma: its TYPE is F27.seg_F27's own closed type, and its proof is seg_F27's own script
   (F27.v:141-278) line for line, with the one evt step of each arm -- the `sl_run` argument that F27.v:165-191
   and F27.v:229-255 prove inline -- replaced by an application of this file's old form
   (f27_r0_run_of_F_bounded / f27_rm_run_of_F_bounded, i.e. the twins at ExecF.RNG_all). It compiles only if the
   extracted runs are exactly the runs seg_F27 consumes, so it machine-checks the "same stretch" claim.
   Source cut lemma: F27.seg_F27 (F27.v:139). Per run: f27_r0_run <- the r = 0 arm F27.v:165-191, consumed at
   F27.v:165; f27_rm_run <- the r <> 0 arm F27.v:229-255, consumed at F27.v:229.
   Generalisations of the extracted statements, all discharged here from seg_F27's own context: t_rp (g_in g) j
   -> 0 (Er, F27.v:161) and -> -1 (Er', b7_unk_rpm, F27.v:224); t_unk (g_in g) j -> u (0 <= u < 2 ^ 63 from
   b7_unk_rp0, F27.v:163-164) and -> -1 (Eu, F27.v:224); [s1 + 136] -> fr + 128 and [s1 + 176] -> fr + 64 (B7K's
   spills HS136 / HS176, F27.v:154-160); the three ports words -> -7 (PORTS, F27.v:225).
   The address bounds the `_of_F_bounded` corollaries ask for come from seg_F27's own context and from nothing
   else: `0 <= A1 + 136` and `A1 + 136 + 8 <= 2 ^ 64` are the first two conjuncts of the spill's own
   `bytes_at` (HS136); the three ports bounds are the first two conjuncts of PORTS' own `u32`; and the two
   bounds on A1 + 176 need A1 = A (the FRA spill base), which is seg_F27's FRA record itself: FRA carries
   `rg regs 9 A` with `0 <= A` and `A + 416 <= 2 ^ 64`, and the two bases agree modulo 2 ^ 64 (both are
   `getr regs 9`), which with A1's own range forces A1 = A. Nothing is weakened and no premise is added. *)
Section SrcTie.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.

Lemma seg_F27_src : ltac:(let T := type of F27.seg_F27 in exact T).
Proof.
  intros B APIf SH SK ra empty FF j H0 H1 g c HInv.
  pose proof (proj1 FF) as SEGS.
  unfold Inv_A82604_at, B7CUT in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HK &
    Hs9 & Hs4 & Ha0 & HPO & HFI & Had1 & Had2). subst c.
  rewrite SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  rewrite Hasz in HFRA, HENT.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin0 & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  (* FRA's own bounds on its spill base A: A + 416 <= g_S g < APPMEM_END, and 0 < sp <= A because the slot
     window [g_S g - SLOT_STACK, g_S g) is a present stack window (FRA's own stk conjunct). *)
  assert (HAb : 0 <= A /\ A + 416 <= 2 ^ 64).
  { pose proof Hwin0 as (HW0 & HW1 & _).
    unfold AF.SLOT_STACK, APPMEM_END in *. lia. }
  pose proof HK as (HLK & H23 & H22 & Hphi0 & Hphi50 & Hflen & Hblk & Hs280 & H24 & H18 & H152 & Hg & Hph & Hlen &
    HLT & HS136 & HS120 & HS176).
  destruct HS136 as (A1 & H91 & Hq136).
  destruct HS176 as (A3 & H93 & Hq176).
  pose proof (f27_rd8 mem _ _ Hq136 ltac:(apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8)) as
    RD136.
  pose proof (f27_rd8 mem _ _ Hq176 ltac:(apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8)) as
    RD176.
  assert (EW : ULMem.wa (A3 + 176) = ULMem.wa (A1 + 176)).
  { apply f27_wa_shift. unfold rg in H91, H93. rewrite <- H91, <- H93. reflexivity. }
  rewrite EW in RD176. clear EW.
  (* the bounds of the spill cell [s1 + 136], from its own bytes_at *)
  pose proof Hq136 as (HB136a & HB136b & _).
  rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8 in HB136b.
    change (Z.of_nat 8) with 8 in HB136b.
  (* the FRA spill base A and the B7K base A1 are the same register, so they are the same Z *)
  assert (HA9 : forall A2, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 = Z_to_bv 64 A2
    -> - 408 <= A2 -> A2 < 2 ^ 64 -> A2 = A).
  { intros A2 H2 Hlo2 Hhi2. unfold rg in Hr9. rewrite H2 in Hr9.
    apply (f_equal (@bv_unsigned 64)) in Hr9.
      rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit_wrap in Hr9.
    Z.div_mod_to_equations. lia. }
  assert (EA1 : A1 = A) by (apply HA9; [unfold rg in H91; exact H91 | lia | lia]).
  destruct (Z.eq_dec (t_rp (g_in g) j) 0) as [Er|Er].
  - (* r = 0: the loop registers are set; exit at 0x8265c. *)
    destruct (b7_unk_rp0 _ _ Er) as (Hu & _).
    assert (Hu63 : 0 <= t_unk (g_in g) j < 2 ^ 63) by lia.
    rewrite Er in Hs9.
    apply (sl_run regs (Z_to_bv 64 0x82604) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x8265c /\ mem' = mem /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 20 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 20 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 7 = Z_to_bv 64 (fr + 128) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 10 = Z_to_bv 64 (phi + 26) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 14 = Z_to_bv 64 (phi + 26) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 15 = Z_to_bv 64 12 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 11 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 12 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 13 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 16 = Z_to_bv 64 0)
      (Post B APIf ra g)).
    + exact Hhalt.
    + (* the inline run of F27.v:178-191, as this file's old form *)
      apply f27F_ul_of_lib.
      exact (f27_r0_run_of_F_bounded regs mem A1 fr phi (t_unk (g_in g) j)
               Hs9 Hs4 Ha0 H91 H22 Hu63 RD136 ltac:(lia) ltac:(lia)).
    + intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR26 & HR20 & HR21 & HR22 & HR23 & HR24 & HR18 &
         HR7 & HR10 & HR14 & HR15 & HR11 & HR12 & HR13 & HR16) Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply H0.
      unfold Inv_A8265c_at, B7CUT.
      exists phi, regs'', mem, md', fr.
      rewrite ?Hasz.
      cbv beta.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs regs'' mem md md' HFRA);
          [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
          | rewrite Hreg; exact HR26 | exact Hmat ]. }
      split; [exact (ent_mat APIf g (hb1 phi (flen g j)) mem md md' HENT Hmat)|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [apply (b7_flsi_regs g j fr regs regs'' mem HFLSI); rewrite Hreg; exact HR9|].
      split; [apply (b7_B7K_regs g j phi fr regs regs'' mem HK); rewrite Hreg; assumption|].
      split; [exact Er|].
      split; [lia|].
      split; [unfold rg; rewrite Hreg, HR20; exact Hs4|].
      split; [unfold rg; rewrite Hreg; exact HR7|].
      split; [exact HPO|].
      split; [exact HFI|].
      split; [unfold rg; rewrite Hreg; exact HR10|].
      split; [unfold rg; rewrite Hreg; exact HR14|].
      split; [unfold rg; rewrite Hreg; exact HR15|].
      split; [unfold rg; rewrite Hreg; exact HR11|].
      split; [unfold rg; rewrite Hreg; exact HR12|].
      split; [unfold rg; rewrite Hreg; exact HR13|].
      unfold rg; rewrite Hreg; exact HR16.
  - (* r <> 0: r = unk = -1, the three ports words are -7; exit at 0x82750. *)
    destruct (b7_unk_rpm _ _ Er) as (Er' & Eu).
    destruct (proj2 HPO Er) as (P0 & P4 & P8).
    pose proof (f27_rd4 mem _ _ P0 ltac:(apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4)) as
      RD0.
    pose proof (f27_rd4 mem _ _ P4 ltac:(apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4)) as
      RD4.
    pose proof (f27_rd4 mem _ _ P8 ltac:(apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4)) as
      RD8.
    (* the bounds of the three ports words, from their own u32 *)
    pose proof P0 as (PB0a & PB0b & _).
      rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4 in PB0b.
      change (Z.of_nat 4) with 4 in PB0b.
    pose proof P4 as (PB4a & PB4b & _).
      rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4 in PB4b.
      change (Z.of_nat 4) with 4 in PB4b.
    pose proof P8 as (PB8a & PB8b & _).
      rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4 in PB8b.
      change (Z.of_nat 4) with 4 in PB8b.
    rewrite Er' in Hs9. rewrite Eu in Hs4, Ha0.
    apply (sl_run regs (Z_to_bv 64 0x82604) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x82750 /\ mem' = mem /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 2 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 3 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 3 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 4 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 4 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 8 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 8 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 9 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 19 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 19 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 26 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 21 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 21 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 22 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 23 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 23 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 24 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 24 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 18 =
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 18 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr R 25 = Z_to_bv 64 (fr + 64))
      (Post B APIf ra g)).
    + exact Hhalt.
    + (* the inline run of F27.v:238-255, as this file's old form *)
      apply f27F_ul_of_lib.
      exact (f27_rm_run_of_F_bounded regs mem A1 fr Hs9 Hs4 Ha0 H91 RD136 RD176 RD0 RD4 RD8
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR26 & HR21 & HR22 & HR23 & HR24 & HR18 & HR25)
        Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply H1.
      unfold Inv_A82750_at.
      exists phi, regs'', mem, md', fr.
      rewrite ?Hasz.
      cbv beta.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs regs'' mem md md' HFRA);
          [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
          | rewrite Hreg; exact HR26 | exact Hmat ]. }
      split; [exact (ent_mat APIf g (hb1 phi (flen g j)) mem md md' HENT Hmat)|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      assert (HFLSI' : FLSI g j fr regs'' mem)
        by (apply (b7_flsi_regs g j fr regs regs'' mem HFLSI); rewrite Hreg; exact HR9).
      split; [exact HFLSI'|].
      apply (b7_a826a4 g j phi fr regs'' mem HFLSI').
      * apply (b7_B7K_regs g j phi fr regs regs'' mem HK); rewrite Hreg; assumption.
      * unfold rg; rewrite Hreg; exact HR25.
Qed.

End SrcTie.

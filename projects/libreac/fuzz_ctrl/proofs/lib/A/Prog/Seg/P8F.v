(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 104 of its 130 lines of code are new or changed and 370 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P8.v, with its module paths and module names changed; 45 of its 95 lines of code are new or changed and 80 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/P8.v blob a7df44fac3a8 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives P8.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of P8.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)
(* The footprint twin of P8.v p8_evt (0x81c20-0x81c30, four instructions and the call of reac_ports_parse with
   q = a1 = 0, which fails and writes only its 16-byte frame [sp - 16, sp)). The four instructions of the segment
   itself touch no memory (a branch and three register moves), so the run's only footprint premise is the callee
   window, the premise reac_ports_parse_contract_F states. The callee premise sits where P8.v's Section Hypothesis
   HPP sits, with the footprint contract in place of the plain one. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot P7 P8.
(* Last: StepF's step / if_true / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

Section CallF.
(* The callee's footprint contract, in the position of P8.v's Section Hypothesis HPP. *)
Hypothesis HPPF : reac_ports_parse_contract_F.

Lemma p8_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    a0 = Z_to_bv 64 (-1) -> s2 = Z_to_bv 64 (-1) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_PARSE_FRAME <= bv_unsigned sp ->
    ExecF.rng RNG (bv_unsigned sp - REAC_PORTS_PARSE_FRAME) REAC_PORTS_PARSE_FRAME ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' t3' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c34) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  Fr (Z_to_bv 64 0x81c34) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_PORTS_PARSE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c20) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m lo -> -> HST Hlo RFR.
  step. (* 81c20 beq a0,s2,81c28 *)
  if_true.
  step. step. (* 81c28 mv a0,s5; 81c2c li a1,0 *)
  step. (* 81c30 jal reac_ports_parse *)
  pose proof HPPF as HP. unfold reac_ports_parse_contract_F, REAC_PORTS_PARSE in HP.
  eapply ExecF.evtF_cut.
  { eapply HP with (p := bv_unsigned s5) (q := 0) (lo := lo) (bs := repeat (Z_to_bv 8 0) 20).
    all: try (symmetry; apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.Z_to_bv_bv_unsigned).
    all: try reflexivity.
    all: try assumption.
    all: try (intros _ HH; exfalso; apply HH; reflexivity).
    all: try exact (u64_range _).
    all: lia. }
  intros ms' (t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & WM & MIi & ST' & Hif).
  subst ms'.
  rewrite ports_ok_q0 in Hif |- *. cbv iota in Hif |- *.
  replace (ret_pc (Z_to_bv 64 531508)) with (Z_to_bv 64 531508)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  do 11 eexists. exists m'.
  split; [reflexivity|].
  split; [exact Hif|]. split; [exact WM | exact ST'].
Qed.

(* P8.p8_evt's statement (after its callee premise) as a corollary: p8_evt_F at RNG_all, the rng premise by
   rng_all. *)
Lemma p8_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    a0 = Z_to_bv 64 (-1) -> s2 = Z_to_bv 64 (-1) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_PARSE_FRAME <= bv_unsigned sp ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' t3' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c34) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  Fr (Z_to_bv 64 0x81c34) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_PORTS_PARSE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c20) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m lo E0 E2 HST Hlo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof HST as (ST0 & _ & _).
  eapply ExecF.evtF_evt, (p8_evt_F ExecF.RNG_all); try eassumption.
  unfold REAC_PORTS_PARSE_FRAME in *. apply ExecF.rng_all; lia.
Qed.

End CallF.

(* The pin: p8_evt_of_F states P8.p8_evt's text after its first premise, term for term (constr_eq: syntactic, not
   up to conversion); the two first premises are the plain and the footprint contract of reac_ports_parse. *)
Example p8_evt_of_F_verbatim : True.
Proof.
  lazymatch type of P8.p8_evt with ?P -> ?A =>
  lazymatch type of p8_evt_of_F with ?Q -> ?B =>
    constr_eq P reac_ports_parse_contract;
    constr_eq Q reac_ports_parse_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.

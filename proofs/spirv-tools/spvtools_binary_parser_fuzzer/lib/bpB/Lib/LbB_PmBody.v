(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_PmBase LbB_PmOwn LbB_PiStmt LbB_PmOL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section BODY.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Hypothesis IHEAD : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PI0A H LINV w s LB LBs m mo c msF R F fc -> EXITKA H LINV w (c_widx c) Q ->
    U2HK H LINV w c F fc Q -> as_SR H Q (mkCfg msF mo).

  Hypothesis OHEAD : forall (w : pmwA H) (I : ictxR) s LB LBs m mo c msF R F fc (Q : config -> Prop) (lw : Z),
    pmw_okA H w -> OLIA H LINV w s LB LBs m mo c msF R F fc I -> c_widx c < i_io I + i_iwc I -> EXITKA H LINV w lw Q ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc', OLIA H LINV w s' LB' LBs' m' mo' c' msF' R' F' fc' I ->
       omeas I c' < omeas I c -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).

  Hypothesis XEXIT : forall (w : pmwA H) (I : ictxR) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> OLIA H LINV w s LB LBs m mo c msF R F fc I -> i_io I + i_iwc I <= c_widx c ->
    EXITKA H LINV w (i_io I) Q -> as_SR H Q (mkCfg msF mo).

  Lemma pm_oloopB : forall (w : pmwA H) (I : ictxR) (Q : config -> Prop), pmw_okA H w -> EXITKA H LINV w (i_io I) Q ->
    forall s LB LBs m mo c msF R F fc, OLIA H LINV w s LB LBs m mo c msF R F fc I -> as_SR H Q (mkCfg msF mo).
  Proof.
    intros w I Q OK EK.
    assert (IND : forall k s LB LBs m mo c msF R F fc, Z.to_nat (omeas I c) = k ->
                    OLIA H LINV w s LB LBs m mo c msF R F fc I -> as_SR H Q (mkCfg msF mo)).
    { intros k. induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf).
      intros s LB LBs m mo c msF R F fc Hk HOLI.
      assert (Hm0 : 0 <= omeas I c) by (unfold omeas; pose proof (zw_next_range (t3b (c_v3 c))); lia).
      destruct (Z.lt_ge_cases (c_widx c) (i_io I + i_iwc I)) as [Hlt|Hge].
      - apply (OHEAD w I s LB LBs m mo c msF R F fc Q (i_io I) OK HOLI Hlt EK).
        intros s' LB' LBs' m' mo' c' msF' R' F' fc' HOLI' HM.
        assert (Hm0' : 0 <= omeas I c') by (unfold omeas; pose proof (zw_next_range (t3b (c_v3 c'))); lia).
        eapply (IH (Z.to_nat (omeas I c'))); [lia | reflexivity | exact HOLI'].
      - exact (XEXIT w I s LB LBs m mo c msF R F fc Q OK HOLI Hge EK). }
    intros s LB LBs m mo c msF R F fc HOLI. exact (IND _ s LB LBs m mo c msF R F fc eq_refl HOLI).
  Qed.

  Theorem pm_bodyB : pm_body_allB H LINV.
  Proof.
    intros w Q s LB LBs m mo c msF R F fc OK P0 EK.
    apply (IHEAD w s LB LBs m mo c msF R F fc Q OK P0 EK).
    intros I s' LB' LBs' m' mo' c' msF' R' HOLI Hio.
    rewrite <- Hio in EK.
    exact (pm_oloopB w I Q OK EK s' LB' LBs' m' mo' c' msF' R' F fc HOLI).
  Qed.
End BODY.

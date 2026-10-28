(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3 SymTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmLH LbB_PmOL LbB_TablStmt LbB_PmLeaf LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_PmU2K LbB_PmWXK.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma sx32A_range : forall e, 0 <= e < 2 ^ 32 -> 0 <= sx32A e < 2 ^ 64.
Proof. intros e He. unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec e (2 ^ 31)); lia. Qed.
Lemma sx32A_nz : forall e, 0 < e < 2 ^ 32 -> sx32A e <> 0.
Proof. intros e He. unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec e (2 ^ 31)); lia. Qed.
Lemma ev_sextw_sx32A : forall E (a : expr) (e : Z), edenot E a = Z_to_bv 64 (sx32A e) -> 0 <= e < 2 ^ 32 ->
  edenot E (EAluw ALU_ADD a (ELit 0)) = Z_to_bv 64 (sx32A e).
Proof.
  intros E a e Ha He. cbn [edenot]. rewrite Ha. rewrite aluw_add_0. unfold PropExec.v_lw.
  pose proof (sx32A_range e He) as R. rewrite (u64_of_Z (sx32A e) R).
  rewrite <- (bv_swrap_wrap' 32 (sx32A e)).
  replace (bv_wrap 32 (sx32A e)) with e.
  - exact (swrap32_sx32A e He).
  - unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). unfold sx32A, PrsGrammar.sx32.
    destruct (Z.ltb_spec e (2 ^ 31)); [rewrite Z.mod_small by lia; reflexivity|].
    replace (e + 2 ^ 64 - 2 ^ 32) with (e + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. reflexivity.
Qed.

Ltac intbl_incl := apply LbB_PmU2K.tbl_incl; vm_compute; reflexivity.

Section TCK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Lemma HHc : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Theorem pm_checkkA : forall (w : pmwA H) (lw : Z) (Q : config -> Prop),
    pmw_okA H w -> EXITKA H LINV w lw Q -> CHECKKA H LINV w Q.
  Proof.
    intros w lw Q OK KX.
    intros s LB LBs m mo c msF R F fc tbl spal e X00 INCL Htr BUD Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 G23 He.
    assert (X0 : PMXAT H LINV w s LB LBs m mo c (OB_PARSED_OPERAND :: S_INSTR) TBL_EEF44 [] [] spal).
    { eapply pmxa_restrict; first [exact HHc | exact LINV_frame | exact OK | exact X00 | exact INCL | apply incl_refl | idtac].
      all: first [exact HHc | exact LINV_frame | exact OK | exact X00 | exact INCL | apply incl_refl]. }
    clear X00.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (env_world_seed H w R []) as HE.
    assert (E23 : edenot (Eseed R (wenv_vals w ++ [])) (EAluw ALU_ADD (EVar 23) (ELit 0)) = Z_to_bv 64 (sx32A e)).
    { apply (ev_sextw_sx32A _ (EVar 23) e); [exact G23 | lia]. }
    pose proof (sx32A_range e ltac:(lia)) as SXR. pose proof (sx32A_nz e He) as SXN.
    pm_go HHc LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word) [KWord (SA (EVar 32) 93) 1 (ELit 0)]
          300%nat [EXIT_RET; EXIT_OPC; EXIT_IWC] [false] 41%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_EXIT.
    { split_scs. all: first [ cbn [sc_denot]; rewrite ?E23, ?ev_lit0; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia
                            | match goal with |- ?g => idtac "SCLEFT" g end ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    set (r := if e <? 2 ^ 31 then e else e - 2 ^ 32).
    assert (Hr : - 2 ^ 31 <= r < 2 ^ 31 /\ r <> 0).
    { subst r. destruct (Z.ltb_spec e (2 ^ 31)); lia. }
    assert (Er : Z_to_bv 64 (sx32A e) = Z_to_bv 64 r).
    { subst r. unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec e (2 ^ 31)); [reflexivity|].
      apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      replace (e + 2 ^ 64 - 2 ^ 32) with ((e - 2 ^ 32) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity. }
    eapply (KX s LB LBs M1 mo1 c msF1 R1 F fc EXIT_RET S_INSTR r).
    - constructor.
      + exists TBL_EEF44, spal. split; [exact X1 | split; [intbl_incl | intros Hr0; exfalso; lia]].
      + exact KR1.
      + exact VIS1.
      + exact RF1.
      + exact FZ0.
      + exact (regs_tbl_restrict w [] _ R1 RT_EXIT HTx1 ltac:(vm_compute; reflexivity)).
      + rewrite (HR1 3%bv); exact G3_0.
      + rewrite (HR1 4%bv); exact G4_0.
      + split; [rewrite (HR1 23%bv); rewrite <- Er; exact G23 | lia].
      + exact Htr.
      + exact Hbsz.
      + intros Hr0. exfalso. lia.
    - left. split; reflexivity.
  Qed.
End TCK.

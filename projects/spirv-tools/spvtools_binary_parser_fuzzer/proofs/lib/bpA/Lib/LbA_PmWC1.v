(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3 SymTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_RtOwn LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmCall LbA_PmXp LbA_PmGlue LbA_PmVops LbA_PmHdr LbA_PmLH LbA_PmOL LbA_TablStmt LbA_PmLeaf LbA_PmExit LbA_PmInit LbA_PmFin LbA_PmExit2 LbA_PmU2K LbA_PmWT2.
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

Ltac intbl_incl := apply LbA_PmU2K.tbl_incl; vm_compute; reflexivity.

Section TCK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Lemma HHc : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Theorem pm_checkkA : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      (F0 : bvmap 5 word) (fc0 : bv 32),
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    pmw_okA H w ->
    CHECKKA H LINV w (pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 st0 LB0 LF p c0 lo B shi m0 mo0).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi F0 fc0 w OK.
    intros s LB LBs m mo c msF R F fc tbl spal e X00 INCL Htr BUD Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 G25 He.
    pose proof (pmxa_restrict H HHc LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X00 INCL ltac:(intros ke Hke; exact Hke)) as X0.
    clear X00.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (env_world_seed H w R []) as HE.
    assert (E25 : edenot (Eseed R (wenv_vals w ++ [])) (EAluw ALU_ADD (EVar 25) (ELit 0)) = Z_to_bv 64 (sx32A e)).
    { apply (ev_sextw_sx32A _ (EVar 25) e); [exact G25 | lia]. }
    pose proof (sx32A_range e ltac:(lia)) as SXR. pose proof (sx32A_nz e He) as SXN.
    pm_go HHc LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word) [KWord (SA (EVar 32) 93) 1 (ELit 0)]
          300%nat [0xee140; 0xee7d8] [false; true] 41%N S_MODULE (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_EDFB0.
    { split_scs. all: first [ cbn [sc_denot]; rewrite ?E25, ?ev_lit; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia
                            | match goal with |- ?g => idtac "SCLEFT" g end ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    eapply (pm_epi_e H HHbp LINV LINV_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi
              s LB LBs M1 mo1 c TBL_EEF44 spal msF1 R1 F fc OK X1);
      [intbl_incl | exact Htr | exact Hbsz | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | exact (regs_tbl_restrict w [] _ R1 RT_EDFB0 HTx1 ltac:(vm_compute; reflexivity))
      | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0].
  Qed.
End TCK.

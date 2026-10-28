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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase PmHyps PrsGrammar PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablGrammar TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RtOwn LbB_DStat LbB_TablStmt LbB_ContStmt LbB_PmLeaf LbB_PmLeafW LbB_PmLH LbB_PmVops LbB_PmVup LbB_PmU2K LbB_PmOL LbB_PmWG LbB_PmWPT.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmOHD LbB_PmU2H LbB_PmOH LbB_PmWX2 LbB_PmWX3 LbB_PmWX5 LbB_PmWX LbB_PmWT4 LbB_PmWC1 LbB_PmWZ7 LbB_PmU3L LbB_PmU3T LbB_PmU3X LbB_PmU3I LbB_PmU4E LbB_PmBody LbB_PmMain.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmOLX LbB_SnStmt LbB_PmU5M LbB_PmU6R LbB_PmU7 LbB_PmU9 LbB_MkStr LbB_TablITG LbB_PmS8T LbB_PmWNT LbB_PiStmt LbB_PmBody LbB_PmMain LbB_BiW32.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Strcmp3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Fixpoint zlist (a : Z) (n : nat) : list Z := match n with O => [] | S k => a :: zlist (a + 1) k end.
Lemma in_zlist : forall n a t, a <= t < a + Z.of_nat n -> In t (zlist a n).
Proof.
  induction n as [|n IH]; intros a t Ht; cbn [zlist]; [lia|].
  destruct (Z.eq_dec a t) as [E|NE]; [left; exact E | right; apply IH; rewrite Nat2Z.inj_succ in Ht; lia].
Qed.

Section ALL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.

  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HU16 : put_u16_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV ds_repA.
  Hypothesis HEXH : exhausted_stmtA H LINV.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.
  Hypothesis HPDIAGE : pdiagE_stmtA H LINV ds_repA.
  Hypothesis HINT : put_int_stmtA H LINV ds_repA.

  Hypothesis HTL : tabl_leavesA.
  Hypothesis HFW : fixword_stmtA.
  Hypothesis TFS : take_first_stmtA H.
  Hypothesis PTS : push_types_stmtA H.

  Hypothesis V4C : v4slow_stmt H V32_SLOW_CREF.
  Hypothesis V4R : v4slow_stmt H V32_SLOW_RREF.
  Hypothesis HVO : vopnd_slow_stmt H.
  Hypothesis HVOT : votpb_stmt H.

  Hypothesis HSN : setnum_stmtA H LINV.

  Lemma arms_allA : forall t, arm_stmtAX H LINV t (arm_pcA t).
  Proof.
    intros t.
    pose proof (arm_STR_AX H HHbp LINV LINV_frame LINV_cl LINV_relro HOWN ds_repA DSL HCSEQ HDTOR HU16 HU64 HPDIAG0 HEXH
                  (mkstr_ok H HHbp) (import_type_get_okA H HHbp (@RtB_Strcmp3.strcmp_icpt_ok HCEIL))) as STR.
    pose proof (arm_RID_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE HU32 HTL LINV_cl LINV_relro HOWN) as RID.
    pose proof (arm_MASK_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HU32 HTL PTS LINV_cl LINV_relro HOWN) as MSK.
    pose proof (arm_SPEC_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HPDIAGE HU32 HTL PTS LINV_cl LINV_relro HOWN) as SPC.
    pose proof (arm_TYL_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HU32 HTL LINV_cl LINV_relro HSN) as TYL.
    pose proof (arm_DEFAULT_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HINT) as DF.
    pose proof (arm_ID_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE HU32 HTL LINV_cl LINV_relro) as IDA.
    pose proof (arm_LITINT_A H HHbp LINV LINV_frame) as LI. pose proof (arm_LITFLOAT_A H HHbp LINV LINV_frame) as LF'.
    pose proof (arm_TYPEID_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE) as TY.
    pose proof (arm_SCOPE_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HTL LINV_relro) as SC.
    pose proof (arm_EXTNUM_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HU32 HTL HVOT PTS LINV_cl LINV_relro HOWN) as EX.
    pose proof (arm_ENUM_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HU32 HTL PTS LINV_cl LINV_relro HOWN) as EN.
    pose proof (arm_SRCLANG_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HU32 HTL PTS LINV_cl LINV_relro HOWN) as SL.
    unfold arm_pcA.
    destruct (Z.lt_ge_cases t 1) as [H0|H1].
    { replace ((1 <=? t) && (t <=? 107))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). apply arm_AX_of_A, DF. }
    destruct (Z.lt_ge_cases 107 t) as [H2|H3].
    { replace ((1 <=? t) && (t <=? 107))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia). apply arm_AX_of_A, DF. }
    pose proof (in_zlist 107 1 t ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as HIn. vm_compute in HIn.
    repeat match type of HIn with
           | _ \/ _ => destruct HIn as [HIn|HIn];
               [subst t; lazymatch goal with |- arm_stmtAX _ _ ?tt ?pc => let v := eval vm_compute in pc in change pc with v end;
                first [ apply STR; lia | apply arm_AX_of_A ];
                first [ apply RID; reflexivity | apply SPC; reflexivity | apply TYL; lia
                      | apply IDA; lia | apply LI; lia | apply LF'; reflexivity | apply TY; reflexivity | apply SC; lia
                      | apply SL; reflexivity | exact EX | apply MSK; inlist | apply EN; inlist | apply DF ] |]
           | False => destruct HIn
           end.
  Qed.

  Let HHa : asan_rt_hyps H := rt_bp_base H HHbp.

  Theorem pm_body_allB_all : pm_body_allB H LINV.
  Proof.
    apply (pm_bodyB H LINV).
    - exact (@pm_ihead HCEIL H HHbp LINV LINV_frame LINV_cl LINV_relro HOWN HTL V4C PTS ds_repA DSL HCSEQ HDTOR HU16 HPDIAG0).
    - intros w I s LB LBs m mo c msF R F fc Q lw.
      exact (@LbB_PmOH.pm_oheadA HCEIL H HHbp LINV LINV_frame LINV_cl LINV_relro HOWN HTL TFS arms_allA
               (pm_push_tailAX H HHbp LINV LINV_frame LINV_cl HOWN HVO (biw32_ok H HHa V4R) HFW HEXH)
               (pm_checkkA H HHbp LINV LINV_frame)
               (pm_ohz H HHbp LINV LINV_frame HTL ds_repA DSL HCSEQ HDTOR HU16 HU64 HPDIAG0)
               HEXH w I s LB LBs m mo c msF R F fc Q lw).
    - exact (pm_xexitA H HHbp LINV LINV_frame HTL ds_repA DSL HCSEQ HDTOR HU16 HU64 HPDIAG0 (pm_nt_emplace H HHbp LINV LINV_cl HOWN)).
  Qed.

  Theorem parse_inst_okB_all : parse_inst_stmtB H LINV.
  Proof using HHbp LINV_frame LINV_cl LINV_relro HOWN ds_repA DSL HCTOR HCSEQ HDTOR HU16 HU32 HU64 HEXH HPDIAG0 HPDIAGE HINT
    HTL HFW TFS PTS V4C V4R HVO HVOT HSN.
    exact (parse_inst_okB H HHbp LINV LINV_frame pm_body_allB_all).
  Qed.
End ALL.

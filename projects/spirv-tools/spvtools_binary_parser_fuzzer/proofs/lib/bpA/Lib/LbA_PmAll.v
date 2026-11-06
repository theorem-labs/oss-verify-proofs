(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase PmHyps PrsGrammar PmZw PmODefsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablGrammar TablFacts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmXp LbA_PmExit LbA_PmInit LbA_PmFin LbA_PmExit2 LbA_DiagStmt LbA_PmDS LbA_PmGlue.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_RtOwn LbA_DStat LbA_TablStmt LbA_ContStmt LbA_PmLeaf LbA_PmLeafW LbA_PmLH LbA_PmVops LbA_PmVup LbA_PmU2K LbA_PmU2D LbA_PmOL LbA_PmWG LbA_PmWPT.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PmOHD LbA_PmU2 LbA_PmOH LbA_PmU2Dz LbA_PmU2Lz LbA_PmOHX LbA_PmWX2 LbA_PmWX3 LbA_PmWX5 LbA_PmWX LbA_PmWT4 LbA_PmWC1 LbA_PmWZ7 LbA_PmU3L LbA_PmU3T LbA_PmU3X LbA_PmU3I LbA_PmU4E LbA_PmBody LbA_PmMain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PmOLX LbA_SnStmt LbA_PmU5M LbA_PmU6R LbA_PmU7 LbA_PmU9 LbA_MkStr LbA_TablITG LbA_PmS8T LbA_PmWNT.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtA_Strcmp3.
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

  Lemma HNT : forall (w : pmwA H) s LB LBs m mo c msF R F fc (ty wd enc rid : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf33c4) fc None m (seg_rom asegs) -> rfull R -> frm_zero fc ->
    regs_tbl w R RT_3054 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 25%bv = Z_to_bv 64 ty -> 0 <= ty <= 3 -> PropExec.getr R 23%bv = Z_to_bv 64 wd -> 0 <= wd < 2 ^ 64 ->
    PropExec.getr R 19%bv = Z_to_bv 64 enc -> 0 <= enc < 2 ^ 64 ->
    rw_cells asegs m (wa_ff w + 10436) [C4 (Z_to_bv 64 rid)] -> 0 <= rid < 2 ^ 32 ->
    c_tr c = [] -> pm_bud (wa_n w) c -> 2 * (Zlength (t3c (c_m2 c)) + 1) <= wa_n w + 2 ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> 8 * t3b (c_m2 c) <= 16 * Zlength (t3c (c_m2 c)) + 504 ->
    (forall s' LB' LBs' m' mo' msF' R' F' fc' tbl' (t : Z * Z * list (Z * (Z * (Z * Z * Z)))),
       as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 0xf3d2c) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' ->
       PMXA H LINV w s' LB' LBs' m' mo' (set_m2A c t) S_INSTR tbl' [] -> incl TBL_X5 tbl' ->
       regs_tbl w R' RT_X5 -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
       c_tr (set_m2A c t) = [] -> pm_bud (wa_n w) (set_m2A c t) -> (forall q k, In (q, k) (c_blocks (set_m2A c t)) -> k <= 2 ^ 40) ->
       Zlength (t3c (c_m2 c)) <= Zlength (t3c t) <= Zlength (t3c (c_m2 c)) + 1 -> 8 * t3b t <= 16 * Zlength (t3c t) + 504 ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof. exact (pm_nt_emplace H HHbp LINV LINV_cl HOWN). Qed.

  Hypothesis HSN : setnum_stmtA H LINV.

  Lemma ARM_STR : forall t, (t = 11 \/ t = 48) -> arm_stmtAX H LINV t 0xefac0.
  Proof.
    exact (arm_STR_AX H HHbp LINV LINV_frame LINV_cl LINV_relro HOWN ds_repA DSL HCSEQ HDTOR HU16 HU64 HPDIAG0 HEXH
             (mkstr_ok H HHbp) (import_type_get_okA H HHbp (@RtA_Strcmp3.strcmp_icpt_ok HCEIL))).
  Qed.

  Lemma ARM_RID : forall t, t = 3 -> arm_stmtA H LINV t 0xf043c.
  Proof. exact (arm_RID_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE HU32 HTL LINV_cl LINV_relro HOWN). Qed.
  Lemma ARM_MASK : forall t, In t MASK_TYPES -> arm_stmtA H LINV t 0xef260.
  Proof. exact (arm_MASK_A H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTL PTS LINV_cl LINV_relro HOWN). Qed.
  Lemma ARM_SPEC : forall t, t = 8 -> arm_stmtA H LINV t 0xf00e8.
  Proof. exact (arm_SPEC_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HPDIAGE HU32 HTL PTS LINV_cl LINV_relro HOWN). Qed.
  Lemma ARM_TYL : forall t, (t = 9 \/ t = 47) -> arm_stmtA H LINV t 0xefe0c.
  Proof. exact (arm_TYL_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HU32 HTL LINV_cl LINV_relro HSN). Qed.

  Lemma arms_allA : forall t, arm_stmtAX H LINV t (arm_pcA t).
  Proof.
    intros t.
    pose proof (arm_DEFAULT_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HINT) as DF.
    pose proof (arm_ID_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE HU32 HTL LINV_cl LINV_relro) as IDA.
    pose proof (arm_LITINT_A H HHbp LINV LINV_frame) as LI. pose proof (arm_LITFLOAT_A H HHbp LINV LINV_frame) as LF'.
    pose proof (arm_TYPEID_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE) as TY.
    pose proof (arm_SCOPE_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HTL LINV_relro) as SC.
    pose proof (arm_EXTNUM_A H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAG0 HU32 HTL HVOT PTS LINV_cl LINV_relro HOWN) as EX.
    pose proof (arm_ENUM_A H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTL PTS LINV_cl LINV_relro HOWN) as EN.
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
                first [ apply ARM_STR; lia | apply arm_AX_of_A ];
                first [ apply ARM_RID; reflexivity | apply ARM_SPEC; reflexivity | apply ARM_TYL; lia
                      | apply IDA; lia | apply LI; lia | apply LF'; reflexivity | apply TY; reflexivity | apply SC; lia
                      | apply SL; reflexivity | exact EX | apply ARM_MASK; inlist | apply EN; inlist | apply DF ] |]
           | False => destruct HIn
           end.
  Qed.

  Theorem pm_body_allA : pm_body_all H LINV.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi F fc w OK.
    apply (pm_bodyA H HHbp LINV LINV_frame LINV_cl LINV_relro HOWN HTL TFS arms_allA
             (pm_push_tailAX H HHbp LINV LINV_frame LINV_cl HOWN HVO V4R HFW HEXH)
             (pm_checkkA H HHbp LINV LINV_frame)
             ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi F fc); [ | | | | | | exact OK].
    -   intros s LB LBs m mo c msF R F1 fc1 Q OK' HL HLT XD XL HK.
      exact (pm_ihead H HHbp LINV LINV_frame LINV_cl LINV_relro HOWN HTL V4C PTS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi
               s LB LBs m mo c msF R F1 fc1 Q OK' HL HLT XD XL HK).
    -   intros s LB LBs m mo c msF R F1 fc1.
      exact (pm_u2dz H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU16 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi
               s LB LBs m mo c msF R F1 fc1).
    -   intros s LB LBs m mo c msF R F1 fc1 rr op OK' X' Htr' Hbsz' KR' VIS' RF' FZ' HT' G3' G4' G10 Rr Hr Rop COP CD.
      exact (pm_u2lz H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU16 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi
               s LB LBs m mo c msF R F1 fc1 rr op OK' X' Htr' Hbsz' KR' VIS' RF' FZ' HT' G3' G4' G10 Rr Hr Rop COP).
    -   intros I.
      exact (pm_xexitA H HHbp LINV LINV_frame HTL ds_repA DSL HCTOR HCSEQ HDTOR HU16 HU64 HNT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi
               F fc I).
    -   intros s LB LBs m mo c msF R F1 fc1 io iwc op t.
      exact (pm_ohx H HHbp LINV LINV_frame HEXH ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi
               s LB LBs m mo c msF R F1 fc1 io iwc op t).
    -   exact (pm_ohz H HHbp LINV LINV_frame HTL ds_repA DSL HCTOR HCSEQ HDTOR HU16 HU64 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi F fc).
  Qed.

  Theorem parse_module_okA_all : parse_module_stmtA H LINV.
  Proof. exact (parse_module_okA H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 HU64 HTL pm_body_allA). Qed.
End ALL.

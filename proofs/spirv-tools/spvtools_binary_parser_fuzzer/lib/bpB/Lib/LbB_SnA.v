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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 RtB_Iface RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK LbB_SnK LbB_SnFind.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_SnTA.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_SnA () := "C46Stdlib5Lists4List2InC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4fentI46Stdlib5Lists4List6Exists00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK2WpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4rtblC45stdpp9bitvector;definitions;bv_unsignedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4ftblK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK2PwC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_RFSC45stdpp9bitvector;definitions7Z_to_bvC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK2W3C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchK47Corelib4Init9Datatypes6option02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK9sn_rangesC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2or00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7app_objC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK2tSK47Corelib4Init9Datatypes3nat02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK2tFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK2tHK47Corelib4Init5Logic2eq01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK8tabs_wf3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK8Pw_step3C47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry04K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit6wboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_okbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit3finC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK8tabs_ok3I47Corelib4Init9Datatypes4list00I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK9kst_pd_okK47Corelib5Lists7ListDef6Forall01K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4fknTC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN6swinsTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC46Stdlib5Lists4List7forallbC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_chkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4tupdC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5ftblsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5winsTC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC46Stdlib5Lists4List?Forall_cons_iffC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK9RFS_step3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK9winsT3_eqC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK2kTK5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK5kT_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S4flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK8scT_flatC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState<unsigned_litC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9scs_denotC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame;munch_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN:rtbl_keptkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5keptkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK8sn_keepUC5ARocqVerifyHarness?AgentSubmission7LibHash4HRep6nval32C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit2gzC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7existsbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_DCtorK7inb_In'C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit7rtbl_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4wenvC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK2rgC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt5sx32AC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3sxwC5ARocqVerifyHarness?AgentSubmission6LibPrs:PrsGrammar4sx32C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind8sxw_sx32C4ARocqVerifyHarness?AgentSubmission8PropExec4getrK4ARocqVerifyHarness?AgentSubmission8PropExec7FPState01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula08C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind;snfind_specC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6aonlyTC4ARocqVerifyHarness?AgentSubmission8PropExec7seg_romC4ARocqVerifyHarness?AgentSubmission8PropExec4mkstI47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4rsubC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit9rtbl_keepC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge7mkst_MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call8blk_thenC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN7dk_runNK45stdpp9bitvector;definitions2bv01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec3evtK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I5ARocqVerifyHarness?AgentSubmission7LibHash4HRep5umapx00I4ARocqVerifyHarness?AgentSubmission6CatSim6msteps00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsK47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tabI5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AI47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnA3RT2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnA3SF2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnA3FT2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnTA4RTK4C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnTA3SF4C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnTA3FT4C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_SnTA3HT4C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind9SNF_FOUNDC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind<SNF_NOTFOUNDC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt9ADS_STACKC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9AFS_FLAGSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOK47Corelib4Init9Datatypes3nat01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_SnK6kst_snK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_SnFind9SNF_ENTRYC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4KEPTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8non_argT".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 33) (ELit k).

Definition RT2 : list (reg * expr) :=
  [(1%bv, ELit 0xf943c); (2%bv, spx (-96)); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, spx (-96));
   (10%bv, EVar 52); (18%bv, EVar 40); (19%bv, EVar 41); (20%bv, EVar 36); (21%bv, EVar 32); (22%bv, EVar 35);
   (23%bv, EVar 45); (24%bv, ELit SHBASE); (25%bv, EVar 47); (26%bv, EVar 48); (27%bv, EVar 49)].
Definition SF2 : list fent :=
  [(-96, 8%nat, ELit 0); (-8, 8%nat, EVar 34); (-16, 8%nat, EVar 38); (-24, 8%nat, EVar 39); (-32, 8%nat, EVar 40);
   (-40, 8%nat, EVar 41); (-48, 8%nat, EVar 42); (-56, 8%nat, EVar 43); (-64, 8%nat, EVar 44); (-72, 8%nat, EVar 45);
   (-80, 8%nat, EVar 46)].
Definition FT2 : list fent := [(1016, 8%nat, EVar 53)].

Section SnA.
  Local Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

  Local Notation PO_SIZE := LbB_SnK.PO_SIZE (only parsing).
  Local Notation kst_sn := LbB_SnK.kst_sn (only parsing).
  Local Notation dj2 := LbB_SnK.dj2 (only parsing).
  Local Notation rg := LbB_SnK.rg (only parsing).
  Local Notation shT := LbB_SnK.shT (only parsing).
  Local Notation kT := LbB_SnK.kT (only parsing).
  Local Notation kwin := LbB_SnK.kwin (only parsing).
  Local Notation shN := LbB_SnK.shN (only parsing).
  Local Notation shP := LbB_SnK.shP (only parsing).
  Local Notation POA := LbB_SnK.POA (only parsing).
  Local Notation kP := LbB_SnK.kP (only parsing).
  Local Notation kN := LbB_SnK.kN (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m1 : mem) (this po tid pcons icount lo ff fp : Z) (LF : list fframe).

  Variables (bl bc nd nk bw enc : Z).
  Variables (LBl : list (Z * Z)) (ents : list (Z * (Z * (Z * Z * Z)))).

  Hypothesis DSA : addressable m1 po PO_SIZE.
  Hypothesis DSW : wr_at asegs m1 po PO_SIZE.
  Hypothesis DSO : app_obj po PO_SIZE.
  Hypothesis DS8 : po mod 8 = 0.
  Hypothesis DSV : shvis m1 po (po + PO_SIZE).
  Hypothesis DSH : po + PO_SIZE + 64 <= AAPP_HI.
  Hypothesis DSM : po + PO_SIZE <= aceil.
  Hypothesis DSin : obj_inframe LF po PO_SIZE.

  Hypothesis PCA : addressable m1 pcons 48.
  Hypothesis PCO : app_obj pcons 48.
  Hypothesis PC8 : pcons mod 8 = 0.
  Hypothesis PCC : rw_cells asegs m1 (pcons + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis DISJ : forall a, po <= a < po + PO_SIZE -> ~ (pcons <= a < pcons + 48).
  Hypothesis ICN : 0 <= icount < 2 ^ 63.

  Hypothesis STK : stk asegs m1 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ADS_STACK.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPHI : bv_unsigned sp <= AAPP_HI.
  Hypothesis SPOBJ : forall O n, O = po /\ n = PO_SIZE \/ O = pcons /\ n = 48 ->
                     O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O.

  Hypothesis FFR : aframe_range H 4 ff fp.
  Hypothesis FSB_OK : afsb_ok H.
  Hypothesis FFDS : ff + 1024 <= po \/ po + PO_SIZE <= ff.
  Hypothesis FFPC : ff + 1024 <= pcons \/ pcons + 48 <= ff.
  Hypothesis FPPC : fp + 1 <= pcons \/ pcons + 48 <= fp.
  Hypothesis FPDS : fp + 1 <= po \/ po + PO_SIZE <= fp.
  Hypothesis HULL : hull_hi (po + PO_SIZE) <= ff \/ ff + 1024 <= hull_lo po.
  Hypothesis FRW : wr_at asegs m1 ff 1024.
  Hypothesis FSV : shvis m1 ff (ff + 1024).
  Hypothesis FSW : wr_at asegs m1 (sh ff) 128.
  Hypothesis FLW : wr_at asegs m1 fp 1.

  Hypothesis MI1 : mem_inv asegs m1.
  Hypothesis AC1 : ACONST m1.
  Hypothesis LV1 : LINV_P5 m1.

  Hypothesis THA : addressable m1 this 288.
  Hypothesis THO : app_obj this 288.
  Hypothesis TH8 : this mod 8 = 0.
  Hypothesis THS : dj2 (this + 288) (bv_unsigned sp - ADS_STACK) (bv_unsigned sp) this.
  Hypothesis THF : dj2 (ff + 1024) this (this + 288) ff.
  Hypothesis THP : dj2 (fp + 1) this (this + 288) fp.

  Hypothesis THD : dj2 (this + 272) po (po + PO_SIZE) this.
  Hypothesis THC1 : rw_cells asegs m1 (this + 8) [C8 (Z_to_bv 64 pcons)].
  Hypothesis THC2 : rw_cells asegs m1 (this + 80) [C8 (Z_to_bv 64 icount)].
  Hypothesis TIDR : rg 0 tid (2 ^ 32).
  Hypothesis BLR : rg 0 bl (2 ^ 64).
  Hypothesis BCR : rg 0 bc (2 ^ 64).
  Hypothesis NDR : rg 0 nd (2 ^ 64) /\ rg 0 nk (2 ^ 32) /\ rg 0 bw (2 ^ 32) /\ rg 0 enc (2 ^ 32).

  Hypothesis UM1 : umapx MI_A 32 (nval32 ASEGS) LBl m1 (this + 136) bl bc ents.
  Hypothesis UG1 : gz m1 (this + 136) 40.
  Hypothesis UG2 : bc <> 0 -> gz m1 bl (8 * bc).
  Hypothesis UG3 : forall p k v, In (p, (k, v)) ents -> gz m1 p 32.
  Hypothesis UFO : forall a, umap_foot 32 (this + 136) bl bc ents a ->
    outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)] a
    /\ outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + PO_SIZE); (ff, ff + 1024); (sh ff, sh ff + 128); (fp, fp + 1)] (a / 8 + SHBASE)
    /\ 0 <= a < 2 ^ 47.

  Local Notation Wp := (@LbB_SnK.Wp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc) (only parsing).
  Local Notation PW := (@LbB_SnK.PW sp po ff fp) (only parsing).
  Local Notation PWF := (@LbB_SnK.PWF sp po ff fp) (only parsing).
  Local Notation Pw := (@LbB_SnK.Pw sp m1 po ff fp) (only parsing).
  Local Notation Pw_cz := (@LbB_SnK.Pw_cz sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation Pw_m1 := (@LbB_SnK.Pw_m1 sp m1 po ff fp) (only parsing).
  Local Notation sn_ranges := (@LbB_SnK.sn_ranges HCEIL H sp m1 this po pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sh_mono8 := (@LbB_SnK.sh_mono8 sp this po pcons icount ICN) (only parsing).
  Local Notation pw_aconst := (@LbB_SnK.pw_aconst HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_out_img := (@LbB_SnK.pw_out_img HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_sh_apart := (@LbB_SnK.pw_sh_apart HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_hull_apart := (@LbB_SnK.pw_hull_apart HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sn_keep := (@LbB_SnK.sn_keep HCEIL H sp m1 this po pcons icount lo ff fp DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation sn_keepT := (@LbB_SnK.sn_keepT HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK THA THO TH8 THS THF THP THD THC1 THC2) (only parsing).
  Local Notation evWp := (@LbB_SnK.evWp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc ICN) (only parsing).
  Local Notation sn_vals := (@LbB_SnK.sn_vals HCEIL H sp m1 this po pcons icount lo ff fp DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation kst_pd_ok := (@LbB_SnK.kst_pd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation sn_keepU := (@LbB_SnK.sn_keepU sp m1 this po pcons icount ff fp bl bc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation evT := (@LbB_SnK.evT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc THO) (only parsing).
  Local Notation shT_start := (@LbB_SnK.shT_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc THO) (only parsing).
  Local Notation shT_apart := (@LbB_SnK.shT_apart HCEIL H sp m1 this po pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK TH8 THF) (only parsing).
  Local Notation kT_ok := (@LbB_SnK.kT_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK THA THO TH8 THS THF THP THD THC1 THC2) (only parsing).
  Local Notation scT_flat := (@LbB_SnK.scT_flat ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc THO) (only parsing).
  Local Notation tS := (@LbB_SnK.tS sp) (only parsing).
  Local Notation tF := (@LbB_SnK.tF ff) (only parsing).
  Local Notation tH := (@LbB_SnK.tH ff) (only parsing).
  Local Notation tL := (@LbB_SnK.tL fp) (only parsing).
  Local Notation sn_wins := (@LbB_SnK.sn_wins HCEIL H sp m1 this po pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tab_vals := (@LbB_SnK.tab_vals HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf3 := (@LbB_SnK.tabs_wf3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf4 := (@LbB_SnK.tabs_wf4 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation wk_stk := (@LbB_SnK.wk_stk sp this po pcons icount lo ICN LO) (only parsing).
  Local Notation wk_win := (@LbB_SnK.wk_win sp this po pcons icount ICN) (only parsing).
  Local Notation inPW := (@LbB_SnK.inPW sp po ff fp) (only parsing).
  Local Notation Pw_ext := (@LbB_SnK.Pw_ext sp m1 po ff fp) (only parsing).
  Local Notation in_stk := (@LbB_SnK.in_stk sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_p2 := (@LbB_SnK.in_p2 sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_p8 := (@LbB_SnK.in_p8 sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_fr := (@LbB_SnK.in_fr sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_sh := (@LbB_SnK.in_sh sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_fl := (@LbB_SnK.in_fl sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation shb_eq := (@LbB_SnK.shb_eq sp this po pcons icount ff ICN) (only parsing).
  Local Notation W3 := (@LbB_SnK.W3 sp ff) (only parsing).
  Local Notation winsT3_eq := (@LbB_SnK.winsT3_eq sp ff) (only parsing).
  Local Notation Pw_step3 := (@LbB_SnK.Pw_step3 sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation Pw_step4 := (@LbB_SnK.Pw_step4 sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation HHb := (@LbB_SnK.HHb HCEIL H HHbp) (only parsing).
  Local Notation afs_ok_frame := (@LbB_SnK.afs_ok_frame H sp this po pcons icount ff fp LF ICN) (only parsing).
  Local Notation afs_ok_stack := (@LbB_SnK.afs_ok_stack HCEIL H sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation afs_ok_shadow := (@LbB_SnK.afs_ok_shadow HCEIL H sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_ok3 := (@LbB_SnK.tabs_ok3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation tabs_ok4 := (@LbB_SnK.tabs_ok4 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation tP2 := (@LbB_SnK.tP2 po) (only parsing).
  Local Notation tP8 := (@LbB_SnK.tP8 po) (only parsing).
  Local Notation po_wins := (@LbB_SnK.po_wins sp po pcons SPOBJ) (only parsing).
  Local Notation po_sh_wins := (@LbB_SnK.po_sh_wins HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf5p := (@LbB_SnK.tabs_wf5p HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO DSH PCO ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS) (only parsing).
  Local Notation Pw_step5p := (@LbB_SnK.Pw_step5p sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation tabs_ok5p := (@LbB_SnK.tabs_ok5p HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation afs_ok_po := (@LbB_SnK.afs_ok_po H po ff fp LF DSin) (only parsing).
  Local Notation RFS_step5p := (@LbB_SnK.RFS_step5p HCEIL H HHbp sp m1 this po pcons icount lo ff fp LF DSin ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation RFS_step3 := (@LbB_SnK.RFS_step3 HCEIL H HHbp sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation po_rng := (@LbB_SnK.po_rng po DSO) (only parsing).
  Local Notation evP := (@LbB_SnK.evP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation shP_start := (@LbB_SnK.shP_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation POA_start := (@LbB_SnK.POA_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation po_sh_self := (@LbB_SnK.po_sh_self po DSO DS8) (only parsing).
  Local Notation flatP := (@LbB_SnK.flatP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation flat_shP := (@LbB_SnK.flat_shP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation kP_ok := (@LbB_SnK.kP_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation nd_facts := (@LbB_SnK.nd_facts sp m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation nd_out := (@LbB_SnK.nd_out sp this po tid ff fp bl bc nd nk bw enc ents UFO) (only parsing).
  Local Notation evN := (@LbB_SnK.evN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation ndA_start := (@LbB_SnK.ndA_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation shN_start := (@LbB_SnK.shN_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation flatN := (@LbB_SnK.flatN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation flat_shN := (@LbB_SnK.flat_shN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation kN_ok := (@LbB_SnK.kN_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents DSO ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation SF5 := (@LbB_SnK.SF5 HCEIL H HHbp ra sp gp tp) (only parsing).
  Local Notation tabs_wf1 := (@LbB_SnK.tabs_wf1 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation Pw_step1 := (@LbB_SnK.Pw_step1 sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation tabs_ok1 := (@LbB_SnK.tabs_ok1 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation RFS_L_step1 := (@LbB_SnK.RFS_L_step1 HCEIL H HHbp sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation nopo := (@LbB_SnK.nopo sp ff fp) (only parsing).
  Local Notation po_cells_keep := (@LbB_SnK.po_cells_keep HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FPDS) (only parsing).
  Local Notation po4 := (@LbB_SnK.po4 po nk bw enc) (only parsing).
  Local Notation po4_keep := (@LbB_SnK.po4_keep HCEIL H sp m1 this po pcons icount lo ff fp nk bw enc DSO ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FPDS) (only parsing).
  Local Notation nopo_w3 := (@LbB_SnK.nopo_w3 sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation nopo_w1 := (@LbB_SnK.nopo_w1 sp ff fp) (only parsing).
  Local Notation nopo_sf := (@LbB_SnK.nopo_sf sp ff fp) (only parsing).
  Local Notation inPW_sf := (@LbB_SnK.inPW_sf sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation sf_stack_keep := (@LbB_SnK.sf_stack_keep HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sn_Pok := (@LbB_SnK.sn_Pok H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 po ff fp LF nk bw enc) (only parsing).
  Local Notation sn_fin_ok := (@LbB_SnK.sn_fin_ok H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 po ff fp LF nk bw enc) (only parsing).

  Notation spz := (bv_unsigned sp) (only parsing).

  Ltac evwp := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wp;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac tnormp H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac dkrunP3 HRT HSF HFT HHT HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) (kst_sn ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3]
                    (tabs_wf3 SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step3 SF FT HT ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] (kst_sn ++ kf) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok3; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Ltac dkrunP4 HRT HSF HFT HHT HLT HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HLT with ftbl _ _ _ ?LT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []; tL LT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) (kst_sn ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          let ks4 := eval vm_compute in (nkeys (EVar 53) (s_log SSr) LT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3; tL LT ks4]
                    (tabs_wf4 SF FT HT LT ks1 ks2 ks3 ks4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step4 SF FT HT LT ks1 ks2 ks3 ks4)
                    Q R F pc fc m ro RT [] (kst_sn ++ kf) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok4; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | exact HLT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac tcomp HTS :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS; clear E
    end.
  Ltac tsplit HTS H1 H2 H3 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; clear HTS; cbn [fst snd] in H1, H2, H3.
  Ltac tsplit4 HTS H1 H2 H3 H4 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; clear HTS; cbn [fst snd] in H1, H2, H3, H4.

  Ltac rgetp HRT r H :=
    lazymatch type of HRT with
    | rtbl ?W ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (H : PropExec.getr R r = edenot (wenv W) e)
          by (apply (rtbl_In W R RT r e HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
        unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wp in H;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in H;
        rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z in H by (pose proof sn_vals; lia)
    end.
  Ltac dkrunP1 HRT HSF HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (kst_sn ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          eapply (dk_runN Wp [tS SF ks1] (tabs_wf1 SF ks1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step1 SF ks1) Q R F pc fc m ro RT [] kst_sn fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok1; [exact HP | exact HMI | exact HSF | vm_compute; reflexivity]
          | exact HP | exact HMI | apply kst_pd_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end
    end.
  Ltac dkrunP5p HRT HSF HFT HHT HP2 HP8 HP HMI fuel stops kx scr0 :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HP2 with ftbl _ _ _ ?P2 =>
      lazymatch type of HP8 with ftbl _ _ _ ?P8 =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []; tP2 P2 []; tP8 P8 []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops scr0 (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kx) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          let ks4 := eval vm_compute in (kwin 2 4 (nkeys (EVar 35) (s_log SSr) P2)) in
          let ks5 := eval vm_compute in (kwin 8 20 (nkeys (EVar 35) (s_log SSr) P8)) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3; tP2 P2 ks4; tP8 P8 ks5]
                    (tabs_wf5p SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step5p SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5)
                    Q R F pc fc m ro RT [] (kst_sn ++ kx) fuel stops scr0 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok5p; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | exact HP2 | exact HP8 | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end end
    end.
  Ltac tsplit5 HTS H1 H2 H3 H4 H5 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; apply Forall_cons_iff in HTS as [H5 HTS];
    clear HTS; cbn [fst snd] in H1, H2, H3, H4, H5.

  Ltac dkrunP3k HRT HSF HFT HHT HP HMI fuel stops kx :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kx) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3]
                    (tabs_wf3 SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step3 SF FT HT ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] (kst_sn ++ kx) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok3; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Ltac scT := unfold scs_denot; repeat (apply Forall_cons; [cbn [sc_denot]; unfold elenZ; cbn [edenot]; rewrite ?unsigned_lit by (clear; lia);
                                           first [apply scT_flat; clear; lia] |]); apply Forall_nil.

  Lemma sc_disj18 : forall segs base E a1 a2 x1 x2, estart E a1 = x1 -> estart E a2 = x2 -> flat E a1 1 -> flat E a2 8 ->
    x1 + 1 <= x2 \/ x2 + 8 <= x1 -> sc_denot segs base E (SCDisj a1 (ELit 1) a2 (ELit 8)).
  Proof.
    intros segs base E a1 a2 x1 x2 E1 E2 F1 F2 D. cbn [sc_denot]. unfold elenZ. cbn [edenot].
    rewrite !unsigned_lit by (clear; lia). rewrite E1, E2. tauto.
  Qed.

  Lemma sn_pre : forall Q R m, rfull R -> rtbl Wp R RT2 -> ftbl Wp spz m SF2 -> ftbl Wp ff m FT2 -> ftbl Wp (ff / 8) m [] ->
    Pw m -> mem_inv asegs m -> as_RFS H ((4, ff, fp) :: LF) m ->
    (forall R' m' p v, rfull R' -> In (p, (tid, v)) ents -> PropExec.getr R' 10 = Z_to_bv 64 p ->
       rtbl Wp R' RTK4 -> ftbl Wp spz m' SF4 -> ftbl Wp ff m' FT4 -> ftbl Wp (ff / 8) m' HT4 ->
       Pw m' -> mem_inv asegs m' -> as_RFS H ((4, ff, fp) :: LF) m' -> munch W3 m m' ->
       evt asegs Q (MS R' F (Z_to_bv 64 LbB_SnFind.SNF_FOUND) fc None m' (seg_rom asegs))) ->
    (forall R' m', rfull R' ->
       rtbl Wp R' RTK4 -> ftbl Wp spz m' SF4 -> ftbl Wp ff m' FT4 -> ftbl Wp (ff / 8) m' HT4 ->
       Pw m' -> mem_inv asegs m' -> as_RFS H ((4, ff, fp) :: LF) m' -> munch W3 m m' ->
       evt asegs Q (MS R' F (Z_to_bv 64 LbB_SnFind.SNF_NOTFOUND) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS R F (Z_to_bv 64 0xf943c) fc None m (seg_rom asegs)).
  Proof.
    intros Q R m RF HRT HSF HFT HHT HP HMI HRFS KF KN.
    dkrunP3k HRT HSF HFT HHT HP HMI 600%nat [LbB_SnFind.SNF_ENTRY] (kT 144).
    - apply (kT_ok R [] m 144 HP HMI). lia.
    - pose proof sn_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
      pose proof sn_vals as (V1 & V2 & V3 & V4 & V5).
      pose proof THO as (T1 & T2 & T3).
      assert (SS : (this + 144) / 8 + SHBASE + 1 <= ff \/ ff + 1024 <= (this + 144) / 8 + SHBASE).
      { clear - R4 R5 R8 R11 T1 T3. unfold AIMG_TOP, AAPP_HI, ALOWSH_LO, AHI_LO, AFS_HDR, AFS_SIZE, SHBASE in *.
        Z.div_mod_to_equations. lia. }
      assert (EF : forall k, estart (HLib.Eseed R (Wp ++ [])) (SA (EVar 52) k) = ff + k).
      { intros k. unfold estart. cbn [edenot a_base a_off]. change (ev (HLib.Eseed R (Wp ++ [])) 52) with (Z_to_bv 64 ff).
        rewrite unsigned_lit by lia. reflexivity. }
      unfold scs_denot. repeat apply Forall_cons; try apply Forall_nil.
      all: first
        [ cbn [sc_denot]; unfold elenZ; cbn [edenot]; rewrite unsigned_lit by (clear; lia); apply scT_flat; clear; lia
        | eapply sc_disj18;
          [ apply shT_start; clear; lia | apply EF | apply scT_flat; clear; lia
          | unfold flat; rewrite EF; clear - R4 R5 R8 R9 R12; unfold AFS_HDR, AFS_SIZE, AIMG_TOP in *; lia
          | clear - SS; lia ] ].
    - intros R1 m1' RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
      tsplit HTS1 HSF1 HFT1 HHT1.
      cbn [s_pc].
      assert (G10 : PropExec.getr R1 10 = Z_to_bv 64 (this + 144)).
      { rewrite (rtbl_In _ R1 _ 10%bv (EAlu ALU_ADD (EVar 32) (ELit 144)) HRT1 ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)).
        unfold wenv. rewrite <- (app_nil_r Wp). apply evT. lia. }
      rgetp HRT1 (21%bv : bv 5) G21. rgetp HRT1 (20%bv : bv 5) G20. rgetp HRT1 (24%bv : bv 5) G24.
      destruct (sn_keepU m1' HP1) as (UM & UG1' & UG2' & UG3').
      assert (G20' : PropExec.getr R1 20 = sxw tid).
      { rewrite G20, LbB_SnFind.sxw_sx32 by (unfold rg in TIDR; lia). reflexivity. }
      assert (G24' : PropExec.getr R1 24 = Z_to_bv 64 SHBASE) by exact G24.
      assert (WK : exists R', LbB_SnFind.keptS R1 R' /\
                ((exists p v, CatSim.msteps asegs (MS R1 F (Z_to_bv 64 LbB_SnFind.SNF_ENTRY) fc None m1' (seg_rom asegs))
                                (MS R' F (Z_to_bv 64 LbB_SnFind.SNF_FOUND) fc None m1' (seg_rom asegs))
                              /\ PropExec.getr R' 10 = Z_to_bv 64 p /\ In (p, (tid, v)) ents)
                 \/ CatSim.msteps asegs (MS R1 F (Z_to_bv 64 LbB_SnFind.SNF_ENTRY) fc None m1' (seg_rom asegs))
                                (MS R' F (Z_to_bv 64 LbB_SnFind.SNF_NOTFOUND) fc None m1' (seg_rom asegs)))).
      { edestruct (@LbB_SnFind.find_okS (PropExec.mkFP F fc) AC_A) with (rom := seg_rom asegs) (M0 := m1') (this := this)
          (key := tid) (ents := ents) (R := R1) (A := LBl) (bl := bl) (bc := bc) (L := LY_A) (MI := MI_A) (NS := 32) (nval := nval32 ASEGS)
          as (R' & KP & HW).
        all: try first [(exists R'; split; [exact KP | exact HW])
                   | exact UM | exact UG1' | exact UG2' | exact UG3' | exact G10 | exact G21 | exact G20' | exact G24'
                   | (unfold rg in TIDR; lia) | (pose proof THO as (T1 & _); unfold AIMG_TOP in T1; lia) | lia].
      }
      assert (RFm : as_RFS H ((4, ff, fp) :: LF) m1') by (eapply RFS_step3; [exact HRFS | exact MU1 | exact WM1]).
      assert (MUW : munch W3 m m1') by (rewrite winsT3_eq in MU1; exact MU1).
      destruct WK as (R' & KP & [(p & v & MSf & GP & IN) | MSn]);
        (assert (AO : forall r, In r non_argT -> PropExec.getr R' r = PropExec.getr R1 r);
         [ intros r Hr; destruct KP as (KA & KB & KC & KD); unfold non_argT in Hr;
           repeat (destruct Hr as [<- | Hr]; [first [exact KB | exact KC | exact KD | apply KA; unfold LbB_SnFind.non_argS; repeat (first [left; reflexivity | right])] |]);
           contradiction |]).
      + eapply evt_of_msteps; [exact MSf |].
        assert (RF' : rfull R') by exact (msteps_full asegs _ _ MSf RF1).
        apply (KF R' m1' p v RF' IN GP); try assumption.
        all: first
          [ apply (rtbl_keep _ R1 R' RTK4 non_argT); [apply (rtbl_sub _ R1 _ RTK4 HRT1); vm_compute; reflexivity | vm_compute; reflexivity | exact AO]
          | apply (ftbl_sub _ _ _ _ _ HSF1); vm_compute; reflexivity
          | apply (ftbl_sub _ _ _ _ _ HFT1); vm_compute; reflexivity
          | apply (ftbl_sub _ _ _ _ _ HHT1); vm_compute; reflexivity ].
      + eapply evt_of_msteps; [exact MSn |].
        assert (RF' : rfull R') by exact (msteps_full asegs _ _ MSn RF1).
        apply (KN R' m1' RF'); try assumption.
        all: first
          [ apply (rtbl_keep _ R1 R' RTK4 non_argT); [apply (rtbl_sub _ R1 _ RTK4 HRT1); vm_compute; reflexivity | vm_compute; reflexivity | exact AO]
          | apply (ftbl_sub _ _ _ _ _ HSF1); vm_compute; reflexivity
          | apply (ftbl_sub _ _ _ _ _ HFT1); vm_compute; reflexivity
          | apply (ftbl_sub _ _ _ _ _ HHT1); vm_compute; reflexivity ].
  Qed.
End SnA.

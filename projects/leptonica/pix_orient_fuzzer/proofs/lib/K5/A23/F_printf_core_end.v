(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import SFModel Arr SysStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FP ITree Nodes Decode.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Bytes PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Printf_mlib Printf_zfacts.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import FX_lib F_memset F_memcpy F_memchr I_strnlen F_fwritex F_pop_arg F_printf_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import PrintfModel. (* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import F_printf_core_common.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import R_m2s I_consts.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import IcptSpec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import F_achk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_printf_core_end () := "C69OSSVerify5KrLib2K54Spec5Monad1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>F_printf_iface?sink_frame_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23DF_printf_core_common4POSTC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53A23DF_printf_core_common7ctx_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23DF_printf_core_common4finvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53A23DF_printf_core_common8lo_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>F_printf_iface4frm0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23DF_printf_core_common3FokC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23DF_printf_core_common1WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23DF_printf_core_common8hi_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236FX_lib2zbC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23DF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib2K53A23DF_printf_core_common6S_EXITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec6evt_eqC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23DF_printf_core_common5S_ENDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53A239FX_Layout7got_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239FX_Layout9ssp_guardC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib2K54Spec;PrintfModel7INT_MAXC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K53A236F_achk9SHADOW_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236F_achk9SHADOW_HIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00".   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS X1 N1 X2 N2 : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS X1 N1 X2 N2 SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS X1 N1 X2 N2 SINK TOPOK OUT.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^63)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 2142208)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((2186832 <= Fp /\ Fp + 232 <= 2285568) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((7878496 <= B /\ B + BS <= lo /\ B + BS <= 7884800) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis SEP_X1 : (AP + 8 <= X1 /\ X1 + N1 <= VA /\ 0 <= N1)%Z.                 (* [comment removed for export] *)
  Hypothesis SEP_X2 : (7884800 <= X2 /\ X2 + N2 <= lo /\ 0 <= N2 /\ (X2 + N2 <= SHADOW_LO \/ SHADOW_HI <= X2))%Z.   (* [comment removed for export] *)
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  (* [comment removed for export] *)
  Hypothesis RIP : rip_stmt.
  Hypothesis HA0 : aext m0 lo q A fmt B BS X2 N2.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS X1 N1 X2 N2 q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS X1 N1 X2 N2 SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS X1 N1 X2 N2 ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS X1 N1 X2 N2 SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS X1 N1 X2 N2 SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS X1 N1 X2 N2 q m0 lo A fmt AP VA slots LO SEP_F SEP_B SEP_X1 SEP_X2 HAP HA0).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS X1 N1 X2 N2 q m0 lo A fmt AP VA slots LO SEP_F SEP_B SEP_X1 SEP_X2 HAP HA0).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq Fp B BS X1 N1 X2 N2 q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B SEP_X1 SEP_X2 HAP RIP HA0).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS X1 N1 X2 N2 SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B SEP_X1 SEP_X2 HAP BS0 HA0).
  Local Notation memset_callq := (F_printf_core_common.memset_callq Fp B BS X1 N1 X2 N2 q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B SEP_X1 SEP_X2 HAP RIP HA0).
  Local Notation memset_postq := (F_printf_core_common.memset_postq q gp tp lo).
  Local Notation chkr_W := (F_printf_core_common.chkr_W Fp B BS X1 N1 X2 N2 q m0 lo A fmt AP VA LO SEP_F SEP_B SEP_X1 SEP_X2 HAP HA0).
  Local Notation ictx_W := (F_printf_core_common.ictx_W Fp B BS X1 N1 X2 N2 q m0 lo A fmt AP VA LO SEP_F SEP_B SEP_X1 SEP_X2 HAP HA0).
  Local Notation hsh := (F_printf_core_common.hsh B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_stack0 := (F_printf_core_common.chkr_stack0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_fmt0 := (F_printf_core_common.chkr_fmt0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_pfx0 := (F_printf_core_common.chkr_pfx0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_xdig0 := (F_printf_core_common.chkr_xdig0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation chkr_nulls0 := (F_printf_core_common.chkr_nulls0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation arg_ok_chk := (F_printf_core_common.arg_ok_chk Fp B BS X1 N1 X2 N2).
  Local Notation chkr_buf0 := (F_printf_core_common.chkr_buf0 B BS X2 N2 q m0 lo A fmt HA0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS X1 N1 X2 N2 SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B SEP_X1 SEP_X2 HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS X1 N1 X2 N2 SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS X1 N1 X2 N2 SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS X1 N1 X2 N2 q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS X1 N1 X2 N2 q lo AP VA LO GLO SEP_F SEP_B SEP_X1 SEP_X2 HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS X1 N1 X2 N2 SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS X1 N1 X2 N2 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
    try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
         lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
    try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
         lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
    unfold zlength in *; hush.
  Ltac hyp :=
    lazymatch goal with
    | |- rw_cells _ ?m ?A ?cs =>
        match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
    | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
    end.
  Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
  Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  (* [comment removed for export] *)
  Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Local Ltac transport_call_extra segs W m m' MU WM ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    end.
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
  Local Ltac mem_after_store ::= mem_after_store_fast.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
  Local Ltac lia ::= lia3.
  Ltac chk0_tac :=
    first [ apply chkr_stack0; try unfold zrepeat; unfold zlength in *; rewrite ?repeat_length, ?Z2Nat.id by lia; lia
          | apply chkr_fmt0; unfold zlength in *; lia
          | apply chkr_pfx0; unfold PFX_A, zlength in *; lia
          | apply chkr_xdig0; unfold XDIG_A, zlength in *; lia
          | match goal with H : chkr m0 ?b ?n |- chkr m0 _ _ => apply (chkr_sub m0 b n _ _ H); unfold zlength in *; lia end ].
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : ro_cells _ _ 2174000 _ |- _ => exact H end
        | match goal with H : ro_cells _ _ 7749080 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | |
      | match goal with H : munch _ m0 _ |- _ => exact H end
      | match goal with H : wmono _ m0 _ |- _ => exact H end
      | chk0_tac ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call asegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac. (* [comment removed for export] *)
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp & BCHK);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
    pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
    let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
  Ltac mk_tinv :=
    lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      unfold tinv, body_loc;
      split; [mk_finv|];
      split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
      split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
      split; [match goal with H : SINK m _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
      split; [lia|];
      split; [assumption|];
      split; [assumption|];
      split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.

  Hypothesis HS_EXIT : S_EXIT.

  (* [comment removed for export] *)
  Lemma L_END : S_END.
Proof using GLO HAP HS_EXIT LO SEP_F VAHI SEP_X1 SEP_X2.
ltac2:(KReplay.run1 (kr_t_F_printf_core_end ()) ["PrintfCore"] "p'0h01Kh11Hh22Hah34__p1h44__x1h54__x2h64__x3h74__x4h84__x5h94__x6h:1yh;1zh<1mh=1xh>3LU0h?4LZB0h@7__arithhA4__ffhB4__p2hC4__p3hD4__p4hE8__sat129hF8__sat130hG8__sat131hH8__sat132hI8__varmaphJ5__withK4__x7hL4__x8hM4__x9hN4cstrhO5cstr0hP5cstr1hQ5cstr2hR1nhS3APChT2BYhU3DIGhV2FIhW3FI'hX3FOKhY3FRMhZ4FRhih[2Fth\2HSh]2Hrh^3LOWh_2LUh`3LZBha2MIhb2MUhc2NXhd3PADhe4SSP1hf4SSP2hg2SThh3VAAhi2WMhj2_Hhk3ahihl3alohm3apvhn1bi001bho4digshp2fchq4j128hr4l10nhs3padht3pfxhu2plhv3plphw1rhx3s2shy2sthz2x1h{3x10h|3x11h}3x12h~3x13i013x14i023x15i033x16i043x17i053x18i063x21i073x22i083x23i093x24i0:3x25i0;3x26i0<3x27i0=3x28i0>3x29i0?3x30i0@3x31i0A2x5i0B2x6i0C2x7i0D2zap%0p%1p&0p&1p;1p;2p;Lp;Np;<p;3p;:p;>p;Pp;Op;4p;7p;9p;6p;Up;Bp;8p,2StR0p4p300R1p10000p4p710p8P1p1000dp4p710p8P1g001nR1p4p710p8g0033j14Tg003Xj1fTg0046j1zTg004Yj15Tg005>k21<Tg005jj1|Tg006Lk10BTg006lmL0fTg0084mN0:Tg0099j1rTg009Wj2=Tg00:4m<1;Tg00;=j10Tg00;\k20?Tg00<Tk10>Tg00=4j3RTg00=Tj1yTg00>Lk10aTg00?Kk20^Tg00@Oj27Tg00@kS00j28Tg00AFk207Tg00B=m:0WTg00C?j3oTg00D6m>0QTg00E?k10OTg00F4j26TP1lP>Tg00FZj1?Tg00G8lOFTg00Gmk10MTg00HOk10qTg00INj3jTg00JKk10jTg00KUj2iTg00L5j3:k106Tg00LOk10iTg00MJk10hTg00N>k20gTg00NUj2mTg00OHj3nTg00Okk40eTg00PWk10dTg00QDj21Tg00Qfj43Tg00RSk30<Tg00S@j1]Tg00S^j7dTg00TSj2STg00Tmk20bTg00Uok10`Tg00Vok20_Tg00WOk40]Tg00Wok10\Tg00X`k20[Tg00Yhk30ZTg00ZSk309Tg00[8m90YTg00\9k40XTg00]6k208Tg00]`j2^Tg00^=k60;Tg00^[R1j1aTg00_;R2j2wTg00_Xk20VTg00`;k30UTg00`Xj4tTg00a?j1gTg00adk204Tg00bLj2qTg00bhk203Tg00cEk30HTg00cik202Tg00dRj2vTg00e>k10PTg00e\k10RTg00f:k10STg00fek201Tg00gHk31:Tg00gkj4cTg00hVj3uTg00i9k319Tg00i\k20NTg00j?k30KTg00jbk217Tg00kDk216Tg00l0k315Tg00lOk413Tg00mAj2}Tg00m[k20GTg00n8k211Tg00o2k210Tg0108k60FTg010Tk10~Tg0115k40ETg011Pj1kTg011ik20{Tg012JmU0uTg013Qk60tTg014Hk10sTg014jk20rTg015Jk20vTg015imB0wTg016imU0xTg017ok40yTg018hk30zTg019_k40DTg01:Tj4eTg01;Mk40CTg01<Ek30oTg01=9mB0|Tg01=_m<0}Tg01>Dj3xTg01>mk20nTg01?Kk412Tg01?ij7{Tg01@Mk60lTg01A1k714Tg01AUk70kTg01B9k800Tf0R3#5#4p=P%43#4#4#4p=Gg01B]R4f2R5f1R6P3H0yp=@%53#4#4#4p=Z%03#0p>0p%03#0#0#0p>0m%03#0#0#0#0#0#0#0p>0@%53#5p=Y%03#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=Xg01CUR7/73p=;B0z463p=_%43#4p=TP4P5P6P3H0Dp=`P4f3R8g01D3R9P5CeP4P6g01E0R:P3Ce'8p=<P4f6R;f5R<f4R=H0CAj856/83'8p=E1863,85p=J%43#5p=Q%53#5#5#5p=H%53#4#5#4p=p%43#?p=Nf7R>P;P<P=P8P5P6P3Fd60o4p=BP4P8P5P6H0D/83p=lP4P5P6P3H0Cp>0IP4P6P:P3Cep=hAj<=8P4P5P9P6Ce/83'8p>0=P4P6P9P3Cep>0AP;P<P=P8P5C3P6P3C3p=2P=P81156P3C3p=9P;P<P=P8P5P6P3C3C3p>0cg01EoR9g01FOS017:3p=Og01FoR?/S3p=Vg01GMS029:93p=LA:?63p=[g01GmR@P@P@P?P?P?g01HLP1P1P1P2g01HlP<P=P8P5P6P3NB0|p>0TP@P?P3P1P6P5P8P=P<P;P>f8R1N<0}p>05202?3p=IAx?63p=~Ax?639x?5p=b20n?3p=\P?P5P6P3H12p=A20N?3p=MP?P6g01IOR2P3Ccp=W201?3p=UP5g01J6RAg01JURBPBg01K5RCP?P6P2P3Ccg01KUR2F{p=DP6PAPBPBPCP3J0lp=sP5PAPBPBPCP6P3K14p=CP5PAPBPBPCP6P3K0kp>0LP6PAPBPBPCP3P2F{p>18P=PAPBPBPCP8PAPBPBPCP5P2F{P6P3L00p=KP;PAPBPBPCP<P=P8PAPBPBPCP5P6P3L00L00p>0Jg01L5RA#4S03#4S04#4S05#4S06#4R2#4S07#fRD#zREQ03#5S08#fS0901<E%f2S0:#zS0;Q05#f#zS0<#|\EQ0<$0BS0=Q0=Q0=p,2raR2p,1qRFp,2gpRGp,2tpRHp,3s0eRIp,3s1eRJp,3s2eRKp,3s3eRLp,3s4eRMp,3s5eRNp,3s6eROp,3s7eRPp,3s8eRQp,3s9eRRp,4s10eRSp,4s11eRTp,1FRUp,3fc0S0>p,2m0RVp,2loRWp,6canaryRXp,1ARYp,3fmtS0?p,2APRZp,2VAR[p,5slotsR\p,3nlaS0@p,3nltS0ANL0fPBp,2FpR]p,1BR^p,2BSR_p,2X1R`p,2N1Rap,2X2Rbp,2N2RcP2PFPIPJPKPLPMPNPOPPPQPRPSPTPVPWPXPYQ0?PZP[P\f?S0BNN0:f@Q05#PS0C#G#r,=FRdPZQ0@Q0Af=S0Df<f;S0Ef:S0Ff9ReP1P>P;P<N<1;3@fA%5AS0G#4S0H#4S0I#4#Z#r,=Fg01LZRfg01MRS0J#0S0K#0S0L#0S0M#0S0N#0S0O#0S0P#0S0Q#0S0R#0S0S#0S0T$0p$0m$0@Rg00?<&0>fRh3R3@fBRiQ08#Y#G#r,=F&0@g#X#X#X#X#X#X#X00?<=Rfh3@p,4SINKRgfCPiO2fD%y;=Rfh7@ZfF$0afHRi-0^UfERj#;g01N1,7j'8P1P]P^P_P`PaPbPcP2PFPIPJPKPLPMPNPOPPPQPRPSPTPVPWPXPYQ0?PZP[P\PiNN0:Q00fIRj-074P]P^P_P`PaPbPcPFPWPZN:0WS0U?oVj1_VjQ0G#5S0V#4S0W#4#T#r,=FRkP2PIPJPKPLPMPNPOPPPQPRPSPTPXN>0QRl5@jA`jWdPjPYQ0?$0ORmPjP[P\Pj16D:#y=RfhR:Pj%yX=RfhRhC<FE3J3JP0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZPiPjMP>fdRj16DdRfPGPHfcS0XfbS0YfaRnQ04#5#Q#?,6DRoQ0V#5#YS0Z#5#H#H#H#H#H#H#?,6DRpf`Rqf_S0[f^S0\f]Rrf\Rsf[S0]fZS0^fYRtfXRu16Di16D]RifWS0_fVS0`fURvfTRwfSS0afRS0bfQRxfPRyfOS0cfNS0dfMRzMOFfLR{%5A#H#P#Z#p#Q#P#NS0e,6DR|fKS0f&0MER}fJ&0q4R~GBPeQ0f-074Q0U?oV{1_V{A@{klA`{WdP{PYPmP{P[P\P{P:P{PhC<FE3J3JQ00Q0U?oVz1_VzA@zklPzPWPdPzPYPmPzP[P\PzP:PzPhC<FECl3JP0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZP{PzMP>fhS0fPfPGPHfgS0gffS0hfeRzPoPpPjQ0XQ0YPnPqQ0[Q0\PrPs16D{PiQ0]Q0^PtPuQ0_Q0`PvPwQ0aQ0bPxMOFPyP|Q0cP}Q0dP~GBP3Q0UQ0c7oV1_VyA@yklPyPWPdPyPYPmPyP[P\PyP:PyPhC<FECl3JQ001_VxA@xklA`xWdPxPYPmPxP[P\PxP:PxPhC<FE3JP0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZPyPxMP>flRxPfPGPHfkS0cfjS0UfiS0dPoPpQ0fQ0gQ0hPzPjQ0XQ0YPnPq16DyPiQ0[Q0\PrPsQ0]Q0^PtPuQ0_Q0`PvMOFPwP|Q0aP}Q0bP~GBP3Q0a,_VA@wklA`wWdPwPYPmPwP[P\PwP:PwPhC<FE3JQ00A@vklPvPWPdPvPYPmPvP[P\PvP:PvPhC<FEClP0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZPwPvMP>fpRvPfPGPHfoS0afnRyfmR{PoPpPxQ0cQ0UQ0dQ0fQ0gQ0hPzPj16DwPiQ0XQ0YPnPqQ0[Q0\PrPsQ0]Q0^PtMOFPuP|Q0_P}Q0`P~GBP3Q0_?@klPuPWPdPuPYPmPuP[P\PuP:PuPhC<FEClQ00A`tWdPtPYPmPtP[P\PtP:PtPhC<FEP0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZPuPtMP>ftS0_PfPGPHfsRtfrRlfqS0`PoPpPvQ0aPyP{PxQ0cQ0UQ0dQ0f16DuPiQ0gQ0hPzPjQ0XQ0YPnPqQ0[Q0\PrMOFPsP|Q0]P}Q0^P~GBP3Q0]?`WdPsPYPmPsP[P\PsP:PsPhC<FEQ00B0IrYmPrP[P\PrP:1hrhJ0=P0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZPsPrMP>fxS0]PfPGPHfwS0^fvS0bfuRdPoPpQ0_PtPlQ0`PvQ0aPyP{Px16DsPiQ0cQ0UQ0dQ0fQ0gQ0hPzPjQ0XQ0YPnMOFPqP|Q0[P}Q0\P~GBP3Q0[@0IYmPqP[P\PqP:1hqhJ0=Q00Ajn[\PnP:PnPhC<P0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZPqPnMP>f|S0iPfPGPHf{S0jfzS0kfyS0lPoPpQ0]Q0^Q0bPdQ0_PtPlQ0`Pv16DqPiQ0aPyP{PxQ0cQ0UQ0dQ0fQ0gQ0hPzMOFPjP|Q0XP}Q0YP~GBP3Q0X?j[\PjP:PjPhC<Q0020Az:1hzhP0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZPjPzMP>p+01AS0mPfPGPHp+01@S0nf~S0of}S0pPoPpQ0iQ0jQ0kQ0lQ0]Q0^Q0bPdQ0_16DjPiPtPlQ0`PvQ0aPyP{PxQ0cQ0UQ0dMOFQ0fP|Q0gP}Q0hP~GBP3Q0g00A:Q0f/hhQ0?$0jQ0</imRmQ0?,i?Rh5:@S0h&0i\Q0<&0h\'iS0<Q0R1iE\R:+0gS0q5:@S0rP4P0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZQ0dQ0UMP>S0sp+01FS0tPfPGPHp+01ES0up+01DS0vp+01CS0wPoPpp+01BS0xQ0mQ0nQ0oQ0pQ0iQ0jQ0kQ0lQ0d,6DS0yPiQ0]Q0^Q0bPdQ0_PtPlQ0`PvQ0aPyMOFS0zP{P|PxP}Q0cP~Q0:Q08#4Rz#4S0{#4S0|#4#TRu#5#Q#TRk#4#Q#Y#T#Q#Z#Y#?RwQ0:/mw3nRwg01O1Q09Q0{#?Q09%?k'm3nQ09Q09%?u'm7n7Q0H#5S09#fRu%Yz#T#NRz1muz3nS0:H0eS0}Q04#?S04PEPEPEPEPEPE&0dERz11EyPzQ0i,1ES0~PzF2Q0w,1ES10PEPzPEQ0bPzD9S1111EGS12PEPEPzQ0y,1EPzQ0m,1ES0yPEPzPEPlPzD9S13F2F2Q0t,1ES14PEPEPEPzPEQ0kPzD9S1511EpS16PEPzPEQ0_PzD9S17Q0u,1ES18PEPEPzPEQ0]PzD9S19Q0o,1ES1:PEPz11EvPzK0cS1;F2P}PEPEPEPEPzPEQ0jPzD9S1<11EoS1=PEPzPEPdPzD9S1>C311EHS1?PEPEPzPEPiPzD9S1@Q0n,1ES1APEPzPEQ0`PzD9S1BC311EfS1CPEPEPEPzPEQ0lPzD9S1DQ0x,1ES1EPEPzPEPtPzD9S1FQ0v,1ES1GPEPEPzPEQ0^PzD9S1HQ0p,1ES1IPEPzPEQ0aPzD9S1JC3F2F2F2P{P9PE16D7S1K:0<Di#]Rk%5A#H#p#Q#Q#Q#T#P#NS1L,6DS1M%5A#H#P#Z#p#Z#NS1N,6DS1On0100000020000S1PPxP}Q0cP~FdQ0;#|S1QQ0;/1wS0;'SQ1Q20b4|Q0;3:dQ01,S9&0`w#Odg01OcS0100_?S0;#|S1QQ0;Q01P?Q0}Q04H0]'1S0;'SQ1Q&0\wQ0;3:dg01POS0;PEPEPEPEPEQ1JQ1IPzC3Q1GQ1HQ12PEPEPzQ0U,6D,1EPzQ1EQ1FF2F2p+01GS1J,1ES1QPEPEQ1<Q16Q1>Q14PEQ1DQ1AQ1BC3F2P}PEPEPEPEPzQ0~PzC3S0~Q1=Q11C3Q1?PEQ1@Q0yQ13C3Q1CPEPEQ15Q10Q17Q18Q1;F2F2F2PyP3P{P}PxP~Fd+0[X:EP9PEg01QV:0<Di#]Q0::0ZuD:09D|Q04,6D:09D|n0100000020000Q1PPkQ0eQ1LQ1NQ04PuQ0:Q1L#VQ1N#VN90YH0XPkP91S93A:9k3RuP9P0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZP{PyMP>PEPEPEPEPEQ13Q0yPzC3Q1QQ15Q12PEPEPz16D{,1EPzQ18Q11F2F2p+01JS11,1ES13PEPEPEPzQ1:PzC3S1:Q16Q19p+01IS1N,1ES1LPEQ0~Q10Q17C3F2P}PEPEPEPEPzQ1APzC3S1AQ1=Q1DC3Q1?PEQ1@Q1GQ1>C3Q1CPEPEPEPzQ1IPzC3S1IQ14Q1Hp+01HS1>,1ES17PEQ1<Q1EQ1FC3F2F2F2Q0`P9PEP6Q1MQ1On0100000020000PvP}Q0aP~GB^0uP6%Lk1S?7Q1K-08DS1K9:?7S1FdS0:Q1FP?Q1K208DiS04/^3#]S0e#LX;?P6P7P3J0;Q04/^7#]S1P#LP?Q041^37#]S1;#LX;?P3P]Q0rQ0<#aS1BQ05#?Ru%a:S05'wRw'[S0}&06@S01&06?S1R%a6%a3'[A:@6320V6340UX:@X=@S1SQ0<Q1BQ1B#VQ0qPwQ0RPu%VuP:Q05Q05#VJ0TN905S0qP<CtQ0}Q0h%amRw%ahR@'[S1TQ01Q1RQ1SPmPw%VwPhP@%V@N905S1SP>CtQ1T%gmS1R%;wS01%ghS1U%;@S1V%g:S1WQ05#;S1XQ0<#gS0<Q1B#;S1YQ03#?R:Q0Z#?R@+04S0Z1q7:S1Z%;@203:@Rh,q7[[S1[%;:Rwg01R;RmB0H:@6UW2S1\%;h\m^2wS1]Q07#?Rh-04:S07Q1Z%;h203:hS1^,q7[[S1ZB0H:h6VmX2wS1_Q1^#;\m^2wS1`p-0Rwg01RWRmQ0Q#IS0QQ0P#IS0PQ0O#IQ0N#IQ0M#IQ0K#IQ0J-02?Rh'~S0J'~3b3bg01SCS0K'vQ0T#IQ0S#IQ0R#IQ0L#IS0L;bh3bQ0K'v&0>mS0R5Rm3R&0BmS0S%\1&0P?Rh7Ae%\e?A;h7Ae%\=S0T7A5%\>9Ahe%\<S0M7A87A6&0R?S0N&0S?R@P@201?7S0OQ0{#MS0{'W&0MBRBP@P@P?Q0{g01SoS0{%UuS1aQ06#M61:?S06CcPBP@P@Q0V#MS0VQ065u?%U:>19?DS06'WPBP@P@Q0G#MS0GQ0H#MS0H'WPBP@%5A#Y#G#P#Z#G#G#NS1b#US1cQ0I#MR:5D@S0IQ09#MS099u?:S1dQ03#MR:5D@Q0OQ095D@S09Q0E,s@S035C@5C@5C@PBP@%GA#p#H#T#P#Z#NS1e#US1f20N?ARA5D@Q0W#5#T#NS0W#U9u?AS1gQ0C#5#Y#G#G#G#NS0C#U5D@5C@Q0HQ1a5u?S1a=D@AQ1gQ0V5D@5C@60L@PBP@P@Q0GQ0|#P#G#NS0|#US1g60K?,W:PBQ0O=D@AP?PAg01TVQ06Cc-18@5C@DKK0JDKDKDKDK217@CS06P3P5Q02,S921635#LdB15?76H13S02bAbIbJX4?X5?X6?X7?X8?X9?XK?XL?XM?W3%;11wu1,[e1wue,=;Q1^'717<;Q1b/7eQ0F,=e/7<Q0F#;Q0D'83JQ1e/7<S1eQ0W,=<R9Q0C'7'81=1u/7<179e'8'}Q0|-0G1,7>%;>S0DQ1^,q>'8[[[[[[[^4?^5?^6?^7?^8?^9?^K?^L?^M?^3wP31=bcg01U='7g01V9/7b'}S1^Q1BQ05PcPbP[PZPFPWP]P<Q0Fp,4VAHIp,3HAPS05p,6SEP_X2S1Bp,5SEP_FS0Gp,2LOS0VOAb@bEbFbGbHbQbPbObNb?b>-11]-10]S1hJ0F1^]7R9#]S1i#LRC%O9S1j\CQ1jPC[&0~9P3H0EQ1jQ001^63S1j#O1[56S1k#k[S1l1[63S1m#k1^56S1n#ORC[1[85S1o#k\C20{63P6n2001000000120000000X:?X=?Q1l^:?^=?P3P]P7P6O3S1lA:?]7S1p#kp,7HS_EXITP0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUQ0>PVPWPXPYQ0?PZP[P\Q0@Q0ANU0uP4P0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZPtQ0_MP>PEPEPEPEPEQ19Q1QPzC3p+01MS1q,1ES1rPEPzQ0yPzC3S0yQ12PEPEPz16DtS1s,1EPzp+01KS1t,1ES1uQ0~F2F2p+01PS1v,1EPEPEPEPzQ18PzC3S18Q16Q1:p+01OS1w,1ES1xPEPEPzQ10PzC3S10Q1LQ15C3F2P}PEPEPEPEPzQ14PzQ1=Q1AF2Q1?PEQ1@Q13Q1<C3Q1CPEPEPEPzQ1GPzC3S1Gp+01LS1y,1ES1zQ1Ip+01NR4,1ES1{PEPEPzQ1EPzQ17Q1DF2S1DF2F2F2Q0^Q1MQ0bP}PdP~FdRCQ1vPfPGPHQ1wP4Q1qPoPpQ1yQ1tQ11Q1NQ1>Q1JQ0tQ0uQ0vQ1sPiQ0wQ0xQ0mQ0nQ0oQ0pQ0iQ0jQ0kQ0lQ0]MOFQ0^Q1MQ0bP}PdP~FdRfQ0;/SCQ0;?:CfeP3Q1vQ1wP4Q1qPoPpQ1yQ1tQ11Q1NQ1>Q1JQ0tQ0uQ0vPiQ0wQ0xQ0mQ0nQ0oQ0pQ0iQ0jQ0kQ0lQ0]Q0^Q0bPdQ0_PtPlQ0`PvQ0aPyP{PxQ0cQ0UQ0dQ0fQ0gPsPjQ0XQ0YPnPqQ0[Q0\PrOeJ0tbcb0b1b0b0b0b1W0%OkQ0:Q1FP?Q1KQ0e#OX;?P6P7P3J0;Q1P#OP?Q04Q1;#OX;?P3P]Q1hJ0FQ1i#ORk%L9Rr\kPk\r&0s9P3H0EPrQ00Q1j#LQ1k[RrQ1mQ1n#LR9[Q1o\920r63P6n2001000000120000000X<?XR?Pr^<?^R?Q1lQ1pP0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPZPlPtMP>PEPEPEPEPEQ1HQ14PzC3Q1zQ1AQ12PEPEPz16Dl,1EPzQ13Q1<F2F2Q1xPEPEQ1GQ16Q1IQ1{Q1DF2P}PEPEPEQ18Q1=Q1:C3Q1?PEQ1@Q1LQ15C3Q1CPEPEQ10Q1uQ0~Q1rPEQ0yQ1QQ19C3F2F2F2Q0bQ1OPdP}Q0_P~GBQ0rQ0}Q0qPeCtQ0}Q0hQ1TQ1SQ0ECtQ1TQ1RQ01Q1UQ1VQ1WQ1XQ0<Q1YQ0ZQ1[Q1\Q1]Q07Q1ZQ1_Q1`Q0QQ0PQ0LQ0J'~3bQ0K'vQ0R5RmQ0SQ0M9Ah;Q0T7A5%\;9Ah8?A;h7A6Q0NP@P@P?Q08#MRhQ0{Q0OCcPBP@P@Q0H,W:PBP@Q0IQ1d=D@AQ091s@15C@5C@5C@PBP@Q1f=D@h1s@e5C@Q1a=D@hQ0F,s@5C@60L@PBP@P@Q1c/WAPBP@P@Q1g:0K?:,WAPBQ03DKDKK0JDKDKQ06Q02bAbIbJX4?X5?X6?X7?X8?X9?X3wXBwXCwXDwA:?57175=Q1b/7;1=;>/75Q0D/813JQ1eQ0F'81=;u/7<Q0E'8'}Q1b/7=Q0|-0G;,7<Q0B[[[[[[^4?^5?^6?^7?^8?^9?^3w^Bw^Cw^DwP3g01W5Q0W,=]Rw/7[Q0C,7wQ1^PcPbPZP]PFPWQ0EQ05Q1BQ0Gp,3GLOQ0VO@b@bEbFbGbHbQbPbObNb?b>+0vb0b1b0b0b0b1W0n0110001020101P3O1b0bnNB0wQ0sQ0zP{P|PxP}Q0cP~GBeb_b`WfWeP6P3O2n2001000010121000000W1WhP6P3O2n2001000010121000000W1WTP6P3O2n2001000010121000000W1WgP6P3O2n2001000010121000000W1WZP6P3O2n2001000010121000000W1WiP6P3O2n2001000010121000000W1WbP6P3O2n2001000010121000000W1WaP6P3O2n2001000010121000000bWW]WXWYWSW\WdWUW^WVbjXmEWsWoWqXkEXlEXrEXvEXuEZ0DEXxEXtEXw?Xy0W<WpW[Z0@EZ0?EZ0>EZ0=EZ0<EZ0;EZ0:EZ09EZ08EZ07EZ06EZ05EZ04EZ03EZ02EZ01EX~EX}EX|EX{EZ0CEZ0BEZ0AEWzP0P]P^P_P`PaPbPcPgP2PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUQ0>PVPWPXPYQ0?PZP[P\Q0@Q0ANU0xeo"). Qed.
End PrintfCore.

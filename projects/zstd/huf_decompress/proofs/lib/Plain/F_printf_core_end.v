(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_memset F_memcpy F_memchr F_strnlen Stdio_kit F_syscalls StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_printf_core_common.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_printf_core_end () := "C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface?sink_frame_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common4POSTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5PlainDF_printf_core_common7ctx_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common4finvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5PlainDF_printf_core_common8lo_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common3FokC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common8hi_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9F_pop_arg7va_areaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common9zb_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib5PlainDF_printf_core_common6S_EXITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec6evt_eqC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5PlainDF_printf_core_common5S_ENDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5Plain:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^47)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 155648)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((156856 <= Fp /\ Fp + 232 <= 359072) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((359080 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 156792 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 228064 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [psegs psegs] in *; fold psegs in *.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
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
Proof using GLO HAP HS_EXIT LO SEP_F VAHI.
ltac2:(KReplay.run1 (kr_t_F_printf_core_end ()) ["PrintfCore"] "p'0h01Kh11Hh21bi001bh32Hah44__x1h54__x2h64__x3h74__x4h81mh91zh:1xh;1yh<3LU0h=4LZB0h>7__arithh?4__ffh@4__p1hA4__p2hB4__p3hC8__sat129hD8__sat130hE8__sat131hF8__sat132hG8__varmaphH5__withI4__x5hJ4__x6hK4__x7hL4cstrhM5cstr0hN5cstr1hO5cstr2hP1nhQ3APChR2BYhS3DIGhT2FIhU3FI'hV3FOKhW3FRMhX4FRhihY2FthZ2HSh[2Hrh\3LOWh]2LUh^3LZBh_2MIh`2MUha2NXhb3PADhc4SSP1hd4SSP2he2SThf3VAAhg2WMhh2_Hhi3ahihj3alohk3apvhl5dietRhm6dietR0hn6dietR1ho6dietR2hp6dietR3hq4digshr9drhs_dieths2fcht4j128hu4l10nhv3padhw3pfxhx2plhy3plphz1rh{3s2sh|2sth}2x1h~3x10i013x11i023x12i033x13i043x14i053x15i063x16i073x17i083x18i093x21i0:3x22i0;3x23i0<3x24i0=3x25i0>3x26i0?3x27i0@3x28i0A3x29i0B3x30i0C3x31i0D2x5i0E2x6i0F2x7i0G2zap%0p%1p&0p&1p;1p;2p;Lp;Jp;<p;3p;6p;>p;Op;7p;4p;5p;Qp;Bp;8p,2StR0p4p300R1p10000p4p710p8P1p1000ap4p710p8P1g001jR1p4p710p8g002nR2p4p7210g003ZR3p4p710p8g0048j15Tg004]j1dTg005;j1vTg005^j1:TP2k211Tg006Cj1lTg006ek109Tg007EmL0gTg008LmJ07Tg009Pj1kTg009nj2BTg00:Km<1?Tg00;Sj10Tg00<2k20;Tg00<gk10<Tg00=Gj3QTg00=gj1yTg00>\k10fTg00?Lk20cTg00@Oj29Tg00@kR2j2<Tg00AFk205Tg00B:k60VTg00C;j3hTg00Com>0PTg00E7k10LTg00F2j24TP1lL>Tg00FXj1?Tg00G6lO@Tg00Ghk10ETg00HJk113Tg00ICj3rTg00J?k10qTg00KHj2sTg00Khj36k102Tg00LBk10nTg00M:k10mTg00Mkk20lTg00NBj7FTg00O4k10kTg00Oaj21Tg00PCj43Tg00Q0j3zTg00Q]j1XTg00R;k10iTg00SAk10hTg00TIk208Tg00UEj2;Tg00U_j2jTg00VRj3iTg00W5k40eTg00Wak50dTg00XJk30bTg00Y1k30aTg00Z3k20`Tg00Znk20_Tg00[Vk20^Tg00\Nk306Tg00]3j2wTg00]]k20\TP3j6VTg00^_k20[Tg00_Zk30ZTg00`Ek30YTg00a@k20XTg00bBk10WTg00cBk20UTg00cbk40TTg00dBk10STg00e3m>0RTg00ekk40QTg00fFj2`Tg00fcR3j1^Tg00gCR1j2uTg00g`k20OTg00hCk30NTg00h`j4qTg00iGj1pTg00ilk200Tg00jTj2gTg00k0k203Tg00kMj3~Tg00l1k204Tg00lZj2tTg00mFk10KTg00mdj2fTg00nBk11BTg00n`k11ATg00oKk20JTg00onk31@Tg010Qj4cTg011<j3}Tg011_k31>Tg012Bk20ITg012ek30GTg013Hk21;Tg013jk21:Tg014Vk319Tg0155k418Tg015gk20DTg016Ak20=Tg016^k212Tg017Uk210Tg018Xk60CTg0194k10~Tg019Uk40@Tg01:0j1nTg01:Ik20|Tg01:jmQ0zTg01<0k60yTg01<dk10xTg01=Fk20vTg01=fk20{Tg01>Ek60uTg01?;mQ0}Tg01@@j4bTg01A6k30tTg01Ajk40ATg01B\k40>Tg01CQk30sTg01DBk20rTg01EJmB14Tg01F0m<15Tg01FUk316Tg01G>k417Tg01G\j7{Tg01H@k70pTg01Hdk71<Tg01IHj8xTg01Ilk60oTf0R4#5#5p=8%:4#5p=M%54#5#5#5p=Pg01JPR5f2R6f1R7P4Cbp=C%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p>0w%:4#:p=J%04#0#0#0#0#0#0#0p>0j%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=Ug01KER8/94p=DB0t574p=\P5P6P7P4H0Ap=_P5f3R9g01KcR:P6CbP5P7g01L`R;P4Cb'<p=AP5f6R<f5R=f4R>H0>Ar967/<4'<p=I1<74,<6p=T%54#:p=7%:4#:#:#:p=H%54#?p=Kf7R?P<P=P>P9P6P7P4FF60s5p=EP5P9P6P7H0A/<4p=oP5P6P7P4H0>p>0?P5P7P;P4Cbp=mAr=>9P5P6P:P7Cb/<4'<p>0BP5P7P:P4Cbp>0:P<P=P>P9P6C3P7P4C3p=2P>P91167P4C3p==g01M_S0000r4p=]P<P=P>P9P6P7P4C3C3p>0]g01NfR:g01OFS01764p=Ng01OfS0296:4p=Og01PFR@?674p=Zg01PdRAPAPAP@P@P@g01QCP3P3P3P1g01QcP=P>P9P6P7P4NB14p>0MPAP@P4P3P7P6P9P>P=P<P?f8S03N<15p>01204@4p=RB16@74p=GP@P6P7P4H17p=Y20I@4p=[P@P7g01RFR3P4Ccp=a20J@4p=WP6g01RmR1g01SLRBPBg01SlRCP@P7P3P4Ccg01TLR3F{p=LP6P1PBPBPCP7P4K0pp=eP6P1PBPBPCP7P4K1<p>0HP7P1PBPBPCP4P3F{p>1=P>P1PBPBPCP9P1PBPBPCP6P3F{P7P4Gxp=SP<P1PBPBPCP=P>P9P1PBPBPCP6P7P4GxGxp>0FP7P1PBPBPCP4J0op=|g01TlR1#5S04#5S05#5S06#8R3#5S07#dRD#vREQ04#:S08#dS09011E%d3S0:#vS0;Q06#d#vS0<#l\EQ0<$09S0=Q0=Q0=p,2raR3p,1qRFp,2gpRGp,2tpRHp,3s0eRIp,3s1eRJp,3s2eRKp,3s3eRLp,3s4eRMp,3s5eRNp,3s6eROp,3s7eRPp,3s8eRQp,3s9eRRp,4s10eRSp,4s11eRTp,1FRUp,3fc0S0>p,2m0RVp,2loRWp,6canaryRXp,1ARYp,3fmtRZp,2APR[p,2VAR\p,5slotsR]p,3nlaS0?p,3nltS0@NL0gPBp,2FpR^p,1BR_p,2BSR`P3PFPIPJPKPLPMPNPOPPPQPRPSPTPVPWPXPYPZP[P\P]f?NJ07f@S0AQ06#M#P#k,BFRaP[Q0?Q0@f=f<S0Bf;S0Cf:S0Df9RbQ03P?P<P=N<1?3CfA%:1S0E#5S0F#8#M#8#k,BFg01UQRcg01VFS0G#0S0H#0S0I#0S0J#0S0K#0S0L#0S0M#0S0N#0S0O$0wRd00;=&0<cRe3Q3CfBRfQ08#JS0P#P#k,BF&0jd#U#U#U#U#U#U#U00;==Qce3Cp,4SINKRdfCPfO2fD%y<=Qce7C[fF$0ffHRf-0cUfERg#Dg01Ve,9g'<Q03P^P_P`P3PFPIPJPKPLPMPNPOPPPQPRPSPTPVPWPXPYPZP[P\P]PfNJ07P2fIRg-055P^P_P`PFPWP[J0VS0Q?hVg1\VgQ0E#:S0R#5S0S#5#8#k,BFRhP3PIPJPKPLPMPNPOPPPQPRPSPTPXN>0PRi5CgA_gWaPgPY&0LZRjPgP\P]Pg14D;#y=QceR;Pg%yX=QceReCAFI3T3TP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PfPgML>fdRg14DaRcPGPHfcRkfbS0TfaRlQ05#:#7#?,4DRmQ0R#H#H#H#H#H#H#H#?,4DRnf`Rof_S0Uf^S0Vf]Rpf\Rqf[S0WfZS0XfYRrfXRs14Df14D^RffWS0YfVS0ZfURtfTRufSS0[fRS0\fQRvfPRwfOS0]fNS0^fMRxMO@fLRy%P1#7#J#7#7#8#M#KRz,4DR{fKR|&0EER}fJ&135R~GEPb2055|Q0Q?hVy1\VyACyhiA_yWaPyPYPjPyP\P]PyP;PyPeCAFI3T3TP2Q0Q?hVx1\VxACxhiPxPWPaPxPYPjPxP\P]PxP;PxPeCAFICo3TP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PyPxML>fhRxPcPGPHfgR|ffS0_feRbPmPnPgPkQ0TPlPoQ0UQ0VPpPq14DyPfQ0WQ0XPrPsQ0YQ0ZPtPuQ0[Q0\PvMO@PwP{Q0]P}Q0^P~GEP4Q0QQ0]7hV1\VwACwhiPwPWPaPwPYPjPwP\P]PwP;PwPeCAFICo3TP21\VvACvhiA_vWaPvPYPjPvP\P]PvP;PvPeCAFI3TP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PwPvML>flRvPcPGPHfkS0]fjS0QfiRyPmPnPxP|Q0_PbPgPkQ0TPlPo14DwPfQ0UQ0VPpPqQ0WQ0XPrPsQ0YQ0ZPtMO@PuP{Q0[P}Q0\P~GEP4Q0[,\VACuhiA_uWaPuPYPjPuP\P]PuP;PuPeCAFI3TP2ACthiPtPWPaPtPYPjPtP\P]PtP;PtPeCAFICoP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PuPtML>fpS0[PcPGPHfoS0\fnS0^fmS0`PmPnPvQ0]Q0QPyPxP|Q0_PbPg14DuPfPkQ0TPlPoQ0UQ0VPpPqQ0WQ0XPrMO@PsP{Q0YP}Q0ZP~GEP4Q0Y?ChiPsPWPaPsPYPjPsP\P]PsP;PsPeCAFICoP2A_rWaPrPYPjPrP\P]PrP;PrPeCAFIP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PsPrML>ftRrPcPGPHfsRifrRhfqRuPmPnQ0[Q0\Q0^Q0`PvQ0]Q0QPyPx14DsPfP|Q0_PbPgPkQ0TPlPoQ0UQ0VPpMO@PqP{Q0WP}Q0XP~GEP4Q0W?_WaPqPYPjPqP\P]PqP;PqPeCAFIP2B0?pYjPpP\P]PpP;1mpeJ0BP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PqPpML>fxRpPcPGPHfwRafvS0WfuS0XPmPnPrPiPhPuQ0[Q0\Q0^Q0`Pv14DqPfQ0]Q0QPyPxP|Q0_PbPgPkQ0TPlMO@PoP{Q0UP}Q0VP~GEP4Q0U@0?YjPoP\P]PoP;1moeJ0BP2Arl\]PlP;PlPeCAP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PoPlML>f|S0UPcPGPHf{RqfzRsfyRtPmPnPpPaQ0WQ0XPrPiPhPuQ0[14DoPfQ0\Q0^Q0`PvQ0]Q0QPyPxP|Q0_PbMO@PgP{PkP}Q0TP~GEP4Ark\]PgP;PgPeCAP220:b;1mbeP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PgPbML>p+01AS0VPcPGPHp+01@S0Yf~S0Zf}S0aPmPnQ0UPqPsPtPpPaQ0WQ0XPr14DgPfPiPhPuQ0[Q0\Q0^Q0`PvQ0]Q0QPyMO@PxP{P|P}Q0_P~GEP420:|;1mxe&0qZQ0</sjS0b1s@ZS0c56AS0d&0n]Q0<&0m]'sS0<Q0O1sE]S0e+0lS0f56AS0gPcPEPmPEPnPE14DvPEP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[Q0`Q0^ML>Q00p-0Rj[P5P4p+01KS0hP>PGPHp+01JS0ip+01IS0jp+01HS0kP9P6p+01GS0lp+01FS0mp+01ES0np+01DS0op+01CS0pp+01BS0qQ0VQ0YQ0ZP7PfQ0aQ0UPqPsPtPpPaQ0WQ0XPrPiMO@PhP{PuP}Q0[P~FFRePEPEPEPEPEPE&0kER;11EiP;Q0q,1ES0rP;F2Q0k,1ES0sPEP;PEPqP;D=S0t11EGS0uPEPEP;11E7P;Q0m,1ES0vPEP;PEPaP;D=S0wF2F2Q0h,1ES0xPEPEPEP;PEQ0YP;D=S0y11E6S0zPEP;PEPtP;D=S0{Q0i,1ES0|PEPEP;PEQ0aP;D=S0}Q0o,1ES0~PEP;PEQ0XP;D=S10C3S11F2P}PEPEPEPEP;PEQ0VP;D=S1211E9S13PEP;PEPsP;D=S14C3S1511EHS16PEPEP;PEPfP;D=S17Q0n,1ES18PEP;PEQ0WP;D=S19C311E>S1:PEPEPEP;PEQ0ZP;D=S1;Q0l,1ES1<PEP;PEPpP;D=S1=Q0j,1ES1>PEPEP;PEQ0UP;D=S1?Q0p,1ES1@PEP;PEPrP;D=S1AC3F2F2F2PhP:PE14D8S1B9zDf#XRo%P1#7#H#H#M#K,4DS1C%P1#7#J#7#7#7#8#K,4DS1Dn0100000020000S1EPuP}Q0[P~FFS1F%lES1G&0ie;6}Q00$0hRw2085eQ1F#]Re36Q1G/;}PePwPwQ05#?S05,4DS1Gg01W^Q09Q08#5S1F#5Re#?Q09%5eS1H#5#8Re#:#7#8S1I#?'j3iQ09Q09%?e'j7i8Q0F#:#dReQ1F#J#8#KS09Q09,je3iS09H0eS1Jp+01LS1KP=PGPHQ0hQ0iQ0jP>P9Q0kQ0lQ0mQ0nQ0oQ0pQ0qQ0VQ0YP6PfQ0ZQ0aQ0UPqPsPtPpPaQ0WQ0XPrMO@S1LPiP{PhP}I0d40b>0a5u-0`~A6w47X8wPEQ09-0_eS1M-0^{S1NPEPEPEPEPEQ10Q0~P;C3Q0|Q0}Q0uPEPEP;Q13P;Q0sQ0{F2F2p+01MS13,1ES10PEPEPEP;Q0rP;C3S0rQ1:Q0tC3S1:Q1K,1ES1OPEQ0yQ0vQ0wK0]P}PEPEPEPEP;Q1@P;C3S1P11E=S1QQ1?C3Q16PEQ17Q1<Q1=C311E<PEPEQ12Q1>Q14Q0xPEQ1;Q18Q19C3S19F2F2F2S1RPrP:PEg01XPS1S9zDf#XS1TP4Q1G:06D{S1Gn0100000020000PiP}PhP~FF#]=6w7X2EPEQ05,Bz,4DS1UQ1RPrP:PEQ1TQ1NP4n0100000020000PiP}PhP~FF#]=6w7X2EPEQ1BQ1RPrP:PEAzDf4#XQ1NQ1Un0100000020000PiP}PhP~FF#]=6w7X2EPEQ1M,Bz,4DQ1RPrP:PEPoP4Q1Un0100000020000PiP}PhP~FF#]=6w7X2EPEPEPEPEPEQ1AQ1@P;C3Q1>Q1?Q0uPEPEP;Q0zP;Q1<Q1=F2F2Q1OPEQ15Q0xQ19C3P}PEPEQ1:Q16PEQ17Q0vQ0wC3Q1QPEPEQ0yQ0sQ0{Q0|Q11F2F2F2PiQ1EPhP}PuP~FF#],;w1wD{Q1M'B,4DQ1M-0\zEVQ1Sg01Y5EVQ1GQ05-0[zEVQ09:0ZeD:06D{Q09:0Y{eEVQ1LPiP{PhP}PuP~FF-085P5Q1LPiP{PhP}PuP~Q0:Q1I#5#7#J#8#7#M#8#J#?ReQ0:/je3iReQ1JQ05Q0;#lRzQ0;/1eRw';20X5{=6zwdQ01,;:&0We#Ndg01YkS0100U@Rw#lRzQ01P@Q1JQ05H0T,1wRw';&0Se=6zwdN>0REVbrH0QPoP:1;:4A6:o4RwP:P0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PhPiML>PEPEPEPEPEQ0wQ0vP;C3Q1OQ0yQ0uPEPEP;14Dh,1EP;Q0|Q0tF2F2p+01OS0t,1ES0wPEPEPEP;Q0~P;C3S0~11EnS05Q0}p+01NS1J,1ES01PEQ0rQ0sQ0{C3F2P}PEPEPEPEP;Q18P;C3S1811EmS0{Q1;C3Q16PEQ17Q1>Q14C311EcS14PEPEQ1PQ0xQ1?Q10PEQ12Q1<Q1=C3F2F2F2Q0WP:PEP7Q1CQ1Dn0100000020000Q0XP}PrP~GE^0wP7%Oo1;@8Q1B,wDS1B96@8S1=dS0;Q1=P@Q1B1wDfS0:/`4#XS1I#OX9@P7P8P4EVQ0:/`8#XS1L#OP@Q0:1`48#XS09#OX9@P4P^Q0gQ0<#^S1GQ06#?RwQ0e#^S06'uRz'ZS1S&02AS1M&02@S1E%^7%^4'ZA6A7420O7440NX;AX:ARAQ0<Q1GQ1G,;@Q0fPzQ0OPw1;@wQ0eQ06Q06,;@J0MN901S0fQ0DCqQ1SQ0dQ0b#^RzQ0c#^Re'ZS11Q1MQ1EPAQ0bPz1;@zQ0cPe1;@eN901S1EQ0BCqQ11Q0b#pS0b%DzS0BQ0<#pS0<Q1G#DS1MQ0c#pS0c%DeS1QQ0e#pS0eQ06#DS1:Q04#?ReQ0P#:#?Rz+00S0P1g8eS19%Dz203ezS15,g8[[S0z%DeS1@g01ZWRAA~ez7UW3S1AQ1@Q15#D\A]3S15Q07#?Rz-00eS07Q19%Dz203ezS1U,g8[[S19Q1@A~ez7VAW3S1RQ1@Q1U#D\A]3S1@g01[3RAQ0L#RQ0K#RS0KQ0I#RQ0H#RQ0G-04@Rz'G'GS0G'G'Gg01[_S0H'tQ0O#RQ0N#RQ0M#RQ0J#RS0J/Gz'G'G'GQ0H't&0<AS0M5QA3Q&09AS0N&0K@S0O1f@<1f@?7Y>7Y6Q0O1f@=7Y97Y7&1B@S0I&1A@RzPz20J@8S0LQ0S#[S1N'a&0EBRBPzPzP@Q1Ng01\KS1N%WwS1TQ1F#[61@@S1FCcPBPzPzQ0R#[S0RQ1F5}@%We>1>@DS1F'aPBPzPzQ0E#[S0EQ0F#[S0F'aPBPz%81#J#8#M#7#7#J#8#KS1V#WS1W20I@1Re5LzQ0S#:#8#KS0S#W9}@eS1X%51#M#H#7#7#7#P#KS1Y#W5Lz5ezQ0FQ1T5}@S1T=LzeQ1XQ0R5Lz5ez60HzPBPz%51#J#8#M#8#P#P#KS1X#WS0RQ04#[R15LzPBPzPzQ0EQ1H#M#P#KS1H#WS0460G@,a1PBQ0L=LzeP@Peg01]2Q1FCc-1=z5ezDSK0FDSDSDSDS21;zCS1FP4P6Q02,;:21:46#OdB19@87H18S02b?bGbHX4@X5@X6@X7@XI@XJ@XK@%D<1uw<,Z?1uw?,B<Q1U'919=<Q1V/9>S1VQ0S,B>R:Q1Y'9'<1B?w/9>Q03,9:'<+0DQ1X/9<Q03Q1H+0=,9?%D?Q1U,g?'<[[[[[[[^4@^5@^6@^7@^I@^J@^K@P4Q1GQ06P\P[PFPWP^P?Q0Dp,4VAHIp,3HAPS0Dp,5SEP_FS06p,3GLOS1Gp,2LOS1UO>b>bCbDbEbFbObNbMbLb=b<-12^-10^S0EJ0C1`^8R:#XS1Z#ORC%N:S1[\CQ1[PC[&0~:P4H0@Q1[P21`74S1[#N1Z67S1\#n[S1]1Z74S1^#n1`67S1_#NRC[1Z96S1`#n\C20|74P7n2001000000120000000X;@X:@Q1]^;@^:@P4P^P8P7O3S1]A6@^8S1a#np,7HS_EXITP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUQ0>PVPWPXPYPZP[P\P]Q0?Q0@NQ0zP5P0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PpPtML>PEPEPEPEPEQ0}Q1OP;C3p+01RS1b,1ES1cPEP;Q0vP;C3S0vQ0uPEPEP;14DpR5,1EP;p+01PS1d,1ES1eQ0rF2F2p+01US1f,1EPEPEPEP;Q0|P;C3S0|Q05Q0~p+01TS1g,1ES1hPEPEP;Q0sP;C3S0sQ01Q0yC3F2P}PEPEPEPEP;Q0xP;Q0{Q18F2Q16PEQ17Q0wQ12C3Q14PEPEPEP;Q1>P;C3S1>p+01QS1i,1ES1jQ1Pp+01SS1k,1ES1lPEPEP;Q1<P;Q10Q1;F2S1;F2F2F2Q0UQ1CPqP}PsP~FFRCQ1fPcPGPHQ1gQ1kQ1bPmPnQ1iQ1dQ0tQ1JQ13Q1KQ0hQ0iQ0jP5PfQ0kQ0lQ0mQ0nQ0oQ0pQ0qQ0VQ0YQ0ZQ0aMO@Q0UQ1CPqP}PsP~FFR5Q00/;CQ00?6C5eP4Q1fQ1gQ1kQ1bPmPnQ1iQ1dQ0tQ1JQ13Q1KQ0hQ0iQ0jPfQ0kQ0lQ0mQ0nQ0oQ0pQ0qQ0VQ0YQ0ZQ0aQ0UPqPsPtPpPaQ0WQ0XPrPiPhPuQ0[Q0\Q0^Q0`PvPlPyPxP|Q0_PbPgPkQ0TOeJ0ybab0b1b0b0b0b1W0%NoQ0;Q1=P@Q1BQ1I#NX9@P7P8P4EVQ1L#NP@Q0:Q09#NX9@P4P^Q0EJ0CQ1Z#NRo%O:Rk\oPo\k&0x:P4H0@PkP2Q1[#OQ1\[R2Q1^Q1_#ORk[Q1`\k20v74P7n2001000000120000000X8@XP@P2^8@^P@Q1]Q1aP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PaPpML>PEPEPEPEPEQ1?Q0xP;C3Q1jQ18Q0uPEPEP;14Da,1EP;Q0wQ12F2F2Q1hPEPEQ1>Q05Q1PQ1lQ1;F2P}PEPEPEQ0|Q0{Q0~C3Q16PEQ17Q01Q0yC3Q14PEPEQ0sQ1eQ0rQ1cPEQ0vQ1OQ0}C3F2F2F2PqQ1DPsP}PtP~GEQ0gQ1SQ0ff>CqQ1SQ0dQ11Q1EQ0ACqQ11Q0bQ0BQ0<Q1MQ0cQ1QQ0eQ1:Q0PQ0zQ1AQ15Q07Q19Q1RQ1@Q0KQ0JQ0G'G'GQ0H'tQ0M5QAQ0NQ0O1f@>7Y61f@9Q0O7Y>7Y7Q0IPzPzP@Q08#[RAQ1NQ0LCcPBPzPzQ0F,a1PBPzQ1W=LzA1|z<5ezQ1T=LzA1|z?5ez60HzPBPzQ0R=LzePBPzPzQ04:0G@1,aePBQ03,|zDSK0FDSDSQ1FQ02b?bGbHX4@X5@X6@X7@X@jXAjXBjA6@68196>Q1V/<<1B=w/9>/<?+0DQ1X/99Q1H-0==,9>Q0C[[[[[^4@^5@^6@^7@^@j^Aj^BjP4g01]YQ0S,B^Rj/9\Q1Y,9jP[P^PFPWQ0CQ0DQ06Q1GQ1UO<b>bCbDbEbFbObNbMbLb=b<+0{b0b1b0b0b0b1W0n0110001020101P4O1b0b2J0ubpbobnbmblP0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXP[PyQ0QML>Q0mPcPGPHQ0nQ0oQ0pPmPnQ0qQ0VQ0YQ0ZQ0aQ0UPqPsPt14DyPfPpPaQ0WQ0XPrPiPhPuQ0[Q0\Q0^MO@Q0`P{PvP}Q0]P~GEeb]b^WdWcP7P4O2n2001000010121000000W1WfP7P4O2n2001000010121000000W1WRP7P4O2n2001000010121000000W1WeP7P4O2n2001000010121000000W1WXP7P4O2n2001000010121000000W1WgP7P4O2n2001000010121000000W1W`P7P4O2n2001000010121000000W1W_P7P4O2n2001000010121000000bUW[WVWWWQWZWbWSW\WTbhXkEWvWqWtXiEXjEXuEXyEXxEZ0GEX{EXwEXz@X|0W8WsWYZ0CEZ0BEZ0AEZ0@EZ0?EZ0>EZ0=EZ0<EZ0;EZ0:EZ09EZ08EZ07EZ06EZ05EZ04EZ03EZ02EZ01EX~EZ0FEZ0EEZ0DEW}P0P^P_P`PdP3PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUQ0>PVPWPXPYPZP[P\P]Q0?Q0@NQ0}eo"). Qed.
End PrintfCore.

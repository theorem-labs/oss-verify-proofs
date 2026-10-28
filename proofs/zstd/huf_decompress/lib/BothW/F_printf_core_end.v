(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit Stdio_kitI F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Printf_zfacts F_printf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import F_printf_core_common.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_printf_core_end () := "C5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface?sink_frame_stmtC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common4POSTC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common7ctx_allC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common4finvK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8lo_cellsK47Corelib4Init9Datatypes3nat02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common3FokC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common1WC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common8hi_cellsC5ARocqVerifyHarness?AgentSubmission6Common<F_fmt_fp_lib2zbC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW9F_pop_arg7va_areaC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common9zb_lengthC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64s_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sC47Corelib4Init3Nat3mulK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC47Corelib4Init5Logic6eq_indC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common6S_EXITC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF7evtF_eqC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accC5ARocqVerifyHarness?AgentSubmission5BothWDF_printf_core_common5S_ENDC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls7got_sspC5ARocqVerifyHarness?AgentSubmission5BothW:F_syscalls9ssp_guardI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission6Common5FmtFp7INT_MAXC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litI4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Local Ltac acc_hint ::= lazymatch goal with |- acc_in _ (wa ?e, ?n) => change (wa e) with (Z_to_bv 64 e : word); solve_acc1 end.
  Local Ltac acc_enrich ::=
    repeat match goal with
    | H : nth_error ?l ?k = Some ?x |- _ =>
        lazymatch goal with _ : (k < length l)%nat |- _ => fail | _ => pose proof (nth_error_some_bound l k x H) end
    end;
    rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length, ?zb_length in *; cbn [length] in *; unfold zlength in *.
  Context {St : Type}.
  Variables (Fp B BS : Z) (RB : region) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS RB SINK TOPOK OUT.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (RNG : footprint) (rstk rfmt : region).
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
  Hypothesis HA : (A + zlength fmt <= 724992)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((737200 <= Fp /\ Fp + 232 <= 762616) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((6345432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis RSK : (r_lo rstk <= lo /\ q <= r_hi rstk)%Z.
  Hypothesis RFM : inreg rfmt A (zlength fmt).
  Hypothesis RPF : inreg rfmt 68436 9.
  Hypothesis RBI : inreg RB B BS.
  Hypothesis RG_stk : rng RNG lo (q - lo).
  Hypothesis RG_img : rng_aimg RNG.
  Hypothesis RG_ap : rng RNG AP 8.
  Hypothesis RG_va : rng RNG VA (8 * zlength slots).
  Hypothesis RG_F : rng RNG Fp 232.
  Hypothesis RG_B : rng RNG B BS.
  Hypothesis RG_fmt : rng RNG A (zlength fmt).
  Hypothesis RR_stk : rrng RNG rstk.
  Hypothesis RR_fmt : rrng RNG rfmt.
  Hypothesis RR_B : rrng RNG RB.
  Hypothesis ENV0 : ashenv m0.
  Hypothesis RC_stk : rclean m0 rstk.
  Hypothesis RC_fmt : rclean m0 rfmt.
  Hypothesis RC_B : rclean m0 RB.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation appW_W := (F_printf_core_common.appW_W Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B).
  Local Notation ashsafe_W := (F_printf_core_common.ashsafe_W Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP KH).
  Local Notation env_now := (F_printf_core_common.env_now Fp B BS q m0 lo AP VA LO GLO SEP_F SEP_B HAP KH ENV0).
  Local Notation rc_now := (F_printf_core_common.rc_now Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B).
  Local Notation arg_ok_s_W := (F_printf_core_common.arg_ok_s_W Fp B BS RNG q lo fmt AP slots).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  (* [comment removed for export] *)
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq RNG q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA RG_stk RG_img RG_ap RG_va).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq Fp B BS RB HSTRN RNG q gp tp m0 lo AP VA LO GLO QHI SEP_F SEP_B HAP KH RBI RG_stk RG_img ENV0 RC_B).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS RB SINK TOPOK OUTFP TOK RNG q gp tp m0 lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS RB SINK RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS RB SINK RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS RB SINK TOPOK OUTFP RNG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  (* [comment removed for export] *)
  Ltac len_norm := unfold zlength, zrepeat; rewrite ?repeat_length, ?zb_length, ?length_map, ?length_firstn, ?length_skipn, ?length_app; cbn [length]; try rewrite !Z2Nat.id by lia.
  Ltac inreg_side := solve [ unfold inreg in *; len_norm; unfold zlength in *; lia ].
  Ltac rng_side :=
    lazymatch goal with |- rng ?RNG0 ?lo' ?len' =>
      first [ assumption
            | match goal with H : rng RNG0 ?lo ?len |- _ => apply (rng_sub' RNG0 lo len lo' len' H); solve [len_norm; unfold zlength in *; lia] end ]
    end.
  Ltac body_reg_stk := exists rstk; split; [ exact RC_stk | split; [ inreg_side | exact RR_stk ] ].
  Ltac hypMU := match goal with H : munch _ m0 _ |- _ => exact H end.
  Ltac hypWM := match goal with H : wmono _ m0 _ |- _ => exact H end.
  (* [comment removed for export] *)
  Ltac memset_pad PADa :=
    eapply (memset_callZ RNG (r_lo rstk) (r_hi rstk) (r_rlo rstk) (r_rhi rstk));
    [ exact PADa | match goal with H : mem_inv _ _ |- _ => exact H end | lia | lia | lia | lia
    | match goal with H : stk _ _ _ _ |- _ => exact H end | lia | exact KH
    | eapply env_now; [ hypMU | hypWM ]
    | apply rclean_shclean; eapply rc_now; [ exact RC_stk | hypMU | hypWM ]
    | lia | lia | lia | lia | exact RG_img | rng_side | rng_side | exact RR_stk ].
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
  Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evtF_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
    eapply implAM_eq_ms; [ | tac ]; [ mseq | .. ].
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
  Ltac out_call_with r :=
    ileave; eapply implAM_bind;
    [ eapply (out_callq r);
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 721936 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6203920 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | |
      | hypMU | hypWM
      | first [ assumption | idtac ]
      | first [ inreg_side | idtac ]
      | first [ rng_side | idtac ]
      | first [ assumption | idtac ] ]
    | cbv beta ].
  Tactic Notation "out_call" constr(r) := out_call_with r.
  Tactic Notation "out_call" := out_call_with rfmt.
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call bsegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [bsegs bsegs] in *; fold bsegs in *.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    let rb := fresh "rb" in let RCb := fresh "RCb" in let IRb := fresh "IRb" in let RRb := fresh "RRb" in let RGb := fresh "RGb" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & (rb & RCb & IRb & RRb) & RGb & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & PFlo & PFhi & Hi4 & Hfl & HnI & Hnp & Hplp);
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
      split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [first [assumption | reflexivity | lia | zl] |];
      split; [match goal with H : rclean m0 ?r, H2 : inreg ?r _ _, H3 : rrng _ ?r |- _ => exists r; split; [exact H| split; [exact H2| exact H3]] end |];
      split; [assumption|];
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.

  Hypothesis HS_EXIT : S_EXIT.

  (* [comment removed for export] *)
  Lemma L_END : S_END.
Proof.
ltac2:(KReplay.run1 (kr_t_F_printf_core_end ()) ["CANSEC1"; "PrintfCore"] "p'0h01Kh11Hh21bi001bh32Hah44__x1h54__x2h64__x3h74__x4h81mh91zh:1xh;1yh<3LU0h=4LZB0h>7__arithh?4__ffh@4__p1hA4__p2hB4__p3hC8__sat129hD8__sat130hE8__sat131hF8__sat132hG8__varmaphH5__withI4__x5hJ4__x6hK4__x7hL4cstrhM5cstr0hN5cstr1hO5cstr2hP1nhQ3APChR2BYhS3DIGhT2FIhU3FI'hV3FOKhW3FRMhX4FRhihY2FthZ2HSh[2Hrh\3LOWh]2LUh^3LZBh_2MIh`2MUha2NXhb3PADhc4SSP1hd4SSP2he2SThf3VAAhg2WMhh2_Hhi3ahihj3alohk3apvhl4digshm2fchn4j128ho4l10nhp3padhq3pfxhr2plhs3plpht1rhu3s2shv2sthw2x1hx3x10hy3x11hz3x12h{3x13h|3x14h}3x15h~3x16i013x17i023x18i033x21i043x22i053x23i063x24i073x25i083x26i093x27i0:3x28i0;3x29i0<3x30i0=3x31i0>2x5i0?2x6i0@2x7i0A2zap%0p%1p&0p&1p;1p;2p;Pp;Jp;<p;3p;6p;>p;Lp;Op;7p;4p;5p;Up;:p;Bp;8p,2StR0p4p300R1p10000p4p710p8P1p1000ap4p710p8P1g001jR1p4p710p8g002nR2p4p7210g003ZR3p4p710p8g0048j15Tg004]j1gTg005;j1wTg005^j17TP2k216Tg006Cj1tTg006ek10<Tg007EmP0hTg008LmJ0:Tg009Pj1jTg009nj2?Tg00:Km<1ETg00;Sj10Tg00<2k20?Tg00<gj1|Tg00=Gj3QTg00=gj1zTg00>\k10gTg00?Lk20dTg00@Oj2:Tg00@kR2j2<Tg00AFk208Tg00B:k60YTg00C;j3lTg00Com>0PTg00E7k10OTg00F2j24TP1lLDTg00FXj1BTg00G6lOHTg00Ghk10ETg00HJk115Tg00ICj78Tg00J5j3oTg00K1k10tTg00L:j2uTg00LZj39k105Tg00M4k10pTg00Mlk10oTg00N]k20nTg00O4k10mTg00Oaj21Tg00PCj43Tg00Q0j3{Tg00Q]j1TTg00R;j2=Tg00RUk10jTg00S\k10iTg00Tdj2nTg00UWj3mTg00V:k40fTg00Vfk50eTg00WOk30cTg00X6k30bTg00YAk20aTg00Z=j2[Tg00[Ek20`Tg00[mk20_Tg00\ek309Tg00]Jj2xTg00^4k20^TP3j6UTg00_6k20]Tg00`1k30\Tg00`\k30[Tg00aWk20ZTg00b\k20XTg00c^k10WTg00d^k20VTg00e>k40UTg00e^k10TTg00fOm>0STg00gHk10RTg00h>k20QTg00h_j2`Tg00i<R3j1aTg00i\R1j2vTg00j9k20NTg00j\k30MTg00k9j4iTg00k`j1pTg00lEk203Tg00lmj2kTg00mIk206Tg00mfk302Tg00nJk207Tg00o3k201Tg00o_k11DTg010=j2hTg010[k11CTg0119k11BTg011dk20KTg012Gk31ATg012jj4eTg013Uk300Tg0148k31@Tg014[k20ITg015>k30GTg015ak21>Tg016Ck21=Tg016ok31<Tg017Nk41;Tg018@k20DTg018Zk20>Tg0197k214Tg019nk213Tg01;1k60ATg01;Mk112Tg01;nk40@Tg01<Ij1rTg01<bk210Tg01=CmU0|Tg01>Ik70{Tg01?@k10zTg01?bk20yTg01@Bk20~Tg01@am:0xTg01A^mU11Tg01Bcj4^Tg01CYk30wTg01DMk40JTg01E?k40;Tg01F4k40vTg01Fhk317Tg01GomB18Tg01HUm<0uTg01I:k319Tg01Ick41:Tg01JAj7}Tg01Jek70sTg01KIk70rTg01Kmj8yTg01LQk60qTf0R4#5#5p=6%54#5#5#5p=]g01M5R5f2R6f1R7P4C^p=E%74#5p=A%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p>0}%74#7p=W%04#0#0#0#0#0#0#0p>0l%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=Vg01MjR8/:4p=@B0w574p=_P5P6P7P4H0Jp=cP5f3R9g01NHR:P6C^P5P7g01OER;P4C^'<p=CP5f6R<f5R=f4R>H0;Ao967/<4'<p=I1<74,<6p=P%54#7p=;%74#7#7#7p=J%54#7#5#7p=d%54#Bp=LP5P6P7P4H0vp=FP5P9P6P7H0J/<4p=sP5P6P7P4H0;p>0BP5P7P;P4C^p=qAo=>9P5P6P:P7C^/<4'<p>0CP5P7P:P4C^p>0=P<P=P>P9P6C3P7P4C3p=2P>P91167P4C3p=>P<P=P>P9P6P7P4C3C3p>0kg01PDS00@1774p=\g01QKR:g01QkS01794p=Mg01RKS0299:4p=Ng01RkR??974p=Yg01SIR@P@P@P?P?P?g01ShP3P3P3P1g01THP=P>P9P6P7P4NB18p>0LP@P?P4P3P7P6P9P>P=P<f7R3f8S03N<0up>04207?4p=SB19?74p=GP?P6P7P4H1:p=K20I?4p=XP?P7g01TkR1P4Cep=b20K?4p=ZP6g01URRAg01V1RBPBg01VQRCP?P7P1P4Ceg01W1R1F}p=OP6PAPBPBPCP7P4K0sp=fP6PAPBPBPCP7P4K0rp>0HP7PAPBPBPCP4P1F}p>1?P>PAPBPBPCP9PAPBPBPCP6P1F}P7P4Gyp=RP<PAPBPBPCP=P>P9PAPBPBPCP6P7P4GyGyp>0FP7PAPBPBPCP4J0qp=~g01WQRA#5S04#5S05#5S06#6R1#5S07#gRD#wREQ04#7S08#gS09016E%g1S0:#wS0;Q06#g#wS0<#t\EQ0<$0<S0=Q0=Q0=p,2RBS0>p,3RNGR1p,4rstkS0?p,4rfmtS0@p,2raRFp,1qRGp,2gpRHp,2tpRIp,3s0eRJp,3s1eRKp,3s2eRLp,3s3eRMp,3s4eRNp,3s5eROp,3s6eRPp,3s7eRQp,3s8eRRp,3s9eRSp,4s10eRTp,4s11eRUp,1FRVp,3fc0S0Ap,2m0RWp,2loRXp,6canaryRYp,1ARZp,3fmtR[p,2APR\p,2VAR]p,5slotsR^p,3nlaS0Bp,3nltS0CNP0hPBp,2FpR_p,1BR`p,2BSRaPFPGPJPKPLPMPNPOPPPQPRPSPTPUPWPXPYPZP[P\P]P^f?NJ0:f@Q06#7S0D#5#]#j,?GRbP\Q0BQ0Cf=f<f;S0Ef:S0Ff9S0GQ03P3P<P=N<1E3EfA%7AS0H#5S0I#6#A#6#j,?Gg01X6Rcg01XkS0J#0S0K#0S0L#0S0M#0S0N#0S0O#0S0P#0S0Q#0S0R$0}Rd00?=%|cRe3Q3EfBRfQ08#WS0S#]#j,?G&0ld#V#V#V#V#V#V#V00?==Qce3Ep,4SINKRdfCPfO2fD%z<=Qce7E\fF$0gfHRf-0dVfERg#@g01YJ,:g'<Q03P_P`PaPFPGPJPKPLPMPNPOPPPQPRPSPTPUPWPXPYPZP[P\P]P^PfNJ0:P2fIRg-085P_P`PaPGPXP\J0YRh?lWg1_WgQ0H#7S0T#5S0U#5#6#j,?GRiPFPJPKPLPMPNPOPPPQPRPSPTPUPYN>0PRj5EgAcgXbPgPZ&0O[RkPgP]P^Pg14D;#z=QceR;Pg%zY=QceReCCFI3P3PP0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PfPgMLDfdRg14DbRcPHPIfcS0VfbS0WfaRlQ05#7#;#B,4DRmQ0T#J#J#J#J#J#J#J#B,4DRnf`Rof_S0Xf^S0Yf]Rpf\Rqf[S0ZfZS0[fYRrfXRs14Df14D_RffWS0\fVS0]fURtfTRufSRvfRS0^fQRwfPRxfORyfNS0_fMRzMOHfLR{%dA#6#;#d#A#;#A#LS0`,4DR|fKS0a&0EER}fJ&155R~F85F1Q0GQ0a-085AlhW{1_W{AE{ijAc{XbP{PZPkP{P]P^P{P;P{PeCCFI3P3PP2AlhWz1_WzAEzijPzPXPbPzPZPkPzP]P^PzP;PzPeCCFICs3PP0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\P{PzMLDfhS0aPcPHPIfgS0bffS0cfeRzPmPnPgQ0VQ0WPlPoQ0XQ0YPpPq14D{PfQ0ZQ0[PrPsQ0\Q0]PtPuPvQ0^PwMOHPxP|PyP}Q0_P~F85F1P4AlhWy1_WxAExijPxPXPbPxPZPkPxP]P^PxP;PxPeCCFICs3PP21_WwAEwijAcwXbPwPZPkPwP]P^PwP;PwPeCCFI3PP0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PxPwMLDflRwPcPHPIfkRyfjRhfiR{PmPnQ0aQ0bQ0cPzPgQ0VQ0WPlPo14DxPfQ0XQ0YPpPqQ0ZQ0[PrPsQ0\Q0]PtMOHPuP|PvP}Q0^P~F85F1P41_WvAEuijAcuXbPuPZPkPuP]P^PuP;PuPeCCFI3PP2AEtijPtPXPbPtPZPkPtP]P^PtP;PtPeCCFICsP0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PuPtMLDfpRtPcPHPIfoS0^fnRvfmRxPmPnPwPyPhP{Q0aQ0bQ0cPzPg14DuPfQ0VQ0WPlPoQ0XQ0YPpPqQ0ZQ0[PrMOHPsP|Q0\P}Q0]P~F85F1P4Q0\?EijPsPXPbPsPZPkPsP]P^PsP;PsPeCCFICsP2AcrXbPrPZPkPrP]P^PrP;PrPeCCFIP0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PsPrMLDftS0\PcPHPIfsRrfrRjfqS0]PmPnPtQ0^PvPxPwPyPhP{Q0a14DsPfQ0bQ0cPzPgQ0VQ0WPlPoQ0XQ0YPpMOHPqP|Q0ZP}Q0[P~F85F1P4Q0Z?cXbPqPZPkPqP]P^PqP;PqPeCCFIP2B0BpZkPpP]P^PpP;1qpeJ0CP0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PqPpMLDfxS0ZPcPHPIfwS0[fvS0_fuRbPmPnQ0\PrPjQ0]PtQ0^PvPxPw14DqPfPyPhP{Q0aQ0bQ0cPzPgQ0VQ0WPlMOHPoP|Q0XP}Q0YP~F85F1P4Q0X@0BZkPoP]P^PoP;1qoeJ0CP2Aol]^PlP;PlPeCCP0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PoPlMLDf|S0dPcPHPIf{S0efzS0ffyS0gPmPnQ0ZQ0[Q0_PbQ0\PrPjQ0]Pt14DoPfQ0^PvPxPwPyPhP{Q0aQ0bQ0cPzMOHPgP|Q0VP}Q0WP~F85F1P4Q0V?o]^PgP;PgPeCCP220=z;1qzeP0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PgPzMLDp+01AS0hPcPHPIp+01@S0if~S0jf}S0kPmPnQ0dQ0eQ0fQ0gQ0ZQ0[Q0_PbQ0\14DgPfPrPjQ0]PtQ0^PvPxPwPyPhP{MOHQ0aP|Q0bP}Q0cP~F85F1P4Q0b00=;Q0a/qe&0t[Q0</ukS0c1u?[S0l59@S0m&0p^Q0<&0o^'uS0<Q0R1uE^S0n+0nS0o59@S0pP5P1P0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\P{PhMLDS0qp+01FS0rPcPHPIp+01ES0sp+01DS0tp+01CS0uPmPnp+01BS0vQ0hQ0iQ0jQ0kQ0dQ0eQ0fQ0g14D{RkPfQ0ZQ0[Q0_PbQ0\PrPjQ0]PtQ0^PvMOHS0wPxP|PwP}PyP~F8S0xPEPEPEPEPEPE&0mERe11EvPeQ0d,1ES0yPeF2Q0u,1ES0zPEPePEQ0_PeD>S0{11EHS0|PEPEPe11EkPeQ0h,1ES0}PEPePEPjPeD>S0~F2F2Q0r,1ES10PEPEPEPePEQ0fPeD>S1111EnS12PEPePEQ0\PeD>S13Q0s,1ES14PEPEPePEQ0ZPeD>S15Q0j,1ES16PEPe11EtPeK0kS17F2P}PEPEPEPEPePEQ0ePeD>S1811EmS19PEPePEPbPeD>S1:C311EIS1;PEPEPePEPfPeD>S1<Q0i,1ES1=PEPePEQ0]PeD>S1>C311EcS1?PEPEPEPePEQ0gPeD>S1@Q0v,1ES1APEPePEPrPeD>S1BQ0t,1ES1CPEPEPePEQ0[PeD>S1DQ0k,1ES1EPEPePEQ0^PeD>S1FC3F2F2F2PxP:PE14D8S1G9{Df#TRk%dA#6#;#A#6#;#6#A#L,4DS1H%dA#6#;#d#A#A#6#L,4DS1In0100000020000S1JPwP}PyP~F8S1Kg01ZCS1L#|R;%tE/=}Q00$0jRz$0iRsQ05#BS05,4DS1Mg01[HQ09Q08#5S1N#5Ri#BQ09%5iS1O#5#6Ri#7#;#6S1P#B'n3mQ09Q09%Bi'n7m8Q0I#7#gRiQ1N#W#6#LRu1niu3mS09H0fS1QQ0wPxP|PwP}I0e40c>0b5y-0a~S1RPEPEPEPEPEQ1FQ1EPeC3Q1CQ1DQ0|PEPEPe14Dh,1EPeQ1AQ1BF2F2p+01GS1F,1ES1SPEPEQ18Q12Q1:Q10PEQ1@Q1=Q1>C3F2P}PEPEPEPEPeQ0yPeC3S0yQ19Q0{C3Q1;PEQ1<Q0}Q0~C3Q1?PEPEQ11Q0zQ13Q14Q17F2F2F2S17PvQ1JPxP}PwP~F8/\;,[zRu99s4X8sPEQ09-0`iS1J-0_|S1>Q17PvP:PEg01\:S1T9{Df#TS1UP4Q1M:09D|S1Mn0100000020000PxP}PwP~F8/\;,[z=9suX2EPEQ0`Q05'?,4DS1VQ17PvP:PEQ1UQ1>P4n0100000020000PxP}PwP~F8/\;,[z=9suX2EPEQ1GQ17PvP:PEA{Df4#TQ1>Q1Vn0100000020000PxP}PwP~F8/\;,[z=9suX2EPEQ0`Q1J'?,4DQ17PvP:PEPkP4Q1Vn0100000020000PxP}PwP~F8/\;,[z=9suX2EQ1K/\;,[zRz,=s1xD|Q1J'?,4DQ0`Q1J+0^EUQ1Tg01\_EUQ1MQ0`Q05+0]EUQ09:0\iD:09D|Q09:0[|iEUQ1R=9szeQ0x-0Z5P5Q0wPxP|PwP}PyP~Q0:Q1P#5#;#W#6#;#A#6#W#BRzQ0:/nz3mRzQ1QQ05Q0;#tRsQ0;/1zRi'=20X5|=9sidQ01,=:&0Wz#Mdg01]URi00V?Rs#tR|PiP?Q1QQ05H0U,1sRs'=&0Tz=9|sdN>0SEUQ1L&0R1+0QPkP:1=:4A9:k4RsP:P0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PxPvMLDPEPEPEPEPEQ0~Q0}PeC3Q1SQ11Q0|PEPEPe14Dx,1EPeQ14Q0{F2F2p+01JS0{,1ES0~PEPEPEPeQ16PeC3S16Q12Q15p+01IS1L,1ES05PEQ0yQ0zQ13C3F2P}PEPEPEPEPeQ1=PeC3S1=Q19Q1@C3Q1;PEQ1<Q1CQ1:C3Q1?PEPEPEPeQ1EPeC3S1EQ10Q1Dp+01HS1:,1ES13PEQ18Q1AQ1BC3F2F2F2Q0]P:PEP7Q1HQ1In0100000020000PtP}Q0^P~F85F1^0sP7%Nk1=?8Q1G,xDS1G99?8S1BdS1QQ1BP?Q1G1xDfS01/`4#TS0;#NX9?P7P8P4EUQ01/`8#TS0:#NP?Q011`48#TS1P#NX9?P4P_Q0pQ0<#aS0wQ06#BRsQ0n#aR|'vRz'YS06&05@Ri&05?R;%a7%a4'YA9@7420N7440MX;@X:@R@Q0<Q0wQ0w,=?Q0oPzQ0RPs1=?sQ0nP|1=?|J0LN904S0oP=CiQ06Q0mQ0c#aRzQ0l#aRu'YS1RPiP;P@Q0cPz1=?zQ0lPu1=?uN904S09P3CiQ1RQ0c#pS0c%@zS0`Q0<#pS0<Q0w#@S1MQ0l#pS0l%@uS1TQ0n#pS0n%@|S1JQ04#BRuQ0S#7#BRz+03S0S1k8uS1K%@z206uzR@,k8[[S1V%@uR;g01^ARiB02uz7UW3S17%@@\i^3;S1>Q07#BR@-03uS07Q1K%@@206u@Rz,k8[[S1KB02u@7ViX3;S1U%@z\i^3;S1Wg01^]R;Q0O#SQ0N#SS0NQ0L#SQ0K#SQ0J-07?Ri'G'GS0J'G'Gg01_IS0K+01Q0R#SQ0Q#SQ0P#SQ0M#SS0M/Gi'G'G'GQ0K+01%|;S0P5Q;3Q&0<;S0Q&1D?Ri1h?<?K>i7K61h?3?K3i?K3i1h?=7K97K7&1C?S0R&1B?R@P@20K?8S0LQ0D#XS0D'b&0EBRBP@P@P?Q0Dg01`5S0D%ZsS0OQ1N#X61A?S1NCePBP@P@Q0T#XS0TQ1N600?%Zu>1@?DS1N'bPBP@P@Q0H#XS0HQ0I#XS0I'bPBP@%;A#A#;#W#J#;#A#6#LS1X#ZS1Y20I?ARu5O@Q0U#7#6#LS0U#Z:00?uS1Z%;A#W#;#6#d#J#6#LS1[#Z5O@5f@Q0IQ0O600?S0O=O@uQ1ZQ0T5O@5f@60H@PBP@%7A#]#;#W#A#6#]#]#LS1Z#ZS0TQ04#XRA5O@PBP@P@Q0HQ1O#A#]#LS1O#ZS0460G?,bAPBQ0L=O@uP?Pug01`\Q1NCe-1?@5f@DRK0FDRDRDRDR21>@CS1NP4P6Q02,=:21=46#NdB1<?87H1;S02b?bGbHX4?X5?X6?X7?XI?XJ?XK?%@<1vs<,Y31vs3,?</:z1:=<Q1X/:>S1XQ0U,?>R:Q1[':'<1?3s/:>Q03,::'<+0DQ1Z/:<Q03Q1O+0>,:3%@31k3z'<[[[[[[[^4?^5?^6?^7?^I?^J?^K?P4Q0wP|P]P\PGPXP_P3Q0Fp,4VAHIp,3HAPS0Fp,5SEP_FS0wp,3GLOS0Hp,2LOS1\O>b>bCbDbEbFbObNbMbLb=b<-14_-13_S1]J0A1`_8R|#TS1^#NRz%M|R:\zPz\:&12|P4H0@P:P21`74S1_#M1Y67S1`#r[R:1Y74S1a#r1`67S1b#MRz[1Y96S1c#r\z21074P7n2001000000120000000X;?X:?P:^;?^:?P4P_P8P7O3S1dA9?_8S1e#rp,7HS_EXITP0P_P`PaQ0>PdP1Q0?Q0@PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVQ0APWPXPYPZP[P\P]P^Q0BQ0CNU0|P5P1P0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PrQ0\MLDPEPEPEPEPEQ15Q1SPeC3p+01MS1f,1ES1gPEPeQ0}PeC3S0}Q0|PEPEPe14DrS1h,1EPep+01KS1i,1ES1jQ0yF2F2p+01PS1k,1EPEPEPEPeQ14PeC3S14Q12Q16p+01OR5,1ES1lPEPEPeQ0zPeC3S0zQ05Q11C3F2P}PEPEPEPEPeQ10PeQ19Q1=F2Q1;PEQ1<Q0~Q18C3Q1?PEPEPEPeQ1CPeC3S1Cp+01LR:,1ES1mQ1Ep+01NRz,1ES1nPEPEPeQ1APeQ13Q1@F2S1@F2F2F2Q0[Q1HQ0_P}PbP~F8RCQ1kPcPHPIP5PzQ1fPmPnP:Q1iQ0{Q1LQ1:Q1FQ0rQ0sQ0tQ1hPfQ0uQ0vQ0hQ0iQ0jQ0kQ0dQ0eQ0fQ0gQ0ZMOHQ0[Q1HQ0_P}PbP~F8RcQ00/=CQ00?9CceP4Q1kP5PzQ1fPmPnP:Q1iQ0{Q1LQ1:Q1FQ0rQ0sQ0tPfQ0uQ0vQ0hQ0iQ0jQ0kQ0dQ0eQ0fQ0gQ0ZQ0[Q0_PbQ0\PrPjQ0]PtQ0^PvPxPwPyPhP{Q0aQ0bPqPgQ0VQ0WPlPoQ0XQ0YPpOeK0{bab0b1b0b0b0b1W0%MkQ1QQ1BP?Q1GQ0;#MX9?P7P8P4EUQ0:#MP?Q01Q1P#MX9?P4P_Q1]J0AQ1^#MRk%N|Rp\kPk\p&0z|P4H0@PpP2Q1_#NQ1`[R2Q1aQ1b#NRp[Q1c\p20y74P7n2001000000120000000X8?XP?P2^8?^P?Q1dQ1eP0P_P`PaPdPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYP\PjPrMLDPEPEPEPEPEQ1DQ10PeC3Q1mQ1=Q0|PEPEPe14Dj,1EPeQ0~Q18F2F2Q1lPEPEQ1CQ12Q1EQ1nQ1@F2P}PEPEPEQ14Q19Q16C3Q1;PEQ1<Q05Q11C3Q1?PEPEQ0zQ1jQ0yQ1gPEQ0}Q1SQ15C3F2F2F2Q0_Q1IPbP}Q0\P~F85F1Q0pQ06Q0oQ0GCiQ06Q0mQ1RQ09Q0ECiQ1RQ0cQ0`Q0<Q1MQ0lQ1TQ0nQ1JQ0SQ1VQ17Q1>Q07Q1KQ1UQ1Wp-0R~Q0NQ0MQ0J'G'GQ0K+01Q0P5Q;Q0Q1h?>9Ki61h?9?K>i7K7Q0RP@P@P?Q08#XRiQ0DQ0LCePBP@P@Q0I,bAPBP@Q1Y=O@i1~@<5f@Q0O=O@i1~@35f@60H@PBP@Q0T=O@uPBP@P@Q04:0G?A,buPBQ03,~@DRK0FDRDRQ1NQ02b?bGbHX4?X5?X6?X7?X@~XA~WBA9?681:6>Q1X/<<1?=s/:>/<3+0DQ1Z/:9Q1O-0>=,:>Q0E[[[[[^4?^5?^6?^7?^@~^A~^B~P4g01aCQ0U,?_R~/:]Q1[,:~P\P_PGPXQ0EQ0FQ0wQ0HQ1\O<b>bCbDbEbFbObNbMbLb=b<+0~b0b1b0b0b0b1W0n0110001020101P4O1b0b2N:0xQ0qQ0x5F1eb]b^WdWcP7P4O2n2001000010121000000W1WfP7P4O2n2001000010121000000W1WRP7P4O2n2001000010121000000W1WeP7P4O2n2001000010121000000W1WXP7P4O2n2001000010121000000W1WgP7P4O2n2001000010121000000W1W`P7P4O2n2001000010121000000W1W_P7P4O2n2001000010121000000bUW[WVWWWQWZWbWSW\WTbhXkEWpWlWnXiEXjEXoEXsEXrEZ0AEXuEXqEXt?Xv0W8WmWYZ0=EZ0<EZ0;EZ0:EZ09EZ08EZ07EZ06EZ05EZ04EZ03EZ02EZ01EX~EX}EX|EX{EXzEXyEXxEZ0@EZ0?EZ0>EWwP0P_P`PaQ0>PdP1Q0?Q0@PFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVQ0APWPXPYPZP[P\P]P^Q0BQ0CNU11eo"). Qed.
End PrintfCore.
End CANSEC1.

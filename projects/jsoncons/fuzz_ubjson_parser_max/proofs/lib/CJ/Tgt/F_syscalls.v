(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac ITree Nodes SysStep.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_F_syscalls () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1nil"; "1option"; "2or"; "3Z"; "0F"; "4bvmap"; "5C4"; "5cell"; "6evt"; "7mkR"; "7stk"; "8MS"; "9mem_inv"; ":rw_cells"]; [";rsegs"; ";sysret_post"; "<seg_rom"; "=add"; "=le"; "=sub"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0errv"; "0fc"]; ["0gp"; "0lo"; "0m"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"]; ["0sp"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rsegs := Ubsan.Ubsan_loaded_segments.
Definition sysret_entry := 0x99ce4%Z.
Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
Section SE.
Local Abbreviation SEC_T_sysret_spec := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_F_syscalls "TE'QByR0%211&7y5%2213yQ0%711'3y8%:11%311p0:1'5&<&@r3r1&QCrQ3%22C1%746541&?r4&CrQ2%82I1-U4%4221(1'9(8%11@(2%114%63531%>4E=81&>r5%22H1&D&ErQ6%I2Q:1+@%4221%62G1'4rQ5%O2Q@1%J21G+4%L221rQ7%Q42QE1%>21;%@241%A237%;221+U4%D21A&:&ArQ:rQ9rQ8rIrHrGrFrErDrCrBrAr@rQ1r8r;r:r7r9%DFCBAMQOQI@?>=<;:987654321&=&;rQ4rQ0rOrNrMrLrKrJr?r>r=r<%=OQ2Q1Q0Q<QGQA<R>R8E;:98765ONMLKJIHGF4321&QA+cWW4%22S31(0%11S4&B%11RI%F78K5J3H1%Q=3RKH1p0Q?1p0QB1p0QO1p0R71p0R;1p0RK1pR4S41pQNS@1pR6S71pR0S=1p>S@1pSFSD1pSDSE1pSBSF1pS@SG1pR@SH1pR>SI1pS0SJ1pRNSK1pRLSL1pRJSM1pRHSN1pRFSO1pRDT01pRBT11pQLT21pQJT31pQHT41pQFT51pQDT61pQBT71pQ@T81pQ>T91pR<T:1pR:T;1pS>T<1pS<T=1pS:T>1pSHT?1pR2T@1pS2TA1pR8TB1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 32%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 33%nat 0%nat).
Variable errv : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 34%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_sysret_spec) 35%nat 0%nat).
Lemma sysret_spec : ltac:(sec_stmt2 constr:(SEC_T_sysret_spec) 36%nat 0%nat).
Proof.
intros ST ERR MI LO SEP TP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
do 3 step. if_cases Hc; zify_cond Hc.
-
step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
- carve_frame 16%nat ST.
do 14 step.
pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
rewrite negw_errno in ERR by lia.
unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
release_frame FR ST (bv_unsigned sp).
finish.
Qed.
End SE.
Definition got_ssp := 0xb5f18%Z.
Definition ssp_guard := 0xe8f20%Z.
End CEIL_WRAP_1.

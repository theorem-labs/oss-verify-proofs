(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac ITree Nodes SysStep Decode.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import F_syscalls RMallocRep.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_mm_syscalls () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree.Exc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_mm_syscalls.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1cons"; "1nil"; "1option"; "2and"; "2eq"; "2or"; "3Z"; "0F"; "0L"; "4bvmap"; "0P"; "0RUNp"; "5C4"; "5C8"]; ["5cell"; "6dec_mprotect"; "6dec_munmap"; "6mmap_len"; "6range_ans"; "7evt"; "8mkR"; "8stk"; ":exc"; "9enode"; "9epost"; "9impl"; ";MS"; "<mem_inv"; "=NMprotect"; "=NMunmap"]; ["=at_node"; "=node"; ">alloc_ceiling"; "?rw_cells"; "@rsegs"; "ARVMLOCK"; "Armprotect_post"; "Armunmap_post"; "Arvmwait_post"; "BRPAGE_SIZE"; "Brmprotect_entry"; "Brmunmap_entry"; "Cseg_rom"; "Dadd"; "Dland"; "Dle"]; ["Dlt"; "Dmodulo"; "Dpow"; "Dsub"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0errv"; "0fc"; "0gp"; "0lo"]; ["0m"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "EZ_to_bv"]; ["Ebv"; "Ebv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0y"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition RVMLOCK : Z := 0xe8854.
Definition rvmwait_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a0 a2 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' RVMLOCK [C4 (Z_to_bv 64 0)].
Section SE.
Local Abbreviation SEC_T_rvmwait_spec := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_mm_syscalls "T:'R@yR0%211&;y5%2213yQ0%711'4y8%:11%311p0:1'8&G&Q4r2r1&RArQ2%22C1%746541&Q3r3&Q5(2'@(>&R?z%22M1%411(3%117%93831%=4D<;1&Mr4%22G1&Q?&QCrQ5%H2Q91+Q0%4221%6281&Q2v=%211r5%;221&E&Q8rQ8rQ7rQ6rQ4rQ3rQ1rQ0rNrLrKrJrIrHrGrFrErDrCrBrAr@r?r>r=r<r;r:r9r8r6r7%Q0Q1ONMQ;LKR1JIHGFEDCBA@?>=<;:987654321&L&FrOrM%3OQ4Q3Q2Q@Q1Q0R6ON2M1LKJIHGFEDCBA@?>=<;:+e^Q<%QO2RJ1(1%11RK&Q<%11R@%;77@5?3=1%Q>3RB=1p0Q@1p0QF1p0QN1p0R21p0RA1pT0RJ1pT2RL1pSLS21pDS51pUBS91pU@S:1pU>S;1pU<S<1pT<S=1pT:S>1pTLS?1pTJS@1pTHSA1pTFSB1pTDSC1pTBSD1pT@SE1pT>SF1pSHSG1pSFSH1pSDSI1pSBSJ1pS@SK1pS>SL1pS<SM1pS:SN1pT8SO1pT6T01pU:T11pU8T21pU6T31pUDT41pSNT51pTNT61pT4T71")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 32%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 33%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rvmwait_spec) 34%nat 0%nat).
Lemma rvmwait_spec : ltac:(sec_stmt2 constr:(SEC_T_rvmwait_spec) 35%nat 0%nat).
Proof.
intros ST VML MI LO CEILJ. pose proof alloc_ceiling_lo as CEILJ0. unfold RVMLOCK in *.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 32%nat ST.
do 7 step.
step. if_cases KVW; zify_cond KVW. 2:{ exfalso. rewrite ?unsigned_lit in KVW by lia. first [lia | apply KVW; reflexivity]. }
clear KVW.
do 5 step.
release_frame FR ST (bv_unsigned sp).
unfold rvmwait_post. finish.
Qed.
End SE.
Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
/\ (match a with RgDone true => True | _ => wmono rsegs m m' end)
/\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
/\ match a with RgErr e => (1 <= e <= 4095)%Z | _ => True end.
Section SE.
Local Abbreviation SEC_T_rmunmap_spec := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_mm_syscalls "VN'R@yR0%211&;y5%2213yQ0%711'4y8%:11%311p0:1'8&G&Q4r5r1&RArQ5%22C1%746541&Q3r6&Q=rQ4%82I1-U4%4221(2'@(>r3%211(3%115%73631%?4F>91&Mr7%22I1r8&Q5&R?z%22Q<1%?11%B3A1<%J4Q1761&Q?&Q2v=%211%421Q5'6rQ2r9%>2QH1%43QH31&Q@r;%22A1r<&C%114%Q9231&QB+2+R0%3221%E251'5%=2L:%>2;4%3221&QCrQ?%QK2R<1%321:%N2C1'7rQ>%R02RA1%QK21QH+4%QM221rQ@%R52RF1%=21D%Q8241%Q9237%;221r@r?%O11%R7231r=%Q@221rQA%RA2S21%QC218%E241rA%Q81;%R@221%RA2BR>%QI221%RC22G%QK216%M231+U4%QN21<&K'Q1&Q0%11S4'H'D%211&I(OrCrB%3221&B%1243%74=931&J&Q7rQErQDrQCrQBrQ=rQ3rQ1rQ0rOrNrMrLrKrFrErD%AG@?>=R0<SH;RJ:98765432HGQ;QE1%C2M1&L&FrQ<rQ;rQ:rQ9rQ8rQ7rQ6rJrIrHrG%<OONMLQNR:RDR?K;:98765T=T7JS9IHGFEDC4321&Q;%SG2U11(1%11U2&Q<%11TG%D77I5H3G1%QH7QGTIQEQBQ:F1p0QJ1p0QM1p0R61p0RA1p0RN1p0S41p0S91p0SC1p0SG1p0SH1p0SN1p0T41p0T=1p0TA1p0U21pT0U;1pSJUG1pFU=1p2U>1pT2U@1pSLUF1pDUI1pUBUM1pU@UN1pU>UO1pU<V01pT<V11pT:V21pTLV31pTJV41pTHV51pTFV61pTDV71pTBV81pT@V91pT>V:1pSHV;1pSFV<1pSDV=1pSBV>1pS@V?1pS>V@1pS<VA1pS:VB1pT8VC1pT6VD1pU:VE1pU8VF1pU6VG1pUDVH1pSNVI1pTNVJ1pT4VK1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 32%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 33%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 34%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 35%nat 0%nat).
Variable errv : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 36%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rmunmap_spec) 37%nat 0%nat).
Lemma rmunmap_spec : ltac:(sec_stmt2 constr:(SEC_T_rmunmap_spec) 38%nat 0%nat).
Proof.
intros ST ERR MI VML CEILJ -> -> A0 AL L0 LO SEP1 SEP2 SEP3 TP.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (mmap_len_ge L) as ML.
pose proof alloc_ceiling_lo as CEILJ0. unfold RVMLOCK in VML.
unfold rmunmap_entry. apply impl_enode.
carve_frame 32%nat ST.
do 6 step.
step.
call_sp rvmwait_spec; [exact ST | unfold RVMLOCK; exact VML | exact MI | lia | lia | ]. unfold RVMLOCK in *.
match goal with H : stk rsegs _ _ _ |- _ => rename H into ST end. match goal with H : rw_cells rsegs _ 0xe8854 _ |- _ => rename H into VML end. match goal with H : mem_inv rsegs _ |- _ => first [ rename H into MI | idtac ] end.
do 3 step.
step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as D. clear Hdec.
destruct ans as [e|[|]].
- destruct D as [-> He]. unfold efferr, eff0. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmunmap_post, munmap_ret, rg_errno. finish; lia.
- rewrite D. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
- rewrite D. unfold eff0. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
Qed.
End SE.
Lemma rmprotect_args : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_mm_syscalls "QI'8'6&QAr2+TP0%3221z%63721&Q?r4%2241&Q=r6r5%3221%421;&QB+2+R0%3221%<251'5'R@yR0%211&R?&Q>+_ooooooooolP0&RAr7%5271%3281%6251%82:1%Q13:14&QC%I27H+SoO%K221%>2@1%<2A1%?21>%A2C1%?2D1%@2E;%:221%E2G1%F2HQ3%Q?3H21%L2?1p0N1p0Q91p0Q:1p0Q>1p0Q?1pFQG1p2QH1").
Proof.
intros A L HA HL A0 L0 B. rewrite (Z.land_comm 18446744073709547520).
rewrite (unsigned_lit A), (unsigned_lit (A + L + 4095)) by lia. rewrite !land_m4096 by lia.
assert (E1 : (A - A mod 4096 = A)%Z) by lia.
assert (E2 : ((A + L + 4095) - (A + L + 4095) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed.
Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
/\ rw_cells rsegs m' RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
/\ match a with
| RgErr e => (1 <= e <= 4095)%Z
| RgDone true => rw_cells rsegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
| RgDone false => True
end.
Section SE.
Local Abbreviation SEC_T_rmprotect_spec := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_mm_syscalls "WG'R@yR0%211&;y5%2213yQ0%711'4y8%:11%311p0:1'8&G&Q4r6r1&RArQ6%22C1%746541&Q3r7&Q=rQ5%82I1-U4%4221(2'@(>r3%211(3%115%73631%?4F>91r8&Q9(?&R?+TP0%22Q:1%411%@3?1:%H4O871&Mr9%22Q21'6rQ2%;2QC4%33QC21&QAr<%221>z%83Q=21&Q@r>%2241&Q?r@r?%Q9221%Q:21H&QB+2+R0%3221%9251'5%;2@9%?2:4%3221&QCrQC%QL2R=1+Q0%4221%C2E1'7rQB%R22RC1%QM21QJ+4%QO221rQD%R72RH1%>21;%M241%N237%;221rDrC%R8221%Q321Q2rQE%RA2S21%Q6216%C241rE%R?219%R@2?R=%Q;221%RB22D%Q=215%J231rF%RF218+RPP0%QB221+mTP0%QD215%Q1231%QF23ErQG%S42SE1%RO21RL%S021Q2%QK21RB+8%S32RD1%QN215%Q;241+U4rQH%S>2SO1%R3231&K'Q1&Q0%11SF'H'D%211&I(NrJrIrH%43321&A%1254%84>:31&J&Q6rQLrQKrQJrQIrQ;rQ:rQ9rQ8rQ7rQ4rQ3rMrLrGrK%@G?>=<R1R;;:987T@T:65S@43HG2QF1%B2M1&L&FrQFrQArQ@rQ?rQ>rQ=rQ<rQ1rQ0rOrN%<ONMLKQCQM;R@RJS5RO:98765JIHGFTOTIEDSO4321&Q:%T;2UC1(1%11UD&Q<%11U9%D77J5I3G1%QH7QGU;QEQBQ9F1p0QJ1p0QO1p0R91p0R;1p0RC1p0RK1p0S41p0SA1p0SH1p0SM1p0T81p0T91p0T=1p0T>1p0TD1p0TE1p0TF1p0TK1p0TO1p0U91p0UJ1pT0V31pSJV?1pJV51pFV61p2V71pT2V91pSLV?1pDVB1pUBVF1pU@VG1pU>VH1pU<VI1pT<VJ1pT:VK1pTLVL1pTJVM1pTHVN1pTFVO1pTDW01pTBW11pT@W21pT>W31pSHW41pSFW51pSDW61pSBW71pS@W81pS>W91pS<W:1pS:W;1pT8W<1pT6W=1pU:W>1pU8W?1pU6W@1pUDWA1pSNWB1pTNWC1pT4WD1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 32%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 33%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 34%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 35%nat 0%nat).
Variable P : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 36%nat 0%nat).
Variable errv : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 37%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rmprotect_spec) 38%nat 0%nat).
Lemma rmprotect_spec : ltac:(sec_stmt2 constr:(SEC_T_rmprotect_spec) 39%nat 0%nat).
Proof.
intros ST ERR PG MI -> -> -> AA LA A0 L0 AL PR LO SEP1 SEP2 SEP3 SEP4 SLO SEP5 TP.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold rmprotect_entry, RPAGE_SIZE in *. apply impl_enode.
carve_frame 16%nat ST.
step. step. step. step.
do 7 step.
destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) AL) as [E1 E2]. rewrite E2, E1.
step. step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as D. clear Hdec.
rewrite (mmap_len_aligned L LA) in D.
destruct ans as [e|[|]].
- destruct D as [-> He]. unfold efferr, eff0. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmprotect_post, munmap_ret, rg_errno. finish; lia.
- rewrite D.
assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr rsegs x = false) by (intros x Hx; apply ref_ro_addr_false; lia).
sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmprotect_post, munmap_ret, rg_errno. finish.
- rewrite D. unfold eff0. sys_nret.
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed.
End SE.
Lemma land_ones64 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_mm_syscalls "E'8'5&Q?zr1%3221&Q@&QB+2+R0%3221%5271%;271'6&Q>r2+_oooooooooooO%3221%53B13p071pUFD1").
Proof. intros y. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
: machine_state -> Prop :=
fun ms' =>
match a with
| MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
/\ (1 <= e <= 4095)%Z
| MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
/\ wmono rsegs m m2 /\ mem_inv rsegs m2
/\ stk rsegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
/\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
/\ mmap_addr_ok len avoid x = true
end.
Lemma rmmap_anon_spec : forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
let prot := (if isnone then 0 else 3)%Z in
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
(0 < len <= 2^62)%Z ->
(lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl rsegs (at_node rsegs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none len avoid else dec_mmap len avoid))
(epost (rmmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
pose proof (wmono_refl rsegs m) as WM.
pose_ceil.
assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
unfold rmmap_entry. apply impl_enode.
carve_frame 64%nat ST.
do 8 step.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
step. step.
step. step. step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec.
assert (D : match ans with
| MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| MmOk a => rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] []
else mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])
/\ mmap_addr_ok len avoid a = true
end).
{ destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ Hdec) as D | pose proof (dec_mmap_Some _ _ _ _ Hdec) as D];
destruct ans; exact D. }
clear Hdec. destruct ans as [e|x].
- clear MU1. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
step. step. step.
rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
if_cases K; zify_cond K.
+
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
do 10 step. release_frame FR ST (bv_unsigned sp).
unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
finish; lia.
+
rewrite ?unsigned_lit in K by lia.
step. step. step. step.
replace (Z_to_bv 64 18446744073709551604) with (errno_ret 12) by (apply bv_eq; reflexivity).
step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
do 10 step. release_frame FR ST (bv_unsigned sp).
unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia).
finish; lia.
- clear MU. destruct D as [-> Hok]. pose proof (mmap_addr_ok_true _ _ _ Hok) as ((XA & X0 & XC) & XAV).
pose_ceil. pose proof (mmap_len_ge len) as ML.
lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
destruct isnone; sys_nret_raw.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
set (m' := mm);
assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
end.
1: pose proof (rw_cells_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
pose proof (stk_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
2: pose proof (rw_cells_zeros_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
pose proof (stk_zeros rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
all: fold m' in FR', ST'; clear FR; rename ST into ST0.
all: step; step; step.
all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].
all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.
all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
all: apply evt_done; unfold rmmap_anon_post, mmap_raw; cbv iota.
all: do 14 eexists; eexists; split; [subst m'; reflexivity|].
all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; split; [exact ERR| exact Hok].
Qed.
Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
R a r u /\
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
/\ (u = false -> wmono rsegs m m')
/\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
Lemma rmmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(A L P : Z) (errv : word) (lo : Z),
(forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = fixed_shape A L r u) ->
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
rw_cells rsegs m RVMLOCK [C4 (Z_to_bv 64 0)] -> (alloc_ceiling <= lo)%Z ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 50 ->
a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
(0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z -> (0 <= P < 4)%Z ->
(lo <= bv_unsigned sp - 96)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
(A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl rsegs (at_node rsegs) (enode (NMmap A L P 50) dec)
(epost (rmmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros DEC ST ERR MI VML CEILJ -> -> -> -> -> -> A0 LEN AL PR LO SEP1 SEP2 SEP3 TP.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (mmap_len_ge L) as ML.
pose proof alloc_ceiling_lo as CEILJ0. unfold RVMLOCK in VML.
unfold rmmap_entry. apply impl_enode.
carve_frame 64%nat ST.
do 8 step.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 P).
do 6 step.
step.
call_sp rvmwait_spec; [exact ST | unfold RVMLOCK; exact VML | exact MI | lia | lia | ]. unfold RVMLOCK in *.
match goal with H : stk rsegs _ _ _ |- _ => rename H into ST end. match goal with H : rw_cells rsegs _ 0xe8854 _ |- _ => rename H into VML end. match goal with H : mem_inv rsegs _ |- _ => first [ rename H into MI | idtac ] end.
do 6 step. step.
subst z0 zm1 z50 zA zL zP.
step. step. step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & ->). clear Hdec.
pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
destruct u; unfold fixed_shape; cbv iota.
all: sys_nret.
all: step; step; step.
all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
all: step; call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia |]; match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
all: do 10 step; release_frame FR ST (bv_unsigned sp).
all: unfold rmmap_fixed_post; apply evt_done; exists r; eexists; do 15 eexists; split; [exact HR|]; split; [reflexivity|].
all: split; [ eapply munch_weaken; [|exact MU]; intros y; cbn; lia |].
all: split; [ first [intros; discriminate | intros _; assumption] |].
all: split; [lazymatch goal with H : mem_inv rsegs ?mm |- mem_inv rsegs ?mm => exact H end|].
all: split; [lazymatch goal with H : stk rsegs ?mm ?a ?b |- stk rsegs ?mm _ _ => exact H end|].
all: lazymatch goal with H : rw_cells rsegs ?mm ?a ?c |- rw_cells rsegs ?mm _ _ => exact H end.
Qed.
End CEIL_WRAP_1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_am_A F_am_K F_am_K2 F_am_C F_am_D F_am_E F_am_F F_am_G F_am_H F_am_P.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_alloc_meta () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_alloc_meta.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."], [["0A"; "0C"; "0C1"; "0C2"; "0C3"; "1bool"; "1length"; "1list"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "3N"; "3Z"]; ["0L"; "0RUNp"; "4magree"; "5am_took"; "6carve_st"; "7asegs"; "8ivs_covered"; "9fresh_addr"; "9mem"; "9pres_except"; ":cell"; ":cells_size"; ";ivl"; ";munch"; "<bytes_at"; "<wr_at"]; ["=alloc_ceiling"; ">rw_cells"; "?aptr"; "?brkstate"; "?c_brk"; "?conc"; "?ctx"; "?live_ranges"; "?mstate"; "?ranges_free"; "?region"; "?s_regions"; "?s_reserved"; "@add"; "@le"; "@lt"]; ["@of_nat"; "@pow"; "@sub"; "0W"; "0X"; "0a"; "0bs"; "0c"; "0cs"; "0m"; "0m'"; "0m1"; "0m2"; "0m3"; "0n"; "0p"]; ["0q"; "0st"; "0stA"; "0stB"; "0stY"; "Abv"; "Abv_unsigned"; "BN_countable"; "Cgmap"; "Deq_dec"; "0tp"; "0x"; "0y"]]).
Module A2 := MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).
Lemma magree_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta ":'?!p021&H&Br2r1%33211pSD51p471"). Proof. intros C m. intros a _ _; reflexivity. Qed.
Lemma magree_trans : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "Q0'?!p021&H&Br6r3r2%43321r9r1%211r8%116p031pS<?1%719p061pS<B1r7r5%A3921p041p081p0@1p0A1pSLG1pSJH1pSHI1p:K1p8L1p6M1").
Proof. intros C1 C2 C3 m1 m2 m3. intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.
Lemma magree_of_pres : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "@'?!p021&H&Ir3r2r1%43321&Br4%23165p041pSF:1pSD;1p4=1").
Proof. intros C m m'. intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
Lemma pres_of_magree : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "@'?!p021&H&Br3r2r1%43321&Ir4%23165p041pSF:1pSD;1p4=1").
Proof. intros C m m'. intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (wview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.
Lemma magree_of_munch : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "Q0'?!p021'7&L%211'R5yR0%211'8y8%511%311p051&Mr3r2r1%43321&Fr5r4%3221&Br6%2314:p041p091pSF?1pSD@1pS8I1p4M1").
Proof. intros C W m m'.
intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.
Lemma rw_cells_magree : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "QD'?!p021'R5yR0%211'8y8%511%311p051&H'7'J%211&Q1&Er4r2r1%544321&Br6r5%33217';&Q>%1248&Q?&Q=&Q@&K%11?%311%52;1%72@1%;291&=r9%11E%311p051pS<Q:1%L4KEDJp021p0E1p0J1pSBQ11p2Q@1pSFQ61pSDQ81p4QA1").
Proof. intros C m m' A cs.
intros H AG HC. pose proof (rw_cells_bound _ _ _ _ H). eapply A2.rw_cells_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Lemma bytes_at_magree : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "QC'?!p021'R5yR0%211'8y8%511%311p051&H'7%115&N&Er4r2r1%544321&Br6r5%33217';&Q>%1248&Q?&Q=&Q@&6%12G?%311%52;1%72@1%;291&=r9%11E%311p051pS<Q91%L4KEDJp021p0E1p0J1pS>Q11p2Q?1pSFQ51pSDQ71p4Q@1").
Proof. intros C m m' A bs.
intros H AG HC. pose proof (bytes_at_bound _ _ _ _ H). eapply A2.bytes_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Lemma wr_at_magree : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "QI'?!p021'R5yR0%211'8y8%511%311p051&H&O&Er4r2r1%544321&Br6r5%33217';&Q>%1248&Q?&Q=%127=%32<1%7251&=r9%11A%311p051pS<Q31z%>21A%<2CB&QA+2+R0%3221%D251r8r7%Q24Q121Kp041p0;1p0>1p0M1p0Q21pSNQD1p2QE1pSFQ;1pSDQ=1p4QF1").
Proof. intros C m m' A n. intros H AG HC H0 H1. eapply A2.wr_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha]. Qed.
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Lemma ETP : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta ">'<'?&Q=&R6yR0vR:%3221-U4%6221&QB+SYa0+U4%3221%=3<51").
Proof. rewrite TP, unsigned_lit by lia. reflexivity. Qed.
Lemma brk_am_took : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "D'Q8&Q2'?'<'Q3&Q4&Q6&Cr3r2r1%43321%611%811%816%:11%=3<31pS@?1pT2A1pS:C1"). Proof. intros X q c. reflexivity. Qed.
Lemma am_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> Malloc.M RR) (bl : Malloc.M RR) :
am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
= kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. reflexivity. Qed.
Lemma conc_am_took : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "B'Q8&Q2'?'<&Q5&Cr4r3r2%43321r1%7221%8262%:3;21pTJ=1pS@=1pT2?1pS:A1"). Proof. intros X q c y. reflexivity. Qed.
Lemma brk_carve : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "A'Q8&Q2'<'Q3&Q4&Q6&Dr2r1%3221%511%711%715%911%<3;31pT0>1pT:@1").
Proof. intros stY p.
unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
Lemma conc_carve : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "@'Q8&Q2'<'?&Q5&Dr3r2%3221r1%6221%7252%:3921pTJ<1pT0=1pT:?1").
Proof. intros stY p y. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.
Lemma live_ranges_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "Q1'Q8'<'R8'>&R9&R7'Q:%544321&Q;r1%211r2%411%<3631'7'9'?%2211%411&Q<%119r3%311%F3531&Q7%114r4%311%K3:31p061p0A1pT8O1pT6Q01").
Proof. intros stA stB. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.
Lemma fresh_of_ranges_free : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_alloc_meta "QI'Q8'?'<'R8'>&R9&R7'Q:%544321&Q;r4%211vR1%411%<3631'7'9%12@@%311&Q<r5%211%31:%E3521'5&Q9&Q7r6%211%4319C(:%M3721&Q>&Q=%127>&Q0vA%211%6241';r7%921E&Q?%:23@%22H1%6241&G%13;Q3Dp031p0;1p0C1p0L1p0Q61pS<QD1pQ2QE1pTHQF1pT:QH1").
Proof. intros stY x L a.
intros E1 E2 RF XC Ha. split; [lia|]. rewrite (live_ranges_same st stY E1 E2) in RF.
eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.
End ASM.
End CEIL_WRAP_1.

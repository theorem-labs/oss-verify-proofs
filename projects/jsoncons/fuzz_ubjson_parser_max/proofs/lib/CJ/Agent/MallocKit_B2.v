(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_enframe MallocTree MallocKit_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocKit_B2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0C"; "1bool"; "1length"; "1list"; "1option"; "1true"; "2and"; "2eq"; "2not"; "3Z"; "4wview"; "5asegs"; "6agree_on"; "7mem"; "7pans_mem"]; ["7pres_except"; "8u64arr"; "8u8arr"; "9cell"; "9cells_size"; ":ivl"; ":munch"; ":outside"; ":stk"; ";wr_at"; "<rw_cells"; "=aptr"; "=peek_answer_ok"; ">add"; ">le"; ">lt"]; [">mul"; ">of_nat"; ">pow"; ">sub"; "0W"; "0a"; "0bs"; "0c"; "0cs"; "0h"; "0hi"; "0lo"; "0m"; "0m'"; "0n"; "0o"]; ["0p"; "?bv"; "0ws"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma implT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
(c = true -> implT o k s Q ms) -> implT o (guard t c k bail) s Q ms.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| apply implT_undef]. Qed.
Lemma peek_ok_pans : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "C&>&K':'8'2&L&?r4r3r2r1%544321%711(6%;3:21pRD=1pR@>1pS2@1pS0B1").
Proof. intros o p c h.
pose proof (pans_mem_range o p c h). unfold peek_answer_ok.
apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.
Lemma implT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
implT o (k (rdv pans_mem o st q)) s Q ms -> implT o (rd8 st q k) s Q ms.
Proof.
intros H. unfold rd8. unfold rdv in H.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
apply implT_peek. rewrite peek_ok_pans. exact H.
Qed.
Lemma implT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
implT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> implT o (rd16 st q k) s Q ms.
Proof. intros H. unfold rd16. apply implT_rd8, implT_rd8. exact H. Qed.
Lemma implT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
implT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
+ 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
implT o (rd32 st q k) s Q ms.
Proof. intros H. unfold rd32. apply implT_rd8, implT_rd8, implT_rd8, implT_rd8. exact H. Qed.
Lemma implT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
(c = true -> implT o t1 s Q ms) -> (c = false -> implT o t2 s Q ms) -> implT o (if c then t1 else t2) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.
Lemma wview_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "I'QAyR0%211'5y8%511%311pS851'8r2r1%211r3%113%63831&;&<%23158r4%4331:%<3>31p071pR<D1pRL@1pRJA1").
Proof. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.
Lemma wr_at_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "J'QAyR0%211'5y8%511%311p051':&I&<r4r2r1%544321&=r5r3%342716%:49382p021p071pRN>1p2?1pRLA1pRJB1").
Proof.
intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite (wview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.
Lemma rw_cells_agree' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "Q1'QAyR0%211'5y8%511%311p051':'4'C%211&J&<r4r2r1%544321&=r5r3&Q1&D%118%311%746;51%>4=7<6p021p0;1pRBB1p2F1pRLH1pRJI1").
Proof.
intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply wr_at_agree; eauto.
Qed.
Lemma u64arr_agree' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "Q3'QAyR0%211'5y8%511%311p051':'4%118&A&<r4r2r1%544321&=r5r3&Q0+8&Q1&3%12F:%311%6251%:49>81%A4@:?9p021p0>1pS6E1p2H1pRLJ1pRJK1").
Proof.
intros m m' A ws [HB HW] AG. split.
- eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
- eapply wr_at_agree; [exact HW|]. exact AG.
Qed.
Lemma u8arr_agree' : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "Q0'QAyR0%211'5y8%511%311p051':'4%115&B&<r4r2r1%544321&=r5r3&Q1&3%12A8%311%746;51%>4=7<6p021p0;1pR>B1p2E1pRLG1pRJH1").
Proof. intros m m' A bs [HB HW] AG. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto]. Qed.
Lemma stk_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "L'QAyR0%211'5y8%511%311p051':&H&<r4r2r1%544321&=r5r3&Q3%1272%544931%<4;5:4p021p091pRF@1pRHA1pRLC1pRJD1").
Proof.
intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|].
intros a Ha. rewrite (wview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. exact Ha.
Qed.
Definition grp_region_addr (st : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).
Lemma pres_except_of_munch_nw : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "QA':!pS821'4&E%211'QAyR0%211'5y8%511%311p051&Fr3r2r1%43321'7&Nz%2215&O&Q2+2+R0%3221%52;1%:271&9r7%11@%311&G%124Dp031p081pR<Q61&@r6r4%3321Kp051p0J1pRLQ01pRJQ11pR:Q:1p4Q>1").
Proof.
intros C W m m' MU HW a Ha Hc.
assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [exact E|]. rewrite (wview_ext m m' (wa a) E). tauto.
Qed.
Lemma pres_except_agree : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "Q?':!p021&>&@r5r4r3%43321&Nz%2214&M%1276&Q2+2+R0%3221%9251'7r6r1%=221&O%<24C%2241%7241&9r:r2%211%411p061pR<Q11&=r8r7%3421AQ0p051p0E1p0M1p0Q11pRNQ:1p2Q;1pRLQ91pRJQ:1p4Q<1").
Proof. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; exact Ha]. Qed.
Lemma u64arr_pres : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "QB':!p021&>'4'QAyR0%211%411&@r5r4r3%43321&A&<r2%342751'7&Nr1%22;1&O&M&Q0+8&Q1&3%12EA%311%6251%82E1%:2<1%?2<1&9r9%11D%311p051pR<Q71r6%K4J1ONp031p0J1p0O1pS6Q51p2Q>1pRLQ<1pRJQ=1p4Q?1").
Proof.
intros C m m' A ws HP H HC. pose proof (u64arr_bound asegs m A ws H).
eapply u64arr_agree'; [exact H|]. eapply pres_except_agree; eauto; lia.
Qed.
Lemma u8arr_pres : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B2 "Q?':!p021&>'4'QAy8%211%411&@r5r4r3%43321&B&<r2%342751'7&Nr1%22;1&O&M&Q1&3%12C?%311%52B1%7291%<291&9r9%11A%311p051pR<Q41r6%H4G1LKp031p0G1p0L1pR>Q21p2Q;1pRLQ91pRJQ:1p4Q<1").
Proof.
intros C m m' A bs HP H HC. pose proof (u8arr_bound asegs m A bs H).
eapply u8arr_agree'; [exact H|]. eapply pres_except_agree; eauto; lia.
Qed.
End CEIL_WRAP_1.

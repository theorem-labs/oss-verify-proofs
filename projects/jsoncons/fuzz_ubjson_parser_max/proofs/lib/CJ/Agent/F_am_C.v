(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_am_A F_am_K.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_am_C () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1option"; "2eq"; "3N"; "3Z"; "4carve_st"; "5NSLOTS"; "5a_check"; "5a_nslots"; "5aadd"; "5aptr"; "5area"; "5c_avail_meta_area_count"; "5c_meta_area_tail"; "5c_secret"]; ["5ctx"; "5mctx"; "5mkArea"; "5mstate"; "5optr"; "5s_areas"; "5set_areas"; "5set_avail_meta_area_count"; "5set_avail_meta_areas"; "5set_meta_area_head"; "5set_meta_area_tail"; "5upd_ctx"; "6sub"; "0ar"; "0c"; "0p"]; ["0st"; "0st1"; "0st2"; "0stC"; "7insert"; "7lookup"; "8N_countable"; "8Z_countable"; "8prod_countable"; "9prod_eq_dec"; ":map_insert"; ";gmap"; ";gmap_lookup"; ";gmap_partial_alter"; "<eq_dec"; "=eq_dec"]; ["0tl"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition pgal (z : Z) : Prop := z mod 4096 = 0.
Lemma carve_st_some : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_C "S:'C&;'<'3&D&>&@r4%211%411(1r2%22;1%:3941'2%11=&Q5'Q;&Q9'4&Q>'5&Q?%544321&Q8&Q6&Q7%36872651%;4K51J&Q<%14M73Lr3&Er5%211%C6Q2Q17541%J2Q2I%Q23F21r6%711%H6Q7Q6<:71(0%11Q8%Q83L31&6r7%2218&K'A&H&:+TP0%2271%Q;2QD1&G&L&=r1%211+1%5221%7214%=291qQN?1%A21C&F&Q4&Q:&Q=%14R4Q>Q:R3%34R5R4Q:1(B&8%11Q8%R02R9M&9%11Q;%63431%Q>1E%=7R>R=QC9Q921%?21G&Jr8%R92RB1%311%Q621Lr9&?%RB1R=%211%QA1RI&7%E3321%K7RLRKR1G71?%M21Q5tR8RO:1tR6S0@1tR4S1Q11%RO3S2QD1p0QH1p0QO1p0RH1pQLS41pS2S61pR0S71pR2S91").
Proof. intros st p tl ar.
intros HT Har Hp. assert (NE : tl <> p) by (intros ->; rewrite Hp in Har; discriminate).
unfold carve_st.
cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
cbn [s_areas upd_ctx set_areas]. rewrite Har. rewrite lookup_insert_ne by exact NE. rewrite Hp. reflexivity.
Qed.
Lemma carve_st_none : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_C "RJ'C&;'3&D&>&@r2%211%411(0%119%93831'2'<%211&Q5'Q;&Q9'4&Q>'5&Q?%544321&Q8&Q6&Q7%36872651%;4J51>&Q<%14L73@&Er3%211%B6Q0D64K1%I1E%Q13E21&6r4%2217&K'A&H(1&:+TP0%2281%42Q=1&G&L&=r1%211+1%5221%7214%>291qQN@1%B21D&I%A2QJF%211%F21;&Jr5%F2QO1%311%K21@&F&Q4&Q:&Q=%14R6QAQ=QJ%34R7QKQ=1r6(B&?%11R5&7%432R41%QA1M%<7R?R3QE8721%>21OtR8RB@1tR6RCF1tR4RDK1%RC3REQ?1p0QC1p0R<1pR0RG1pR2RI1").
Proof. intros st p.
intros HT Hp. unfold carve_st.
cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
cbn [s_areas upd_ctx set_areas]. rewrite Hp. reflexivity.
Qed.
End CEIL_WRAP_1.

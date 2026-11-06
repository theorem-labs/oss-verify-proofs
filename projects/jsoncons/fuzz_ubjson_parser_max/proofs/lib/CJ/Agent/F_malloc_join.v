(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_malloc_join () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1length"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2or"; "3N"; "3Z"; "4write_to_mem"; "5mem"; "6mrel"; "6unk_agree"; "7disjoint_from"; "7ivl"]; ["7munch"; "8wa"; "9RKGroup"; "9aptr"; "9get_shadow"; "9ghdr"; "9mstate"; "9r_base"; "9r_kind"; "9r_len"; "9region"; "9rkind"; "9round_up_pg"; "9s_groups"; "9s_next_rid"; "9s_regions"]; ["9s_reserved"; "9shadow"; ":add"; ":le"; ":of_nat"; ":pow"; "0W"; "0a"; "0bs"; "0m"; "0m'"; "0o"; "0r"; "0rid"; "0st"; "0st'"]; [";lookup"; "<bv"; "=N_countable"; "=Z_countable"; "=prod_countable"; ">prod_eq_dec"; "?gmap"; "?gmap_lookup"; "@eq_dec"; "Aeq_dec"]]).
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma unk_agree_ext : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_join "QB'F&;&=r4r2r1%43321'6'QF'8&QH&QB'J%544321&O%11<r5%311%;3531'Q1&Dr6%221Ar7%421C%B3631pRLA1&C&QE'9&QI%34FE21&QD&QC%26IHG541'E%L49521&M%11A%21@%Q13421%Q73BDIp021p0A1p0J1p0Q71pRDQ=1pRHQ>1pS0Q@1pRNQA1").
Proof. intros st st' o m.
intros UA ER ES EG rid r off h Hr Hk Ho Hc NG. rewrite ER in Hr. rewrite ES in Hc.
apply (UA rid r off h Hr Hk Ho Hc). intros (b & gh & Hb & Hf & Hx). apply NG. exists b, gh. rewrite EG. auto.
Qed.
Lemma unk_agree_munch : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_join "RL'F&;'QAyR0%211'3y8%511%311p051'2&?%211&=r5r4r3%43321&@r2%23154'8'J'6%C12&Q@'QF&QH&QB%348217&QG%14:439&Or9%211%:6>=64@1(0r1%22@1%@3?41'K&H%11G(B%E3421&>r7&G%11Q0&L&I%11Q3%311%83751p0:1p0@1pRJQ21pRLQ41r:%K11%Q36Q7Q6OMQ91%Q63Q51G'5&Q3z%B1Q>%3221&Q2%B1QA%D11%3251&Q5+2+R0%3221%<251%>2:1p0@1pRJQH1pRLQJ1r8r6%R53QA21p041p0K1p0R11p0R51pR>R;1pRFR?1pRDRH1pRHRI1pRNRK1").
Proof. intros st o m m' W.
intros UA MU HD HB rid r off h Hr Hk Ho Hc NG.
rewrite <- (UA rid r off h Hr Hk Ho Hc NG). apply MU.
destruct (HB rid r Hr) as [B0 B1]. rewrite wa_unsigned by lia.
eapply disjoint_outside; [apply (HD rid r Hr Hk)| lia].
Qed.
Lemma unk_agree_write : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_join "S8'F&;'9'2'QAy8%211%411&=r5r4r3%43321'8'J'6'3%113&Q@'QF&QH&QB%349218&QG%14;43:r2&Or8%211%;6@?7541(0r1%22B1%B3@41'K&H%11;(B%G3421'7&Q3&Q2r7&Q4&1r6%22Q81%411%7261&G%11Q7%;231&L&I%11Q;%311%?261%A21?%C271p0E1p0K1pRJQ?1pRLQA1r9%Q611%Q?6QDQCQ;Q9Q81%QC3QA1Q2'5z%D1Q<%N221%B1Q>%D11%Q0241&Q5+2+R0%3221%Q6251%<291p0>1pRJR31pRLR51%Q;2?R:%Q82R>R;%Q:11%Q=2Q91%Q?21:r:&:&A%11QA%33R11Q?%RE35N1p071p0<1p0>1p0Q31p0RF1pRBRL1pR@S21pRDS41pRHS51pRNS71").
Proof. intros st o m a bs.
intros UA HD HB A0 A1 rid r off h Hr Hk Ho Hc NG.
rewrite <- (UA rid r off h Hr Hk Ho Hc NG). destruct (HB rid r Hr) as [B0 B1].
rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (HD rid r Hr Hk);
destruct (Z.leb_spec0 a (r_base r + off)); destruct (Z.ltb_spec0 (r_base r + off) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity; exfalso; lia.
Qed.
Lemma mrel_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_join "Q5'F'6'QF'8&QH&QB'J%544321&Or1%211r2%411%<3631&N%114r3%311%A3?31'2'4'9%2211%411&Q0%119r4%311%K3531'<r5%2215p041p0?1p0E1pS0Q31pRNQ41").
Proof. intros st st'.
intros ER EN ES. split; [| rewrite EN; lia | exact ES].
intros rid r H. exists r. rewrite ER. repeat split; auto. lia.
Qed.
End CEIL_WRAP_1.

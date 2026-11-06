(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W12 ASlot_W13 ASlot_W14 ASlot_W18 ASlot_I ASlot_M0 ASlot_M2 ASlot_M3 ASlot_M4P ASlot_M4 ASlot_M5P.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_M5D () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_M5D.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1app"; "1list"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3N"; "3Z"; "0N"; "4ncls"; "4nreq"; "5meta_slot"; "6slot_ok"; "7ivl"]; ["7outside"; "8UNIT"; "8aptr"; "8area"; "8get_meta_rec"; "8get_stride"; "8mstate"; "8region"; "8s_areas"; "8size_class"; "0SC"; "9add"; "9le"; "9lt"; "9mul"; "9pow"]; ["0W1"; "0W2"; "0a"; "0b"; "0c"; "0cnt1"; "0g"; "0idx"; "0j"; "0n"; "0r"; "0s"; "0sc"; "0st"; "0stA"; "0stB"]; [":is_Some"; ":lookup"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "<N_countable"; "<Z_countable"; "<prod_countable"; "=prod_eq_dec"; ">gmap"; ">gmap_lookup"; "?eq_dec"; "@eq_dec"; "0tp"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma slot_ok_N : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5D "Q6'F&B'G'9'>r7r6r5r4r3r2%76654321'3&E&Dr8%221;%411&K+4%22:1%93B41&Lz%221?r:r9%G621<FECp041p081p0C1pFL1pRDM1pR@N1pRFQ01pR8Q21pR>Q31pRLQ51").
Proof. intros st g b r idx n N.
intros SO STR N0. destruct SO. constructor; try assumption; try lia.
intros off O0 OF. apply so_q16; lia.
Qed.
Lemma outside_app' : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5D "D'1&?%211'9&5&@&0r3r2%33821r1%6221'2%8263%9264%3221%<251pR6>1pR4@1pR2A1").
Proof. intros W1 W2 a. induction W1 as [|[lo hi] W1 IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma arith_prog_dec : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5D "Q8'9&Mzr2%3221'7'4'2&Lr1%2281r3%4231%6231'3r6&Kr5&Nr4%221;%5241%83F71%@2:1qRBH1%C2I1&6r7%:2;I%=2>1%@3N31%511p0C1pRBQ11%M291p0O1pRDQ41pRHQ51pR:Q61pR6Q71").
Proof. intros a c s n.
intros Hs. destruct (Z.eq_dec ((a - c) mod s) 0) as [M0|M1].
- pose proof (Z.div_mod (a - c) s ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
destruct (Z_le_dec 0 ((a - c) / s)) as [L0|L0]; [destruct (Z_le_dec ((a - c) / s) n) as [L1|L1]|].
+ left. exists ((a - c) / s). split; [lia|]. lia.
+ right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
+ right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
- right. intros j Hj E. apply M1. subst a. replace (c + s * j - c) with (j * s) by lia. apply Z_mod_mult.
Qed.
Lemma errno_lit5 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5D "D'QCyR0%211'3r1&QB+SYa0%2261%53641'9&K&QDr2%22<1-U4%5221+SY[L%>3821p0:1pSLA1").
Proof. intros tp. intros ->. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma meta_slot_mono : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5D "Q7'F&B&Q@'C&QA'QI&QH'8&QK'9&QL%544321&QG&QE&QF%36872651%;4?51=&QJ%14A73?r1&Hr4%211%C6FD7541%F2E1r2%F6IG:814%I2H1p041pR6L1&=%12:6r3%32<1p031p061pR>Q31pS0Q51pRNQ61").
Proof. intros stA stB g.
intros HA (ar & arr & kk & Ha & Hk & E). destruct (HA ar ltac:(rewrite Ha; eexists; reflexivity)) as [arr' Ha'].
exists ar, arr', kk. auto.
Qed.
Definition nreq (sc cnt1 : Z) : Z := UNIT + cnt1 * (UNIT * size_class sc) - IB.
Definition ncls (sc cnt1 : Z) : Z := size_to_class (nreq sc cnt1).
Lemma nest_class : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5D "R8'9'2&Lzr1%3221&M+Q@%2241%8241+1%9217+Q0%;291%=231&K&N&Ir4%211&A%5221r2%7221%9214+RP0%H221'3&<r5r3%3221%?13+@%B221%C215+<%F221%;3Q671&;%12;:%Q72Q61+J%Q9231%Q;231%M2<=%N21@%Q021>%O18%Q12M1%Q@231%Q=2F;%QB2QAE&O+2%221Q;%QB2I1%QH251+4%Q<2L1%Q<2K<%QK221%QM251%QN2<1%QO2>1%R02E1%R12L1p0Q91p0QF1pR<R51pQFQM1pRJR71").
Proof. intros sc SC cnt1.
intros C1 SM. pose proof (size_class_range sc SC) as SZR.
assert (E : nreq sc cnt1 = size_class sc * 16 * cnt1 + 12) by (unfold nreq, UNIT, IB; lia).
assert (QR : 1 <= size_class sc * cnt1 <= 127) by (unfold UNIT in SM; nia).
pose proof (stc_q_eq (size_class sc) cnt1 SZR C1 ltac:(unfold UNIT in SM; lia)) as EJ.
assert (EJ' : ncls sc cnt1 = stc_q (size_class sc * cnt1)) by (unfold ncls; rewrite E; exact EJ).
destruct (nest_class_props (size_class sc * cnt1) QR) as [J1 J2]. rewrite <- EJ' in J1, J2.
split; [exact E|]. split; [exact J1|]. split; [unfold UNIT; nia|].
split.
{ destruct (Z_lt_le_dec sc (ncls sc cnt1)) as [L|GE]; [exact L|]. exfalso.
destruct (Z.eq_dec (ncls sc cnt1) sc) as [EQ|NE]; [rewrite EQ in J2; nia|].
pose proof (size_class_mono (ncls sc cnt1) sc ltac:(lia) ltac:(lia)). nia. }
split; [lia|]. nia.
Qed.
End CEIL_WRAP_1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel PmModelFacts PmSpecs PmParKit.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmTxtKit2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTxtKit2.PMTK2.G."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1list"; "1option"; "2and"; "3Z"; "4Segment"; "0M"; "0M'"; "5agree_on"; "6defined"; "6u32_at"; "6u8_at"; "7CHUNK"; "7p_b"; "7p_k"; "7p_src"]; ["7parser_at"; "7pst"; "7sr_qc"; "7vstr"; "7vstr_at"; "8dkr"; "9T3"; "9T4"; ":with_tb"; ";add"; ";le"; ";lt"; ";modulo"; ";mul"; ";pow"; "0a"]; ["0ois"; "0op"; "0s"; "0segs"; "<bv"; "0tb"; "0tg"; "0w"]]).
Module PMTK2.
Section G.
Variable segs : list Segment.
Variable A : pm_addrs.
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').
Definition with_tb (s : PM.pst) (tb : PM.vstr) (tg : Z) : PM.pst :=
PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) tb tg (PM.p_b s) (PM.p_k s) (PM.p_stk s).
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmTxtKit2 "RK'4'A'C&@vQ3v0&F&Gv6r5r4r3%9887654321&Jzr6%3221&Ir7+\0%3221&N+2+R0%3221%<251&8v7r8+Z@%44F321r9+[8%@221+H%94K821&E&B&?%11;%311&<%64Q2?21&=%11=%Q02O1r:%411&M+Q0&>%115%O2N1%5241%Q5271%Q:21Or;%>11%812%Q62Q51%<2;1%Q34QEQ241&Dr>%Q?21Q3%35QMQKQ619&9r?%23Q91QAr@&Hr=r<%33:21%R78R6R5R4R3Q?571p071p0;1p0@1p0G1p0Q21p0Q61p0Q>1p0QD1p0QJ1p0R41p0R91pR>RF1pR<RE1pR6RG1pR2RI1pR4RJ1")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable tb : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable tg : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Lemma parser_tb_set : ltac:(sec_stmt2 constr:(SECT) 5%nat 0%nat).
Proof.
intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG AGv DKC Hb Hb' AGV TB' D'.
assert (SUB : forall a n, op <= a -> a + n <= op + 336 -> ag a n) by (intros a n X Y; eapply L5C.agree_on_sub; [exact AG|lia|lia]).
unfold with_tb, PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H0]|].
split; [exact D'|]. split; [exact I|].
split; [apply (L5C.u8_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H8]|].
split; [apply (L5C.u8_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H9]|].
split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H12]|].
split; [apply (L5C.u8_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H20]|].
split; [apply (PMF.nullis_at_agree segs A M M'); [lia|lia| apply SUB; lia| exact NI]|].
split.
{ destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F1]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F2]|].
split; [apply (L5C.defined_agree M M'); [apply SUB; lia|exact F3]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F4]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F5]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F6]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact F7]|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [apply (PMPK.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia|exact H328]|].
split; [exact I|]. split; [exact TB'|].
split; [apply (PMF.vec_at_agree segs M M'); [lia|lia|exact Hb|exact Hb'| exact AGv| exact AGV| exact VEC]|].
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End S.
End G.
Lemma u8_of_u32 : ltac2:(TCodec.tc2 tcn__PmTxtKit2 "Q:'1'5%211'Q4yR0%211'2y8%511%311p051'4'3&Jzr1%3221&K&N+2+Q0%3221%5271%;271&:r5r4r3r2%544321&;r6&L+X0%2271%544:91p071p0>1pR@K1pR0L1p>N1pR8Q71").
Proof. intros segs M a w.
intros Hw H. unfold L5.u32_at, L5.u8_at in *. unfold word_to_le_bytes in H. rewrite L5.unsigned_lit in H by lia.
change (Z_to_le_bytes 4 w) with (Z_to_bv 8 w :: Z_to_le_bytes 3 (Z.shiftr w 8)) in H.
change (rdn segs M (Z_to_bv 64 a) 4) with
(match (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) with
| Some b => match rdn segs M (Z_to_bv 64 a + 1) 3 with Some rest => Some (b :: rest) | None => None end | None => None end) in H.
cbn [rdn]. destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [b0|]; [|discriminate].
destruct (rdn segs M (Z_to_bv 64 a + 1) 3) as [rest|]; [|discriminate]. injection H as Hb _. rewrite Hb. f_equal. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End PMTK2.

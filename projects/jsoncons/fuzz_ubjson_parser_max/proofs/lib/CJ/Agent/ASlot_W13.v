(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3 ASlot_W1 ASlot_W10 ASlot_W12.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W13 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W13.CEIL_WRAP_1.ENF."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_AB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1cons"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2or"; "3N"; "3Z"; "0N"; "4enf0_st"]; ["5mw_ok"; "6b8"; "6meta_word"; "7le1"; "8Known"; "8RKGroup"; "8aptr"; "8cell_read"; "8cellval"; "8enframe_at"; "8get_shadow"; "8ghdr"; "8m_last_idx"; "8m_mem"; "8m_set_maplen"; "8meta"]; ["8mstate"; "8optr"; "8r_kind"; "8r_len"; "8region"; "8rkind"; "8round_up_pg"; "8s_groups"; "8s_regions"; "9add"; "9div"; "9le"; "9lor"; "9lt"; "9modulo"; "9mul"]; ["9sub"; "0a"; "0b"; "0b'"; "0g"; "0gh"; "0idx"; "0mr"; "0off"; "0r"; "0r0"; "0st"; ":lookup"; ";Z_to_bv"; ";bv"; "<N_countable"]; ["<Z_countable"; "<prod_countable"; "=prod_eq_dec"; ">gmap"; ">gmap_lookup"; "?eq_dec"; "@eq_dec"; "0stride"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.
Lemma enf_facts : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W13 "TC'9':&Q1&MvQG%211(0&FvQB%3221%93851'5'Q4%211&QL'<'R3&R5&QO%344217&R4%146439&2'=%2391@&Q8vQK%211%>6=@9741vQI%H2B1%N3B31'Q5&Q2%115(E%Q33421&Q;z&8%13IAQ0%4231&Q>+@%2241%Q<3F17vQF%:291&L%11Q=%=241%QC241&Q=+Q0%2251&Q9%12@=&Q?vR7+1%52;1%4231%7261&Q6&Q3%11Q4%311%N251%O2I:%K2;J%R53Q?1Q0'7%12QIQA'K%QO11&R2&R6%24QNQLQF1&R1&R0%26R1QOQNQI41%R14R:418%QN4R;529r2&Q7%11QK%R86>=5431r1%RB2?1%RH3?31r3%R53R<R41%RK3R=1R4';r4%QH3R@R81+9%Q:221&Q@%Q:2Q9QE%Q=2Q<1+4%4221%R2261%QA24Q>%7214%R521;%>241p0@1p0D1pS<Q51pS8Q71'H&G&J%12RIRK%321>(D%11R@%SF3731%RC2RBQ1%R02R>Q6v>%R4221%R521G%RH21R3&Q:%R62RDQ5%R92M1%321RF+RPP0%R?221p071p0=1pSBS?1%T72@1%T82I1%T92R31%T:2R61%T;2R81%T<2RF1%T=2RJ1%T>2S11%T?2S61%T@2S<1%TA2SB1%TB2T81").
Proof.
destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL' AVr FRr FBr MPL SCr].
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *.
repeat (split; [assumption|]). exact Q16.
Qed.
Definition enf0_st : mstate :=
wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
(wr8 (fst b, snd b + (16 + stride * idx) + -3) idx
(wr16 (fst b, snd b + (16 + stride * idx) + -2) ((snd b + (16 + stride * idx) - (snd b + 16)) / 16) st)).
Lemma enf0_st_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W13 "Q1'9':'Q0&2&F&IvQKvQDvQFv>z%6554321%93:81&?%=3<21&8%13><5(6'<'=vQB%B3321&Q9%83543+@&Q?vR7%221C%6241%7261%=4<;91%N3K?1%Q02B1").
Proof.
pose proof enf_facts as (Hmem & _).
assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
unfold enframe_at. change (get_meta_rec st g) with mr. rewrite Hmem. cbn [default from_option id]. fold stride.
change (negb (0 =? 0)) with false. cbv iota beta. unfold aadd. cbn [fst snd].
unfold set_size. cbn [fst snd].
replace (snd b + (UNIT + stride * idx) + (stride - IB) - (snd b + (UNIT + stride * idx)) - N) with 0 by (unfold UNIT, IB; lia).
cbn [Z.eqb negb Z.leb]. unfold enf0_st, UNIT. split; reflexivity.
Qed.
Lemma meta_word_mod4096 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W13 "C'O&@r1%211':'=&Q>&Br2%211+TP0%5221&Nz%2216%811%<3;51p0>1pSFB1").
Proof. intros r0.
intros (LI & FB & SC & ML). unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen m_set_maplen].
rewrite Z.land_0_l. Z.div_mod_to_equations. lia.
Qed.
Lemma le1_lor_m64 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W13 "Q4'='9&Q;zr1%3221&Q=+Q0%2241%8241':'3'QNy8%211%411&C&QMyR0&Q<r2+_oooooooooon0%3221%6251%811(1&A+V0%9281%311(4%11A%73B31%G3B91p0I1pS4Q31").
Proof. intros a.
intros Ha. unfold le1. cbn [Z_to_le_bytes]. f_equal. unfold b8. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
rewrite <- !(Z.land_ones _ 8) by lia. change (Z.ones 8) with 255.
rewrite <- (Z.land_ones (Z.lor a 18446744073709551552) 64) by lia.
change (Z.ones 64) with 18446744073709551615.
rewrite !Z.land_lor_distr_l. rewrite <- !Z.land_assoc.
change (Z.land 18446744073709551615 255) with 255. change (Z.land 18446744073709551552 255) with 192.
change (Z.land 192 255) with 192. reflexivity.
Qed.
Definition pp : aptr := (fst b, snd b + (16 + stride * idx)).
End ENF.
End CEIL_WRAP_1.

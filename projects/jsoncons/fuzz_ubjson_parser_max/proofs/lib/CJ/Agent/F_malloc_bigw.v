(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_malloc_bigw () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_bigw.CEIL_WRAP_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1cons"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "3N"; "3Z"; "4big_meta"; "4big_ml"]; ["5sxv"; "6asegs"; "7b8"; "7meta_word"; "7unmap_seqs"; "7wz"; "7zeros"; "8bytes_at"; "8le4"; "9Unknown"; "9cell_read"; "9cellval"; "9get_shadow"; "9hdr_havoc"; "9mctx"; "9mstate"]; ["9s_shadow"; "9set_unmap_seq_map"; "9shadow"; "9u32"; "9upd_ctx"; ":add"; ":div"; ":le"; ":lor"; ":lt"; ":modulo"; ":of_nat"; ":pow"; ":shiftl"; ":shiftr"; "0b"]; ["0c"; "0h"; "0k"; "0m"; "0n"; "0o"; "0rid"; "0st"; ";empty"; ";lookup"; "<Z_to_bv"; "<bv"; "<bv_swrap"; "<bv_unsigned"; "=N_countable"; "=Z_countable"]; [">gmap"; ">gmap_empty"; ">gmap_lookup"; "?eq_dec"; "@eq_dec"; "0v"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma unmap_seqs_empty : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_bigw "N'O':'3'QKy8%211%411&D&Q4'N&Q1&QH'R0'=&R4&QO%443213&R1%145435%8231r1%;221qS2=1%?213%A11&FuQ0%211%K3F41pS@M1").
Proof. intros st. reflexivity. Qed.
End CEIL_WRAP_1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require StrFun.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Definition big_ml (n : Z) : Z := Z.land ((n + IB + UNIT + 4095) / 4096) (2^52 - 1).
Definition big_meta (rid : N) (n : Z) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 1 63 (big_ml n).
Definition big_metaA (rid : N) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 0 0 0.
Definition big_st (st : mstate) (g : aptr) (rid : N) (n v : Z) : mstate :=
upd_ctx (set_mmap_counter v)
(put_meta g (big_meta rid n)
(put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st)))).
Lemma big_ml_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_bigw "J'='9&Q7zr1%3221&Q9&Q<+2+Q0%3221%5271%;271':&?r2%211&Q6&Q5+TPC%2251+TP0%5221%:3G71p0<1pS:I1").
Proof. intros n.
intros Hn. unfold big_ml, IB, UNIT. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
replace (n + 4 + 16 + 4095) with (n + 4115) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.
Lemma zeros_bytes_at : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_bigw "QH'QKyR0%211'6y8%511%311p051'='4&Q7zr2%3221&Q5r3&Q;%115%4231&Q<+2+R0%3221%=251'9r1%@2?1&Q9r4%=11%3251%7251&G&Ar7r6%F21H(1&B%11L(5%11Q4%53Q531%;4:971p0=1pS<Q51r5&F%11D%A4@>31p051p0L1p0Q71pS6Q<1pT>Q>1pS8Q@1").
Proof.
intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
rewrite nth_error_repeat by exact Hi.
destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
rewrite Z.add_0_r in HB. exact HB.
Qed.
Lemma cell_read_hdr_havoc_fresh : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_bigw "R3'O'7'<'=%3221':'6'Q2%211&QI'R0&R3&QN%34;216&R2%14=438&2r2%23@?1&Q0r3%211%=6D?9741(0%11A%D3A31&Q:&8%13JI8+@%4221z%K3M21'9&Q7%124?&Q9+<%22B1%6241';'K&J&L&Mr6r7%3221%Q03Q>Q=3%6221&Q5%H3QAQ@6r5%3221%<251(Ir1%211%QE3A41qS4QH1%D2QI1p0F1p0N1p0Q61pS<QM1pS0QM1pS@R21").
Proof.
intros st b o SH B16 Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty.
replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
rewrite lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn. eexists. reflexivity.
Qed.
Lemma big_word_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_bigw "QB'<'='9&Q7zr1%3221&Q9&Q<+2+Q0%3221%5271%;271':'QKyR0%211&QJ&Q8&QM&Q=&Q>&Q5r2+TPC%3221%92;1%82<1+<%8221%=2?1%<2@1%<214%@2B1%?2C1+So0%B221%D2F1&E&C&>r3%221C%411%611%Q03M81p0Q21pS:Q?1pS>QA1").
Proof. intros rid n.
intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
rewrite (unsigned_lit (n + 4115)) by lia. rewrite Z.shiftr_div_pow2 by lia.
rewrite (unsigned_lit ((n + 4115) / 2 ^ 12)) by (Z.div_mod_to_equations; lia). rewrite Z.shiftl_mul_pow2 by lia.
rewrite unsigned_lit by (Z.div_mod_to_equations; lia). change (2 ^ 12) with 4096.
rewrite (StrFun.lor_add _ _ 12); [| lia| lia| change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia].
unfold wz. f_equal. lia.
Qed.
Lemma meta_word_big_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_bigw "L'<'='9&Q7zr1%3221&Q9&Q<+2+Q0%3221%5271%;271&C&>r3r2%3221%511%A2@1+R0%>2=1%@241%F241p0<1pS:I1pS>K1").
Proof. intros rid n.
intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
Z.div_mod_to_equations. lia.
Qed.
Lemma ctr_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_bigw "Q0'=&Q7zr1%3221':'QKyR0%211&QJ&QLyQ0&Q5&QM&E&@r2%211%411%62<1+1%9221%<2;1%>2@1&Q3%=295%211%<11%>11%H3E61p0J1pS2O1").
Proof. intros c.
intros Hc. rewrite addw_word. rewrite wz_unsigned by apply sxv_range. f_equal. apply sxv_congr.
unfold u32. rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma le4_sxv : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_bigw "B'=':'3'QKy8%211%411&H&E&@r1%211%411%611%614%811%?3:31pT<A1").
Proof. intros v.
apply le4_congr. rewrite wz_unsigned by apply sxv_range. rewrite sxv_mod32.
unfold wz. rewrite Z_to_bv_unsigned. change (bv_modulus 64) with (2^64). symmetry. apply MallocRep.mod_mod_pow2. lia.
Qed.
End CEIL_WRAP_2.

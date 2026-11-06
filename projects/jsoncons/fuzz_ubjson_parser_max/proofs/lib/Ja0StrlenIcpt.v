(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Ja0MemIsZero Ja0RegionPoisoned Ja0AsanMemset Ja0AsanMemcpy Ja0Readers.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ja0Memchr Ja0SegStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0StrlenIcpt () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0StrlenIcpt.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0StrlenIcpt.FPX_1.ASL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.muslA.Ja0SegStrlen."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "0K"; "4bytes_le_to_Z"]; ["5store_ok"; "5word_to_le_bytes"; "6bvmap"; "0M"; "0M'"; "0M1"; "0M2"; "7wbytes"; "8msteps"; "9ret_ok"; ":HIGHEND"; ":SB"; ":frame_only"; ":keeps_but"; ":rt_layout_globs"; "<FR"]; ["<M11"; "<M9"; "<c1_post"; "<cR_post"; "<cR_pre"; "<cRqa_post"; "<out_agree"; "<qlR_inv"; "<qlR_post"; "<slots_ok"; ";RIPL"; ";sl_icpt_globs"; "=getr"; "=mkst"; "=rdn"; ">keeps_cs"]; ["?mem_grows"; "@slenH"; "Aloaded_segments"; "Badd"; "Bdiv"; "Ble"; "Blor"; "Blt"; "Bof_nat"; "Bpow"; "Bsub"; "0a"; "0buf"; "0fS"; "0faS"; "0fx"]; ["0i"; "0j"; "0k"; "0kS"; "0lS"; "0laS"; "0mem0"; "0n"; "0p"; "0q"; "0ra"; "0regs"; "0regs'"; "0regs0"; "0ret"; "0rg"]; ["0rom"; "0s"; "0sp"; "CBV"; "CZ_to_bv"; "Cbv"; "Cbv_unsigned"; "0t"; "0u0"; "0u1"; "0v"; "0w0"; "0w1"; "0x"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
#[local] Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac xval := gres; rwH; unfold v_xori; imm_norm; unorm; rewrite lxor_ones64 by lia; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
#[local] Ltac peel0 :=
rewrite rdn_wbytes_out;
[ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia ].
Section SE.
Local Abbreviation SEC_T_tryinit_fast_run := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "T:&By5'REyR0%211%5241'6y8%611%311p061'=':&Q<r5(RC+2(8%33A21%6251&RDr1%22C1%;3C41r6+1%;3I19%>231r3%A3I21&Ir4%211&QE+`PPP0&QJ+@%2261%5241&QG&QI+R0%22J1%42M1'1&@&QBr9%=2H<%M2Q>1u@%645421(7%Q93921'3%11Q?%QB11&Q>r:+QW^^H%Q=3QI1Q;/01QIu1%64A521(0(2%Q>2QKQ9(5%11QL%43QM31%62?1%QK3?81';'9'H&Q=vQOr=+`Ql<%R03R<1QN/01R<r<r;%8576321&G+8%QC2Q71%R32RD1&Au8%221Q0%73:41%QI2Q=QH%R92RJ1%R?3RM9R=%RB2B1%8271%=3641%G5FR=Q81@%I3QE@1+:%RF3S41RD%RI2RA1%RC2S4R>%RL3S421%RL2RDRG%RF2S7QK%RO3S721%RO2RG>%S13S91>%S12RIRD%S33S;1QE&M%S?1S@%Q?11%QB32E1%QC33S21%QD34RK1%631Q9S1%Q>281%Q?2;1%Q@2>1%QA2B1%QB2H1qTJSG1%QE2SH1p0QG1p0R:1p0RE1p0RK1p0S21p0S61p0S=1pU@SJ1pTNT21pU2SM1pQ8SN1pTHT41")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_tryinit_fast_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_tryinit_fast_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_tryinit_fast_run) 2%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_tryinit_fast_run) 3%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_tryinit_fast_run) 4%nat 0%nat).
Lemma tryinit_fast_run : ltac:(sec_stmt2 constr:(SEC_T_tryinit_fast_run) 5%nat 0%nat).
Proof.
intros H2 H1 Hret Ht1 Ht2 Hok HI.
assert (HI' : rdn ASEGS (wbytes (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr regs 8)))
(0x13b9d8 : word) 1%nat = Some [Z_to_bv 8 1]).
{ peel0. peel0. exact HI. }
eexists. split.
- stepiv (ltac:(oF' 0x8078c%Z)) (ltac:(oD' 0x8078c%Z)) (Z_to_bv 64 (t - 16)) ltac:(wval).
stepsd (ltac:(oF' 0x80790%Z)) (ltac:(oD' 0x80790%Z)) (Z_to_bv 64 (t - 8)) ret
ltac:(apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
stepsd (ltac:(oF' 0x80794%Z)) (ltac:(oD' 0x80794%Z)) (Z_to_bv 64 (t - 16)) (getr regs 8)
ltac:(apply (store_ok_mono _ _ M); [apply wbytes_grows|];
apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
stepn (ltac:(oF' 0x80798%Z)) (ltac:(oD' 0x80798%Z)).
stepn (ltac:(oF' 0x8079c%Z)) (ltac:(oD' 0x8079c%Z)).
mlb (ltac:(oF' 0x807a0%Z)) (ltac:(oD' 0x807a0%Z)) (0x13b9d8 : word) HI'.
stepn (ltac:(oF' 0x807a4%Z)) (ltac:(oD' 0x807a4%Z)).
stepfence (ltac:(oF' 0x807a8%Z)) (ltac:(oD' 0x807a8%Z)).
stepb_ft (ltac:(oF' 0x807ac%Z)) (ltac:(oD' 0x807ac%Z)) ltac:(cond).
stepld (ltac:(oF' 0x807b0%Z)) (ltac:(oD' 0x807b0%Z)) ret ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 8)) by (symmetry; wval) end;
peel0; apply rdn_wbytes_hit8; unorm; lia).
stepld (ltac:(oF' 0x807b4%Z)) (ltac:(oD' 0x807b4%Z)) (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 16)) by (symmetry; wval) end;
apply rdn_wbytes_hit8; unorm; lia).
stepiv (ltac:(oF' 0x807b8%Z)) (ltac:(oD' 0x807b8%Z)) (Z_to_bv 64 t) ltac:(wval).
stepret (ltac:(oF' 0x807bc%Z)) (ltac:(oD' 0x807bc%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity. solve_keeps_but.
Qed.
End SE.
Definition sl_icpt_globs (M : word -> option byte) : Prop :=
rdn ASEGS M (0x13b9d8 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M (0x134450 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x125294)) /\
rdn ASEGS M (0x132628 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1cc828)) /\
rdn ASEGS M (0x1cc923 : word) 1%nat = Some [Z_to_bv 8 1].
#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv.
Section ASL.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra : word.
Variables p K n s : Z.
Variable buf : list byte.
Variables kS fS lS faS laS : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis Hn_def : n = (K + 1)%Z.
Hypothesis HfS_def : fS = (SB + p / 8)%Z. Hypothesis HlS_def : lS = (SB + (p + n - 1) / 8)%Z.
Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z. Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.
Hypothesis HK : (0 <= K)%Z /\ (K + 1 <= 2 ^ 40)%Z.
Hypothesis HappS : in_app8 p n.
Hypothesis Hs : (0x1000000 <= s - 2216)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis HshS : (lS + 8 <= s - 2216)%Z.
Hypothesis HSL : slenH mem0 (Z_to_bv 64 p) buf K.
Hypothesis HdjS : (p + Z.of_nat (length buf) <= s - 2216 \/ s <= p)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2216)) 2216%nat = true.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : rt_layout_globs mem0.
Hypothesis HI : sl_icpt_globs mem0.
Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> mem0 x = Some (Z_to_bv 8 0).
Hypothesis HLS : (0 < n)%Z -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS).
Hypothesis HkS : kS = 0%Z \/ ((p + n - 1) mod 8 < kS <= 7)%Z.
Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laS) 8%nat = Some w1.
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
#[local] Ltac hide_dj := try hide HdjS; try hide HkS; try hide HappS.
Lemma Hn : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt ";'9&QEzvR7%3221&QI+2+Q8%3221%8261%:261"). Proof. hide_dj. lia. Qed.
Lemma sp_s : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "9':'REyR0%211vRB&RDvRA%2251%83541"). Proof. hide_dj. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma pS_facts : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "N'9&QEzvR8%3221&QCvR7%2241+8%4221&J%:221&QD%12:5%=2<1%>225%@221&QG%12@<&QJ+1%22>1%:21>%F2:1%G22>%I221p081%K2;1%L2A1%M2I1").
Proof.
hide_dj.
unhide HappS.
unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappS as [[H1 H2]|[H1 H2]];
(repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
Qed.
Lemma pD_facts : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "N'9&QEzvR8%3221&QCvR7%2241+8%4221&J%:221&QD%12:5%=2<1%>225%@221&QG%12@<&QJ+1%22>1%:21>%F2:1%G22>%I221p081%K2;1%L2A1%M2I1").
Proof. hide_dj. exact pS_facts. Qed.
Lemma flS_facts : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "Q3&QGzvR7%3221'9&QE&KvQM%3221vR4%5231%7231&QC+8%2251&QJvRA+RU8%3221%>251+7%62>1vQN%B221%C22A%E221%;2A6vR5%G221%H22D%J221%K261%L2=1%M2F1p0O1").
Proof.
hide_dj.
intros Hn0. pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). repeat split; lia.
Qed.
Definition out_agree (M : word -> option byte) : Prop :=
forall x : word, (bv_unsigned x < s - 2216 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
Lemma out_agree_refl : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "3&Q6vR6%211"). Proof. hide_dj. intros x _. reflexivity. Qed.
Lemma out_agree_w : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "Q5'REyR0%211'6y8%511%311p051'=&Q6r3%211'9&QE+8%2215+RU8%4271%6231&Gr5&RD&QJvRAr4%3221%52I1&Au8%221C%;3:41%F11p0>1p0F1pUFQ01pT6K1pQ8M1").
Proof.
hide_dj.
intros M k v HF Hk x Hx. pose proof (u64_range x).
destruct Hx as [Hx|Hx].
- rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
- rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
Lemma out_agree_rdn : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "Q:'REyR0%211'6y8%511%311p051'4&Q6r3%211&QE&QC&RF%12>5&QHr2%211%6241&QJvRA+RU8%3221%<251':'3%11F%I11&Q>&QBr5r4%44321GvR6%64513I%;3831p0=1p0K1pT6O1pSHQ61pQ8Q21").
Proof. hide_dj. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
Lemma out_agree_globs : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "D'REyR0%211'6y8%511%311p051&Q6r1%211'9&Nr2%211&Q;%113%6231p081pQ8<1").
Proof.
hide_dj.
intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). destruct HI as (I1 & I2 & I3 & I4).
unfold rt_layout_globs, sl_icpt_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
repeat split; assumption.
Qed.
Section SE.
Local Abbreviation SEC_T_out_agree_store_ok := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "Q:'REyR0%211'6y8%511%311p051'='4&Q@vR6r3%3221'9&QE&QHr2%211%4217+RU8%6291%8231':'1&@&QBr5&RD&QJvRAr4%3221%52Q01%94871F(7%=3<21p0?1p0I1pT4N1pT6Q01pQ8Q21")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_out_agree_store_ok) 0%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_out_agree_store_ok) 1%nat 0%nat).
Variable j : ltac:(sec_ty2 constr:(SEC_T_out_agree_store_ok) 2%nat 0%nat).
Lemma out_agree_store_ok : ltac:(sec_stmt2 constr:(SEC_T_out_agree_store_ok) 3%nat 0%nat).
Proof.
hide_dj.
intros HGr Hk.
apply (store_ok_mono _ _ mem0 M _ HGr).
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2216)) _ 2216%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
Qed.
End SE.
Lemma out_agree_slenH : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "E'REyR0%211'6y8%511%311p051&Q6r1%211'QAr2&RDvR8%22>1vQLv>%746321p091pQ8=1").
Proof.
hide_dj.
intros M HF. pose proof pS_facts as (Pp & Ppn & _). unhide HdjS. unfold HIGHEND in *.
destruct HSL as [Hbuf Hwin Hnw HK0 Hz Hnz Hro]. rewrite u_Z2bv in Hnw by lia.
constructor; try assumption.
- rewrite (rdn_ext ASEGS (length buf) M mem0); [exact Hbuf | unorm; lia|].
intros x Hx. rewrite u_Z2bv in Hx by lia. apply HF. lia.
- unorm. lia.
- intros i Hi. rewrite HF by (unorm; lia). apply Hro. exact Hi.
Qed.
#[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
#[local] Ltac fsok := apply out_agree_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].
#[local] Ltac oagree := repeat (apply out_agree_w; [|lia]); apply out_agree_refl.
Definition M9 (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
(Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
(Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
(Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
(Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
(Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
(Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr rg 21)))
(Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr rg 22)).
Definition M11 (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (M9 rg) (Z_to_bv 64 (s - 2152)) (word_to_le_bytes 8 (0x62b34 : word))) (Z_to_bv 64 (s - 2160)) (word_to_le_bytes 8 (Z_to_bv 64 s)).
Lemma M9_out_agree : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "<&By5'REyR0%211%5241&Q6&Q1r1%211%411pU061"). Proof. hide_dj. intros rg. unfold M9. oagree. Qed.
Lemma M9_grows : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "=&By5'REyR0%211%5241&Q@vR6&Q1r1%211%5241pU071"). Proof. hide_dj. intros rg. unfold M9. grows. Qed.
Lemma M11_out_agree : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "<&By5'REyR0%211%5241&Q6&Q0r1%211%411pU061"). Proof. hide_dj. intros rg. unfold M11, M9. oagree. Qed.
Lemma M11_grows : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "=&By5'REyR0%211%5241&Q@vR6&Q0r1%211%5241pU071"). Proof. hide_dj. intros rg. unfold M11, M9. grows. Qed.
Definition slots_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) /\
rdn ASEGS M (Z_to_bv 64 (s - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 21)) /\
rdn ASEGS M (Z_to_bv 64 (s - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 22)).
Definition FR (regs0 : bvmap 5 word) (M : word -> option byte) : Prop := out_agree M /\ mem_grows mem0 M /\ slots_ok regs0 M.
#[local] Ltac peel :=
rewrite rdn_wbytes_out;
[ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
#[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.
Section SE.
Local Abbreviation SEC_T_M11_FR := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "<&By5'REyR0%211%5241&Or1&Q0%112%4231pTL61")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_M11_FR) 0%nat 0%nat).
Lemma M11_FR : ltac:(sec_stmt2 constr:(SEC_T_M11_FR) 1%nat 0%nat).
Proof.
hide_dj. split; [apply M11_out_agree | split; [apply M11_grows|]]. unfold M11, M9. repeat split; slot. Qed.
End SE.
Lemma rdn_slot_ext : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "QE'REyR0%211'6y8%511%311p051'='9&QE&QJvRA+RS0%3221&RFr1%22@1%8241&QG%1238%<231':r5r2%211r4%113%63F31p081pULL1+8%F218%G29D%I221'3%11O%Q211&Q>&QB&RDr3%O2N1%32Q:1u8%746F21%847D32%I3:21p0>1p0C1pT6Q:1pQ>Q<1pQ<Q=1").
Proof.
hide_dj.
intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
Qed.
Lemma slots_ok_ext : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "Q:&By5'REyR0%211%5241'6y8%611%311p061'9&QE&QJvRA+RS0%3221&RFr1%22@1%8241&QG%1238%<231':r3r2%211r4%113%63E31p081pULL1&Q9%1269r5%321;p031p061pQ>M1pQ<N1pTLQ41").
Proof.
hide_dj.
intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8). unfold slots_ok.
rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
Qed.
Lemma FR_region : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "Q0&By5'REyR0%211%5241'6y8%611%311p061&Or3r2%3221&L&QJvRA+RS0%3221%53817&Q@r4%221;r6%>213p031p071p0>1pQ:C1pQ8D1pTLJ1").
Proof.
hide_dj.
intros regs0 M M' (O & G & R) HF HGr. split; [|split].
- intros x Hx. rewrite (HF x) by lia. apply O. exact Hx.
- eapply mem_grows_trans; [exact G | exact HGr].
- apply (slots_ok_ext regs0 M M'); [|exact R]. intros x Hx. apply HF. lia.
Qed.
Lemma rdnWS : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "R0'REyR0%211'6y8%511%311p051&Q6r1%211'9&QGzvR7%3221&QE+R0%2241%8241';'3%11A':%E12&Q>&QBr5&RDvQN%22M1u8%746521(0r2%22=1%=3<41vR5%:2Q51%>4=<18%72BO%B3A21&?%119%L2O1&QI+2%221N%Q4251%Q6251%81Q9%Q32Q61%Q8225%Q:221%Q;251%Q<2>1%Q=2D1qUJQ31%Q62Q41qUHQ51%Q82Q61p0Q:1p0QD1pQ8QH1").
Proof.
hide_dj.
intros M HO Hn64. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
destruct (HWS Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
Qed.
Lemma rdn1S : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "QA'REyR0%211'6y8%511%311p051'=&Q6r2%211&QGzvR7%3221'9&QEvQMr3%3221vR4%:231%7231':'3%11E%H11&Q>&QBr5&RDr4%22Q01u1%746521(0(2%72Q2I(5%11Q3%43Q431%62@1%C3@81p0E1p0N1p0Q31pUNQ71pQ8Q91").
Proof.
hide_dj.
intros M z HO Hn0 Hz. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZS Hn0) by (unorm; lia). reflexivity.
Qed.
Lemma rdnLS : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "Q='REyR0%211'6y8%511%311p051'=&Q6r2%211&QGzvR7%3221':r3vR4%33;21'3%11@%C11&Q>&QBr5&RDr4%22K1u1%746521(0(2vR3%82N1(5%11O%53Q031%72A1%G3A91p0E1p0J1p0O1pUNQ31pQ8Q51").
Proof.
hide_dj.
intros M z HO Hn0 ->. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HLS Hn0). reflexivity.
Qed.
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mlbu0 F D z RD :=
chain_step; [reflexivity
| eapply step_lbu; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
| step_simpl; vnorm].
#[local] Ltac mlbk F D z RD k :=
chain_step; [reflexivity
| eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
| step_simpl; vnorm; rewrite (v_lb_k k ltac:(lia))].
#[local] Ltac mldw F D z R w :=
chain_step; [reflexivity
| eapply step_ld with (bs := w) (v := Z_to_bv 64 (bytes_le_to_Z w)); [exact F | reflexivity | exact D | maddr z; exact R | unorm; reflexivity]
| step_simpl; vnorm].
Definition c1_post (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 2 = Z_to_bv 64 (s - 2144).
Lemma ret_ok_62b2c : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt ":&I(RCyR0+\Zi<(8%43321'RE%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma ret_ok_62b34 : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt ":&I(RCyR0+\ZiD(8%43321'RE%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma ret_ok_62b48 : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt ":&I(RCyR0+\Zj8(8%43321'RE%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_c1_run := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "QO&By5'REyR0%211%5241':&Q<r1(RC+:(8%33;21%6251&RDvR8%22=1%;3=41r2+2%;3C19%>231vRB%A3C21r3+1%A3I1?%D231vR:%G3I21';'9'H&QB&Q=vQOr5+\ZgH%M3Q31K/01Q3vR6vR@%8576321+\Zk0%Q33Q91Q1/01Q9&Q0%11;%>5=Q8317%A3@71&Q2%11Q;&M&Q:%231BQ>%H241%I271qTJQD1%L2QE1p0N1p0Q51p0Q<1pTHQI1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c1_run) 0%nat 0%nat).
Lemma c1_run : ltac:(sec_stmt2 constr:(SEC_T_c1_run) 1%nat 0%nat).
Proof.
hide_dj.
intros H10 H2 H1.
rewrite sp_s in H2.
pose proof pS_facts as (PSp & PSn & _). unfold HIGHEND in *.
pose proof (out_agree_globs (M9 regs) (M9_out_agree regs)) as (_ & (I1 & I2 & I3 & I4)).
pose proof (out_agree_globs (M11 regs) (M11_out_agree regs)) as (_ & (J1 & J2 & J3 & J4)).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x62af8 : word) mem0 rom) (mkst r1 (0x7f87c : word) (M9 regs) rom)
/\ (getr r1 18 = Z_to_bv 64 p /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ getr r1 1 = (0x62b2c : word)
/\ keeps_but RIPL regs r1)).
{ unfold M9. eexists. split.
- stepiv (ltac:(oF' 0x62af8%Z)) (ltac:(oD' 0x62af8%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepsd (ltac:(oF' 0x62afc%Z)) (ltac:(oD' 0x62afc%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(fsok).
stepsd (ltac:(oF' 0x62b00%Z)) (ltac:(oD' 0x62b00%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).
stepsd (ltac:(oF' 0x62b04%Z)) (ltac:(oD' 0x62b04%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).
stepsd (ltac:(oF' 0x62b08%Z)) (ltac:(oD' 0x62b08%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).
stepsd (ltac:(oF' 0x62b0c%Z)) (ltac:(oD' 0x62b0c%Z)) (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).
stepsd (ltac:(oF' 0x62b10%Z)) (ltac:(oD' 0x62b10%Z)) (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).
stepsd (ltac:(oF' 0x62b14%Z)) (ltac:(oD' 0x62b14%Z)) (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).
stepsd (ltac:(oF' 0x62b18%Z)) (ltac:(oD' 0x62b18%Z)) (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(fsok).
stepiv (ltac:(oF' 0x62b1c%Z)) (ltac:(oD' 0x62b1c%Z)) (Z_to_bv 64 s) ltac:(wval).
stepiv (ltac:(oF' 0x62b20%Z)) (ltac:(oD' 0x62b20%Z)) (Z_to_bv 64 (s - 2144)) ltac:(wval).
stepiv (ltac:(oF' 0x62b24%Z)) (ltac:(oD' 0x62b24%Z)) (Z_to_bv 64 p) ltac:(wval).
stepn (ltac:(oF' 0x62b28%Z)) (ltac:(oD' 0x62b28%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q18 & Q8 & Q2 & Q1 & K1).
destruct (asan_inited_run r1 (M9 regs) rom (0x62b2c : word) Q1 ret_ok_62b2c I1) as (r2 & RUN2 & V10 & OA).
assert (V18 : getr r2 18 = Z_to_bv 64 p) by (rewrite (OA 18%bv) by (intros E; discriminate E); exact Q18).
assert (V8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (OA 8%bv) by (intros E; discriminate E); exact Q8).
assert (V2 : getr r2 2 = Z_to_bv 64 (s - 2144)) by (rewrite (OA 2%bv) by (intros E; discriminate E); exact Q2).
assert (K2 : keeps_but RIPL r1 r2) by (intros r Hr HL; apply OA; intros ->; cbv in Hr; intuition discriminate).
assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x62b2c : word) (M9 regs) rom) (mkst r3 (0x8078c : word) (M9 regs) rom)
/\ (getr r3 18 = Z_to_bv 64 p /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 2144) /\ getr r3 1 = (0x62b34 : word)
/\ keeps_but RIPL r2 r3)).
{ eexists. split.
- stepb_ft (ltac:(oF' 0x62b2c%Z)) (ltac:(oD' 0x62b2c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x62b30%Z)) (ltac:(oD' 0x62b30%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S3 as (r3 & RUN3 & T18 & T8 & T2 & T1 & K3).
destruct (tryinit_fast_run r3 (M9 regs) rom (0x62b34 : word) (s - 2144) T2 T1 ret_ok_62b34 ltac:(lia) ltac:(lia)
ltac:(replace (s - 2144 - 16)%Z with (s - 2160)%Z by lia; apply out_agree_store_ok; [apply M9_grows | cbn; lia]) I1)
as (r4 & RUN4 & U10 & U2 & U8 & U1 & K4).
replace (s - 2144 - 8)%Z with (s - 2152)%Z in RUN4 by lia. replace (s - 2144 - 16)%Z with (s - 2160)%Z in RUN4 by lia.
rewrite T8 in RUN4. change (wbytes (wbytes (M9 regs) (Z_to_bv 64 (s - 2152)) (word_to_le_bytes 8 (0x62b34 : word))) (Z_to_bv 64 (s - 2160)) (word_to_le_bytes 8 (Z_to_bv 64 s))) with (M11 regs) in RUN4.
assert (U18 : getr r4 18 = Z_to_bv 64 p) by (rewrite (K4 18%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact T18).
rewrite T8 in U8.
assert (S5 : exists r5, msteps ASEGS (mkst r4 (0x62b34 : word) (M11 regs) rom) (mkst r5 (0x125294 : word) (M11 regs) rom)
/\ (getr r5 10 = Z_to_bv 64 p /\ getr r5 9 = Z_to_bv 64 1 /\ getr r5 18 = Z_to_bv 64 p /\ getr r5 8 = Z_to_bv 64 s
/\ getr r5 2 = Z_to_bv 64 (s - 2144) /\ getr r5 1 = (0x62b48 : word) /\ keeps_but RIPL r4 r5)).
{ eexists. split.
- stepn (ltac:(oF' 0x62b34%Z)) (ltac:(oD' 0x62b34%Z)).
mld (ltac:(oF' 0x62b38%Z)) (ltac:(oD' 0x62b38%Z)) (0x134450 : word) J2.
stepiv (ltac:(oF' 0x62b3c%Z)) (ltac:(oD' 0x62b3c%Z)) (Z_to_bv 64 1) ltac:(wval).
stepiv (ltac:(oF' 0x62b40%Z)) (ltac:(oD' 0x62b40%Z)) (Z_to_bv 64 p) ltac:(wval).
stepjr (ltac:(oF' 0x62b44%Z)) (ltac:(oD' 0x62b44%Z)) (Z_to_bv 64 0x125294) ltac:(gres; reflexivity).
vnorm. apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S5 as (r5 & RUN5 & W10 & W9 & W18 & W8 & W2 & W1 & K5).
destruct (ref_strlen (M11 regs) (Z_to_bv 64 p) buf K rom r5 (0x62b48 : word) (out_agree_slenH (M11 regs) (M11_out_agree regs))
ret_ok_62b48 W1 W10) as (r6 & RUN6 & AG6 & X10).
assert (X9 : getr r6 9 = Z_to_bv 64 1) by (rewrite (sl_agree_getr _ _ 9%bv AG6) by (cbv; intuition discriminate); exact W9).
assert (X18 : getr r6 18 = Z_to_bv 64 p) by (rewrite (sl_agree_getr _ _ 18%bv AG6) by (cbv; intuition discriminate); exact W18).
assert (X8 : getr r6 8 = Z_to_bv 64 s) by (rewrite (sl_agree_getr _ _ 8%bv AG6) by (cbv; intuition discriminate); exact W8).
assert (X2 : getr r6 2 = Z_to_bv 64 (s - 2144)) by (rewrite (sl_agree_getr _ _ 2%bv AG6) by (cbv; intuition discriminate); exact W2).
assert (K6 : keeps_but RIPL r5 r6).
{ intros r Hr HL. apply (sl_agree_getr _ _ r AG6). unfold sl_clob. cbv in Hr. cbn [In]. intuition (subst; discriminate). }
eexists. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
stepb_ft (ltac:(oF' 0x62b48%Z)) (ltac:(oD' 0x62b48%Z)) ltac:(cond).
stepn (ltac:(oF' 0x62b4c%Z)) (ltac:(oD' 0x62b4c%Z)).
mld (ltac:(oF' 0x62b50%Z)) (ltac:(oD' 0x62b50%Z)) (0x132628 : word) J3.
mlbu (ltac:(oF' 0x62b54%Z)) (ltac:(oD' 0x62b54%Z)) (0x1cc923 : word) J4.
stepb_ft (ltac:(oF' 0x62b58%Z)) (ltac:(oD' 0x62b58%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x62b5c%Z)) (ltac:(oD' 0x62b5c%Z)) (Z_to_bv 64 n) ltac:(wval).
apply mst_refl.
- unfold c1_post. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia|].
eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. eapply keeps_but_trans; [exact K3|].
eapply keeps_but_trans; [| eapply keeps_but_trans; [exact K5 | eapply keeps_but_trans; [exact K6 |]]].
+ intros r Hr HL. apply K4; [exact Hr|]. cbv in HL |- *. intuition.
+ solve_keeps_but.
Qed.
End SE.
Definition cR_pre (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 2 = Z_to_bv 64 (s - 2144).
Definition cR_post (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 K /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Lemma ret_ok_62ccc : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt ":&I(RCyR0+\[V<(8%43321'RE%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_cRr_run := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "QO&By5'REyR0%211%5241'6y8%611%311p061&Q4r1%211&Or4r3%3221&QG+R0vR7%3221';'9'H&QB&Q=vQOr6(RC+\Zk0(8%33M21/01Mr7vR@%:598321r2+\Zm@%:3Q418/01Q4%?5>41M6%B3A61&Q3%117&M&Q:%231C:r8%Q321Q5%K231%L271%M2:1qQ:Q;1%Q02Q<1qTJQB1%Q22QC1p0Q41p0Q91p0Q>1pTHQG1pQ8QC1pTLQI1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_cRr_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRr_run) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRr_run) 2%nat 0%nat).
Lemma cRr_run : ltac:(sec_stmt2 constr:(SEC_T_cRr_run) 3%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H9 & H18 & H8 & H2) HFR Hn64.
pose proof HFR as (HO & HGr & HR).
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x62b60 : word) M rom) (mkst r1 (0x7ab68 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ getr r1 1 = (0x62ccc : word)
/\ getr r1 21 = Z_to_bv 64 K /\ getr r1 9 = Z_to_bv 64 n /\ getr r1 18 = Z_to_bv 64 p /\ getr r1 8 = Z_to_bv 64 s /\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepiv (ltac:(oF' 0x62b60%Z)) (ltac:(oD' 0x62b60%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepiv (ltac:(oF' 0x62b64%Z)) (ltac:(oD' 0x62b64%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x62b68%Z)) (ltac:(oD' 0x62b68%Z)) (Z_to_bv 64 (s - 2136)) ltac:(wval).
stepb_ft (ltac:(oF' 0x62b6c%Z)) (ltac:(oD' 0x62b6c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x62b70%Z)) (ltac:(oD' 0x62b70%Z)).
stepb_tk (ltac:(oF' 0x62b74%Z)) (ltac:(oD' 0x62b74%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x62c78%Z)) (ltac:(oD' 0x62c78%Z)) (Z_to_bv 64 K) ltac:(wval).
stepb_tk (ltac:(oF' 0x62c7c%Z)) (ltac:(oD' 0x62c7c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x62cc0%Z)) (ltac:(oD' 0x62cc0%Z)) (Z_to_bv 64 p) ltac:(wval).
stepiv (ltac:(oF' 0x62cc4%Z)) (ltac:(oD' 0x62cc4%Z)) (Z_to_bv 64 n) ltac:(wval).
stepn (ltac:(oF' 0x62cc8%Z)) (ltac:(oD' 0x62cc8%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q21 & Q9 & Q18 & Q8 & K1).
pose proof (out_agree_globs M HO) as (HGM & _).
pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2144)) (0x62ccc : word) p n (s - 2144)
ltac:(unorm; reflexivity) ltac:(lia) HappS ltac:(lia) ltac:(unfold SB in *; lia)
ltac:(replace (s - 2144 - 72)%Z with (s - 2216)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
(ret_ok_62ccc) HGM kS) as RP.
specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZS; [lia | unfold SB in *; lia])).
specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlS_def; apply HLS; lia) HkS).
destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
assert (S21 : getr r2 21 = Z_to_bv 64 K) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
assert (S9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
assert (S18 : getr r2 18 = Z_to_bv 64 p) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
assert (S8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepb_tk (ltac:(oF' 0x62ccc%Z)) (ltac:(oD' 0x62ccc%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x62d84%Z)) (ltac:(oD' 0x62d84%Z)) (Z_to_bv 64 K) ltac:(wval).
stepn (ltac:(oF' 0x62d88%Z)) (ltac:(oD' 0x62d88%Z)).
apply mst_refl.
- unfold cR_post. post.
- eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
Qed.
End SE.
Definition cRqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
getr rg 11 = Z_to_bv 64 fS /\ getr rg 12 = Z_to_bv 64 lS /\ getr rg 13 = Z_to_bv 64 (p + n - 1) /\ getr rg 14 = Z_to_bv 64 (Z.lor u1 u0)
/\ getr rg 10 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_cRqa_run := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "S1'REyR0%211'6y8%511%311p051&By5%2218'3%117&Q4r3%211&Q6r5%211'9&QGzvR7%3221&QE+R0%2241%8241':%J1A&Q>&QBr7&RDvQN%22Q21u8%746521(0%12KF%<3;31r8vR5%:2Q:1%>4=318%A3@16&?%11?%H2K1&QI+2%221J%Q0251%Q2251';'H&Q=vQOr;(RC+\Zk0(8%33QM21/01QMr<vR@%:598321r1+\Zm<%:3R418/01R4%?5>4176%A3Q961&Q5r:%M11r9%O11%5331;&M&Q:%231G>%QO241%R02;1qTJR:1%O2R;1p0Q11p0Q21p0Q;1p0QA1p0QO1p0R91p0R=1pUJRA1pUHRB1pTHRE1pQ8RI1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 1%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 2%nat 0%nat).
Variable w1 : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 3%nat 0%nat).
Lemma cRqa_run : ltac:(sec_stmt2 constr:(SEC_T_cRqa_run) 4%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H9 & H18 & H8 & H2) HO Hn64 R0 R1 B0 B1.
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
unfold SB, HIGHEND in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
pose proof (Z.mod_pos_bound fS 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as Ml.
pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
eexists. split.
- stepiv (ltac:(oF' 0x62b60%Z)) (ltac:(oD' 0x62b60%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
stepiv (ltac:(oF' 0x62b64%Z)) (ltac:(oD' 0x62b64%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x62b68%Z)) (ltac:(oD' 0x62b68%Z)) (Z_to_bv 64 (s - 2136)) ltac:(wval).
stepb_ft (ltac:(oF' 0x62b6c%Z)) (ltac:(oD' 0x62b6c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x62b70%Z)) (ltac:(oD' 0x62b70%Z)).
stepb_ft (ltac:(oF' 0x62b74%Z)) (ltac:(oD' 0x62b74%Z)) ltac:(cond).
stepn (ltac:(oF' 0x62b78%Z)) (ltac:(oD' 0x62b78%Z)).
mld (ltac:(oF' 0x62b7c%Z)) (ltac:(oD' 0x62b7c%Z)) (0x132638 : word) G1.
mld (ltac:(oF' 0x62b80%Z)) (ltac:(oD' 0x62b80%Z)) (0x13acf8 : word) G2.
stepiv (ltac:(oF' 0x62b84%Z)) (ltac:(oD' 0x62b84%Z)) (Z_to_bv 64 (p + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x62b88%Z)) (ltac:(oD' 0x62b88%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x62b8c%Z)) (ltac:(oD' 0x62b8c%Z)) (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x62b90%Z)) (ltac:(oD' 0x62b90%Z)) (Z_to_bv 64 fS) ltac:(wval).
stepiv (ltac:(oF' 0x62b94%Z)) (ltac:(oD' 0x62b94%Z)) (Z_to_bv 64 lS) ltac:(wval).
stepiv (ltac:(oF' 0x62b98%Z)) (ltac:(oD' 0x62b98%Z)) (Z_to_bv 64 faS)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
stepiv (ltac:(oF' 0x62b9c%Z)) (ltac:(oD' 0x62b9c%Z)) (Z_to_bv 64 laS)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
mldw (ltac:(oF' 0x62ba0%Z)) (ltac:(oD' 0x62ba0%Z)) faS R0 w0.
mldw (ltac:(oF' 0x62ba4%Z)) (ltac:(oD' 0x62ba4%Z)) laS R1 w1.
stepov (ltac:(oF' 0x62ba8%Z)) (ltac:(oD' 0x62ba8%Z)) (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
apply mst_refl.
- unfold cRqa_post. split; [post | solve_keeps_but].
Qed.
End SE.
Definition qlR_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 11 = Z_to_bv 64 (fS + i) /\ getr rg 12 = Z_to_bv 64 lS /\ getr rg 10 = Z_to_bv 64 0 /\ getr rg 21 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Definition qlR_post (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 0 /\ getr rg 21 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_qloopR_run := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "R='REyR0%211'6y8%511%311p051'4&By5%2219'=&Q6r4%211&QGzvR7%3221&Q7r3%2281&QE%127:':&QCvQMr5%3221&QHr7%211%7241+1%9221vR4%<3I21';'9'H&QB&Q=vQOr8(RC+\[U8(8%33Q?21/01Q?r:vR@%:598321r1+\[UH%:3QF18/01QF%?5>4176%B3A61&Q8%117&M&Q:%231C:%I241%J271qTJQG1%M2QH1p0O1p0Q=1p0Q@1p0QD1p0QI1pT2QM1pTHQO1pTDR31pQ8R51")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_qloopR_run) 0%nat 0%nat).
Lemma qloopR_run : ltac:(sec_stmt2 constr:(SEC_T_qloopR_run) 1%nat 0%nat).
Proof.
hide_dj.
intros q.
induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H21 & H9 & H18 & H8 & H2) Hi Hq;
pose proof (flS_facts Hn0) as (F1 & F2 & _); unfold SB in *.
- eexists. split.
+ mlbu0 (ltac:(oF' 0x62ca8%Z)) (ltac:(oD' 0x62ca8%Z)) (fS + i)%Z rdn1S.
stepiv (ltac:(oF' 0x62cac%Z)) (ltac:(oD' 0x62cac%Z)) (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x62cb0%Z)) (ltac:(oD' 0x62cb0%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_ft (ltac:(oF' 0x62cb4%Z)) (ltac:(oD' 0x62cb4%Z)) ltac:(cond).
apply mst_refl.
+ unfold qlR_post. post.
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x62ca8 : word) M rom) (fun rg => qlR_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
+ eexists. split.
* mlbu0 (ltac:(oF' 0x62ca8%Z)) (ltac:(oD' 0x62ca8%Z)) (fS + i)%Z rdn1S.
stepiv (ltac:(oF' 0x62cac%Z)) (ltac:(oD' 0x62cac%Z)) (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x62cb0%Z)) (ltac:(oD' 0x62cb0%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x62cb4%Z)) (ltac:(oD' 0x62cb4%Z)) ltac:(cond).
apply mst_refl.
* unfold qlR_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
Qed.
End SE.
Lemma cRqf_run : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "R5'REyR0%211'6y8%511%311p051&By5%2218'=&Q5r2r1r3%43321'9&QEz&QF%1286%4231&QG&QI+2+R0%3221%5271%<271':r4%<2A1%33F1>';'H&QB&Q=vQOr7(RC+\Zm<(8%33Q:21/01Q:r8vR@%:598321+\Zm@%93Q@17/01Q@%>5=Q5165%A3@51&Q3%11Q8&M&Q:%231BQ;%Q9241%Q:271qTJQB1%K2QC1p0M1p0Q21p0Q@1pUDQF1pUBQG1pTHQI1pQ8QM1").
Proof.
hide_dj.
intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H9 & H18 & H8 & H2) BL E.
eexists. split.
- stepb_ft (ltac:(oF' 0x62bac%Z)) (ltac:(oD' 0x62bac%Z)) ltac:(cond).
apply mst_refl.
- unfold cR_post. post.
Qed.
Section SE.
Local Abbreviation SEC_T_cRqs_run := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "RA'REyR0%211'6y8%511%311p051&By5%2218'=&Q5r2r1r3%43321&Q6r5%211'9&QGzvR7%3221&QE+R0%2241%8241&QFr4%221=%72:1&QI+2%2219%?251%A251&<':r6%<2G1%33O1D%511';'H&QB&Q=vQOr9(RC+\Zm<(8%33QD21/01QDr:vR@%:598321+\Zm@%93QJ17/01QJ%>5=Q?165%A3@51&Q3%11QB&M&Q:%231BQE%Q@241%QA271qTJQL1%K2QM1p0M1p0Q41p0Q>1p0QH1p0QL1pUDR21pUBR31pTHR51pQ8R91")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 1%nat 0%nat).
Variable u0 : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 2%nat 0%nat).
Variable u1 : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 3%nat 0%nat).
Lemma cRqs_run : ltac:(sec_stmt2 constr:(SEC_T_cRqs_run) 4%nat 0%nat).
Proof.
hide_dj.
intros (H13 & H14 & HL' & H15 & H10 & H9 & H18 & H8 & H2) HO Hn64 BL NE.
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x62ca4 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
{ unhide HkS. destruct HkS as [K0|K7].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x62bac%Z)) (ltac:(oD' 0x62bac%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x62c88%Z)) (ltac:(oD' 0x62c88%Z)) (Z_to_bv 64 K) ltac:(wval).
mlbk (ltac:(oF' 0x62c8c%Z)) (ltac:(oD' 0x62c8c%Z)) lS rdnLS kS.
stepiv (ltac:(oF' 0x62c90%Z)) (ltac:(oD' 0x62c90%Z)) (Z_to_bv 64 ((p + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x62c94%Z)) (ltac:(oD' 0x62c94%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepov (ltac:(oF' 0x62c98%Z)) (ltac:(oD' 0x62c98%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((p + n - 1) mod 8 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepiv (ltac:(oF' 0x62c9c%Z)) (ltac:(oD' 0x62c9c%Z)) (Z_to_bv 64 1) ltac:(vlit).
stepov (ltac:(oF' 0x62ca0%Z)) (ltac:(oD' 0x62ca0%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlR_inv. post.
- eexists. split.
+ stepb_tk (ltac:(oF' 0x62bac%Z)) (ltac:(oD' 0x62bac%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x62c88%Z)) (ltac:(oD' 0x62c88%Z)) (Z_to_bv 64 K) ltac:(wval).
mlbk (ltac:(oF' 0x62c8c%Z)) (ltac:(oD' 0x62c8c%Z)) lS rdnLS kS.
stepiv (ltac:(oF' 0x62c90%Z)) (ltac:(oD' 0x62c90%Z)) (Z_to_bv 64 ((p + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x62c94%Z)) (ltac:(oD' 0x62c94%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepov (ltac:(oF' 0x62c98%Z)) (ltac:(oD' 0x62c98%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((p + n - 1) mod 8 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepiv (ltac:(oF' 0x62c9c%Z)) (ltac:(oD' 0x62c9c%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepov (ltac:(oF' 0x62ca0%Z)) (ltac:(oD' 0x62ca0%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlR_inv. post. }
cbv beta. intros r1 ((I13 & I14 & I15 & I21 & I9 & I18 & I8 & I2) & K1).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x62cb8 : word) M rom) (fun rg => qlR_post rg /\ keeps_but RIPL regs rg)).
{ destruct (Z.lt_ge_cases fS lS) as [Hfl|Hfl].
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x62ca8 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0x62ca4%Z)) (ltac:(oD' 0x62ca4%Z)) ltac:(cond).
apply mst_refl.
* split; [unfold qlR_inv; repeat split; assumption | exact K1].
+ cbv beta. intros r2 (I2' & K2).
destruct (qloopR_run M (Z.to_nat (lS - fS - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x62ca4%Z)) (ltac:(oD' 0x62ca4%Z)) ltac:(cond).
apply mst_refl.
+ split; [unfold qlR_post; repeat split; assumption | exact K1]. }
cbv beta. intros r4 ((J15 & J21 & J9 & J18 & J8 & J2) & K4).
eexists. split.
- stepiv (ltac:(oF' 0x62cb8%Z)) (ltac:(oD' 0x62cb8%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x62cbc%Z)) (ltac:(oD' 0x62cbc%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x62d84%Z)) (ltac:(oD' 0x62d84%Z)) (Z_to_bv 64 K) ltac:(wval).
stepn (ltac:(oF' 0x62d88%Z)) (ltac:(oD' 0x62d88%Z)).
apply mst_refl.
- unfold cR_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
Qed.
End SE.
Lemma cR_run : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "QJ&By5'REyR0%211%5241'6y8%611%311p061&Q4r1%211&Or4r3%3221';'9'H&QB&Q=vQOr5(RC+\Zk0(8%33I21/01Ir6vR@%:598321r2+\Zm@%:3Q018/01Q0%?5>41I6%B3A61&Q3%117&M&Q:%231C:r7%O21Q1%K231%L271%M2:1qQ:Q71%Q02Q81qTJQ>1%Q22Q?1p0Q41p0Q91pTHQB1pQ8Q>1pTLQD1").
Proof.
hide_dj.
intros regs0 M regs P1 HFR. pose proof HFR as (HO & HGr & HR).
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
{ exfalso. lia. }
destruct (Z.le_gt_cases n 64) as [Hle|Hgt].
- destruct (rdnWS M HO ltac:(lia)) as (w0 & w1 & R0 & R1 & B0 & B1).
destruct (cRqa_run M regs w0 w1 P1 HO ltac:(lia) R0 R1 B0 B1) as (r2 & RUN2 & P2 & K2).
pose proof (lor_bound64 _ _ B1 B0) as BL.
destruct (Z.eq_dec (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0)) 0) as [E|NE].
+ destruct (cRqf_run M r2 _ _ P2 BL E) as (r3 & RUN3 & P3 & K3). exists r3, M.
split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
+ destruct (cRqs_run M r2 _ _ P2 HO ltac:(lia) BL NE) as (r3 & RUN3 & P3 & K3). exists r3, M.
split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
- exact (cRr_run regs0 M regs P1 HFR Hgt).
Qed.
Section SE.
Local Abbreviation SEC_T_c3_run := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "S>&By5'REyR0%211%5241'6y8%611%311p061&Q3r2%211&Or4%2214';'9'H&QB&Q=vQOr5(RC+\Zm@(8%33H21/01HvR@%95872?1r1vR:%<5;21B4%?3>41':&Q<+:%>3Q51<%3281&RDv>%22Q71%83Q741+2%E3Q<1C%:2?1vRB%=3Q<21+1%J3QA1H%?2D1%A3Q@1D+8%N3QE1L%C2H1r6%E213%G3QF31+9%Q43QK1Q2%I2N1%J262%L3QK21+B%Q93R01Q7%N2Q31%O2;2%Q13R021+C%Q>3R51Q<%Q32Q81%Q42@2%Q63R521+D%QC3R:1QA%Q82Q=1%Q92E2%Q;3R:21+E%QH3R?1QF%Q=2QB1%Q>2J2%Q@3R?21+F%QM3RD1QK%QB2QG1%QC2O2%QE3RD21&M&Q:%231R4QL%R:241%R;2:1%R<2@1%R=2F1%R>2L1%R?2Q21%R@2Q81%RA2Q?1%RB2QD1%RC2QJ1%RD2R41qTJS21%RG2S31p0RI1p0RM1pQ8S11pTHS71pTLS81")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c3_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c3_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_c3_run) 2%nat 0%nat).
Lemma c3_run : ltac:(sec_stmt2 constr:(SEC_T_c3_run) 3%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H2) (HO & HGr & (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8)).
eexists. split.
- stepiv (ltac:(oF' 0x62bb0%Z)) (ltac:(oD' 0x62bb0%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepld (ltac:(oF' 0x62bb4%Z)) (ltac:(oD' 0x62bb4%Z)) ra ltac:(maddr (s - 8)%Z; exact R1).
stepld (ltac:(oF' 0x62bb8%Z)) (ltac:(oD' 0x62bb8%Z)) (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
stepld (ltac:(oF' 0x62bbc%Z)) (ltac:(oD' 0x62bbc%Z)) (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
stepld (ltac:(oF' 0x62bc0%Z)) (ltac:(oD' 0x62bc0%Z)) (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
stepld (ltac:(oF' 0x62bc4%Z)) (ltac:(oD' 0x62bc4%Z)) (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
stepld (ltac:(oF' 0x62bc8%Z)) (ltac:(oD' 0x62bc8%Z)) (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
stepld (ltac:(oF' 0x62bcc%Z)) (ltac:(oD' 0x62bcc%Z)) (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).
stepld (ltac:(oF' 0x62bd0%Z)) (ltac:(oD' 0x62bd0%Z)) (getr regs0 22) ltac:(maddr (s - 64)%Z; exact R8).
stepiv (ltac:(oF' 0x62bd4%Z)) (ltac:(oD' 0x62bd4%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x62bd8%Z)) (ltac:(oD' 0x62bd8%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity; [exact H10 | symmetry; apply sp_s | solve_keeps_but].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_strlen_icpt_run := (ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "R<&By5'REyR0%211%5241':&Q<r1(RC+:(8%33;21%6251&RDvR8%22=1%;3=41r2+2%;3C19%>231vRB%A3C21r3+1%A3I1?%D231vR:%G3I21';'6y8%O11%311p0O1'9'H&QB&Q=vQOr6+\ZgH%Q23Q81Q0/01Q8vR6vR@%8576321%958NDQ82%<3;21%Q;2Q0Q6v>%Q62QA1%Q?3QA31%Q?2Q4L%QA3QC1K&Q?%12@Q7&Q6%11QC&Q@%12@QE%J231%K261%L291%M2Q:1%N2=1%O2B1qQ:Q11%Q72Q21qTJR11%Q92R21p0Q;1p0QB1p0QI1pTHR61")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_strlen_icpt_run) 0%nat 0%nat).
Theorem strlen_icpt_run : ltac:(sec_stmt2 constr:(SEC_T_strlen_icpt_run) 1%nat 0%nat).
Proof.
hide_dj.
intros H10 H2 H1.
destruct (c1_run regs H10 H2 H1) as (r1 & RUN1 & P1 & K1).
destruct (cR_run regs (M11 regs) r1 P1 (M11_FR regs)) as (r2 & M2 & RUN2 & P2 & K2 & F2).
destruct (c3_run regs r2 M2 P2 F2) as (r4 & RUN4 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & K4).
exists r4, M2. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN4.
- assert (KB : keeps_but RIPL regs r4).
{ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. exact K4. }
destruct F2 as (HO & HGr & _).
split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [| split; [exact HO | exact HGr]].
intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1, H1; reflexivity|].
destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|]. destruct (decide (r = 19%bv)) as [->|N19]; [exact Q19|].
destruct (decide (r = 20%bv)) as [->|N20]; [exact Q20|]. destruct (decide (r = 21%bv)) as [->|N21]; [exact Q21|].
destruct (decide (r = 22%bv)) as [->|N22]; [exact Q22|].
apply KB; [exact Hr|]. cbv. intuition congruence.
Qed.
End SE.
Corollary wrap_strlen_run : ltac2:(TCodec.tc2 tcn__Ja0StrlenIcpt "R<&By5'REyR0%211%5241':&Q<r1(RC+:(8%33;21%6251&RDvR8%22=1%;3=41r2+2%;3C19%>231vRB%A3C21r3+1%A3I1?%D231vR:%G3I21';'6y8%O11%311p0O1'9'H&QB&Q=vQOr6+\Z`D%Q23Q81Q0/01Q8vR6vR@%8576321%958NDQ82%<3;21%Q;2Q0Q6v>%Q62QA1%Q?3QA31%Q?2Q4L%QA3QC1K&Q?%12@Q7&Q6%11QC&Q@%12@QE%J231%K261%L291%M2Q:1%N2=1%O2B1qQ:Q11%Q72Q21qTJR11%Q92R21p0Q;1p0QB1p0QI1pTHR61").
Proof.
hide_dj.
intros regs H10 H2 H1.
destruct (strlen_icpt_run regs H10 H2 H1) as (r' & M' & RUN & REST).
exists r', M'. split; [|exact REST].
eapply msteps_trans; [|exact RUN].
stepn (ltac:(oF' 0x62a14%Z)) (ltac:(oD' 0x62a14%Z)).
apply mst_refl.
Qed.
End ASL.
End FPX_1.

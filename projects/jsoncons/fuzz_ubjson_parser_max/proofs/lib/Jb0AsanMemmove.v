(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Jb0MemIsZero Jb0RegionPoisoned Jb0AsanMemset Jb0AsanMemcpy.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Jb0MemcpyBase Jb0IntMemmove.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0AsanMemmove () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0AsanMemmove.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0AsanMemmove.FPX_1.AMM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0IntMemmove."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.muslA.Jb0MemcpyBase."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4bytes_le_to_Z"; "5store_ok"]; ["5word_to_le_bytes"; "6bvmap"; "0M"; "0M'"; "0M1"; "0M2"; "0MC"; "0Mj"; "7wbytes"; "8msteps"; "9ret_ok"; ";FR"; ";M9"; ";c1_post"; ";cR_post"; ";cR_pre"]; [";cRqa_post"; ";cW_post"; ";cW_pre"; ";cWqa_post"; ";out_agree"; ";qlR_inv"; ";qlR_post"; ";qlW_inv"; ";qlW_post"; ";slots_ok"; ":RIPL"; ":mm_icpt_globs"; "<mm_result"; "=HIGHEND"; "=SB"; "=frame_only"]; ["=keeps_but"; "=rt_layout_globs"; ">getr"; ">mkst"; ">rdn"; "?keeps_cs"; "@mem_grows"; "AmcH"; "Bloaded_segments"; "Cadd"; "Cdiv"; "Cle"; "Clor"; "Clt"; "Cof_nat"; "Cpow"]; ["Csub"; "Cto_nat"; "0a"; "0bs"; "0fD"; "0fS"; "0faD"; "0faS"; "0fx"; "0i"; "0j"; "0k"; "0kD"; "0kS"; "0lD"; "0lS"]; ["0laD"; "0laS"; "0mem0"; "0n"; "0pd"; "0ps"; "0q"; "0ra"; "0regs"; "0regs'"; "0regs0"; "0rg"; "0rom"; "0s"; "0sp"; "DBV"]; ["DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0u0"; "0u1"; "0v"; "0w0"; "0w1"; "0x"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition mm_icpt_globs (M : word -> option byte) : Prop :=
rdn ASEGS M (0x134f08 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d719)) /\
rdn ASEGS M (0x13d719 : word) 1%nat = Some [Z_to_bv 8 1].
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
#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv.
Section AMM.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra : word.
Variables pd ps n s : Z.
Variable bs : list byte.
Variables kS fS lS faS laS : Z.
Variables kD fD lD faD laD : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis HfS_def : fS = (SB + ps / 8)%Z. Hypothesis HlS_def : lS = (SB + (ps + n - 1) / 8)%Z.
Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z. Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.
Hypothesis HfD_def : fD = (SB + pd / 8)%Z. Hypothesis HlD_def : lD = (SB + (pd + n - 1) / 8)%Z.
Hypothesis HfaD_def : faD = (fD - fD mod 8)%Z. Hypothesis HlaD_def : laD = (lD - lD mod 8)%Z.
Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
Hypothesis HappS : in_app8 ps n.
Hypothesis HappD : in_app8 pd n.
Hypothesis Hs : (0x1000000 <= s - 2216)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis HshS : (lS + 8 <= s - 2216)%Z.
Hypothesis HshD : (lD + 8 <= s - 2216)%Z.
Hypothesis HdjS : (0 < n -> ps + n <= s - 2216 \/ s <= ps)%Z.
Hypothesis HdjD : (0 < n -> pd + n <= s - 2216 \/ s <= pd)%Z.
Hypothesis Hover : (pd + n <= ps \/ ps + n <= pd)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2216)) 2216%nat = true.
Hypothesis Hdst : store_ok ASEGS mem0 (Z_to_bv 64 pd) (Z.to_nat n) = true.
Hypothesis Hsrc : rdn ASEGS mem0 (Z_to_bv 64 ps) (Z.to_nat n) = Some bs.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : rt_layout_globs mem0.
Hypothesis HI : mm_icpt_globs mem0.
Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> mem0 x = Some (Z_to_bv 8 0).
Hypothesis HLS : (0 < n)%Z -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS).
Hypothesis HkS : kS = 0%Z \/ ((ps + n - 1) mod 8 < kS <= 7)%Z.
Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laS) 8%nat = Some w1.
Hypothesis HZD : (0 < n)%Z -> forall x : word, (fD <= bv_unsigned x < lD)%Z -> mem0 x = Some (Z_to_bv 8 0).
Hypothesis HLD : (0 < n)%Z -> mem0 (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD).
Hypothesis HkD : kD = 0%Z \/ ((pd + n - 1) mod 8 < kD <= 7)%Z.
Hypothesis HWD : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faD) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laD) 8%nat = Some w1.
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (rewrite (zbv_wrap_up (n - 65)); f_equal; lia); try solve_keeps_but.
#[local] Ltac hide_dj := try hide HdjS; try hide HdjD; try hide Hover; try hide HkS; try hide HkD; try hide HappS; try hide HappD.
#[using="Hs_def"] Lemma sp_s : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "9':'S1yR0%211vRN&S0vRM%2251%83541"). Proof. hide_dj. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[using="pd fS lS fD lD Hn HappS"] Lemma pS_facts : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "N'9&QKzvRE%3221&QIvRC%2241+8%4221&Q=%:221&QJ%12:5%=2<1%>225%@221&QM%12@<&R0+1%22>1%:21>%F2:1%G22>%I221p081%K2;1%L2A1%M2I1").
Proof.
hide_dj.
unhide HappS.
unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappS as [[H1 H2]|[H1 H2]];
(repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
Qed.
#[using="ps fS lS fD lD Hn HappD"] Lemma pD_facts : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "N'9&QKzvRD%3221&QIvRC%2241+8%4221&Q=%:221&QJ%12:5%=2<1%>225%@221&QM%12@<&R0+1%22>1%:21>%F2:1%G22>%I221p081%K2;1%L2A1%M2I1").
Proof.
hide_dj.
unhide HappD.
unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappD as [[H1 H2]|[H1 H2]];
(repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
Qed.
#[using="pd ps fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS HshS"] Lemma flS_facts : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q3&QMzvRC%3221'9&QK&Q>vR5%3221vR?%5231%7231&QI+8%2251&R0vRM+RU8%3221%>251+7%62>1vR7%B221%C22A%E221%;2A6vRA%G221%H22D%J221%K261%L2=1%M2F1p0O1").
Proof.
hide_dj.
intros Hn0. pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). repeat split; lia.
Qed.
#[using="pd ps fS lS HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD HshD"] Lemma flD_facts : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q3&QMzvRC%3221'9&QK&Q>vR4%3221vR>%5231%7231&QI+8%2251&R0vRM+RU8%3221%>251+7%62>1vR6%B221%C22A%E221%;2A6vR@%G221%H22D%J221%K261%L2=1%M2F1p0O1").
Proof.
hide_dj.
intros Hn0. pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound fD 8 ltac:(lia)). pose proof (Z.mod_pos_bound lD 8 ltac:(lia)). repeat split; lia.
Qed.
Definition out_agree (M : word -> option byte) : Prop :=
forall x : word, (bv_unsigned x < s - 2216 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
#[using="Type"] Lemma out_agree_refl : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "3&Q4vRB%211"). Proof. hide_dj. intros x _. reflexivity. Qed.
#[using="pd ps n fS lS fD lD Hs"] Lemma out_agree_w : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q5'S1yR0%211'6y8%511%311p051'=&Q4r3%211'9&QK+8%2215+RU8%4271%6231&Hr5&S0&R0vRMr4%3221%52I1&@u8%221C%;3:41%F11p0>1p0F1pV<Q01pTHK1pQ6M1").
Proof.
hide_dj.
intros M k v HF Hk x Hx. pose proof (u64_range x).
destruct Hx as [Hx|Hx].
- rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
- rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
#[using="pd ps n fS lS fD lD Hs"] Lemma out_agree_rdn : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q:'S1yR0%211'6y8%511%311p051'4&Q4r3%211&QK&QI&S2%12>5&QNr2%211%6241&R0vRM+RU8%3221%<251':'3%11F%I11&QD&QHr5r4%44321GvRB%64513I%;3831p0=1p0K1pTHO1pT6Q61pQ6Q21").
Proof. hide_dj. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
#[using="pd ps n fS lS fD lD Hs HG HI"] Lemma out_agree_globs : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "D'S1yR0%211'6y8%511%311p051&Q4r1%211'9&QAr2%211&Q;%113%6231p081pQ6<1").
Proof.
hide_dj.
intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). destruct HI as (I1 & I2).
unfold rt_layout_globs, mm_icpt_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
repeat split; assumption.
Qed.
Section SE.
Local Abbreviation SEC_T_out_agree_store_ok := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q:'S1yR0%211'6y8%511%311p051'='4&QFvRBr3%3221'9&QK&QNr2%211%4217+RU8%6291%8231':'1&?&QHr5&S0&R0vRMr4%3221%52Q01%94871F(7%=3<21p0?1p0I1pTFN1pTHQ01pQ6Q21")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_out_agree_store_ok) 0%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_out_agree_store_ok) 1%nat 0%nat).
Variable j : ltac:(sec_ty2 constr:(SEC_T_out_agree_store_ok) 2%nat 0%nat).
Lemma out_agree_store_ok : ltac:(sec_stmt2 constr:(SEC_T_out_agree_store_ok) 3%nat 0%nat).
Proof using pd ps n fS lS fD lD Hs Hok M k j.
hide_dj.
intros HGr Hk.
apply (store_ok_mono _ _ mem0 M _ HGr).
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2216)) _ 2216%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
Qed.
End SE.
#[using="pd fS lS fD lD Hn HappS Hs HdjS Hsrc"] Lemma out_agree_src : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "O'S1yR0%211'6y8%511%311p051&Q4r1%211':'3%118%;11&QD&QHr2&S0vRE%22C1&R1vRC%211%948741(0vR3%22>1%A3>41p0C1pQ6G1").
Proof.
hide_dj.
intros M HF. pose proof pS_facts as (Pp & Ppn & _). unhide HdjS. unfold HIGHEND in *.
rewrite (rdn_ext ASEGS (Z.to_nat n) M mem0); [exact Hsrc | unorm; rewrite Z2Nat.id by lia; lia|].
intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite Z2Nat.id in Hx by lia. apply HF. lia.
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
#[using="pd ps n fS lS fD lD Hs"] Lemma M9_out_agree : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "<&Ay5'S1yR0%211%5241&Q4&Lr1%211%411pUH61"). Proof. hide_dj. intros rg. unfold M9. oagree. Qed.
#[using="Type"] Lemma M9_grows : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "=&Ay5'S1yR0%211%5241&QFvRB&Lr1%211%5241pUH71"). Proof. hide_dj. intros rg. unfold M9. grows. Qed.
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
Local Abbreviation SEC_T_M9_FR := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "<&Ay5'S1yR0%211%5241&Kr1&L%112%4231pUF61")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_M9_FR) 0%nat 0%nat).
Lemma M9_FR : ltac:(sec_stmt2 constr:(SEC_T_M9_FR) 1%nat 0%nat).
Proof using pd ps n fS lS fD lD Hs regs0.
hide_dj. split; [apply M9_out_agree | split; [apply M9_grows|]]. unfold M9. repeat split; slot. Qed.
End SE.
#[using="pd ps n fS lS fD lD Hs"] Lemma rdn_slot_ext : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "QE'S1yR0%211'6y8%511%311p051'='9&QK&R0vRM+RS0%3221&S2r1%22@1%8241&QM%1238%<231':r5r2%211r4%113%63F31p081pVBL1+8%F218%G29D%I221'3%11O%Q211&QD&QH&S0r3%O2N1%32Q:1u8%746F21%847D32%I3:21p0>1p0C1pTHQ:1pQ<Q<1pQ:Q=1").
Proof.
hide_dj.
intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
Qed.
#[using="pd ps n fS lS fD lD Hs"] Lemma slots_ok_ext : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q:&Ay5'S1yR0%211%5241'6y8%611%311p061'9&QK&R0vRM+RS0%3221&S2r1%22@1%8241&QM%1238%<231':r3r2%211r4%113%63E31p081pVBL1&Q9%1269r5%321;p031p061pQ<M1pQ:N1pUFQ41").
Proof.
hide_dj.
intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8). unfold slots_ok.
rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
Qed.
#[using="pd ps n fS lS fD lD Hs"] Lemma FR_region : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q0&Ay5'S1yR0%211%5241'6y8%611%311p061&Kr3r2%3221&Q?&R0vRM+RS0%3221%53817&QFr4%221;r6%>213p031p071p0>1pQ8C1pQ6D1pUFJ1").
Proof.
hide_dj.
intros regs0 M M' (O & G & R) HF HGr. split; [|split].
- intros x Hx. rewrite (HF x) by lia. apply O. exact Hx.
- eapply mem_grows_trans; [exact G | exact HGr].
- apply (slots_ok_ext regs0 M M'); [|exact R]. intros x Hx. apply HF. lia.
Qed.
#[using="pd ps fS lS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS Hs HshS HshD HWS"] Lemma rdnWS : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "R0'S1yR0%211'6y8%511%311p051&Q4r1%211'9&QMzvRC%3221&QK+R0%2241%8241';'3%11A':%E12&QD&QHr5&S0vR7%22M1u8%746521(0r2%22=1%=3<41vRA%:2Q51%>4=<18%72BO%B3A21&>%119%L2O1&QO+2%221N%Q4251%Q6251%81Q9%Q32Q61%Q8225%Q:221%Q;251%Q<2>1%Q=2D1qV@Q31%Q62Q41qV>Q51%Q82Q61p0Q:1p0QD1pQ6QH1").
Proof.
hide_dj.
intros M HO Hn64. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
destruct (HWS Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
Qed.
#[using="pd ps fS lS fD lD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD Hs HshS HshD HWD"] Lemma rdnWD : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "R0'S1yR0%211'6y8%511%311p051&Q4r1%211'9&QMzvRC%3221&QK+R0%2241%8241';'3%11A':%E12&QD&QHr5&S0vR6%22M1u8%746521(0r2%22=1%=3<41vR@%:2Q51%>4=<18%72BO%B3A21&>%119%L2O1&QO+2%221N%Q4251%Q6251%81Q9%Q32Q61%Q8225%Q:221%Q;251%Q<2>1%Q=2D1qV@Q31%Q62Q41qV>Q51%Q82Q61p0Q:1p0QD1pQ6QH1").
Proof.
hide_dj.
intros M HO Hn64. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
destruct (HWD Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
Qed.
#[using="pd ps faS laS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS Hs HshS HshD HZS"] Lemma rdn1S : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "QA'S1yR0%211'6y8%511%311p051'=&Q4r2%211&QMzvRC%3221'9&QKvR5r3%3221vR?%:231%7231':'3%11E%H11&QD&QHr5&S0r4%22Q01u1%746521(0(2%72Q2I(5%11Q3%43Q431%62@1%C3@81p0E1p0N1p0Q31pVDQ71pQ6Q91").
Proof.
hide_dj.
intros M z HO Hn0 Hz. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZS Hn0) by (unorm; lia). reflexivity.
Qed.
#[using="pd ps fS lS faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD Hs HshD HZD"] Lemma rdn1D : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "QA'S1yR0%211'6y8%511%311p051'=&Q4r2%211&QMzvRC%3221'9&QKvR4r3%3221vR>%:231%7231':'3%11E%H11&QD&QHr5&S0r4%22Q01u1%746521(0(2%72Q2I(5%11Q3%43Q431%62@1%C3@81p0E1p0N1p0Q31pVDQ71pQ6Q91").
Proof.
hide_dj.
intros M z HO Hn0 Hz. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZD Hn0) by (unorm; lia). reflexivity.
Qed.
#[using="pd ps fS faS laS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS Hs HshS HLS"] Lemma rdnLS : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q='S1yR0%211'6y8%511%311p051'=&Q4r2%211&QMzvRC%3221':r3vR?%33;21'3%11@%C11&QD&QHr5&S0r4%22K1u1%746521(0(2vR=%82N1(5%11O%53Q031%72A1%G3A91p0E1p0J1p0O1pVDQ31pQ6Q51").
Proof.
hide_dj.
intros M z HO Hn0 ->. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HLS Hn0). reflexivity.
Qed.
#[using="pd ps fS lS fD faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD Hs HshD HLD"] Lemma rdnLD : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q='S1yR0%211'6y8%511%311p051'=&Q4r2%211&QMzvRC%3221':r3vR>%33;21'3%11@%C11&QD&QHr5&S0r4%22K1u1%746521(0(2vR<%82N1(5%11O%53Q031%72A1%G3A91p0E1p0J1p0O1pVDQ31pQ6Q51").
Proof.
hide_dj.
intros M z HO Hn0 ->. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HLD Hn0). reflexivity.
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
getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_c1_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "R?&Ay5'S1yR0%211%5241':&QBr1(RO+:(8%33;21%6251&S0vRD%22=1%;3=41r2+;%;3C19%>231vRE%92D1%B3D31r3+<%B3J1@%E231vRC%@2K1%I3K31r4+2%I3Q11G%L231vRN%O3Q121r5+1%O3Q71M%Q2231vRG%Q53Q721';'9'I&QH&QCvR8r7+^oW8%Q;3QA1Q9/01QAvRBvRL%8576321+^oY4%QA3QG1Q?/01QG&L%11;%>5=QF317%A3@71&M%11QI&Q@&Q:%231BQL%H241%I271qUDR21%L2R31p0N1p0Q51p0Q<1p0QD1p0QL1pUBR91")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c1_run) 0%nat 0%nat).
Lemma c1_run : ltac:(sec_stmt2 constr:(SEC_T_c1_run) 1%nat 0%nat).
Proof using fS lS fD lD Hs_def Hn HappS HappD Hs Hok HG HI regs.
hide_dj.
intros H10 H11 H12 H2 H1.
rewrite sp_s in H2.
pose proof pS_facts as (PSp & PSn & _). pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
pose proof (out_agree_globs (M9 regs) (M9_out_agree regs)) as (_ & (I1 & I2)).
unfold M9 in *.
eexists. split.
- stepiv (ltac:(oF' 0x77ce8%Z)) (ltac:(oD' 0x77ce8%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepsd (ltac:(oF' 0x77cec%Z)) (ltac:(oD' 0x77cec%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(fsok).
stepsd (ltac:(oF' 0x77cf0%Z)) (ltac:(oD' 0x77cf0%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).
stepsd (ltac:(oF' 0x77cf4%Z)) (ltac:(oD' 0x77cf4%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).
stepsd (ltac:(oF' 0x77cf8%Z)) (ltac:(oD' 0x77cf8%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).
stepsd (ltac:(oF' 0x77cfc%Z)) (ltac:(oD' 0x77cfc%Z)) (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).
stepsd (ltac:(oF' 0x77d00%Z)) (ltac:(oD' 0x77d00%Z)) (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).
stepsd (ltac:(oF' 0x77d04%Z)) (ltac:(oD' 0x77d04%Z)) (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).
stepsd (ltac:(oF' 0x77d08%Z)) (ltac:(oD' 0x77d08%Z)) (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(fsok).
stepiv (ltac:(oF' 0x77d0c%Z)) (ltac:(oD' 0x77d0c%Z)) (Z_to_bv 64 s) ltac:(wval).
stepiv (ltac:(oF' 0x77d10%Z)) (ltac:(oD' 0x77d10%Z)) (Z_to_bv 64 (s - 2144)) ltac:(wval).
stepn (ltac:(oF' 0x77d14%Z)) (ltac:(oD' 0x77d14%Z)).
mld (ltac:(oF' 0x77d18%Z)) (ltac:(oD' 0x77d18%Z)) (0x134f08 : word) I1.
mlbu (ltac:(oF' 0x77d1c%Z)) (ltac:(oD' 0x77d1c%Z)) (0x13d719 : word) I2.
stepb_ft (ltac:(oF' 0x77d20%Z)) (ltac:(oD' 0x77d20%Z)) ltac:(cond).
apply mst_refl.
- unfold c1_post. post.
Qed.
End SE.
Definition cR_pre (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 2 = Z_to_bv 64 (s - 2144).
Definition cR_post (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_cRz_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "QD'S1yR0%211'6y8%511%311p051&Ay5%2218&Or1%211':'=vRCz%43321';'9'I&QH&QCvR8r4(RO+^oY4(8%33L21/01Lr5vRL%:598321+^o[L%93Q217/01Q2%>5=I165%A3@51&N%11L&Q@&Q:%231BO%H241%I271qUDQ41%L2Q51p0N1p0Q41pUBQ81pQ6Q<1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRz_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRz_run) 1%nat 0%nat).
Lemma cRz_run : ltac:(sec_stmt2 constr:(SEC_T_cRz_run) 2%nat 0%nat).
Proof using fS lS fD lD Hn HappS HappD Hs M regs.
hide_dj.
intros (H10 & H11 & H12 & H8 & H2) Hn0.
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
eexists. split.
- stepiv (ltac:(oF' 0x77d24%Z)) (ltac:(oD' 0x77d24%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - ps)) ltac:(xval).
stepiv (ltac:(oF' 0x77d28%Z)) (ltac:(oD' 0x77d28%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x77d2c%Z)) (ltac:(oD' 0x77d2c%Z)) (Z_to_bv 64 (s - 2136)) ltac:(wval).
stepb_ft (ltac:(oF' 0x77d30%Z)) (ltac:(oD' 0x77d30%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x77d34%Z)) (ltac:(oD' 0x77d34%Z)) (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x77d38%Z)) (ltac:(oD' 0x77d38%Z)).
stepb_tk (ltac:(oF' 0x77d3c%Z)) (ltac:(oD' 0x77d3c%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x77e80%Z)) (ltac:(oD' 0x77e80%Z)) ltac:(cond).
stepn (ltac:(oF' 0x77e84%Z)) (ltac:(oD' 0x77e84%Z)).
apply mst_refl.
- unfold cR_post. post.
Qed.
End SE.
#[using="Type"] Lemma ret_ok_77f60 : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove ":&J(ROyR0+^ok0(8%43321'S1%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_cRr_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "QO&Ay5'S1yR0%211%5241'6y8%611%311p061&Or1%211&Kr4r3%3221&QM+R0vRC%3221';'9'I&QH&QCvR8r6(RO+^oY4(8%33M21/01Mr7vRL%:598321r2+^o[L%:3Q418/01Q4%?5>41M6%B3A61&N%117&Q@&Q:%231C:r8%Q321Q5%K231%L271%M2:1qQ8Q;1%Q02Q<1qUDQB1%Q22QC1p0Q41p0Q91p0Q>1pUBQG1pQ6QC1pUFQI1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_cRr_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRr_run) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRr_run) 2%nat 0%nat).
Lemma cRr_run : ltac:(sec_stmt2 constr:(SEC_T_cRr_run) 3%nat 0%nat).
Proof using kS fS lS faS laS fD lD faD laD HfS_def HlS_def HfD_def HlD_def Hn HappS HappD Hs HshS HshD Hok HG HI HZS HLS HkS HWS HWD regs0 M regs.
hide_dj.
intros (H10 & H11 & H12 & H8 & H2) HFR Hn64.
pose proof HFR as (HO & HGr & HR).
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x77d24 : word) M rom) (mkst r1 (0x7ae38 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 ps /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ getr r1 1 = (0x77f60 : word)
/\ getr r1 21 = Z_to_bv 64 pd /\ getr r1 22 = Z_to_bv 64 ps /\ getr r1 9 = Z_to_bv 64 n /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 19 = Z_to_bv 64 (n - 65) /\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepiv (ltac:(oF' 0x77d24%Z)) (ltac:(oD' 0x77d24%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - ps)) ltac:(xval).
stepiv (ltac:(oF' 0x77d28%Z)) (ltac:(oD' 0x77d28%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x77d2c%Z)) (ltac:(oD' 0x77d2c%Z)) (Z_to_bv 64 (s - 2136)) ltac:(wval).
stepb_ft (ltac:(oF' 0x77d30%Z)) (ltac:(oD' 0x77d30%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x77d34%Z)) (ltac:(oD' 0x77d34%Z)) (Z_to_bv 64 (n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepn (ltac:(oF' 0x77d38%Z)) (ltac:(oD' 0x77d38%Z)).
stepb_tk (ltac:(oF' 0x77d3c%Z)) (ltac:(oD' 0x77d3c%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x77e80%Z)) (ltac:(oD' 0x77e80%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x77f48%Z)) (ltac:(oD' 0x77f48%Z)) (Z_to_bv 64 pd) ltac:(wval).
stepiv (ltac:(oF' 0x77f4c%Z)) (ltac:(oD' 0x77f4c%Z)) (Z_to_bv 64 ps) ltac:(wval).
stepiv (ltac:(oF' 0x77f50%Z)) (ltac:(oD' 0x77f50%Z)) (Z_to_bv 64 ps) ltac:(wval).
stepiv (ltac:(oF' 0x77f54%Z)) (ltac:(oD' 0x77f54%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x77f58%Z)) (ltac:(oD' 0x77f58%Z)) (Z_to_bv 64 n) ltac:(wval).
stepn (ltac:(oF' 0x77f5c%Z)) (ltac:(oD' 0x77f5c%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q21 & Q22 & Q9 & Q8 & Q19 & K1).
pose proof (out_agree_globs M HO) as (HGM & _).
pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2144)) (0x77f60 : word) ps n (s - 2144)
ltac:(unorm; reflexivity) ltac:(lia) HappS ltac:(lia) ltac:(unfold SB in *; lia)
ltac:(replace (s - 2144 - 72)%Z with (s - 2216)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
(ret_ok_77f60) HGM kS) as RP.
specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZS; [lia | unfold SB in *; lia])).
specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlS_def; apply HLS; lia) HkS).
destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
assert (S21 : getr r2 21 = Z_to_bv 64 pd) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
assert (S22 : getr r2 22 = Z_to_bv 64 ps) by (rewrite (K2 22%bv) by (cbv; tauto); exact Q22).
assert (S9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
assert (S8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
assert (S19 : getr r2 19 = Z_to_bv 64 (n - 65)) by (rewrite (K2 19%bv) by (cbv; tauto); exact Q19).
eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x77f60%Z)) (ltac:(oD' 0x77f60%Z)) (Z_to_bv 64 ps) ltac:(wval).
stepiv (ltac:(oF' 0x77f64%Z)) (ltac:(oD' 0x77f64%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x77f68%Z)) (ltac:(oD' 0x77f68%Z)) (Z_to_bv 64 0) ltac:(wval).
stepiv (ltac:(oF' 0x77f6c%Z)) (ltac:(oD' 0x77f6c%Z)) (Z_to_bv 64 pd) ltac:(wval).
stepb_tk (ltac:(oF' 0x77f70%Z)) (ltac:(oD' 0x77f70%Z)) ltac:(cond).
apply mst_refl.
- unfold cR_post. post.
- eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
Qed.
End SE.
Definition cRqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
getr rg 13 = Z_to_bv 64 fS /\ getr rg 14 = Z_to_bv 64 lS /\ getr rg 15 = Z_to_bv 64 (ps + n - 1) /\ getr rg 16 = Z_to_bv 64 (Z.lor u1 u0)
/\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_cRqa_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "S1'S1yR0%211'6y8%511%311p051&Ay5%2218'3%117&Or3%211&Q4r5%211'9&QMzvRC%3221&QK+R0%2241%8241':%J1A&QD&QHr7&S0vR7%22Q21u8%746521(0%12KF%<3;31r8vRA%:2Q:1%>4=318%A3@16&>%11?%H2K1&QO+2%221J%Q0251%Q2251';'I&QCvR8r;(RO+^oY4(8%33QM21/01QMr<vRL%:598321r1+^o[H%:3R418/01R4%?5>4176%A3Q961&Q0r:%M11r9%O11%5331;&Q@&Q:%231G>%QO241%R02;1qUDR:1%O2R;1p0Q11p0Q21p0Q;1p0QA1p0QO1p0R91p0R=1pV@RA1pV>RB1pUBRE1pQ6RI1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 1%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 2%nat 0%nat).
Variable w1 : ltac:(sec_ty2 constr:(SEC_T_cRqa_run) 3%nat 0%nat).
Lemma cRqa_run : ltac:(sec_stmt2 constr:(SEC_T_cRqa_run) 4%nat 0%nat).
Proof using fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS HappD Hs HshS HG HI M regs w0 w1.
hide_dj.
intros (H10 & H11 & H12 & H8 & H2) HO Hn64 R0 R1 B0 B1.
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
unfold SB, HIGHEND in *.
pose proof (Z.div_mod ps 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound ps 8 ltac:(lia)) as Mp.
pose proof (Z.mod_pos_bound fS 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as Ml.
pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
eexists. split.
- stepiv (ltac:(oF' 0x77d24%Z)) (ltac:(oD' 0x77d24%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - ps)) ltac:(xval).
stepiv (ltac:(oF' 0x77d28%Z)) (ltac:(oD' 0x77d28%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x77d2c%Z)) (ltac:(oD' 0x77d2c%Z)) (Z_to_bv 64 (s - 2136)) ltac:(wval).
stepb_ft (ltac:(oF' 0x77d30%Z)) (ltac:(oD' 0x77d30%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x77d34%Z)) (ltac:(oD' 0x77d34%Z)) (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x77d38%Z)) (ltac:(oD' 0x77d38%Z)).
stepb_ft (ltac:(oF' 0x77d3c%Z)) (ltac:(oD' 0x77d3c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x77d40%Z)) (ltac:(oD' 0x77d40%Z)).
mld (ltac:(oF' 0x77d44%Z)) (ltac:(oD' 0x77d44%Z)) (0x1343a0 : word) G1.
stepiv (ltac:(oF' 0x77d48%Z)) (ltac:(oD' 0x77d48%Z)) (Z_to_bv 64 (ps + n)) ltac:(wval).
mld (ltac:(oF' 0x77d4c%Z)) (ltac:(oD' 0x77d4c%Z)) (0x13ca38 : word) G2.
stepiv (ltac:(oF' 0x77d50%Z)) (ltac:(oD' 0x77d50%Z)) (Z_to_bv 64 (ps / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x77d54%Z)) (ltac:(oD' 0x77d54%Z)) (Z_to_bv 64 (ps + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x77d58%Z)) (ltac:(oD' 0x77d58%Z)) (Z_to_bv 64 ((ps + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x77d5c%Z)) (ltac:(oD' 0x77d5c%Z)) (Z_to_bv 64 fS) ltac:(wval).
stepiv (ltac:(oF' 0x77d60%Z)) (ltac:(oD' 0x77d60%Z)) (Z_to_bv 64 lS) ltac:(wval).
stepiv (ltac:(oF' 0x77d64%Z)) (ltac:(oD' 0x77d64%Z)) (Z_to_bv 64 faS)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
stepiv (ltac:(oF' 0x77d68%Z)) (ltac:(oD' 0x77d68%Z)) (Z_to_bv 64 laS)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
mldw (ltac:(oF' 0x77d6c%Z)) (ltac:(oD' 0x77d6c%Z)) faS R0 w0.
mldw (ltac:(oF' 0x77d70%Z)) (ltac:(oD' 0x77d70%Z)) laS R1 w1.
stepov (ltac:(oF' 0x77d74%Z)) (ltac:(oD' 0x77d74%Z)) (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
apply mst_refl.
- unfold cRqa_post. split; [post | solve_keeps_but].
Qed.
End SE.
Definition qlR_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 13 = Z_to_bv 64 (fS + i) /\ getr rg 14 = Z_to_bv 64 lS /\ getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Definition qlR_post (rg : bvmap 5 word) : Prop :=
getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_qloopR_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "R='S1yR0%211'6y8%511%311p051'4&Ay5%2219'=&Q4r4%211&QMzvRC%3221&Q5r3%2281&QK%127:':&QIvR5r5%3221&QNr7%211%7241+1%9221vR?%<3I21';'9'I&QH&QCvR8r8(RO+^oi@(8%33Q?21/01Q?r:vRL%:598321r1+^oj0%:3QF18/01QF%?5>4176%B3A61&Q6%117&Q@&Q:%231C:%I241%J271qUDQG1%M2QH1p0O1p0Q=1p0Q@1p0QD1p0QI1pTDQM1pUBQO1pU>R31pQ6R51")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_qloopR_run) 0%nat 0%nat).
Lemma qloopR_run : ltac:(sec_stmt2 constr:(SEC_T_qloopR_run) 1%nat 0%nat).
Proof using faS laS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS Hs HshS HshD HZS M.
hide_dj.
intros q.
induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H10 & H11 & H12 & H8 & H19 & H2) Hi Hq;
pose proof (flS_facts Hn0) as (F1 & F2 & _); unfold SB in *.
- eexists. split.
+ mlbu0 (ltac:(oF' 0x77f30%Z)) (ltac:(oD' 0x77f30%Z)) (fS + i)%Z rdn1S.
stepiv (ltac:(oF' 0x77f34%Z)) (ltac:(oD' 0x77f34%Z)) (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x77f38%Z)) (ltac:(oD' 0x77f38%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_ft (ltac:(oF' 0x77f3c%Z)) (ltac:(oD' 0x77f3c%Z)) ltac:(cond).
apply mst_refl.
+ unfold qlR_post. post.
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77f30 : word) M rom) (fun rg => qlR_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
+ eexists. split.
* mlbu0 (ltac:(oF' 0x77f30%Z)) (ltac:(oD' 0x77f30%Z)) (fS + i)%Z rdn1S.
stepiv (ltac:(oF' 0x77f34%Z)) (ltac:(oD' 0x77f34%Z)) (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x77f38%Z)) (ltac:(oD' 0x77f38%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x77f3c%Z)) (ltac:(oD' 0x77f3c%Z)) ltac:(cond).
apply mst_refl.
* unfold qlR_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
Qed.
End SE.
#[using="fD lD"] Lemma cRqf_run : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "R5'S1yR0%211'6y8%511%311p051&Ay5%2218'=&Q0r2r1r3%43321'9&QKz&QL%1286%4231&QM&QO+2+R0%3221%5271%<271':r4%<2A1%33F1>';'I&QH&QCvR8r7(RO+^o[H(8%33Q:21/01Q:r8vRL%:598321+^o[L%93Q@17/01Q@%>5=Q5165%A3@51&N%11Q8&Q@&Q:%231BQ;%Q9241%Q:271qUDQB1%K2QC1p0M1p0Q21p0Q@1pV:QF1pV8QG1pUBQI1pQ6QM1").
Proof.
hide_dj.
intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H8 & H19 & H2) BL E.
eexists. split.
- stepb_ft (ltac:(oF' 0x77d78%Z)) (ltac:(oD' 0x77d78%Z)) ltac:(cond).
apply mst_refl.
- unfold cR_post. post.
Qed.
Section SE.
Local Abbreviation SEC_T_cRqs_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "RA'S1yR0%211'6y8%511%311p051&Ay5%2218'=&Q0r2r1r3%43321&Q4r5%211'9&QMzvRC%3221&QK+R0%2241%8241&QLr4%221=%72:1&QO+2%2219%?251%A251&<':r6%<2G1%33O1D%511';'I&QH&QCvR8r9(RO+^o[H(8%33QD21/01QDr:vRL%:598321+^o[L%93QJ17/01QJ%>5=Q?165%A3@51&N%11QB&Q@&Q:%231BQE%Q@241%QA271qUDQL1%K2QM1p0M1p0Q41p0Q>1p0QH1p0QL1pV:R21pV8R31pUBR51pQ6R91")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 1%nat 0%nat).
Variable u0 : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 2%nat 0%nat).
Variable u1 : ltac:(sec_ty2 constr:(SEC_T_cRqs_run) 3%nat 0%nat).
Lemma cRqs_run : ltac:(sec_stmt2 constr:(SEC_T_cRqs_run) 4%nat 0%nat).
Proof using kS faS laS fD lD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS HappD Hs HshS HshD HZS HLS HkS M regs u0 u1.
hide_dj.
intros (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H8 & H19 & H2) HO Hn64 BL NE.
pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound (ps + n - 1) 8 ltac:(lia)) as Mq.
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77f2c : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
{ unhide HkS. destruct HkS as [K0|K7].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x77d78%Z)) (ltac:(oD' 0x77d78%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x77f14%Z)) (ltac:(oD' 0x77f14%Z)) lS rdnLS kS.
stepiv (ltac:(oF' 0x77f18%Z)) (ltac:(oD' 0x77f18%Z)) (Z_to_bv 64 ((ps + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x77f1c%Z)) (ltac:(oD' 0x77f1c%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepov (ltac:(oF' 0x77f20%Z)) (ltac:(oD' 0x77f20%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((ps + n - 1) mod 8 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepiv (ltac:(oF' 0x77f24%Z)) (ltac:(oD' 0x77f24%Z)) (Z_to_bv 64 1) ltac:(vlit).
stepov (ltac:(oF' 0x77f28%Z)) (ltac:(oD' 0x77f28%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlR_inv. post.
- eexists. split.
+ stepb_tk (ltac:(oF' 0x77d78%Z)) (ltac:(oD' 0x77d78%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x77f14%Z)) (ltac:(oD' 0x77f14%Z)) lS rdnLS kS.
stepiv (ltac:(oF' 0x77f18%Z)) (ltac:(oD' 0x77f18%Z)) (Z_to_bv 64 ((ps + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x77f1c%Z)) (ltac:(oD' 0x77f1c%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepov (ltac:(oF' 0x77f20%Z)) (ltac:(oD' 0x77f20%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((ps + n - 1) mod 8 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepiv (ltac:(oF' 0x77f24%Z)) (ltac:(oD' 0x77f24%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepov (ltac:(oF' 0x77f28%Z)) (ltac:(oD' 0x77f28%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlR_inv. post. }
cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I11 & I12 & I8 & I19 & I2) & K1).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77f40 : word) M rom) (fun rg => qlR_post rg /\ keeps_but RIPL regs rg)).
{ destruct (Z.lt_ge_cases fS lS) as [Hfl|Hfl].
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77f30 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0x77f2c%Z)) (ltac:(oD' 0x77f2c%Z)) ltac:(cond).
apply mst_refl.
* split; [unfold qlR_inv; repeat split; assumption | exact K1].
+ cbv beta. intros r2 (I2' & K2).
destruct (qloopR_run M (Z.to_nat (lS - fS - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x77f2c%Z)) (ltac:(oD' 0x77f2c%Z)) ltac:(cond).
apply mst_refl.
+ split; [unfold qlR_post; repeat split; assumption | exact K1]. }
cbv beta. intros r4 ((J15 & J10 & J11 & J12 & J8 & J19 & J2) & K4).
eexists. split.
- stepiv (ltac:(oF' 0x77f40%Z)) (ltac:(oD' 0x77f40%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x77f44%Z)) (ltac:(oD' 0x77f44%Z)) ltac:(cond).
apply mst_refl.
- unfold cR_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
Qed.
End SE.
#[using="kS fS lS faS laS fD lD faD laD HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def Hn HappS HappD Hs HshS HshD Hok HG HI HZS HLS HkS HWS HWD"] Lemma cR_run : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "QJ&Ay5'S1yR0%211%5241'6y8%611%311p061&Or1%211&Kr4r3%3221';'9'I&QH&QCvR8r5(RO+^oY4(8%33I21/01Ir6vRL%:598321r2+^o[L%:3Q018/01Q0%?5>41I6%B3A61&N%117&Q@&Q:%231C:r7%O21Q1%K231%L271%M2:1qQ8Q71%Q02Q81qUDQ>1%Q22Q?1p0Q41p0Q91pUBQB1pQ6Q>1pUFQD1").
Proof.
hide_dj.
intros regs0 M regs P1 HFR. pose proof HFR as (HO & HGr & HR).
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
{ destruct (cRz_run M regs P1 Hn0) as (r2 & RUN2 & P2 & K2). exists r2, M.
split; [exact RUN2 | split; [exact P2 | split; [exact K2 | exact HFR]]]. }
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
Definition cW_pre (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 19 = Z_to_bv 64 (n - 65) /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Definition cW_post (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
#[using="fS lS fD lD Hn HappS HappD"] Lemma cWz_run : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "QD'S1yR0%211'6y8%511%311p051&Ay5%2218&Q2r1%211':'=vRCz%43321';'9'I&QH&QCvR8r4(RO+^o[L(8%33L21/01Lr5vRL%:598321+^o^8%93Q217/01Q2%>5=I165%A3@51&Q1%11L&Q@&Q:%231BO%H241%I271qUDQ41%L2Q51p0N1p0Q41pUBQ81pQ6Q<1").
Proof.
hide_dj.
intros M regs (H10 & H11 & H12 & H8 & H19 & H2) Hn0. pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
rewrite (zbv_wrap_up (n - 65)) in H19.
eexists. split.
- stepiv (ltac:(oF' 0x77d7c%Z)) (ltac:(oD' 0x77d7c%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
stepb_ft (ltac:(oF' 0x77d80%Z)) (ltac:(oD' 0x77d80%Z)) ltac:(cond).
stepn (ltac:(oF' 0x77d84%Z)) (ltac:(oD' 0x77d84%Z)).
stepb_tk (ltac:(oF' 0x77d88%Z)) (ltac:(oD' 0x77d88%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x77f0c%Z)) (ltac:(oD' 0x77f0c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x77f10%Z)) (ltac:(oD' 0x77f10%Z)).
apply mst_refl.
- unfold cW_post. post.
Qed.
#[using="Type"] Lemma ret_ok_78000 : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove ":&J(ROyR0+_PP0(8%43321'S1%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_cWr_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "QO&Ay5'S1yR0%211%5241'6y8%611%311p061&Q2r1%211&Kr4r3%3221&QM+R0vRC%3221';'9'I&QH&QCvR8r6(RO+^o[L(8%33M21/01Mr7vRL%:598321r2+^o^8%:3Q418/01Q4%?5>41M6%B3A61&Q1%117&Q@&Q:%231C:r8%Q321Q5%K231%L271%M2:1qQ8Q;1%Q02Q<1qUDQB1%Q22QC1p0Q41p0Q91p0Q>1pUBQG1pQ6QC1pUFQI1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_cWr_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cWr_run) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cWr_run) 2%nat 0%nat).
Lemma cWr_run : ltac:(sec_stmt2 constr:(SEC_T_cWr_run) 3%nat 0%nat).
Proof using fS lS faS laS kD fD lD faD laD HfS_def HlS_def HfD_def HlD_def Hn HappS HappD Hs HshS HshD Hok HG HI HWS HZD HLD HkD HWD regs0 M regs.
hide_dj.
intros (H10 & H11 & H12 & H8 & H19 & H2) HFR Hn64.
pose proof HFR as (HO & HGr & HR).
pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x77d7c : word) M rom) (mkst r1 (0x7ae38 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 pd /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ getr r1 1 = (0x78000 : word)
/\ getr r1 9 = Z_to_bv 64 pd /\ getr r1 21 = Z_to_bv 64 ps /\ getr r1 18 = Z_to_bv 64 n /\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepiv (ltac:(oF' 0x77d7c%Z)) (ltac:(oD' 0x77d7c%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
stepb_ft (ltac:(oF' 0x77d80%Z)) (ltac:(oD' 0x77d80%Z)) ltac:(cond).
stepn (ltac:(oF' 0x77d84%Z)) (ltac:(oD' 0x77d84%Z)).
stepb_tk (ltac:(oF' 0x77d88%Z)) (ltac:(oD' 0x77d88%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x77f0c%Z)) (ltac:(oD' 0x77f0c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x77fec%Z)) (ltac:(oD' 0x77fec%Z)) (Z_to_bv 64 pd) ltac:(wval).
stepiv (ltac:(oF' 0x77ff0%Z)) (ltac:(oD' 0x77ff0%Z)) (Z_to_bv 64 ps) ltac:(wval).
stepiv (ltac:(oF' 0x77ff4%Z)) (ltac:(oD' 0x77ff4%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x77ff8%Z)) (ltac:(oD' 0x77ff8%Z)) (Z_to_bv 64 n) ltac:(wval).
stepn (ltac:(oF' 0x77ffc%Z)) (ltac:(oD' 0x77ffc%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q9 & Q21 & Q18 & K1).
pose proof (out_agree_globs M HO) as (HGM & _).
pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2144)) (0x78000 : word) pd n (s - 2144)
ltac:(unorm; reflexivity) ltac:(lia) HappD ltac:(lia) ltac:(unfold SB in *; lia)
ltac:(replace (s - 2144 - 72)%Z with (s - 2216)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
(ret_ok_78000) HGM kD) as RP.
specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZD; [lia | unfold SB in *; lia])).
specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlD_def; apply HLD; lia) HkD).
destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
assert (S9 : getr r2 9 = Z_to_bv 64 pd) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
assert (S21 : getr r2 21 = Z_to_bv 64 ps) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
assert (S18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x78000%Z)) (ltac:(oD' 0x78000%Z)) (Z_to_bv 64 ps) ltac:(wval).
stepiv (ltac:(oF' 0x78004%Z)) (ltac:(oD' 0x78004%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x78008%Z)) (ltac:(oD' 0x78008%Z)) (Z_to_bv 64 0) ltac:(wval).
stepiv (ltac:(oF' 0x7800c%Z)) (ltac:(oD' 0x7800c%Z)) (Z_to_bv 64 pd) ltac:(wval).
stepb_tk (ltac:(oF' 0x78010%Z)) (ltac:(oD' 0x78010%Z)) ltac:(cond).
apply mst_refl.
- unfold cW_post. post.
- eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
Qed.
End SE.
Definition cWqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
getr rg 13 = Z_to_bv 64 fD /\ getr rg 14 = Z_to_bv 64 lD /\ getr rg 15 = Z_to_bv 64 (pd + n - 1) /\ getr rg 16 = Z_to_bv 64 (Z.lor u1 u0)
/\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_cWqa_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "S1'S1yR0%211'6y8%511%311p051&Ay5%2218'3%117&Q2r3%211&Q4r5%211'9&QMzvRC%3221&QK+R0%2241%8241':%J1A&QD&QHr7&S0vR6%22Q21u8%746521(0%12KF%<3;31r8vR@%:2Q:1%>4=318%A3@16&>%11?%H2K1&QO+2%221J%Q0251%Q2251';'I&QCvR8r;(RO+^o[L(8%33QM21/01QMr<vRL%:598321r1+^o^4%:3R418/01R4%?5>4176%A3Q961&Q3r:%M11r9%O11%5331;&Q@&Q:%231G>%QO241%R02;1qUDR:1%O2R;1p0Q11p0Q21p0Q;1p0QA1p0QO1p0R91p0R=1pV@RA1pV>RB1pUBRE1pQ6RI1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cWqa_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cWqa_run) 1%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_cWqa_run) 2%nat 0%nat).
Variable w1 : ltac:(sec_ty2 constr:(SEC_T_cWqa_run) 3%nat 0%nat).
Lemma cWqa_run : ltac:(sec_stmt2 constr:(SEC_T_cWqa_run) 4%nat 0%nat).
Proof using fS lS HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappS HappD Hs HshD HG HI M regs w0 w1.
hide_dj.
intros (H10 & H11 & H12 & H8 & H19 & H2) HO Hn64 R0 R1 B0 B1.
rewrite (zbv_wrap_up (n - 65)) in H19.
pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
unfold SB, HIGHEND in *.
pose proof (Z.div_mod pd 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound pd 8 ltac:(lia)) as Mp.
pose proof (Z.mod_pos_bound fD 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lD 8 ltac:(lia)) as Ml.
pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
eexists. split.
- stepiv (ltac:(oF' 0x77d7c%Z)) (ltac:(oD' 0x77d7c%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
stepb_ft (ltac:(oF' 0x77d80%Z)) (ltac:(oD' 0x77d80%Z)) ltac:(cond).
stepn (ltac:(oF' 0x77d84%Z)) (ltac:(oD' 0x77d84%Z)).
stepb_ft (ltac:(oF' 0x77d88%Z)) (ltac:(oD' 0x77d88%Z)) ltac:(cond).
stepn (ltac:(oF' 0x77d8c%Z)) (ltac:(oD' 0x77d8c%Z)).
mld (ltac:(oF' 0x77d90%Z)) (ltac:(oD' 0x77d90%Z)) (0x1343a0 : word) G1.
stepiv (ltac:(oF' 0x77d94%Z)) (ltac:(oD' 0x77d94%Z)) (Z_to_bv 64 (pd + n)) ltac:(wval).
mld (ltac:(oF' 0x77d98%Z)) (ltac:(oD' 0x77d98%Z)) (0x13ca38 : word) G2.
stepiv (ltac:(oF' 0x77d9c%Z)) (ltac:(oD' 0x77d9c%Z)) (Z_to_bv 64 (pd / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x77da0%Z)) (ltac:(oD' 0x77da0%Z)) (Z_to_bv 64 (pd + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x77da4%Z)) (ltac:(oD' 0x77da4%Z)) (Z_to_bv 64 ((pd + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x77da8%Z)) (ltac:(oD' 0x77da8%Z)) (Z_to_bv 64 fD) ltac:(wval).
stepiv (ltac:(oF' 0x77dac%Z)) (ltac:(oD' 0x77dac%Z)) (Z_to_bv 64 lD) ltac:(wval).
stepiv (ltac:(oF' 0x77db0%Z)) (ltac:(oD' 0x77db0%Z)) (Z_to_bv 64 faD)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
stepiv (ltac:(oF' 0x77db4%Z)) (ltac:(oD' 0x77db4%Z)) (Z_to_bv 64 laD)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
mldw (ltac:(oF' 0x77db8%Z)) (ltac:(oD' 0x77db8%Z)) faD R0 w0.
mldw (ltac:(oF' 0x77dbc%Z)) (ltac:(oD' 0x77dbc%Z)) laD R1 w1.
stepov (ltac:(oF' 0x77dc0%Z)) (ltac:(oD' 0x77dc0%Z)) (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
apply mst_refl.
- unfold cWqa_post. split; [post | solve_keeps_but].
Qed.
End SE.
Definition qlW_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 13 = Z_to_bv 64 (fD + i) /\ getr rg 14 = Z_to_bv 64 lD /\ getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Definition qlW_post (rg : bvmap 5 word) : Prop :=
getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = Z_to_bv 64 ps /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_qloopW_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "R='S1yR0%211'6y8%511%311p051'4&Ay5%2219'=&Q4r4%211&QMzvRC%3221&Q7r3%2281&QK%127:':&QIvR4r5%3221&QNr7%211%7241+1%9221vR>%<3I21';'9'I&QH&QCvR8r8(RO+^onD(8%33Q?21/01Q?r:vRL%:598321r1+^oo4%:3QF18/01QF%?5>4176%B3A61&Q8%117&Q@&Q:%231C:%I241%J271qUDQG1%M2QH1p0O1p0Q=1p0Q@1p0QD1p0QI1pTDQM1pUBQO1pU>R31pQ6R51")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_qloopW_run) 0%nat 0%nat).
Lemma qloopW_run : ltac:(sec_stmt2 constr:(SEC_T_qloopW_run) 1%nat 0%nat).
Proof using fS lS faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappD Hs HshD HZD M.
hide_dj.
intros q.
induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H10 & H11 & H12 & H2) Hi Hq;
pose proof (flD_facts Hn0) as (F1 & F2 & _); unfold SB in *.
- eexists. split.
+ mlbu0 (ltac:(oF' 0x77fd4%Z)) (ltac:(oD' 0x77fd4%Z)) (fD + i)%Z rdn1D.
stepiv (ltac:(oF' 0x77fd8%Z)) (ltac:(oD' 0x77fd8%Z)) (Z_to_bv 64 (fD + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x77fdc%Z)) (ltac:(oD' 0x77fdc%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_ft (ltac:(oF' 0x77fe0%Z)) (ltac:(oD' 0x77fe0%Z)) ltac:(cond).
apply mst_refl.
+ unfold qlW_post. post.
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77fd4 : word) M rom) (fun rg => qlW_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
+ eexists. split.
* mlbu0 (ltac:(oF' 0x77fd4%Z)) (ltac:(oD' 0x77fd4%Z)) (fD + i)%Z rdn1D.
stepiv (ltac:(oF' 0x77fd8%Z)) (ltac:(oD' 0x77fd8%Z)) (Z_to_bv 64 (fD + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x77fdc%Z)) (ltac:(oD' 0x77fdc%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x77fe0%Z)) (ltac:(oD' 0x77fe0%Z)) ltac:(cond).
apply mst_refl.
* unfold qlW_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
Qed.
End SE.
#[using="fS lS"] Lemma cWqf_run : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "R5'S1yR0%211'6y8%511%311p051&Ay5%2218'=&Q3r2r1r3%43321'9&QKz&QL%1286%4231&QM&QO+2+R0%3221%5271%<271':r4%<2A1%33F1>';'I&QH&QCvR8r7(RO+^o^4(8%33Q:21/01Q:r8vRL%:598321+^o^8%93Q@17/01Q@%>5=Q5165%A3@51&Q1%11Q8&Q@&Q:%231BQ;%Q9241%Q:271qUDQB1%K2QC1p0M1p0Q21p0Q@1pV:QF1pV8QG1pUBQI1pQ6QM1").
Proof.
hide_dj.
intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H2) BL E.
eexists. split.
- stepb_ft (ltac:(oF' 0x77dc4%Z)) (ltac:(oD' 0x77dc4%Z)) ltac:(cond).
apply mst_refl.
- unfold cW_post. post.
Qed.
Section SE.
Local Abbreviation SEC_T_cWqs_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "RA'S1yR0%211'6y8%511%311p051&Ay5%2218'=&Q3r2r1r3%43321&Q4r5%211'9&QMzvRC%3221&QK+R0%2241%8241&QLr4%221=%72:1&QO+2%2219%?251%A251&<':r6%<2G1%33O1D%511';'I&QH&QCvR8r9(RO+^o^4(8%33QD21/01QDr:vRL%:598321+^o^8%93QJ17/01QJ%>5=Q?165%A3@51&Q1%11QB&Q@&Q:%231BQE%Q@241%QA271qUDQL1%K2QM1p0M1p0Q41p0Q>1p0QH1p0QL1pV:R21pV8R31pUBR51pQ6R91")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cWqs_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cWqs_run) 1%nat 0%nat).
Variable u0 : ltac:(sec_ty2 constr:(SEC_T_cWqs_run) 2%nat 0%nat).
Variable u1 : ltac:(sec_ty2 constr:(SEC_T_cWqs_run) 3%nat 0%nat).
Lemma cWqs_run : ltac:(sec_stmt2 constr:(SEC_T_cWqs_run) 4%nat 0%nat).
Proof using fS lS kD faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappS HappD Hs HshD HZD HLD HkD M regs u0 u1.
hide_dj.
intros (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H2) HO Hn64 BL NE.
pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound (pd + n - 1) 8 ltac:(lia)) as Mq.
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77fd0 : word) M rom) (fun rg => qlW_inv rg 0 /\ keeps_but RIPL regs rg)).
{ unhide HkD. destruct HkD as [K0|K7].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x77dc4%Z)) (ltac:(oD' 0x77dc4%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x77fb8%Z)) (ltac:(oD' 0x77fb8%Z)) lD rdnLD kD.
stepiv (ltac:(oF' 0x77fbc%Z)) (ltac:(oD' 0x77fbc%Z)) (Z_to_bv 64 ((pd + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x77fc0%Z)) (ltac:(oD' 0x77fc0%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kD)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepov (ltac:(oF' 0x77fc4%Z)) (ltac:(oD' 0x77fc4%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((pd + n - 1) mod 8 <? kD)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepiv (ltac:(oF' 0x77fc8%Z)) (ltac:(oD' 0x77fc8%Z)) (Z_to_bv 64 1) ltac:(vlit).
stepov (ltac:(oF' 0x77fcc%Z)) (ltac:(oD' 0x77fcc%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlW_inv. post.
- eexists. split.
+ stepb_tk (ltac:(oF' 0x77dc4%Z)) (ltac:(oD' 0x77dc4%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x77fb8%Z)) (ltac:(oD' 0x77fb8%Z)) lD rdnLD kD.
stepiv (ltac:(oF' 0x77fbc%Z)) (ltac:(oD' 0x77fbc%Z)) (Z_to_bv 64 ((pd + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x77fc0%Z)) (ltac:(oD' 0x77fc0%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kD)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepov (ltac:(oF' 0x77fc4%Z)) (ltac:(oD' 0x77fc4%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((pd + n - 1) mod 8 <? kD)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepiv (ltac:(oF' 0x77fc8%Z)) (ltac:(oD' 0x77fc8%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepov (ltac:(oF' 0x77fcc%Z)) (ltac:(oD' 0x77fcc%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlW_inv. post. }
cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I11 & I12 & I2) & K1).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77fe4 : word) M rom) (fun rg => qlW_post rg /\ keeps_but RIPL regs rg)).
{ destruct (Z.lt_ge_cases fD lD) as [Hfl|Hfl].
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x77fd4 : word) M rom) (fun rg => qlW_inv rg 0 /\ keeps_but RIPL regs rg)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0x77fd0%Z)) (ltac:(oD' 0x77fd0%Z)) ltac:(cond).
apply mst_refl.
* split; [unfold qlW_inv; repeat split; assumption | exact K1].
+ cbv beta. intros r2 (I2' & K2).
destruct (qloopW_run M (Z.to_nat (lD - fD - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x77fd0%Z)) (ltac:(oD' 0x77fd0%Z)) ltac:(cond).
apply mst_refl.
+ split; [unfold qlW_post; repeat split; assumption | exact K1]. }
cbv beta. intros r4 ((J15 & J10 & J11 & J12 & J2) & K4).
eexists. split.
- stepiv (ltac:(oF' 0x77fe4%Z)) (ltac:(oD' 0x77fe4%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x77fe8%Z)) (ltac:(oD' 0x77fe8%Z)) ltac:(cond).
apply mst_refl.
- unfold cW_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
Qed.
End SE.
#[using="fS lS faS laS kD fD lD faD laD HfS_def HlS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappS HappD Hs HshS HshD Hok HG HI HWS HZD HLD HkD HWD"] Lemma cW_run : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "QJ&Ay5'S1yR0%211%5241'6y8%611%311p061&Q2r1%211&Kr4r3%3221';'9'I&QH&QCvR8r5(RO+^o[L(8%33I21/01Ir6vRL%:598321r2+^o^8%:3Q018/01Q0%?5>41I6%B3A61&Q1%117&Q@&Q:%231C:r7%O21Q1%K231%L271%M2:1qQ8Q71%Q02Q81qUDQ>1%Q22Q?1p0Q41p0Q91pUBQB1pQ6Q>1pUFQD1").
Proof.
hide_dj.
intros regs0 M regs P1 HFR. pose proof HFR as (HO & HGr & HR).
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
{ destruct (cWz_run M regs P1 Hn0) as (r2 & RUN2 & P2 & K2). exists r2, M.
split; [exact RUN2 | split; [exact P2 | split; [exact K2 | exact HFR]]]. }
destruct (Z.le_gt_cases n 64) as [Hle|Hgt].
- destruct (rdnWD M HO ltac:(lia)) as (w0 & w1 & R0 & R1 & B0 & B1).
destruct (cWqa_run M regs w0 w1 P1 HO ltac:(lia) R0 R1 B0 B1) as (r2 & RUN2 & P2 & K2).
pose proof (lor_bound64 _ _ B1 B0) as BL.
destruct (Z.eq_dec (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0)) 0) as [E|NE].
+ destruct (cWqf_run M r2 _ _ P2 BL E) as (r3 & RUN3 & P3 & K3). exists r3, M.
split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
+ destruct (cWqs_run M r2 _ _ P2 HO ltac:(lia) BL NE) as (r3 & RUN3 & P3 & K3). exists r3, M.
split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
- exact (cWr_run regs0 M regs P1 HFR Hgt).
Qed.
#[using="Type"] Lemma ret_ok_77dcc : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove ":&J(ROyR0+^o^<(8%43321'S1%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
#[local] Notation MMR M := (mm_result M (Z_to_bv 64 pd) (Z_to_bv 64 ps) bs) (only parsing).
#[using="fS lS fD lD Hn HappS HappD Hs HdjS Hover Hdst Hsrc"] Lemma mcH_M : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "L'S1yR0%211'6y8%511%311p051&Q4r1%211&QFvRBr2%3221'QGr3&S0vRD%22B1vRE%42D1vRCvR3%9585321p0;1p0@1pQ6D1").
Proof.
hide_dj.
intros M HO HGr. pose proof pS_facts as (PSp & PSn & _). pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
pose proof (rdn_length _ _ _ _ _ Hsrc) as LEN. unhide Hover.
constructor.
- lia.
- exact LEN.
- rewrite LEN. apply out_agree_src. exact HO.
- rewrite LEN. apply (store_ok_mono _ _ mem0 M _ HGr). exact Hdst.
- unorm. lia.
- unorm. lia.
- unorm. lia.
Qed.
#[using="mem0 fS lS fD lD Hn HappD Hs HdjD Hsrc"] Lemma slots_ok_mm : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "Q1&Ay5'S1yR0%211%5241'6y8%611%311p061'QGr1&S0vRD%22<1vRE%42>1vRCvR3%9585321&Q9r3r2%3221r4&Q<%145<:8%7231p051pQ>:1pQ6E1pUFK1").
Proof.
hide_dj.
intros regs0 M MC R. pose proof pD_facts as (Pp & Ppn & _). unfold HIGHEND in *.
pose proof (rdn_length _ _ _ _ _ Hsrc) as LEN. unhide HdjD.
apply (slots_ok_ext regs0 M); [|exact R]. intros x Hx. pose proof (u64_range x).
rewrite (mm_result_pw M (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs MC).
destruct (Z_lt_le_dec 0 n) as [Np|Nz]; [| first [ rewrite (proj1 (length_zero_iff_nil bs) ltac:(lia)); reflexivity | replace (Z.to_nat n) with 0%nat by lia; reflexivity ] ].
destruct (HdjD Np) as [Hd|Hd].
- apply wbytes_above. rewrite LEN. unorm. lia.
- apply wbytes_below; [rewrite LEN; unorm; lia | unorm; lia].
Qed.
Section SE.
Local Abbreviation SEC_T_c3_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "SC&Ay5'S1yR0%211%5241'6y8%611%311p061&Q1r2%211&Kr4%2214';'9'I&QH&QCvR8r5(RO+^o^8(8%33H21/01HvRL%95872?1r1vRG&Q<&S0vRD%22Q11vRE%42Q31vR3%74I421%D5C:91<%G3F<1':&QB+:%F3Q=1D%32@1%53Q<1<+2%J3QA1H%72D1vRN%:3QA21+1%O3QF1M%<2I1%>3QE1I+8%Q33QJ1Q1%@2M1r6%B213%D3QK31+9%Q93R01Q7%F2Q31%G262%I3R021+B%Q>3R51Q<%K2Q81%L2;2%N3R521+C%QC3R:1QA%Q02Q=1%Q12@2%Q33R:21+D%QH3R?1QF%Q52QB1%Q62E2%Q83R?21+E%QM3RD1QK%Q:2QG1%Q;2J2%Q=3RD21+F%R23RI1R0%Q?2QL1%Q@2O2%QB3RI21&Q@&Q:%231R9R1%R?241%R@2:1%RA2@1%RB2F1%RC2L1%RD2Q21%RE2Q81%RF2Q?1%RG2QD1%RH2QJ1%RI2R11qUDS71%RL2S81p0RN1p0S21pQ6S61pUBS<1pUFS=1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c3_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c3_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_c3_run) 2%nat 0%nat).
Lemma c3_run : ltac:(sec_stmt2 constr:(SEC_T_c3_run) 3%nat 0%nat).
Proof using fS lS faS laS fD lD faD laD Hs_def Hn HappS HappD Hs HdjS HdjD Hover Hdst Hsrc Hret HWS HWD regs0 regs M.
hide_dj.
intros (H10 & H11 & H12 & H2) (HO & HGr & HR).
pose proof pS_facts as (PSp & PSn & _). pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
pose proof (mcH_M M HO HGr) as MC.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x77dc8 : word) M rom) (mkst r1 (0x8ad80 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 pd /\ getr r1 11 = Z_to_bv 64 ps /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = (0x77dcc : word)
/\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepn (ltac:(oF' 0x77dc8%Z)) (ltac:(oD' 0x77dc8%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & Q2 & K1).
destruct (int_memmove_run M (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs rom MC ltac:(lia) r1 (0x77dcc : word) ret_ok_77dcc Q1 Q10 Q11 Q12) as (r2 & RUN2 & KP).
pose proof (slots_ok_mm regs0 M MC HR) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
assert (V2 : getr r2 2 = Z_to_bv 64 (s - 2144)) by (rewrite (KP 2%bv) by (cbv; tauto); exact Q2).
assert (V10 : getr r2 10 = Z_to_bv 64 pd) by (rewrite (KP 10%bv) by (cbv; tauto); exact Q10).
eexists. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x77dcc%Z)) (ltac:(oD' 0x77dcc%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepld (ltac:(oF' 0x77dd0%Z)) (ltac:(oD' 0x77dd0%Z)) ra ltac:(maddr (s - 8)%Z; exact R1).
stepld (ltac:(oF' 0x77dd4%Z)) (ltac:(oD' 0x77dd4%Z)) (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
stepld (ltac:(oF' 0x77dd8%Z)) (ltac:(oD' 0x77dd8%Z)) (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
stepld (ltac:(oF' 0x77ddc%Z)) (ltac:(oD' 0x77ddc%Z)) (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
stepld (ltac:(oF' 0x77de0%Z)) (ltac:(oD' 0x77de0%Z)) (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
stepld (ltac:(oF' 0x77de4%Z)) (ltac:(oD' 0x77de4%Z)) (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
stepld (ltac:(oF' 0x77de8%Z)) (ltac:(oD' 0x77de8%Z)) (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).
stepld (ltac:(oF' 0x77dec%Z)) (ltac:(oD' 0x77dec%Z)) (getr regs0 22) ltac:(maddr (s - 64)%Z; exact R8).
stepiv (ltac:(oF' 0x77df0%Z)) (ltac:(oD' 0x77df0%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x77df4%Z)) (ltac:(oD' 0x77df4%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity; [exact V10 | symmetry; apply sp_s |].
eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; apply keeps_keeps_cs; exact KP|]. solve_keeps_but.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_asan_memmove_run := (ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "S2&Ay5'S1yR0%211%5241':&QBr1(RO+:(8%33;21%6251&S0vRD%22=1%;3=41r2+;%;3C19%>231vRE%92D1%B3D31r3+<%B3J1@%E231vRC%@2K1%I3K31r4+2%I3Q11G%L231vRN%O3Q121r5+1%O3Q71M%Q2231vRG%Q53Q721';'6y8%Q=11%311p0Q=1'9'I&QH&QCvR8r8+^oW8%Q@3QF1Q>/01QFvRBvRL%8576321&Q<vR3%24QHQ@Q91%<5;Q?G15%?3>51%QL2QAQG%QN3R01QD%QN2QCQ3%R03R21Q2%R02QEO%R23R41N&QE%12CQH&Q4%11R4&QF%12CR6'QG%15R8R0QIQCA%O231%Q0261%Q1291%Q22<1%Q32?1%Q42B1%Q52E1qQ@Q71%Q=2Q81qUDRE1%Q?2RF1p0QA1p0QH1p0QO1p0R71p0R?1pUBRL1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_asan_memmove_run) 0%nat 0%nat).
Theorem asan_memmove_run : ltac:(sec_stmt2 constr:(SEC_T_asan_memmove_run) 1%nat 0%nat).
Proof using kS fS lS faS laS kD fD lD faD laD Hs_def HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def HfaD_def HlaD_def Hn HappS HappD Hs HshS HshD HdjS HdjD Hover Hok Hdst Hsrc Hret HG HI HZS HLS HkS HWS HZD HLD HkD HWD regs.
hide_dj.
intros H10 H11 H12 H2 H1.
destruct (c1_run regs H10 H11 H12 H2 H1) as (r1 & RUN1 & P1 & K1).
destruct (cR_run regs (M9 regs) r1 P1 (M9_FR regs)) as (r2 & M2 & RUN2 & P2 & K2 & F2).
destruct (cW_run regs M2 r2 P2 F2) as (r3 & M3 & RUN3 & P3 & K3 & F3).
destruct (c3_run regs r3 M3 P3 F3) as (r4 & RUN4 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & K4).
exists r4, M3. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
- assert (KB : keeps_but RIPL regs r4).
{ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. eapply keeps_but_trans; [exact K3|]. exact K4. }
destruct F3 as (HO & HGr & _). pose proof (mcH_M M3 HO HGr) as MC3.
split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [| split; [exact HO | split; [exact HGr | exact MC3]]].
intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1, H1; reflexivity|].
destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|]. destruct (decide (r = 19%bv)) as [->|N19]; [exact Q19|].
destruct (decide (r = 20%bv)) as [->|N20]; [exact Q20|]. destruct (decide (r = 21%bv)) as [->|N21]; [exact Q21|].
destruct (decide (r = 22%bv)) as [->|N22]; [exact Q22|].
apply KB; [exact Hr|]. cbv. intuition congruence.
Qed.
End SE.
#[using="Type"] Corollary asan_memmove_result_pw : ltac2:(TCodec.tc2 tcn__Jb0AsanMemmove "L'S1yR0%211'6y8%511%311p051'QGr2&S0vRD%22;1vRE%42=1vRCvR3%9585321':&Q<r3%251975<&H%143;7>%63B31p081pVBH1pQ@D1").
Proof. hide_dj. intros Mj x MC. apply (mm_result_pw _ _ _ _ _ MC). Qed.
End AMM.
End FPX_1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit MemsetLib As0StepLib Jb0MemIsZero Jb0RegionPoisoned Jb0AsanMemset Jb0AsanMemcpy.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Jb0SumsMemset_code Jb0SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0MemsetIcpt () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0AsanMemset."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0MemsetIcpt.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0MemsetIcpt.FPX_1.AMSI."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3repeat"; "4Z"; "0L"]; ["5bytes_le_to_Z"; "6store_ok"; "6word_to_le_bytes"; "7bvmap"; "0M"; "0M'"; "0M1"; "0M2"; "0Mj"; "8wbytes"; "9msteps"; ":ret_ok"; ";ms_icpt_globs"; "=FR"; "=M9"; "=c1_post"]; ["=cW_post"; "=cW_pre"; "=cWqa_post"; "=out_agree"; "=qlW_inv"; "=qlW_post"; "=slots_ok"; "<RIPL"; ">HIGHEND"; ">SB"; ">frame_only"; ">keeps_but"; ">rt_layout_globs"; "?cbyte"; "?ms_agree"; "@getr"]; ["@mkst"; "@rdn"; "Akeeps_cs"; "Bmem_grows"; "Cloaded_segments"; "Dadd"; "Ddiv"; "Dle"; "Dlor"; "Dlt"; "Dof_nat"; "Dpow"; "Dsub"; "Dto_nat"; "0a"; "0cv"]; ["0fD"; "0faD"; "0fx"; "0i"; "0j"; "0k"; "0kD"; "0lD"; "0laD"; "0mem0"; "0n"; "0pd"; "0q"; "0r1"; "0r2"; "0ra"]; ["0regs"; "0regs'"; "0regs0"; "0rg"; "0rom"; "0s"; "0sp"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0u0"; "0u1"; "0v"; "0w0"; "0w1"]; ["0x"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
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
#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv.
Section AMSI.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra cv : word.
Variables pd n s : Z.
Variables kD fD lD faD laD : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis HfD_def : fD = (SB + pd / 8)%Z. Hypothesis HlD_def : lD = (SB + (pd + n - 1) / 8)%Z.
Hypothesis HfaD_def : faD = (fD - fD mod 8)%Z. Hypothesis HlaD_def : laD = (lD - lD mod 8)%Z.
Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
Hypothesis HappD : in_app8 pd n.
Hypothesis Hs : (0x1000000 <= s - 2216)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis HshD : (lD + 8 <= s - 2216)%Z.
Hypothesis HdjD : (0 < n -> pd + n <= s - 2216 \/ s <= pd)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2216)) 2216%nat = true.
Hypothesis Hdst : store_ok ASEGS mem0 (Z_to_bv 64 pd) (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : rt_layout_globs mem0.
Hypothesis HI : ms_icpt_globs mem0.
Hypothesis HZD : (0 < n)%Z -> forall x : word, (fD <= bv_unsigned x < lD)%Z -> mem0 x = Some (Z_to_bv 8 0).
Hypothesis HLD : (0 < n)%Z -> mem0 (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD).
Hypothesis HkD : kD = 0%Z \/ ((pd + n - 1) mod 8 < kD <= 7)%Z.
Hypothesis HWD : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faD) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laD) 8%nat = Some w1.
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (rewrite (zbv_wrap_up (n - 65)); f_equal; lia); try solve_keeps_but.
#[local] Ltac hide_dj := try hide HdjD; try hide HkD; try hide HappD.
Lemma sp_s : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "9':'RIyR0%211vRF&RHvRE%2251%83541"). Proof. hide_dj. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma pD_facts : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "N'9&QGzvR;%3221&QEvR:%2241+8%4221&Q8%:221&QF%12:5%=2<1%>225%@221&QI%12@<&QL+1%22>1%:21>%F2:1%G22>%I221p081%K2;1%L2A1%M2I1").
Proof.
hide_dj.
unhide HappD.
unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappD as [[H1 H2]|[H1 H2]];
(repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
Qed.
Lemma pS_facts : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "N'9&QGzvR;%3221&QEvR:%2241+8%4221&Q8%:221&QF%12:5%=2<1%>225%@221&QI%12@<&QL+1%22>1%:21>%F2:1%G22>%I221p081%K2;1%L2A1%M2I1").
Proof. hide_dj. exact pD_facts. Qed.
Lemma flD_facts : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "Q3&QIzvR:%3221'9&QG&Q9vR0%3221vR7%5231%7231&QE+8%2251&QLvRE+RU8%3221%>251+7%62>1vR1%B221%C22A%E221%;2A6vR8%G221%H22D%J221%K261%L2=1%M2F1p0O1").
Proof.
hide_dj.
intros Hn0. pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound fD 8 ltac:(lia)). pose proof (Z.mod_pos_bound lD 8 ltac:(lia)). repeat split; lia.
Qed.
Definition out_agree (M : word -> option byte) : Prop :=
forall x : word, (bv_unsigned x < s - 2216 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
Lemma out_agree_refl : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "3&Q3vR9%211"). Proof. hide_dj. intros x _. reflexivity. Qed.
Lemma out_agree_w : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "Q5'RIyR0%211'6y8%511%311p051'>&Q3r3%211'9&QG+8%2215+RU8%4271%6231&Ir5&RH&QLvREr4%3221%52I1&Bu8%221C%;3:41%F11p0>1p0F1pULQ01pT<K1pQ:M1").
Proof.
hide_dj.
intros M k v HF Hk x Hx. pose proof (u64_range x).
destruct Hx as [Hx|Hx].
- rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
- rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
Lemma out_agree_rdn : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "Q:'RIyR0%211'6y8%511%311p051'4&Q3r3%211&QG&QE&RJ%12>5&QJr2%211%6241&QLvRE+RU8%3221%<251':'3%11F%I11&QA&QDr5r4%44321GvR9%64513I%;3831p0=1p0K1pT<O1pSNQ61pQ:Q21").
Proof. hide_dj. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
Lemma out_agree_globs : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "D'RIyR0%211'6y8%511%311p051&Q3r1%211'9&Q<r2%211&L%113%6231p081pQ:<1").
Proof.
hide_dj.
intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). destruct HI as (I1 & I2 & I3).
unfold rt_layout_globs, ms_icpt_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
repeat split; assumption.
Qed.
Section SE.
Local Abbreviation SEC_T_out_agree_store_ok := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "Q:'RIyR0%211'6y8%511%311p051'>'4&QCvR9r3%3221'9&QG&QJr2%211%4217+RU8%6291%8231':'1&A&QDr5&RH&QLvREr4%3221%52Q01%94871F(7%=3<21p0?1p0I1pT:N1pT<Q01pQ:Q21")) (only parsing).
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
Lemma M9_out_agree : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "<&Cy5'RIyR0%211%5241&Q3&Nr1%211%411pU861"). Proof. hide_dj. intros rg. unfold M9. oagree. Qed.
Lemma M9_grows : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "=&Cy5'RIyR0%211%5241&QCvR9&Nr1%211%5241pU871"). Proof. hide_dj. intros rg. unfold M9. grows. Qed.
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
Local Abbreviation SEC_T_M9_FR := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "<&Cy5'RIyR0%211%5241&Mr1&N%112%4231pU661")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_M9_FR) 0%nat 0%nat).
Lemma M9_FR : ltac:(sec_stmt2 constr:(SEC_T_M9_FR) 1%nat 0%nat).
Proof.
hide_dj. split; [apply M9_out_agree | split; [apply M9_grows|]]. unfold M9. repeat split; slot. Qed.
End SE.
Lemma rdn_slot_ext : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "QE'RIyR0%211'6y8%511%311p051'>'9&QG&QLvRE+RS0%3221&RJr1%22@1%8241&QI%1238%<231':r5r2%211r4%113%63F31p081pV2L1+8%F218%G29D%I221'3%11O%Q211&QA&QD&RHr3%O2N1%32Q:1u8%746F21%847D32%I3:21p0>1p0C1pT<Q:1pQ@Q<1pQ>Q=1").
Proof.
hide_dj.
intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
Qed.
Lemma slots_ok_ext : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "Q:&Cy5'RIyR0%211%5241'6y8%611%311p061'9&QG&QLvRE+RS0%3221&RJr1%22@1%8241&QI%1238%<231':r3r2%211r4%113%63E31p081pV2L1&Q6%1269r5%321;p031p061pQ@M1pQ>N1pU6Q41").
Proof.
hide_dj.
intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8). unfold slots_ok.
rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
Qed.
Lemma FR_region : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "Q0&Cy5'RIyR0%211%5241'6y8%611%311p061&Mr3r2%3221&Q:&QLvRE+RS0%3221%53817&QCr4%221;r6%>213p031p071p0>1pQ<C1pQ:D1pU6J1").
Proof.
hide_dj.
intros regs0 M M' (O & G & R) HF HGr. split; [|split].
- intros x Hx. rewrite (HF x) by lia. apply O. exact Hx.
- eapply mem_grows_trans; [exact G | exact HGr].
- apply (slots_ok_ext regs0 M M'); [|exact R]. intros x Hx. apply HF. lia.
Qed.
Lemma rdnWD : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "R0'RIyR0%211'6y8%511%311p051&Q3r1%211'9&QIzvR:%3221&QG+R0%2241%8241';'3%11A':%E12&QA&QDr5&RHvR1%22M1u8%746521(0r2%22=1%=3<41vR8%:2Q51%>4=<18%72BO%B3A21&@%119%L2O1&QK+2%221N%Q4251%Q6251%81Q9%Q32Q61%Q8225%Q:221%Q;251%Q<2>1%Q=2D1qV0Q31%Q62Q41qUNQ51%Q82Q61p0Q:1p0QD1pQ:QH1").
Proof.
hide_dj.
intros M HO Hn64. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
destruct (HWD Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
Qed.
Lemma rdn1D : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "QA'RIyR0%211'6y8%511%311p051'>&Q3r2%211&QIzvR:%3221'9&QGvR0r3%3221vR7%:231%7231':'3%11E%H11&QA&QDr5&RHr4%22Q01u1%746521(0(2%72Q2I(5%11Q3%43Q431%62@1%C3@81p0E1p0N1p0Q31pV4Q71pQ:Q91").
Proof.
hide_dj.
intros M z HO Hn0 Hz. pose proof (flD_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZD Hn0) by (unorm; lia). reflexivity.
Qed.
Lemma rdnLD : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "Q='RIyR0%211'6y8%511%311p051'>&Q3r2%211&QIzvR:%3221':r3vR7%33;21'3%11@%C11&QA&QDr5&RHr4%22K1u1%746521(0(2vR6%82N1(5%11O%53Q031%72A1%G3A91p0E1p0J1p0O1pV4Q31pQ:Q51").
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
getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_c1_run := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "R>&Cy5'RIyR0%211%5241':&Q?r1(RG+:(8%33;21%6251&RHvR;%22=1%;3=41r2+;%;3C19%>231vQO%A3C21r3+<%A3I1?%D231vR:%?2J1%H3J31r4+2%H3Q01F%K231vRF%N3Q021r5+1%N3Q61L%Q1231vR?%Q43Q621';'9'J&QD&Q@vR2r7+_PRH%Q:3Q@1Q8/01Q@vR9vRD%8576321+_PTD%Q@3QF1Q>/01QF&N%11;%>5=QE317%A3@71&O%11QH&Q;&Q7%231BQK%H241%I271qU4R11%L2R21p0N1p0Q51p0Q<1p0QD1p0QK1pU2R81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c1_run) 0%nat 0%nat).
Lemma c1_run : ltac:(sec_stmt2 constr:(SEC_T_c1_run) 1%nat 0%nat).
Proof.
hide_dj.
intros H10 H11 H12 H2 H1.
rewrite sp_s in H2.
pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
pose proof (out_agree_globs (M9 regs) (M9_out_agree regs)) as (_ & (I1 & I2 & I3)).
unfold M9 in *.
eexists. split.
- stepiv (ltac:(oF' 0x78058%Z)) (ltac:(oD' 0x78058%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepsd (ltac:(oF' 0x7805c%Z)) (ltac:(oD' 0x7805c%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(fsok).
stepsd (ltac:(oF' 0x78060%Z)) (ltac:(oD' 0x78060%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).
stepsd (ltac:(oF' 0x78064%Z)) (ltac:(oD' 0x78064%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).
stepsd (ltac:(oF' 0x78068%Z)) (ltac:(oD' 0x78068%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).
stepsd (ltac:(oF' 0x7806c%Z)) (ltac:(oD' 0x7806c%Z)) (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).
stepsd (ltac:(oF' 0x78070%Z)) (ltac:(oD' 0x78070%Z)) (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).
stepsd (ltac:(oF' 0x78074%Z)) (ltac:(oD' 0x78074%Z)) (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).
stepsd (ltac:(oF' 0x78078%Z)) (ltac:(oD' 0x78078%Z)) (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(fsok).
stepiv (ltac:(oF' 0x7807c%Z)) (ltac:(oD' 0x7807c%Z)) (Z_to_bv 64 s) ltac:(wval).
stepiv (ltac:(oF' 0x78080%Z)) (ltac:(oD' 0x78080%Z)) (Z_to_bv 64 (s - 2144)) ltac:(wval).
stepn (ltac:(oF' 0x78084%Z)) (ltac:(oD' 0x78084%Z)).
mld (ltac:(oF' 0x78088%Z)) (ltac:(oD' 0x78088%Z)) (0x134f08 : word) I1.
mlbu (ltac:(oF' 0x7808c%Z)) (ltac:(oD' 0x7808c%Z)) (0x13d719 : word) I2.
stepb_ft (ltac:(oF' 0x78090%Z)) (ltac:(oD' 0x78090%Z)) ltac:(cond).
apply mst_refl.
- unfold c1_post. post.
Qed.
End SE.
Definition cW_pre (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
/\ getr rg 2 = Z_to_bv 64 (s - 2144).
Definition cW_post (rg : bvmap 5 word) : Prop :=
getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_cWz_run := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "QD'RIyR0%211'6y8%511%311p051&Cy5%2218&Q1r1%211':'>vR:z%43321';'9'J&QD&Q@vR2r4(RG+_PTD(8%33L21/01Lr5vRD%:598321+_PW<%93Q217/01Q2%>5=I165%A3@51&Q0%11L&Q;&Q7%231BO%H241%I271qU4Q41%L2Q51p0N1p0Q41pU2Q81pQ:Q<1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cWz_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cWz_run) 1%nat 0%nat).
Lemma cWz_run : ltac:(sec_stmt2 constr:(SEC_T_cWz_run) 2%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H11 & H12 & H8 & H2) Hn0.
pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
eexists. split.
- stepiv (ltac:(oF' 0x78094%Z)) (ltac:(oD' 0x78094%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
stepiv (ltac:(oF' 0x78098%Z)) (ltac:(oD' 0x78098%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x7809c%Z)) (ltac:(oD' 0x7809c%Z)) (Z_to_bv 64 (s - 2136)) ltac:(wval).
stepb_ft (ltac:(oF' 0x780a0%Z)) (ltac:(oD' 0x780a0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x780a4%Z)) (ltac:(oD' 0x780a4%Z)) (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x780a8%Z)) (ltac:(oD' 0x780a8%Z)).
stepb_tk (ltac:(oF' 0x780ac%Z)) (ltac:(oD' 0x780ac%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x781fc%Z)) (ltac:(oD' 0x781fc%Z)) ltac:(cond).
stepn (ltac:(oF' 0x78200%Z)) (ltac:(oD' 0x78200%Z)).
apply mst_refl.
- unfold cW_post. post.
Qed.
End SE.
Lemma ret_ok_7824c : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt ":&K(RGyR0+_Pb<(8%43321'RI%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_cWr_run := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "QO&Cy5'RIyR0%211%5241'6y8%611%311p061&Q1r1%211&Mr4r3%3221&QI+R0vR:%3221';'9'J&QD&Q@vR2r6(RG+_PTD(8%33M21/01Mr7vRD%:598321r2+_PW<%:3Q418/01Q4%?5>41M6%B3A61&Q0%117&Q;&Q7%231C:r8%Q321Q5%K231%L271%M2:1qQ<Q;1%Q02Q<1qU4QB1%Q22QC1p0Q41p0Q91p0Q>1pU2QG1pQ:QC1pU6QI1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_cWr_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cWr_run) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cWr_run) 2%nat 0%nat).
Lemma cWr_run : ltac:(sec_stmt2 constr:(SEC_T_cWr_run) 3%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H11 & H12 & H8 & H2) HFR Hn64.
pose proof HFR as (HO & HGr & HR).
pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x78094 : word) M rom) (mkst r1 (0x7ae38 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 pd /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ getr r1 1 = (0x7824c : word)
/\ getr r1 9 = Z_to_bv 64 pd /\ getr r1 22 = cv /\ getr r1 18 = Z_to_bv 64 n /\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepiv (ltac:(oF' 0x78094%Z)) (ltac:(oD' 0x78094%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
stepiv (ltac:(oF' 0x78098%Z)) (ltac:(oD' 0x78098%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x7809c%Z)) (ltac:(oD' 0x7809c%Z)) (Z_to_bv 64 (s - 2136)) ltac:(wval).
stepb_ft (ltac:(oF' 0x780a0%Z)) (ltac:(oD' 0x780a0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x780a4%Z)) (ltac:(oD' 0x780a4%Z)) (Z_to_bv 64 (n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepn (ltac:(oF' 0x780a8%Z)) (ltac:(oD' 0x780a8%Z)).
stepb_tk (ltac:(oF' 0x780ac%Z)) (ltac:(oD' 0x780ac%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x781fc%Z)) (ltac:(oD' 0x781fc%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x78238%Z)) (ltac:(oD' 0x78238%Z)) (Z_to_bv 64 pd) ltac:(wval).
stepiv (ltac:(oF' 0x7823c%Z)) (ltac:(oD' 0x7823c%Z)) cv ltac:(gres; rwH; apply v_addi_0).
stepiv (ltac:(oF' 0x78240%Z)) (ltac:(oD' 0x78240%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x78244%Z)) (ltac:(oD' 0x78244%Z)) (Z_to_bv 64 n) ltac:(wval).
stepn (ltac:(oF' 0x78248%Z)) (ltac:(oD' 0x78248%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q9 & Q22 & Q18 & K1).
pose proof (out_agree_globs M HO) as (HGM & _).
pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2144)) (0x7824c : word) pd n (s - 2144)
ltac:(unorm; reflexivity) ltac:(lia) HappD ltac:(lia) ltac:(unfold SB in *; lia)
ltac:(replace (s - 2144 - 72)%Z with (s - 2216)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
(ret_ok_7824c) HGM kD) as RP.
specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZD; [lia | unfold SB in *; lia])).
specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlD_def; apply HLD; lia) HkD).
destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
assert (S9 : getr r2 9 = Z_to_bv 64 pd) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
assert (S22 : getr r2 22 = cv) by (rewrite (K2 22%bv) by (cbv; tauto); exact Q22).
assert (S18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x7824c%Z)) (ltac:(oD' 0x7824c%Z)) cv ltac:(gres; rwH; apply v_addi_0).
stepiv (ltac:(oF' 0x78250%Z)) (ltac:(oD' 0x78250%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x78254%Z)) (ltac:(oD' 0x78254%Z)) (Z_to_bv 64 0) ltac:(wval).
stepiv (ltac:(oF' 0x78258%Z)) (ltac:(oD' 0x78258%Z)) (Z_to_bv 64 pd) ltac:(wval).
stepb_tk (ltac:(oF' 0x7825c%Z)) (ltac:(oD' 0x7825c%Z)) ltac:(cond).
apply mst_refl.
- unfold cW_post. post.
- eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
Qed.
End SE.
Definition cWqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
getr rg 13 = Z_to_bv 64 fD /\ getr rg 14 = Z_to_bv 64 lD /\ getr rg 15 = Z_to_bv 64 (pd + n - 1) /\ getr rg 16 = Z_to_bv 64 (Z.lor u1 u0)
/\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_cWqa_run := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "S1'RIyR0%211'6y8%511%311p051&Cy5%2218'3%117&Q1r3%211&Q3r5%211'9&QIzvR:%3221&QG+R0%2241%8241':%J1A&QA&QDr7&RHvR1%22Q21u8%746521(0%12KF%<3;31r8vR8%:2Q:1%>4=318%A3@16&@%11?%H2K1&QK+2%221J%Q0251%Q2251';'J&Q@vR2r;(RG+_PTD(8%33QM21/01QMr<vRD%:598321r1+_PW8%:3R418/01R4%?5>4176%A3Q961&Q2r:%M11r9%O11%5331;&Q;&Q7%231G>%QO241%R02;1qU4R:1%O2R;1p0Q11p0Q21p0Q;1p0QA1p0QO1p0R91p0R=1pV0RA1pUNRB1pU2RE1pQ:RI1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cWqa_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cWqa_run) 1%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_cWqa_run) 2%nat 0%nat).
Variable w1 : ltac:(sec_ty2 constr:(SEC_T_cWqa_run) 3%nat 0%nat).
Lemma cWqa_run : ltac:(sec_stmt2 constr:(SEC_T_cWqa_run) 4%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H11 & H12 & H8 & H2) HO Hn64 R0 R1 B0 B1.
pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
unfold SB, HIGHEND in *.
pose proof (Z.div_mod pd 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound pd 8 ltac:(lia)) as Mp.
pose proof (Z.mod_pos_bound fD 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lD 8 ltac:(lia)) as Ml.
pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
eexists. split.
- stepiv (ltac:(oF' 0x78094%Z)) (ltac:(oD' 0x78094%Z)) (Z_to_bv 64 (2 ^ 64 - 1 - pd)) ltac:(xval).
stepiv (ltac:(oF' 0x78098%Z)) (ltac:(oD' 0x78098%Z)) (Z_to_bv 64 (s - 2048)) ltac:(wval).
stepiv (ltac:(oF' 0x7809c%Z)) (ltac:(oD' 0x7809c%Z)) (Z_to_bv 64 (s - 2136)) ltac:(wval).
stepb_ft (ltac:(oF' 0x780a0%Z)) (ltac:(oD' 0x780a0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x780a4%Z)) (ltac:(oD' 0x780a4%Z)) (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
stepn (ltac:(oF' 0x780a8%Z)) (ltac:(oD' 0x780a8%Z)).
stepb_ft (ltac:(oF' 0x780ac%Z)) (ltac:(oD' 0x780ac%Z)) ltac:(cond).
stepn (ltac:(oF' 0x780b0%Z)) (ltac:(oD' 0x780b0%Z)).
mld (ltac:(oF' 0x780b4%Z)) (ltac:(oD' 0x780b4%Z)) (0x1343a0 : word) G1.
stepiv (ltac:(oF' 0x780b8%Z)) (ltac:(oD' 0x780b8%Z)) (Z_to_bv 64 (pd + n)) ltac:(wval).
mld (ltac:(oF' 0x780bc%Z)) (ltac:(oD' 0x780bc%Z)) (0x13ca38 : word) G2.
stepiv (ltac:(oF' 0x780c0%Z)) (ltac:(oD' 0x780c0%Z)) (Z_to_bv 64 (pd / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x780c4%Z)) (ltac:(oD' 0x780c4%Z)) (Z_to_bv 64 (pd + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x780c8%Z)) (ltac:(oD' 0x780c8%Z)) (Z_to_bv 64 ((pd + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x780cc%Z)) (ltac:(oD' 0x780cc%Z)) (Z_to_bv 64 fD) ltac:(wval).
stepiv (ltac:(oF' 0x780d0%Z)) (ltac:(oD' 0x780d0%Z)) (Z_to_bv 64 lD) ltac:(wval).
stepiv (ltac:(oF' 0x780d4%Z)) (ltac:(oD' 0x780d4%Z)) (Z_to_bv 64 faD)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
stepiv (ltac:(oF' 0x780d8%Z)) (ltac:(oD' 0x780d8%Z)) (Z_to_bv 64 laD)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
mldw (ltac:(oF' 0x780dc%Z)) (ltac:(oD' 0x780dc%Z)) faD R0 w0.
mldw (ltac:(oF' 0x780e0%Z)) (ltac:(oD' 0x780e0%Z)) laD R1 w1.
stepov (ltac:(oF' 0x780e4%Z)) (ltac:(oD' 0x780e4%Z)) (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
apply mst_refl.
- unfold cWqa_post. split; [post | solve_keeps_but].
Qed.
End SE.
Definition qlW_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 13 = Z_to_bv 64 (fD + i) /\ getr rg 14 = Z_to_bv 64 lD /\ getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Definition qlW_post (rg : bvmap 5 word) : Prop :=
getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 pd /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144).
Section SE.
Local Abbreviation SEC_T_qloopW_run := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "R='RIyR0%211'6y8%511%311p051'4&Cy5%2219'>&Q3r4%211&QIzvR:%3221&Q4r3%2281&QG%127:':&QEvR0r5%3221&QJr7%211%7241+1%9221vR7%<3I21';'9'J&QD&Q@vR2r8(RG+_Pa0(8%33Q?21/01Q?r:vRD%:598321r1+_Pa@%:3QF18/01QF%?5>4176%B3A61&Q5%117&Q;&Q7%231C:%I241%J271qU4QG1%M2QH1p0O1p0Q=1p0Q@1p0QD1p0QI1pT8QM1pU2QO1pTJR31pQ:R51")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_qloopW_run) 0%nat 0%nat).
Lemma qloopW_run : ltac:(sec_stmt2 constr:(SEC_T_qloopW_run) 1%nat 0%nat).
Proof.
hide_dj.
intros q.
induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H10 & H11 & H12 & H2) Hi Hq;
pose proof (flD_facts Hn0) as (F1 & F2 & _); unfold SB in *.
- eexists. split.
+ mlbu0 (ltac:(oF' 0x78220%Z)) (ltac:(oD' 0x78220%Z)) (fD + i)%Z rdn1D.
stepiv (ltac:(oF' 0x78224%Z)) (ltac:(oD' 0x78224%Z)) (Z_to_bv 64 (fD + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x78228%Z)) (ltac:(oD' 0x78228%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_ft (ltac:(oF' 0x7822c%Z)) (ltac:(oD' 0x7822c%Z)) ltac:(cond).
apply mst_refl.
+ unfold qlW_post. post.
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x78220 : word) M rom) (fun rg => qlW_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
+ eexists. split.
* mlbu0 (ltac:(oF' 0x78220%Z)) (ltac:(oD' 0x78220%Z)) (fD + i)%Z rdn1D.
stepiv (ltac:(oF' 0x78224%Z)) (ltac:(oD' 0x78224%Z)) (Z_to_bv 64 (fD + i + 1)) ltac:(wval).
stepov (ltac:(oF' 0x78228%Z)) (ltac:(oD' 0x78228%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x7822c%Z)) (ltac:(oD' 0x7822c%Z)) ltac:(cond).
apply mst_refl.
* unfold qlW_inv. post.
+ cbv beta. intros r1 (I1 & K1).
destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
Qed.
End SE.
Lemma cWqf_run : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "R5'RIyR0%211'6y8%511%311p051&Cy5%2218'>&Q2r2r1r3%43321'9&QGz&QH%1286%4231&QI&QK+2+R0%3221%5271%<271':r4%<2A1%33F1>';'J&QD&Q@vR2r7(RG+_PW8(8%33Q:21/01Q:r8vRD%:598321+_PW<%93Q@17/01Q@%>5=Q5165%A3@51&Q0%11Q8&Q;&Q7%231BQ;%Q9241%Q:271qU4QB1%K2QC1p0M1p0Q21p0Q@1pUJQF1pUHQG1pU2QI1pQ:QM1").
Proof.
hide_dj.
intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H2) BL E.
eexists. split.
- stepb_ft (ltac:(oF' 0x780e8%Z)) (ltac:(oD' 0x780e8%Z)) ltac:(cond).
apply mst_refl.
- unfold cW_post. post.
Qed.
Section SE.
Local Abbreviation SEC_T_cWqs_run := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "RA'RIyR0%211'6y8%511%311p051&Cy5%2218'>&Q2r2r1r3%43321&Q3r5%211'9&QIzvR:%3221&QG+R0%2241%8241&QHr4%221=%72:1&QK+2%2219%?251%A251&<':r6%<2G1%33O1D%511';'J&QD&Q@vR2r9(RG+_PW8(8%33QD21/01QDr:vRD%:598321+_PW<%93QJ17/01QJ%>5=Q?165%A3@51&Q0%11QB&Q;&Q7%231BQE%Q@241%QA271qU4QL1%K2QM1p0M1p0Q41p0Q>1p0QH1p0QL1pUJR21pUHR31pU2R51pQ:R91")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cWqs_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_cWqs_run) 1%nat 0%nat).
Variable u0 : ltac:(sec_ty2 constr:(SEC_T_cWqs_run) 2%nat 0%nat).
Variable u1 : ltac:(sec_ty2 constr:(SEC_T_cWqs_run) 3%nat 0%nat).
Lemma cWqs_run : ltac:(sec_stmt2 constr:(SEC_T_cWqs_run) 4%nat 0%nat).
Proof.
hide_dj.
intros (H13 & H14 & HL' & H15 & H10 & H11 & H12 & H2) HO Hn64 BL NE.
pose proof pD_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
pose proof (flD_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
pose proof (Z.mod_pos_bound (pd + n - 1) 8 ltac:(lia)) as Mq.
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7821c : word) M rom) (fun rg => qlW_inv rg 0 /\ keeps_but RIPL regs rg)).
{ unhide HkD. destruct HkD as [K0|K7].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x780e8%Z)) (ltac:(oD' 0x780e8%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x78204%Z)) (ltac:(oD' 0x78204%Z)) lD rdnLD kD.
stepiv (ltac:(oF' 0x78208%Z)) (ltac:(oD' 0x78208%Z)) (Z_to_bv 64 ((pd + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x7820c%Z)) (ltac:(oD' 0x7820c%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kD)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepov (ltac:(oF' 0x78210%Z)) (ltac:(oD' 0x78210%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((pd + n - 1) mod 8 <? kD)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepiv (ltac:(oF' 0x78214%Z)) (ltac:(oD' 0x78214%Z)) (Z_to_bv 64 1) ltac:(vlit).
stepov (ltac:(oF' 0x78218%Z)) (ltac:(oD' 0x78218%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlW_inv. post.
- eexists. split.
+ stepb_tk (ltac:(oF' 0x780e8%Z)) (ltac:(oD' 0x780e8%Z)) ltac:(cond).
mlbk (ltac:(oF' 0x78204%Z)) (ltac:(oD' 0x78204%Z)) lD rdnLD kD.
stepiv (ltac:(oF' 0x78208%Z)) (ltac:(oD' 0x78208%Z)) (Z_to_bv 64 ((pd + n - 1) mod 8))
ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
stepov (ltac:(oF' 0x7820c%Z)) (ltac:(oD' 0x7820c%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kD)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepov (ltac:(oF' 0x78210%Z)) (ltac:(oD' 0x78210%Z)) (Z_to_bv 64 1)
ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
replace ((pd + n - 1) mod 8 <? kD)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepiv (ltac:(oF' 0x78214%Z)) (ltac:(oD' 0x78214%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepov (ltac:(oF' 0x78218%Z)) (ltac:(oD' 0x78218%Z)) (Z_to_bv 64 0) ltac:(vlit).
apply mst_refl.
+ unfold qlW_inv. post. }
cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I11 & I12 & I2) & K1).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x78230 : word) M rom) (fun rg => qlW_post rg /\ keeps_but RIPL regs rg)).
{ destruct (Z.lt_ge_cases fD lD) as [Hfl|Hfl].
- eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x78220 : word) M rom) (fun rg => qlW_inv rg 0 /\ keeps_but RIPL regs rg)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0x7821c%Z)) (ltac:(oD' 0x7821c%Z)) ltac:(cond).
apply mst_refl.
* split; [unfold qlW_inv; repeat split; assumption | exact K1].
+ cbv beta. intros r2 (I2' & K2).
destruct (qloopW_run M (Z.to_nat (lD - fD - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x7821c%Z)) (ltac:(oD' 0x7821c%Z)) ltac:(cond).
apply mst_refl.
+ split; [unfold qlW_post; repeat split; assumption | exact K1]. }
cbv beta. intros r4 ((J15 & J10 & J11 & J12 & J2) & K4).
eexists. split.
- stepiv (ltac:(oF' 0x78230%Z)) (ltac:(oD' 0x78230%Z)) (Z_to_bv 64 0) ltac:(vlit).
stepb_tk (ltac:(oF' 0x78234%Z)) (ltac:(oD' 0x78234%Z)) ltac:(cond).
apply mst_refl.
- unfold cW_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
Qed.
End SE.
Lemma cW_run : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "QJ&Cy5'RIyR0%211%5241'6y8%611%311p061&Q1r1%211&Mr4r3%3221';'9'J&QD&Q@vR2r5(RG+_PTD(8%33I21/01Ir6vRD%:598321r2+_PW<%:3Q018/01Q0%?5>41I6%B3A61&Q0%117&Q;&Q7%231C:r7%O21Q1%K231%L271%M2:1qQ<Q71%Q02Q81qU4Q>1%Q22Q?1p0Q41p0Q91pU2QB1pQ:Q>1pU6QD1").
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
Lemma ret_ok_780f8 : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt ":&K(RGyR0+_PWH(8%43321'RI%115/031%911"). Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma keeps_but_ms' : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "E'3'RIy5%211%411&CyR0%611%3261&Q>r2r1%3221&Q;r4r3%33216p051pTN:1pTL;1pQ0@1").
Proof. hide_dj. intros L r1 r2 AG. apply keeps_but_cs. apply keeps_keeps_cs. apply ms_agree_keeps. exact AG. Qed.
Lemma slots_ok_ms : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "Q1&Cy5'RIyR0%211%5241'6y8%611%311p061&Q6r2r1%3221r3&I&RHvR;%22@1&=&Q=vQO%211&QMvR:%211%73C41%<3@91%B2>1p0@1pQ:E1pU6K1").
Proof.
hide_dj.
intros regs0 M R. pose proof pD_facts as (Pp & Ppn & _). unhide HdjD. unfold HIGHEND in *.
apply (slots_ok_ext regs0 M); [|exact R]. intros x Hx. pose proof (u64_range x).
destruct (Z_lt_le_dec 0 n) as [Np|Nz]; [| first [ rewrite (proj1 (length_zero_iff_nil bs) ltac:(lia)); reflexivity | replace (Z.to_nat n) with 0%nat by lia; reflexivity ] ].
destruct (HdjD Np) as [Hd|Hd].
- apply wbytes_above. rewrite repeat_length. unorm. lia.
- apply wbytes_below; [rewrite repeat_length; unorm; lia | unorm; lia].
Qed.
Section SE.
Local Abbreviation SEC_T_c3_run := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "SH&Cy5'RIyR0%211%5241'6y8%611%311p061&Q0r2%211&Mr4%2214';'9'J&QD&Q@vR2r5(RG+_PW<(8%33H21/01HvRD%95872?1r1vR?&I&RHvR;%22Q11&=&Q=vQO%211&QMvR:%211%73Q441%<3N91%I5H?>1A%L3KA1':&Q?+:%K3QB1I%32E1%53QA1A+2%O3QF1M%72I1vRF%:3QF21+1%Q43QK1Q2%<2N1%>3QJ1N+8%Q83QO1Q6%@2Q21r6%B213%D3R031+9%Q>3R51Q<%F2Q81%G262%I3R521+B%QC3R:1QA%K2Q=1%L2;2%N3R:21+C%QH3R?1QF%Q02QB1%Q12@2%Q33R?21+D%QM3RD1QK%Q52QG1%Q62E2%Q83RD21+E%R23RI1R0%Q:2QL1%Q;2J2%Q=3RI21+F%R73RN1R5%Q?2R11%Q@2O2%QB3RN21&Q;&Q7%231R>R6%RD241%RE2:1%RF2@1%RG2F1%RH2L1%RI2Q21%RJ2Q81%RK2Q?1%RL2QD1%RM2QJ1%RN2R11qU4S<1%S12S=1p0S31p0S71pQ:S;1pU2SA1pU6SB1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c3_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c3_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_c3_run) 2%nat 0%nat).
Lemma c3_run : ltac:(sec_stmt2 constr:(SEC_T_c3_run) 3%nat 0%nat).
Proof.
hide_dj.
intros (H10 & H11 & H12 & H2) (HO & HGr & HR).
pose proof pD_facts as (Pp & Ppn & _). unfold HIGHEND in *.
pose proof (out_agree_globs M HO) as (_ & (I1 & I2 & I3)).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x780ec : word) M rom) (mkst r1 (0x126be8 : word) M rom)
/\ (getr r1 10 = Z_to_bv 64 pd /\ getr r1 11 = cv /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = (0x780f8 : word)
/\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepn (ltac:(oF' 0x780ec%Z)) (ltac:(oD' 0x780ec%Z)).
mld (ltac:(oF' 0x780f0%Z)) (ltac:(oD' 0x780f0%Z)) (0x1363b0 : word) I3.
stepjr (ltac:(oF' 0x780f4%Z)) (ltac:(oD' 0x780f4%Z)) (Z_to_bv 64 0x126be8) ltac:(gres; reflexivity).
vnorm. apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & Q2 & K1).
replace (0x126be8 : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
pose proof (memset_summary M (Z_to_bv 64 pd) cv (0x780f8 : word) n rom ltac:(lia) ltac:(unorm; lia)
ltac:(apply (store_ok_mono _ _ mem0 M _ HGr); exact Hdst) ret_ok_780f8 r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & V10 & AG).
pose proof (slots_ok_ms regs0 M HR) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
assert (V2 : getr r2 2 = Z_to_bv 64 (s - 2144)) by (rewrite (ms_agree_getr _ _ 2%bv AG) by (cbv; intuition discriminate); exact Q2).
eexists. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x780f8%Z)) (ltac:(oD' 0x780f8%Z)) (Z_to_bv 64 (s - 2032)) ltac:(wval).
stepld (ltac:(oF' 0x780fc%Z)) (ltac:(oD' 0x780fc%Z)) ra ltac:(maddr (s - 8)%Z; exact R1).
stepld (ltac:(oF' 0x78100%Z)) (ltac:(oD' 0x78100%Z)) (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
stepld (ltac:(oF' 0x78104%Z)) (ltac:(oD' 0x78104%Z)) (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
stepld (ltac:(oF' 0x78108%Z)) (ltac:(oD' 0x78108%Z)) (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
stepld (ltac:(oF' 0x7810c%Z)) (ltac:(oD' 0x7810c%Z)) (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
stepld (ltac:(oF' 0x78110%Z)) (ltac:(oD' 0x78110%Z)) (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
stepld (ltac:(oF' 0x78114%Z)) (ltac:(oD' 0x78114%Z)) (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).
stepld (ltac:(oF' 0x78118%Z)) (ltac:(oD' 0x78118%Z)) (getr regs0 22) ltac:(maddr (s - 64)%Z; exact R8).
stepiv (ltac:(oF' 0x7811c%Z)) (ltac:(oD' 0x7811c%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x78120%Z)) (ltac:(oD' 0x78120%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity; [exact V10 | symmetry; apply sp_s |].
eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_ms'; exact AG|]. solve_keeps_but.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_memset_icpt_run := (ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "S3&Cy5'RIyR0%211%5241':&Q?r1(RG+:(8%33;21%6251&RHvR;%22=1%;3=41r2+;%;3C19%>231vQO%A3C21r3+<%A3I1?%D231vR:%?2J1%H3J31r4+2%H3Q01F%K231vRF%N3Q021r5+1%N3Q61L%Q1231vR?%Q43Q621';'6y8%Q<11%311p0Q<1'9'J&QD&Q@vR2r8+_PRH%Q?3QE1Q=/01QEvR9vRD%8576321&I&=&Q=%11Q:&QM%11Q6%53E31%73QLQD1%A5@QCL1:%D3C:1%R02QEQK%R23R41QH%R22QGQ8%R43R61Q7%R42QIQ4%R63R81Q3&QB%12HQL&Q3%11R8&QC%12HR:%Q2231%Q3261%Q4291%Q52<1%Q62?1%Q72B1qQBQ91%Q?2Q:1qU4RF1%QA2RG1p0QC1p0QJ1p0R11p0R91p0R@1pU2RM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_memset_icpt_run) 0%nat 0%nat).
Theorem memset_icpt_run : ltac:(sec_stmt2 constr:(SEC_T_memset_icpt_run) 1%nat 0%nat).
Proof.
hide_dj.
intros H10 H11 H12 H2 H1.
destruct (c1_run regs H10 H11 H12 H2 H1) as (r1 & RUN1 & P1 & K1).
destruct (cW_run regs (M9 regs) r1 P1 (M9_FR regs)) as (r3 & M3 & RUN3 & P3 & K3 & F3).
destruct (c3_run regs r3 M3 P3 F3) as (r4 & RUN4 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & K4).
exists r4, M3. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
- assert (KB : keeps_but RIPL regs r4).
{ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K3|]. exact K4. }
destruct F3 as (HO & HGr & _).
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
Corollary wrap_memset_run : ltac2:(TCodec.tc2 tcn__Jb0MemsetIcpt "S3&Cy5'RIyR0%211%5241':&Q?r1(RG+:(8%33;21%6251&RHvR;%22=1%;3=41r2+;%;3C19%>231vQO%A3C21r3+<%A3I1?%D231vR:%?2J1%H3J31r4+2%H3Q01F%K231vRF%N3Q021r5+1%N3Q61L%Q1231vR?%Q43Q621';'6y8%Q<11%311p0Q<1'9'J&QD&Q@vR2r8+^m`0%Q?3QE1Q=/01QEvR9vRD%8576321&I&=&Q=%11Q:&QM%11Q6%53E31%73QLQD1%A5@QCL1:%D3C:1%R02QEQK%R23R41QH%R22QGQ8%R43R61Q7%R42QIQ4%R63R81Q3&QB%12HQL&Q3%11R8&QC%12HR:%Q2231%Q3261%Q4291%Q52<1%Q62?1%Q72B1qQBQ91%Q?2Q:1qU4RF1%QA2RG1p0QC1p0QJ1p0R11p0R91p0R@1pU2RM1").
Proof.
hide_dj.
intros regs H10 H11 H12 H2 H1.
destruct (memset_icpt_run regs H10 H11 H12 H2 H1) as (r' & M' & RUN & REST).
exists r', M'. split; [|exact REST].
eapply msteps_trans; [|exact RUN].
stepn (ltac:(oF' 0x77600%Z)) (ltac:(oD' 0x77600%Z)).
apply mst_refl.
Qed.
End AMSI.
End FPX_1.

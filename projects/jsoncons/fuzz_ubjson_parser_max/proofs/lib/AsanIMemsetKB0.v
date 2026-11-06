(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SumsLib Sums_codeK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanIMemsetKB0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanIMemsetKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nat"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3repeat"; "4Z"; "5store_ok"; "5word_to_le_bytes"; "6bvmap"; "7align15"]; ["7asan_imemset_entry"; "7asanreflect_fx"; "7cbyte_"; "7cpat_"; "7imemset_clob"; "7imemset_words"; "8wbytes"; "9msteps"; ":at_"; ":regs_agree"; ":ret_ok"; ";getr"; ";mkst"; ";v_andi"; ";v_or"; "<code_at"]; ["<msetk"; "=loaded_segments"; ">In"; "?add"; "?land"; "?le"; "?lt"; "?modulo"; "?mul"; "?of_nat"; "?pow"; "?sub"; "?to_nat"; "0base"; "0c"; "0i"]; ["0k"; "0mem0"; "0n"; "0r"; "0regs"; "0regs'"; "0ret"; "0rom"; "0s"; "0segs"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0x"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition imemset_words : list (bv 32) :=
[W_103828; W_10382c; W_103830; W_103834; W_103838; W_10383c; W_103840; W_103844;
W_103848; W_10384c; W_103850; W_103854; W_103858; W_10385c; W_103860; W_103864;
W_103868; W_10386c; W_103870; W_103874; W_103878; W_10387c; W_103880; W_103884].
Definition imemset_clob : list reg := [11; 12; 13].
Definition align15 (n : Z) (s : word) : Z := Z.land (Z.lor n (bv_unsigned s)) 15.
Lemma land15_range : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "A';&Q5zr1%3221'6&Q4r2+?%3221%9281&Q6+@%2241%9241p0;1pSN@1").
Proof.
intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia.
apply Z.mod_pos_bound. lia.
Qed.
Lemma align15_range : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "D';'QLyR0%211&Q5zr2%3221'6&?r3%2215%8271&Q6+@%2241%8241p0:1pSB?1pS6C1").
Proof.
intros n s Hn. unfold align15. apply land15_range. apply Z.lor_nonneg. pose proof (u64_range s). lia.
Qed.
Lemma u_align15 : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "Q1';'QLyR0%211'6&Q5zr2%3221&Q6&Q:+2+R0%3221%5271%;271'7&QM&M&N&QKr3%22D1%421@+?%7221%92H1&?%127E%=3M31p0?1pSBL1pS6Q01").
Proof.
intros n s Hn. pose proof (u64_range s) as Hs.
pose proof (Z_lor_range n (bv_unsigned s) Hn Hs) as Hl.
unfold v_andi, v_or, align15. rewrite (u_Z2bv n) by lia.
rewrite (u_Z2bv (Z.lor n (bv_unsigned s))) by lia.
change (bv_wrap 64 15) with 15%Z.
pose proof (land15_range (Z.lor n (bv_unsigned s)) ltac:(lia)).
apply u_Z2bv; lia.
Qed.
Lemma align15_n16 : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "F';'QLyR0%211&Q5zr2%3221'7&?r3%2215%43<17&Q7r4+@%3221%93A1<p061p0<1pSBA1pS6E1").
Proof.
intros n s Hn H. unfold align15 in H. pose proof (u64_range s).
rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [H _].
change 15%Z with (Z.ones 4) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.
Definition cbyte_ (c : word) : byte := Z_to_bv 8 (bv_unsigned c).
Definition cpat_ (c : word) : word := Z_to_bv 64 (bv_unsigned c * M8).
Lemma cpat_bytes : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "K'QLyR0%211&Q6&QMr1%2251+X0%5221'7'1y8%<11%311&=u8&Cr2%211%5241&:&B%115%33;18%?3;51p0A1pRNH1").
Proof. intros c Hc. pose proof (u64_range c). apply rep8_bytes. lia. Qed.
Section IMEMSET.
Variable segs : list Segment.
Variable base : word.
Variable mem0 : word -> option byte.
Variables s c : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 imemset_words.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.
Hypothesis HC256 : align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z.
#[local] Abbreviation cbyte := (cbyte_ c).
#[local] Abbreviation cpat := (cpat_ c).
#[local] Abbreviation MS := (msetk mem0 s (cbyte_ c)).
#[local] Abbreviation CL := (fun r => In r imemset_clob).
Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at imemset_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & _).
Ltac msb F D kk :=
chain_step; [reflexivity
| eapply MmapSim.step_sb_at with (a := at_ s kk) (v := c) (b := cbyte);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
| gres; rwH; reflexivity | reflexivity
| apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
| step_simpl];
rewrite (msetk_extend1 mem0 s cbyte kk) by lia; vn.
Ltac msd F D kk :=
chain_step; [reflexivity
| eapply step_sd_at with (a := at_ s kk) (v := cpat);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
| gres; rwH; reflexivity
| apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
| step_simpl];
rewrite (cpat_bytes c) by lia;
rewrite (msetk_extend mem0 s cbyte kk 8) by lia; change (Z.of_nat 8) with 8%Z; zlit_at; vn.
Lemma bl_loop : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "S2'2&>y5'QLyR0%211%5241';&Jr2%211'7&Kr4(QJ+1(5%33?21%6251r3%93?21r5+;%93E17%<231vQ>%?3E21r6+=%?3K1=%B231&HvQH%221D%G3M41r7+<%G3Q31E%J231vQB%9281%N3Q431'6&Q5z%221B&Q6%12D8%6231&Q9r:%211&Q;%12>Q6%221C%Q<3Q@41'8'GvQI&L&Ar;vQ=+H%Q1221&Q0vQA&B%11Q;r9%544Q621vQG%=5<;821r1%948Q:6Q3%@5?2I14%C3B41&I%R;1R<&Q2&D%23381qS841%631F:%Q:281qS<R?1%N2R@1p0Q01p0Q81p0Q@1p0QH1p0R11p0R81p0RC1pS2RG1pS>RJ1pS:RJ1pS0S11").
Proof.
get_code. pose proof (u64_range s) as Hs.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
- eexists. split.
+ msb C24 D_103840 k.
an C28 D_103844.
ab_ft C32 D_103848 ltac:(condz).
an C36 D_10384c.
aret C92 D_103884 ret.
replace (k + 1)%Z with n by lia. apply mst_refl.
+ unfold imemset_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s (k + 1)
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
+ eexists. split.
* msb C24 D_103840 k.
an C28 D_103844.
ab_tk C32 D_103848 ltac:(condz).
apply mst_refl.
* post. unfold imemset_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
Lemma al_loop : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "S?'2&>y5'QLyR0%211%5241';&Jr2%211'7&Kr4(QJ+1(5%33?21%6251r3%93?21r5+;%93E17%<231&CvQ>%211%A3G41r6+=%A3M1?%D231&HvQH%221F%I3O41r7+<%I3Q51G%L231vQB%9281%Q03Q631&Q5z%221A&Q3+@%22<1%6219&Q8&Q9r;%211%4217&Q;r8%22A1%321;%QA3QE51&Q6&QM%12QKQ5+X0%4221'8'6'GvQI&L&Ar=vQ=+R<%Q:221&Q0vQA&B%11QE%443Q>1KvQG%<5;:721r1r<%948QC6Q<%@5?3215%C3B51&I%RF1RG&Q2&D%23391qS841%631F;%L281qS<RJ1%O2RK1p0Q11p0Q71p0QB1p0QG1p0QK1p0R31p0R<1p0RE1p0S01pS2S41pS>S71pS:S71pS0S>1").
Proof.
get_code. pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hk16 Hi Hc256.
- eexists. split.
+ msd C76 D_103874 k.
msd C80 D_103878 (k + 8)%Z.
an C84 D_10387c.
ab_ft C88 D_103880 ltac:(condz).
aret C92 D_103884 ret.
replace (k + 8 + 8)%Z with n by lia. apply mst_refl.
+ unfold imemset_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s (k + 16)
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
+ eexists. split.
* msd C76 D_103874 k.
msd C80 D_103878 (k + 8)%Z.
an C84 D_10387c.
ab_tk C88 D_103880 ltac:(condz).
replace (k + 8 + 8)%Z with (k + 16)%Z by lia. apply mst_refl.
* post. unfold imemset_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 16)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia) Hc256) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
Theorem imemset_run : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "RC&>y5'QLyR0%211%5241&Jr1%211'7&Kr3(QJ+1(5%33>21%6251r2%93>21r4+:%93D17%<231vQH%?3D21r5+;%?3J1=%B231vQ>%E3J21r6+<%E3Q01C%H231&QKvQB%22Q21%M3Q241'8'6'GvQI&L&Ar8&HvQ=z%3221vQAvQG%9587321r7&F&:y8%QG11&B%11N&Q<%11I%73531%93=Q81%E5DQI;1=%H3G=1&I%R11R2&Q2&D%233QO1qS841%631KR1%Q1281qS<R51%Q42R61p0Q61p0Q?1p0QF1p0QM1p0R81pS>R=1pS:R=1").
Proof.
get_code. intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
pose proof (align15_range n s Hn) as HA.
change (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) with (MS n). change mem0 with (MS 0).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MS 0) rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = c /\ getr r 12 = Z_to_bv 64 n
/\ getr r 13 = Z_to_bv 64 (align15 n s) /\ regs_agree CL regs r)).
{ eexists. split.
- an C0 D_103828.
av C4 D_10382c (Z_to_bv 64 (align15 n s))
ltac:(rewrite <- (u_align15 n s) by lia; symmetry; apply Z_to_bv_bv_unsigned).
apply mst_refl.
- post. unfold imemset_clob. solve_regs_agree. }
cbv beta. intros r0 (R1 & R10 & R11 & R12 & R13 & AG0).
destruct (Z.eq_dec (align15 n s) 0) as [HA0|HA0].
-
destruct (Z.eq_dec n 0) as [Hz|Hnz].
+ eexists. split.
* ab_tk C8 D_103830 ltac:(condz).
ab_tk C40 D_103850 ltac:(condz).
aret C92 D_103884 ret.
rewrite Hz. apply mst_refl.
* exact AG0.
+ pose proof (HC256 HA0 Hnz) as Hc256.
pose proof (align15_n16 n s Hn HA0) as Hn16.
eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s 0
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
* eexists. split.
-- ab_tk C8 D_103830 ltac:(condz).
ab_ft C40 D_103850 ltac:(condz).
av C44 D_103854 (at_ s n) ltac:(apply v_add_at; lia).
av C48 D_103858 (Z_to_bv 64 (bv_unsigned c * 2 ^ 8)) ltac:(apply v_slli_mul; lia).
av_or C52 D_10385c (Z_to_bv 64 (bv_unsigned c * 257))
ltac:(rewrite v_or_shl by (unorm; lia); f_equal; lia).
av C56 D_103860 (Z_to_bv 64 (bv_unsigned c * 257 * 2 ^ 16))
ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).
av_or C60 D_103864 (Z_to_bv 64 (bv_unsigned c * 16843009))
ltac:(rewrite v_or_shl by (unorm; lia); unorm; f_equal; lia).
av C64 D_103868 (Z_to_bv 64 (bv_unsigned c * 16843009 * 2 ^ 32))
ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).
av_or C68 D_10386c (cpat_ c)
ltac:(rewrite v_or_shl by (unorm; lia); unfold cpat_, M8; unorm; f_equal; lia).
an C72 D_103870.
apply mst_refl.
-- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
* cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
assert (Hdiv : (n = 16 * (n / 16))%Z) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
assert (Hi : exists i : nat, (Z.of_nat i * 16 = n - 0 - 16)%Z) by (exists (Z.to_nat (n / 16 - 1)); lia).
destruct Hi as (i & Hi).
destruct (al_loop i r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia) Hi Hc256) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
-
destruct (Z.eq_dec n 0) as [Hz|Hnz].
+ eexists. split.
* ab_ft C8 D_103830 ltac:(condz).
ab_tk C12 D_103834 ltac:(condz).
aret C92 D_103884 ret.
rewrite Hz. apply mst_refl.
* exact AG0.
+ eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s 0
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C8 D_103830 ltac:(condz).
ab_ft C12 D_103834 ltac:(condz).
av C16 D_103838 (at_ s n) ltac:(apply v_add_at; lia).
an C20 D_10383c.
apply mst_refl.
-- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
* cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
destruct (bl_loop (Z.to_nat (n - 1)) r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End IMEMSET.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Definition asan_imemset_entry : word := 0x8add8.
Lemma asan_imemset_code : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "6&O&Q1&@z&E%544321").
Proof. unfold imemset_words. code_at_vm. Qed.
Theorem asan_imemset : ltac2:(TCodec.tc2 tcn__AsanIMemsetKB0 "SM'QLyR0%211'3y8%511%311p051';&>y5%2219&Q5zr4%3221&Q6&Q3&QMr7%22C1r5%5221&Q:+2+R0%3221%;251'7'0&<&Q1r9r8&Q<r6%211%746541(4%;3:21&?%12F9%>3Q21M&9%@3Q4;O%211r:%M2Q>1+X0%Q1221p051p091&J%11Q0&K(QJ+1(5%33Q@21%52Q81%Q03QJ1I+:%73QD15%92N1r<%Q53QO21+;%<3QI1:%>2Q41%Q93R315+<%@3QM1>%B2J1&QK%12R9:%Q?3R931'8'6'G&L&A&@rAr=%554D321r1r;&Fr@&:r?%R92RJ1%C2RH1r>%QL11%63RJ31%93>81%B5A<;1>%D3R3>1&I%S41RJ&Q2&D%233B1qS841%631Q9D%M281qS<S01%Q02S11p0Q21p0Q91p0Q>1p0QD1p0QL1p0QO1p0R<1p0RI1p0S61pS>SD1pS:S<1pS@SA1pS6SA1pRNSH1pSBSI1pS4SE1").
Proof.
intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
rewrite <- (at_0 asan_imemset_entry).
apply (imemset_run _ _ mem0 s c n rom asan_imemset_code Hn Hnw Hok HC256).
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

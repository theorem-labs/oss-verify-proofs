(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SumsLib Sums2_codeK AsanIMemsetK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanIStrncpyK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanIMemsetK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanIStrncpyK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanIStrncpyK.ISTRNCPY."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"]; ["3Z"; "4store_ok"; "5bvmap"; "6align15"; "8MZ"; "7asan_istrncpy_entry"; "7asan_sealed_src"; "7asanreflect_fx"; "7istrncpy_clob"; "7istrncpy_words"; "7sealed8"; "7strncpy_sealed_bytes"; "9wbytes"; ":msteps"; ";at_"; ";regs_agree"]; [";ret_ok"; "<getr"; "<mkst"; "<rdn"; "=b_"; "=code_at"; "=cpyH"; "=memk"; ">loaded_segments"; "?In"; "@add"; "@le"; "@lt"; "@of_nat"; "@pow"; "@sub"]; ["@to_nat"; "0base"; "0d"; "0dst"; "0i"; "0j"; "0k"; "0mem"; "0mem0"; "0r"; "0regs"; "0regs'"; "0regs0"; "0ret"; "0rom"; "0rr"]; ["0segs"; "0src"; "ABV"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0x"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition istrncpy_words : list (bv 32) :=
[W_103d3c; W_103d40; W_103d44; W_103d48; W_103d4c; W_103d50; W_103d54; W_103d58;
W_103d5c; W_103d60; W_103d64; W_103d68; W_103d6c; W_103d70; W_103d74; W_103d78;
W_103d7c; W_103d80; W_103d84; W_103d88; W_103d8c; W_103d90; W_103d94; W_103d98;
W_103d9c; W_103da0; W_103da4; W_103da8].
Definition istrncpy_clob : list reg := [11; 12; 13; 14; 15].
Definition sealed8 : list byte :=
[Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e].
Definition strncpy_sealed_bytes : list byte := sealed8 ++ zeros 4087.
Lemma length_strncpy_sealed_bytes : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK ":'<'6&4'R4y8%211&K%5221uSoO%93821").
Proof. unfold strncpy_sealed_bytes. rewrite length_app, length_zeros. reflexivity. Qed.
Lemma sealed8_nz : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "G'@';&Q;zr1%3221&Q<+8%2241%8241&>'<&R5y8&Q4&Jr2%3221%6251%83C1@%:11p0<1pS<F1").
Proof.
intros j Hj.
assert (E : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7)%Z) by lia.
destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst j; cbv; discriminate.
Qed.
Lemma align15_4087 : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK ">'R4yR0%211&>'<'@&C+SoGr1%3221z%73621%911pS6;1").
Proof.
intros d H. unfold align15 in H. rewrite Z.land_lor_distr_l in H.
apply Z.lor_eq_0_iff in H as [H _]. cbv in H. discriminate.
Qed.
Section ISTRNCPY.
Variable segs : list Segment.
Variable base : word.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 istrncpy_words.
Hypothesis Hsrc : rdn segs mem0 src 8%nat = Some sealed8.
Hypothesis Hnul : rdn segs mem0 (at_ src 8) 1%nat = Some [Z_to_bv 8 0].
Hypothesis Hsnw : (bv_unsigned src + 9 < 2 ^ 64)%Z.
Hypothesis Hok : store_ok segs mem0 dst 4095%nat = true.
Hypothesis Hnw : (bv_unsigned dst + 4095 < 2 ^ 64)%Z.
Hypothesis Hdisj : (bv_unsigned dst + 4095 <= bv_unsigned src \/ bv_unsigned src + 9 <= bv_unsigned dst)%Z.
#[local] Abbreviation CL := (fun r => In r istrncpy_clob).
Ltac condv :=
rwH; rewrite ?at_addi; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.
Lemma HMC : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "8'Q6vR0vQHvQCvR1+8&J%76654321").
Proof.
pose proof (u64_range dst). pose proof (u64_range src).
apply CPYH.
- lia.
- reflexivity.
- exact Hsrc.
- cbn [length]. eapply (store_ok_sub segs mem0 dst dst 4095%nat 8%nat); [lia | exact Hok | lia | cbn; lia].
- lia.
- lia.
- lia.
Qed.
#[local] Abbreviation MK := (memk mem0 dst sealed8).
Definition MZ (k : Z) : word -> option byte := msetk (MK 8) (at_ dst 8) (Z_to_bv 8 0) k.
Lemma MZ_0 : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "C'<'R4yR0%211'8y8%511%311p051&Dz%211&Q7vQHvQC&J+8%544321%B3:71").
Proof. reflexivity. Qed.
Lemma MZ_final : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "B'<'R4yR0%211'8y8%511%311p051&D+SoG%211&LvQHvQC&K%43321%A3961").
Proof.
unfold MZ, msetk, strncpy_sealed_bytes, zeros. rewrite (memk_n _ _ _ _ _ _ HMC).
rewrite wbytes_app. reflexivity.
Qed.
Lemma MK8_ok : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "B'<'2&AvR0&Q7vQHvQC&J+8%544321&N%1253&Q@+SoG%211%=4<641(9%A3@21").
Proof.
unfold memk. pose proof (u64_range dst).
apply (store_ok_at segs mem0 dst 4095%nat); [lia | exact Hok | lia | cbn; lia].
Qed.
Lemma at8_nw : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "@&Q<&Q:&R5yR0&NvQC+8%3221%6251+SoG%9221&Q>+2+R0%3221%?251").
Proof. pose proof (u64_range dst). rewrite at_u by lia. lia. Qed.
Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at istrncpy_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60
& C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & _).
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ _ HMC) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia | lia]
| step_simpl]; vn.
Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (memk _ _ _ ?a) _) _ =>
first [constr_eq a kk | replace (memk mem0 dst sealed8 a) with (memk mem0 dst sealed8 kk) by (f_equal; lia)] end.
Ltac msb F D kk :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ _ HMC) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia
| gres; rwH; reflexivity | apply sb_val_b | lia | lia]
| step_simpl]; vn.
Ltac mz_at kk := match goal with |- msteps _ (mkst _ _ (MZ ?a) _) _ =>
first [constr_eq a kk | replace (MZ a) with (MZ kk) by (f_equal; lia)] end.
Ltac mzsb F D kk :=
mz_at kk; unfold MZ;
chain_step; [reflexivity
| eapply MmapSim.step_sb_at with (a := at_ (at_ dst 8) kk) (v := Z_to_bv 64 0) (b := Z_to_bv 8 0);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi, ?at_at; first [reflexivity | f_equal; lia]
| gres; rwH; reflexivity | reflexivity
| apply (wr_s segs (MK 8) (at_ dst 8) 4087 (Z_to_bv 8 0) ltac:(lia) at8_nw MK8_ok); cbn; lia ]
| step_simpl];
rewrite (msetk_extend1 (MK 8) (at_ dst 8) (Z_to_bv 8 0) kk) by lia; fold (MZ (kk + 1)); vn.
Lemma fill_loop : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "RO'6&By5'R4yR0%211%5241'@&Q0r2%211'<&Q1r4(R2+1(:%33?21%6251r3%93?21r5+;%93E17%<231&NvQC&Q:+8%221:%5241%D3J71r6+<%D3Q01B%G231+SoO%<2;1%K3Q131&Q;z%221D&Q<%@2?;%2218&Q=r:%211&Q?%12=Er7%3221%421Q5%Q:3Q>61'=';'MvR0&Q2&Gr;vQA+R4%Q6221&Dr9%211vQN%:598521r1+SoG%711%>5=3J15%A3@51&O%R81R9&Q9&H%23391qSD41%631D;%J281qSHR<1%M2R=1p0O1p0Q91p0Q=1p0QA1p0QI1p0R51p0R@1pS>RD1pSLRG1pSFRG1pS:RN1").
Proof.
get_code. pose proof (u64_range dst) as Hd.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H12 Hk Hkn Hi.
- eexists. split.
+ mzsb C68 D_103d80 k.
an C72 D_103d84.
ab_ft C76 D_103d88 ltac:(condz).
an C80 D_103d8c.
aret C108 D_103da8 ret.
mz_at 4087%Z. apply mst_refl.
+ unfold istrncpy_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + (k + 1)) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
+ eexists. split.
* mzsb C68 D_103d80 k.
an C72 D_103d84.
ab_tk C76 D_103d88 ltac:(condz).
mz_at (k + 1)%Z. apply mst_refl.
* post. unfold istrncpy_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R12 & AG).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
Lemma copy_iter : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "S2&By5'R4yR0%211%5241'@'<&Q1r2(R2+:(:%33<21%6251vQC%93<21r3+;%93B17%<231vR1%?3B21r4+<%?3H1=%B231&R3+SoO%22J1%G3J41r5+=%G3Q01E%J231%82Q0<%M3Q021';&Q;z%2219&Q<+8%22<1%7241'='MvR0&Q2&Gr8&NvQA%221;&Q7vQH&Jr7%443Q;21vQN%<5;:721r1&Q:+1%2271%;4:QB91%B5A5=17%E3D71%QL27QG%QN3R11QF%QN29QC%R03R31QB%R02;Q?%R23R51Q<%R22=Q9%Q@2R8;%R53R821&O%R<1R=&Q9&H%233D1qSD41%631Q1F%Q?281%Q@2<1%QA2?1%QB2B1%QC2E1qSHRD1%Q=2RE1p0Q?1p0QH1p0QO1p0R81p0R?1pS<RJ1pSFRL1").
Proof.
get_code. intros regs j H10 H11 H12 H13 Hj. pose proof (u64_range dst). pose proof (u64_range src).
eexists. split.
- av C8 D_103d44 (at_ src j) ltac:(apply v_add_at; lia).
mlbu C12 D_103d48 j.
ab_ft C16 D_103d4c
ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; pose proof (u8_range (b_ sealed8 j));
rewrite (u_Z2bv (bv_unsigned (b_ sealed8 j))) by lia; rewrite (u_Z2bv 0) by lia;
apply sealed8_nz; lia).
av C20 D_103d50 (at_ dst j) ltac:(apply v_add_at; lia).
an C24 D_103d54.
msb C28 D_103d58 j.
ab_tk C32 D_103d5c ltac:(condv).
mk_at (j + 1)%Z. apply mst_refl.
- post; try (unfold istrncpy_clob; solve_regs_agree). unfold v_addi. unorm. reflexivity.
Qed.
Lemma copy8 : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "RJ&By5'R4yR0%211%5241&O%516&Q9r1&H%33421qSD51r2%83215'<&Q1(R2+:(:%33C21%5281vQC%83C21r3+;%93I17%;231vR1%>3I21r4+<%?3O1=%A231&R3+SoO%22Q11%F3Q141r5+=%G3Q71E%I231z%92Q81%M3Q831'=';'MvR0&Q2&Gr7&NvQA+8%3221&Q7vQH&J%342Q51AvQN%<5;:621%645Q848%>5=QF813%A3@31%QA2QHQ=%QC3QN1Q<%QC2QJQ9%QE3R01Q8%QE2QLQ5%QG3R21Q2%QG2QNO%Q62R5B%QJ3R521r8%R53QO1R2%N231%O271%Q02:1%Q12=1%Q22@1qSHR<1%Q52R=1p0Q71p0Q?1p0QH1p0QO1p0R91pT0RC1pSJRD1").
Proof.
intros regs0 rr K A B C D.
Ltac cp_iter :=
match goal with
| K : regs_agree _ ?regs0 ?rr, A : getr ?rr 10 = _, B : getr ?rr 11 = _, C : getr ?rr 12 = _, D : getr ?rr 13 = Z_to_bv 64 ?v |- _ =>
let jj := eval vm_compute in v in
let jj1 := eval vm_compute in (v + 1)%Z in
change (Z_to_bv 64 v) with (Z_to_bv 64 jj) in D;
try change (memk mem0 dst sealed8 v) with (memk mem0 dst sealed8 jj);
eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK jj1) rom)
(fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
/\ getr r 13 = Z_to_bv 64 jj1 /\ regs_agree CL regs0 r));
[ destruct (copy_iter rr jj A B C D ltac:(lia)) as (r' & RUN & B10 & B11 & B12 & B13 & K');
exists r'; split; [exact RUN | repeat split; try assumption; eapply regs_agree_trans; [exact K | exact K']]
| cbv beta; clear rr K A B C D; intros rr (A & B & C & D & K) ]
end.
do 8 cp_iter.
exists rr. split; [apply mst_refl | repeat split; assumption].
Qed.
Theorem istrncpy_run : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "R<&By5'R4yR0%211%5241&Q0r1%211'<&Q1r3(R2+1(:%33>21%6251r2%93>21r4+:%93D17%<231vQC%?3D21r5+;%?3J1=%B231vR1%E3J21r6+<%E3Q01C%H231&R3+SoO%22Q21%M3Q241'=';'MvR0&Q2&Gr8&NvQAz%3221vQHvQN%9587321r7&L&K%236Q11%>5=QB416%A3@61&O%QJ1QK&Q9&H%233QH1qSD41%631DQJ%J281qSHQN1%M2QO1p0O1p0Q81p0Q?1p0QF1p0R11pSLR61pSFR61").
Proof.
get_code. intros regs ret Hret H1 H10 H11 H12. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs.
rewrite <- MZ_final.
change (mkst regs (at_ base 0) mem0 rom) with (mkst regs (at_ base 0) (MK 0) rom).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 0) rom)
(fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
/\ getr r 13 = Z_to_bv 64 0 /\ regs_agree CL regs r)).
{ eexists. split.
- ab_ft C0 D_103d3c ltac:(condz).
an C4 D_103d40.
apply mst_refl.
- post. unfold istrncpy_clob. solve_regs_agree. }
cbv beta. intros r0 (A10 & A11 & A12 & A13 & K0).
destruct (copy8 regs r0 K0 A10 A11 A12 A13) as (r8 & RUN8 & L10 & L11 & L12 & L13 & K8).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 8) rom)
(fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
/\ getr r 13 = Z_to_bv 64 8 /\ regs_agree CL regs r)).
{ exists r8. split; [exact RUN8 | repeat split; assumption]. }
cbv beta. clear r8 RUN8 L10 L11 L12 L13 K8. intros r8 (L10 & L11 & L12 & L13 & K8).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + 0) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
{ eexists. split.
- av C8 D_103d44 (at_ src 8) ltac:(apply v_add_at; lia).
chain_step; [reflexivity
| eapply step_lbu with (b := Z_to_bv 8 0);
[exact C12 | reflexivity | exact D_103d48
| gres; rwH; imm_norm; rewrite at_addi; replace (at_ src (8 + 0)) with (at_ src 8) by (f_equal; lia);
unfold memk; change (firstn (Z.to_nat 8) sealed8) with sealed8;
rewrite rdn_wbytes_out;
[ exact Hnul
| change (length sealed8) with 8%nat; rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| change (length sealed8) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ] ]
| step_simpl]; vn.
ab_tk C16 D_103d4c ltac:(condz).
change (memk mem0 dst sealed8 8) with (MZ 0).
av C40 D_103d64 (at_ dst 8) ltac:(apply v_add_at; lia).
an C44 D_103d68.
an C48 D_103d6c.
av C52 D_103d70 (Z_to_bv 64 (align15 4087 (at_ dst 8)))
ltac:(rewrite <- (u_align15 4087 (at_ dst 8)) by lia; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (align15_4087 (at_ dst 8)) as HA. pose proof (align15_range 4087 (at_ dst 8) ltac:(lia)) as HAR.
ab_ft C56 D_103d74 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; rewrite !u_Z2bv by lia; exact HA).
ab_ft C60 D_103d78 ltac:(condz).
av C64 D_103d7c (at_ dst 4095) ltac:(apply v_add_at; lia).
apply mst_refl.
- post.
+ rewrite <- H1. apply K8. unfold istrncpy_clob. cbn. intros [X|[X|[X|[X|[X|[]]]]]]; discriminate.
+ unfold istrncpy_clob in *. ra_chain. }
cbv beta. intros r9 (M1 & M11 & M12 & K9).
destruct (fill_loop (Z.to_nat 4086) r9 ret 0 Hret M1 M11 M12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r10 & RUN & K10).
exists r10. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End ISTRNCPY.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
Definition asan_istrncpy_entry : word := 0x8af34.
Definition asan_sealed_src : Z := 0x11b12.
Lemma asan_istrncpy_code : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "6&Q5&Q8&Ez&I%544321").
Proof. unfold istrncpy_words. code_at_vm. Qed.
Lemma asan_sealed_src_img : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "QK'R4yR0%211'8y8%511%311pT>51'@';&Q;&Fr1%3221&Q<&Q:+9%2261%4261%:261'<r3&R3r2%22G1%411(0%11F%83F31p0:1pS:F1'5%11K%N11&Q3&Q8%>2Q3Iu8%443?21(1&J%2291%F3941&N+8%2291u1%=4<H21(3z%L2Q>1(7%11Q?%53Q@31%?2F1%Q33F81%Q?2>1p0K1pS@QC1").
Proof.
intros mem Hnone. unfold asan_sealed_src in *. split.
- rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
Theorem asan_istrncpy_sealed : ltac2:(TCodec.tc2 tcn__AsanIStrncpyK "SM'R4yR0%211'8y8%511%311pT>51p062&By5%2219'@';&Q;&Fr1%3221&Q<&Q:+9%2261%4261%:261'<r7&R3r2%22K1%411(0%11J%83J31p0:1pS:F1'2&A&Q8r6r5uSoO%544321(9%C3821&R5%12Q<7+SoO%L221&Q>+2+R0%3221%Q2251'?%:2QEM%Q4219%Q:21Q9%Q;2Q43%5221&Q0%11E&Q1(R2+1(:%33QG21%52Q91%Q;3R11Mr8+:%83QL16%:231r:%QA3R721r9+;%>3R21<%@231%QD2R=QO%QG3R=21+<%C3R71A%E2:1%QI2RBQ5%QL3RB21'='M&Q2&Gr<&Er?r=%6554321r;&Lr>&K%33721%<5;RC517%>3QO71&O%S61RL&Q9&H%233RI1qSD41%631BRK%RO281qSHS21%I2S31p0K1p0Q11p0Q81p0Q?1p0QG1p0QJ1p0R11p0R;1p0RE1pSLSF1pSFS>1pSNSB1pS8SI1pSBSE1").
Proof.
intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
destruct (asan_sealed_src_img mem0 Hnone) as [Hs Hn].
rewrite <- (at_0 asan_istrncpy_entry).
apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 asan_sealed_src) rom asan_istrncpy_code Hs Hn); try assumption;
unfold asan_sealed_src in *; u_norm; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

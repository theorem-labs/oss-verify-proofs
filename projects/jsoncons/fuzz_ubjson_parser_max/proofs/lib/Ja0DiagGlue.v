(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA
Ja0RegionPoisoned Ja0AsanMemcpy Ja0DiagWritev Ja0DiagKit Ja0DiagChk Ja0DiagMemcpy Ja0DiagStrnlen.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DiagGlue () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0AsanMemcpy."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagChk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagGlue.DG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagMemcpy."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagStrnlen.DSN."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3add"; "4map"]; ["5Z"; "6word_to_le_bytes"; "7bvmap"; "0M"; "0M'"; "0R"; "0R'"; "8msteps"; "9in_app8"; "9mc_icpt_globs"; ":chk_pre"; ";PRE7"; ";SUF7"; ";agree0"; "<zsh"; "=cstr"]; ["=sn_cells"; ">SB"; ">rt_layout_globs"; "?u32_at"; "?u8_at"; "?writable"; "@zeros_at"; "AFPState"; "Agetr"; "Amkst"; "Ardn"; "Aseg_rom"; "Bmem_grows"; "Cloaded_segments"; "0S"; "DIn"]; ["Eadd"; "Ediv"; "Ele"; "Elt"; "Emin"; "Emodulo"; "Eof_nat"; "Epow"; "Esub"; "0a"; "0b0"; "0b1"; "0b2"; "0b3"; "0b4"; "0b5"]; ["0b6"; "0bs"; "0fx"; "0k"; "0l1"; "0l2"; "0n"; "0p"; "0pd"; "0ps"; "0s"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"; "0t8"; "0w"]; ["0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DG.
Import DK. Import DSN.
Ltac alia := first [ lia | match goal with H : _ \/ _ |- _ => destruct H; lia end ].
Ltac sc := first [ assumption | reflexivity | dk_rk | dk_gmem | (dk_arith_goal; alia) ].
Definition diag_cells (M : word -> option byte) (can : Z) : Prop :=
L5.u8_at RSEGS M 1292760 1 /\ L5.u8_at RSEGS M 1292761 1 /\ L5.u8_at RSEGS M 1886332 1 /\ L5.u64_at RSEGS M 1289464 2147450880
/\ L5.u64_at RSEGS M 1262792 1163716 /\ L5.u64_at RSEGS M 1263168 1198508 /\ L5.u64_at RSEGS M 6876608 can
/\ L5.u32_at RSEGS M 1273408 5 /\ L5.u64_at RSEGS M 1273504 0 /\ L5.u64_at RSEGS M 1273496 6878616 /\ L5.u32_at RSEGS M 1273544 0
/\ L5.u32_at RSEGS M 1273548 4294967295 /\ L5.u32_at RSEGS M 1273552 4294967295 /\ L5.u64_at RSEGS M 1273480 1159804 /\ L5.u32_at RSEGS M 1273528 2
/\ L5.writable RSEGS M 1273408 152.
Lemma cstr_rd1 : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "Q>'R<yR0%211'8y8%511%311p051'@'5%115'Or4r3r2r1%544321':%?18&Q:&Q=r5&R;%12F;&>&4%12E=u1%4221%:49861(1&2(3z%<2N1(7%11O%53Q031%73Q1I1%92M1%G3F;1p0I1pTNQ01pT4Q11pT@Q41pQ8Q61").
Proof. intros M p bs t8.
intros [A _ _]. rewrite (SeqExec.rdn_firstn RSEGS M _ _ _ (length bs + 1) A) by lia. f_equal.
rewrite firstn_app. rewrite firstn_all2 by lia. replace (length bs + 1 - length bs)%nat with 1%nat by lia. reflexivity.
Qed.
Lemma chk_pre_intro : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "S0'R<yR0%211'8y8%511%311p051'@'9&QBzr2%3221+SooO%5231%7231+SoomohRTP0r4%9221&Q@r5%2214+1%4221+@%6221&QG+2+Q?%3221%E251&QH+R8%22@1%I2B1%J2?6&Q5&Q=r9r6%9218%544319&Q2r:%211&Q1&QAr;+8%3221%O251+7%E221&R=r1%22QG1%Q?241&QC&QD%Q82<@%>21<%Q:2@1%Q;21>+Q<%Q62Q51%Q>2D1%8241%:2<1%QL2<1':r=%11QL(1&R;%12R7R0%32R71%73R751p091pU2R=1&Jr<%QN2Q6QK%342Q31Q<p051p0Q81p0Q<1p0QC1p0QE1p0QJ1p0R71p0R;1pTFRD1pT>RE1pT@RF1pQ8RH1").
Proof. intros M p n s.
intros Hn Hp Hpn Hs1 Hs2 W G Z0. unfold chk_pre. replace (p + (n + 1) - 1) with (p + n) by lia.
assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). unfold SB in *.
split; [lia|]. split; [right; unfold HIGHBEG, HIGHEND; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [apply (store_ok_of_writable M (s - 72) 72); [exact W | reflexivity]|]. split; [exact G | exact Z0].
Qed.
Ltac rkb K :=
lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
let z := eval vm_compute in (Z.of_nat k) in
rewrite (DK.keeps_but_reg _ _ _ k (@BV 5 z I) K eq_refl) by (first [cbv; tauto | cbv; intuition discriminate]) end.
Ltac rkc K :=
lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (DK.keeps_cs_reg _ _ k K) by (cbn; tauto) end.
Definition filew (z : Z) : Prop :=
1273408 <= z < 1273412 \/ 1273416 <= z < 1273432 \/ 1273440 <= z < 1273456 \/ 1273464 <= z < 1273472 \/ 1273496 <= z < 1273512 \/ 1273544 <= z < 1273548.
Definition agree0 (M M' : word -> option byte) (S : Z) : Prop :=
forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M' x = M x.
Ltac flia := unfold filew; lia.
Ltac scc := first [ sc | dk_cell ltac:(unfold filew; dk_qlia) ].
Ltac xf0 Ms AG := dk_xf Ms AG ltac:(unfold filew; alia).
Section SE.
Local Abbreviation SEC_T_sn_cells_agree := (ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "N'R<yR0%211'8y8%511%311p051'@&QB+SoomohRTP0&QHr1+UZ0%3221%6251&Mr4r3r2%43321&Q0r5%211p011p051p0;1pRNC1pQ:E1pQ8F1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_sn_cells_agree) 0%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_sn_cells_agree) 1%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_sn_cells_agree) 2%nat 0%nat).
Lemma sn_cells_agree : ltac:(sec_stmt2 constr:(SEC_T_sn_cells_agree) 3%nat 0%nat).
Proof.
intros HS AG (C1 & C2 & C3 & (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & C5 & C6).
assert (X : forall (w : word) k bs, (bv_unsigned w + Z.of_nat k <= 1273408 \/ 1273560 <= bv_unsigned w) -> bv_unsigned w + Z.of_nat k <= 0x1000000 ->
rdn RSEGS M w k = Some bs -> rdn RSEGS M' w k = Some bs).
{ intros w k bs Hw Hw2 H. rewrite <- H. pose proof (bv_unsigned_in_range _ w) as Rw. apply rdn_ext; [lia|]. intros x Hx. apply AG; unfold filew; lia. }
unfold sn_cells, rt_layout_globs.
repeat split; first [ (eapply u8_ext; [intros x Hx; apply AG; unfold filew; lia | lia | lia | eassumption])
| (eapply u64_ext; [intros x Hx; apply AG; unfold filew; lia | lia | lia | eassumption])
| (apply X; [vm_compute; (left + right); intros Q; discriminate Q | vm_compute; intros Q; discriminate Q | assumption]) ].
Qed.
End SE.
Lemma mc_globs_agree : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "N'R<yR0%211'8y8%511%311p051'@&QB+SoomohRTP0&QHr1+UZ0%3221%6251&Mr4r3r2%43321&Ir5%211p011p051p0;1pRNC1pQ:E1pQ8F1").
Proof. intros M M' S.
intros HS AG (G1 & G2 & G3).
assert (X : forall (w : word) k bs, (bv_unsigned w + Z.of_nat k <= 1273408 \/ 1273560 <= bv_unsigned w) -> bv_unsigned w + Z.of_nat k <= 0x1000000 ->
rdn RSEGS M w k = Some bs -> rdn RSEGS M' w k = Some bs).
{ intros w k bs Hw Hw2 H. rewrite <- H. pose proof (bv_unsigned_in_range _ w) as Rw. apply rdn_ext; [lia|]. intros x Hx. apply AG; unfold filew; lia. }
unfold mc_icpt_globs. repeat split; (apply X; [vm_compute; (left + right); intros Q; discriminate Q | vm_compute; intros Q; discriminate Q | assumption]).
Qed.
Lemma cstr_nul : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "Q?'R<yR0%211'8y8%511%311p051'@'5%115&QBzr3%3221&Q@r4&QF&4%12>6%311%6251+9%8221&QG+2+R0%3221%A251'Or6r5%3421@C&Q4&Q=r7%B2O5%D11%G281%64541Kp081p0=1p0L1pTNQ11pT4Q21pT@Q51pQ8Q71").
Proof. intros M p bs t8.
intros Hp Hn [A _ _]. unfold L5.u8_at.
pose proof (Ja0DiagStrlen.rdn_byte_at M p _ _ (length bs) A ltac:(lia) Hp ltac:(lia)) as B.
rewrite app_nth2 in B by lia. replace (length bs - length bs)%nat with 0%nat in B by lia. exact B.
Qed.
Lemma u8_of_u32_5 : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "Q4'R<yR0%211'8y8%511%311p051'@&QBzr1%3221&Q@r2+4%3221&QG+2+R0%3221%<251&Q3&Q=r4r3+5%544321&Q4r5%247164p041p0;1p0E1pSDJ1pQ8L1").
Proof. intros M a.
intros Ha Hb C. unfold L5.u32_at in C. unfold L5.u8_at.
pose proof (Ja0DiagStrlen.rdn_byte_at M a _ _ 0%nat C ltac:(lia) Ha ltac:(lia)) as B. rewrite Z.add_0_r in B. rewrite B. repeat f_equal; try (apply bv_eq; vm_compute; reflexivity).
Qed.
Ltac shz :=
lazymatch goal with |- L5KA.zeros_at ?M ((?S - ?c) / 8 + ?d) ?l =>
let q := eval vm_compute in (c / 8) in
replace ((S - c) / 8) with (S / 8 - q) by (replace (S - c) with (S + (- q) * 8) by (clear; lia); rewrite Z_div_plus_full by (clear; lia); clear; lia);
unfold SB in *; dk_gmem end.
Definition PRE7 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 90549) 7 with Some l => l | None => [] end.
Definition SUF7 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 90558) 7 with Some l => l | None => [] end.
Lemma pre7_img : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "H':'8'5'R<y8%211%411%611&Q:&Q=yR0%811(0%118q031&R;+Rh]E%2271u7%;4:521(1&K%22@1%G3@41"). Proof. vm_compute. reflexivity. Qed.
Lemma suf7_img : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "H':'8'5'R<y8%211%411%611&Q:&Q=yR0%811(0%118q031&R;+Rh]N%2271u7%;4:521(1&L%22@1%G3@41"). Proof. vm_compute. reflexivity. Qed.
Lemma list_bv_eq : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "E'5'R<y8%211%411':'@%711&?&R=%118r2%449621r1%64;841%:3831r3%<3=16p031pT<?1pT:@1").
Proof. intros l1 l2.
revert l2. induction l1 as [|a l1 IH]; intros [|b l2] H; try discriminate H; [reflexivity|].
cbn [map] in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma PRE7_eq : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "Q1':'5'R<y8%211%411&K(3&R;+SE%2271+SC%4291+S1%62;1+S7%82=1+S5%:2?1+QJ%<2A1+Q0%>2C1(7%11D%B3E31%C3F61%D3G91%E3H<1%F3I?1%G3JB1%H3KE1%Q03KJ1").
Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.
Lemma SUF7_eq : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "M':'5'R<y8%211%411&L&2&Au4&R;yR0+QXTlbY0%3221%6251(3+RE%72>1+RD%92@1+:%;2B1(7%11C%93D31%:3E61%;3F91%D3G=1%L3GF1").
Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.
Lemma rdn_43 : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "R@'R<yR0%211'8y8%511%311p051'@&QBzr5%3221&Q@r6+7%3221&QG+2+R0%3221%<251&Q3&Q=r8r7%44321<&Q4r9+4%A261%44831Ar:+5%E261%84<31Er;+6%I261%<4@31I':'5%11Q5%Q811&Q:r<&R;%12Q>;u7%54J421(1&2&Au4%82QEF%3221(3%;2QEM%<2QFQ2%=2QGQ2(7%11QH%63QI31%73QJ51%83QK71%>3QL:1%@2H1%K3HB1p0M1p0Q21p0Q71p0Q=1p0QC1p0QM1pT2R21pT0R31pSNR41pU0R51pSDR61pQ8R81").
Proof. intros M a w b4 b5 b6.
unfold L5.u32_at, L5.u8_at. intros Ha Hb C0 C4 C5 C6. change 7%nat with (4 + 3)%nat.
apply rdn_app_Z; [lia | cbn; lia | exact C0|]. change (Z.of_nat 4) with 4.
apply rdn_cons; [lia | cbn; lia | exact C4|]. replace (a + 4 + 1) with (a + 5) by lia.
apply rdn_cons; [lia | cbn; lia | exact C5|]. replace (a + 5 + 1) with (a + 6) by lia. exact C6.
Qed.
Lemma rdn_7 : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "S2'R<yR0%211'8y8%511%311p051'@&QBzr8%3221&Q@r9+7%3221&QG+2+R0%3221%<251&Q4&Q=r;r:%44321<r<+1%@251%84731@r=%C25>%;4:21Cr>+3%G251%?4>31Gr?+4%K261%C4B31Kr@+5%O261%G4F31OrA+6%Q3261%K4J31Q3':'5%11Q?%QB11&Q:rB&R;%12QH;u7%54Q4421(1(3%62QJD%72QKI%82QLN%92QMQ2%:2QNQ7%;2QOQ;%<2R0Q;(7%11R1%:3R231%;3R351%<3R471%=3R591%>3R6;1%?3R7=1%@3R8?1%B2J1%M3JD1p0O1p0Q41p0Q91p0Q>1p0QC1p0QG1p0QL1p0R21p0R<1pT2RA1pT0RB1pSNRC1pSLRD1pSJRE1pSHRF1pSFRG1pSDRH1pQ8RJ1").
Proof. intros M a b0 b1 b2 b3 b4 b5 b6.
unfold L5.u8_at. intros Ha Hb C0 C1 C2 C3 C4 C5 C6.
apply rdn_cons; [lia | cbn; lia | exact C0|]. apply rdn_cons; [lia | cbn; lia | exact C1|].
replace (a + 1 + 1) with (a + 2) by lia. apply rdn_cons; [lia | cbn; lia | exact C2|].
replace (a + 2 + 1) with (a + 3) by lia. apply rdn_cons; [lia | cbn; lia | exact C3|].
replace (a + 3 + 1) with (a + 4) by lia. apply rdn_cons; [lia | cbn; lia | exact C4|].
replace (a + 4 + 1) with (a + 5) by lia. apply rdn_cons; [lia | cbn; lia | exact C5|].
replace (a + 5 + 1) with (a + 6) by lia. exact C6.
Qed.
Lemma PRE7_len : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue ":':'6&4'R<y8%211&K%5221u7%93821"). Proof. reflexivity. Qed.
Lemma SUF7_len : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue ":':'6&4'R<y8%211&L%5221u7%93821"). Proof. reflexivity. Qed.
Lemma stk_zsh : ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "QM'R<yR0%211'8y8%511%311p051'@':&QEr3+@%3221z%63721'9&QB&Q@+SoomohRTP0+UZ0%3221r4%6221+TPPPPPPPP0%8231%:231&Q6r6&QH&Q1&QAr5+8%3221%A251+e8%8221+e@%<3;21+UX0%<2=1%I21:%J2M;r7%K21Ar8%N221&Nr:%23146p041p091p0;1p0?1p0M1p0Q91pT>QA1pTBQB1pRNQC1pQ8QE1").
Proof. intros M S pd n.
intros Hal HS Z0 H1 Hn H2. apply zsh_of_hull. intros x Hx. unfold SB in *.
assert (E : S = 8 * (S / 8)).
{ pose proof (Z.div_mod S 16 ltac:(lia)) as D16. rewrite Hal in D16.
assert (Q : S / 8 = 2 * (S / 16)) by (symmetry; apply (Z.div_unique S 8 (2 * (S / 16)) 0); lia). lia. }
assert (L1 : S / 8 - 672 <= pd / 8) by (apply Z.div_le_lower_bound; lia).
assert (L2 : (pd + n - 1) / 8 <= S / 8) by (apply Z.div_le_upper_bound; lia).
assert (R8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
specialize (Z0 (bv_unsigned x - (2147450880 + S / 8 - 680)) ltac:(lia)).
replace (2147450880 + S / 8 - 680 + (bv_unsigned x - (2147450880 + S / 8 - 680))) with (bv_unsigned x) in Z0 by lia.
rewrite Z_to_bv_bv_unsigned in Z0. exact Z0.
Qed.
Section SE.
Local Abbreviation SEC_T_memcpy_stage := (ltac2:(TCodec.tc2 tcn__Ja0DiagGlue "X6'Q7&By5'R<yR0%211%5241'8y8%611%311p061'@'5%115':&Q8r7&R;&QFu1%211%42D1%7261+QS_[H%72E1%;3E31r8u2%:11%<2L1%?241r6%?2M1%C3M31r9u:%B11%D2Q41%G241%I3Q317r:u;%H11%J2Q:1%M241%O3Q91=r;u<%N11%Q02Q@1%Q3241%Q53Q?1C&4%12Q=F%Q411%Q93Q<Q71&QB&QG+2+Q8%3221%52Q31+SoomohRTP0&QHr<+RUH%3221%;251r=+Q?%=2<1%?231&H%129Kr>%321;&QCz%2214r@%4231'=&Q@r?%2251rB%G21E%O231%Q0239%8221%825;rC%M21K%Q5231%Q6239%>221rA%?261%Q:21=%A2>3%Q<219%D231&Q5&Q=rFrE%Q;21Q9%54431Q:rG%74614B%S81S1&Q:rH%S02S>8%QN2S:G%44<321(1%12S8J%S83831&Q2rI%211&IrJ%211&NrK%231?CrL%4316A';'9'G&Q9rQ1rQ0+^liH%SH2T61rO&Q;%11Q5%8576431r2r1%;5:2SH14%=3Q:41%T324S=rM%T32TA1%T73TA31'6&Q?(3u3u4u8u9uBuCuDuEuFuGuHuIuJuK(7%11B%A3C31%B3D51%C3E71%D3F91%E3G;1%F3H=1%G3I?1%H3JA1%I3KC1%J3LE1%K3MG1%L3NI1%M3OK1%N3Q0M1%O3Q1TL1%Q03Q2U51%Q23Q3Q:1r4%U91Q=%U;2UK1%U>231rQ2%U@213%UB3UL31p081pT8Q<1&R=%12V1QE%T62QKT4%SJ221%T?2QM3%SG221&<%72V7QL%TC2R11%SJ2R2QI%T1231%R;231%611r3%G11%D12%V53V:21p051p0=1pU2VB1&Q<%12R>R9%U52VARN%S;4SCR;R61%S72V>S0%V>3S>21%RJ251%RK281%RL2M1%RM2R;1%RN2R@1qQ:VH1%S12VI1qQ>VO1%S32W01p0S51p0S81p0S<1p0S@1p0SD1p0SN1p0T11p0T81p0T?1p0TF1p0U01p0U31p0U71p0U:1p0U=1p0UB1p0UI1p0V01p0V51p0V<1p0VC1p0VJ1p0W31pT4W@1pT>WC1pTDWD1pTBWE1pTFWF1pQ8WH1pQ<WN1pT6X51")) (only parsing).
Variable fx : ltac:(sec_ty2 constr:(SEC_T_memcpy_stage) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_memcpy_stage) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_memcpy_stage) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_memcpy_stage) 3%nat 0%nat).
Variable pd : ltac:(sec_ty2 constr:(SEC_T_memcpy_stage) 4%nat 0%nat).
Variable ps : ltac:(sec_ty2 constr:(SEC_T_memcpy_stage) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_memcpy_stage) 6%nat 0%nat).
Variable bs : ltac:(sec_ty2 constr:(SEC_T_memcpy_stage) 7%nat 0%nat).
Lemma memcpy_stage : ltac:(sec_stmt2 constr:(SEC_T_memcpy_stage) 8%nat 0%nat).
Proof.
intros G1 G2 G10 G11 G12 En Hn Hs1 Hs2 HappS HappD Hps0 Hpd0 DJS DJD OV W1 W2 RD HG HI ZS ZD.
assert (Hps : 0 <= ps /\ ps + n + 8 <= HIGHEND) by (unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *; lia).
assert (Hpd : 0 <= pd /\ pd + n + 8 <= HIGHEND) by (unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *; lia).
dk_fpreg_in G1. dk_fpreg_in G2. dk_fpreg_in G10. dk_fpreg_in G11. dk_fpreg_in G12.
assert (RET : ret_ok (Z_to_bv 64 1162616)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Dps : 0 <= (ps + n - 1) / 8 <= 2 ^ 44) by (unfold HIGHBEG, HIGHEND in *; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Dpd : 0 <= (pd + n - 1) / 8 <= 2 ^ 44) by (unfold HIGHBEG, HIGHEND in *; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
destruct (@diag_memcpy fx M s pd ps n bs (Z_to_bv 64 1162616) R) as (R' & Mj & RUN & V10 & KCS & OUT & GR).
- lia.
- exact HappS.
- exact HappD.
- lia.
- lia.
- unfold SB. lia.
- unfold SB. lia.
- intros _. exact DJS.
- intros _. exact DJD.
- exact OV.
- apply (store_ok_of_writable M (s - 2232) 2232); [exact W1 | reflexivity].
- apply (store_ok_of_writable M pd n); [exact W2 | rewrite En; rewrite Nat2Z.id; reflexivity].
- rewrite En, Nat2Z.id. exact RD.
- exact RET.
- exact HG.
- exact HI.
- exact ZS.
- exact ZD.
- exact G1.
- exact G2.
- exact G10.
- exact G11.
- exact G12.
- exists R', (wbytes Mj (Z_to_bv 64 pd) bs). unfold HIGHBEG, HIGHEND in *.
split. { replace (0x77338%bv : word) with (Z_to_bv 64 0x77338) in RUN by (apply bv_eq; reflexivity). exact RUN. }
split. { rewrite (getr_reg R' 10 10%bv eq_refl). exact V10. }
split. { intros k Hk. apply (keeps_cs_reg R R' k KCS Hk). }
split. { intros x Hx Hd. rewrite MemSplit.wbytes_outside; [apply OUT; exact Hx | rewrite L5.unsigned_lit by lia; lia | rewrite L5.unsigned_lit by lia; lia]. }
split. { eapply mem_grows_trans; [exact GR | apply wbytes_grows]. }
apply SeqExec.rdn_wbytes_hit. rewrite L5.unsigned_lit by lia. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_wv_entry_stage := (forall fx (R : bvmap 5 word) (M : word -> option byte) (f sp buf len wpos wbase fd : Z), getr R (reg 9) = Z_to_bv 64 f -> getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 11) = Z_to_bv 64 buf -> getr R (reg 8) = Z_to_bv 64 len ->
0 <= sp -> sp + 40 < 2 ^ 63 -> 0 <= f -> (f + 124 <= sp + 8 \/ sp + 40 <= f) -> f + 124 < 2 ^ 63 ->
0 <= wbase <= wpos -> wpos < 2 ^ 63 -> 0 <= len < 2 ^ 62 -> 0 <= buf < 2 ^ 64 -> 0 <= fd < 2 ^ 31 ->
L5.u64_at RSEGS M (f + 40) wpos -> L5.u64_at RSEGS M (f + 56) wbase -> L5.u32_at RSEGS M (f + 120) fd -> L5.writable RSEGS M (sp + 8) 32 ->
exists R' M',
msteps RSEGS (st fx R 0x11b2b8 M) (st fx R' 0x11b304 M')
/\ getr R' (reg 17) = Z_to_bv 64 66 /\ getr R' (reg 10) = Z_to_bv 64 fd
/\ getr R' (reg 11) = Z_to_bv 64 (if Z.eqb wpos wbase then sp + 24 else sp + 8) /\ getr R' (reg 12) = Z_to_bv 64 (if Z.eqb wpos wbase then 1 else 2)
/\ getr R' (reg 18) = Z_to_bv 64 (if Z.eqb wpos wbase then 1 else 2) /\ getr R' (reg 19) = Z_to_bv 64 (if Z.eqb wpos wbase then sp + 24 else sp + 8)
/\ getr R' (reg 22) = Z_to_bv 64 (wpos - wbase + len)
/\ (forall k, In k [1; 2; 3; 4; 8; 9; 20; 21; 23; 24; 25; 26; 27]%nat -> getr R' (reg k) = getr R (reg k))
/\ L5.u64_at RSEGS M' (sp + 8) wbase /\ L5.u64_at RSEGS M' (sp + 16) (wpos - wbase) /\ L5.u64_at RSEGS M' (sp + 24) buf /\ L5.u64_at RSEGS M' (sp + 32) len
/\ (forall x : word, ~ (sp + 8 <= bv_unsigned x < sp + 40) -> M' x = M x)
/\ mem_grows M M') (only parsing).
Variable fx : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 2%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 4%nat 0%nat).
Variable buf : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 5%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 6%nat 0%nat).
Variable wpos : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 7%nat 0%nat).
Variable wbase : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 8%nat 0%nat).
Variable fd : ltac:(sec_ty2 constr:(SEC_T_wv_entry_stage) 9%nat 0%nat).
Lemma wv_entry_stage : ltac:(sec_stmt2 constr:(SEC_T_wv_entry_stage) 10%nat 0%nat).
Proof.
intros G9 G2 G11 G8 Hs0 Hs1 Hf0 Hfs Hf1 Hw0 Hw1 Hlen Hbuf Hfd C40 C56 C120 W.
dk_fpreg_in G9. dk_fpreg_in G2. dk_fpreg_in G11. dk_fpreg_in G8.
destruct (@wv_entry fx M (seg_rom RSEGS) f sp buf len wpos wbase fd (conj Hs0 Hs1) (conj Hf0 (conj Hfs Hf1)) (conj Hw0 Hw1) Hlen Hfd C40 C56 C120
(store_ok_of_writable M (sp + 8) 32 32 W eq_refl) R G9 G2 G11 G8) as (R' & RUN & V17 & V10 & V11 & V12 & V18 & V19 & V22 & K).
exists R', (wve_mem M sp buf len wpos wbase).
replace (0x11b2b8%bv : word) with (Z_to_bv 64 0x11b2b8) in RUN by (apply bv_eq; reflexivity).
replace (0x11b304%bv : word) with (Z_to_bv 64 0x11b304) in RUN by (apply bv_eq; reflexivity).
unfold wve_iov, wve_cnt in *.
split; [exact RUN|].
split. { rewrite (getr_reg R' 17 17%bv eq_refl). exact V17. } split. { rewrite (getr_reg R' 10 10%bv eq_refl). exact V10. }
split. { rewrite (getr_reg R' 11 11%bv eq_refl). exact V11. } split. { rewrite (getr_reg R' 12 12%bv eq_refl). exact V12. }
split. { rewrite (getr_reg R' 18 18%bv eq_refl). exact V18. } split. { rewrite (getr_reg R' 19 19%bv eq_refl). exact V19. }
split. { rewrite (getr_reg R' 22 22%bv eq_refl). exact V22. }
split. { intros k Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [dk_kb K|]). destruct Hk. }
unfold wve_mem, W64.
assert (X : forall a v Mx, 0 <= a -> a + 8 < 2 ^ 63 -> L5.u64_at RSEGS (wbytes Mx (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v))) a v).
{ intros a v Mx Ha Hb. unfold L5.u64_at. apply SeqExec.rdn_wbytes_hit8. rewrite L5.unsigned_lit by lia. lia. }
assert (Y : forall a b v w Mx, 0 <= a -> a + 8 < 2 ^ 63 -> 0 <= b -> b + 8 < 2 ^ 63 -> (a + 8 <= b \/ b + 8 <= a) -> L5.u64_at RSEGS Mx a v ->
L5.u64_at RSEGS (wbytes Mx (Z_to_bv 64 b) (word_to_le_bytes 8 (Z_to_bv 64 w))) a v).
{ intros a b v w Mx Ha Ha' Hb Hb' D C. unfold L5.u64_at in *. rewrite rdn_wbytes_out; [exact C | | |];
rewrite ?length_N_to_le_bytes; rewrite !L5.unsigned_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia. }
split. { apply Y; try lia. apply Y; try lia. apply Y; try lia. apply X; lia. }
split. { apply Y; try lia. apply Y; try lia. apply X; lia. }
split. { apply Y; try lia. apply X; lia. }
split. { apply X; lia. }
split. { intros x Hx. rewrite !MemSplit.wbytes_outside; try reflexivity; rewrite ?length_N_to_le_bytes; rewrite ?L5.unsigned_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia. }
repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.
End SE.
End DG.

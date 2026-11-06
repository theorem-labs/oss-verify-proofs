(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
FPSteps AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SegRunStrlen () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanCore.APC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSound.APS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegRun.SR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegRunStrlen.SRS.WithSegs."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3map"]; ["4Z"; "0E"; "5bytes_le_to_Z"; "6bvmap"; "0R"; "0R'"; "7sr_fresh"; "7sr_vars_lt"; "8ext_list"; "9ELit"; "9LHit"; "9SA"; "9adenot"; "9env"; "9expr"; "9kentry"]; ["9know_lookup"; "9lres"; "9sidecond"; "9sr_upd"; ":estart"; ":flat"; ":know_ok"; ":rd1"; ":regs_ok"; ";getr"; ";rdn"; "<byte_zero"; "<bytes_nonzero"; "<ro_covered"; "<strlen_spec"; "<strlen_step_stmt"]; ["<words_readable"; "=SL"; ">NoDup"; "?add"; "?le"; "?lt"; "?modulo"; "?of_nat"; "?pow"; "0a"; "0b"; "0fk"; "0h"; "0i"; "0k"; "0kz"]; ["0m"; "0n"; "0nb"; "0nx"; "0off"; "0r"; "0ro_hi"; "0ro_lo"; "0sb"; "0segs"; "0sk"; "0sr"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"]; ["0x_len"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module SRS.
Section WithSegs.
Variable segs : list Segment.
Definition SL : list nat := [11; 12; 13; 14; 15; 16]%nat.
Lemma SL_nodup : ltac2:(TCodec.tc2 tcn__SegRunStrlen "4'QB'6&QA%3221").
Proof.
unfold SL. repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.
Lemma regs_after_strlen : ltac2:(TCodec.tc2 tcn__SegRunStrlen "S<'M'5'N%211&Cy5'R>yR0%211%5241'6'@&Q8r6r5r4%43321'<'2&Gr3%2218(9%63521%B1C&>r1(R<+:(:%33I21%>3751%711r2+;%83N16%C3<31%<11+<%<3Q21:%G3@D1%@11+=%@3Q61>%K3DM1%D11+>%D3Q:1B%O3HQ21%H11+?%H3Q>1F%Q33LQ71%L11r7+@%M3QC1K%Q83Q131%Q111&Q9r=r8%3221r>%5213%Q@3QI31p081p0>1p0C1p0H1p0M1p0Q21p0Q81pT<QA1%?2QMQ<&R=%12R5QM%QL3R531&Hr:&?&QG%11QH%82R>1%I2G1qT<R;1&QA%74R=R?21%:39R;1&Q3&Fr9%2316R?u:(I%11RA%73431%RE391Q;p0E1p0J1p0R=1p0RE1pT0RK1pT8RM1pQ<RO1pQ:S01pTHS71pQ4S;1").
Proof.
intros E sr R R' nx kz HR Hsv Hkept Ha0.
set (E' := APS.ext_list E nx (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) SL)).
pose proof (APS.ext_list_agree E nx (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) SL)) as Hag. fold E' in Hag.
rewrite APS.sr_vars_lt_eq in Hsv.
assert (OLD : forall i, (i < 32)%nat -> edenot E' (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
{ intros i Hi. symmetry. apply (APS.edenot_agree' nx); [exact Hag|]. apply APSX.nth_sr_vars_lt'; assumption. }
apply APSX.regs_ok_pointwise. intros r Hr0.
pose proof (ridx_range r) as Hrr.
rewrite nth_sr_upd.
destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10].
{ rewrite (APSX.reg_of_ridx r 10 H10). cbn [edenot]. exact Ha0. }
destruct (in_dec Nat.eq_dec (ridx r) SL) as [Hin|Hnin].
- destruct (In_nth SL (ridx r) 0%nat Hin) as (j & Hj & Hnth).
rewrite <- Hnth at 1. rewrite APSX.nth_sr_fresh_in by (apply SL_nodup || exact Hj).
cbn [edenot]. unfold E'. rewrite APS.ext_list_at by (rewrite length_map; exact Hj).
rewrite (map_nth (fun r0 => getr R' (Z_to_bv 5 (Z.of_nat r0))) SL 0%nat j) || idtac.
replace (nth j (map (fun r0 : nat => getr R' (Z_to_bv 5 (Z.of_nat r0))) SL) (Z_to_bv 64 0))
with (getr R' (Z_to_bv 5 (Z.of_nat (nth j SL 0%nat)))).
2:{ clear - Hj. unfold SL in *. cbn [length] in Hj.
do 6 (destruct j as [|j]; [reflexivity|]). lia. }
rewrite Hnth. rewrite <- (APSX.reg_of_ridx r _ eq_refl). reflexivity.
- rewrite APSX.nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
assert (NE : forall n, In n (10%nat :: SL) -> r <> Z_to_bv 5 (Z.of_nat n)).
{ intros n Hn X. subst r. unfold SL in Hn. cbn [In] in Hn.
assert (RX : forall m, (m < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat m)) = m).
{ intros m Hm. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
rewrite Z.mod_small by lia. lia. }
repeat (destruct Hn as [<-|Hn]; [rewrite RX in * by lia; apply Hnin || apply H10; cbn; auto 10; fail|]).
exact Hn. }
rewrite (Hkept r); try (intros X; subst r; first [apply H10; reflexivity | apply Hnin; cbn; tauto]).
pose proof (HR r) as X. unfold sr_get in X.
destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
exact X.
Qed.
Lemma lez_1 : ltac2:(TCodec.tc2 tcn__SegRunStrlen "@'R>y8%211'<'@&B(3r1(7%117%43831%611&R?%12<6%;3:31pSF=1").
Proof. intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.
Lemma byte_hit_sound : ltac2:(TCodec.tc2 tcn__SegRunStrlen "RG'M'R>yR0%211'8y8%511%311p051'5'O%211'N'@'2%611&Q6vR9r7r6r5%544321'<'Q1&Q0r4u1(4(7%11?'Q2%311%88?=<76531(J(Ir3%211r2%53271%A3@71&Q5r9(K%12HG+1%53421'=';%Q71Q:%Q=11&Q:r:&Lr;r8%=21Q5%4231%74Q861O(1(3r1%Q11QG%33QH21%52?1%Q:3?71&R?%12QM6&QF&QH+2+R0%3221%52QE1%QC3QL71%K2:1qSFR51%N2R61p0Q01p0Q71p0QJ1pSJR11pU4R41pT:R51pTBR71pSNR91pT2R=1pQ4RF1").
Proof.
intros E m k sb off z h HK HL Hfl.
pose proof (know_lookup_sound segs E m k sb off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
destruct bs as [|b [|]]; try discriminate. exists b. split; [exact Hrd|].
unfold extz in Hv. rewrite lez_1 in Hv. cbn [edenot] in Hv.
apply (f_equal bv_unsigned) in Hv. rewrite !Z_to_bv_unsigned in Hv. unfold bv_wrap in Hv.
change (bv_modulus 64) with (2 ^ 64) in Hv. pose proof (u8_range b).
rewrite Z.mod_small in Hv by lia. exact Hv.
Qed.
Lemma bytes_nonzero_sound : ltac2:(TCodec.tc2 tcn__SegRunStrlen "RM'M'R>yR0%211'8y8%511%311p051'5'O%211'N'6'@&Q6vR9r7r6r4%544321'<'2&Q<r5r2r3%46;93821(9%83721';&QDzr1%3221&QE&QG%11=%3251%9251&Q5r;(K&QC%12DC%32L1+1%73621p091pSLQ31%>1Q0%@2B1%F2B1'=%Q=1Q@%QC11&Q:r<&Lr=r9%B2Q<Q3%D221%5241u1%94QA821(1(3(7%11QO%33R0Q51%52A1%QC3A71&>&R?%12R6Q:%QG3QN1Q<%411%Q@261qSFR91%K2R:1p0M1pSLR41p0Q21p0QG1p0R11pT:R81pT6R:1pTBR<1pSNR>1pSHR?1pT2RC1pQ4RL1").
Proof.
intros E m fk k sb nb. induction nb as [|nb IH]; intros off HK H Hfl i Hi; [lia|].
cbn [SR.bytes_nonzero] in H.
destruct (know_lookup segs k sb off 1 false [] []) as [v scs h| | ] eqn:HL; try discriminate.
destruct v as [z| | | | | | |]; try discriminate. destruct scs; [|discriminate].
apply andb_true_iff in H as [Hz Hrest]. apply negb_true_iff in Hz. apply Z.eqb_neq in Hz.
destruct (Z.eq_dec i 0) as [->|Hi0].
- rewrite Z.add_0_r. destruct (byte_hit_sound E m k sb off z h HK HL) as (b & Hrd & Hb).
{ specialize (Hfl 0 ltac:(lia)). rewrite Z.add_0_r in Hfl. exact Hfl. }
exists b. split; [exact Hrd|]. rewrite Hb. intros X. apply Hz.
apply (proj2 (Z.mod_divide z 256 ltac:(lia))). apply (Z.divide_trans _ (2 ^ 64)); [exists (2 ^ 56); reflexivity|].
apply (proj1 (Z.mod_divide z (2 ^ 64) ltac:(lia))). exact X.
- destruct (IH (off + 1) HK Hrest) with (i := i - 1) as (b & Hrd & Hb).
+ intros i' Hi'. replace (off + 1 + i') with (off + (1 + i')) by lia. apply Hfl. lia.
+ lia.
+ exists b. replace (off + i) with (off + 1 + (i - 1)) by lia. split; assumption.
Qed.
Lemma byte_zero_sound : ltac2:(TCodec.tc2 tcn__SegRunStrlen "R5'M'R>yR0%211'8y8%511%311p051'5'O%211'N'@&Q6vR9r5r4r3%544321'<'2&Q;r2%249761(9%63521&Q5r7(K%12=<+1%53421'=';%J1M%Q011&Q:r8&Lr9r6%=21J%4231u1%84N721(1(3r1(7%11Q<%43Q=31%62A1%Q13A81&R?%12QB7z%Q53Q<21%H251qSFQE1%K2QF1p0M1p0Q41p0Q<1pT:QC1pTBQE1pSNQG1pT2QK1pQ4R41").
Proof.
intros E m k sb off HK H Hfl. unfold SR.byte_zero in H.
destruct (know_lookup segs k sb off 1 false [] []) as [v scs h| | ] eqn:HL; try discriminate.
destruct v as [z| | | | | | |]; try discriminate. destruct scs; [|discriminate]. apply Z.eqb_eq in H.
destruct (byte_hit_sound E m k sb off z h HK HL Hfl) as (b & Hrd & Hb).
exists b. split; [exact Hrd|]. pose proof (u8_range b).
rewrite <- (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Hb.
rewrite Z.mod_mod_divide; [exact H|]. exists (2 ^ 56). reflexivity.
Qed.
Lemma words_readable_sound : ltac2:(TCodec.tc2 tcn__SegRunStrlen "RD'M'R>yR0%211'8y8%511%311p051'5'O%211'N'6'@&Q6vR9r7r6r5%544321r8%746153'<'2&Q@r3r4%36<;:921(9%73621';&QDzr1%3221&QE&QG%11D%3251%9251&Q5r<(K&QCr2%22L1%42J1+1%83721'=%Q:1Q=%Q@11&Q:&Lr=r9%=2Q8O%?221%5241u1%84Q=C21(1(3(7%11QK%33QLQ01%52@1%Q=3@71qSFQO1%D2R01%Q82F1p0Q01pSLQK1p0Q<1p0QE1p0QH1pT:QO1pT6R11pTBR31pSNR51pSHR61pT2R:1pQ4RC1").
Proof.
intros E m fk k sb nb. induction nb as [|nb IH]; intros off HKf HK H i Hi; [lia|].
cbn [SR.words_readable] in H. apply andb_true_iff in H as [H1 Hrest].
destruct (Z.eq_dec i 0) as [->|Hi0].
- rewrite Z.add_0_r.
destruct (kn_readable_sound segs E m fk m k sb off 1 HKf HK ltac:(lia) ltac:(lia) H1) as (Hfl & bs & Hrd & Hlen).
split; [exact Hfl|]. destruct bs as [|b [|]]; try discriminate. exists b. exact Hrd.
- destruct (IH (off + 1) HKf HK Hrest (i - 1) ltac:(lia)) as (Hfl & b & Hrd).
replace (off + i) with (off + 1 + (i - 1)) by lia. split; [exact Hfl | exists b; exact Hrd].
Qed.
Lemma ro_covered_sound : ltac2:(TCodec.tc2 tcn__SegRunStrlen "QA'M'R>yR0%211'8y8%511%311p051'5'O%211'@&Q6vR9r5r4r3%544321'<'2&Q=r2%23617(9%63521';&QDr1%22>1&QE%123?%6231r8&R=%12Q1=%311(0%11Q0%D3Q031p081pSLM1p0A1p0I1pT>Q01pT@Q11pSNQ31pT2Q71pQ4Q@1").
Proof.
intros E m k ro_lo ro_hi HK H i Hi. unfold SR.ro_covered in H.
apply existsb_exists in H as (K & Hin & HKc).
destruct K; try discriminate. apply andb_true_iff in HKc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as Hok. cbn [kentry_ok] in Hok.
destruct Hok as (_ & _ & Hnone). apply Hnone. lia.
Qed.
Lemma rdn1_rd1 : ltac2:(TCodec.tc2 tcn__SegRunStrlen "Q6'R>yR0%211'8y8%511%311p051'<'5%115%811&Q:vR9r3r2u1%544321(1(3r1(7%11A%43B31%62>1%A3>81&>&Q7r4%23@1?(0%11J%H3J31%711p091pSFN1pSDQ21pT2N1").
Proof.
intros m a b H. unfold rd1. cbn [rdn] in H.
destruct (m a) as [x|]; [discriminate|]. destruct (seg_rom segs a); discriminate.
Qed.
Lemma flat_byte : ltac2:(TCodec.tc2 tcn__SegRunStrlen "Q0'M'N'@&Q5r5(Kr4r3%3221r2%73621';&QDz%2215&QE%1279%6231r7r6&QC%12A>%A231+1%E3621p081p0@1pSLI1pT4J1pTFK1pTBM1pQ4O1").
Proof. intros E sb sk n i Hf Hi. unfold flat, estart in *. cbn [a_base a_off] in *. lia. Qed.
Lemma estart_off : ltac2:(TCodec.tc2 tcn__SegRunStrlen "F'M'N'@'<&Q4r4(Kr3&QCr2r1%3221%6251%9281%8275%;2:1%8216%>3?41pSL@1pTFA1pTBC1pQ4E1").
Proof. intros. unfold estart. cbn [a_base a_off]. lia. Qed.
Theorem strlen_step_sound : ltac2:(TCodec.tc2 tcn__SegRunStrlen ">'@&Q>vR9r2r1r3%544321&Q?r4%247146p041pT>;1pT@<1pU2=1").
Proof.
intros x_len ro_lo ro_hi STRLEN fx kz ss w ss' w' E R M Hcl H [HR HK].
pose proof Hcl as Hcl0. unfold SR.closed in Hcl0.
apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
destruct (SR.closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
cbv zeta beta delta [SR.step_strlen] in H.
destruct (Z.eqb (s_pc ss) x_len) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
destruct (SR.ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
destruct (split_lit (SR.reg ss 10)) as [sb sk] eqn:Hsp.
destruct (xhi (facts_of (s_know ss)) (SR.reg ss 10)) as [shi|] eqn:Hshi; [|discriminate].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
apply SR.some_pair_inj in H as [<- <-].
repeat (apply andb_true_iff in Hc as [Hc ?X]).
rename X into Hro. rename X0 into Hfl. rename X1 into Hwr. rename X2 into Hzb. rename X3 into Hnzb. rename X4 into Hal. rename X5 into Hhi.
apply Z.leb_le in Hc. apply Z.ltb_lt in Hhi. apply Z.leb_le in Hal. unfold two64 in Hhi.
set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := SR.wden segs E M w) in *. set (nx := s_next ss) in *.
set (n := sk + kz - (sk + kz) mod 8 + 8 - sk) in *.
pose proof (Z.mod_pos_bound (sk + kz) 8 ltac:(lia)) as HM8.
assert (Hn1 : kz + 1 <= n <= kz + 8) by (subst n; lia).
pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
pose proof (SR.reg_sound10 E ss R HR) as R10.
pose proof (xhi_sound segs E m fk (SR.reg ss 10) shi HKf Hshi) as XS.
rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) sb sk Hsp) in R10, XS.
set (S := estart E (SA sb sk)) in *.
change (bv_unsigned (edenot E sb) + sk) with S in R10, XS.
pose proof (u64_range (Z_to_bv 64 S)) as HS0.
assert (Hnlt : 0 <= n < 2 ^ 64) by (clear - Hn1 Hc Hhi XS HS0; lia).
assert (Hlen : bv_unsigned (edenot E (ELit n)) = n) by (cbn [edenot]; apply u64_of_Z; exact Hnlt).
destruct (APSX.w_flat_x_sound segs E m fk sb sk (ELit n) HKf Hfl) as (Slo & Shi & _). rewrite Hlen in Shi.
fold S in Slo, Shi.
assert (HS64 : 0 <= S < 2 ^ 64) by (clear - Slo Shi Hn1 Hc; lia).
rewrite (u64_of_Z S HS64) in XS.
set (s := Z_to_bv 64 S) in *.
assert (Hus : bv_unsigned s = S) by (subst s; apply u64_of_Z; exact HS64).
assert (FL : flat E (SA sb sk) n) by (unfold flat; fold S; clear - HS64 Shi Hn1 Hc; lia).
destruct (ealign_sound segs E m k sb HK) as [Hal64 Hdiv].
assert (B8 : bv_unsigned (edenot E sb) mod 8 = 0).
{ destruct Hdiv as [q Hq]. rewrite Hq.
assert (P : 2 ^ ealign k sb = 2 ^ (ealign k sb - 3) * 8).
{ replace (ealign k sb) with (ealign k sb - 3 + 3) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
rewrite P, Z.mul_assoc. apply Z_mod_mult. }
assert (MODS : forall x, (S + x) mod 8 = (sk + x) mod 8).
{ intros x. subst S. unfold estart. cbn [a_base a_off].
rewrite <- Z.add_assoc. rewrite Z.add_mod, B8, Z.add_0_l by lia. apply Z.mod_mod. lia. }
assert (BYTE : forall i, 0 <= i < n ->
exists b, rdn segs m (Z_to_bv 64 (S + i)) 1 = Some [b]
/\ (i < kz -> bv_unsigned b <> 0) /\ (i = kz -> bv_unsigned b = 0)).
{ intros i Hi.
assert (AD : adenot E (SA sb (sk + i)) = Z_to_bv 64 (S + i)) by (rewrite APSX.adenot_SA, estart_off; reflexivity).
destruct (Z.lt_total i kz) as [Hlt|[Heq|Hgt]].
- destruct (bytes_nonzero_sound E m fk k sb (Z.to_nat kz) sk HK Hnzb) with (i := i) as (b & Hrd & Hb).
+ intros i' Hi'. eapply flat_byte; [exact FL | lia].
+ lia.
+ rewrite AD in Hrd. exists b. split; [exact Hrd|]. split; [intros _; exact Hb | intros; lia].
- subst i. destruct (byte_zero_sound E m k sb (sk + kz) HK Hzb ltac:(eapply flat_byte; [exact FL | lia])) as (b & Hrd & Hb).
rewrite AD in Hrd. exists b. split; [exact Hrd|]. split; [intros; lia | intros _; exact Hb].
- destruct (words_readable_sound E m fk k sb (Z.to_nat (sk + kz - (sk + kz) mod 8 + 8 - (sk + kz + 1))) (sk + kz + 1) HKf HK Hwr
(i - kz - 1) ltac:(lia)) as (_ & b & Hrd).
replace (sk + kz + 1 + (i - kz - 1)) with (sk + i) in Hrd by lia.
rewrite AD in Hrd. exists b. split; [exact Hrd|]. split; intros; lia. }
destruct (rdn_defined segs m (Z.to_nat n) s) as (buf & Hbuf & Hlbuf).
{ rewrite Hus. clear - Shi Hnlt. lia. }
{ intros j Hj. destruct (BYTE (Z.of_nat j) ltac:(lia)) as (b & Hrd & _). rewrite Hus. eapply rdn1_rd1. exact Hrd. }
assert (NTH : forall i, 0 <= i < n -> exists b, nth (Z.to_nat i) buf (Z_to_bv 8 0) = b
/\ (i < kz -> bv_unsigned b <> 0) /\ (i = kz -> bv_unsigned b = 0)).
{ intros i Hi. destruct (BYTE i Hi) as (b & Hrd & Hb1 & Hb2). exists b.
pose proof (APSX.rdn_nth segs m (Z.to_nat n) s buf (Z.to_nat i) ltac:(rewrite Hus; clear - Shi Hnlt; lia) Hbuf ltac:(lia)) as X.
rewrite Hus, Z2Nat.id in X by lia. rewrite Hrd in X. injection X as <-. split; [reflexivity | split; assumption]. }
destruct (SR.ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
assert (R10' : getr R 10%bv = s) by exact R10.
destruct (STRLEN fx m s buf kz (seg_rom segs) R (Z_to_bv 64 ret) ltac:(rewrite Hlbuf; exact Hbuf)) as (regs' & Hms & Hkept & Ha0).
{ rewrite Hus, Hlbuf, Z2Nat.id by lia.
pose proof (Z.div_mod (S + kz) 8 ltac:(lia)) as D1. rewrite (MODS kz) in D1. subst n. clear - D1 HM8 Hc. lia. }
{ rewrite Hus, Hlbuf, Z2Nat.id by lia. clear - XS Hhi. lia. }
{ exact Hc. }
{ destruct (NTH kz ltac:(lia)) as (b & <- & _ & Hb). apply Hb. reflexivity. }
{ intros j Hj. destruct (NTH (Z.of_nat j) ltac:(lia)) as (b & Hb & Hnz & _). rewrite Nat2Z.id in Hb. rewrite Hb. apply Hnz. lia. }
{ eapply ro_covered_sound; [exact HK | exact Hro]. }
{ exact Hrok. }
{ exact R1. }
{ exact R10'. }
set (E' := APS.ext_list E nx (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) SL)).
pose proof (APS.ext_list_agree E nx (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) SL)) as Hag. fold E' in Hag.
exists fx, E', regs'.
split; [exact Hag|]. split; [cbn [s_next]; lia|].
assert (Hw : SR.wden segs E' M w = m) by (symmetry; eapply SR.wden_agree; [exact Hag | exact Fw]).
split.
- split.
+ cbn [s_regs s_next]. apply (regs_after_strlen E (s_regs ss) R regs' nx kz HR Fsr0 Hkept Ha0).
+ cbn [s_know]. rewrite Hw. eapply APS.know_ok_agree'; [exact Hag | exact Fkn0 | exact HK].
- cbn [s_pc]. rewrite Hw, Hpc. exact Hms.
Qed.
End WithSegs.
End SRS.

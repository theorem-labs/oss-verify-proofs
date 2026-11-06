(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem JatCls JatCellEx JatPoison
ArtBridge JatInv JatInvMalloc JatLift JatWrapKit JatFsInv JatFsInvLaws Ja0RegionPoisoned Ja0AsanMemcpy.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JatWrapC JatWrapVis.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapRng () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0AsanMemcpy."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLift."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"]; ["0FF"; "0L"; "0LB"; "0LK"; "4store_ok"; "4word_to_le_bytes"; "5page_base"; "6bvmap"; "0M"; "0R"; "0R'"; "7bhid"; "8mrestrict"; "8page_allowedb"; "9in_block"; "9regs_preserved"]; [":BIGSHADOW_HI"; ":BIGSHADOW_LO"; ":FS_BYTES"; ":S"; ":aacc"; ":aclient"; ":aclientw"; ":app_rng"; ":ar_fs"; ":ar_sptop"; ":art_private"; ":fframe"; ":hl_img_hi"; ":hl_img_lo"; ":hl_rt_static"; ":in_fframe"]; [":shadow_allowed"; ";in_app8"; "<SB"; "=art_client_ok"; "=art_run"; "=rn_HI"; "=rn_ar"; ">art_vis"; "?rdn"; "@keeps_cs"; "Aloaded_segments"; "Badd"; "Bdiv"; "Ble"; "Blt"; "Bmodulo"]; ["Bof_nat"; "Bpow"; "Bsub"; "0a"; "0b"; "0bs"; "0fS"; "0hi"; "0i"; "0k"; "0lS"; "0lo"; "0model"; "0n"; "0p"; "0rn"]; ["0scr"; "0sp"; "CZ_to_bv"; "Cbv"; "Cbv_unsigned"; "0w0"; "0w1"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section SE.
Variables (R R' : bvmap 5 word).
Lemma keeps_cs_preserved : keeps_cs R R' -> regs_preserved R R'.
Proof.
intros KC r Hr.
unfold callee_saved_idx in Hr. rewrite <- (Z_to_bv_bv_unsigned _ r). set (z := bv_unsigned r) in *. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [apply KC; unfold callee_saved; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right] |]). destruct Hr.
Qed.
End SE.
Ltac lit_cell H :=
unfold cell in H;
match type of H with rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
match goal with |- rdn _ _ ?w _ = _ => replace w with (Z_to_bv 64 a : word) by (apply bv_eq; reflexivity); exact H end end.
Ltac conj_find H := first [ exact H | exact (proj1 H) | let H' := fresh in pose proof (proj2 H) as H'; conj_find H' ].
Lemma le1_one : ltac2:(TCodec.tc2 tcn__JatWrapRng "C';'4'RCy8%211%411&Eu1&RByR0+1%3221%6251(3%62;4(6%11<%43=31%B3=61").
Proof. vm_compute. repeat f_equal; apply bv_eq; reflexivity. Qed.
Lemma art_cli_facts : ltac2:(TCodec.tc2 tcn__JatWrapRng "QO'QD'4'8'?%2211%411&Q;%611'RCyR0%211'7y8%511%311p051&QCr6r5r4r3r2r1%76654321':&Q@&R2&Q9&QFr7%211%411+XPPP0%7221&R1+2+Q?%3221%<215%>3C61&Q8%11;&Q2%B3G21+RPP0+VbTP0%D212%F3K31&QM&QK+@%22D1%421?%M261%N2;1%O2@1p0Q11pQBQ:1p2QE1pQ8QD1pQ2QE1pQ6QH1pU0QN1").
Proof. intros rn LB FF LK A M (_ & _ & C3 & C4 & _ & _ & _ & _ & _ & _ & C11 & C12 & _). repeat split; assumption. Qed.
Lemma art_rng_off_window : ltac2:(TCodec.tc2 tcn__JatWrapRng "Q7'?&QNzr3%3221r2%5231':&QMr1%2281r6%;231%6231&=&QKr8%221<%:271r5%C231%>231%811p0:1pTBH1'>r7%<21@%D219r4%F214%6231p081p0K1p0N1pT@Q31pTHQ41pTLQ51pTNQ61").
Proof.
intros p n lo hi Hn Hw OFF. destruct (Z_lt_le_dec p hi) as [Lt | Ge]; [left | right; exact Ge].
pose proof (OFF 0 ltac:(lia)) as O0. rewrite Z.add_0_r in O0.
destruct (Z_lt_le_dec lo (p + n)) as [X | X]; [|lia].
exfalso. apply (OFF (lo - p) ltac:(lia)). lia.
Qed.
Lemma in_block_dec : ltac2:(TCodec.tc2 tcn__JatWrapRng "?'4'8'?%2211%411'>&Nr2r1%3221&=%112%7231pU@;1pQ6:1").
Proof.
induction LB as [|b LB IH]; intros x; [right; intros (b & [] & _)|].
destruct (IH x) as [H | H]; [left; destruct H as (b' & Hb' & R); exists b'; split; [right; exact Hb' | exact R]|].
destruct (Z_le_gt_dec (fst b) x) as [L1 | L1]; [destruct (Z_lt_le_dec x (fst b + snd b)) as [L2 | L2]|].
- left. exists b. split; [left; reflexivity | lia].
- right. intros (b' & [<- | Hb'] & R); [lia | apply H; exists b'; split; assumption].
- right. intros (b' & [<- | Hb'] & R); [lia | apply H; exists b'; split; assumption].
Qed.
Lemma in_fframe_dec : ltac2:(TCodec.tc2 tcn__JatWrapRng ">'4&Q;%211'?'>&Q?r2r1%3221&=%112%7231pU@91pQ2;1").
Proof.
induction FF as [|f FF IH]; intros x; [right; intros (f & [] & _)|].
destruct (IH x) as [H | H]; [left; destruct H as (f' & Hf' & R); exists f'; split; [right; exact Hf' | exact R]|].
assert (D : (ff_addr f <= x < ff_addr f + ff_bytes (ff_class f) - 8 /\ ~ (ff_addr f + 24 <= x < ff_addr f + 32))
\/ ~ (ff_addr f <= x < ff_addr f + ff_bytes (ff_class f) - 8 /\ ~ (ff_addr f + 24 <= x < ff_addr f + 32))) by lia.
destruct D as [D | D].
- left. exists f. split; [left; reflexivity | exact D].
- right. intros (f' & [<- | Hf'] & R); [exact (D R) | apply H; exists f'; split; assumption].
Qed.
Section Rng.
Variable rn : art_run.
Variables (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (M : word -> option byte) (model : Model).
Hypothesis LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
0x691000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES).
Hypothesis CLI : art_client_ok rn LB FF LK A M.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x691000.
Variable g : art_fsg.
Hypothesis FS : art_fsinv rn g FF LK M.
Hypothesis SHDEF : forall a : word, in_shadow_rw (U a) -> M a <> None.
#[using="LB FF LK A M CLI"] Lemma art_cli_hi : ltac2:(TCodec.tc2 tcn__JatWrapRng "B':&QM+SoomohPPP0&QEvR?%211%5241&QK+XPPP0%2241+@%4221&R1+2+Q?%3221%?251%A2;1").
Proof. pose proof CLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C10 & _ & C12 & _). unfold rn_HI. lia. Qed.
#[local] Ltac hi_facts := pose proof art_cli_hi as (HI1 & HI2).
#[local] Abbreviation Mr0 := (mrestrict (bhid A model) M).
#[local] Abbreviation cls := (fun sp scr a => hl_img_lo L <= a < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp scr a).
Section SE.
Local Abbreviation SEC_T_art_cls_off_scratch := (ltac2:(TCodec.tc2 tcn__JatWrapRng "Q>'?&QM&QEvR?%211&R2r3r2%3221%8251'>':&Q=vA%211r1%?221&QN&Q<%116%3251%:251&Q5&QF%11EvBv@%57>321ED<%B271qT8M1qU2N1qU4O1r4%231KJ&=r5%O214%Q421O%E2Q03%L221%611p081p0Q11pT8Q;1pU2Q<1pU4Q=1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_cls_off_scratch) 0%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SEC_T_art_cls_off_scratch) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_cls_off_scratch) 2%nat 0%nat).
Lemma art_cls_off_scratch : ltac:(sec_stmt2 constr:(SEC_T_art_cls_off_scratch) 3%nat 0%nat).
Proof using LK A M CLI HLlo HLhi g FS sp scr a.
intros SHI Ha X.
pose proof CLI as (C1 & _). hi_facts.
pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & _ & G3 & _).
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
destruct Ha as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; rewrite ?HLlo, ?HLhi in H.
- lia.
- destruct H as (b' & Hb' & Rb). destruct (C1 b' Hb') as (_ & _ & _ & _ & K5 & _). rewrite HIeq in K5. lia.
- lia.
- lia.
- destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). unfold FS_BYTES in *. lia.
- destruct H as (_ & X2). pose proof (art_S_hi (ahl_ceil (rn_ar rn) + (2 ^ 47 - ahl_ceil (rn_ar rn)) - 1) ltac:(lia)). lia.
- destruct H as (f & Hf & (_ & X2)). pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
unfold FS_BYTES in *. pose proof (art_S_hi (ff_addr f + ff_bytes (ff_class f) - 1) ltac:(lia)). lia.
- destruct H as (b' & Hb' & (_ & X2)). destruct (C1 b' Hb') as (_ & _ & _ & _ & K5 & _). rewrite HIeq in K5.
pose proof (art_S_hi (fst b' + snd b' - 1) ltac:(lia)). lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rng_shadow_allowed := (ltac2:(TCodec.tc2 tcn__JatWrapRng "RB'?&QMzr3%3221':r1%6251&QNr4%2241%6241'>&Q=vA%211%?21:&Q<%114%;2=1%?241&Q5&QFvR?%211vBv@r2%77>432I1F%A291qT8N1qU2O1qU4Q01r8r7&QKr6%221:%63541p0L1pTBQ81r5%721Q1&Q1%Q;221&Q0%Q=215%Q3231%=2<7&R1+2+Q?%3221%QD251%QE2D=%D2EC%Q@2?1%QD231';'2&Mv0&F&RByR0&Q3%11N%4231%611%9281(9%=3<21p0?1p0D1p0K1p0Q31p0R81pT8R=1pTLR>1pT:R?1pU2R@1pU4RA1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rng_shadow_allowed) 0%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SEC_T_art_rng_shadow_allowed) 1%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_rng_shadow_allowed) 2%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_rng_shadow_allowed) 3%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_rng_shadow_allowed) 4%nat 0%nat).
Lemma art_rng_shadow_allowed : ltac:(sec_stmt2 constr:(SEC_T_art_rng_shadow_allowed) 5%nat 0%nat).
Proof using LK M CLI HLlo HLhi g FS sp scr b n a.
intros Hb CLS APP TOP Ha.
hi_facts. specialize (CLS (a - b) ltac:(lia)). replace (b + (a - b)) with a in CLS by ring. cbn beta in CLS. rewrite HLlo, HLhi in CLS.
pose proof CLI as (C1 & _). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (SAst & SAfs & IMGSH & _).
unfold BIGSHADOW_LO, BIGSHADOW_HI in APP.
assert (NOSH : forall x y, 0 <= x -> x + y <= 2 ^ 47 -> 0 < y -> in_shadow_of x y a -> False).
{ intros x y Hx Hxy Hy (X1 & X2). pose proof (art_S_lo x Hx). pose proof (art_S_hi (x + y - 1) ltac:(lia)). lia. }
destruct CLS as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
- apply IMGSH. apply art_in_shadow_of_S. lia.
- destruct H as (b' & Hb' & R). destruct (C1 b' Hb') as (_ & _ & _ & _ & _ & _ & _ & _ & SAb & _). apply SAb. apply art_in_shadow_of_S. exact R.
- apply SAst. apply art_in_shadow_of_S. lia.
- apply IMGSH. apply art_in_shadow_of_S. lia.
- destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
apply SAfs. apply art_in_shadow_of_S. unfold FS_BYTES in *. lia.
- exfalso. pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & G3 & _). apply (NOSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [unfold rn_HI in *; lia | lia | unfold rn_HI in *; lia | exact H].
- exfalso. destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & G3 & _). unfold FS_BYTES in *. apply (NOSH (ff_addr f) (ff_bytes (ff_class f))); [lia | unfold rn_HI in *; lia | exact I3 | exact H].
- exfalso. destruct H as (b' & Hb' & H). destruct (C1 b' Hb') as (K1 & _ & _ & K4 & K5 & _). apply (NOSH (fst b') (snd b')); [lia | unfold rn_HI in *; lia | exact K4 | exact H].
Qed.
End SE.
#[using="LB FF LK A M CLI"] Lemma art_rng_app8 : ltac2:(TCodec.tc2 tcn__JatWrapRng "D'?&QMzr2%3221&Q7&QFvR?%211r4r3%63321&QAr5%2215p041p0<1p0=1pTLB1pTNC1").
Proof.
intros p n Hp Hn (_ & APP & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16).
unfold in_app8, LOWEND, HIGHBEG, HIGHEND. unfold BIGSHADOW_LO, BIGSHADOW_HI in APP. destruct APP as [X | X]; [left | right]; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_rng_facts := (ltac2:(TCodec.tc2 tcn__JatWrapRng "U2'?&QMzr2%3221&QN%1243r3&R1+2+Q8%3221%;251':r1%>2=1r5%<231%5231'>&Q=vA%211%F219&Q<%114%E2<1%>241&Q5&QFvR?%211vBv@%67=321KOD%@281qT8Q41qU2Q51qU4Q61r9r8&QKr7%221Q8%63541p0K1pTBQ>1&Q4vHr6%3321Q2&Q7%13E:3&QB&QL+8%22@1%@241&R2%B2DC+1%3221%8217%F2:1&QG&Kv0vR<%3221r:%6321O%R62BR4%R72R5QJ%QL221%Q12QLC&QE%11Q>%R<231%R1251'RCyR0%211&RD%123R5%RC2R=1%R@22RB%R9221';'7y8%;11%311&L%13IQ=RJ(1&RB%127RN%3271%;3751p0=1pU@C1'<%72FS3%;3Q3QG1%92?RJ%;2?1%C3?31%D3S;RMS9&QOr;%R521Q9%QE21QC%421QI%S<21S3+7%SB2S51%S7231%S22:1%S92<1qTDSG1%C2SH1'4%11Q0%Q311&QH&QJ%Q22QJR>r4%D21R9%R7221%Q32QB1u8%847621%Q72;T2%Q?3;21%K2T0R@%R>2T11%Q:2QI1%>4=<17%Q=2ASM%QE3A21%T0271qU>D1%Q:2E1qU<F1%Q<2G1%T52J1%T62Q?1%T72R61%T82R?1tTFTFRG1tT>TGRN1p0S41p0S71p0S<1p0T?1p0TF1p0TI1pTLTN1pTNTO1pU2U01pU4U11")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rng_facts) 0%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SEC_T_art_rng_facts) 1%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_rng_facts) 2%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_rng_facts) 3%nat 0%nat).
Lemma art_rng_facts : ltac:(sec_stmt2 constr:(SEC_T_art_rng_facts) 4%nat 0%nat).
Proof using LK LAZY CLI HLlo HLhi g FS SHDEF sp scr p n.
intros Hp Hn Hn40 CLS AACC APPR fS lS.
pose proof APPR as (_ & APP & TOP). hi_facts.
destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16).
assert (P47 : p + n + 16 <= 2 ^ 47) by (clear - TOP T16; lia).
assert (VSH : forall a, p <= a < p + n -> page_allowedb A (page_base (Z_to_bv 64 (HeapIfaceA.S a))) = true).
{ intros a Ha. apply (art_rng_shadow_allowed sp scr p n a Hp CLS APP ltac:(lia) Ha). }
assert (FL : Ja0RegionPoisoned.SB <= fS <= lS /\ lS < 0x10007fff8000).
{ unfold fS, lS, Ja0RegionPoisoned.SB. pose proof (art_S_lo p Hp). pose proof (art_S_hi (p + n - 1) ltac:(lia)). pose proof (art_S_mono p (p + n - 1) ltac:(lia)).
unfold HeapIfaceA.S, HeapIfaceA.SB in *. lia. }
assert (SfS : HeapIfaceA.S p = fS) by (unfold HeapIfaceA.S, HeapIfaceA.SB, fS, Ja0RegionPoisoned.SB; lia).
assert (SlS : HeapIfaceA.S (p + n - 1) = lS) by (unfold HeapIfaceA.S, HeapIfaceA.SB, lS, Ja0RegionPoisoned.SB; lia).
assert (VSHx : forall x, fS <= x <= lS -> page_allowedb A (page_base (Z_to_bv 64 x)) = true).
{ intros x Hx. destruct (art_shadow_preimage p n x Hp Hn ltac:(rewrite SfS, SlS; exact Hx)) as (a & Ha & Sa). rewrite <- Sa. apply VSH. exact Ha. }
unfold Ja0RegionPoisoned.SB in FL.
assert (RfS : 0 <= fS /\ lS < 2 ^ 64) by lia.
split.
{ intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
apply (art_aclient_vis rn LB FF LK A M model LAZY CLI L HLlo HLhi g FS sp scr (U x)); [pose proof (u64_range x); lia|].
replace (U x) with (p + (U x - p)) by ring. apply CLS. lia. }
split. { unfold Ja0RegionPoisoned.SB. lia. }
split.
{ intros x Hx. unfold mrestrict. rewrite (art_vis_allowed A model x ltac:(rewrite <- (Z_to_bv_bv_unsigned 64 x); apply VSHx; lia)).
pose proof (art_aacc_zero M p n Hp Hn AACC (U x) ltac:(unfold fS, lS, Ja0RegionPoisoned.SB in Hx; lia)) as Bz.
unfold byte_at in Bz. rewrite Z_to_bv_bv_unsigned in Bz. exact Bz. }
split.
{ destruct (art_aacc_last M p n Hn AACC) as (kS & BkS & HkS). exists kS. split; [|exact HkS].
unfold mrestrict. rewrite (art_vis_allowed A model (Z_to_bv 64 lS) ltac:(apply VSHx; lia)). exact BkS. }
assert (SHRW : forall y q, fS <= q <= lS -> q - q mod 8 <= y < q - q mod 8 + 8 -> in_shadow_rw y /\ page_allowedb A (page_base (Z_to_bv 64 y)) = true).
{ intros y q Hq Hy. pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Rq.
assert (E8 : y / 8 = q / 8). { symmetry. apply (Z.div_unique y 8 (q / 8) (y - 8 * (q / 8))); clear - Hy Dq Rq; lia. }
assert (Ry : 0 <= y < 2 ^ 64 /\ 0 <= q < 2 ^ 64) by (clear - Hy Hq RfS Rq FL; lia).
split.
- unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI. unfold BIGSHADOW_LO, BIGSHADOW_HI in APP.
pose proof (Z.div_mod p 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Rs.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Re.
assert (EfS : fS = 0x7fff8000 + p / 8) by reflexivity. assert (ElS : lS = 0x7fff8000 + (p + n - 1) / 8) by reflexivity.
clear - APP Hy Hq Dq Rq Ds Rs De Re EfS ElS Hn Hn40 Hp P47. destruct APP as [X | X]; [left | right]; lia.
- rewrite (art_page_base_word y q (proj1 Ry) (proj2 Ry) E8). apply VSHx. exact Hq. }
assert (DEF8 : forall q, fS <= q <= lS -> exists w, rdn ASEGS Mr0 (Z_to_bv 64 (q - q mod 8)) 8 = Some w).
{ intros q Hq. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Rq.
destruct (art_rdn_defined 8 Mr0 (q - q mod 8) ltac:(lia) ltac:(cbn; lia)) as (w & Hw & _); [|exists w; exact Hw].
intros x Hx. cbn in Hx. destruct (SHRW (U x) q Hq ltac:(lia)) as (RW & AL).
unfold mrestrict. rewrite (art_vis_allowed A model x ltac:(rewrite <- (Z_to_bv_bv_unsigned 64 x); exact AL)).
exact (SHDEF x RW). }
destruct (DEF8 fS ltac:(lia)) as (w0 & H0). destruct (DEF8 lS ltac:(lia)) as (w1 & H1). exists w0, w1. split; assumption.
Qed.
End SE.
#[using="Type"] Lemma art_rng_rdn : ltac2:(TCodec.tc2 tcn__JatWrapRng "QJ'?'5'4'RCy8%211%411&QMzr3%3221&QN&QKr4&R0%116%4231&R1+2+R0%3221%:251&QG&Kv0vR<%3221r5%>1?%73321';'7%11J&QH&QJvH&RByR0r6%3221%74651=(1%12Q4M%=3;31&L%12C:r7%;2:1%?4>31:%82Q;F%D3B21p081p0G1p0Q01p0Q<1pT<QA1pTLQG1pTNQI1").
Proof.
intros p n bs Hp Hn V RD. rewrite (rdn_mrestrict_eq ASEGS (bhid A model) n M (Z_to_bv 64 p)); [exact RD|].
apply (art_vis_avoids (bhid A model) p n Hp Hn V).
Qed.
#[using="Type"] Lemma art_rng_store_ok : ltac2:(TCodec.tc2 tcn__JatWrapRng "QA'?'5&QMzr2%3221&QN&QKr3&R0%116%4231&R1+2+R0%3221%:251&QG&Kv0vR<%3221r4%>1?%73321';'2&D&QJvH&RByR0r5%3221%74651<(9%;3:21&L%12A9r6%:291%>4=319%A3@17p071p0D1p0M1p0Q91pTLQ>1pTNQ@1").
Proof.
intros p n Hp Hn V OK. rewrite (art_store_ok_ext ASEGS n Mr0 M (Z_to_bv 64 p)); [exact OK | rewrite art_u_lit by lia; lia |].
intros x Hx. rewrite art_u_lit in Hx by lia. unfold mrestrict. rewrite (V x Hx). reflexivity.
Qed.
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x691000.
Section SE.
Local Abbreviation SEC_T_art_clientw_not_private := (ltac2:(TCodec.tc2 tcn__JatWrapRng "M'?&Q6vA&QFvR?%211vBv@r3r2r1%:79654321'>&QN&Q1%2261&QM&Q0%2219%7241&=&Q:%15DA@?>%311p051p0>1pU@J1pU2K1pU4L1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_clientw_not_private) 0%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SEC_T_art_clientw_not_private) 1%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_clientw_not_private) 2%nat 0%nat).
Lemma art_clientw_not_private : ltac:(sec_stmt2 constr:(SEC_T_art_clientw_not_private) 3%nat 0%nat).
Proof using LK A M CLI g FS HLroimg sp scr x.
intros CW APP PRIV.
hi_facts. pose proof CLI as (C1 & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in APP.
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & G3 & G4 & _).
assert (NOSH : forall a y, 0 <= a -> a + y <= 2 ^ 47 -> 0 < y -> in_shadow_of a y x -> False).
{ intros a y Ha Hay Hy (X1 & X2). pose proof (art_S_lo a Ha). pose proof (art_S_hi (a + y - 1) ltac:(lia)). lia. }
unfold aclientw, aclient_g in CW.
destruct PRIV as [NC | [RO | (b & Hb & BS)]].
- apply NC. unfold aclient, aclient_g.
destruct CW as [H|[H|[H|[H|[H|[H|H]]]]]].
+ left; exact H.
+ right; left. split; [exact (proj1 H) | lia].
+ right; right; left. split; [exact (proj1 H) | intros X; apply (proj2 H); left; exact X].
+ do 3 right; left; exact H.
+ do 4 right; left; exact H.
+ do 5 right; left; exact H.
+ destruct H as (b & _ & []).
- pose proof (HLroimg x RO) as IM.
destruct CW as [H|[H|[H|[H|[H|[H|H]]]]]].
+ destruct H as (b & Hb & Rb). destruct (C1 b Hb) as (_ & K2 & _). lia.
+ lia.
+ apply (proj2 H). right; exact RO.
+ destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). unfold FS_BYTES in *. lia.
+ apply (NOSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [lia | lia | lia | exact H].
+ destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
unfold FS_BYTES in *. apply (NOSH (ff_addr f) (ff_bytes (ff_class f))); [lia | lia | exact I3 | exact H].
+ destruct H as (b & _ & []).
- destruct (C1 b Hb) as (K1 & _ & _ & K4 & K5 & _). apply (NOSH (fst b) (snd b)); [lia | lia | exact K4 | exact BS].
Qed.
End SE.
#[using="Type"] Lemma art_clientw_cls : ltac2:(TCodec.tc2 tcn__JatWrapRng "Q3'?&Q6vA&QFvR?%211vBv@r3r2r1%:79654321'>':&QM&Q=%11>%3217&QN&Q<%11B%32;1%9251&Q5%17FCBA@?>%=231qT8J1qU2K1qU4L1r4%231FEp0D1pU@Q01pU2Q11pU4Q21").
Proof. intros sp scr x H. right. apply aclientw_client. exact H. Qed.
Hypothesis HLstimg : forall a, hl_rt_static L a -> 0x10000 <= a < 0x691000.
#[using="LK A M CLI g FS HLstimg"] Lemma art_clientw_not_static : ltac2:(TCodec.tc2 tcn__JatWrapRng "M'?&Q6vA&QFvR?%211vBv@r3r2r1%:79654321'>&QN&Q1%2261&QM&Q0%2219%7241&=&Q>%12D>%311p051p0>1pU@J1pU2K1pU4L1").
Proof.
intros sp scr x CW APP ST. hi_facts. pose proof CLI as (C1 & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in APP. pose proof (HLstimg x ST) as IM.
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & G3 & G4 & _).
assert (NOSH : forall a y, 0 <= a -> a + y <= 2 ^ 47 -> 0 < y -> in_shadow_of a y x -> False).
{ intros a y Ha Hay Hy (X1 & X2). pose proof (art_S_lo a Ha). pose proof (art_S_hi (a + y - 1) ltac:(lia)). lia. }
unfold aclientw, aclient_g in CW.
destruct CW as [H|[H|[H|[H|[H|[H|H]]]]]].
+ destruct H as (b & Hb & Rb). destruct (C1 b Hb) as (_ & K2 & _). lia.
+ lia.
+ apply (proj2 H). left; exact ST.
+ destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). unfold FS_BYTES in *. lia.
+ apply (NOSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [lia | lia | lia | exact H].
+ destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
unfold FS_BYTES in *. apply (NOSH (ff_addr f) (ff_bytes (ff_class f))); [lia | lia | exact I3 | exact H].
+ destruct H as (b & _ & []).
Qed.
End Rng.

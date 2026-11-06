(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtBridge JatInv JatLift JatFsInv JatFsInvLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapVis () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1bool"; "1false"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0FF"; "0L"; "0LB"; "4m_vm_lazy"; "4page_base"; "4page_in_ranges"]; ["0M"; "5bhid"; "6page_allowedb"; "7in_block"; "8BIGSHADOW_HI"; "8BIGSHADOW_LO"; "8FS_BYTES"; "8S"; "8aacc"; "8aclient"; "8ar_fs"; "8ar_sptop"; "8byte_at"; "8hl_img_hi"; "8hl_img_lo"; "8in_shadow_of"]; ["8shadow_allowed"; "9rn_HI"; "9rn_ar"; ":add"; ":div"; ":le"; ":lt"; ":modulo"; ":pow"; ":sub"; "0a"; "0a'"; "0b"; "0i"; "0k"; "0lo"]; ["0model"; "0n"; "0n'"; "0p"; "0rn"; "0scr"; "0sp"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "0x"; "0y"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section Vis.
Variable rn : art_run.
Variables (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (M : word -> option byte) (model : Model).
Hypothesis LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
0x691000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES).
Hypothesis CLI : art_client_ok rn LB FF LK A M.
#[using="Type"] Lemma art_vis_notlazy : ltac2:(TCodec.tc2 tcn__JatWrapVis "F'QHyR0%211'6'1&?&>r1%211&=vQ@%211%7241(2%;3:21&Av0r2%33281%@3?16p061pSFC1").
Proof. intros x H. unfold bhid, mkH. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma art_vis_allowed : ltac2:(TCodec.tc2 tcn__JatWrapVis "E'QHyR0%211'6'1&Bv0&>r1%211%5241(4%93821&AvQ@r2%33:21(2%?3>21p071pSFB1").
Proof. intros x H. unfold bhid, mkH. rewrite H. apply andb_false_r. Qed.
#[using="LAZY"] Lemma art_vis_byte : ltac2:(TCodec.tc2 tcn__JatWrapVis "Q;'QHyR0%211'8&Q6&QIr1%2261+VbTP0%5221&Q5&Q1vQD%211%4217&Cv<%221:'5&J&Q2%119%311%=21@&Q3&F%2241%G2D1%:251%J2<1%K2@1%L2F1'6'1&Av0vQ@r2%43321(2%83721p0:1pSFQ81").
Proof.
intros x H. apply art_vis_notlazy. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:E; [|reflexivity]. exfalso.
destruct (LAZY x E) as (L1 & L2 & L3 & L4). destruct H as [H | [H | [H | H]]]; [lia | lia | exact (L3 H) | exact (L4 H)].
Qed.
#[using="Type"] Lemma art_vis_shadow : ltac2:(TCodec.tc2 tcn__JatWrapVis "H'9&Q0v0r3r2%43321&Or4%23154'6'1&AvQ@&QGyR0%221<%53>41(2%93821p0;1p0?1pSFE1pS4F1pRFG1").
Proof. intros a n x SA Hx. apply art_vis_allowed. exact (SA x Hx). Qed.
#[using="Type"] Lemma in_shadow_of_sub : ltac2:(TCodec.tc2 tcn__JatWrapVis "L'9&Q5r5r3%3221&Q3r4%2214r6%4217%9231&Q6z%2217&O%137=9r9r8%4321@p041p071p0;1p0B1pSFG1pS6H1pRHI1pS4J1pRFK1").
Proof.
intros a n a' n' x H1 H2 Hn (X1 & X2). unfold in_shadow_of, HeapIfaceA.S in *.
assert (a / 8 <= a' / 8) by (apply Z.div_le_mono; lia). assert ((a' + n' - 1) / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x691000.
Variable g : art_fsg.
Hypothesis FS : art_fsinv rn g FF LK M.
Section SE.
Local Abbreviation SEC_T_art_aclient_vis := (ltac2:(TCodec.tc2 tcn__JatWrapVis "QA'9'5&Q5zr1%3221&Q6&Q8+2+R0%3221%5271%;271'8&Nv;%211r2%@221&M%115%?241%E241&I&Q2vQD%211v<v:r4r3%87@54321>%C2:1'6'1&Av0vQ@&QGyR0%221:%63541(2%:3921p0<1p0Q11pRFQ>1pS<Q?1pS>Q@1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_aclient_vis) 0%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SEC_T_art_aclient_vis) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_aclient_vis) 2%nat 0%nat).
Lemma art_aclient_vis : ltac:(sec_stmt2 constr:(SEC_T_art_aclient_vis) 3%nat 0%nat).
Proof using LK M LAZY CLI HLlo HLhi g FS sp scr a.
intros Ra H.
rewrite HLlo, HLhi in H.
pose proof CLI as (C1 & _ & SAst & SAfs & _).
assert (UA : U (Z_to_bv 64 a) = a) by (apply art_u_lit; exact Ra).
destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
- apply art_vis_byte. rewrite UA. lia.
- apply art_vis_byte. rewrite UA. right; right; left. exact H.
- apply art_vis_byte. rewrite UA. right; left. unfold rn_HI. lia.
- apply art_vis_byte. rewrite UA. rewrite HLlo, HLhi in H. lia.
- apply art_vis_byte. rewrite UA. right; right; right. destruct H as (f & Hf & R1 & _).
pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). unfold FS_BYTES in *. lia.
- exact (art_vis_shadow _ _ _ SAst H).
- destruct H as (f & Hf & H). apply (art_vis_shadow (ar_fs (rn_ar rn)) FS_BYTES a SAfs).
pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
apply (in_shadow_of_sub _ _ (ff_addr f) (ff_bytes (ff_class f))); [lia | lia | lia | exact H].
- destruct H as (b & Hb & H). destruct (C1 b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & SAb & _). exact (art_vis_shadow _ _ _ SAb H).
Qed.
End SE.
#[using="Type"] Lemma art_S_mono : ltac2:(TCodec.tc2 tcn__JatWrapVis "='9&Q5r2r1%3221&Gr3%211%316%8221p061pRJ;1pRF<1").
Proof. intros a b H. unfold HeapIfaceA.S. assert (a / 8 <= b / 8) by (apply Z.div_le_mono; lia). lia. Qed.
#[using="Type"] Lemma art_S_lo : ltac2:(TCodec.tc2 tcn__JatWrapVis "<'9&Q5zr1%3221+QoooPP0&Gr2%211%8241p061pRF;1").
Proof. intros a H. unfold HeapIfaceA.S, HeapIfaceA.SB. assert (0 <= a / 8) by (apply Z.div_pos; lia). lia. Qed.
#[using="Type"] Lemma art_S_hi : ltac2:(TCodec.tc2 tcn__JatWrapVis "?'9&Q6r1&Q8+2+Q?%3221%6251&Gr2%211+`PQoooPP0%;221p061pRF>1").
Proof. intros a H. unfold HeapIfaceA.S, HeapIfaceA.SB. assert (a / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415 in *. lia. Qed.
#[using="Type"] Lemma art_in_shadow_of_S : ltac2:(TCodec.tc2 tcn__JatWrapVis "E'9'5&Q5r3r1%3221&Q6&Q3r2%2261%4261%:261&Or4&G%117%433=1p061pRFB1pS4C1pS0D1").
Proof. intros lo n a H. split; apply art_S_mono; lia. Qed.
Hypothesis IMGSH : shadow_allowed A 0x10000 (0x691000 - 0x10000).
Section SE.
Local Abbreviation SEC_T_art_buf_shadow_allowed := (ltac2:(TCodec.tc2 tcn__JatWrapVis "R<'9&Q5zr3%3221'5r1%6251&Q6r4%2241%6241'8&Nv;%211&Q3r6r2%3221%C251&M%118%?241%C241&I&Q2vQD%211v<v:r8r7%87C54321>%F2:1p0H1pRLQ41r5%F21M&E%Q7221&D%Q9215%O231%L2K7&K%11B%Q>231%Q?2@;%Q12AQ0%Q:2=1%Q>231'6'1&Bv0&>&QGyR0&G%11Q;%4231%611%9281(4%=3<21p0?1p0D1p0I1p0Q11p0R21pRFR71pS4R81pRJR91pS<R:1pS>R;1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_buf_shadow_allowed) 0%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SEC_T_art_buf_shadow_allowed) 1%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_buf_shadow_allowed) 2%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_buf_shadow_allowed) 3%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_buf_shadow_allowed) 4%nat 0%nat).
Lemma art_buf_shadow_allowed : ltac:(sec_stmt2 constr:(SEC_T_art_buf_shadow_allowed) 5%nat 0%nat).
Proof using LK M CLI HLlo HLhi g FS IMGSH sp scr b n a.
intros Hb CLS APP TOP Ha.
specialize (CLS (a - b) ltac:(lia)). replace (b + (a - b)) with a in CLS by ring. rewrite HLlo, HLhi in CLS.
pose proof CLI as (C1 & _ & SAst & SAfs & _ & _ & _ & _ & _ & CT).
pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & _ & _ & (_ & _ & G7) & _).
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
- exfalso. apply (NOSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [lia | lia | lia | exact H].
- exfalso. destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
unfold FS_BYTES in *. apply (NOSH (ff_addr f) (ff_bytes (ff_class f))); [lia | lia | exact I3 | exact H].
- exfalso. destruct H as (b' & Hb' & H). destruct (C1 b' Hb') as (K1 & _ & _ & K4 & K5 & _). apply (NOSH (fst b') (snd b')); [lia | lia | exact K4 | exact H].
Qed.
End SE.
#[using="Type"] Lemma art_page_base_word : ltac2:(TCodec.tc2 tcn__JatWrapVis "Q5'9'5&Q5zr2%3221&Q6&Q8+2+R0%3221%5271%;271'6&Q4r4+8%3221r3%5213%73D31'QHyR0%211&>&QGr5%2251%411%427>%611%B3831p0<1p0E1p0F1pSHQ31pSFQ41").
Proof.
intros x y Hx Hy E. unfold page_base, page_base_of, page_size. rewrite !art_u_lit by lia.
replace (x / 4096) with (x / 8 / 512) by (rewrite Z.div_div by lia; reflexivity). replace (y / 4096) with (y / 8 / 512) by (rewrite Z.div_div by lia; reflexivity).
rewrite E. reflexivity.
Qed.
End Vis.
Lemma art_aacc_zero : ltac2:(TCodec.tc2 tcn__JatWrapVis "QA'QHyR0%211'3y8%511%311p051'9&Q5zr2%3221&Q6%1243&Hr5r4r3%43321'5&Q3+QoooPP0&Q4r6+8%3221%6251r1%D221&Q9%:27?+1%3221%;219%>2=1%G281%A281&Lr8%231MNp041pSFQ21p0H1p0N1p0Q11pS4Q61pS8Q71pQ2Q91").
Proof.
intros M p n Hp Hn AC x Hx. set (a := 8 * (x - 0x7fff8000) + 7).
pose proof (Z.div_mod p 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as R1.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as R2.
assert (Ha : p <= a < p + n) by (unfold a; lia).
assert (Sa : HeapIfaceA.S a = x).
{ unfold HeapIfaceA.S, HeapIfaceA.SB, a. replace (8 * (x - 2147450880) + 7) with (7 + (x - 2147450880) * 8) by ring. rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
assert (Ma : a mod 8 = 7).
{ unfold a. replace (8 * (x - 2147450880) + 7) with (7 + (x - 2147450880) * 8) by ring. rewrite Z.mod_add by lia. reflexivity. }
destruct (AC a Ha) as [Z0 | (v & Bv & Rv & Lv)]; [rewrite Sa in Z0; exact Z0 | lia].
Qed.
Lemma art_aacc_last : ltac2:(TCodec.tc2 tcn__JatWrapVis "QE'QHyR0%211'3y8%511%311p051'9&Q6zr1%3221&Hr4r3r2%43321'7'5&Lr6&Q3+QoooPP0&Q4&Q9r5%521=+1%4221+8%7221%:291%=3<1F'8'6%13LIJ&Q7%1298%N21L&Q5+7%22O1%H241%:281%J2<1qRNQ61%M2Q71p0O1p0Q51pS4Q:1pS8Q;1pQ2Q=1").
Proof.
intros M p n Hn AC. destruct (AC (p + n - 1) ltac:(lia)) as [Z0 | (v & Bv & Rv & Lv)]; unfold HeapIfaceA.S, HeapIfaceA.SB in *.
- exists 0. split; [rewrite Z.add_comm; exact Z0 | left; reflexivity].
- exists v. split; [rewrite Z.add_comm; exact Bv | right; lia].
Qed.
Lemma art_shadow_preimage : ltac2:(TCodec.tc2 tcn__JatWrapVis "Q9'9&Q5zr3%3221&Q6%1243'5&Gr5%211%:218&Q9&Q3r4%2261+1%5221%:11%B2@1%=291'7r7r1%G221r6%=241%F241%E241'6%F17%23O1F%I241qRFQ11%=2Q21p0?1p0N1p0Q11pSFQ61pS4Q71pRJQ81").
Proof.
intros b n x Hb Hn (X1 & X2). unfold HeapIfaceA.S, HeapIfaceA.SB in *.
pose proof (Z.div_mod b 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound b 8 ltac:(lia)) as R1.
pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)) as R2.
destruct (Z.eq_dec (x - 2147450880) (b / 8)) as [E | NE].
- exists b. split; [lia | lia].
- exists (8 * (x - 2147450880)). split; [lia|]. replace (8 * (x - 2147450880)) with (0 + (x - 2147450880) * 8) by ring. rewrite Z.div_add by lia. change (0 / 8) with 0. lia.
Qed.

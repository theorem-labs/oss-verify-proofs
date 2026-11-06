(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull HeapIfaceAJx ShadowRLaws.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__StrictOfJ () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceANull."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StrictOfJ.Strict."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0C"; "1bool"; "1cons"; "1fst"; "1list"; "1nil"; "1option"; "1prod"; "1snd"; "2I"; "2and"; "2eq"; "2not"; "3Forall"; "4Z"]; ["0F"; "0FF"; "0HIR"; "0K"; "0L"; "0LB"; "0LB'"; "0LK"; "5Model"; "6bvmap"; "0M"; "0M'"; "0R"; "7credit"; "7lb_remove"; "8BIGSHADOW_HI"]; ["8BIGSHADOW_LO"; "8S"; "8SB"; "8aaligned16_spec"; "8ablock_range"; "8aclient"; "8aclientw"; "8afree_spec"; "8ahandle_no_return_spec"; "8aheap_pres"; "8amalloc_spec"; "8amem_pre"; "8amemcpy_spec_at"; "8amemset_spec"; "8asan_iface"; "8asan_iface_ok"]; ["8astack_malloc_spec"; "8ff_bytes"; "8ff_remove"; "8fframe"; "8hl_scr_mem"; "8in_shadow_of"; "8ri_inv"; "8rt_flagptr"; "8rt_frame"; "8rt_lazy"; "8rt_leak_frames"; "8rt_perm"; "8rt_release_frame"; "8rt_small_high"; "8rt_statics"; "8rt_wf"]; ["8shadow_blk"; "8vml"; "9strict_of"; ":afree_null_spec"; ";FPState"; ";getr"; "<TSet"; "=sj_cls"; "=sj_wf"; ">In"; ">incl"; "?add"; "?div"; "?le"; "?lt"; "?modulo"]; ["?pow"; "0V"; "0a"; "0ar"; "0b"; "0cr"; "0dst"; "0f"; "0fx"; "0k"; "0mo"; "0model"; "0n"; "0pc"; "0scfg"; "0scr"]; ["0sp"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0u"; "0x"; "0y"]]).
Lemma sj_div8_lt : ltac2:(TCodec.tc2 tcn__StrictOfJ "E'?&R>r2r1%3221'<&R?+8%2261z%53:21&R<r4%2216r3%4218%?231p071p0>1pV@C1pV>D1").
Proof. intros x y.
intros Hxy Hy. pose proof (Z.div_mod y 8 ltac:(lia)) as D. rewrite Hy, Z.add_0_r in D.
apply Z.div_lt_upper_bound; lia.
Qed.
Lemma sj_S_mono : ltac2:(TCodec.tc2 tcn__StrictOfJ "='?&R=r2r1%3221&Q1r3%211%316%8221p061pV@;1pV><1").
Proof. intros x y. intros H. unfold HeapIfaceA.S. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.
Lemma sj_S_range : ltac2:(TCodec.tc2 tcn__StrictOfJ "G'?';&R=zr1%3221&R>&R@+2+Q?%3221%5271%;271&Q2&Q1r2%211%?241&O%=231%C231p091pV>F1").
Proof. intros x.
intros H. unfold HeapIfaceA.S, BIGSHADOW_HI, SB in *. split.
- pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
- assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma sj_mod8_of16 : ltac2:(TCodec.tc2 tcn__StrictOfJ ">'?'<&R?r1+@%3221z%63721r2+8%8221%:3;15p051pV<=1").
Proof. intros u.
intros H. pose proof (Z.div_mod u 16 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (16 * (u / 16)) with ((2 * (u / 16)) * 8) by ring. apply Z_mod_mult.
Qed.
Lemma sj_ffbytes_mod8 : ltac2:(TCodec.tc2 tcn__StrictOfJ "Q0'?&R9r1(3z+1+2+3+4(6%11:%83;31%93<51%:3=71%;3>91%<3?;1%?3@>1';'<&R?&QAr2%211+8%5221%73I1E&R=+R0%2216%<241p0>1pUDO1").
Proof. intros k. intros Hk. unfold ff_bytes. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; lia. Qed.
Lemma sj_frame_mod8 : ltac2:(TCodec.tc2 tcn__StrictOfJ "Q1'?&R9r1(3z+1+2+3+4(6%11:%83;31%93<51%:3=71%;3>91%<3?;1%?3@>1'<&R?r3&QAr2%211%5241%73H1Dr4+8%9221%;3L1Hp051p0>1pUDO1pQ2Q01").
Proof. intros F k.
intros Hk HF. pose proof (sj_ffbytes_mod8 k Hk) as (K8 & K64).
apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (ff_bytes k)); apply Z.mod_divide; lia.
Qed.
Lemma sj_sfilter_In : forall (A : Type) (P : A -> Prop) (D : forall x, Decision (P x)) (l : list A) x, In x (filter P l) <-> P x /\ In x l.
Proof.
induction l as [|a l IH]; intros x; [cbn; tauto|]. rewrite list_basics.list.filter_cons. destruct (decide (P a)) as [Y | N]; cbn [In]; rewrite IH.
- split; [intros [<- | H]; tauto | intros (Hp & [-> | H]); tauto].
- split; [tauto | intros (Hp & [-> | H]); tauto].
Qed.
Lemma sj_lb_remove_in : ltac2:(TCodec.tc2 tcn__StrictOfJ "A'?'5'8%1233%311&R9r1&Nr3r2%3221%63851%73934p021pU:;1pQ<;1pV<@1").
Proof. intros u LB b.
induction LB as [|b0 LB IH]; cbn [lb_remove]; [intros []|].
destruct (Z.eqb (fst b0) u); [intros H; right; exact H|]. intros [E|H]; [left; exact E|right; exact (IH H)].
Qed.
Lemma sj_ff_remove_in : ltac2:(TCodec.tc2 tcn__StrictOfJ "@'?'5&QC%211&R9r1&QBr3r2%3221%63851%73934p021pU@;1pQ4;1pQ2?1").
Proof. intros F FF f.
induction FF as [|f0 FF IH]; cbn [ff_remove]; [intros []|].
destruct (Z.eqb (ff_addr f0) F); [intros H; right; exact H|]. intros [E|H]; [left; exact E|right; exact (IH H)].
Qed.
Section Strict.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable HIR : asan_iface.
Definition rt_flag_in_fs : Prop :=
forall LB FF LK cr A M V F k rs fl,
ri_inv HIR LB FF LK cr A M V -> In (F, k, rs) FF -> cell_is (hl_segs L) M (F + ff_bytes k - 8) 8 fl -> 0 <= fl < 2 ^ 64 ->
ar_fs ar <= fl < ar_fs ar + FS_BYTES.
Hypothesis IMG : hl_img_hi L <= BIGSHADOW_LO.
Hypothesis FLAG : rt_flag_in_fs.
Hypothesis OK : HAJ.asan_iface_okR L ar C scfg HIR.
#[local] Abbreviation HIS := (HAJ.strict_of HIR).
Definition sj_cls (FF LK : list fframe) : Prop := Forall (fun f => In (ff_class f) [1; 2; 3]) (FF ++ LK).
Definition sj_wf (LB : list (Z * Z)) (FF LK : list fframe) : Prop :=
(forall b, In b LB -> ablock_range L ar (fst b) (snd b) /\ fframes_apart (fst b) (snd b) (FF ++ LK))
/\ (forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
/\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) [0; 1; 2; 3; 4])
/\ app_mem (ar_fs ar) FS_BYTES
/\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\ ar_sptop ar mod 16 = 0.
#[using="OK"] Lemma sj_wf_of : ltac2:(TCodec.tc2 tcn__StrictOfJ "Q6'5'8'?%2211%411&QC%611&M'S3yR0%211'7y8%511%311p051&R1&QFvBr7r6r5r4r3r2r1%9887654321&R8r8%231:9p041pU4?1pQFA1p2M1pU<K1pQ@M1pQ4N1pQ<Q11").
Proof.
intros LB FF LK cr A M V RI. destruct (HAJ.aior_wf _ _ _ _ _ OK LB FF LK cr A M V RI) as (WB & WF & W3 & _ & _ & _ & _ & _ & (_ & _ & W9 & W10) & _).
split; [|split; [|split; [exact W3|exact (conj W9 W10)]]].
- intros b Hb. destruct (WB b Hb) as (B1 & _ & _ & _ & _ & B6 & _). exact (conj B1 B6).
- intros f Hf. destruct (WF f Hf) as (F1 & F2 & F3 & F4 & _). exact (conj F1 (conj F2 (conj F3 F4))).
Qed.
Lemma sj_bsh_range : ltac2:(TCodec.tc2 tcn__StrictOfJ "Q0'?&Q4vDvRCr3r2%544321&QEr4%23154';&R>&Q0%2219&O%42;1%6231&R=z%221?&R@+2+R0%3221%=2D1%?261%@2:1p0B1p0F1pU6M1pUJN1pV<O1").
Proof. intros u n a.
intros (B1 & _ & _ & B4 & _ & (A0 & _ & A2)) (X1 & X2).
pose proof (sj_S_range u ltac:(lia)) as R1. pose proof (sj_S_range (u + n - 1) ltac:(lia)) as R2.
unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *. lia.
Qed.
Lemma sj_bsh_not_w : ltac2:(TCodec.tc2 tcn__StrictOfJ "Q9'5'8'?%2211%411&QC%611&R8r7r6r5%43321&R9r3r8%33<21&QE&4r4%23AA1&9%13CC3%63319&=&Q6vDvRCr:r9%574321ED;%711p091p0A1p0F1pU6Q01pU:Q01pV0Q21pV2Q31pQ@Q01pQ4Q11pQ<Q41").
Proof. intros LB FF LK sp scr b a.
intros (WB & WF & FSA & SP1 & SP2) Hb Hsh W. destruct (WB b Hb) as (BR & BA). pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (sj_bsh_range (fst b) (snd b) a BR Hsh) as (RA & _). pose proof Hsh as (X1 & X2).
unfold aclientw, aclient_g in W. destruct W as [W|[W|[W|[W|[W|[W|W]]]]]].
-
destruct W as (b' & Hb' & Y). destruct (WB b' Hb') as ((_ & _ & _ & _ & _ & (_ & AM & _)) & _).
unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
-
destruct W as (W & _). unfold BIGSHADOW_HI in *. lia.
-
destruct W as (W & _). lia.
-
destruct W as (f & Hf & Y & _). destruct (WF f Hf) as (F1 & F2 & _). destruct FSA as (_ & AM & _).
unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *. pose proof (sj_ffbytes_mod8 (ff_class f)) as _. lia.
-
destruct W as (W & _). assert (E8 : ahl_ceil ar mod 8 = 0).
{ pose proof (Z.div_mod (ar_sptop ar) 16 ltac:(lia)) as D. rewrite SP2, Z.add_0_r in D.
replace (ar_sptop ar - 8388608) with ((2 * (ar_sptop ar / 16) - 1048576) * 8) by lia. apply Z_mod_mult. }
pose proof (sj_div8_lt (fst b + snd b - 1) (ahl_ceil ar) ltac:(lia) E8) as LT. unfold HeapIfaceA.S in *. lia.
-
destruct W as (f & Hf & (Y1 & Y2)). destruct (WF f Hf) as (F1 & F2 & F3 & F4).
pose proof (sj_ffbytes_mod8 _ F4) as (K8 & K64). pose proof (sj_frame_mod8 _ _ F4 F3) as F8.
pose proof (sj_mod8_of16 _ B3) as U8.
destruct (BA f (in_or_app _ _ _ (or_introl Hf))) as [Ap|Ap].
+ pose proof (sj_div8_lt (fst b + snd b - 1) (ff_addr f) ltac:(lia) F8) as LT. unfold HeapIfaceA.S in *. lia.
+ pose proof (sj_div8_lt (ff_addr f + ff_bytes (ff_class f) - 1) (fst b) ltac:(lia) U8) as LT. unfold HeapIfaceA.S in *. lia.
- destruct W as (_ & _ & []).
Qed.
Lemma sj_keep : ltac2:(TCodec.tc2 tcn__StrictOfJ "QK'5'8'?%2211%411&QC%611'S3yR0%211'7y8%511%311p051&R8r5r4r3%43321&R9r2r8%33D21&QE&4%13HH8&9%13JJ:%53318'<r6&S2%12I?%311r7%113%73H31p091p0@1pU6Q61pU:Q61'>&R0r1%D3Q;Q;1%C3Q<Q<2%43O21qU:Q=1%73Q>1>%83Q?2Lp021p0;1p0Q21pQHQ81pQFQ91pQ@QB1pQ4QC1pQ<QF1").
Proof. intros LB FF LK M M'.
intros (WB & _) KEEP SB. rewrite Forall_forall in *. intros b Hb. destruct (WB b Hb) as ((B1 & _ & B3 & B4 & _) & _).
apply (shadow_blk_frame M M' (fst b) (snd b)); [lia|exact (sj_mod8_of16 _ B3)|exact B4| |exact (SB b Hb)].
intros a Ha. exact (KEEP b a Hb Ha).
Qed.
Lemma sj_keep_pres : ltac2:(TCodec.tc2 tcn__StrictOfJ "QD'5'8'?%2211%411&QC%611'S3yR0%211'7y8%511%311p051&R8r8r6r5%43321&R:r9%23C61&Q9vDvRCr4r3%58437<;:21'>&R0&4r1%23OO1&9%13Q1Q13%63C31qU:Q21r;%:3Q421p011p0=1p0D1p0H1pQHN1pQFO1pV0Q<1pV2Q=1pQ@Q:1pQ4Q;1pQ>Q>1pQ<Q?1").
Proof. intros LB LB' FF LK sp scr M M'.
intros WF INC (HP & _) SB. pose proof WF as (WB & _).
assert (WF' : sj_wf LB' FF LK).
{ destruct WF as (W1 & W2 & W3). split; [|split; [exact W2|exact W3]]. intros b Hb. exact (W1 b (INC b Hb)). }
apply (sj_keep LB' FF LK M M' WF').
- intros b a Hb Ha. destruct (WB b (INC b Hb)) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (_ & Ra).
apply HP; [exact Ra|]. do 6 right. exists b. split; [exact Hb|exact Ha].
- rewrite Forall_forall in *. intros b Hb. exact (SB b (INC b Hb)).
Qed.
#[using="OK"] Theorem strict_malloc : ltac2:(TCodec.tc2 tcn__StrictOfJ "8&Q:vDvRCvRN&R2vB%211%746541").
Proof.
intros fx R M model LB FF LK cr A n K (RI & SB & FC) HALT MI H10 Hn CR Htp Hra STK K0 POST.
pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
apply (HAJ.aior_malloc _ _ _ _ _ OK fx R M model LB FF LK cr A n K RI HALT MI H10 Hn CR Htp Hra STK K0).
intros R' M' model' A' u Hu RP BR BA FA DEF SHu HP MRT INC MI' RI'.
apply (POST R' M' model' A' u Hu RP BR BA FA DEF SHu HP MRT INC MI'). split; [exact RI'|]. split; [|exact FC].
constructor; [exact SHu|]. exact (sj_keep_pres LB LB FF LK _ _ M M' WF (incl_refl _) HP SB).
Qed.
#[using="OK"] Theorem strict_aligned : ltac2:(TCodec.tc2 tcn__StrictOfJ "8&Q3vDvRCvRN&R2vB%211%746541").
Proof.
intros fx R M model LB FF LK cr A n K (RI & SB & FC) HALT MI H10 H11 Hn Hn16 CR Htp Hra STK K0 POST.
pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
apply (HAJ.aior_aligned _ _ _ _ _ OK fx R M model LB FF LK cr A n K RI HALT MI H10 H11 Hn Hn16 CR Htp Hra STK K0).
intros R' M' model' A' u Hu RP BR BA FA DEF SHu HP MRT INC MI' RI'.
apply (POST R' M' model' A' u Hu RP BR BA FA DEF SHu HP MRT INC MI'). split; [exact RI'|]. split; [|exact FC].
constructor; [exact SHu|]. exact (sj_keep_pres LB LB FF LK _ _ M M' WF (incl_refl _) HP SB).
Qed.
#[using="OK"] Theorem strict_free : ltac2:(TCodec.tc2 tcn__StrictOfJ "8&Q7vDvRCvRN&R2vB%211%746541").
Proof.
intros fx R M model LB FF LK cr A u n K (RI & SB & FC) HALT MI Hin H10 Htp Hra STK K0 POST.
pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
apply (HAJ.aior_free _ _ _ _ _ OK fx R M model LB FF LK cr A u n K RI HALT MI Hin H10 Htp Hra STK K0).
intros R' M' model' A' RP HP MRT INC MI' RI'.
apply (POST R' M' model' A' RP HP MRT INC MI'). split; [exact RI'|]. split; [|exact FC].
exact (sj_keep_pres LB (lb_remove u LB) FF LK _ _ M M' WF (fun b Hb => sj_lb_remove_in u LB b Hb) HP SB).
Qed.
#[using="OK"] Theorem strict_free_null_of : ltac2:(TCodec.tc2 tcn__StrictOfJ ":&R3vDvRCvRNvB%544321&R2%113%847651p041").
Proof.
intros FN fx R M model LB FF LK cr A K (RI & SB & FC) HALT MI H10 Htp Hra STK K0 POST.
pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
apply (FN fx R M model LB FF LK cr A K RI HALT MI H10 Htp Hra STK K0).
intros R' M' model' A' RP HP MRT INC MI' RI'.
apply (POST R' M' model' A' RP HP MRT INC MI'). split; [exact RI'|]. split; [|exact FC].
exact (sj_keep_pres LB LB FF LK _ _ M M' WF (incl_refl _) HP SB).
Qed.
#[using="OK"] Theorem strict_stack_malloc : ltac2:(TCodec.tc2 tcn__StrictOfJ "H'?&R9r1(3+1+2+3(6%118%63931%73:51%83;71%;3<:1&Q@vDvRCvRN&R2vB%211r2%8576521p0:1pUDG1").
Proof.
intros k Hk fx R M model LB FF LK cr A K sp (RI & SB & FC) HALT MI Htp Hra STK ROOM RS K0 POST.
pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
assert (Hk' : In k [0; 1; 2; 3; 4]) by (cbn [In] in *; tauto).
apply (HAJ.aior_stack_malloc _ _ _ _ _ OK k Hk' fx R M model LB FF LK cr A K RI HALT MI Htp Hra STK ROOM RS K0).
intros R' M' model' F fl LK' H10 RP P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 HP MRT MI' RI'.
apply (POST R' M' model' F fl LK' H10 RP P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 HP MRT MI'). split; [exact RI'|]. split.
- exact (sj_keep_pres LB LB FF LK _ _ M M' WF (incl_refl _) HP SB).
- unfold sj_cls in *. rewrite Forall_forall in *. intros f Hf. cbn [app] in Hf. destruct Hf as [<-|Hf]; [exact Hk|].
apply FC. apply in_app_or in Hf. destruct Hf as [Hf|Hf]; apply in_or_app; [left; exact Hf|right; exact (P5 f Hf)].
Qed.
#[using="IMG FLAG OK"] Theorem strict_release : ltac2:(TCodec.tc2 tcn__StrictOfJ "7&QLvDvRC&R2vB%211%63541").
Proof.
intros LB FF LK cr A M M' V F k rs fl (RI & SB & FC) Hin CF W C0 DEF.
pose proof (sj_wf_of LB FF LK cr A M V RI) as WF. pose proof (FLAG LB FF LK cr A M V F k rs fl RI Hin CF) as FL.
split; [exact (HAJ.aior_release _ _ _ _ _ OK LB FF LK cr A M M' V F k rs fl RI Hin CF W C0 DEF)|]. split.
- apply (sj_keep LB FF LK M M' WF); [|exact SB]. intros b a Hb Ha.
pose proof WF as (WB & _ & (_ & AM & _) & _). destruct (WB b Hb) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (RA & Ra).
assert (NE : a <> fl) by (intros ->; specialize (FL Ra); unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *; lia).
destruct (W a Ra NE) as [E|X]; [exact E|exfalso; exact (sj_bsh_not_w LB FF LK 0 0 b a WF Hb Ha X)].
- unfold sj_cls in *. rewrite Forall_forall in *. intros f Hf. apply FC. apply in_app_or in Hf. apply in_or_app.
destruct Hf as [Hf|Hf]; [left; exact (sj_ff_remove_in F FF f Hf)|right; exact Hf].
Qed.
#[using="OK"] Theorem strict_leak : ltac2:(TCodec.tc2 tcn__StrictOfJ "5&QJ&R2vB%211%411").
Proof.
intros LB FF LK cr A M V FX (RI & SB & FC) INC ND.
split; [exact (HAJ.aior_leak _ _ _ _ _ OK LB FF LK cr A M V FX RI INC ND)|]. split; [exact SB|].
unfold sj_cls in *. rewrite Forall_forall in *. intros f Hf. apply FC. apply in_app_or in Hf. apply in_or_app.
destruct Hf as [Hf|Hf]; [left; exact (proj2 (proj1 (sj_sfilter_In _ _ _ _ _) Hf))|].
apply in_app_or in Hf. destruct Hf as [Hf|Hf]; [left; exact (INC f Hf)|right; exact Hf].
Qed.
#[using="OK"] Theorem strict_no_return : ltac2:(TCodec.tc2 tcn__StrictOfJ "8&Q8vDvRCvRN&R2vB%211%746541").
Proof.
intros fx R M model LB FF LK cr A K sp (RI & SB & FC) HALT MI Htp Hra STK K0 POST.
pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
apply (HAJ.aior_no_return _ _ _ _ _ OK fx R M model LB FF LK cr A K RI HALT MI Htp Hra STK K0).
intros R' M' model' lo RP Hlo Hlo8 SZ KEEP SCR MRT MI' RI'.
apply (POST R' M' model' lo RP Hlo Hlo8 SZ KEEP SCR MRT MI'). split; [exact RI'|]. split; [|exact FC].
apply (sj_keep LB FF LK M M' WF); [|exact SB]. intros b a Hb Ha.
pose proof WF as (WB & _ & _ & SP1 & SP2). destruct (WB b Hb) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (_ & Ra).
pose proof BR as (_ & _ & _ & B4 & B5 & _). pose proof STK as (_ & ST2 & _).
apply KEEP; [exact Ra| |].
- do 6 right. exists b. split; [exact Hb|exact Ha].
- intros (Y1 & _). pose proof (sj_S_mono (fst b + snd b - 1) lo ltac:(fold sp in ST2; lia)) as MO.
destruct Ha as (_ & X2). assert (E8 : lo mod 8 = 0).
{ pose proof (Z.div_mod lo 4096 ltac:(lia)) as D. rewrite Hlo8, Z.add_0_r in D. rewrite D.
replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by ring. apply Z_mod_mult. }
pose proof (sj_div8_lt (fst b + snd b - 1) lo ltac:(fold sp in ST2; lia) E8) as LT. unfold HeapIfaceA.S in *. lia.
Qed.
Lemma sj_mem_keep : ltac2:(TCodec.tc2 tcn__StrictOfJ "S>'R4&Iy5'S3yR0%211%5241'7y8%611%311p061'H'5'8'?%2211%411&QC%611&M&R6&Q;vDvRCvBr=r<r;r:r9r8r7r6r5r4r3r2%@??>=<;:987654321';&R=zr1%3221&R>&R@+2+R0%3221%5271%;271&Q5&S4&R5r?(S1(:%23QG;1%5241%72QG1&QD%11Q6%;7Q7Q6Q3Q231I&=%H2Q1L&R;%12Q3Q2%G2O1%M241%611'<&S2%12R4Q5%Q811r@%113%63R231p081p0@1p0M1pU6R11'>&R0r>&4%13R6R6Q;&9%13R8R8Q=%63531qU:R91%93R:1QN%93QI64qU:R<1%<3R=1R2p041p0?1p0QJ1pQHRF1pQ8R=1pUJRD1pU>RE1p2RD1pU<RB1pQ@RD1pQ4RE1pQ<RH1pUHRN1pQFS01pQJS61pUBS=1").
Proof. intros fx R M model LB FF LK cr A dst n K M'.
intros PRE KEEP SB. destruct PRE as (RI & _ & _ & _ & _ & _ & _ & _ & _ & _ & DW & _).
pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
apply (sj_keep LB FF LK M M' WF); [|exact SB]. intros b a Hb Ha.
pose proof WF as (WB & _). destruct (WB b Hb) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (_ & Ra).
apply KEEP; [exact Ra| |].
- do 6 right. exists b. split; [exact Hb|exact Ha].
- intros (Y1 & Y2). pose proof (DW (a - dst) ltac:(lia)) as X. replace (dst + (a - dst)) with a in X by ring.
exact (sj_bsh_not_w LB FF LK _ _ b a WF Hb Ha X).
Qed.
#[using="OK"] Lemma sj_strict_mem_pre : ltac2:(TCodec.tc2 tcn__StrictOfJ "R6'R4&Iy5'S3yR0%211%5241'7y8%611%311p061'H'5'8'?%2211%411&QC%611&M&R6&Q;vDvRC&R2vB%211r<r;r:r9r8r7r6r5r4r3r2r1%B?A@=<;:987654321';r=%E?DCA1?>=<;:98765'>&R0&4%13Q0Q08&9%13Q2Q2:%53F31qU:Q31%83Q41E&R7%12FE%>231%?2=1p0A1pQ8Q51pUJQ<1pU>Q=1p2Q<1pU<Q:1pQ@Q<1pQ4Q=1pQ<Q@1pUHQF1pQFQH1pQJQN1pUBR51").
Proof. intros fx R M model LB FF LK cr A dst n K. intros ((RI & SB & FC) & REST). exact (conj (conj RI REST) (conj SB FC)). Qed.
#[using="IMG OK"] Theorem strict_memset : ltac2:(TCodec.tc2 tcn__StrictOfJ "8&Q=vDvRCvRN&R2vB%211%746541").
Proof.
intros fx R M model LB FF LK cr A dst c n K PRE H11 POST.
destruct (sj_strict_mem_pre _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (PRER & SB & FC).
apply (HAJ.aior_memset _ _ _ _ _ OK fx R M model LB FF LK cr A dst c n K PRER H11).
intros R' M' model' H10 RP NB KEEP SCR MRT MI' RI'.
apply (POST R' M' model' H10 RP NB KEEP SCR MRT MI'). split; [exact RI'|]. split; [|exact FC].
exact (sj_mem_keep fx R M model LB FF LK cr A dst n K M' PRER KEEP SB).
Qed.
#[using="IMG OK"] Theorem strict_memcpy_at : ltac2:(TCodec.tc2 tcn__StrictOfJ "A'?'2&Q<vDvRCvRNvBr2r1%76654321&R2%115r3%;6:98216p051pUF>1pUL@1").
Proof.
intros pc mo MC fx R M model LB FF LK cr A dst src n bs K PRE H11 AC SRC APR CLS RD OV POST.
destruct (sj_strict_mem_pre _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (PRER & SB & FC).
apply (MC fx R M model LB FF LK cr A dst src n bs K PRER H11 AC SRC APR CLS RD OV).
intros R' M' model' H10 RP NB KEEP SCR MRT MI' RI'.
apply (POST R' M' model' H10 RP NB KEEP SCR MRT MI'). split; [exact RI'|]. split; [|exact FC].
exact (sj_mem_keep fx R M model LB FF LK cr A dst n K M' PRER KEEP SB).
Qed.
#[using="OK"] Theorem strict_frame : ltac2:(TCodec.tc2 tcn__StrictOfJ "7&QHvDvRC&R2vB%211%63541").
Proof.
intros LB FF LK cr A M M' V (RI & SB & FC) PRIV DEF.
pose proof (sj_wf_of LB FF LK cr A M V RI) as WF.
split; [exact (HAJ.aior_frame _ _ _ _ _ OK LB FF LK cr A M M' V RI PRIV DEF)|]. split; [|exact FC].
apply (sj_keep LB FF LK M M' WF); [|exact SB]. intros b a Hb Ha.
pose proof WF as (WB & _). destruct (WB b Hb) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (_ & Ra).
apply PRIV; [exact Ra|]. right. right. exists b. split; [exact Hb|exact Ha].
Qed.
#[using="OK"] Theorem strict_wf : ltac2:(TCodec.tc2 tcn__StrictOfJ "7&QOvDvRC&R2vB%211%63541").
Proof.
intros LB FF LK cr A M V (RI & SB & FC).
destruct (HAJ.aior_wf _ _ _ _ _ OK LB FF LK cr A M V RI) as (WB & WF & REST).
rewrite Forall_forall in SB. unfold sj_cls in FC. rewrite Forall_forall in FC.
split. { intros b Hb. destruct (WB b Hb) as (B1 & B2 & _ & B4 & B5 & B6 & B7).
split; [exact B1|]. split; [exact B2|]. split; [exact (SB b Hb)|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|exact B7]. }
split. { intros f Hf. destruct (WF f Hf) as (F1 & F2 & F3 & _ & F5 & F6).
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact (FC f (in_or_app _ _ _ (or_introl Hf)))|]. split; [exact F5|exact F6]. }
exact REST.
Qed.
#[using="OK"] Theorem strict_lazy : ltac2:(TCodec.tc2 tcn__StrictOfJ "7&QIvDvRC&R2vB%211%63541").
Proof. intros LB FF LK cr A M model (RI & _ & _). exact (HAJ.aior_lazy _ _ _ _ _ OK LB FF LK cr A M model RI). Qed.
#[using="OK"] Theorem strict_perm : ltac2:(TCodec.tc2 tcn__StrictOfJ "5&QK&R2vB%211%411").
Proof.
intros LB LB' FF FF' LK cr A M V (RI & SB & FC) ELB ND EFF NDF.
split; [exact (HAJ.aior_perm _ _ _ _ _ OK LB LB' FF FF' LK cr A M V RI ELB ND EFF NDF)|]. split.
- rewrite Forall_forall in *. intros b Hb. exact (SB b (proj2 (ELB b) Hb)).
- unfold sj_cls in *. rewrite Forall_forall in *. intros f Hf. apply FC. apply in_app_or in Hf. apply in_or_app.
destruct Hf as [Hf|Hf]; [left; exact (proj2 (EFF f) Hf)|right; exact Hf].
Qed.
#[using="OK"] Theorem strict_statics : ltac2:(TCodec.tc2 tcn__StrictOfJ "7&QNvDv1&R2vB%211%63541").
Proof. intros LB FF LK cr A M V (RI & _ & _). exact (HAJ.aior_statics _ _ _ _ _ OK LB FF LK cr A M V RI). Qed.
#[using="OK"] Theorem strict_flagptr : ltac2:(TCodec.tc2 tcn__StrictOfJ "6&QGvD&R2vB%211%5241").
Proof.
intros LB FF LK cr A M V LB' FF' LK' cr' A' M' V' F k rs rs' fl (RI & _ & _) (RI' & _ & _).
exact (HAJ.aior_flagptr _ _ _ _ _ OK LB FF LK cr A M V LB' FF' LK' cr' A' M' V' F k rs rs' fl RI RI').
Qed.
#[using="OK"] Theorem strict_small_high : ltac2:(TCodec.tc2 tcn__StrictOfJ "5&QM&R2vB%211%411").
Proof. intros LB FF LK cr A M V (RI & _ & _). exact (HAJ.aior_small_high _ _ _ _ _ OK LB FF LK cr A M V RI). Qed.
#[using="IMG FLAG OK"] Theorem strict_ok : ltac2:(TCodec.tc2 tcn__StrictOfJ "9'Q?vDvRCv1vRN&R2vB%211%8576541").
Proof.
constructor.
- exact strict_malloc.
- exact strict_aligned.
- exact strict_free.
- exact strict_stack_malloc.
- exact strict_release.
- exact strict_leak.
- exact strict_no_return.
- exact strict_memset.
- exact (strict_memcpy_at _ _ (HAJ.aior_memcpy _ _ _ _ _ OK)).
- exact (strict_memcpy_at _ _ (HAJ.aior_memmove _ _ _ _ _ OK)).
- exact strict_frame.
- exact strict_wf.
- exact strict_lazy.
- exact strict_perm.
- exact strict_statics.
- exact strict_flagptr.
- exact strict_small_high.
Qed.
End Strict.
Lemma strict_of_nil : ltac2:(TCodec.tc2 tcn__StrictOfJ "Q5'Q>&M'5'8'?%2211%411'S3yR0%211'7y8%511%311p051&R1&QFr5(6%11>&QC%311r4r3r2r1%:897554321&R2r6%211%>81;99=876p051pU4A1pQFC1p2L1pU<Q21pQ6Q41").
Proof. intros HIR cr A M V. intros RI. split; [exact RI|]. split; constructor. Qed.

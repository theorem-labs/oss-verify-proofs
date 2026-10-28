(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3n
YI00 YI02 YI01 YI07 YI03 YI04 YI06 UI2m UI2a UI2b
UI25 UI2j UI2k UI2d UI2f UI0s UI28 UI29 UIYs UIYt.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inl' := repeat (first [ left; reflexivity | right ]).
Ltac inl := cbv; inl'.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma tperm_tabs : forall (ti lm lc li tm ld g : Z * Z) (B : list (Z * Z)),
Permutation ([ld; ti; lm; lc; li; tm] ++ g :: B) ([ti; lm; lc; li; tm; ld; g] ++ B).
Proof.
intros.
change ([ld; ti; lm; lc; li; tm] ++ g :: B) with (ld :: ([ti; lm; lc; li; tm] ++ g :: B)).
change ([ti; lm; lc; li; tm; ld; g] ++ B) with ([ti; lm; lc; li; tm] ++ ld :: (g :: B)). apply Permutation_middle.
Qed.
Lemma tperm_ok8 : forall (bb ti lm lc li tm ld g : Z * Z) (B : list (Z * Z)),
Permutation (bb :: [ti; lm; lc; li; tm; ld; g] ++ B) ([ld; ti; lm; lc; li; tm] ++ g :: bb :: B).
Proof.
intros. eapply perm_trans; [apply (Permutation_middle ([ti; lm; lc; li; tm; ld; g]) B bb)|].
change ([ti; lm; lc; li; tm; ld; g] ++ bb :: B) with ([ti; lm; lc; li; tm; ld; g] ++ (bb :: B)).
apply Permutation_sym. apply tperm_tabs.
Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma tjournal_restart_sub : forall STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1,
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 -> sp1 mod 16 = 0 -> 0 <= STK1 -> alloc_ceiling + STK1 <= sp1 -> sp1 < 2 ^ 63 ->
journal ubs2_msyms MR STK1 sp1 FP1 Lc Ac memc mdc Lc Ac memc mdc.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 (HH & Hvm & Hhigh & Hblk & Hgone & (Hal & Hstk0 & Hceil & H63 & Hstw) & Herr & Himg)
Hlo Hhi Hal1 Hstk1 Hceil1 H631.
split; [exact HH|]. split; [exists (m_vmmaps mdc); apply with_vmmaps_self|].
split; [intros a Ha Hna; split; [reflexivity | split; intros X; exact X]|].
split; [intros; reflexivity|]. split; [intros a n i H1 H2; exfalso; exact (H2 H1)|].
split; [| split; [exact Herr | apply img_kept_refl]].
split; [exact Hal1|]. split; [exact Hstk1|]. split; [exact Hceil1|]. split; [exact H631|].
intros a Ha. apply Hstw. lia.
Qed.
Lemma tseps_of_perm : forall L1 A1 m1 md1 l rest,
heap_ok MR L1 A1 m1 md1 -> Permutation (blocks L1 A1) (l ++ rest) -> seps l.
Proof.
intros L1 A1 m1 md1 l. induction l as [|b l IH]; intros rest HH HP; cbn; [exact I|].
split.
- apply seps_from_of_all. intros c Hc.
exact (heap_sep_perm _ _ LAWS _ _ _ _ b (l ++ rest) c HH HP ltac:(apply in_app_iff; left; exact Hc)).
- apply (IH (b :: rest) HH). eapply Permutation_trans; [exact HP|]. cbn [app]. apply Permutation_middle.
Qed.
Lemma tsep_parts : forall L1 A1 m1 md1 l R t b,
heap_ok MR L1 A1 m1 md1 -> Permutation (blocks L1 A1) (l ++ R) -> In t l -> In b R ->
fst t + snd t <= fst b \/ fst b + snd b <= fst t.
Proof.
intros L1 A1 m1 md1 l R t b HH HP Ht Hb.
destruct (in_split _ _ Ht) as (l1 & l2 & ->).
apply (heap_sep_perm _ _ LAWS _ _ _ _ t (l1 ++ l2 ++ R) b HH).
- eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
- apply in_app_iff. right. apply in_app_iff. right. exact Hb.
Qed.
Lemma trodata_ok_of_heap : forall L1 A1 m1 md1, heap_ok MR L1 A1 m1 md1 -> lzw_rodata_ok m1.
Proof.
intros L1 A1 m1 md1 HH i Hi. apply (il_rodata IMG L1 A1 m1 md1 _ (proj1 HH)).
change (ms_debruijn ubs2_msyms) with ubs2_D_debruijn32. unfold ubs2_D_debruijn32, ubs2_D_const_u64_0x0101010101010102. lia.
Qed.
Theorem ubs2_lzw : lzw_spec API.
Proof.
unfold lzw_spec.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs pR nP img idl icl bi Li
HJ Hid Hra0 Htp0 G10 G11 G12 G13 G14 Hal16 Hwlo HpR1 HpR2 HpR8 HnP Hidl Hicl Hbi Hbi1 Hbi2 HRO.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : LZW_STK = 8400) by reflexivity.
pose proof (ubs2_resetDict API IMG) as RESET.
pose proof HJ as (HH0 & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc bi Li HH0 Hbi ltac:(lia)) as (Hbi0 & Hbi3 & _).
apply (SR_mono _ _ (tlzw_post API STK sp0 FP L A mem md Lc Ac memc regs pR)); [| intros c' Hc'; exact Hc'].
eapply SR_bind; [eapply (tlzw_pro API IMG); eassumption|].
cbv beta. intros c' [Hdone | Hok]; [apply SR_ret; exact Hdone|].
destruct Hok as (L6 & A6 & regs6 & mem6 & md6 & g & ti & lm & lc & li & tm & ld & -> & HJ6 & Hid6 & G2 & G3 & G4 & G8 & G20 & G21 & G18 & G19 & G9
& HFS & W0 & W8 & W16 & W24 & W32 & W40 & W48 & V56 & V60 & V64 & V66 & HB6 & Htok6 & Wg & Hgsep & MHI6 & MBL6).
pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [HMR HMR0].
remember (nP / (4094 - idl)) as MRv eqn:HMRv. apply hideP_i in HMRv.
replace (2 * (MRv + nP + 2)) with (2 * (nP + 2 + MRv)) in HB6, Htok6 by lia.
pose proof (bv_unsigned_in_range 64 (getr regs 3)) as Hgp. change (bv_modulus 64) with (2 ^ 64) in Hgp.
set (cx := mkTCX (spZ regs - 112) g ti lm lc li tm ld img nP idl icl pR MRv bi Li (bv_unsigned (getr regs 3))).
assert (Htabs : tcx_tabs cx = [(ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl); (ld, 2 * (nP + 2 + MRv)); (g, 72)]) by reflexivity.
assert (HCX : tcx_ok cx).
{ unfold tcx_ok; cbn [y_sp y_g y_ti y_lm y_lc y_li y_tm y_ld y_img y_nP y_idl y_icl y_pR y_MR y_bi y_Li y_gp cx].
assert (Hspm : (spZ regs - 112) mod 16 = 0).
{ replace (spZ regs - 112) with (spZ regs + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
repeat split; first [lia | exact Hspm | exact HpR8]. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HH6.
assert (HBt : Permutation (blocks L6 A6) (tcx_tabs cx ++ blocks Lc Ac)).
{ eapply Permutation_trans; [exact HB6|]. rewrite Htabs. apply tperm_tabs. }
assert (Hin6 : forall b, In b (tcx_tabs cx) -> In b (blocks L6 A6)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HBt|]. apply in_app_iff. left. exact Hb. }
assert (HRG : tcx_ranges cx).
{ unfold tcx_ranges. rewrite Htabs. cbn [ranges].
assert (R : forall p n, In (p, n) (tcx_tabs cx) -> 0 < n -> (4096 <= p /\ p + n <= alloc_ceiling /\ p mod 16 = 0 /\ 0 < n)).
{ intros p n Hp Hn. destruct (heap_blocks_range _ _ LAWS _ _ _ _ p n HH6 (Hin6 _ Hp) Hn) as (R1 & R2 & R3). repeat split; assumption. }
rewrite Htabs in R. cbv [In] in R.
assert (Hsq : 8 <= 2 * idl * idl) by nia.
repeat split; try exact I;
first [ eapply proj1; eapply R; [tauto | lia]
| eapply (fun p n H1 H2 => proj1 (proj2 (R p n H1 H2))); [tauto | lia]
| eapply (fun p n H1 H2 => proj1 (proj2 (proj2 (R p n H1 H2)))); [tauto | lia]
| lia ]. }
assert (HBi6 : In (bi, Li) (blocks L6 A6)).
{ eapply Permutation_in; [apply Permutation_sym; exact HBt|]. apply in_app_iff. right. exact Hbi. }
assert (HSEP : tcx_seps cx).
{ unfold tcx_seps. cbn [y_bi y_Li cx].
destruct (in_split _ _ Hbi) as (b1 & b2 & Hsplit).
eapply (tseps_of_perm L6 A6 mem6 md6 _ (b1 ++ b2) HH6).
eapply Permutation_trans; [exact HBt|]. rewrite Hsplit, <- app_assoc. change ([(bi, Li)] ++ (b1 ++ b2)) with ((bi, Li) :: (b1 ++ b2)).
apply Permutation_app_head. apply Permutation_sym. apply Permutation_middle. }
assert (HBL : tcx_blocks cx (blocks L6 A6)) by (split; [exact Hin6 | exact HBi6]).
assert (HWIN : tcx_win STK sp0 cx) by (unfold tcx_win; cbn [y_sp cx]; split; lia).
assert (HWT : tcx_wtok STK sp0 FP (blocks L A) cx).
{ intros b Hb. rewrite Htabs in Hb. cbv [In] in Hb.
destruct Hb as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; [.. | exact Wg]; apply (fun x H => proj1 (Htok6 x H)); cbv [In]; inl'. }
destruct (arr16_of_present ubs2segs mem6 tm (Z.to_nat (2049 * idl))) as (TM0 & LenTM & ATM).
{ intros a Ha. rewrite Z2Nat.id in Ha by lia. replace a with (tm + (a - tm)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ tm (4098 * idl) (a - tm) HH6 ltac:(apply Hin6; rewrite Htabs; inl) ltac:(lia))). }
assert (HFX6 : tlzw_regs_fix regs6 cx).
{ unfold tlzw_regs_fix, y_tisz; cbn [y_sp y_g y_idl y_pR y_icl y_gp cx]. rewrite Z_to_bv_bv_unsigned.
repeat split; try assumption. rewrite G4. exact Htp0. }
assert (HGA6 : gen_at mem6 cx 0 0 0).
{ unfold gen_at; cbn [y_g y_ti y_lm y_lc y_li y_tm y_ld y_img y_nP cx].
repeat split; first [apply val_mem_word_mem; assumption | assumption]. }
eapply SR_bind.
{ eapply (tlzw_init_run API IMG RESET cx STK sp0 FP L A mem md L6 A6 md6 regs6 mem6 TM0 HCX HRG HSEP HBL HWIN HWT HJ6 HFX6 HGA6 ATM LenTM). }
cbv beta. intros c' (regsH & memH & -> & HJH & HFX & HGAH & HTB & HINV & R11 & R22 & MEMI).
set (FPl := [(ti, ti + 2 * idl * idl); (lm, lm + 8192); (lc, lc + 4096); (li, li + 8192); (tm, tm + 4098 * idl); (ld, ld + 2 * (nP + 2 + MRv)); (g, g + 72)]).
assert (JL0 : journal ubs2_msyms MR LZW_STK (spZ regs) FPl L6 A6 memH md6 L6 A6 memH md6).
{ eapply (tjournal_restart_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJH); lia. }
assert (HWINl : tcx_win LZW_STK (spZ regs) cx) by (unfold tcx_win; cbn [y_sp cx]; split; lia).
assert (HWTl : tcx_wtok LZW_STK (spZ regs) FPl (blocks L6 A6) cx).
{ intros b Hb blc i Hin Hi. right. left. split.
- rewrite Htabs in Hb. subst FPl. cbv [In] in Hb.
destruct Hb as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]; cbn [fst snd] in Hi |- *.
+ exists (ti, ti + 2 * idl * idl). split; [cbv [In]; inl' | cbn [fst snd]; lia].
+ exists (lm, lm + 8192). split; [cbv [In]; inl' | cbn [fst snd]; lia].
+ exists (lc, lc + 4096). split; [cbv [In]; inl' | cbn [fst snd]; lia].
+ exists (li, li + 8192). split; [cbv [In]; inl' | cbn [fst snd]; lia].
+ exists (tm, tm + 4098 * idl). split; [cbv [In]; inl' | cbn [fst snd]; lia].
+ exists (ld, ld + 2 * (nP + 2 + MRv)). split; [cbv [In]; inl' | cbn [fst snd]; lia].
+ exists (g, g + 72). split; [cbv [In]; inl' | cbn [fst snd]; lia].
- exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact Hin | lia]. }
assert (Hs0 : la_s (lzw_init (y_idl cx) TM0) < y_nP cx) by (cbn; lia).
eapply SR_bind.
{ eapply (crawl_loop API IMG RESET cx LZW_STK (spZ regs) FPl L6 A6 memH md6 L6 A6 md6 HCX HRG HSEP HBL HWINl HWTl
(Z.to_nat (y_nP cx - 0)) (lzw_init (y_idl cx) TM0) regsH memH); try eassumption.
all: cbn [la_lp la_mp la_dp la_s lzw_init]; first [exact HGAH | exact R11 | exact R22 | lia]. }
cbv beta. intros c' (r & HCR & Hr).
destruct HCR as (regs' & mem' & Hc' & JL' & HAE & HF' & Hrest).
pose proof HRG as HRG'. unfold tcx_ranges in HRG'. rewrite Htabs in HRG'. cbn [ranges] in HRG'.
assert (FPcond : forall a, inFP FPl a ->
(inFP FP a /\ a < alloc_ceiling) \/ (exists b n, In (b, n) (blocks L6 A6) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n)).
{ intros a Ha. subst FPl.
Ltac fp1 Ha HWT Hin6 Htabs Hceil p n :=
eapply (sub_cond_of_wtok _ _ _ _ _ p n); [apply HWT; rewrite Htabs; inl | apply Hin6; rewrite Htabs; inl | | exact Hceil | apply inFP_cons; left; exact Ha].
apply inFP_cons in Ha as [Ha|Ha]; [fp1 Ha HWT Hin6 Htabs Hceil ti (2 * idl * idl); lia|].
apply inFP_cons in Ha as [Ha|Ha]; [fp1 Ha HWT Hin6 Htabs Hceil lm 8192; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [fp1 Ha HWT Hin6 Htabs Hceil lc 4096; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [fp1 Ha HWT Hin6 Htabs Hceil li 8192; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [fp1 Ha HWT Hin6 Htabs Hceil tm (4098 * idl); lia|].
apply inFP_cons in Ha as [Ha|Ha]; [fp1 Ha HWT Hin6 Htabs Hceil ld (2 * (nP + 2 + MRv)); lia|].
apply inFP_cons in Ha as [Ha|Ha]; [fp1 Ha HWT Hin6 Htabs Hceil g 72; lia|].
exfalso. exact (inFP_nil _ Ha). }
assert (HJ' : journal ubs2_msyms MR STK sp0 FP L A mem md L6 A6 mem' md6).
{ eapply (journal_sub_gen _ _ LAWS); [exact HJH | exact JL' | lia | lia | exact FPcond]. }
pose proof (journal_high_kept _ _ _ _ _ _ _ _ _ _ _ _ _ JL') as JHK. pose proof (journal_blocks_kept _ _ _ _ _ _ _ _ _ _ _ _ _ JL') as JBK.
change (ms_segs ubs2_msyms) with ubs2segs in JHK, JBK.
assert (MHIx : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - LZW_STK <= a < spZ regs) -> mbyte ubs2segs mem' a = mbyte ubs2segs memc a).
{ intros a Ha Hna. rewrite (proj1 (JHK a Ha ltac:(lia))).
rewrite (MEMI a ltac:(lia)) by first [ unfold rd_written, y_tisz; cbn [y_sp y_g y_ld y_ti y_lm y_lc y_li y_idl cx]; lia
| unfold RESET_STK; cbn [y_sp cx]; lia | left; lia ].
apply MHI6; [exact Ha | lia]. }
assert (MBLx : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem' (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hb Hi.
destruct (heap_blocks _ _ LAWS _ _ _ _ b m i HH0 Hb Hi) as (_ & Hb0 & Hb1 & _).
assert (Hbin : In (b, m) (blocks L6 A6)) by (eapply Permutation_in; [apply Permutation_sym; exact HBt | apply in_app_iff; right; exact Hb]).
assert (SEP : forall t, In t (tcx_tabs cx) -> fst t + snd t <= b \/ b + m <= fst t).
{ intros t Ht. exact (tsep_parts L6 A6 mem6 md6 _ _ t (b, m) HH6 HBt Ht Hb). }
rewrite Htabs in SEP. cbv [In] in SEP.
pose proof (SEP (ti, 2 * idl * idl) ltac:(tauto)) as S1. pose proof (SEP (lm, 8192) ltac:(tauto)) as S2. pose proof (SEP (lc, 4096) ltac:(tauto)) as S3.
pose proof (SEP (li, 8192) ltac:(tauto)) as S4. pose proof (SEP (tm, 4098 * idl) ltac:(tauto)) as S5. pose proof (SEP (ld, 2 * (nP + 2 + MRv)) ltac:(tauto)) as S6.
pose proof (SEP (g, 72) ltac:(tauto)) as S7.
cbn [fst snd] in S1, S2, S3, S4, S5, S6, S7. clear SEP.
rewrite (JBK b m i Hbin Hbin Hi).
2:{ subst FPl. intros Hf. repeat (apply inFP_cons in Hf as [Hf|Hf]; [lia|]). exact (inFP_nil _ Hf). }
rewrite (MEMI (b + i) ltac:(lia)) by first [ unfold rd_written, y_tisz; cbn [y_sp y_g y_ld y_ti y_lm y_lc y_li y_idl cx]; lia
| unfold RESET_STK; cbn [y_sp cx]; lia | right; exists b, m; split; [exact Hbin | lia] ].
exact (MBL6 b m i Hb Hi). }
assert (HFS' : frame_saved ubs2_msyms regs mem' (spZ regs)).
{ eapply (frame_saved_kept ubs2_msyms); [| intros a Ha; apply HAE; cbn [y_sp cx]; lia].
eapply (frame_saved_kept ubs2_msyms); [exact HFS |]. intros a Ha. apply MEMI; [lia | | unfold RESET_STK; cbn [y_sp cx]; lia | left; lia].
unfold rd_written, y_tisz; cbn [y_sp y_g y_ld y_ti y_lm y_lc y_li y_idl cx]. lia. }
assert (Hnz6 : nz [(ld, 2 * (nP + 2 + MRv)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]
= [(ld, 2 * (nP + 2 + MRv)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]).
{ apply tnz_id. intros b Hb. exact (proj2 (Htok6 b Hb)). }
assert (Hftok : forall b, In b (nz [(ld, 2 * (nP + 2 + MRv)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]) ->
ftok FP (blocks L A) b).
{ rewrite Hnz6. intros [p n] Hb. eapply ftok_of_wtok; [exact (proj1 (Htok6 _ Hb)) | | exact Hceil].
cbv [In] in Hb. repeat (destruct Hb as [Hb|Hb]; [apply pair_equal_spec in Hb as [<- <-]; lia|]). destruct Hb. }
assert (Hgtok : ftok FP (blocks L A) (g, 72)) by (eapply ftok_of_wtok; [exact Wg | lia | exact Hceil]).
assert (Hrng : forall b, In b [(ld, 2 * (nP + 2 + MRv)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)] -> 0 <= fst b < 2 ^ 64).
{ intros b Hb. cbv [In] in Hb. repeat (destruct Hb as [<-|Hb]; [cbn [fst]; lia|]). destruct Hb. }
pose proof HF' as (F2 & F8 & F20 & F21 & F18 & F19 & F9 & F4 & F3).
cbn [y_sp y_g y_idl y_pR y_icl y_gp cx] in F2, F8, F20, F21, F18, F19, F9, F4, F3.
rewrite Z_to_bv_bv_unsigned in F3.
assert (GP : forall m lp dp mp, gen_at m cx lp dp mp ->
gptrs m g (ld, 2 * (nP + 2 + MRv)) (ti, 2 * idl * idl) (lm, 8192) (lc, 4096) (li, 8192) (tm, 4098 * idl)).
{ intros m lp' dp' mp' (V0 & V8 & V16 & V24 & V32 & V40 & _). unfold gptrs. cbn [fst y_g y_ti y_lm y_lc y_li y_tm y_ld cx] in *.
repeat split; apply val_mem_word_mem; assumption. }
assert (FIN : forall c'' rv Bfin (mid : word -> option byte),
tclean_post API STK sp0 FP L A mem md regs mid Bfin rv c'' ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - LZW_STK <= a < spZ regs) -> ~ (pR <= a < pR + 12) ->
mbyte ubs2segs mid a = mbyte ubs2segs memc a) ->
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mid (b + i) = mbyte ubs2segs memc (b + i)) ->
(forall b, In b (blocks Lc Ac) -> In b Bfin) ->
((rv = 0 /\ exists bb Lbb M, Bfin = (bb, Lbb) :: blocks Lc Ac /\
(forall blc i, In (bb, Lbb) blc -> 0 <= i < Lbb -> wr_byte STK sp0 FP (blocks L A) blc (bb + i)) /\
word_mem ubs2segs mid pR bb /\ val_mem ubs2segs mid (pR + 8) 4 M /\ 1 <= M <= Lbb)
\/ ((rv = 2 \/ rv = 5) /\ Bfin = blocks Lc Ac /\ (forall a, pR <= a < pR + 12 -> mbyte ubs2segs mid a = mbyte ubs2segs memc a))) ->
tlzw_post API STK sp0 FP L A mem md Lc Ac memc regs pR c'').
{ intros c'' rv Bfin mid (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & Hid2 & HP2 & H10 & MHI2 & MBL2 & HB2) Mhi Mbl Hsub Hcase.
exists L2, A2, regs2, mem2, md2, rv. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact H10|].
split. { intros a Ha Hna Hnp. rewrite (MHI2 a Ha ltac:(lia)). exact (Mhi a Ha ltac:(lia) Hnp). }
split. { intros b m i Hb Hi. rewrite (MBL2 b m i (Hsub _ Hb) Hi). exact (Mbl b m i Hb Hi). }
destruct Hcase as [(-> & bb & Lbb & M & -> & Hw & W1 & W2 & HM) | (Hrv & -> & HpR)].
- left. split; [reflexivity|]. exists bb, Lbb, M. split; [exact HB2|]. split; [exact Hw|].
split. { intros k Hk. rewrite (MHI2 (pR + Z.of_nat k)); [apply W1; exact Hk | lia | lia]. }
split. { intros k Hk. rewrite (MHI2 (pR + 8 + Z.of_nat k)); [apply W2; exact Hk | lia | lia]. }
exact HM.
- right. split; [exact Hrv|]. split; [exact HB2|]. intros a Ha. rewrite (MHI2 a); [apply HpR; exact Ha | lia | lia]. }
destruct r as [X'|X'|X']; [ | destruct Hr | ]; subst c'.
-
destruct Hrest as [HGA' HINV'].
eapply SR_mono.
{ eapply (tlzw_eidx API IMG STK sp0 FP L A mem md L6 A6 md6 regs regs' mem' g
(ld, 2 * (nP + 2 + MRv)) (ti, 2 * idl * idl) (lm, 8192) (lc, 4096) (li, 8192) (tm, 4098 * idl) (blocks Lc Ac));
try eassumption; try lia.
- rewrite Hnz6. exact HB6.
- exact (GP _ _ _ _ HGA').
- rewrite F4. symmetry. exact Htp0. }
cbv beta. intros c'' HC. eapply (FIN c'' 5 (blocks Lc Ac) mem' HC).
+ intros a Ha Hna _. exact (MHIx a Ha Hna).
+ exact MBLx.
+ intros b Hb. exact Hb.
+ right. split; [right; reflexivity|]. split; [reflexivity|]. intros a Ha. apply MHIx; lia.
-
destruct Hrest as (HGA' & HINV' & Hs').
pose proof (lp_exit_bound (y_idl cx) (y_nP cx) (y_MR cx) X' ltac:(unfold lzw_par; cbn [y_idl y_nP y_MR cx]; lia) HINV') as Hlpx.
pose proof (mp_bound (y_idl cx) (y_nP cx) X' ltac:(cbn; lia) HINV') as Hmpb.
assert (Hdpb : 4 <= la_dp X' <= 4096).
{ destruct X' as [TI LM LI TM s lp dp mp Cn R]. cbn [la_dp].
destruct HINV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & _). cbn [y_idl cx] in Hdp. lia. }
assert (Hlp0 : 0 <= la_lp X') by exact (proj2 Hlpx).
assert (Hlp1 : la_lp X' + 1 <= y_cap cx) by (unfold y_cap; exact (proj2 (proj1 Hlpx))).
eapply SR_bind.
{ eapply (tlzw_epiA API IMG cx STK sp0 FP L A mem md L6 A6 md6 regs' mem' (la_lp X') (la_dp X') (la_mp X') (blocks Lc Ac)
HCX HRG HSEP HWIN HJ' Hid6 HBt HWT HF' HGA' Hlp0 Hlp1 Hdpb Hmpb
(trodata_ok_of_heap _ _ _ _ (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ'))); cbn [y_pR y_sp cx]; lia. }
cbv beta. intros cmid Hmid.
eapply SR_bind.
{ eapply (tlzw_epiB API IMG cx STK sp0 FP L A mem md regs' mem' (la_lp X') (blocks Lc Ac) cmid HCX HRG HSEP HWIN HWT);
[exact F4 | exact Hlp0 | exact Hlp1 | cbn [y_pR y_sp cx]; lia | cbn [y_pR cx]; lia | exact Hmid]. }
cbv beta. intros c'' (L7 & A7 & regs7 & mem7 & md7 & rr & -> & HJ7 & Hid7 & E2 & E3 & E4 & E8 & E9 & MHI7 & MBL7 & MG7 & Hcase).
cbn [y_sp y_g y_pR cx] in E2, E8, MHI7, MBL7, MG7, Hcase.
assert (HFS7 : frame_saved ubs2_msyms regs mem7 (spZ regs)).
{ eapply (frame_saved_kept ubs2_msyms); [exact HFS'|]. intros a Ha. apply MHI7; lia. }
assert (Mhi7 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - LZW_STK <= a < spZ regs) -> ~ (pR <= a < pR + 12) ->
mbyte ubs2segs mem7 a = mbyte ubs2segs memc a).
{ intros a Ha Hna Hnp. rewrite (MHI7 a Ha ltac:(lia) Hnp). exact (MHIx a Ha Hna). }
assert (Mbl7 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem7 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hb Hi. rewrite (MBL7 b m i Hb Hi). exact (MBLx b m i Hb Hi). }
assert (GP7 : gptrs mem7 g (ld, 2 * (nP + 2 + MRv)) (ti, 2 * idl * idl) (lm, 8192) (lc, 4096) (li, 8192) (tm, 4098 * idl)).
{ destruct (GP _ _ _ _ HGA') as (Q40 & Q0 & Q8 & Q16 & Q24 & Q32). unfold gptrs. cbn [fst] in *.
repeat split; intros k Hk.
- replace (g + 40 + Z.of_nat k) with (g + (40 + Z.of_nat k)) by lia. rewrite (MG7 (40 + Z.of_nat k)) by lia.
replace (g + (40 + Z.of_nat k)) with (g + 40 + Z.of_nat k) by lia. apply Q40. exact Hk.
- rewrite (MG7 (Z.of_nat k)) by lia. apply Q0. exact Hk.
- replace (g + 8 + Z.of_nat k) with (g + (8 + Z.of_nat k)) by lia. rewrite (MG7 (8 + Z.of_nat k)) by lia.
replace (g + (8 + Z.of_nat k)) with (g + 8 + Z.of_nat k) by lia. apply Q8. exact Hk.
- replace (g + 16 + Z.of_nat k) with (g + (16 + Z.of_nat k)) by lia. rewrite (MG7 (16 + Z.of_nat k)) by lia.
replace (g + (16 + Z.of_nat k)) with (g + 16 + Z.of_nat k) by lia. apply Q16. exact Hk.
- replace (g + 24 + Z.of_nat k) with (g + (24 + Z.of_nat k)) by lia. rewrite (MG7 (24 + Z.of_nat k)) by lia.
replace (g + (24 + Z.of_nat k)) with (g + 24 + Z.of_nat k) by lia. apply Q24. exact Hk.
- replace (g + 32 + Z.of_nat k) with (g + (32 + Z.of_nat k)) by lia. rewrite (MG7 (32 + Z.of_nat k)) by lia.
replace (g + (32 + Z.of_nat k)) with (g + 32 + Z.of_nat k) by lia. apply Q32. exact Hk. }
assert (CL : forall Bfin,
Permutation (blocks L7 A7) (nz [(ld, 2 * (nP + 2 + MRv)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)] ++ (g, 72) :: Bfin) ->
SR ubs2segs (mkCfg (mkst regs7 (Z_to_bv 64 TPC_CLEAN) mem7 (seg_rom ubs2segs)) md7)
(tclean_post API STK sp0 FP L A mem md regs mem7 Bfin rr)).
{ intros Bfin HBf.
assert (Hr2 : 0 <= rr < 2 ^ 64) by (destruct Hcase as [(-> & _) | (-> & _)]; lia).
eapply (tlzw_clean API IMG STK sp0 FP L A mem md L7 A7 md7 regs regs7 mem7 g
(ld, 2 * (nP + 2 + MRv)) (ti, 2 * idl * idl) (lm, 8192) (lc, 4096) (li, 8192) (tm, 4098 * idl) Bfin rr);
try eassumption; try lia.
- rewrite E3. exact F3.
- rewrite E4, F4, Htp0. reflexivity. }
destruct Hcase as [(-> & bb & Lbb & M & HB7 & Hw & Hbb & W1 & W2 & HM) | (-> & HB7 & HpR)].
+
eapply SR_mono; [apply (CL ((bb, Lbb) :: blocks Lc Ac)); rewrite Hnz6|].
{ eapply Permutation_trans; [exact HB7|]. rewrite Htabs. apply tperm_ok8. }
cbv beta. intros c3 HC. eapply (FIN c3 0 ((bb, Lbb) :: blocks Lc Ac) mem7 HC Mhi7 Mbl7).
* intros b Hb. right. exact Hb.
* left. split; [reflexivity|]. exists bb, Lbb, M. repeat split; try assumption; lia.
+
eapply SR_mono; [apply (CL (blocks Lc Ac)); rewrite Hnz6|].
{ eapply Permutation_trans; [exact HB7|]. rewrite Htabs. apply Permutation_sym. apply tperm_tabs. }
cbv beta. intros c3 HC. eapply (FIN c3 2 (blocks Lc Ac) mem7 HC Mhi7 Mbl7).
* intros b Hb. exact Hb.
* right. split; [left; reflexivity|]. split; [reflexivity|]. intros a Ha. rewrite (HpR a Ha). apply MHIx; lia.
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

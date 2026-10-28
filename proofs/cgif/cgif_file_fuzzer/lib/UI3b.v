(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c
YI06 UI5b YI09 YI08 YI0t YI0r YI0o YI0s UI3p UI3n UI3o
UI3k YI62.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u UI30 UI3g UI39 UI37 UI3e UI32 UI33.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0h YI0v UI2z UIZ2 UIZ4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3l UI3f UI35 UI34.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inl' := repeat (first [ left; reflexivity | right ]).
Ltac inl := cbv; inl'.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tperm_tabs : forall (ti lm lc li tm ld g : Z * Z) (B : list (Z * Z)),
Permutation ([ld; ti; lm; lc; li; tm] ++ g :: B) ([ti; lm; lc; li; tm; ld; g] ++ B).
Proof using.
intros.
change ([ld; ti; lm; lc; li; tm] ++ g :: B) with (ld :: ([ti; lm; lc; li; tm] ++ g :: B)).
change ([ti; lm; lc; li; tm; ld; g] ++ B) with ([ti; lm; lc; li; tm] ++ ld :: (g :: B)). apply Permutation_middle.
Qed.
Lemma tperm_ok8 : forall (bb ti lm lc li tm ld g : Z * Z) (B : list (Z * Z)),
Permutation (bb :: [ti; lm; lc; li; tm; ld; g] ++ B) ([ld; ti; lm; lc; li; tm] ++ g :: bb :: B).
Proof using.
intros. eapply perm_trans; [apply (Permutation_middle ([ti; lm; lc; li; tm; ld; g]) B bb)|].
change ([ti; lm; lc; li; tm; ld; g] ++ bb :: B) with ([ti; lm; lc; li; tm; ld; g] ++ (bb :: B)).
apply Permutation_sym. apply tperm_tabs.
Qed.
Lemma lzw_bfin_le : forall bq x n1 n2, 0 <= n1 -> 0 <= n2 ->
rb_le (rb_free (rb_malloc (rb_malloc (rb_acc bq 7 x) n1) n2) n1) (rb_acc bq 9 (x + prN n1 + prN n2 - prN n1)).
Proof using.
intros bq x n1 n2 H1 H2. apply rb_free_acc'.
pose proof (mdelta_le n1 H1). pose proof (mdelta_le n2 H2).
unfold rb_le, rb_malloc, rb_acc, PGSZ in *. cbn. lia.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma tjournal_restart_sub : forall STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1,
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 -> sp1 mod 16 = 0 -> 0 <= STK1 -> alloc_ceiling + STK1 <= sp1 -> sp1 < 2 ^ 63 ->
journal ubs0_msyms MR STK1 sp1 FP1 Lc Ac memc mdc Lc Ac memc mdc.
Proof using API.
intros STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 (HH & Hvm & Hhigh & Hblk & Hgone & (Hal & Hstk0 & Hceil & H63 & Hstw) & Herr & Himg)
Hlo Hhi Hal1 Hstk1 Hceil1 H631.
split; [exact HH|]. split; [apply YI16.os_step_refl|].
split; [intros a Ha Hna; split; [reflexivity | split; intros X; exact X]|].
split; [intros; reflexivity|]. split; [intros a n i H1 H2; exfalso; exact (H2 H1)|].
split; [| split; [exact Herr | apply img_kept_refl]].
split; [exact Hal1|]. split; [exact Hstk1|]. split; [exact Hceil1|]. split; [exact H631|].
intros a Ha. apply Hstw. lia.
Qed.
Lemma tseps_of_perm : forall L1 A1 m1 md1 l rest,
heap_ok MR L1 A1 m1 md1 -> Permutation (blocks L1 A1) (l ++ rest) -> seps l.
Proof using LAWS.
intros L1 A1 m1 md1 l. induction l as [|b l IH]; intros rest HH HP; cbn; [exact I|].
split.
- apply seps_from_of_all. intros c Hc.
exact (heap_sep_perm _ _ LAWS _ _ _ _ b (l ++ rest) c HH HP ltac:(apply in_app_iff; left; exact Hc)).
- apply (IH (b :: rest) HH). eapply Permutation_trans; [exact HP|]. cbn [app]. apply Permutation_middle.
Qed.
Lemma tsep_parts : forall L1 A1 m1 md1 l R t b,
heap_ok MR L1 A1 m1 md1 -> Permutation (blocks L1 A1) (l ++ R) -> In t l -> In b R ->
fst t + snd t <= fst b \/ fst b + snd b <= fst t.
Proof using LAWS.
intros L1 A1 m1 md1 l R t b HH HP Ht Hb.
destruct (in_split _ _ Ht) as (l1 & l2 & ->).
apply (heap_sep_perm _ _ LAWS _ _ _ _ t (l1 ++ l2 ++ R) b HH).
- eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
- apply in_app_iff. right. apply in_app_iff. right. exact Hb.
Qed.
Lemma trodata_ok_of_heap : forall L1 A1 m1 md1, heap_ok MR L1 A1 m1 md1 -> lzw_rodata_ok m1.
Proof using IMG.
intros L1 A1 m1 md1 HH i Hi. apply (il_rodata IMG L1 A1 m1 md1 _ (proj1 HH)).
change (ms_debruijn ubs0_msyms) with ubs0_D_debruijn32. unfold ubs0_D_debruijn32, ubs0_D_const_u64_0x0101010101010102. lia.
Qed.
Hypothesis CBLV : cbl_specV API.
Hypothesis CBBV : cbb_specV API.
Theorem ubs0_lzwX : lzw_specX API.
Proof using CBBV CBLV IMG.
unfold lzw_specX.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs pR nP img idl icl bi Li PIX bq
HJ Hid Hra0 Htp0 G10 G11 G12 G13 G14 Hal16 Hwlo HpR1 HpR2 HpR8 HnP Hidl Hicl Hbi Hbi1 Hbi2 HRO GPIX LenPIX HRq HRM.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : LZW_STK = 8400) by reflexivity.
pose proof (ubs0_reset_specV API IMG) as RESET.
pose proof HJ as (HH0 & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
destruct (heap_blocks_range ubs0_msyms MR LAWS Lc Ac memc mdc bi Li HH0 Hbi ltac:(lia)) as (Hbi0 & Hbi3 & _).
apply (SR_mono _ _ (tlzw_postV_R API (fun m b M0 => M0 <= 2 * nP + 16 /\ lzw_vok idl icl PIX m b M0) (lzw_vnone idl icl PIX) STK sp0 FP L A mem md Lc Ac memc regs pR bq)).
2:{ intros c' (L2 & A2 & regs2 & mem2 & md2 & res & Hc & HJ2 & Hid2 & HPR2 & Hr2 & HM1 & HM2 & Hcase).
exists L2, A2, regs2, mem2, md2, res. split; [exact Hc|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HPR2|].
split; [exact Hr2|]. split; [exact HM1|]. split; [exact HM2|].
destruct Hcase as [(Hr0 & bb & Lbb & M & HPb & Hwb & Hbb & HMb & HM3 & [HMle HVb] & HRo) | (Hr5 & HPb & HpRb & HVN & HRo)].
- left. split; [exact Hr0|]. exists bb, Lbb, M. split; [exact HPb|]. split; [exact Hwb|]. split; [exact Hbb|]. split; [exact HMb|].
split; [exact HM3|]. split; [exact HMle|]. split; [exact HVb | exact HRo].
- right. split; [exact Hr5|]. split; [exact HPb|]. split; [exact HpRb|]. split; [exact HVN | exact HRo]. }
eapply SR_bind; [eapply (tlzw_proV_R API IMG (fun m b M0 => M0 <= 2 * nP + 16 /\ lzw_vok idl icl PIX m b M0) (lzw_vnone idl icl PIX)); eassumption|].
cbv beta. intros c' Hok.
destruct Hok as (L6 & A6 & regs6 & mem6 & md6 & g & ti & lm & lc & li & tm & ld & -> & HJ6 & Hid6 & G2 & G3 & G4 & G8 & G20 & G21 & G18 & G19 & G9
& HFS & W0 & W8 & W16 & W24 & W32 & W40 & W48 & V56 & V60 & V64 & V66 & HB6 & Htok6 & Wg & Hgsep & MHI6 & MBL6 & HRq6).
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
destruct (arr16_of_present ubs0segs mem6 tm (Z.to_nat (2049 * idl))) as (TM0 & LenTM & ATM).
{ intros a Ha. rewrite Z2Nat.id in Ha by lia. replace a with (tm + (a - tm)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ tm (4098 * idl) (a - tm) HH6 ltac:(apply Hin6; rewrite Htabs; inl) ltac:(lia))). }
assert (HFX6 : tlzw_regs_fix regs6 cx).
{ unfold tlzw_regs_fix, y_tisz; cbn [y_sp y_g y_idl y_pR y_icl y_gp cx]. rewrite Z_to_bv_bv_unsigned.
repeat split; try assumption. rewrite G4. exact Htp0. }
assert (HGA6 : gen_at mem6 cx 0 0 0).
{ unfold gen_at; cbn [y_g y_ti y_lm y_lc y_li y_tm y_ld y_img y_nP cx].
repeat split; first [apply val_mem_word_mem; assumption | assumption]. }
assert (GPIX6 : garr8 ubs0segs mem6 (y_img cx) PIX).
{ cbn [y_img cx]. eapply garr8_frame; [exact GPIX|]. intros a Ha. rewrite LenPIX, Z2Nat.id in Ha by lia.
replace a with (bi + (a - bi)) by lia. apply (MBL6 bi Li (a - bi) Hbi). lia. }
eapply SR_bind.
{ eapply (tlzw_init_runV API IMG RESET cx STK sp0 FP L A mem md L6 A6 md6 regs6 mem6 TM0 PIX HCX HRG HSEP HBL HWIN HWT HJ6 HFX6 HGA6 ATM LenTM GPIX6 LenPIX). }
cbv beta. intros c' (regsH & memH & -> & HJH & HFX & HGAH & HTB & HINV & R11 & R22 & MEMI & HVT0 & HVI0).
assert (HSC0 : sim_ctx idl nP PIX) by (split; [exact Hidl | split; [exact LenPIX | exact (vtabs_px _ _ _ _ HVT0)]]).
set (FPl := [(ti, ti + 2 * idl * idl); (lm, lm + 8192); (lc, lc + 4096); (li, li + 8192); (tm, tm + 4098 * idl); (ld, ld + 2 * (nP + 2 + MRv)); (g, g + 72)]).
assert (JL0 : journal ubs0_msyms MR LZW_STK (spZ regs) FPl L6 A6 memH md6 L6 A6 memH md6).
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
{ eapply (crawl_loop API IMG RESET cx LZW_STK (spZ regs) FPl L6 A6 memH md6 L6 A6 md6 PIX (lzw_fin idl PIX) HCX HRG HSEP HBL HWINl HWTl
(Z.to_nat (y_nP cx - 0)) (lzw_init (y_idl cx) TM0) (mkLV (repeat 0 4096) [y_idl cx]) regsH memH); try eassumption.
all: try (cbn [la_lp la_mp la_dp la_s lzw_init]; first [exact HGAH | exact R11 | exact R22 | lia]).
eapply (sim_init idl nP PIX HSC0). reflexivity. }
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
assert (HJ' : journal ubs0_msyms MR STK sp0 FP L A mem md L6 A6 mem' md6).
{ eapply (journal_sub_gen _ _ LAWS); [exact HJH | exact JL' | lia | lia | exact FPcond]. }
pose proof (journal_high_kept _ _ _ _ _ _ _ _ _ _ _ _ _ JL') as JHK. pose proof (journal_blocks_kept _ _ _ _ _ _ _ _ _ _ _ _ _ JL') as JBK.
change (ms_segs ubs0_msyms) with ubs0segs in JHK, JBK.
assert (MHIx : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - LZW_STK <= a < spZ regs) -> mbyte ubs0segs mem' a = mbyte ubs0segs memc a).
{ intros a Ha Hna. rewrite (proj1 (JHK a Ha ltac:(lia))).
rewrite (MEMI a ltac:(lia)) by first [ unfold rd_written, y_tisz; cbn [y_sp y_g y_ld y_ti y_lm y_lc y_li y_idl cx]; lia
| unfold RESET_STK; cbn [y_sp cx]; lia | left; lia ].
apply MHI6; [exact Ha | lia]. }
assert (MBLx : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs0segs mem' (b + i) = mbyte ubs0segs memc (b + i)).
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
assert (HFS' : frame_saved ubs0_msyms regs mem' (spZ regs)).
{ eapply (frame_saved_kept ubs0_msyms); [| intros a Ha; apply HAE; cbn [y_sp cx]; lia].
eapply (frame_saved_kept ubs0_msyms); [exact HFS |]. intros a Ha. apply MEMI; [lia | | unfold RESET_STK; cbn [y_sp cx]; lia | left; lia].
unfold rd_written, y_tisz; cbn [y_sp y_g y_ld y_ti y_lm y_lc y_li y_idl cx]. lia. }
assert (Hnz6 : nz [(ld, 2 * (nP + 2 + MRv)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]
= [(ld, 2 * (nP + 2 + MRv)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]).
{ apply tnz_id. intros b Hb. exact (proj2 (Htok6 b Hb)). }
assert (Hftok : forall b, In b [(ld, 2 * (nP + 2 + MRv)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)] ->
ftok FP (blocks L A) b).
{ intros [p n] Hb. eapply ftok_of_wtok; [exact (proj1 (Htok6 _ Hb)) | | exact Hceil].
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
assert (FIN : forall c'' rv Bfin (mid : word -> option byte) (bfin : rbound),
tclean_post_R API STK sp0 FP L A mem md regs mid Bfin rv bfin c'' ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - LZW_STK <= a < spZ regs) -> ~ (pR <= a < pR + 12) ->
mbyte ubs0segs mid a = mbyte ubs0segs memc a) ->
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs0segs mid (b + i) = mbyte ubs0segs memc (b + i)) ->
(forall b, In b (blocks Lc Ac) -> In b Bfin) ->
((rv = 0 /\ exists bb Lbb M, Bfin = (bb, Lbb) :: blocks Lc Ac /\
(forall blc i, In (bb, Lbb) blc -> 0 <= i < Lbb -> wr_byte STK sp0 FP (blocks L A) blc (bb + i)) /\
word_mem ubs0segs mid pR bb /\ val_mem ubs0segs mid (pR + 8) 4 M /\ 1 <= M <= Lbb /\ M <= 2 * nP + 16 /\ lzw_vok idl icl PIX mid bb M /\
(forall s, res_ok s bfin -> res_ok s (lzw_rb bq (prN Lbb))))
\/ (rv = 5 /\ Bfin = blocks Lc Ac /\ (forall a, pR <= a < pR + 12 -> mbyte ubs0segs mid a = mbyte ubs0segs memc a) /\
lzw_vnone idl icl PIX /\ (forall s, res_ok s bfin -> res_ok s (lzw_rb bq 0)))) ->
tlzw_postV_R API (fun m b M0 => M0 <= 2 * nP + 16 /\ lzw_vok idl icl PIX m b M0) (lzw_vnone idl icl PIX) STK sp0 FP L A mem md Lc Ac memc regs pR bq c'').
{ intros c'' rv Bfin mid bfin (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & Hid2 & HP2 & H10 & MHI2 & MBL2 & HB2 & HRo2) Mhi Mbl Hsub Hcase.
exists L2, A2, regs2, mem2, md2, rv. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact H10|].
split. { intros a Ha Hna Hnp. rewrite (MHI2 a Ha ltac:(lia)). exact (Mhi a Ha ltac:(lia) Hnp). }
split. { intros b m i Hb Hi. rewrite (MBL2 b m i (Hsub _ Hb) Hi). exact (Mbl b m i Hb Hi). }
destruct Hcase as [(-> & bb & Lbb & M & -> & Hw & W1 & W2 & HM & HM2 & (out & VS & VG & VM) & HRimp) | (Hrv & -> & HpR & HVN & HRimp)].
- left. split; [reflexivity|]. exists bb, Lbb, M. split; [exact HB2|]. split; [exact Hw|].
split. { intros k Hk. rewrite (MHI2 (pR + Z.of_nat k)); [apply W1; exact Hk | lia | lia]. }
split. { intros k Hk. rewrite (MHI2 (pR + 8 + Z.of_nat k)); [apply W2; exact Hk | lia | lia]. }
split; [exact HM|]. split; [| exact (HRimp _ HRo2)]. split; [exact HM2|]. exists out. split; [exact VS|]. split; [| exact VM].
eapply garr8_frame; [exact VG|]. intros a Ha. replace a with (bb + (a - bb)) by lia. apply (MBL2 bb Lbb (a - bb)); [left; reflexivity | lia].
- right. split; [exact Hrv|]. split; [exact HB2|]. split; [intros a Ha; rewrite (MHI2 a); [apply HpR; exact Ha | lia | lia] |]. split; [exact HVN | exact (HRimp _ HRo2)]. }
destruct r as [X'|X' V'|X' V']; [ | destruct Hr | ]; subst c'.
-
destruct Hrest as (HGA' & HINV' & HFINN).
eapply SR_mono.
{ eapply (tlzw_eidx_R API IMG STK sp0 FP L A mem md L6 A6 md6 regs regs' mem' g
(ld, 2 * (nP + 2 + MRv)) (ti, 2 * idl * idl) (lm, 8192) (lc, 4096) (li, 8192) (tm, 4098 * idl) (blocks Lc Ac)
(rb_acc bq 7 (lzw_x7 idl nP)));
try eassumption; try lia.
all: first [exact HB6 | exact (GP _ _ _ _ HGA') | rewrite F4; symmetry; exact Htp0 | intros b0 Hb0; apply Hftok; exact Hb0]. }
cbv beta. intros c'' HC. eapply (FIN c'' 5 (blocks Lc Ac) mem' _ HC).
+ intros a Ha Hna _. exact (MHIx a Ha Hna).
+ exact MBLx.
+ intros b Hb. exact Hb.
+ right. split; [reflexivity|]. split; [reflexivity|]. split; [intros a Ha; apply MHIx; lia|].
split.
*
unfold lzw_vnone. rewrite lzw_stream_raster, (sim_codes idl nP PIX HSC0 ltac:(lia)). rewrite HFINN. reflexivity.
*
intros s Hs. apply (lzw_exit_eidx s bq idl nP (rb_acc bq 7 (lzw_x7 idl nP))); [apply rb_le_refl|].
unfold lzw_frees7. cbn [snd] in Hs. rewrite (hideP_e _ HMRv) in Hs.
replace (2 * (nP + 2 + nP / (4094 - idl))) with (2 * (nP / (4094 - idl) + nP + 2)) in Hs by lia. exact Hs.
-
destruct Hrest as (HGA' & HINV' & Hs' & HVT' & HVI' & HSX').
pose proof (lp_exit_bound (y_idl cx) (y_nP cx) (y_MR cx) X' ltac:(unfold lzw_par; cbn [y_idl y_nP y_MR cx]; lia) HINV') as Hlpx.
pose proof (mp_bound (y_idl cx) (y_nP cx) X' ltac:(cbn; lia) HINV') as Hmpb.
assert (Hdpb : 4 <= la_dp X' <= 4096).
{ destruct X' as [TI LM LI TM s lp dp mp Cn R]. cbn [la_dp].
destruct HINV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & _). cbn [y_idl cx] in Hdp. lia. }
assert (Hlp0 : 0 <= la_lp X') by exact (proj2 Hlpx).
assert (Hlp1 : la_lp X' + 1 <= y_cap cx) by (unfold y_cap; exact (proj2 (proj1 Hlpx))).
set (n1 := 12 * (la_lp X' + 1) / 8 + 3). set (n2 := 384 * (la_lp X' + 1) / 255 + 4).
assert (Hn2 : 0 <= n2) by (pose proof (Z.div_pos (384 * (la_lp X' + 1)) 255 ltac:(lia) ltac:(lia)); subst n2; lia).
destruct (lzw_rooms_epi bq idl nP (la_lp X') Hidl ltac:(lia) HRM Hlp0
ltac:(rewrite <- (hideP_e _ HMRv); unfold y_cap, cap in Hlp1; cbn [y_nP y_MR cx] in Hlp1; exact Hlp1)) as [RM1 RM2].
assert (RM2' : room (rb_malloc (rb_acc bq 7 (lzw_x7 idl nP)) n1) n2).
{ eapply room_mono; [apply rb_malloc_acc_k; subst n1; pose proof (Z.div_pos (12 * (la_lp X' + 1)) 8 ltac:(lia) ltac:(lia)); lia | | exact RM2]. lia. }
eapply SR_bind.
{ eapply (tlzw_epiAV_R API IMG cx STK sp0 FP L A mem md L6 A6 md6 regs' mem' (la_lp X') (la_dp X') (la_mp X') (blocks Lc Ac) (v_LD V') (rb_acc bq 7 (lzw_x7 idl nP))
HCX HRG HSEP HWIN HJ' Hid6 HBt HWT HF' HGA' Hlp0 Hlp1 Hdpb Hmpb
(trodata_ok_of_heap _ _ _ _ (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ')));
[cbn [y_pR y_sp cx]; lia | cbn [y_pR y_sp cx]; lia | exact (proj2 (proj2 HVT')) | exact (proj2 (proj2 HVI')) | exact HRq6 | exact RM1 | exact RM2']. }
cbv beta. intros cmid Hmid.
eapply SR_bind.
{ eapply (tlzw_epiBV_R API IMG CBLV CBBV cx STK sp0 FP L A mem md regs' mem' (la_lp X') (blocks Lc Ac) (v_LD V' ++ [y_idl cx + 1]) cmid (rb_acc bq 7 (lzw_x7 idl nP)) HCX HRG HSEP HWIN HWT);
[exact F4 | exact Hlp0 | exact Hlp1 | cbn [y_pR y_sp cx]; lia | cbn [y_pR cx]; lia
| rewrite length_app; cbn [length]; pose proof (proj2 (proj2 HVI')) as LenLD'; lia | exact Hmid]. }
cbv beta. intros c'' (L7 & A7 & regs7 & mem7 & md7 & rr & -> & HJ7 & Hid7 & E2 & E3 & E4 & E8 & E9 & MHI7 & MBL7 & MG7 & Hcase & HRq7).
fold n1 in HRq7. fold n2 in HRq7.
cbn [y_sp y_g y_pR cx] in E2, E8, MHI7, MBL7, MG7, Hcase.
assert (HFS7 : frame_saved ubs0_msyms regs mem7 (spZ regs)).
{ eapply (frame_saved_kept ubs0_msyms); [exact HFS'|]. intros a Ha. apply MHI7; lia. }
assert (Mhi7 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - LZW_STK <= a < spZ regs) -> ~ (pR <= a < pR + 12) ->
mbyte ubs0segs mem7 a = mbyte ubs0segs memc a).
{ intros a Ha Hna Hnp. rewrite (MHI7 a Ha ltac:(lia) Hnp). exact (MHIx a Ha Hna). }
assert (Mbl7 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs0segs mem7 (b + i) = mbyte ubs0segs memc (b + i)).
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
set (bfin7 := rb_free (rb_malloc (rb_malloc (rb_acc bq 7 (lzw_x7 idl nP)) n1) n2) n1) in HRq7.
assert (CL : forall Bfin,
Permutation (blocks L7 A7) ([(ld, 2 * (nP + 2 + MRv)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)] ++ (g, 72) :: Bfin) ->
SR ubs0segs (mkCfg (mkst regs7 (Z_to_bv 64 TPC_CLEAN) mem7 (seg_rom ubs0segs)) md7)
(tclean_post_R API STK sp0 FP L A mem md regs mem7 Bfin rr
(lzw_frees7 bfin7 (2 * (nP + 2 + MRv)) (2 * idl * idl) 8192 4096 8192 (4098 * idl)))).
{ intros Bfin HBf.
assert (Hr2 : 0 <= rr < 2 ^ 64) by (destruct Hcase as (-> & _); lia).
unfold lzw_frees7.
eapply (tlzw_clean_R API IMG STK sp0 FP L A mem md L7 A7 md7 regs regs7 mem7 g
(ld, 2 * (nP + 2 + MRv)) (ti, 2 * idl * idl) (lm, 8192) (lc, 4096) (li, 8192) (tm, 4098 * idl) Bfin rr bfin7);
try eassumption; try lia.
all: first [rewrite E3; exact F3 | rewrite E4, F4, Htp0; reflexivity | intros b0 Hb0; apply Hftok; exact Hb0]. }
destruct Hcase as (-> & bb & Lbb & M & HB7 & Hw & Hbb & W1 & W2 & HM & HM2 & VG7 & VM7 & HLbb).
+
eapply SR_mono; [apply (CL ((bb, Lbb) :: blocks Lc Ac))|].
{ eapply Permutation_trans; [exact HB7|]. rewrite Htabs. apply tperm_ok8. }
cbv beta. intros c3 HC. eapply (FIN c3 0 ((bb, Lbb) :: blocks Lc Ac) mem7 _ HC Mhi7 Mbl7).
* intros b Hb. right. exact Hb.
* left. split; [reflexivity|]. exists bb, Lbb, M. split; [reflexivity|]. split; [exact Hw|]. split; [exact W1|]. split; [exact W2|]. split; [lia|]. split; [exact HM2|].
split.
{
destruct HSX' as (msF & (_ & HLF) & HFSX). exists (raster_of idl icl (v_LD V' ++ [idl + 1])).
split; [| split; [exact VG7 | exact VM7]].
rewrite lzw_stream_raster, (sim_codes idl nP PIX HSC0 ltac:(lia)). rewrite HFSX. cbn [option_map]. rewrite HLF. reflexivity. }
intros s Hs.
assert (ELbb : Lbb = n2).
{ rewrite HLbb. subst n2. rewrite length_app. cbn [length]. pose proof (proj2 (proj2 HVI')) as LenLD'. cbn [y_nP cx] in LenLD'.
rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. rewrite LenLD'. reflexivity. }
rewrite ELbb. apply (lzw_exit_ok s bq idl nP n1 n2 bfin7).
-- subst bfin7. apply lzw_bfin_le; [subst n1; pose proof (Z.div_pos (12 * (la_lp X' + 1)) 8 ltac:(lia) ltac:(lia)); lia | exact Hn2].
-- unfold lzw_frees7. cbn [snd] in Hs. unfold lzw_frees7 in Hs. rewrite (hideP_e _ HMRv) in Hs.
replace (2 * (nP + 2 + nP / (4094 - idl))) with (2 * (nP / (4094 - idl) + nP + 2)) in Hs by lia. exact Hs.
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

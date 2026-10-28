(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw YCbx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC8f AC8c AC93 AC9g AC9f AC95 AC91 AC99 AC92 AC9b AC96 AC9j AC9h AC9a AC9i AC9c AC9d AC9e AC94 AC97 AC98.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0m YI0u YI00 YO07 YI0i YI0h YI0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88 YC89 YC5d YC7y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC90 AC8w AC8v AC8q AC8l AC8k AC8o AC8n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma seps_from_mono : forall (o b : Z * Z) os bs,
fst b <= fst o /\ fst o + snd o <= fst b + snd b ->
Forall2 (fun o' b' : Z * Z => fst b' <= fst o' /\ fst o' + snd o' <= fst b' + snd b') os bs ->
seps_from b bs -> seps_from o os.
Proof.
intros o b os bs Ho HF. induction HF as [|o' b' os' bs' Ho' HF IH]; cbn; intros Hs; [exact I|].
destruct Hs as [H1 H2]. split; [lia | apply IH; exact H2].
Qed.
Lemma seps_mono : forall objs blks : list (Z * Z),
Forall2 (fun o b : Z * Z => fst b <= fst o /\ fst o + snd o <= fst b + snd b) objs blks -> seps blks -> seps objs.
Proof.
intros objs blks HF. induction HF as [|o b os bs Ho HF IH]; cbn; intros Hs; [exact I|].
destruct Hs as [H1 H2]. split; [eapply seps_from_mono; [exact Ho | exact HF | exact H1] | apply IH; exact H2].
Qed.
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AFREEN4 : afree_null04_rule SEGS B MT.
Variable XN : xnums.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Variable CTX : list (list Z).
Hypothesis HUCTX : forall c, In c CTX ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun ra => if ra =? pc_malloc_ra0 (as_code B) then [] else [ra]) ((BASE + 0x14a4) :: tl c))) (as_universe B).
Lemma zone2_of_app : forall a n, in_app a n -> off_img a n -> zone2 a n.
Proof. intros a n [_ H] Hi. split; [exact Hi|]. unfold kLowShadowBeg, kHighMemBeg in H. lia. Qed.
Lemma asep_perm : forall ly S W mem md b c rest,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (b :: rest) -> In c rest -> zdisjoint (block_rng b) (block_rng c).
Proof.
intros ly S W mem md b c rest HAR HP Hc. destruct (in_split _ _ Hc) as (r1 & r2 & ->).
eapply (sep_blocks_perm SEGS B LAWS ly S W mem md b c (r1 ++ r2)); [exact HAR|].
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma aseps_of_perm : forall ly S W mem md l rest,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (l ++ rest) -> seps (map block_rng l).
Proof.
intros ly S W mem md l. induction l as [|b l IH]; intros rest HAR HP; cbn; [exact I|]. split.
- assert (G : forall c, In c l -> zdisjoint (block_rng b) (block_rng c)).
{ intros c Hc. eapply asep_perm; [exact HAR | exact HP | apply in_app_iff; left; exact Hc]. }
clear - G. induction l as [|c l IH']; cbn; [exact I|]. split.
+ pose proof (G c ltac:(left; reflexivity)) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D |- *. lia.
+ apply IH'. intros c' Hc'. apply G. right. exact Hc'.
- apply (IH (b :: rest) HAR). eapply Permutation_trans; [exact HP|]. cbn [app]. apply Permutation_middle.
Qed.
Hypothesis HMAGIC : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) -> lzw_rodata_ok H mem.
Hypothesis HGP : 0 <= as_gp B < 2 ^ 64.
Hypothesis HXM : forall nP idl, 1 <= nP <= 100000000 -> 2 <= idl <= 256 -> pro_msum MT nP idl + epi_msum MT nP idl <= xm_lzw XN nP idl.
Hypothesis HXN : forall nP idl, 1 <= nP <= 100000000 -> 2 <= idl <= 256 -> pro_msum MT nP idl + epi_msum MT nP idl <= xn_lzw XN nP idl.
Lemma pro_msum_nonneg : forall nP idl, 1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= pro_msum MT nP idl.
Proof.
intros nP idl HnP Hidl. unfold pro_msum. pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [M1 M2].
pose proof (mo_malloc_nonneg MT MLAW 72 ltac:(lia)). pose proof (mo_malloc_nonneg MT MLAW (2 * idl * idl) ltac:(nia)).
pose proof (mo_malloc_nonneg MT MLAW 8192 ltac:(lia)). pose proof (mo_malloc_nonneg MT MLAW 4096 ltac:(lia)).
pose proof (mo_malloc_nonneg MT MLAW (4098 * idl) ltac:(lia)).
pose proof (mo_malloc_nonneg MT MLAW (2 * (lzw_MR nP idl + nP + 2)) ltac:(unfold lzw_MR in *; lia)). lia.
Qed.
Lemma epi_msum_frees : forall nP idl, 1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 8 * mo_free MT <= epi_msum MT nP idl.
Proof.
intros nP idl HnP Hidl. unfold epi_msum. pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [M1 M2].
pose proof (mo_malloc_nonneg MT MLAW (12 * (lzw_MR nP idl + nP + 2) / 8 + 3) ltac:(pose proof (Z.div_pos (12 * (lzw_MR nP idl + nP + 2)) 8); unfold lzw_MR in *; lia)).
pose proof (mo_malloc_nonneg MT MLAW (384 * (lzw_MR nP idl + nP + 2) / 255 + 4) ltac:(pose proof (Z.div_pos (384 * (lzw_MR nP idl + nP + 2)) 255); unfold lzw_MR in *; lia)). lia.
Qed.
Lemma tepi_preX_of : forall STK sp0 lyc Sc W memc mdc regs pR nP idl icl WE lyE SE regsE memE mdE E ctx ti lm lc li tm ld lp CODES0 acc,
tepi_pre B STK sp0 lyc Sc W memc mdc regs pR nP idl icl WE lyE SE regsE memE mdE E ctx ti lm lc li tm ld lp ->
arr16 SEGS (mrestrict (w_H WE) memE) ld CODES0 -> Z.of_nat (length CODES0) = lp -> mo_le MT Sc SE acc -> 0 <= acc ->
tepi_preX B MT STK sp0 lyc Sc W memc mdc regs pR nP idl icl WE lyE SE regsE memE mdE E ctx ti lm lc li tm ld lp CODES0 acc.
Proof.
intros * HP HA HL HM HZ. unfold tepi_preX. unfold tepi_pre in HP.
repeat (lazymatch type of HP with _ /\ _ => split; [exact (proj1 HP)|]; apply proj2 in HP end).
split; [exact HP|]. split; [exact HA|]. split; [exact HL|]. split; [exact HM | exact HZ].
Qed.
Theorem pb_lzwX : tlzw_specX SEGS B MT XN (BASE + A_LZW) CTX pa_relro_lo pa_relro_hi.
Proof.
unfold tlzw_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP img idl icl bi Li ch PIX
HJc HROD Hra0 Hra4 Hgp Htp G10 G11 G12 G13 G14 Hch Hctx Hal16 Hwlo Hwhi HpR8 HpRside HpR0 HpR63 HpRw HpRok HnP Hidl Hicl Hbi Hbi1 Hbi2 GPIX LenPIX Hev Hlive MOK.
pose proof (HXM nP idl HnP Hidl) as XMc. pose proof (HXN nP idl HnP Hidl) as XNc.
pose proof (epi_msum_frees nP idl HnP Hidl) as Hepi0. pose proof (pro_msum_nonneg nP idl HnP Hidl) as Hpro0.
pose proof (mo_free_nonneg MT MLAW) as Mf.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJc as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HEV : LZW_EV = 19) by reflexivity.
assert (HC : tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl)
by (unfold tlzw_caller; repeat (split; [assumption|]); assumption).
pose proof (tlzw_pR_bound B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as HpR47.
assert (HJ0 : ajournal SEGS B LZW_TSTK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0).
{ eapply (ajournal_sub_init SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - sp0) HJc); [lia | | lia | rewrite HTS, Has; lia | lia].
rewrite Zminus_mod, Hal16, Hsp0al. reflexivity. }
eapply SRr_bind.
{
eapply (tlzw_proX B TL LAWS MT MLAW AMALLOC4 AMEMSET HUL CTX HUCTX W LZW_TSTK (spZ regs) [] lyc Sc memc mdc [] regs pR nP img idl icl bi Li ch (xm_lzw XN nP idl) HJ0);
first [eassumption | lia]. }
cbv beta. intros W6 c6 _ Hok.
destruct Hok as (ly6 & S6 & regs6 & mem6 & md6 & ctx & ti & lm & lc & li & tm & ld & -> & HJ6 & Gsp6 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 &
G22 & G23 & G24 & G25 & G26 & G10' & HFR6 & S192 & S184 & S176 & S168 & S160 & S152 & S144 & S136 & S112 & S104 & S96 & S88 & S80 &
V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & HB6 & Htok6 & Hfrs6 & MACC6).
pose proof HJ6 as (HAR6 & _ & _ & _ & _ & _ & Hnev6 & _).
pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [HMRb HMR0].
assert (HMRle : nP / (4094 - idl) <= 26055).
{ assert (nP / (4094 - idl) * 3838 <= nP / (4094 - idl) * (4094 - idl)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (am_syms _ _ _ _ (proj1 HARc)) as HSY. pose proof (aso_cells B HSY) as Hcells. pose proof HGP as Hgp64.
rewrite ?C1, ?C2, ?C3, ?C4 in *.
set (cx := mkACX (spZ regs) ctx ti lm lc li tm ld img nP idl icl pR (lzw_MR nP idl) bi Li (as_gp B) (as_tp B)).
assert (Htabs : acx_tabs cx = lzw_tabs ti lm lc li tm ld nP idl) by reflexivity.
assert (HCX : acx_ok cx).
{ unfold acx_ok. cbn [z_sp z_ctx z_ti z_lm z_lc z_li z_tm z_ld z_img z_nP z_idl z_icl z_pR z_MR z_bi z_Li z_gp z_tp cx]. unfold lzw_MR.
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has.
repeat match goal with |- _ /\ _ => split end; first [exact Hal16 | exact HpR8 | lia | reflexivity | match goal with |- ?g => idtac "HCXLEFT" g end]. }
assert (Hin6 : forall b, In b (lzw_tabs ti lm lc li tm ld nP idl ++ [(ctx, 72)]) -> In b (ablocks B ly6 S6)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB6|].
apply in_app_iff in Hb as [Hb|Hb]; apply in_app_iff; [left; exact Hb | right; left; destruct Hb as [<-|[]]; reflexivity]. }
assert (HBi6 : In (bi, Li) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HB6|]; apply in_app_iff; right; right; exact Hbi).
assert (R : forall p n, In (p, n) (lzw_tabs ti lm lc li tm ld nP idl ++ [(ctx, 72)]) -> 0 < n ->
(4096 <= p /\ zone2 p n) /\ p + n <= alloc_ceiling /\ p mod 16 = 0 /\ 0 < n).
{ intros p n Hp Hn. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR6 (Hin6 _ Hp)) as (M16 & M4096 & Mceil & Mapp & _ & _ & Mn). pose proof (proj1 Mapp) as Mhi.
pose proof (blk_off_imgP _ _ _ _ _ _ p n HAR6 (Hin6 _ Hp)) as Mhi_img.
pose proof (req_size_pos n ltac:(lia)). pose proof (zone2_le p n (req_size n) (zone2_of_app p (req_size n) Mapp Mhi_img) ltac:(lia)) as HZ2.
split; [split; [exact M4096 | exact HZ2]|]. repeat split; first [assumption | lia]. }
assert (Hti0 : 0 < 2 * idl * idl) by nia. assert (Hld0 : 0 < 2 * (lzw_MR nP idl + nP + 2)) by (unfold lzw_MR; lia).
pose proof (R ld _ ltac:(unfold lzw_tabs; cbn; tauto) Hld0) as Rld. pose proof (R ti _ ltac:(unfold lzw_tabs; cbn; tauto) Hti0) as Rti.
pose proof (R lm 8192 ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rlm. pose proof (R lc 4096 ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rlc.
pose proof (R li 8192 ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rli. pose proof (R tm _ ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rtm.
pose proof (R ctx 72 ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rg.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HAR6 HBi6) as (_ & _ & Bceil & Bapp & _ & _ & BLi). pose proof (proj1 Bapp) as Bhi.
pose proof (blk_off_imgP _ _ _ _ _ _ bi Li HAR6 HBi6) as Bhi_img.
pose proof (zone2_of_app bi (req_size Li) Bapp Bhi_img) as Bzone.
assert (HRG : acx_ranges cx).
{ unfold acx_ranges. rewrite Htabs. unfold lzw_tabs. cbn [ranges app z_bi z_img z_nP z_Li z_ctx cx]. rewrite ?C1, ?C2, ?C3, ?C4.
destruct Rld as ([? ?] & ? & ? & ?). destruct Rti as ([? ?] & ? & ? & ?). destruct Rlm as ([? ?] & ? & ? & ?). destruct Rlc as ([? ?] & ? & ? & ?).
destruct Rli as ([? ?] & ? & ? & ?). destruct Rtm as ([? ?] & ? & ? & ?). destruct Rg as ([? ?] & ? & ? & ?).
repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
assert (HSEP : acx_seps cx).
{ unfold acx_seps, acx_objs, z_cap, z_tisz, z_tmsz, cap. cbn [z_ld z_ti z_lm z_lc z_li z_tm z_ctx z_img z_nP z_MR z_idl cx].
destruct (in_split _ _ Hbi) as (b1 & b2 & Eb).
apply (seps_mono _ (map block_rng (lzw_tabs ti lm lc li tm ld nP idl ++ [(ctx, 72); (bi, Li)]))).
- unfold lzw_tabs. cbn [map app block_rng fst snd].
pose proof (req_size_pos (2 * (lzw_MR nP idl + nP + 2)) ltac:(lia)). pose proof (req_size_pos (2 * idl * idl) ltac:(lia)).
pose proof (req_size_pos 8192 ltac:(lia)). pose proof (req_size_pos 4096 ltac:(lia)). pose proof (req_size_pos (4098 * idl) ltac:(lia)).
pose proof (req_size_pos 72 ltac:(lia)).
repeat (apply Forall2_cons; [unfold block_rng; cbn [fst snd]; lia|]). apply Forall2_nil.
- eapply (aseps_of_perm ly6 S6 _ _ _ _ (b1 ++ b2) HAR6).
eapply Permutation_trans; [exact HB6|]. rewrite Eb, <- app_assoc. apply Permutation_app_head. cbn [app].
apply perm_skip. apply Permutation_sym. apply Permutation_middle. }
assert (HBL : acx_blk (ablocks B ly6 S6) cx).
{ split; [apply Hin6; apply in_app_iff; right; left; reflexivity|]. split; [exact HBi6|]. intros b Hb. apply Hin6. apply in_app_iff. left. exact Hb. }
assert (HTOK : acx_tok cx (ablocks B lyc Sc)) by (unfold acx_tok; rewrite Htabs; exact Htok6).
assert (HLC : lzw_loop_ctx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly6 S6).
{ unfold lzw_loop_ctx. cbn [z_pR z_nP z_idl z_icl z_sp z_gp z_tp z_ctx cx]. rewrite Htabs.
split; [exact HC|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact HCX|]. split; [exact HRG|]. split; [exact HSEP|]. split; [exact HBL|]. split; [exact HTOK|].
split; [exact HB6|]. split; [exact Hfrs6 | lia]. }
assert (HIR : init_regs regs6 cx).
{ unfold init_regs, alzw_regs_fix. cbn [z_sp z_gp z_tp z_ctx z_ti z_lm z_idl z_li z_ld cx]. rewrite G3, G4.
repeat match goal with |- _ /\ _ => split end; assumption. }
assert (HIM : init_mem (mrestrict (w_H W6) mem6) cx).
{ unfold init_mem, agen_ptrs. cbn [z_sp z_ctx z_ti z_lm z_lc z_li z_tm z_ld z_img z_nP z_idl z_icl z_pR cx].
repeat match goal with |- _ /\ _ => split end; assumption. }
assert (GPIX6 : garr8 SEGS (mrestrict (w_H W6) mem6) img PIX).
{ eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bi Li img PIX HJ6 Hbi HBi6); [lia | rewrite LenPIX; lia | intros a _ (r0 & Hr0 & _); exact Hr0 | exact GPIX]. }
assert (LenPIX' : length PIX = Z.to_nat (z_nP cx)) by (cbn [z_nP cx]; rewrite <- LenPIX, Nat2Z.id; reflexivity).
eapply SRr_bind.
{ apply (tinit_segX B LAWS AMEMSET cx lyc Sc W memc mdc ly6 S6 W6 regs6 mem6 md6 regs PIX HCX HRG HSEP HBL HTOK HJ6 eq_refl eq_refl HIR HIM HFR6 GPIX6 LenPIX'). }
cbv beta. intros W7 c7 _ (-> & regsH & memH & mdH & TM0 & -> & HJH & HRH & H26 & HG & HT & HI & HSL & HSS & HFRH & HKI & HVT0 & HVI0).
assert (HSC0 : sim_ctx idl nP PIX) by (split; [exact Hidl | split; [exact LenPIX' | exact (vtabs_px SEGS _ _ _ _ HVT0)]]).
eapply SRr_bind.
{ eapply (AC8l.crawl_loop B LAWS AMEMSET cx lyc Sc W memc mdc ly6 S6 W6 regs (mrestrict (w_H W6) memH) PIX (lzw_fin (z_idl cx) PIX) HCX HRG HSEP HBL HTOK eq_refl eq_refl
(conj HSL (conj HSS HFRH)) (Z.to_nat (z_nP cx)) (lzw_init (z_idl cx) TM0) (mkLV (repeat 0 4096) [z_idl cx]) regsH memH mdH);
cbn [la_lp la_dp la_mp la_s lzw_init]; first [exact HJH | exact HRH | exact HG | exact HT | exact HI | exact H26 | apply aabove_eq_refl | exact HVT0 | exact HVI0
| eapply (sim_init (z_idl cx) (z_nP cx) PIX HSC0); reflexivity | cbn [z_nP z_idl cx]; lia ]. }
cbv beta. intros W8 c8 _ (-> & r & HCR & Hr).
destruct HCR as (regs' & mem' & md' & -> & HJ' & HA' & Hrest).
destruct (minv cx W6 regs (mrestrict (w_H W6) memH) HCX (conj HSL (conj HSS HFRH)) mem' HA') as (HSL' & HSS' & HFR').
destruct r as [X' | X' V' | X' V']; [ | destruct Hr | ].
-
destruct Hrest as (HFX' & HG' & HI' & HFINN).
destruct X' as [TI LM LI TM s lp dp mp Cn Rn]. cbn [la_lp la_dp la_mp la_s] in *. cbn [z_idl z_nP cx] in HI'.
pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0').
pose proof (countA_nonneg LI LM) as HA0.
pose proof (lp_exit_bound idl nP (nP / (4094 - idl)) _ ltac:(unfold lzw_par; lia) HI') as Hlpx. cbn [la_lp] in Hlpx. unfold cap in Hlpx.
eapply (teidx_failX B TL LAWS MT MLAW AFREE4 AFREEN4 XN HUL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly6 S6 W6 regs' mem' md' lp dp mp PIX
(xm_lzw XN nP idl) (pro_msum MT nP idl) HLC HJ' HFX' HG');
[ lia | lia | lia | exact HSL' | exact HSS' | exact HFR'
|   unfold lzw_vnone; cbn [z_idl z_icl cx]; rewrite lzw_stream_raster, (sim_codes idl nP PIX HSC0 ltac:(lia)); cbn [z_idl cx] in HFINN; rewrite HFINN; reflexivity
| exact MOK | exact MACC6 | exact Hpro0 | clear - XMc Hepi0 Mf; lia | cbn [z_nP z_idl cx]; clear - XNc Hepi0 Mf; lia ].
-
destruct Hrest as (HRH' & HG' & HI' & HsN & HVT' & HVI' & HSX').
destruct (tepi_seed B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly6 S6 W6 regs' mem' md' X' HLC HJ' HRH' HG' HI' HsN HSL' HSS' HFR'
(HMAGIC _ _ (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' HROD))) as (E & HPRE).
destruct HVT' as (GLC' & GPIX' & ALD'). pose proof HVI' as (LenLC' & LenPIXv & LenLD'). destruct HSX' as (msF & [_ HLF] & HFSX).
eapply (tlzw_epiX B TL LAWS MT MLAW AMALLOC4 AFREE4 AFREEN4 XN AMEMCPY HUL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP img idl icl bi Li
W6 ly6 S6 regs' mem' md' E ctx ti lm lc li tm ld (la_lp X') (v_LD V') PIX (xm_lzw XN nP idl) (pro_msum MT nP idl)); first
[ eassumption
| eapply tepi_preX_of; [exact HPRE | exact ALD' | exact LenLD' | exact MACC6 | exact Hpro0]
| rewrite lzw_stream_raster, (sim_codes idl nP PIX HSC0 ltac:(lia)); cbn [z_idl cx] in HFSX; rewrite HFSX; cbn [option_map]; rewrite HLF; reflexivity
| clear - XMc; lia | clear - XNc; lia ].
Qed.
End S.
End e.
End d.

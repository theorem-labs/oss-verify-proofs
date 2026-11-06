(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI07 YI03 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdv YCdx YCdw YCgl YCg2 YCgi YCgh YCg4 YCg0 YCfy YCg8 YCg1 YCfz YCga YCg5 YCgm YCgj YCg9 YCgk YCgc YCgd YCgf YCg3 YCg6 YCg7.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Lemma asep_perm : forall ly S W mem md b c rest,
AR trbsegs B ly S W mem md -> Permutation (ablocks B ly S) (b :: rest) -> In c rest -> zdisjoint (block_rng b) (block_rng c).
Proof.
intros ly S W mem md b c rest HAR HP Hc. destruct (in_split _ _ Hc) as (r1 & r2 & ->).
eapply (sep_blocks_perm trbsegs B LAWS ly S W mem md b c (r1 ++ r2)); [exact HAR|].
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma aseps_of_perm : forall ly S W mem md l rest,
AR trbsegs B ly S W mem md -> Permutation (ablocks B ly S) (l ++ rest) -> seps (map block_rng l).
Proof.
intros ly S W mem md l. induction l as [|b l IH]; intros rest HAR HP; cbn; [exact I|]. split.
- assert (G : forall c, In c l -> zdisjoint (block_rng b) (block_rng c)).
{ intros c Hc. eapply asep_perm; [exact HAR | exact HP | apply in_app_iff; left; exact Hc]. }
clear - G. induction l as [|c l IH']; cbn; [exact I|]. split.
+ pose proof (G c ltac:(left; reflexivity)) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D |- *. lia.
+ apply IH'. intros c' Hc'. apply G. right. exact Hc'.
- apply (IH (b :: rest) HAR). eapply Permutation_trans; [exact HP|]. cbn [app]. apply Permutation_middle.
Qed.
Lemma lzw_rodata_of_arodata : forall (H : word -> bool) mem, arodata_ok B (aview trbsegs H mem) -> lzw_rodata_ok H mem.
Proof.
intros H mem HR. unfold lzw_rodata_ok, A_rodata_magic. intros k Hk.
assert (Hro : forall a, 0x103d8 <= a < 0x103e0 -> in_ro_tfa a).
{ intros a Ha. unfold in_ro_tfa. left. eexists. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia. }
assert (BY : forall a v, 0x103d8 <= a < 0x103e0 ->
option_map (fun b : byte => bv_unsigned b) (seg_rom trbsegs (Z_to_bv 64 a)) = Some v ->
mbyte trbsegs (mrestrict H mem) a = Some (Z_to_bv 8 v)).
{ intros a v Ha Hv. destruct (tl_lib_consts B TL a ltac:(unfold lib_const_addr; lia)) as [Ho He].
pose proof (HR a (Hro a Ha) Ho He) as Hb. rewrite Hv in Hb.
destruct (aview_byte trbsegs H mem a v Hb) as (b & Hm & Hbv & _). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Hbv. pose proof (bv_unsigned_in_range 8 b) as Hr8.
rewrite Z.mod_small; [reflexivity|]. exact Hr8. }
do 8 (destruct k as [|k]; [apply BY; [cbn; lia | vm_compute; reflexivity] |]). lia.
Qed.
Theorem trb_lzw : tlzw_spec B.
Proof.
unfold tlzw_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP img idl icl bi Li ch
HJc HROD Hra0 Hra4 Hgp Htp G10 G11 G12 G13 G14 Hch Hctx Hal16 Hwlo Hwhi HpR8 HpRside HpR0 HpR63 HpRw HpRok HnP Hidl Hicl Hbi Hbi1 Hbi2 Hev Hlive.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HJc as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HEV : LZW_EV = 19) by reflexivity.
assert (HC : tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl)
by (unfold tlzw_caller; repeat (split; [assumption|]); assumption).
pose proof (tlzw_pR_bound B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as HpR47.
assert (HJ0 : ajournal trbsegs B LZW_TSTK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0).
{ eapply (ajournal_sub_init trbsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - sp0) HJc); [lia | | lia | rewrite HTS, Has; lia | lia].
rewrite Zminus_mod, Hal16, Hsp0al. reflexivity. }
eapply SRr_bind.
{ eapply (tlzw_pro B TL LAWS ML AMALLOC AFREE AMEMSET W LZW_TSTK (spZ regs) [] lyc Sc memc mdc [] regs pR nP img idl icl bi Li ch HJ0);
first [eassumption | lia]. }
cbv beta. intros W6 c6 _ [Hfail | Hok].
{
destruct Hfail as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Hfrs2 & HPerm2).
apply SRr_ret. eapply tlzw_fail_post with (res := 2);
[exact LAWS | exact HC | exact HJ2 | lia | exact HP2 | exact Ha0 | left; reflexivity | exact Hfrs2 | exact HPerm2]. }
destruct Hok as (ly6 & S6 & regs6 & mem6 & md6 & ctx & ti & lm & lc & li & tm & ld & -> & HJ6 & Gsp6 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 &
G22 & G23 & G24 & G25 & G26 & G10' & HFR6 & S192 & S184 & S176 & S168 & S160 & S152 & S144 & S136 & S112 & S104 & S96 & S88 & S80 &
V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & HB6 & Htok6 & Hfrs6).
pose proof HJ6 as (HAR6 & _ & _ & _ & _ & _ & Hnev6 & _).
pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [HMRb HMR0].
assert (HMRle : nP / (4094 - idl) <= 26055).
{ assert (nP / (4094 - idl) * 3838 <= nP / (4094 - idl) * (4094 - idl)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (am_syms _ _ _ _ (proj1 HARc)) as HSY. pose proof (aso_cells B HSY) as Hcells. pose proof (tl_gp B TL) as Hgp64.
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
pose proof (blk_off_img _ _ _ _ _ _ p n HAR6 (Hin6 _ Hp)) as Mhi_img.
pose proof (req_size_pos n ltac:(lia)). pose proof (zone2_le p n (req_size n) (zone2_of_app p (req_size n) Mapp Mhi_img) ltac:(lia)) as HZ2.
split; [split; [exact M4096 | exact HZ2]|]. repeat split; first [assumption | lia]. }
assert (Hti0 : 0 < 2 * idl * idl) by nia. assert (Hld0 : 0 < 2 * (lzw_MR nP idl + nP + 2)) by (unfold lzw_MR; lia).
pose proof (R ld _ ltac:(unfold lzw_tabs; cbn; tauto) Hld0) as Rld. pose proof (R ti _ ltac:(unfold lzw_tabs; cbn; tauto) Hti0) as Rti.
pose proof (R lm 8192 ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rlm. pose proof (R lc 4096 ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rlc.
pose proof (R li 8192 ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rli. pose proof (R tm _ ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rtm.
pose proof (R ctx 72 ltac:(unfold lzw_tabs; cbn; tauto) ltac:(lia)) as Rg.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HAR6 HBi6) as (_ & _ & Bceil & Bapp & _ & _ & BLi). pose proof (proj1 Bapp) as Bhi.
pose proof (blk_off_img _ _ _ _ _ _ bi Li HAR6 HBi6) as Bhi_img.
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
assert (HIR : alzw_regs_fix regs6 cx).
{ unfold alzw_regs_fix. cbn [z_sp z_gp z_tp z_ctx z_idl cx]. rewrite G3, G4.
repeat match goal with |- _ /\ _ => split end; assumption. }
assert (HIM : init_mem (mrestrict (w_H W6) mem6) cx).
{ unfold init_mem, agen_ptrs. cbn [z_sp z_ctx z_ti z_lm z_lc z_li z_tm z_ld z_img z_nP z_idl z_icl z_pR cx].
repeat match goal with |- _ /\ _ => split end; assumption. }
eapply SRr_bind.
{ apply (tinit_seg B TL LAWS AMEMSET cx lyc Sc W memc mdc ly6 S6 W6 regs6 mem6 md6 regs HCX HRG HSEP HBL HTOK HJ6 eq_refl eq_refl HIR HIM HFR6). }
cbv beta. intros W7 c7 _ (-> & regsH & memH & mdH & TM0 & -> & HJH & HRH & H26 & HG & HT & HI & HSL & HSS & HFRH & HKI).
eapply SRr_bind.
{ eapply (crawl_loop B TL LAWS AMEMSET cx lyc Sc W memc mdc ly6 S6 W6 regs (mrestrict (w_H W6) memH) HCX HRG HSEP HBL HTOK eq_refl eq_refl
(conj HSL (conj HSS HFRH)) (Z.to_nat (z_nP cx)) (lzw_init (z_idl cx) TM0) regsH memH mdH);
cbn [la_lp la_dp la_mp la_s lzw_init]; first [exact HJH | exact HRH | exact HG | exact HT | exact HI | exact H26 | apply aabove_eq_refl | cbn [z_nP z_idl cx]; lia]. }
cbv beta. intros W8 c8 _ (-> & r & HCR & Hr).
destruct HCR as (regs' & mem' & md' & -> & HJ' & HA' & Hrest).
destruct (minv cx W6 regs (mrestrict (w_H W6) memH) HCX (conj HSL (conj HSS HFRH)) mem' HA') as (HSL' & HSS' & HFR').
destruct r as [X' | X' | X']; [ | destruct Hr | ].
-
destruct Hrest as (HFX' & HG' & HI').
destruct X' as [TI LM LI TM s lp dp mp Cn Rn]. cbn [la_lp la_dp la_mp la_s] in *. cbn [z_idl z_nP cx] in HI'.
pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0').
pose proof (countA_nonneg LI LM) as HA0.
pose proof (lp_exit_bound idl nP (nP / (4094 - idl)) _ ltac:(unfold lzw_par; lia) HI') as Hlpx. cbn [la_lp] in Hlpx. unfold cap in Hlpx.
eapply (teidx_fail B TL LAWS ML AFREE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly6 S6 W6 regs' mem' md' lp dp mp HLC HJ' HFX' HG');
[lia | lia | lia | exact HSL' | exact HSS' | exact HFR'].
-
destruct Hrest as (HRH' & HG' & HI' & HsN).
destruct (tepi_seed B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly6 S6 W6 regs' mem' md' X' HLC HJ' HRH' HG' HI' HsN HSL' HSS' HFR'
(lzw_rodata_of_arodata _ _ (arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' HROD))) as (E & HPRE).
eapply (tlzw_epi B TL LAWS ML AMALLOC AFREE AMEMCPY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP img idl icl bi Li
W6 ly6 S6 regs' mem' md' E ctx ti lm lc li tm ld (la_lp X')); first [eassumption | exact HPRE].
Qed.
End S.
End d.

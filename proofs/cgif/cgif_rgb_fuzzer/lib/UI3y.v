(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI04 YI05
UI1e UI39 UI1i UI57 UI1h YI0x UI16 UI26 UO3n UO0e
YI07 YP14 YI08 YI0c YI0g UI3h UI3d UI4v UIZm
UI4t UI40.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition E2_CAL : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x174).
Definition E2_MSET : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x18c).
Definition E2_M1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1b0).  Definition E2_M2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1cc).  Definition E2_M3 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1dc).
Definition E2_M4 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1f8).
Definition SZ_f : Z := 2097236. Definition SZ_h : Z := 1572927. Definition SZ_u : Z := 524309.
Lemma malloc_post_perm : forall (old blk2 blkc : list (Z * Z)) res n (Wt : Prop),
Permutation blkc old ->
(res = 0 /\ blk2 = blkc) \/ (res <> 0 /\ res mod 16 = 0 /\ (exists b1 b2, blk2 = b1 ++ (res, n) :: b2 /\ blkc = b1 ++ b2) /\ Wt) ->
Permutation blk2 (old ++ optb res n) /\ (forall x, In x blkc -> In x blk2).
Proof.
intros old blk2 blkc res n Wt HP [[-> ->] | (Hnz & _ & (b1 & b2 & -> & ->) & _)].
- unfold optb. rewrite Z.eqb_refl, app_nil_r. split; [exact HP | intros x Hx; exact Hx].
- unfold optb. destruct (Z.eqb_spec res 0) as [Hc|Hc]; [lia|]. split.
+ eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
eapply Permutation_trans; [| apply Permutation_cons_append]. apply perm_skip. exact HP.
+ intros x Hx. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx].
Qed.
Lemma slot_kept_at : forall regs0 (m m' : word -> option byte) off v,
slot regs0 m off v -> (forall x0, sp regs0 + off <= x0 < sp regs0 + off + 8 -> mbyte ubs2segs m' x0 = mbyte ubs2segs m x0) -> slot regs0 m' off v.
Proof. intros regs0 m m' off v Hs HI k Hk. rewrite HI; [apply Hs; exact Hk | lia]. Qed.
Lemma malloc_res_range {rc : YN05.RunCeil}   : forall (MR : MR_t) (LAWS : MR_laws ubs2_msyms MR) L2 A2 mem2 md2 (blkc : list (Z * Z)) res n (Wt : Prop),
heap_ok MR L2 A2 mem2 md2 -> 0 < n ->
(res = 0 /\ blocks L2 A2 = blkc) \/ (res <> 0 /\ res mod 16 = 0 /\ (exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blkc = b1 ++ b2) /\ Wt) ->
0 <= res < 2 ^ 64.
Proof.
intros MR LAWS L2 A2 mem2 md2 blkc res n Wt HH Hn [[-> _] | (Hnz & _ & (b1 & b2 & HB & _) & _)]; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_blocks_range ubs2_msyms MR LAWS L2 A2 mem2 md2 res n HH ltac:(rewrite HB; apply in_app_iff; right; left; reflexivity) Hn) as (H0 & H1 & _). lia.
Qed.
Definition boxP (P : Prop) : Prop := P.
Ltac add_region HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_E2a : sstate :=
mkSS PC_A1 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 112 120 112 112 [] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Section j.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Lemma ubs2_rgbadd_E2a :
K_M2 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
K_XB API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
K_A1 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KM2 KXB regs1 Lc Ac memc mdc pnew fimg imgl HAT. unfold K_M2, cfg_at in KM2. unfold K_XB, cfg_at in KXB.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & G8 & G26 & G18 & G9 & G21 & G27 & S112 & S120 & Hfc & Hobj & Hcg & Himg & Hpnz & Hfnz & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HHt & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HCSv : CALLOC_STACK = 8224) by reflexivity.
assert (HCHT : CHT_SIZE = 48) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity. assert (HTS0 : TS0 = 524309) by reflexivity.
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE HHc Hrin ltac:(lia)) as (Rr0 & Rr1 & Rr16).
pose proof (obj_at_range _ _ _ _ _ Hcfp) as Rcfg. pose proof (Rcfg 1%nat fmt eq_refl) as Rfmt. cbn in Rfmt.
assert (HfN2 : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HNmax HNMv; nia).
assert (HBp : In (pnew, fmt * N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; right; left; reflexivity).
assert (HBf : In (fimg, N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; right; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ pnew (fmt * N) HHc HBp ltac:(lia)) as (Rp0 & Rp1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fimg N HHc HBf ltac:(lia)) as (Rf0 & Rf1 & _).
assert (Hib : img_block img fmt N = [(img, fmt * N)]) by (unfold img_block, fmt_okb; destruct Hfmt as [-> | ->]; reflexivity).
assert (HimgB : In (img, fmt * N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. unfold BASE. rewrite Hib. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
assert (CGK : forall m', (forall b n i, In (b, n) (blocks Lc Ac) -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) -> cgif_at m' g s).
{ intros m' Hk. eapply (cgif_at_kept _ _ g s N (blocks Lc Ac)); [| exact Hcg | exact Hk].
eapply Permutation_trans; [exact HB|]. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
assert (RGK : forall m', (forall b n i, In (b, n) (blocks Lc Ac) -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) ->
rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur m').
{ intros m' Hk. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply (Hk r RGB_SIZE i Hrin Hi). }
assert (Hfmt34 : 3 <= fmt <= 4) by lia.
change (fmt = 3 \/ fmt = 4) with (boxP (fmt = 3 \/ fmt = 4)) in Hfmt.
change (bef = 0 \/ beffmt = 3 \/ beffmt = 4) with (boxP (bef = 0 \/ beffmt = 3 \/ beffmt = 4)) in Hbef.
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof Hal0 as Hal16. unfold UI4v.sp0 in Hal16, Hclo, Hceil, H63, Hstw, HJ.
set (sp0 := spZ regs0) in *. assert (Hsp0 : sp0 = spZ regs0) by reflexivity.
assert (Hspv : sp regs0 = sp0 - 5168) by (unfold sp, UI4v.sp0, RGBA_FRAME; lia).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 5168) by (rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv; apply unsigned_lit_small; lia).
assert (Hsp16 : (sp0 - 5168) mod 16 = 0).
{ replace (sp0 - 5168) with (sp0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal16 | lia]. }
assert (HS : st_ok ubs2segs E ss_E2a (mkst regs1 (Z_to_bv 64 PC_A1) memc (seg_rom ubs2segs))).
{ unfold ss_E2a. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | constructor].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16. repeat split; lia. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_A1) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (KH1 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> ~ (sp0 - 5168 + 112 <= x < sp0 - 5168 + 112) -> mbyte ubs2segs (ms_mem ms) x = mbyte ubs2segs memc x).
{ intros x Hx Hlx Hnx. mb_frame_g HF; [reflexivity | rewrite HU2; lia]. }
assert (KB1 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem ms) (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1]. mb_frame_g HF; [reflexivity | rewrite HU2; lia]. }
clear HF HG.
jreg HS (10%bv:reg) as M10.
jreg HS (2%bv:reg) as M2. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in M2.
jreg HS (4%bv:reg) as M4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in M4.
jreg HS (1%bv:reg) as M1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := 48) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hinit | exact M10 | lia
| exact M2 | lia | exact Hsp16 | lia | lia | exact M4 | exact M1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear M10 M2 M4 M1.
cbv beta. intros c' (L1 & A1 & regs2 & mem1 & md1 & c & -> & HJ1 & Hinit1 & HP1 & Hr10 & Hres & Hkeep1 & Hhi1). clear HJ.
cbn [ms_regs ms_mem mkst] in HP1, Hr10, Hkeep1, Hhi1, HJ1.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep1, Hhi1.
pose proof (proj1 HJ1) as HH1.
assert (KH2 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> ~ (sp0 - 5168 + 112 <= x < sp0 - 5168 + 112) -> mbyte ubs2segs mem1 x = mbyte ubs2segs memc x).
{ intros x Hx Hlx Hnx. rewrite <- (KH1 x Hx Hlx Hnx). apply (proj1 (Hhi1 x Hx ltac:(lia))). }
assert (KB2 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem1 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB1 b m i Hbm Hi). apply (Hkeep1 b m i Hbm Hi). }
jafter_call_keep HS 32%nat regs2 mem1 HP1 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi1 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS KH1 KB1. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hcat); cbn [ms_regs mkst] in Hcat; rewrite Hr10 in Hcat; symmetry in Hcat.
destruct Hres as [[-> HBeq] | (Hcnz & Hc16 & (cb1 & cb2 & HBc & HBcc) & Wc)].
{
pin_reg' HS (10%bv:reg) 0 Hr10.
jrun_to LAWS ubs2tbl_ok HS HJ1 PC_XB.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG |- *.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KH3 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> ~ (sp0 - 5168 + 112 <= x < sp0 - 5168 + 112) -> mbyte ubs2segs (ms_mem msx) x = mbyte ubs2segs memc x)
by (intros x Hx Hlx Hnx; rewrite <- (KH2 x Hx Hlx Hnx); mb_frame_g HF; [reflexivity | rewrite HU2; lia]);
assert (KB3 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KB2 b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1]; mb_frame_g HF; [reflexivity | rewrite HU2; lia])
end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_XB) end.
lazymatch goal with |- SR _ (mkCfg (mkst _ _ ?memx _) _) _ => apply (KXB _ L1 A1 memx md1 pnew fimg) end.
split.
{ split; [exact HJ1|]. split; [exact Hinit1|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc _ (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x Hx Hlx; apply KH3; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros i Hi. apply KH3; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [exact Hfmt|].
split; [jreg HS (18%bv:reg) as Hq; rewrite Hq, (HE 18%nat 18%bv eq_refl); exact G18|].
split; [jreg HS (9%bv:reg) as Hq; rewrite Hq, (HE 9%nat 9%bv eq_refl); exact G9|].
split; [jreg HS (21%bv:reg) as Hq; rewrite Hq, (HE 21%nat 21%bv eq_refl); exact G21|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 8%nat 8%bv eq_refl); exact G8|].
split; [exact (RGK _ KB3)|]. split; [exact (CGK _ KB3)|].
split; [exact Hpnz|]. split; [exact Hfnz|]. rewrite HBeq. exact HB. }
assert (HBc1 : In (c, 48) (blocks L1 A1)) by (rewrite HBc; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ c 48 HH1 HBc1 ltac:(lia)) as (Rc0 & Rc1 & _).
assert (HB1 : Permutation (blocks L1 A1) ((BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]) ++ [(c, CHT_SIZE)])).
{ rewrite HBc. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. eapply Permutation_trans; [| apply Permutation_cons_append]. apply perm_skip. rewrite <- HBcc. exact HB. }
assert (Hsub1 : forall x0, In x0 (blocks Lc Ac) -> In x0 (blocks L1 A1)).
{ intros x0 Hx0. rewrite HBc. rewrite HBcc in Hx0. apply in_app_iff in Hx0. apply in_app_iff. destruct Hx0 as [Hx0|Hx0]; [left; exact Hx0 | right; right; exact Hx0]. }
assert (Hcdis : forall b m, In (b, m) (blocks Lc Ac) -> c + 48 <= b \/ b + m <= c).
{ intros b m Hbm. pose proof (heap_sep_perm _ _ LAWS L1 A1 mem1 md1 (c, 48) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]) (b, m) HH1
ltac:(eapply Permutation_trans; [exact HB1 | apply Permutation_sym, Permutation_cons_append]) ltac:(eapply Permutation_in; [exact HB | exact Hbm])) as X.
cbn [fst snd] in X. lia. }
add_fact' HS 36%nat (mkAF 4096 (CEIL_MAX - 48) 4); [| rewrite Hcat, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
assert (Wc' : wtok' RGBA_STK sp0 (FPfoot r g bef beffmt s N) (blocks L A) (c, 48)) by (intros blc i Hin Hi; apply (Wc blc i Hin Hi)).
jrun_to LAWS ubs2tbl_ok HS HJ1 ubs2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KH2m : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> ~ (sp0 - 5168 + 112 <= x < sp0 - 5168 + 112) -> mbyte ubs2segs (ms_mem msx) x = mbyte ubs2segs memc x)
by (intros x Hx Hlx Hnx; rewrite <- (KH2 x Hx Hlx Hnx); mb_frame_g HF; [reflexivity | rewrite HU2; lia]);
assert (KB2m : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KB2 b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1]; mb_frame_g HF; [reflexivity | rewrite HU2; lia])
end.
clear KH2 KB2 HF.
(jreg HS (10%bv:reg) as Mm10); (jreg HS (11%bv:reg) as Mm11); (jreg HS (12%bv:reg) as Mm12); (jreg HS (1%bv:reg) as Mm1).
cbn [ms_regs mkst] in Mm10, Mm11, Mm12, Mm1. rewrite Hcat in Mm10.
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset_spec E1 ss1 ms1 _ _ _ _ _ _ _ _ _ _ c 0 48);
[ exact HS | reflexivity | reflexivity | exact HJ1 | exact Mm10 | exact Mm11 | exact Mm12 | exact Mm1
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia
| intros i Hi; apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ c 48 i (proj1 HJ1) HBc1 Hi))
| intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ c 48); [exact Wc' | exact HBc1 | lia] ] end. }
clear Mm10 Mm11 Mm12 Mm1.
cbv beta. intros c' (regs2m & mem1m & -> & HJ1m & Hd10 & Hfr2 & Hout2 & Hgr2 & Zc). clear HJ1. rename HJ1m into HJ1.
cbn [ms_regs ms_mem mkst] in Hfr2, Hout2, Hgr2, Zc, HJ1.
pose proof (proj1 HJ1) as HH1m.
assert (KH2 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> ~ (sp0 - 5168 + 112 <= x < sp0 - 5168 + 112) -> mbyte ubs2segs mem1m x = mbyte ubs2segs memc x).
{ intros x Hx Hlx Hnx. rewrite <- (KH2m x Hx Hlx Hnx). unfold mbyte. rewrite (Hout2 (Z_to_bv 64 x)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
assert (KB2 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem1m (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB2m b m i Hbm Hi). pose proof (Hcdis b m Hbm) as Hbd.
destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1].
unfold mbyte. rewrite (Hout2 (Z_to_bv 64 (b + i))) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
clear KH2m KB2m.
jafter_stretch_keep HS 48%nat regs2m mem1m MEMSET_CLOB E2_MSET [0%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor].
eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS Hfr2 Hd10. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 36%nat) 0 48 0 48 [mkChunk 0 (CZero 48)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havoc. rewrite Hcat, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. cbn [ms_mem mkst]. apply (present_writable ubs2_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ c 48 o HH1m HBc1 Ho)). }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off ms_mem mkst]. intros i Hi.
rewrite Z.add_0_r. apply Zc. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
ew_havoc. rewrite Hcat. ew_havoc. rewrite HU2, unsigned_lit_small by lia. split; [lia | exact I]. }
Ltac wr2 Hcat HU2 Wc' HBin :=
wr_norm;
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 36); [reflexivity | ew_havoc; rewrite Hcat; apply unsigned_lit_small; lia | |];
[ cbn [r_wlo r_whi]; intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ _ 48); [exact Wc' | exact HBin | lia]
| eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]; apply wr_ok_nil ].
Ltac kstep KHp KBp HF Hcat HU2 Hcdis LAWS Lc Ac memc mdc HHc KHn KBn :=
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KHn : forall x, alloc_ceiling <= x < 2 ^ 64 -> _ <= x -> ~ (_ <= x < _) -> mbyte ubs2segs (ms_mem msx) x = mbyte ubs2segs memc x)
by (intros x Hx Hlx Hnx; rewrite <- (KHp x Hx Hlx Hnx); mb_frame_g HF; [reflexivity | rewrite Hcat, unsigned_lit_small by lia; lia | rewrite HU2; lia]);
assert (KBn : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KBp b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1];
pose proof (Hcdis b m Hbm) as Hbd; mb_frame_g HF; [reflexivity | rewrite Hcat, unsigned_lit_small by lia; lia | rewrite HU2; lia]);
clear KHp KBp HF
end.
jrun_to LAWS ubs2tbl_ok HS HJ1 ubs2_A_malloc. { wr2 Hcat HU2 Wc' HBc1. }
cbn [ms_mem mkst] in HF, HG. kstep KH2 KB2 HF Hcat HU2 Hcdis LAWS Lc Ac memc mdc HHc KH3 KB3. clear HG.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Kc3 : forall i, 0 <= i < 48 -> mbyte ubs2segs (ms_mem msx) (c + i) = mbyte ubs2segs (ms_mem msx) (c + i)) by (intros; reflexivity) end.
jreg HS (10%bv:reg) as Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := SZ_f) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ1 | exact Hinit1 | exact Ma0 | unfold SZ_f; lia
| exact Mq2 | lia | exact Hsp16 | lia | lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear Ma0 Mq2 Mq4 Mq1.
cbv beta. intros c' (L2 & A2 & regs3 & mem2 & md2 & f & -> & HJ2 & Hinit2 & HP2 & Hf10 & Hresf & Hkeep2 & Hhi2). clear HJ1.
cbn [ms_regs ms_mem mkst] in HP2, Hf10, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
destruct (malloc_post_perm _ _ _ f SZ_f _ HB1 Hresf) as [HB2 Hsub2].
pose proof (malloc_res_range MR LAWS L2 A2 mem2 md2 _ f SZ_f _ HH2 ltac:(unfold SZ_f; lia) Hresf) as Rf. clear Hresf.
assert (HBc2 : In (c, 48) (blocks L2 A2)) by (apply Hsub2; exact HBc1).
assert (KH4 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> ~ (sp0 - 5168 + 112 <= x < sp0 - 5168 + 112) -> mbyte ubs2segs mem2 x = mbyte ubs2segs memc x).
{ intros x Hx Hlx Hnx. rewrite <- (KH3 x Hx Hlx Hnx). apply (proj1 (Hhi2 x Hx ltac:(lia))). }
assert (KB4 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB3 b m i Hbm Hi). apply (Hkeep2 b m i (Hsub1 _ Hbm) Hi). }
jafter_call_keep HS 54%nat regs3 mem2 HP2 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_live_blk MR LAWS _ _ _ 36); [ew_havoc; rewrite Hcat; apply unsigned_lit_small; lia | exact HH2 | exact HBc2 | intros i Hi; apply (Hkeep2 c 48 i HBc1 Hi) | lia | lia | lia | lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS KH3 KB3. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hfat); cbn [ms_regs mkst] in Hfat; rewrite Hf10 in Hfat; symmetry in Hfat. clear Hf10.
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_malloc. { wr2 Hcat HU2 Wc' HBc2. }
cbn [ms_mem mkst] in HF, HG. kstep KH4 KB4 HF Hcat HU2 Hcdis LAWS Lc Ac memc mdc HHc KH5 KB5. clear HG.
jreg HS (10%bv:reg) as Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := SZ_h) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hinit2 | exact Ma0 | unfold SZ_h; lia
| exact Mq2 | lia | exact Hsp16 | lia | lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear Ma0 Mq2 Mq4 Mq1.
cbv beta. intros c' (L3 & A3 & regs4 & mem3 & md3 & h & -> & HJ3 & Hinit3 & HP3 & Hh10 & Hresh & Hkeep3 & Hhi3). clear HJ2.
cbn [ms_regs ms_mem mkst] in HP3, Hh10, Hkeep3, Hhi3, HJ3.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep3, Hhi3.
pose proof (proj1 HJ3) as HH3.
destruct (malloc_post_perm _ _ _ h SZ_h _ HB2 Hresh) as [HB3 Hsub3].
pose proof (malloc_res_range MR LAWS L3 A3 mem3 md3 _ h SZ_h _ HH3 ltac:(unfold SZ_h; lia) Hresh) as Rh. clear Hresh.
assert (HBc3 : In (c, 48) (blocks L3 A3)) by (apply Hsub3; exact HBc2).
assert (KH6 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> ~ (sp0 - 5168 + 112 <= x < sp0 - 5168 + 112) -> mbyte ubs2segs mem3 x = mbyte ubs2segs memc x).
{ intros x Hx Hlx Hnx. rewrite <- (KH5 x Hx Hlx Hnx). apply (proj1 (Hhi3 x Hx ltac:(lia))). }
assert (KB6 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem3 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB5 b m i Hbm Hi). apply (Hkeep3 b m i (Hsub2 _ (Hsub1 _ Hbm)) Hi). }
jafter_call_keep HS 70%nat regs4 mem3 HP3 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_live_blk MR LAWS _ _ _ 36); [ew_havoc; rewrite Hcat; apply unsigned_lit_small; lia | exact HH3 | exact HBc3 | intros i Hi; apply (Hkeep3 c 48 i HBc2 Hi) | lia | lia | lia | lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS KH5 KB5. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hhat); cbn [ms_regs mkst] in Hhat; rewrite Hh10 in Hhat; symmetry in Hhat. clear Hh10.
jrun_to LAWS ubs2tbl_ok HS HJ3 ubs2_A_malloc. { wr2 Hcat HU2 Wc' HBc3. }
cbn [ms_mem mkst] in HF, HG. kstep KH6 KB6 HF Hcat HU2 Hcdis LAWS Lc Ac memc mdc HHc KH7 KB7. clear HG.
jreg HS (10%bv:reg) as Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := SZ_u) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Hinit3 | exact Ma0 | unfold SZ_u; lia
| exact Mq2 | lia | exact Hsp16 | lia | lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear Ma0 Mq2 Mq4 Mq1.
cbv beta. intros c' (L4 & A4 & regs5 & mem4 & md4 & u & -> & HJ4 & Hinit4 & HP4 & Hu10 & Hresu & Hkeep4 & Hhi4). clear HJ3.
cbn [ms_regs ms_mem mkst] in HP4, Hu10, Hkeep4, Hhi4, HJ4.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep4, Hhi4.
pose proof (proj1 HJ4) as HH4.
destruct (malloc_post_perm _ _ _ u SZ_u _ HB3 Hresu) as [HB4 Hsub4].
pose proof (malloc_res_range MR LAWS L4 A4 mem4 md4 _ u SZ_u _ HH4 ltac:(unfold SZ_u; lia) Hresu) as Ru. clear Hresu.
assert (HBc4 : In (c, 48) (blocks L4 A4)) by (apply Hsub4; exact HBc3).
assert (KH8 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> ~ (sp0 - 5168 + 112 <= x < sp0 - 5168 + 112) -> mbyte ubs2segs mem4 x = mbyte ubs2segs memc x).
{ intros x Hx Hlx Hnx. rewrite <- (KH7 x Hx Hlx Hnx). apply (proj1 (Hhi4 x Hx ltac:(lia))). }
assert (KB8 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem4 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB7 b m i Hbm Hi). apply (Hkeep4 b m i (Hsub3 _ (Hsub2 _ (Hsub1 _ Hbm))) Hi). }
jafter_call_keep HS 86%nat regs5 mem4 HP4 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_live_blk MR LAWS _ _ _ 36); [ew_havoc; rewrite Hcat; apply unsigned_lit_small; lia | exact HH4 | exact HBc4 | intros i Hi; apply (Hkeep4 c 48 i HBc3 Hi) | lia | lia | lia | lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS KH7 KB7. rename HS2 into HS.
(jreg HS (10%bv:reg) as Huat); cbn [ms_regs mkst] in Huat; rewrite Hu10 in Huat; symmetry in Huat. clear Hu10.
jrun_to LAWS ubs2tbl_ok HS HJ4 ubs2_A_malloc. { wr2 Hcat HU2 Wc' HBc4. }
cbn [ms_mem mkst] in HF, HG. kstep KH8 KB8 HF Hcat HU2 Hcdis LAWS Lc Ac memc mdc HHc KH9 KB9. clear HG.
jreg HS (10%bv:reg) as Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := SZ_h) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ4 | exact Hinit4 | exact Ma0 | unfold SZ_h; lia
| exact Mq2 | lia | exact Hsp16 | lia | lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear Ma0 Mq2 Mq4 Mq1.
cbv beta. intros c' (L5 & A5 & regs6 & mem5 & md5 & p & -> & HJ5 & Hinit5 & HP5 & Hp10 & Hresp & Hkeep5 & Hhi5). clear HJ4.
cbn [ms_regs ms_mem mkst] in HP5, Hp10, Hkeep5, Hhi5, HJ5.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep5, Hhi5.
pose proof (proj1 HJ5) as HH5.
destruct (malloc_post_perm _ _ _ p SZ_h _ HB4 Hresp) as [HB5 Hsub5].
pose proof (malloc_res_range MR LAWS L5 A5 mem5 md5 _ p SZ_h _ HH5 ltac:(unfold SZ_h; lia) Hresp) as Rp. clear Hresp.
assert (HBc5 : In (c, 48) (blocks L5 A5)) by (apply Hsub5; exact HBc4).
assert (KH10 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> ~ (sp0 - 5168 + 112 <= x < sp0 - 5168 + 112) -> mbyte ubs2segs mem5 x = mbyte ubs2segs memc x).
{ intros x Hx Hlx Hnx. rewrite <- (KH9 x Hx Hlx Hnx). apply (proj1 (Hhi5 x Hx ltac:(lia))). }
assert (KB10 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem5 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB9 b m i Hbm Hi). apply (Hkeep5 b m i (Hsub4 _ (Hsub3 _ (Hsub2 _ (Hsub1 _ Hbm)))) Hi). }
jafter_call_keep HS 102%nat regs6 mem5 HP5 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_live_blk MR LAWS _ _ _ 36); [ew_havoc; rewrite Hcat; apply unsigned_lit_small; lia | exact HH5 | exact HBc5 | intros i Hi; apply (Hkeep5 c 48 i HBc4 Hi) | lia | lia | lia | lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi5 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS KH9 KB9. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hpat); cbn [ms_regs mkst] in Hpat; rewrite Hp10 in Hpat; symmetry in Hpat. clear Hp10.
jrun_to LAWS ubs2tbl_ok HS HJ5 ubs2_A_malloc. { wr2 Hcat HU2 Wc' HBc5. }
cbn [ms_mem mkst] in HF, HG. kstep KH10 KB10 HF Hcat HU2 Hcdis LAWS Lc Ac memc mdc HHc KH11 KB11. clear HG.
jreg HS (10%bv:reg) as Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := SZ_f) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ5 | exact Hinit5 | exact Ma0 | unfold SZ_f; lia
| exact Mq2 | lia | exact Hsp16 | lia | lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear Ma0 Mq2 Mq4 Mq1.
cbv beta. intros c' (L6 & A6 & regs7 & mem6 & md6 & x & -> & HJ6 & Hinit6 & HP6 & Hx10 & Hresx & Hkeep6 & Hhi6). clear HJ5.
cbn [ms_regs ms_mem mkst] in HP6, Hx10, Hkeep6, Hhi6, HJ6.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep6, Hhi6.
pose proof (proj1 HJ6) as HH6.
destruct (malloc_post_perm _ _ _ x SZ_f _ HB5 Hresx) as [HB6 Hsub6].
pose proof (malloc_res_range MR LAWS L6 A6 mem6 md6 _ x SZ_f _ HH6 ltac:(unfold SZ_f; lia) Hresx) as Rx. clear Hresx.
assert (HBc6 : In (c, 48) (blocks L6 A6)) by (apply Hsub6; exact HBc5).
assert (KH12 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 <= x0 -> ~ (sp0 - 5168 + 112 <= x0 < sp0 - 5168 + 112) -> mbyte ubs2segs mem6 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hlx Hnx. rewrite <- (KH11 x0 Hx Hlx Hnx). apply (proj1 (Hhi6 x0 Hx ltac:(lia))). }
assert (KB12 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem6 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB11 b m i Hbm Hi). apply (Hkeep6 b m i (Hsub5 _ (Hsub4 _ (Hsub3 _ (Hsub2 _ (Hsub1 _ Hbm))))) Hi). }
jafter_call_keep HS 118%nat regs7 mem6 HP6 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_live_blk MR LAWS _ _ _ 36); [ew_havoc; rewrite Hcat; apply unsigned_lit_small; lia | exact HH6 | exact HBc6 | intros i Hi; apply (Hkeep6 c 48 i HBc5 Hi) | lia | lia | lia | lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS KH11 KB11. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hxat); cbn [ms_regs mkst] in Hxat; rewrite Hx10 in Hxat; symmetry in Hxat. clear Hx10.
lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_M2) end.
apply (KM2 regs7 L6 A6 mem6 md6 pnew fimg imgl c f h u p x).
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
assert (HU2f : bv_unsigned (ew Ef 2) = sp0 - 5168) by (ew_havoc; exact HU2);
assert (HUcf : bv_unsigned (ew Ef 36) = c) by (ew_havoc; rewrite Hcat; apply unsigned_lit_small; lia);
pose proof (fun off n e v Hin => st_chunk_val ubs2segs Ef ssf msf 0%nat _ 36%nat off n e c v HS eq_refl eq_refl Hin HUcf) as VF;
pose proof (fun off len o n Hin => st_chunk_zero_val ubs2segs Ef ssf msf 0%nat _ 36%nat off len c o n HS eq_refl eq_refl Hin HUcf) as ZF;
pose proof (fun off n e v Hin => st_chunk_val ubs2segs Ef ssf msf 1%nat _ 2%nat off n e (sp0 - 5168) v HS eq_refl eq_refl Hin HU2f) as WF
end.
cbn [ms_mem mkst] in VF, ZF, WF.
split.
{ split; [exact HJ6|]. split; [exact Hinit6|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc _ (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x0 Hx Hlx; apply KH12; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros i Hi. apply KH12; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [exact Hfmt|]. split; [exact HN1|].
split; [jreg HS (8%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 8%nat 8%bv eq_refl); exact G8|].
split; [jreg HS (26%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 26%nat 26%bv eq_refl); exact G26|].
split; [jreg HS (18%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 18%nat 18%bv eq_refl); exact G18|].
split; [jreg HS (9%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 9%nat 9%bv eq_refl); exact G9|].
split; [jreg HS (21%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 21%nat 21%bv eq_refl); exact G21|].
split; [jreg HS (27%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 27%nat 27%bv eq_refl); exact G27|].
split; [eapply slot_kept_at; [exact S112 | intros x0 Hx0; rewrite Hspv in Hx0; apply KH12; lia]|].
split; [eapply slot_kept_at; [exact S120 | intros x0 Hx0; rewrite Hspv in Hx0; apply KH12; lia]|].
split; [jreg HS (20%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact Hcat|].
split; [jreg HS (10%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact Hxat|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 32); [exact Hfc | reflexivity |]. intros i Hi. apply KH12; unfold OFF_fcfg; lia. }
split; [exact (RGK _ KB12)|]. split; [exact (CGK _ KB12)|].
split. { split; [|exact (proj2 Himg)]. eapply arr8_frame; [exact (proj1 Himg)|]. intros a Ha. replace a with (img + (a - img)) by lia.
apply (KB12 img (fmt * N)); [exact HimgB | rewrite (proj2 Himg) in Ha; lia]. }
split; [exact Hpnz|]. split; [exact Hfnz|]. split; [exact Hcnz|]. split; [exact Hc16|].
split; [exact Rf|]. split; [exact Rh|]. split; [exact Ru|]. split; [exact Rp|]. split; [exact Rx|].
split. { cbn [obj_at LAY_Cht]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [apply (VF 0 8%N (SOff 58 0) f); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact Hfat | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 8 8%N (SOff 74 0) h); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact Hhat | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 16 8%N (SOff 90 0) u); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact Huat | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 24 8%N (SOff 106 0) p); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact Hpat | lia | cbn; lia] | lia]|].
split; [split; [apply (ZF 32 12 32 8%nat); [cbv; tauto | lia | cbn; lia] | lia]|].
split; [split; [apply (ZF 32 12 40 4%nat); [cbv; tauto | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 44 4%N (SLit 524309) TS0); [cbv; tauto | reflexivity | rewrite HTS0; lia | cbn; lia] | rewrite HTS0; lia]|].
exact I. }
eapply Permutation_trans; [exact HB6|].
change SZ_f with (4 * TS0). change SZ_h with (3 * TS0). change SZ_u with TS0. rewrite HCHT.
rewrite <- !app_assoc. cbn [app]. apply Permutation_refl.
Qed.
End j.
End d.

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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI04 YI05 YI0h
UI1e UI39 UI1i UI57 YI0x
YI07 YP14 YI08 YI0c YI0g UI3h UI3d UI4v UIZm UI4l.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition Q0_MAL : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xa6c).
Lemma U_add_small_q : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Hx Hy Rx Ry Rs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. lia. Qed.

Lemma U_sll_small_q : forall E a x k, U E a = x -> 0 <= x -> 0 <= k < 64 -> x * 2 ^ k < 2 ^ 64 ->
U E (SAlu ALU_SLL a (SLit k)) = x * 2 ^ k.
Proof.
intros E a x k Hx Rx Hk Rs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, U_lit by lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma land2_small : forall x, 0 <= x -> 0 <= Z.land x 2 < 4.
Proof.
intros x Hx. assert (H0 : 0 <= Z.land x 2) by (apply Z.land_nonneg; right; lia).
split; [exact H0|]. destruct (Z.eq_dec (Z.land x 2) 0) as [->|Hnz]; [lia|].
apply (Z.log2_lt_pow2 (Z.land x 2) 2); [lia|]. pose proof (Z.log2_land x 2 Hx ltac:(lia)) as Hl.
change (Z.log2 2) with 1 in Hl. lia.
Qed.
Lemma U_seqz_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_SLTU (SOff n 0) (SLit 1)) = nha v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn Hv), U_lit by lia.
unfold nha. destruct (Z.eqb_spec v 0) as [->|Hnz]; [reflexivity|].
destruct (Z.ltb_spec v 1); [lia | reflexivity].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_Q0a : sstate :=
mkSS PC_HD sr_atoms
[ YQ0b.mkRegion (Some 20%nat) 0 48 0 0 (obj_chunks_from LAY_Cht 51) ;
YQ0b.mkRegion (Some 2%nat) 0 128 0 128
[mkChunk 8 (CVal 8 (SOff 60 0)); mkChunk 16 (CVal 8 (SOff 45 0)); mkChunk 24 (CVal 8 (SOff 59 0)); mkChunk 48 (CVal 8 (SOff 58 0))] ;
YQ0b.mkRegion (Some 8%nat) 0 RGB_SIZE 0 0 (obj_chunks_from LAY_Rgb 32) ;
YQ0b.mkRegion (Some 45%nat) 0 RGBFC_SIZE 0 0 (obj_chunks_from LAY_RgbFrameConfig 46) ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (20%nat, mkAF 4096 (CEIL_MAX - 48) 4);
(8%nat, mkAF 4096 (CEIL_MAX - RGB_SIZE) 4); (45%nat, mkAF CEIL_MIN (2^63 - RGBFC_SIZE) 3);
(60%nat, mkAF 1 RGB_NMAX 0); (39%nat, mkAF 0 65535 0); (47%nat, mkAF 3 4 0); (48%nat, mkAF 0 (2^32 - 1) 0);
(56%nat, mkAF 0 (2^24) 0); (19%nat, mkAF 0 1 0) ] [] []).
Section l.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Lemma ubs2_rgbadd_Q0a :
K_LH API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest 0 ->
K_SM API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
K_XC API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
K_HD API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KLH KSM KXC regs1 Lc Ac memc mdc ha pnew fimg imgl C HAT. unfold K_LH, cfg_at in KLH. unfold K_SM, cfg_at in KSM. unfold K_XC, cfg_atF in KXC.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & G19 & G20 & G8 & G21 & HMEM).
destruct HMEM as (Hslm & _ & _ & _ & _ & _ & _ & _ & Hfc & Hobj & Hcg & Himg & Hcht & EhS & EuS & ETS & Hsum & Hpnz & Hfnz & HB).
destruct Hslm as (S8 & S16 & S24 & S48).
destruct Hcht as (Hst & Harr & Hinv & HTT & Hts & RhS & RuS & RTS).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HHt & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HCHT : CHT_SIZE = 48) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity. assert (HRFCv : RGBFC_SIZE = 24) by reflexivity.
assert (HMTS : MAX_TABLE_SIZE = 16777216) by reflexivity.
destruct C as [c f h u p x T hS uS TS HT ent]. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent] in *.
subst hS uS TS.
pose proof (ts_chain_ok T Hts) as (HT1 & HT4 & HT2).
pose proof Hinv as ((LenU & LenK & LenF & LenX & LenP) & (Hcnt & Helen & _) & (_ & KeysB & PalB) & _). rewrite HTT in *.
set (cnt := ht_cnt HT) in *.
set (KEEP := (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]) ++ (c, CHT_SIZE) :: cht_blocks f h u p x T) in *.
assert (HBK : Permutation (blocks Lc Ac) KEEP).
{ eapply Permutation_trans; [exact HB|]. unfold cht_blks. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T]. subst KEEP. rewrite <- app_assoc. apply Permutation_refl. }
assert (Hkeep_in : forall b m, In (b, m) KEEP -> In (b, m) (blocks Lc Ac)).
{ intros b m Hbm. eapply Permutation_in; [apply Permutation_sym; exact HBK | exact Hbm]. }
assert (Hck : In (c, CHT_SIZE) KEEP) by (subst KEEP; apply in_app_iff; right; left; reflexivity).
assert (HBc : In (c, 48) (blocks Lc Ac)) by (rewrite <- HCHT; exact (Hkeep_in _ _ Hck)).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ c 48 HHc HBc ltac:(lia)) as (Rc0 & Rc1 & Rc16).
assert (Hcr : c + 48 <= r \/ r + RGB_SIZE <= c).
{ assert (Hp : Permutation (blocks Lc Ac) ((c, CHT_SIZE) :: (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]) ++ cht_blocks f h u p x T)).
{ eapply Permutation_trans; [exact HBK|]. subst KEEP. apply Permutation_sym. apply Permutation_middle. }
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (c, CHT_SIZE) _ (r, RGB_SIZE) HHc Hp ltac:(apply in_app_iff; left; apply in_app_iff; left; left; reflexivity)) as X.
cbn [fst snd] in X. rewrite HCHT in X. lia. }
assert (Hrk : In (r, RGB_SIZE) KEEP) by (subst KEEP; apply in_app_iff; left; apply in_app_iff; left; left; reflexivity).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE HHc (Hkeep_in _ _ Hrk) ltac:(lia)) as (Rr0 & Rr1 & Rr16).
pose proof (obj_at_range _ _ _ _ _ Hcfp) as Rcfg. pose proof (Rcfg 0%nat img eq_refl) as Rimg. pose proof (Rcfg 1%nat fmt eq_refl) as Rfmt.
pose proof (Rcfg 2%nat fattr eq_refl) as Rfattr. pose proof (Rcfg 4%nat delay eq_refl) as Rdelay. cbn in Rimg, Rfmt, Rfattr, Rdelay.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rrgb. pose proof (Rrgb 7%nat W eq_refl) as RW. pose proof (Rrgb 9%nat bef eq_refl) as Rbef.
pose proof (Rrgb 10%nat beffmt eq_refl) as Rbf. cbn in RW, Rbef, Rbf.
pose proof (obj_at_range _ _ _ _ _ Hst) as Rstr. pose proof (Rstr 0%nat f eq_refl) as Rf. pose proof (Rstr 3%nat p eq_refl) as Rp. pose proof (Rstr 4%nat x eq_refl) as Rx. cbn in Rf, Rp, Rx.
assert (HfN2 : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HNmax HNMv; nia).
assert (HBpn : In (pnew, fmt * N) KEEP) by (subst KEEP; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ pnew (fmt * N) HHc (Hkeep_in _ _ HBpn) ltac:(lia)) as (Rpn0 & Rpn1 & _).
assert (HBfi : In (fimg, N) KEEP) by (subst KEEP; apply in_app_iff; left; apply in_app_iff; right; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fimg N HHc (Hkeep_in _ _ HBfi) ltac:(lia)) as (Rfi0 & Rfi1 & _).
assert (ARR : forall b m, In (b, m) (cht_blocks f h u p x T) -> In (b, m) KEEP) by (intros b m Hbm; subst KEEP; apply in_app_iff; right; right; exact Hbm).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ f (4 * T) HHc (Hkeep_in _ _ (ARR f (4 * T) ltac:(cbv [cht_blocks In]; tauto))) ltac:(lia)) as (Rf0 & Rf1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ h (3 * T) HHc (Hkeep_in _ _ (ARR h (3 * T) ltac:(cbv [cht_blocks In]; tauto))) ltac:(lia)) as (Rh0 & Rh1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ u T HHc (Hkeep_in _ _ (ARR u T ltac:(cbv [cht_blocks In]; tauto))) ltac:(lia)) as (Ru0 & Ru1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ p (3 * T) HHc (Hkeep_in _ _ (ARR p (3 * T) ltac:(cbv [cht_blocks In]; tauto))) ltac:(lia)) as (Rp0 & Rp1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ x (4 * T) HHc (Hkeep_in _ _ (ARR x (4 * T) ltac:(cbv [cht_blocks In]; tauto))) ltac:(lia)) as (Rx0 & Rx1 & _).
assert (Hib : img_block img fmt N = [(img, fmt * N)]) by (unfold img_block, fmt_okb; destruct Hfmt as [-> | ->]; reflexivity).
assert (HimgK : In (img, fmt * N) KEEP).
{ subst KEEP. apply in_app_iff. left. apply in_app_iff. left. unfold BASE. rewrite Hib. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
assert (CGK : forall m', (forall b n i, In (b, n) KEEP -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) -> cgif_at m' g s).
{ intros m' Hk. eapply (cgif_at_kept _ _ g s N KEEP); [| exact Hcg | exact Hk].
subst KEEP. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
assert (RGK : forall m', (forall b n i, In (b, n) KEEP -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) ->
rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur m').
{ intros m' Hk. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply (Hk r RGB_SIZE i Hrk Hi). }
assert (IMK : forall m', (forall b n i, In (b, n) KEEP -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) -> img_at N img fmt m' imgl).
{ intros m' Hk. split; [|exact (proj2 Himg)]. eapply arr8_frame; [exact (proj1 Himg)|]. intros a Ha. replace a with (img + (a - img)) by lia.
apply (Hk img (fmt * N)); [exact HimgK | rewrite (proj2 Himg) in Ha; lia]. }
assert (ARK : forall m', (forall b n i, In (b, n) KEEP -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) ->
cht_arrays ubs2segs m' f h u p x HT).
{ intros m' Hk. destruct Harr as (A1 & A2 & A3 & A4 & A5).
split; [eapply arr32_frame; [exact A1 | intros a Ha; replace a with (f + (a - f)) by lia; apply (Hk f (4 * T) (a - f) (ARR f (4 * T) ltac:(cbv [cht_blocks In]; tauto))); rewrite LenF in Ha; lia]|].
split; [eapply arr8_frame; [exact A2 | intros a Ha; replace a with (h + (a - h)) by lia; apply (Hk h (3 * T) (a - h) (ARR h (3 * T) ltac:(cbv [cht_blocks In]; tauto))); rewrite LenK in Ha; lia]|].
split; [eapply arr8_frame; [exact A3 | intros a Ha; replace a with (u + (a - u)) by lia; apply (Hk u T (a - u) (ARR u T ltac:(cbv [cht_blocks In]; tauto))); rewrite LenU in Ha; lia]|].
split; [eapply arr8_frame; [exact A4 | intros a Ha; replace a with (p + (a - p)) by lia; apply (Hk p (3 * T) (a - p) (ARR p (3 * T) ltac:(cbv [cht_blocks In]; tauto))); rewrite LenP in Ha; lia]|].
eapply arr32_frame; [exact A5 | intros a Ha; replace a with (x + (a - x)) by lia; apply (Hk x (4 * T) (a - x) (ARR x (4 * T) ltac:(cbv [cht_blocks In]; tauto))); rewrite LenX in Ha; lia]. }
assert (Hfmt34 : 3 <= fmt <= 4) by lia.
change (fmt = 3 \/ fmt = 4) with (boxP (fmt = 3 \/ fmt = 4)) in Hfmt.
change (bef = 0 \/ beffmt = 3 \/ beffmt = 4) with (boxP (bef = 0 \/ beffmt = 3 \/ beffmt = 4)) in Hbef.
assert (Hha01 : 0 <= ha <= 1) by lia. change (ha = 0 \/ ha = 1 /\ fmt = 4) with (boxP (ha = 0 \/ ha = 1 /\ fmt = 4)) in Hha.
set (rgbv := [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cur]) in *.
set (cfgv := [img; fmt; fattr; fgen; delay]) in *.
set (chtv := [f; h; u; p; x; cnt; T]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (rgbv ++ [r; cfp] ++ cfgv ++ chtv ++ [fimg; pnew; N]) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (rgbv ++ [r; cfp] ++ cfgv ++ chtv ++ [fimg; pnew; N]) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HVr : forall j v, nth_error rgbv j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. apply HV. rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]. }
assert (HVg : forall j v, nth_error cfgv j = Some v -> ew E (46 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (46 + j)%nat with (32 + (14 + j))%nat by lia. apply HV.
assert (Hj5 : (j < length cfgv)%nat) by (apply nth_error_Some; congruence).
subst rgbv cfgv. rewrite nth_error_app2 by (cbn; lia). rewrite nth_error_app2 by (cbn; lia). cbn [length Nat.sub Nat.add].
rewrite nth_error_app1 by (cbn in Hj5 |- *; lia). replace (j - 0)%nat with j by lia. exact Hj. }
assert (HVc : forall j v, nth_error chtv j = Some v -> ew E (51 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (51 + j)%nat with (32 + (19 + j))%nat by lia. apply HV.
assert (Hj7 : (j < length chtv)%nat) by (apply nth_error_Some; congruence).
subst rgbv cfgv chtv. rewrite nth_error_app2 by (cbn; lia). rewrite nth_error_app2 by (cbn; lia). rewrite nth_error_app2 by (cbn; lia). cbn [length Nat.sub Nat.add].
rewrite nth_error_app1 by (cbn in Hj7 |- *; lia). replace (j - 0)%nat with j by lia. exact Hj. }
assert (HE39 : ew E 39 = Z_to_bv 64 W) by (apply (HV 7%nat); reflexivity).
assert (HE41 : ew E 41 = Z_to_bv 64 bef) by (apply (HV 9%nat); reflexivity).
assert (HE42 : ew E 42 = Z_to_bv 64 beffmt) by (apply (HV 10%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 r) by (apply (HV 12%nat); reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 cfp) by (apply (HV 13%nat); reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 img) by (apply (HV 14%nat); reflexivity).
assert (HE47 : ew E 47 = Z_to_bv 64 fmt) by (apply (HV 15%nat); reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 fattr) by (apply (HV 16%nat); reflexivity).
assert (HE51 : ew E 51 = Z_to_bv 64 f) by (apply (HV 19%nat); reflexivity).
assert (HE54 : ew E 54 = Z_to_bv 64 p) by (apply (HV 22%nat); reflexivity).
assert (HE55 : ew E 55 = Z_to_bv 64 x) by (apply (HV 23%nat); reflexivity).
assert (HE56 : ew E 56 = Z_to_bv 64 cnt) by (apply (HV 24%nat); reflexivity).
assert (HE58 : ew E 58 = Z_to_bv 64 fimg) by (apply (HV 26%nat); reflexivity).
assert (HE59 : ew E 59 = Z_to_bv 64 pnew) by (apply (HV 27%nat); reflexivity).
assert (HE52 : ew E 52 = Z_to_bv 64 h) by (apply (HV 20%nat); reflexivity).
assert (HE53 : ew E 53 = Z_to_bv 64 u) by (apply (HV 21%nat); reflexivity).
assert (HE57 : ew E 57 = Z_to_bv 64 T) by (apply (HV 25%nat); reflexivity).
assert (HE60 : ew E 60 = Z_to_bv 64 N) by (apply (HV 28%nat); reflexivity).
assert (HE8 : ew E 8 = Z_to_bv 64 r) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE19 : ew E 19 = Z_to_bv 64 ha) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE20 : ew E 20 = Z_to_bv 64 c) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HE21 : ew E 21 = Z_to_bv 64 2) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
pose proof Hal0 as Hal16. unfold UI4v.sp0 in Hal16, Hclo, Hceil, H63, Hstw, HJ.
set (sp0 := spZ regs0) in *. assert (Hsp0 : sp0 = spZ regs0) by reflexivity.
assert (Hspv : sp regs0 = sp0 - 5168) by (unfold sp, UI4v.sp0, RGBA_FRAME; lia).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 5168) by (rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = r) by (rewrite HE8; apply unsigned_lit_small; lia).
assert (HU45 : bv_unsigned (ew E 45) = cfp) by (rewrite HE45; apply unsigned_lit_small; lia).
assert (Hsp16 : (sp0 - 5168) mod 16 = 0).
{ replace (sp0 - 5168) with (sp0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal16 | lia]. }
assert (Hha2 : 0 <= ha <= 1) by lia.
assert (SLOTC : forall off v n, slot regs0 memc off v -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> chunk_ok ubs2segs E memc (sp0 - 5168) (mkChunk off (CVal 8 (SOff n 0)))).
{ intros off v n Hs Hn Hv. apply chunk_ok_val with (v := v); [cbn [sv_denot]; rewrite Z.add_0_r, Hn; apply Z_to_bv_bv_unsigned | lia | cbn; lia |].
apply (proj2 (val_mem_word_mem ubs2segs _ _ _)). rewrite <- Hspv. exact Hs. }
assert (HS : st_ok ubs2segs E ss_Q0a (mkst regs1 (Z_to_bv 64 PC_HD) memc (seg_rom ubs2segs))).
{ unfold ss_Q0a. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ eapply (region_ok_obj ubs2segs _ memc 20 c); [exact HU20 | lia | lia | exact Hst | reflexivity | | intros i Hi; lia].
exact HVc.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
apply Forall_cons; [apply (SLOTC _ N); [exact S8 | exact HE60 | lia]|].
apply Forall_cons; [apply (SLOTC _ cfp); [exact S16 | exact HE45 | lia]|].
apply Forall_cons; [apply (SLOTC _ pnew); [exact S24 | exact HE59 | lia]|].
apply Forall_cons; [apply (SLOTC _ fimg); [exact S48 | exact HE58 | lia]|].
apply Forall_nil.
+ eapply (region_ok_obj ubs2segs _ memc 8 r); [exact HU8 | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
exact HVr.
+ eapply (region_ok_obj ubs2segs _ memc 45 cfp); [exact HU45 | lia | lia | exact Hcfp | reflexivity | | intros i Hi; lia].
exact HVg.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU20, HU8, HU45.
repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU20, HU8, HU45, HE60, HE39, HE47, HE48, HE56, HE19, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_HD) memc (seg_rom ubs2segs))) in HJ.
Ltac wrq HU2 :=
apply wr_ok_cons_ro; [cbn; lia|];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
Ltac kstepq KHp KBp HF HU20 HU2 HU8 HU45 Hkeep_in LAWS Lc Ac memc mdc HHc KHn KBn :=
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KHn : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> _ <= x0 -> mbyte ubs2segs (ms_mem msx) x0 = mbyte ubs2segs memc x0)
by (intros x0 Hx Hlx; rewrite <- (KHp x0 Hx Hlx); mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia | rewrite HU8; lia | rewrite HU45; lia]);
assert (KBn : forall b m i, In (b, m) _ -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KBp b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ Hbm)) as [Hb0 Hb1];
mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia | rewrite HU8; lia | rewrite HU45; lia]);
clear KHp KBp
end.
jrun LAWS ubs2tbl_ok HS HJ. { wrq HU2. }
cbn [ms_mem mkst] in HF, HG.
assert (KH1 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 + 128 <= x0 -> mbyte ubs2segs (ms_mem ms) x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hlx. mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia | rewrite HU8; lia | rewrite HU45; lia]. }
assert (KB1 : forall b m i, In (b, m) KEEP -> 0 <= i < m -> mbyte ubs2segs (ms_mem ms) (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ Hbm)) as [Hb0 Hb1].
mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia | rewrite HU8; lia | rewrite HU45; lia]. }
clear HF HG.
assert (STK : forall m', (forall b n i, In (b, n) KEEP -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) ->
obj_at ubs2segs m' c LAY_Cht [f; h; u; p; x; cnt; T]).
{ intros m' Hk. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 48); [exact Hst | reflexivity |]. intros i Hi. apply (Hk c CHT_SIZE i Hck). rewrite HCHT. exact Hi. }
assert (SLOT : forall Ef ssf (msf : machine_state) rg off e v,
st_ok ubs2segs Ef ssf msf -> nth_error (ss_mem ssf) 1 = Some rg -> r_base rg = Some 2%nat -> bv_unsigned (ew Ef 2) = sp0 - 5168 ->
In (mkChunk off (CVal 8 e)) (r_chunks rg) -> sv_denot Ef e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> slot regs0 (ms_mem msf) off v).
{ intros Ef ssf msf rg off e v HSf Hrg Hb HU Hin He Hv. unfold slot. apply (proj1 (val_mem_word_mem ubs2segs _ _ _)). rewrite Hspv.
apply (st_chunk_val ubs2segs Ef ssf msf 1%nat rg 2%nat off 8%N e (sp0 - 5168) v HSf Hrg Hb Hin HU He); [exact Hv | cbn; lia]. }
assert (RINVK : forall Lx Ax memx mdx, journal ubs2_msyms MR RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 Lx Ax memx mdx -> st_init_done Ax = true ->
(forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 + 128 <= x0 -> mbyte ubs2segs memx x0 = mbyte ubs2segs memc x0) ->
rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lx Ax memx mdx).
{ intros Lx Ax memx mdx HJx Hix KHx.
split; [exact HJx|]. split; [exact Hix|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc memx (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x0 Hx Hlx; apply KHx; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros i Hi. apply KHx; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
jbranch ubs2tbl HS.
{
rewrite branch_geu_U, U_lit, (U_atom _ 56 cnt) in Hc by first [lia | ew_havoc; exact HE56]. apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PC_SM. { wrq HU2. }
cbn [ms_mem mkst] in HF, HG |- *. kstepq KH1 KB1 HF HU20 HU2 HU8 HU45 Hkeep_in LAWS Lc Ac memc mdc HHc KH2 KB2. clear HF HG.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?regsF _ ?memF _) _) _ =>
apply (KSM regsF Lc Ac memF mdc ha pnew fimg imgl (mkCHT c f h u p x T h u T HT ent)) end.
unfold at_SM. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent].
split; [exact (RINVK Lc Ac _ mdc HJ Hinit KH2)|].
split. { split; [jreg HS (2%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|]. split; [lia|].
split; [jreg HS (15%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE46|].
split; [jreg HS (14%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE47|].
split; [jreg HS (11%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE56|].
split; [jreg HS (27%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE60|].
split; [jreg HS (26%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE45|].
split; [jreg HS (18%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE59|].
split; [jreg HS (20%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE20|].
split; [jreg HS (8%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE8|].
split; [jreg HS (21%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE21|].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (fun off e v Hin He Hv => SLOT Ef ssf msf _ off e v HS eq_refl eq_refl HU2 Hin He Hv) as SL; cbn [ms_mem mkst] in SL end.
split. { split; [apply (SL 8 (SOff 60 0) N); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE60 | lia]|].
split; [apply (SL 16 (SOff 45 0) cfp); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE45 | lia]|].
split; [apply (SL 24 (SOff 59 0) pnew); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE59 | lia]|].
apply (SL 48 (SOff 58 0) fimg); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE58 | lia]. }
split. { split; [apply (SL 64 (SAlu ALU_SLTU (SOff 19 0) (SLit 1)) (nha ha)); [cbv; tauto | rewrite denot_lit_U, (U_seqz_atom _ 19 ha HE19) by lia; reflexivity | unfold nha; destruct (ha =? 0); lia]|].
split; [apply (SL 88 (SOff 41 0) bef); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE41 | lia]|].
split; [apply (SL 104 (SExt true 32 (SOff 42 0)) (sx32v beffmt)); [cbv; tauto | rewrite denot_lit_U, (U_sext32_sx32v _ 42 beffmt HE42) by lia; reflexivity | apply sx32v_range; lia]|].
split; [apply (SL 112 (SOff 46 0) img); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE46 | lia]|].
apply (SL 120 (SOff 47 0) fmt); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE47 | lia]. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 32); [exact Hfc | reflexivity |]. intros i Hi. apply KH2; unfold OFF_fcfg; lia. }
split; [exact (RGK _ KB2)|]. split; [exact (CGK _ KB2)|]. split; [exact (IMK _ KB2)|].
split; [exact (STK _ KB2)|].
split; [exact (ARK _ KB2)|]. split; [exact Hinv|]. split; [exact HTT|]. split; [exact Hts|].
split; [exact Hpnz|]. split; [exact Hfnz|]. exact HB. }
rewrite branch_geu_U, U_lit, (U_atom _ 56 cnt) in Hc by first [lia | ew_havoc; exact HE56]. apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
add_fact' HS 56%nat (mkAF 256 (2^24) 0); [| rewrite HE56, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc. { wrq HU2. }
cbn [ms_mem mkst] in HF, HG. kstepq KH1 KB1 HF HU20 HU2 HU8 HU45 Hkeep_in LAWS Lc Ac memc mdc HHc KH2 KB2. clear HF HG.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Ma0 : getr (ms_regs msx) 10 = Z_to_bv 64 (4 * cnt))
by (eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; replace (4 * cnt) with (cnt * 2 ^ 2) by lia;
apply (U_sll_small_q _ _ cnt 2); [apply (U_atom _ 56 cnt HE56); lia | lia | lia | lia]) end.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := 4 * cnt) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hinit | exact Ma0 | lia
| exact Mq2 | lia | exact Hsp16 | lia | lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear Ma0 Mq2 Mq4 Mq1.
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & fdp & -> & HJ2 & Hinit2 & HP2 & Hf10 & Hres & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hf10, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
destruct (malloc_post_perm _ _ _ fdp (4 * cnt) _ HB Hres) as [HB2 Hsub2].
assert (HBc2 : In (c, 48) (blocks L2 A2)) by (apply Hsub2; exact HBc).
assert (KH3 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 + 128 <= x0 -> mbyte ubs2segs mem2 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hlx. rewrite <- (KH2 x0 Hx Hlx). apply (proj1 (Hhi2 x0 Hx ltac:(lia))). }
assert (KB3 : forall b m i, In (b, m) KEEP -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB2 b m i Hbm Hi). apply (Hkeep2 b m i (Hkeep_in _ _ Hbm) Hi). }
jafter_call_keep HS 61%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply (region_kept_block_ro ubs2segs _ _ _ 20); [ew_havoc; exact HU20 | exact HBc | exact Hkeep2 | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 8); [ew_havoc; exact HU8 | exact (Hkeep_in _ _ Hrk) | exact Hkeep2 | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 45); [ew_havoc; exact HU45 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS KH2 KB2. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hfat); cbn [ms_regs mkst] in Hfat; rewrite Hf10 in Hfat; symmetry in Hfat.
destruct Hres as [[-> HBeq] | (Hfdnz & Hfd16 & (fb1 & fb2 & HBf & HBfc) & Wf)].
{
pin_reg' HS (10%bv:reg) 0 Hf10.
jrun_to LAWS ubs2tbl_ok HS HJ2 PC_XC. { wrq HU2. }
cbn [ms_mem mkst] in HF, HG |- *.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KH4 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 + 128 <= x0 -> mbyte ubs2segs (ms_mem msx) x0 = mbyte ubs2segs memc x0)
by (intros x0 Hx Hlx; rewrite <- (KH3 x0 Hx Hlx); mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia | rewrite HU8; lia | rewrite HU45; lia]);
assert (KB4 : forall b m i, In (b, m) KEEP -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KB3 b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ Hbm)) as [Hb0 Hb1];
mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia | rewrite HU8; lia | rewrite HU45; lia])
end.
clear HF HG.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?regsF _ ?memF _) _) _ =>
apply (KXC fx regsF L2 A2 memF md2 ha pnew fimg (mkCHT c f h u p x T h u T HT ent) cnt (ht_pal HT) Hfrm0) end.
unfold at_XC, chtq_ok. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent].
split; [exact (RINVK L2 A2 _ md2 HJ2 Hinit2 KH4)|].
split. { split; [jreg HS (2%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [exact Hfmt|].
split; [jreg HS (20%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE20|].
split; [jreg HS (18%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE59|].
split; [jreg HS (8%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE8|].
split; [jreg HS (21%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE21|].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (fun off e v Hin He Hv => SLOT Ef ssf msf _ off e v HS eq_refl eq_refl ltac:(ew_havoc; exact HU2) Hin He Hv) as SL; cbn [ms_mem mkst] in SL end.
split; [apply (SL 48 (SOff 58 0) fimg); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE58 | lia]|].
split; [exact (RGK _ KB4)|]. split; [exact (CGK _ KB4)|].
split. { split; [exact (STK _ KB4)|].
split; [exact (proj1 (proj2 (proj2 (proj2 (ARK _ KB4)))))|].
split; [exact LenP|]. split; [exact Hts|].
intros b Hb. unfold cht_blks in Hb. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T] in Hb.
destruct Hb as [<-|Hb]; [cbn [fst]; lia|].
destruct b as [b m]. cbn [fst]. exact (proj1 (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ (ARR b m Hb)))). }
split; [exact Hpnz|]. split; [exact Hfnz|]. rewrite HBeq. exact HB. }
assert (HBfd2 : In (fdp, 4 * cnt) (blocks L2 A2)) by (rewrite HBf; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fdp (4 * cnt) HH2 HBfd2 ltac:(lia)) as (Rfd0 & Rfd1 & _).
rewrite (optb_nz fdp _ Hfdnz) in HB2.
add_fact' HS 65%nat (mkAF 4096 (CEIL_MAX - 1) 4); [| rewrite Hfat, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
jrun_to LAWS ubs2tbl_ok HS HJ2 PC_LH. { wrq HU2. }
cbn [ms_mem mkst] in HF, HG |- *. kstepq KH3 KB3 HF HU20 HU2 HU8 HU45 Hkeep_in LAWS Lc Ac memc mdc HHc KH4 KB4.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (PRES : forall k, 0 <= k < 4 * cnt -> exists b, mbyte ubs2segs (ms_mem msx) (fdp + k) = Some b)
by (intros k Hk; apply (present_mbyte ubs2_msyms); eapply (present_grows _ _ _ HG); apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ fdp (4 * cnt) k HH2 HBfd2 Hk))) end.
clear HF HG.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?regsF _ ?memF _) _) _ =>
apply (KLH regsF L2 A2 memF md2 ha pnew fimg imgl (mkCHT c f h u p x T h u T HT ent) fdp) end.
unfold at_LH. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent].
split; [exact (RINVK L2 A2 _ md2 HJ2 Hinit2 KH4)|].
split. { split; [jreg HS (2%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|]. split; [lia|]. split; [subst cnt; lia|].
split; [jreg HS (9%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; exact Hq|].
split; [jreg HS (19%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; exact Hq|].
split; [jreg HS (22%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; exact Hq|].
split; [jreg HS (23%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; exact Hq|].
split; [jreg HS (24%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact Hfat|].
split; [jreg HS (25%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; exact Hq|].
split; [jreg HS (18%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE59|].
split; [jreg HS (26%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE45|].
split; [jreg HS (27%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE60|].
split; [jreg HS (20%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE20|].
split; [jreg HS (8%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE8|].
split; [jreg HS (21%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE21|].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (fun off e v Hin He Hv => SLOT Ef ssf msf _ off e v HS eq_refl eq_refl ltac:(ew_havoc; exact HU2) Hin He Hv) as SL; cbn [ms_mem mkst] in SL end.
split. { split; [apply (SL 8 (SOff 60 0) N); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE60 | lia]|].
split; [apply (SL 16 (SOff 45 0) cfp); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE45 | lia]|].
split; [apply (SL 24 (SOff 59 0) pnew); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE59 | lia]|].
apply (SL 48 (SOff 58 0) fimg); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE58 | lia]. }
split. { split; [split; [apply (SL 64 (SAlu ALU_SLTU (SOff 19 0) (SLit 1)) (nha ha)); [cbv; tauto | rewrite denot_lit_U, (U_seqz_atom _ 19 ha) by first [lia | ew_havoc; exact HE19]; reflexivity | unfold nha; destruct (ha =? 0); lia]|];
split; [apply (SL 88 (SOff 41 0) bef); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE41 | lia]|];
split; [apply (SL 104 (SExt true 32 (SOff 42 0)) (sx32v beffmt)); [cbv; tauto | rewrite denot_lit_U, (U_sext32_sx32v _ 42 beffmt) by first [lia | ew_havoc; exact HE42]; reflexivity | apply sx32v_range; lia]|];
split; [apply (SL 112 (SOff 46 0) img); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE46 | lia]|];
apply (SL 120 (SOff 47 0) fmt); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE47 | lia]|].
split; [apply (SL 32 (SOff 48 0) fattr); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE48 | lia]|].
apply (SL 40 (SOff 39 0) W); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE39 | lia]. }
split; [apply (SL 96 (SAlu ALU_XOR (SOff 65 0) (SLit (-1))) (2 ^ 64 - 1 - fdp)); [cbv; tauto | rewrite denot_lit_U, (U_not _ 65 fdp) by first [lia | exact Hfat]; reflexivity | lia]|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 32); [exact Hfc | reflexivity |]. intros i Hi. apply KH4; unfold OFF_fcfg; lia. }
split; [exact (RGK _ KB4)|]. split; [exact (CGK _ KB4)|]. split; [exact (IMK _ KB4)|].
split; [exact (STK _ KB4)|].
split; [exact (ARK _ KB4)|]. split; [exact Hinv|]. split; [exact HTT|]. split; [exact Hts|]. split; [exact Hsum|].
split; [intros j Hj; lia|].
split; [exact PRES|].
split; [exact Hpnz|]. split; [exact Hfnz|]. split; [exact Hfdnz|]. split; [exact Hfd16|].
eapply Permutation_trans; [exact HB2|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.
End l.
End d.

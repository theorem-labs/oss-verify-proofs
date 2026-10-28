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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3n YI00 YI02 YI01 YI03 YI04 YI05
UI1e UI39 UI1i UI57 UI1h YI0x UI16 UI26 UO0e
YI07 YP14 YI08 YI0c YI0g UI3h UI3d UI4v UIZm
YI0h UI40 UI3y.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Definition E2_R1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x26c).
Definition E2_R2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x27c).
Lemma val_mem4_of_bytes : forall segs (m : word -> option byte) a (b0 b1 b2 b3 : byte),
mbyte segs m a = Some b0 -> mbyte segs m (a + 1) = Some b1 -> mbyte segs m (a + 2) = Some b2 -> mbyte segs m (a + 3) = Some b3 ->
val_mem segs m a 4 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
Proof.
intros segs m a b0 b1 b2 b3 H0 H1 H2 H3.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
set (v := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
assert (Hv : 0 <= v < 2 ^ (8 * Z.of_nat 4)) by (subst v; cbn; lia).
intros k Hk. rewrite le_byte_small by (exact Hv || exact Hk).
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- change (Z.of_nat 0) with 0. rewrite Z.add_0_r, H0, Z.mul_0_r, Z.shiftr_0_r. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. subst v. lia.
- change (Z.of_nat 1) with 1. rewrite H1. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (8 * 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. subst v. lia.
- change (Z.of_nat 2) with 2. rewrite H2. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (8 * 2) with 16. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. subst v. lia.
- change (Z.of_nat 3) with 3. rewrite H3. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (8 * 3) with 24. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. subst v. lia.
Qed.
Lemma arr32_of_present : forall segs (m : word -> option byte) base n,
(forall i, 0 <= i < 4 * Z.of_nat n -> exists b, mbyte segs m (base + i) = Some b) ->
exists l, arr32 segs m base l /\ length l = n.
Proof.
intros segs m base n. induction n as [|n IH]; intros Hp.
- exists []. split; [intros j Hj; cbn in Hj; lia | reflexivity].
- destruct (IH ltac:(intros i Hi; apply Hp; lia)) as (l & Hl & Hlen).
destruct (Hp (4 * Z.of_nat n) ltac:(lia)) as [b0 Hb0]. destruct (Hp (4 * Z.of_nat n + 1) ltac:(lia)) as [b1 Hb1].
destruct (Hp (4 * Z.of_nat n + 2) ltac:(lia)) as [b2 Hb2]. destruct (Hp (4 * Z.of_nat n + 3) ltac:(lia)) as [b3 Hb3].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
exists (l ++ [bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3]). split; [| rewrite length_app; cbn; lia].
intros j Hj. rewrite length_app in Hj. cbn in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt|Hge].
+ rewrite app_nth1 by lia. apply Hl. exact Hlt.
+ assert (j = n) by lia. subst j. rewrite app_nth2 by lia. rewrite Hlen, Nat.sub_diag. cbn [nth]. split; [| lia].
apply val_mem4_of_bytes; [exact Hb0 | | |].
* replace (base + 4 * Z.of_nat n + 1) with (base + (4 * Z.of_nat n + 1)) by lia. exact Hb1.
* replace (base + 4 * Z.of_nat n + 2) with (base + (4 * Z.of_nat n + 2)) by lia. exact Hb2.
* replace (base + 4 * Z.of_nat n + 3) with (base + (4 * Z.of_nat n + 3)) by lia. exact Hb3.
Qed.
Lemma arr8_Forall : forall segs (m : word -> option byte) base l, arr8 segs m base l -> Forall (fun v => 0 <= v < 256) l.
Proof.
intros segs m base l H. apply Forall_forall. intros v Hv. destruct (In_nth l v 0 Hv) as (i & Hi & <-). exact (proj2 (H i Hi)).
Qed.
Lemma arr8_zero : forall segs (m : word -> option byte) base n,
(forall i, 0 <= i < n -> mbyte segs m (base + i) = Some (Z_to_bv 8 0)) -> arr8 segs m base (repeat 0 (Z.to_nat n)).
Proof.
intros segs m base n H j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [apply H; lia | lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition CHT_LITS : list (option Z) := [None; None; None; None; Some 0; Some 0; Some 524309].
Definition ss_E2b : sstate :=
mkSS PC_M2 sr_atoms
[ YQ0b.mkRegion (Some 20%nat) 0 48 0 48 (obj_chunks_gen LAY_Cht 32 CHT_LITS) ;
YQ0b.mkRegion (Some 2%nat) 0 128 0 112 [mkChunk 112 (CVal 8 (SOff 39 0)); mkChunk 120 (CVal 8 (SOff 40 0))] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (20%nat, mkAF 4096 (CEIL_MAX - 48) 4); (27%nat, mkAF 1 RGB_NMAX 0); (39%nat, mkAF 3 4 0); (40%nat, mkAF 4096 CEIL_MAX 0) ] [] []).
Section q.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Lemma ubs2_rgbadd_E2b :
K_HL API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest 0 ->
K_X38 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
K_M2 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KHL KX38 regs1 Lc Ac memc mdc pnew fimg imgl c f h u p x HAT. unfold K_HL, cfg_at in KHL. unfold K_X38, cfg_at in KX38.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & G8 & G26 & G18 & G9 & G21 & G27 & S112 & S120 & G20 & G10
& Hfc & Hobj & Hcg & Himg & Hpnz & Hfnz & Hcnz & Hc16 & Rf & Rh & Ru & Rp & Rx & Hcht & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HHt & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HCHT : CHT_SIZE = 48) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity. assert (HTS0 : TS0 = 524309) by reflexivity.
assert (HRFCv : RGBFC_SIZE = 24) by reflexivity.
set (KEEP := BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]) in *.
set (TMP := [(c, CHT_SIZE)] ++ optb f (4 * TS0) ++ optb h (3 * TS0) ++ optb u TS0 ++ optb p (3 * TS0) ++ optb x (4 * TS0)).
assert (HBkt : Permutation (blocks Lc Ac) (KEEP ++ TMP)).
{ subst KEEP TMP. rewrite <- !app_assoc. cbn [app]. exact HB. }
assert (Hkeep_in : forall b m, In (b, m) KEEP -> In (b, m) (blocks Lc Ac)).
{ intros b m Hbm. eapply Permutation_in; [apply Permutation_sym; exact HBkt|]. apply in_app_iff. left. exact Hbm. }
assert (Hrk : In (r, RGB_SIZE) KEEP) by (subst KEEP; apply in_app_iff; left; left; reflexivity).
pose proof (Hkeep_in _ _ Hrk) as Hrin.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE HHc Hrin ltac:(lia)) as (Rr0 & Rr1 & Rr16).
pose proof (obj_at_range _ _ _ _ _ Hcfp) as Rcfg. pose proof (Rcfg 0%nat img eq_refl) as Rimg. pose proof (Rcfg 1%nat fmt eq_refl) as Rfmt. cbn in Rimg, Rfmt.
assert (HfN2 : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HNmax HNMv; nia).
assert (HBpn : In (pnew, fmt * N) (blocks Lc Ac)) by (apply Hkeep_in; subst KEEP; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ pnew (fmt * N) HHc HBpn ltac:(lia)) as (Rpn0 & Rpn1 & _).
assert (HBfi : In (fimg, N) (blocks Lc Ac)) by (apply Hkeep_in; subst KEEP; apply in_app_iff; right; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fimg N HHc HBfi ltac:(lia)) as (Rfi0 & Rfi1 & _).
assert (HBc : In (c, 48) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HBkt|]. apply in_app_iff. right. left. rewrite HCHT. reflexivity. }
destruct (heap_blocks_range _ _ LAWS _ _ _ _ c 48 HHc HBc ltac:(lia)) as (Rc0 & Rc1 & _).
assert (Hcdis : forall b m, In (b, m) KEEP -> c + 48 <= b \/ b + m <= c).
{ intros b m Hbm. pose proof (heap_sep_app' API Lc Ac memc mdc KEEP TMP (b, m) (c, 48) HHc HBkt Hbm ltac:(subst TMP; left; rewrite HCHT; reflexivity)) as X. cbn [fst snd] in X. lia. }
assert (Hib : img_block img fmt N = [(img, fmt * N)]) by (unfold img_block, fmt_okb; destruct Hfmt as [-> | ->]; reflexivity).
assert (HimgK : In (img, fmt * N) KEEP).
{ subst KEEP. apply in_app_iff. left. unfold BASE. rewrite Hib. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
destruct (heap_blocks_range _ _ LAWS _ _ _ _ img (fmt * N) HHc (Hkeep_in _ _ HimgK) ltac:(lia)) as (Rim0 & Rim1 & _).
assert (CGK : forall m', (forall b n i, In (b, n) KEEP -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) -> cgif_at m' g s).
{ intros m' Hk. eapply (cgif_at_kept _ _ g s N KEEP); [| exact Hcg | exact Hk].
subst KEEP. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
assert (RGK : forall m', (forall b n i, In (b, n) KEEP -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) ->
rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur m').
{ intros m' Hk. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply (Hk r RGB_SIZE i Hrk Hi). }
assert (IMK : forall m', (forall b n i, In (b, n) KEEP -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs memc (b + i)) -> img_at N img fmt m' imgl).
{ intros m' Hk. split; [|exact (proj2 Himg)]. eapply arr8_frame; [exact (proj1 Himg)|]. intros a Ha. replace a with (img + (a - img)) by lia.
apply (Hk img (fmt * N)); [exact HimgK | rewrite (proj2 Himg) in Ha; lia]. }
assert (Hfmt34 : 3 <= fmt <= 4) by lia.
change (fmt = 3 \/ fmt = 4) with (boxP (fmt = 3 \/ fmt = 4)) in Hfmt.
change (bef = 0 \/ beffmt = 3 \/ beffmt = 4) with (boxP (bef = 0 \/ beffmt = 3 \/ beffmt = 4)) in Hbef.
set (E := Ereg regs1 (map (Z_to_bv 64) [f; h; u; p; 0; 0; TS0] ++ (map (Z_to_bv 64) [fmt; img] ++ []))).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error [f; h; u; p; 0; 0; TS0] j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE32 : ew E 32 = Z_to_bv 64 f) by (apply (HV 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 h) by (apply (HV 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 u) by (apply (HV 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 p) by (apply (HV 3%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 0) by (apply (HV 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 TS0) by (apply (HV 6%nat); reflexivity).
assert (HE27 : ew E 27 = Z_to_bv 64 N) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HE10 : ew E 10 = Z_to_bv 64 x) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE39 : ew E 39 = Z_to_bv 64 fmt) by (subst E; exact (Ereg_vals2 regs1 [f; h; u; p; 0; 0; TS0] [fmt; img] [] 0%nat fmt eq_refl)).
assert (HE40 : ew E 40 = Z_to_bv 64 img) by (subst E; exact (Ereg_vals2 regs1 [f; h; u; p; 0; 0; TS0] [fmt; img] [] 1%nat img eq_refl)).
pose proof Hal0 as Hal16. unfold UI4v.sp0 in Hal16, Hclo, Hceil, H63, Hstw, HJ.
set (sp0 := spZ regs0) in *. assert (Hsp0 : sp0 = spZ regs0) by reflexivity.
assert (Hspv : sp regs0 = sp0 - 5168) by (unfold sp, UI4v.sp0, RGBA_FRAME; lia).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 5168) by (rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = c) by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
assert (Hsp16 : (sp0 - 5168) mod 16 = 0).
{ replace (sp0 - 5168) with (sp0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal16 | lia]. }
assert (HS : st_ok ubs2segs E ss_E2b (mkst regs1 (Z_to_bv 64 PC_M2) memc (seg_rom ubs2segs))).
{ unfold ss_E2b. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply (region_ok_obj_gen ubs2segs _ memc 20 c); [exact HU20 | lia | lia | exact Hcht | reflexivity | | |].
* intros j v Hj. apply (Ereg_vals regs1 _ _ j v). exact Hj.
* intros j z Hj. unfold CHT_LITS in Hj. destruct j as [|[|[|[|[|[|[|j]]]]]]]; cbn in Hj; try discriminate Hj; try (injection Hj as <-; reflexivity). destruct j; discriminate Hj.
* intros i Hi. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ c 48 i HHc HBc Hi)).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
constructor; [|constructor; [|constructor]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ fmt); [cbn [sv_denot]; rewrite Z.add_0_r, HE39, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_word_mem. unfold slot in S112. rewrite Hspv in S112. exact S112.
* eapply (chunk_ok_val _ _ _ _ _ _ _ img); [cbn [sv_denot]; rewrite Z.add_0_r, HE40, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_word_mem. unfold slot in S120. rewrite Hspv in S120. exact S120.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU20. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU20, HE27, HE39, HE40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_M2) memc (seg_rom ubs2segs))) in HJ.
assert (Wc' : wtok' RGBA_STK sp0 (FPfoot r g bef beffmt s N) (blocks L A) (c, 48)).
{ intros blc i Hin Hi. right. right. exists c, 48. split; [exact Hin|]. split; [| cbn [fst snd] in Hi |- *; lia].
rewrite <- HCHT. exact (proj2 (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc KEEP TMP c CHT_SIZE HHc HBkt HBent
ltac:(intros x1 Hx1; subst KEEP; apply in_app_iff; left; exact Hx1) ltac:(subst TMP; left; reflexivity) ltac:(lia))). }
Ltac wr2 HU20 HU2 Wc' HBin :=
wr_norm;
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 20); [reflexivity | ew_havoc; exact HU20 | |];
[ cbn [r_wlo r_whi]; intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ _ 48); [exact Wc' | exact HBin | lia]
| eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]; apply wr_ok_nil ].
Ltac kstep KHp KBp HF HU20 HU2 Hcdis Hkeep_in LAWS Lc Ac memc mdc HHc KHn KBn :=
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KHn : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> _ <= x0 -> mbyte ubs2segs (ms_mem msx) x0 = mbyte ubs2segs memc x0)
by (intros x0 Hx Hlx; rewrite <- (KHp x0 Hx Hlx); mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia]);
assert (KBn : forall b m i, In (b, m) _ -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KBp b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ Hbm)) as [Hb0 Hb1];
pose proof (Hcdis b m Hbm) as Hbd; mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia]);
clear KHp KBp
end.
assert (TOX38 : forall (regsx : bvmap 5 word) (memx : word -> option byte),
journal ubs2_msyms MR RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac memx mdc ->
(forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 + 112 <= x0 -> mbyte ubs2segs memx x0 = mbyte ubs2segs memc x0) ->
(forall b m i, In (b, m) KEEP -> 0 <= i < m -> mbyte ubs2segs memx (b + i) = mbyte ubs2segs memc (b + i)) ->
getr regsx 2 = Z_to_bv 64 (sp regs0) -> getr regsx 3 = getr regs0 3 -> getr regsx 4 = getr regs0 4 ->
getr regsx 20 = Z_to_bv 64 c -> getr regsx 18 = Z_to_bv 64 pnew -> getr regsx 9 = Z_to_bv 64 fimg -> getr regsx 8 = Z_to_bv 64 r -> getr regsx 21 = Z_to_bv 64 2 ->
obj_at ubs2segs memx c LAY_Cht [f; h; u; p; x; 0; TS0] ->
SR ubs2segs (mkCfg (mkst regsx (Z_to_bv 64 PC_X38) memx (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest)).
{ intros regsx memx HJx KHx KBx R2 R3 R4 R20 R18 R9 R8 R21 Hchx.
apply (KX38 regsx Lc Ac memx mdc pnew fimg c f h u p x 0 TS0). split.
{ split; [exact HJx|]. split; [exact Hinit|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc memx (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x0 Hx Hlx; apply KHx; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros i Hi. apply KHx; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split; [split; [exact R2 | split; [exact R3 | exact R4]]|].
split; [exact Hfmt|]. split; [exact R20|]. split; [exact R18|]. split; [exact R9|]. split; [exact R8|]. split; [exact R21|].
split; [exact (RGK _ KBx)|]. split; [exact (CGK _ KBx)|]. split; [exact Hpnz|]. split; [exact Hfnz|]. split; [exact Hchx|]. exact HB. }
Ltac x38_exit TOX38 HS HJ KHp KBp HU20 HU2 Hcdis Hkeep_in HE HE32 HE33 HE34 HE35 HE10 HE37 HE38 G2 G3 G4 G20 G18 G9 G8 G21 Rf Rh Ru Rp Rx HTS0 LAWS Lc Ac memc mdc HHc c f h u p x :=
cbn [ms_mem mkst] in *;
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
let HF := match goal with HFx : frame_of _ _ _ (ms_mem msx) |- _ => HFx end in
let KH9 := fresh "KH9" in let KB9 := fresh "KB9" in
assert (KH9 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> _ <= x0 -> mbyte ubs2segs (ms_mem msx) x0 = mbyte ubs2segs memc x0)
by (intros x0 Hx Hlx; rewrite <- (KHp x0 Hx Hlx); mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia]);
assert (KB9 : forall b m i, In (b, m) _ -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KBp b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ Hbm)) as [Hb0 Hb1];
pose proof (Hcdis b m Hbm) as Hbd; mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia]);
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl); cbn [ss_pc]; lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_X38) end;
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let VF := fresh "VF" in let ZF := fresh "ZF" in
pose proof (fun off n e v Hin => st_chunk_val ubs2segs Ef ssf msf 0%nat _ 20%nat off n e c v HS eq_refl eq_refl Hin HU20) as VF;
cbn [ms_mem mkst] in VF;
eapply (TOX38 (ms_regs msf));
[ exact HJ | exact KH9 | exact KB9
| let Q := fresh "Q" in jreg HS (2%bv:reg) as Q; cbn [ms_regs mkst] in Q; rewrite Q, (HE 2%nat 2%bv eq_refl); exact G2
| let Q := fresh "Q" in jreg HS (3%bv:reg) as Q; cbn [ms_regs mkst] in Q; rewrite Q, (HE 3%nat 3%bv eq_refl); exact G3
| let Q := fresh "Q" in jreg HS (4%bv:reg) as Q; cbn [ms_regs mkst] in Q; rewrite Q, (HE 4%nat 4%bv eq_refl); exact G4
| let Q := fresh "Q" in jreg HS (20%bv:reg) as Q; cbn [ms_regs mkst] in Q; rewrite Q, (HE 20%nat 20%bv eq_refl); exact G20
| let Q := fresh "Q" in jreg HS (18%bv:reg) as Q; cbn [ms_regs mkst] in Q; rewrite Q, (HE 18%nat 18%bv eq_refl); exact G18
| let Q := fresh "Q" in jreg HS (9%bv:reg) as Q; cbn [ms_regs mkst] in Q; rewrite Q, (HE 9%nat 9%bv eq_refl); exact G9
| let Q := fresh "Q" in jreg HS (8%bv:reg) as Q; cbn [ms_regs mkst] in Q; rewrite Q, (HE 8%nat 8%bv eq_refl); exact G8
| let Q := fresh "Q" in jreg HS (21%bv:reg) as Q; cbn [ms_regs mkst] in Q; rewrite Q, (HE 21%nat 21%bv eq_refl); exact G21
| cbn [obj_at LAY_Cht]; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N];
split; [split; [apply (VF 0 8%N (SOff 32 0) f); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE32 | lia | cbn; lia] | lia]|];
split; [split; [apply (VF 8 8%N (SOff 33 0) h); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE33 | lia | cbn; lia] | lia]|];
split; [split; [apply (VF 16 8%N (SOff 34 0) u); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE34 | lia | cbn; lia] | lia]|];
split; [split; [apply (VF 24 8%N (SOff 35 0) p); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE35 | lia | cbn; lia] | lia]|];
split; [split; [apply (VF 32 8%N (SOff 10 0) x); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE10 | lia | cbn; lia] | lia]|];
split; [split; [apply (VF 40 4%N (SLit 0) 0); [cbv; tauto | reflexivity | lia | cbn; lia] | lia]|];
split; [split; [apply (VF 44 4%N (SLit 524309) TS0); [cbv; tauto | reflexivity | rewrite HTS0; lia | cbn; lia] | rewrite HTS0; lia]|];
exact I ]
end
end.
jrun LAWS ubs2tbl_ok HS HJ. { wr2 HU20 HU2 Wc' HBc. }
cbn [ms_mem mkst] in HF, HG.
assert (KH1 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 + 112 <= x0 -> mbyte ubs2segs (ms_mem ms) x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hlx. mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia]. }
assert (KB1 : forall b m i, In (b, m) KEEP -> 0 <= i < m -> mbyte ubs2segs (ms_mem ms) (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ Hbm)) as [Hb0 Hb1].
pose proof (Hcdis b m Hbm) as Hbd. mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia]. }
pose proof HG as HGA. clear HF HG.
Ltac wrw HU20 HU2 Wc' HBin := eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 20); [reflexivity | ew_havoc; exact HU20 | |];
[ cbn [r_wlo r_whi]; intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ _ 48); [exact Wc' | exact HBin | lia]
| eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]; apply wr_ok_nil ].
jbranch ubs2tbl HS.
2: { jrun_to LAWS ubs2tbl_ok HS HJ PC_X38. { wrw HU20 HU2 Wc' HBc. }
x38_exit TOX38 HS HJ KH1 KB1 HU20 HU2 Hcdis Hkeep_in HE HE32 HE33 HE34 HE35 HE10 HE37 HE38 G2 G3 G4 G20 G18 G9 G8 G21 Rf Rh Ru Rp Rx HTS0 LAWS Lc Ac memc mdc HHc c f h u p x. }
rewrite branch_ne_U, U_lit, (U_atom _ 32 f) in Hc by first [lia | ew_havoc; exact HE32]. assert (Hfnz' : f <> 0) by (apply negb_true_iff, Z.eqb_neq in Hc; exact Hc). clear Hc.
jrun LAWS ubs2tbl_ok HS HJ. { wrw HU20 HU2 Wc' HBc. }
cbn [ms_mem mkst] in HF, HG. kstep KH1 KB1 HF HU20 HU2 Hcdis Hkeep_in LAWS Lc Ac memc mdc HHc KH2 KB2.
pose proof (mem_grows_trans _ _ _ HGA HG) as HGA'. clear HGA HF HG. rename HGA' into HGA.
jbranch ubs2tbl HS.
2: { jrun_to LAWS ubs2tbl_ok HS HJ PC_X38. { wrw HU20 HU2 Wc' HBc. }
x38_exit TOX38 HS HJ KH2 KB2 HU20 HU2 Hcdis Hkeep_in HE HE32 HE33 HE34 HE35 HE10 HE37 HE38 G2 G3 G4 G20 G18 G9 G8 G21 Rf Rh Ru Rp Rx HTS0 LAWS Lc Ac memc mdc HHc c f h u p x. }
rewrite branch_ne_U, U_lit, (U_atom _ 33 h) in Hc by first [lia | ew_havoc; exact HE33]. assert (Hhnz : h <> 0) by (apply negb_true_iff, Z.eqb_neq in Hc; exact Hc). clear Hc.
jrun LAWS ubs2tbl_ok HS HJ. { wrw HU20 HU2 Wc' HBc. }
cbn [ms_mem mkst] in HF, HG. kstep KH2 KB2 HF HU20 HU2 Hcdis Hkeep_in LAWS Lc Ac memc mdc HHc KH3 KB3.
pose proof (mem_grows_trans _ _ _ HGA HG) as HGA'. clear HGA HF HG. rename HGA' into HGA.
jbranch ubs2tbl HS.
2: { jrun_to LAWS ubs2tbl_ok HS HJ PC_X38. { wrw HU20 HU2 Wc' HBc. }
x38_exit TOX38 HS HJ KH3 KB3 HU20 HU2 Hcdis Hkeep_in HE HE32 HE33 HE34 HE35 HE10 HE37 HE38 G2 G3 G4 G20 G18 G9 G8 G21 Rf Rh Ru Rp Rx HTS0 LAWS Lc Ac memc mdc HHc c f h u p x. }
rewrite branch_ne_U, U_lit, (U_atom _ 34 u) in Hc by first [lia | ew_havoc; exact HE34]. assert (Hunz : u <> 0) by (apply negb_true_iff, Z.eqb_neq in Hc; exact Hc). clear Hc.
jrun LAWS ubs2tbl_ok HS HJ. { wrw HU20 HU2 Wc' HBc. }
cbn [ms_mem mkst] in HF, HG. kstep KH3 KB3 HF HU20 HU2 Hcdis Hkeep_in LAWS Lc Ac memc mdc HHc KH4 KB4.
pose proof (mem_grows_trans _ _ _ HGA HG) as HGA'. clear HGA HF HG. rename HGA' into HGA.
jbranch ubs2tbl HS.
2: { jrun_to LAWS ubs2tbl_ok HS HJ PC_X38. { wrw HU20 HU2 Wc' HBc. }
x38_exit TOX38 HS HJ KH4 KB4 HU20 HU2 Hcdis Hkeep_in HE HE32 HE33 HE34 HE35 HE10 HE37 HE38 G2 G3 G4 G20 G18 G9 G8 G21 Rf Rh Ru Rp Rx HTS0 LAWS Lc Ac memc mdc HHc c f h u p x. }
rewrite branch_ne_U, U_lit, (U_atom _ 35 p) in Hc by first [lia | ew_havoc; exact HE35]. assert (Hpnz' : p <> 0) by (apply negb_true_iff, Z.eqb_neq in Hc; exact Hc). clear Hc.
jrun LAWS ubs2tbl_ok HS HJ. { wrw HU20 HU2 Wc' HBc. }
cbn [ms_mem mkst] in HF, HG. kstep KH4 KB4 HF HU20 HU2 Hcdis Hkeep_in LAWS Lc Ac memc mdc HHc KH5 KB5.
pose proof (mem_grows_trans _ _ _ HGA HG) as HGA'. clear HGA HF HG. rename HGA' into HGA.
jbranch ubs2tbl HS.
2: { jrun_to LAWS ubs2tbl_ok HS HJ PC_X38. { wrw HU20 HU2 Wc' HBc. }
x38_exit TOX38 HS HJ KH5 KB5 HU20 HU2 Hcdis Hkeep_in HE HE32 HE33 HE34 HE35 HE10 HE37 HE38 G2 G3 G4 G20 G18 G9 G8 G21 Rf Rh Ru Rp Rx HTS0 LAWS Lc Ac memc mdc HHc c f h u p x. }
rewrite branch_ne_U, U_lit, (U_atom _ 10 x) in Hc by first [lia | ew_havoc; exact HE10]. assert (Hxnz : x <> 0) by (apply negb_true_iff, Z.eqb_neq in Hc; exact Hc). clear Hc.
rename KH5 into KH6. rename KB5 into KB6.
subst TMP. rewrite (optb_nz f _ Hfnz'), (optb_nz h _ Hhnz), (optb_nz u _ Hunz), (optb_nz p _ Hpnz'), (optb_nz x _ Hxnz) in HBkt. cbn [app] in HBkt.
assert (ARRS : forall b m, In (b, m) [(f, 4 * TS0); (h, 3 * TS0); (u, TS0); (p, 3 * TS0); (x, 4 * TS0)] ->
In (b, m) (blocks Lc Ac) /\ ~ In (b, m) (blocks L A) /\ 4096 <= b /\ b + m <= alloc_ceiling /\
(c + 48 <= b \/ b + m <= c) /\ (forall b' m', In (b', m') KEEP -> b + m <= b' \/ b' + m' <= b)).
{ intros b m Hbm.
assert (Hm : 0 < m) by (cbv [In] in Hbm; destruct Hbm as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; injection Hq as <- <-; lia).
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc KEEP ((c, CHT_SIZE) :: [(f, 4 * TS0); (h, 3 * TS0); (u, TS0); (p, 3 * TS0); (x, 4 * TS0)]) b m
HHc HBkt HBent ltac:(intros x1 Hx1; subst KEEP; apply in_app_iff; left; exact Hx1) ltac:(right; exact Hbm) Hm) as [Hin Hnot].
destruct (heap_blocks_range _ _ LAWS _ _ _ _ b m HHc Hin Hm) as (Hb0 & Hb1 & _).
split; [exact Hin|]. split; [exact Hnot|]. split; [exact Hb0|]. split; [exact Hb1|]. split.
- pose proof (heap_sep_app' API Lc Ac memc mdc (KEEP ++ [(c, CHT_SIZE)]) [(f, 4 * TS0); (h, 3 * TS0); (u, TS0); (p, 3 * TS0); (x, 4 * TS0)] (c, 48) (b, m) HHc
ltac:(rewrite <- app_assoc; exact HBkt) ltac:(apply in_app_iff; right; left; rewrite HCHT; reflexivity) Hbm) as X. cbn [fst snd] in X. lia.
- intros b' m' Hbm'. pose proof (heap_sep_app' API Lc Ac memc mdc KEEP _ (b', m') (b, m) HHc HBkt Hbm' ltac:(right; exact Hbm)) as X. cbn [fst snd] in X. lia. }
destruct (ARRS f (4 * TS0) ltac:(cbv [In]; tauto)) as (HBf_in & _ & Rf0 & Rf1 & _ & _).
destruct (ARRS h (3 * TS0) ltac:(cbv [In]; tauto)) as (HBh_in & _ & Rh0 & Rh1 & _ & _).
destruct (ARRS u TS0 ltac:(cbv [In]; tauto)) as (HBu_in & Hu_tmp & Ru0 & Ru1 & Hcu & Hudis).
destruct (ARRS p (3 * TS0) ltac:(cbv [In]; tauto)) as (HBp_in & Hp_tmp & Rp0 & Rp1 & Hcp & Hpdis).
destruct (ARRS x (4 * TS0) ltac:(cbv [In]; tauto)) as (HBx_in & _ & Rx0 & Rx1 & _ & _).
assert (Hpu : p + 3 * TS0 <= u \/ u + TS0 <= p).
{ pose proof (heap_sep_app' API Lc Ac memc mdc (KEEP ++ [(c, CHT_SIZE); (f, 4 * TS0); (h, 3 * TS0); (u, TS0)]) [(p, 3 * TS0); (x, 4 * TS0)] (u, TS0) (p, 3 * TS0) HHc
ltac:(rewrite <- app_assoc; exact HBkt) ltac:(apply in_app_iff; right; cbv [In]; tauto) ltac:(left; reflexivity)) as X. cbn [fst snd] in X. lia. }
clear ARRS.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset. { wrw HU20 HU2 Wc' HBc. }
cbn [ms_mem mkst] in HF, HG. kstep KH6 KB6 HF HU20 HU2 Hcdis Hkeep_in LAWS Lc Ac memc mdc HHc KH7 KB7.
pose proof (mem_grows_trans _ _ _ HGA HG) as HGA'. clear HGA HF HG. rename HGA' into HGA.
jreg HS (10%bv:reg) as Ma0. rewrite HE35 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?Ef _ _ =>
eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset_spec Ef _ _ RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac _ p 0 (3 * TS0));
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ] end.
- intros i Hi. eapply (present_grows _ _ _ HGA). apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ p (3 * TS0) i HHc HBp_in Hi)).
- intros a Ha. right. right. exists p, (3 * TS0). split; [exact HBp_in|]. split; [exact Hp_tmp | lia]. }
clear Ma0 Ma1 Ma2 Mra.
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hz2). clear HJ.
cbn [ms_regs ms_mem mkst] in Hfr2, Hout2, Hgr2, Hz2, HJ2.
jafter_stretch_keep HS 41%nat regs2 mem2 MEMSET_CLOB E2_R1 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU20; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU20; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU20; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (KH8 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 + 112 <= x0 -> mbyte ubs2segs mem2 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hlx. rewrite <- (KH7 x0 Hx Hlx). unfold mbyte. rewrite (Hout2 (Z_to_bv 64 x0)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
assert (KB8 : forall b m i, In (b, m) KEEP -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB7 b m i Hbm Hi). destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ Hbm)) as [Hb0 Hb1].
pose proof (Hpdis b m Hbm) as Hbd. unfold mbyte. rewrite (Hout2 (Z_to_bv 64 (b + i))) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
pose proof (mem_grows_trans _ _ _ HGA Hgr2) as HGA'. clear HGA KH7 KB7. rename HGA' into HGA.
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_memset. { wrw HU20 HU2 Wc' HBc. }
cbn [ms_mem mkst] in HF, HG. kstep KH8 KB8 HF HU20 HU2 Hcdis Hkeep_in LAWS Lc Ac memc mdc HHc KH9 KB9.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Zp9 : forall i, 0 <= i < 3 * TS0 -> mbyte ubs2segs (ms_mem msx) (p + i) = Some (Z_to_bv 8 0))
by (intros i Hi; rewrite <- (Hz2 i Hi); mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia]) end.
pose proof (mem_grows_trans _ _ _ HGA HG) as HGA'. clear HGA HF HG Hz2. rename HGA' into HGA.
jreg HS (10%bv:reg) as Ma0. rewrite HE34 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?Ef _ _ =>
eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset_spec Ef _ _ RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac _ u 0 TS0);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ] end.
- intros i Hi. eapply (present_grows _ _ _ HGA). apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ u TS0 i HHc HBu_in Hi)).
- intros a Ha. right. right. exists u, TS0. split; [exact HBu_in|]. split; [exact Hu_tmp | lia]. }
clear Ma0 Ma1 Ma2 Mra.
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10' & Hfr3 & Hout3 & Hgr3 & Hz3). clear HJ2.
cbn [ms_regs ms_mem mkst] in Hfr3, Hout3, Hgr3, Hz3, HJ3.
jafter_stretch_keep HS 47%nat regs3 mem3 MEMSET_CLOB E2_R2 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr3. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU20; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU20; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU20; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (KH10 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp0 - 5168 + 112 <= x0 -> mbyte ubs2segs mem3 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hlx. rewrite <- (KH9 x0 Hx Hlx). unfold mbyte. rewrite (Hout3 (Z_to_bv 64 x0)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
assert (KB10 : forall b m i, In (b, m) KEEP -> 0 <= i < m -> mbyte ubs2segs mem3 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB9 b m i Hbm Hi). destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc (Hkeep_in _ _ Hbm)) as [Hb0 Hb1].
pose proof (Hudis b m Hbm) as Hbd. unfold mbyte. rewrite (Hout3 (Z_to_bv 64 (b + i))) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
assert (Zp10 : forall i, 0 <= i < 3 * TS0 -> mbyte ubs2segs mem3 (p + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. rewrite <- (Zp9 i Hi). unfold mbyte. rewrite (Hout3 (Z_to_bv 64 (p + i))) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
pose proof (mem_grows_trans _ _ _ HGA Hgr3) as HGA'. clear HGA KH9 KB9 Zp9. rename HGA' into HGA.
jrun_to LAWS ubs2tbl_ok HS HJ3 PC_HL. { wrw HU20 HU2 Wc' HBc. }
cbn [ms_mem mkst] in HF, HG |- *. kstep KH10 KB10 HF HU20 HU2 Hcdis Hkeep_in LAWS Lc Ac memc mdc HHc KH11 KB11.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Zp11 : forall i, 0 <= i < 3 * TS0 -> mbyte ubs2segs (ms_mem msx) (p + i) = Some (Z_to_bv 8 0))
by (intros i Hi; rewrite <- (Zp10 i Hi); mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia]);
assert (Zu11 : forall i, 0 <= i < TS0 -> mbyte ubs2segs (ms_mem msx) (u + i) = Some (Z_to_bv 8 0))
by (intros i Hi; rewrite <- (Hz3 i Hi); mb_frame_g HF; [reflexivity | rewrite HU20; lia | rewrite HU2; lia]) end.
pose proof (mem_grows_trans _ _ _ HGA HG) as HGA'. clear HGA HF HG Zp10 Hz3. rename HGA' into HGA.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_HL) end.
lazymatch type of HS with st_ok _ _ _ ?msf => set (memF := ms_mem msf) in * end.
destruct (arr32_of_present ubs2segs memF f (Z.to_nat TS0)
ltac:(intros i Hi; rewrite Z2Nat.id in Hi by lia; apply (present_mbyte ubs2_msyms); eapply (present_grows _ _ _ HGA); apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ f (4 * TS0) i HHc HBf_in ltac:(lia)))))
as (frequ & Hfrequ & Hflen).
destruct (arr8_of_present ubs2segs memF h (Z.to_nat (3 * TS0))
ltac:(intros i Hi; rewrite Z2Nat.id in Hi by lia; apply (present_mbyte ubs2_msyms); eapply (present_grows _ _ _ HGA); apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ h (3 * TS0) i HHc HBh_in ltac:(lia)))))
as (keys & Hkeys & Hklen).
destruct (arr32_of_present ubs2segs memF x (Z.to_nat TS0)
ltac:(intros i Hi; rewrite Z2Nat.id in Hi by lia; apply (present_mbyte ubs2_msyms); eapply (present_grows _ _ _ HGA); apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ x (4 * TS0) i HHc HBx_in ltac:(lia)))))
as (colidx & Hcolidx & Hxlen).
assert (Zf : zlen frequ = TS0) by (unfold zlen; rewrite Hflen; apply Z2Nat.id; lia).
assert (Zk : zlen keys = 3 * TS0) by (unfold zlen; rewrite Hklen; apply Z2Nat.id; lia).
assert (Zx : zlen colidx = TS0) by (unfold zlen; rewrite Hxlen; apply Z2Nat.id; lia).
pose (C0 := mkCHT c f h u p x TS0 h u TS0 (ht_init TS0 frequ keys colidx) []).
lazymatch goal with |- SR _ (mkCfg (mkst ?regsF _ _ _) _) _ => apply (KHL regsF Lc Ac memF mdc 0 pnew fimg imgl C0) end.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
assert (HU2f : bv_unsigned (ew Ef 2) = sp0 - 5168) by (ew_havoc; exact HU2);
assert (HUcf : bv_unsigned (ew Ef 20) = c) by (ew_havoc; exact HU20);
pose proof (fun off n e v Hin => st_chunk_val ubs2segs Ef ssf msf 0%nat _ 20%nat off n e c v HS eq_refl eq_refl Hin HUcf) as VF;
pose proof (fun off n e v Hin => st_chunk_val ubs2segs Ef ssf msf 1%nat _ 2%nat off n e (sp0 - 5168) v HS eq_refl eq_refl Hin HU2f) as WF
end.
cbn [ms_mem mkst] in VF, WF. fold memF in VF, WF.
assert (SLOT : forall off e v, In (mkChunk off (CVal 8 e)) (r_chunks (nth 1 (ss_mem ltac:(lazymatch type of HS with st_ok _ _ ?ssf _ => exact ssf end)) (YQ0b.mkRegion None 0 0 0 0 []))) ->
sv_denot ltac:(lazymatch type of HS with st_ok _ ?Ef _ _ => exact Ef end) e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> slot regs0 memF off v).
{ intros off e v Hin He Hv. unfold slot. apply (proj1 (val_mem_word_mem ubs2segs _ _ _)). rewrite Hspv.
apply (WF off 8%N e v Hin He); [exact Hv | cbn; lia]. }
split.
{ split; [exact HJ3|]. split; [exact Hinit|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc _ (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x0 Hx Hlx; apply KH11; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros i Hi. apply KH11; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [exact Hfmt|]. split; [lia|]. split; [left; reflexivity|].
split. {
split; [jreg HS (9%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; exact Hq|].
split; [jreg HS (18%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq; exact HE39|].
split; [jreg HS (19%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; exact Hq|].
split; [jreg HS (20%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; cbn [ch_c C0]; rewrite Hq, (HE 20%nat 20%bv eq_refl); exact G20|].
split; [jreg HS (8%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 8%nat 8%bv eq_refl); exact G8|].
jreg HS (21%bv:reg) as Hq; cbn [ms_regs mkst] in Hq; rewrite Hq, (HE 21%nat 21%bv eq_refl); exact G21. }
split. {
split; [apply (SLOT 8 (SOff 27 0) N); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE27 | lia]|].
split; [apply (SLOT 16 (SOff 26 0) cfp); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; rewrite (HE 26%nat 26%bv eq_refl); exact G26 | lia]|].
split; [apply (SLOT 24 (SOff 18 0) pnew); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; rewrite (HE 18%nat 18%bv eq_refl); exact G18 | lia]|].
apply (SLOT 48 (SOff 9 0) fimg); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; rewrite (HE 9%nat 9%bv eq_refl); exact G9 | lia]. }
split; [apply (SLOT 32 (SLit 65280) 65280); [cbv; tauto | reflexivity | lia]|].
split; [apply (SLOT 40 (SOff 39 0) fmt); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE39 | lia]|].
split; [apply (SLOT 56 (SOff 27 0) N); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE27 | lia]|].
split; [apply (SLOT 64 (SLit 1) 1); [cbv; tauto | reflexivity | lia]|].
split; [apply (SLOT 80 (SLit 4294967295) (2 ^ 32 - 1)); [cbv; tauto | reflexivity | lia]|].
split; [apply (SLOT 112 (SOff 39 0) fmt); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE39 | lia]|].
split; [apply (SLOT 120 (SOff 40 0) img); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE40 | lia]|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 32); [exact Hfc | reflexivity |]. intros i Hi. apply KH11; unfold OFF_fcfg; lia. }
split; [exact (RGK _ KB11)|]. split; [exact (CGK _ KB11)|]. split; [exact (IMK _ KB11)|].
split. {
split. { cbn [ch_c ch_f ch_hS ch_uS ch_p ch_x ch_H ch_TS C0]. cbn [ht_cnt ht_init].
cbn [obj_at LAY_Cht]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [apply (VF 0 8%N (SOff 32 0) f); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE32 | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 8 8%N (SOff 33 0) h); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE33 | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 16 8%N (SOff 34 0) u); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE34 | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 24 8%N (SOff 35 0) p); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE35 | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 32 8%N (SOff 10 0) x); [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE10 | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 40 4%N (SLit 0) 0); [cbv; tauto | reflexivity | lia | cbn; lia] | lia]|].
split; [split; [apply (VF 44 4%N (SLit 524309) TS0); [cbv; tauto | reflexivity | rewrite HTS0; lia | cbn; lia] | rewrite HTS0; lia]|].
exact I. }
split. { cbn [ch_f ch_h ch_u ch_p ch_x ch_H C0]. unfold cht_arrays. cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx ht_init].
split; [exact Hfrequ|]. split; [exact Hkeys|]. split; [apply arr8_zero; exact Zu11|]. split; [apply arr8_zero; exact Zp11 | exact Hcolidx]. }
split; [cbn [ch_H ch_ent C0]; apply ht_init_inv; [lia | exact Zf | exact Zk | exact Zx | exact (arr8_Forall _ _ _ _ Hkeys)]|].
split; [cbn [ch_H ch_T C0 ht_T ht_init]; reflexivity|].
split; [cbn [ch_T C0]; unfold ts_chain; left; reflexivity|].
cbn [ch_hS ch_uS ch_TS C0]. rewrite HTS0. lia. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [change (zsum (map snd (ch_ent C0))) with 0; lia|].
split; [exact Hpnz|]. split; [exact Hfnz|].
cbn [cht_blks cht_blocks ch_c ch_f ch_h ch_u ch_p ch_x ch_T C0]. subst KEEP. rewrite <- app_assoc in HBkt. exact HBkt.
Qed.
Theorem ubs2_rgbadd_E2 : seg_E2 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KHL KX38 KXB.
exact (ubs2_rgbadd_E2a API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
(ubs2_rgbadd_E2b KHL KX38) KXB).
Qed.
End q.
End d.

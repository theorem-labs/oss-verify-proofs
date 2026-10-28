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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI04
UI1e UI39 UI1i UI57 UI1h YI0x UI16 UI11
YI07 YP14 YI08 YI0c YI0g UI3h UI3d UI4v UIZm.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export UI4t.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition FIN_RETAF : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1608).
Definition FIN_RETFR : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1618).
Definition PC_FIN2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x15f0).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition fcfg_chunks : list YQ0b.chunk :=
[ mkChunk 128 (CVal 8 (SOff 44 0)); mkChunk 136 (CVal 8 (SOff 45 0)); mkChunk 144 (CVal 4 (SOff 46 0));
mkChunk 148 (CVal 4 (SOff 47 0)); mkChunk 152 (CVal 2 (SOff 48 0)); mkChunk 154 (CVal 2 (SOff 49 0));
mkChunk 156 (CVal 1 (SOff 50 0)) ].
Definition ss_FIN : sstate :=
mkSS PC_FIN2 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 128 166 128 160 fcfg_chunks ;
YQ0b.mkRegion (Some 8%nat) 0 RGB_SIZE 48 60 (obj_chunks_from LAY_Rgb 32) ;
YQ0b.mkRegion (Some 19%nat) 0 RGBFC_SIZE 0 0 (obj_chunks_from LAY_RgbFrameConfig 51) ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (8%nat, mkAF 4096 (CEIL_MAX - RGB_SIZE) 4);
(19%nat, mkAF CEIL_MIN (2^63 - RGBFC_SIZE) 3);
(9%nat, mkAF 0 255 0); (12%nat, mkAF 2 4 0); (11%nat, mkAF 1 9 0); (46%nat, mkAF 1 9 0); (52%nat, mkAF 3 4 0) ] [] []).
Definition ss_FINa : sstate :=
mkSS PC_FIN sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 154 156 [mkChunk 16 (CVal 8 (SOff 32 0)); mkChunk 64 (CVal 8 (SOff 33 0)); mkChunk 144 (CVal 4 (SOff 34 0))] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (9%nat, mkAF 0 255 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 1 9 0) ] [] []).
Section e.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis ADDF : forall fx', addframe_specG (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Definition at_FIN2 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg sizeLCT : Z) : Prop :=
rgba_inv (fx:=fx) API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc mdc /\ rgba_regs regs0 regs1 /\
(fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ 0 <= sizeLCT <= 255 /\
getr regs1 12 = Z_to_bv 64 (if ha =? 1 then FATTR_HAS_ALPHA else FATTR_HAS_SET_TRANS) /\ getr regs1 11 = Z_to_bv 64 (fattr1 fattr) /\
getr regs1 9 = Z_to_bv 64 sizeLCT /\ getr regs1 8 = Z_to_bv 64 r /\ getr regs1 18 = Z_to_bv 64 pnew /\
getr regs1 19 = Z_to_bv 64 cfp /\
slots_mid regs0 cfp N memc pnew fimg /\
fcfg_at regs0 fattr delay memc fimg sizeLCT 0 /\ rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur memc /\ cgif_at memc g s /\
(forall i, 0 <= i < 768 -> exists b, mbyte ubs2segs memc (sp regs0 + OFF_apal + i) = Some b) /\
pnew <> 0 /\ fimg <> 0 /\
Permutation (blocks Lc Ac) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]).
Section h.
Context {fxi : YK11.FPState}.
Lemma FIN2_at : forall regs1 Lc Ac memc mdc ha pnew fimg sizeLCT,
K_XF (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_FIN2 regs1 Lc Ac memc mdc ha pnew fimg sizeLCT ->
SR ubs2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_FIN2) memc (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg sizeLCT KXF HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & Hsz & G12 & G11 & G9 & G8 & G18 & G19 & Hsl & Hfc & Hobj & Hcg & Hapal & Hpnew & Hfimg & HB).
pose proof Hsl as (S8 & S16 & S24 & S48).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HHt & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HRFCv : RGBFC_SIZE = 24) by reflexivity. assert (HAFv : ADDFRAME_STK = 9728) by reflexivity.
pose proof Hal0 as Hal16. unfold UI4v.sp0 in Hal16, Hclo, Hceil, H63, Hstw, HJ.
set (sp0 := spZ regs0) in *. assert (Hsp0 : sp0 = spZ regs0) by reflexivity.
assert (Hspv : sp regs0 = sp0 - 5168) by (unfold sp, UI4v.sp0, RGBA_FRAME; lia).
rewrite Hspv in *.
assert (Hsp16 : (sp0 - 5168) mod 16 = 0).
{ replace (sp0 - 5168) with (sp0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal16 | lia]. }
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE HHc Hrin ltac:(lia)) as (Rr0 & Rr1 & Rr16).
assert (HfN : 0 < fmt * N) by (clear - Hfmt HN1; nia).
assert (Hpin : In (pnew, fmt * N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc pnew (fmt * N) HHc Hpin HfN) as (Rp0 & Rp1 & _).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rrgb.
pose proof (Rrgb 0%nat g eq_refl) as Rg. pose proof (Rrgb 9%nat bef eq_refl) as Rbef. pose proof (Rrgb 10%nat beffmt eq_refl) as Rbeffmt. pose proof (Rrgb 11%nat cur eq_refl) as Rcur.
cbn in Rg, Rbef, Rbeffmt, Rcur.
pose proof (obj_at_range _ _ _ _ _ Hcfp) as Rcfg. pose proof (Rcfg 1%nat fmt eq_refl) as Rfmt. cbn in Rfmt.
pose proof Hfc as Hfc'. unfold fcfg_at, OFF_fcfg, OFF_apal in Hfc'. rewrite Hspv in Hfc'.
pose proof (obj_at_range _ _ _ _ _ Hfc') as Rfc. pose proof (Rfc 1%nat fimg eq_refl) as Rfimg. pose proof (Rfc 4%nat delay eq_refl) as Rdelay. cbn in Rfimg, Rdelay.
set (av := if ha =? 1 then FATTR_HAS_ALPHA else FATTR_HAS_SET_TRANS) in G12.
assert (Hav : av = 2 \/ av = 4) by (subst av; unfold FATTR_HAS_ALPHA, FATTR_HAS_SET_TRANS; destruct (ha =? 1); lia).
assert (Hf1 : fattr1 fattr = 1 \/ fattr1 fattr = 9) by (unfold fattr1; destruct (Z.land fattr 1 =? 0); lia).
set (f1 := fattr1 fattr) in *.
set (rgbv := [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cur]) in *.
set (fcv := [sp0 - 5168 + 166; fimg; f1; 0; delay; sizeLCT; 0]) in *.
set (cfgv := [img; fmt; fattr; fgen; delay]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (rgbv ++ fcv ++ cfgv) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (rgbv ++ fcv ++ cfgv) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE32 : ew E 32 = Z_to_bv 64 g) by (apply (HV 0%nat); reflexivity).
assert (HE41 : ew E 41 = Z_to_bv 64 bef) by (apply (HV 9%nat); reflexivity).
assert (HE43 : ew E 43 = Z_to_bv 64 cur) by (apply (HV 11%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 (sp0 - 5168 + 166)) by (apply (HV 12%nat); reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 fimg) by (apply (HV 13%nat); reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 f1) by (apply (HV 14%nat); reflexivity).
assert (HE47 : ew E 47 = Z_to_bv 64 0) by (apply (HV 15%nat); reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 delay) by (apply (HV 16%nat); reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 sizeLCT) by (apply (HV 17%nat); reflexivity).
assert (HE50 : ew E 50 = Z_to_bv 64 0) by (apply (HV 18%nat); reflexivity).
assert (HE52 : ew E 52 = Z_to_bv 64 fmt) by (apply (HV 20%nat); reflexivity).
assert (HE9 : ew E 9 = Z_to_bv 64 sizeLCT) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE11 : ew E 11 = Z_to_bv 64 f1) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HE12 : ew E 12 = Z_to_bv 64 av) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HE18 : ew E 18 = Z_to_bv 64 pnew) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 5168) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = r) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU19 : bv_unsigned (ew E 19) = cfp) by (rewrite (HE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; lia).
pose proof Hfc' as Hq. cbn [obj_at LAY_FrameConfig] in Hq. unfold field_ok in Hq. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in Hq.
destruct Hq as ((F0 & _) & (F1 & _) & (F2 & _) & (F3 & _) & (F4 & _) & (F5 & _) & (F6 & _) & _).
assert (HS : st_ok (fx:=fxi) ubs2segs E ss_FIN (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_FIN2) memc (seg_rom ubs2segs))).
{ unfold ss_FIN. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold fcfg_chunks.
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (sp0 - 5168 + 166)); [cbn [sv_denot]; rewrite Z.add_0_r, HE44, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 5168 + 128) with (sp0 - 5168 + 128 + 0) by lia; exact F0]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ fimg); [cbn [sv_denot]; rewrite Z.add_0_r, HE45, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 5168 + 136) with (sp0 - 5168 + 128 + 8) by lia; exact F1]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ f1); [cbn [sv_denot]; rewrite Z.add_0_r, HE46, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 5168 + 144) with (sp0 - 5168 + 128 + 16) by lia; exact F2]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [cbn [sv_denot]; rewrite Z.add_0_r, HE47, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 5168 + 148) with (sp0 - 5168 + 128 + 20) by lia; exact F3]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ delay); [cbn [sv_denot]; rewrite Z.add_0_r, HE48, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 5168 + 152) with (sp0 - 5168 + 128 + 24) by lia; exact F4]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ sizeLCT); [cbn [sv_denot]; rewrite Z.add_0_r, HE49, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 5168 + 154) with (sp0 - 5168 + 128 + 26) by lia; exact F5]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [cbn [sv_denot]; rewrite Z.add_0_r, HE50, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 5168 + 156) with (sp0 - 5168 + 128 + 28) by lia; exact F6]. }
apply Forall_nil.
+ eapply (region_ok_obj ubs2segs _ memc 8 r); [exact HU8 | lia | lia | exact Hobj | reflexivity | | ].
* intros j v Hj. apply (Ereg_vals regs1 _ [] j v). rewrite nth_error_app1; [exact Hj | apply nth_error_Some; subst rgbv; congruence].
* intros i Hi. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE i HHc Hrin ltac:(unfold RGB_SIZE; lia))).
+ eapply (region_ok_obj ubs2segs _ memc 19 cfp); [exact HU19 | lia | lia | exact Hcfp | reflexivity | | intros i Hi; lia].
intros j v Hj. replace (51 + j)%nat with (32 + (length (rgbv ++ fcv) + j))%nat by (subst rgbv fcv; cbn; lia).
apply (Ereg_vals regs1 _ [] (length (rgbv ++ fcv) + j)%nat v). rewrite app_assoc, nth_error_app2 by lia.
replace (length (rgbv ++ fcv) + j - length (rgbv ++ fcv))%nat with j by lia. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HU19. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU19, HE9, HE12, HE11, HE46, HE52, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_FIN2) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cgif_addframe.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_block; [reflexivity | exact HU8 | exact Hrin | cbn; lia | cbn; unfold RGB_SIZE; lia | | apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]].
intros a Ha. cbn [r_wlo r_whi] in Ha. exists (r, r + RGB_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold RGB_SIZE; lia]. }
cbn [ms_mem mkst] in HF, HG.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 + 128 <= a < sp0 - 5168 + 160) -> ~ (r + 48 <= a < r + 60) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hn1 Hn2. mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU19; lia]. }
assert (Hsepr : forall b m, In (b, m) (cgif_blocks g s N ++ optb bef (beffmt * N) ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N); (fimg, N)]) ->
r + RGB_SIZE <= b \/ b + m <= r).
{ intros b m Hbm. pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (r, RGB_SIZE) _ (b, m) HHc ltac:(eapply Permutation_trans; [exact HB|]; unfold BASE; cbn [app]; rewrite <- !app_assoc; apply Permutation_refl) Hbm) as Hs.
cbn [fst snd] in Hs. lia. }
assert (KB1 : forall b m i, In (b, m) (cgif_blocks g s N ++ optb bef (beffmt * N) ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N); (fimg, N)]) -> 0 <= i < m ->
mbyte ubs2segs (ms_mem ms) (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. pose proof (Hsepr b m Hbm) as Hs.
destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB|]; unfold BASE; cbn [app]; right; rewrite <- !app_assoc; exact Hbm)) as [Hb0 Hb1].
apply K1; unfold RGB_SIZE in Hs; lia. }
pose proof (st_region_chunks ubs2segs _ _ _ 0%nat _ 2%nat (sp0 - 5168) HS eq_refl eq_refl HU2) as HC0. cbn [r_chunks] in HC0.
pose proof (fun c Hc => proj1 (Forall_forall _ _) HC0 c Hc) as CH.
clear HF HG.
set (nattr := Z.lor f1 av).
assert (Hnattr : 0 <= nattr < 16) by (subst nattr; destruct Hf1 as [-> | ->]; destruct Hav as [-> | ->]; cbv; split; congruence).
assert (Unattr : U E (SAlu ALU_OR (SOff 11 0) (SOff 12 0)) = nattr).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 11 f1 HE11), (U_atom E 12 av HE12) by lia. apply zcanon_id. unfold M64. lia. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hfc2 : obj_at ubs2segs (ms_mem msx) (sp0 - 5168 + 128) LAY_FrameConfig [sp0 - 5168 + 166; fimg; nattr; 0; delay; sizeLCT; sizeLCT]) end.
{ cbn [obj_at LAY_FrameConfig]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 0) with (sp0 - 5168 + 128) by lia.
eapply (val_of_chunk_ok ubs2segs E _ (sp0 - 5168) 128 8%N (SOff 44 0) (sp0 - 5168 + 166)); [exact (CH (mkChunk 128 (CVal 8 (SOff 44 0))) ltac:(cbv; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE44 | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 8) with (sp0 - 5168 + 136) by lia.
eapply (val_of_chunk_ok ubs2segs E _ (sp0 - 5168) 136 8%N (SOff 45 0) fimg); [exact (CH (mkChunk 136 (CVal 8 (SOff 45 0))) ltac:(cbv; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE45 | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 16) with (sp0 - 5168 + 144) by lia.
pose proof (val_mem_low_of_chunk ubs2segs E _ (sp0 - 5168) 144 4%N _ (CH (mkChunk 144 (CVal 4 (SAlu ALU_OR (SOff 11 0) (SOff 12 0)))) ltac:(cbv; tauto)) ltac:(cbn; lia)) as V.
change (bv_unsigned (sv_denot E (SAlu ALU_OR (SOff 11 0) (SOff 12 0)))) with (U E (SAlu ALU_OR (SOff 11 0) (SOff 12 0))) in V.
rewrite Unattr in V. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V. rewrite Z.mod_small in V by lia. exact V. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 20) with (sp0 - 5168 + 148) by lia.
eapply (val_of_chunk_ok ubs2segs E _ (sp0 - 5168) 148 4%N (SOff 47 0) 0); [exact (CH (mkChunk 148 (CVal 4 (SOff 47 0))) ltac:(cbv; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE47 | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 24) with (sp0 - 5168 + 152) by lia.
eapply (val_of_chunk_ok ubs2segs E _ (sp0 - 5168) 152 2%N (SOff 48 0) delay); [exact (CH (mkChunk 152 (CVal 2 (SOff 48 0))) ltac:(cbv; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE48 | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 26) with (sp0 - 5168 + 154) by lia.
eapply (val_of_chunk_ok ubs2segs E _ (sp0 - 5168) 154 2%N (SOff 49 0) sizeLCT); [exact (CH (mkChunk 154 (CVal 2 (SOff 49 0))) ltac:(cbv; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE49 | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 28) with (sp0 - 5168 + 156) by lia.
eapply (val_of_chunk_ok ubs2segs E _ (sp0 - 5168) 156 1%N (SOff 9 0) sizeLCT); [exact (CH (mkChunk 156 (CVal 1 (SOff 9 0))) ltac:(cbv; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE9 | cbn; lia | cbn; lia]. }
exact I. }
jreg HS (10%bv:reg) as Ha0. rewrite HE32 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite HU2 in Ha1.
jreg HS (2%bv:reg) as Ha2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Ha2.
jreg HS (4%bv:reg) as Ha4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Ha4.
jreg HS (1%bv:reg) as Hra1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hspms : spZ (ms_regs msx) = sp0 - 5168) by (unfold spZ; rewrite Ha2; apply unsigned_lit_small; lia) end.
set (restF := (r, RGB_SIZE) :: optb bef (beffmt * N) ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N)]).
assert (HBc : Permutation (blocks Lc Ac) (cgif_blocks g s N ++ (fimg, N) :: restF)).
{ eapply Permutation_trans; [exact HB|]. unfold BASE. subst restF.
cbn [app]. rewrite <- !app_assoc. cbn [app].
apply (Permutation_trans (l' := (fimg, N) :: (r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef (beffmt * N) ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N)])).
- eapply Permutation_trans; [| apply perm_swap]. apply perm_skip.
replace (cgif_blocks g s N ++ optb bef (beffmt * N) ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N); (fimg, N)])
with ((cgif_blocks g s N ++ optb bef (beffmt * N) ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N)]) ++ [(fimg, N)]) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_sym, Permutation_cons_append.
- eapply Permutation_trans; [| apply Permutation_middle]. apply perm_skip. apply Permutation_middle. }
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := ADDFRAME_STK) (FP1 := blocks_fp (cgif_blocks g s N))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) =>
st_init_done A5 = true /\ exists s' : cgif_st, cgif_at mem5 g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
Permutation (blocks L5 A5) (cgif_blocks g s' N ++ (fimg, N) :: restF));
[ exact HS | reflexivity | exact HJ | exact Hra1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; lia
| rewrite Hspms; lia | exact Ha4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (ADDF fxi Lc Ac _ _ mdc g (sp0 - 5168 + 128) s N (sp0 - 5168 + 166) fimg nattr 0 delay sizeLCT sizeLCT restF HPRE1 Hinit Ha0);
[ rewrite Ha1; f_equal; lia | destruct (proj1 (Z.mod_divide (sp0 - 5168) 16 ltac:(lia)) Hsp16) as [kq Hkq]; rewrite Hkq; replace (kq * 16 + 128) with ((kq * 2 + 16) * 8) by lia; apply Z_mod_mult | rewrite Hspms; lia | lia | exact Hfc2 | | exact Hwf | | exact HBc].
- eapply (cgif_at_kept _ _ g s N (cgif_blocks g s N ++ optb bef (beffmt * N) ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N); (fimg, N)])); [| exact Hcg | exact KB1].
apply Permutation_refl.
- unfold pal_ok. intros _. rewrite Hspms. split; [lia|]. split; [lia|]. intros i Hi. rewrite K1 by lia. apply Hapal. lia. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & s' & -> & HJc5 & HP5 & Hinit5 & Hat5 & Hwf5 & HW5 & HH5 & Hattr5 & Hraw5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hra1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5|].
split; [exact Hinit5|]. exists s'. repeat (split; [assumption|]). exact HB5.
- intros a Ha. left. split.
+ destruct Ha as (rr & Hrr & Harr). exists rr. split; [right; apply in_app_iff; left; exact Hrr | exact Harr].
+ apply inFP_blocks_fp in Ha as (b & n & Hbn & Habn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc b n HHc ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; left; unfold BASE; right; apply in_app_iff; left; exact Hbn)) as [_ R1]. lia. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & Hinit5 & s' & Hat5 & Hwf5 & HW5 & HH5 & Hattr5 & Hraw5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5, Hat5.
pose proof HJc5 as (HHc5 & _ & Hhi5 & Hblk5 & _). rewrite Hspms in Hhi5.
rewrite HW in HW5. rewrite HHt in HH5. pose proof (proj1 HJ5) as HH5'.
assert (Hrin5 : In (r, RGB_SIZE) (blocks L5 A5)) by (eapply Permutation_in; [apply Permutation_sym; exact HB5|]; apply in_app_iff; right; right; left; reflexivity).
assert (KR5 : forall i, 0 <= i < RGB_SIZE -> mbyte ubs2segs mem5 (r + i) = mbyte ubs2segs (ms_mem ms) (r + i)).
{ intros i Hi. apply (Hblk5 r RGB_SIZE i Hrin Hrin5 Hi). intros HF1.
apply inFP_blocks_fp in HF1 as (b & n & Hbn & Habn).
pose proof (Hsepr b n ltac:(apply in_app_iff; left; exact Hbn)) as Hs.
destruct (blocks_range _ _ LAWS Lc Ac memc mdc b n HHc ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; left; unfold BASE; right; apply in_app_iff; left; exact Hbn)) as [Rb0 Rb1].
unfold RGB_SIZE in Hs. lia. }
assert (KH5 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 <= x -> mbyte ubs2segs mem5 x = mbyte ubs2segs (ms_mem ms) x).
{ intros x Hx Hlx. apply (proj1 (Hhi5 x Hx ltac:(lia))). }
jafter_call_keep HS 56%nat regs5 mem5 HP5 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi5 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_live_blk MR LAWS _ _ _ 8); [exact HU8 | exact HH5' | exact Hrin5 | exact KR5 | cbn; lia | cbn; unfold RGB_SIZE; lia | cbn; lia | cbn; unfold RGB_SIZE; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 19); [exact HU19 | exact Hhi5 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS Ha0 Ha1 Ha2 Ha4 Hra1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ5 ubs2_A_free.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_block; [reflexivity | ew_havoc; exact HU8 | exact Hrin5 | cbn; lia | cbn; unfold RGB_SIZE; lia | | apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]].
intros a Ha. cbn [r_wlo r_whi] in Ha. exists (r, r + RGB_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold RGB_SIZE; lia]. }
cbn [ms_regs ms_mem mkst] in HF, HG.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 + 128 <= a < sp0 - 5168 + 160) -> ~ (r + 48 <= a < r + 60) ->
mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem5 a)
by (intros a Ha Hn1 Hn2; mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU19; lia]) end.
clear HF HG.
jreg HS (10%bv:reg) as Fq10. rewrite HE41 in Fq10.
jreg HS (2%bv:reg) as Fq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Fq2.
jreg HS (4%bv:reg) as Fq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Fq4.
jreg HS (1%bv:reg) as Fq1.
set (rest6 := cgif_blocks g s' N ++ (fimg, N) :: (r, RGB_SIZE) :: img_block img fmt N ++ rest ++ [(pnew, fmt * N)]).
assert (HB5' : Permutation (blocks L5 A5) (optb bef (beffmt * N) ++ rest6)).
{ eapply Permutation_trans; [exact HB5|]. subst restF rest6.
replace (cgif_blocks g s' N ++ (fimg, N) :: (r, RGB_SIZE) :: optb bef (beffmt * N) ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N)])
with ((cgif_blocks g s' N ++ [(fimg, N); (r, RGB_SIZE)]) ++ optb bef (beffmt * N) ++ (img_block img fmt N ++ rest ++ [(pnew, fmt * N)])) by (rewrite <- !app_assoc; reflexivity).
replace (optb bef (beffmt * N) ++ cgif_blocks g s' N ++ (fimg, N) :: (r, RGB_SIZE) :: img_block img fmt N ++ rest ++ [(pnew, fmt * N)])
with (optb bef (beffmt * N) ++ (cgif_blocks g s' N ++ [(fimg, N); (r, RGB_SIZE)]) ++ (img_block img fmt N ++ rest ++ [(pnew, fmt * N)])) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_app_swap_app. }
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API))
with (p := bef) (n := beffmt * N) (rest := rest6) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ5 | exact HB5'
| exact Fq10 | exact Fq2 | lia | exact Hsp16 | lia | lia | exact Fq4 | exact Fq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hb0 _ i Hi. exists (bef, bef + beffmt * N). split; [| cbn; lia].
right. apply in_app_iff. right. unfold optfp. rewrite (proj2 (Z.eqb_neq _ _) Hb0). left. reflexivity. }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & HB6 & Hkeep6 & Hhi6). clear HJ5.
lazymatch type of Hkeep6 with context [mbyte _ mem6 _ = mbyte _ (ms_mem ?msx) _] => cbn [ms_regs ms_mem mkst] in HP6, Hkeep6, Hhi6 end.
pose proof (proj1 HJ6) as HH6.
assert (Hrin6 : In (r, RGB_SIZE) (blocks L6 A6)) by (eapply Permutation_in; [apply Permutation_sym; exact HB6|]; subst rest6; apply in_app_iff; right; right; left; reflexivity).
jafter_call_keep HS 72%nat regs6 mem6 HP6 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_live_blk MR LAWS _ _ _ 8); [ew_havoc; exact HU8 | exact HH6 | exact Hrin6 | intros i Hi; exact (Hkeep6 r RGB_SIZE i Hrin6 Hi) | cbn; lia | cbn; unfold RGB_SIZE; lia | cbn; lia | cbn; unfold RGB_SIZE; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 19); [ew_havoc; exact HU19 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS Fq10 Fq2 Fq4 Fq1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ6 PC_XF.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_block; [reflexivity | ew_havoc; exact HU8 | exact Hrin6 | cbn; lia | cbn; unfold RGB_SIZE; lia | | apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]].
intros a Ha. cbn [r_wlo r_whi] in Ha. exists (r, r + RGB_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold RGB_SIZE; lia]. }
cbn [ms_regs ms_mem mkst] in HF, HG, HJ6.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5168 + 128 <= a < sp0 - 5168 + 160) -> ~ (r + 48 <= a < r + 60) ->
mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem6 a)
by (intros a Ha Hn1 Hn2; mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU19; lia]);
pose proof (st_region_chunks ubs2segs _ _ _ 1%nat _ 8%nat r HS eq_refl eq_refl ltac:(ew_havoc; exact HU8)) as HC1
end.
cbn [r_chunks] in HC1. pose proof (fun c Hc => proj1 (Forall_forall _ _) HC1 c Hc) as CH1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KHF : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 160 <= x -> mbyte ubs2segs (ms_mem msx) x = mbyte ubs2segs memc x)
end.
{ intros x Hx Hlx. rewrite K3 by lia. etransitivity; [apply (proj1 (Hhi6 x Hx ltac:(lia)))|]. rewrite K2 by lia. etransitivity; [apply (KH5 x Hx ltac:(lia))|]. apply K1; lia. }
assert (Hsep6 : forall b m, In (b, m) (cgif_blocks g s' N) -> (r + RGB_SIZE <= b \/ b + m <= r) /\ b + m <= alloc_ceiling /\ In (b, m) (blocks L6 A6)).
{ intros b m Hbm.
assert (Hin6 : In (b, m) (blocks L6 A6)) by (eapply Permutation_in; [apply Permutation_sym; exact HB6|]; subst rest6; apply in_app_iff; left; exact Hbm).
pose proof (heap_sep_perm _ _ LAWS L6 A6 mem6 md6 (r, RGB_SIZE) (cgif_blocks g s' N ++ (fimg, N) :: img_block img fmt N ++ rest ++ [(pnew, fmt * N)]) (b, m) HH6
ltac:(eapply Permutation_trans; [exact HB6|]; subst rest6;
replace (cgif_blocks g s' N ++ (fimg, N) :: (r, RGB_SIZE) :: img_block img fmt N ++ rest ++ [(pnew, fmt * N)])
with ((cgif_blocks g s' N ++ [(fimg, N)]) ++ (r, RGB_SIZE) :: (img_block img fmt N ++ rest ++ [(pnew, fmt * N)])) by (rewrite <- app_assoc; reflexivity);
replace ((r, RGB_SIZE) :: cgif_blocks g s' N ++ (fimg, N) :: img_block img fmt N ++ rest ++ [(pnew, fmt * N)])
with ((r, RGB_SIZE) :: (cgif_blocks g s' N ++ [(fimg, N)]) ++ (img_block img fmt N ++ rest ++ [(pnew, fmt * N)])) by (rewrite <- app_assoc; reflexivity);
apply Permutation_sym; apply Permutation_middle)
ltac:(apply in_app_iff; left; exact Hbm)) as Hs.
cbn [fst snd] in Hs. destruct (blocks_range _ _ LAWS L6 A6 mem6 md6 b m HH6 Hin6) as [_ Hb1]. split; [lia | split; [exact Hb1 | exact Hin6]]. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 82600) with (Z_to_bv 64 PC_XF).
lazymatch goal with |- SR _ (mkCfg (mkst ?regsx _ ?memx _) _) _ =>
apply (KXF fxi regsx L6 A6 memx md6 (bv_unsigned (getr regs5 10)) fimg N s' pnew fmt cur HFRM) end.
pose proof (bv_unsigned_in_range 64 (getr regs5 10)) as Rres. change (bv_modulus 64) with (2 ^ 64) in Rres.
split.
{ split; [exact HJ6|].
split. { apply blocks_In in Hrin6 as (q & _ & Hq). exact (init_done_of_block A6 (q, RGB_SIZE) (proj1 (proj2 HH6)) Hq). }
split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc _ (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x Hx Hlx; apply KHF; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros i Hi. apply KHF; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [lia|].
split; [jreg HS (9%bv:reg) as Hq; rewrite Hq; exact HE45|].
split. { jreg HS (21%bv:reg) as Hq. rewrite Hq, Z_to_bv_bv_unsigned. change 60%nat with (56 + 4)%nat.
rewrite (ew_havoc_new E 56 _ 4 (Z_to_bv 64 0)) by (cbn; lia). reflexivity. }
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 8%nat 8%bv eq_refl); exact G8|].
split. {
lazymatch goal with |- rgb_obj2 _ _ _ _ _ _ _ _ _ _ ?memx _ _ _ =>
eapply (obj_at_upd ubs2segs memc memx r LAY_Rgb RGB_SIZE rgbv _ [9%nat; 10%nat] [(48, 56); (56, 60)]);
[exact Hobj | reflexivity | reflexivity | reflexivity | | | ] end.
- intros i Hi Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. unfold RGB_SIZE in Hi.
rewrite K3 by lia. etransitivity; [apply (Hkeep6 r RGB_SIZE i Hrin6 ltac:(unfold RGB_SIZE; lia))|]. rewrite K2 by lia. etransitivity; [apply KR5; unfold RGB_SIZE; lia|]. apply K1; lia.
- intros j f v' Hj Hf Hv'. cbv [In] in Hj. destruct Hj as [<- | [<- | []]]; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
+ split; [| lia]. eapply (val_of_chunk_ok ubs2segs _ _ r 48 8%N (SOff 18 0) pnew); [exact (CH1 (mkChunk 48 (CVal 8 (SOff 18 0))) ltac:(cbv; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE18 | cbn; lia | cbn; lia].
+ split; [| lia]. eapply (val_of_chunk_ok ubs2segs _ _ r 56 4%N (SOff 52 0) fmt); [exact (CH1 (mkChunk 56 (CVal 4 (SOff 52 0))) ltac:(cbv; tauto)) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE52 | cbn; lia | cbn; lia].
- intros j Hj. do 12 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; tauto] |]). reflexivity. }
split. { eapply (cgif_at_kept _ _ g s' N (cgif_blocks g s' N)); [rewrite app_nil_r; apply Permutation_refl | exact Hat5 |].
intros b m i Hbm Hi. destruct (Hsep6 b m Hbm) as (Hs & Hb1 & Hin6).
destruct (blocks_range _ _ LAWS L6 A6 mem6 md6 b m HH6 Hin6) as [Hb0 _].
rewrite K3 by (unfold RGB_SIZE in Hs; lia). etransitivity; [apply (Hkeep6 b m i Hin6 Hi)|]. apply K2; unfold RGB_SIZE in Hs; lia. }
split; [exact Hwf5|]. split; [exact HW5|]. split; [exact HH5|]. split; [exact Hattr5|]. split; [exact Hraw5|].
split; [right; exact Hfmt|]. split; [exact Hfimg|].
split. { refine (proj2 (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N)]) [(fimg, N)] fimg N
HHc _ HBent ltac:(intros x1 Hx1; apply in_app_iff; left; exact Hx1) ltac:(left; reflexivity) ltac:(lia))).
eapply Permutation_trans; [exact HB|]. rewrite <- app_assoc. apply Permutation_refl. }
eapply Permutation_trans; [exact HB6|]. subst rest6. unfold BASE. rewrite (optb_nz pnew (fmt * N) Hpnew).
cbn [app]. rewrite <- !app_assoc. cbn [app].
apply (Permutation_trans (l' := (fimg, N) :: (r, RGB_SIZE) :: cgif_blocks g s' N ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N)])).
- replace (cgif_blocks g s' N ++ (fimg, N) :: (r, RGB_SIZE) :: img_block img fmt N ++ rest ++ [(pnew, fmt * N)])
with ((cgif_blocks g s' N ++ [(fimg, N)]) ++ (r, RGB_SIZE) :: (img_block img fmt N ++ rest ++ [(pnew, fmt * N)])) by (rewrite <- app_assoc; reflexivity).
eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
rewrite <- app_assoc. cbn [app]. eapply Permutation_trans; [| apply perm_swap]. apply perm_skip. apply Permutation_sym, Permutation_middle.
-
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
apply (Permutation_trans (l' := (pnew, fmt * N) :: (fimg, N) :: cgif_blocks g s' N ++ img_block img fmt N ++ rest)).
+ replace (cgif_blocks g s' N ++ img_block img fmt N ++ rest ++ [(pnew, fmt * N)]) with ((cgif_blocks g s' N ++ img_block img fmt N ++ rest) ++ [(pnew, fmt * N)]) by (rewrite <- !app_assoc; reflexivity).
eapply Permutation_trans; [apply perm_skip; apply Permutation_sym, Permutation_cons_append|]. apply perm_swap.
+ eapply Permutation_trans; [| apply Permutation_middle]. apply perm_skip. rewrite !app_assoc. apply Permutation_cons_append.
Qed.
Lemma FIN_at : forall regs1 Lc Ac memc mdc ha pnew fimg sizeLCT,
K_XF (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_FIN (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg sizeLCT ->
SR ubs2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_FIN) memc (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg sizeLCT KXF HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & Hsz & G9 & G18 & G8 & Hsl & S64 & Hfc & Hobj & Hcg & Hapal & Hpnew & Hfimg & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HHt & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof Hsl as (S8 & S16 & S24 & S48).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (Hnha : nha ha = 0 \/ nha ha = 1) by (unfold nha; destruct (ha =? 0); [right | left]; reflexivity).
assert (Hf1 : fattr1 fattr = 1 \/ fattr1 fattr = 9) by (unfold fattr1; destruct (Z.land fattr 1 =? 0); lia).
set (E := Ereg regs1 (map (Z_to_bv 64) [cfp; nha ha; fattr1 fattr] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (B32 : ew E 32 = Z_to_bv 64 cfp) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (B33 : ew E 33 = Z_to_bv 64 (nha ha)) by (subst E; apply (Ereg_vals regs1 _ [] 1%nat); reflexivity).
assert (B34 : ew E 34 = Z_to_bv 64 (fattr1 fattr)) by (subst E; apply (Ereg_vals regs1 _ [] 2%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE9 : ew E 9 = Z_to_bv 64 sizeLCT) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (F2a : val_mem ubs2segs memc (sp regs0 + 144) 4 (fattr1 fattr)).
{ pose proof Hfc as Hq. unfold fcfg_at, OFF_fcfg, OFF_apal in Hq. cbn [obj_at LAY_FrameConfig] in Hq. unfold field_ok in Hq.
cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in Hq.
destruct Hq as (_ & _ & (F2 & _) & _). replace (sp regs0 + 144) with (sp regs0 + 128 + 16) by lia. exact F2. }
assert (HS : st_ok (fx:=fxi) ubs2segs E ss_FINa (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_FIN) memc (seg_rom ubs2segs))).
{ unfold ss_FINa. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [intros o Ho; apply Hstw; unfold sp, sp0, RGBA_FRAME in *; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, B32, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold sp0, RGBFC_SIZE in *; lia | cbn; lia | apply val_mem_word_mem; exact S16].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, B33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S64].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, B34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F2a].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE9, B33, B34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_FIN) memc (seg_rom ubs2segs))) in HJ.
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
clearbody E.
assert (FINPACK : forall ss ms', st_ok (fx:=fxi) ubs2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = PC_FIN2 ->
journal ubs2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms') mdc ->
(forall x0, 0 <= x0 < 2 ^ 64 -> ~ (sp regs0 + 154 <= x0 < sp regs0 + 156) -> mbyte ubs2segs (ms_mem ms') x0 = mbyte ubs2segs memc x0) ->
val_mem ubs2segs (ms_mem ms') (sp regs0 + 154) 2 sizeLCT ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 9; 8; 18]%bv = true ->
sr_get (ss_regs ss) 19 = SOff 32 0 ->
sr_get (ss_regs ss) 11 = SOff 34 0 ->
getr (ms_regs ms') 12 = Z_to_bv 64 (if ha =? 1 then FATTR_HAS_ALPHA else FATTR_HAS_SET_TRANS) ->
SR ubs2segs (mkCfg ms' mdc) (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest)).
{ intros ss ms' HS' Hrv Hpc HJF FRF Vnl QK Q19 Q11 F12.
pose proof (regs_kept_of_st_ok ubs2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
apply (FIN2_at (ms_regs ms') Lc Ac (ms_mem ms') mdc ha pnew fimg sizeLCT KXF HFRM).
assert (HIF : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 + 156 <= x0 -> mbyte ubs2segs (ms_mem ms') x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hsx. apply FRF; lia. }
assert (KBF : forall b m i, In (b, m) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]) -> 0 <= i < m -> mbyte ubs2segs (ms_mem ms') (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. destruct (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc b m i HHc ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hbm]) Hi) as (_ & B0 & B1 & _).
apply FRF; unfold sp, sp0, RGBA_FRAME in *; lia. }
assert (KS : forall off v, 0 <= off -> off + 8 <= 154 -> slot regs0 memc off v -> slot regs0 (ms_mem ms') off v).
{ intros off v H0 H1 Hs. unfold slot in *. intros k Hk. rewrite FRF by (unfold sp, sp0, RGBA_FRAME in *; lia). apply Hs. exact Hk. }
unfold at_FIN2.
split.
{ split; [exact HJF|]. split; [exact Hinit|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc (ms_mem ms') (sp regs0 + 156)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HIF]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HIF; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split; [split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2 | split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]]|].
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|]. split; [exact Hsz|].
split; [exact F12|].
split. { eapply (getr_of_U ubs2segs); [exact HS'|]. rewrite Q11. apply (U_atom E 34 (fattr1 fattr) B34). lia. }
split; [rewrite (GK 9%bv ltac:(cbv; auto 20)); exact G9|]. split; [rewrite (GK 8%bv ltac:(cbv; auto 20)); exact G8|].
split; [rewrite (GK 18%bv ltac:(cbv; auto 20)); exact G18|].
split. { eapply (getr_of_U ubs2segs); [exact HS'|]. rewrite Q19. apply (U_atom E 32 cfp B32). unfold sp0, RGBFC_SIZE in *. lia. }
split. { unfold slots_mid. unfold SL_N, SL_cfp, SL_new, SL_fimg in *. repeat split; apply KS; (lia || assumption). }
split. { unfold fcfg_at, OFF_fcfg, OFF_apal in *.
eapply (obj_at_upd ubs2segs memc (ms_mem ms') (sp regs0 + 128) LAY_FrameConfig 32 _ _ [5%nat] [(26, 28)] Hfc eq_refl eq_refl); [reflexivity | | |].
- intros i0 Hi0 Hw. apply in_wins_cons_false in Hw as [Hw _]. apply FRF; unfold sp, sp0, RGBA_FRAME in *; lia.
- intros j fd v' Hj Hf Hv'. destruct Hj as [<-|[]]. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-.
split; [cbn [fst snd N.to_nat]; replace (sp regs0 + 128 + 26) with (sp regs0 + 154) by lia; exact Vnl | cbn; lia].
- intros j Hj. do 5 (destruct j as [|j]; [reflexivity|]). destruct j as [|j]; [exfalso; apply Hj; left; reflexivity | reflexivity]. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (KBF r RGB_SIZE i); [apply in_app_iff; left; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)])); [| exact Hcg | exact KBF].
unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split. { intros i Hi. rewrite FRF by (unfold OFF_apal, sp, sp0, RGBA_FRAME in *; lia). apply Hapal. exact Hi. }
split; [exact Hpnew|]. split; [exact Hfimg|]. exact HB. }
Ltac wrF HU2 :=
(lazymatch goal with |- wr_ok ?Ee ?rs ?stk ?spp ?fp ?b0 ?bc => let rs' := eval vm_compute in rs in change (wr_ok Ee rs' stk spp fp b0 bc) end);
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; unfold sp, sp0, RGBA_FRAME in *; lia | apply wr_ok_nil].
jrun LAWS ubs2tbl_ok HS HJ. { wrF HU2. }
cbn [ms_mem mkst] in HF, HJ.
assert (FR8 : forall x0, 0 <= x0 < 2 ^ 64 -> ~ (sp regs0 + 154 <= x0 < sp regs0 + 156) -> mbyte ubs2segs (ms_mem ms) x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx0q Hn. mb_frame_g HF; [reflexivity | rewrite HU2; lia]. }
jbranch ubs2tbl HS.
-
assert (Hha0 : ha = 0).
{ revert Hc. rewrite branch_ne_U, (U_atom E 33 (nha ha) B33), U_lit by lia. unfold nha. destruct (Z.eqb_spec ha 0); [auto | intros HH0; discriminate HH0]. }
jrun_to LAWS ubs2tbl_ok HS HJ PC_FIN2. { wrF HU2. }
cbn [ms_regs ms_mem mkst] in HF0, HJ.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (st_chunk_val ubs2segs E ssf msf 0%nat _ 2%nat 154 2%N (SOff 9 0) (sp regs0) sizeLCT HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE9) ltac:(cbn; lia) ltac:(cbn; lia)) as Mnl1
end.
change (N.to_nat 2) with 2%nat in Mnl1.
apply (FINPACK _ _ HS eq_refl eq_refl HJ).
+ intros x0 Hx0q Hn. rewrite <- (FR8 x0 Hx0q Hn). mb_frame_g HF0; [reflexivity | rewrite HU2; lia].
+ exact Mnl1.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ jreg HS (12%bv:reg) as Hq. rewrite Hq, Hha0. reflexivity.
-
assert (Hha1 : ha = 1).
{ revert Hc. rewrite branch_ne_U, (U_atom E 33 (nha ha) B33), U_lit by lia. unfold nha. destruct (Z.eqb_spec ha 0); [intros HH0; discriminate HH0 | intros _; lia]. }
jrun_to LAWS ubs2tbl_ok HS HJ PC_FIN2. { wrF HU2. }
cbn [ms_regs ms_mem mkst] in HF0, HJ.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (st_chunk_val ubs2segs E ssf msf 0%nat _ 2%nat 154 2%N (SOff 9 0) (sp regs0) sizeLCT HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE9) ltac:(cbn; lia) ltac:(cbn; lia)) as Mnl1
end.
change (N.to_nat 2) with 2%nat in Mnl1.
apply (FINPACK _ _ HS eq_refl eq_refl HJ).
+ intros x0 Hx0q Hn. rewrite <- (FR8 x0 Hx0q Hn). mb_frame_g HF0; [reflexivity | rewrite HU2; lia].
+ exact Mnl1.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ jreg HS (12%bv:reg) as Hq. rewrite Hq, Hha1. reflexivity.
Qed.
End h.
Lemma ubs2_rgbadd_FIN : seg_FIN API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KXF fx1 regs1 Lc Ac memc mdc ha pnew fimg sizeLCT HFRM HAT. exact (FIN_at regs1 Lc Ac memc mdc ha pnew fimg sizeLCT KXF HFRM HAT). Qed.
End e.
End d.

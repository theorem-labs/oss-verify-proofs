(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI1i YI57 YI07 YP14 YI08 YI0c YI0g YI3h YI3d YI4v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition LAY_RASAVE : layout_t :=
[(5032, 8%N); (5040, 8%N); (5048, 8%N); (5056, 8%N); (5064, 8%N); (5072, 8%N); (5080, 8%N);
(5088, 8%N); (5096, 8%N); (5104, 8%N); (5112, 8%N); (5120, 8%N); (5128, 8%N)].
Definition rasave_vals (regs0 : bvmap 5 word) : list Z :=
map (fun rr : reg => bv_unsigned (getr regs0 rr)) [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma u64_range8 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Lemma byte_mod32 : forall v k, 0 <= v -> (k < 4)%nat ->
Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)) = Z_to_bv 8 (le_byte (v mod 2 ^ 32) 4 k).
Proof.
intros v k Hv Hk. unfold le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_mod _ (2 ^ 32)) by lia. change 256 with (2 ^ 8). rewrite Z.mod_mod by lia.
rewrite <- !Z.land_ones by lia. rewrite !Z.shiftr_land. rewrite <- !Z.land_assoc.
apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.shiftr_spec by lia.
destruct (Z_lt_le_dec n 8).
- rewrite (Z.ones_spec_low 8 n) by lia. rewrite !Bool.andb_true_r. rewrite Z.ones_spec_low by lia. rewrite Bool.andb_true_r. reflexivity.
- rewrite (Z.ones_spec_high 8 n) by lia. rewrite !Bool.andb_false_r. reflexivity.
Qed.
Lemma val_of_chunk4 : forall segs E mem base off (e : sv) v,
chunk_ok segs E mem base (mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem segs mem (base + off) 4 (v mod 2 ^ 32).
Proof.
intros segs E mem base off e v H He Hv k Hk. unfold chunk_ok in H. cbn [c_off c_val c_len cv_len] in H.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. rewrite He in Hb1.
unfold byte_of_word in Hb1. rewrite Z_to_bv_unsigned in Hb1.
unfold bv_wrap, bv_modulus in Hb1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb1. rewrite Z.mod_small in Hb1 by lia.
injection Hb1 as <-. rewrite Hb2. f_equal. apply byte_mod32; lia.
Qed.
Definition LAY_Rgb11 : layout_t :=
[(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 4%N); (36, 4%N); (40, 2%N); (42, 2%N); (44, 2%N); (48, 8%N); (56, 4%N)].
Lemma obj_at_rgb_set_cur : forall (m m' : word -> option byte) rr vals c c',
length vals = 11%nat ->
obj_at src2segs m rr LAY_Rgb (vals ++ [c]) ->
(forall i, 0 <= i < 60 -> mbyte src2segs m' (rr + i) = mbyte src2segs m (rr + i)) ->
val_mem src2segs m' (rr + 60) 4 c' -> 0 <= c' < 2 ^ 32 ->
obj_at src2segs m' rr LAY_Rgb (vals ++ [c']).
Proof.
intros m m' rr vals c c' Hlen Hobj Hkeep Hv Hc'.
change LAY_Rgb with (LAY_Rgb11 ++ [(60, 4%N)]) in *.
apply (proj1 (obj_at_app_g src2segs m rr LAY_Rgb11 [(60, 4%N)] vals [c] Hlen)) in Hobj. destruct Hobj as [H1 H2].
apply (proj2 (obj_at_app_g src2segs m' rr LAY_Rgb11 [(60, 4%N)] vals [c'] Hlen)). split.
- eapply obj_at_transport; [exact H1|]. intros f i Hf Hi. unfold LAY_Rgb11 in Hf. cbv [In] in Hf.
repeat (destruct Hf as [<-|Hf]; [cbn [fst snd] in *; rewrite <- Z.add_assoc; apply Hkeep; lia|]). destruct Hf.
- cbn [obj_at]. split; [|exact I]. split; [exact Hv | exact Hc'].
Qed.
Section h.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Lemma obj_at_rasave : forall memc, ra_saved_ok regs0 memc -> obj_at src2segs memc (sp regs0) LAY_RASAVE (rasave_vals regs0).
Proof.
intros memc HR. unfold ra_saved_ok in HR.
assert (X : forall j (rr : reg) off, nth_error RA_SAVED j = Some rr -> off = 5128 - 8 * Z.of_nat j ->
field_ok src2segs memc (sp regs0) (off, 8%N) (bv_unsigned (getr regs0 rr))).
{ intros j rr off Hj ->. split; [|apply u64_range8]. cbn [fst snd]. apply val_mem_word_mem.
replace (sp regs0 + (5128 - 8 * Z.of_nat j)) with (spZ regs0 - 8 * (Z.of_nat j + 1)) by (unfold sp, sp0, RGBA_FRAME; lia). exact (HR j rr Hj). }
cbn [obj_at LAY_RASAVE rasave_vals map].
split; [apply (X 12%nat); reflexivity|]. split; [apply (X 11%nat); reflexivity|]. split; [apply (X 10%nat); reflexivity|].
split; [apply (X 9%nat); reflexivity|]. split; [apply (X 8%nat); reflexivity|]. split; [apply (X 7%nat); reflexivity|].
split; [apply (X 6%nat); reflexivity|]. split; [apply (X 5%nat); reflexivity|]. split; [apply (X 4%nat); reflexivity|].
split; [apply (X 3%nat); reflexivity|]. split; [apply (X 2%nat); reflexivity|]. split; [apply (X 1%nat); reflexivity|].
split; [apply (X 0%nat); reflexivity|]. exact I.
Qed.
Definition ss_XS : sstate :=
mkSS PC_XS sr_atoms
[ YQ0b.mkRegion (Some 8%nat) 0 RGB_SIZE 60 64 (obj_chunks_from LAY_Rgb 32) ;
YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 (obj_chunks_from LAY_RASAVE 44) ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (8%nat, mkAF 4096 (CEIL_MAX - RGB_SIZE) 4) ] [] []).
Section l.
Context {fxi : YK11.FPState}.
Lemma XS_at : forall regs1 Lc Ac memc mdc res s' bef' beffmt' cur1,
frm_zero (@fp_csr fxi) ->
at_XS (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc res s' bef' beffmt' cur1 ->
SR src2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XS) memc (seg_rom src2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc res s' bef' beffmt' cur1 HFRM HAT.
destruct HAT as (HINV & HREGS & Rres & G21 & G8 & Hobj & Hcg & Hwf & HW & HH & Hattr & Hraw & Hbef & HB).
pose proof HINV as (HJ & Hinit & _ & Hra0 & Hal0 & Htp0 & HRA & _).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity. assert (HSZ : RGB_SIZE = 64) by reflexivity.
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE HHc Hrin ltac:(lia)) as (Hr0 & Hr1 & Hr16).
set (rgbv := [g; wfn; ctx; path; attr; gen; loops; W; H; bef'; beffmt'; cur1]).
set (E := Ereg regs1 (map (Z_to_bv 64) (rgbv ++ rasave_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error (rgbv ++ rasave_vals regs0) jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v) by (intros jj v Hjj; subst E; apply Ereg_vals; exact Hjj).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HU8 : bv_unsigned (ew E 8) = r) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) src2segs E ss_XS (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XS) memc (seg_rom src2segs))).
{ unfold ss_XS. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply (region_ok_obj src2segs _ memc 8 r); [exact HU8 | lia | unfold RGB_SIZE; lia | exact Hobj | reflexivity | | ].
* intros jj v Hjj. apply (Ereg_vals regs1 _ [] jj v). rewrite nth_error_app1; [exact Hjj | apply nth_error_Some; subst rgbv; congruence].
* intros i Hi. apply (present_writable src2_msyms). apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE i HHc Hrin ltac:(unfold RGB_SIZE; lia))).
+ eapply (region_ok_obj_gen src2segs _ memc 2 (sp regs0)); [exact HU2 | unfold sp, sp0 in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | apply obj_at_rasave; exact HRA | reflexivity | | | intros i Hi; lia].
* intros jj v Hjj. replace (44 + jj)%nat with (32 + (length rgbv + jj))%nat by (subst rgbv; cbn; lia).
apply (Ereg_vals regs1 _ [] (length rgbv + jj)%nat v). rewrite nth_error_app2 by lia. replace (length rgbv + jj - length rgbv)%nat with jj by lia. exact Hjj.
* intros jj z Hjj. destruct jj; discriminate Hjj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8.
repeat split; try exact I. unfold sp, sp0, RGB_SIZE, RGBA_FRAME in *. first [left; lia | right; lia].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8.
change (2 ^ 4) with 16. unfold sp, sp0, RGB_SIZE, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XS) memc (seg_rom src2segs))) in HJ.
jrun LAWS src2tbl_ok HS HJ.
{ eapply wr_ok_cons_block; [reflexivity | exact HU8 | exact Hrin | cbn; lia | cbn; unfold RGB_SIZE; lia | | apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]].
intros a Ha. cbn [r_wlo r_whi] in Ha. exists (r, r + RGB_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold RGB_SIZE; lia]. }
cbn [ms_mem mkst] in HF.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | exact Hh | exact Hl | exact HS | reflexivity | vm_compute; reflexivity |].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
assert (RG : forall (rr : reg) e, sr_get (ss_regs ssf) rr = e -> getr (ms_regs ms) rr = sv_denot E e)
by (intros rr e He; rewrite <- He; apply (st_ok_reg _ _ _ _ rr HS)) end.
assert (HX : forall n jj (rr : reg), n = (44 + jj)%nat -> nth_error [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv jj = Some rr -> ew E n = getr regs0 rr).
{ intros n jj rr -> Hjj. replace (44 + jj)%nat with (32 + (length rgbv + jj))%nat by (subst rgbv; cbn; lia).
rewrite (HV (length rgbv + jj)%nat (bv_unsigned (getr regs0 rr))); [apply Z_to_bv_bv_unsigned|].
rewrite nth_error_app2 by lia. replace (length rgbv + jj - length rgbv)%nat with jj by lia.
unfold rasave_vals. rewrite nth_error_map, Hjj. reflexivity. }
unfold rgba_post.
exists fxi, Lc, Ac, (ms_regs ms), (ms_mem ms), mdc, s', bef', beffmt', (res mod 2 ^ 32).
split. { rewrite (RG 1%bv (SOff 56 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 56%nat 12%nat 1%bv eq_refl eq_refl), Z_to_bv_bv_unsigned, Hra0. reflexivity. }
split; [exact HFRM|]. split; [exact HJ|].
split. { apply regs_preserved_intro_g.
- rewrite (RG 2%bv (SOff 2 5136) eq_refl). cbn [sv_denot]. rewrite HU2. unfold sp, sp0, RGBA_FRAME, spZ.
rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs0 2)) at 2. f_equal. lia.
- rewrite (RG 3%bv (SOff 3 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HE 3%nat 3%bv eq_refl), Z_to_bv_bv_unsigned. exact G3.
- rewrite (RG 4%bv (SOff 4 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HE 4%nat 4%bv eq_refl), Z_to_bv_bv_unsigned. exact G4.
- rewrite (RG 8%bv (SOff 55 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 55%nat 11%nat 8%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 9%bv (SOff 54 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 54%nat 10%nat 9%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 18%bv (SOff 53 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 53%nat 9%nat 18%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 19%bv (SOff 52 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 52%nat 8%nat 19%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 20%bv (SOff 51 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 51%nat 7%nat 20%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 21%bv (SOff 50 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 50%nat 6%nat 21%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 22%bv (SOff 49 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 49%nat 5%nat 22%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 23%bv (SOff 48 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 48%nat 4%nat 23%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 24%bv (SOff 47 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 47%nat 3%nat 24%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 25%bv (SOff 46 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 46%nat 2%nat 25%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 26%bv (SOff 45 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 45%nat 1%nat 26%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned.
- rewrite (RG 27%bv (SOff 44 0) eq_refl). cbn [sv_denot]. rewrite Z.add_0_r, (HX 44%nat 0%nat 27%bv eq_refl eq_refl). apply Z_to_bv_bv_unsigned. }
split; [exact Hinit|].
assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (r + 60 <= a < r + 64) -> mbyte src2segs (ms_mem ms) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF; [reflexivity | rewrite HU8; lia | rewrite HU2; lia]. }
split. { change [g; wfn; ctx; path; attr; gen; loops; W; H; bef'; beffmt'; res mod 2 ^ 32] with ([g; wfn; ctx; path; attr; gen; loops; W; H; bef'; beffmt'] ++ [res mod 2 ^ 32]).
eapply obj_at_rgb_set_cur; [reflexivity | exact Hobj | intros i Hi; apply MB; lia | | apply Z.mod_pos_bound; lia].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (mem_ok_region src2segs E (ms_mem ms) (ss_mem ssf) _ (st_ok_mem_ok src2segs E ssf _ HS) ltac:(left; reflexivity)) as HR0 end.
destruct HR0 as (_ & _ & _ & Hcs). cbn [r_chunks r_base base_val] in Hcs. rewrite HU8 in Hcs.
apply (val_of_chunk4 src2segs E (ms_mem ms) r 60 (SOff 21 0) res); [exact (Forall_inv Hcs) | | exact Rres].
cbn [sv_denot]. rewrite Z.add_0_r, (HE 21%nat 21%bv eq_refl), G21, unsigned_lit_small by lia. reflexivity. }
split. { eapply (cgif_at_kept _ _ g s' N (cgif_blocks g s' N) []); [rewrite app_nil_r; apply Permutation_refl | exact Hcg |].
intros b n i Hin Hi.
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (r, RGB_SIZE) _ (b, n) HHc HB ltac:(apply in_app_iff; left; exact Hin)) as Hsep.
cbn [fst snd] in Hsep. destruct (heap_blocks src2_msyms MR LAWS Lc Ac memc mdc b n i HHc ltac:(eapply blocks_perm_in; [exact HB | right; apply in_app_iff; left; exact Hin]) Hi) as (_ & Hb0 & Hb1 & _).
apply MB; unfold RGB_SIZE in Hsep; lia. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact Hattr|]. split; [exact Hraw|]. split; [exact Hbef | exact HB].
Qed.
End l.
Lemma src2_rgbadd_XS : seg_XS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest.
Proof. intros fx1 regs1 Lc Ac memc mdc res s' bef' beffmt' cur1 HFRM HAT. exact (XS_at regs1 Lc Ac memc mdc res s' bef' beffmt' cur1 HFRM HAT). Qed.
Lemma ra_saved_kept : forall (m m' : word -> option byte) lo,
ra_saved_ok regs0 m -> lo <= sp0 regs0 - 104 -> alloc_ceiling <= sp0 regs0 - 104 -> sp0 regs0 < 2 ^ 63 ->
(forall x, alloc_ceiling <= x < 2 ^ 64 -> lo <= x -> mbyte src2segs m' x = mbyte src2segs m x) ->
ra_saved_ok regs0 m'.
Proof.
intros m m' lo HR Hlo Hc H63 HK j rr Hj k Hk.
assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some RA_SAVED j)); congruence).
rewrite HK; [apply (HR j rr Hj); exact Hk | lia | lia].
Qed.
Section o.
Context {fxi : YK11.FPState}.
Definition ss_XF : sstate := mkSS PC_XF sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma XF_at : forall regs1 Lc Ac memc mdc res tb tn s' bef' beffmt' cur1,
K_XS (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_XF (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc res tb tn s' bef' beffmt' cur1 ->
SR src2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XF) memc (seg_rom src2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc res tb tn s' bef' beffmt' cur1 KXS HFRM HAT.
destruct HAT as (HINV & HREGS & Rres & G25 & G21 & G8 & Hobj & Hcg & Hwf & HW & HH & Hattr & Hraw & Hbef & Htb & Hnot & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & HINV').
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HB' : Permutation (blocks Lc Ac) ((tb, tn) :: BASE r g N img fmt rest s' bef' beffmt')).
{ eapply Permutation_trans; [exact HB | apply Permutation_sym, Permutation_cons_append]. }
assert (Htbin : In (tb, tn) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB' | left; reflexivity]).
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) src2segs E ss_XF (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XF) memc (seg_rom src2segs))).
{ unfold ss_XF. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XF) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_free. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K0 : forall x, ms_mem ms x = memc x) by (intros x; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Hq10. rewrite (HE 25%nat 25%bv eq_refl), G25 in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hq2.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), G4 in Hq4.
jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS src2_errno_low IMG (aa_free API)) with (a := tb) (n := tn) (spc := sp regs0);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Htbin | exact Hq10 | exact Hq2
| unfold sp, sp0, RGBA_FRAME in *; lia | exact Hsp16 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hq4; exact Htp0 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin0. exfalso. exact (Hnot Hin0). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hinit2).
pose proof (perm_after_rm1 _ _ _ _ HB' Hrm) as HB2.
assert (Hrin2 : In (r, RGB_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
change (Z_to_bv 64 82608) with (Z_to_bv 64 PC_XS).
apply (KXS fxi regs2 L2 A2 mem2 md2 res s' bef' beffmt' cur1 HFRM).
assert (HI : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp regs0 <= x -> mbyte src2segs mem2 x = mbyte src2segs memc x).
{ intros x Hx Hsx. etransitivity; [exact (proj1 (Hhi2 x Hx ltac:(lia)))|]. unfold mbyte. rewrite K0. reflexivity. }
assert (Hkeep' : forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m -> mbyte src2segs mem2 (b + i) = mbyte src2segs memc (b + i)).
{ intros b m i Hbm Hi. etransitivity; [exact (Hkeep b m i Hbm Hi)|]. unfold mbyte. rewrite K0. reflexivity. }
split.
{
split; [exact HJ2|]. split; [exact Hinit2|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept memc mem2 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro | exact HINV']. }
split. { split; [rewrite (regs_preserved_frame _ _ HP2 2%bv ltac:(vm_compute; reflexivity)); exact Hq2|].
split; [rewrite (regs_preserved_frame _ _ HP2 3%bv ltac:(vm_compute; reflexivity)); jreg HS (3%bv:reg) as Hq3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hq3; exact Hq3|].
rewrite (regs_preserved_frame _ _ HP2 4%bv ltac:(vm_compute; reflexivity)), Hq4. reflexivity. }
split; [exact Rres|].
split. { rewrite (regs_preserved_frame _ _ HP2 21%bv ltac:(vm_compute; reflexivity)). jreg HS (21%bv:reg) as Hq21. rewrite (HE 21%nat 21%bv eq_refl), G21 in Hq21. exact Hq21. }
split. { rewrite (regs_preserved_frame _ _ HP2 8%bv ltac:(vm_compute; reflexivity)). jreg HS (8%bv:reg) as Hq8. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hq8. exact Hq8. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i Hrin2 Hi). }
split. { eapply (cgif_at_kept _ _ g s' N (blocks L2 A2)); [| exact Hcg | exact Hkeep'].
eapply Permutation_trans; [exact HB2|]. unfold BASE. apply Permutation_middle. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact Hattr|]. split; [exact Hraw|]. split; [exact Hbef | exact HB2].
Qed.
End o.
Lemma src2_rgbadd_XF : seg_XF API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest.
Proof. intros KXS fx1 regs1 Lc Ac memc mdc res tb tn s' bef' beffmt' cur1 HFRM HAT. exact (XF_at regs1 Lc Ac memc mdc res tb tn s' bef' beffmt' cur1 KXS HFRM HAT). Qed.
Lemma tmp_not_entry : forall Lc Ac memc mdc b n restb,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) ((b, n) :: restb) ->
(forall x, In x (blocks L A) -> In x restb) -> 0 < n -> ~ In (b, n) (blocks L A).
Proof.
intros Lc Ac memc mdc b n restb HH HP Hsub Hn Hin. apply Hsub in Hin.
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (b, n) restb (b, n) HH HP Hin) as Hs. cbn [fst snd] in Hs. lia.
Qed.
Definition ss_XB : sstate := mkSS PC_XB sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma src2_rgbadd_XB : seg_XB API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KXF regs1 Lc Ac memc mdc pnew fimg HAT.
destruct HAT as (HINV & HREGS & Hfmt & G9 & G25 & G21 & G8 & Hobj & Hcg & Hpnew & Hfimg & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
assert (HB' : Permutation (blocks Lc Ac) ((pnew, fmt * N) :: BASE r g N img fmt rest s bef beffmt ++ [(fimg, N)])).
{ eapply Permutation_trans; [exact HB|]. apply Permutation_sym. apply Permutation_middle. }
assert (Hpin : In (pnew, fmt * N) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB' | left; reflexivity]).
assert (Hpnot : ~ In (pnew, fmt * N) (blocks L A)).
{ eapply tmp_not_entry; [exact HHc | exact HB' | | lia]. intros x Hx. apply in_app_iff. left. eapply Permutation_in; [exact HBent | exact Hx]. }
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok src2segs E ss_XB (mkst regs1 (Z_to_bv 64 PC_XB) memc (seg_rom src2segs))).
{ unfold ss_XB. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_XB) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_free. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K0 : forall x, ms_mem ms x = memc x) by (intros x; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Hq10. rewrite (HE 9%nat 9%bv eq_refl), G9 in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hq2.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), G4 in Hq4.
jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS src2_errno_low IMG (aa_free API)) with (a := pnew) (n := fmt * N) (spc := sp regs0);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hpin | exact Hq10 | exact Hq2
| unfold sp, sp0, RGBA_FRAME in *; lia | exact Hsp16 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hq4; exact Htp0 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin0. exfalso. exact (Hpnot Hin0). }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hinit2).
pose proof (perm_after_rm1 _ _ _ _ HB' Hrm) as HB2.
assert (Hrin2 : In (r, RGB_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
assert (HI : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp regs0 <= x -> mbyte src2segs mem2 x = mbyte src2segs memc x).
{ intros x Hx Hsx. etransitivity; [exact (proj1 (Hhi2 x Hx ltac:(lia)))|]. unfold mbyte. rewrite K0. reflexivity. }
assert (Hkeep' : forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m -> mbyte src2segs mem2 (b + i) = mbyte src2segs memc (b + i)).
{ intros b m i Hbm Hi. etransitivity; [exact (Hkeep b m i Hbm Hi)|]. unfold mbyte. rewrite K0. reflexivity. }
change (Z_to_bv 64 82600) with (Z_to_bv 64 PC_XF).
apply (KXF fx regs2 L2 A2 mem2 md2 2 fimg N s bef beffmt cur Hfrm0).
split.
{
split; [exact HJ2|]. split; [exact Hinit2|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept memc mem2 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [rewrite (regs_preserved_frame _ _ HP2 2%bv ltac:(vm_compute; reflexivity)); exact Hq2|].
split; [rewrite (regs_preserved_frame _ _ HP2 3%bv ltac:(vm_compute; reflexivity)); jreg HS (3%bv:reg) as Hq3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hq3; exact Hq3|].
rewrite (regs_preserved_frame _ _ HP2 4%bv ltac:(vm_compute; reflexivity)), Hq4. reflexivity. }
split; [lia|].
split. { rewrite (regs_preserved_frame _ _ HP2 25%bv ltac:(vm_compute; reflexivity)). jreg HS (25%bv:reg) as Hq25. rewrite (HE 25%nat 25%bv eq_refl), G25 in Hq25. exact Hq25. }
split. { rewrite (regs_preserved_frame _ _ HP2 21%bv ltac:(vm_compute; reflexivity)). jreg HS (21%bv:reg) as Hq21. rewrite (HE 21%nat 21%bv eq_refl), G21 in Hq21. exact Hq21. }
split. { rewrite (regs_preserved_frame _ _ HP2 8%bv ltac:(vm_compute; reflexivity)). jreg HS (8%bv:reg) as Hq8. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hq8. exact Hq8. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i Hrin2 Hi). }
split. { eapply (cgif_at_kept _ _ g s N (blocks L2 A2)); [| exact Hcg | exact Hkeep'].
eapply Permutation_trans; [exact HB2|]. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbef|].
split; [exact Hfimg|].
split. { eapply tmp_not_entry; [exact (proj1 HJ2) | | | lia].
- eapply Permutation_trans; [exact HB2|]. apply Permutation_sym. apply Permutation_cons_append.
- intros x Hx. eapply Permutation_in; [exact HBent | exact Hx]. }
exact HB2.
Qed.
Goal True. idtac "XB-DONE". exact I. Qed.
End h.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths and module names changed; 902 of its 977 lines of code are new or changed and 416 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC81 YC4b YC1h YC88 YL02.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YN0g YC85.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel CtrlParsed disco_classify_c SightModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require SightLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Strategy expand [fsum blocksum].
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Definition TCHECK_SIGHTING_STK : Z := 64 + 2 * ESTACK.
Definition tcheck_sighting_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TCHECK_SIGHTING_STK [] regs ly S W mem md 0 (fun ly' S' W' _ mem' _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCHECK_SIGHTING_STK <= a < spZ regs) ->
         aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)).
Definition tcheck_sighting_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (s f len u st : Z) (G FB U : list byte),
  afn_pre SEGS B TCHECK_SIGHTING_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 f -> getr regs 12 = w64 len -> getr regs 13 = w64 u ->
  getr regs 14 = w64 st ->
  0 < s -> s mod 4 = 0 -> s + 24 <= 2 ^ 63 -> 0 < f -> f + 50 <= 2 ^ 63 -> 0 < u -> u + 6 <= 2 ^ 63 ->
  0 <= len < 2 ^ 64 -> 0 <= st < 2 ^ 64 -> len <= 65535 ->
  length G = 24%nat -> garr8 SEGS (mrestrict (w_H W) mem) s (map bv_unsigned G) ->
  length FB = 50%nat -> garr8 SEGS (mrestrict (w_H W) mem) f (map bv_unsigned FB) ->
  length U = 6%nat -> garr8 SEGS (mrestrict (w_H W) mem) u (map bv_unsigned U) ->
  amem_range s 24 -> amem_range f 50 -> amem_range u 6 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF s 24 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) s 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF f 50 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) f 50 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF u 6 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) u 6 ->
  (s + 24 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= s) ->
  (f + 50 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= f) ->
  off_img s 24 -> off_img f 50 -> (s + 24 <= f \/ f + 50 <= s) ->
  (u + 6 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= u) ->
  sighting_facts G FB U len st ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_check_sighting) regs mem md) (tcheck_sighting_post fq regs ly S W mem md).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Definition cs_Rs : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 0 [YP09.mkChunk 0 (CData 0 0 24)].
Definition cs_Rf : YP09.region := YP09.mkRegion (Some 11%nat) 0 50 0 0 [YP09.mkChunk 0 (CData 1 0 50)].
Definition cs_regions : smem := [stack_region 64; got_regionP; bcell_regionP 32].
Definition cs_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 25) 2); (11%nat, mkAF 1 (2 ^ 47 - 51) 0);
  (12%nat, mkAF 50 65535 0); (13%nat, mkAF 1 (2 ^ 47 - 7) 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_cs : sstate := mkSS AF_both3_check_sighting sr_atoms cs_regions None cs_facts.
Definition CBx : sv := SOff 32 0.
Definition cs_SH : list shent := [mkSHE 10 0 24; mkSHE 11 0 50].
Definition EC (regs : bvmap 5 word) (G FB : list byte) : env :=
  edset (edset (Eimg (Ereg regs [Z_to_bv 64 SB])) 0 G) 1 FB.
Lemma getr_regupd8 : forall (regs : bvmap 5 word) v (r : bv 5), bv_unsigned r <> 8 -> getr (regupd regs 8 v) r = getr regs r.
Proof. intros regs v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. intros ->. apply Hr. reflexivity. Qed.
Lemma cs_ew_low : forall regs G FB n, (n < A_TEXT)%nat -> ew (EC regs G FB) n = ew (Ereg regs [Z_to_bv 64 SB]) n.
Proof. intros regs G FB n Hn. unfold EC, edset. cbn [ew]. apply Eimg_low. exact Hn. Qed.
Lemma cs_img : forall regs G FB, img_env VAL A_LIM (EC regs G FB).
Proof. intros regs G FB a Ha. exact (Eimg_env (Ereg regs [Z_to_bv 64 SB]) a Ha). Qed.
Lemma cs_regs_ok : forall regs G FB, regs_ok (EC regs G FB) sr_atoms regs.
Proof.
intros regs G FB. apply (regs_ok_agree_pd (fun _ => true) (fun _ => false) (Eimg (Ereg regs [Z_to_bv 64 SB]))).
- split; [intros n _; reflexivity | intros d Hd; discriminate Hd].
- vm_compute. reflexivity.
- apply regs_ok_Eimg_Ereg.
Qed.
Lemma cs_chunk_data : forall E m base d (L : list byte),
  ed E d = L -> garr8 SEGS m base (map bv_unsigned L) ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CData d 0 (Z.of_nat (length L)))).
Proof.
intros E m base d L Hd HL. apply (YN0g.chunk_ok_cdata SEGS E m base 0 d (Z.of_nat (length L))).
- rewrite Hd. reflexivity.
- intros k Hk. rewrite Hd in *. rewrite Z.add_0_r.
  rewrite (garr8_mbyte SEGS _ _ _ k HL) by (rewrite length_map; exact Hk).
  rewrite (nth_error_nth' L (Z_to_bv 8 0)) by exact Hk. f_equal.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hk).
  rewrite map_nth. apply Z_to_bv_bv_unsigned.
Qed.
Lemma cs_entry : forall ly S W (regs : bvmap 5 word) mem md (s f len u : Z) (G FB : list byte),
  AR SEGS B ly S W mem md -> astk_ok TCHECK_SIGHTING_STK ly (spZ regs) ->
  (forall a, spZ regs - TCHECK_SIGHTING_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 f -> getr regs 12 = w64 len -> getr regs 13 = w64 u ->
  0 < s -> s mod 4 = 0 -> 0 < f -> 0 < u -> 50 <= len <= 65535 ->
  length G = 24%nat -> garr8 SEGS (mrestrict (w_H W) mem) s (map bv_unsigned G) ->
  length FB = 50%nat -> garr8 SEGS (mrestrict (w_H W) mem) f (map bv_unsigned FB) ->
  amem_range s 24 -> amem_range f 50 -> amem_range u 6 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF s 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF f 50 ->
  (s + 24 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= s) ->
  (f + 50 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= f) ->
  off_img s 24 -> off_img f 50 -> (s + 24 <= f \/ f + 50 <= s) ->
  forall fq : YK11.FPState,
  st_ok_pi SEGS VAL (EC regs G FB) ss_cs
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_check_sighting)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CBx cs_SH (EC regs G FB) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md s f len u G FB HAR Hstk Hpres H10 H11 H12 H13 Hs0 Hs4 Hf0 Hu0 Hlen HGl HG HFl HF
  Hms Hmf Hmu RAs RAf Ds Df Ois Oif Dsf fq.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_SIGHTING_STK = 8256) by reflexivity.
pose proof (pal_got_shadow B TL) as HBgot. pose proof (pal_cell B TL) as HBcell.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 0)) as RgotV. pose proof (pa_val_range (A_OBJ 12)) as RcellV.
unfold amem_range in Hms, Hmf, Hmu. unfold off_img in Ois, Oif.
rewrite C4, C5 in *. rewrite C3 in Hms, Hmf, Hmu.
pose proof (proj1 C1) as C1a.
rewrite restrict_mkst_fx.
set (E := EC regs G FB).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n) by (intros n Hn; apply cs_ew_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 u) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EC, edset; cbn [ew]; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EC, edset; cbn [ew]; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HE0 : ed E 0 = G) by reflexivity. assert (HE1 : ed E 1 = FB) by reflexivity.
split.
- unfold ss_cs. apply pa_entry_st_ok_full.
  + apply cs_regs_ok.
  + vm_compute. reflexivity.
  + unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HgotR, HcellR.
    unfold cs_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbv; discriminate |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CBx SB);
      [cbn [sv_denot CBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbv; discriminate |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold cs_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E12, E13, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cs_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E CBx 10 s 24 s 0 24 RAs).
    * unfold U, CBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
    * lia. * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. clear - Hx Hms Hs0; lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E CBx 11 f 50 f 0 50 RAf).
    * unfold U, CBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
    * lia. * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. clear - Hx Hmf Hf0; lia.
Qed.
Lemma cs_add_sf : forall (fq : YK11.FPState) E ss ms (s f : Z) (G FB : list byte),
  st_ok_pi SEGS VAL E ss ms ->
  ew E 10 = Z_to_bv 64 s -> ew E 11 = Z_to_bv 64 f -> ed E 0 = G -> ed E 1 = FB ->
  length G = 24%nat -> length FB = 50%nat ->
  garr8 SEGS (ms_mem ms) s (map bv_unsigned G) -> garr8 SEGS (ms_mem ms) f (map bv_unsigned FB) ->
  0 < s -> s + 24 <= 2 ^ 63 -> 0 < f -> f + 50 <= 2 ^ 63 -> (s + 24 <= f \/ f + 50 <= s) ->
  all_disjoint E cs_Rs (ss_mem ss) -> all_disjoint E cs_Rf (ss_mem ss) ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (cs_Rf :: cs_Rs :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros fq E ss ms s f G FB HS E10 E11 HD0 HD1 HGl HFl HG HF Hs0 Hs1 Hf0 Hf1 Dsf Ds Df.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Rs : region_ok SEGS E (ms_mem ms) cs_Rs).
{ unfold region_ok, cs_Rs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 10%nat s E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor]. pose proof (cs_chunk_data E _ s 0 G HD0 HG) as Hc. rewrite HGl in Hc. exact Hc. }
assert (Rf : region_ok SEGS E (ms_mem ms) cs_Rf).
{ unfold region_ok, cs_Rf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 11%nat f E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor]. pose proof (cs_chunk_data E _ f 1 FB HD1 HF) as Hc. rewrite HFl in Hc. exact Hc. }
pose proof (st_ok_pi_add_region E ss ms cs_Rs HS eq_refl Rs Ds) as H1.
refine (st_ok_pi_add_region E _ ms cs_Rf H1 eq_refl Rf _).
cbn [ss_mem all_disjoint]. split; [|exact Df].
unfold extent_disjoint, cs_Rs, cs_Rf. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat s E10), (VB 11%nat f E11) by lia. lia.
Qed.
Lemma cs_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 t Ht. apply H. unfold shadow_addr in *.
assert (A1 : (SHADOW_OFF + x / 8) / 8 * 8 <= (SHADOW_OFF + x' / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (A2 : (SHADOW_OFF + (x' + n' - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.
Lemma cs_shok : forall (H : word -> bool) m E s f,
  U E CBx = SHADOW_OFF -> U E (SOff 10 0) = s -> U E (SOff 11 0) = f ->
  amem_range s 24 -> amem_range f 50 ->
  range_addressable (aview SEGS H m) SHADOW_OFF s 24 -> range_addressable (aview SEGS H m) SHADOW_OFF f 50 ->
  sh_ok SEGS CBx cs_SH E (mrestrict H m).
Proof.
intros H m E s f HB Hs Hf Hms Hmf RAs RAf.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in Hms, Hmf. rewrite C3, C4, C5 in Hms, Hmf.
unfold sh_ok, cs_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS H m E CBx 10 s 24 s 0 24 RAs HB Hs); [lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS H m E CBx 11 f 50 f 0 50 RAf HB Hf); [lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.
Lemma cs_keep_frame : forall E rs (H : word -> bool) (m m' m0 : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall x, in_wrange E rs x -> lo <= x < hi) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs H m m' m0 lo hi HF Hw HK a Ha Hn. rewrite <- (HK a Ha Hn). apply (aview_eq_of SEGS). apply HF.
rewrite unsigned_lit_small by lia. intros Hx. apply Hw in Hx. apply Hn. exact Hx.
Qed.
Lemma cs_aview_garr : forall (H : word -> bool) m p (L : list Z) j,
  garr8 SEGS (mrestrict H m) p L -> (j < length L)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j L 0).
Proof.
intros H m p L j HG Hj. unfold aview. rewrite (garr8_mbyte SEGS _ _ _ j HG Hj). cbn [option_map]. f_equal.
destruct (HG j Hj) as [_ Hr]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.
Lemma cs_nth_fld : forall (L : list byte) a b k d, (k < b)%nat -> nth k (fld L a b) d = nth (a + k) L d.
Proof.
intros L a b k d Hk. unfold fld.
assert (H1 : forall (X : list byte) b' k', (k' < b')%nat -> nth k' (firstn b' X) d = nth k' X d).
{ induction X as [|x X IH]; intros [|b'] [|k'] Hk'; cbn; try lia; try reflexivity. apply IH. lia. }
assert (H2 : forall (X : list byte) a' k', nth k' (skipn a' X) d = nth (a' + k') X d).
{ induction X as [|x X IH]; intros [|a'] k'; cbn; try reflexivity; [destruct k'; reflexivity | apply IH]. }
rewrite H1 by exact Hk. apply H2.
Qed.
Lemma cs_nth_eq6 : forall (A Bl : list byte) ka kb, map bv_unsigned (fld A ka 6) = map bv_unsigned (fld Bl kb 6) ->
  forall i, (i < 6)%nat -> bv_unsigned (nth (ka + i) A (zb 0)) = bv_unsigned (nth (kb + i) Bl (zb 0)).
Proof.
intros A Bl ka kb Heq i Hi. apply (f_equal (fun l => nth i l (bv_unsigned (zb 0)))) in Heq. cbv beta in Heq.
rewrite !map_nth, !cs_nth_fld in Heq by exact Hi. exact Heq.
Qed.
Lemma cs_aregs : forall (fq : YK11.FPState) (H : word -> bool) E ss ms regs0 extra,
  st_ok SEGS E ss (restrict H ms) -> (forall n, (n < 32)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  aregs_preserved regs0 (ms_regs ms).
Proof.
intros fq H E ss ms regs0 extra HS HA Hcs r Hr.
assert (Hin : In (Z_to_bv 5 r : bv 5) CALLEE_SAVED).
{ unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
  assert (Hq : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hq as [->|Hq]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
  subst. repeat (first [left; apply bv_eq; reflexivity | right]). }
pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
change (ms_regs ms) with (ms_regs (restrict H ms)).
rewrite (st_ok_reg SEGS E ss (restrict H ms) _ HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA. 2:{ pose proof (u5_range (Z_to_bv 5 r : bv 5)). lia. }
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition cs_q36 : sv :=
  SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 48)) (SLit (-14636698788954112))) (SLit 3817799680)) (SLit 21).
Definition cs_mask : sv :=
  SAlu ALU_AND
    (SAlu ALU_ADD
       (SAlu ALU_SLTU (SLit 0)
          (SAlu ALU_AND
             (SAlu ALU_SUB (SOff 12 (-52))
                (SMd M_MUL
                   (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 48)) (SLit (-14636698788954112))) (SLit 3817799680)) (SLit 21))
                   (SLit 36)))
             (SLit 65535)))
       (SLit (-1)))
    (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 48)) (SLit (-14636698788954112))) (SLit 3817799680)) (SLit 21)).
Definition cs_rem : sv :=
  SAlu ALU_SLL
    (SAluw ALU_SUB (SOff 12 (-52))
       (SMd M_MUL
          (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 48)) (SLit (-14636698788954112))) (SLit 3817799680)) (SLit 21))
          (SLit 36)))
    (SLit 48).
Definition zq36 (l : Z) : Z := ((l - 52) mod 65536) / 36.
Definition zmask (l : Z) : Z := if ((l - 52) mod 65536) mod 36 =? 0 then ((l - 52) mod 65536) / 36 else 0.
Definition zrem (l : Z) : Z := (((l - 52) mod 65536) mod 36) * 281474976710656.
Definition zcL (z : Z) : Z := z mod 18446744073709551616.
Definition zmdL (op : mulop) (a b : Z) : Z :=
  match op with M_MUL => a * b | M_MULHU => Z.shiftr (a * b) 64 | _ => zmd_raw 64 op a b end.
Definition sw32L (z : Z) : Z := (z + 2147483648) mod 4294967296 - 2147483648.
Fixpoint cs_z12 (l : Z) (v : sv) : Z :=
  match v with
  | SLit z => zcL z
  | SOff n z => if Nat.eqb n 12 then zcL (l + z) else 0
  | SAlu op a b => zcL (zalu_raw 63 64 op (cs_z12 l a) (cs_z12 l b))
  | SAluw op a b => zcL (sw32L (zalu_raw 31 32 op (cs_z12 l a mod 4294967296) (cs_z12 l b mod 4294967296)))
  | SMd op a b => zcL (zmdL op (cs_z12 l a) (cs_z12 l b))
  | _ => 0
  end.
Fixpoint cs_only12 (v : sv) : bool :=
  match v with
  | SLit _ => true
  | SOff n _ => Nat.eqb n 12
  | SAlu _ a b | SAluw _ a b | SMd _ a b => cs_only12 a && cs_only12 b
  | _ => false
  end.
Lemma U_SAluw' : forall E op a b, U E (SAluw op a b) = zcanon (bv_swrap 32 (zalu_raw 31 32 op (U E a mod 2 ^ 32) (U E b mod 2 ^ 32))).
Proof. intros E op a b. rewrite U_of_S, S_SAluw. unfold bv_wrap, zcanon, M64. reflexivity. Qed.
Lemma cs_z12_sound : forall E l v, ew E 12 = Z_to_bv 64 l -> 0 <= l < 2 ^ 64 -> cs_only12 v = true -> U E v = cs_z12 l v.
Proof.
intros E l v H12 Hl. induction v; cbn [cs_only12 cs_z12]; intros Hv; try discriminate.
- rewrite U_SLit. reflexivity.
- destruct (Nat.eqb_spec n 12); [subst n | discriminate]. rewrite U_SOff, H12, unsigned_lit_small by lia. reflexivity.
- apply andb_prop in Hv as [Ha Hb]. rewrite U_SAlu, IHv1, IHv2 by assumption. reflexivity.
- apply andb_prop in Hv as [Ha Hb]. rewrite U_SAluw', IHv1, IHv2 by assumption. reflexivity.
- apply andb_prop in Hv as [Ha Hb]. rewrite U_SMd, IHv1, IHv2 by assumption. destruct op; reflexivity.
Qed.
Lemma cs_m16a : forall a, (a mod 18446744073709551616) mod 65536 = a mod 65536.
Proof. intros a. apply Z.mod_mod_divide. exists 281474976710656. reflexivity. Qed.
Lemma cs_m16b : forall a, (a mod 4294967296) mod 65536 = a mod 65536.
Proof. intros a. apply Z.mod_mod_divide. exists 65536. reflexivity. Qed.
Lemma cs_alg : forall l, 0 <= l < 2 ^ 64 ->
  cs_z12 l cs_q36 = zq36 l /\ cs_z12 l cs_mask = zmask l /\ cs_z12 l cs_rem = zrem l.
Proof.
intros l Hl. cbn [cs_z12 cs_q36 cs_mask cs_rem zalu_raw zmdL Nat.eqb].
replace (Z.land (zcL 48) 63) with 48 by reflexivity. replace (Z.land (zcL 21) 63) with 21 by reflexivity.
replace (zcL 3817799680) with 3817799680 by reflexivity. replace (zcL 36) with 36 by reflexivity.
replace (zcL 65535) with 65535 by reflexivity. replace (zcL 0) with 0 by reflexivity.
replace (zcL (-1)) with 18446744073709551615 by reflexivity.
replace (zcL (-14636698788954112)) with 18432107374920597504 by reflexivity.
remember ((l - 52) mod 65536) as x eqn:Hxe.
assert (Hx : 0 <= x < 65536) by (rewrite Hxe; apply Z.mod_pos_bound; lia).
assert (HA : zcL (zcL (Z.shiftl (zcL (l + 0)) 48) + 18432107374920597504) = x * 281474976710656).
{ unfold zcL. rewrite Z.add_0_r, (Z.mod_small l 18446744073709551616) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 48) with 281474976710656.
  rewrite Zplus_mod_idemp_l.
  replace (l * 281474976710656 + 18432107374920597504) with ((l - 52) * 281474976710656 + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. change 18446744073709551616 with (65536 * 281474976710656).
  rewrite Z.mul_mod_distr_r by lia. rewrite Hxe. reflexivity. }
remember (x / 36) as q eqn:Hqe.
pose proof (Z.div_mod x 36 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as MB. rewrite <- Hqe in DM.
assert (Hq : 0 <= q <= 1820) by lia.
assert (HQ : zcL (Z.shiftr (zcL (Z.shiftr (x * 281474976710656 * 3817799680) 64)) 21) = q).
{ unfold zcL. replace (x * 281474976710656 * 3817799680) with (x * 58255 * 2 ^ 64) by lia.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
  rewrite (Z.mod_small (x * 58255)) by lia. change (2 ^ 21) with 2097152.
  assert (D : x * 58255 / 2097152 = q).
  { symmetry. apply Z.div_unique_pos with (r := 28 * q + x mod 36 * 58255); lia. }
  rewrite D. apply Z.mod_small. lia. }
rewrite HA, HQ.
assert (Hr : (l + -52 - q * 36) mod 65536 = x mod 36).
{ rewrite <- Zminus_mod_idemp_l. replace (l + -52) with (l - 52) by lia. rewrite <- Hxe.
  rewrite Z.mod_small by lia. lia. }
split; [rewrite Hqe, Hxe; reflexivity |]. split.
- assert (HR : zcL (Z.land (zcL (zcL (l + -52) - zcL (q * 36))) 65535) = x mod 36).
  { unfold zcL. rewrite (Z.mod_small (q * 36)) by lia. change 65535 with (Z.ones 16).
    rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    rewrite Zminus_mod_idemp_l, cs_m16a, Hr. apply Z.mod_small. lia. }
  rewrite HR. unfold zmask. rewrite <- Hxe, <- Hqe.
  destruct (Z.eqb_spec (x mod 36) 0) as [Hm|Hm].
  + rewrite Hm. cbn [Z.ltb Z.compare]. replace (zcL (zcL 0 + 18446744073709551615)) with (Z.ones 64) by reflexivity.
    rewrite Z.land_comm, Z.land_ones by lia. unfold zcL. rewrite (Z.mod_small q (2 ^ 64)) by lia. apply Z.mod_small. lia.
  + replace (0 <? x mod 36) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (zcL (zcL 1 + 18446744073709551615)) with 0 by reflexivity. rewrite Z.land_0_l.
    reflexivity.
- unfold zrem. rewrite <- Hxe.
  unfold zcL at 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 48) with 281474976710656.
  change 18446744073709551616 with (65536 * 281474976710656). rewrite Z.mul_mod_distr_r by lia. f_equal.
  change (65536 * 281474976710656) with 18446744073709551616.
  unfold zcL, sw32L. rewrite cs_m16a. rewrite (Z.mod_small (q * 36)) by lia.
  rewrite <- Zminus_mod_idemp_l, cs_m16b, Zminus_mod_idemp_l.
  replace ((l + -52) mod 18446744073709551616 mod 4294967296 - q * 36 mod 4294967296 + 2147483648 - 2147483648)
    with ((l + -52) mod 18446744073709551616 mod 4294967296 - q * 36 mod 4294967296) by lia.
  rewrite (Z.mod_small (q * 36) 4294967296) by lia.
  rewrite <- Zminus_mod_idemp_l, cs_m16b, cs_m16a, Zminus_mod_idemp_l. exact Hr.
Qed.
Lemma cs_U_len : forall E len, ew E 12 = Z_to_bv 64 len -> 0 <= len <= 65535 ->
  U E cs_q36 = zq36 len /\ U E cs_mask = zmask len /\ U E cs_rem = zrem len.
Proof.
intros E len H12 Hl.
pose proof (fun v => cs_z12_sound E len v H12 ltac:(lia)) as HU.
rewrite !HU by (vm_compute; reflexivity). apply cs_alg. lia.
Qed.
Lemma cs_skipn_cons : forall (L : list byte) k, (k < length L)%nat -> skipn k L = nth k L (zb 0) :: skipn (S k) L.
Proof.
intros L k. revert L. induction k as [|k IH]; intros [|x L] Hl; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma cs_U_byte : forall E d (L : list byte) i, ed E d = L -> 0 <= i -> (Z.to_nat i < length L)%nat ->
  U E (SData d i 1) = fb L (Z.to_nat i).
Proof.
intros E d L i Hd Hi Hl. unfold U. cbn [sv_denot]. rewrite unsigned_lit. unfold data_word. rewrite Hd.
rewrite (cs_skipn_cons L (Z.to_nat i) Hl). change (N.to_nat 1) with 1%nat. cbn [firstn]. rewrite bytes_le_single.
unfold fb. apply YP0m.zcanon_small. pose proof (u8_range (nth (Z.to_nat i) L (zb 0))). lia.
Qed.
Lemma cs_U_word : forall E d (L : list byte) i, ed E d = L -> 0 <= i -> (Z.to_nat i + 4 <= length L)%nat ->
  U E (SExt true 32 (SData d i 4)) = zcanon (bv_swrap 32 (fu L (Z.to_nat i) 4)).
Proof.
intros E d L i Hd Hi Hl. rewrite U_SExt. cbv iota. unfold U at 1. cbn [sv_denot]. rewrite unsigned_lit. unfold data_word. rewrite Hd.
change (bytes_le_to_Z (firstn (N.to_nat 4) (skipn (Z.to_nat i) L))) with (fu L (Z.to_nat i) 4).
pose proof (SightLib.fu4_range L (Z.to_nat i) Hl) as R.
rewrite (YP0m.zcanon_small (fu L (Z.to_nat i) 4)) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Z.mod_small by lia. reflexivity.
Qed.
Fixpoint cs_sumexp (n : nat) : sv :=
  match n with O => SLit 0 | S k => SAlu ALU_ADD (cs_sumexp k) (SData 1 (18 + Z.of_nat k) 1) end.
Definition cs_sum32 : sv := Eval vm_compute in cs_sumexp 32.
Lemma cs_U_sumexp : forall E (L : list byte) n, ed E 1 = L -> length L = 50%nat -> (n <= 32)%nat ->
  U E (cs_sumexp n) = psum (fld L 18 32) n /\ 0 <= psum (fld L 18 32) n <= 255 * Z.of_nat n.
Proof.
intros E L n Hd HL. induction n as [|k IH]; intros Hk.
- cbn [cs_sumexp psum]. rewrite U_SLit. split; reflexivity || lia.
- destruct (IH ltac:(lia)) as [IHu IHr]. cbn [cs_sumexp psum]. rewrite U_SAlu. cbn [zalu_raw]. rewrite IHu.
  rewrite (cs_U_byte E 1 L (18 + Z.of_nat k) Hd) by lia.
  replace (Z.to_nat (18 + Z.of_nat k)) with (18 + k)%nat by lia.
  rewrite (cs_nth_fld L 18 32 k (Z_to_bv 8 0)) by lia. unfold fb.
  pose proof (u8_range (nth (18 + k) L (zb 0))) as R8. change (zb 0) with (Z_to_bv 8 0) in R8.
  split; [apply YP0m.zcanon_small|]; lia.
Qed.
Lemma cs_U_sum32 : forall E (L : list byte), ed E 1 = L -> length L = 50%nat ->
  U E cs_sum32 = psum (fld L 18 32) 32 /\ 0 <= psum (fld L 18 32) 32 <= 8160.
Proof.
intros E L Hd HL. change cs_sum32 with (cs_sumexp 32). destruct (cs_U_sumexp E L 32 Hd HL ltac:(lia)) as [H1 H2].
split; [exact H1 | change (255 * Z.of_nat 32) with 8160 in H2; lia].
Qed.
Lemma U_or : forall E a b, U E (SAlu ALU_OR a b) = Z.lor (U E a) (U E b).
Proof.
intros E a b. rewrite U_SAlu. cbn [zalu_raw]. pose proof (U_range E a). pose proof (U_range E b). unfold M64 in *.
apply YP0m.zcanon_small. apply Z_lor_range; lia.
Qed.
Lemma U_sltu1 : forall E a, U E (SAlu ALU_SLTU a (SLit 1)) = if U E a =? 0 then 1 else 0.
Proof.
intros E a. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. pose proof (U_range E a). unfold M64 in *.
replace (zcanon 1) with 1 by reflexivity.
destruct (Z.ltb_spec (U E a) 1), (Z.eqb_spec (U E a) 0); try lia; reflexivity.
Qed.
Lemma cs_U_q36 : forall E len, ew E 12 = Z_to_bv 64 len -> 0 <= len <= 65535 -> U E cs_q36 = zq36 len.
Proof. intros E len H Hl. exact (proj1 (cs_U_len E len H Hl)). Qed.
Lemma cs_U_mask : forall E len, ew E 12 = Z_to_bv 64 len -> 0 <= len <= 65535 -> U E cs_mask = zmask len.
Proof. intros E len H Hl. exact (proj1 (proj2 (cs_U_len E len H Hl))). Qed.
Lemma cs_U_rem : forall E len, ew E 12 = Z_to_bv 64 len -> 0 <= len <= 65535 -> U E cs_rem = zrem len.
Proof. intros E len H Hl. exact (proj2 (proj2 (cs_U_len E len H Hl))). Qed.
Lemma cs_U_sum : forall E (L : list byte), ed E 1 = L -> length L = 50%nat -> U E cs_sum32 = psum (fld L 18 32) 32.
Proof. intros E L Hd HL. exact (proj1 (cs_U_sum32 E L Hd HL)). Qed.
Lemma cs_sw : forall x, 0 <= x < 2 ^ 32 -> zcanon (bv_swrap 32 x) = x + (2 ^ 64 - 2 ^ 32) * (x / 2 ^ 31).
Proof. intros x Hx. rewrite <- unsigned_lit. apply SightLib.sw_u. exact Hx. Qed.
Lemma cs_lor01 : forall a b : bool, Z.lor (if a then 1 else 0) (if b then 1 else 0) = if a || b then 1 else 0.
Proof. intros [|] [|]; reflexivity. Qed.
Lemma cs_land255 : forall x, 0 <= x -> Z.land x 255 = x mod 256.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Definition cs_KEEP (H : word -> bool) (sp : Z) (m m0 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TCHECK_SIGHTING_STK <= a < sp) -> aview SEGS H m a = aview SEGS H m0 a.
Lemma cs_KEEP_frame : forall E rs (H : word -> bool) (m m' m0 : word -> option byte) sp,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall x, in_wrange E rs x -> sp - TCHECK_SIGHTING_STK <= x < sp) ->
  cs_KEEP H sp m m0 -> cs_KEEP H sp m' m0.
Proof. intros E rs H m m' m0 sp HF Hw HK. exact (cs_keep_frame E rs H m m' m0 _ _ HF Hw HK). Qed.
Lemma cs_ra_keep : forall (H : word -> bool) sp (m m0 : word -> option byte) a n,
  cs_KEEP H sp m m0 -> kHighShadowEnd <= sp - TCHECK_SIGHTING_STK -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview SEGS H m0) SHADOW_OFF a n -> range_addressable (aview SEGS H m) SHADOW_OFF a n.
Proof.
intros H sp m m0 a n HK Hk Ha Han HR.
apply (YC85.range_addressable_kept_win (aview SEGS H m0) (aview SEGS H m) (sp - TCHECK_SIGHTING_STK) sp a n); try assumption.
Qed.
Lemma cs_hull_keep : forall (H : word -> bool) sp (m m0 : word -> option byte) a n,
  cs_KEEP H sp m m0 -> kHighShadowEnd <= sp - TCHECK_SIGHTING_STK -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis (aview SEGS H m0) a n -> shadow_hull_vis (aview SEGS H m) a n.
Proof.
intros H sp m m0 a n HK Hk Ha Han Hn0 HR.
apply (YC85.shadow_hull_vis_kept_win (aview SEGS H m0) (aview SEGS H m) (sp - TCHECK_SIGHTING_STK) sp a n); try assumption.
Qed.
Lemma cs_garr_keep : forall (H : word -> bool) sp (m m0 : word -> option byte) p (L : list Z),
  cs_KEEP H sp m m0 -> 0 <= p -> p + Z.of_nat (length L) <= 2 ^ 64 ->
  (p + Z.of_nat (length L) <= sp - TCHECK_SIGHTING_STK \/ sp <= p) ->
  garr8 SEGS (mrestrict H m0) p L -> garr8 SEGS (mrestrict H m) p L.
Proof.
intros H sp m m0 p L HK Hp Hp2 Hd HG. apply (garr8_aview_kept SEGS H H m0 m p L); [|exact HG].
intros a Ha. apply HK; lia.
Qed.
Lemma cs_aview_some : forall (H : word -> bool) m p (L : list Z) a,
  garr8 SEGS (mrestrict H m) p L -> p <= a < p + Z.of_nat (length L) -> aview SEGS H m a <> None.
Proof.
intros H m p L a HG Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (cs_aview_garr H m p L (Z.to_nat (a - p)) HG) by lia. discriminate.
Qed.
Lemma cs_eq_bytes : forall (H : word -> bool) m p q (L1 L2 : list byte) k1 k2 n,
  garr8 SEGS (mrestrict H m) p (map bv_unsigned L1) -> garr8 SEGS (mrestrict H m) q (map bv_unsigned L2) ->
  (k1 + n <= length L1)%nat -> (k2 + n <= length L2)%nat ->
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS H m (p + Z.of_nat k1 + i) = aview SEGS H m (q + Z.of_nat k2 + i)) ->
  map bv_unsigned (fld L1 k1 n) = map bv_unsigned (fld L2 k2 n).
Proof.
intros H m p q L1 L2 k1 k2 n H1 H2 Hl1 Hl2 Heq.
apply (nth_ext _ _ (bv_unsigned (zb 0)) (bv_unsigned (zb 0))).
{ rewrite !length_map. unfold fld. rewrite !length_firstn, !length_skipn. lia. }
intros i Hi. rewrite length_map in Hi. unfold fld in Hi. rewrite length_firstn, length_skipn in Hi.
rewrite !map_nth, !cs_nth_fld by lia.
specialize (Heq (Z.of_nat i) ltac:(lia)).
replace (p + Z.of_nat k1 + Z.of_nat i) with (p + Z.of_nat (k1 + i)) in Heq by lia.
replace (q + Z.of_nat k2 + Z.of_nat i) with (q + Z.of_nat (k2 + i)) in Heq by lia.
rewrite (cs_aview_garr H m p _ (k1 + i) H1), (cs_aview_garr H m q _ (k2 + i) H2) in Heq by (rewrite length_map; lia).
injection Heq as Heq.
rewrite (nth_indep _ 0 (bv_unsigned (zb 0))), (nth_indep (map bv_unsigned L2) 0 (bv_unsigned (zb 0))) in Heq by (rewrite length_map; lia).
rewrite !map_nth in Heq. exact Heq.
Qed.
Lemma cs_awr_of : forall E rs STK sp0 FP bl0 blc ly own,
  bv_unsigned (ew E 2) = sp0 ->
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (match YP09.r_base r with Some n => Nat.eqb n 2 | None => false end && (- STK <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0))) rs = true ->
  awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own Hsp. induction rs as [|r rs IH]; intros HF.
- apply awr_ok_nil.
- cbn [forallb] in HF. apply andb_prop in HF as [Hr HF]. specialize (IH HF).
  apply orb_prop in Hr as [Hr | Hr].
  + apply awr_ok_cons_ro; [apply Z.leb_le; exact Hr | exact IH].
  + destruct (YP09.r_base r) as [n|] eqn:Hb; [|discriminate Hr].
    apply andb_prop in Hr as [Hr H3]. apply andb_prop in Hr as [H1 H2].
    apply Nat.eqb_eq in H1. subst n.
    apply (awr_ok_cons_stack E r rs STK sp0 FP bl0 blc ly own 2 Hb Hsp); [apply Z.leb_le; exact H2 | apply Z.leb_le; exact H3 | exact IH].
Qed.
Lemma cs_ne_lt : forall n k, (n < 32)%nat -> (32 <=? k)%nat = true -> n <> k.
Proof. intros n k Hn Hk. apply Nat.leb_le in Hk. lia. Qed.
Lemma cs_lt_le : forall n a b, (n < a)%nat -> (a <=? b)%nat = true -> (n < b)%nat.
Proof. intros n a b Hn Hk. apply Nat.leb_le in Hk. lia. Qed.
Lemma cs_wr_of : forall E rs sp STK, bv_unsigned (ew E 2) = sp ->
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (match YP09.r_base r with Some n => Nat.eqb n 2 | None => false end && (- STK <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0))) rs = true ->
  forall x, in_wrange E rs x -> sp - STK <= x < sp.
Proof.
intros E rs sp STK Hsp HF x (r & Hin & Hr). rewrite forallb_forall in HF. specialize (HF r Hin).
apply orb_prop in HF as [HF | HF].
- apply Z.leb_le in HF. lia.
- destruct (YP09.r_base r) as [n|] eqn:Hb; [|discriminate HF].
  apply andb_prop in HF as [HF H3]. apply andb_prop in HF as [H1 H2].
  apply Nat.eqb_eq in H1. subst n. apply Z.leb_le in H2. apply Z.leb_le in H3.
  try rewrite Hb in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
Qed.
Ltac cs_wr Usp :=
  apply cs_wr_of; [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp | vm_compute; reflexivity].
Ltac cs_keep Usp :=
  lazymatch goal with
  | HFr : frame_of ?Ef ?rs (mrestrict ?Hh ?m1) (mrestrict ?Hh' ?m2), KP : cs_KEEP ?Hh ?sp ?m1 ?m0 |- _ =>
    let K2 := fresh "KP" in
    let rs' := eval vm_compute in rs in change (frame_of Ef rs' (mrestrict Hh m1) (mrestrict Hh' m2)) in HFr;
    pose proof (cs_KEEP_frame _ rs' Hh m1 m2 m0 sp HFr ltac:(cs_wr Usp) KP) as K2; clear KP HFr; rename K2 into KP
  end.
Ltac cs_bool H :=
  repeat match type of H with
  | negb _ = true => apply (proj1 (negb_true_iff _)) in H
  | negb _ = false => apply (proj1 (negb_false_iff _)) in H
  end;
  first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H
        | apply (proj1 (Z.ltb_lt _ _)) in H | apply (proj1 (Z.ltb_ge _ _)) in H
        | apply (proj1 (Z.leb_le _ _)) in H | apply (proj1 (Z.leb_gt _ _)) in H
        | apply andb_prop in H | apply orb_prop in H | idtac ].
Lemma cs_len_split1 : forall (A : Type) (l : list A) n, length l = S n -> exists w l', l = w :: l' /\ length l' = n.
Proof. intros A [|w l] n H; [discriminate H | exists w, l; split; [reflexivity | injection H as H; exact H]]. Qed.
Ltac cs_split Hlen :=
  lazymatch type of Hlen with
  | length ?l = O => destruct l; [clear Hlen | discriminate Hlen]
  | length ?l = S _ =>
    let w := fresh "w" in let l' := fresh "ws" in let El := fresh "El" in let Hl := fresh "Hlen" in
    destruct (cs_len_split1 _ l _ Hlen) as (w & l' & El & Hl); clear Hlen; cs_split Hl; subst l
  end.
Ltac cs_after HS HJ SHOK :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in let HEI := fresh "HEI" in
intros ws ms' mat' Hlen HEI HS SHOK HJ HF HFr HG;
cbn [sh_j sh_ss] in Hlen;
let ssZ := fresh "ssZ" in
lazymatch type of HS with
| st_ok_pi ?a1 ?a2 ?a3 ?ssB ?a5 => pose (ssZ := ssB); change (st_ok_pi a1 a2 a3 ssZ a5) in HS
| st_ok ?a1 ?a2 ?ssB ?a4 => pose (ssZ := ssB); change (st_ok a1 a2 ssZ a4) in HS
end;
cs_split Hlen;
subst ssZ;
cbn [sh_j sh_ss extK length Nat.add] in HS, SHOK, HEI;
cbn [ms_mem mkst] in HF, HFr, HG, HJ;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac cs_awr Usp :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
apply cs_awr_of; [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp | vm_compute; reflexivity].
Ltac cs_run RUN HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss = (st', rs)) by (vm_cast_no_check (@eq_refl _ (st', rs)));
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "cs_run: no hypothesis  img_env _ _ E" end in
eapply (RUN W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(unfold A_LIM; cbn; clear; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
cs_after HS HJ SHOK ]
end end
end
| _ => fail "cs_run: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac cs_envtac := cbn [ew ed ewset havoc Nat.eqb Nat.ltb nth Nat.sub]; first [assumption | reflexivity].
Ltac cs_lia1 Dk D1 D2 D3 := clear D1 D2 D3; lia.
Ltac cs_lia0 D1 D2 D3 D4 := clear D1 D2 D3 D4; lia.
Theorem pb_check_sighting : tcheck_sighting_spec.
Proof.
unfold tcheck_sighting_spec.
intros fq ly S W regs mem md ch s f len u st G FB U HPRE0 HROD H10 H11 H12 H13 H14 Hs0 Hs4 Hs63 Hf0 Hf63 Hu0 Hu63
  Hlen Hst Hlen16 HGl HG HFl HF HUl HU Hms Hmf Hmu RAs SHs RAf SHf RAu SHu Ds Df Ois Oif Dsf Du HSF.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (paj_ret_at (PL := PL_both3_0) (PI := PI)) as RET.
pose proof HSF as (L50 & E2b & E3b & _).
pose proof HPRE0 as (HAR & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0' & Hpres0 & _ & HQT).
rewrite getr_regupd8 in Hra0, Hgp0, Htp0 by (vm_compute; discriminate).
assert (Hsp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite getr_regupd8 by (vm_compute; discriminate); reflexivity).
rewrite Hsp in Hstk0', Hpres0.
pose proof (ajournal_init SEGS B TCHECK_SIGHTING_STK [] ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch HPRE0) as HJ.
rewrite Hsp in HJ.
pose proof Hstk0' as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_SIGHTING_STK = 8256) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Bs : s + 24 <= 2 ^ 47 - 1) by (unfold amem_range in Hms; rewrite C3, C4, C5 in Hms; lia).
assert (Bf : f + 50 <= 2 ^ 47 - 1) by (unfold amem_range in Hmf; rewrite C3, C4, C5 in Hmf; lia).
assert (Bu : u + 6 <= 2 ^ 47 - 1) by (unfold amem_range in Hmu; rewrite C3, C4, C5 in Hmu; lia).
assert (HKH : kHighShadowEnd <= spZ regs - TCHECK_SIGHTING_STK) by (rewrite C2; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 12 ltac:(lia)) as HcellR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HgotR, HcellR. change (A_OBJ 0) with 241%nat in HgotR. change (A_OBJ 12) with 253%nat in HcellR.
destruct (cs_entry ly S W regs mem md s f len u G FB HAR Hstk0' Hpres0 H10 H11 H12 H13 Hs0 Hs4 Hf0 Hu0 ltac:(lia)
  HGl HG HFl HF Hms Hmf Hmu RAs RAf Ds Df Ois Oif Dsf fq) as [HS SHOK].
remember (EC regs G FB) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply cs_img).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n) by (intros n Hn; subst E; apply cs_ew_low; exact Hn).
assert (EQ1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (EQ2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EQ3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (EQ4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 u) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 st) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HD0 : ed E 0 = G) by (subst E; reflexivity). assert (HD1 : ed E 1 = FB) by (subst E; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite EQ2; reflexivity).
assert (KP : cs_KEEP (w_H W) (spZ regs) mem mem) by (intros a _ _; reflexivity).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_both3_check_sighting)) with (Z_to_bv 64 (BASE + AF_both3_check_sighting)).
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
cs_keep Usp.
repeat match goal with H : mem_grows _ _ |- _ => clear H | H : frame_of _ _ _ _ |- _ => clear H end.
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msX) |- _ => rename HSx into HS; set (ms1 := msX) in * end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
assert (HspT : spZ (ms_regs ms1) = spZ regs - 64) by (unfold spZ at 1; rewrite Rsp, Usp; apply unsigned_lit_small; lia).
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc setpc].
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fq) W _ _ TCHECK_SIGHTING_STK (spZ regs) []
    ly S W mem md [] ly S _ 0 s (f + 6) 6 (-64) (Z_to_bv 64 (BASE + 10900)) HJ).
  - rewrite Ra0, E10. reflexivity.
  - rewrite Ra1, E11, unsigned_lit_small by lia. reflexivity.
  - exact Ra2.
  - lia. - lia. - lia. - lia. - lia.
  - rewrite HspT. lia.
  - reflexivity. - lia. - rewrite WS, Hes. lia.
  - rewrite Rgp, EQ3. exact Hgp0.
  - rewrite Rtp, EQ4. exact Htp0.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. rewrite HspT, Hes. split; [|cs_lia1 Ds Df Du Dsf]. rewrite (KP a) by cs_lia1 Ds Df Du Dsf.
    apply (cs_aview_some _ _ s (map bv_unsigned G) a HG). rewrite length_map, HGl. lia.
  - intros a Ha. rewrite HspT, Hes. split; [|cs_lia1 Df Ds Du Dsf]. rewrite (KP a) by cs_lia1 Df Ds Du Dsf.
    apply (cs_aview_some _ _ f (map bv_unsigned FB) a HF). rewrite length_map, HFl. lia.
  - intros a Ha. rewrite Hes. cs_lia1 Ds Df Du Dsf.
  - intros a Ha. rewrite Hes. cs_lia1 Df Ds Du Dsf.
  - unfold amem_range in Hms |- *. lia.
  - unfold amem_range in Hmf |- *. lia.
  - apply (cs_ra_keep _ _ _ _ s 6 KP HKH); [lia | lia |]. apply (range_addressable_sub _ _ s 24); [exact RAs | lia | lia].
  - intros _. apply (cs_hull_keep _ _ _ _ s 6 KP HKH); [lia | lia | lia |]. apply (cs_hull_sub _ s 24); [exact SHs | lia | lia | lia].
  - apply (cs_ra_keep _ _ _ _ (f + 6) 6 KP HKH); [lia | lia |]. apply (range_addressable_sub _ _ f 50); [exact RAf | lia | lia].
  - intros _. apply (cs_hull_keep _ _ _ _ (f + 6) 6 KP HKH); [lia | lia | lia |]. apply (cs_hull_sub _ f 50); [exact SHf | lia | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2). clear HJ.
assert (Hv0 : v = w64 0).
{ apply (proj2 Hcmp). intros i Hi. rewrite (KP (s + i)) by cs_lia1 Ds Df Du Dsf. rewrite (KP (f + 6 + i)) by cs_lia1 Df Ds Du Dsf.
  replace (s + i) with (s + Z.of_nat (Z.to_nat i)) by lia. replace (f + 6 + i) with (f + Z.of_nat (6 + Z.to_nat i)) by lia.
  rewrite (cs_aview_garr _ _ _ _ _ HG) by (rewrite length_map; lia).
  rewrite (cs_aview_garr _ _ _ _ _ HF) by (rewrite length_map; lia).
  f_equal. rewrite (nth_indep _ 0 (bv_unsigned (zb 0))) by (rewrite length_map; lia).
  rewrite (nth_indep (map bv_unsigned FB) 0 (bv_unsigned (zb 0))) by (rewrite length_map; lia).
  rewrite !map_nth. exact (cs_nth_eq6 G FB 0 6 (SightLib.bytes_eqb_true _ _ E2b) (Z.to_nat i) ltac:(lia)). }
assert (KP2 : cs_KEEP (w_H W) (spZ regs) mem2 mem).
{ intros a Ha Hn. rewrite (Hfr2 a Ha) by (rewrite Hes; cs_lia0 Ds Df Du Dsf). apply (KP a Ha Hn). }
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply region_kept_aview; [reflexivity | | exact Hpres2]); intros a Ha; apply Hfr2;
  first [ rewrite Usp in Ha | rewrite (HEI 241%nat) in Ha by (cbv; lia) | rewrite (HEI 253%nat) in Ha by (cbv; lia) ];
  rewrite ?Hes; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS2 ltac:(cbn [ms_regs restrict mkst]; rewrite Hv, Hv0; reflexivity) eq_refl) as HS3.
clear HS2.
lazymatch type of HS3 with st_ok_pi _ _ _ ?ssx _ => let ss' := eval vm_compute in ssx in change ssx with ss' in HS3 end.
remember (havoc E 512 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS3.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 512)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply ew_havoc_old; exact Hn).
assert (HD0_2 : ed E2 0 = G) by (rewrite HE2; exact HD0). assert (HD1_2 : ed E2 1 = FB) by (rewrite HE2; exact HD1).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (SHOK2 : sh_ok SEGS CBx cs_SH E2 (mrestrict (w_H W) mem2)).
{ apply (cs_shok (w_H W) mem2 E2 s f).
  - unfold YP0e.U, CBx. cbn [sv_denot]. rewrite OLD2 by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by (unfold SB; lia). reflexivity.
  - unfold YP0e.U. cbn [sv_denot]. rewrite OLD2 by lia. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
  - unfold YP0e.U. cbn [sv_denot]. rewrite OLD2 by lia. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
  - exact Hms. - exact Hmf.
  - apply (cs_ra_keep _ _ _ _ s 24 KP2 HKH); [lia | lia | exact RAs].
  - apply (cs_ra_keep _ _ _ _ f 50 KP2 HKH); [lia | lia | exact RAf]. }
clear KP SHOK. rename KP2 into KP.
paj_run_tok RUN HS3 HJ2 SHOK2 Bspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp2 |].
cs_keep Usp2.
repeat match goal with H : mem_grows _ _ |- _ => clear H | H : frame_of _ _ _ _ |- _ => clear H end.
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msX) |- _ => rename HSx into HS; set (ms2 := msX) in * end.
prreg HS (10%bv : bv 5) Rb0. prreg HS (11%bv : bv 5) Rb1. prreg HS (12%bv : bv 5) Rb2. prreg HS (1%bv : bv 5) Rrb.
prreg HS (2%bv : bv 5) Rspb. prreg HS (3%bv : bv 5) Rgpb. prreg HS (4%bv : bv 5) Rtpb.
assert (HspT2 : spZ (ms_regs ms2) = spZ regs - 64) by (unfold spZ at 1; rewrite Rspb, Usp2; apply unsigned_lit_small; lia).
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc setpc].
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fq) W _ _ TCHECK_SIGHTING_STK (spZ regs) []
    ly S W mem md [] ly S _ 0 s u 6 (-64) (Z_to_bv 64 (BASE + 10920)) HJ2).
  - rewrite Rb0, OLD2, E10 by lia. reflexivity.
  - rewrite Rb1, OLD2, E13 by lia. reflexivity.
  - exact Rb2.
  - lia. - lia. - lia. - lia. - lia.
  - rewrite HspT2. lia.
  - reflexivity. - lia. - rewrite WS, Hes. lia.
  - rewrite Rgpb, OLD2, EQ3 by lia. exact Hgp0.
  - rewrite Rtpb, OLD2, EQ4 by lia. exact Htp0.
  - exact Rrb.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. rewrite HspT2, Hes. split; [|cs_lia1 Ds Df Du Dsf]. rewrite (KP a) by cs_lia1 Ds Df Du Dsf.
    apply (cs_aview_some _ _ s (map bv_unsigned G) a HG). rewrite length_map, HGl. lia.
  - intros a Ha. rewrite HspT2, Hes. split; [|cs_lia1 Du Ds Df Dsf]. rewrite (KP a) by cs_lia1 Du Ds Df Dsf.
    apply (cs_aview_some _ _ u (map bv_unsigned U) a HU). rewrite length_map, HUl. lia.
  - intros a Ha. rewrite Hes. cs_lia1 Ds Df Du Dsf.
  - intros a Ha. rewrite Hes. cs_lia1 Du Ds Df Dsf.
  - unfold amem_range in Hms |- *. lia.
  - exact Hmu.
  - apply (cs_ra_keep _ _ _ _ s 6 KP HKH); [lia | lia |]. apply (range_addressable_sub _ _ s 24); [exact RAs | lia | lia].
  - intros _. apply (cs_hull_keep _ _ _ _ s 6 KP HKH); [lia | lia | lia |]. apply (cs_hull_sub _ s 24); [exact SHs | lia | lia | lia].
  - apply (cs_ra_keep _ _ _ _ u 6 KP HKH); [lia | lia | exact RAu].
  - intros _. apply (cs_hull_keep _ _ _ _ u 6 KP HKH); [lia | lia | lia | exact SHu]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v3 & -> & HJ3 & HP3 & Hv3 & Hcmp3 & Hfr3 & Hpres3). clear HJ2.
assert (Hvn : v3 <> w64 0).
{ intros Hz0. pose proof (proj1 Hcmp3 Hz0) as Hz. clear Hz0. apply (SightLib.bytes_eqb_false _ _ E3b).
  assert (Q : map bv_unsigned (fld G 0 6) = map bv_unsigned (fld U 0 6)).
  { apply (cs_eq_bytes (w_H W) (ms_mem ms2) s u G U 0 0 6); [| | lia | lia |].
    - apply (cs_garr_keep _ _ _ _ s _ KP); [cs_lia1 Ds Df Du Dsf | rewrite length_map; cs_lia1 Ds Df Du Dsf | rewrite length_map; cs_lia1 Ds Df Du Dsf | exact HG].
    - apply (cs_garr_keep _ _ _ _ u _ KP); [cs_lia1 Du Ds Df Dsf | rewrite length_map; cs_lia1 Du Ds Df Dsf | rewrite length_map; cs_lia1 Du Ds Df Dsf | exact HU].
    - intros i Hi. change (Z.of_nat 0) with 0. rewrite !Z.add_0_r. apply Hz. lia. }
  rewrite Q. unfold fld. change (skipn 0 U) with U. rewrite firstn_all2 by lia. reflexivity. }
assert (KP3 : cs_KEEP (w_H W) (spZ regs) mem3 mem).
{ intros a Ha Hn. rewrite (Hfr3 a Ha) by (rewrite Hes; cs_lia0 Ds Df Du Dsf). apply (KP a Ha Hn). }
jafter_call_keep_hi HS 528%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply region_kept_aview; [reflexivity | | exact Hpres3]); intros a Ha; apply Hfr3;
  first [ rewrite Usp2 in Ha | rewrite (HEI2 241%nat) in Ha by (cbv; lia) | rewrite (HEI2 253%nat) in Ha by (cbv; lia) ];
  rewrite ?Hes; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4.
remember (havoc E2 528 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS4.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 528)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (HD0_3 : ed E3 0 = G) by (rewrite HE3; exact HD0_2). assert (HD1_3 : ed E3 1 = FB) by (rewrite HE3; exact HD1_2).
assert (E532 : ew E3 532 = v3) by (rewrite HE3; cbn [ew havoc Nat.ltb Nat.sub nth map CLOB]; exact Hv3).
pose proof (st_ok_pi_add_fact _ _ _ 532%nat (mkAF 1 (2 ^ 64 - 1) 0) HS4) as HS5.
specialize (HS5 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E532; rewrite Z.pow_0_r, Z.mod_1_r;
  pose proof (u64_range v3) as Rv; assert (Hv1 : bv_unsigned v3 <> 0) by (intros Hz; apply Hvn; apply bv_eq; rewrite Hz; reflexivity);
  repeat split; lia)).
clear HS4.
assert (E1_3 : ew E3 1 = getr regs 1) by (rewrite OLD3, OLD2 by lia; exact EQ1).
assert (E10_3 : ew E3 10 = Z_to_bv 64 s) by (rewrite OLD3, OLD2 by lia; exact E10).
assert (E11_3 : ew E3 11 = Z_to_bv 64 f) by (rewrite OLD3, OLD2 by lia; exact E11).
assert (E12_3 : ew E3 12 = Z_to_bv 64 len) by (rewrite OLD3, OLD2 by lia; exact E12).
assert (E14_3 : ew E3 14 = Z_to_bv 64 st) by (rewrite OLD3, OLD2 by lia; exact E14).
assert (E32_3 : ew E3 32 = Z_to_bv 64 SB) by (rewrite OLD3, OLD2 by lia; exact E32).
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
assert (GS3 : garr8 SEGS (mrestrict (w_H W) mem3) s (map bv_unsigned G))
  by (apply (cs_garr_keep _ _ _ _ s _ KP3); [cs_lia1 Ds Df Du Dsf | rewrite length_map; cs_lia1 Ds Df Du Dsf | rewrite length_map; cs_lia1 Ds Df Du Dsf | exact HG]).
assert (GF3 : garr8 SEGS (mrestrict (w_H W) mem3) f (map bv_unsigned FB))
  by (apply (cs_garr_keep _ _ _ _ f _ KP3); [cs_lia1 Df Ds Du Dsf | rewrite length_map; cs_lia1 Df Ds Du Dsf | rewrite length_map; cs_lia1 Df Ds Du Dsf | exact HF]).
lazymatch type of HS5 with st_ok_pi _ _ _ ?ssx _ =>
  assert (D1 : all_disjoint E3 cs_Rs (ss_mem ssx));
  [ let rs' := eval vm_compute in (ss_mem ssx) in change (all_disjoint E3 cs_Rs rs');
    unfold cs_Rs; cbn [all_disjoint]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite Usp3, (HEI3 241%nat), (HEI3 253%nat) by (cbv; lia); rewrite E10_3, unsigned_lit_small by (clear - Hs0 Bs; lia);
    clear - Ds Ois HgotR HcellR Hceil Hslo C1 WS Hs0 Bs; unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Ois;
    repeat match goal with |- _ /\ _ => split end; try exact I; lia | ];
  assert (D2 : all_disjoint E3 cs_Rf (ss_mem ssx));
  [ let rs' := eval vm_compute in (ss_mem ssx) in change (all_disjoint E3 cs_Rf rs');
    unfold cs_Rf; cbn [all_disjoint]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite Usp3, (HEI3 241%nat), (HEI3 253%nat) by (cbv; lia); rewrite E11_3, unsigned_lit_small by (clear - Hf0 Bf; lia);
    clear - Df Oif HgotR HcellR Hceil Hslo C1 WS Hf0 Bf; unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Oif;
    repeat match goal with |- _ /\ _ => split end; try exact I; lia | ]
end.
pose proof (cs_add_sf fq E3 _ _ s f G FB HS5 E10_3 E11_3 HD0_3 HD1_3 HGl HFl GS3 GF3 Hs0 ltac:(clear - Bs; lia) Hf0 ltac:(clear - Bf; lia) Dsf D1 D2) as HS6.
clear HS5.
lazymatch type of HS6 with st_ok_pi _ _ _ ?ssx _ => let ss' := eval vm_compute in ssx in change ssx with ss' in HS6 end.
assert (SHOK3 : sh_ok SEGS CBx cs_SH E3 (mrestrict (w_H W) mem3)).
{ apply (cs_shok (w_H W) mem3 E3 s f).
  - unfold YP0e.U, CBx. cbn [sv_denot]. rewrite E32_3, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by (unfold SB; lia). reflexivity.
  - unfold YP0e.U. cbn [sv_denot]. rewrite E10_3, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
  - unfold YP0e.U. cbn [sv_denot]. rewrite E11_3, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
  - exact Hms. - exact Hmf.
  - apply (cs_ra_keep _ _ _ _ s 24 KP3 HKH); [lia | lia | exact RAs].
  - apply (cs_ra_keep _ _ _ _ f 50 KP3 HKH); [lia | lia | exact RAf]. }
clear KP SHOK2. rename KP3 into KP.
pose proof (SightLib.fu4_range G 20 ltac:(lia)) as FU20. pose proof (SightLib.fu4_range G 8 ltac:(lia)) as FU8.
pose proof (u8_range (nth 12 G (zb 0))) as B12. pose proof (u8_range (nth 13 G (zb 0))) as B13.
pose proof (u8_range (nth 14 G (zb 0))) as B14. pose proof (u8_range (nth 16 FB (zb 0))) as B16.
pose proof (u8_range (nth 17 FB (zb 0))) as B17.
pose proof (proj2 (cs_U_sum32 E3 FB HD1_3 HFl)) as PS.
change (bv_unsigned (nth 12 G (zb 0))) with (fb G 12) in B12. change (bv_unsigned (nth 13 G (zb 0))) with (fb G 13) in B13.
change (bv_unsigned (nth 14 G (zb 0))) with (fb G 14) in B14. change (bv_unsigned (nth 16 FB (zb 0))) with (fb FB 16) in B16.
change (bv_unsigned (nth 17 FB (zb 0))) with (fb FB 17) in B17.
clear Ds Df Du Dsf Ois Oif Hms Hmf Hmu RAu SHu HU HUl E3b E2b HROD.
assert (LR : 0 <= len <= 65535) by lia. assert (LR64 : 0 <= len < 2 ^ 64) by lia. assert (STR : 0 <= st < 2 ^ 64) by lia.
let cs_side := idtac; first [ cs_envtac | exact LR | exact LR64 | exact STR | exact FU20 | exact FU8 | exact HFl
  | (clear; lia) | (clear - PS; lia) | (rewrite HGl; clear; cbn; lia) | (rewrite HFl; clear; cbn; lia) ] in
let cs_hc H :=
  try (fold cs_mask in H); try (fold cs_rem in H); try (fold cs_q36 in H); try (fold cs_sum32 in H);
  lazymatch type of H with
  | branch_taken BC_EQ (sv_denot ?Eb ?a) (sv_denot ?Eb ?b) = ?bv => change ((YP0e.U Eb a =? YP0e.U Eb b) = bv) in H
  | branch_taken BC_NE (sv_denot ?Eb ?a) (sv_denot ?Eb ?b) = ?bv => change (negb (YP0e.U Eb a =? YP0e.U Eb b) = bv) in H
  | branch_taken BC_LTU (sv_denot ?Eb ?a) (sv_denot ?Eb ?b) = ?bv => change ((YP0e.U Eb a <? YP0e.U Eb b) = bv) in H
  | branch_taken BC_GEU (sv_denot ?Eb ?a) (sv_denot ?Eb ?b) = ?bv => change (negb (YP0e.U Eb a <? YP0e.U Eb b) = bv) in H
  | _ => idtac
  end;
  lazymatch type of H with context [YP0e.U ?Ex _] =>
    let E12x := fresh "E12x" in let E14x := fresh "E14x" in let D0x := fresh "D0x" in let D1x := fresh "D1x" in
    let Ey := fresh "Ey" in
    assert (E12x : ew Ex 12 = Z_to_bv 64 len) by (change (ew E3 12 = Z_to_bv 64 len); exact E12_3);
    assert (E14x : ew Ex 14 = Z_to_bv 64 st) by (change (ew E3 14 = Z_to_bv 64 st); exact E14_3);
    assert (D0x : ed Ex 0 = G) by (change (ed E3 0 = G); exact HD0_3);
    assert (D1x : ed Ex 1 = FB) by (change (ed E3 1 = FB); exact HD1_3);
    revert E12x E14x D0x D1x H; generalize Ex; intros Ey E12x E14x D0x D1x H;
    repeat (rewrite U_or in H); repeat (rewrite U_sltu1 in H);
    repeat (rewrite U_and_lit in H by cs_side);
    try (rewrite (cs_U_mask Ey len E12x LR) in H);
    try (rewrite (cs_U_rem Ey len E12x LR) in H);
    try (rewrite (cs_U_q36 Ey len E12x LR) in H);
    try (rewrite (cs_U_sum Ey FB D1x HFl) in H);
    try (rewrite (cs_U_word Ey 0 G 20 D0x) in H by cs_side);
    try (rewrite (cs_U_word Ey 0 G 8 D0x) in H by cs_side);
    try (rewrite (cs_U_byte Ey 0 G 12 D0x) in H by cs_side);
    try (rewrite (cs_U_byte Ey 0 G 13 D0x) in H by cs_side);
    try (rewrite (cs_U_byte Ey 0 G 14 D0x) in H by cs_side);
    try (rewrite (cs_U_byte Ey 1 FB 16 D1x) in H by cs_side);
    try (rewrite (cs_U_byte Ey 1 FB 17 D1x) in H by cs_side);
    try (rewrite (U_atom Ey 12 len E12x LR64) in H);
    try (rewrite (U_atom Ey 14 st E14x STR) in H);
    repeat (rewrite U_lit in H by cs_side);
    clear E12x E14x D0x D1x; try clear Ey
  end;
  change (Z.to_nat 20) with 20%nat in H; change (Z.to_nat 8) with 8%nat in H;
  change (Z.to_nat 12) with 12%nat in H; change (Z.to_nat 13) with 13%nat in H; change (Z.to_nat 14) with 14%nat in H;
  change (Z.to_nat 16) with 16%nat in H; change (Z.to_nat 17) with 17%nat in H;
  rewrite ?cs_lor01, ?Z.lor_0_l in H; rewrite ?cs_land255 in H by cs_side;
  rewrite ?(cs_sw (fu G 20 4)), ?(cs_sw (fu G 8 4)) in H by cs_side;
  cs_bool H in
let cs_fin := idtac;
  unfold zq36, zmask, zrem, geo, fsum, blocksum, s32 in *;
  repeat match goal with H : context [if ?c then _ else _] |- _ => let Hif := fresh "Hif" in destruct c eqn:Hif end;
  repeat match goal with
  | H : (_ =? _) = _ |- _ => cs_bool H
  | H : (_ <? _) = _ |- _ => cs_bool H
  | H : (_ <=? _) = _ |- _ => cs_bool H
  | H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
  | H : (_ || _) = true |- _ => apply orb_prop in H
  | H : (_ && _) = false |- _ => apply andb_false_iff in H
  | H : (_ || _) = false |- _ => apply orb_false_iff in H; destruct H
  end;
  lia in
let cs_pre := idtac;
  try lazymatch goal with H : branch_taken _ _ _ = _ |- _ => cs_hc H; let T := type of H in change (@id Prop T) in H end in
let cs_refute := idtac;
  repeat match goal with
  | H : branch_taken _ _ _ = _ |- _ => cs_hc H; revert H
  | H : @id Prop _ |- _ => unfold id in H; revert H
  end;
  clear - LR STR FU20 FU8 B12 B13 B14 B16 B17 PS HSF;
  destruct HSF as (_ & _ & _ & E4a & E4b & (_ & Hrole & Hdecl) & E6);
  intros;
  first
  [ repeat match goal with H : context [psum _ _] |- _ => clear H | H : context [fb _ _] |- _ => clear H
           | H : context [fu G 8 4] |- _ => clear H end; cs_fin
  | repeat match goal with H : context [psum _ _] |- _ => clear H | H : context [fb _ _] |- _ => clear H
           | H : context [fu G 20 4] |- _ => clear H | H : context [len] |- _ => clear H | H : context [st] |- _ => clear H end; cs_fin
  | repeat match goal with H : context [fu _ _ _] |- _ => clear H | H : context [fb G _] |- _ => clear H
           | H : context [len] |- _ => clear H | H : context [st] |- _ => clear H end; cs_fin
  | repeat match goal with H : context [fu _ _ _] |- _ => clear H | H : context [fb FB _] |- _ => clear H | H : context [psum _ _] |- _ => clear H
           | H : context [len] |- _ => clear H | H : context [st] |- _ => clear H end; cs_fin ] in
let cs_ret := idtac;
  lazymatch goal with HSr : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc), HJr : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let R1 := fresh "R1" in
  prreg HSr (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HSr eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat';
  unfold tcheck_sighting_post; apply apost_base_same_fx;
  exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1; rewrite ?E1_3; unfold YK0s.ret_ok in Hra0; rewrite Hra0; reflexivity |];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJr |];
  split; [eapply (cs_aregs fq (w_H W) Ex _ msc regs [Z_to_bv 64 SB] HSr);
          [ intros n Hn; repeat lazymatch goal with |- ew (ewset ?E0 ?k ?v) n = _ => refine (eq_trans (ew_ewset_other E0 k v n (cs_ne_lt n k Hn eq_refl)) _) end;
            exact (eq_trans (OLD3 n (cs_lt_le n 32 528 Hn eq_refl)) (eq_trans (OLD2 n (cs_lt_le n 32 512 Hn eq_refl)) (EL n (cs_lt_le n 32 A_TEXT Hn eq_refl))))
          | vm_compute; reflexivity ] |];
  split; [apply Permutation_refl | exact KP]
  end in
let rec go := idtac;
  lazymatch goal with HSg : st_ok_pi _ _ _ _ (restrict _ _), HJg : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHg : sh_ok _ _ _ _ _ |- _ =>
  cs_run RUN HSg HJg SHg Bspan; [cs_awr Usp3 |];
  cs_keep Usp3;
  repeat match goal with H : mem_grows _ _ |- _ => clear H | H : frame_of _ _ _ _ |- _ => clear H end;
  lazymatch goal with
  | HS' : st_ok _ _ (setpc _ _) (restrict _ _) |- _ => exfalso; cs_refute
  | HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
    let K := eval vm_compute in (run_K A_LIM CBx cs_SH ss) in
    let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K CBx Bspan cs_SH (start K CBx Bspan cs_SH ss) end in
    lazymatch why with
    | SR_jalr _ => cs_ret
    | SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' Bspan; [cs_pre; go | cs_pre; go]
    | _ => let pc := eval vm_compute in (ss_pc ss) in fail "STUCK" pc why
    end
  end end in
go.
Qed.
End h.
End f.
End d.

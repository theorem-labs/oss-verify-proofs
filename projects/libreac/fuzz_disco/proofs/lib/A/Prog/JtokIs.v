(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 4602 of its 4661 lines of code are new or changed and 310 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntStep.v, with its module paths and module names changed; 583 of its 665 lines of code are new or changed and 4579 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI0s YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import StrlenDef ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import jtok_is_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Section h.
Variable B : asyms.
Definition TJTOK_IS_STK : Z := 48 + 2 * ESTACK.
Definition tjtok_is_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md (kind vk vn : Z) (P T : list byte)
  : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TJTOK_IS_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
         aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
       ((jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regs' 10 = w64 1) \/
       (~ jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regs' 10 = w64 0))).
Definition tjtok_is_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (v x kind vk vp vn : Z) (T slack P : list byte),
  afn_pre SEGS B TJTOK_IS_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W mem ->
  getr regs 10 = w64 v -> getr regs 11 = Z_to_bv 64 kind -> getr regs 12 = w64 x ->
  -2 ^ 31 <= kind < 2 ^ 31 -> -2 ^ 31 <= vk < 2 ^ 31 ->
  0 < v -> v mod 8 = 0 -> v + 20 <= 2 ^ 63 ->
  val_mem SEGS (mrestrict (w_H W) mem) v 8 vp -> val_mem SEGS (mrestrict (w_H W) mem) (v + 8) 8 vn ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 16) 4 (vk mod 2 ^ 32) ->
  0 <= vp < 2 ^ 64 -> 0 <= vn < 2 ^ 64 ->
  amem_range v 20 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 20 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) v 20 ->
  (v + 20 <= spZ regs - TJTOK_IS_STK \/ spZ regs <= v) ->
  ~ In (Z_to_bv 8 0) T ->
  garr8 SEGS (mrestrict (w_H W) mem) x (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) ->
  (- (x + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < x -> x + Z.of_nat (length T + 1 + length slack) <= 2 ^ 63 ->
  Z.of_nat (length T) + 1 < 2 ^ 32 ->
  amem_range x (Z.of_nat (length T + 1)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x (Z.of_nat (length T + 1)) ->
  shadow_hull_vis (aview SEGS (w_H W) mem) x (Z.of_nat (length T + 1)) ->
  (x + Z.of_nat (length T + 1 + length slack) <= spZ regs - TJTOK_IS_STK \/ spZ regs <= x) ->
  (vk = kind -> vn = Z.of_nat (length T) ->
     length P = length T /\ garr8 SEGS (mrestrict (w_H W) mem) vp (map bv_unsigned P) /\
     0 <= vp /\ vp + Z.of_nat (length T) <= 2 ^ 63 /\
     amem_range vp (Z.of_nat (length T)) /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF vp (Z.of_nat (length T)) /\
     (0 < Z.of_nat (length T) -> shadow_hull_vis (aview SEGS (w_H W) mem) vp (Z.of_nat (length T))) /\
     (vp + Z.of_nat (length T) <= spZ regs - TJTOK_IS_STK \/ spZ regs <= vp)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_jtok_is) regs mem md) (tjtok_is_post fq regs ly S W mem md kind vk vn P T).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_strlen).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Lemma getr_regupd8 : forall (regs : bvmap 5 word) v (r : bv 5), r <> 8%bv -> getr (regupd regs 8 v) r = getr regs r.
Proof. intros regs v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. exact Hr. Qed.
Lemma reg_ne8 : forall r : bv 5, bv_unsigned r <> 8 -> r <> 8%bv.
Proof. intros r H X. subst r. apply H. reflexivity. Qed.
Ltac rne8 := apply reg_ne8; cbv; intros X; discriminate X.
Lemma spZ_regupd8 : forall (regs : bvmap 5 word) v, spZ (regupd regs 8 v) = spZ regs.
Proof. intros regs v. unfold spZ. rewrite getr_regupd8 by rne8. reflexivity. Qed.
Lemma afn_pre_s0 : forall STK ly S W (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  AR SEGS B ly S W mem md /\ YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ astk_ok STK ly (spZ regs) /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) /\ qtight S.
Proof.
intros STK ly S W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & _ & HQT).
unfold raZ in Hra4. rewrite spZ_regupd8 in Hstk, Hpres.
rewrite !getr_regupd8 in Hra, Hra4, Hgp, Htp by rne8.
exact (conj HAR (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj Hstk (conj Hpres HQT))))))).
Qed.
Definition JB : sv := SOff 35 0.
Definition jt_regions : smem := [ stack_region 48; got_regionP; bcell_regionP 35 ].
Definition jt_vregion : YP09.region := YP09.mkRegion (Some 10%nat) 0 20 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 4 (SOff 34 0))].
Definition jt_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 8 (2^47 - 24) 3); (34%nat, mkAF 0 (2^32 - 1) 0);
    (35%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition ss_jt : sstate := mkSS AF_jtok_is sr_atoms jt_regions None jt_facts.
Definition jt_SH : list shent := [ mkSHE 10 0 20 ].
Definition JBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition jt_extra (vp vn vk : Z) : list word := map (Z_to_bv 64) [vp; vn; vk mod 2 ^ 32; SHADOW_OFF].
Lemma jt_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch v vp vn vk,
  afn_pre SEGS B TJTOK_IS_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  getr regs 10 = w64 v -> 0 < v -> v mod 8 = 0 -> amem_range v 20 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 20 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (jt_extra vp vn vk))) ss_jt
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_jtok_is)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS JB jt_SH (Eimg (Ereg regs (jt_extra vp vn vk))) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch v vp vn vk HPRE0 H10 Hv0 Hv8 Hvr Hva.
pose proof (afn_pre_s0 _ _ _ _ _ _ _ _ HPRE0) as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TJTOK_IS_STK = 8240) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (jt_extra vp vn vk))).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E34 : ew E 34 = Z_to_bv 64 (vk mod 2 ^ 32)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E307 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v' Hn Hv'. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv'. }
pose proof (Z.mod_pos_bound vk (2 ^ 32) ltac:(lia)) as Hvk.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvr.
split.
- unfold ss_jt. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold jt_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite E307, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E307) by (pose proof (pa_val_range (A_OBJ 66)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 JB SHADOW_OFF);
      [cbn [sv_denot JB]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold jt_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E307) by (pose proof (pa_val_range (A_OBJ 66)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [jt_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E34, E35, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, jt_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E JB 10 v 20 v 0 20 Hva).
  + unfold U, JB. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros a Ha. unfold SHADOW_OFF. lia.
Qed.
Lemma jt_kept_frame : forall E rs H (m m' : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/
    (lo <= base_val E (YP09.r_base r) + YP09.r_wlo r /\ base_val E (YP09.r_base r) + YP09.r_whi r <= hi)) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi HF Hr a Ha Hna. unfold aview, mbyte.
rewrite (frame_of_outside E rs _ _ lo hi (Z_to_bv 64 a) HF Hr); [reflexivity|].
rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma ra_xfer : forall (rd rd' : Z -> option Z) a n, (forall s, 0 <= s < 2 ^ 46 -> rd' s = rd s) ->
  0 <= a -> a + n <= 2 ^ 47 -> range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n Hag H0 H1 H y Hy. destruct (H y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite Hag; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF. lia.
Qed.
Lemma hull_xfer : forall (rd rd' : Z -> option Z) a n, (forall s, 0 <= s < 2 ^ 46 -> rd' s = rd s) ->
  0 <= a -> 0 < n -> a + n <= 2 ^ 47 -> shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n Hag H0 Hn H1 H s Hs. rewrite Hag; [exact (H s Hs)|]. unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.
Lemma hull_sub : forall (rd : Z -> option Z) a n m, 0 <= a -> 0 < m <= n ->
  shadow_hull_vis rd a n -> shadow_hull_vis rd a m.
Proof. intros rd a n m H0 Hm H s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *. lia. Qed.
Lemma jt_arr_view : forall H (m : word -> option byte) p (L : list byte),
  garr8 SEGS (mrestrict H m) p (map bv_unsigned L) ->
  forall j, (j < length L)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (bv_unsigned (nth j L (Z_to_bv 8 0))).
Proof.
intros H m p L G j Hj. unfold aview.
rewrite (garr8_mbyte SEGS _ _ _ j G) by (rewrite length_map; exact Hj).
cbn [option_map]. f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma jt_xfacts : forall W mem memT (regs : bvmap 5 word) x (T slack : list byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
     aview SEGS (w_H W) memT a = aview SEGS (w_H W) mem a) ->
  2 ^ 46 <= spZ regs - TJTOK_IS_STK ->
  ~ In (Z_to_bv 8 0) T -> garr8 SEGS (mrestrict (w_H W) mem) x (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) ->
  (- (x + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < x -> (x + Z.of_nat (length T) + 1 + Z.of_nat (length slack) <= spZ regs - TJTOK_IS_STK \/ spZ regs <= x) ->
  x + Z.of_nat (length T) + 1 <= 2 ^ 47 -> x + Z.of_nat (length T) + 1 + Z.of_nat (length slack) <= 2 ^ 63 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x (Z.of_nat (length T) + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) mem) x (Z.of_nat (length T) + 1) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W mem ->
  first_byte SEGS W memT x (Z.of_nat (length T) + 1) 0 (Z.of_nat (length T)) /\
  (forall a, x <= a < x + (Z.of_nat (length T) + 1) -> aview SEGS (w_H W) memT a <> None) /\
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (Z.of_nat (length T) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) memT) x (Z.of_nat (length T) + 1) /\
  (forall a, x + Z.of_nat (length T) < a < x + Z.of_nat (length T) - (x + Z.of_nat (length T)) mod 8 + 8 ->
     aview SEGS (w_H W) memT a <> None) /\
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memT /\
  (forall i, 0 <= i < Z.of_nat (length T) ->
     aview SEGS (w_H W) memT (x + i) = Some (bv_unsigned (nth (Z.to_nat i) T (Z_to_bv 8 0)))).
Proof.
intros W mem memT regs x T slack K Hlo HT0 GT Hslk Hx0 Hxs Hx47 Hx63 Hxa Hxh Hrom.
assert (Kx : forall a, x <= a < x + Z.of_nat (length T) + 1 + Z.of_nat (length slack) ->
  aview SEGS (w_H W) memT a = aview SEGS (w_H W) mem a) by (intros a Ha; apply K; lia).
assert (Klo : forall s, 0 <= s < 2 ^ 46 -> aview SEGS (w_H W) memT s = aview SEGS (w_H W) mem s) by (intros s Hs; apply K; lia).
assert (Hv : forall j, (j < length T + 1 + length slack)%nat -> aview SEGS (w_H W) memT (x + Z.of_nat j) =
  Some (bv_unsigned (nth j (T ++ Z_to_bv 8 0 :: slack) (Z_to_bv 8 0)))).
{ intros j Hj. rewrite Kx by lia. apply (jt_arr_view (w_H W) mem x _ GT). rewrite length_app. cbn [length]. lia. }
assert (HvT : forall i, 0 <= i < Z.of_nat (length T) ->
  aview SEGS (w_H W) memT (x + i) = Some (bv_unsigned (nth (Z.to_nat i) T (Z_to_bv 8 0)))).
{ intros i Hi. replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. rewrite Hv by lia. rewrite app_nth1 by lia. reflexivity. }
split; [|split; [|split; [|split; [|split; [|split]]]]].
- split; [lia|]. split.
  + intros i Hi. rewrite (HvT i Hi). eexists; split; [reflexivity|]. intros Hz. apply HT0.
    replace (Z_to_bv 8 0) with (nth (Z.to_nat i) T (Z_to_bv 8 0)); [apply nth_In; lia|].
    apply bv_eq. rewrite Hz. reflexivity.
  + intros _. rewrite Hv by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
- intros a Ha. replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia. rewrite Hv by lia. discriminate.
- apply (ra_xfer (aview SEGS (w_H W) mem)); [exact Klo | lia | lia | exact Hxa].
- apply (hull_xfer (aview SEGS (w_H W) mem)); [exact Klo | lia | lia | lia | exact Hxh].
- intros a Ha. replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia. rewrite Hv by lia. discriminate.
- apply (consts_view_keep SEGS _ _ W mem memT Hrom). intros a Ha. apply Klo. unfold MC_CONSTS_LO, MC_CONSTS_HI in Ha. lia.
- exact HvT.
Qed.
Lemma jt_strlen_at : forall (fq : YK11.FPState) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> 0 < x -> 0 <= n -> n + 1 < 2 ^ 32 -> x + n + 1 <= 2 ^ 63 ->
  first_byte SEGS W memT x (n + 1) 0 n -> src_ok SEGS W regsT memT x (n + 1) -> amem_range x (n + 1) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (n + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) memT) x (n + 1) ->
  (forall a, x + n < a < x + n - (x + n) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memT ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 (SIGMA DS___interceptor_trampoline_strlen)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst (fx := fq) regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = w64 n /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros fq W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n o raw HJ Ha0 Hx0 Hn0 Hn32 Hxn Hfb Hsrc Hamr Hra_x Hhull Htail Hrom
  Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at; try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (ASTRLEN fq lyc Sc W regsT memT mdc x n HPRE Ha0 Hx0 Hn0 Hn32 Hxn Hfb Hsrc Hamr Hra_x Hhull Htail Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
Lemma jt_kind_cmp : forall E' vk kind, ew E' 34 = Z_to_bv 64 (vk mod 2 ^ 32) -> ew E' 11 = Z_to_bv 64 kind ->
  -2 ^ 31 <= vk < 2 ^ 31 -> -2 ^ 31 <= kind < 2 ^ 31 ->
  (U E' (SExt true 32 (SOff 34 0)) =? U E' (SOff 11 0)) = (vk =? kind).
Proof.
intros E' vk kind H34 H11 Rvk Rk.
rewrite U_SExt, !U_SOff, H34, H11, !Z.add_0_r.
rewrite unsigned_lit_small by (pose proof (Z.mod_pos_bound vk (2 ^ 32)); lia).
rewrite Z_to_bv_unsigned.
unfold bv_swrap, bv_wrap, zcanon, M64.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
change (2 ^ Z.of_N 32) with (2 ^ 32).
destruct (Z.eqb_spec vk kind) as [Heq|Hne]; [apply Z.eqb_eq | apply Z.eqb_neq]; lia.
Qed.
Lemma jt_finish : forall (fq : YK11.FPState) (regs : bvmap 5 word) ly S W mem md kind vk vn P T regsf memf mdf mat',
  ajournal SEGS B TJTOK_IS_STK (spZ regs) [] ly S W mem md [] ly S W memf mdf 0 ->
  aregs_preserved regs regsf -> getr regsf 1 = getr regs 1 -> YK0s.ret_ok (getr regs 1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
    aview SEGS (w_H W) memf a = aview SEGS (w_H W) mem a) ->
  ((jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regsf 10 = w64 1) \/
   (~ jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regsf 10 = w64 0)) ->
  tjtok_is_post fq regs ly S W mem md kind vk vn P T W
    (mkCfg (mkst (fx := fq) regsf (v_jalr (getr regsf 1) 0) memf (seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdf) mat' mdf)).
Proof.
intros fq regs ly S W mem md kind vk vn P T regsf memf mdf mat' HJ HP H1 Hra HK HQ.
unfold tjtok_is_post; apply apost_base_same_fx. exists ly, S, regsf, memf, (with_vm_backing (m_vm_lazy mdf) mat' mdf).
unfold YK0s.ret_ok in Hra.
split; [rewrite H1, Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split; [exact HP|]. split; [apply Permutation_refl|]. split; [exact HK | exact HQ].
Qed.
Lemma jt_seqz : forall E' (b : word), ew E' 56 = b ->
  (bv_unsigned b = 0 -> sv_denot E' (SAlu ALU_SLTU (SOff 56 0) (SLit 1)) = w64 1) /\
  (bv_unsigned b <> 0 -> sv_denot E' (SAlu ALU_SLTU (SOff 56 0) (SLit 1)) = w64 0).
Proof.
intros E' b Hb. pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
split; intros H0;
rewrite denot_lit_U, U_SAlu, U_SOff, Hb, Z.add_0_r, U_lit by lia;
rewrite (zcanon_id (bv_unsigned b)) by (unfold M64; lia);
cbn [zalu_raw]; destruct (Z.ltb_spec (bv_unsigned b) 1) as [H1|H1]; try lia; reflexivity.
Qed.
Lemma jt_bcmp_result : forall (bres : word) (P T : list byte) (memT : word -> option byte) (W : world SEGS) vp x n,
  length P = length T -> n = Z.of_nat (length T) ->
  (bres = w64 0 <-> forall i, 0 <= i < n -> aview SEGS (w_H W) memT (vp + i) = aview SEGS (w_H W) memT (x + i)) ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W) memT (vp + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W) memT (x + i) = Some (bv_unsigned (nth (Z.to_nat i) T (Z_to_bv 8 0)))) ->
  (bres = w64 0 <-> P = T).
Proof.
intros bres P T memT W vp x n HL Hn Hcmp HvP HvT. rewrite Hcmp. split.
- intros Hall. apply (nth_ext P T (Z_to_bv 8 0) (Z_to_bv 8 0) HL). intros j Hj.
  specialize (Hall (Z.of_nat j) ltac:(lia)). rewrite HvP, HvT in Hall by lia. rewrite Nat2Z.id in Hall.
  injection Hall as Hall. apply bv_eq. exact Hall.
- intros -> i Hi. rewrite HvP, HvT by lia. reflexivity.
Qed.
Theorem pb_jtok_is : tjtok_is_spec.
Proof.
unfold tjtok_is_spec.
intros fq ly S W regs mem md ch v x kind vk vp vn T slack P
  HPRE0 HRO HROM H10 H11 H12 Rkind Rvk Hv0 Hv8 Hv63 Mvp Mvn Mvk Rvp Rvn Hvr Hva Hvh Hvs HT0 GT Hslk Hx0 Hx63 HTl Hxr Hxa Hxh Hxs HPv.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (jt_entry fq ly S W regs mem md ch v vp vn vk HPRE0 H10 Hv0 Hv8 Hvr Hva) as [HS SHOK].
pose proof (ajournal_init SEGS B TJTOK_IS_STK [] ly S W _ mem md ch HPRE0) as HJ. rewrite spZ_regupd8 in HJ.
pose proof (afn_pre_s0 _ _ _ _ _ _ _ _ HPRE0) as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TJTOK_IS_STK = 8240) by reflexivity.
assert (Hs46 : 2 ^ 46 <= spZ regs - TJTOK_IS_STK) by lia.
rewrite Nat2Z.inj_add in Hxr, Hxa, Hxh. change (Z.of_nat 1) with 1 in Hxr, Hxa, Hxh.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvr, Hxr.
pose (RUN := paj_run (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
remember (Eimg (Ereg regs (jt_extra vp vn vk))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (jt_extra vp vn vk)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 kind) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 x) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 vp) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 vn) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (vk mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (jt_extra vp vn vk)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_jtok_is)) with (Z_to_bv 64 (BASE + AF_jtok_is)).
paj_run_tok RUN HS HJ SHOK JBspan. { awr_ok_tac. exact Usp. }
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hna. apply (jt_kept_frame E (ss_mem ss_jt) (w_H W) mem (ms_mem ms) (spZ regs - 48) (spZ regs) HFr); [|exact Ha|lia].
  intros r Hr. cbn [ss_mem ss_jt jt_regions In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base stack_region got_regionP bcell_regionP];
  [right; cbn [base_val]; rewrite Usp; lia | left; lia | left; lia]. }
clear HF HFr HG.
destruct (jt_xfacts W mem (ms_mem ms) regs x T slack K1 Hs46 HT0 GT Hslk Hx0 ltac:(lia) ltac:(lia) ltac:(lia) Hxa Hxh HROM)
  as (Fb & Fsrc & Fra & Fhull & Ftail & From & _).
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10.
assert (Usp1 : spZ (ms_regs ms) = spZ regs + -48).
{ change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)). rewrite R2, Usp. apply unsigned_lit_small. lia. }
pose proof (Z.mod_pos_bound vk (2 ^ 32) ltac:(lia)) as Hvk.
eapply SRr_bind.
{ apply (jt_strlen_at fq W (ms_regs ms) (ms_mem ms) TJTOK_IS_STK (spZ regs) [] ly S W mem md [] ly S _ 0 x
    (Z.of_nat (length T)) (-48) (Z_to_bv 64 (VAL A_TEXT + 11828)) HJ).
  - rewrite R10, E12. reflexivity.
  - exact Hx0.
  - lia.
  - exact HTl.
  - lia.
  - exact Fb.
  - intros a Ha. split; [exact (Fsrc a Ha) | rewrite Usp1; unfold ESTACK; lia].
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - exact Fra.
  - exact Fhull.
  - exact Ftail.
  - exact From.
  - exact Usp1.
  - reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hk10 & Hfr2 & Hpr2).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hna. rewrite Hfr2 by (unfold ESTACK; lia). exact (K1 a Ha Hna). }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpJ2 & _).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split.
  - intros a Ha. cbn [base_val YP09.r_lo YP09.r_hi YP09.r_base] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; [lia | unfold ESTACK; lia].
  - intros a Ha _. cbn [base_val YP09.r_wlo YP09.r_whi YP09.r_base] in Ha. rewrite Usp in Ha.
    apply (apresent_writable SEGS). apply HpJ2. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
clear R1 R2 R3 R4 R10 Usp1 Fb Fsrc Fra Fhull Ftail From K1 Hpr2 Hfr2.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 36)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : env_agree 32 (Ereg regs (jt_extra vp vn vk)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (Fa40 : ew Ea 40 = Z_to_bv 64 (Z.of_nat (length T))).
{ rewrite HEa. unfold havoc, CLOB. cbn [ew map nth Nat.ltb Nat.leb Nat.sub]. exact Hk10. }
assert (Fa10 : ew Ea 10 = Z_to_bv 64 v) by (rewrite OLDa by lia; exact E10).
assert (Fa32 : ew Ea 32 = Z_to_bv 64 vp) by (rewrite OLDa by lia; exact E32).
assert (Fa33 : ew Ea 33 = Z_to_bv 64 vn) by (rewrite OLDa by lia; exact E33).
assert (Fa34 : ew Ea 34 = Z_to_bv 64 (vk mod 2 ^ 32)) by (rewrite OLDa by lia; exact E34).
assert (Fa35 : ew Ea 35 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDa by lia; exact E35).
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
assert (VBa : forall n v', ew Ea n = Z_to_bv 64 v' -> 0 <= v' < 2 ^ 64 -> base_val Ea (Some n) = v').
{ intros n v' Hn Hv'. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv'. }
pose proof (st_ok_pi_add_region Ea _ _ jt_vregion HS eq_refl) as HSv.
match type of HSv with ?t1 -> ?t2 -> _ => assert (HR1 : t1); [|assert (HR2 : t2); [|specialize (HSv HR1 HR2); clear HR1 HR2]] end.
{ unfold region_ok, jt_vregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
  rewrite (VBa 10%nat v Fa10) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (chunk_ok_val SEGS Ea _ v 0 8 (SOff 32 0) vp); [cbn [sv_denot]; rewrite Fa32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2 v 8 vp); [|exact Mvp].
    intros kk Hkk. apply K2; lia.
  - apply (chunk_ok_val SEGS Ea _ v 8 8 (SOff 33 0) vn); [cbn [sv_denot]; rewrite Fa33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2 (v + 8) 8 vn); [|exact Mvn].
    intros kk Hkk. apply K2; lia.
  - apply (chunk_ok_val SEGS Ea _ v 16 4 (SOff 34 0) (vk mod 2 ^ 32)); [cbn [sv_denot]; rewrite Fa34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2 (v + 16) 4 (vk mod 2 ^ 32)); [|exact Mvk].
    intros kk Hkk. apply K2; lia. }
{ apply all_disjoint_of_extents. unfold extent_of_region, jt_vregion. cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VBa 10%nat v Fa10) by lia. cbn [base_val]. rewrite Uspa. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; try lia; try exact I. }
clear HS. rename HSv into HS.
assert (SHOKa : sh_ok SEGS JB jt_SH Ea (mrestrict (w_H W) mem2)).
{ unfold sh_ok, jt_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem2 Ea JB 10 v 20 v 0 20).
  + apply (ra_xfer (aview SEGS (w_H W) mem)); [intros s Hs; apply K2; lia | lia | lia | exact Hva].
  + unfold U, JB. cbn [sv_denot]. rewrite Fa35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite Fa10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros a Ha. unfold SHADOW_OFF. lia. }
clear SHOK.
paj_run_tok RUN HS HJ2 SHOKa JBspan. { awr_ok_tac; exact Uspa. }
remember (ewset (ewset Ea 512 w) 513 w0) as Eb eqn:HEb in HS, SHOKa, HEI1.
assert (OLDb : forall n, (n < 512)%nat -> ew Eb n = ew Ea n) by (intros n Hn; rewrite HEb; rewrite !ew_ewset_other by lia; reflexivity).
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hna. rewrite (jt_kept_frame Ea _ (w_H W) mem2 (ms_mem ms0) (spZ regs - 48) (spZ regs) HFr); [exact (K2 a Ha Hna) | | exact Ha | lia].
  intros r Hr. cbn [ss_mem In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base jt_vregion];
  [left; lia | right; cbn [base_val]; rewrite Uspa; lia]. }
clear HF HFr HG.
assert (Fb11 : ew Eb 11 = Z_to_bv 64 kind) by (rewrite OLDb, OLDa by lia; exact E11).
assert (Fb34 : ew Eb 34 = Z_to_bv 64 (vk mod 2 ^ 32)) by (rewrite OLDb by lia; exact Fa34).
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact Uspa).
assert (HAEb : env_agree 32 (Ereg regs (jt_extra vp vn vk)) Eb).
{ split; [intros n Hn; rewrite OLDb by lia; exact (proj1 HAEa n Hn) | rewrite HEb; exact (proj2 HAEa)]. }
assert (Fb1 : ew Eb 1 = getr regs 1) by (rewrite OLDb, OLDa by lia; exact E1).
pose (RET := paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)).
psrr_branch_tok RUN BR HS SHOKa JBspan.
- rewrite branch_ne_U, (jt_kind_cmp Eb vk kind Fb34 Fb11 Rvk Rkind) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ2 SHOKa JBspan. { awr_ok_tac; exact Uspb. }
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hna. rewrite (jt_kept_frame Eb _ (w_H W) (ms_mem ms0) (ms_mem ms1) (spZ regs - 48) (spZ regs) HFr);
      [exact (K3 a Ha Hna) | | exact Ha | lia].
    intros r Hr. cbn [ss_mem add_cond In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base jt_vregion];
    [left; lia | right; cbn [base_val]; rewrite Uspb; lia]. }
  prreg HS (1%bv : bv 5) R1f. prreg HS (10%bv : bv 5) R10f.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  apply jt_finish.
  + exact HJ2.
  + eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs (jt_extra vp vn vk) HS); [exact HAEb | vm_compute; reflexivity].
  + rewrite R1f. exact Fb1.
  + exact Hra.
  + exact K4.
  + right. split; [intros (Hm & _); exact (Hc Hm) | rewrite R10f; reflexivity].
- rewrite branch_ne_U, (jt_kind_cmp Eb vk kind Fb34 Fb11 Rvk Rkind) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ2 SHOKa JBspan. { awr_ok_tac; exact Uspb. }
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hna. rewrite (jt_kept_frame Eb _ (w_H W) (ms_mem ms0) (ms_mem ms1) (spZ regs - 48) (spZ regs) HFr);
      [exact (K3 a Ha Hna) | | exact Ha | lia].
    intros r Hr. cbn [ss_mem add_cond In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base jt_vregion];
    [left; lia | right; cbn [base_val]; rewrite Uspb; lia]. }
  clear HF HFr HG.
  assert (Fb33 : ew Eb 33 = Z_to_bv 64 vn) by (rewrite OLDb by lia; exact Fa33).
  assert (Fb40 : ew Eb 40 = Z_to_bv 64 (Z.of_nat (length T))) by (rewrite OLDb by lia; exact Fa40).
  psrr_branch_tok RUN BR HS SHOKa JBspan.
  + rewrite branch_ne_U, (U_atom Eb 33 vn Fb33), (U_atom Eb 40 (Z.of_nat (length T)) Fb40) in Hc0 by lia.
    apply negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_tok RUN HS HJ2 SHOKa JBspan. { awr_ok_tac; exact Uspb. }
    assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
    { intros a Ha Hna. rewrite (jt_kept_frame Eb _ (w_H W) (ms_mem ms1) (ms_mem ms2) (spZ regs - 48) (spZ regs) HFr);
        [exact (K4 a Ha Hna) | | exact Ha | lia].
      intros r Hr. cbn [ss_mem add_cond In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base jt_vregion];
      [left; lia | right; cbn [base_val]; rewrite Uspb; lia]. }
    prreg HS (1%bv : bv 5) R1f. prreg HS (10%bv : bv 5) R10f.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    apply jt_finish.
    * exact HJ2.
    * eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs (jt_extra vp vn vk) HS); [exact HAEb | vm_compute; reflexivity].
    * rewrite R1f. exact Fb1.
    * exact Hra.
    * exact K5.
    * right. split; [intros (_ & Hm & _); apply Hc0; rewrite unsigned_lit_small in Hm by lia; exact Hm | rewrite R10f; reflexivity].
  + rewrite branch_ne_U, (U_atom Eb 33 vn Fb33), (U_atom Eb 40 (Z.of_nat (length T)) Fb40) in Hc0 by lia.
    apply negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_tok RUN HS HJ2 SHOKa JBspan. { awr_ok_tac; exact Uspb. }
    assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
    { intros a Ha Hna. rewrite (jt_kept_frame Eb _ (w_H W) (ms_mem ms1) (ms_mem ms2) (spZ regs - 48) (spZ regs) HFr);
        [exact (K4 a Ha Hna) | | exact Ha | lia].
      intros r Hr. cbn [ss_mem add_cond In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base jt_vregion];
      [left; lia | right; cbn [base_val]; rewrite Uspb; lia]. }
    clear HF HFr HG.
    destruct (jt_xfacts W mem (ms_mem ms2) regs x T slack K5 Hs46 HT0 GT Hslk Hx0 ltac:(lia) ltac:(lia) ltac:(lia) Hxa Hxh HROM)
      as (_ & Fsrc3 & Fra3 & Fhull3 & _ & _ & FvT).
    destruct (HPv Hc Hc0) as (HlenP & GP & HvP0 & HvP63 & HvPr & HvPa & HvPh & HvPs).
    pose proof HvPr as HvPr'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HvPr'.
    assert (FvP : forall i, 0 <= i < Z.of_nat (length T) ->
      aview SEGS (w_H W) (ms_mem ms2) (vp + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))).
    { intros i Hi. rewrite K5 by lia. replace (vp + i) with (vp + Z.of_nat (Z.to_nat i)) by lia.
      apply (jt_arr_view (w_H W) mem vp P GP). lia. }
    assert (Fb3 : ew Eb 3 = getr regs 3) by (rewrite OLDb, OLDa by lia; exact E3).
    assert (Fb4 : ew Eb 4 = getr regs 4) by (rewrite OLDb, OLDa by lia; exact E4).
    assert (Fb12 : ew Eb 12 = Z_to_bv 64 x) by (rewrite OLDb, OLDa by lia; exact E12).
    assert (Fb32 : ew Eb 32 = Z_to_bv 64 vp) by (rewrite OLDb by lia; exact Fa32).
    assert (Fb35 : ew Eb 35 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDb by lia; exact Fa35).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    assert (Usp3 : spZ (ms_regs ms2) = spZ regs + -48).
    { change (spZ (ms_regs ms2)) with (bv_unsigned (getr (ms_regs ms2) 2)). rewrite Q2, Uspb. apply unsigned_lit_small. lia. }
    eapply SRr_bind.
    { apply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq) W (ms_regs ms2) (ms_mem ms2)
        TJTOK_IS_STK (spZ regs) [] ly S W mem md [] ly S _ 0 vp x (Z.of_nat (length T)) (-48)
        (Z_to_bv 64 (VAL A_TEXT + 11916)) HJ2).
      - rewrite Q10, Fb32. reflexivity.
      - rewrite Q11, Fb12. reflexivity.
      - rewrite Q12, Fb40. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact Usp3.
      - reflexivity.
      - lia.
      - unfold ESTACK. lia.
      - rewrite Q3, Fb3. exact Hgp.
      - rewrite Q4, Fb4. exact Htp.
      - exact Q1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split; [|rewrite Usp3; unfold ESTACK; lia].
        replace a with (vp + (a - vp)) by lia. rewrite FvP by lia. discriminate.
      - intros a Ha. split; [apply Fsrc3; lia | rewrite Usp3; unfold ESTACK; lia].
      - intros a Ha. unfold ESTACK. lia.
      - intros a Ha. unfold ESTACK. lia.
      - exact HvPr.
      - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
      - apply (ra_xfer (aview SEGS (w_H W) mem)); [intros s Hs; apply K5; lia | lia | lia | exact HvPa].
      - intros Hn. apply (hull_xfer (aview SEGS (w_H W) mem)); [intros s Hs; apply K5; lia | lia | lia | lia | exact (HvPh Hn)].
      - apply (range_addressable_sub _ _ x (Z.of_nat (length T) + 1)); [exact Fra3 | lia | lia].
      - intros Hn. apply (hull_sub _ x (Z.of_nat (length T) + 1)); [lia | lia | exact Fhull3]. }
    intros W3 c3 _ (-> & regs3 & mem3 & md3 & bres & -> & HJ3 & HP3 & Hv3 & Hcmp & Hfr3 & Hpr3).
    assert (K6 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
      aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
    { intros a Ha Hna. rewrite Hfr3 by (unfold ESTACK; lia). exact (K5 a Ha Hna). }
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpJ3 & _).
    jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W) mem3) HP3 [1]%nat HS3.
    match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
      split.
      - intros a Ha. cbn [base_val YP09.r_lo YP09.r_hi YP09.r_base] in Ha. rewrite Uspb in Ha.
        apply (mbyte_of_aview SEGS). apply Hfr3; [lia | unfold ESTACK; lia].
      - intros a Ha _. cbn [base_val YP09.r_wlo YP09.r_whi YP09.r_base] in Ha. rewrite Uspb in Ha.
        apply (apresent_writable SEGS). apply HpJ3. lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
    remember (havoc Eb 52 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
    assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [assumption | cbv; lia]).
    assert (OLDc : forall n, (n < 52)%nat -> ew Ec n = ew Eb n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
    assert (HAEc : env_agree 32 (Ereg regs (jt_extra vp vn vk)) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
    assert (Fc56 : ew Ec 56 = bres).
    { rewrite HEc. unfold havoc, CLOB. cbn [ew map nth Nat.ltb Nat.leb Nat.sub]. exact Hv3. }
    assert (Fc1 : ew Ec 1 = getr regs 1) by (rewrite OLDc by lia; exact Fb1).
    assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact Uspb).
    assert (SHOKc : sh_ok SEGS JB [] Ec (mrestrict (w_H W) mem3)) by constructor.
    paj_run_tok RUN HS HJ3 SHOKc JBspan. { awr_ok_tac; exact Uspc. }
    assert (K7 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a).
    { intros a Ha Hna. rewrite (jt_kept_frame Ec _ (w_H W) mem3 (ms_mem ms3) (spZ regs - 48) (spZ regs) HFr);
        [exact (K6 a Ha Hna) | | exact Ha | lia].
      intros r Hr. cbn [ss_mem In] in Hr. destruct Hr as [<-|[]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base];
      right; cbn [base_val]; rewrite Uspc; lia. }
    pose proof (jt_bcmp_result bres P T (ms_mem ms2) W vp x (Z.of_nat (length T)) HlenP eq_refl Hcmp FvP FvT) as HPT.
    prreg HS (1%bv : bv 5) R1f.
    pose proof (st_ok_pi_restrict_reg (w_H W) Ec _ ms3 10%bv HS) as R10f.
    lazymatch type of R10f with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in R10f end.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    apply jt_finish.
    * exact HJ3.
    * eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (jt_extra vp vn vk) HS); [exact HAEc | vm_compute; reflexivity].
    * rewrite R1f. exact Fc1.
    * exact Hra.
    * exact K7.
    * unfold jtok_match. destruct (Z.eq_dec (bv_unsigned bres) 0) as [H0|H0].
      -- left. assert (Hb0 : bres = w64 0) by (apply bv_eq; rewrite H0; reflexivity).
         split; [split; [exact Hc | split; [rewrite unsigned_lit_small by lia; exact Hc0 | exact (proj1 HPT Hb0)]] |].
         rewrite R10f. exact (proj1 (jt_seqz Ec bres Fc56) H0).
      -- right. split; [intros (_ & _ & HPT'); apply H0; rewrite (proj2 HPT HPT'); reflexivity |].
         rewrite R10f. exact (proj2 (jt_seqz Ec bres Fc56) H0).
Qed.
End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 691 of its 732 lines of code are new or changed and 504 lines of the source are left out. *)
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YA0o YCbm YA0q YG0s YC1h YC85 YC88 YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma ct_nth_skipn : forall (A : Type) (l : list A) i n d, nth n (skipn i l) d = nth (i + n) l d.
Proof. intros A l i. revert l. induction i as [|i IH]; intros l n d; [reflexivity|]. destruct l as [|x l]; [destruct n; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity. Qed.
Lemma ct_nth_firstn : forall (A : Type) n (l : list A) i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A n. induction n as [|n IH]; intros l i d Hi; [lia|]. destruct l as [|x l]; [destruct i; reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma ct_u8 : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.
Lemma ct_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (ct_u8 b) as Hb.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma ct_s32_small : forall u, 0 <= u < 2 ^ 32 -> 0 <= bv_swrap 32 u -> bv_swrap 32 u = u.
Proof.
intros u Hu H. unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
change (bv_modulus 32) with (2 ^ 32) in *. lia.
Qed.
Lemma ct_val4 : forall segs m t (T : list byte) k, garr8 segs m t (map bv_unsigned T) -> length T = 400%nat -> 0 <= k -> k + 4 <= 400 ->
  val_mem segs m (t + k) 4 (u_at T k 4) /\ 0 <= u_at T k 4 < 2 ^ 32.
Proof.
intros segs m t T k HG HL Hk Hk4.
assert (HB : forall j, (j < 4)%nat -> mbyte segs m (t + k + Z.of_nat j) = Some (Z_to_bv 8 (bv_unsigned (nth (Z.to_nat k + j) T (Z_to_bv 8 0))))).
{ intros j Hj. replace (t + k + Z.of_nat j) with (t + Z.of_nat (Z.to_nat k + j)) by lia.
  rewrite (garr8_mbyte segs m t _ (Z.to_nat k + j) HG) by (rewrite length_map; lia).
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth. reflexivity. }
unfold u_at, sub.
assert (HN : forall j, nth j (skipn (Z.to_nat k) T) (Z_to_bv 8 0) = nth (Z.to_nat k + j) T (Z_to_bv 8 0)) by (intros j; apply ct_nth_skipn).
assert (HRl : (4 <= length (skipn (Z.to_nat k) T))%nat) by (rewrite length_skipn; lia).
revert HN HRl. generalize (skipn (Z.to_nat k) T) as R. intros R HN HRl.
destruct R as [|b0 [|b1 [|b2 [|b3 R']]]]; cbn [length] in HRl; try lia.
cbn [firstn]. rewrite !ct_ble_cons. change (firstn 0 R') with (@nil byte). cbn [bytes_le_to_Z].
pose proof (ct_u8 b0) as R0. pose proof (ct_u8 b1) as R1. pose proof (ct_u8 b2) as R2. pose proof (ct_u8 b3) as R3.
split; [|clear - R0 R1 R2 R3; lia].
intros j Hj. rewrite HB by exact Hj. rewrite <- HN. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
destruct j as [|[|[|[|j]]]]; [| | | | lia]; cbn [nth].
- change (8 * Z.of_nat 0) with 0. change (2 ^ 0) with 1. clear - R0 R1 R2 R3. lia.
- change (8 * Z.of_nat 1) with 8. change (2 ^ 8) with 256. clear - R0 R1 R2 R3. lia.
- change (8 * Z.of_nat 2) with 16. change (2 ^ 16) with 65536. clear - R0 R1 R2 R3. lia.
- change (8 * Z.of_nat 3) with 24. change (2 ^ 24) with 16777216. clear - R0 R1 R2 R3. lia.
Qed.
Lemma ct_val4_s32 : forall segs m t (T : list byte) k, garr8 segs m t (map bv_unsigned T) -> length T = 400%nat -> 0 <= k -> k + 4 <= 400 ->
  0 <= s32_at T k -> val_mem segs m (t + k) 4 (s32_at T k) /\ 0 <= s32_at T k < 2 ^ 32.
Proof.
intros segs m t T k HG HL Hk Hk4 Hs. destruct (ct_val4 segs m t T k HG HL Hk Hk4) as [HV HR].
unfold s32_at in *. rewrite ct_s32_small by assumption. split; assumption.
Qed.
Lemma ct_aview_T : forall segs (H : word -> bool) m t (T : list byte) k, garr8 segs (mrestrict H m) t (map bv_unsigned T) -> length T = 400%nat -> 0 <= k < 400 ->
  aview segs H m (t + k) = Some (bv_unsigned (nth (Z.to_nat k) T (Z_to_bv 8 0))).
Proof.
intros segs H m t T k HG HL Hk. unfold aview.
replace (t + k) with (t + Z.of_nat (Z.to_nat k)) by lia.
rewrite (garr8_mbyte segs _ t _ (Z.to_nat k) HG) by (rewrite length_map; lia).
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth.
cbn [option_map]. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma ct_mac_eq : forall segs (H : word -> bool) m t (T : list byte) i j, garr8 segs (mrestrict H m) t (map bv_unsigned T) -> length T = 400%nat ->
  0 <= i -> 0 <= j -> j < 8 -> i < 8 ->
  (forall k, 0 <= k < 6 -> aview segs H m (t + 48 * i + k) = aview segs H m (t + 48 * j + k)) ->
  mac_of T i = mac_of T j.
Proof.
intros segs H m t T i j HG HL Hi Hj Hj8 Hi8 HE. unfold mac_of, sub.
apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
- rewrite !length_firstn, !length_skipn. lia.
- intros n Hn. rewrite length_firstn, length_skipn in Hn.
  rewrite !ct_nth_firstn by lia. rewrite !ct_nth_skipn.
  pose proof (HE (Z.of_nat n) ltac:(lia)) as Q.
  rewrite <- !Z.add_assoc in Q.
  rewrite !(ct_aview_T segs H m t T) in Q by (first [exact HG | exact HL | lia]).
  injection Q as Q. apply bv_eq.
  replace (Z.to_nat (48 * i) + n)%nat with (Z.to_nat (48 * i + Z.of_nat n)) by lia.
  replace (Z.to_nat (48 * j) + n)%nat with (Z.to_nat (48 * j + Z.of_nat n)) by lia.
  exact Q.
Qed.
Lemma ct_kept_run : forall segs (H : word -> bool) E rs (m m' m0 : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs H m a = aview segs H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs H m' a = aview segs H m0 a.
Proof.
intros segs H E rs m m' m0 lo hi HF HW HK a Ha Hn. rewrite <- (HK a Ha Hn). apply aview_eq_of. apply HF.
rewrite unsigned_lit_small by lia. intros X. apply Hn. apply HW. exact X.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Definition TCHECK_TABLE_STK : Z := 96 + 2 * ESTACK.
Definition tcheck_table_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TCHECK_TABLE_STK [] regs ly S W mem md 0 (fun ly' S' W' _ mem' _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCHECK_TABLE_STK <= a < spZ regs) ->
         aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)).
Definition tcheck_table_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t : Z) (T : list byte),
  afn_pre SEGS B TCHECK_TABLE_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 t -> 0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  amem_range t 400 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) t 400 ->
  (t + 400 <= spZ regs - TCHECK_TABLE_STK \/ spZ regs <= t) ->
  off_img t 400 ->
  tbl_T1 T -> tbl_T2 T -> tbl_T3 T ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_check_table) regs mem md) (tcheck_table_post fq regs ly S W mem md).

Definition CT_SB : Z := 0x7fff8000.
Definition CT_Bx0 : sv := SOff 32 0.
Definition CT_Bspan : Z * Z := (CT_SB, CT_SB + 2 ^ 44 - 1).
Definition CT_SH0 : list shent := [mkSHE 10 0 400].
Definition ct_tab_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 400 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 33 0))].
Definition ct_regions : smem := [stack_region 96; got_regionP; bcell_regionP 32; ct_tab_region].
Definition ct_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 401) 3); (33%nat, mkAF 0 8 0); (32%nat, mkAF CT_SB CT_SB 0)] [] [].
Definition ss_ct : sstate := mkSS AF_both3_check_table sr_atoms ct_regions None ct_facts.
Definition ct_extra (n : Z) : list word := map (Z_to_bv 64) [CT_SB; n].
Lemma ct_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md (t : Z) (T : list byte),
  AR SEGS B ly S W mem md -> astk_ok TCHECK_TABLE_STK ly (spZ regs) ->
  (forall a, spZ regs - TCHECK_TABLE_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 t -> 0 < t -> t mod 8 = 0 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  amem_range t 400 -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  (t + 400 <= spZ regs - TCHECK_TABLE_STK \/ spZ regs <= t) -> off_img t 400 -> tbl_T1 T ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (ct_extra (n_of T)))) ss_ct
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_check_table)) mem (seg_rom SEGS))) /\
  sh_ok SEGS CT_Bx0 CT_SH0 (Eimg (Ereg regs (ct_extra (n_of T)))) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md t T HAR Hstk Hpres G10 Ht0 Ht8 HLT HGT HAM HRA HOW HOI T1.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity.
unfold tbl_T1 in T1.
destruct (ct_val4_s32 SEGS (mrestrict (w_H W) mem) t T 384 HGT HLT ltac:(lia) ltac:(lia) ltac:(unfold n_of in T1; lia)) as [VN RN].
fold (n_of T) in VN, RN.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
set (E := Eimg (Ereg regs (ct_extra (n_of T)))).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E32 : ew E 32 = Z_to_bv 64 CT_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (n_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall kk v, ew E kk = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some kk) = v).
{ intros kk v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp. fold (spZ regs) in Rsp.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
split.
- rewrite restrict_mkst_fx. unfold ss_ct. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ct_regions, ct_tab_region, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CT_Bx0 CT_SB);
      [cbn [sv_denot CT_Bx0]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold CT_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat t E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ t 384 4 _ (n_of T)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VN].
  + apply pairwise_disjoint_of_extents. unfold ct_regions, ct_tab_region, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [ct_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold CT_SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold CT_SB in *. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, CT_SH0. constructor; [|constructor].
  eapply shent_ok_of_range; [exact HRA | unfold CT_Bx0; rewrite (U_atom E 32 CT_SB E32) by (unfold CT_SB; lia); reflexivity
    | rewrite (U_atom E 10 t E10) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF in *; lia].
Qed.

Definition L_OUT : Z := 0x28b0.
Definition L_IN : Z := 0x28ec.
Definition L_EPI : Z := 0x2938.

Ltac ct_awr Usp :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  let aw := fresh "aw" in let rw := fresh "rw" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros aw (rw & Hin & Ha); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Ha;
    first [ exfalso; lia
          | left; rewrite Usp in Ha; lia ] | ]); try destruct Hin.
Ltac ct_wr Usp :=
  let aw := fresh "aw" in let rw := fresh "rw" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros aw (rw & Hin & Ha);
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rw rs1) in Hin end;
  cbn [In] in Hin; cbv beta;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Ha;
     first [ exfalso; lia
           | rewrite Usp in Ha; lia ] | ]); try destruct Hin.

Definition LSTK : Z := 2 * ESTACK.
Definition NOTT : afact := mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 2) 0.
Definition CT_Bx : sv := SOff 18 0.
Definition sr_lit : list sv := sr_set (sr_set sr_atoms 23%bv (SLit 2)) 24%bv (SLit 7).
Definition LKEPT : list (bv 5) := [2; 3; 4; 8; 18; 19; 21; 23; 24; 26; 27]%bv.
Definition LKEPTA : list (bv 5) := [2; 3; 4; 8; 18; 19; 21; 26; 27]%bv.
Definition ct_kept0 (regs0 regs : bvmap 5 word) : Prop := forall r, In r LKEPT -> getr regs r = getr regs0 r.
Definition ct_r0 (regs0 : bvmap 5 word) (sp0 t n : Z) : Prop :=
  getr regs0 2 = Z_to_bv 64 (sp0 - 96) /\ getr regs0 3 = w64 (as_gp B) /\ getr regs0 4 = w64 (as_tp B) /\
  getr regs0 8 = Z_to_bv 64 t /\ getr regs0 18 = Z_to_bv 64 CT_SB /\ getr regs0 19 = Z_to_bv 64 n /\
  getr regs0 21 = Z_to_bv 64 (2 ^ 64 - 1 - t) /\ getr regs0 23 = Z_to_bv 64 2 /\ getr regs0 24 = Z_to_bv 64 7.
Definition ct_tab (W : world SEGS) (sp0 t : Z) (T : list byte) (mem : word -> option byte) : Prop :=
  0 < t /\ t mod 8 = 0 /\ length T = 400%nat /\ garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) /\
  amem_range t 400 /\ range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) t 400 /\ (t + 400 <= sp0 - TCHECK_TABLE_STK \/ sp0 <= t) /\
  tbl_T1 T /\ tbl_T2 T /\ tbl_T3 T.
Definition ct_mem (W : world SEGS) (sp0 : Z) (mem memc : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - TCHECK_TABLE_STK <= a < sp0) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a.
Definition ct_lpost (fq : YK11.FPState) (regs0 : bvmap 5 word) (W : world SEGS) (sp0 : Z) (mem : word -> option byte)
  (lyc : alayout) (Sc : astate) (memL : word -> option byte) (mdL : Model) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + L_EPI)) mem' (seg_rom SEGS)) md' /\
    ajournal SEGS B LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc W mem' md' 0 /\
    ct_kept0 regs0 regs' /\ ct_mem W sp0 mem mem'.
Lemma ct_kept0_step : forall regs0 regs regs', ct_kept0 regs0 regs -> getr regs0 23 = Z_to_bv 64 2 -> getr regs0 24 = Z_to_bv 64 7 ->
  (forall r, In r LKEPTA -> getr regs' r = getr regs r) -> getr regs' 23 = Z_to_bv 64 2 -> getr regs' 24 = Z_to_bv 64 7 -> ct_kept0 regs0 regs'.
Proof.
intros regs0 regs regs' HK H23 H24 HA G23 G24 r Hr. cbv [LKEPT In] in Hr.
repeat (destruct Hr as [<-|Hr]; [first [rewrite G23; symmetry; exact H23 | rewrite G24; symmetry; exact H24
  | rewrite HA by (cbv; tauto); apply HK; cbv; tauto] |]). destruct Hr.
Qed.
Lemma ct_denot48 : forall E nb ni b x, ew E nb = Z_to_bv 64 b -> ew E ni = Z_to_bv 64 x -> 0 <= b -> 0 <= x < 8 -> b + 48 * x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff nb 0) (SMd M_MUL (SOff ni 0) (SLit 48))) = Z_to_bv 64 (b + 48 * x).
Proof.
intros E nb ni b x Hb Hx Rb Rx Rbx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom E ni x Hx), (U_atom E nb b Hb) by lia.
rewrite (zcanon_id 48) by (unfold M64; lia). rewrite (zcanon_id (x * 48)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma ct_memc : forall W sp0 t T mem memc, ct_tab W sp0 t T mem -> ct_mem W sp0 mem memc -> alloc_ceiling <= sp0 - TCHECK_TABLE_STK ->
  garr8 SEGS (mrestrict (w_H W) memc) t (map bv_unsigned T) /\ range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) t 400.
Proof.
intros W sp0 t T mem memc (Ht0 & Ht8 & HLT & HGT & HAM & HRA & HSV & HOW & T1 & T2 & T3) HM Hc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity.
split; [|split].
- apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem memc t); [|exact HGT].
  intros a Ha. rewrite length_map, HLT in Ha. apply HM; lia.
- apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) memc) (sp0 - TCHECK_TABLE_STK) sp0 t 400); [intros s Hs1 Hs2; apply HM; assumption | lia | lia | lia | exact HRA].
- apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) memc) (sp0 - TCHECK_TABLE_STK) sp0 t 400); [intros s Hs1 Hs2; apply HM; assumption | lia | lia | lia | lia | exact HSV].
Qed.
Lemma ct_src : forall (H : word -> bool) m t (T : list byte) a, garr8 SEGS (mrestrict H m) t (map bv_unsigned T) -> length T = 400%nat ->
  t <= a < t + 400 -> aview SEGS H m a <> None.
Proof.
intros H m t T a HG HL Ha. replace a with (t + (a - t)) by lia. rewrite (ct_aview_T SEGS H m t T (a - t) HG HL) by lia. discriminate.
Qed.
Lemma ct_hull_sub : forall rd x n a m, shadow_hull_vis rd x n -> x <= a -> a + m <= x + n -> 0 < m -> shadow_hull_vis rd a m.
Proof.
intros rd x n a m H Hxa Ham Hm s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x a 8 ltac:(lia) Hxa) as D1.
pose proof (Z.div_le_mono (a + m - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
assert (D3 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + a / 8) / 8) by (apply Z.div_le_mono; lia).
assert (D4 : (SHADOW_OFF + (a + m - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma ct_bcmp_ne : forall W sp0 t T mem memT i j (v : word),
  ct_tab W sp0 t T mem -> garr8 SEGS (mrestrict (w_H W) memT) t (map bv_unsigned T) -> 0 <= i -> i < j -> j < n_of T ->
  (v = w64 0 <-> forall k, 0 <= k < 6 -> aview SEGS (w_H W) memT (t + 48 * i + k) = aview SEGS (w_H W) memT (t + 48 * j + k)) ->
  v <> w64 0.
Proof.
intros W sp0 t T mem memT i j v Htab HG Hi Hij Hjn Hcmp Hv.
destruct Htab as (_ & _ & HLT & _ & _ & _ & _ & _ & T1 & _ & T3). unfold tbl_T1 in T1.
pose proof (proj1 Hcmp Hv) as Hq. apply (T3 i j Hi Hij Hjn). exact (ct_mac_eq SEGS (w_H W) memT t T i j HG HLT Hi ltac:(lia) ltac:(lia) ltac:(lia) Hq).
Qed.
Lemma ct_bv_pos : forall v : word, v <> w64 0 -> 1 <= bv_unsigned v <= 2 ^ 64 - 1.
Proof.
intros v Hv. pose proof (bv_unsigned_in_range 64 v) as R. change (bv_modulus 64) with (2 ^ 64) in R.
destruct (Z.eq_dec (bv_unsigned v) 0) as [E0|E0]; [|lia]. exfalso. apply Hv. apply bv_eq. rewrite E0. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Definition in_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 1 (2 ^ 47 - 401) 3); (18%nat, mkAF CT_SB CT_SB 0);
           (21%nat, NOTT); (25%nat, mkAF 1 7 0)] [] [].
Definition ss_in : sstate := mkSS L_IN sr_lit [] None in_facts.
Ltac ct_fin HS HJ Kn HKP :=
  pmkst HS; apply SRr_ret; split; [reflexivity|];
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end;
  split; [reflexivity|]; split; [exact HJ|]; split; [exact HKP | exact Kn].

Lemma ct_inner : forall (fq : YK11.FPState) (k : nat) (j i : Z) W sp0 t T mem lyc Sc memL mdL (regs0 regs : bvmap 5 word) memc mdc,
  ct_tab W sp0 t T mem -> ct_r0 regs0 sp0 t (n_of T) ->
  Z.of_nat k = n_of T - j -> 0 <= i -> i + 1 <= j < n_of T ->
  ajournal SEGS B LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc W memc mdc 0 ->
  ct_mem W sp0 mem memc -> ct_kept0 regs0 regs ->
  getr regs 9 = Z_to_bv 64 (t + 48 * i) -> getr regs 20 = Z_to_bv 64 (i + 1) -> getr regs 22 = Z_to_bv 64 (i + 1) -> getr regs 25 = Z_to_bv 64 j ->
  (forall (regs' : bvmap 5 word) memc' mdc', i + 1 < n_of T ->
     ajournal SEGS B LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc W memc' mdc' 0 -> ct_mem W sp0 mem memc' ->
     ct_kept0 regs0 regs' -> getr regs' 20 = Z_to_bv 64 (i + 1) -> getr regs' 22 = Z_to_bv 64 (i + 1 + 1) ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + L_OUT)) memc' (seg_rom SEGS)) mdc') (ct_lpost fq regs0 W sp0 mem lyc Sc memL mdL)) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + L_IN)) memc (seg_rom SEGS)) mdc) (ct_lpost fq regs0 W sp0 mem lyc Sc memL mdL).
Proof.
intros fq k. induction k as [|k IH]; intros j i W sp0 t T mem lyc Sc memL mdL regs0 regs memc mdc Htab H0 Hk Hi Hj HJ HM HK G9 G20 G22 G25 HOUT; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Htab as (Ht0 & Ht8 & HLT & HGT & HAM & HRA & HSV & HOW & T1 & T2 & T3).
pose proof H0 as (R2 & R3 & R4 & R8 & R18 & R19 & R21 & R23 & R24).
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLS : LSTK = 8192) by reflexivity. assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
unfold tbl_T1 in T1. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
assert (Q2 : getr regs 2 = Z_to_bv 64 (sp0 - 96)) by (rewrite (HK 2%bv ltac:(cbv; tauto)); exact R2).
assert (Q3 : getr regs 3 = w64 (as_gp B)) by (rewrite (HK 3%bv ltac:(cbv; tauto)); exact R3).
assert (Q4 : getr regs 4 = w64 (as_tp B)) by (rewrite (HK 4%bv ltac:(cbv; tauto)); exact R4).
assert (Q8 : getr regs 8 = Z_to_bv 64 t) by (rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8).
assert (Q18 : getr regs 18 = Z_to_bv 64 CT_SB) by (rewrite (HK 18%bv ltac:(cbv; tauto)); exact R18).
assert (Q19 : getr regs 19 = Z_to_bv 64 (n_of T)) by (rewrite (HK 19%bv ltac:(cbv; tauto)); exact R19).
assert (Q21 : getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - t)) by (rewrite (HK 21%bv ltac:(cbv; tauto)); exact R21).
assert (Q23 : getr regs 23 = Z_to_bv 64 2) by (rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23).
assert (Q24 : getr regs 24 = Z_to_bv 64 7) by (rewrite (HK 24%bv ltac:(cbv; tauto)); exact R24).
destruct (ct_memc W sp0 t T mem memc Htab HM ltac:(lia)) as (HGc & HRAc & HSVc).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 96)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Q2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = Z_to_bv 64 t) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact Q8).
assert (E9 : ew E 9 = Z_to_bv 64 (t + 48 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact G9).
assert (E18 : ew E 18 = Z_to_bv 64 CT_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact Q18).
assert (E19 : ew E 19 = Z_to_bv 64 (n_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact Q19).
assert (E20 : ew E 20 = Z_to_bv 64 (i + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact G20).
assert (E21 : ew E 21 = Z_to_bv 64 (2 ^ 64 - 1 - t)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact Q21).
assert (E22 : ew E 22 = Z_to_bv 64 (i + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact G22).
assert (E25 : ew E 25 = Z_to_bv 64 j) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact G25).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 96) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_in (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_IN)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_in. apply pa_entry_st_ok_full.
  - rewrite HE. unfold sr_lit. repeat (apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; assumption]). apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [|split; [exact I | exact I]]. cbn [in_facts f_atoms atoms_ok]. unfold afact_ok, NOTT. cbn [af_lo af_hi af_al2].
    rewrite Usp, E8, E18, E21, E25, !unsigned_lit_small by (unfold CT_SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold CT_SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok SEGS CT_Bx [] E (mrestrict (w_H W) memc)) by constructor.
clear HE.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS). pose (BR := paj_branch (fx := fq) (PI := PI)).
paj_run_tok RUN HS HJ SHOK CT_Bspan; [ct_awr Usp |].
pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) HM) as K1. clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?msx) =>
  pose proof (st_ok_restrict_reg segs Hh Ex ss msx 11%bv HS) as Ra1;
  let e := eval vm_compute in (sr_get (ss_regs ss) 11%bv) in change (sr_get (ss_regs ss) 11%bv) with e in Ra1;
  cbn [ms_regs restrict mkst] in Ra1 end.
rewrite (ct_denot48 E 8 25 t j E8 E25) in Ra1 by lia.

pmkst HS.
destruct (ct_memc W sp0 t T mem (ms_mem ms) Htab K1 ltac:(lia)) as (HGm & HRAm & HSVm).
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fq) W (ms_regs ms) (ms_mem ms) LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc _ 0
    (t + 48 * i) (t + 48 * j) 6 0 (Z_to_bv 64 (BASE + 10512)) HJ).
  - rewrite Ra0, E9. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia. - lia. - lia. - lia. - lia.
  - unfold spZ. rewrite Rsp, Usp. lia.
  - reflexivity. - lia. - rewrite HLS. lia.
  - rewrite Rgp, E3. exact Q3.
  - rewrite Rtp, E4. exact Q4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [apply (ct_src (w_H W) (ms_mem ms) t T a HGm HLT); lia | unfold spZ; rewrite Rsp, Usp, HES; lia].
  - intros a Ha. split; [apply (ct_src (w_H W) (ms_mem ms) t T a HGm HLT); lia | unfold spZ; rewrite Rsp, Usp, HES; lia].
  - intros a Ha. rewrite HES. lia.
  - intros a Ha. rewrite HES. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - apply (range_addressable_sub _ _ t 400); [exact HRAm | lia | lia].
  - intros _. apply (ct_hull_sub _ t 400); [exact HSVm | lia | lia | lia].
  - apply (range_addressable_sub _ _ t 400); [exact HRAm | lia | lia].
  - intros _. apply (ct_hull_sub _ t 400); [exact HSVm | lia | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
pose proof (ct_bcmp_ne W sp0 t T mem (ms_mem ms) i j v Htab HGm Hi ltac:(lia) ltac:(lia) Hcmp) as V0.
assert (K2 : ct_mem W sp0 mem mem2).
{ intros a Ha Hn. rewrite (Hfr a Ha) by (rewrite HES; lia). exact (K1 a Ha Hn). }
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 _) as Eh eqn:HEh in HS.
assert (HEIh : img_env VAL A_LIM Eh) by (rewrite HEh; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD : forall n, (n < 34)%nat -> ew Eh n = ew E n) by (intros n Hn; rewrite HEh; apply ew_havoc_old; exact Hn).
assert (HAEh : env_agree 32 (Ereg regs []) Eh) by (rewrite HEh; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HEh.
prreg HS (10%bv : bv 5) Rv.
assert (F38 : afact_ok Eh 38 (mkAF 1 (2 ^ 64 - 1) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite <- Rv, Hv. pose proof (ct_bv_pos v V0). rewrite Z.pow_0_r, Z.mod_1_r. lia. }
apply (st_ok_pi_add_fact Eh _ _ 38 _ HS) in F38. clear HS. rename F38 into HS.
assert (SHOK2 : sh_ok SEGS CT_Bx [] Eh (mrestrict (w_H W) mem2)) by constructor.
assert (Usp2 : bv_unsigned (ew Eh 2) = sp0 - 96) by (rewrite OLD by lia; exact Usp).
assert (F25 : ew Eh 25 = Z_to_bv 64 j) by (rewrite OLD by lia; exact E25).
assert (F19 : ew Eh 19 = Z_to_bv 64 (n_of T)) by (rewrite OLD by lia; exact E19).
assert (F20 : ew Eh 20 = Z_to_bv 64 (i + 1)) by (rewrite OLD by lia; exact E20).
assert (F22 : ew Eh 22 = Z_to_bv 64 (i + 1)) by (rewrite OLD by lia; exact E22).
paj_run_tok RUN HS HJ2 SHOK2 CT_Bspan; [ct_awr Usp2 |].
pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp2) K2) as K3. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK2 CT_Bspan.
- rewrite branch_ne_U, (U_atom_off Eh 25 j 1 F25 ltac:(lia) ltac:(lia)), (U_atom Eh 19 (n_of T) F19 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 CT_Bspan L_IN; [ct_awr Usp2 |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp2) K3) as K4. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] (LKEPTA ++ [9; 20; 22]%bv) HS HAEh ltac:(vm_compute; reflexivity)) as HKk.
  cbn [ms_regs restrict] in HKk.
  prreg HS (25%bv : bv 5) N25. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
  rewrite F25, unsigned_lit_small in N25 by lia.
  pmkst HS.
  apply (IH (j + 1) i W sp0 t T mem lyc Sc memL mdL regs0 _ _ _ Htab H0 ltac:(lia) Hi ltac:(lia) HJ2 K4).
  + apply (ct_kept0_step regs0 regs); [exact HK | exact R23 | exact R24 | intros r Hr; apply HKk; apply in_app_iff; left; exact Hr | exact N23 | exact N24].
  + rewrite (HKk 9%bv ltac:(cbv; tauto)). exact G9.
  + rewrite (HKk 20%bv ltac:(cbv; tauto)). exact G20.
  + rewrite (HKk 22%bv ltac:(cbv; tauto)). exact G22.
  + exact N25.
  + exact HOUT.
- rewrite branch_ne_U, (U_atom_off Eh 25 j 1 F25 ltac:(lia) ltac:(lia)), (U_atom Eh 19 (n_of T) F19 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ2 SHOK2 CT_Bspan; [ct_awr Usp2 |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp2) K3) as K4. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK2 CT_Bspan.
  + paj_run_to_tok RUNTO HS HJ2 SHOK2 CT_Bspan L_EPI; [ct_awr Usp2 |].
    pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp2) K4) as K5. clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] LKEPTA HS HAEh ltac:(vm_compute; reflexivity)) as HKk.
    cbn [ms_regs restrict] in HKk.
    prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
    ct_fin HS HJ2 K5 (ct_kept0_step regs0 regs _ HK R23 R24 HKk N23 N24).
  + rewrite branch_eq_U, (U_atom Eh 20 (i + 1) F20 ltac:(lia)), (U_atom Eh 19 (n_of T) F19 ltac:(lia)) in Hc0.
    apply Z.eqb_neq in Hc0.
    paj_run_to_tok RUNTO HS HJ2 SHOK2 CT_Bspan L_OUT; [ct_awr Usp2 |].
    pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp2) K4) as K5. clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] (LKEPTA ++ [20]%bv) HS HAEh ltac:(vm_compute; reflexivity)) as HKk.
    cbn [ms_regs restrict] in HKk.
    prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
    rewrite F22, unsigned_lit_small in N22 by lia.
    pmkst HS.
    apply (HOUT _ _ _ ltac:(lia) HJ2 K5).
    * apply (ct_kept0_step regs0 regs); [exact HK | exact R23 | exact R24 | intros r Hr; apply HKk; apply in_app_iff; left; exact Hr | exact N23 | exact N24].
    * rewrite (HKk 20%bv ltac:(cbv; tauto)). exact G20.
    * exact N22.
Qed.

Definition out_region : YP09.region := YP09.mkRegion (Some 32%nat) 0 48 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition out_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 1 (2 ^ 47 - 401) 3); (18%nat, mkAF CT_SB CT_SB 0);
           (20%nat, mkAF 0 7 0); (21%nat, NOTT); (32%nat, mkAF 1 (2 ^ 47 - 65) 3); (33%nat, mkAF 0 2 0)] []
          [(SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 20 0) (SLit 48)), SOff 32 0)].
Definition ss_out : sstate := mkSS L_OUT sr_lit [out_region] None out_facts.
Definition out_extra (t i r : Z) : list word := map (Z_to_bv 64) [t + 48 * i; r].
Lemma ct_outer : forall (fq : YK11.FPState) (k : nat) (i : Z) W sp0 t T mem lyc Sc memL mdL (regs0 regs : bvmap 5 word) memc mdc,
  ct_tab W sp0 t T mem -> ct_r0 regs0 sp0 t (n_of T) ->
  Z.of_nat k = n_of T - i -> 0 <= i < n_of T ->
  ajournal SEGS B LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc W memc mdc 0 ->
  ct_mem W sp0 mem memc -> ct_kept0 regs0 regs ->
  getr regs 20 = Z_to_bv 64 i -> getr regs 22 = Z_to_bv 64 (i + 1) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + L_OUT)) memc (seg_rom SEGS)) mdc) (ct_lpost fq regs0 W sp0 mem lyc Sc memL mdL).
Proof.
intros fq k. induction k as [|k IH]; intros i W sp0 t T mem lyc Sc memL mdL regs0 regs memc mdc Htab H0 Hk Hi HJ HM HK G20 G22; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Htab as (Ht0 & Ht8 & HLT & HGT & HAM & HRA & HSV & HOW & T1 & T2 & T3).
pose proof H0 as (R2 & R3 & R4 & R8 & R18 & R19 & R21 & R23 & R24).
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLS : LSTK = 8192) by reflexivity. assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
unfold tbl_T1 in T1. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
assert (Q2 : getr regs 2 = Z_to_bv 64 (sp0 - 96)) by (rewrite (HK 2%bv ltac:(cbv; tauto)); exact R2).
assert (Q8 : getr regs 8 = Z_to_bv 64 t) by (rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8).
assert (Q18 : getr regs 18 = Z_to_bv 64 CT_SB) by (rewrite (HK 18%bv ltac:(cbv; tauto)); exact R18).
assert (Q19 : getr regs 19 = Z_to_bv 64 (n_of T)) by (rewrite (HK 19%bv ltac:(cbv; tauto)); exact R19).
assert (Q21 : getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - t)) by (rewrite (HK 21%bv ltac:(cbv; tauto)); exact R21).
assert (Q23 : getr regs 23 = Z_to_bv 64 2) by (rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23).
assert (Q24 : getr regs 24 = Z_to_bv 64 7) by (rewrite (HK 24%bv ltac:(cbv; tauto)); exact R24).
destruct (ct_memc W sp0 t T mem memc Htab HM ltac:(lia)) as (HGc & HRAc & HSVc).
assert (RL : role_of_e T i = 0 \/ role_of_e T i = 1 \/ role_of_e T i = 2) by (apply T2; lia).
destruct (ct_val4_s32 SEGS (mrestrict (w_H W) memc) t T (48 * i + 8) HGc HLT ltac:(lia) ltac:(lia) ltac:(unfold role_of_e in RL; lia)) as [VR RR].
change (s32_at T (48 * i + 8)) with (role_of_e T i) in VR, RR.
remember (Eimg (Ereg regs (out_extra t i (role_of_e T i)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (out_extra t i (role_of_e T i))) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 96)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Q2).
assert (E8 : ew E 8 = Z_to_bv 64 t) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact Q8).
assert (E18 : ew E 18 = Z_to_bv 64 CT_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact Q18).
assert (E19 : ew E 19 = Z_to_bv 64 (n_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact Q19).
assert (E20 : ew E 20 = Z_to_bv 64 i) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact G20).
assert (E21 : ew E 21 = Z_to_bv 64 (2 ^ 64 - 1 - t)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact Q21).
assert (E22 : ew E 22 = Z_to_bv 64 (i + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact G22).
assert (E32 : ew E 32 = Z_to_bv 64 (t + 48 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (role_of_e T i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 96) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_out (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_OUT)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_out. apply pa_entry_st_ok_full.
  - rewrite HE. unfold sr_lit. repeat (apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; assumption]). apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, out_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (t + 48 * i) 8 4 _ (role_of_e T i));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    replace (t + 48 * i + 8) with (t + (48 * i + 8)) by lia. exact VR.
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - split; [|split; [exact I|]].
    + cbn [out_facts f_atoms atoms_ok]. unfold afact_ok, NOTT. cbn [af_lo af_hi af_al2].
      rewrite Usp, E8, E18, E20, E21, E32, E33, !unsigned_lit_small by (unfold CT_SB; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold CT_SB. repeat match goal with |- _ /\ _ => split end; lia.
    + cbn [out_facts f_alias alias_ok]. split; [|exact I].
      rewrite (ct_denot48 E 8 20 t i E8 E20) by lia. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (SHOK : sh_ok SEGS CT_Bx [] E (mrestrict (w_H W) memc)) by constructor.
clear HE.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS). pose (BR := paj_branch (fx := fq) (PI := PI)).
paj_run_tok RUN HS HJ SHOK CT_Bspan;
  [ eapply (obl_of_range SEGS (w_H W) memc E CT_Bx _ 4 t 400 HRAc);
    [ unfold CT_Bx; rewrite (U_atom E 18 CT_SB E18) by (unfold CT_SB; lia); reflexivity
    | rewrite (U_atom_off E 32 (t + 48 * i) 8 E32) by lia; lia
    | rewrite (U_atom_off E 32 (t + 48 * i) 8 E32) by lia; lia ]
  | ct_awr Usp | ].
pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) HM) as K1. clear HF HFr HG.

psrr_branch_tok RUN BR HS SHOK CT_Bspan.
- lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (F20 : ew Ex 20 = Z_to_bv 64 i) by (cbn [ew ewset Nat.eqb]; exact E20);
    assert (F19 : ew Ex 19 = Z_to_bv 64 (n_of T)) by (cbn [ew ewset Nat.eqb]; exact E19);
    rewrite branch_geu_U, (U_atom_off Ex 20 i 1 F20 ltac:(lia) ltac:(lia)), (U_atom Ex 19 (n_of T) F19 ltac:(lia)) in Hc end.
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_tok RUN HS HJ SHOK CT_Bspan; [ct_awr Usp |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) K1) as K2. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK CT_Bspan.
  + paj_run_to_tok RUNTO HS HJ SHOK CT_Bspan L_EPI; [ct_awr Usp |].
    pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) K2) as K3. clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ LKEPTA HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKk.
    cbn [ms_regs restrict] in HKk.
    prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
    ct_fin HS HJ K3 (ct_kept0_step regs0 regs _ HK R23 R24 HKk N23 N24).
  + exfalso. lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (F20b : ew Ex 20 = Z_to_bv 64 i) by (cbn [ew ewset Nat.eqb]; exact E20);
      assert (F19b : ew Ex 19 = Z_to_bv 64 (n_of T)) by (cbn [ew ewset Nat.eqb]; exact E19);
      rewrite branch_eq_U, (U_atom_off Ex 20 i 1 F20b ltac:(lia) ltac:(lia)), (U_atom Ex 19 (n_of T) F19b ltac:(lia)) in Hc0 end.
    apply Z.eqb_neq in Hc0. lia.
- lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (F20 : ew Ex 20 = Z_to_bv 64 i) by (cbn [ew ewset Nat.eqb]; exact E20);
    assert (F19 : ew Ex 19 = Z_to_bv 64 (n_of T)) by (cbn [ew ewset Nat.eqb]; exact E19);
    rewrite branch_geu_U, (U_atom_off Ex 20 i 1 F20 ltac:(lia) ltac:(lia)), (U_atom Ex 19 (n_of T) F19 ltac:(lia)) in Hc end.
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK CT_Bspan L_IN; [ct_awr Usp |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) K1) as K2. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ (LKEPTA ++ [22]%bv) HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKk.
  cbn [ms_regs restrict] in HKk.
  prreg HS (9%bv : bv 5) N9. prreg HS (20%bv : bv 5) N20. prreg HS (25%bv : bv 5) N25.
  prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24.
  rewrite E32 in N9. rewrite E20, unsigned_lit_small in N20 by lia. rewrite E22 in N25.
  pmkst HS.
  apply (ct_inner fq (Z.to_nat (n_of T - (i + 1))) (i + 1) i W sp0 t T mem lyc Sc memL mdL regs0 _ _ _ Htab H0 ltac:(lia) ltac:(lia) ltac:(lia) HJ K2).
  + apply (ct_kept0_step regs0 regs); [exact HK | exact R23 | exact R24 | intros r Hr; apply HKk; apply in_app_iff; left; exact Hr | exact N23 | exact N24].
  + exact N9.
  + exact N20.
  + rewrite (HKk 22%bv ltac:(cbv; tauto)). exact G22.
  + exact N25.
  + intros regs' memc' mdc' Hlt HJ' HM' HK' H20' H22'.
    exact (IH (i + 1) W sp0 t T mem lyc Sc memL mdL regs0 regs' memc' mdc' Htab H0 ltac:(lia) ltac:(lia) HJ' HM' HK' H20' H22').
Qed.

Definition CT_CLOB : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 22; 25; 28; 29; 30; 31]%bv.
Lemma ct_clob_kept : forall r : bv 5, reg_in r CT_CLOB = false -> r = 0%bv \/ In r LKEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Lemma ct_alu64_not : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Theorem pb_check_table : tcheck_table_spec.
Proof.
unfold tcheck_table_spec.
intros fq ly S W regs mem md ch t T HPRE0 HROD G10 Ht0 Ht8 Ht63 HLT HGT HAM HRA HSV HOW HOI T1 T2 T3.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Q8 : forall r : bv 5, bv_unsigned r <> 8 -> getr (regupd regs 8 (Z_to_bv 64 0)) r = getr regs r).
{ intros r Hr. apply getr_other. intros X. apply Hr. rewrite X. reflexivity. }
pose proof (ajournal_init SEGS B TCHECK_TABLE_STK [] ly S W _ mem md ch HPRE0) as HJ.
pose proof HPRE0 as (HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & _ & HQT).
assert (Esp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite Q8 by (cbv; lia); reflexivity).
assert (Era : raZ (regupd regs 8 (Z_to_bv 64 0)) = raZ regs) by (unfold raZ; rewrite Q8 by (cbv; lia); reflexivity).
rewrite Esp in HJ, Hstk, Hpres. rewrite Era in Hra4. rewrite Q8 in Hra0, Hgp, Htp by (cbv; lia).
clear HPRE0 Esp Era Q8.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity.
destruct (ct_entry fq ly S W regs mem md t T HAR Hstk Hpres G10 Ht0 Ht8 HLT HGT HAM HRA HOW HOI T1) as [HS SHOK].
remember (Eimg (Ereg regs (ct_extra (n_of T)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ct_extra (n_of T))) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E32 : ew E 32 = Z_to_bv 64 CT_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (n_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_both3_check_table)) with (Z_to_bv 64 (BASE + AF_both3_check_table)).
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)). pose (RET := paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI)).
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCHECK_TABLE_STK <= a < spZ regs) -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by reflexivity.
paj_run_tok RUN HS HJ SHOK CT_Bspan; [ct_awr Usp |].
pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (spZ regs - TCHECK_TABLE_STK) (spZ regs) HFr ltac:(ct_wr Usp) K0) as K1. clear HF HFr HG K0.
psrr_branch_tok RUN BR HS SHOK CT_Bspan.
- paj_run_tok RUN HS HJ SHOK CT_Bspan; [ct_awr Usp |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (spZ regs - TCHECK_TABLE_STK) (spZ regs) HFr ltac:(ct_wr Usp) K1) as K2. clear HF HFr HG K1.
  prreg HS (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold tcheck_table_post. apply apost_base_same_fx.
  eexists ly, S, _, _, _.
  split; [cbn [ms_regs]; rewrite R1, E1, Hra0; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (ct_extra (n_of T)) HS); [env_agree_chain HAE | vm_compute; reflexivity]|].
  split; [apply Permutation_refl | exact K2].
- lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (F33 : ew Ex 33 = Z_to_bv 64 (n_of T)) by (cbn [ew ewset Nat.eqb]; exact E33);
    rewrite branch_eq_U, (U_atom Ex 33 (n_of T) F33 ltac:(unfold tbl_T1 in T1; lia)), U_lit in Hc by lia end.
  apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK CT_Bspan L_OUT; [ct_awr Usp |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (spZ regs - TCHECK_TABLE_STK) (spZ regs) HFr ltac:(ct_wr Usp) K1) as K2. clear HF HFr HG K1.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [3; 4; 26; 27]%bv HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKm.
  cbn [ms_regs restrict] in HKm.
  prreg HS (2%bv : bv 5) M2. prreg HS (8%bv : bv 5) M8. prreg HS (18%bv : bv 5) M18. prreg HS (19%bv : bv 5) M19.
  prreg HS (20%bv : bv 5) M20. prreg HS (21%bv : bv 5) M21. prreg HS (22%bv : bv 5) M22.
  prreg HS (23%bv : bv 5) M23. prreg HS (24%bv : bv 5) M24.

  rewrite E10, ct_alu64_not in M21 by lia.
  rewrite Usp in M2. replace (spZ regs + -96) with (spZ regs - 96) in M2 by lia.
  rewrite E10 in M8. rewrite E32 in M18. rewrite E33 in M19.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?msX) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ss) got_regionP) in
    pose proof (st_ok_pi_submem E ss (restrict (w_H W) msX) [r0] HS ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity)) as HS1 end.
  clear HS. rename HS1 into HS.
  lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
    pose proof (ajournal_sub_init SEGS B TCHECK_TABLE_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX) mdX 0 LSTK (spZ regs - 96) [] (-96) HJ
      ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(unfold LSTK, ESTACK; lia) ltac:(rewrite WS; unfold LSTK, ESTACK; lia)) as HJL;
    assert (Htab : ct_tab W (spZ regs) t T mem) by exact (conj Ht0 (conj Ht8 (conj HLT (conj HGT (conj HAM (conj HRA (conj HSV (conj HOW (conj T1 (conj T2 T3))))))))));
    assert (H0 : ct_r0 (ms_regs msX) (spZ regs) t (n_of T)) by
      (repeat split; first [exact M2 | rewrite (HKm 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HKm 4%bv ltac:(cbv; tauto)); exact Htp
        | exact M8 | exact M18 | exact M19 | exact M21 | exact M23 | exact M24]) end.
  pmkst HS.
  eapply SRr_bind.
  { apply (ct_outer fq (Z.to_nat (n_of T)) 0 W (spZ regs) t T mem ly S _ _ _ _ _ _ Htab H0 ltac:(unfold tbl_T1 in T1; lia) ltac:(unfold tbl_T1 in T1; lia) HJL K2
      (fun r _ => eq_refl) M20 M22). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJL3 & HK3 & HM3).
  pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 LSTK (spZ regs - 96) [] [] ly S W mem3 md3 0 HJ HJL3
    ltac:(rewrite WS; unfold LSTK, ESTACK; lia) ltac:(lia)) as HJ3.
  match type of HJ3 with ?P -> _ => assert (HFP : P); [|specialize (HJ3 HFP); clear HFP] end.
  { intros a Ha. exfalso. exact (inFP_nil _ Ha). }
  cbn [app] in HJ3. replace (0 + 0) with 0 in HJ3 by reflexivity.
  jafter_stretch_pi HS 34%nat regs3 (mrestrict (w_H W) mem3) CT_CLOB L_EPI HS2.
  match type of HS2 with ?P -> ?Q -> _ => assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
  { intros r0 Hr0. cbn [ms_regs restrict]. destruct (ct_clob_kept r0 Hr0) as [-> | Hin]; [rewrite !getr_zero; reflexivity | exact (HK3 r0 Hin)]. }
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
    eapply (region_kept_stack_sub SEGS B E); [exact HJL3 | exact HJ3 | exact Usp | lia | rewrite WS; lia | lia | lia | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 34 _) as Et eqn:HEt in HS.
  assert (HEIt : img_env VAL A_LIM Et) by (rewrite HEt; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDt : forall n, (n < 34)%nat -> ew Et n = ew E n) by (intros n Hn; rewrite HEt; apply ew_havoc_old; exact Hn).
  assert (HAEt : env_agree 32 (Ereg regs (ct_extra (n_of T))) Et) by (rewrite HEt; apply env_agree_havoc_ge; [lia | exact HAE]).
  clear HEt.
  assert (Usp3 : bv_unsigned (ew Et 2) = spZ regs) by (rewrite OLDt by lia; exact Usp).
  assert (SHOK3 : sh_ok SEGS CT_Bx0 [] Et (mrestrict (w_H W) mem3)) by constructor.
  paj_run_tok RUN HS HJ3 SHOK3 CT_Bspan; [ct_awr Usp3 |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (spZ regs - TCHECK_TABLE_STK) (spZ regs) HFr ltac:(ct_wr Usp3) HM3) as K4. clear HF HFr HG.
  prreg HS (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold tcheck_table_post. apply apost_base_same_fx.
  eexists ly, S, _, _, _.
  split; [cbn [ms_regs]; rewrite R1, OLDt, E1, Hra0 by lia; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (ct_extra (n_of T)) HS); [env_agree_chain HAEt | vm_compute; reflexivity]|].
  split; [apply Permutation_refl | exact K4].
Qed.
End h.
End f.
End d.

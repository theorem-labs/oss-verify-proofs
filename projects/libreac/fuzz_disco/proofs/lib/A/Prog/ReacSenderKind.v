(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue_defect.v, with its module paths and module names changed; 379 of its 457 lines of code are new or changed and 577 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacRivalKindOf.v, with its numbers changed; 717 of its 810 lines of code are new or changed and 364 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacRivalKindOf ReacMasterOnlyCadenceNs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
reac_rate_snap_c reac_rival_kind_of_c reac_master_only_cadence_ns_c reac_sender_kind_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YA0o YCbm YA0q YImgTop.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TMOC : treac_master_only_cadence_ns_spec B.
Hypothesis TRIVAL : treac_rival_kind_of_spec B.
Definition REAC_SENDER_KIND_STK : Z := 16 + REAC_MASTER_ONLY_CADENCE_NS_STK.
Definition treac_sender_kind_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (e now r d s c fs : Z) : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState,
    freg_kept (@YK11.fp_regs fq) (@YK11.fp_regs fq') /\ @YK11.fp_csr fq' = @YK11.fp_csr fq /\
    apost_base (fx := fq') SEGS B REAC_SENDER_KIND_STK [] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (reac_sender_kind_model e r d s c fs now) /\
         Permutation (ablocks B ly' S') (ablocks B ly S) /\ W' = W /\
         (forall a : word, ~ (spZ regs - REAC_SENDER_KIND_STK <= bv_unsigned a < spZ regs) -> mem' a = mem a)) W' c'.
Definition treac_sender_kind_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (e now fps r d s c fs : Z),
  afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
  getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
  getr regs 12 = w64 fps -> -2 ^ 31 <= fps < 2 ^ 31 ->
  (e <> 0 ->
     e + 40 <= 2 ^ 63 /\ in_app (e + 8) 32 /\ off_img (e + 8) 32 /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 32 /\
     (forall a, e + 8 <= a < e + 40 -> apresent (w_H W) mem a) /\
     -2 ^ 31 <= r < 2 ^ 31 /\ 0 <= d < 2 ^ 8 /\ 0 <= s < 2 ^ 8 /\ 0 <= c < 2 ^ 32 /\ 0 <= fs < 2 ^ 64 /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 32) 8 fs) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 96) + -1628) 8 D3837 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_sender_kind) regs mem md)
    (treac_sender_kind_post fq regs ly S W mem md e now r d s c fs).
Definition sk_SB : Z := 0x7fff8000.
Definition sk_Bx : sv := SOff 32 0.
Definition sk_Bspan : Z * Z := (sk_SB, sk_SB + 2 ^ 44 - 1).
Definition sk_regions : smem :=
  [ stack_region 16; got_regionP; bcell_regionP 32;
    YP09.mkRegion (Some 10%nat) 8 40 0 0
      [YP09.mkChunk 8 (CVal 4 (SOff 34 0)); YP09.mkChunk 12 (CVal 1 (SOff 33 0));
       YP09.mkChunk 20 (CVal 4 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0))] ].
Definition sk_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 140737479966720 3); (32%nat, mkAF sk_SB sk_SB 0);
            (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
            (36%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition ss_sk : sstate := mkSS AF_reac_sender_kind sr_atoms sk_regions None sk_facts.
Definition sk_SH : list shent := [ mkSHE 10 8 40 ].
Definition sk_extra (d ru c fs : Z) : list word := map (Z_to_bv 64) [sk_SB; d; ru; c; fs].
Lemma sk_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (e d ru c fs : Z),
  afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch ->
  getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 -> e <> 0 ->
  in_app (e + 8) 32 -> off_img (e + 8) 32 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 32 ->
  0 <= d < 2 ^ 8 -> 0 <= ru < 2 ^ 32 -> 0 <= c < 2 ^ 32 -> 0 <= fs < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 ru ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 32) 8 fs ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (sk_extra d ru c fs))) ss_sk
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_sender_kind)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS sk_Bx sk_SH (Eimg (Ereg regs (sk_extra d ru c fs))) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch e d ru c fs HPRE H10 Re He8 Ne Happ Himg HRA Rd Rru Rc Rfs M8 M12 M20 M32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
pose proof (proj1 (@ASAN_CEIL_range _)) as CR.
assert (Hext : 4096 <= e + 8 /\ e + 40 <= 140737479966720) by (clear - Happ CR; unfold in_app, kLowShadowBeg, kHighMemBeg in Happ; lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (sk_extra d ru c fs))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 e) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 sk_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ru) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 fs) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E307 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
unfold IMG_LO, IMG_TOP in HcellR, HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_sk. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold sk_regions, stack_region, got_regionP, bcell_regionP.
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
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 sk_Bx sk_SB);
      [cbn [sv_denot sk_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold sk_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat e E10) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      -- apply (chunk_ok_val SEGS E _ e 8 4 _ ru); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M8].
      -- apply (chunk_ok_val SEGS E _ e 12 1 _ d); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M12].
      -- apply (chunk_ok_val SEGS E _ e 20 4 _ c); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M20].
      -- apply (chunk_ok_val SEGS E _ e 32 8 _ fs); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M32].
  + apply pairwise_disjoint_of_extents. unfold sk_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat e E10) by lia.
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E307) by (pose proof (pa_val_range (A_OBJ 66)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Happ Himg. clear.
    unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, IMG_LO, IMG_TOP. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [sk_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold sk_SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Happ He8 Ne Re Rd Rru Rc Rfs. clear.
    unfold sk_SB, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, sk_SH. constructor; [|constructor].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (UB : U E sk_Bx = SHADOW_OFF).
  { unfold U, sk_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold sk_SB; lia). reflexivity. }
  assert (UE : U E (SOff 10 0) = e).
  { unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity. }
  rewrite UB, UE. rewrite <- (aview_rd_of SEGS). split.
  + replace (40 - 8) with 32 by lia. exact HRA.
  + intros a Ha. cbn [Z.min Z.max] in Ha. revert Happ Ha. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Definition sk_regions0 : smem := [ stack_region 16 ].
Definition sk_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 0 0) ] [] [].
Definition ss_sk0 : sstate := mkSS AF_reac_sender_kind sr_atoms sk_regions0 None sk_facts0.
Lemma sk_entry0 : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 sk_SB])) ss_sk0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_sender_kind)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS sk_Bx [] (Eimg (Ereg regs [Z_to_bv 64 sk_SB])) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch HPRE H10.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [Z_to_bv 64 sk_SB])).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split; [|constructor].
unfold ss_sk0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sk_regions0, stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- unfold sk_regions0. cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [sk_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, !unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0. clear. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Lemma sk_val_mem_mod32 : forall m a r, val_mem SEGS m a 4 r -> val_mem SEGS m a 4 (r mod 2 ^ 32).
Proof.
intros m a r H k Hk. rewrite (H k Hk). f_equal. f_equal. unfold YO0f.le_byte.
replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma sk_mbyte_keep : forall H (m m' : word -> option byte) lo hi a,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) -> ~ (lo <= a mod 2 ^ 64 < hi) ->
  mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof.
intros H m m' lo hi a Hk Hw. unfold mbyte, mrestrict.
rewrite (Hk (Z_to_bv 64 a)); [reflexivity|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact Hw.
Qed.
Lemma sk_aview_keep : forall H (m m' : word -> option byte) lo hi a,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) -> ~ (lo <= a mod 2 ^ 64 < hi) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' lo hi a Hk Hw. unfold aview. rewrite (sk_mbyte_keep H m m' lo hi a Hk Hw). reflexivity. Qed.
Lemma sk_val_mem_keep : forall H (m m' : word -> option byte) lo hi a n v,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  (forall k, 0 <= k < Z.of_nat n -> ~ (lo <= (a + k) mod 2 ^ 64 < hi)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' lo hi a n v Hk Hb Hv k Hkn.
rewrite (sk_mbyte_keep H m m' lo hi (a + Z.of_nat k) Hk (Hb (Z.of_nat k) ltac:(lia))). exact (Hv k Hkn).
Qed.
Lemma sk_garr8_keep : forall H (m m' : word -> option byte) lo hi a l,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  (forall k, 0 <= k < Z.of_nat (length l) -> ~ (lo <= (a + k) mod 2 ^ 64 < hi)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' lo hi a l Hk Hb Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (sk_val_mem_keep H m m' lo hi _ 1 _ Hk); [|exact Hv].
intros k Hk1. cbn in Hk1. replace k with 0 by lia. rewrite Z.add_0_r. apply Hb. lia.
Qed.
Lemma sk_ra_keep : forall H (m m' : word -> option byte) lo hi B0 a len,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  (forall x, a <= x < a + len -> ~ (lo <= shadow_of_addr B0 x mod 2 ^ 64 < hi)) ->
  range_addressable (aview SEGS H m) B0 a len -> range_addressable (aview SEGS H m') B0 a len.
Proof.
intros H m m' lo hi B0 a len Hk Hb Hra x Hx.
rewrite (sk_aview_keep H m m' lo hi _ Hk (Hb x Hx)). exact (Hra x Hx).
Qed.
Lemma sk_apresent_keep : forall H (m m' : word -> option byte) lo hi a,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) -> ~ (lo <= a mod 2 ^ 64 < hi) ->
  apresent H m a -> apresent H m' a.
Proof.
intros H m m' lo hi a Hk Hw [Hh Hb]. split; [exact Hh|].
rewrite (Hk (Z_to_bv 64 a)); [exact Hb|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact Hw.
Qed.
Definition sk_wins16 (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (match YP09.r_base r with Some 2%nat => true | _ => false end && (YP09.r_wlo r =? -16) && (YP09.r_whi r =? 0))) rs.
Lemma sk_keep_step : forall E rs (m0 m1 m2 : word -> option byte) sp,
  (forall x : word, ~ (sp - 16 <= bv_unsigned x < sp) -> m1 x = m0 x) ->
  frame_of E rs m1 m2 -> sk_wins16 rs = true -> bv_unsigned (ew E 2) = sp ->
  forall x : word, ~ (sp - 16 <= bv_unsigned x < sp) -> m2 x = m0 x.
Proof.
intros E rs m0 m1 m2 sp Hk HF Hw Hsp x Hx. rewrite (HF x); [exact (Hk x Hx)|].
intros (r & Hin & Ha). unfold sk_wins16 in Hw. rewrite forallb_forall in Hw. specialize (Hw r Hin).
destruct r as [b lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hw, Ha.
apply orb_true_iff in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
destruct b as [[|[|[|b]]]|]; cbn in Hw; try discriminate.
rewrite !andb_true_iff, !Z.eqb_eq in Hw. destruct Hw as [Hl Hh].
cbn [base_val] in Ha. rewrite Hsp in Ha. apply Hx. lia.
Qed.
Lemma sk_br_d : forall E d, ew E 33 = Z_to_bv 64 d -> 0 <= d < 2 ^ 8 ->
  branch_taken BC_NE (sv_denot E (SOff 33 0)) (sv_denot E (SLit 0)) = negb (d =? 0).
Proof. intros E d H Hd. rewrite branch_ne_U, (U_atom E 33 d H), U_lit by lia. reflexivity. Qed.
Lemma sk_br_r : forall E ru r, ew E 34 = Z_to_bv 64 ru -> ru = r mod 2 ^ 32 -> -2 ^ 31 <= r < 2 ^ 31 ->
  branch_taken BC_LTU (sv_denot E (SLit 1)) (sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff 34 0)) (SLit (-1)))) =
  negb ((r =? 1) || (r =? 2)).
Proof.
intros E ru r H Hru Hr. rewrite branch_ltu_U, U_lit by lia.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_SExt, U_SLit.
rewrite (U_atom E 34 ru H) by (subst ru; pose proof (Z.mod_pos_bound r (2 ^ 32) ltac:(lia)); lia). cbv iota. subst ru.
unfold bv_swrap, bv_wrap, zcanon, M64.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity. change (2 ^ Z.of_N 32) with (2 ^ 32).
destruct (Z.eqb_spec r 1) as [->|N1]; [vm_compute; reflexivity|].
destruct (Z.eqb_spec r 2) as [->|N2]; [vm_compute; reflexivity|].
cbn [orb negb]. apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.
Lemma sk_br_c : forall E c, ew E 35 = Z_to_bv 64 c -> 0 <= c < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff 35 0))) (sv_denot E (SLit 0)) = (c =? 0).
Proof.
intros E c H Hc. rewrite branch_eq_U, U_SExt, (U_atom E 35 c H), U_lit by lia. cbv iota.
unfold bv_swrap, bv_wrap, zcanon, M64.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
change (2 ^ Z.of_N 32) with (2 ^ 32).
destruct (Z.eqb_spec c 0) as [->|Nc]; [vm_compute; reflexivity|].
apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.
Lemma sk_br_fs : forall E fs now, ew E 36 = Z_to_bv 64 fs -> 0 <= fs < 2 ^ 64 -> ew E 11 = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SOff 36 0)) (sv_denot E (SOff 11 0)) = negb (fs <? now).
Proof. intros E fs now H1 R1 H2 R2. rewrite branch_geu_U, (U_atom E 36 fs H1 R1), (U_atom E 11 now H2 R2). reflexivity. Qed.
Lemma sk_st_ok_refx : forall (fa fb : YK11.FPState) E ss regs pc mem H,
  st_ok (fx := fa) SEGS E ss (restrict H (mkst (fx := fa) regs pc mem (seg_rom SEGS))) ->
  st_ok (fx := fb) SEGS E ss (restrict H (mkst (fx := fb) regs pc mem (seg_rom SEGS))).
Proof.
intros fa fb E ss regs pc mem H HS. unfold st_ok in *.
cbn [restrict mkst ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem] in *.
destruct HS as (_ & H2 & H3 & H4 & _ & H6 & H7 & H8 & H9).
exact (conj eq_refl (conj H2 (conj H3 (conj H4 (conj eq_refl (conj H6 (conj H7 (conj H8 H9)))))))).
Qed.
Lemma sk_getr_upd_other : forall (regs : bvmap 5 word) (r r' : bv 5) v, r' <> r -> getr (regupd regs r v) r' = getr regs r'.
Proof. intros regs r r' v H. unfold getr. destruct (bv_eqb r' 0); [reflexivity|]. apply regupd_other. exact H. Qed.
Lemma sk_getr_upd_8 : forall (regs : bvmap 5 word) v, getr (regupd regs 8 v) 8 = v.
Proof. intros regs v. unfold getr. cbn [bv_eqb]. apply regupd_same. Qed.
Lemma sk_hi_far : forall k (rd : bv 5) j, 0 <= k < 2 ^ 40 -> plookup (@pl_tpi _ PL_disco) k = Some (PHi rd j) ->
  VAL (A_HI j) < IMG_TOP + 2 ^ 31 \/ 2 ^ 64 - 2 ^ 31 <= VAL (A_HI j).
Proof.
intros k rd j Hk40 Hk. pose proof pa_B_ok as HB. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot dsym (clookup pa_tbl) VAL (@pa_sigma _ disco_listing PI) disco_listing pa_cert k _ Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
assert (Htop : VAL A_TEXT + k < IMG_TOP).
{ pose proof (pa_tbl_ok _ _ Hf) as Hfw.
  unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
  unfold code_read in Hfw.
  destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
  destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
  assert (Himg : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k)))).
  { exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
  pose proof (pa_img_range _ Himg) as HR.
  rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
  rewrite Z.mod_small in HR by lia. lia. }
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|]; [|discriminate].
destruct i; cbn [andb] in Hc; try (rewrite andb_false_r in Hc; discriminate Hc).
apply andb_prop in Hc as [_ Hc]. apply andb_prop in Hc as [_ Hc]. apply Z.eqb_eq in Hc.
unfold auipc_val, zcanon, M64 in Hc.
match type of Hc with context [bv_signed ?b] =>
  assert (Hs : - 2 ^ 31 <= bv_signed b < 2 ^ 31) by
    (unfold bv_signed, bv_swrap, bv_wrap; change (bv_modulus 32) with 4294967296;
     change (bv_half_modulus 32) with 2147483648; Z.div_mod_to_equations; lia) end.
rewrite <- Hc. Z.div_mod_to_equations. lia.
Qed.
Lemma sk_far96 : VAL (A_HI 96) < IMG_TOP + 2 ^ 31 \/ 2 ^ 64 - 2 ^ 31 <= VAL (A_HI 96).
Proof. apply (sk_hi_far AF_reac_rate_snap 10%bv 96); [unfold AF_reac_rate_snap; lia | vm_compute; reflexivity]. Qed.
Lemma sk_far97 : VAL (A_HI 97) < IMG_TOP + 2 ^ 31 \/ 2 ^ 64 - 2 ^ 31 <= VAL (A_HI 97).
Proof. apply (sk_hi_far (AF_reac_rate_snap + 4) 11%bv 97); [unfold AF_reac_rate_snap; lia | vm_compute; reflexivity]. Qed.
Lemma sk_final : forall now fs, 0 <= fs < now -> now < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_ADD (alu64 ALU_SLTU (alu64 ALU_ADD (Z_to_bv 64 now)
    (mul_div M_MUL (Z_to_bv 64 fs) (Z_to_bv 64 (-1)))) (Z_to_bv 64 1000000000)) (Z_to_bv 64 2)) (Z_to_bv 64 0)
  = w64 (if now - fs <? 10 ^ 9 then 3 else 2).
Proof.
intros now fs Hf Hn.
rewrite zmd64_sound, !zalu64_sound. unfold w64. f_equal.
unfold zalu64, zmd64, zcanon, M64. cbn [zalu_raw zmd_raw].
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (1000000000 mod 2 ^ 64) with 1000000000 by reflexivity.
replace (2 mod 2 ^ 64) with 2 by reflexivity.
replace (0 mod 2 ^ 64) with 0 by reflexivity.
rewrite (Z.mod_small fs), (Z.mod_small now) by lia.
assert (Hx : (fs * (2 ^ 64 - 1)) mod 2 ^ 64 = (2 ^ 64 - fs) mod 2 ^ 64).
{ replace (fs * (2 ^ 64 - 1)) with ((2 ^ 64 - fs) + (fs - 1) * 2 ^ 64) by ring. apply Z_mod_plus_full. }
rewrite Hx, ?Zmod_mod.
assert (Hy : (now + (2 ^ 64 - fs) mod 2 ^ 64) mod 2 ^ 64 = now - fs).
{ rewrite Zplus_mod_idemp_r. replace (now + (2 ^ 64 - fs)) with ((now - fs) + 1 * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
rewrite Hy, ?Zmod_mod. change (10 ^ 9) with 1000000000.
destruct (now - fs <? 1000000000); reflexivity.
Qed.
Lemma sk_post_ret : forall (fq : YK11.FPState) ly S W regs mem md e now r d s c fs regsF memF mdF,
  ajournal SEGS B REAC_SENDER_KIND_STK (spZ regs) [] ly S W mem md [] ly S W memF mdF 0 ->
  aregs_preserved regs regsF ->
  getr regsF 10 = w64 (reac_sender_kind_model e r d s c fs now) ->
  (forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> memF x = mem x) ->
  treac_sender_kind_post fq regs ly S W mem md e now r d s c fs W
    (mkCfg (mkst regsF (getr regs 1) memF (seg_rom SEGS)) mdF).
Proof.
intros fq ly S W regs mem md e now r d s c fs regsF memF mdF HJ HP H10 Hk.
assert (WS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
exists fq. split; [intros k _ _ _; reflexivity|]. split; [reflexivity|].
exists fq, ly, S, regsF, memF, mdF. split; [reflexivity|]. split; [intros; reflexivity|]. split; [left; reflexivity|].
split; [exact HJ|]. split; [exact HP|].
split; [exact H10|]. split; [apply Permutation_refl|]. split; [reflexivity|].
intros a Ha. apply Hk. rewrite WS in Ha. lia.
Qed.
Lemma sk_agree_ewset : forall E0 E n v, (32 <= n)%nat -> env_agree 32 E0 E -> env_agree 32 E0 (ewset E n v).
Proof.
intros E0 E n v Hn [HA HD]. split; [intros i Hi; rewrite ew_ewset_other by lia; apply HA; exact Hi | exact HD].
Qed.
Lemma sk_tail : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (e now r d s c fs : Z) regsT memT mdT,
  afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 -> e <> 0 ->
  e + 40 <= 2 ^ 63 -> in_app (e + 8) 32 -> off_img (e + 8) 32 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 32 ->
  (forall a, e + 8 <= a < e + 40 -> apresent (w_H W) mem a) ->
  -2 ^ 31 <= r < 2 ^ 31 -> 0 <= d < 2 ^ 8 -> 0 <= s < 2 ^ 8 -> 0 <= c < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c ->
  reac_sender_kind_model e r d s c fs now = reac_rival_kind_model d r s c ->
  ajournal SEGS B REAC_SENDER_KIND_STK (spZ regs) [] ly S W mem md [] ly S W memT mdT 0 ->
  (forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> memT x = mem x) ->
  getr regsT 1 = getr regs 1 -> getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
  getr regsT 10 = getr regs 10 -> aregs_preserved regs regsT ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_reac_rival_kind_of)) memT (seg_rom SEGS)) mdT)
    (treac_sender_kind_post fq regs ly S W mem md e now r d s c fs).
Proof.
intros fq ly S W regs mem md ch e now r d s c fs regsT memT mdT HPRE HRO H10 Re He8 Ne He40 Happ Himg HRA Hpe
  Rr Rd Rs Rc M8 M12 M16 M20 HM HJ Hk R1 R3 R4 R10 HP.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@ASAN_CEIL_range _)) as CR.
assert (WS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
rewrite WS in Hslo.
assert (R2 : getr regsT 2 = getr regs 2) by (apply (HP 2); left; reflexivity).
assert (R8 : getr regsT 8 = getr regs 8) by (apply (HP 8); right; right; right; left; reflexivity).
assert (Hsp : spZ regsT = spZ regs) by (unfold spZ; rewrite R2; reflexivity).
assert (Hext : 4096 <= e + 8 /\ e + 40 <= 140737479966720)
  by (clear - Happ CR; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (Hac : e + 40 <= alloc_ceiling) by (clear - Happ C1; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (Hlo : forall a, 0 <= a < alloc_ceiling -> ~ (spZ regs - 16 <= a < spZ regs)) by (intros a Ha; lia).
eapply SRr_mono.
{ apply (TRIVAL fq ly S W regsT memT mdT ch e r d s c).
  - eapply (afn_pre_at SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ HJ).
    + rewrite Hsp. lia.
    + reflexivity.
    + lia.
    + rewrite WR. lia.
    + rewrite WR, WS. lia.
    + rewrite R1. exact Hra.
    + unfold raZ. rewrite R1. exact Hra4.
    + rewrite R3. exact Hgp.
    + rewrite R4. exact Htp.
    + rewrite Hsp. unfold s0Z. rewrite R8.
      apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
      intros a Ha. apply (sk_aview_keep (w_H W) mem memT (spZ regs - 16) (spZ regs) a Hk). rewrite Z.mod_small by lia. lia.
  - eapply arodata_ok_journalP; first [exact pa_relro_img | exact RO | exact HJ | exact HRO].
  - rewrite R10. exact H10.
  - exact Re.
  - exact He8.
  - intros _. split; [lia|]. split; [apply (in_app_sub (e + 8) 32); [exact Happ | lia | lia | lia]|].
    split; [unfold off_img in *; lia|].
    split.
    { apply (sk_ra_keep (w_H W) mem memT (spZ regs - 16) (spZ regs) SHADOW_OFF (e + 8) 16 Hk).
      - intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
        assert (0 <= 2147450880 + x / 8 < alloc_ceiling) by (clear - Hx Hext C1; Z.div_mod_to_equations; lia).
        rewrite Z.mod_small by lia. apply Hlo. lia.
      - intros x Hx. apply HRA. lia. }
    split; [intros a Ha; apply (sk_apresent_keep (w_H W) mem memT (spZ regs - 16) (spZ regs) a Hk); [rewrite Z.mod_small by lia; lia | apply Hpe; lia]|].
    split; [exact Rr|]. split; [exact Rd|]. split; [exact Rs|]. split; [exact Rc|].
    split; [apply (sk_val_mem_keep (w_H W) mem memT (spZ regs - 16) (spZ regs) _ _ _ Hk); [intros k Hk'; cbn in Hk'; rewrite Z.mod_small by lia; lia | exact M8]|].
    split; [apply (sk_val_mem_keep (w_H W) mem memT (spZ regs - 16) (spZ regs) _ _ _ Hk); [intros k Hk'; cbn in Hk'; rewrite Z.mod_small by lia; lia | exact M12]|].
    split; [apply (sk_val_mem_keep (w_H W) mem memT (spZ regs - 16) (spZ regs) _ _ _ Hk); [intros k Hk'; cbn in Hk'; rewrite Z.mod_small by lia; lia | exact M16]|].
    apply (sk_val_mem_keep (w_H W) mem memT (spZ regs - 16) (spZ regs) _ _ _ Hk); [intros k Hk'; cbn in Hk'; rewrite Z.mod_small by lia; lia | exact M20]. }
intros W' c' _ HQ. unfold treac_rival_kind_of_post, apost_base in HQ.
destruct HQ as (fqr & ly' & S' & regs' & mem' & md' & Hc & Hfqr & Hcsr & HJ1 & HP1 & Hv & HPm & HW & Hk1).
subst c' W'.
assert (HJ2 := ajournal_sub SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ1).
specialize (HJ2 ltac:(rewrite Hsp, WS, WR; lia) ltac:(rewrite Hsp; lia) ltac:(intros a (rg & Hrg & _); destruct Hrg)).
exists fq. split; [intros k _ _ _; reflexivity|]. split; [reflexivity|].
exists fqr, ly', S', regs', mem', md'.
split; [rewrite R1; reflexivity|]. split; [exact Hfqr|]. split; [exact Hcsr|].
split; [exact HJ2|].
split; [exact (aregs_preserved_trans _ _ _ HP HP1)|].
split; [rewrite Hv, (proj2 (Z.eqb_neq e 0) Ne), HM; reflexivity|].
split; [exact HPm|]. split; [reflexivity|].
intros a Ha. rewrite WS in Ha. rewrite (Hk1 a); [apply Hk; lia|]. rewrite Hsp, WR. lia.
Qed.
Ltac sk_keep Usp :=
  repeat match goal with
  | H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end;
  lazymatch goal with
  | HF : frame_of ?Ex ?rs ?m1 ?m2, HM : forall x : word, ~ (?lo <= bv_unsigned x < ?hi) -> ?m1 x = ?m0 x |- _ =>
    let HM' := fresh "HM" in
    pose proof (sk_keep_step Ex rs m0 m1 m2 _ HM HF ltac:(vm_compute; reflexivity)
      ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp)) as HM';
    clear HM HF; rename HM' into HM
  end.
Ltac sk_run RUN Usp :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK sk_Bspan;
  [ first [apply awr_ok_nil | awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp] |];
  sk_keep Usp end.
Ltac sk_bvne := let Hq := fresh "Hq" in intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate.
Lemma sk_walk0 : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (now r d s c fs : Z),
  afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_sender_kind) regs mem md)
    (treac_sender_kind_post fq regs ly S W mem md 0 now r d s c fs).
Proof.
intros fq ly S W regs mem md ch now r d s c fs HPRE H10.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (sk_entry0 fq ly S W regs mem md ch HPRE H10) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_SENDER_KIND_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_ret_at (PL := PL_disco) (PI := PI)) as RET.
pose proof (paj_branch (PI := PI)) as BR.
remember (Eimg (Ereg regs [Z_to_bv 64 sk_SB])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 sk_SB]) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HM : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> mem x = mem x) by (intros; reflexivity).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_sender_kind)) with (Z_to_bv 64 (BASE + AF_reac_sender_kind)).
sk_run RUN Usp.
psrr_branch_tok RUN BR HS SHOK sk_Bspan.
2:{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite branch_eq_U, (U_atom Ex 10 0 ltac:(rewrite ?ew_ewset_other by lia; exact E10)), U_lit in Hc by lia end.
    discriminate Hc. }
sk_run RUN Usp.
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
  prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat'; rewrite R1, E1, Hra;
  apply sk_post_ret;
  [ apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
  | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 sk_SB] HS);
    [repeat (apply sk_agree_ewset; [lia|]); exact HAE | vm_compute; reflexivity]
  | rewrite R10; reflexivity
  | exact HM ]
end.
Qed.
Lemma sk_walk1 : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (e now fps r d s c fs : Z),
  afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
  getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
  getr regs 12 = w64 fps -> -2 ^ 31 <= fps < 2 ^ 31 -> e <> 0 ->
  e + 40 <= 2 ^ 63 -> in_app (e + 8) 32 -> off_img (e + 8) 32 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 32 ->
  (forall a, e + 8 <= a < e + 40 -> apresent (w_H W) mem a) ->
  -2 ^ 31 <= r < 2 ^ 31 -> 0 <= d < 2 ^ 8 -> 0 <= s < 2 ^ 8 -> 0 <= c < 2 ^ 32 -> 0 <= fs < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c ->
  val_mem SEGS (mrestrict (w_H W) mem) (e + 32) 8 fs ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 96) + -1628) 8 D3837 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_sender_kind) regs mem md)
    (treac_sender_kind_post fq regs ly S W mem md e now r d s c fs).
Proof.
intros fq ly S W regs mem md ch e now fps r d s c fs HPRE HRO H10 Re He8 H11 Rnow H12 Rfps Ne He40 Happ Himg HRAe Hpe
  Rr Rd Rs Rc Rfs M8 M12 M16 M20 M32 HRA HRT H6 H3.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@ASAN_CEIL_range _)) as CR.
assert (WS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
assert (Hext : 4096 <= e + 8 /\ e + 40 <= 140737479966720)
  by (clear - Happ CR; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (Hac : e + 40 <= alloc_ceiling) by (clear - Happ C1; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
set (ru := r mod 2 ^ 32).
assert (Rru : 0 <= ru < 2 ^ 32) by (subst ru; apply Z.mod_pos_bound; lia).
pose proof (sk_val_mem_mod32 _ _ _ M8) as M8u. fold ru in M8u.
destruct (sk_entry fq ly S W regs mem md ch e d ru c fs HPRE H10 Re He8 Ne Happ Himg HRAe Rd Rru Rc Rfs M8u M12 M20 M32) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_SENDER_KIND_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (paj_ret_at (PL := PL_disco) (PI := PI)) as RET.
remember (Eimg (Ereg regs (sk_extra d ru c fs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HER : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n rr Hr)).
assert (E1 : ew E 1 = getr regs 1) by (apply HER; [lia | reflexivity]).
assert (E2 : ew E 2 = getr regs 2) by (apply HER; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs 3) by (apply HER; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (apply HER; [lia | reflexivity]).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite (HER 11%nat 11%bv) by (first [lia | reflexivity]); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 fps) by (rewrite (HER 12%nat 12%bv) by (first [lia | reflexivity]); exact H12).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (sk_extra d ru c fs) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ j)).
assert (E33 : ew E 33 = Z_to_bv 64 d) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 ru) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 c) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 fs) by exact (EX 4%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (sk_extra d ru c fs)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE EX.
assert (HM : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> mem x = mem x) by (intros; reflexivity).
assert (Ee : (e =? 0) = false) by (apply Z.eqb_neq; exact Ne).
unfold cfg_at. change (w64 (BASE + AF_reac_sender_kind)) with (Z_to_bv 64 (BASE + AF_reac_sender_kind)).
sk_run RUN Usp.
psrr_branch_tok RUN BR HS SHOK sk_Bspan.
- lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (sk_br_d Ex d ltac:(rewrite ?ew_ewset_other by lia; exact E33) Rd) in Hc end.
  sk_run RUN Usp.
  lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
    rewrite (st_ok_restrict_mkst SEGS (w_H W) Ex ssx msc HS eq_refl);
    cbn [ss_pc setpc]; rewrite pa_sigma_reac_rival_kind_of;
    prreg HS (1%bv : bv 5) Q1; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (10%bv : bv 5) Q10;
    apply (sk_tail fq ly S W regs mem md ch e now r d s c fs (ms_regs msc) (ms_mem msc) _ HPRE HRO H10 Re He8 Ne He40 Happ Himg HRAe Hpe
      Rr Rd Rs Rc M8 M12 M16 M20);
    [ unfold reac_sender_kind_model; rewrite Ee, Hc; reflexivity
    | exact HJ | exact HM
    | rewrite Q1; exact E1 | rewrite Q3; exact E3 | rewrite Q4; exact E4 | rewrite Q10; apply HER; [lia | reflexivity]
    | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sk_extra d ru c fs) HS);
      [repeat (apply sk_agree_ewset; [lia|]); exact HAE | vm_compute; reflexivity] ]
  end.
- rename Hc into Hd0.
  lazymatch type of Hd0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (sk_br_d Ex d ltac:(rewrite ?ew_ewset_other by lia; exact E33) Rd) in Hd0 end.
  sk_run RUN Usp.
  psrr_branch_tok RUN BR HS SHOK sk_Bspan.
  + rename Hc into Hr0.
    lazymatch type of Hr0 with branch_taken _ _ (sv_denot ?Ex _) = _ =>
      rewrite (sk_br_r Ex ru r ltac:(rewrite ?ew_ewset_other by lia; exact E34) eq_refl Rr) in Hr0 end.
    apply (proj1 (negb_true_iff _)) in Hr0.
    sk_run RUN Usp.
    psrr_branch_tok RUN BR HS SHOK sk_Bspan.
    * rename Hc into Hc0.
      lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
        rewrite (sk_br_c Ex c ltac:(rewrite ?ew_ewset_other by lia; exact E35) Rc) in Hc0 end.
      assert (HMv : reac_sender_kind_model e r d s c fs now = 3)
        by (unfold reac_sender_kind_model; rewrite Ee, Hd0; cbn [orb]; rewrite Hr0, Hc0; reflexivity).
      sk_run RUN Usp.
      lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
        prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
        intros mat'; rewrite R1, E1, Hra;
        apply sk_post_ret;
        [ apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
        | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sk_extra d ru c fs) HS);
          [repeat (apply sk_agree_ewset; [lia|]); exact HAE | vm_compute; reflexivity]
        | rewrite R10, HMv; reflexivity
        | exact HM ]
      end.
    * rename Hc into Hc0.
      lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
        rewrite (sk_br_c Ex c ltac:(rewrite ?ew_ewset_other by lia; exact E35) Rc) in Hc0 end.
      sk_run RUN Usp.
      psrr_branch_tok RUN BR HS SHOK sk_Bspan.
      -- rename Hc into Hf0.
         lazymatch type of Hf0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
           rewrite (sk_br_fs Ex fs now ltac:(rewrite ?ew_ewset_other by lia; exact E36) Rfs
             ltac:(rewrite ?ew_ewset_other by lia; exact E11) Rnow) in Hf0 end.
         apply (proj1 (negb_true_iff _)) in Hf0. apply Z.ltb_ge in Hf0.
         assert (HMv : reac_sender_kind_model e r d s c fs now = 3)
           by (unfold reac_sender_kind_model; rewrite Ee, Hd0; cbn [orb]; rewrite Hr0, Hc0, (proj2 (Z.leb_le now fs) Hf0); reflexivity).
         sk_run RUN Usp.
         lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
        prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
        intros mat'; rewrite R1, E1, Hra;
        apply sk_post_ret;
        [ apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
        | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sk_extra d ru c fs) HS);
          [repeat (apply sk_agree_ewset; [lia|]); exact HAE | vm_compute; reflexivity]
        | rewrite R10, HMv; reflexivity
        | exact HM ]
      end.
      -- rename Hc into Hf0.
         lazymatch type of Hf0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
           rewrite (sk_br_fs Ex fs now ltac:(rewrite ?ew_ewset_other by lia; exact E36) Rfs
             ltac:(rewrite ?ew_ewset_other by lia; exact E11) Rnow) in Hf0 end.
         apply (proj1 (negb_false_iff _)) in Hf0. apply Z.ltb_lt in Hf0.
         assert (HMv : reac_sender_kind_model e r d s c fs now = if now - fs <? 10 ^ 9 then 3 else 2)
           by (unfold reac_sender_kind_model; rewrite Ee, Hd0; cbn [orb]; rewrite Hr0, Hc0, (proj2 (Z.leb_gt now fs) Hf0); reflexivity).
         sk_run RUN Usp.
         lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
           prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
           prreg HS (10%bv : bv 5) Q10;
           let Hms := fresh "Hms" in
           pose proof (st_ok_restrict_mkst SEGS (w_H W) Ex ssx msc HS eq_refl) as Hms;
           rewrite Hms in HS; rewrite Hms; clear Hms;
           set (regsC := ms_regs msc) in *; set (memC := ms_mem msc) in *
         end.
         cbn [ss_pc setpc]. rewrite pa_sigma_reac_master_only_cadence_ns.
         assert (WM : REAC_MASTER_ONLY_CADENCE_NS_STK = 4208) by reflexivity.
         pose proof (pa_obj_img 65 ltac:(unfold disco_nobj; lia)) as H65. unfold IMG_LO, IMG_TOP in H65.
         pose proof sk_far96 as HF96.
         pose proof sk_far97 as HF97.
         unfold IMG_TOP in HF96, HF97. pose proof (pa_val_range (A_HI 96)) as V96. pose proof (pa_val_range (A_HI 97)) as V97.
         eapply SRr_bind.
         { apply (TMOC fq ly S W regsC memC _ [] fps).
           - eapply (afn_pre_at SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-16) _ HJ).
             + unfold spZ at 1. rewrite sk_getr_upd_other by sk_bvne. rewrite Q2, Usp, unsigned_lit_small by lia. reflexivity.
             + reflexivity.
             + lia.
             + rewrite WM. lia.
             + rewrite WM, WS. lia.
             + rewrite sk_getr_upd_other by sk_bvne. rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
             + unfold raZ. rewrite sk_getr_upd_other by sk_bvne. rewrite Q1, unsigned_lit_small by lia. unfold IMG_LO in HBLO. lia.
             + rewrite sk_getr_upd_other by sk_bvne. rewrite Q3, E3. exact Hgp.
             + rewrite sk_getr_upd_other by sk_bvne. rewrite Q4, E4. exact Htp.
             + unfold s0Z. rewrite sk_getr_upd_8. apply achain_low. rewrite unsigned_lit_small by lia. lia.
           - eapply arodata_ok_journalP; first [exact pa_relro_img | exact RO | exact HJ | exact HRO].
           - rewrite Q10, E12. reflexivity.
           - exact Rfps.
           - apply (sk_ra_keep (w_H W) mem memC (spZ regs - 16) (spZ regs) SHADOW_OFF (VAL (A_OBJ 65)) 12 HM); [|exact HRA].
             intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
             assert (0 <= 2147450880 + x / 8 < alloc_ceiling) by (clear - Hx H65 C1; Z.div_mod_to_equations; lia).
             rewrite Z.mod_small by lia. lia.
           - apply (sk_garr8_keep (w_H W) mem memC (spZ regs - 16) (spZ regs) _ _ HM); [|exact HRT].
             intros k Hk'. assert (Hlen : Z.of_nat (length (map (fun b : byte => bv_unsigned b) RATES)) = 12) by (vm_compute; reflexivity). rewrite Hlen in Hk'. rewrite Z.mod_small by lia. lia.
           - apply (sk_val_mem_keep (w_H W) mem memC (spZ regs - 16) (spZ regs) _ _ _ HM); [|exact H6].
             intros k Hk'. cbn in Hk'. clear - Hk' HF97 V97 Hceil Hslo Hshi H47 C1 WS. Z.div_mod_to_equations. lia.
           - apply (sk_val_mem_keep (w_H W) mem memC (spZ regs - 16) (spZ regs) _ _ _ HM); [|exact H3].
             intros k Hk'. cbn in Hk'. clear - Hk' HF96 V96 Hceil Hslo Hshi H47 C1 WS. Z.div_mod_to_equations. lia. }
         intros W2 c2 _ HQ. unfold treac_master_only_cadence_ns_post, apost_base in HQ.
         destruct HQ as (fq' & HFK & HFC & fq2 & ly2 & S2 & regs2 & mem2 & md2 & Hc2 & Hfq2 & Hcsr2 & HJ1 & HP1 & Ha0 & HPm & HW2 & Hk2).
         subst c2 W2.
         assert (HspC : spZ regsC = spZ regs - 16).
         { unfold spZ at 1. rewrite Q2, Usp, unsigned_lit_small by lia. lia. }
         assert (HJ2 := ajournal_sub SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ1).
         specialize (HJ2 ltac:(rewrite HspC, WS, WM; lia) ltac:(rewrite HspC; lia) ltac:(intros a (rg & Hrg & _); destruct Hrg)).
         assert (Hk3 : forall x : word, ~ (spZ regs - 4224 <= bv_unsigned x < spZ regs) -> mem2 x = mem x).
         { intros x Hx. rewrite (Hk2 x); [apply HM; lia | rewrite HspC, WM; lia]. }
         eapply SRr_mono with (Q := apost_base (fx := fq') SEGS B REAC_SENDER_KIND_STK [] regs ly S W mem md 0
           (fun ly' S' W' regs' mem' md' =>
              getr regs' 10 = w64 (reac_sender_kind_model e r d s c fs now) /\
              Permutation (ablocks B ly' S') (ablocks B ly S) /\ W' = W /\
              (forall a : word, ~ (spZ regs - REAC_SENDER_KIND_STK <= bv_unsigned a < spZ regs) -> mem' a = mem a))).
         2:{ intros W' c' _ HQ. exists fq'. split; [exact HFK|]. split; [exact HFC|]. exact HQ. }
         lazymatch goal with HS : st_ok _ _ _ _ |- _ => pose proof (sk_st_ok_refx fq fq2 _ _ _ _ _ _ HS) as HSq; clear HS end.
         clear HFK HFC RUN BR RET.
         clear fq.
         pose proof (paj_run B LAWS) as RUN. pose proof (paj_ret_at (PL := PL_disco) (PI := PI)) as RET.
         jafter_call_keep_pi HSq 37%nat regs2 (mrestrict (w_H W) mem2) HP1 [0]%nat HS2.
         match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
         { cbn [ms_mem restrict mkst]. apply Forall_cons; [|apply Forall_nil].
           eapply (region_kept_stack_sub SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs));
             [exact HJ1 | exact HJ2 | | rewrite HspC; lia | rewrite WS; lia | lia | cbn; lia | cbn; lia].
           cbn [ew ewset Nat.eqb]. rewrite ?ew_ewset_other by lia. exact Usp. }
         rewrite <- restrict_mkst_fx in HS2.
         pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) (10 ^ 9) HS2 ltac:(cbn [ms_regs mkst restrict]; exact Ha0) eq_refl) as HS3.
         clear HS2.
         lazymatch type of HS3 with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS3 end.
         lazymatch type of HS3 with st_ok_pi _ _ (havoc ?Ex _ _) _ _ =>
           assert (HEIc : img_env VAL A_LIM (havoc Ex 37 (map (getr regs2) CLOB))) by (apply img_env_havoc; [assumption | cbv; lia]);
           assert (OLDc : forall n, (n < 37)%nat -> ew (havoc Ex 37 (map (getr regs2) CLOB)) n = ew E n)
             by (intros n Hn; rewrite YN3v.ew_havoc_old by exact Hn; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; reflexivity);
           assert (HAEc : env_agree 32 (Ereg regs (sk_extra d ru c fs)) (havoc Ex 37 (map (getr regs2) CLOB)))
             by (apply env_agree_havoc_ge; [cbv; lia | repeat (apply sk_agree_ewset; [lia|]); exact HAE])
         end.
         remember (havoc _ 37 (map (getr regs2) CLOB)) as Ec eqn:HEc. clear HEc.
         assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact Usp).
         assert (E1c : ew Ec 1 = getr regs 1) by (rewrite OLDc by lia; exact E1).
         assert (SHOKc : sh_ok SEGS sk_Bx [] Ec (mrestrict (w_H W) mem2)) by constructor.
         assert (HMc : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> mem2 x = mem2 x) by (intros; reflexivity).
         clear HSq SHOK HJ HM.
         rename HS3 into HS. rename HJ2 into HJ. rename SHOKc into SHOK. rename HMc into HM.
         rewrite Q1.
         sk_run RUN Uspc.
         lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
           prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
           eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
           intros mat';
           exists fq2, ly2, S2, (ms_regs msc), (ms_mem msc); eexists;
           split; [rewrite R1, E1c, Hra; reflexivity|];
           split; [exact Hfq2|]; split; [exact Hcsr2|];
           split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
           split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sk_extra d ru c fs) HS);
             [repeat (apply sk_agree_ewset; [lia|]); exact HAEc | vm_compute; reflexivity]|];
           split; [rewrite R10, (OLDc 11%nat ltac:(lia)), (OLDc 36%nat ltac:(lia)), E11, E36, HMv; apply sk_final; lia|];
           split; [exact HPm|]; split; [reflexivity|];
           intros a Ha; rewrite WS in Ha; rewrite (HM a) by lia; apply Hk3; lia
         end.
  + rename Hc into Hr0.
    lazymatch type of Hr0 with branch_taken _ _ (sv_denot ?Ex _) = _ =>
      rewrite (sk_br_r Ex ru r ltac:(rewrite ?ew_ewset_other by lia; exact E34) eq_refl Rr) in Hr0 end.
    apply (proj1 (negb_false_iff _)) in Hr0.
    assert (HMv : reac_sender_kind_model e r d s c fs now = reac_rival_kind_model d r s c)
      by (unfold reac_sender_kind_model; rewrite Ee, Hd0; cbn [orb]; rewrite Hr0; reflexivity).
    sk_run RUN Usp.
    lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
      rewrite (st_ok_restrict_mkst SEGS (w_H W) Ex ssx msc HS eq_refl);
      cbn [ss_pc setpc]; rewrite pa_sigma_reac_rival_kind_of;
      prreg HS (1%bv : bv 5) Q1; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (10%bv : bv 5) Q10;
      apply (sk_tail fq ly S W regs mem md ch e now r d s c fs (ms_regs msc) (ms_mem msc) _ HPRE HRO H10 Re He8 Ne He40 Happ Himg HRAe Hpe
        Rr Rd Rs Rc M8 M12 M16 M20);
      [ exact HMv
      | exact HJ | exact HM
      | rewrite Q1; exact E1 | rewrite Q3; exact E3 | rewrite Q4; exact E4 | rewrite Q10; apply HER; [lia | reflexivity]
      | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sk_extra d ru c fs) HS);
        [repeat (apply sk_agree_ewset; [lia|]); exact HAE | vm_compute; reflexivity] ]
    end.
Qed.
Theorem pb_reac_sender_kind : treac_sender_kind_spec.
Proof.
unfold treac_sender_kind_spec.
intros fq ly S W regs mem md ch e now fps r d s c fs HPRE HRO H10 Re He8 H11 Rnow H12 Rfps HF HRA HRT H6 H3.
destruct (Z.eq_dec e 0) as [He0 | Ne].
- subst e. exact (sk_walk0 fq ly S W regs mem md ch now r d s c fs HPRE H10).
- destruct (HF Ne) as (He40 & Happ & Himg & HRAe & Hpe & Rr & Rd & Rs & Rc & Rfs & M8 & M12 & M16 & M20 & M32).
  exact (sk_walk1 fq ly S W regs mem md ch e now fps r d s c fs HPRE HRO H10 Re He8 H11 Rnow H12 Rfps Ne He40 Happ Himg HRAe Hpe
    Rr Rd Rs Rc Rfs M8 M12 M16 M20 M32 HRA HRT H6 H3).
Qed.
End h.
End f.
End d.

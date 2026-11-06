(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 4602 of its 4661 lines of code are new or changed and 310 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntStep.v, with its module paths, module names and numbers changed; 142 of its 197 lines of code are new or changed and 4606 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0s YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_pin_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma pin_garr8_le4 : forall segs E m base off e (w : word),
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = w ->
  garr8 segs m (base + off) (map (fun b : byte => bv_unsigned b) (Mem.le4 w)).
Proof.
intros segs E m base off e w Hc He j Hj.
rewrite length_map, Mem.length_le4 in Hj.
destruct (Hc (Z.of_nat j) ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm. injection Hb as Hb. subst b. rewrite He in Hm.
assert (Hnth : nth j (map (fun b : byte => bv_unsigned b) (Mem.le4 w)) 0 = Z.shiftr (bv_unsigned w) (8 * Z.of_nat j) mod 256).
{ unfold Mem.le4. destruct j as [|[|[|[|j]]]]; [| | | | lia]; cbn [Z_to_le_bytes map nth];
  rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite ?Z.shiftr_shiftr by lia; reflexivity. }
rewrite Hnth. split; [|apply Z.mod_pos_bound; lia].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hm. f_equal.
unfold byte_of_word, YO0f.le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, !Z.mod_mod by lia. reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition REAC_HUNT_PIN_STK : Z := 16 + ESTACK.
Definition treac_hunt_pin_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md (h : Z)
  : world SEGS -> config -> Prop :=
  fun W' c' =>
    apost_base (fx := fq) SEGS B REAC_HUNT_PIN_STK [(h + 432, h + 440)] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         garr8 SEGS (mrestrict (w_H W') mem') (h + 432)
           (map (fun b : byte => bv_unsigned b) (Mem.le4 (Z_to_bv 64 1) ++ Mem.le4 (getr regs 11))) /\
         Permutation (ablocks B ly' S') (ablocks B ly S)) W' c'.
Definition treac_hunt_pin_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h hb hn : Z),
  afn_pre SEGS B REAC_HUNT_PIN_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  getr regs 10 = w64 h -> 0 < h -> h mod 8 = 0 ->
  In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_hunt_pin) regs mem md)
    (treac_hunt_pin_post fq regs ly S W mem md h).
Definition PINBx : sv := SOff 32 0.
Definition PINspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pin_regions : smem :=
  [ stack_region 16; got_regionP; bcell_regionP 32; YP09.mkRegion (Some 10%nat) 0 480 432 440 [] ].
Definition pin_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition ss_pin : sstate := mkSS AF_both3_reac_hunt_pin sr_atoms pin_regions None pin_facts.
Definition pin_SH : list shent := [mkSHE 10 0 480].
Theorem pb_reac_hunt_pin : treac_hunt_pin_spec.
Proof.
unfold treac_hunt_pin_spec.
intros fq ly S W regs mem md ch h hb hn HPRE H10 Hh0 Hh8 Hin Hhb Hhn.
pose proof (pa_segs_low) as Hsegs.
pose proof (ajournal_init SEGS B REAC_HUNT_PIN_STK [(h + 432, h + 440)] ly S W _ mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (G1 : getr (regupd regs 8 (Z_to_bv 64 0)) 1 = getr regs 1) by (unfold getr; cbn; rewrite regupd_other; [reflexivity | intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X]).
assert (G2 : getr (regupd regs 8 (Z_to_bv 64 0)) 2 = getr regs 2) by (unfold getr; cbn; rewrite regupd_other; [reflexivity | intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X]).
assert (Usp0 : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite G2; reflexivity).
rewrite Usp0 in HJ, Hstk, Hpres. rewrite G1 in Hra.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_PIN_STK = 4112) by reflexivity.
destruct ((al_blocks _ _ LAWS) ly S W mem md hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hin) as Hbimg.
destruct ((al_const _ _ LAWS) ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img_all 0 ltac:(vm_compute; lia)) as HO1. pose proof (pa_obj_img_all 12 ltac:(vm_compute; lia)) as HO66.
pose proof (pa_val_range (A_OBJ 0)) as HV1. pose proof (pa_val_range (A_OBJ 12)) as HV66.
unfold IMG_LO, IMG_TOP in HO1, HO66. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
assert (Hq : 0 < req_size hn) by lia.
assert (Hhr : h < 2 ^ 64) by (unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hbapp; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) k) by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO1 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO66 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E) by (split; [intros k Hk; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (HS : st_ok_pi SEGS VAL E ss_pin (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_hunt_pin)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pin. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pin_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok; cbv zeta;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO1) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO66) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    + rewrite (VB 10%nat h E10) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hbpres (h + o) ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold pin_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat h E10) by lia. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO1) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO66) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hbapp.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [pin_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hbapp.
    repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok SEGS PINBx pin_SH E (mrestrict (w_H W) mem)).
{ unfold pin_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E PINBx 10 h 480 h 0 480).
  - apply (range_addressable_of_block SEGS B LAWS ly S W mem md hb hn h 480 HAR Hin); lia.
  - unfold PINBx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 10 h E10). lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, SHADOW_OFF, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *. lia. }
unfold cfg_at. change (w64 (BASE + AF_both3_reac_hunt_pin)) with (Z_to_bv 64 (BASE + AF_both3_reac_hunt_pin)).
pose (RUN := paj_run (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose (RET := paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
clear HE EL.
paj_run_tok RUN HS HJ SHOK PINspan.
- awr_ok_tac; first [rewrite E2; reflexivity
  | eapply awr_ok_cons_gen with (k := 10%nat) (b := h); [reflexivity | rewrite E10; apply unsigned_lit_small; lia | | apply awr_ok_nil];
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; left; split;
    [exists (h + 432, h + 440); split; [left; reflexivity | cbn [fst snd]; lia] | exists hb, hn; split; [exact Hin | lia]] ].
- repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let R1 := fresh "R1" in prreg HS (1%bv : bv 5) R1;
  let HRG := fresh "HRG" in
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & (_ & HRG & _) & _);
  cbn [abs_ss setpc ss_mem] in HRG;
  let m := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with m in HRG;
  apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv in HRG;
  unfold region_ok in HRG; cbv zeta in HRG; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in HRG;
  rewrite (VB 10%nat h E10) in HRG by lia;
  let HCK := fresh "HCK" in destruct HRG as (_ & _ & _ & HCK);
  let C436 := fresh "C436" in let C432 := fresh "C432" in
  pose proof (Forall_inv HCK) as C436; pose proof (Forall_inv (Forall_inv_tail HCK)) as C432; clear HCK;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat';
  unfold treac_hunt_pin_post;
  apply apost_base_same_fx; eexists ly, S, _, _, _;
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [Z_to_bv 64 SHADOW_OFF] HS); [exact HAE | vm_compute; reflexivity]|];
  split; [|apply Permutation_refl];
  cbn [ms_mem]; rewrite map_app; apply garr8_app; split;
  [ exact (pin_garr8_le4 SEGS E _ h 432 (SLit 1) (Z_to_bv 64 1) C432 eq_refl)
  | rewrite length_map, Mem.length_le4; replace (h + 432 + Z.of_nat 4) with (h + 436) by lia;
    apply (pin_garr8_le4 SEGS E _ h 436 (SOff 11 0) (getr regs 11) C436);
    cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ]
  end.
Qed.
End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxSetResweep.v, with its module paths, module names and numbers changed; 174 of its 248 lines of code are new or changed and 208 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase YC1g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacHuntRole.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c hunt_c reac_hunt_heard_anything_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition SB_HA : Z := 0x7fff8000.
Definition REAC_HUNT_HEARD_ANYTHING_STK : Z := 16 + ESTACK.
Definition HA_Bx : sv := SOff 32 0.
Definition HA_span : Z * Z := (SB_HA, SB_HA + 2 ^ 44 - 1).
Definition ha_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3);
            (32%nat, mkAF SB_HA SB_HA 0); (33%nat, mkAF 0 4294967295 0) ] [] [].
Definition HA_R : YP09.region := YP09.mkRegion (Some 10%nat) 384 388 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 33 0))].
Definition ha_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; HA_R ].
Definition ss_ha : sstate := mkSS AF_reac_hunt_heard_anything sr_atoms ha_regions None ha_facts.
Definition ha_SH : list shent := [ mkSHE 10 0 480 ].
Lemma ha_val : forall E v, ew E 33 = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  U E (SAlu ALU_SLT (SLit 0) (SExt true 32 (SOff 33 0))) = if 0 <? bv_swrap 32 v then 1 else 0.
Proof.
intros E v H33 Hv.
rewrite U_SAlu, U_SExt. rewrite (U_atom E 33 v H33) by lia. rewrite U_SLit. cbn [zalu_raw].
change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small v) by lia.
assert (HM : bv_half_modulus 32 = 2147483648) by reflexivity.
assert (HMM : bv_modulus 32 = 4294967296) by reflexivity.
assert (Hs : -2147483648 <= bv_swrap 32 v < 2147483648).
{ unfold bv_swrap, bv_wrap. rewrite HM, HMM. pose proof (Z.mod_pos_bound (v + 2147483648) 4294967296 ltac:(lia)). lia. }
set (s := bv_swrap 32 v) in *.
assert (HM64 : bv_half_modulus 64 = 9223372036854775808) by reflexivity.
assert (HMM64 : bv_modulus 64 = 18446744073709551616) by reflexivity.
assert (S0 : bv_swrap 64 (zcanon 0) = 0) by reflexivity.
assert (Ss : bv_swrap 64 (zcanon s) = s).
{ unfold zcanon, M64, bv_swrap, bv_wrap. rewrite HM64, HMM64. change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia. }
rewrite S0, Ss. destruct (0 <? s); reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition ERA (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs [Z_to_bv 64 SB_HA; Z_to_bv 64 v]).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition treac_hunt_heard_anything_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (H : list byte) : world SEGS -> config -> Prop :=
  fun W' c' =>
    apost_base (fx := fq) SEGS B REAC_HUNT_HEARD_ANYTHING_STK [] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (reac_hunt_heard_anything_model (s32_at H 384)) /\
         ly' = ly /\ S' = S /\ W' = W /\
         Permutation (ablocks B ly' S') (ablocks B ly S)) W' c'.
Definition treac_hunt_heard_anything_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h hb hn : Z) (H : list byte),
  afn_pre SEGS B REAC_HUNT_HEARD_ANYTHING_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  getr regs 10 = w64 h -> 0 < h -> h mod 8 = 0 ->
  In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
  hunt_ok H ->
  garr8 SEGS (mrestrict (w_H W) mem) h (map (fun b : byte => bv_unsigned b) H) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_hunt_heard_anything) regs mem md)
    (treac_hunt_heard_anything_post fq regs ly S W mem md H).
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Lemma ha_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md (h hb hn v : Z),
  AR SEGS B ly S W mem md -> astk_ok REAC_HUNT_HEARD_ANYTHING_STK ly (spZ regs) ->
  (forall a, spZ regs - REAC_HUNT_HEARD_ANYTHING_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 h -> h mod 8 = 0 ->
  In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 <= v < 2 ^ 32 -> val_mem SEGS (mrestrict (w_H W) mem) (h + 384) 4 v ->
  st_ok_pi (fx := fq) SEGS VAL (ERA regs v) ss_ha
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_hunt_heard_anything)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS HA_Bx ha_SH (ERA regs v) (mrestrict (w_H W) mem).
Proof.
  intros fq ly S W regs mem md h hb hn v HAR Hstk Hpres H10 H8 Hin Hhb Hh480 Hv Mv.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_HUNT_HEARD_ANYTHING_STK = 4112) by reflexivity.
  destruct (al_blocks _ _ LAWS ly S W mem md hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbia & Hbpres & _).
  pose proof (blk_off_imgP B ly S W mem md hb hn HAR Hin) as Hbimg.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 66 ltac:(vm_compute; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(vm_compute; lia)) as HgotR.
  unfold IMG_LO, IMG_TOP in HcellR, HgotR.
  rewrite restrict_mkst_fx.
  set (E := ERA regs v).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB_HA; Z_to_bv 64 v]) n)
    by (intros n Hn; subst E; unfold ERA; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_HA) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (subst E; unfold ERA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66)))
    by (subst E; unfold ERA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w).
  { intros n w Hn Hw. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hw. }
  unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP in Hbimg, Hbia.
  split.
  - unfold ss_ha. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold ha_regions, stack_region, got_regionP, bcell_regionP, HA_R.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
        [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Ecell) by (pose proof (pa_val_range (A_OBJ 66)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 HA_Bx SB_HA);
        [cbn [sv_denot HA_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_HA; zside | zside |].
        rewrite Z.add_0_r. unfold SB_HA. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
      * rewrite (VB 10%nat h E10) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ h 384 4 (SOff 33 0) v);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
    + apply pairwise_disjoint_of_extents.
      unfold ha_regions, stack_region, got_regionP, bcell_regionP, HA_R, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 10%nat h E10) by lia.
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Ecell) by (pose proof (pa_val_range (A_OBJ 66)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Hb4096 Hbceil Hbimg Hhb Hh480.
      clear. intros. repeat split; lia.
    + split; [|split; exact I].
      cbn [ha_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB_HA; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Hb4096 Hbceil Hhb Hh480 H8 Hv.
      clear. unfold SB_HA. intros. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, ha_SH. apply Forall_cons; [|apply Forall_nil].
    eapply shent_ok_of_range.
    + exact (range_addressable_of_block SEGS B LAWS ly S W mem md hb hn h 480 HAR Hin Hhb Hh480).
    + unfold U, HA_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB_HA; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Theorem pb_reac_hunt_heard_anything : treac_hunt_heard_anything_spec.
Proof.
unfold treac_hunt_heard_anything_spec.
intros fq ly S W regs mem md ch h hb hn H HPRE H10 Hh0 H8 Hin Hhb Hh480 HOK HG.
assert (G : forall r : bv 5, r <> 8%bv -> getr (regupd regs 8 (Z_to_bv 64 0)) r = getr regs r)
  by (intros r Hr; unfold getr; rewrite regupd_other by exact Hr; reflexivity).
assert (Usp0 : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs)
  by (unfold spZ; rewrite G by (intro X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X); reflexivity).
assert (Ura0 : getr (regupd regs 8 (Z_to_bv 64 0)) 1 = getr regs 1)
  by (apply G; intro X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X).
pose proof (ajournal_init SEGS B REAC_HUNT_HEARD_ANYTHING_STK [] ly S W _ mem md ch HPRE) as HJ. rewrite Usp0 in HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite Ura0 in Hra. rewrite Usp0 in Hstk, Hpres.
pose proof HOK as (HL & _).
assert (Rv : 0 <= u_at H 384 4 < 2 ^ 32).
{ unfold u_at. pose proof (disco_table.ble_range (sub H 384 4)) as R.
  rewrite (disco_table.length_sub H 384 4) in R by (try rewrite HL; lia). exact R. }
pose proof (hunt_val4 SEGS (mrestrict (w_H W) mem) h H 384 HG ltac:(lia) ltac:(rewrite HL; lia)) as Mv.
destruct (ha_entry fq ly S W regs mem md h hb hn (u_at H 384 4) HAR Hstk Hpres H10 H8 Hin Hhb Hh480 Rv Mv) as [HS SHOK].
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
remember (ERA regs (u_at H 384 4)) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERA; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB_HA; Z_to_bv 64 (u_at H 384 4)]) n)
  by (intros n Hn; subst E; unfold ERA; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E33 : ew E 33 = Z_to_bv 64 (u_at H 384 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB_HA; Z_to_bv 64 (u_at H 384 4)]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
unfold cfg_at. change (w64 (BASE + AF_reac_hunt_heard_anything)) with (Z_to_bv 64 (BASE + AF_reac_hunt_heard_anything)).
paj_run_tok RUN HS HJ SHOK HA_span;
  [ lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
    eapply awr_ok_cons_stack;
      [reflexivity | exact Usp | azlit_tac | azlit_tac |];
    apply awr_ok_cons_ro; [azlit_tac|];
    apply awr_ok_cons_ro; [azlit_tac|];
    apply awr_ok_cons_ro; [azlit_tac|];
    apply awr_ok_nil
  | ].
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_restrict_reg _ E ssx msx (10%bv : bv 5) HS) as R10;
  replace (sr_get (ss_regs ssx) (10%bv : bv 5))
    with (SAlu ALU_SLT (SLit 0) (SExt true 32 (SOff 33 0))) in R10
    by (vm_compute; reflexivity)
end.
prreg HS (1%bv : bv 5) R1.
rewrite E1 in R1.
eapply (paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat9. cbn [ms_regs ms_mem]. rewrite R1, Hra.
unfold treac_hunt_heard_anything_post.
apply apost_base_same_fx.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  exists ly, S, (ms_regs msx), (ms_mem msx); eexists
end.
split; [reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [Z_to_bv 64 SB_HA; Z_to_bv 64 (u_at H 384 4)] HS);
        [exact HAE | vm_compute; reflexivity]|].
split; [rewrite R10, denot_lit_U, (ha_val E (u_at H 384 4) E33 Rv); reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
apply Permutation_refl.
Qed.
End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_arm_scene on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxArmScene.v, with its module paths and numbers changed; 263 of its 323 lines of code are new or changed and 599 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0d YP0c YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_verdict_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition SB_VN : Z := 0x7fff8000.
Definition REAC_HUNT_VERDICT_NAME_STK : Z := 16 + ESTACK.
Definition VN_Bx : sv := SOff 32 0.
Definition VN_span : Z * Z := (SB_VN, SB_VN + 2 ^ 44 - 1).
Definition vn_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB_VN SB_VN 0); (A_OBJ 59, mkAF IMG_LO IMG_TOP 3) ] [] [].
Definition VN_T : YP09.region := YP09.mkRegion (Some (A_OBJ 59)) 0 24 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 60) (-96))); YP09.mkChunk 8 (CVal 8 (SOff (A_OBJ 60) (-64)));
   YP09.mkChunk 16 (CVal 8 (SOff (A_OBJ 60) (-32)))].
Definition vn_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; VN_T ].
Definition ss_vn : sstate := mkSS AF_both3_reac_hunt_verdict_name sr_atoms vn_regions None vn_facts.
Definition vn_SH : list shent := [ mkSHE (A_OBJ 59) 0 24 ].
Lemma vn_bad : forall E v, ew E 10 = Z_to_bv 64 v -> -2 ^ 31 <= v < 2 ^ 31 ->
  branch_taken BC_LTU (sv_denot E (SLit 2)) (sv_denot E (SAluw ALU_ADD (SOff 10 0) (SLit (-1)))) = false ->
  v = 1 \/ v = 2 \/ v = 3.
Proof.
intros E v H10 Hv Hc. rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc.
rewrite (U_of_S E (SAluw ALU_ADD (SOff 10 0) (SLit (-1)))), S_SAluw, !U_SLit, U_SOff, H10 in Hc. cbn [zalu_raw] in Hc.
rewrite Z_to_bv_unsigned in Hc.
assert (W64 : forall z, bv_wrap 64 z = z mod 18446744073709551616) by (intros z; reflexivity).
assert (S32 : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648) by (intros z; reflexivity).
rewrite !W64, S32 in Hc. unfold zcanon, M64 in Hc.
change (2 ^ 64) with 18446744073709551616 in Hc. change (2 ^ 32) with 4294967296 in Hc.
change (2 ^ 31) with 2147483648 in Hv.
Z.div_mod_to_equations. lia.
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
Definition ERV (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB_VN]).
Definition vn_asan_addr (a : Z) : Z :=
  if a =? A_MASTER then VAL (A_OBJ 60) - 96
  else if a =? A_SLAVE then VAL (A_OBJ 60) - 64
  else if a =? A_REFUSED then VAL (A_OBJ 60) - 32
  else VAL (A_OBJ 60).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition treac_hunt_verdict_name_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (v : Z) : world SEGS -> config -> Prop :=
  fun W' c' =>
    apost_base (fx := fq) SEGS B REAC_HUNT_VERDICT_NAME_STK [] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (vn_asan_addr (reac_hunt_verdict_name_model v)) /\ getr regs' 10 <> w64 0 /\
         garr8 SEGS (mrestrict (w_H W') mem') (vn_asan_addr (reac_hunt_verdict_name_model v))
           (map (fun b : byte => bv_unsigned b) (reac_hunt_verdict_name_str v)) /\
         ly' = ly /\ S' = S /\ W' = W /\
         Permutation (ablocks B ly' S') (ablocks B ly S)) W' c'.
Definition treac_hunt_verdict_name_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (v : Z),
  afn_pre SEGS B REAC_HUNT_VERDICT_NAME_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  getr regs 10 = w64 v -> -2 ^ 31 <= v < 2 ^ 31 ->
  VAL (A_OBJ 59) mod 8 = 0 ->
  zseps [(VAL (A_OBJ 59), 24); (VAL (A_OBJ 0), 8); (VAL (A_OBJ 12), 8)] ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 59)) 24 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 59)) 8 (VAL (A_OBJ 60) - 96) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 59) + 8) 8 (VAL (A_OBJ 60) - 64) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 59) + 16) 8 (VAL (A_OBJ 60) - 32) ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 60) - 96) (map (fun b : byte => bv_unsigned b) S_MASTER) ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 60) - 64) (map (fun b : byte => bv_unsigned b) S_SLAVE) ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 60) - 32) (map (fun b : byte => bv_unsigned b) S_REFUSED) ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 60)) (map (fun b : byte => bv_unsigned b) S_HUNTING) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_hunt_verdict_name) regs mem md)
    (treac_hunt_verdict_name_post fq regs ly S W mem md v).

Local Ltac vn_awr Usp :=
  lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | azlit_tac | azlit_tac |];
  apply awr_ok_cons_ro; [azlit_tac|]; apply awr_ok_cons_ro; [azlit_tac|]; apply awr_ok_cons_ro; [azlit_tac|];
  apply awr_ok_nil.
Local Ltac vn_keep HFr Usp K :=
  lazymatch type of HFr with frame_of ?Ex ?rs ?m1 ?m2 =>
  assert (K : forall a, 0 <= a < IMG_TOP -> mbyte SEGS m2 a = mbyte SEGS m1 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hr := fresh "Hr" in let Hin := fresh "Hin" in
    intros a Ha; unfold IMG_TOP in Ha; unfold mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
    rewrite unsigned_lit_small by lia; unfold in_wrange;
    let rs' := eval vm_compute in rs in change rs with rs';
    intros (r & Hr & Hin); cbn [In] in Hr;
    repeat (destruct Hr as [Hr | Hr];
      [subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hin; try rewrite Usp in Hin; lia |]);
    destruct Hr
  | ] end.
Local Ltac vn_ret HS fq W ly S regs E1 DSV Hra HAE HJ c HA HSTR G K :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let R10 := fresh "R10" in let R1 := fresh "R1" in let mat9 := fresh "mat" in
    pose proof (st_ok_pi_restrict_reg _ _ ssx msx (10%bv : bv 5) HS) as R10;
    replace (sr_get (ss_regs ssx) (10%bv : bv 5)) with (SOff (A_OBJ 60) c) in R10 by (vm_compute; reflexivity);
    pose proof (st_ok_pi_restrict_reg _ _ ssx msx (1%bv : bv 5) HS) as R1;
    replace (sr_get (ss_regs ssx) (1%bv : bv 5)) with (SOff 1 0) in R1 by (vm_compute; reflexivity);
    cbn [sv_denot] in R1; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned in R1; rewrite (DSV c) in R10 by lia;
    eapply (paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat9; cbn [ms_regs ms_mem]; rewrite R1, Hra;
    unfold treac_hunt_verdict_name_post;
    apply apost_base_same_fx;
    exists ly, S, (ms_regs msx), (ms_mem msx); eexists;
    split; [reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SB_VN] HS); [exact HAE | vm_compute; reflexivity]|];
    rewrite HA, HSTR;
    split; [rewrite R10; unfold w64; f_equal; lia|];
    split; [rewrite R10; unfold w64; let X := fresh "X" in intro X; apply (f_equal bv_unsigned) in X;
            rewrite !unsigned_lit_small in X by lia; lia|];
    split; [apply (garr8_frame SEGS _ _ _ _ G);
            let a := fresh "a" in let Ha := fresh "Ha" in
            intros a Ha; apply K; unfold IMG_TOP; rewrite length_map in Ha; cbn [length S_MASTER S_SLAVE S_REFUSED S_HUNTING cstr map app] in Ha; lia|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; apply Permutation_refl
  end.
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Lemma vn_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md,
  AR SEGS B ly S W mem md -> astk_ok REAC_HUNT_VERDICT_NAME_STK ly (spZ regs) ->
  (forall a, spZ regs - REAC_HUNT_VERDICT_NAME_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  VAL (A_OBJ 59) mod 8 = 0 ->
  zseps [(VAL (A_OBJ 59), 24); (VAL (A_OBJ 0), 8); (VAL (A_OBJ 12), 8)] ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 59)) 24 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 59)) 8 (VAL (A_OBJ 60) - 96) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 59) + 8) 8 (VAL (A_OBJ 60) - 64) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 59) + 16) 8 (VAL (A_OBJ 60) - 32) ->
  st_ok_pi (fx := fq) SEGS VAL (ERV regs) ss_vn
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_hunt_verdict_name)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS VN_Bx vn_SH (ERV regs) (mrestrict (w_H W) mem).
Proof.
  intros fq ly S W regs mem md HAR Hstk Hpres HA8 HZ HRA M0 M1 M2.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_HUNT_VERDICT_NAME_STK = 4112) by reflexivity.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img_all 12 ltac:(vm_compute; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img_all 0 ltac:(vm_compute; lia)) as HgotR.
  pose proof (pa_obj_img_all 59 ltac:(vm_compute; lia)) as HtabR.
  pose proof (pa_obj_img_all 60 ltac:(vm_compute; lia)) as HstrR.
  unfold IMG_LO, IMG_TOP in HcellR, HgotR, HtabR, HstrR.
  cbn [zseps zseps_from fst snd] in HZ.
  rewrite restrict_mkst_fx.
  set (E := ERV regs).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB_VN]) n)
    by (intros n Hn; subst E; unfold ERV; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_VN) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Egot : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
    by (subst E; unfold ERV; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
    by (subst E; unfold ERV; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Etab : ew E (A_OBJ 59) = Z_to_bv 64 (VAL (A_OBJ 59)))
    by (subst E; unfold ERV; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Estr : ew E (A_OBJ 60) = Z_to_bv 64 (VAL (A_OBJ 60)))
    by (subst E; unfold ERV; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w).
  { intros n w Hn Hw. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hw. }
  assert (DS : forall c, -96 <= c <= 0 -> sv_denot E (SOff (A_OBJ 60) c) = Z_to_bv 64 (VAL (A_OBJ 60) + c)).
  { intros c Hc. cbn [sv_denot]. rewrite Estr, unsigned_lit_small by lia. reflexivity. }
  split.
  - unfold ss_vn. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold vn_regions, stack_region, got_regionP, bcell_regionP, VN_T.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Egot) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 VN_Bx SB_VN);
        [cbn [sv_denot VN_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_VN; zside | zside |].
        rewrite Z.add_0_r. unfold SB_VN. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
      * rewrite (VB (A_OBJ 59) (VAL (A_OBJ 59)) Etab) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor; [|constructor]]].
        -- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 59)) 0 8 (SOff (A_OBJ 60) (-96)) (VAL (A_OBJ 60) - 96));
           [exact (DS (-96) ltac:(lia)) | zside | zside | rewrite Z.add_0_r; exact M0].
        -- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 59)) 8 8 (SOff (A_OBJ 60) (-64)) (VAL (A_OBJ 60) - 64));
           [exact (DS (-64) ltac:(lia)) | zside | zside | exact M1].
        -- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 59)) 16 8 (SOff (A_OBJ 60) (-32)) (VAL (A_OBJ 60) - 32));
           [exact (DS (-32) ltac:(lia)) | zside | zside | exact M2].
    + apply pairwise_disjoint_of_extents.
      unfold vn_regions, stack_region, got_regionP, bcell_regionP, VN_T, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Egot) by lia.
      rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by lia.
      rewrite (VB (A_OBJ 59) (VAL (A_OBJ 59)) Etab) by lia.
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HtabR HZ.
      clear. intros. repeat split; lia.
    + split; [|split; exact I].
      cbn [vn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E32, Etab, !unsigned_lit_small by (unfold SB_VN; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 HtabR HA8.
      clear. unfold SB_VN, IMG_LO, IMG_TOP. intros. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, vn_SH. apply Forall_cons; [|apply Forall_nil].
    eapply shent_ok_of_range.
    + exact HRA.
    + unfold U, VN_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB_VN; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite Etab, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Theorem pb_reac_hunt_verdict_name : treac_hunt_verdict_name_spec.
Proof.
unfold treac_hunt_verdict_name_spec.
intros fq ly S W regs mem md ch v HPRE H10 Hv HA8 HZ HRA M0 M1 M2 GM GS GR GH.
assert (G8 : forall r : bv 5, r <> 8%bv -> getr (regupd regs 8 (Z_to_bv 64 0)) r = getr regs r)
  by (intros r Hr; unfold getr; rewrite regupd_other by exact Hr; reflexivity).
assert (Usp0 : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs)
  by (unfold spZ; rewrite G8 by (intro X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X); reflexivity).
assert (Ura0 : getr (regupd regs 8 (Z_to_bv 64 0)) 1 = getr regs 1)
  by (apply G8; intro X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X).
pose proof (ajournal_init SEGS B REAC_HUNT_VERDICT_NAME_STK [] ly S W _ mem md ch HPRE) as HJ. rewrite Usp0 in HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite Ura0 in Hra. rewrite Usp0 in Hstk, Hpres.
destruct (vn_entry fq ly S W regs mem md HAR Hstk Hpres HA8 HZ HRA M0 M1 M2) as [HS0 SHOK].
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_VERDICT_NAME_STK = 4112) by reflexivity.
pose proof (pa_obj_img_all 60 ltac:(vm_compute; lia)) as HstrR. unfold IMG_LO, IMG_TOP in HstrR.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
remember (ERV regs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERV; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB_VN]) n)
  by (intros n Hn; subst E; unfold ERV; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Estr : ew E (A_OBJ 60) = Z_to_bv 64 (VAL (A_OBJ 60)))
  by (subst E; unfold ERV; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB_VN]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (DSV : forall c, -96 <= c <= 0 -> sv_denot E (SOff (A_OBJ 60) c) = Z_to_bv 64 (VAL (A_OBJ 60) + c)).
{ intros c Hc. cbn [sv_denot]. rewrite Estr, unsigned_lit_small by lia. reflexivity. }
assert (NE10 : (10%bv : bv 5) <> 0%bv) by (intro X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X).
clear HEdef EL.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_hunt_verdict_name)) with (Z_to_bv 64 (BASE + AF_both3_reac_hunt_verdict_name)).
assert (Hcase : v = 1 \/ v = 2 \/ v = 3 \/ (v <> 1 /\ v <> 2 /\ v <> 3)) by lia.
destruct Hcase as [Hv1 | [Hv2 | [Hv3 | (N1 & N2 & N3)]]].
- subst v.
  pose proof (st_ok_pi_set_reg (fx := fq) E ss_vn _ (10%bv : bv 5) (SLit 1) HS0 NE10 H10) as HS. clear HS0.
  paj_run_tok RUN HS HJ SHOK VN_span; [vn_awr Usp | ].
  vn_keep HFr Usp K.
  assert (HA : vn_asan_addr (reac_hunt_verdict_name_model 1) = VAL (A_OBJ 60) - 96) by reflexivity.
  assert (HSTR : reac_hunt_verdict_name_str 1 = S_MASTER) by reflexivity.
  vn_ret HS fq W ly S regs E1 DSV Hra HAE HJ (-96) HA HSTR GM K.
- subst v.
  pose proof (st_ok_pi_set_reg (fx := fq) E ss_vn _ (10%bv : bv 5) (SLit 2) HS0 NE10 H10) as HS. clear HS0.
  paj_run_tok RUN HS HJ SHOK VN_span; [vn_awr Usp | ].
  vn_keep HFr Usp K.
  assert (HA : vn_asan_addr (reac_hunt_verdict_name_model 2) = VAL (A_OBJ 60) - 64) by reflexivity.
  assert (HSTR : reac_hunt_verdict_name_str 2 = S_SLAVE) by reflexivity.
  vn_ret HS fq W ly S regs E1 DSV Hra HAE HJ (-64) HA HSTR GS K.
- subst v.
  pose proof (st_ok_pi_set_reg (fx := fq) E ss_vn _ (10%bv : bv 5) (SLit 3) HS0 NE10 H10) as HS. clear HS0.
  paj_run_tok RUN HS HJ SHOK VN_span; [vn_awr Usp | ].
  vn_keep HFr Usp K.
  assert (HA : vn_asan_addr (reac_hunt_verdict_name_model 3) = VAL (A_OBJ 60) - 32) by reflexivity.
  assert (HSTR : reac_hunt_verdict_name_str 3 = S_REFUSED) by reflexivity.
  vn_ret HS fq W ly S regs E1 DSV Hra HAE HJ (-32) HA HSTR GR K.
- paj_run_tok RUN HS0 HJ SHOK VN_span; [vn_awr Usp | ].
  vn_keep HFr Usp K1. clear HFr HF HG.
  psrr_branch_tok RUN BR HS0 SHOK VN_span.
  + paj_run_tok RUN HS0 HJ SHOK VN_span; [vn_awr Usp | ].
    vn_keep HFr Usp K2.
    lazymatch type of K2 with context [mbyte _ ?m2 _ = mbyte _ ?m1 _] =>
      assert (K : forall a, 0 <= a < IMG_TOP -> mbyte SEGS m2 a = mbyte SEGS (mrestrict (w_H W) mem) a)
        by (intros a Ha; rewrite (K2 a Ha); exact (K1 a Ha))
    end.
    assert (HA : vn_asan_addr (reac_hunt_verdict_name_model v) = VAL (A_OBJ 60) - 0).
    { unfold reac_hunt_verdict_name_model.
      rewrite (proj2 (Z.eqb_neq v 1) N1), (proj2 (Z.eqb_neq v 2) N2), (proj2 (Z.eqb_neq v 3) N3).
      unfold vn_asan_addr. cbn -[pa_val]. lia. }
    assert (HSTR : reac_hunt_verdict_name_str v = S_HUNTING).
    { unfold reac_hunt_verdict_name_str.
      rewrite (proj2 (Z.eqb_neq v 1) N1), (proj2 (Z.eqb_neq v 2) N2), (proj2 (Z.eqb_neq v 3) N3). reflexivity. }
    replace (VAL (A_OBJ 60)) with (VAL (A_OBJ 60) - 0) in GH by lia.
    vn_ret HS0 fq W ly S regs E1 DSV Hra HAE HJ 0 HA HSTR GH K.
  + exfalso. destruct (vn_bad E v E10 Hv Hc) as [X | [X | X]]; lia.
Qed.
End h.
End f.
End d.

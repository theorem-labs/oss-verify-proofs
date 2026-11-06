(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (record f8f98a95), ex_string's high-surrogate cut (ExsB_Stmt.v CUT_HEX2,
   B 0x844e4): q + 8's shadow (report 0x84870 via 0x8486c, not reached), ld a0,0(s1) (in->end); sub; blt a0,6 ->
   0x847c0 (CUT_FAIL: no room for `\uXXXX`); p + 6's shadow (report 0x848c4 via 0x847a8); lbu (p + 6); bne 92 -> FAIL;
   UBSan beq s4,a2 (a2 = -1: NOT taken); p + 7's shadow (report 0x847bc via 0x847b4); lbu (p + 7); bne 117 -> FAIL;
   UBSan bltu -3,s4 (NOT taken); a0 = p + 8, a1 = sp + 32, jal ex_hex4 (B 0x84548, texhex4_runB), then CUT_HEX2R at
   the return B 0x8454c.
   Two fresh states, split on in->end - (p + 6) < 6 (the text bytes p + 6, p + 7 are a region only when they exist).
   Numerals: 0x194, 0x1fc, 0x470 (DERIVED: cut offsets); 6, 7, 8 (LENGTH: offsets in `\uXXXX\uYYYY`); 32, 36
   (LENGTH: frame slots); atoms 45, 46, 47 (DERIVED: in->end and the two bytes). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB ExsB_Stmt ExsB_Model ExsB_Lib ExsB_Sym ExsB_Exit ExsB_Cont ExsB_LH ExsB_Callee.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).


Definition ES_T6 : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 46 0))].
Definition ES_T7 : YP09.region := YP09.mkRegion (Some 19%nat) 7 8 0 0 [YP09.mkChunk 7 (CVal 1 (SOff 47 0))].
Definition es_h2_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (19%nat, mkAF 4096 ES_CEIL 0);
           (20%nat, mkAF 4096 ES_CEIL 0); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (45%nat, mkAF 4096 ES_CEIL 0);
           (46%nat, mkAF 0 255 0); (47%nat, mkAF 0 255 0)] [] [].
Definition ss_h2a : sstate :=
  mkSS (ES_PC + 0x194) (sr_set sr_atoms 23%bv es_q8shx) [ES_RE] None es_h2_facts.
Definition ss_h2b : sstate :=
  mkSS (ES_PC + 0x194) (sr_set (sr_set (sr_set sr_atoms 23%bv es_q8shx) 26%bv (SLit 92)) 12%bv (SLit (-1)))
    [ES_RE; ES_T6; ES_T7] None es_h2_facts.
Definition es_SH2b : list shent := [mkSHE 9 0 8; mkSHE 20 0 1; mkSHE 19 7 8].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis HHEX4 : texhex4_runB SK B prh_pst ARx (B_prog_sigma AS_ex_hex4).

Definition ES_KEPT_H2A : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 25; 26; 27]%bv.
Ltac es_h2_chain MK :=
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a,
                      MK0 : forall a, _ -> _ -> aview _ _ ?m a = aview _ _ ?mc a |- _ =>
    let MK2 := fresh "MK" in
    assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview sg H m' a = aview sg H mc a)
      by (intros a Ha Hn; rewrite (KEPT a Ha Hn); exact (MK0 a Ha Hn));
    clear KEPT MK0; rename MK2 into MK end.

Definition ES_KEPT_H2B : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 25; 27]%bv.

(* ESB's registers at a leaf: the atoms of KL, s7 (q + 8's shadow address, pinned) and s10 (92) by hand *)
Ltac es_h2_HR HS HEx regs KL HR E9 E22 R23 R26 EWf :=
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?msF) =>
    let HKR := fresh "HKR" in
    pose proof (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) _ _ _ regs _ KL HS
      ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR;
    let HX := fresh "HX" in
    assert (HX : forall r, In r [23; 26]%bv -> getr (ms_regs msF) r = getr regs r);
    [ let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; destruct Hr as [<- | [<- | []]];
      [ let Q := fresh "Q" in es_reg0 HS (23%bv : bv 5) Q;
        rewrite Q, (es_denot_shx Ef 9 22 _ SHADOW_OFF ltac:(first [exact E9 | rewrite EWf by lia; exact E9])
          ltac:(first [exact E22 | rewrite EWf by lia; exact E22])) by (unfold SHADOW_OFF; lia); symmetry; exact R23
      | first [ exact (HKR 26%bv ltac:(cbn; tauto))
              | let Q := fresh "Q" in es_reg0 HS (26%bv : bv 5) Q; rewrite Q; symmetry; exact R26 ] ]
    | assert (HR : forall r, In r ES_REGS -> getr (ms_regs msF) r = getr regs r)
        by exact (es_regs_of regs _ KL [23; 26]%bv HKR HX ltac:(vm_compute; reflexivity)) ]
  end.

Lemma es_cut_hex2 : forall E p, CUT_HEX2R B ARx SK E p -> CUT_HEX2 B ARx SK E p.
Proof.
intros E p HH2R. unfold CUT_HEX2.
intros lyc Sc Hpc regs memc mdc k acc hi HP HB HEG GA Hp6 Hc92 Hc117 Hhi Hhr V36 R18 R19 R20 R12.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as ((HFN & HROD & HTOP) & _ & _ & Ve & _ & _ & _ & _ & _ & (_ & _ & _ & Hxam & _) & _).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC8 & HC16 & HC24 & R2 & R8 & R9 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof (es_cur_ar B ARx SK E lyc Sc Hpc regs memc mdc k HB) as HAR.
pose proof HEG as (HG1 & HG2 & HG3).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (es_cut_mem B ARx SK LAWS E lyc Sc Hpc regs memc mdc k HHEAD HP HB) as
  (HRAx & _ & HTX & (bx & mx & Hbxm & Hbxs & Hxm & Hxhd) & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbxm) as (Bx1 & Bx2 & Bx3 & Bxapp & Bxpres & _).
assert (Hreqx : mx <= req_size mx) by (unfold req_size; destruct (Z.eqb_spec mx 0); lia).
unfold es_SP in *.
set (o := e_scr E + Z.of_nat (length acc)) in *.
assert (VeC : val_mem rsegs (rdW (e_W E) memc) (e_q E + 8) 8 (e_x0 E + es_len E)).
{ apply (es_val_kept (w_H (e_W E)) (e_mem E) memc); [|exact Ve]. intros x Hx. cbn in Hx. apply HWIN; [lia|].
  intros (r & Hr & Hra). cbn [In es_FP] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; unfold es_len in *; lia. }
assert (HRAq : range_addressable (aview rsegs (w_H (e_W E)) memc) SHADOW_OFF (e_q E + 8) 8).
{ apply (es_stk_ra B ARx LAWS lyc Sc Hpc (e_W E) memc mdc (e_q E + 8) 8 HAR); lia. }
assert (HPN : Forall (fun rz => getr regs (fst rz) = Z_to_bv 64 (snd rz)) ([] : list (bv 5 * Z))) by constructor.
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_B)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
destruct (Z_lt_le_dec (e_x0 E + es_len E - (p + 6)) 6) as [Hshort | Hlong].
- (* no room for the second escape *)
  remember (es_xE regs (e_regs E) [w64 (e_x0 E + es_len E)]) as Ex eqn:HEx.
  assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
  assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
  assert (E9 : ew Ex 9 = Z_to_bv 64 (e_q E + 8)) by (rewrite HEx, (es_xE_reg _ _ _ 9%bv 9) by reflexivity; exact R9).
  assert (E19 : ew Ex 19 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
  assert (E20 : ew Ex 20 = Z_to_bv 64 (p + 6)) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
  assert (E22 : ew Ex 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite HEx, (es_xE_reg _ _ _ 22%bv 22) by reflexivity; exact R22).
  assert (E45 : ew Ex 45 = Z_to_bv 64 (e_x0 E + es_len E)) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
  assert (HBx : U Ex (SOff 22 0) = SHADOW_OFF) by (rewrite (U_atom Ex 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
  assert (UA : forall Ef, (forall n, (n < 512)%nat -> ew Ef n = ew Ex n) ->
    U Ef (SAlu ALU_ADD (SMd M_MUL (SOff 20 0) (SLit (-1))) (SOff 45 0)) = e_x0 E + es_len E - (p + 6)).
  { intros Ef HW. rewrite es_U_sub_r;
      rewrite ?(es_U_off Ef Ex 45 0 _ HW ltac:(lia) E45 ltac:(lia) ltac:(lia)),
              ?(es_U_off Ef Ex 20 0 _ HW ltac:(lia) E20 ltac:(lia) ltac:(lia)); lia. }
  assert (E46 : ew Ex 46 = Z_to_bv 64 0) by (rewrite HEx, (es_xE_extra _ _ _ 1) by lia; reflexivity).
  assert (E47 : ew Ex 47 = Z_to_bv 64 0) by (rewrite HEx, (es_xE_extra _ _ _ 2) by lia; reflexivity).
  assert (HS : st_ok_pi rsegs VAL Ex ss_h2a
    (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x194))) memc (YK11.seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_h2a.
    apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
    - apply regs_ok_pin; [rewrite HEx; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
      unfold es_q8shx. rewrite (es_denot_shx Ex 9 22 (e_q E + 8) SHADOW_OFF E9 E22) by (unfold SHADOW_OFF; lia).
      exact R23.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, ES_RE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs Ex _ (e_q E + 8) 0 8 (SOff 45 0) (e_x0 E + es_len E));
        [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact VeC.
    - apply pairwise_disjoint_of_extents. cbn. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok es_h2_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E9, E19, E20, E22, E45, E46, E47, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF, ES_CEIL. repeat split; lia. }
  assert (SHOK : sh_ok rsegs (SOff 22 0) es_SHc Ex (rdW (e_W E) memc)).
  { unfold es_SHc. constructor; [|constructor].
    apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 22 0) 9 (e_q E + 8) 8 (e_q E + 8) 0 8 HRAq HBx);
      [rewrite (U_atom Ex 9 (e_q E + 8) E9) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold SHADOW_OFF. lia. }
  paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
  { es_awr ltac:(fun a Ha => fail). }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. rename KEPT into MK.
  es_envkeep HS Ex EWf.
  psrr_branch_tok RUN BR HS SHOK ES_SPAN.
  + rewrite (es_branch_lt_vals _ _ _ _ 6 (UA _ EWf) (es_U_lit _ 6 ltac:(lia))) in Hc by lia.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x470).
    { es_awr ltac:(fun a Ha => fail). }
    es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h2_chain MK.
    clear EWf. es_envkeep HS Ex EWf.
    es_h2_HR HS HEx regs ES_KEPT_H2A HR E9 E22 R23 R26 EWf.
    pmkst HS. es_pc_to 0x470.
    apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
    ++ apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
         [intros a [] | exact MK | exact HR | exact HPM].
    ++ apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc117. apply (exs_dec_hi_short _ hi Hhi Hhr). rewrite length_skipn.
       pose proof (es_rest_length E (p + 2) ltac:(lia)). lia.
  + rewrite (es_branch_lt_vals _ _ _ _ 6 (UA _ EWf) (es_U_lit _ 6 ltac:(lia))) in Hc by lia.
    apply Z.ltb_ge in Hc. lia.
- (* the second escape's six bytes exist *)
  destruct (HTX (p + 6) ltac:(lia)) as [V6 R6]. destruct (HTX (p + 7) ltac:(lia)) as [V7 R7].
  remember (es_xE regs (e_regs E) [w64 (e_x0 E + es_len E); w64 (es_byte E (p + 6)); w64 (es_byte E (p + 7))]) as Ex eqn:HEx.
  assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
  assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
  assert (E9 : ew Ex 9 = Z_to_bv 64 (e_q E + 8)) by (rewrite HEx, (es_xE_reg _ _ _ 9%bv 9) by reflexivity; exact R9).
  assert (E19 : ew Ex 19 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
  assert (E20 : ew Ex 20 = Z_to_bv 64 (p + 6)) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
  assert (E22 : ew Ex 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite HEx, (es_xE_reg _ _ _ 22%bv 22) by reflexivity; exact R22).
  assert (E45 : ew Ex 45 = Z_to_bv 64 (e_x0 E + es_len E)) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
  assert (HBx : U Ex (SOff 22 0) = SHADOW_OFF) by (rewrite (U_atom Ex 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
  assert (UA : forall Ef, (forall n, (n < 512)%nat -> ew Ef n = ew Ex n) ->
    U Ef (SAlu ALU_ADD (SMd M_MUL (SOff 20 0) (SLit (-1))) (SOff 45 0)) = e_x0 E + es_len E - (p + 6)).
  { intros Ef HW. rewrite es_U_sub_r;
      rewrite ?(es_U_off Ef Ex 45 0 _ HW ltac:(lia) E45 ltac:(lia) ltac:(lia)),
              ?(es_U_off Ef Ex 20 0 _ HW ltac:(lia) E20 ltac:(lia) ltac:(lia)); lia. }
  assert (E46 : ew Ex 46 = Z_to_bv 64 (es_byte E (p + 6))) by (rewrite HEx, (es_xE_extra _ _ _ 1) by lia; reflexivity).
  assert (E47 : ew Ex 47 = Z_to_bv 64 (es_byte E (p + 7))) by (rewrite HEx, (es_xE_extra _ _ _ 2) by lia; reflexivity).
  assert (HS : st_ok_pi rsegs VAL Ex ss_h2b
    (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x194))) memc (YK11.seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_h2b.
    apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
    - apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [rewrite HEx; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X | exact R26] | intros X; discriminate X | exact R12].
      unfold es_q8shx. rewrite (es_denot_shx Ex 9 22 (e_q E + 8) SHADOW_OFF E9 E22) by (unfold SHADOW_OFF; lia).
      exact R23.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      +
        unfold region_ok, ES_RE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs Ex _ (e_q E + 8) 0 8 (SOff 45 0) (e_x0 E + es_len E));
          [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact VeC.
      + unfold region_ok, ES_T6. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E20, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs Ex _ (p + 6) 0 1 (SOff 46 0) (es_byte E (p + 6)));
          [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact V6.
      + unfold region_ok, ES_T7. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E19, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs Ex _ p 7 1 (SOff 47 0) (es_byte E (p + 7)));
          [cbn [sv_denot]; rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        replace (p + 7) with (p + 7) by reflexivity. exact V7.
    - apply pairwise_disjoint_of_extents. unfold extent_of_region, ES_RE, ES_T6, ES_T7.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E19, E20, !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok es_h2_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E9, E19, E20, E22, E45, E46, E47, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF, ES_CEIL. repeat split; lia. }
  assert (SHOK : sh_ok rsegs (SOff 22 0) es_SH2b Ex (rdW (e_W E) memc)).
  { unfold es_SH2b. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 22 0) 9 (e_q E + 8) 8 (e_q E + 8) 0 8 HRAq HBx);
      [rewrite (U_atom Ex 9 (e_q E + 8) E9) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold SHADOW_OFF. lia.
    - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 22 0) 20 (e_x0 E) (es_len E) (p + 6) 0 1 HRAx HBx);
        [rewrite (U_atom Ex 20 (p + 6) E20) by lia; reflexivity | lia | lia |].
      intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bxapp. unfold SHADOW_OFF. lia.
    - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 22 0) 19 (e_x0 E) (es_len E) p 7 8 HRAx HBx);
        [rewrite (U_atom Ex 19 p E19) by lia; reflexivity | lia | lia |].
      intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bxapp. unfold SHADOW_OFF. lia. }
  assert (HPAIR := es_rest_pair E p ltac:(lia) ltac:(lia)).
  paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
  { es_awr ltac:(fun a Ha => fail). }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. rename KEPT into MK.
  es_envkeep HS Ex EWf.
  psrr_branch_tok RUN BR HS SHOK ES_SPAN.
  { rewrite (es_branch_lt_vals _ _ _ _ 6 (UA _ EWf) (es_U_lit _ 6 ltac:(lia))) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  rewrite (es_branch_lt_vals _ _ _ _ 6 (UA _ EWf) (es_U_lit _ 6 ltac:(lia))) in Hc by lia. clear Hc.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
  { es_awr ltac:(fun a Ha => fail). }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h2_chain MK.
  clear EWf. es_envkeep HS Ex EWf.
  psrr_branch_tok RUN BR HS SHOK ES_SPAN.
  + (* p + 6 is not a backslash *)
    es_Uhc Hc EWf. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x470).
    { es_awr ltac:(fun a Ha => fail). }
    es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h2_chain MK.
    clear EWf. es_envkeep HS Ex EWf.
    es_h2_HR HS HEx regs ES_KEPT_H2B HR E9 E22 R23 R26 EWf.
    pmkst HS. es_pc_to 0x470.
    apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
    ++ apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
         [intros a [] | exact MK | exact HR | exact HPM].
    ++ apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc117. rewrite (exs_dec_hi_pair _ hi _ _ _ _ _ _ _ Hhi Hhr HPAIR).
       destruct (Z.eqb_spec (es_byte E (p + 6)) 92); [contradiction | reflexivity].
  + es_Uhc Hc EWf. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb6.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
    { es_awr ltac:(fun a Ha => fail). }
    es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h2_chain MK.
    clear EWf. es_envkeep HS Ex EWf.
    psrr_branch_tok RUN BR HS SHOK ES_SPAN.
    * (* p + 7 is not a u *)
      es_Uhc Hc EWf. apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x470).
      { es_awr ltac:(fun a Ha => fail). }
      es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h2_chain MK.
      clear EWf. es_envkeep HS Ex EWf.
      es_h2_HR HS HEx regs ES_KEPT_H2B HR E9 E22 R23 R26 EWf.
      pmkst HS. es_pc_to 0x470.
      apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
      -- apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
           [intros a [] | exact MK | exact HR | exact HPM].
      -- apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc117. rewrite (exs_dec_hi_pair _ hi _ _ _ _ _ _ _ Hhi Hhr HPAIR).
           rewrite Hb6, Z.eqb_refl. destruct (Z.eqb_spec (es_byte E (p + 7)) 117); [contradiction | reflexivity].
    * es_Uhc Hc EWf. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb7.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
      { es_awr ltac:(fun a Ha => fail). }
      es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr.
      lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msC end.
      lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a |- _ =>
        assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> aview sg H m' a = aview sg H memc a)
          by (intros a Ha; rewrite (KEPT a Ha ltac:(tauto)); exact (MK a Ha ltac:(tauto))) end.
      clear KEPT MK.
      lazymatch type of HS with st_ok _ ?Ef _ _ =>
        assert (EWc : forall n, (n < 512)%nat -> ew Ef n = ew Ex n)
          by (intros n Hn; repeat (rewrite ew_ewset_other by lia); reflexivity);
        assert (HEIc : img_env VAL A_LIM Ef) by assumption end.
      es_reg_st HS (1%bv : bv 5) R1. rewrite (codeptr_val _ _ HEIc) in R1.
      es_reg_st HS (2%bv : bv 5) R2'. es_reg_st HS (10%bv : bv 5) R10'. es_reg_st HS (11%bv : bv 5) R11'.
      rewrite es_den0, (EWc 2%nat ltac:(lia)), E2 in R2'.
      rewrite (es_den_off _ 19 8 p ltac:(rewrite (EWc 19%nat ltac:(lia)); exact E19)) in R10' by lia.
      rewrite (es_den_off _ 2 32 (es_sp E - 144) ltac:(rewrite (EWc 2%nat ltac:(lia)); exact E2)) in R11' by lia.
      assert (HKR : forall r, In r ES_REGS -> getr (ms_regs msC) r = getr regs r).
      { pose proof (regs_kept_of_st_ok _ _ _ _ regs _ ES_KEPT_H2B HS ltac:(es_agree_tac HEx)
          ltac:(vm_compute; reflexivity)) as H0. cbn [ms_regs restrict] in H0.
        apply (es_regs_of regs _ ES_KEPT_H2B [23; 26]%bv H0); [|vm_compute; reflexivity].
        intros r Hr. destruct Hr as [<- | [<- | []]].
        - es_reg_st HS (23%bv : bv 5) Q.
          rewrite Q, (es_denot_shx _ 9 22 _ SHADOW_OFF ltac:(rewrite (EWc 9%nat ltac:(lia)); exact E9)
            ltac:(rewrite (EWc 22%nat ltac:(lia)); exact E22)) by (unfold SHADOW_OFF; lia).
          symmetry; exact R23.
        - es_reg_st HS (26%bv : bv 5) Q. rewrite Q. symmetry; exact R26. }
      assert (HKR3 : forall r, In r [18; 19; 20]%bv -> getr (ms_regs msC) r = getr regs r).
      { pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [18; 19; 20]%bv HS ltac:(es_agree_tac HEx)
          ltac:(vm_compute; reflexivity)) as H0. cbn [ms_regs restrict] in H0. exact H0. }
      pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres' & _).
      assert (HSP : spZ (ms_regs msC) = es_sp E - 144) by (unfold spZ; rewrite R2'; apply unsigned_lit_small; lia).
      pmkst HS.
      eapply SRr_bind.
      { apply (HHEX4 (STK_ex_string + e_d E) (es_sp E + e_d E) (es_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E)
          (e_md E) [] lyc Sc Hpc (e_W E) (ms_mem msC) _ k (ms_regs msC) (p + 8) (es_sp E - 144 + 32)
          (firstn 4 (es_rest E (p + 8))) HJ).
        - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
        - unfold raZ. rewrite R1. apply Z.leb_le. vm_compute. reflexivity.
        - exact R10'.
        - exact R11'.
        - rewrite HSP. lia.
        - rewrite HSP, es_stk_val. unfold EXH_STK. lia.
        - rewrite HSP. lia.
        - intros x Hx. rewrite HSP in Hx. apply HJpres'. rewrite es_stk_val. unfold EXH_STK in Hx. lia.
        - lia.
        - apply (es_amem_sub _ _ _ _ Hxam); unfold es_len in *; lia.
        - apply (es_ra_kept (w_H (e_W E)) memc); [intros x Hx; apply MK2; unfold shadow_of_addr, SHADOW_OFF; lia|].
          intros x Hx. apply HRAx. lia.
        - apply (es_garr8_kept (w_H (e_W E)) memc); [intros a Ha; apply MK2; rewrite length_firstn in Ha; lia|].
          apply (es_text_garr8 E _ (p + 8) 4 HTX); lia.
        - rewrite length_firstn. pose proof (es_rest_length E (p + 8) ltac:(lia)). lia.
        - rewrite ?HSP. lia.
        - rewrite ?es_stk_val. lia.
        - lia.
        - apply (es_stk_ra B ARx LAWS lyc Sc Hpc (e_W E) (ms_mem msC) _ _ 4 HARc); lia.
        - intros x Hx. apply HJpres'. rewrite es_stk_val. lia.
        - right. lia.
        - right. rewrite HSP. unfold EXH_STK. lia. }
      cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & HAR' & HMNk & HKP & HRES).
      rewrite R1. es_pc_to 0x1fc.
      assert (HK' : forall a, 0 <= a < 2 ^ 64 ->
        ~ ((es_sp E - 144 - 16 <= a < es_sp E - 144) \/ (es_sp E - 144 + 32 <= a < es_sp E - 144 + 32 + 4)) ->
        aview rsegs (w_H (e_W E)) mem' a = aview rsegs (w_H (e_W E)) memc a).
      { intros a Ha Hn. etransitivity; [|exact (MK2 a Ha)]. apply HKP; [exact Ha | rewrite HSP; unfold EXH_STK; tauto | tauto]. }
      assert (HR' : forall r, In r ES_REGS -> getr regs' r = getr regs r).
      { intros r Hr. rewrite (es_aregs_ES _ _ HAR' r Hr). exact (HKR r Hr). }
      assert (HR3 : forall r, In r [18; 19; 20]%bv -> getr regs' r = getr regs r).
      { intros r Hr. rewrite (es_aregs_l [18; 19; 20]%bv _ _ ltac:(vm_compute; reflexivity) HAR' r Hr). exact (HKR3 r Hr). }
      apply (HH2R lyc Sc Hpc regs' mem' md' k acc hi HP).
      -- apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k regs' mem' md'
           (fun a => (es_sp E - 144 - 16 <= a < es_sp E - 144) \/ (es_sp E - 144 + 32 <= a < es_sp E - 144 + 32 + 4))
           HHEAD HP HB HJ').
         ++ intros a [Ha | Ha]; right; [left | right]; unfold es_SP; lia.
         ++ exact HK'.
         ++ exact HR'.
         ++ intros H0. exact (HMNk (HPM H0)).
      -- exact HEG.
      -- apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. apply HK'; [lia|]. unfold o in *. lia.
      -- lia.
      -- exact Hc92.
      -- exact Hc117.
      -- exact Hhi.
      -- exact Hhr.
      -- apply (es_val_kept (w_H (e_W E)) memc); [|exact V36]. intros a Ha. unfold es_SP in Ha. apply HK'; lia.
      -- exact Hb6.
      -- exact Hb7.
      -- rewrite exs_hex4_firstn in HRES. destruct (PjGrammar.hex4 (es_rest E (p + 8))) as [lo|].
         ++ destruct HRES as [H10 V]. split; [exact H10 | unfold es_SP; exact V].
         ++ exact (proj1 HRES).
      -- rewrite (HR3 18%bv ltac:(cbn; tauto)). exact R18.
      -- rewrite (HR3 19%bv ltac:(cbn; tauto)). exact R19.
      -- rewrite (HR3 20%bv ltac:(cbn; tauto)). exact R20.
Qed.
End c.

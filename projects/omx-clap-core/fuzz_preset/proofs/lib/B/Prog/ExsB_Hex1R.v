(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (record f8f98a95), ex_string after its first ex_hex4 call
   (ExsB_Stmt.v CUT_HEX1R, B 0x844b4):
     li a2,-1; bnez a0 -> 0x847c0 (CUT_FAIL: not four hex digits); lw a0,36(sp) (the value h); beqz h -> 0x847c0
     (CUT_FAIL: U+0000); andi a0,h,-1024; ld a1,24(sp) (0xdc00); beq -> 0x847c0 (CUT_FAIL: a lone low surrogate);
     UBSan bltu -5, s4 (NOT taken: p + 2 < 2 ^ 47); s4 = p + 6; ld a1,16(sp) (0xd800);
     bne -> 0x84588 (CUT_UTF8 at p + 6 with cp = h) else 0x844e4 (CUT_HEX2: a high surrogate).
   Numerals: 0x164, 0x194, 0x238, 0x470 (DERIVED: cut offsets); 16, 24, 36 (LENGTH: frame slots); 55296 = 0xd800,
   56320 = 0xdc00 (WORD: the spilled constants, ESB); 65535 (LENGTH: four hex digits); 1024 (LENGTH: surrogate block). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB ExsB_Stmt ExsB_Model ExsB_Lib ExsB_Sym ExsB_Exit ExsB_Cont ExsB_LH.
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


Definition ES_RF : YP09.region := YP09.mkRegion (Some 2%nat) 16 40 0 0
  [YP09.mkChunk 16 (CVal 8 (SLit 55296)); YP09.mkChunk 24 (CVal 8 (SLit 56320)); YP09.mkChunk 36 (CVal 4 (SOff 45 0))].
Definition ss_h1r_some : sstate :=
  mkSS (ES_PC + 0x164) (sr_set sr_atoms 10%bv (SLit 0)) [ES_RF] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF 4096 ES_CEIL 0); (20%nat, mkAF 4096 ES_CEIL 0);
              (45%nat, mkAF 0 65535 0)] [] []).
Definition ss_h1r_none : sstate :=
  mkSS (ES_PC + 0x164) (sr_set sr_atoms 10%bv (SLit (-1))) [] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF 4096 ES_CEIL 0); (20%nat, mkAF 4096 ES_CEIL 0)] [] []).

Definition ES_KEPT_H : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.
(* a run that writes nothing: chain its KEPT clause into MK (every byte equal to the cut's memc) *)
Ltac es_h1_chain MK :=
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a,
                      MK0 : forall a, _ -> _ -> aview _ _ ?m a = aview _ _ ?mc a |- _ =>
    let MK2 := fresh "MK" in
    assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview sg H m' a = aview sg H mc a)
      by (intros a Ha Hn; rewrite (KEPT a Ha Hn); exact (MK0 a Ha Hn));
    clear KEPT MK0; rename MK2 into MK end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.

Lemma es_cut_hex1r : forall E p, CUT_UTF8 B ARx SK E (p + 6) -> CUT_HEX2 B ARx SK E p -> CUT_HEX1R B ARx SK E p.
Proof.
intros E p HU8 HH2. unfold CUT_HEX1R. intros lyc Sc Hpc regs memc mdc k acc HP HB HEG GA Hp6 Hc92 Hc17 HRES R18 R19 R20.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC8 & HC16 & HC24 & R2 & R8 & R9 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof HEG as (HG1 & HG2 & HG3).
unfold es_SP in *.
set (o := e_scr E + Z.of_nat (length acc)) in *.
assert (HPN : Forall (fun rz => getr regs (fst rz) = Z_to_bv 64 (snd rz)) ([] : list (bv 5 * Z))) by constructor.
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_B)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
destruct (PjGrammar.hex4 (es_rest E (p + 2))) as [h|] eqn:Hh.
2: { (* not four hex digits *)
  remember (es_xE regs (e_regs E) []) as Ex eqn:HEx.
  assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
  assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
  assert (E19 : ew Ex 19 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
  assert (E20 : ew Ex 20 = Z_to_bv 64 (p + 2)) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
  assert (HS : st_ok_pi rsegs VAL Ex ss_h1r_none
    (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x164))) memc (YK11.seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_h1r_none.
    apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
    - apply regs_ok_pin; [rewrite HEx; apply regs_ok_Eimg_Ereg | intros X; discriminate X | exact HRES].
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - apply pairwise_disjoint_of_extents. cbn. exact I.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E19, E20, !unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold ES_CEIL. repeat split; lia. }
  assert (SHOK : sh_ok rsegs (SOff 22 0) [] Ex (rdW (e_W E) memc)) by apply Forall_nil.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x470).
  { apply awr_ok_nil. }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr.
  es_leaf_regs HS HEx regs ES_REGS ([] : list (bv 5 * Z)) HPN HR.
  pmkst HS. es_pc_to 0x470.
  apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
      [intros a [] | exact KEPT | exact HR | exact HPM].
  + apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc17.
    apply exs_dec_u_nohex. exact Hh. }
destruct HRES as [R10 V36].
pose proof (exs_hex4_range _ _ Hh) as Hhr.
remember (es_xE regs (e_regs E) [w64 h]) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
assert (E19 : ew Ex 19 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
assert (E20 : ew Ex 20 = Z_to_bv 64 (p + 2)) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
assert (E45 : ew Ex 45 = Z_to_bv 64 h) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
assert (U2 : bv_unsigned (ew Ex 2) = es_sp E - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi rsegs VAL Ex ss_h1r_some
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x164))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_h1r_some.
  apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  - apply regs_ok_pin; [rewrite HEx; apply regs_ok_Eimg_Ereg | intros X; discriminate X | exact R10].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, ES_RF. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val rsegs Ex _ (es_sp E - 144) 16 8 (SLit 55296) 55296); [reflexivity | cbn; lia | cbn; lia | exact HC16].
    + apply (chunk_ok_val rsegs Ex _ (es_sp E - 144) 24 8 (SLit 56320) 56320); [reflexivity | cbn; lia | cbn; lia | exact HC24].
    + apply (chunk_ok_val rsegs Ex _ (es_sp E - 144) 36 4 (SOff 45 0) h);
        [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V36].
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E19, E20, E45, !unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold ES_CEIL. repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 22 0) [] Ex (rdW (e_W E) memc)) by apply Forall_nil.
paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ es_awr ltac:(fun a Ha => fail). }
es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. rename KEPT into MK.
es_envkeep HS Ex EWf.
assert (UH : forall Ef, (forall n, (n < 512)%nat -> ew Ef n = ew Ex n) -> U Ef (SOff 45 0) = h)
  by (intros Ef HW; rewrite (es_U_off Ef Ex 45 0 h HW ltac:(lia) E45) by lia; lia).
assert (UM : forall Ef, (forall n, (n < 512)%nat -> ew Ef n = ew Ex n) ->
  U Ef (SAlu ALU_AND (SOff 45 0) (SLit (-1024))) = h - h mod 1024)
  by (intros Ef HW; apply es_U_andm; [exact (UH Ef HW) | lia]).
psrr_branch_tok RUN BR HS SHOK ES_SPAN.
- (* h = 0 *)
  rewrite branch_eq_U, (UH _ EWf), es_U_lit in Hc by lia. apply Z.eqb_eq in Hc. subst h.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x470).
  { es_awr ltac:(fun a Ha => fail). }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h1_chain MK.
    es_leaf_regs HS HEx regs ES_KEPT_H ([] : list (bv 5 * Z)) HPN HR.
    pmkst HS. es_pc_to 0x470.
    apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
    -- apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
         [intros a [] | exact MK | exact HR | exact HPM].
    -- apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc17. apply exs_dec_u_zero. exact Hh.
- rewrite branch_eq_U, (UH _ EWf), es_U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hh0.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
  { es_awr ltac:(fun a Ha => fail). }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h1_chain MK.
  clear EWf. es_envkeep HS Ex EWf.
  psrr_branch_tok RUN BR HS SHOK ES_SPAN.
  + (* a lone low surrogate *)
    rewrite branch_eq_U, (UM _ EWf), es_U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x470).
    { es_awr ltac:(fun a Ha => fail). }
    es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h1_chain MK.
    es_leaf_regs HS HEx regs ES_KEPT_H ([] : list (bv 5 * Z)) HPN HR.
    pmkst HS. es_pc_to 0x470.
    apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
    -- apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
         [intros a [] | exact MK | exact HR | exact HPM].
    -- apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc17. apply (exs_dec_u_low _ h Hh). pose proof (Z.mod_pos_bound h 1024 ltac:(lia)). lia.
  + rewrite branch_eq_U, (UM _ EWf), es_U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hlo.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
    { es_awr ltac:(fun a Ha => fail). }
    es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h1_chain MK.
    clear EWf. es_envkeep HS Ex EWf.
    psrr_branch_tok RUN BR HS SHOK ES_SPAN.
    * (* not a surrogate: UTF8 at p + 6 *)
      rewrite branch_ne_U, (UM _ EWf), es_U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x238).
      { es_awr ltac:(fun a Ha => fail). }
      es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h1_chain MK.
      es_leaf_regs HS HEx regs ES_KEPT_H ([] : list (bv 5 * Z)) HPN HR.
      clear EWf. es_envkeep HS Ex EWf.
      es_reg0 HS (20%bv : bv 5) R20'.
      pmkst HS. es_pc_to 0x238.
      pose proof (Z.mod_pos_bound h 1024 ltac:(lia)) as Hm.
      assert (Hns : ~ (55296 <= h < 57344)) by lia.
      apply (HU8 lyc Sc Hpc _ _ _ k acc h HP).
      -- apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
           [intros a [] | exact MK | exact HR | exact HPM].
      -- apply (es_esg_step E p acc 6 (PjGrammar.utf8 h) HEG ltac:(lia)).
         ++ pose proof (exs_utf8_len_bmp h ltac:(lia)). lia.
         ++ rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc17. rewrite (exs_dec_u_bmp _ h Hh Hh0 Hns).
            unfold es_rest. rewrite exs_skipn_skipn.
            replace (4 + Z.to_nat (p + 2 - e_x0 E))%nat with (Z.to_nat (p + 6 - e_x0 E)) by lia. reflexivity.
      -- lia.
      -- apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. apply MK; [lia | tauto].
      -- apply (es_val_kept (w_H (e_W E)) memc); [|exact V36]. intros a Ha. unfold es_SP in Ha. apply MK; [|tauto]. lia.
      -- rewrite (HKR 18%bv ltac:(cbn; tauto)). exact R18.
      -- rewrite R20', (es_den_off _ 19 6 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
    * (* a high surrogate: HEX2 *)
      rewrite branch_ne_U, (UM _ EWf), es_U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x194).
      { es_awr ltac:(fun a Ha => fail). }
      es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h1_chain MK.
      es_leaf_regs HS HEx regs ES_KEPT_H ([] : list (bv 5 * Z)) HPN HR.
      clear EWf. es_envkeep HS Ex EWf.
      es_reg0 HS (20%bv : bv 5) R20'. es_reg0 HS (12%bv : bv 5) R12'.
      pmkst HS. es_pc_to 0x194.
      pose proof (Z.mod_pos_bound h 1024 ltac:(lia)) as Hm.
      apply (HH2 lyc Sc Hpc _ _ _ k acc h HP).
      -- apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
           [intros a [] | exact MK | exact HR | exact HPM].
      -- exact HEG.
      -- apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. apply MK; [lia | tauto].
      -- exact Hp6.
      -- exact Hc92.
      -- exact Hc17.
      -- exact Hh.
      -- lia.
      -- apply (es_val_kept (w_H (e_W E)) memc); [|exact V36]. intros a Ha. unfold es_SP in Ha. apply MK; [|tauto]. lia.
      -- rewrite (HKR 18%bv ltac:(cbn; tauto)). exact R18.
      -- rewrite (HKR 19%bv ltac:(cbn; tauto)). exact R19.
      -- rewrite R20', (es_den_off _ 19 6 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
      -- rewrite R12'. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.
End c.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 pin asan 1be0f53d96cb), ex_string's high-surrogate cut
   (ExsA_Stmt.v CUT_HEX2, A 0x841a8):
     sub a0,s6,s5; li a1,6; blt a0,a1 -> 0x8442c (CUT_FAIL: no room for `\uXXXX`); p + 6's shadow (slow block
     0x84414, report 0x84520, not reached); lbu a0,0(s5) (p + 6); bne a0,s11 (92) -> FAIL; addi a0,s4,7; p + 7's shadow
     (slow block 0x84420, report 0x84428, not reached); lbu (p + 7); li a1,117; bne -> FAIL; addi a0,s4,8;
     addi a1,sp,32; jal ex_hex4 (A 0x841f4, texhex4_runA through HHEX4), then CUT_HEX2R at the return A 0x841f8.
   Two fresh states, split on in->end - (p + 6) < 6 (the text bytes p + 6, p + 7 are a region only when they exist).
   PORTED from lib/B/Prog/ExsB_Hex2.v (a Theorem Labs lane's B' walk): the same split, the same runs, the same branch tree and
   the same call. CHANGED for A': the pcs; in->end is ESB's cached s6 (atom 22): A' neither re-reads it nor tests
   q + 8's shadow, so the donor's in->end region ES_RE, its atom and q + 8's shadow entry go; no UBSan edge (B' tested
   `beq s4,-1` and `bltu -3,s4`, and pinned a2 = -1 and s10 = 92); hi is s1 (atom 9, callee-saved across the call;
   B': 36(sp)); the backslash test reads s11 (atom 27 = 92, ESB); p / p + 6 / o are s4 / s5 / s3 (atoms 20 / 21 / 19;
   B': s3 / s4 / s2); the shadow base is s7 (atom 23); the two bytes are atoms 45 / 46 (B': 46 / 47).
   Numerals: 0x174, 0x1c4, 0x3f8 (DERIVED: cut offsets); 6, 7, 8 (LENGTH: offsets in `\uXXXX\uYYYY`); 32 (LENGTH:
   the out slot); 92, 117 (WORD: `\` and `u`); atoms 45, 46 (DERIVED: the two bytes). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA ExsA_Stmt ExsA_Lib ExsA_Sym ExsA_Exit ExsA_Cont ExsA_LH ExsA_Callee.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExsB_Model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

(* the bytes p + 6 (through s5 = atom 21) and p + 7 (through s4 = atom 20), read only *)
Definition ES_T6 : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 45 0))].
Definition ES_T7 : YP09.region := YP09.mkRegion (Some 20%nat) 7 8 0 0 [YP09.mkChunk 7 (CVal 1 (SOff 46 0))].
Definition ss_h2a : sstate :=
  mkSS (ES_PC + 0x174) sr_atoms [] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF 4096 ES_CEIL 0); (21%nat, mkAF 4096 ES_CEIL 0);
              (22%nat, mkAF 4096 ES_CEIL 0)] [] []).
Definition ss_h2b : sstate :=
  mkSS (ES_PC + 0x174) sr_atoms [ES_T6; ES_T7] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF 4096 ES_CEIL 0); (21%nat, mkAF 4096 ES_CEIL 0);
              (22%nat, mkAF 4096 ES_CEIL 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (45%nat, mkAF 0 255 0);
              (46%nat, mkAF 0 255 0)] [] []).
Definition es_SH2b : list shent := [mkSHE 21 0 1; mkSHE 20 7 8].
(* the registers every HEX2 segment keeps as atoms (a0 / a1 are written) *)
Definition ES_KEPT_H2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Ltac es_h2_chain MK :=
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a,
                      MK0 : forall a, _ -> _ -> aview _ _ ?m a = aview _ _ ?mc a |- _ =>
    let MK2 := fresh "MK" in
    assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview sg H m' a = aview sg H mc a)
      by (intros a Ha Hn; rewrite (KEPT a Ha Hn); exact (MK0 a Ha Hn));
    clear KEPT MK0; rename MK2 into MK end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis HHEX4 : texhex4_runA SK B prh_pst ARx (A_prog_sigma AS_ex_hex4).

Lemma es_cut_hex2 : forall E p, CUT_HEX2R B ARx SK E p -> CUT_HEX2 B ARx SK E p.
Proof.
intros E p HH2R. unfold CUT_HEX2.
intros lyc Sc Hpc regs memc mdc k acc hi HP HB HEG GA Hp6 Hc92 Hc117 Hhi Hhr R9 R19 R20 R21.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as ((HFN & HROD & HTOP) & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Hxam & _) & _).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC0 & HC8 & HC16 & HC24 & R2 & R8 & R18 & R22 &
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
assert (HPN : Forall (fun rz => getr regs (fst rz) = Z_to_bv 64 (snd rz)) ([] : list (bv 5 * Z))) by constructor.
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_A)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
destruct (Z_lt_le_dec (e_x0 E + es_len E - (p + 6)) 6) as [Hshort | Hlong].
- (* no room for the second escape *)
  remember (es_xE regs (e_regs E) []) as Ex eqn:HEx.
  assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
  assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
  assert (E20 : ew Ex 20 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
  assert (E21 : ew Ex 21 = Z_to_bv 64 (p + 6)) by (rewrite HEx, (es_xE_reg _ _ _ 21%bv 21) by reflexivity; exact R21).
  assert (E22 : ew Ex 22 = Z_to_bv 64 (e_x0 E + es_len E)) by (rewrite HEx, (es_xE_reg _ _ _ 22%bv 22) by reflexivity; exact R22).
  assert (UA : forall Ef, (forall n, (n < 512)%nat -> ew Ef n = ew Ex n) ->
    U Ef (SAlu ALU_ADD (SMd M_MUL (SOff 21 0) (SLit (-1))) (SOff 22 0)) = e_x0 E + es_len E - (p + 6)).
  { intros Ef HW. rewrite es_U_sub_r;
      rewrite ?(es_U_off Ef Ex 22 0 _ HW ltac:(lia) E22 ltac:(lia) ltac:(lia)),
              ?(es_U_off Ef Ex 21 0 _ HW ltac:(lia) E21 ltac:(lia) ltac:(lia)); lia. }
  assert (HS : st_ok_pi rsegs VAL Ex ss_h2a
    (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x174))) memc (YK11.seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_h2a.
    apply (pa_entry_st_ok_full (fx := fx) (L := A_prog_listing) (PI := PI_prog_A)).
    - rewrite HEx. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - apply pairwise_disjoint_of_extents. cbn. exact I.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E20, E21, E22, !unsigned_lit_small by lia.
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold ES_CEIL. repeat split; lia. }
  assert (SHOK : sh_ok rsegs (SOff 23 0) [] Ex (rdW (e_W E) memc)) by apply Forall_nil.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
  { apply awr_ok_nil. }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. rename KEPT into MK.
  es_envkeep HS Ex EWf.
  psrr_branch_tok RUN BR HS SHOK ES_SPAN.
  + rewrite (es_branch_lt_vals _ _ _ _ 6 (UA _ EWf) (es_U_lit _ 6 ltac:(lia))) in Hc by lia.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x3f8).
    { apply awr_ok_nil. }
    es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h2_chain MK.
    es_leaf_regs HS HEx regs ES_KEPT_H2 ([] : list (bv 5 * Z)) HPN HR.
    pmkst HS. es_pc_to 0x3f8.
    apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
    ++ apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
         [intros a [] | exact MK | exact HR | exact HPM].
    ++ apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc117.
       apply (exs_dec_hi_short _ hi Hhi Hhr). rewrite length_skipn.
       pose proof (es_rest_length E (p + 2) ltac:(lia)). lia.
  + rewrite (es_branch_lt_vals _ _ _ _ 6 (UA _ EWf) (es_U_lit _ 6 ltac:(lia))) in Hc by lia.
    apply Z.ltb_ge in Hc. lia.
- (* the second escape's six bytes exist *)
  destruct (HTX (p + 6) ltac:(lia)) as [V6 R6]. destruct (HTX (p + 7) ltac:(lia)) as [V7 R7].
  remember (es_xE regs (e_regs E) [w64 (es_byte E (p + 6)); w64 (es_byte E (p + 7))]) as Ex eqn:HEx.
  assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
  assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
  assert (E20 : ew Ex 20 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
  assert (E21 : ew Ex 21 = Z_to_bv 64 (p + 6)) by (rewrite HEx, (es_xE_reg _ _ _ 21%bv 21) by reflexivity; exact R21).
  assert (E22 : ew Ex 22 = Z_to_bv 64 (e_x0 E + es_len E)) by (rewrite HEx, (es_xE_reg _ _ _ 22%bv 22) by reflexivity; exact R22).
  assert (E23 : ew Ex 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite HEx, (es_xE_reg _ _ _ 23%bv 23) by reflexivity; exact R23).
  assert (E27 : ew Ex 27 = Z_to_bv 64 92) by (rewrite HEx, (es_xE_reg _ _ _ 27%bv 27) by reflexivity; exact R27).
  assert (E45 : ew Ex 45 = Z_to_bv 64 (es_byte E (p + 6))) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
  assert (E46 : ew Ex 46 = Z_to_bv 64 (es_byte E (p + 7))) by (rewrite HEx, (es_xE_extra _ _ _ 1) by lia; reflexivity).
  assert (HBx : U Ex (SOff 23 0) = SHADOW_OFF) by (rewrite (U_atom Ex 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia); reflexivity).
  assert (UA : forall Ef, (forall n, (n < 512)%nat -> ew Ef n = ew Ex n) ->
    U Ef (SAlu ALU_ADD (SMd M_MUL (SOff 21 0) (SLit (-1))) (SOff 22 0)) = e_x0 E + es_len E - (p + 6)).
  { intros Ef HW. rewrite es_U_sub_r;
      rewrite ?(es_U_off Ef Ex 22 0 _ HW ltac:(lia) E22 ltac:(lia) ltac:(lia)),
              ?(es_U_off Ef Ex 21 0 _ HW ltac:(lia) E21 ltac:(lia) ltac:(lia)); lia. }
  assert (HS : st_ok_pi rsegs VAL Ex ss_h2b
    (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x174))) memc (YK11.seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_h2b.
    apply (pa_entry_st_ok_full (fx := fx) (L := A_prog_listing) (PI := PI_prog_A)).
    - rewrite HEx. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold region_ok, ES_T6. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E21, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs Ex _ (p + 6) 0 1 (SOff 45 0) (es_byte E (p + 6)));
          [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact V6.
      + unfold region_ok, ES_T7. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E20, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs Ex _ p 7 1 (SOff 46 0) (es_byte E (p + 7)));
          [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        exact V7.
    - apply pairwise_disjoint_of_extents. unfold extent_of_region, ES_T6, ES_T7.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E20, E21, !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E20, E21, E22, E23, E45, E46, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF, ES_CEIL. repeat split; lia. }
  assert (SHOK : sh_ok rsegs (SOff 23 0) es_SH2b Ex (rdW (e_W E) memc)).
  { unfold es_SH2b. constructor; [|constructor; [|constructor]].
    - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 23 0) 21 (e_x0 E) (es_len E) (p + 6) 0 1 HRAx HBx);
        [rewrite (U_atom Ex 21 (p + 6) E21) by lia; reflexivity | lia | lia |].
      intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bxapp. unfold SHADOW_OFF. lia.
    - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 23 0) 20 (e_x0 E) (es_len E) p 7 8 HRAx HBx);
        [rewrite (U_atom Ex 20 p E20) by lia; reflexivity | lia | lia |].
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
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x3f8).
    { es_awr ltac:(fun a Ha => fail). }
    es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h2_chain MK.
    es_leaf_regs HS HEx regs ES_KEPT_H2 ([] : list (bv 5 * Z)) HPN HR.
    pmkst HS. es_pc_to 0x3f8.
    apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
    ++ apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
         [intros a [] | exact MK | exact HR | exact HPM].
    ++ apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc117.
       rewrite (exs_dec_hi_pair _ hi _ _ _ _ _ _ _ Hhi Hhr HPAIR).
       destruct (Z.eqb_spec (es_byte E (p + 6)) 92); [contradiction | reflexivity].
  + es_Uhc Hc EWf. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb6.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
    { es_awr ltac:(fun a Ha => fail). }
    es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h2_chain MK.
    clear EWf. es_envkeep HS Ex EWf.
    psrr_branch_tok RUN BR HS SHOK ES_SPAN.
    * (* p + 7 is not a u *)
      es_Uhc Hc EWf. apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x3f8).
      { es_awr ltac:(fun a Ha => fail). }
      es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. es_h2_chain MK.
      es_leaf_regs HS HEx regs ES_KEPT_H2 ([] : list (bv 5 * Z)) HPN HR.
      pmkst HS. es_pc_to 0x3f8.
      apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
      -- apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
           [intros a [] | exact MK | exact HR | exact HPM].
      -- apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc117.
         rewrite (exs_dec_hi_pair _ hi _ _ _ _ _ _ _ Hhi Hhr HPAIR).
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
      rewrite (es_den_off _ 20 8 p ltac:(rewrite (EWc 20%nat ltac:(lia)); exact E20)) in R10' by lia.
      rewrite (es_den_off _ 2 32 (es_sp E - 144) ltac:(rewrite (EWc 2%nat ltac:(lia)); exact E2)) in R11' by lia.
      assert (HKR : forall r, In r ES_REGS -> getr (ms_regs msC) r = getr regs r).
      { pose proof (regs_kept_of_st_ok _ _ _ _ regs _ ES_REGS HS ltac:(es_agree_tac HEx)
          ltac:(vm_compute; reflexivity)) as H0. cbn [ms_regs restrict] in H0. exact H0. }
      assert (HKR3 : forall r, In r [9; 19; 20; 21]%bv -> getr (ms_regs msC) r = getr regs r).
      { pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [9; 19; 20; 21]%bv HS ltac:(es_agree_tac HEx)
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
      rewrite R1. es_pc_to 0x1c4.
      assert (HK' : forall a, 0 <= a < 2 ^ 64 ->
        ~ ((es_sp E - 144 - 16 <= a < es_sp E - 144) \/ (es_sp E - 144 + 32 <= a < es_sp E - 144 + 32 + 4)) ->
        aview rsegs (w_H (e_W E)) mem' a = aview rsegs (w_H (e_W E)) memc a).
      { intros a Ha Hn. etransitivity; [|exact (MK2 a Ha)]. apply HKP; [exact Ha | rewrite HSP; unfold EXH_STK; tauto | tauto]. }
      assert (HR' : forall r, In r ES_REGS -> getr regs' r = getr regs r).
      { intros r Hr. rewrite (es_aregs_ES _ _ HAR' r Hr). exact (HKR r Hr). }
      assert (HR3 : forall r, In r [9; 19; 20; 21]%bv -> getr regs' r = getr regs r).
      { intros r Hr. rewrite (es_aregs_l [9; 19; 20; 21]%bv _ _ ltac:(vm_compute; reflexivity) HAR' r Hr). exact (HKR3 r Hr). }
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
      -- rewrite (HR3 9%bv ltac:(cbn; tauto)). exact R9.
      -- exact Hb6.
      -- exact Hb7.
      -- rewrite exs_hex4_firstn in HRES. destruct (PjGrammar.hex4 (es_rest E (p + 8))) as [lo|].
         ++ destruct HRES as [H10 V]. split; [exact H10 | unfold es_SP; exact V].
         ++ exact (proj1 HRES).
      -- rewrite (HR3 19%bv ltac:(cbn; tauto)). exact R19.
      -- rewrite (HR3 20%bv ltac:(cbn; tauto)). exact R20.
      -- rewrite (HR3 21%bv ltac:(cbn; tauto)). exact R21.
Qed.
End c.

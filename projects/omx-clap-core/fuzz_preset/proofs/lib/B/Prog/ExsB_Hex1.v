(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (record f8f98a95), ex_string's first `\u` cut (ExsB_Stmt.v CUT_HEX1):
     B 0x8449c sub a0,a1,s4; blt a0,4 -> 0x847c0 (CUT_FAIL: fewer than four bytes after the u);
     a1 = sp + 36, a0 = s4 = p + 2, jal ex_hex4 (B 0x844b0, the callee's run form texhex4_runB, ExsB_Callee.v),
     then CUT_HEX1R at the return B 0x844b4.
   Numerals: 0x14c, 0x164, 0x470 (DERIVED: cut offsets); 36 (LENGTH: the out slot); 4 (LENGTH: four digits). *)
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

Definition ss_hex1 : sstate :=
  mkSS (ES_PC + 0x14c) sr_atoms [] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 ES_CEIL 0); (19%nat, mkAF 4096 ES_CEIL 0);
              (20%nat, mkAF 4096 ES_CEIL 0)] [] []).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis HHEX4 : texhex4_runB SK B prh_pst ARx (B_prog_sigma AS_ex_hex4).

Lemma es_cut_hex1 : forall E p, CUT_HEX1R B ARx SK E p -> CUT_HEX1 B ARx SK E p.
Proof.
intros E p HH1R. unfold CUT_HEX1. intros lyc Sc Hpc regs memc mdc k acc HP HB HEG GA Hp1 Hc92 Hc117 R18 R19 R20 R11.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC8 & HC16 & HC24 & R2 & R8 & R9 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof (es_cur_ar B ARx SK E lyc Sc Hpc regs memc mdc k HB) as HAR.
pose proof HEG as (HG1 & HG2 & HG3).
unfold es_SP in *.
set (o := e_scr E + Z.of_nat (length acc)) in *.
remember (es_xE regs (e_regs E) []) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
assert (E11 : ew Ex 11 = Z_to_bv 64 (e_x0 E + es_len E)) by (rewrite HEx, (es_xE_reg _ _ _ 11%bv 11) by reflexivity; exact R11).
assert (E19 : ew Ex 19 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
assert (E20 : ew Ex 20 = Z_to_bv 64 (p + 2)) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
assert (U2 : bv_unsigned (ew Ex 2) = es_sp E - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew Ex 11) = e_x0 E + es_len E) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ex 19) = p) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew Ex 20) = p + 2) by (rewrite E20; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi rsegs VAL Ex ss_hex1
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x14c))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_hex1. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  - rewrite HEx. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U11, U19, U20. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold ES_CEIL. repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 22 0) [] Ex (rdW (e_W E) memc)) by apply Forall_nil.
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_B)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
destruct (es_cut_mem B ARx SK LAWS E lyc Sc Hpc regs memc mdc k HHEAD HP HB) as (HRAx & _ & HTX & _ & _).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as ((HFN & HROD & HTOP) & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Hxam & _) & _).
pose proof HFN as (HAR0 & Hra & Hra4 & Hgp & Htp & _).
assert (HPN : Forall (fun rz => getr regs (fst rz) = Z_to_bv 64 (snd rz)) ([] : list (bv 5 * Z))) by constructor.
paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ apply awr_ok_nil. }
es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. rename KEPT into MK.
es_envkeep HS Ex EWf.
assert (UA : forall Ef, (forall n, (n < 512)%nat -> ew Ef n = ew Ex n) ->
  U Ef (SAlu ALU_ADD (SOff 11 0) (SMd M_MUL (SOff 20 0) (SLit (-1)))) = e_x0 E + es_len E - (p + 2)).
{ intros Ef HW. rewrite es_U_sub;
    rewrite ?(es_U_off Ef Ex 11 0 _ HW ltac:(lia) E11 ltac:(lia) ltac:(lia)),
            ?(es_U_off Ef Ex 20 0 _ HW ltac:(lia) E20 ltac:(lia) ltac:(lia)); lia. }
psrr_branch_tok RUN BR HS SHOK ES_SPAN.
- (* fewer than four bytes after the u *)
  rewrite (es_branch_lt_vals _ _ _ _ 4 (UA _ EWf) (es_U_lit _ 4 ltac:(lia))) in Hc by lia. apply Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x470).
  { apply awr_ok_nil. }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr.
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a |- _ =>
    assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview sg H m' a = aview sg H memc a)
      by (intros a Ha Hn; rewrite (KEPT a Ha Hn); exact (MK a Ha Hn)) end.
  es_leaf_regs HS HEx regs ES_REGS ([] : list (bv 5 * Z)) HPN HR.
  pmkst HS. es_pc_to 0x470.
  apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
      [intros a [] | exact MK2 | exact HR | exact HPM].
  + apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc117.
    apply exs_dec_u_short. pose proof (es_rest_length E (p + 2) ltac:(lia)). lia.
- rewrite (es_branch_lt_vals _ _ _ _ 4 (UA _ EWf) (es_U_lit _ 4 ltac:(lia))) in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
  { apply awr_ok_nil. }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msC end.
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a |- _ =>
    idtac "KEPTFORM" m' m;
    assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> aview sg H m' a = aview sg H memc a)
      by (intros a Ha; rewrite (KEPT a Ha ltac:(tauto)); exact (MK a Ha ltac:(tauto))) end.
  clear KEPT MK.
  es_reg_st HS (1%bv : bv 5) R1. rewrite (codeptr_val _ _ HEI) in R1.
  es_reg_st HS (2%bv : bv 5) R2'. es_reg_st HS (10%bv : bv 5) R10'. es_reg_st HS (11%bv : bv 5) R11'.
  rewrite es_den0 in R2', R10'. rewrite E2 in R2'. rewrite E20 in R10'.
  rewrite (es_den_off _ 2 36 (es_sp E - 144) E2) in R11' by lia.
  assert (HKR : forall r, In r ES_REGS -> getr (ms_regs msC) r = getr regs r).
  { pose proof (regs_kept_of_st_ok _ _ _ _ regs _ ES_REGS HS ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as H0.
    cbn [ms_regs restrict] in H0. exact H0. }
  pose proof HJ as (HARc & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (HSP : spZ (ms_regs msC) = es_sp E - 144) by (unfold spZ; rewrite R2'; apply unsigned_lit_small; lia).
  pmkst HS.
  eapply SRr_bind.
  { apply (HHEX4 (STK_ex_string + e_d E) (es_sp E + e_d E) (es_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E)
      (e_md E) [] lyc Sc Hpc (e_W E) (ms_mem msC) _ k (ms_regs msC) (p + 2) (es_sp E - 144 + 36)
      (firstn 4 (es_rest E (p + 2))) HJ).
    - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite R1. apply Z.leb_le. vm_compute. reflexivity.
    - exact R10'.
    - exact R11'.
    - rewrite ?HSP. lia.
    - rewrite HSP, es_stk_val. unfold EXH_STK. lia.
    - rewrite ?HSP. lia.
    - intros x Hx. rewrite HSP in Hx. apply HJpres. rewrite es_stk_val. unfold EXH_STK in Hx. lia.
    - lia.
    - apply (es_amem_sub _ _ _ _ Hxam); unfold es_len in *; lia.
    - apply (es_ra_kept (w_H (e_W E)) memc); [intros x Hx; apply MK2; unfold shadow_of_addr, SHADOW_OFF; lia|].
      intros x Hx. apply HRAx. lia.
    - apply (es_garr8_kept (w_H (e_W E)) memc); [intros a Ha; apply MK2; rewrite length_firstn in Ha; lia|].
      apply (es_text_garr8 E _ (p + 2) 4 HTX); lia.
    - rewrite length_firstn. pose proof (es_rest_length E (p + 2) ltac:(lia)). lia.
    - rewrite ?HSP. lia.
    - rewrite ?es_stk_val. lia.
    - lia.
    - apply (es_stk_ra B ARx LAWS lyc Sc Hpc (e_W E) (ms_mem msC) _ _ 4 HARc); lia.
    - intros x Hx. apply HJpres. rewrite es_stk_val. lia.
    - right. lia.
    - right. rewrite HSP. unfold EXH_STK. lia. }
  cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & HAR' & HMNk & HKP & HRES).
  rewrite R1. es_pc_to 0x164.
  assert (HK' : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((es_sp E - 144 - 16 <= a < es_sp E - 144) \/ (es_sp E - 144 + 36 <= a < es_sp E - 144 + 36 + 4)) ->
    aview rsegs (w_H (e_W E)) mem' a = aview rsegs (w_H (e_W E)) memc a).
  { intros a Ha Hn. etransitivity; [|exact (MK2 a Ha)]. apply HKP; [exact Ha | rewrite HSP; unfold EXH_STK; tauto | tauto]. }
  assert (HR' : forall r, In r ES_REGS -> getr regs' r = getr regs r).
  { intros r Hr. rewrite (es_aregs_ES _ _ HAR' r Hr). exact (HKR r Hr). }
  assert (HKR3 : forall r, In r [18; 19; 20]%bv -> getr (ms_regs msC) r = getr regs r).
  { pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [18; 19; 20]%bv HS ltac:(es_agree_tac HEx)
      ltac:(vm_compute; reflexivity)) as H0. cbn [ms_regs restrict] in H0. exact H0. }
  assert (HR3 : forall r, In r [18; 19; 20]%bv -> getr regs' r = getr regs r).
  { intros r Hr. rewrite (es_aregs_l [18; 19; 20]%bv _ _ ltac:(vm_compute; reflexivity) HAR' r Hr). exact (HKR3 r Hr). }
  apply (HH1R lyc Sc Hpc regs' mem' md' k acc HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k regs' mem' md'
      (fun a => (es_sp E - 144 - 16 <= a < es_sp E - 144) \/ (es_sp E - 144 + 36 <= a < es_sp E - 144 + 36 + 4))
      HHEAD HP HB HJ').
    * intros a [Ha | Ha]; right; [left | right]; unfold es_SP; lia.
    * exact HK'.
    * exact HR'.
    * intros H0. exact (HMNk (HPM H0)).
  + exact HEG.
  + apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. apply HK'; [lia|].
    unfold o in *. lia.
  + lia.
  + exact Hc92.
  + exact Hc117.
  + rewrite exs_hex4_firstn in HRES. destruct (PjGrammar.hex4 (es_rest E (p + 2))) as [h|].
    * destruct HRES as [H10 V]. split; [exact H10 | unfold es_SP; exact V].
    * exact (proj1 HRES).
  + rewrite (HR3 18%bv ltac:(cbn; tauto)). exact R18.
  + rewrite (HR3 19%bv ltac:(cbn; tauto)). exact R19.
  + rewrite (HR3 20%bv ltac:(cbn; tauto)). exact R20.
Qed.
End c.

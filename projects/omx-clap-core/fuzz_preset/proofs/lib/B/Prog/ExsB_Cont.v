(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (record f8f98a95), ex_string's CONT cut (ExsB_Stmt.v CUT_CONT):
     B 0x84708 lbu a1,0(s7) / bnez -> 0x84848 (q + 8's shadow, report 0x8484c), ld a1,0(s1) (in->end), mv s3,s4,
     mv s2,a0, bgeu s4,a1 -> 0x847c0 (p >= in->end: return -1), j 0x8443c (the loop head)
   from the loop head's invariant at the new p (LH_AT E p, the walk's induction hypothesis). Two runs from one fresh
   state: to the branch, then to B 0x847c0 (CUT_FAIL) or to B 0x8443c (LH_AT). q + 8's shadow branch is decided by its
   shadow entry (the real stack, es_stk_ra); the run writes nothing.
   Numerals: 0x3b8, 0x470, 0xec (DERIVED: cut offsets); atom 45 (DERIVED: in->end); region bound 8 (LENGTH). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB ExsB_Stmt ExsB_Model ExsB_Lib ExsB_Sym ExsB_Exit.
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

(* the CONT state: in->end (atom 45) through s1 = q + 8 (atom 9); s7 (23) is q + 8's shadow address *)
Definition ES_RE : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 45 0))].
Definition es_q8shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 22 0).
Definition ss_cont : sstate :=
  mkSS (ES_PC + 0x3b8) (sr_set sr_atoms 23%bv es_q8shx) [ES_RE] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
              (20%nat, mkAF 4096 ES_CEIL 0); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (45%nat, mkAF 4096 ES_CEIL 0)]
      [] []).
Definition es_SHc : list shent := [mkSHE 9 0 8].
Definition ES_KEPT_C : list (bv 5) := [2; 3; 4; 5; 8; 9; 14; 15; 16; 17; 21; 22; 24; 25; 26; 27]%bv.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.

Lemma es_cut_cont : forall E p, LH_AT B ARx SK E p -> CUT_CONT B ARx SK E p.
Proof.
intros E p HLH. unfold CUT_CONT. intros lyc Sc Hpc regs memc mdc k acc HP HB HK HEG GA R10 R20.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & Ve & _).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC8 & HC16 & HC24 & R2 & R8 & R9 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof (es_cur_ar B ARx SK E lyc Sc Hpc regs memc mdc k HB) as HAR.
pose proof HEG as (HG1 & HG2 & HG3).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
unfold es_SP in *.
(* in->end at the cut: the caller's window outside FP *)
assert (VeC : val_mem rsegs (rdW (e_W E) memc) (e_q E + 8) 8 (e_x0 E + es_len E)).
{ apply (es_val_kept (w_H (e_W E)) (e_mem E) memc); [|exact Ve]. intros x Hx. cbn in Hx. apply HWIN; [lia|].
  intros (r & Hr & Hra). cbn [In es_FP] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; unfold es_len in *; lia. }
assert (HRAq : range_addressable (aview rsegs (w_H (e_W E)) memc) SHADOW_OFF (e_q E + 8) 8).
{ apply (es_stk_ra B ARx LAWS lyc Sc Hpc (e_W E) memc mdc (e_q E + 8) 8 HAR); lia. }
remember (es_xE regs (e_regs E) [w64 (e_x0 E + es_len E)]) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
assert (E9 : ew Ex 9 = Z_to_bv 64 (e_q E + 8)) by (rewrite HEx, (es_xE_reg _ _ _ 9%bv 9) by reflexivity; exact R9).
assert (E20 : ew Ex 20 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
assert (E22 : ew Ex 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite HEx, (es_xE_reg _ _ _ 22%bv 22) by reflexivity; exact R22).
assert (E45 : ew Ex 45 = Z_to_bv 64 (e_x0 E + es_len E)) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
assert (U2 : bv_unsigned (ew Ex 2) = es_sp E - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew Ex 9) = e_q E + 8) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew Ex 20) = p) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew Ex 22) = SHADOW_OFF) by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U45 : bv_unsigned (ew Ex 45) = e_x0 E + es_len E) by (rewrite E45; apply unsigned_lit_small; lia).
assert (HBx : U Ex (SOff 22 0) = SHADOW_OFF) by (rewrite (U_atom Ex 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
assert (HS : st_ok_pi rsegs VAL Ex ss_cont
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x3b8))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_cont. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  - apply regs_ok_pin; [rewrite HEx; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    unfold es_q8shx. rewrite (es_denot_shx Ex 9 22 (e_q E + 8) SHADOW_OFF E9 E22) by (unfold SHADOW_OFF; lia).
    exact R23.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, ES_RE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs Ex _ (e_q E + 8) 0 8 (SOff 45 0) (e_x0 E + es_len E));
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact VeC.
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U20, U22, U45. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, ES_CEIL. repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 22 0) es_SHc Ex (rdW (e_W E) memc)).
{ unfold es_SHc. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 22 0) 9 (e_q E + 8) 8 (e_q E + 8) 0 8 HRAq HBx);
    [rewrite (U_atom Ex 9 (e_q E + 8) E9) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia. }
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
assert (HPM : es_P E memc) by exact HMN.
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_B)).
unfold cfg_at, w64. rewrite es_pc_eq.
paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ intros a (rg & Hin & Har). cbn [ss_mem ss_cont In] in Hin. destruct Hin as [<- | []]. cbn in Har. lia. }
assert (MEQ : forall a, aview rsegs (w_H (e_W E)) (ms_mem ms) a = aview rsegs (w_H (e_W E)) memc a).
{ intros a. apply aview_eq_of. apply HFr. intros (rg & Hin & Har). cbn [ss_mem ss_cont In] in Hin.
  destruct Hin as [<- | []]. cbn in Har. lia. }
clear HF HG HFr.
psrr_branch_tok RUN BR HS SHOK ES_SPAN.
- (* p >= in->end: return -1 *)
  rewrite branch_geu_U, (U_atom Ex 20 p E20), (U_atom Ex 45 _ E45) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x470).
  { intros a (rg & Hin & Har). cbn [ss_mem add_cond ss_cont In] in Hin. destruct Hin as [<- | []]. cbn in Har. lia. }
  assert (MEQ2 : forall a, aview rsegs (w_H (e_W E)) (ms_mem ms0) a = aview rsegs (w_H (e_W E)) memc a).
  { intros a. rewrite <- (MEQ a). apply aview_eq_of. apply HFr. intros (rg & Hin & Har). cbn [ss_mem add_cond ss_cont In] in Hin.
    destruct Hin as [<- | []]. cbn in Har. lia. }
  clear HF HG HFr.
  es_envkeep HS Ex EWf.
  pose proof (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) _ _ _ regs _ ES_KEPT_C HS
    ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
  es_reg0 HS (23%bv : bv 5) R23'.
  pmkst HS. es_pc_to 0x470.
  eapply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc (ms_regs ms0) (ms_mem ms0) _ k HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k (ms_regs ms0) (ms_mem ms0) _ (fun _ => False)
      HHEAD HP HB HJ); [intros a [] | intros a _ _; apply MEQ2 | | exact HPM].
    apply (es_regs_of regs (ms_regs ms0) ES_KEPT_C [23%bv] HKR); [|vm_compute; reflexivity].
    intros r [<- | []]. rewrite R23', (es_denot_shx _ 9 22 (e_q E + 8) SHADOW_OFF
      ltac:(first [exact E9 | rewrite EWf by lia; exact E9]) ltac:(first [exact E22 | rewrite EWf by lia; exact E22])) by (unfold SHADOW_OFF; lia).
    symmetry; exact R23.
  + rewrite HG3, (es_rest_end E p) by lia. reflexivity.
- (* p < in->end: back to the loop head *)
  rewrite branch_geu_U, (U_atom Ex 20 p E20), (U_atom Ex 45 _ E45) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0xec).
  { intros a (rg & Hin & Har). cbn [ss_mem add_cond ss_cont In] in Hin. destruct Hin as [<- | []]. cbn in Har. lia. }
  assert (MEQ2 : forall a, aview rsegs (w_H (e_W E)) (ms_mem ms0) a = aview rsegs (w_H (e_W E)) memc a).
  { intros a. rewrite <- (MEQ a). apply aview_eq_of. apply HFr. intros (rg & Hin & Har). cbn [ss_mem add_cond ss_cont In] in Hin.
    destruct Hin as [<- | []]. cbn in Har. lia. }
  clear HF HG HFr.
  es_envkeep HS Ex EWf.
  pose proof (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) _ _ _ regs _ ES_KEPT_C HS
    ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
  es_reg0 HS (23%bv : bv 5) R23'. es_reg0 HS (18%bv : bv 5) R18'. es_reg0 HS (19%bv : bv 5) R19'.
  es_reg0 HS (11%bv : bv 5) R11'.
  pmkst HS. es_pc_to 0xec.
  eapply (HLH lyc Sc Hpc (ms_regs ms0) (ms_mem ms0) _ k acc HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k (ms_regs ms0) (ms_mem ms0) _ (fun _ => False)
      HHEAD HP HB HJ); [intros a [] | intros a _ _; apply MEQ2 | | exact HPM].
    apply (es_regs_of regs (ms_regs ms0) ES_KEPT_C [23%bv] HKR); [|vm_compute; reflexivity].
    intros r [<- | []]. rewrite R23', (es_denot_shx _ 9 22 (e_q E + 8) SHADOW_OFF
      ltac:(first [exact E9 | rewrite EWf by lia; exact E9]) ltac:(first [exact E22 | rewrite EWf by lia; exact E22])) by (unfold SHADOW_OFF; lia).
    symmetry; exact R23.
  + pose proof HK as (K14 & K15 & K16 & K17 & K5).
    split; [rewrite HKR by (cbn; repeat (first [left; reflexivity | right])); exact K14|].
    split; [rewrite HKR by (cbn; repeat (first [left; reflexivity | right])); exact K15|].
    split; [rewrite HKR by (cbn; repeat (first [left; reflexivity | right])); exact K16|].
    split; [rewrite HKR by (cbn; repeat (first [left; reflexivity | right])); exact K17|].
    rewrite HKR by (cbn; repeat (first [left; reflexivity | right])); exact K5.
  + exact HEG.
  + exact Hc.
  + apply (es_garr8_kept (w_H (e_W E)) memc (ms_mem ms0)); [|exact GA]. intros a _. apply MEQ2.
  + rewrite R18', es_den0; try (rewrite EWf by lia). rewrite HEx, (es_xE_reg _ _ _ 10%bv 10) by reflexivity. exact R10.
  + rewrite R19', es_den0; try (rewrite EWf by lia). rewrite E20. reflexivity.
  + rewrite R11', es_den0; try (rewrite EWf by lia). rewrite E45. reflexivity.
Qed.
End c.

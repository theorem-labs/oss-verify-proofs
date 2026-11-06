(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 pin asan 1be0f53d96cb), ex_string's CONT cut (ExsA_Stmt.v
   CUT_CONT): A 0x84378 `lbu a0,0(s8)` (q + 8's shadow, report 0x844ac via 0x844a8), `ld s6,0(s2)` (in->end, reloaded),
   `mv s4,s5` (the new p), `bltu s5,s6` -> A 0x84110 (LH_AT at p), else `j 0x8442c` (CUT_FAIL: the text ends).
   ONE engine run from a fresh state: in->end in a read-only region at s2 = q + 8 (atom 45), s8 pinned to q + 8's
   shadow address in the form the engine's shadow token reads; q + 8's shadow entry from the real stack (es_stk_ra).
   PORTED from lib/B/Prog/ExsB_Cont.v (a Theorem Labs lane's B' walk), the same run and branch split. CHANGED for A': the pcs;
   B's CONT moved o / p into s2 / s3 and tested `bgeu`, A's moves only p (s5 -> s4) and tests `bltu`; in->end goes to
   s6, a register of ESB (B: a1, of LH_AT); q + 8 is in s2 (B: s1) and its shadow address in s8 (B: s7).
   Numerals: 0xdc, 0x344, 0x3f8 (DERIVED: cut offsets); 8 (LENGTH: in->end); atom 45 (DERIVED: in->end's value). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA ExsA_Stmt ExsA_Lib ExsA_Sym ExsA_Exit.
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

(* the CONT state: in->end (atom 45) through s2 = q + 8 (atom 18); s8 (24) is q + 8's shadow address *)
Definition ES_RE : YP09.region := YP09.mkRegion (Some 18%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 45 0))].
Definition es_q8shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 23 0).
Definition ss_cont : sstate :=
  mkSS (ES_PC + 0x344) (sr_set sr_atoms 24%bv es_q8shx) [ES_RE] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
              (21%nat, mkAF 4096 ES_CEIL 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (45%nat, mkAF 4096 ES_CEIL 0)]
      [] []).
Definition es_SHc : list shent := [mkSHE 18 0 8].
Definition ES_KEPT_C : list (bv 5) := [2; 3; 4; 8; 13; 14; 15; 16; 18; 19; 23; 25; 26; 27]%bv.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.

Lemma es_cut_cont : forall E p, LH_AT B ARx SK E p -> CUT_CONT B ARx SK E p.
Proof.
intros E p HLH. unfold CUT_CONT. intros lyc Sc Hpc regs memc mdc k acc HP HB HK HEG GA R19 R21.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & Ve & _).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC0 & HC8 & HC16 & HC24 & R2 & R8 & R18 & R22 &
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
assert (E18 : ew Ex 18 = Z_to_bv 64 (e_q E + 8)) by (rewrite HEx, (es_xE_reg _ _ _ 18%bv 18) by reflexivity; exact R18).
assert (E21 : ew Ex 21 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 21%bv 21) by reflexivity; exact R21).
assert (E23 : ew Ex 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite HEx, (es_xE_reg _ _ _ 23%bv 23) by reflexivity; exact R23).
assert (E45 : ew Ex 45 = Z_to_bv 64 (e_x0 E + es_len E)) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
assert (U2 : bv_unsigned (ew Ex 2) = es_sp E - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew Ex 18) = e_q E + 8) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew Ex 21) = p) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew Ex 23) = SHADOW_OFF) by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U45 : bv_unsigned (ew Ex 45) = e_x0 E + es_len E) by (rewrite E45; apply unsigned_lit_small; lia).
assert (HBx : U Ex (SOff 23 0) = SHADOW_OFF) by (rewrite (U_atom Ex 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia); reflexivity).
assert (HS : st_ok_pi rsegs VAL Ex ss_cont
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x344))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_cont. apply (pa_entry_st_ok_full (fx := fx) (L := A_prog_listing) (PI := PI_prog_A)).
  - apply regs_ok_pin; [rewrite HEx; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    unfold es_q8shx. rewrite (es_denot_shx Ex 18 23 (e_q E + 8) SHADOW_OFF E18 E23) by (unfold SHADOW_OFF; lia).
    exact R24.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, ES_RE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U18. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs Ex _ (e_q E + 8) 0 8 (SOff 45 0) (e_x0 E + es_len E));
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact VeC.
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U18, U21, U23, U45. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, ES_CEIL. repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 23 0) es_SHc Ex (rdW (e_W E) memc)).
{ unfold es_SHc. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 23 0) 18 (e_q E + 8) 8 (e_q E + 8) 0 8 HRAq HBx);
    [rewrite (U_atom Ex 18 (e_q E + 8) E18) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia. }
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
assert (HPM : es_P E memc) by exact HMN.
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_A)).
unfold cfg_at, w64. rewrite es_pc_eq.
paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ intros a (rg & Hin & Har). cbn [ss_mem ss_cont In] in Hin. destruct Hin as [<- | []]. cbn in Har. lia. }
assert (MEQ : forall a, aview rsegs (w_H (e_W E)) (ms_mem ms) a = aview rsegs (w_H (e_W E)) memc a).
{ intros a. apply aview_eq_of. apply HFr. intros (rg & Hin & Har). cbn [ss_mem ss_cont In] in Hin.
  destruct Hin as [<- | []]. cbn in Har. lia. }
clear HF HG HFr.
psrr_branch_tok RUN BR HS SHOK ES_SPAN.
- (* p < in->end: back to the loop head *)
  rewrite branch_ltu_U, (U_atom Ex 21 p E21), (U_atom Ex 45 _ E45) in Hc by lia.
  apply Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0xdc).
  { intros a (rg & Hin & Har). cbn [ss_mem add_cond ss_cont In] in Hin. destruct Hin as [<- | []]. cbn in Har. lia. }
  assert (MEQ2 : forall a, aview rsegs (w_H (e_W E)) (ms_mem ms0) a = aview rsegs (w_H (e_W E)) memc a).
  { intros a. rewrite <- (MEQ a). apply aview_eq_of. apply HFr. intros (rg & Hin & Har). cbn [ss_mem add_cond ss_cont In] in Hin.
    destruct Hin as [<- | []]. cbn in Har. lia. }
  clear HF HG HFr.
  es_envkeep HS Ex EWf.
  pose proof (regs_kept_of_st_ok_pi (L := A_prog_listing) (PI := PI_prog_A) _ _ _ regs _ ES_KEPT_C HS
    ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
  es_reg0 HS (24%bv : bv 5) R24'. es_reg0 HS (22%bv : bv 5) R22'. es_reg0 HS (20%bv : bv 5) R20'.
  pmkst HS. es_pc_to 0xdc.
  eapply (HLH lyc Sc Hpc (ms_regs ms0) (ms_mem ms0) _ k acc HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k (ms_regs ms0) (ms_mem ms0) _ (fun _ => False)
      HHEAD HP HB HJ); [intros a [] | intros a _ _; apply MEQ2 | | exact HPM].
    apply (es_regs_of regs (ms_regs ms0) ES_KEPT_C [22%bv; 24%bv] HKR); [|vm_compute; reflexivity].
    intros r [<- | [<- | []]].
    * rewrite R22', es_den0; try (rewrite EWf by lia). rewrite E45. symmetry; exact R22.
    * rewrite R24', (es_denot_shx _ 18 23 (e_q E + 8) SHADOW_OFF
        ltac:(first [exact E18 | rewrite EWf by lia; exact E18]) ltac:(first [exact E23 | rewrite EWf by lia; exact E23]))
        by (unfold SHADOW_OFF; lia).
      symmetry; exact R24.
  + pose proof HK as (K13 & K14 & K15 & K16).
    split; [rewrite HKR by (cbn; repeat (first [left; reflexivity | right])); exact K13|].
    split; [rewrite HKR by (cbn; repeat (first [left; reflexivity | right])); exact K14|].
    split; [rewrite HKR by (cbn; repeat (first [left; reflexivity | right])); exact K15|].
    rewrite HKR by (cbn; repeat (first [left; reflexivity | right])); exact K16.
  + exact HEG.
  + exact Hc.
  + apply (es_garr8_kept (w_H (e_W E)) memc (ms_mem ms0)); [|exact GA]. intros a _. apply MEQ2.
  + rewrite HKR by (cbn; repeat (first [left; reflexivity | right])). exact R19.
  + rewrite R20', es_den0; try (rewrite EWf by lia). rewrite E21. reflexivity.
- (* p >= in->end: return -1 *)
  rewrite branch_ltu_U, (U_atom Ex 21 p E21), (U_atom Ex 45 _ E45) in Hc by lia.
  apply Z.ltb_ge in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x3f8).
  { intros a (rg & Hin & Har). cbn [ss_mem add_cond ss_cont In] in Hin. destruct Hin as [<- | []]. cbn in Har. lia. }
  assert (MEQ2 : forall a, aview rsegs (w_H (e_W E)) (ms_mem ms0) a = aview rsegs (w_H (e_W E)) memc a).
  { intros a. rewrite <- (MEQ a). apply aview_eq_of. apply HFr. intros (rg & Hin & Har). cbn [ss_mem add_cond ss_cont In] in Hin.
    destruct Hin as [<- | []]. cbn in Har. lia. }
  clear HF HG HFr.
  es_envkeep HS Ex EWf.
  pose proof (regs_kept_of_st_ok_pi (L := A_prog_listing) (PI := PI_prog_A) _ _ _ regs _ ES_KEPT_C HS
    ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
  es_reg0 HS (24%bv : bv 5) R24'. es_reg0 HS (22%bv : bv 5) R22'.
  pmkst HS. es_pc_to 0x3f8.
  eapply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc (ms_regs ms0) (ms_mem ms0) _ k HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k (ms_regs ms0) (ms_mem ms0) _ (fun _ => False)
      HHEAD HP HB HJ); [intros a [] | intros a _ _; apply MEQ2 | | exact HPM].
    apply (es_regs_of regs (ms_regs ms0) ES_KEPT_C [22%bv; 24%bv] HKR); [|vm_compute; reflexivity].
    intros r [<- | [<- | []]].
    * rewrite R22', es_den0; try (rewrite EWf by lia). rewrite E45. symmetry; exact R22.
    * rewrite R24', (es_denot_shx _ 18 23 (e_q E + 8) SHADOW_OFF
        ltac:(first [exact E18 | rewrite EWf by lia; exact E18]) ltac:(first [exact E23 | rewrite EWf by lia; exact E23]))
        by (unfold SHADOW_OFF; lia).
      symmetry; exact R24.
  + rewrite HG3, (es_rest_end E p) by lia. reflexivity.
Qed.
End c.

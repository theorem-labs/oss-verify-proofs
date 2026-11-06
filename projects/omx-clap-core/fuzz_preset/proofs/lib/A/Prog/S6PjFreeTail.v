(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_free_seg_tail.v, with its module paths, module names and numbers changed; 688 of its 990 lines of code are new or changed and 603 lines of the source are left out. *)
(* fuzz_preset image A, slice S6 (WalkS6): pj_free's walk (lib/A/Prog/S6PjFree.v), the TAIL segments.
   rule 24: proves no function (kind: segment lemma of pj_free's walk).
   - pf_seg_EP (pfs_EP): from the epilogue cut (slot 80, AF_pf + 320) the twelve restores, sp += 96 and the ret, to
     the walk's post (fpostW .. pf_Q) from the cut invariant pf_EP.
   - pf_seg_LX (pfs_LX): from the cut after the loop (slot 57, AF_pf + 228) the frees of kids, keys and str
     (three `jal fuzz_free`, returning at 252 / 276 / 304) and the memset of v's 56 bytes (`jal checked_memset`,
     returning at 320 = the epilogue cut), then pf_seg_EP. HOW: four engine stretches (YC1fPx paj_run_tok_x_inv
     over YCbqG's ajournal_x), each seated by S6PjFree.v's pft_seat at v's registers and v's header; each call
     crosses by YCbqGcallW.v aj_call_xW_sp with PjFreeCommon's instrumented fuzz_free text, the memset by
     YGcallMxmn.v aj_intrin_at_xm_fr over the row AIM; what a call keeps is S6PjFreeKeep.v's (pfk_frame,
     pfk_vnode, pfk_acct_free / pfk_acct_null), and Pm rides every call by srr_inv_call (PCALL).
     Section hypotheses of pf_seg_LX beyond pf_seg_EP's: VISF (the kit's MARKED frame-hull fact), pal_pst_img /
     pal_pst_ro / pal_ret_free (image facts discharged at PI_prog_A), FREE and AIM (the callee texts), PCALL.
     Numerals: 96 / 88 .. 0 (LENGTH: the frame and its slots), 56 / 40 / 32 / 24 / 16 (LENGTH: struct pj and its
     fields), 16 (LENGTH: the instance's cf_head), 4096 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (LENGTH: the bands); every pc
     offset is DERIVED (the listing's slot differences times 4). No ADDRESS.
   THE RE-HIDING MOVE: fuzz_free can hide shadow again, so both segments conclude SRr' SEGS RZ_cf (YA0nH) and run over
   R := wle' SEGS RZ_cf: the _invR runners (YC1fPx), the calls by YCbqGcallW.aj_call_xW_spR, the memset by the engine's
   R form of aj_intrin_at_xm_fr, the frame's journal at wle' (pfl_inv, pf_EP), what a call keeps by S6PjFreeKeep.v's
   R forms (pfk_frameR, pfk_vnodeR), and the walk's post pf_FIN at fpostWR (wle' SEGS RZ_cf). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YCbqGcallW YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjStringCommon PjFreeCommon PjFreePure S6PjFree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S6PjFreeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S6PjFreeGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfHeadSh.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.



(* ---- the epilogue seat: the frame of the twelve saved words (atoms 32 .. 43, pf_saves1's order) ---- *)
Definition pf_frameE : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 96 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
     YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0));
     YP09.mkChunk 48 (CVal 8 (SOff 38 0)); YP09.mkChunk 56 (CVal 8 (SOff 39 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0));
     YP09.mkChunk 72 (CVal 8 (SOff 41 0)); YP09.mkChunk 80 (CVal 8 (SOff 42 0)); YP09.mkChunk 88 (CVal 8 (SOff 43 0))].
Definition pf_factsE : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_pfE : sstate := mkSS (AF_pf + PF_EP) sr_atoms [pf_frameE] None pf_factsE.
Definition PFE_Bx : sv := SOff 44 0.

(* ---- the tail's three call sites, as offsets from pj_free's entry (DERIVED: the listing's slot differences
   times 4; the disassembly's +0xfc, +0x114, +0x130) ---- *)
Definition PFL_R1 : Z := 252.   (* the return site of `jal fuzz_free` (kids) *)
Definition PFL_R2 : Z := 276.   (* the return site of `jal fuzz_free` (keys) *)
Definition PFL_R3 : Z := 304.   (* the return site of `jal fuzz_free` (str)  *)
(* pj_free's entry offset as a numeral (DERIVED: its slot times 4) *)
(* glue another loop segment can use *)
Lemma pfl_AF : AF_pf = 20228.
Proof. vm_compute. reflexivity. Qed.

Section lt. Context {rc : YM05.RunCeil}.
(* fpre's raZ bound at the tail's four return sites: CLOSED top-level slot lemmas over the ONE image-A listing
   instance (PRW_StepKit.pa_slot_lt_ceil_b at PL := PL_prog_A), never a vm_compute inside a big proof. The goal of
   each vm_compute is the boolean slot test of a CLOSED listing at a CLOSED key: no world, memory or PAImg in it. *)
Lemma pfl_ceil_1 : forall PAx : PAImg A_prog_listing,
  @pa_val _ A_prog_listing PAx A_TEXT + (AF_pf + PFL_R1) < YM05.alloc_ceiling.
Proof.
intros PAx. apply (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PAx) (AF_pf + PFL_R1));
  [rewrite pfl_AF; unfold PFL_R1; lia | vm_compute; reflexivity].
Qed.
Lemma pfl_ceil_2 : forall PAx : PAImg A_prog_listing,
  @pa_val _ A_prog_listing PAx A_TEXT + (AF_pf + PFL_R2) < YM05.alloc_ceiling.
Proof.
intros PAx. apply (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PAx) (AF_pf + PFL_R2));
  [rewrite pfl_AF; unfold PFL_R2; lia | vm_compute; reflexivity].
Qed.
Lemma pfl_ceil_3 : forall PAx : PAImg A_prog_listing,
  @pa_val _ A_prog_listing PAx A_TEXT + (AF_pf + PFL_R3) < YM05.alloc_ceiling.
Proof.
intros PAx. apply (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PAx) (AF_pf + PFL_R3));
  [rewrite pfl_AF; unfold PFL_R3; lia | vm_compute; reflexivity].
Qed.
(* fuzz_free's own stack budget is non-negative (a CLOSED numeral at prh_img_A) *)
End lt.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg A_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParams_preset.
(* the fixed re-hideable zone of the cf layer (YGcfRehidePost.v) at this section's run ceiling *)
#[local] Notation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* the epilogue's environment: the registers, then the twelve saved words *)
Definition pf_EE (regs r0 : bvmap 5 word) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (map (fun c => getr r0 (Z_to_bv 5 (Z.of_nat (snd c)))) pf_saves1)).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Variable CTX0 : list (list Z).
Variable PB : astate -> Prop.
Variable FX : pf_obs.
Local Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).


Theorem pf_seg_EP : pfs_EP SK B ARx Pm CTX0 PB FX.
Proof.
intros en ly S Hp W regs mem md k HPRE (HFR & HQ).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HFR as (HJ & HWIN & Hsp & HSV & HPRS & G3 & G4 & G27 & HROD & HPM).
pose proof HPRE as ([HFPRE0 _] & _).
pose proof HFPRE0 as (_ & Hra & _).
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
set (r0 := fe_regs en) in *.
set (E := pf_EE regs r0).
assert (EL : forall n, (n < A_TEXT)%nat ->
  ew E n = ew (Ereg regs (map (fun c => getr r0 (Z_to_bv 5 (Z.of_nat (snd c)))) pf_saves1)) n)
  by (intros n Hn; subst E; unfold pf_EE; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 12)%nat -> ew E (32 + j) =
  nth j (map (fun c => getr r0 (Z_to_bv 5 (Z.of_nat (snd c)))) pf_saves1) (Z_to_bv 64 0)).
{ intros j Hj. rewrite EL by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. reflexivity. }
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = fe_sp0 en - 96) by (rewrite E2; exact Hsp).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pf_EE; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E ss_pfE (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_pf + PF_EP))) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pfE. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, pf_frameE.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]]]]]]].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 0 8 (SOff 32 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 26)))));
        [cbn [sv_denot]; change (ew E 32) with (ew E (32 + 0)); rewrite (EX 0%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 0 26%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 8 8 (SOff 33 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 25)))));
        [cbn [sv_denot]; change (ew E 33) with (ew E (32 + 1)); rewrite (EX 1%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 8 25%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 16 8 (SOff 34 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 24)))));
        [cbn [sv_denot]; change (ew E 34) with (ew E (32 + 2)); rewrite (EX 2%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 16 24%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 24 8 (SOff 35 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 23)))));
        [cbn [sv_denot]; change (ew E 35) with (ew E (32 + 3)); rewrite (EX 3%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 24 23%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 32 8 (SOff 36 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 22)))));
        [cbn [sv_denot]; change (ew E 36) with (ew E (32 + 4)); rewrite (EX 4%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 32 22%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 40 8 (SOff 37 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 21)))));
        [cbn [sv_denot]; change (ew E 37) with (ew E (32 + 5)); rewrite (EX 5%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 40 21%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 48 8 (SOff 38 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 20)))));
        [cbn [sv_denot]; change (ew E 38) with (ew E (32 + 6)); rewrite (EX 6%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 48 20%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 56 8 (SOff 39 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 19)))));
        [cbn [sv_denot]; change (ew E 39) with (ew E (32 + 7)); rewrite (EX 7%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 56 19%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 64 8 (SOff 40 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 18)))));
        [cbn [sv_denot]; change (ew E 40) with (ew E (32 + 8)); rewrite (EX 8%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 64 18%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 72 8 (SOff 41 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 9)))));
        [cbn [sv_denot]; change (ew E 41) with (ew E (32 + 9)); rewrite (EX 9%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 72 9%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 80 8 (SOff 42 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 8)))));
        [cbn [sv_denot]; change (ew E 42) with (ew E (32 + 10)); rewrite (EX 10%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 80 8%nat ltac:(vm_compute; tauto))].
    + apply (chunk_ok_val SEGS E _ (fe_sp0 en - 96) 88 8 (SOff 43 0) (bv_unsigned (getr r0 (Z_to_bv 5 (Z.of_nat 1)))));
        [cbn [sv_denot]; change (ew E 43) with (ew E (32 + 11)); rewrite (EX 11%nat) by lia; unfold pf_saves1; cbn [nth map snd];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | apply bv_unsigned_in_range | lia
        | exact (HSV 88 1%nat ltac:(vm_compute; tauto))].
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    unfold pf_factsE. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. unfold fe_sp0 in *. lia. }
assert (SHOK : sh_ok SEGS PFE_Bx [] E (mrestrict (w_H W) mem)) by constructor.
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm (fe_mem en) -> Pm m)
  (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PA)).
unfold pf_cfg.
(* ---- slots 80-92: the twelve restores, sp += 96; the run stops at the ret ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1); [gs_awr0|].
(* the epilogue writes nothing *)
assert (M : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Ha). cbn [ss_pfE ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [pf_frameE YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
clear HF HFr HG.
rewrite M in HJ, HPM.
(* the ret keeps the world: its SRr step is lifted to SRr' *)
apply (SRr_SRr' SEGS RZ_cf).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
assert (HAE : env_agree 32 (Ereg regs (map (fun c => getr r0 (Z_to_bv 5 (Z.of_nat (snd c)))) pf_saves1)) E)
  by (split; [intros n Hn; subst E; unfold pf_EE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ [3%bv; 4%bv; 27%bv] HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
unfold pf_FIN, fpostWR.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?rr _ ?mm _) ?dd = _ /\ _ =>
  exists ly, S, Hp, rr, mm, dd end.
eexists.
split.
{ rewrite R1. cbn [sv_denot]. change (ew E 43) with (ew E (32 + 11)). rewrite (EX 11%nat) by lia.
  unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
  replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) by (apply bv_eq; reflexivity).
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [rewrite M; apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS RZ_cf)); exact HJ|].
split; [rewrite M; exact HWIN|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2.
    rewrite Usp. replace (fe_sp0 en - 96 + 96) with (fe_sp0 en) by lia. unfold fe_sp0, spZ. apply Z_to_bv_bv_unsigned.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (KR 3%bv) by (cbn; tauto). exact G3.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (KR 4%bv) by (cbn; tauto). exact G4.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (8%bv : bv 5) Rr8. rewrite Rr8. cbn [sv_denot]. change (ew E 42) with (ew E (32 + 10)). rewrite (EX 10%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (9%bv : bv 5) Rr9. rewrite Rr9. cbn [sv_denot]. change (ew E 41) with (ew E (32 + 9)). rewrite (EX 9%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
  - assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (18%bv : bv 5) Rr18. rewrite Rr18. cbn [sv_denot]. change (ew E 40) with (ew E (32 + 8)). rewrite (EX 8%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
    + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (19%bv : bv 5) Rr19. rewrite Rr19. cbn [sv_denot]. change (ew E 39) with (ew E (32 + 7)). rewrite (EX 7%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
    + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (20%bv : bv 5) Rr20. rewrite Rr20. cbn [sv_denot]. change (ew E 38) with (ew E (32 + 6)). rewrite (EX 6%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
    + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (21%bv : bv 5) Rr21. rewrite Rr21. cbn [sv_denot]. change (ew E 37) with (ew E (32 + 5)). rewrite (EX 5%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
    + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (22%bv : bv 5) Rr22. rewrite Rr22. cbn [sv_denot]. change (ew E 36) with (ew E (32 + 4)). rewrite (EX 4%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
    + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (23%bv : bv 5) Rr23. rewrite Rr23. cbn [sv_denot]. change (ew E 35) with (ew E (32 + 3)). rewrite (EX 3%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
    + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (24%bv : bv 5) Rr24. rewrite Rr24. cbn [sv_denot]. change (ew E 34) with (ew E (32 + 2)). rewrite (EX 2%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
    + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (25%bv : bv 5) Rr25. rewrite Rr25. cbn [sv_denot]. change (ew E 33) with (ew E (32 + 1)). rewrite (EX 1%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
    + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). prreg HS (26%bv : bv 5) Rr26. rewrite Rr26. cbn [sv_denot]. change (ew E 32) with (ew E (32 + 0)). rewrite (EX 0%nat) by lia.
      unfold pf_saves1. cbn [nth map snd]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
    + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (KR 27%bv) by (cbn; tauto). exact G27. }
rewrite M. exact HQ.
Qed.

(* ================================================================ the segment after the loop (pfs_LX) ========
   From the cut pf_LX (slot 57, AF_pf + 228): the ASan check of v + 24 (not taken) and `ld a0,24(s0)` to
   `jal fuzz_free` (kids, returns at 252); the same for v + 32 (keys, 276) and for v + 16 (str, 304); then
   `li a2,56; mv a0,s0; li a1,0; jal checked_memset` (the memset row AIM, returns at 320 = PF_EP), and the
   epilogue segment pf_seg_EP. fn_own nd = Dk ++ Dy ++ Ds is the order of the three frees. *)
(* ---- the Section hypotheses the segment takes: the same text as S6PjFreeEnt.v / S6PjFreeKeep.v ---- *)
(* a MARKED kit fact the instance discharges by ARx_frame_hull_vis_cf_ok, as image B's VISF *)
Hypothesis VISF : YGcfFsVis.ARx_frame_hull_vis SEGS B ARx.
(* image fact, discharged at PI_prog_A by S1ImgA.v pst_in_img_A: alloc.c's statics are image bytes *)
Hypothesis pal_pst_img : forall a, Exists (in_zr a) PST -> in_img SEGS a.
(* image fact, discharged at PI_prog_A by S1ImgA.v pst_not_ro_A: they are no read-only bytes *)
Hypothesis pal_pst_ro : forall a, Exists (in_zr a) PST ->
  ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.
(* image fact, discharged at PI_prog_A by vm_compute: the four `jal fuzz_free` return sites of pj_free *)
Hypothesis pal_ret_free : forall off, In off [200; PFL_R1; PFL_R2; PFL_R3] ->
  In (BASE + AF_pf + off) (@pi_ret_sites prh_img_A F_pj_free RT_fuzz_free).
(* the callee texts the segment cites: fuzz_free (PjFreeCommon's instrumented text) and the memset row *)
Hypothesis FREE : tfuzz_free_specO (PA := PA) B ARx SK PB FX.
Hypothesis AIM : aintrin_realizes_xm SEGS B ARx OSet (SIGMA AS___asan_memset).
(* the segment crosses three calls and the memset row, whose keeps are the memnorm one *)
Hypothesis PCALL : srr_inv_call SEGS Pm.

Ltac pfl_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ---- what holds at every cut of the tail: pf_LX with the blocks still to free as a parameter (the frame's journal at
   wle' SEGS RZ_cf, as pf_LX's: every cut of the tail but the first lies after a free) ---- *)
Definition pfl_inv (en : PfEnt) (nd : PfNode) (R : list (Z * Z))
  (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pf_frameR SK B ARx Pm (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_vregs en regs /\
  exists Fd Lam,
    pf_acct B FX en ly S Hp W mem Fd R Lam /\ pf_vnode B en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ R).

(* ---- the callee-saved registers the tail reads, across a call ---- *)
(* glue another loop segment can use *)
Lemma pfl_pres : forall (r r' : bvmap 5 word), aregs_preserved r r' ->
  getr r' 2 = getr r 2 /\ getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4 /\ getr r' 8 = getr r 8 /\
  getr r' 9 = getr r 9 /\ getr r' 18 = getr r 18 /\ getr r' 19 = getr r 19 /\ getr r' 20 = getr r 20 /\
  getr r' 21 = getr r 21 /\ getr r' 27 = getr r 27.
Proof.
intros r r' H.
assert (K : forall z (b : bv 5), acallee_saved z -> Z_to_bv 5 z = b -> getr r' b = getr r b)
  by (intros z b Hz <-; exact (H z Hz)).
repeat split.
- apply (K 2); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 3); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 4); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 8); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 9); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 18); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 19); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 20); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 21); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 27); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
Qed.

(* ---- a harness block of the ledger: its bounds (image B's pj_free_glue.v pfg_lam_blk over A's cf_head) ---- *)

(* ---- a byte of a live ledger block's allocator range that hits v's node: that block IS v's place ---- *)
(* glue another loop segment can use *)
Lemma pfl_apart : forall en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  pf_vnode B en nd ly S Lam W mem ->
  YM05.alloc_ceiling <= fe_sp0 en ->
  In (a, k) Lam -> a - 16 <= x < a - 16 + req_size (k + 16) -> fe_v en <= x < fe_v en + 56 ->
  ~ In (a, k) (fe_D en) /\ a <= fe_v en /\ fe_v en + 56 <= a + k.
Proof.
intros en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x HAR HLED HVN Hsp0 Hin Hx Hv.
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & _ & _ & _ & _ & _ & _ & _ & _ & Hplace).
destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HLED Hin)
  as (Hk0 & Ha0 & Hak & Ha16 & Hab & Hhp). change (@cf_head CP) with 16 in *.
pose proof (req_size_pos (k + 16) ltac:(lia)) as [Rk1 Rk2].
destruct Hplace as [(a' & k' & HaL & HaD & Hav & Hvk) | [(b & m & Hbm & HnL & Hbv & Hvm) |
  (cid & pos & Hcp & Hf1 & Hf2)]].
- destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W mem md Lam peak cnt fail ran most own a' k' HAR HLED HaL)
    as (Hk0' & Ha0' & Hak' & Ha16' & Hab' & _). change (@cf_head CP) with 16 in *.
  pose proof (req_size_pos (k' + 16) ltac:(lia)) as [Rk1' Rk2'].
  destruct (Z.eq_dec a a') as [Ea | Hnea]; [destruct (Z.eq_dec k k') as [Ek | Hnek]|].
  + subst a' k'. split; [exact HaD | split; lia].
  + exfalso.
    assert (Hne2 : (a - 16, k + 16) <> (a' - 16, k' + 16))
      by (intros Eq; injection Eq as E1 E2; apply Hnek; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab' Hne2) as HZ.
    unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
  + exfalso.
    assert (Hne2 : (a - 16, k + 16) <> (a' - 16, k' + 16))
      by (intros Eq; injection Eq as E1 E2; apply Hnea; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab' Hne2) as HZ.
    unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
- exfalso.
  assert (Hne2 : (a - 16, k + 16) <> (b, m)).
  { intros Eq. injection Eq as E1 E2. apply HnL.
    change (@cf_head CP) with 16 in *.
    replace (b + 16) with a by lia. replace (m - 16) with k by lia. exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hbm Hne2) as HZ.
  unfold zdisjoint in HZ. cbn [fst snd] in HZ.
  pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2]. lia.
- exfalso.
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) cid pos
    HAR Hab Hcp) as HZ.
  unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
Qed.

(* ---- v's 56 bytes are no image bytes ---- *)
(* glue another loop segment can use *)
Lemma pfl_vimg : forall en nd ly S Hp W mem md Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  pf_vnode B en nd ly S Lam W mem -> YM05.alloc_ceiling <= fe_sp0 en ->
  forall x, fe_v en <= x < fe_v en + 56 -> ~ in_img SEGS x.
Proof.
intros en nd ly S Hp W mem md Lam peak cnt fail ran most own HAR HLED HVN HCEIL x Hx.
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & _ & _ & _ & _ & _ & _ & _ & _ & Hplace).
destruct Hplace as [(a & k & HaL & _ & Hav & Hvk) | [(b & m & Hbm & _ & Hbv & Hvm) |
  (cid & pos & Hcp & Hf1 & Hf2)]].
- destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HLED HaL)
    as (Hk0 & Ha0 & Hak & Ha16 & Hab & _). change (@cf_head CP) with 16 in *.
  pose proof (req_size_pos (k + 16) ltac:(lia)) as [Rk1 Rk2].
  apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) x HAR Hab). lia.
- pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2].
  apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m x HAR Hbm). lia.
- apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos x HAR Hcp). lia.
Qed.

(* ---- a byte array of zeros from the bytes a view shows ---- *)
(* glue another loop segment can use *)
Lemma pfl_val1_of_aview : forall H m a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv kk Hk. assert (Ek : kk = 0%nat) by lia. subst kk.
replace (a + Z.of_nat 0) with a by lia.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb.
rewrite YI04.le_byte_small by (cbn in Rb |- *; lia). cbn [Z.of_nat].
rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* glue another loop segment can use *)
Lemma pfl_garr8_of_aview : forall H m p l, Forall (fun x => 0 <= x < 256) l ->
  (forall j, (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 SEGS (mrestrict H m) p l.
Proof.
intros H m p l Hl Hv j Hj. split.
- apply pfl_val1_of_aview. exact (Hv j Hj).
- apply (proj1 (Forall_forall _ _) Hl). apply nth_In. exact Hj.
Qed.

(* ---- the pc0-filtered trace of an empty chain ---- *)
(* glue another loop segment can use *)
Lemma pfl_trace : forall pc0 r, prh_trace pc0 r [] = pc0 :: (if r =? pc0 then [] else [r]).
Proof.
intros pc0 r. unfold prh_trace. cbn [flat_map app]. rewrite app_nil_r.
destruct (r =? pc0); reflexivity.
Qed.

(* ---- the registers a stretch does not write: the same symbolic value before and after ---- *)
(* glue another loop segment can use *)
Lemma pfl_kept : forall (H : word -> bool) E ss0 ms0 ss1 ms1 (l : list (bv 5)),
  st_ok_pi SEGS VAL E ss0 (restrict H ms0) -> st_ok SEGS E ss1 (restrict H ms1) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss1) r) (sr_get (ss_regs ss0) r)) l = true ->
  forall r, In r l -> getr (ms_regs ms1) r = getr (ms_regs ms0) r.
Proof.
intros H E ss0 ms0 ss1 ms1 l HS0 HS1 Hl r Hr.
rewrite (st_ok_restrict_reg SEGS H E ss1 ms1 r HS1).
rewrite (st_ok_pi_restrict_reg H E ss0 ms0 r HS0).
rewrite forallb_forall in Hl. rewrite (sv_eqb_eq _ _ (Hl r Hr)). reflexivity.
Qed.

(* ---- THE SEATED STATE of a tail stretch at any pc after the loop ---- *)
(* glue another loop segment can use *)
Lemma pfl_seat : forall en nd ly S Hp W regs mem md k Lam pc,
  pf_pre B ARx CTX0 PB FX en ->
  pf_frameR SK B ARx Pm (wle' SEGS RZ_cf) en ly S Hp W regs mem md k -> pf_vregs en regs ->
  pf_vnode B en nd ly S Lam W mem ->
  st_ok_pi SEGS VAL (PFT_E regs nd) (ss_pft (AF_pf + pc))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_pf + pc))) mem (seg_rom SEGS))) /\
  sh_ok SEGS PFT_Bx PFT_SH (PFT_E regs nd) (mrestrict (w_H W) mem).
Proof.
intros en nd ly S Hp W regs mem md k Lam pc HPRE HFR HVR HVN.
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
pose proof HFR as (_ & _ & Hsp & _).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & _ & _ & Hra & _ & _).
apply (pft_seat en nd W regs mem (AF_pf + pc) HVR).
- rewrite Hsp. unfold fe_sp0 in *. lia.
- rewrite Hsp. unfold fe_sp0 in *. lia.
- lia.
- exact Hv8.
- exact Hstr.
- exact Hkids.
- exact Hkeys.
- exact Hnn.
- exact Hra.
- exact Hamr.
Qed.

(* ---- the cut rides through a stretch that stores nothing ---- *)
Lemma pfl_inv_stretch : forall en nd R ly S Hp W regs mem md k regs' mem' md' k',
  pfl_inv en nd R ly S Hp W regs mem md k -> mem' = mem ->
  ajournal_xR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp W mem' md' k' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
  getr regs' 27 = getr regs 27 ->
  pfl_inv en nd R ly S Hp W regs' mem' md' k'.
Proof.
intros en nd R ly S Hp W regs mem md k regs' mem' md' k' HI -> HJ' K2 K3 K4 K8 K9 K18 K19 K20 K21 K27.
pose proof HI as ((HJ & HWIN & Hsp & HSAV & HPRES & H3 & H4 & H27 & HROD & HMN) & HVR & Fd & Lam & HAC & HVN & HPD).
split.
{ split; [exact HJ'|]. split; [exact HWIN|].
  split; [unfold spZ; rewrite K2; exact Hsp|].
  split; [exact HSAV|]. split; [exact HPRES|].
  split; [rewrite K3; exact H3|]. split; [rewrite K4; exact H4|].
  split; [rewrite K27; exact H27|]. split; [exact HROD | exact HMN]. }
split; [unfold pf_vregs; rewrite K8, K9, K18, K19, K20, K21; exact HVR|].
exists Fd, Lam. split; [exact HAC | split; [exact HVN | exact HPD]].
Qed.

(* ---- ONE `jal fuzz_free` of the tail: the next block of the order goes, the cut moves to the return site ---- *)
Lemma pfl_call : forall en nd R blk p ret E ss ms ly S Hp W mdc k Q,
  pf_pre B ARx CTX0 PB FX en -> List.NoDup (fe_D en) ->
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_fuzz_free ->
  pfl_inv en nd (blk ++ R) ly S Hp W (ms_regs ms) (ms_mem ms) mdc k ->
  (p = 0 /\ blk = [] \/ exists kk, blk = [(p, kk)] /\ In (p, kk) (fe_Lam en)) ->
  getr (ms_regs ms) 10 = w64 p ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_pf + ret)) ->
  In (BASE + (AF_pf + ret)) (@pi_ret_sites prh_img_A F_pj_free RT_fuzz_free) ->
  BASE + (AF_pf + ret) < YM05.alloc_ceiling ->
  0 <= AF_pf + ret < 2 ^ 40 -> (AF_pf + ret) mod 2 = 0 -> 4096 <= AF_pf + ret ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     pfl_inv en nd R ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (pf_cfg ret regs2 mem2 md2) Q) ->
  SRr' SEGS RZ_cf W (mkCfg ms mdc) Q.
Proof.
intros en nd R blk p ret E ss ms ly S Hp W mdc k Q HPRE HND HS Hrv Hpc HI HBLK Ha0 Hra HRET HRC
  Hret40 Hret2 Hret4096 KONT.
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
pose proof pfa_stk_ff as FS0.
pose proof HPRE as (HFPRE & HUNIV & _ & _ & HFWIN & _ & HSAFE & _).
pose proof HFPRE as (HAFN & HROD0 & HSTKHI & HRAZ0 & HFRM0).
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk00 & Hpres0 & Hch0 & HQT0).
pose proof Hstk00 as (Hal16 & Hstk0' & Hceil' & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HI as (HFR & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ & HWINk & Hsp & HSAV & HPRES & H3 & H4 & H27 & HRODk & HMNk).
pose proof HVR as (R8 & R9 & R18 & R19 & R20 & R21).
pose proof HAC as (HROOM & HLED & HPL & HPB & EF & HRE).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
assert (Hvne : fe_v en <> 0) by (clear - Hv4096; lia).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & HB4).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HCEIL : YM05.alloc_ceiling <= fe_sp0 en) by lia.
assert (HRAU : bv_unsigned (Z_to_bv 64 (BASE + (AF_pf + ret))) = BASE + (AF_pf + ret))
  by (apply unsigned_lit_small; lia).
(* the block the call frees, and its ledger entry *)
assert (HEX : exists n, (p = 0 \/ In (p, n) Lam) /\
   ((p = 0 /\ blk = []) \/ (p <> 0 /\ blk = [(p, n)] /\ In (p, n) Lam))).
{ destruct HBLK as [(Hp0 & Eb) | (kk & Eb & Hin)].
  - exists 0. split; [left; exact Hp0 | left; split; [exact Hp0 | exact Eb]].
  - assert (HinL : In (p, kk) Lam).
    { apply (Permutation_in _ HPL) in Hin. apply in_app_or in Hin as [HinF | HinL]; [|exact HinL].
      exfalso. rewrite Eb in HPD. cbn [app] in HPD.
      pose proof (Permutation_NoDup HPD HND) as HN2.
      exact (NoDup_remove_2 _ _ _ HN2 (in_or_app _ _ _ (or_introl HinF))). }
    destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W (ms_mem ms) mdc Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en)
      (fe_most en) (fe_own en) p kk HAR HLED HinL) as (Hk0 & Hp4096 & Hpceil & Hp16 & Hab & Hhp).
    change (@cf_head CP) with 16 in *.
    exists kk. split; [right; exact HinL | right; split; [lia | split; [exact Eb | exact HinL]]]. }
destruct HEX as (n & HPN & HCASE2).
assert (HFP1 : forall x, inFP (if p =? 0 then @nil (Z * Z) else ablocks_fp [(p - 16, n + 16)]) x ->
   p <> 0 /\ p - 16 <= x < p - 16 + req_size (n + 16)).
{ intros x. destruct (Z.eqb_spec p 0) as [Hp0 | Hne]; intros Hx.
  - exfalso. exact (inFP_nil x Hx).
  - split; [exact Hne|].
    destruct (inFP_ablocks_fp_inv _ _ Hx) as (q & m & [Hq | []] & Hr).
    injection Hq as -> ->. exact Hr. }
assert (HBAB : p <> 0 -> In (p, n) Lam /\ In (p - 16, n + 16) (ablocks B ly S) /\
   4096 + 16 <= p /\ p - 16 + req_size (n + 16) <= YM05.alloc_ceiling).
{ intros Hne. destruct HCASE2 as [(Hp0 & _) | (_ & _ & HinL)]; [exfalso; exact (Hne Hp0)|].
  destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W (ms_mem ms) mdc Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en)
    (fe_most en) (fe_own en) p n HAR HLED HinL) as (Hk0 & Hp4096 & Hpceil & Hp16 & Hab & Hhp).
  change (@cf_head CP) with 16 in *.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W (ms_mem ms) mdc _ _ HAR Hab) as (_ & _ & Hclim & _).
  split; [exact HinL | split; [exact Hab | split; [exact Hp4096 | exact Hclim]]]. }
assert (HSINK : ~ YI16.sink_open_fp (if p =? 0 then @nil (Z * Z) else ablocks_fp [(p - 16, n + 16)])).
{ destruct (Z.eqb_spec p 0) as [Hp0 | Hne].
  - apply sink_closed_pos. apply Forall_nil.
  - destruct (HBAB Hne) as (_ & _ & Hp4096 & _).
    apply sink_closed_ablocks_fp. constructor; [cbn [fst]; lia | apply Forall_nil]. }
assert (HTR : In (call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms) []) (as_universe B)).
{ assert (HRAZ : raZ (ms_regs ms) = BASE + (AF_pf + ret))
    by (unfold raZ; rewrite Hra; exact HRAU).
  apply call_trace_in.
  - exact (proj1 HUNIV RT_fuzz_free).
  - rewrite call_trace_nil, HRAZ, <- pfl_trace.
    change (pc_free_ra0 (as_code B)) with (prh_pc0 B RT_fuzz_free).
    exact (prh_univ_closure_lit B CTX0 F_pj_free RT_fuzz_free _ HUNIV HRET). }
eapply (SRr'_bind SEGS RZ_cf).
{ eapply (aj_call_xW_spR (fx := fx) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ A_prog_listing PA)
    (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W E ss ms
    (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp mdc k
    (STK_fuzz_free (PI := prh_img_A)) 0 (if p =? 0 then @nil (Z * Z) else ablocks_fp [(p - 16, n + 16)])
    (-96 - fe_d en) (Z_to_bv 64 (BASE + (AF_pf + ret))) [] _ HS Hrv HJ).
  - rewrite Hsp. lia.
  - lia.
  - lia.
  - exact FS0.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite H3. exact Hgp0.
  - rewrite H4. exact Htp0.
  - exact Hra.
  - apply (ret_ok_codeptr_v (PI := PA)); [exact Hret40 | exact Hret2].
  - rewrite HRAU. lia.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1 HWIN1.
    assert (HFPRE1 : fpre (PA := PA) B ARx (STK_fuzz_free (PI := prh_img_A)) ly S Hp W (ms_regs ms) (ms_mem ms) mdc []).
    { split; [exact HPRE1|]. split; [exact HRODk|]. split.
      - rewrite Hsp, Eshi. unfold fe_sp0 in *. lia.
      - split; [unfold raZ; rewrite Hra, HRAU; exact HRC | exact HFRM0]. }
    assert (HPBS : PB S)
      by exact (pf_safe_here FX PB _ ly S (pf_safe_after FX PB _ _ _ _ _ _ (HSAFE Hvne) HRE)).
    eapply (SRrG_mono SEGS (wle' SEGS RZ_cf)).
    { rewrite Hpc.
      exact (FREE (fe_most en) (fe_own en) ly S Hp W (ms_regs ms) (ms_mem ms) mdc [] p n Lam
        (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en)
        HFPRE1 HROOM HPBS HTR Ha0 HPN HLED). }
    cbv beta. intros W' c' _ HQ. apply fpostW_x_of_apostR. exact HQ.
  - intros x Hx. destruct (HFP1 x Hx) as (Hne & Hr). destruct (HBAB Hne) as (HinL & Hab & _).
    assert (HinD : In (p, n) (fe_D en)).
    { destruct HCASE2 as [(Hp0 & _) | (_ & Eb & _)]; [exfalso; exact (Hne Hp0)|].
      apply (Permutation_in _ (Permutation_sym HPD)). rewrite Eb. apply in_or_app. right.
      left. reflexivity. }
    left. unfold fe_FP.
    replace (fe_v en =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (inFP_ablocks_fp (prhPj_hbl (fe_D en)) (p - 16) (n + 16) (x - (p - 16))
      ltac:(unfold prhPj_hbl; apply in_map_iff; exists (p, n); split;
            [change (@cf_head CP) with 16; reflexivity | exact HinD])
      ltac:(lia)) as (r0 & Hr1 & Hr2).
    exists r0. split; [right; exact Hr1|].
    replace (p - 16 + (x - (p - 16))) with x in Hr2 by lia. exact Hr2. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HXc & HP2 & HK).
unfold fQmn in HK. cbv beta in HK. destruct HK as ((HFX & HROOM2 & HARM) & HMNc).
replace (STK_fuzz_free (PI := prh_img_A) + 0) with (STK_fuzz_free (PI := prh_img_A)) in HJc by lia.
replace (fe_sp0 en + fe_d en + (-96 - fe_d en) + 0) with (fe_sp0 en - 96) in HJc by lia.
pose proof (pfl_pres _ _ HP2) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P27).
assert (HPM2 : Pm (ms_mem ms) -> Pm mem2) by (intros h; exact (PCALL _ _ HMNc h)).
pose proof (pfk_frameR SK B ARx pal_pst_ro Pm CTX0 PB FX (wle' SEGS RZ_cf) en ly S Hp W (ms_regs ms) (ms_mem ms) mdc k
  (STK_fuzz_free (PI := prh_img_A)) (if p =? 0 then @nil (Z * Z) else ablocks_fp [(p - 16, n + 16)])
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE HFR HJc HJ2 HSINK
  ltac:(unfold spZ; rewrite P2; reflexivity) P3 P4 P27 HPM2) as HFR2.
apply (KONT ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1)).
split; [exact HFR2|].
split; [unfold pf_vregs; rewrite P8, P9, P18, P19, P20, P21; exact HVR|].
destruct HCASE2 as [(Hp0 & Eb) | (Hne & Eb & HinL)].
- subst p blk. cbn [app] in HAC, HPD.
  destruct HARM as [(_ & EHp & Eab & HLED2) | (Hne & _)]; [|exfalso; exact (Hne eq_refl)].
  exists Fd, Lam. split; [|split].
  + exact (pfk_acct_null B FX en ly S Hp W (ms_mem ms) Fd R Lam ly2 S2 Hp2 W2 mem2 HAC HFX HROOM2 Eab HLED2).
  + eapply (pfk_vnodeR SK B ARx LAWS VISF (wle' SEGS RZ_cf) en nd ly S Hp W (ms_mem ms) mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam
      (STK_fuzz_free (PI := prh_img_A)) (fe_sp0 en - 96) _ k1
      (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
      (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en));
    [ exact HVN | exact HAR | exact HLED | exact HJc | exact HLED2 | | | | | ].
    * intros x Hx. exfalso. exact (inFP_nil x Hx).
    * intros b Hin Hnin. exfalso. apply Hnin. rewrite Eab. exact Hin.
    * intros a kk Hin _. exact Hin.
    * intros a kk Hin. exact Hin.
    * intros x Hx. exfalso. exact (inFP_nil x Hx).
  + exact HPD.
- subst blk. cbn [app] in HAC, HPD.
  destruct HARM as [(Hp0 & _) | (_ & EHp & (b1 & b2 & Eb1 & Eb2) & l1 & l2 & ELam & HLED2)];
    [exfalso; exact (Hne Hp0)|].
  replace (p =? 0) with false in HFX by (symmetry; apply Z.eqb_neq; exact Hne).
  assert (HinD : In (p, n) (fe_D en)).
  { apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. left. reflexivity. }
  destruct (HBAB Hne) as (_ & Hab & Hp4096 & Hclim).
  change (@cf_head CP) with 16 in Eb1, Eb2.
  exists (Fd ++ [(p, n)]), (l1 ++ l2). split; [|split].
  + apply (pfk_acct_free B FX en ly S Hp W (ms_mem ms) Fd (p, n) R Lam ly2 S2 Hp2 W2 mem2 l1 l2
      HAC HFX HROOM2 ELam (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2))) HLED2).
  + eapply (pfk_vnodeR SK B ARx LAWS VISF (wle' SEGS RZ_cf) en nd ly S Hp W (ms_mem ms) mdc Lam ly2 S2 Hp2 W2 mem2 md2 (l1 ++ l2)
      (STK_fuzz_free (PI := prh_img_A)) (fe_sp0 en - 96) _ k1
      (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
      (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en));
    [ exact HVN | exact HAR | exact HLED | exact HJc | exact HLED2 | | | | | ].
    * intros x Hx Hvx. destruct (HFP1 x Hx) as (_ & Hr).
      destruct (pfl_apart en nd ly S Hp W (ms_mem ms) mdc Lam (fe_peak en) (fe_cnt en) (fe_fail en)
        (fe_ran en) (fe_most en) (fe_own en) p n x HAR HLED HVN HCEIL HinL Hr Hvx) as (HnD & _).
      exact (HnD HinD).
    * intros b Hin Hnin. exists p, n. split; [exact HinD | split; [exact HinL|]].
      rewrite Eb1 in Hin. rewrite Eb2 in Hnin.
      apply in_app_or in Hin as [G1 | [G2 | G3]].
      -- exfalso. apply Hnin. apply in_or_app. left. exact G1.
      -- change (@cf_head CP) with 16. symmetry. exact G2.
      -- exfalso. apply Hnin. apply in_or_app. right. exact G3.
    * intros a kk Hin Hnin. rewrite ELam in Hin. apply in_app_or in Hin as [G1 | [G2 | G3]].
      -- apply in_or_app. left. exact G1.
      -- exfalso. apply Hnin. rewrite <- G2. exact HinD.
      -- apply in_or_app. right. exact G3.
    * intros a kk Hin. rewrite ELam. apply in_app_or in Hin as [G1 | G1]; apply in_or_app;
        [left; exact G1 | right; right; exact G1].
    * intros x Hx. destruct (HFP1 x Hx) as (_ & Hr). exists (p - 16), (n + 16).
      split; [exact Hab | exact Hr].
  + rewrite <- app_assoc. cbn [app]. exact HPD.
Qed.

(* ================================================================ the three frees ============================ *)
(* slot 57 .. the `jal fuzz_free` of v->kids: the shadow check of v + 24 (not taken), `ld a0,24(s0)` *)
Lemma pfl_S1 : forall en nd R ly S Hp W regs mem md k Q,
  pf_pre B ARx CTX0 PB FX en -> pf_node en nd ->
  pfl_inv en nd (fn_Dk nd ++ R) ly S Hp W regs mem md k ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2, pfl_inv en nd R ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (pf_cfg PFL_R1 regs2 mem2 md2) Q) ->
  SRr' SEGS RZ_cf W (pf_cfg PF_LX regs mem md) Q.
Proof.
intros en nd R ly S Hp W regs mem md k Q HPRE HNODE HI KONT.
pose proof HI as (HFR & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HMNk).
pose proof HNODE as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
destruct (pfl_seat en nd ly S Hp W regs mem md k Lam PF_LX HPRE HFR HVR HVN) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (PFT_E regs nd)) by (unfold PFT_E; apply Eimg_env).
pose proof HS as HS0.
assert (HPM : Pm (fe_mem en) -> Pm mem) by exact HMNk.
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS
  (fun m => Pm (fe_mem en) -> Pm m) (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf)
  (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
unfold pf_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM PF_Bspan; [gs_awr0|].
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  cbn [ss_pft ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [pft_vhdr YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
clear HF HFr HG.
pose proof (pfl_kept (w_H W) (PFT_E regs nd) (ss_pft (AF_pf + PF_LX)) _ _ _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 27%bv] HS0 HS
  ltac:(cbn [ss_regs setpc ss_pft]; vm_compute; reflexivity)) as RK.
cbn [ms_regs mkst] in RK.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (E33 : ew (PFT_E regs nd) 33 = w64 (fn_kids nd)).
{ unfold PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (QR : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_pf + PFL_R1)))
  by (rewrite Q1; f_equal; rewrite pfl_AF; unfold PFL_R1; lia).
assert (HNDL : List.NoDup (fe_D en))
  by (first [exact HNDD | apply NoDup_ListNoDup; exact HNDD]).
apply (pfl_call en nd R (fn_Dk nd) (fn_kids nd) PFL_R1 _ _ ms ly S Hp W _ k Q HPRE HNDL HS).
- reflexivity.
- reflexivity.
- apply (pfl_inv_stretch en nd (fn_Dk nd ++ R) ly S Hp W regs mem md k
    (ms_regs ms) (ms_mem ms) _ _ HI MM HJ
    (RK 2%bv ltac:(pfl_in)) (RK 3%bv ltac:(pfl_in)) (RK 4%bv ltac:(pfl_in))
    (RK 8%bv ltac:(pfl_in)) (RK 9%bv ltac:(pfl_in)) (RK 18%bv ltac:(pfl_in))
    (RK 19%bv ltac:(pfl_in)) (RK 20%bv ltac:(pfl_in)) (RK 21%bv ltac:(pfl_in))
    (RK 27%bv ltac:(pfl_in))).
- destruct HKIDSn as [(H1 & _ & H2) | (kk & Hlin & _ & Heq)];
  [left; split; [exact H1 | exact H2] | right; exists kk; split; [exact Heq | exact Hlin]].
- rewrite Q10, E33. reflexivity.
- exact QR.
- rewrite Z.add_assoc. apply pal_ret_free. pfl_in.
- exact (pfl_ceil_1 PA).
- rewrite pfl_AF; unfold PFL_R1; lia.
- rewrite pfl_AF; unfold PFL_R1; reflexivity.
- rewrite pfl_AF; unfold PFL_R1; lia.
- exact KONT.
Qed.

(* the `jal fuzz_free` of v->keys: the shadow check of v + 32 (not taken), `ld a0,32(s0)` *)
Lemma pfl_S2 : forall en nd R ly S Hp W regs mem md k Q,
  pf_pre B ARx CTX0 PB FX en -> pf_node en nd ->
  pfl_inv en nd (fn_Dy nd ++ R) ly S Hp W regs mem md k ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2, pfl_inv en nd R ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (pf_cfg PFL_R2 regs2 mem2 md2) Q) ->
  SRr' SEGS RZ_cf W (pf_cfg PFL_R1 regs mem md) Q.
Proof.
intros en nd R ly S Hp W regs mem md k Q HPRE HNODE HI KONT.
pose proof HI as (HFR & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HMNk).
pose proof HNODE as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
destruct (pfl_seat en nd ly S Hp W regs mem md k Lam PFL_R1 HPRE HFR HVR HVN) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (PFT_E regs nd)) by (unfold PFT_E; apply Eimg_env).
pose proof HS as HS0.
assert (HPM : Pm (fe_mem en) -> Pm mem) by exact HMNk.
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS
  (fun m => Pm (fe_mem en) -> Pm m) (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf)
  (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
unfold pf_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM PF_Bspan; [gs_awr0|].
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  cbn [ss_pft ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [pft_vhdr YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
clear HF HFr HG.
pose proof (pfl_kept (w_H W) (PFT_E regs nd) (ss_pft (AF_pf + PFL_R1)) _ _ _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 27%bv] HS0 HS
  ltac:(cbn [ss_regs setpc ss_pft]; vm_compute; reflexivity)) as RK.
cbn [ms_regs mkst] in RK.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (E34 : ew (PFT_E regs nd) 34 = w64 (fn_keys nd)).
{ unfold PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (QR : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_pf + PFL_R2)))
  by (rewrite Q1; f_equal; rewrite pfl_AF; unfold PFL_R2; lia).
assert (HNDL : List.NoDup (fe_D en))
  by (first [exact HNDD | apply NoDup_ListNoDup; exact HNDD]).
apply (pfl_call en nd R (fn_Dy nd) (fn_keys nd) PFL_R2 _ _ ms ly S Hp W _ k Q HPRE HNDL HS).
- reflexivity.
- reflexivity.
- apply (pfl_inv_stretch en nd (fn_Dy nd ++ R) ly S Hp W regs mem md k
    (ms_regs ms) (ms_mem ms) _ _ HI MM HJ
    (RK 2%bv ltac:(pfl_in)) (RK 3%bv ltac:(pfl_in)) (RK 4%bv ltac:(pfl_in))
    (RK 8%bv ltac:(pfl_in)) (RK 9%bv ltac:(pfl_in)) (RK 18%bv ltac:(pfl_in))
    (RK 19%bv ltac:(pfl_in)) (RK 20%bv ltac:(pfl_in)) (RK 21%bv ltac:(pfl_in))
    (RK 27%bv ltac:(pfl_in))).
- destruct HKEYSn as [(H1 & _ & H2) | (_ & kk & Hlin & _ & Heq)];
  [left; split; [exact H1 | exact H2] | right; exists kk; split; [exact Heq | exact Hlin]].
- rewrite Q10, E34. reflexivity.
- exact QR.
- rewrite Z.add_assoc. apply pal_ret_free. pfl_in.
- exact (pfl_ceil_2 PA).
- rewrite pfl_AF; unfold PFL_R2; lia.
- rewrite pfl_AF; unfold PFL_R2; reflexivity.
- rewrite pfl_AF; unfold PFL_R2; lia.
- exact KONT.
Qed.

(* the `jal fuzz_free` of v->str: `addi a0,s0,16`, the shadow check (not taken), `ld a0,16(s0)` *)
Lemma pfl_S3 : forall en nd R ly S Hp W regs mem md k Q,
  pf_pre B ARx CTX0 PB FX en -> pf_node en nd ->
  pfl_inv en nd (fn_Ds nd ++ R) ly S Hp W regs mem md k ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2, pfl_inv en nd R ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (pf_cfg PFL_R3 regs2 mem2 md2) Q) ->
  SRr' SEGS RZ_cf W (pf_cfg PFL_R2 regs mem md) Q.
Proof.
intros en nd R ly S Hp W regs mem md k Q HPRE HNODE HI KONT.
pose proof HI as (HFR & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HMNk).
pose proof HNODE as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
destruct (pfl_seat en nd ly S Hp W regs mem md k Lam PFL_R2 HPRE HFR HVR HVN) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (PFT_E regs nd)) by (unfold PFT_E; apply Eimg_env).
pose proof HS as HS0.
assert (HPM : Pm (fe_mem en) -> Pm mem) by exact HMNk.
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS
  (fun m => Pm (fe_mem en) -> Pm m) (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf)
  (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
unfold pf_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM PF_Bspan; [gs_awr0|].
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  cbn [ss_pft ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [pft_vhdr YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
clear HF HFr HG.
pose proof (pfl_kept (w_H W) (PFT_E regs nd) (ss_pft (AF_pf + PFL_R2)) _ _ _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 27%bv] HS0 HS
  ltac:(cbn [ss_regs setpc ss_pft]; vm_compute; reflexivity)) as RK.
cbn [ms_regs mkst] in RK.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (E32 : ew (PFT_E regs nd) 32 = w64 (fn_str nd)).
{ unfold PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (QR : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_pf + PFL_R3)))
  by (rewrite Q1; f_equal; rewrite pfl_AF; unfold PFL_R3; lia).
assert (HNDL : List.NoDup (fe_D en))
  by (first [exact HNDD | apply NoDup_ListNoDup; exact HNDD]).
apply (pfl_call en nd R (fn_Ds nd) (fn_str nd) PFL_R3 _ _ ms ly S Hp W _ k Q HPRE HNDL HS).
- reflexivity.
- reflexivity.
- apply (pfl_inv_stretch en nd (fn_Ds nd ++ R) ly S Hp W regs mem md k
    (ms_regs ms) (ms_mem ms) _ _ HI MM HJ
    (RK 2%bv ltac:(pfl_in)) (RK 3%bv ltac:(pfl_in)) (RK 4%bv ltac:(pfl_in))
    (RK 8%bv ltac:(pfl_in)) (RK 9%bv ltac:(pfl_in)) (RK 18%bv ltac:(pfl_in))
    (RK 19%bv ltac:(pfl_in)) (RK 20%bv ltac:(pfl_in)) (RK 21%bv ltac:(pfl_in))
    (RK 27%bv ltac:(pfl_in))).
- destruct HSTRn as [(H1 & H2) | (kk & Hlin & Heq)];
  [left; split; [exact H1 | exact H2] | right; exists kk; split; [exact Heq | exact Hlin]].
- rewrite Q10, E32. reflexivity.
- exact QR.
- rewrite Z.add_assoc. apply pal_ret_free. pfl_in.
- exact (pfl_ceil_3 PA).
- rewrite pfl_AF; unfold PFL_R3; lia.
- rewrite pfl_AF; unfold PFL_R3; reflexivity.
- rewrite pfl_AF; unfold PFL_R3; lia.
- exact KONT.
Qed.

(* ================================================================ the memset and the cut pf_EP ================ *)
Lemma pfl_S4 : forall en nd ly S Hp W regs mem md k,
  pf_pre B ARx CTX0 PB FX en -> pf_node en nd ->
  pfl_inv en nd [] ly S Hp W regs mem md k ->
  SRr' SEGS RZ_cf W (pf_cfg PFL_R3 regs mem md) (pf_FIN SK B ARx Pm FX en).
Proof.
intros en nd ly S Hp W regs mem md k HPRE HNODE HI.
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
pose proof HI as (HFR & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ0 & HWINk & Hsp & HSAV & HPRES & H3 & H4 & H27 & HRODk & HMNk).
pose proof HVR as (R8 & R9 & R18 & R19 & R20 & R21).
pose proof HAC as (HROOM & HLED & HPL & HPB & EF & HRE).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
pose proof HPRE as (HFPRE & HUNIV & _ & _ & HFWIN & _ & HSAFE & _).
pose proof HFPRE as (HAFN & HROD0 & HSTKHI & HRAZ0 & _).
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk00 & Hpres0 & Hch0 & HQT0).
pose proof Hstk00 as (Hal16 & Hstk0' & Hceil' & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof (ajxR_ar HJ0) as HAR. pose proof (ajxR_ly HJ0) as Hly. pose proof (ajxR_secs HJ0) as Hsecs.
pose proof (ajxR_rel HJ0) as Hwle. pose proof (ajxR_io HJ0) as Hios. pose proof (ajxR_frs HJ0) as Hfrs.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & HB4).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
assert (Esp0 : fe_sp0 en = spZ (fe_regs en)) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HCEIL : YM05.alloc_ceiling <= fe_sp0 en) by lia.
cbn [app] in Hfrs.
assert (HFPv : forall a, fe_v en <= a < fe_v en + 56 -> inFP (fe_FP en) a).
{ intros a Ha. unfold fe_FP. replace (fe_v en =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  exists (fe_v en, fe_v en + 56). split; [left; reflexivity | cbn [fst snd]; lia]. }
destruct (pfl_seat en nd ly S Hp W regs mem md k Lam PFL_R3 HPRE HFR HVR HVN) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (PFT_E regs nd)) by (unfold PFT_E; apply Eimg_env).
pose proof HS as HS0.
assert (HPM : Pm (fe_mem en) -> Pm mem) by exact HMNk.
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS
  (fun m => Pm (fe_mem en) -> Pm m) (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf)
  (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
unfold pf_cfg.
paj_run_tok_x_inv RUN HS HJ0 SHOK HPM PF_Bspan; [gs_awr0|].
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  cbn [ss_pft ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [pft_vhdr YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
clear HF HFr HG.
pose proof (pfl_kept (w_H W) (PFT_E regs nd) (ss_pft (AF_pf + PFL_R3)) _ _ _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 27%bv] HS0 HS
  ltac:(cbn [ss_regs setpc ss_pft]; vm_compute; reflexivity)) as RK.
cbn [ms_regs mkst] in RK.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (E8 : ew (PFT_E regs nd) 8 = w64 (fe_v en)).
{ unfold PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl). exact R8. }
assert (QR : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_pf + PF_EP)))
  by (rewrite Q1; f_equal; rewrite pfl_AF; unfold PF_EP; lia).
assert (Q10' : getr (ms_regs ms) 10 = w64 (fe_v en)) by (rewrite Q10; exact E8).
assert (Q11' : getr (ms_regs ms) 11 = w64 0) by (rewrite Q11; apply bv_eq; vm_compute; reflexivity).
assert (Q12' : getr (ms_regs ms) 12 = w64 56) by (rewrite Q12; apply bv_eq; vm_compute; reflexivity).
assert (HSP2 : spZ (ms_regs ms) = fe_sp0 en - 96)
  by (unfold spZ; rewrite (RK 2%bv ltac:(pfl_in)); exact Hsp).
pmkst HS.
(* the memset keeps the world: the engine's R form of the _fr rule (YGcallMxmn.aj_intrin_at_xm_frR, the frame's journal
   at wle') is an SRr step, lifted to SRr' *)
eapply (SRr'_bind SEGS RZ_cf).
{ apply (SRr_SRr' SEGS RZ_cf).
  eapply (aj_intrin_at_xm_frR (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf)
    (wle'_trans SEGS RZ_cf) OSet (SIGMA AS___asan_memset)
    AIM W (ms_regs ms) (ms_mem ms) (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp _ k
    (fe_v en) 0 56 (-96 - fe_d en) _ HJ0).
  - exact Q10'.
  - exact Q11'.
  - exact Q12'.
  - lia.
  - lia.
  - lia.
  - rewrite HSP2. lia.
  - lia.
  - lia.
  - lia.
  - rewrite (RK 3%bv ltac:(pfl_in)), H3. exact Hgp0.
  - rewrite (RK 4%bv ltac:(pfl_in)), H4. exact Htp0.
  - exact QR.
  - apply (ret_ok_codeptr_v (PI := PA));
      [rewrite pfl_AF; unfold PF_EP; lia | rewrite pfl_AF; unfold PF_EP; reflexivity].
  - intros a Ha. split.
    + destruct Hplace as [(a' & k' & HaL & _ & Hav & Hvk) | [(b & m & Hbm & _ & Hbv & Hvm) |
        (cid & pos & Hcp & Hf1 & Hf2)]].
      * left. right. left. split; [exact (HFPv a Ha)|].
        destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W mem md Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en)
          (fe_most en) (fe_own en) a' k' HAR HLED HaL) as (Hk0 & Ha0' & Hak & Ha16 & Hab & Hhp).
        change (@cf_head CP) with 16 in *.
        pose proof (req_size_pos (k' + 16) ltac:(lia)) as [Rk1 Rk2].
        exists (a' - 16), (k' + 16). split; [exact Hab | lia].
      * left. right. left. split; [exact (HFPv a Ha)|].
        pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2].
        exists b, m. split; [exact Hbm | lia].
      * right. split; [exact (HFPv a Ha)|].
        exists cid, pos. split; [rewrite Hfrs in Hcp; exact Hcp|].
        unfold in_zr, frame_rng. cbn [fst snd]. lia.
    + lia.
  - exact Hamr.
  - rewrite MM. exact Hvra.
  - intros _. rewrite MM. exact Hvhull.
  - exact I. }
cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & Hmn4).
replace (fe_sp0 en + fe_d en + (-96 - fe_d en)) with (fe_sp0 en - 96) in Hfr4 by lia.
pose proof (pfl_pres _ _ HP4) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P27).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (fe_v en <= a < fe_v en + 56) ->
   ~ (fe_sp0 en - 96 - ESTACK <= a < fe_sp0 en - 96) ->
   aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. rewrite <- MM. exact (Hfr4 a Ha H1 H2). }
apply (pf_seg_EP en ly S Hp W regs4 mem4 md4 k HPRE).
split.
{ split; [exact HJ4|].
  split.
  { intros a Ha Hn. rewrite KEEP; [exact (HWINk a Ha Hn) | lia | lia | lia]. }
  split; [unfold spZ; rewrite P2; exact HSP2|].
  split.
  { intros o r Hro. pose proof (pfk_saved_rng o r Hro) as Ho.
    apply (pjs1_val_keep W W mem mem4 (fe_sp0 en - 96 + o) 8 _ (HSAV o r Hro)).
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP; lia. }
  split.
  { intros a Ha. apply Hpres4. rewrite MM. exact (HPRES a Ha). }
  split; [rewrite P3, (RK 3%bv ltac:(pfl_in)); exact H3|].
  split; [rewrite P4, (RK 4%bv ltac:(pfl_in)); exact H4|].
  split; [rewrite P27, (RK 27%bv ltac:(pfl_in)); exact H27|].
  split.
  { intros a Hro Hno Herr.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(sg & Hin & _ & Hr) | Hr];
      [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
    pose proof (Hsegs a Hi) as Hlo.
    rewrite KEEP;
    [ exact (HRODk a Hro Hno Herr)
    | unfold kLowMemEnd in Hlo; lia
    | intros Hvx; exact (pfl_vimg en nd ly S Hp W mem md Lam (fe_peak en) (fe_cnt en) (fe_fail en)
        (fe_ran en) (fe_most en) (fe_own en) HAR HLED HVN HCEIL a Hvx Hi)
    | unfold kLowMemEnd in Hlo; unfold YM05.alloc_ceiling in *; lia ]. }
  intros H0. exact (PCALL _ _ Hmn4 (HPM H0)). }
split.
{ split; [|exact HRE].
  split; [exact HROOM|].
  rewrite app_nil_r in HPD.
  exists Lam. split.
  { eapply Permutation_trans; [exact HPL|]. apply Permutation_app_tail.
    apply Permutation_sym. exact HPD. }
  split.
  { eapply Permutation_trans; [exact HPB|]. apply Permutation_app_tail.
    unfold prhPj_hbl. apply Permutation_map. apply Permutation_sym. exact HPD. }
  split.
  { apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem4 Lam
      (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) HLED).
    - intros a Ha. pose proof (pal_pst_img a Ha) as Hi. pose proof (Hsegs a Hi) as Hlo.
      apply KEEP;
      [ unfold kLowMemEnd in Hlo; lia
      | intros Hvx; exact (pfl_vimg en nd ly S Hp W mem md Lam (fe_peak en) (fe_cnt en) (fe_fail en)
          (fe_ran en) (fe_most en) (fe_own en) HAR HLED HVN HCEIL a Hvx Hi)
      | unfold kLowMemEnd in Hlo; unfold YM05.alloc_ceiling in *; lia ].
    - intros a kk i Hin Hi. change (@cf_head CP) with 16.
      destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W mem md Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en)
        (fe_most en) (fe_own en) a kk HAR HLED Hin) as (Hk0 & Ha0 & Hak & Ha16 & Hab & Hhp).
      change (@cf_head CP) with 16 in *.
      pose proof (req_size_pos (kk + 16) ltac:(lia)) as [Rk1 Rk2].
      assert (Hrng : a - 16 <= a - 16 + i < a - 16 + req_size (kk + 16)) by lia.
      apply KEEP.
      + lia.
      + intros Hvx.
        destruct (pfl_apart en nd ly S Hp W mem md Lam (fe_peak en) (fe_cnt en) (fe_fail en)
          (fe_ran en) (fe_most en) (fe_own en) a kk (a - 16 + i) HAR HLED HVN HCEIL Hin Hrng Hvx) as (_ & Hav & _).
        lia.
      + lia.
    - intros a kk Hin Hab. exact Hab.
    - apply Permutation_refl. }
  split; [intros H0; exfalso; lia|].
  intros _. unfold pj_zeroR. apply pfl_garr8_of_aview.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
  - intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat.
    assert (Hj56 : 0 <= Z.of_nat j < 56) by lia.
    rewrite (Heff (Z.of_nat j) Hj56). reflexivity. }
intros H0. exact (PCALL _ _ Hmn4 (HPM H0)).
Qed.

(* ================================================================ THE SEGMENT ================================= *)
Theorem pf_seg_LX : pfs_LX SK B ARx Pm CTX0 PB FX.
Proof.
intros en nd ly S Hp W regs mem md k HPRE HNODE Hv0 HLX.
apply (pfl_S1 en nd (fn_Dy nd ++ fn_Ds nd) ly S Hp W regs mem md k _ HPRE HNODE HLX).
intros ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HI1.
apply (pfl_S2 en nd (fn_Ds nd) ly1 S1 Hp1 W1 regs1 mem1 md1 k1 _ HPRE HNODE HI1).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HI2.
assert (HI2' : pfl_inv en nd (fn_Ds nd ++ []) ly2 S2 Hp2 W2 regs2 mem2 md2 k2)
  by (rewrite app_nil_r; exact HI2).
apply (pfl_S3 en nd [] ly2 S2 Hp2 W2 regs2 mem2 md2 k2 _ HPRE HNODE HI2').
intros ly3 S3 Hp3 W3 regs3 mem3 md3 k3 HI3.
exact (pfl_S4 en nd ly3 S3 Hp3 W3 regs3 mem3 md3 k3 HPRE HNODE HI3).
Qed.
End f.
End d.

Print Assumptions pf_seg_EP.
Print Assumptions pf_seg_LX.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1292 of its 1364 lines of code are new or changed and 442 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_E2.v, with its numbers changed; 452 of its 950 lines of code are new or changed and 866 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c): segment CA4 of the re-walk of check_no_overread
   (cno): the THIRD PADDED COPY, CN_COPY3 (+532) to CN_INIT (+608) or, on the third NULL, CN_INIT3 (+792).
   FREE-PIECES-102 Part 7 row R7-3.
   rule 24: proves no function (kind: segment lemma).
   THE CODE (DERIVED offsets from cno's entry):
     +532 .. +540  s9 = s11 + 32 (d1); s5 = s11 + 128 (d2); s10 = s11 + 224 (d3)
     +544 .. +548  a0 = s3 (size + 16); jal __wrap_malloc
     +552 .. +560  s6 = a0 (r3); sd s5, 48(s1); sd s9, 56(s1); +564 beqz a0 -> +792 (CN_INIT3, the third NULL)
     +568 .. +588  s3 = s10; beqz s4 (size = 0) -> +592; a0 = s6, a1 = s7 (data), a2 = s4; jal __asan_memcpy
     +592 .. +604  a0 = s6 + s4; a2 = 16; a1 = 0; jal __asan_memset; returns to +608 (CN_INIT)
   THE RELATION and the SECTION HYPOTHESES are Cno102A_E2.v's (CA2): ARx := ARcfx; IMG, PAL, HW, IMGSH, AMALLOC, ACPY,
   ASET. The kit lemmas are Cno102A_E2.v's e2_* and Cno102A_E3.v's e3_*, applied here to this section's parameters.
   Numerals: offsets (DERIVED); 16 (LENGTH: the pad); 0 (the pad's fill byte); 32 / 128 / 224 (OFFSET: d1 / d2 / d3 in
   the frame at s11); 48 / 56 (OFFSET: the d2 / d1 slots of the frame at s1); register numbers (WORD). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YImgTop YG00cf YG01cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcallx YGcallcf YGcallSx YGcallMx YGcallMxmn FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveSec PresetLiveBounds PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Cno102A_Base Cno102A_Ro
  Cno102A_E Cno102A_E0 Cno102A_E2 Cno102A_E3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section e4. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_room_live_a8.
#[local] Existing Instance prh_room_malloc_a8.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instance PL_cno_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable CTX0 : list (list Z).
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Hypothesis IMG : cn_img B.
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
Hypothesis HW : prh_head_wide.
Hypothesis IMGSH : forall ly S Hp W mem md a, ARcf SEGS B ly S Hp W mem md -> pa_lo <= a < pa_hi ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the keep form, as in Cno102A_E2.v *)
Hypothesis AMALLOC : forall fz : YK11.FPState, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fz) SEGS B.
Hypothesis ACPY : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARcfx OCpy (SIGMA AS___asan_memcpy).
Hypothesis ASET : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARcfx OSet (SIGMA AS___asan_memset).
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs SEGS B.
Let XSL := ARx_xs_law_xs SEGS B.
(* Cno102A_E2.v's kit at this section's parameters *)
#[local] Notation e2_chain := (@Cno102A_E2.e2_chain fx rc ci SK PA B CTX0).
#[local] Notation e2_univ := (@Cno102A_E2.e2_univ rc ci PA B CTX0).
#[local] Notation e2_counts_at := (@Cno102A_E2.e2_counts_at fx rc ci PA B CTX0).
#[local] Notation e2_hp_apart := (@Cno102A_E2.e2_hp_apart rc PA B).
#[local] Notation e2_src_shadow := (@Cno102A_E2.e2_src_shadow rc ci PA B IMGSH).
#[local] Notation e2_own_pst := (@Cno102A_E2.e2_own_pst rc ci PA B IMG).
#[local] Notation e2_own_wr := (@Cno102A_E2.e2_own_wr rc ci PA B IMG).
#[local] Notation e2_ledger_own := (@Cno102A_E2.e2_ledger_own rc ci PA B IMG).
#[local] Notation e2_hs_add := (@Cno102A_E2.e2_hs_add rc PA).
#[local] Notation e2_blocks_in := (@Cno102A_E2.e2_blocks_in rc ci SK PA B).
#[local] Notation e2_src_kept := (@Cno102A_E2.e2_src_kept rc ci SK PA B IMG).
#[local] Notation e2_ledger_blk := (@Cno102A_E2.e2_ledger_blk rc ci PA B IMG HW).
#[local] Notation e2_garr8_some := (@Cno102A_E2.e2_garr8_some rc PA).
#[local] Notation e2_mbyte_of_aview2 := (@Cno102A_E2.e2_mbyte_of_aview2 rc PA).
#[local] Notation e3_copy_keep := (@Cno102A_E3.e3_copy_keep rc ci PA B IMGSH).
#[local] Notation e3_cevsl2 := (@Cno102A_E3.e3_cevsl2 rc PA).

(* +552 is cno's third __wrap_malloc return site *)
Lemma e4_site : In (cn_pc 552) (pi_ret_sites F_check_no_overread RT_malloc).
Proof. unfold cn_pc. rewrite (cni_base B IMG). vm_compute. tauto. Qed.

(* the three copies' blocks and events are the first two's then the third's *)
Lemma e4_cblks : forall D r1 r2 r3, cn_cblks D r1 r2 r3 = flat_map (cn_cblk D) [r1; r2] ++ cn_cblk D r3.
Proof. intros D r1 r2 r3. unfold cn_cblks. cbn [flat_map]. rewrite app_nil_r, app_assoc. reflexivity. Qed.
Lemma e4_cevs : forall D r1 r2 r3, cn_cevs D r1 r2 r3 = cn_cevsl D [r1; r2] ++ cn_cevsl D [r3].
Proof. intros D r1 r2 r3. unfold cn_cevs, cn_cevsl. rewrite e4_cblks. cbn [flat_map]. rewrite !app_nil_r, !map_app. reflexivity. Qed.
Lemma e4_cblk0 : forall D, cn_cblk D 0 = [].
Proof. intros D. reflexivity. Qed.

(* ======== CA4 ======== *)
Theorem cn_CA4 : @cn_seg_CA4 fx rc ci CfParams_preset prh_room_live_a8 SK PA B ARcfx CTX0.
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k r1 r2 own HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & HE).
(* the entry cut's LAST conjunct (the hull stages): the stage budget, kept apart so HE is cn_early as before *)
destruct HE as [HE HHULL].
pose proof (cn_pre_fpre B ARcfx CTX0 D HPRE) as HFPRE. pose proof (cn_pre_mn B ARcfx CTX0 D HPRE) as HMN.
pose proof (cn_pre_univ B ARcfx CTX0 D HPRE) as HUNIV. pose proof (cn_pre_ctx B ARcfx CTX0 D HPRE) as HCTX.
pose proof (cn_pre_r10 B ARcfx CTX0 D HPRE) as Ha0. pose proof (cn_pre_r11 B ARcfx CTX0 D HPRE) as Ha1.
pose proof (cn_pre_size B ARcfx CTX0 D HPRE) as Hsz. pose proof (cn_pre_src B ARcfx CTX0 D HPRE) as HSRC.
pose proof (cn_pre_home B ARcfx CTX0 D HPRE) as HHOME. pose proof (cn_pre_ledger B ARcfx CTX0 D HPRE) as HLED.
pose proof (cn_pre_cnt B ARcfx CTX0 D HPRE) as HCNT. pose proof (cn_pre_ran B ARcfx CTX0 D HPRE) as HRAN.
pose proof (cn_pre_most B ARcfx CTX0 D HPRE) as HRQ. pose proof (cn_pre_live B ARcfx CTX0 D HPRE) as HLIVE.
pose proof (cn_pre_max16 B ARcfx CTX0 D HPRE) as HMAX1. pose proof (cn_pre_maxpj B ARcfx CTX0 D HPRE) as HMAX2.
pose proof (cn_pre_frames B ARcfx CTX0 D HPRE) as HFRS. pose proof (cn_pre_room B ARcfx CTX0 D HPRE) as HROOM.
pose proof (cn_pre_frm0 B ARcfx CTX0 D HPRE) as HFRM. pose proof (cn_pre_wild B ARcfx CTX0 D HPRE) as HWILD.
pose proof (cn_pre_pksec B ARcfx CTX0 D HPRE) as HPKS. pose proof (cn_pre_pk24 B ARcfx CTX0 D HPRE) as HPK24.
destruct (cn_entry_facts B ARcfx CTX0 D HPRE)
  as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & Hgp0 & Htp0 & Hra40 & Hch0 & HAR0).
pose proof (e5_S1 D Hal16) as [HS1mod HS1b].
pose proof cn_stk_val as HSTK.
pose proof HB as (Hfz & Hfk & HJ & HFR & HSV & G3 & G4 & HROD).
pose proof HFR as (Hfrs & Hnin & Hflag & Hfpr & Hshp).
pose proof HJ as HJ'. apply e_J0 in HJ'.
pose proof (ajx_ar HJ') as HAR. pose proof (ajx_ly HJ') as Hly. pose proof (ajx_pres HJ') as Hpres.
pose proof (ajx_qt HJ') as HQT.
pose proof HE as HEc.
destruct HEc as (HHp & HLG & HCP & HPERM & HROOMc & HRP & HBUD & HOWN01 & Hown & HOWN0 & HCD).
assert (RG : forall r v, In (r, v) (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, r1);
  (23%bv, ci_data D)]) -> getr regs r = w64 v)
  by (intros r v Hin'; exact (proj1 (Forall_forall _ _) HR (r, v) Hin')).
pose proof (cni_base B IMG) as HBASE. pose proof cn_off_val as HOFF.
pose proof alloc_ceiling_val as [AC _]. pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsz0 : 0 <= cn_size D) by (unfold cn_size; lia).
pose proof (proj1 (Forall_forall _ _) HCP r1 (or_introl eq_refl)) as HCP1.
pose proof (proj1 (Forall_forall _ _) HCP r2 (or_intror (or_introl eq_refl))) as HCP2.
pose proof (e5_geo_of_base B ARcfx LAWS D fxk ly S Hp W regs mem md k HB) as [G HARc].
pose proof G as (EFa & Fa0 & Fa1 & Fa32 & Fapp & S16g & Hacg & Hkbg & Hlog & H47g).
(* +532 addi s9, s11, 32; +536 addi s5, s11, 128; +540 addi s10, s11, 224; +544 mv a0, s3; +548 jal __wrap_malloc *)
apply (cn_hs_addi W fxk regs mem md _ 532 536 25%bv 27%bv 32); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X1.
apply (cn_hs_addi W fxk _ mem _ _ 536 540 21%bv 27%bv 128); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X2.
apply (cn_hs_addi W fxk _ mem _ _ 540 544 26%bv 27%bv 224); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X3.
apply (cn_hs_addi W fxk _ mem _ _ 544 548 10%bv 19%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X4.
apply (cn_hs_call W fxk _ mem _ _ 548 552 AS___wrap_malloc); [vm_compute; reflexivity | lia | reflexivity |].
intros X5.
lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg _ ?mo) _ => set (regsT := rg); set (mdT := mo) end.
assert (RT : forall r v, In (r, v) (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, r1);
  (23%bv, ci_data D)]) -> r <> 1%bv -> r <> 10%bv -> r <> 21%bv -> r <> 25%bv -> r <> 26%bv -> getr regsT r = w64 v).
{ intros r v Hin' H1 H10 H21 H25 H26. unfold regsT. rewrite !getr_other by (intros E; subst; contradiction).
  exact (RG r v Hin'). }
assert (HF27 : getr regs 27%bv = w64 (cn_F D)) by (apply RG; ro_in).
assert (T10 : getr regsT 10%bv = w64 (cn_size D + 16)).
{ unfold regsT. ro_getr. rewrite (RG 19%bv (cn_size D + 16) ltac:(ro_in)).
  rewrite e2_addi by (unfold cn_size in *; lia). f_equal. lia. }
assert (T25 : getr regsT 25%bv = w64 (cn_d1 D)).
{ unfold regsT. ro_getr. rewrite HF27, e2_addi by lia. reflexivity. }
assert (T21 : getr regsT 21%bv = w64 (cn_d2 D)).
{ unfold regsT. ro_getr. rewrite HF27, e2_addi by lia. reflexivity. }
assert (T26 : getr regsT 26%bv = w64 (cn_d3 D)).
{ unfold regsT. ro_getr. rewrite HF27, e2_addi by lia. reflexivity. }
assert (T2 : getr regsT 2%bv = w64 (cn_S1 D))
  by (apply RT; [ro_in | discriminate | discriminate | discriminate | discriminate | discriminate]).
assert (T8 : getr regsT 8%bv = w64 (cn_sp0 D))
  by (apply RT; [ro_in | discriminate | discriminate | discriminate | discriminate | discriminate]).
assert (T1 : getr regsT 1%bv = w64 (cn_pc 552)) by (unfold regsT; ro_getr; reflexivity).
assert (T3 : getr regsT 3%bv = getr (ci_regs D) 3%bv) by (unfold regsT; ro_getr; exact G3).
assert (T4 : getr regsT 4%bv = getr (ci_regs D) 4%bv) by (unfold regsT; ro_getr; exact G4).
assert (HSPT : spZ regsT = cn_S1 D) by (unfold spZ; rewrite T2; unfold w64; apply unsigned_lit_small; unfold cn_sp0 in *; lia).
assert (Hpc552 : 4096 <= cn_pc 552 < 2 ^ 40).
{ unfold cn_pc. rewrite HBASE, HOFF. unfold A_prog_base. lia. }
assert (HRAT : raZ regsT = cn_pc 552) by (unfold raZ; rewrite T1; unfold w64; apply unsigned_lit_small; lia).
(* the journal at the call *)
pose proof (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ')))))
  as HJT.
(* the chain and the universe *)
destruct (e2_chain D fxk ly S Hp W regs mem md k HPRE HB) as (ch1 & Hach & Hsp1).
assert (HCH : chain_pre ly (aview SEGS (w_H W) mem) regsT ch1).
{ apply (achain_chain_pre ly _ (cn_S1 D) (cn_sp0 D) ch1 regsT Hach).
  - rewrite HSPT. unfold cn_sp0 in *. rewrite HSTK in *. lia.
  - unfold s0Z. rewrite T8. unfold w64. apply unsigned_lit_small. unfold cn_sp0 in *. lia.
  - rewrite HRAT. lia. }
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch1) (as_universe B))
  by exact (e2_univ D regsT ch1 RT_malloc (cn_pc 552) HUNIV HCTX e4_site HRAT Hsp1).
(* the malloc's trace is a FIXED one of the universe (P'' set: the call rule asks `admits`, YG01.admits_fix, and its
   post carries the trace in the journal's wild budget, which ajournal_xw_fix1 drops again) *)
assert (HTRc : In (call_trace ly (pc_malloc_ra0 (as_code B)) regsT ch1) (as_universe B)).
{ apply YCbq.call_trace_in; [exact (proj1 HUNIV RT_malloc) | exact HTR]. }
pose proof (alloc_model_laws_x_cf B (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HAR))) as AMX.
pose proof (Cno102A_E2.e2_live_pj_nonneg (ci_x D)) as HLP.
unfold cn_cfg. rewrite (pal_malloc B PAL). unfold w64 at 1.
eapply SRr_bind.
{ eapply (YGcallMxmnKeep.aj_malloc_at_x_m_keep (fx := fxk) (SK := SK) SEGS B prh_pst ARcfx QM_cf (QMm_cf SEGS B) malloc_cf cf_malloc_max
    free_cf (Wf_cf (as_universe B)) xs_cf LAWS (@pa_segs_low _ _ PA) (pal_env B PAL) OWNLOW WFL AMX (QMQ_cf SEGS B) XSL
    (YGcallMxmnKeep.amalloc_realizes_x_xs_keep (fx := fxk) SEGS B (AMALLOC fxk))
    W regsT mem STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly S Hp mdT k (cn_size D + 16) (cn_S1 D - cn_sp0 D) (w64 (cn_pc 552)) ch1).
  - exact HJT.
  - exact T10.
  - unfold cn_size in *. lia.
  - cbn [length] in HBUD. unfold cn_size in *. lia.
  - rewrite HSPT. lia.
  - exact HS1mod.
  - lia.
  - unfold ASTACK. rewrite HSTK. lia.
  - rewrite T3. exact Hgp0.
  - rewrite T4. exact Htp0.
  - exact T1.
  - unfold cn_pc. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; rewrite HOFF; [lia | reflexivity].
  - apply (QMm_cf_of_room SEGS B _ _ _ _ _ _ (proj1 HAR) HQT (YGcfRoomLive.room_live_room _ HROOMc));
      [ (* the hull admission at the call: the copies cut's stage budget *)
        exact (PresetHullPay.hull_ok_of_budget _ _ HHULL)
      | (* arodata_ok_cf at the call memory: cn_img's relro facts through the bridge (3c dropped memnorm) *)
        destruct (cni_relro_eq B IMG) as [EL EH];
        exact (YGcfAroBridge.arodata_ok_cf_of_P SEGS B W mem (cni_relro_seg B IMG) (cni_errno_relro B IMG)
          (cni_relro_top B IMG) (cni_ro_reads_nw B IMG) ltac:(rewrite EL, EH; exact HROD)) ].
  - exact HCH.
  - exact (admits_fix _ _ _ (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HAR)) HTR). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPR2 & Hres & Hfrs2 & HPREc & Htrc
  & (p & trc & Hpath & Hgf & Hleaf & Hpn & Hpa) & HARMS & HMNK).
(* the hull: the call uses one padded copy's malloc (PresetHullBudget.hull_used_of_call, any return value), and the
   cpy2 stage's budget pays it to copies' (cn_hpay_copy) *)
pose proof (PresetHullBudget.hull_used_of_call _ _ _ _ (YGcfSecsStep.secs_malloc_step _ _ _ _ _ Hpath)) as HUSED.
pose proof HHULL as HH1. rewrite cn_hrest_copies_split in HH1.
destruct (cn_hpay_copy _ _ _ HH1) as [_ HNEXT].
assert (HHULL2 : PresetHullBudget.hull_budget S2 (cn_hrest_copies (ci_x D))) by (apply HNEXT; exact HUSED).
(* the journal after the call: the fixed trace leaves the budget (YCbqG.v ajournal_xw_fix1) *)
pose proof (ajournal_xw_fix1 HTRc HJ2) as HJ2f. clear HJ2. rename HJ2f into HJ2.
assert (HPM2 : P mem2) by exact (PCALL _ _ HMNK HPM).
pose proof (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) as HPREcf.
destruct (e2_counts_at D ly S Hp W mem [r1; r2] own HPRE HE
  ltac:(unfold cn_cblk; cbn [flat_map]; destruct (r1 =? 0), (r2 =? 0); cbn; lia)) as (CSEC & C24).
assert (HROOM2 : room_live_cf S2)
  by exact (@RM_malloc _ _ prh_room_malloc_a8 fxk rc ci SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ (p, S2) HPREcf CSEC C24 HROOMc Hpath).
(* the registers after the call *)
assert (VP : forall r v, In (r, v) (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, r1);
  (23%bv, ci_data D)]) -> r <> 21%bv -> acallee_saved (bv_unsigned r) -> getr regs2 r = w64 v).
{ intros r v Hin' H21 Hcs. rewrite (e5_pres _ _ r HPR2 Hcs).
  apply RT; [exact Hin' | intros E; exact (Cno102A_E3.e3_ncs r (or_introl E) Hcs)
    | intros E; exact (Cno102A_E3.e3_ncs r (or_intror E) Hcs) | exact H21
    | intros E; subst; revert Hin'; cbn; intros Hin'; repeat (destruct Hin' as [Hin' | Hin']; [discriminate Hin' |]); exact Hin'
    | intros E; subst; revert Hin'; cbn; intros Hin'; repeat (destruct Hin' as [Hin' | Hin']; [discriminate Hin' |]); exact Hin']. }
assert (V2 : getr regs2 2%bv = w64 (cn_S1 D)) by (apply VP; [ro_in | discriminate | apply e5_cs; vm_compute; reflexivity]).
assert (V8 : getr regs2 8%bv = w64 (cn_sp0 D)) by (apply VP; [ro_in | discriminate | apply e5_cs; vm_compute; reflexivity]).
assert (V9 : getr regs2 9%bv = w64 (cn_S1 D)) by (apply VP; [ro_in | discriminate | apply e5_cs; vm_compute; reflexivity]).
assert (V18 : getr regs2 18%bv = w64 (shadow_addr (cn_F D))) by (apply VP; [ro_in | discriminate | apply e5_cs; vm_compute; reflexivity]).
assert (V27 : getr regs2 27%bv = w64 (cn_F D)) by (apply VP; [ro_in | discriminate | apply e5_cs; vm_compute; reflexivity]).
assert (V24 : getr regs2 24%bv = w64 (VAL (A_HI 9))) by (apply VP; [ro_in | discriminate | apply e5_cs; vm_compute; reflexivity]).
assert (V19 : getr regs2 19%bv = w64 (cn_size D + 16)) by (apply VP; [ro_in | discriminate | apply e5_cs; vm_compute; reflexivity]).
assert (V20 : getr regs2 20%bv = w64 (cn_size D)) by (apply VP; [ro_in | discriminate | apply e5_cs; vm_compute; reflexivity]).
assert (V23 : getr regs2 23%bv = w64 (ci_data D)) by (apply VP; [ro_in | discriminate | apply e5_cs; vm_compute; reflexivity]).
assert (V21 : getr regs2 21%bv = w64 (cn_d2 D))
  by (rewrite (e5_pres _ _ 21%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)); exact T21).
assert (V25 : getr regs2 25%bv = w64 (cn_d1 D))
  by (rewrite (e5_pres _ _ 25%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)); exact T25).
assert (V26 : getr regs2 26%bv = w64 (cn_d3 D))
  by (rewrite (e5_pres _ _ 26%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)); exact T26).
assert (V3 : getr regs2 3%bv = getr (ci_regs D) 3%bv)
  by (rewrite (e5_pres _ _ 3%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)); exact T3).
assert (V4 : getr regs2 4%bv = getr (ci_regs D) 4%bv)
  by (rewrite (e5_pres _ _ 4%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)); exact T4).
assert (V10 : getr regs2 10%bv = w64 res) by exact Hres.
assert (Hres64 : 0 <= res < 2 ^ 64).
{ destruct HARMS as [HA | HA].
  - destruct HA as [E _]. rewrite E. lia.
  - destruct HA as (H4096 & Hab2 & _).
    destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJ2)
      ltac:(rewrite Hab2; apply in_or_app; right; left; reflexivity)) as (_ & _ & Hce & _).
    assert (Hsz16 : 0 <= cn_size D + 16) by lia.
    pose proof (e2_req_ge (cn_size D + 16) Hsz16) as Hrq. lia. }
(* +552 mv s6, a0 *)
change (mkCfg (@YK11.mkst fxk regs2 (w64 (cn_pc 552)) mem2 (YK11.seg_rom SEGS)) md2)
  with (@cn_cfg SEGS fxk (cn_pc 552) regs2 mem2 md2).
apply (cn_hs_addi W2 fxk regs2 mem2 md2 _ 552 556 22%bv 10%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X6.
set (regs6 := regupd regs2 22%bv (v_addi (getr regs2 10%bv) 0)).
assert (R6 : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr regs6 r = getr regs2 r).
{ intros r Hr. cbn in Hr. unfold regs6.
  repeat (destruct Hr as [<- | Hr]; [ro_getr; reflexivity |]). destruct Hr. }
assert (R622 : getr regs6 22%bv = w64 res).
{ unfold regs6. ro_getr. rewrite V10, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
(* ---- +556 sd s5, 48(s1); +560 sd s9, 56(s1): the d2 / d1 slots ---- *)
assert (HSTKP : forall a, cn_sp0 D - STK_check_no_overread <= a < cn_sp0 D -> apresent (w_H W2) mem2 a).
{ exact (ajx_pres HJ2). }
unfold cn_cfg, cn_pc, w64. replace (BASE + CN_OFF + 556) with (BASE + 1360) by lia.
apply (s_sd P PLAW W2 regs6 mem2 _ _ 1360 1364 9%bv 21%bv 48 (cn_S1 D + 48));
  [vm_compute; reflexivity | lia | lia | reflexivity | | lia | lia | | exact HPM2 |].
{ rewrite (R6 9%bv ltac:(ro_in)), V9. apply (e2_addi (cn_S1 D) 48); lia. }
{ intros i Hi. apply HSTKP. rewrite HSTK. lia. }
intros mdA memA HsA HfrA HgrA HhA HvA HPA.
apply (s_sd P PLAW W2 regs6 memA mdA _ 1364 1368 9%bv 25%bv 56 (cn_S1 D + 56));
  [vm_compute; reflexivity | lia | lia | reflexivity | | lia | lia | | exact HPA |].
{ rewrite (R6 9%bv ltac:(ro_in)), V9. apply (e2_addi (cn_S1 D) 56); lia. }
{ intros i Hi. apply (e5_apr_grows _ mem2 memA _ HgrA). apply HSTKP. rewrite HSTK. lia. }
intros mdB memB HsB HfrB HgrB HhB HvB HPB.
assert (HJB : ajournal_x SEGS B prh_pst ARcfx STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D)
  (ci_W D) (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)] ly2 S2 Hp W2 memB mdB (k + (st_nev S2 - st_nev S))).
{ assert (HJA : ajournal_x SEGS B prh_pst ARcfx STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D)
    (ci_W D) (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)] ly2 S2 Hp W2 memA mdA (k + (st_nev S2 - st_nev S))).
  { apply (ajournal_x_exec SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memA mdA
      (fun x => cn_S1 D + 48 <= x < cn_S1 D + 48 + 8) HJ2 HfrA HgrA HhA HsA).
    intros a Ha. cbv beta in Ha. left. rewrite HSTK. lia. }
  apply (ajournal_x_exec SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memB mdB
    (fun x => cn_S1 D + 56 <= x < cn_S1 D + 56 + 8) HJA HfrB HgrB HhB HsB).
  intros a Ha. cbv beta in Ha. left. rewrite HSTK. lia. }
assert (KRB : forall a, 0 <= a < 2 ^ 64 -> ~ (cn_S1 D + 48 <= a < cn_S1 D + 64) ->
  aview SEGS (w_H W2) memB a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H48. unfold aview, mbyte.
  rewrite (HfrB (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ha; lia).
  rewrite (HfrA (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ha; lia). reflexivity. }
assert (SL48 : rdword (aview SEGS (w_H W2) memB) (cn_S1 D + 48) = Some (cn_d2 D)).
{ rewrite <- (e_rdword_of_val_mem (w_H W2) memA (cn_S1 D + 48) (cn_d2 D)); [| | unfold cn_d2; lia].
  - apply rdword_ext. intros q Hq. unfold aview, mbyte.
    rewrite (HfrB (Z_to_bv 64 (cn_S1 D + 48 + q))) by (rewrite unsigned_lit_small by lia; lia). reflexivity.
  - rewrite (R6 21%bv ltac:(ro_in)), V21 in HvA. unfold w64 in HvA. rewrite unsigned_lit_small in HvA by (unfold cn_d2; lia).
    exact HvA. }
assert (SL56 : rdword (aview SEGS (w_H W2) memB) (cn_S1 D + 56) = Some (cn_d1 D)).
{ apply e_rdword_of_val_mem; [| unfold cn_d1; lia].
  rewrite (R6 25%bv ltac:(ro_in)), V25 in HvB. unfold w64 in HvB. rewrite unsigned_lit_small in HvB by (unfold cn_d1; lia).
  exact HvB. }
(* +564 beqz a0 -> +792 (CN_INIT3) / +568 *)
replace (BASE + 1368) with (BASE + CN_OFF + 564) by lia.
change (mkCfg (@YK11.mkst fxk regs6 (Z_to_bv 64 (BASE + CN_OFF + 564)) memB (YK11.seg_rom SEGS)) mdB)
  with (@cn_cfg SEGS fxk (cn_pc 564) regs6 memB mdB).
apply (cn_hs_beqz W2 fxk _ memB _ _ 564 10%bv 228 792 568 (res =? 0));
  [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | |].
{ rewrite ro_getr0. unfold regs6. ro_getr. rewrite V10. apply ro_c_eq0. lia. }
intros X7.
destruct (Z.eqb_spec res 0) as [Hz | Hnz].
{ (* ---- THE THIRD NULL: res = 0, +564 beqz a0 -> +792, CN_INIT3: nothing more is written ---- *)
  destruct HARMS as [(Eres & Eab2 & KEPT & Herr & Hoom) | (H4096 & _)]; [|lia].
  destruct KEPT as (KA & KB & KC & KD & KE & KF).
  set (mdE := with_vm_backing (m_vm_lazy mdB) X7 mdB).
  apply SRr_ret. split; [right|exact HPB].
  exists fxk, ly2, S2, Hp, regs6, memB, mdE, (k + (st_nev S2 - st_nev S)), r1, r2.
  split; [reflexivity|].
  assert (HJE : cn_J B ARcfx D ly2 S2 Hp W2 memB mdE (k + (st_nev S2 - st_nev S)) 0).
  { apply cn_J_of_x. unfold mdE.
    exact (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7 HJB). }
  assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W2) memB a = aview SEGS (w_H W) mem a).
  { intros a Hi Hno Her. pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow. unfold kLowMemEnd in Hlow.
    rewrite (KRB a ltac:(lia) ltac:(lia)). exact (KC a Hi Hno Her). }
  assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (cn_S1 D - ASTACK <= a < cn_S1 D) ->
    ~ (cn_S1 D + 48 <= a < cn_S1 D + 64) -> aview SEGS (w_H W2) memB a = aview SEGS (w_H W) mem a).
  { intros a Ha Hw H48. rewrite (KRB a ltac:(lia) H48). apply KA; [exact Ha | unfold cn_sp0 in *; lia]. }
  assert (KBB : forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
    aview SEGS (w_H W2) memB (b + i) = aview SEGS (w_H W) mem (b + i)).
  { intros b m i Hbm Hi.
    destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hbm) as (_ & Hb4096 & Hbtop & _).
    rewrite (KRB (b + i) ltac:(lia) ltac:(lia)). exact (KB b m i Hbm Hi (fun x => x)). }
  (* the frame geometry *)
  assert (EF : ly_F ly2 = ly_F ly).
  { pose proof (ajx_ly HJ2) as HL2.
    destruct HL2 as (_ & _ & _ & _ & _ & EF2 & _).
    destruct Hly as (_ & _ & _ & _ & _ & EF1 & _). rewrite EF2, EF1. reflexivity. }
  assert (Eframe : frame_addr ly2 CN_CID (ci_fpos D) = frame_addr ly CN_CID (ci_fpos D))
    by (unfold frame_addr; rewrite EF; reflexivity).
  assert (Eflag : flag_addr ly2 CN_CID (ci_fpos D) = flag_addr ly CN_CID (ci_fpos D))
    by (unfold flag_addr, frame_addr; rewrite EF; reflexivity).
  assert (HFB : fs_frame_bytes CN_CID = 512) by (vm_compute; reflexivity).
  assert (Hfa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F in *; congruence).
  assert (KFR : forall a, cn_F D <= a < cn_F D + fs_frame_bytes CN_CID ->
    aview SEGS (w_H W2) memB a = aview SEGS (w_H W) mem a).
  { intros a Ha. rewrite HFB in Ha. rewrite (KRB a ltac:(lia) ltac:(lia)).
    apply (KD CN_CID (ci_fpos D) a); [rewrite Hfrs; left; reflexivity | | intros []].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa, HFB. lia. }
  (* the ledger, own unchanged *)
  assert (KI1 : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) memB a = aview SEGS (w_H W) mem a).
  { intros a Hp0. exact (KIMG a (proj1 (cni_pst_ok B IMG a Hp0)) (proj2 (cni_pst_ok B IMG a Hp0)) (cni_pst_errno B IMG a Hp0)). }
  assert (L1 : prh_ledger B ly2 S2 Hp W2 memB (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own).
  { apply (e2_ledger_own ly S Hp W mem ly2 S2 Hp W2 memB (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
      (ci_most D) own own HLG).
    - intros a Hp0 _. exact (KI1 a Hp0).
    - split; [|exact HOWN01]. rewrite <- (cni_own B IMG).
      apply (val_mem_kept SEGS (w_H W) (w_H W2) mem memB); [|exact Hown].
      intros q Hq. apply KI1. rewrite (cni_own B IMG). exact (Cno102A_E2.e2_cell_pst _ _ q prh_pst_own Hq).
    - intros a kk i Hin Hi. apply prh_mbyte_of_aview.
      destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLG Hin) as (Hk0 & Hblk & _).
      pose proof cf_head_nonneg. unfold prh_head_wide in HW.
      assert (Hkc : 0 <= kk + cf_head) by lia. pose proof (e2_req_ge _ Hkc) as Hge.
      replace (a - cf_head + i) with ((a - cf_head) + i) by lia.
      apply (KBB (a - cf_head) (kk + cf_head) i Hblk). lia.
    - intros a kk Hin Hb. rewrite Eab2. exact Hb.
    - apply Permutation_refl. }
  assert (ERS : PresetRoom.rs_live (YGcfRoom.room_of_cf S2) = PresetRoom.rs_live (YGcfRoom.room_of_cf S)).
  { change (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (blocks S2)).
    change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)).
    pose proof (f_equal (map snd) Eab2) as E. unfold ablocks in E. rewrite !map_map in E. cbn [snd] in E. exact E. }
  assert (CPK : forall r, cn_copy B D ly S Hp W mem r -> cn_copy B D ly2 S2 Hp W2 memB r).
  { intros r HCr. apply (e3_copy_keep D ly S Hp W mem ly2 S2 W2 memB mdE (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ
      (ci_ran D) (ci_most D) own r HCr).
    - intros x Hx. rewrite Eab2. exact Hx.
    - exact (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE)).
    - exact L1.
    - intros Hr0 a Ha. destruct HCr as [E1 | (Hin1 & _)]; [contradiction|].
      replace a with (r + (a - r)) by lia. apply (KBB r (cn_size D + 16) (a - r) Hin1).
      pose proof (e2_req_ge (cn_size D + 16) ltac:(lia)). lia. }
  split.
  { (* cn_base *)
    split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJE|].
    split.
    { unfold cn_frame. rewrite Hfrs2. split; [exact Hfrs|]. split; [exact Hnin|].
      split.
      { rewrite Eflag. rewrite <- Hflag. apply rdword_ext. intros q Hq.
        apply KFR. unfold cn_F in *. lia. }
      destruct (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp W2 memB mdE CN_CID (ci_fpos D) (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE))
        ltac:(rewrite Hfrs2, Hfrs; left; reflexivity)) as (_ & _ & HFPR & HFSH).
      split.
      - intros a Ha. destruct (HFPR a ltac:(rewrite Eframe, Hfa; exact Ha)) as [Hpr _]. exact Hpr.
      - intros a Ha. destruct (HFSH (a - shadow_addr (cn_F D)) ltac:(lia)) as [Hpr _].
        replace (shadow_addr (frame_addr ly2 CN_CID (ci_fpos D)) + (a - shadow_addr (cn_F D))) with a in Hpr
          by (rewrite Eframe, Hfa; lia).
        exact Hpr. }
    split.
    { unfold cn_saved in *.
      repeat (let H := fresh "Hs" in apply Forall_cons_iff in HSV as [H HSV]; apply Forall_cons;
        [cbn [fst snd] in H |- *; rewrite <- H; apply rdword_ext; intros q Hq;
         apply KHI; unfold ASTACK, cn_sp0 in *; lia |]).
      apply Forall_nil. }
    split; [rewrite (R6 3%bv ltac:(ro_in)); exact V3|]. split; [rewrite (R6 4%bv ltac:(ro_in)); exact V4|].
    intros a Hro Hno Herr2.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hsg & _ & Ha) | Hr]; [exists sg; split; [exact Hsg | exact Ha] | exact (@pa_relro_img _ _ PA a Hr)]).
    rewrite (KIMG a Hi Hno Herr2).
    exact (HROD a Hro Hno Herr2). }
  split.
  { unfold cn_regsat, cn_core, cn_s8. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - rewrite (R6 2%bv ltac:(ro_in)). exact V2.
    - rewrite (R6 8%bv ltac:(ro_in)). exact V8.
    - rewrite (R6 9%bv ltac:(ro_in)). exact V9.
    - rewrite (R6 18%bv ltac:(ro_in)). exact V18.
    - rewrite (R6 27%bv ltac:(ro_in)). exact V27.
    - rewrite (R6 24%bv ltac:(ro_in)). exact V24.
    - rewrite (R6 19%bv ltac:(ro_in)). exact V19.
    - rewrite (R6 20%bv ltac:(ro_in)). exact V20.
    - rewrite (R6 21%bv ltac:(ro_in)). exact V21.
    - rewrite R622, Eres. reflexivity.
    - rewrite (R6 23%bv ltac:(ro_in)). exact V23.
    - rewrite (R6 25%bv ltac:(ro_in)). exact V25.
    - rewrite (R6 26%bv ltac:(ro_in)). exact V26. }
  split.
  { (* the six slots: 24 / 32 / 40 / 80 kept, 48 / 56 stored here *)
    unfold cn_slots, cn_slotsL in *.
    apply Forall_cons_iff in HSL as [H24 HSL]. apply Forall_cons_iff in HSL as [H32 HSL].
    apply Forall_cons_iff in HSL as [H40 HSL]. apply Forall_cons_iff in HSL as [H80 _].
    cbn [fst snd] in H24, H32, H40, H80.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - rewrite <- H24. apply rdword_ext. intros q Hq. apply KHI; unfold ASTACK, cn_sp0 in *; lia.
    - rewrite <- H32. apply rdword_ext. intros q Hq. apply KHI; unfold ASTACK, cn_sp0 in *; lia.
    - rewrite <- H40. apply rdword_ext. intros q Hq. apply KHI; unfold ASTACK, cn_sp0 in *; lia.
    - exact SL48.
    - exact SL56.
    - rewrite <- H80. apply rdword_ext. intros q Hq. apply KHI; unfold ASTACK, cn_sp0 in *; lia. }
  split; [exact (CPK r1 HCP1)|].
  split; [exact (CPK r2 HCP2)|].
  split; [exact HHp|].
  split; [exists own; exact L1|].
  split.
  { rewrite e4_cblks, e4_cblk0, app_nil_r, Eab2. exact HPERM. }
  split; [exact HROOM2|].
  split.
  { unfold cn_prog in *. rewrite e4_cevs.
    assert (E0 : cn_cevsl D [0] = []) by (unfold cn_cevsl, cn_cblk; reflexivity).
    rewrite E0, app_nil_r.
    destruct HRP as [HRP1 HRP2]. split; [rewrite ERS; exact HRP1|].
    intros sm x0 os i H0 hist Hpos Hrun.
    destruct (HRP2 sm x0 os i H0 hist Hpos Hrun) as (hist' & Hpos').
    exists hist'.
    exact (PresetRoomPosKeep.room_pos_keep_alloc_null SEGS B ly S Hp W regsT mem mdT ch1 sm x0 os _ H0 hist'
      (cn_size D + 16) _ trc S2 HPREcf ltac:(unfold cn_size in *; lia) ltac:(cbn [length] in HBUD; unfold cn_size in *; lia)
      HTRc ltac:(rewrite <- Eres in Hpn; rewrite (proj2 Hpn eq_refl) in Hpath; exact Hpath) Hpos'). }
  split.
  { pose proof (blocks_bytes_bsum B ly2 S2) as EB2. pose proof (blocks_bytes_bsum B ly S) as EB.
    rewrite EB2, Eab2, <- EB. cbn [length] in HBUD. lia. }
  (* the third copy refused: CNO-COPY's refusal is dead at a consumer run. Copy 3's __wrap_malloc returned NULL
     on a granted path (the rule's apath / gflag) at the cut's own state S, after the granted copies of [r1; r2]
     (cn_prog) *)
  split; [|exact HHULL2].
  apply (e2_cdead B D [r1; r2] S HRP
    ltac:(unfold cn_cblk; cbn [flat_map]; destruct (r1 =? 0), (r2 =? 0); cbn; lia) (WFL _ _ _ _ _ _ HAR)).
  left. exists (cn_size D + 16), (call_trace ly (pc_malloc_ra0 (as_code B)) regsT ch1), trc, S2.
  split; [|exact Hgf]. rewrite <- (proj2 Hpn Eres). exact Hpath. }
(* ---- THE THIRD COPY GRANTED: res <> 0 (r3), the new block (res, size + 16); +568 mv s3, s10; +572 beqz s4; +576..588
   the memcpy (ACPY); +592..604 the 16-byte padding of 0 (ASET), returning to +608 (CN_INIT) ---- *)
destruct HARMS as [(Eres & _) | (H4096 & Eab2 & KEPT)]; [exfalso; exact (Hnz Eres)|].
destruct KEPT as (KA & KB & KC & KD & KE & KF).
pose proof alloc_ceiling_val as [AC2 _].
pose proof (e5_S1 D Hal16) as [_ HS1c].
assert (HinNB : In (res, cn_size D + 16) (ablocks B ly2 S2))
  by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJ2) HinNB)
  as (_ & Hr4096 & Hrtop & Hrapp & _ & Hpw).
assert (Hsz16 : 0 <= cn_size D + 16) by lia.
pose proof (e2_req_ge (cn_size D + 16) Hsz16) as Hrq.
assert (Hrq1 : 1 <= req_size (cn_size D + 16))
  by (unfold req_size; destruct (Z.eqb_spec (cn_size D + 16) 0); lia).
assert (HAPART : forall b m, In (b, m) (ablocks B ly S) ->
  zdisjoint (b, req_size m) (res, req_size (cn_size D + 16))).
{ intros b m Hbm. rewrite Eab2, map_app in Hpw. apply pairwise_app_inv in Hpw as (_ & _ & Hx).
  apply (Hx (b, req_size m) (res, req_size (cn_size D + 16))).
  - apply in_map_iff. exists (b, m). split; [reflexivity | exact Hbm].
  - left. reflexivity. }
assert (HNEW : ~ In (res, cn_size D + 16) (ablocks B ly S)).
{ intros Hc. pose proof (HAPART _ _ Hc) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HNEW0 : ~ In (res, cn_size D + 16) (ablocks B (ci_ly D) (ci_S D))).
{ intros Hc. apply HNEW. exact (e2_blocks_in D ly S Hp W mem md k _ _ HJ Hc Hsz16). }
assert (HresHp : ~ In res Hp).
{ intros Hh. pose proof (prh_ledger_heads B ly S Hp W mem _ _ _ _ _ _ _ HLG) as HPh.
  apply (Permutation_in _ HPh) in Hh. apply in_map_iff in Hh as ([a kk] & Eh & Hak). cbn [fst] in Eh.
  destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLG Hak) as (Hk0 & Hblk & _).
  rewrite Eh in Hblk. pose proof (HAPART _ _ Hblk) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof cf_head_nonneg.
  assert (1 <= req_size (kk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia). lia. }
assert (KBB : forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
  aview SEGS (w_H W2) memB (b + i) = aview SEGS (w_H W) mem (b + i)).
{ intros b m i Hbm Hi.
  destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hbm) as (_ & Hb4096 & Hbtop & _).
  pose proof (HAPART _ _ Hbm) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  rewrite (KRB (b + i) ltac:(lia) ltac:(lia)).
  apply (KB b m i Hbm Hi). cbv beta. lia. }
assert (KI1 : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) memB a = aview SEGS (w_H W) mem a).
{ intros a Hp0. pose proof (@pa_segs_low _ _ PA _ (proj1 (cni_pst_ok B IMG a Hp0))) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (KRB a ltac:(lia) ltac:(lia)).
  exact (KC a (proj1 (cni_pst_ok B IMG a Hp0)) (proj2 (cni_pst_ok B IMG a Hp0)) (cni_pst_errno B IMG a Hp0)). }
assert (L1 : prh_ledger B ly2 S2 Hp W2 memB (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own).
{ apply (e2_ledger_own ly S Hp W mem ly2 S2 Hp W2 memB (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
    (ci_most D) own own HLG).
  - intros a Hp0 _. exact (KI1 a Hp0).
  - split; [|exact HOWN01]. rewrite <- (cni_own B IMG).
    apply (val_mem_kept SEGS (w_H W) (w_H W2) mem memB); [|exact Hown].
    intros q Hq. apply KI1. rewrite (cni_own B IMG). exact (Cno102A_E2.e2_cell_pst _ _ q prh_pst_own Hq).
  - intros a kk i Hin Hi. apply prh_mbyte_of_aview.
    destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLG Hin) as (Hk0 & Hblk & _).
    pose proof cf_head_nonneg. unfold prh_head_wide in HW.
    assert (Hkc : 0 <= kk + cf_head) by lia. pose proof (e2_req_ge _ Hkc) as Hge.
    replace (a - cf_head + i) with ((a - cf_head) + i) by lia.
    apply (KBB (a - cf_head) (kk + cf_head) i Hblk). lia.
  - intros a kk Hin Hb. rewrite Eab2. apply in_or_app. left. exact Hb.
  - apply Permutation_refl. }
pose proof HSRC as (HSby & HS4096 & HSce & HSam & _ & _).
assert (SRCK : forall a, ci_data D <= a < ci_data D + cn_size D ->
  aview SEGS (w_H W2) memB a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
{ intros a Ha. assert (Hs0 : 0 < cn_size D) by lia.
  exact (e2_src_kept D ly2 S2 Hp W2 memB _ _ (ci_data D) (cn_size D) (cn_J_of_x B ARcfx _ _ _ _ _ _ _ _ 0 HJB) HLED
    (HHOME Hs0) a Ha). }
assert (SRCD : 0 < cn_size D -> res + cn_size D <= ci_data D \/ ci_data D + cn_size D <= res).
{ intros Hs0. pose proof cf_head_nonneg as CH0.
  assert (BLK : forall b m, In (b, m) (ablocks B ly S) -> b <= ci_data D -> ci_data D + cn_size D <= b + req_size m ->
    res + cn_size D <= ci_data D \/ ci_data D + cn_size D <= res).
  { intros b m Hbm Hb Hm. pose proof (HAPART _ _ Hbm) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (IMGc : (forall a, ci_data D <= a < ci_data D + cn_size D -> in_img SEGS a) ->
    res + cn_size D <= ci_data D \/ ci_data D + cn_size D <= res).
  { intros Hi. destruct (Z_le_gt_dec (res + cn_size D) (ci_data D)) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (ci_data D + cn_size D) res) as [h'|h']; [right; exact h'|]. exfalso.
    destruct (Z_le_gt_dec res (ci_data D)) as [hz|hz].
    - assert (Hz1 : res <= ci_data D < res + req_size (cn_size D + 16)) by lia.
      assert (Hz2 : ci_data D <= ci_data D < ci_data D + cn_size D) by lia.
      exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly2 S2 Hp W2 _ _ (ci_data D) (ajx_ar HJ2)
        (or_introl (ex_intro _ res (ex_intro _ (cn_size D + 16) (conj HinNB Hz1))))) (Hi _ Hz2)).
    - assert (Hz1 : res <= res < res + req_size (cn_size D + 16)) by lia.
      assert (Hz2 : ci_data D <= res < ci_data D + cn_size D) by lia.
      exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly2 S2 Hp W2 _ _ res (ajx_ar HJ2)
        (or_introl (ex_intro _ res (ex_intro _ (cn_size D + 16) (conj HinNB Hz1))))) (Hi _ Hz2)). }
  assert (ROI : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img SEGS a).
  { intros a Hr. destruct Hr as [(sg & Hsg & _ & Hsa) | Hr];
      [exists sg; split; [exact Hsg | exact Hsa] | exact (@pa_relro_img _ _ PA a Hr)]. }
  destruct (HHOME Hs0) as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & Hb & Hm)].
  - destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b m _ _ HLED Hin) as (Hm0 & Hab & _).
    assert (Hmc : 0 <= m + cf_head) by lia. pose proof (e2_req_ge _ Hmc).
    apply (BLK (b - cf_head) (m + cf_head) (e2_blocks_in D ly S Hp W mem md k _ _ HJ Hab Hmc)); lia.
  - apply IMGc. intros a Ha. exact (ROI a (proj1 (Hro a Ha))).
  - apply IMGc. intros a Ha. exact (ROI a (proj1 (Hro a Ha))).
  - assert (Hm0 : 0 <= m) by lia. pose proof (e2_req_ge m Hm0).
    apply (BLK b m (e2_blocks_in D ly S Hp W mem md k _ _ HJ Hin Hm0)); lia. }
assert (SRCH : forall Wc memc mdc pk cnt fl rn mo ow, ARcfx ly2 S2 Hp Wc memc mdc ->
  prh_ledger B ly2 S2 Hp Wc memc (ci_Lam D) pk cnt fl rn mo ow -> 0 < cn_size D ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (ci_data D) (cn_size D) /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) (ci_data D) (cn_size D)).
{ intros Wc memc mdc pk cnt fl rn mo ow HARc' HLc Hs0.
  apply (e2_src_shadow ly2 S2 Hp Wc memc mdc (ci_Lam D) pk cnt fl rn mo ow _ _ HARc' HLc Hs0).
  destruct (HHOME Hs0) as [Hk | (b & m & Hin & Hbn & Hb & Hm)]; [left; exact Hk | right].
  exists b, m. split; [|split; [rewrite HHp; exact Hbn | lia]].
  apply (e2_blocks_in D ly2 S2 Hp W2 memB _ _ _ _ (cn_J_of_x B ARcfx _ _ _ _ _ _ _ _ 0 HJB) Hin). lia. }
assert (DSTH : forall Wc memc mdc pk cnt fl rn mo ow d n, ARcfx ly2 S2 Hp Wc memc mdc ->
  prh_ledger B ly2 S2 Hp Wc memc (ci_Lam D) pk cnt fl rn mo ow -> 0 < n -> res <= d -> d + n <= res + (cn_size D + 16) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF d n /\ shadow_hull_vis (aview SEGS (w_H Wc) memc) d n).
{ intros Wc memc mdc pk cnt fl rn mo ow d n HARc' HLc Hn Hd1 Hd2.
  apply (e2_src_shadow ly2 S2 Hp Wc memc mdc (ci_Lam D) pk cnt fl rn mo ow d n HARc' HLc Hn).
  right. exists res, (cn_size D + 16). split; [exact HinNB|]. split; [exact HresHp|]. lia. }
assert (HWIN : YM05.alloc_ceiling + 8 <= cn_S1 D - ESTACK) by (unfold ESTACK; rewrite HSTK in Hslo; lia).
assert (AWR : forall a, res <= a < res + (cn_size D + 16) ->
  awr_byte STK_check_no_overread (cn_sp0 D) [] (ablocks B (ci_ly D) (ci_S D)) (ablocks B ly2 S2) ly2
    [(CN_CID, ci_fpos D)] a /\
  ~ (cn_sp0 D + (cn_S1 D - cn_sp0 D) - ESTACK <= a < cn_sp0 D + (cn_S1 D - cn_sp0 D))).
{ intros a Ha. split; [|lia].
  right; right; left. exists res, (cn_size D + 16). split; [exact HinNB|]. split; [exact HNEW0|]. lia. }
assert (AMR : forall d n, res <= d -> d + n <= res + (cn_size D + 16) -> 0 <= n -> amem_range d n).
{ intros d n Hd1 Hd2 Hn. unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, ASAN_CEIL in *. lia. }
assert (EF : ly_F ly2 = ly_F ly).
{ pose proof (ajx_ly HJ2) as HL2.
  destruct HL2 as (_ & _ & _ & _ & _ & EF2 & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF1 & _). rewrite EF2, EF1. reflexivity. }
assert (Eframe : frame_addr ly2 CN_CID (ci_fpos D) = frame_addr ly CN_CID (ci_fpos D))
  by (unfold frame_addr; rewrite EF; reflexivity).
assert (Eflag : flag_addr ly2 CN_CID (ci_fpos D) = flag_addr ly CN_CID (ci_fpos D))
  by (unfold flag_addr, frame_addr; rewrite EF; reflexivity).
assert (HFB : fs_frame_bytes CN_CID = 512) by (vm_compute; reflexivity).
assert (Hfa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F in *; congruence).
(* +568 mv s3, s10 *)
apply (cn_hs_addi W2 fxk regs6 memB _ _ 568 572 19%bv 26%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X8.
set (regsM := regupd regs6 19%bv (v_addi (getr regs6 26%bv) 0)).
assert (M19 : getr regsM 19%bv = w64 (cn_d3 D)).
{ unfold regsM. ro_getr. rewrite (R6 26%bv ltac:(ro_in)), V26, e2_addi by (unfold cn_d3; lia). rewrite Z.add_0_r. reflexivity. }
assert (M22 : getr regsM 22%bv = w64 res) by (unfold regsM; ro_getr; exact R622).
assert (MR : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 23%bv; 24%bv; 25%bv; 27%bv] ->
  getr regsM r = getr regs2 r).
{ intros r Hr. rewrite <- (R6 r ltac:(cbn in Hr |- *; tauto)). cbn in Hr. unfold regsM.
  repeat (destruct Hr as [<- | Hr]; [ro_getr; reflexivity |]). destruct Hr. }
assert (TAIL : forall regsX memX mdX,
  cn_J B ARcfx D ly2 S2 Hp W2 memX mdX (k + (st_nev S2 - st_nev S)) 0 -> P memX ->
  (forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv] ->
     getr regsX r = getr regsM r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + cn_size D) -> ~ (cn_S1 D - ESTACK <= a < cn_S1 D) ->
     aview SEGS (w_H W2) memX a = aview SEGS (w_H W2) memB a) ->
  (forall i, 0 <= i < cn_size D ->
     aview SEGS (w_H W2) memX (res + i) = aview SEGS (w_H W2) memB (ci_data D + i)) ->
  SRr SEGS W2 (@cn_cfg SEGS fxk (cn_pc 592) regsX memX mdX)
    (fun W' c' => (cn_ex_init (fx := fx) B ARcfx D W' c' \/ cn_ex_init3 (fx := fx) B ARcfx D W' c') /\
                  P (ms_mem (cfg_ms c')))).
{ intros regsX memX mdX HJX HPX RX KX CX.
  pose proof HJX as HJXc. apply e_J0 in HJXc.
  assert (LX : prh_ledger B ly2 S2 Hp W2 memX (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own).
  { apply (e2_ledger_blk ly2 S2 Hp W2 memB _ memX _ _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJB) L1 HinNB HresHp).
    intros a Ha Hn. apply KX; lia. }
  (* +592 add a0, s6, s4; +596 li a2, 16; +600 li a1, 0; +604 jal __asan_memset *)
  apply (e2_hs_add W2 fxk regsX memX mdX _ 592 596 10%bv 22%bv 20%bv);
    [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X10.
  apply (cn_hs_addi W2 fxk _ memX _ _ 596 600 12%bv 0%bv 16); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X11.
  apply (cn_hs_addi W2 fxk _ memX _ _ 600 604 11%bv 0%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X12.
  apply (cn_hs_call W2 fxk _ memX _ _ 604 608 AS___asan_memset); [vm_compute; reflexivity | lia | reflexivity |].
  intros X13.
  lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg _ ?mo) _ => set (regsS := rg); set (mdS := mo) end.
  assert (S10 : getr regsS 10%bv = w64 (res + cn_size D)).
  { unfold regsS. ro_getr. rewrite (RX 22%bv ltac:(ro_in)), M22, (RX 20%bv ltac:(ro_in)), (MR 20%bv ltac:(ro_in)), V20.
    apply e2_vadd; lia. }
  assert (S11 : getr regsS 11%bv = w64 0) by (unfold regsS; ro_getr; rewrite ro_getr0; apply (e2_addi 0 0); lia).
  assert (S12 : getr regsS 12%bv = w64 16) by (unfold regsS; ro_getr; rewrite ro_getr0; apply (e2_addi 0 16); lia).
  assert (SR1 : getr regsS 1%bv = w64 (cn_pc 608)) by (unfold regsS; ro_getr; reflexivity).
  assert (SR3 : getr regsS 3%bv = w64 (as_gp B))
    by (unfold regsS; ro_getr; rewrite (RX 3%bv ltac:(ro_in)), (MR 3%bv ltac:(ro_in)), V3; exact Hgp0).
  assert (SR4 : getr regsS 4%bv = w64 (as_tp B))
    by (unfold regsS; ro_getr; rewrite (RX 4%bv ltac:(ro_in)), (MR 4%bv ltac:(ro_in)), V4; exact Htp0).
  assert (SSP : spZ regsS = cn_sp0 D + (cn_S1 D - cn_sp0 D)).
  { unfold spZ, regsS. ro_getr. rewrite (RX 2%bv ltac:(ro_in)), (MR 2%bv ltac:(ro_in)), V2. unfold w64.
    rewrite unsigned_lit_small by lia. lia. }
  pose proof (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X13
    (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X12
    (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X11
    (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X10 HJXc))))
    as HJS.
  destruct (DSTH W2 memX _ _ _ _ _ _ _ (res + cn_size D) 16 (ajx_ar HJS) LX ltac:(lia) ltac:(lia) ltac:(lia))
    as [DRA2 DHV2].
  unfold cn_cfg. unfold w64 at 1.
  eapply SRr_bind.
  { apply (aj_intrin_at_xm (fx := fxk) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) OSet
      (SIGMA AS___asan_memset) (ASET fxk)
      W2 regsS memX STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
      [(CN_CID, ci_fpos D)] ly2 S2 Hp mdS (k + (st_nev S2 - st_nev S)) (res + cn_size D) 0 16
      (cn_S1 D - cn_sp0 D) (w64 (cn_pc 608))).
    - exact HJS.
    - exact S10.
    - exact S11.
    - exact S12.
    - lia.
    - lia.
    - lia.
    - exact SSP.
    - exact HS1mod.
    - lia.
    - unfold ESTACK. rewrite HSTK. lia.
    - exact SR3.
    - exact SR4.
    - exact SR1.
    - unfold cn_pc. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; rewrite HOFF; [lia | reflexivity].
    - intros a Ha. apply AWR. lia.
    - apply AMR; lia.
    - exact DRA2.
    - intros _. exact DHV2.
    - exact I. }
  cbv beta. intros W4 c4 Hwle4 (-> & regs3 & mem3 & md3 & -> & HJ3 & HPR3 & H310 & HBY3 & HKP3 & HGR3 & HMN3).
  (* the cut CN_INIT (+608) *)
  apply SRr_ret. split; [left|exact (PCALL _ _ HMN3 HPX)].
  exists fxk, ly2, S2, Hp, regs3, mem3, md3, (k + (st_nev S2 - st_nev S)), r1, r2, res, own.
  split; [reflexivity|].
  assert (HJE : cn_J B ARcfx D ly2 S2 Hp W2 mem3 md3 (k + (st_nev S2 - st_nev S)) 0) by (apply cn_J_of_x; exact HJ3).
  assert (KE3 : forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + (cn_size D + 16)) ->
    ~ (cn_S1 D - ESTACK <= a < cn_S1 D) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) memB a).
  { intros a Ha Hn Hw. rewrite (HKP3 a Ha ltac:(lia) ltac:(lia)). apply KX; lia. }
  assert (KHI3 : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (cn_S1 D - ASTACK <= a < cn_S1 D) ->
    ~ (cn_S1 D + 48 <= a < cn_S1 D + 64) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hw H48. rewrite (KE3 a ltac:(lia) ltac:(lia) ltac:(unfold ASTACK, ESTACK in *; lia)).
    rewrite (KRB a ltac:(lia) H48). apply KA; [exact Ha | unfold cn_sp0 in *; lia]. }
  assert (KIMG3 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Hi Hno Her. pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow. unfold kLowMemEnd in Hlow.
    assert (Hnb : ~ (res <= a < res + (cn_size D + 16))).
    { intros Hr. assert (Hr' : res <= a < res + req_size (cn_size D + 16)) by lia.
      exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly2 S2 Hp W2 _ _ a (ajx_ar HJ2)
        (or_introl (ex_intro _ res (ex_intro _ (cn_size D + 16) (conj HinNB Hr'))))) Hi). }
    rewrite (KE3 a ltac:(lia) Hnb ltac:(lia)), (KRB a ltac:(lia) ltac:(lia)). exact (KC a Hi Hno Her). }
  assert (KFR3 : forall a, cn_F D <= a < cn_F D + fs_frame_bytes CN_CID ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Ha. rewrite HFB in Ha.
    destruct (alx_sep SEGS B ARcfx LAWS ly2 S2 Hp W2 _ _ (ajx_ar HJ2)) as [Hsep Hfb].
    apply pairwise_app_inv in Hsep as (_ & _ & Hsx).
    assert (HFin : In (CN_CID, ci_fpos D) (frames S2)) by (rewrite Hfrs2, Hfrs; left; reflexivity).
    pose proof (Hsx (res, req_size (cn_size D + 16)) (frame_addr ly2 CN_CID (ci_fpos D), fs_frame_bytes CN_CID)
      ltac:(apply in_map_iff; exists (res, cn_size D + 16); split; [reflexivity | exact HinNB])
      ltac:(apply in_map_iff; exists (CN_CID, ci_fpos D); split; [reflexivity | exact HFin])) as HdF.
    cbn [fst snd] in HdF. rewrite Eframe, Hfa, HFB in HdF.
    unfold zdisjoint in HdF. cbn [fst snd] in HdF.
    rewrite (KE3 a ltac:(lia) ltac:(lia) ltac:(lia)), (KRB a ltac:(lia) ltac:(lia)).
    apply (KD CN_CID (ci_fpos D) a); [rewrite Hfrs; left; reflexivity | | cbv beta; lia].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa, HFB. lia. }
  assert (L3 : prh_ledger B ly2 S2 Hp W2 mem3 (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own).
  { apply (e2_ledger_blk ly2 S2 Hp W2 memX _ mem3 _ _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJXc) LX HinNB HresHp).
    intros a Ha Hn. apply HKP3; lia. }
  assert (G3R : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv] ->
    getr regs3 r = getr regsM r).
  { intros r Hr. rewrite <- (RX r Hr). cbn in Hr.
    repeat (destruct Hr as [<- | Hr];
      [lazymatch goal with |- getr _ ?r = _ =>
         rewrite (e5_pres _ _ r HPR3 ltac:(apply e5_cs; vm_compute; reflexivity)) end;
       unfold regsS; ro_getr; reflexivity |]).
    destruct Hr. }
  pose proof L3 as L3c. apply prh_ledger_iff in L3c as [HG3 _].
  destruct HG3 as (_ & _ & _ & _ & _ & _ & HO3 & _).
  assert (CPK : forall r, cn_copy B D ly S Hp W mem r -> cn_copy B D ly2 S2 Hp W2 mem3 r).
  { intros r HCr. apply (e3_copy_keep D ly S Hp W mem ly2 S2 W2 mem3 md3 (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ
      (ci_ran D) (ci_most D) own r HCr).
    - intros x Hx. rewrite Eab2. apply in_or_app. left. exact Hx.
    - exact (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE)).
    - exact L3.
    - intros Hr0 a Ha. destruct HCr as [E1 | (Hin1 & _)]; [contradiction|].
      pose proof (HAPART _ _ Hin1) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hin1) as (_ & Hb4096 & Hbtop & _).
      rewrite (KE3 a ltac:(lia) ltac:(lia) ltac:(lia)).
      replace a with (r + (a - r)) by lia. apply (KBB r (cn_size D + 16) (a - r) Hin1). lia. }
  split.
  { (* cn_base *)
    split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJE|].
    split.
    { unfold cn_frame. rewrite Hfrs2. split; [exact Hfrs|]. split; [exact Hnin|].
      split.
      { rewrite Eflag. rewrite <- Hflag. apply rdword_ext. intros q Hq.
        apply KFR3. unfold cn_F in *. lia. }
      destruct (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp W2 mem3 md3 CN_CID (ci_fpos D) (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE))
        ltac:(rewrite Hfrs2, Hfrs; left; reflexivity)) as (_ & _ & HFPR & HFSH).
      split.
      - intros a Ha. destruct (HFPR a ltac:(rewrite Eframe, Hfa; exact Ha)) as [Hpr _]. exact Hpr.
      - intros a Ha. destruct (HFSH (a - shadow_addr (cn_F D)) ltac:(lia)) as [Hpr _].
        replace (shadow_addr (frame_addr ly2 CN_CID (ci_fpos D)) + (a - shadow_addr (cn_F D))) with a in Hpr
          by (rewrite Eframe, Hfa; lia).
        exact Hpr. }
    split.
    { unfold cn_saved in *.
      repeat (let H := fresh "Hs" in apply Forall_cons_iff in HSV as [H HSV]; apply Forall_cons;
        [cbn [fst snd] in H |- *; rewrite <- H; apply rdword_ext; intros q Hq;
         apply KHI3; unfold ASTACK, cn_sp0 in *; lia |]).
      apply Forall_nil. }
    split; [rewrite (G3R 3%bv ltac:(ro_in)), (MR 3%bv ltac:(ro_in)); exact V3|].
    split; [rewrite (G3R 4%bv ltac:(ro_in)), (MR 4%bv ltac:(ro_in)); exact V4|].
    intros a Hro Hno Herr2.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hsg & _ & Ha) | Hr]; [exists sg; split; [exact Hsg | exact Ha] | exact (@pa_relro_img _ _ PA a Hr)]).
    rewrite (KIMG3 a Hi Hno Herr2).
    exact (HROD a Hro Hno Herr2). }
  split.
  { unfold cn_regsat, cn_core, cn_s8. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; rewrite G3R by ro_in.
    - rewrite (MR 2%bv ltac:(ro_in)). exact V2.
    - rewrite (MR 8%bv ltac:(ro_in)). exact V8.
    - rewrite (MR 9%bv ltac:(ro_in)). exact V9.
    - rewrite (MR 18%bv ltac:(ro_in)). exact V18.
    - rewrite (MR 27%bv ltac:(ro_in)). exact V27.
    - rewrite (MR 24%bv ltac:(ro_in)). exact V24.
    - exact M19.
    - rewrite (MR 20%bv ltac:(ro_in)). exact V20.
    - rewrite (MR 21%bv ltac:(ro_in)). exact V21.
    - exact M22.
    - rewrite (MR 23%bv ltac:(ro_in)). exact V23.
    - rewrite (MR 25%bv ltac:(ro_in)). exact V25. }
  split.
  { unfold cn_slots, cn_slotsL in *.
    apply Forall_cons_iff in HSL as [H24 HSL]. apply Forall_cons_iff in HSL as [H32 HSL].
    apply Forall_cons_iff in HSL as [H40 HSL]. apply Forall_cons_iff in HSL as [H80 _].
    cbn [fst snd] in H24, H32, H40, H80.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - rewrite <- H24. apply rdword_ext. intros q Hq. apply KHI3; unfold ASTACK, cn_sp0 in *; lia.
    - rewrite <- H32. apply rdword_ext. intros q Hq. apply KHI3; unfold ASTACK, cn_sp0 in *; lia.
    - rewrite <- H40. apply rdword_ext. intros q Hq. apply KHI3; unfold ASTACK, cn_sp0 in *; lia.
    - rewrite <- SL48. apply rdword_ext. intros q Hq. apply KE3; unfold ESTACK in *; lia.
    - rewrite <- SL56. apply rdword_ext. intros q Hq. apply KE3; unfold ESTACK in *; lia.
    - rewrite <- H80. apply rdword_ext. intros q Hq. apply KHI3; unfold ASTACK, cn_sp0 in *; lia. }
  split; [exact (CPK r1 HCP1)|].
  split; [exact (CPK r2 HCP2)|].
  split.
  { right. split; [exact HinNB|]. split; [exact HresHp|].
    unfold src_rd. split.
    - intros j Hj. destruct (HSby j Hj) as [Hv Hr]. split; [|exact Hr].
      intros q Hq. etransitivity; [|exact (Hv q Hq)]. apply e2_mbyte_of_aview2.
      assert (Eq : q = 0%nat) by lia. subst q. cbn [Z.of_nat]. rewrite !Z.add_0_r.
      assert (Hj' : 0 <= Z.of_nat j < cn_size D) by (unfold cn_size; lia).
      rewrite (HKP3 (res + Z.of_nat j) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite (CX (Z.of_nat j) Hj'). apply SRCK. lia.
    - split; [lia|]. split; [unfold cn_size in *; lia|].
      split; [apply AMR; unfold cn_size in *; lia|].
      destruct (Z.eq_dec (cn_size D) 0) as [E0 | E0].
      + split; [apply range_addressable_nil; unfold cn_size in *; lia | intros Hl; unfold cn_size in *; lia].
      + destruct (DSTH W2 mem3 md3 _ _ _ _ _ _ res (cn_size D) (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE)) L3 ltac:(lia) ltac:(lia) ltac:(lia))
          as [RA3 HV3].
        unfold cn_size in RA3, HV3. split; [exact RA3 | intros _; exact HV3]. }
  split; [exact Hnz|].
  split; [destruct HOWN01 as [-> | ->]; lia|].
  split; [rewrite (cni_own B IMG); exact (proj1 HO3)|].
  split.
  { intros Ho0. pose proof (HOWN0 Ho0) as HF. apply Forall_cons_iff in HF as [Hr1n HF].
    apply Forall_cons_iff in HF as [Hr2n _]. split; [exact Hr1n | exact Hr2n]. }
  split; [exact HCD|].
  split; [exact HHp|].
  split; [exact L3|].
  split.
  { assert (Ecb : cn_cblk D res = [(res, cn_size D + 16)])
      by (unfold cn_cblk; rewrite (proj2 (Z.eqb_neq res 0) Hnz); reflexivity).
    rewrite e4_cblks, Ecb, Eab2.
    apply Permutation_trans with (flat_map (cn_cblk D) [r1; r2] ++ ablocks B (ci_ly D) (ci_S D)
      ++ [(res, cn_size D + 16)]).
    - rewrite (app_assoc (flat_map (cn_cblk D) [r1; r2]) (ablocks B (ci_ly D) (ci_S D)) [(res, cn_size D + 16)]).
      apply Permutation_app_tail. exact HPERM.
    - rewrite <- (app_assoc (flat_map (cn_cblk D) [r1; r2]) [(res, cn_size D + 16)] (ablocks B (ci_ly D) (ci_S D))).
      apply Permutation_app_head. apply Permutation_app_comm. }
  split; [exact HROOM2|].
  split.
  { unfold cn_prog in *. rewrite e4_cevs.
    assert (Ere : cn_cevsl D [res] = [PresetReqAt.HMal (cn_size D + PresetReqAt.FUZZ_PAD)]).
    { unfold cn_cevsl, cn_cblk. cbn [flat_map]. rewrite (proj2 (Z.eqb_neq res 0) Hnz). reflexivity. }
    rewrite Ere. unfold PresetReqAt.FUZZ_PAD.
    destruct HRP as [HRP1 HRP2]. split.
    - rewrite PresetReqAt.hlive_from_app, PresetReqAt.hlive_from_cons, PresetReqAt.hlive_from_nil.
      cbn [PresetReqAt.hstep].
      change (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (blocks S2)).
      change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)) in HRP1.
      assert (EM : map snd (blocks S2) = map snd (blocks S) ++ [cn_size D + 16]).
      { pose proof (f_equal (map snd) Eab2) as E. unfold ablocks in E. rewrite !map_app, !map_map in E.
        cbn [snd map] in E. exact E. }
      rewrite EM.
      apply Permutation_trans with (cn_size D + 16 :: map snd (blocks S));
        [apply Permutation_sym, Permutation_cons_append | apply perm_skip; exact HRP1].
    - intros sm x0 os i H0 hist Hpos Hrun.
      apply prh_run_at_app_iff in Hrun as [Hrun1 Hrun2].
      destruct (HRP2 sm x0 os i H0 hist Hpos Hrun1) as (hist' & Hpos').
      exists hist'. rewrite length_app. cbn [length]. rewrite Nat.add_assoc, Nat.add_1_r.
      apply (PresetRoomPosKeep.room_pos_keep_alloc SEGS B ly S Hp W regsT mem mdT ch1 sm x0 os _ H0 hist'
        (cn_size D + 16) _ trc p S2 HPREcf ltac:(unfold cn_size in *; lia)
        ltac:(cbn [length] in HBUD; unfold cn_size in *; lia) HTRc Hpath (fun E => Hnz (proj1 Hpn E)) Hpos').
      apply (proj1 (prh_run_at_one sm x0 os _ _)). exact Hrun2. }
  split; [|exact HHULL2].
  pose proof (blocks_bytes_bsum B ly2 S2) as EB2. pose proof (blocks_bytes_bsum B ly S) as EB.
  rewrite EB2, Eab2, bsum_app, <- EB. change (bsum [(res, cn_size D + 16)]) with (cn_size D + 16 + 0).
  cbn [length] in HBUD. lia. }
(* +572 beqz s4 -> +592 (size = 0) / +576 *)
apply (cn_hs_beqz W2 fxk regsM memB _ _ 572 20%bv 20 592 576 (cn_size D =? 0));
  [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | |].
{ rewrite ro_getr0, (MR 20%bv ltac:(ro_in)), V20. apply ro_c_eq0. lia. }
intros X9.
destruct (Z.eqb_spec (cn_size D) 0) as [Hs0 | Hs0].
{ (* size = 0: no copy *)
  apply (TAIL regsM memB _).
  - apply cn_J_of_x. exact (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X9
      (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X8
      (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7 HJB))).
  - exact HPB.
  - intros r _. reflexivity.
  - intros a _ _ _. reflexivity.
  - intros i Hi. lia. }
(* +576 mv a0, s6; +580 mv a1, s7; +584 mv a2, s4; +588 jal __asan_memcpy *)
assert (Hs1 : 0 < cn_size D) by lia.
apply (cn_hs_addi W2 fxk _ memB _ _ 576 580 10%bv 22%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X10.
apply (cn_hs_addi W2 fxk _ memB _ _ 580 584 11%bv 23%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X11.
apply (cn_hs_addi W2 fxk _ memB _ _ 584 588 12%bv 20%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X12.
apply (cn_hs_call W2 fxk _ memB _ _ 588 592 AS___asan_memcpy); [vm_compute; reflexivity | lia | reflexivity |].
intros X13.
lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg _ ?mo) _ => set (regsC := rg); set (mdC := mo) end.
assert (C10 : getr regsC 10%bv = w64 res).
{ unfold regsC. ro_getr. rewrite M22, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (C11 : getr regsC 11%bv = w64 (ci_data D)).
{ unfold regsC. ro_getr. rewrite (MR 23%bv ltac:(ro_in)), V23, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (C12 : getr regsC 12%bv = w64 (cn_size D)).
{ unfold regsC. ro_getr. rewrite (MR 20%bv ltac:(ro_in)), V20, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (CR1 : getr regsC 1%bv = w64 (cn_pc 592)) by (unfold regsC; ro_getr; reflexivity).
assert (CR3 : getr regsC 3%bv = w64 (as_gp B)) by (unfold regsC; ro_getr; rewrite (MR 3%bv ltac:(ro_in)), V3; exact Hgp0).
assert (CR4 : getr regsC 4%bv = w64 (as_tp B)) by (unfold regsC; ro_getr; rewrite (MR 4%bv ltac:(ro_in)), V4; exact Htp0).
assert (CSP : spZ regsC = cn_sp0 D + (cn_S1 D - cn_sp0 D)).
{ unfold spZ, regsC. ro_getr. rewrite (MR 2%bv ltac:(ro_in)), V2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
pose proof (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X13
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X12
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X11
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X10
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X9
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X8
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7 HJB)))))))
  as HJC.
destruct (SRCH W2 memB _ _ _ _ _ _ _ (ajx_ar HJC) L1 Hs1) as [SRA SHV].
destruct (DSTH W2 memB _ _ _ _ _ _ _ res (cn_size D) (ajx_ar HJC) L1 Hs1 ltac:(lia) ltac:(lia)) as [DRA DHV].
unfold cn_cfg. unfold w64 at 1.
eapply SRr_bind.
{ apply (aj_intrin_at_xm (fx := fxk) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) OCpy
    (SIGMA AS___asan_memcpy) (ACPY fxk)
    W2 regsC memB STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly2 S2 Hp mdC (k + (st_nev S2 - st_nev S)) res (ci_data D) (cn_size D)
    (cn_S1 D - cn_sp0 D) (w64 (cn_pc 592))).
  - exact HJC.
  - exact C10.
  - exact C11.
  - exact C12.
  - lia.
  - lia.
  - lia.
  - exact CSP.
  - exact HS1mod.
  - lia.
  - unfold ESTACK. rewrite HSTK. lia.
  - exact CR3.
  - exact CR4.
  - exact CR1.
  - unfold cn_pc. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; rewrite HOFF; [lia | reflexivity].
  - intros a Ha. apply AWR. lia.
  - apply AMR; lia.
  - exact DRA.
  - intros _. exact DHV.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - rewrite (SRCK a Ha). apply (e2_garr8_some _ _ (ci_data D) (ci_x D) a HSby). unfold cn_size in Ha. exact Ha.
      - rewrite CSP. unfold cn_size in *. lia. }
    split; [exact (SRCD Hs1)|]. split; [exact HSam|]. split; [exact SRA | intros _; exact SHV]. }
cbv beta. intros W3 c3 Hwle3 (-> & regsP & memP & mdP & -> & HJP & HPRP & HP10 & HBYP & HKPP & HGRP & HMNP).
change (mkCfg (@YK11.mkst fxk regsP (w64 (cn_pc 592)) memP (YK11.seg_rom SEGS)) mdP)
  with (@cn_cfg SEGS fxk (cn_pc 592) regsP memP mdP).
apply (TAIL regsP memP mdP).
- apply cn_J_of_x. exact HJP.
- exact (PCALL _ _ HMNP HPB).
- intros r Hr. cbn in Hr.
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?r = _ =>
       rewrite (e5_pres _ _ r HPRP ltac:(apply e5_cs; vm_compute; reflexivity)) end;
     unfold regsC; ro_getr; reflexivity |]).
  destruct Hr.
- intros a Ha Hn Hw. apply HKPP; [exact Ha | exact Hn | lia].
- intros i Hi. exact (HBYP i Hi).
Qed.

End e4.

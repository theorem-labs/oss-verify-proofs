(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1292 of its 1364 lines of code are new or changed and 442 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_E2.v, with its numbers changed; 380 of its 986 lines of code are new or changed and 758 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c): segment CA3 of the re-walk of check_no_overread
   (cno): the SECOND PADDED COPY, CN_COPY2 (+460) to CN_COPY3 (+532). FREE-PIECES-102 Part 7
   row R7-3.
   rule 24: proves no function (kind: segment lemma).
   THE CODE (DERIVED offsets from cno's entry):
     +460 .. +464  a0 = s3 (size + 16); jal __wrap_malloc
     +468 .. +472  sd s5, 24(s1) (r1); sd a0, 40(s1) (r2); +476 beqz a0 -> +524 (the refused arm)
     +480 .. +500  s6 = a0; beqz s4 (size = 0) -> +504; a0 = s6, a1 = s7 (data), a2 = s4; jal __asan_memcpy
     +504 .. +516  a0 = s6 + s4; a1 = 0x32; a2 = 16; jal __asan_memset (the padding's magic)
     +520          j +12 -> +532
     +524 .. +528  (refused) a0 = 1; sb a0, -0x558(s8): g_own_ran_out := 1; falls to +532
   THE RELATION and the SECTION HYPOTHESES are Cno102A_E2.v's (CA2): ARx := ARcfx; IMG, PAL, HW, IMGSH, AMALLOC, ACPY,
   ASET. The kit lemmas are Cno102A_E2.v's e2_*, applied here to this section's parameters.
   Numerals: offsets (DERIVED); 16 (LENGTH: the pad); 0x32 (LENGTH: the pad's fill byte); 24 / 40 (OFFSET: the r1 / r2
   slots of the frame at s1); register numbers (WORD). *)
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
  Cno102A_E Cno102A_E0 Cno102A_E2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section e3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
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

(* +468 is cno's second __wrap_malloc return site *)
Lemma e3_site : In (cn_pc 468) (pi_ret_sites F_check_no_overread RT_malloc).
Proof. unfold cn_pc. rewrite (cni_base B IMG). vm_compute. tauto. Qed.

(* ra and a0 are not callee-saved *)
Lemma e3_ncs : forall r : bv 5, (r = 1%bv \/ r = 10%bv) -> ~ acallee_saved (bv_unsigned r).
Proof.
intros r [-> | ->] H; unfold acallee_saved in H.
- assert (E : bv_unsigned (1%bv : bv 5) = 1) by reflexivity. rewrite E in H. lia.
- assert (E : bv_unsigned (10%bv : bv 5) = 10) by reflexivity. rewrite E in H. lia.
Qed.

(* the events of two copies are the first's then the second's *)
Lemma e3_cevsl2 : forall D r1 r2, cn_cevsl D [r1; r2] = cn_cevsl D [r1] ++ cn_cevsl D [r2].
Proof. intros D r1 r2. unfold cn_cevsl. cbn [flat_map]. rewrite !app_nil_r, map_app. reflexivity. Qed.

(* a copy made earlier is a copy at a later state: its block is still live, its bytes are kept, its shadow is the
   later state's block shadow (e2_src_shadow's block arm) *)
Lemma e3_copy_keep : forall D ly S Hp W mem ly' S' W' mem' md' Lam pk cnt fl rn mo ow r,
  cn_copy B D ly S Hp W mem r ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  ARcfx ly' S' Hp W' mem' md' -> prh_ledger B ly' S' Hp W' mem' Lam pk cnt fl rn mo ow ->
  (r <> 0 -> forall a, r <= a < r + cn_size D -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  cn_copy B D ly' S' Hp W' mem' r.
Proof.
intros D ly S Hp W mem ly' S' W' mem' md' Lam pk cnt fl rn mo ow r [-> | (Hin & Hn & Hsrc)] Hinc HAR HL K;
  [left; reflexivity | right].
split; [exact (Hinc _ Hin)|]. split; [exact Hn|].
destruct Hsrc as (Hby & H4096 & Hce & Ham & Hra & Hhv).
specialize (K ltac:(lia)). unfold cn_size in K.
split.
- intros j Hj. destruct (Hby j Hj) as [Hv Hr]. split; [|exact Hr].
  intros q Hq. etransitivity; [|exact (Hv q Hq)]. apply e2_mbyte_of_aview2. apply K. lia.
- split; [exact H4096|]. split; [exact Hce|]. split; [exact Ham|].
  destruct (Z.eq_dec (Z.of_nat (length (ci_x D))) 0) as [E0 | E0].
  + split; [apply range_addressable_nil; lia | intros Hl; lia].
  + assert (Hb : r <= r /\ r + Z.of_nat (length (ci_x D)) <= r + (cn_size D + 16)) by (unfold cn_size; lia).
    destruct (e2_src_shadow ly' S' Hp W' mem' md' Lam pk cnt fl rn mo ow r (Z.of_nat (length (ci_x D))) HAR HL ltac:(lia)
      (or_intror (ex_intro _ r (ex_intro _ (cn_size D + 16) (conj (Hinc _ Hin) (conj Hn Hb)))))) as [RA HV].
    split; [exact RA | intros _; exact HV].
Qed.

(* ======== CA3 ======== *)
Theorem cn_CA3 : @cn_seg_CA3 fx rc ci CfParams_preset prh_room_live_a8 SK PA B ARcfx CTX0.
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k r1 own HPRE HAT HPM.
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
(* r1, the first copy: NULL or a live block below the ceiling *)
pose proof (proj1 (Forall_forall _ _) HCP r1 (or_introl eq_refl)) as HCP1.
assert (Hr1 : 0 <= r1 < 2 ^ 64).
{ destruct HCP1 as [-> | (Hin1 & _)]; [lia|].
  destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hin1) as (_ & H4 & Htop & _).
  pose proof (e2_req_ge (cn_size D + 16) ltac:(lia)). lia. }
(* +460 mv a0, s3; +464 jal __wrap_malloc *)
apply (cn_hs_addi W fxk regs mem md _ 460 464 10%bv 19%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X1.
apply (cn_hs_call W fxk _ mem _ _ 464 468 AS___wrap_malloc); [vm_compute; reflexivity | lia | reflexivity |].
intros X2.
lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg _ ?mo) _ => set (regsT := rg); set (mdT := mo) end.
assert (RT : forall r v, In (r, v) (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, r1);
  (23%bv, ci_data D)]) -> r <> 1%bv -> r <> 10%bv -> getr regsT r = w64 v).
{ intros r v Hin' H1 H10. unfold regsT. rewrite !getr_other by (intros E; subst; contradiction).
  exact (RG r v Hin'). }
assert (T10 : getr regsT 10%bv = w64 (cn_size D + 16)).
{ unfold regsT. ro_getr. rewrite (RG 19%bv (cn_size D + 16) ltac:(ro_in)).
  rewrite e2_addi by (unfold cn_size in *; lia). f_equal. lia. }
assert (T2 : getr regsT 2%bv = w64 (cn_S1 D)) by (apply RT; [ro_in | discriminate | discriminate]).
assert (T8 : getr regsT 8%bv = w64 (cn_sp0 D)) by (apply RT; [ro_in | discriminate | discriminate]).
assert (T1 : getr regsT 1%bv = w64 (cn_pc 468)) by (unfold regsT; ro_getr; reflexivity).
assert (T3 : getr regsT 3%bv = getr (ci_regs D) 3%bv) by (unfold regsT; ro_getr; exact G3).
assert (T4 : getr regsT 4%bv = getr (ci_regs D) 4%bv) by (unfold regsT; ro_getr; exact G4).
assert (HSPT : spZ regsT = cn_S1 D) by (unfold spZ; rewrite T2; unfold w64; apply unsigned_lit_small; unfold cn_sp0 in *; lia).
assert (Hpc468 : 4096 <= cn_pc 468 < 2 ^ 40).
{ unfold cn_pc. rewrite HBASE, HOFF. unfold A_prog_base. lia. }
assert (HRAT : raZ regsT = cn_pc 468) by (unfold raZ; rewrite T1; unfold w64; apply unsigned_lit_small; lia).
(* the journal at the call *)
pose proof (cn_base_mat B ARcfx LAWS D fxk ly S Hp W regs (regupd regs 10%bv (v_addi (getr regs 19%bv) 0)) mem _ k 0 X1 HB
  ltac:(ro_getr; reflexivity) ltac:(ro_getr; reflexivity)) as HB1.
pose proof (cn_base_mat B ARcfx LAWS D fxk ly S Hp W _ regsT mem _ k 0 X2 HB1
  ltac:(unfold regsT; ro_getr; reflexivity) ltac:(unfold regsT; ro_getr; reflexivity)) as HB2.
pose proof HB2 as (_ & _ & HJT & _). apply e_J0 in HJT.
(* the chain and the universe *)
destruct (e2_chain D fxk ly S Hp W regs mem md k HPRE HB) as (ch1 & Hach & Hsp1).
assert (HCH : chain_pre ly (aview SEGS (w_H W) mem) regsT ch1).
{ apply (achain_chain_pre ly _ (cn_S1 D) (cn_sp0 D) ch1 regsT Hach).
  - rewrite HSPT. unfold cn_sp0 in *. rewrite HSTK in *. lia.
  - unfold s0Z. rewrite T8. unfold w64. apply unsigned_lit_small. unfold cn_sp0 in *. lia.
  - rewrite HRAT. lia. }
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch1) (as_universe B))
  by exact (e2_univ D regsT ch1 RT_malloc (cn_pc 468) HUNIV HCTX e3_site HRAT Hsp1).
(* the malloc's trace is a FIXED one of the universe (P'' set: the call rule asks `admits`, YG01.admits_fix, and its
   post carries the trace in the journal's wild budget, which ajournal_xw_fix1 drops again) *)
assert (HTRc : In (call_trace ly (pc_malloc_ra0 (as_code B)) regsT ch1) (as_universe B)).
{ apply YCbq.call_trace_in; [exact (proj1 HUNIV RT_malloc) | exact HTR]. }
pose proof (alloc_model_laws_x_cf B (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HAR))) as AMX.
pose proof (Cno102A_E2.e2_live_pj_nonneg (ci_x D)) as HLP.
assert (HBUD1 : blocks_bytes S + 2 * (cn_size D + 16) + 3 * PRH_FnPj.LIVE_pj_parse (ci_x D) <= LIVE_MAX)
  by (cbn [length] in HBUD; exact HBUD).
unfold cn_cfg. rewrite (pal_malloc B PAL). unfold w64 at 1.
eapply SRr_bind.
{ eapply (YGcallMxmnKeep.aj_malloc_at_x_m_keep (fx := fxk) (SK := SK) SEGS B prh_pst ARcfx QM_cf (QMm_cf SEGS B) malloc_cf cf_malloc_max
    free_cf (Wf_cf (as_universe B)) xs_cf LAWS (@pa_segs_low _ _ PA) (pal_env B PAL) OWNLOW WFL AMX (QMQ_cf SEGS B) XSL
    (YGcallMxmnKeep.amalloc_realizes_x_xs_keep (fx := fxk) SEGS B (AMALLOC fxk))
    W regsT mem STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly S Hp mdT k (cn_size D + 16) (cn_S1 D - cn_sp0 D) (w64 (cn_pc 468)) ch1).
  - exact HJT.
  - exact T10.
  - unfold cn_size in *. lia.
  - unfold cn_size in *. lia.
  - rewrite HSPT. lia.
  - exact HS1mod.
  - lia.
  - unfold ASTACK. rewrite HSTK. lia.
  - rewrite T3. exact Hgp0.
  - rewrite T4. exact Htp0.
  - exact T1.
  - unfold cn_pc. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; rewrite HOFF; [lia | reflexivity].
  - (* the QMm guard at the call: two facts, the hull admission and arodata_ok_cf (part 3c dropped memnorm) *)
    apply (QMm_cf_of_room SEGS B _ _ _ _ _ _ (proj1 HAR) HQT (YGcfRoomLive.room_live_room _ HROOMc));
      [ (* the hull admission at the call: the copy2 cut's stage budget *)
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
   cpy1 stage's budget pays it to cpy2's (cn_hpay_copy) *)
pose proof (PresetHullBudget.hull_used_of_call _ _ _ _ (YGcfSecsStep.secs_malloc_step _ _ _ _ _ Hpath)) as HUSED.
pose proof HHULL as HH1. rewrite cn_hrest_cpy2_split in HH1.
destruct (cn_hpay_copy _ _ _ HH1) as [_ HNEXT].
assert (HHULL2 : PresetHullBudget.hull_budget S2 (cn_hrest_cpy2 (ci_x D))) by (apply HNEXT; exact HUSED).
(* the journal after the call: the fixed trace leaves the budget (YCbqG.v ajournal_xw_fix1) *)
pose proof (ajournal_xw_fix1 HTRc HJ2) as HJ2f. clear HJ2. rename HJ2f into HJ2.
assert (HPM2 : P mem2) by exact (PCALL _ _ HMNK HPM).
pose proof (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) as HPREcf.
destruct (e2_counts_at D ly S Hp W mem [r1] own HPRE HE
  ltac:(unfold cn_cblk; cbn [flat_map]; destruct (r1 =? 0); cbn; lia)) as (CSEC & C24).
assert (HROOM2 : room_live_cf S2)
  by exact (@RM_malloc _ _ prh_room_malloc_a8 fxk rc ci SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ (p, S2) HPREcf CSEC C24 HROOMc Hpath).
(* the registers after the call: preserved, a0 = res *)
assert (VP : forall r v, In (r, v) (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, r1);
  (23%bv, ci_data D)]) -> acallee_saved (bv_unsigned r) -> getr regs2 r = w64 v).
{ intros r v Hin' Hcs. rewrite (e5_pres _ _ r HPR2 Hcs).
  apply RT; [exact Hin' | intros E; exact (e3_ncs r (or_introl E) Hcs) | intros E; exact (e3_ncs r (or_intror E) Hcs)]. }
assert (V2 : getr regs2 2%bv = w64 (cn_S1 D)) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
assert (V8 : getr regs2 8%bv = w64 (cn_sp0 D)) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
assert (V9 : getr regs2 9%bv = w64 (cn_S1 D)) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
assert (V18 : getr regs2 18%bv = w64 (shadow_addr (cn_F D))) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
assert (V27 : getr regs2 27%bv = w64 (cn_F D)) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
assert (V24 : getr regs2 24%bv = w64 (VAL (A_HI 9))) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
assert (V19 : getr regs2 19%bv = w64 (cn_size D + 16)) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
assert (V20 : getr regs2 20%bv = w64 (cn_size D)) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
assert (V21 : getr regs2 21%bv = w64 r1) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
assert (V23 : getr regs2 23%bv = w64 (ci_data D)) by (apply VP; [ro_in | apply e5_cs; vm_compute; reflexivity]).
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
(* ---- +468 sd s5, 24(s1); +472 sd a0, 40(s1): the r1 / r2 slots (the stack window of the journal) ---- *)
assert (HSTKP : forall a, cn_sp0 D - STK_check_no_overread <= a < cn_sp0 D -> apresent (w_H W2) mem2 a).
{ exact (ajx_pres HJ2). }
change (mkCfg (@YK11.mkst fxk regs2 (w64 (cn_pc 468)) mem2 (YK11.seg_rom SEGS)) md2)
  with (@cn_cfg SEGS fxk (cn_pc 468) regs2 mem2 md2).
unfold cn_cfg, cn_pc, w64. replace (BASE + CN_OFF + 468) with (BASE + 1272) by lia.
apply (s_sd P PLAW W2 regs2 mem2 md2 _ 1272 1276 9%bv 21%bv 24 (cn_S1 D + 24));
  [vm_compute; reflexivity | lia | lia | reflexivity | | lia | lia | | exact HPM2 |].
{ rewrite V9. apply (e2_addi (cn_S1 D) 24); lia. }
{ intros i Hi. apply HSTKP. rewrite HSTK. lia. }
intros mdA memA HsA HfrA HgrA HhA HvA HPA.
apply (s_sd P PLAW W2 regs2 memA mdA _ 1276 1280 9%bv 10%bv 40 (cn_S1 D + 40));
  [vm_compute; reflexivity | lia | lia | reflexivity | | lia | lia | | exact HPA |].
{ rewrite V9. apply (e2_addi (cn_S1 D) 40); lia. }
{ intros i Hi. apply (e5_apr_grows _ mem2 memA _ HgrA). apply HSTKP. rewrite HSTK. lia. }
intros mdB memB HsB HfrB HgrB HhB HvB HPB.
assert (HJB : ajournal_x SEGS B prh_pst ARcfx STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D)
  (ci_W D) (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)] ly2 S2 Hp W2 memB mdB (k + (st_nev S2 - st_nev S))).
{ assert (HJA : ajournal_x SEGS B prh_pst ARcfx STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D)
    (ci_W D) (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)] ly2 S2 Hp W2 memA mdA (k + (st_nev S2 - st_nev S))).
  { apply (ajournal_x_exec SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memA mdA
      (fun x => cn_S1 D + 24 <= x < cn_S1 D + 24 + 8) HJ2 HfrA HgrA HhA HsA).
    intros a Ha. cbv beta in Ha. left. rewrite HSTK. lia. }
  apply (ajournal_x_exec SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memB mdB
    (fun x => cn_S1 D + 40 <= x < cn_S1 D + 40 + 8) HJA HfrB HgrB HhB HsB).
  intros a Ha. cbv beta in Ha. left. rewrite HSTK. lia. }
assert (KRB : forall a, 0 <= a < 2 ^ 64 -> ~ (cn_S1 D + 24 <= a < cn_S1 D + 32) -> ~ (cn_S1 D + 40 <= a < cn_S1 D + 48) ->
  aview SEGS (w_H W2) memB a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H24 H40. unfold aview, mbyte.
  rewrite (HfrB (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ha; lia).
  rewrite (HfrA (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ha; lia). reflexivity. }
assert (SL24 : rdword (aview SEGS (w_H W2) memB) (cn_S1 D + 24) = Some r1).
{ rewrite <- (e_rdword_of_val_mem (w_H W2) memA (cn_S1 D + 24) r1); [| | lia].
  - apply rdword_ext. intros q Hq. unfold aview, mbyte.
    rewrite (HfrB (Z_to_bv 64 (cn_S1 D + 24 + q))) by (rewrite unsigned_lit_small by lia; lia). reflexivity.
  - rewrite V21 in HvA. unfold w64 in HvA. rewrite unsigned_lit_small in HvA by lia. exact HvA. }
assert (SL40 : rdword (aview SEGS (w_H W2) memB) (cn_S1 D + 40) = Some res).
{ apply e_rdword_of_val_mem; [| lia]. rewrite V10 in HvB. unfold w64 in HvB. rewrite unsigned_lit_small in HvB by lia.
  exact HvB. }
(* +476 beqz a0 -> +524 (refused) / +480 (granted) *)
replace (BASE + 1280) with (BASE + CN_OFF + 476) by lia.
change (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + CN_OFF + 476)) memB (YK11.seg_rom SEGS)) mdB)
  with (@cn_cfg SEGS fxk (cn_pc 476) regs2 memB mdB).
apply (cn_hs_beqz W2 fxk _ memB _ _ 476 10%bv 48 524 480 (res =? 0));
  [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | |].
{ rewrite ro_getr0, V10. apply ro_c_eq0. lia. }
intros X4.
destruct (Z.eqb_spec res 0) as [Hz | Hnz].
{ (* ---- THE REFUSED COPY: +524 li a0, 1; +528 sb a0, -1368(s8) (g_own_ran_out := 1); falls to +532 ---- *)
  apply (cn_hs_addi W2 fxk _ memB _ _ 524 528 10%bv 0%bv 1);
    [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X5.
  destruct (e2_own_wr W2 memB) as [Hoh How].
  pose proof (@pa_val_range _ _ PA (A_OBJ 13)) as HV13.
  unfold cn_cfg, cn_pc. replace (BASE + CN_OFF + 528) with (BASE + 1332) by lia.
  pose proof (@pa_val_range _ _ PA (A_HI 9)) as HV9.
  apply (e5s_sb P PLAW W2 _ memB _ _ 1332 1336 24%bv 10%bv (-1368) (VAL (A_OBJ 13)));
    [vm_compute; reflexivity | lia | lia | reflexivity
    | ro_getr; rewrite V24; unfold v_addi, w64; rewrite unsigned_lit_small by lia;
      rewrite <- (cni_hi9 B IMG); f_equal; lia
    | lia | exact Hoh | exact How | exact HPB |].
  intros md5 mem5 Hs5 Hfr5 Hgr5 Hhid5 Hv5 HP5.
  destruct HARMS as [(Eres & Eab2 & KEPT & Herr & Hoom) | (H4096 & _)]; [|lia].
  destruct KEPT as (KA & KB & KC & KD & KE & KF).
  pose proof (e5_own_img B IMG) as [Hoi Hol]. unfold kLowMemEnd in Hol.
  assert (KSB : forall a, 0 <= a < 2 ^ 64 -> a <> VAL (A_OBJ 13) ->
    aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W2) memB a).
  { intros a Ha Hne. unfold aview, mbyte. rewrite (Hfr5 (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by exact Ha. exact Hne. }
  assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> a <> VAL (A_OBJ 13) ->
    aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W) mem a).
  { intros a Hi Hno Her Hne. pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow. unfold kLowMemEnd in Hlow.
    rewrite (KSB a ltac:(lia) Hne), (KRB a ltac:(lia) ltac:(lia) ltac:(lia)). exact (KC a Hi Hno Her). }
  assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (cn_S1 D - ASTACK <= a < cn_S1 D) ->
    ~ (cn_S1 D + 24 <= a < cn_S1 D + 32) -> ~ (cn_S1 D + 40 <= a < cn_S1 D + 48) ->
    aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hw H24 H40. rewrite (KSB a ltac:(lia) ltac:(lia)), (KRB a ltac:(lia) H24 H40).
    apply KA; [exact Ha | unfold cn_sp0 in *; lia]. }
  (* ---- THE CUT CN_COPY3 on the refused arm: r2 = 0, own = 1 ---- *)
  replace (BASE + 1336) with (BASE + CN_OFF + 532) by lia.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?mo) _ =>
    change (mkCfg (@YK11.mkst f rg pc mm rom) mo) with (@cn_cfg SEGS f (cn_pc 532) rg mm mo);
    set (regsE := rg); set (mdE := mo) end.
  apply SRr_ret. split; [|exact HP5].
  exists fxk, ly2, S2, Hp, regsE, mem5, mdE, (k + (st_nev S2 - st_nev S)), r1, 0, 1.
  split; [reflexivity|].
  assert (HJ5 : cn_J B ARcfx D ly2 S2 Hp W2 mem5 mdE (k + (st_nev S2 - st_nev S)) 0).
  { apply cn_J_of_x. unfold mdE.
    apply (ajournal_x_pst_write SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) (cni_pst_ok B IMG)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJB); [| exact Hgr5 | exact Hhid5 | exact Hs5].
    intros x Hx. apply Hfr5. intros E. apply Hx. rewrite E. exact e2_own_pst. }
  (* the frame geometry *)
  assert (EF : ly_F ly2 = ly_F ly).
  { pose proof (ajx_ly HJ2) as HL2.
    destruct HL2 as (_ & _ & _ & _ & _ & EF2 & _).
    destruct Hly as (_ & _ & _ & _ & _ & EF1 & _). rewrite EF2, EF1. reflexivity. }
  assert (Eframe : frame_addr ly2 CN_CID (ci_fpos D) = frame_addr ly CN_CID (ci_fpos D))
    by (unfold frame_addr; rewrite EF; reflexivity).
  assert (Eflag : flag_addr ly2 CN_CID (ci_fpos D) = flag_addr ly CN_CID (ci_fpos D))
    by (unfold flag_addr, frame_addr; rewrite EF; reflexivity).
  pose proof (e5_geo_of_base B ARcfx LAWS D fxk ly S Hp W regs mem md k HB) as [G HARc].
  pose proof G as (EFa & Fa0 & Fa1 & Fa32 & Fapp & S16g & Hacg & Hkbg & Hlog & H47g).
  assert (HFB : fs_frame_bytes CN_CID = 512) by (vm_compute; reflexivity).
  assert (Hfa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F in *; congruence).
  assert (KFR : forall a, cn_F D <= a < cn_F D + fs_frame_bytes CN_CID ->
    aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W) mem a).
  { intros a Ha. rewrite HFB in Ha.
    assert (Hne : a <> VAL (A_OBJ 13)).
    { intros Heq. apply (frm_img_x SEGS B ARcfx LAWS ly S Hp W mem md CN_CID (ci_fpos D) (VAL (A_OBJ 13)) HARc
        ltac:(rewrite Hfrs; left; reflexivity)); [| exact Hoi].
      rewrite Hfa, HFB, <- Heq. exact Ha. }
    rewrite (KSB a ltac:(lia) Hne), (KRB a ltac:(lia) ltac:(lia) ltac:(lia)).
    apply (KD CN_CID (ci_fpos D) a); [rewrite Hfrs; left; reflexivity | | intros []].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa, HFB. lia. }
  (* the ledger at the cut, own = 1 *)
  assert (HOWN1 : prh_own W2 mem5 1).
  { split; [|right; reflexivity]. change pi_gz_own_ran_out with 1%nat. rewrite <- (cni_own B IMG).
    apply e5_val_mem1_of_aview; [| lia].
    rewrite Hv5. f_equal. ro_getr. rewrite ro_getr0. vm_compute. reflexivity. }
  assert (KB5 : forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
    aview SEGS (w_H W2) mem5 (b + i) = aview SEGS (w_H W) mem (b + i)).
  { intros b m i Hbm Hi.
    destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hbm) as (_ & Hb4096 & Hbtop & _).
    assert (Hbi : b <= b + i < b + req_size m) by lia.
    assert (Himg : ~ in_img SEGS (b + i)).
    { exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly S Hp W mem md (b + i) HAR
        (or_introl (ex_intro _ b (ex_intro _ m (conj Hbm Hbi)))))). }
    assert (Hne : b + i <> VAL (A_OBJ 13)) by (intros E; apply Himg; rewrite E; exact Hoi).
    rewrite (KSB (b + i) ltac:(lia) Hne), (KRB (b + i) ltac:(lia) ltac:(lia) ltac:(lia)).
    exact (KB b m i Hbm Hi (fun x => x)). }
  assert (L5 : prh_ledger B ly2 S2 Hp W2 mem5 (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) 1).
  { apply (e2_ledger_own ly S Hp W mem ly2 S2 Hp W2 mem5 (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
      (ci_most D) own 1 HLG).
    - intros a Hpst Hne. apply KIMG;
        [exact (proj1 (cni_pst_ok B IMG a Hpst)) | exact (proj2 (cni_pst_ok B IMG a Hpst))
        | exact (cni_pst_errno B IMG a Hpst) | exact Hne].
    - exact HOWN1.
    - intros a kk i Hin Hi. apply prh_mbyte_of_aview.
      destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLG Hin) as (Hk0 & Hblk & _).
      pose proof cf_head_nonneg. unfold prh_head_wide in HW.
      assert (Hkc : 0 <= kk + cf_head) by lia. pose proof (e2_req_ge (kk + cf_head) Hkc) as Hge.
      replace (a - cf_head + i) with ((a - cf_head) + i) by lia.
      apply (KB5 (a - cf_head) (kk + cf_head) i Hblk). lia.
    - intros a kk Hin Hb. rewrite Eab2. exact Hb.
    - apply Permutation_refl. }
  split.
  { (* cn_base *)
    split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ5|].
    split.
    { unfold cn_frame. rewrite Hfrs2. split; [exact Hfrs|]. split; [exact Hnin|].
      split.
      { rewrite Eflag. rewrite <- Hflag. apply rdword_ext. intros q Hq.
        apply KFR. unfold cn_F in *. lia. }
      destruct (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp W2 mem5 mdE CN_CID (ci_fpos D) (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJ5))
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
    split; [unfold regsE; ro_getr; exact V3|]. split; [unfold regsE; ro_getr; exact V4|].
    intros a Hro Hno Herr2.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hsg & _ & Ha) | Hr]; [exists sg; split; [exact Hsg | exact Ha] | exact (@pa_relro_img _ _ PA a Hr)]).
    rewrite (KIMG a Hi Hno Herr2 ltac:(intros ->; exact (cni_pst_rw B IMG _ e2_own_pst Hro))).
    exact (HROD a Hro Hno Herr2). }
  split.
  { unfold cn_regsat, cn_core, cn_s8. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold regsE; ro_getr.
    - exact V2.
    - exact V8.
    - exact V9.
    - exact V18.
    - exact V27.
    - exact V24.
    - exact V19.
    - exact V20.
    - exact V21.
    - exact V23. }
  split.
  { (* the slots: 24 / 40 stored here, 32 / 80 above the call's window and above the ceiling *)
    unfold cn_slotsL in *.
    apply Forall_cons_iff in HSL as [H32 HSL]. apply Forall_cons_iff in HSL as [H80 _]. cbn [fst snd] in H32, H80.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - rewrite <- SL24. apply rdword_ext. intros q Hq. apply KSB; [lia | intros E; rewrite <- E in Hol; lia].
    - rewrite <- H32. apply rdword_ext. intros q Hq. apply KHI; unfold ASTACK, cn_sp0 in *; lia.
    - rewrite <- Eres, <- SL40. apply rdword_ext. intros q Hq. apply KSB; [lia | intros E; rewrite <- E in Hol; lia].
    - rewrite <- H80. apply rdword_ext. intros q Hq. apply KHI; unfold ASTACK, cn_sp0 in *; lia. }
  (* ---- cn_early with the refused copy: rs = [r1; 0], own = 1 ---- *)
  assert (ERS : PresetRoom.rs_live (YGcfRoom.room_of_cf S2) = PresetRoom.rs_live (YGcfRoom.room_of_cf S)).
  { change (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (blocks S2)).
    change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)).
    pose proof (f_equal (map snd) Eab2) as E. unfold ablocks in E. rewrite !map_map in E. cbn [snd] in E. exact E. }
  split; [|exact HHULL2].
  unfold cn_early. split; [exact HHp|].
  split; [exact L5|].
  split.
  { apply Forall_cons; [|apply Forall_cons; [left; reflexivity | apply Forall_nil]].
    apply (e3_copy_keep D ly S Hp W mem ly2 S2 W2 mem5 mdE (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
      (ci_most D) 1 r1 HCP1).
    - intros x Hx. rewrite Eab2. exact Hx.
    - exact (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJ5)).
    - exact L5.
    - intros Hr0 a Ha. destruct HCP1 as [E1 | (Hin1 & _)]; [contradiction|].
      replace a with (r1 + (a - r1)) by lia. apply (KB5 r1 (cn_size D + 16) (a - r1) Hin1).
      pose proof (e2_req_ge (cn_size D + 16) ltac:(lia)). lia. }
  split.
  { unfold cn_cblk in *. cbn [flat_map] in *. rewrite Z.eqb_refl. cbn [app] in *. rewrite Eab2.
    rewrite app_nil_r in HPERM |- *. exact HPERM. }
  split; [exact HROOM2|].
  split.
  { unfold cn_prog in *. rewrite e3_cevsl2.
    assert (E0 : cn_cevsl D [0] = []) by (unfold cn_cevsl, cn_cblk; reflexivity).
    rewrite E0, app_nil_r.
    destruct HRP as [HRP1 HRP2]. split; [rewrite ERS; exact HRP1|].
    intros sm x0 os i H0 hist Hpos Hrun.
    destruct (HRP2 sm x0 os i H0 hist Hpos Hrun) as (hist' & Hpos').
    exists hist'.
    exact (PresetRoomPosKeep.room_pos_keep_alloc_null SEGS B ly S Hp W regsT mem mdT ch1 sm x0 os _ H0 hist'
      (cn_size D + 16) _ trc S2 HPREcf ltac:(unfold cn_size in *; lia) ltac:(unfold cn_size in *; lia)
      HTRc ltac:(rewrite <- Eres in Hpn; rewrite (proj2 Hpn eq_refl) in Hpath; exact Hpath) Hpos'). }
  split.
  { pose proof (blocks_bytes_bsum B ly2 S2) as EB2. pose proof (blocks_bytes_bsum B ly S) as EB.
    rewrite EB2, Eab2, <- EB. cbn [length] in HBUD |- *. lia. }
  split; [right; reflexivity|].
  split; [rewrite (cni_own B IMG); exact (proj1 HOWN1)|].
  split; [intros Hc; discriminate Hc|].
  (* the refused copy: CNO-COPY's refusal is dead at a consumer run. Copy 2's __wrap_malloc returned NULL on a
     granted path (the rule's apath / gflag) at the cut's own state S, after the granted copies of [r1] (cn_prog) *)
  intros _.
  apply (e2_cdead B D [r1] S HRP ltac:(unfold cn_cblk; cbn [flat_map]; destruct (r1 =? 0); cbn; lia)
    (WFL _ _ _ _ _ _ HAR)).
  left. exists (cn_size D + 16), (call_trace ly (pc_malloc_ra0 (as_code B)) regsT ch1), trc, S2.
  split; [|exact Hgf]. rewrite <- (proj2 Hpn Eres). exact Hpath. }
(* ---- THE GRANTED COPY: res <> 0, the new block (res, size + 16); +480 mv s6, a0; +484 beqz s4; +488..500 the
   memcpy (ACPY); +504..516 the 16-byte 0x32 padding (ASET); +520 j to the cut ---- *)
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
(* the old blocks' bytes at the stores' memory are the CA3 entry's (the call kept them, the stores are on the stack) *)
assert (KBB : forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
  aview SEGS (w_H W2) memB (b + i) = aview SEGS (w_H W) mem (b + i)).
{ intros b m i Hbm Hi.
  destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hbm) as (_ & Hb4096 & Hbtop & _).
  pose proof (HAPART _ _ Hbm) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  rewrite (KRB (b + i) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply (KB b m i Hbm Hi). cbv beta. lia. }
(* the ledger at the stores' memory, own unchanged *)
assert (KI1 : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) memB a = aview SEGS (w_H W) mem a).
{ intros a Hp0. pose proof (@pa_segs_low _ _ PA _ (proj1 (cni_pst_ok B IMG a Hp0))) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (KRB a ltac:(lia) ltac:(lia) ltac:(lia)).
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
(* the source *)
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
{ intros Wc memc mdc pk cnt fl rn mo ow HARc HLc Hs0.
  apply (e2_src_shadow ly2 S2 Hp Wc memc mdc (ci_Lam D) pk cnt fl rn mo ow _ _ HARc HLc Hs0).
  destruct (HHOME Hs0) as [Hk | (b & m & Hin & Hbn & Hb & Hm)]; [left; exact Hk | right].
  exists b, m. split; [|split; [rewrite HHp; exact Hbn | lia]].
  apply (e2_blocks_in D ly2 S2 Hp W2 memB _ _ _ _ (cn_J_of_x B ARcfx _ _ _ _ _ _ _ _ 0 HJB) Hin). lia. }
assert (DSTH : forall Wc memc mdc pk cnt fl rn mo ow d n, ARcfx ly2 S2 Hp Wc memc mdc ->
  prh_ledger B ly2 S2 Hp Wc memc (ci_Lam D) pk cnt fl rn mo ow -> 0 < n -> res <= d -> d + n <= res + (cn_size D + 16) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF d n /\ shadow_hull_vis (aview SEGS (w_H Wc) memc) d n).
{ intros Wc memc mdc pk cnt fl rn mo ow d n HARc HLc Hn Hd1 Hd2.
  apply (e2_src_shadow ly2 S2 Hp Wc memc mdc (ci_Lam D) pk cnt fl rn mo ow d n HARc HLc Hn).
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
(* the frame geometry *)
assert (EF : ly_F ly2 = ly_F ly).
{ pose proof (ajx_ly HJ2) as HL2.
  destruct HL2 as (_ & _ & _ & _ & _ & EF2 & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF1 & _). rewrite EF2, EF1. reflexivity. }
assert (Eframe : frame_addr ly2 CN_CID (ci_fpos D) = frame_addr ly CN_CID (ci_fpos D))
  by (unfold frame_addr; rewrite EF; reflexivity).
assert (Eflag : flag_addr ly2 CN_CID (ci_fpos D) = flag_addr ly CN_CID (ci_fpos D))
  by (unfold flag_addr, frame_addr; rewrite EF; reflexivity).
pose proof (e5_geo_of_base B ARcfx LAWS D fxk ly S Hp W regs mem md k HB) as [G HARc].
pose proof G as (EFa & Fa0 & Fa1 & Fa32 & Fapp & S16g & Hacg & Hkbg & Hlog & H47g).
assert (HFB : fs_frame_bytes CN_CID = 512) by (vm_compute; reflexivity).
assert (Hfa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F in *; congruence).
(* +480 mv s6, a0 *)
apply (cn_hs_addi W2 fxk _ memB _ _ 480 484 22%bv 10%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X5.
set (regsG := regupd regs2 22%bv (v_addi (getr regs2 10%bv) 0)).
assert (G22 : getr regsG 22%bv = w64 res).
{ unfold regsG. ro_getr. rewrite V10, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (GR : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 27%bv] ->
  getr regsG r = getr regs2 r).
{ intros r Hr. cbn in Hr. unfold regsG.
  repeat (destruct Hr as [<- | Hr]; [ro_getr; reflexivity |]). destruct Hr. }
assert (TAIL : forall regsX memX mdX,
  cn_J B ARcfx D ly2 S2 Hp W2 memX mdX (k + (st_nev S2 - st_nev S)) 0 -> P memX ->
  (forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 27%bv] ->
     getr regsX r = getr regs2 r) ->
  getr regsX 22%bv = w64 res ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + cn_size D) -> ~ (cn_S1 D - ESTACK <= a < cn_S1 D) ->
     aview SEGS (w_H W2) memX a = aview SEGS (w_H W2) memB a) ->
  (forall i, 0 <= i < cn_size D ->
     aview SEGS (w_H W2) memX (res + i) = aview SEGS (w_H W2) memB (ci_data D + i)) ->
  SRr SEGS W2 (@cn_cfg SEGS fxk (cn_pc 504) regsX memX mdX)
    (fun W' c' => cn_ex_copy3 (fx := fx) B ARcfx D W' c' /\ P (ms_mem (cfg_ms c')))).
{ intros regsX memX mdX HJX HPX RX RX22 KX CX.
  pose proof HJX as HJXc. apply e_J0 in HJXc.
  assert (LX : prh_ledger B ly2 S2 Hp W2 memX (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own).
  { apply (e2_ledger_blk ly2 S2 Hp W2 memB _ memX _ _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJB) L1 HinNB HresHp).
    intros a Ha Hn. apply KX; lia. }
  (* +504 add a0, s6, s4; +508 li a1, 0x32; +512 li a2, 16; +516 jal __asan_memset *)
  apply (e2_hs_add W2 fxk regsX memX mdX _ 504 508 10%bv 22%bv 20%bv);
    [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X10.
  apply (cn_hs_addi W2 fxk _ memX _ _ 508 512 11%bv 0%bv 50); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X11.
  apply (cn_hs_addi W2 fxk _ memX _ _ 512 516 12%bv 0%bv 16); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X12.
  apply (cn_hs_call W2 fxk _ memX _ _ 516 520 AS___asan_memset); [vm_compute; reflexivity | lia | reflexivity |].
  intros X13.
  lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg _ ?mo) _ => set (regsS := rg); set (mdS := mo) end.
  assert (S10 : getr regsS 10%bv = w64 (res + cn_size D)).
  { unfold regsS. ro_getr. rewrite RX22, (RX 20%bv ltac:(ro_in)), V20.
    apply e2_vadd; lia. }
  assert (S11 : getr regsS 11%bv = w64 50) by (unfold regsS; ro_getr; rewrite ro_getr0; apply (e2_addi 0 50); lia).
  assert (S12 : getr regsS 12%bv = w64 16) by (unfold regsS; ro_getr; rewrite ro_getr0; apply (e2_addi 0 16); lia).
  assert (SR1 : getr regsS 1%bv = w64 (cn_pc 520)) by (unfold regsS; ro_getr; reflexivity).
  assert (SR3 : getr regsS 3%bv = w64 (as_gp B))
    by (unfold regsS; ro_getr; rewrite (RX 3%bv ltac:(ro_in)), V3; exact Hgp0).
  assert (SR4 : getr regsS 4%bv = w64 (as_tp B))
    by (unfold regsS; ro_getr; rewrite (RX 4%bv ltac:(ro_in)), V4; exact Htp0).
  assert (SSP : spZ regsS = cn_sp0 D + (cn_S1 D - cn_sp0 D)).
  { unfold spZ, regsS. ro_getr. rewrite (RX 2%bv ltac:(ro_in)), V2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
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
      [(CN_CID, ci_fpos D)] ly2 S2 Hp mdS (k + (st_nev S2 - st_nev S)) (res + cn_size D) 50 16
      (cn_S1 D - cn_sp0 D) (w64 (cn_pc 520))).
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
  change (mkCfg (@YK11.mkst fxk regs3 (w64 (cn_pc 520)) mem3 (YK11.seg_rom SEGS)) md3)
    with (@cn_cfg SEGS fxk (cn_pc 520) regs3 mem3 md3).
  (* +520 j 0xc -> +532, the cut *)
  apply (cn_hs_j W2 fxk regs3 mem3 md3 _ 520 532 12); [vm_compute; reflexivity | lia | reflexivity | lia |].
  intros X14.
  set (mdE := with_vm_backing (m_vm_lazy md3) X14 md3).
  apply SRr_ret. split; [|exact (PCALL _ _ HMN3 HPX)].
  exists fxk, ly2, S2, Hp, regs3, mem3, mdE, (k + (st_nev S2 - st_nev S)), r1, res, own.
  split; [reflexivity|].
  assert (HJE : cn_J B ARcfx D ly2 S2 Hp W2 mem3 mdE (k + (st_nev S2 - st_nev S)) 0).
  { apply cn_J_of_x. unfold mdE.
    exact (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X14 HJ3). }
  assert (KE3 : forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + (cn_size D + 16)) ->
    ~ (cn_S1 D - ESTACK <= a < cn_S1 D) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) memB a).
  { intros a Ha Hn Hw. rewrite (HKP3 a Ha ltac:(lia) ltac:(lia)). apply KX; lia. }
  assert (KHI3 : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (cn_S1 D - ASTACK <= a < cn_S1 D) ->
    ~ (cn_S1 D + 24 <= a < cn_S1 D + 32) -> ~ (cn_S1 D + 40 <= a < cn_S1 D + 48) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hw H24 H40. rewrite (KE3 a ltac:(lia) ltac:(lia) ltac:(unfold ASTACK, ESTACK in *; lia)).
    rewrite (KRB a ltac:(lia) H24 H40). apply KA; [exact Ha | unfold cn_sp0 in *; lia]. }
  assert (KIMG3 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Hi Hno Her. pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow. unfold kLowMemEnd in Hlow.
    assert (Hnb : ~ (res <= a < res + (cn_size D + 16))).
    { intros Hr. assert (Hr' : res <= a < res + req_size (cn_size D + 16)) by lia.
      exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly2 S2 Hp W2 _ _ a (ajx_ar HJ2)
        (or_introl (ex_intro _ res (ex_intro _ (cn_size D + 16) (conj HinNB Hr'))))) Hi). }
    rewrite (KE3 a ltac:(lia) Hnb ltac:(lia)), (KRB a ltac:(lia) ltac:(lia) ltac:(lia)). exact (KC a Hi Hno Her). }
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
    rewrite (KE3 a ltac:(lia) ltac:(lia) ltac:(lia)), (KRB a ltac:(lia) ltac:(lia) ltac:(lia)).
    apply (KD CN_CID (ci_fpos D) a); [rewrite Hfrs; left; reflexivity | | cbv beta; lia].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa, HFB. lia. }
  assert (L3 : prh_ledger B ly2 S2 Hp W2 mem3 (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own).
  { apply (e2_ledger_blk ly2 S2 Hp W2 memX _ mem3 _ _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJXc) LX HinNB HresHp).
    intros a Ha Hn. apply HKP3; lia. }
  assert (G3R : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 27%bv] ->
    getr regs3 r = getr regs2 r).
  { intros r Hr. rewrite <- (RX r Hr). cbn in Hr.
    repeat (destruct Hr as [<- | Hr];
      [lazymatch goal with |- getr _ ?r = _ =>
         rewrite (e5_pres _ _ r HPR3 ltac:(apply e5_cs; vm_compute; reflexivity)) end;
       unfold regsS; ro_getr; reflexivity |]).
    destruct Hr. }
  split.
  { (* cn_base *)
    split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJE|].
    split.
    { unfold cn_frame. rewrite Hfrs2. split; [exact Hfrs|]. split; [exact Hnin|].
      split.
      { rewrite Eflag. rewrite <- Hflag. apply rdword_ext. intros q Hq.
        apply KFR3. unfold cn_F in *. lia. }
      destruct (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp W2 mem3 mdE CN_CID (ci_fpos D) (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE))
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
    split; [rewrite (G3R 3%bv ltac:(ro_in)); exact V3|].
    split; [rewrite (G3R 4%bv ltac:(ro_in)); exact V4|].
    intros a Hro Hno Herr2.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hsg & _ & Ha) | Hr]; [exists sg; split; [exact Hsg | exact Ha] | exact (@pa_relro_img _ _ PA a Hr)]).
    rewrite (KIMG3 a Hi Hno Herr2).
    exact (HROD a Hro Hno Herr2). }
  split.
  { unfold cn_regsat, cn_core, cn_s8. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; rewrite G3R by ro_in.
    - exact V2.
    - exact V8.
    - exact V9.
    - exact V18.
    - exact V27.
    - exact V24.
    - exact V19.
    - exact V20.
    - exact V21.
    - exact V23. }
  split.
  { unfold cn_slotsL in *.
    apply Forall_cons_iff in HSL as [H32 HSL]. apply Forall_cons_iff in HSL as [H80 _]. cbn [fst snd] in H32, H80.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - rewrite <- SL24. apply rdword_ext. intros q Hq. apply KE3; unfold ESTACK in *; lia.
    - rewrite <- H32. apply rdword_ext. intros q Hq. apply KHI3; unfold ASTACK, cn_sp0 in *; lia.
    - rewrite <- SL40. apply rdword_ext. intros q Hq. apply KE3; unfold ESTACK in *; lia.
    - rewrite <- H80. apply rdword_ext. intros q Hq. apply KHI3; unfold ASTACK, cn_sp0 in *; lia. }
  (* ---- cn_early with the granted copy: rs = [r1; res], own unchanged ---- *)
  pose proof L3 as L3c. apply prh_ledger_iff in L3c as [HG3 _].
  destruct HG3 as (_ & _ & _ & _ & _ & _ & HO3 & _).
  split; [|exact HHULL2].
  unfold cn_early. split; [exact HHp|].
  split; [exact L3|].
  split.
  { apply Forall_cons.
    { apply (e3_copy_keep D ly S Hp W mem ly2 S2 W2 mem3 mdE (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
        (ci_most D) own r1 HCP1).
      - intros x Hx. rewrite Eab2. apply in_or_app. left. exact Hx.
      - exact (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE)).
      - exact L3.
      - intros Hr0 a Ha. destruct HCP1 as [E1 | (Hin1 & _)]; [contradiction|].
        pose proof (HAPART _ _ Hin1) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
        destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hin1) as (_ & Hb4096 & Hbtop & _).
        rewrite (KE3 a ltac:(lia) ltac:(lia) ltac:(lia)).
        replace a with (r1 + (a - r1)) by lia. apply (KBB r1 (cn_size D + 16) (a - r1) Hin1). lia. }
    apply Forall_cons; [|apply Forall_nil]. right.
    split; [exact HinNB|]. split; [exact HresHp|].
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
      + destruct (DSTH W2 mem3 mdE _ _ _ _ _ _ res (cn_size D) (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE)) L3 ltac:(lia) ltac:(lia) ltac:(lia))
          as [RA3 HV3].
        unfold cn_size in RA3, HV3. split; [exact RA3 | intros _; exact HV3]. }
  split.
  { unfold cn_cblk in *. cbn [flat_map] in *. rewrite (proj2 (Z.eqb_neq res 0) Hnz). rewrite Eab2.
    rewrite app_nil_r in HPERM. rewrite !app_nil_r.
    apply Permutation_trans with ((if r1 =? 0 then [] else [(r1, cn_size D + 16)]) ++ ablocks B (ci_ly D) (ci_S D)
      ++ [(res, cn_size D + 16)]).
    - rewrite (app_assoc (if r1 =? 0 then [] else [(r1, cn_size D + 16)]) (ablocks B (ci_ly D) (ci_S D))
        [(res, cn_size D + 16)]).
      apply Permutation_app_tail. exact HPERM.
    - rewrite <- (app_assoc (if r1 =? 0 then [] else [(r1, cn_size D + 16)]) [(res, cn_size D + 16)]
        (ablocks B (ci_ly D) (ci_S D))).
      apply Permutation_app_head. apply Permutation_app_comm. }
  split; [exact HROOM2|].
  split.
  { unfold cn_prog in *. rewrite e3_cevsl2.
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
        ltac:(unfold cn_size in *; lia) HTRc Hpath (fun E => Hnz (proj1 Hpn E)) Hpos').
      apply (proj1 (prh_run_at_one sm x0 os _ _)). exact Hrun2. }
  split.
  { pose proof (blocks_bytes_bsum B ly2 S2) as EB2. pose proof (blocks_bytes_bsum B ly S) as EB.
    rewrite EB2, Eab2, bsum_app, <- EB. change (bsum [(res, cn_size D + 16)]) with (cn_size D + 16 + 0).
    cbn [length] in HBUD |- *. lia. }
  split; [exact HOWN01|].
  split; [rewrite (cni_own B IMG); exact (proj1 HO3)|].
  split; [|exact HCD].
  intros Ho0. pose proof (HOWN0 Ho0) as HF. apply Forall_cons_iff in HF as [Hr1n _].
  apply Forall_cons; [exact Hr1n | apply Forall_cons; [exact Hnz | apply Forall_nil]]. }
(* +484 beqz s4 -> +504 (size = 0) / +488 *)
apply (cn_hs_beqz W2 fxk regsG memB _ _ 484 20%bv 20 504 488 (cn_size D =? 0));
  [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | |].
{ rewrite ro_getr0, (GR 20%bv ltac:(ro_in)), V20. apply ro_c_eq0. lia. }
intros X6.
destruct (Z.eqb_spec (cn_size D) 0) as [Hs0 | Hs0].
{ (* size = 0: no copy *)
  apply (TAIL regsG memB _).
  - apply cn_J_of_x. exact (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X6
      (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5
      (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4 HJB))).
  - exact HPB.
  - exact GR.
  - exact G22.
  - intros a _ _ _. reflexivity.
  - intros i Hi. lia. }
(* +488 mv a0, s6; +492 mv a1, s7; +496 mv a2, s4; +500 jal __asan_memcpy *)
assert (Hs1 : 0 < cn_size D) by lia.
apply (cn_hs_addi W2 fxk _ memB _ _ 488 492 10%bv 22%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X7.
apply (cn_hs_addi W2 fxk _ memB _ _ 492 496 11%bv 23%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X8.
apply (cn_hs_addi W2 fxk _ memB _ _ 496 500 12%bv 20%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X9.
apply (cn_hs_call W2 fxk _ memB _ _ 500 504 AS___asan_memcpy); [vm_compute; reflexivity | lia | reflexivity |].
intros X10.
lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg _ ?mo) _ => set (regsC := rg); set (mdC := mo) end.
assert (C10 : getr regsC 10%bv = w64 res).
{ unfold regsC. ro_getr. rewrite G22, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (C11 : getr regsC 11%bv = w64 (ci_data D)).
{ unfold regsC. ro_getr. rewrite (GR 23%bv ltac:(ro_in)), V23, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (C12 : getr regsC 12%bv = w64 (cn_size D)).
{ unfold regsC. ro_getr. rewrite (GR 20%bv ltac:(ro_in)), V20, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (CR1 : getr regsC 1%bv = w64 (cn_pc 504)) by (unfold regsC; ro_getr; reflexivity).
assert (CR3 : getr regsC 3%bv = w64 (as_gp B)) by (unfold regsC; ro_getr; rewrite (GR 3%bv ltac:(ro_in)), V3; exact Hgp0).
assert (CR4 : getr regsC 4%bv = w64 (as_tp B)) by (unfold regsC; ro_getr; rewrite (GR 4%bv ltac:(ro_in)), V4; exact Htp0).
assert (CSP : spZ regsC = cn_sp0 D + (cn_S1 D - cn_sp0 D)).
{ unfold spZ, regsC. ro_getr. rewrite (GR 2%bv ltac:(ro_in)), V2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
pose proof (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X10
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X9
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X8
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X6
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4 HJB)))))))
  as HJC.
destruct (SRCH W2 memB _ _ _ _ _ _ _ (ajx_ar HJC) L1 Hs1) as [SRA SHV].
destruct (DSTH W2 memB _ _ _ _ _ _ _ res (cn_size D) (ajx_ar HJC) L1 Hs1 ltac:(lia) ltac:(lia)) as [DRA DHV].
unfold cn_cfg. unfold w64 at 1.
eapply SRr_bind.
{ apply (aj_intrin_at_xm (fx := fxk) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) OCpy
    (SIGMA AS___asan_memcpy) (ACPY fxk)
    W2 regsC memB STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly2 S2 Hp mdC (k + (st_nev S2 - st_nev S)) res (ci_data D) (cn_size D)
    (cn_S1 D - cn_sp0 D) (w64 (cn_pc 504))).
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
change (mkCfg (@YK11.mkst fxk regsP (w64 (cn_pc 504)) memP (YK11.seg_rom SEGS)) mdP)
  with (@cn_cfg SEGS fxk (cn_pc 504) regsP memP mdP).
apply (TAIL regsP memP mdP).
- apply cn_J_of_x. exact HJP.
- exact (PCALL _ _ HMNP HPB).
- intros r Hr. rewrite <- (GR r Hr). cbn in Hr.
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?r = _ =>
       rewrite (e5_pres _ _ r HPRP ltac:(apply e5_cs; vm_compute; reflexivity)) end;
     unfold regsC; ro_getr; reflexivity |]).
  destruct Hr.
- rewrite (e5_pres _ _ 22%bv HPRP ltac:(apply e5_cs; vm_compute; reflexivity)). unfold regsC. ro_getr. exact G22.
- intros a Ha Hn Hw. apply HKPP; [exact Ha | exact Hn | lia].
- intros i Hi. exact (HBYP i Hi).
Qed.

End e3.

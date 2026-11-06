(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT PRO of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x830dc .. 0x831f4, 71 instructions, no call), in the form of this lane's
   lib/A/W_send_line_entry.v (a segment into a loop head) and of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v.  The statement is W_drain_cx.v dr_pro_stmt.

   The prologue saves the 13 callee-saved registers at 232(sp) .. 328(sp) of its 336-byte frame, keeps the
   relay entry s in s6 and its field addresses s->buf / s->used / s->cap in s10 / s11 / s9, spills
   &s->npartial, &s->overlong, &s->held to 208(sp) / 96(sp) / 128(sp), takes g_s by PAddHi (A_OBJ 22) into
   s2 with g_s >> 3 in s1 and (g_s + 4) >> 3 in s0, loads the shadow base from the GOT (A_OBJ 0 -> A_OBJ 32)
   into s5, and writes the shifted field addresses of g_s and the shadow addresses of s's cells into the
   frame.  No call, no shadow check, no store outside [sp0 - 336, sp0): every representation the outer loop's
   head carries lies below alloc_ceiling + 8 (a live block, the image band) and moves across the stores. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_pro.v, with its module paths, module names and numbers changed; 1682 of its 1766 lines of code are new or changed and 1187 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PjGetB.v, with its module paths and module names changed; 213 of its 253 lines of code are new or changed and 1726 lines of the source are left out. *)
(* fuzz_preset, image B' (#102): check_as_written's Checks segment WB5 (B' 0x82038 -> 0x82058: `seqz a0, s0`,
   `slti a1, s2, 0`, `xori a1, a1, 1`, `bne a0, a1` to the abort tail, `snez a1, s2`, `and a0, a0, a1`, `bnez a0` to the
   abort tail, `mv s1, zero`) from cut_ck to cut_end with r = 0 and own = 0 (Caw102B.v); re-proved by
   the #102 re-walk, B'; re-fitted to the re-keyed base by that re-walk.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   BASE OF RECORD: the kit's cut of the #102 batch, preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) (the cut + this row's caw
   B' files; prepared at preset-tree-at-2026-10-30T02-53-02Z.tsv (sha256 477c088a7ad3; internal record) on the batch tip preset-tree-at-2026-10-30T02-01-18Z.tsv (sha256 a12cae64b2b5; internal record)), this row's lib/B/Prog/Caw102B.v
   (statements of blob 5a8082469eb1, unchanged here); the cut's kit texts by path: PRH_Base.v
   ef7c8ca98529, PRH_FnCheck.v c40cf3fdcd2a (tcheck_as_written_specX :832-902; no text is called in this segment),
   the P'' journal of lib/Reusable/YCbqG.v 219748197d6b (carried here as it is, never destructed).
   WHAT CHANGED (on that batch base) and WHY: the batch text has no run-word list DW (the base dropped
   cawB's c_DW; never read here) and takes the ROOM COUNTS as entry premises after room_live_cf (:862-863), so
   caw_pre now has 27 conjuncts (with the hull budget and HPOS that follow them, Caw102B.v:139-165) and is read BY NAME: the rc range is the base's projection caw_pre_rc (formerly a
   positional destruct). cut_end's r = 1 arm gains the text's OUTCOME exclusion caw_dead C; this segment builds only
   the r = 0 arm, which is unchanged. caw_WB5's statement is unchanged.
   EARLIER (base Caw102B.v blob d5668ec173d5, kit text preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record)): that text's tcheck_as_written_specX binds no run position at entry (the
   post-implication form), so every cut carries THE PROGRESS FACT caw_prog C E S3 (for any entry position whose next
   events are E, a position i + length E at S3), cut_ck at caw_evs C, cut_end per arm (r = 0 with caw_evs C). The
   room counts (caw_cnt C) are not read: the seven steps make no alloc / free step. cut_ck's `caw_ledger C ly3 S3 Hp3
   W3 mem3 0` is CARRIED to cut_end at own = 0, and cut_ck's progress fact `caw_prog C (caw_evs C) S3` is cut_end's
   r = 0 arm as it is (no event since the cut): the seven steps are hand steps that write no memory
   (frame_of_read_only, EM1 .. EM3), so the world W3, the memory mem3 and ly3 / S3 / Hp3 at 0x82058 are cut_ck's.
   Statements take the entry float state explicitly (fx := fx).
   SECTION HYPOTHESES: none. Variable B (the walk's asyms, an instance binding; owner the top, Caw102B_Top.v). The
   lemma premise srr_inv_laws SEGS P (owner: the top, which instantiates P). No named argument of this file's own, no
   image fact.
   caw_WB5R, beside caw_WB5 (whose statement is unchanged): the same seven steps from cut_ckR to caw_K_endR at
   RW := YA0nH.wle' SEGS RZ_cf, the world relation past the scratch's free. The journal is caw_JR at RW; the runs are
   YC1fPx.v's R runners paj_run_x_invR / paj_run_to_x_invR (RW is reflexive and transitive: YA0nH.wle'_refl /
   wle'_trans), the two branches YSRrG.paj_branchR at RW. Its premises are caw_WB5's.
   Generic P, abstract; call-free (srr_inv_laws only). THE TWO ABORT EDGES (0x82044
   and 0x82050, both to the `jal __asan_handle_no_return` at 0x82080) are REFUTED, never walked: each branch's
   condition is false under cut_ck's caw_want (want = -1 with rc <> 0, or want = 0 with rc = 0), computed through
   YP0e.U_SAlu / U_SLit from the atoms' values (cawC_s0_ne0 for rc <> 0). Structure: H2CawF.v's compare (old caw A).
   Numerals: register numbers (WORD), 2 ^ 64 / 2 ^ 31 (WORD: the machine word, rc's int range). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YG0lawscf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Caw102B.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

(* the seat: every register its own atom, atom 32 the shadow base (no memory is read) *)
Definition cawC_E (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Lemma cawC_E_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cawC_E regs) n = getr regs r.
Proof.
intros regs n r Hn. pose proof (u5_range r) as Hr. unfold cawC_E.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn).
Qed.
(* s0 = rc sign-extended: its unsigned value is 0 exactly when rc is *)
Lemma cawC_s0_ne0 : forall rc0, - 2 ^ 31 <= rc0 < 2 ^ 31 -> rc0 <> 0 -> 1 <= bv_unsigned (w64 rc0) < 2 ^ 64.
Proof.
intros rc0 Hr Hn. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
destruct (Z_le_gt_dec 0 rc0) as [Hp|Hm].
- rewrite Z.mod_small by lia. lia.
- replace (rc0 mod 2 ^ 64) with (rc0 + 2 ^ 64) by (rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia;
    rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity). lia.
Qed.

Section f.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B).

(* WB5 Checks: from cut_ck, the two property checks pass (their abort edges are refuted) and s1 := 0, so cut_end holds
   with r = 0 and own = 0 *)
Lemma caw_WB5 : forall C P Q, srr_inv_laws SEGS P -> caw_pre (fx := fx) B C -> caw_K_end (fx := fx) B C P Q ->
  caw_K_ck (fx := fx) B C P Q.
Proof.
intros C P Q PLAW Hpre Kend fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want Hcut HPM.
destruct Hcut as (Hbase & R18 & Hw & Eab & Hrp & HL).
pose proof Hbase as (Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM).
pose proof (caw_pre_rc (fx := fx) B C Hpre) as Hrc.
set (E := cawC_E regs3).
assert (HS : st_ok_pi (fx := fy) SEGS VAL E (mkSS (AF_cawB + CAWB_CK) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (AF_cawB + CAWB_CK))) mem3 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. unfold cawC_E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. exact I.
  - split; [exact I | split; exact I]. }
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cawC_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 SHADOW_OFF]) E)
  by (subst E; unfold cawC_E; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
(* the atoms' values: s0 = rc, s2 = want *)
assert (E8 : ew E 8 = w64 (c_rc C)) by (subst E; rewrite (cawC_E_reg regs3 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = w64 want) by (subst E; rewrite (cawC_E_reg regs3 18 18%bv eq_refl); exact R18).
assert (U8 : U E (SOff 8 0) = bv_unsigned (w64 (c_rc C))).
{ rewrite U_SOff, E8, Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 (w64 (c_rc C))) as H.
  unfold M64. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. }
assert (U18 : U E (SOff 18 0) = bv_unsigned (w64 want)).
{ rewrite U_SOff, E18, Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 (w64 want)) as H.
  unfold M64. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. }
(* the three values the two branches compare, in either arm of caw_want *)
assert (Va : exists a1 b1 c1, U E (SAlu ALU_SLTU (SOff 8 0) (SLit 1)) = a1 /\
  U E (SAlu ALU_XOR (SAlu ALU_SLT (SOff 18 0) (SLit 0)) (SLit 1)) = b1 /\
  U E (SAlu ALU_SLTU (SLit 0) (SOff 18 0)) = c1 /\ a1 = b1 /\ Z.land a1 c1 = 0 /\ 0 <= a1 <= 1 /\ 0 <= c1 <= 1).
{ destruct Hw as [[-> Hrcn] | [-> Hrc0]].
  - pose proof (cawC_s0_ne0 (c_rc C) Hrc Hrcn) as Hs.
    exists 0, 0, 1. split; [|split; [|split]].
    + rewrite U_SAlu, U_SLit, U8. cbn [zalu_raw]. replace (bv_unsigned (w64 (c_rc C)) <? zcanon 1) with false.
      * reflexivity.
      * symmetry. apply Z.ltb_ge. change (zcanon 1) with 1. lia.
    + rewrite !U_SAlu, !U_SLit, U18. vm_compute. reflexivity.
    + rewrite U_SAlu, U_SLit, U18. vm_compute. reflexivity.
    + split; [reflexivity|]. split; [reflexivity|]. lia.
  - exists 1, 1, 0. split; [|split; [|split]].
    + rewrite U_SAlu, U_SLit, U8, Hrc0. vm_compute. reflexivity.
    + rewrite !U_SAlu, !U_SLit, U18. vm_compute. reflexivity.
    + rewrite U_SAlu, U_SLit, U18. vm_compute. reflexivity.
    + split; [reflexivity|]. split; [reflexivity|]. lia. }
destruct Va as (a1 & b1 & c1 & Ua & Ub & Uc & Eab1 & Eand & Ha1 & Hc1).
pose (RUN := @paj_run_x_inv fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (BR := @paj_branch fy rc B_prog_listing PA).
unfold caw_cfg.
(* seqz / slti / xori; stop at `bne a0, a1` (0x82044) *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_END).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM1 end. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ (* 0x82044 taken: the abort edge (rc == 0) != (want >= 0) is refuted *)
  exfalso. rewrite branch_ne_U, Ua, Ub, Eab1, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* snez / and; stop at `bnez a0` (0x82050) *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_END).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM2 end. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ (* 0x82050 taken: the abort edge rc == 0 && want != 0 is refuted *)
  exfalso. rewrite branch_ne_U, U_SAlu, Ua, Uc, U_SLit in Hc. cbn [zalu_raw] in Hc. rewrite Eand in Hc.
  vm_compute in Hc. discriminate Hc. }
clear Hc.
(* mv s1, zero; stop at 0x82058 *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_END).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM3 end. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  assert (Emem : ms_mem msn = mem3) by (rewrite EM3, EM2, EM1; reflexivity);
  rewrite (st_ok_pi_restrict_mkst (fx := fy) (L := B_prog_listing) (PI := PA) (w_H W3) E _ msn HS eq_refl) end.
cbn [ss_pc].
prreg HS (9%bv : bv 5) Q9.
assert (HKP : forall rr, In rr [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms1) rr = getr regs3 rr).
{ eapply (regs_kept_of_st_ok_pi (fx := fy) (L := B_prog_listing) (PI := PA) E _ (restrict (w_H W3) ms1) regs3
    [Z_to_bv 64 SHADOW_OFF]); [exact HS | exact HAE | vm_compute; reflexivity]. }
change (AF_cawB + CAWB_CK + 52) with (AF_cawB + CAWB_END).
apply (Kend fy ly3 S3 Hp3 W3 (ms_regs ms1) (ms_mem ms1) _ k 0 0); [|exact HPM].
rewrite Emem in HJ |- *.
split; [|split; [|split; [right; split; [reflexivity | split; [reflexivity | exact Hrp]] |
  split; [exact Eab | exact HL]]]].
- split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ|].
  split; [intros rr Hr; rewrite <- (Hk rr Hr); apply HKP; cbn [In] in Hr |- *; tauto|].
  split; [unfold spZ; rewrite (HKP 2%bv) by (left; reflexivity); exact Hsp|].
  split; [rewrite (HKP 8%bv) by (cbn; tauto); exact R8|].
  split; [exact HSV|]. split; [exact EHp | exact HROOM].
- rewrite Q9. reflexivity.
Qed.

(* the world relation past the scratch's free (the re-hide's zone) *)
#[local] Abbreviation RW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* caw_WB5 over RW: cut_ckR's journal is at RW, the runs are the R runners, the branches YSRrG.paj_branchR, the
   arrival at 0x82058 is cut_endR *)
Lemma caw_WB5R : forall C P Q, srr_inv_laws SEGS P -> caw_pre (fx := fx) B C ->
  caw_K_endR (fx := fx) B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) C P Q ->
  caw_K_ckR (fx := fx) B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) C P Q.
Proof.
intros C P Q PLAW Hpre Kend fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want Hcut HPM.
destruct Hcut as (Hbase & R18 & Hw & Eab & Hrp & HL).
pose proof Hbase as (Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM).
unfold caw_JR in HJ.
pose proof (caw_pre_rc (fx := fx) B C Hpre) as Hrc.
set (E := cawC_E regs3).
assert (HS : st_ok_pi (fx := fy) SEGS VAL E (mkSS (AF_cawB + CAWB_CK) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (AF_cawB + CAWB_CK))) mem3 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. unfold cawC_E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. exact I.
  - split; [exact I | split; exact I]. }
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cawC_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 SHADOW_OFF]) E)
  by (subst E; unfold cawC_E; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
(* the atoms' values: s0 = rc, s2 = want *)
assert (E8 : ew E 8 = w64 (c_rc C)) by (subst E; rewrite (cawC_E_reg regs3 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = w64 want) by (subst E; rewrite (cawC_E_reg regs3 18 18%bv eq_refl); exact R18).
assert (U8 : U E (SOff 8 0) = bv_unsigned (w64 (c_rc C))).
{ rewrite U_SOff, E8, Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 (w64 (c_rc C))) as H.
  unfold M64. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. }
assert (U18 : U E (SOff 18 0) = bv_unsigned (w64 want)).
{ rewrite U_SOff, E18, Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 (w64 want)) as H.
  unfold M64. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. }
(* the three values the two branches compare, in either arm of caw_want *)
assert (Va : exists a1 b1 c1, U E (SAlu ALU_SLTU (SOff 8 0) (SLit 1)) = a1 /\
  U E (SAlu ALU_XOR (SAlu ALU_SLT (SOff 18 0) (SLit 0)) (SLit 1)) = b1 /\
  U E (SAlu ALU_SLTU (SLit 0) (SOff 18 0)) = c1 /\ a1 = b1 /\ Z.land a1 c1 = 0 /\ 0 <= a1 <= 1 /\ 0 <= c1 <= 1).
{ destruct Hw as [[-> Hrcn] | [-> Hrc0]].
  - pose proof (cawC_s0_ne0 (c_rc C) Hrc Hrcn) as Hs.
    exists 0, 0, 1. split; [|split; [|split]].
    + rewrite U_SAlu, U_SLit, U8. cbn [zalu_raw]. replace (bv_unsigned (w64 (c_rc C)) <? zcanon 1) with false.
      * reflexivity.
      * symmetry. apply Z.ltb_ge. change (zcanon 1) with 1. lia.
    + rewrite !U_SAlu, !U_SLit, U18. vm_compute. reflexivity.
    + rewrite U_SAlu, U_SLit, U18. vm_compute. reflexivity.
    + split; [reflexivity|]. split; [reflexivity|]. lia.
  - exists 1, 1, 0. split; [|split; [|split]].
    + rewrite U_SAlu, U_SLit, U8, Hrc0. vm_compute. reflexivity.
    + rewrite !U_SAlu, !U_SLit, U18. vm_compute. reflexivity.
    + rewrite U_SAlu, U_SLit, U18. vm_compute. reflexivity.
    + split; [reflexivity|]. split; [reflexivity|]. lia. }
destruct Va as (a1 & b1 & c1 & Ua & Ub & Uc & Eab1 & Eand & Ha1 & Hc1).
pose (RUN := @paj_run_x_invR fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW RW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUNTO := @paj_run_to_x_invR fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW RW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := YSRrG.paj_branchR (fx := fy) (rc := rc) (L := B_prog_listing) (PI := PA) RW).
unfold caw_cfg.
(* seqz / slti / xori; stop at `bne a0, a1` (0x82044) *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_END).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM1 end. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ (* 0x82044 taken: the abort edge (rc == 0) != (want >= 0) is refuted *)
  exfalso. rewrite branch_ne_U, Ua, Ub, Eab1, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* snez / and; stop at `bnez a0` (0x82050) *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_END).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM2 end. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ (* 0x82050 taken: the abort edge rc == 0 && want != 0 is refuted *)
  exfalso. rewrite branch_ne_U, U_SAlu, Ua, Uc, U_SLit in Hc. cbn [zalu_raw] in Hc. rewrite Eand in Hc.
  vm_compute in Hc. discriminate Hc. }
clear Hc.
(* mv s1, zero; stop at 0x82058 *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_END).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM3 end. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  assert (Emem : ms_mem msn = mem3) by (rewrite EM3, EM2, EM1; reflexivity);
  rewrite (st_ok_pi_restrict_mkst (fx := fy) (L := B_prog_listing) (PI := PA) (w_H W3) E _ msn HS eq_refl) end.
cbn [ss_pc].
prreg HS (9%bv : bv 5) Q9.
assert (HKP : forall rr, In rr [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms1) rr = getr regs3 rr).
{ eapply (regs_kept_of_st_ok_pi (fx := fy) (L := B_prog_listing) (PI := PA) E _ (restrict (w_H W3) ms1) regs3
    [Z_to_bv 64 SHADOW_OFF]); [exact HS | exact HAE | vm_compute; reflexivity]. }
change (AF_cawB + CAWB_CK + 52) with (AF_cawB + CAWB_END).
apply (Kend fy ly3 S3 Hp3 W3 (ms_regs ms1) (ms_mem ms1) _ k 0 0); [|exact HPM].
rewrite Emem in HJ |- *.
split; [|split; [|split; [right; split; [reflexivity | split; [reflexivity | exact Hrp]] |
  split; [exact Eab | exact HL]]]].
- split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ|].
  split; [intros rr Hr; rewrite <- (Hk rr Hr); apply HKP; cbn [In] in Hr |- *; tauto|].
  split; [unfold spZ; rewrite (HKP 2%bv) by (left; reflexivity); exact Hsp|].
  split; [rewrite (HKP 8%bv) by (cbn; tauto); exact R8|].
  split; [exact HSV|]. split; [exact EHp | exact HROOM].
- rewrite Q9. reflexivity.
Qed.

End f.
End d.

Print Assumptions caw_WB5.
Print Assumptions caw_WB5R.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 1132 of its 1198 lines of code are new or changed and 712 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move; the wle' contract, the internal file WLE-CONTRACT.md):
   every journal of this file is at RZW := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (ajournal_xR / ajournal_xwR) and every
   stretch statement concludes YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (crt102_tail, ct_J_call, ct_at_Z, ct_at_F).
   pj_free's text asks `v <> 0 -> hull_budget S []` at its call: ct_J_call takes `hull_budget Sc []` and crt102_tail
   pays it from crt_pos's run position with the Section hypothesis HOS4 : (length rp_os <= 4)%nat (the text's own
   premise) through Crt102HullPos.hull_budget_nil_of_room_pos. The inline release and __asan_set_shadow_f5 cross by
   the engine's R rules YGcallSx.aj_flag_store_xR and YGcallMxmn.aj_set_shadow_at_xmR. *)
(* base: commit 2fdcfd7be069 (post-landing line). kb round (brief
   the internal file wild-budget-kb-reshape.md): crt_at_J's live state is at kb =
   prh_wk F_check_round_trip, its journal at a budget WS with wbudget [] (prh_wk F_check_round_trip) WS; the tail's
   calls (pj_free, __asan_set_shadow_f5, the inline release) store no wild trace, so the journal stays at WS to the
   `ret`, and QF is the text's budgeted post at that WS (ct_at_F). *)
(* fuzz_preset, image A' (asan, pin 1be0f53d96cb9d6c, twin bff8519bbe3ea0e4): THE TAIL of the walk
   of check_round_trip (fuzz_preset.c new:772-781), from the join J (+0x340) to the `ret` (+0x46c), against the contract
   tcheck_round_trip_specX (lib/A/PRH_FnCheck.v). Its export is crt102_tail:
   `crt_at_J .. -> SRr SEGS Wc (crt_cfg fxk CRT_J_OFF rg memc mdc) QF`, the lemma every arm of the body ends in.
   STATUS: crt102_tail is Qed. Its r = 1 arm is dead (crt_at_J states r = 0); its r = 0 arm closes from crt_at_J's
   ordered free list for copy (the former open goal FREEPERM). Every piece is its own Qed lemma
   (ct_J_call, ct_r0_end, ct_at_Z, ct_at_F, ct_qt_keep and the helpers). On the earlier base ba4ced0dbea, whose QT
   carried no exact position, crt102_tail was Qed (commit 090d18ff610, pins102 rc=0).

   INPUTS OF RECORD (by path):
   - pins: A' asan 1be0f53d96cb9d6c (twin bff8519bbe3ea0e4), B' asan-ubsan d663f82d7f488d30 (twin c90d4fa54d43160b);
     this file is image A' only.
   - base commit 813a63b6cfb3: lib/A/Prog/Crt102Glue.v 5f20c5d5048f (QT = the text's post:
     g_most / g_own_ran_out inside prh_ledger, r = 0, the exact end position; crt_side = the ledger at `ranc most ownc`
     without a position; crt_at_J states r = 0, and its r = 0 arm carries crt_pos Sc crt_evs_J (with prh_cons_from) and
     the tree copy holds, crt_tree_J, with its block sizes against tblk UP TO PERMUTATION and its ORDERED free list
     Fc, map (snd + cf_head) Fc = fo crt_tree_J), Crt102Img.v 176eec830b61,
     Crt102Model.v b493cf5e85a2, S10Env.v d8ca1dd59ead, S1Ledger.v 8cf15eeb6311; the contract texts and Spec BY PATH at
     the kit tip of record, commit 3ac20a5c9e30: PRH_FnPj.v dc0d0aa79c0f (tpj_free_specX over pj_foR: a
     position-free class-24 entry premise for v <> 0, prh_head_wide, the ledger with its g_most / g_own_ran_out cells,
     and the position TRANSFER in its post), PRH_PjOrder.v e5917626b82b, PRH_FnCheck.v 0844ed8c0608, PRH_Base.v
     ee2f5cd7ed35; Spec PresetReqAt.v 43c958024221, PresetRun.v 5ac818ab1fe6, PresetFreeFo.v 50bc9df2f2de (fo / tblk
     are multiset facts only: the model gives no tree-shaped order); the files relocated to the #102 pins, by path from
     commit f67018a892ba.
   - listing read: the internal file crt.A.s (A 0x82bb0 .. 0x82cdc); segment cut:
     DESIGN.md (sha256 d05697dd088c; internal record) (cuts J, Z, Q; Z at +0x348 per Crt102Img).
   - engine: the whole set of the base (at commit bb085d091bbe: YCbqG / YCbqGcall / YCbqGcallW / YGcallSx / YC80x /
     YC1fPx / YGcallMxmn b47cf7942c3d / YSRrMemnorm).
   - rule 24: no walk of check_round_trip exists on the #102 pins outside this one - the cold/* sweep of record on
     census-1 with a positive control (RULE24.md (sha256 96ef6f3404f0; internal record): 14976 cold refs + 4 released, CONTROL OK, LAST
     LINE COMPLETE, 2026-10-29 16:07-17:06Z), beside the index lookup (an internal record of that lookup).
     The old-pin ASan walks it found (ACrt* / BCrt*, entry 0x82550) do not relocate: check_round_trip is
     source-changed on #102. Written new. Model walks read, not cited: S10TxString.v ts_G_entry / ts_at_G (the epilogue
     and the inline release), H5CrtS7.v (the old-pin tail).

   THE SEGMENTS (offsets from check_round_trip's entry, DERIVED as 4 * the listing slot: Crt102Img.v's CRT_J_OFF /
   CRT_Z_OFF / CRT_Z5_OFF; the run probes put `PCall AS_pj_free` at +0x344, `PCall AS___asan_set_shadow_f5` at +0x37c and
   `PW RET_WORD_r` at +0x46c):
   - J (+0x340): `mv a0, s4; jal pj_free` - one engine run (no region), then the call of the tpj_free_specX text at
     n = DOC_D through YCbqGcallW.aj_call_xW_sp at window 0. pj_free's text is the caller-window form fpostWm (the
     same post YCbqGcall.aj_call_xF would need re-stated), and its walk is generic in the float state, so the text is
     taken at the arms' float state fxk (Section hypothesis PJFREE quantifies it) and the run continues at fxk.
   - Z (+0x348): the re-poison of copy's seven shadow bytes (f8 at s2+0x1c .. +0x22), the retired magic `sd a0, 0(s11)`,
     the `beqz s3`, `addi a1, zero, 0x40; mv a0, s2; jal __asan_set_shadow_f5` (the engine's YGcallMxmn.aj_set_shadow_at_xm).
   - F (+0x380): `ld a0, 0x1f8(s3); sb zero, 0(a0)` - THE INLINE RELEASE (YGcallSx.aj_flag_store_x), which turns the state
     into stack_free_state 3 pos S2 (frames back to the entry's, room_live_cf by RL_stack_free) - then `j +0x42c`,
     `mv a0, s6; addi sp, s0, -0xe0`, the thirteen restores in CRT_SAVED's order, `addi sp, sp, 0xe0`, to the `ret`
     (YC1fP.paj_ret_at); aregs_preserved regs regs' from the restores' chunks (crt_saved).

   WHAT IS UNREACHABLE, AND WHY.
   - THE STACK PATH +0x38c .. +0x428 (taken at `beqz s3` when the frame call returned 0). s3 = F = frame_addr lyc 3 pos
     (crt_bregs, the one write of s3 is `mv s3, a0` at +0x70) and frames_bounds_x puts F at or above 4096; ss_Z states
     that as s3's atom fact [4096, 2 ^ 47), so the engine decides the branch statically and its run never enters the
     stack path: no run of it exists to walk.
   - THE FLAG STORE INTO THE FRAME ITSELF. `sb zero, 0(a0)` writes flag_addr; the frame's own bytes are not runtime-owned
     (alx_frames) while the flag byte is (FFLX), so the flag lies outside [F, F + 512) and the store leaves the flag word
     at F + 504 and the saved slots alone (Hflf in ct_at_F).
   - No inline shadow check and no report call is on the tail (listing A 0x82bb0 .. 0x82bf4, 0x82c9c .. 0x82cdc: shadow
     stores, the magic store, the flag load / store, the restores), so no report path needs ruling out.

   THE TWO LEDGER CELLS AT THE JOIN (G4, closed). QT asks g_most = most and g_own_ran_out = own' after pj_free, cells
   every journal's image clause excludes (PST). Since the E sweep both are fields of prh_ledger (`.. fail ran most own`,
   PRH_Base.v ee2f5cd7ed35), and tpj_free_specX's post (PRH_FnPj.v dc0d0aa79c0f) gives the ledger at S' with the
   entry's `most own`: ct_J_call cites that conjunct. __asan_set_shadow_f5 and the release keep both cells with the
   rest of the ledger (S1Ledger.prh_ledger_kept_aview, in ct_qt_keep).

   CLOSURE NOTE (image-dependent files by blob). CfImgA d76378331be3 + YGcfNames e2b68365560e
   (the core-class pair, matching); PRH_Img 934516a622e8 (its ledger cells, pi_g_most included, checked against the A'
   twin bff8519bbe3ea0e4's symtab and by decode: fuzz_malloc's auipc / ld reads 0xa65e0); PRH_ImgB 3216eca68342;
   A/Listing_prog 7ed1529926bd, A/PAImg_prog 505a51ff7d08, B/Listing_prog c97cc46b3e13, S1ImgA 0b2d1e17f367; ZImage
   9f6813318c43 (the #102 relocation's re-pin); lib/Reusable/YGcfStr.v 3aabb6857229 (the libc row's pin-free blob, which
   retired e22d2e598fde and its pre-#102 wrapper pcs; this file read none of them). ACeg / AD2l / AF0m / AF0l / PSstrlen
   are not in the closure, and B is a generic Section variable here: PALib's A' instance is discharged at the binder
   (Crt102Top), which this file does not reach.

   ELABORATION (Set Printing All over crt102_tail's goal and ct_J_call / ct_at_Z / ct_at_F / ct_r0_end / ct_F_entry /
   ct_Z_entry, at f8b33cb68f8): QF and crt_at_J take `fx` (the contract's entry float state, passed by name);
   `fregs_kept_x fx fxk`, `frm_zero (fp_csr fxk)`, `mkst fxk` and `st_ok_pi .. fxk` take the arms' `fxk` as meant;
   ajournal_x, crt_saved, crt_frame, crt_bregs and crt_cfg take no float state. PASS: no class-implicit FPState
   resolved to the wrong one.

   NUMERALS. LENGTH: 28 / 35 (copy's shadow bytes s2 + 0x1c .. + 0x22), 504 / 512 (the flag word at F + fs_frame_bytes 3
   - 8; the class-3 frame), 64 (its shadow bytes = __asan_set_shadow_f5's a1), 56 (struct pj), 104 / 224 / 240 / 32
   (the saves below the entry sp, the frame 0xe0, FRA, the realignment), 16 (cf_head, the stack alignment), 8 (a word),
   4096 (the low page), 2 ^ 20 (the text bound), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (the shadow span, the stack
   band, the word). WORD: 245 (0xf5, the poison value of the set-shadow call), 2 ^ 64 - 8 (s7 = -8, the f8 byte).
   DERIVED: atom indices (the engine's numbering), the cut offsets (Crt102Img's names). No ADDRESS literal: every code
   address is pa_val / pa_sigma of PAImg_prog.v, and ct_base decides BASE's bounds by computation.

   THE REQUEST BOUND. `RQA_crt t <= most` is a premise of the text, carried as the Section hypothesis HRQA and read at the
   pj_free call through Crt102Model.cm_rqa_nonneg. pj_free makes no allocator request (fuzz_free only), so the bound is
   not consumed; __asan_set_shadow_f5 and the flag store make no allocator request either.

   SECTION HYPOTHESES (each with its owner): LAWS (engine AR_laws_x fold), ENV api_env (the contract texts, PALib's
   pal_env; discharged at the binder of B), OWNLOW (engine; at ARcf owned_low_cf), ASFX / FFLX / SFX (aj_flag_store_x's
   three: YG0dcf astack_free_law_cf, AR_flag_law_ok_cf / AR_client_img_law_ok_cf, YGcallScf stack_free_x_any), FFLP (the
   image row, AR_flag_law_ok_cf's first conjunct), SETSH YGcallMxmn.aset_shadow_realizes_xm (the frame-class row that
   discharges FCiface contracts; the rule is the engine's YGcallMxmn.aj_set_shadow_at_xm, cited), PJFREE (the pj_free
   contract text), and the text's own premises HPRE / HCL / HTREE / HRQA. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck PRH_PjOrder PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA Crt102Glue Crt102Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
(* kb round: Crt102Kit's AJW runner (crt_run_xw) and the journal's wild clause (crt_jw_wild), used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* the re-hiding move, used qualified: YA0nH (wle', SRrG, SRr', SRr_SRr', the wle' laws),
   YSRrG (SRrG_msteps, SRr'_bind / _mono / _ret), YGcfRehidePost.RZ_cf (preset's zone); pj_free's hull premise from
   the run position: PresetHullBudget and the image-free Crt102HullPos (hull_budget_nil_of_room_pos) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102HullPos.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.


(* ======================================================================================================== *)
(* image-free: the tree over a larger block list, pairwise lists, a word from its eight bytes *)
Section ct. Variable segs : list Segment.

Lemma ct_cstr_lblk : forall m (lblk lblk' : Z -> Z -> Prop) a k s, pj_cstrR segs m lblk a k s ->
  (lblk a k -> lblk' a k) -> pj_cstrR segs m lblk' a k s.
Proof. intros m lblk lblk' a k s (Hl & Hr) H. exact (conj (H Hl) Hr). Qed.

Lemma ct_mems_lblk : forall m (lblk lblk' : Z -> Z -> Prop) (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H HL HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
split; [exact Hx|].
split; [apply (ct_cstr_lblk m lblk lblk' x k nm Hc); apply HL; left; reflexivity|].
split.
- pose proof (HP 0%nat nm u D1 eq_refl (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))) as HP0.
  replace (a + 56 * Z.of_nat 0) with a in HP0 by lia. exact (HP0 H1).
- apply (IH (a + 56) (ka + 8) D2 H2).
  + intros y kk Hy. apply HL. right. apply in_or_app. right. exact Hy.
  + intros i nm' u' D1' Hi Hinc HPi.
    specialize (HP (S i) nm' u' D1' Hi (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia. exact (HP HPi).
Qed.

(* the tree over a block predicate that holds wherever the old one did, on the tree's own blocks *)
Lemma ct_nodeR_lblk : forall t m (lblk lblk' : Z -> Z -> Prop) p D, pj_nodeR segs m lblk p t D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (ct_cstr_lblk m lblk lblk' str k txt Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (ct_cstr_lblk m lblk lblk' str k s Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hp & Hk)]; [left; exact Hz | right; split; [exact Hp|]].
    apply HL; [|exact Hk]. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP).
  intros x k Hx. apply HL. apply HDi. apply Hinc. exact Hx.
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hp & Hk & Hy)]; [left; exact Hz | right; split; [exact Hp|]].
    subst D. rewrite (proj2 (Z.eqb_neq cap 0)) in HL by lia.
    split; [apply HL; [left; reflexivity | exact Hk] | apply HL; [right; left; reflexivity | exact Hy]]. }
  exists Di. split; [exact ED|].
  apply (ct_mems_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi).
  + intros x k Hx. apply HL. apply HDi. exact Hx.
  + intros i nm u D1 Hil Hinc HP. rewrite Forall_forall in IH.
    specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m lblk lblk' _ D1 HP). intros x k Hx. apply HL. apply HDi. apply Hinc. exact Hx.
Qed.

(* a word from its eight bytes (YCem.v:101 rdword_of_val_mem, restated: YCem's Require closure is cgif's image layer) *)
Lemma ct_rdword_of_vm : forall H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
End ct.

(* pairwise R over a permutation, for a symmetric R (S10TxKit.v s10_pairwise_perm, restated: S10TxKit is not on the
   base) *)
Lemma ct_pairwise_perm : forall (A : Type) (R : A -> A -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros A R Hs l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [pairwise]; intros H.
- exact H.
- destruct H as [Hx Hl]. split; [|exact (IH Hl)].
  rewrite Forall_forall in Hx |- *. intros z Hz. apply Hx. exact (Permutation_in _ (Permutation_sym P) Hz).
- destruct H as [Hy [Hx Hl]]. inversion Hy as [|? ? Hyx Hyl]; subst.
  split; [constructor; [apply Hs; exact Hyx | exact Hx] | split; [exact Hyl | exact Hl]].
- exact (IH2 (IH1 H)).
Qed.
(* an element in both halves of a pairwise list is related to itself *)
Lemma ct_pairwise_app_dup : forall (A : Type) (R : A -> A -> Prop) l1 l2 x,
  pairwise R (l1 ++ l2) -> In x l1 -> In x l2 -> R x x.
Proof.
intros A R l1. induction l1 as [|z l1 IH]; intros l2 x H H1 H2; [destruct H1|].
cbn [pairwise app] in H. destruct H as [Hz Hl]. destruct H1 as [<- | H1].
- rewrite Forall_forall in Hz. apply Hz. apply in_or_app. right. exact H2.
- exact (IH l2 x Hl H1 H2).
Qed.

(* ======================================================================================================== *)
(* __asan_set_shadow_f5 WITH THE MEMNORM KEEP: the engine's YGcallMxmn.aset_shadow_realizes_xm (the contract, FCiface.v:69
   plus the keep) and YGcallMxmn.aj_set_shadow_at_xm (the call rule, YGcallSx.v:146 plus the keep), engine of record
   at commit bb085d091bbe, YGcallMxmn.v b47cf7942c3d. This file carried both as local copies until base d48dc1e7b240
   (Crt102Tail.v a901d1bca110); the definition and the rule's statement are word-for-word the engine's (MN is
   YAkMemnorm), and the one difference was the rule's errno premise, which the copy had narrowed to api_env's errno
   conjunct; citing the engine takes its `api_env segs B` premise (ENV below). *)

(* ======================================================================================================== *)
(* THE THREE SYMBOLIC STATES of the tail (S10Env.v's environment TE: atoms 0-31 the entry registers, 32-63 the current
   ones, 64- the segment's extras; xr r = 32 + r) *)
(* J: `mv a0, s4; jal pj_free` - no region *)
Definition ss_J : sstate := mkSS (CRT_PC_A + CRT_J_OFF) cur_atoms [] None (mkFacts [] [] []).
(* Z: copy's seven shadow bytes through s2 (written f8), the frame's first word through s11 (the retired magic); s3's
   atom is the frame, and its fact 4096 <= s3 is what the engine reads at `beqz s3`: THE STACK PATH IS NEVER ENTERED *)
Definition ss_Z : sstate := mkSS (CRT_PC_A + CRT_Z_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 18)) 28 35 28 35 [];
    YP09.mkRegion (Some (xr 27)) 0 8 0 8 [] ] None
  (mkFacts [(xr 18, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (xr 19, mkAF 4096 (2 ^ 47) 5);
            (xr 27, mkAF 4096 (2 ^ 47) 5)] [] []).
(* F: gp, tp pinned to the entry's and s0 to the entry sp (atom 2); the frame's flag word (F + 504 through s3, read-only,
   its value the flag's address, atom 64), the flag byte (writable), the thirteen saves below the entry sp (read-only,
   the entry registers in CRT_SAVED's order) *)
Definition sr_F : list sv := sr_set (sr_set (sr_set cur_atoms 3%bv (SOff 3 0)) 4%bv (SOff 4 0)) 8%bv (SOff 2 0).
Definition F_saves : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
   YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-104) (CVal 8 (SOff 27 0))].
Definition ss_F : sstate := mkSS (CRT_PC_A + CRT_Z5_OFF) sr_F
  [ YP09.mkRegion (Some (xr 19)) 504 512 0 0 [YP09.mkChunk 504 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some 64%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 2%nat) (-104) 0 0 0 F_saves ] None
  (mkFacts [(xr 19, mkAF 4096 (2 ^ 47) 5); (64%nat, mkAF 0 (2 ^ 47) 0); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

(* a register a run did not write (S10TxString.v's tskeep, restated: that file is not on the base) *)
Ltac ct_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* ======================================================================================================== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
#[local] Notation STKC := (@STK_check_round_trip prh_img_A).
#[local] Notation STKPF := (@STK_pj_free prh_img_A DOC_D).

(* the image's facts the tail reads, by computation *)
Lemma ct_fb3 : fs_frame_bytes CRT_CID = 512.
Proof. vm_compute. reflexivity. Qed.
(* the text segment's base and the function's offset, as bounds (no ADDRESS literal: each is decided by computation) *)
Lemma ct_base : 4096 <= BASE /\ BASE <= 2 ^ 20 /\ BASE mod 4 = 0 /\ 0 <= CRT_PC_A < 2 ^ 20.
Proof.
split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [apply Z.leb_le; vm_compute; reflexivity|].
split; [apply Z.eqb_eq; vm_compute; reflexivity|].
split; [apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity].
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the re-hiding move (the wle' contract, the internal file WLE-CONTRACT.md): the journals sit at the world relation
   RZW := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (ajournal_xR / ajournal_xwR), the relation of QF's journal *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (kb round: crt_at_J's live state is at kb = prh_wk F_check_round_trip) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
(* ---- SECTION HYPOTHESES, each with its owner ---- *)
(* the allocator laws (engine fold, YCbqG c3b5d0111037; at ARcf: AR_laws_x_cf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the runtime's environment (owner: the image binding of B, PALib's pal_env), the premise of the engine's
   set-shadow rule YGcallMxmn.aj_set_shadow_at_xm. Its as_code half holds at A' with AF0l dfca6bb1a8d7 (by
   vm_compute against the listing; the old-pin AF0l eb3d91d8c440 refuted it); B is generic here, so the A' instance is
   discharged at the binder (Crt102Top). *)
Hypothesis ENV : api_env SEGS B.
(* runtime-owned bytes lie below the ceiling (YGcallx.v ARx_owned_low_law; at ARcf: owned_low_cf) *)
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
(* the inline release: exactly the three hypotheses of YGcallSx.v's aj_flag_store_x (ASFX = YG0dcf.v
   astack_free_law_cf, FFLX = AR_flag_law_ok_cf / AR_client_img_law_ok_cf, SFX = YGcallScf.v stack_free_x_any) *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
(* the frame's flag byte is present (at ARcf: AR_flag_law_ok_cf's first conjunct, as H5CrtS7.v
   crt7_fflx and S10TxString.v's FFLP take it) *)
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
(* __asan_set_shadow_f5 at the poison value 0xf5, the engine's _xm contract (owner: the frame-class row that
   discharges FCiface contracts at the instance) *)
Hypothesis SETSH : forall fxk : YK11.FPState,
  YGcallMxmn.aset_shadow_realizes_xm (fx := fxk) SEGS B ARx (SIGMA AS___asan_set_shadow_f5) 245.
(* the callee's contract text: tpj_free_specX (lib/A/PRH_FnPj.v 50f4781cadb9), at every float state (its walk is
   generic in fx), at the caller's universe closure *)
Variable CTX0 : list (list Z).
Hypothesis PJFREE : forall fxk : YK11.FPState,
  tpj_free_specX (fx := fxk) B ARx SK CTX0 DOC_D.

Section g.
(* ---- the entry: tcheck_round_trip_specX's binders and the premises the tail reads ---- *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : PjTree.jv) (D : list (Z * Z))
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
#[local] Notation sp0 := (spZ regs).
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HCL : prh_univ_closure B CTX0.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
(* carried, not consumed: see the header (THE REQUEST BOUND) *)
Hypothesis HRQA : RQA_crt t <= most.
(* THE RUN HAS AT MOST 4 CALLS (the text's premise, PRH_FnCheck.v tcheck_round_trip_specX): pj_free's hull premise is
   paid from crt_pos's run position by Crt102HullPos.hull_budget_nil_of_room_pos, which takes this bound *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

#[local] Notation QFA := (QF (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W)
  (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt)
  (ran := ran) (most := most)).
#[local] Notation JA := (crt_at_J (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W)
  (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt)
  (ran := ran) (most := most)).
#[local] Notation sp1 := (CRT_sp1 (regs := regs)).
#[local] Notation bregs := (crt_bregs (regs := regs)).
#[local] Notation saved := (crt_saved (rc := rc) (L := A_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation framed := (crt_frame (rc := rc) (L := A_prog_listing) (PA := PA)).

(* ---- the tail's own register and range facts ---- *)
Lemma ct_sp1_range : sp0 mod 16 = 0 -> 240 <= sp0 -> sp0 - 240 <= sp1 <= sp0 - 224 /\ sp1 mod 32 = 0.
Proof.
intros Hal H. unfold CRT_sp1, CRT_FRAME, CRT_ALIGN. pose proof (Z.mul_div_le (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
assert (Hm : (sp0 - 224) mod 32 = 0 \/ (sp0 - 224) mod 32 = 16).
{ pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 16 ltac:(lia)).
  assert ((sp0 - 224) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
  pose proof (Z.mod_pos_bound (sp0 - 224) 16 ltac:(lia)). lia. }
split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Qed.
Lemma ct_bregs_pres : forall rg rg' F, bregs rg F -> aregs_preserved rg rg' -> bregs rg' F.
Proof.
intros rg rg' F HBR HP.
refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
  crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
  crt_bregs_s11 := _ |}.
- rewrite (ts_ap rg rg' 2%bv HP) by ts_cs. exact (crt_bregs_sp HBR).
- rewrite (ts_ap rg rg' 3%bv HP) by ts_cs. exact (crt_bregs_gp HBR).
- rewrite (ts_ap rg rg' 4%bv HP) by ts_cs. exact (crt_bregs_tp HBR).
- rewrite (ts_ap rg rg' 8%bv HP) by ts_cs. exact (crt_bregs_s0 HBR).
- rewrite (ts_ap rg rg' 9%bv HP) by ts_cs. exact (crt_bregs_s1 HBR).
- rewrite (ts_ap rg rg' 18%bv HP) by ts_cs. exact (crt_bregs_s2 HBR).
- rewrite (ts_ap rg rg' 20%bv HP) by ts_cs. exact (crt_bregs_s4 HBR).
- rewrite (ts_ap rg rg' 19%bv HP) by ts_cs. exact (crt_bregs_s3 HBR).
- rewrite (ts_ap rg rg' 23%bv HP) by ts_cs. exact (crt_bregs_s7 HBR).
- rewrite (ts_ap rg rg' 26%bv HP) by ts_cs. exact (crt_bregs_s10 HBR).
- rewrite (ts_ap rg rg' 27%bv HP) by ts_cs. exact (crt_bregs_s11 HBR).
Qed.

(* ---- QT at a state, the register aside: the facts the tail carries from pj_free's return to the `ret`. QT
   (Crt102Glue.v 7719492eb9d3) puts the room position on the r = 0 arm only, exact; ct_qt0 is everything else, and
   ct_pos_end is that position, so the one fact pj_free's text does not yet give stands alone ---- *)
Definition ct_qt0 (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS) (mem' : word -> option byte) (r : Z)
  : Prop :=
  room_live_cf S' /\
  exists Lam' peak' cset cnt' ran' own',
  Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ peak <= peak' /\
  0 <= cset <= 3 /\ (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst ms) -> cset = 0) /\
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
  pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') doc t D /\ (forall bk, In bk D -> In bk Lam') /\
  r = 0 /\
  ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ cnt <= cnt' <= cnt + ck_crt_count t cset) \/
   (r = 0 /\ own' = 0 /\ cnt' = cnt + ck_crt_count t cset /\ ran' = ran)).
Definition ct_pos_end (S' : astate) : Prop :=
  exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
    (rp_i + length (PresetReqAt.round_trip rp_sm t))%nat rp_H0 hist' S'.
Definition ct_qt (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS) (mem' : word -> option byte) (r : Z)
  : Prop :=
  ct_qt0 ly' S' Hp' W' mem' r /\ (r = 0 -> ct_pos_end S').

(* the document's header sits in one of the entry's fake frames (ck_tree_ok's ck_obj_home), at every later state *)
Lemma ct_doc_frame : forall ly2 S2 n,
  layout_le n ly ly2 -> (forall f, In f (frames S) -> In f (frames S2)) ->
  exists cid pos, In (cid, pos) (frames S) /\ In (cid, pos) (frames S2) /\
    frame_addr ly2 cid pos <= doc /\ doc + 56 <= frame_addr ly2 cid pos + fs_frame_bytes cid.
Proof.
intros ly2 S2 n Hle Hfr.
pose proof HTREE as (_ & _ & _ & _ & (cid & pos & Hin & H1 & H2) & _).
exists cid, pos.
assert (E : frame_addr ly2 cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite E. split; [exact Hin|]. split; [exact (Hfr _ Hin)|]. split; assumption.
Qed.
(* what a fake-frame home gives at a state: the header's bytes are present, not runtime-owned, client memory *)
Lemma ct_doc_bytes : forall ly2 S2 Hp2 (W2 : world SEGS) m md2 n,
  ARx ly2 S2 Hp2 W2 m md2 -> layout_le n ly ly2 -> (forall f, In f (frames S) -> In f (frames S2)) ->
  4096 <= doc /\ doc + 56 <= YM05.alloc_ceiling /\
  (forall a, doc <= a < doc + 56 -> apresent (w_H W2) m a /\ ~ aowned B ly2 S2 a /\ ~ in_img SEGS a /\
     in_app a 1).
Proof.
intros ly2 S2 Hp2 W2 m md2 n HAR Hle Hfr.
destruct (ct_doc_frame ly2 S2 n Hle Hfr) as (cid & pos & _ & Hin & H1 & H2).
destruct (frames_bounds_x _ _ _ LAWS ly2 S2 Hp2 W2 m md2 cid pos HAR Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 m md2 cid pos HAR Hin) as (_ & _ & Ffr & _).
split; [lia|]. split; [lia|].
intros a Ha. destruct (Ffr a ltac:(lia)) as [Hpr Ho]. split; [exact Hpr|]. split; [exact Ho|].
split; [exact (frm_img_x _ _ _ LAWS ly2 S2 Hp2 W2 m md2 cid pos a HAR Hin ltac:(lia))|].
unfold in_app in *. lia.
Qed.

(* QT's facts survive a change of memory that misses alloc.c's statics, the document's header and every live block
   (the runtime call and the inline release below), at a state with the same blocks and the same room *)
Lemma ct_qt_keep : forall ly2 S2 S2' Hp2 W2 m m' md' r (C : Z -> Prop),
  ct_qt ly2 S2 Hp2 W2 m r ->
  ARx ly2 S2' Hp2 W2 m' md' ->
  ablocks B ly2 S2' = ablocks B ly2 S2 ->
  (room_live_cf S2 -> room_live_cf S2') ->
  (forall i h, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 h S2 ->
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 h S2') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ C a -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a) ->
  (forall a, C a -> ~ Exists (in_zr a) PST /\ ~ (doc <= a < doc + 56) /\
     forall p n, In (p, n) (ablocks B ly2 S2) -> ~ (p <= a < p + req_size n)) ->
  (forall a, doc <= a < doc + 56 -> apresent (w_H W2) m' a) ->
  0 <= doc -> doc + 56 <= 2 ^ 64 ->
  ct_qt ly2 S2' Hp2 W2 m' r.
Proof.
intros ly2 S2 S2' Hp2 W2 m m' md' r C
  ((HRL & Lam' & peak' & cset & cnt' & ran' & own' & HPL & HPA & HPK & Hcs & Hcs0 & HLED &
    HDOC & HDL & HR) & HPE) HAR' EAB HRLk HRPk HK HC HDP Hd0 Hd1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPSTK : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a).
{ intros a Ha. pose proof (@pa_segs_low _ _ PA a (pst_in_img_A a Ha)) as Hlow.
  apply HK; [unfold kLowMemEnd in Hlow; lia | intros Hc; exact (proj1 (HC a Hc) Ha)]. }
assert (HBLK : forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) m' (p + i) = aview SEGS (w_H W2) m (p + i)).
{ intros p n i Hin Hi.
  destruct (alx_blocks _ _ _ LAWS ly2 S2' Hp2 W2 m' md' p n HAR' ltac:(rewrite EAB; exact Hin)) as (_ & H4096 & Hc & _).
  apply HK; [lia|]. intros Hcc. exact (proj2 (proj2 (HC _ Hcc)) p n Hin ltac:(lia)). }
assert (HBP : forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> apresent (w_H W2) m' (p + i)).
{ intros p n i Hin Hi.
  destruct (alx_blocks _ _ _ LAWS ly2 S2' Hp2 W2 m' md' p n HAR' ltac:(rewrite EAB; exact Hin)) as (_ & _ & _ & _ & Hb & _).
  exact (proj1 (Hb (p + i) ltac:(lia))). }
assert (HLB : forall a k, In (a, k) Lam' -> 0 <= k /\ In (a - 16, k + 16) (ablocks B ly2 S2)).
{ intros a k Hin. pose proof (prh_ledger_blocks B ly2 S2 Hp2 W2 m Lam' peak' cnt' SIZE_MAXZ ran' most own' HLED) as HF.
  rewrite Forall_forall in HF. destruct (HF (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  change (@cf_head CfParams_preset) with 16 in Hab. exact (conj Hk0 Hab). }
split; [|intros E; destruct (HPE E) as (hist' & HRP); exists hist'; exact (HRPk _ _ HRP)].
split; [exact (HRLk HRL)|].
exists Lam', peak', cset, cnt', ran', own'.
split; [exact HPL|]. split; [rewrite EAB; exact HPA|]. split; [exact HPK|]. split; [exact Hcs|]. split; [exact Hcs0|].
split.
{ apply (S1Ledger.prh_ledger_kept_aview B ly2 S2 Hp2 W2 m ly2 S2' Hp2 W2 m' Lam' peak' cnt' SIZE_MAXZ ran' most own'
    HLED HPSTK).
  - intros a k i Hin Hi. destruct (HLB a k Hin) as (Hk0 & Hab).
    change (@cf_head CfParams_preset) with 16. apply (HBLK (a - 16) (k + 16) i Hab).
    unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia.
  - intros a k _ Hab. rewrite EAB. exact Hab.
  - apply Permutation_refl. }
split.
{ apply (pj_nodeR_frame SEGS t (mrestrict (w_H W2) m) (mrestrict (w_H W2) m') (prh_lin Lam') doc D HDOC).
  intros x [Hx | ((a, k) & Hb & Hx)].
  - split.
    + apply (mbyte_of_aview SEGS). apply HK; [lia|]. intros Hc. exact (proj1 (proj2 (HC x Hc)) Hx).
    + intros _. apply (apresent_writable SEGS). exact (HDP x Hx).
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx. destruct (HLB a k (HDL _ Hb)) as (Hk0 & Hab).
    assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
    replace x with (a - 16 + (x - (a - 16))) by lia.
    split.
    + apply (mbyte_of_aview SEGS). apply (HBLK (a - 16) (k + 16)); [exact Hab | lia].
    + intros _. apply (apresent_writable SEGS). apply (HBP (a - 16) (k + 16)); [exact Hab | lia]. }
split; [exact HDL|].
exact HR.
Qed.

(* ---- the symbolic states from concrete facts (S10TxString.v's ts_SH_entry / ts_G_entry shape) ---- *)
Lemma ct_Z_entry : forall fxk (Wc : world SEGS) memc rg F,
  getr rg 18 = w64 (shadow_addr F) -> getr rg 19 = w64 F -> getr rg 27 = w64 F ->
  4096 <= F -> F + 512 <= 2 ^ 47 -> F mod 32 = 0 -> in_app F 512 ->
  (forall a, F <= a < F + 8 -> apresent (w_H Wc) memc a) ->
  (forall a, shadow_addr F + 28 <= a < shadow_addr F + 35 -> apresent (w_H Wc) memc a) ->
  st_ok_pi SEGS VAL (TE regs rg []) ss_Z
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_Z_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg F R18 R19 R27 HF0 HF1 HF32 Happ PF PSH.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := TE regs rg []).
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (X18 : bv_unsigned (ew E (xr 18)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
assert (X19 : bv_unsigned (ew E (xr 19)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19. apply unsigned_lit_small. lia. }
assert (X27 : bv_unsigned (ew E (xr 27)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 27%bv 27) by reflexivity. rewrite R27. apply unsigned_lit_small. lia. }
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 18) (shadow_addr F)); [exact X18 | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia | |
      constructor].
    intros o Ho. apply (apresent_writable SEGS). apply PSH. lia.
  + apply (ts_rok E _ (xr 27) F); [exact X27 | lia | lia | | constructor].
    intros o Ho. apply (apresent_writable SEGS). apply PF. lia.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X18, X27.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X18, X19, X27.
  change (2 ^ 5) with 32. change (2 ^ 0) with 1. unfold SHADOW_OFF in *. repeat split; lia.
Qed.

Lemma ct_F_entry : forall fxk (Wc : world SEGS) memc rg F fl,
  getr rg 19 = w64 F -> getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = getr regs 2 ->
  2 ^ 46 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  4096 <= F -> F + 512 <= sp0 - 104 -> F mod 32 = 0 ->
  0 <= fl -> fl + 1 <= sp0 - 104 -> (fl + 1 <= F + 504 \/ F + 512 <= fl) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + 504) 8 fl ->
  saved Wc memc ->
  apresent (w_H Wc) memc fl ->
  st_ok_pi SEGS VAL (TE regs rg [w64 fl]) ss_F
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_Z5_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg [w64 fl]) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg F fl R19 R3 R4 R8 G1 G2 G3 G4 G5 G6 G7 G8 VFL HSV PFL.
set (E := TE regs rg [w64 fl]).
assert (X19 : bv_unsigned (ew E (xr 19)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19. apply unsigned_lit_small. lia. }
assert (E64 : ew E 64 = w64 fl) by exact (te_more_lt regs rg [w64 fl] 0 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = fl) by (rewrite E64; apply unsigned_lit_small; lia).
assert (X2 : bv_unsigned (ew E 2) = sp0) by (unfold E; rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
assert (EN : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros r n Hn; unfold E; apply te_entry; exact Hn).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 fl]) with E.
- unfold sr_F.
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 2%bv 2%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R8].
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 4%bv 4%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R4].
  apply YI04.regs_ok_pin; [apply te_regs_ok | intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 3%bv 3%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R3].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 19) F); [exact X19 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 504 8 (SOff 64 0) fl);
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact VFL.
  + apply (ts_rok E _ 64 fl); [exact X64 | lia | lia | intros o Ho; apply (apresent_writable SEGS);
      replace (fl + o) with fl by lia; exact PFL | constructor].
  + apply (ts_rok E _ 2 sp0); [exact X2 | lia | lia | intros o Ho; lia |].
    unfold F_saves. repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let j := eval vm_compute in (Z.to_nat (- off / 8 - 1)) in
      let r := eval vm_compute in (nth j CRT_SAVED 0%bv) in
      apply (ts_chunk E _ _ off 8 (SOff n 0) (bv_unsigned (getr regs r)));
      [ cbn [sv_denot]; rewrite (EN r n) by reflexivity; rewrite Z.add_0_r; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs r)) as BR; change (bv_modulus 64) with (2 ^ 64) in BR; cbn; lia
      | cbn; lia
      | pose proof (HSV j ltac:(lia)) as V; change (nth j CRT_SAVED 0%bv) with r in V;
        replace (sp0 - 8 * (Z.of_nat j + 1)) with (sp0 + off) in V by (cbn; lia); exact V ]
    end.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X19, X64, X2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X19, X64, X2.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; lia.
Qed.

(* ---- F (+0x380): THE INLINE RELEASE, the epilogue and the `ret`, into QF ---- *)
Lemma ct_at_F : forall fxk ly2 S2 Hp2 W2 mem3 md3 k pos rg r WS,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem3 md3 k WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  bregs rg (frame_addr ly2 CRT_CID pos) -> getr rg 22 = w64 r ->
  saved W2 mem3 -> framed ly2 S2 W2 mem3 pos ->
  ct_qt ly2 S2 Hp2 W2 mem3 r ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem3) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_Z5_OFF))) mem3 (YK11.seg_rom SEGS)) md3)
    QFA.
Proof.
intros fxk ly2 S2 Hp2 W2 mem3 md3 k pos rg r WS HFZ HFK HJ HB HBR R22 HSV HFRM HQ HMN.
pose proof (crt_frame_listed HFRM) as Hin. pose proof (crt_frame_flag_word HFRM) as HFLW.
pose proof (crt_frame_present HFRM) as HFP.
(* the inline release (the engine's YGcallSx.aj_flag_store_xR, at RZW) is an empty-budget rule over ajournal_xR: the journal is rebased to
   the entry whose depot is the current one (YCbqGwild.ajournal_xw_rebaseR) and stepped back to WS after it
   (YCbqGwild.ajournal_xw_unbase0R, from the journal's wild clause Hinc) *)
pose proof (Crt102Kit.crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
(* frm_zero's Z.land / Z.shiftr body makes the unit's lia fail: keep it out of lia's sight *)
assert (HFZ' : unit -> frm_zero (@YK11.fp_csr fxk)) by (intros _; exact HFZ). clear HFZ.
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HROD & HSHI & HRAC & HFZ0).
(* fpre's entry rounding mode (frm_zero of the Section's fx): unused here, and its body stalls lia *)
clear HFZ0.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof crt_stk_A as (HSE & _). pose proof crt_stk_nonneg_A as (_ & _ & _ & HFRA & _).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR2 & HLY2 & _ & _ & _ & HFR2 & _).
destruct (frames_bounds_x _ _ _ LAWS ly2 S2 Hp2 W2 mem3 md3 CRT_CID pos HAR2 Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 mem3 md3 CRT_CID pos HAR2 Hin) as (F32 & _ & Ffr & Fsh).
rewrite ct_fb3 in Fb2, Fb3, Ffr, Fsh, HFLW, HFP.
destruct (FFLX ly2 S2 Hp2 W2 mem3 md3 CRT_CID pos HAR2 Hin) as (Fown & Fapp & Fimg).
pose proof (OWNLOW ly2 S2 Hp2 W2 mem3 md3 _ HAR2 Fown) as Flow.
pose proof (FFLP ly2 S2 Hp2 W2 mem3 md3 CRT_CID pos HAR2 Hin) as Fpr.
assert (Hflf : flag_addr ly2 CRT_CID pos + 1 <= frame_addr ly2 CRT_CID pos + 504 \/
  frame_addr ly2 CRT_CID pos + 512 <= flag_addr ly2 CRT_CID pos).
{ destruct (Z_lt_le_dec (flag_addr ly2 CRT_CID pos) (frame_addr ly2 CRT_CID pos)) as [Hl|Hl]; [left; lia|].
  destruct (Z_le_gt_dec (frame_addr ly2 CRT_CID pos + 512) (flag_addr ly2 CRT_CID pos)) as [Hg|Hg]; [right; lia|].
  exfalso. exact (proj2 (Ffr (flag_addr ly2 CRT_CID pos) ltac:(lia)) Fown). }
assert (VFL : val_mem SEGS (mrestrict (w_H W2) mem3) (frame_addr ly2 CRT_CID pos + 504) 8 (flag_addr ly2 CRT_CID pos)).
{ apply (val_mem_of_rdword SEGS). replace (frame_addr ly2 CRT_CID pos + 504) with (frame_addr ly2 CRT_CID pos + 512 - 8)
    by lia. exact HFLW. }
assert (R8' : getr rg 8 = getr regs 2) by (rewrite R8; unfold w64; apply Z_to_bv_bv_unsigned).
assert (Hsp0 : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
destruct (ct_F_entry fxk W2 mem3 rg (frame_addr ly2 CRT_CID pos) (flag_addr ly2 CRT_CID pos) R19 R3 R4 R8'
  Hsp0 Hal16 Fb1 ltac:(lia) F32 ltac:(lia) ltac:(lia) Hflf VFL HSV Fpr) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [w64 (flag_addr ly2 CRT_CID pos)])) by apply te_env.
assert (U64 : bv_unsigned (ew (TE regs rg [w64 (flag_addr ly2 CRT_CID pos)]) 64) = flag_addr ly2 CRT_CID pos).
{ rewrite (te_more_lt regs rg [w64 (flag_addr ly2 CRT_CID pos)] 0) by lia. cbn [nth]. apply unsigned_lit_small. lia. }
(* F's one write: the flag byte *)
assert (Hwr : forall a, in_wrange (TE regs rg [w64 (flag_addr ly2 CRT_CID pos)]) (ss_mem ss_F) a ->
  a = flag_addr ly2 CRT_CID pos).
{ intros a (rr & Hr & Ha). cbv [ss_F ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ts_bv_some in Ha.
  - lia.
  - rewrite U64 in Ha. lia.
  - lia. }
pose (FS := YGcallSx.aj_flag_store_xR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS pa_segs_low ASFX FFLX SFX
  asym pa_wx (clookup pa_tbl) VAL SIGMA A_prog_listing (@pl_tpi _ PL) (@pl_tw _ PL)
  pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text (@pl_lim _ PL) (@pl_len _ PL) (@pl_tpi_eq _ PL) (@pl_tw_eq _ PL)
  RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
lazymatch type of HS with st_ok_pi _ _ ?E ?ss _ =>
  let K := eval vm_compute in (run_K A_LIM (SLit 0) [] ss) in
  let rr := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss) in
  lazymatch rr with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss = (st', rs))
    by (vm_compute; reflexivity);
  eapply (FS W2 FUEL E K (SLit 0) (2 ^ 63, 2 ^ 63) [] ss st' rs _ STKC sp0 [] ly (set_depot (st_depot S2) S) Hp W mem
    md [] ly2 S2 Hp2 _ _
    CRT_CID pos _ ltac:(unfold A_LIM; cbn; lia) HEI ltac:(unfold CRT_CID; lia) HS SHOK ltac:(vm_compute; reflexivity)
    Hrun I HJr)
  end end.
- (* no inline check, no obligation *)
  match goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end. apply Forall_nil.
- (* the one write is the flag *)
  intros a HW. right. exact (Hwr a HW).
- (* the flag is 0 after the run *)
  intros ws msr Hlen HSr.
  pose proof (ts_region_nth _ _ _ 1 _ HSr eq_refl) as HR1.
  lazymatch type of HSr with st_ok_pi _ _ (extK ?E0 ?KK ?ws0) _ _ =>
    assert (X64 : bv_unsigned (ew (extK E0 KK ws0) 64) = flag_addr ly2 CRT_CID pos)
      by (rewrite (proj1 (env_agree_extK E0 KK ws0) 64%nat) by (cbv; lia); exact U64) end.
  pose proof (ts_field _ _ 64 (flag_addr ly2 CRT_CID pos) _ 0 1 0 1 0 1%N (SLit 0) HR1 X64
    ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0.
  rewrite V0. f_equal; try (rewrite U_SLit; apply bv_eq; vm_compute; reflexivity).
- (* the epilogue's `ret`: the text's post *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HFr1 HFr2 Hgr.
  cbn [ms_mem mkst] in HFr1, HFr2.
  assert (K' : forall a, 0 <= a < 2 ^ 64 -> a <> flag_addr ly2 CRT_CID pos ->
    aview SEGS (w_H W2) (ms_mem ms') a = aview SEGS (w_H W2) mem3 a)
    by (intros a Ha Hn; exact (ts_keep W2 _ (ss_mem ss_F) mem3 (ms_mem ms') _ HFr2 Hwr a Ha Hn)).
  pose proof HJ' as (HAR' & HLY' & _ & _ & _ & HFR' & _).
  prreg HS' (1%bv : bv 5) Q1. prreg HS' (10%bv : bv 5) Q10.
  assert (X1 : getr (ms_regs ms') 1 = getr regs 1).
  { rewrite Q1. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) 1 = _ =>
      rewrite (proj1 (env_agree_extK E0 KK ws0) 1%nat) by (cbv; lia) end.
    apply te_entry. reflexivity. }
  assert (X10 : getr (ms_regs ms') 10 = w64 r).
  { rewrite Q10. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) _ = _ =>
      rewrite (proj1 (env_agree_extK E0 KK ws0) 54%nat) by (cbv; lia) end.
    rewrite (te_cur regs rg _ 22%bv 22) by reflexivity. exact R22. }
  (* the memory is normal after the run (the keep of the frame-of phase, YGcallMxmn.v memnorm_frame_of) *)
  assert (HMN' : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS (ms_mem ms')).
  { intros H0. exact (memnorm_frame_of SEGS (w_H W2) _ _
      (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_Z5_OFF))) mem3 (YK11.seg_rom SEGS)) (ms_mem ms')
      (HMN H0) HS HFr1). }
  (* QT at the released state *)
  assert (HDF : forall f, In f (frames S) -> In f (frames (stack_free_state CRT_CID pos S2))).
  { intros f Hf. rewrite HFR'. exact Hf. }
  pose proof HJ as (_ & HLE2 & _).
  pose proof HJ' as (_ & HLE' & _).
  destruct (ct_doc_bytes ly2 S2 Hp2 W2 mem3 md3 _ HAR2 HLE2 ltac:(intros f Hf; rewrite HFR2; right; exact Hf))
    as (Hd0 & Hd1 & Hdb).
  destruct (ct_doc_bytes ly2 _ Hp2 W2 (ms_mem ms') _ _ HAR' HLE' HDF) as (_ & _ & Hdb').
  assert (HQ' : ct_qt ly2 (stack_free_state CRT_CID pos S2) Hp2 W2 (ms_mem ms') r).
  { apply (ct_qt_keep ly2 S2 (stack_free_state CRT_CID pos S2) Hp2 W2 mem3 (ms_mem ms') _ r
      (fun x => x = flag_addr ly2 CRT_CID pos) HQ HAR').
    - unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
    - apply RL_stack_free.
    - intros i h. apply PresetRoomPosKeep.room_pos_stack_free.
    - intros a Ha Hn. exact (K' a Ha Hn).
    - intros a ->. split; [|split].
      + intros Hps. exact (Fimg (crt_pst_img_A _ Hps)).
      + intros Hd. exact (proj1 (proj2 (Hdb _ Hd)) Fown).
      + intros p n Hpn Hr.
        destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem3 md3 p n HAR2 Hpn) as (_ & _ & _ & _ & Hb & _).
        exact (proj2 (Hb _ Hr) Fown).
    - intros a Ha. exact (proj1 (Hdb' a Ha)).
    - lia.
    - lia. }
  (* the `ret` is the plain runner's (YC1fP.paj_ret_at), lifted into SRr' *)
  apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (paj_ret_at (PL := PL) (PI := PA) W2 _ _ ms' _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
  intros mat''.
  (* QF is the text's BUDGETED post (kb round): the journal at crt_at_J's budget WS, wbudget [] (prh_wk
     F_check_round_trip) WS *)
  unfold QF, fpostFbm, fpostFb, YCbqGwild.apost_base_xbFR.
  exists fxk, ly2, (stack_free_state CRT_CID pos S2), Hp2, (ms_regs ms'), (ms_mem ms'). eexists. exists k, WS.
  split; [rewrite X1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [exact (HFZ' tt)|]. split; [exact HFK|]. split; [exact HB|].
  split; [eapply YCbqGwild.ajournal_xw_unbase0R; [|exact Hinc];
    apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) RZW); exact HJ'|].
  split.
  { eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (map (getr rg) all_regs ++ [w64 (flag_addr ly2 CRT_CID pos)]) HS');
      [| vm_compute; reflexivity].
    split.
    - intros n Hn. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) n = _ =>
        rewrite (proj1 (env_agree_extK E0 KK ws0) n) by lia end.
      unfold TE. apply Eimg_low. unfold A_TEXT. lia.
    - lazymatch goal with |- ed (extK ?E0 ?KK ?ws0) = _ => rewrite (proj2 (env_agree_extK E0 KK ws0)) end.
      reflexivity. }
  (* QF is fpostFm .. (fQmn mem QT) and fpostFm adds its own fQmn: the keep is asked twice *)
  split; [|exact HMN']. split; [|exact HMN'].
  destruct HQ' as ((HRL' & Lam' & peak' & cset & cnt' & ran' & own' & HPL' & HPA' & HPK' & Hcs & Hcs0 & HLED' &
    HDOC' & _ & HR') & HPE').
  unfold QT; cbv beta. split; [exact HRL'|].
  exists Lam', peak', cset, cnt', ran', own'.
  split; [exact HPL'|]. split; [exact HPA'|]. split; [exact HPK'|]. split; [exact Hcs|]. split; [exact Hcs0|].
  split; [exact HLED'|]. split; [exact HDOC'|].
  exists r. split; [exact X10|]. destruct HR' as (Hr00 & HR'). split; [exact Hr00|].
  destruct HR' as [HR1 | (Hr0 & Ho0 & Hc0 & Hra0)]; [left; exact HR1|].
  right. split; [exact Hr0|]. split; [exact Ho0|]. split; [exact Hc0|]. split; [exact Hra0|]. exact (HPE' Hr0).
Qed.

(* ---- Z (+0x348): copy's re-poison, the retired magic, the dead stack path, __asan_set_shadow_f5, then F ---- *)
Lemma ct_at_Z : forall fxk ly2 S2 Hp2 W2 mem2 md2 k pos rg r WS,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 k WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  bregs rg (frame_addr ly2 CRT_CID pos) -> getr rg 22 = w64 r ->
  saved W2 mem2 -> framed ly2 S2 W2 mem2 pos ->
  ct_qt ly2 S2 Hp2 W2 mem2 r ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_Z_OFF))) mem2 (YK11.seg_rom SEGS)) md2)
    QFA.
Proof.
intros fxk ly2 S2 Hp2 W2 mem2 md2 k pos rg r WS HFZ HFK HJ HB HBR R22 HSV HFRM HQ HMN.
assert (HFZ' : unit -> frm_zero (@YK11.fp_csr fxk)) by (intros _; exact HFZ). clear HFZ.
pose proof (crt_frame_listed HFRM) as Hin. pose proof (crt_frame_flag_word HFRM) as HFLW.
pose proof (crt_frame_present HFRM) as HFP.
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HROD & HSHI & HRAC & HFZ0).
(* fpre's entry rounding mode (frm_zero of the Section's fx): unused here, and its body stalls lia *)
clear HFZ0.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof crt_stk_A as (HSE & _). pose proof crt_stk_nonneg_A as (_ & _ & _ & HFRA & _).
pose proof crt_frame_A as (_ & _ & _ & _ & EFRA). unfold CRT_FRAME, CRT_ALIGN in EFRA.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof ct_base as (Hb0 & Hb1 & Hb4 & Hpc).
pose proof HJ as (HAR2 & HLY2 & _ & _ & _ & HFR2 & _).
destruct (ct_sp1_range Hal16 ltac:(lia)) as (Hsp1 & Hsp1m).
destruct (frames_bounds_x _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 CRT_CID pos HAR2 Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 CRT_CID pos HAR2 Hin) as (F32 & _ & Ffr & Fsh).
rewrite ct_fb3 in Fb2, Fb3, Ffr, Fsh, HFLW.
assert (Hshb : SHADOW_OFF <= shadow_addr (frame_addr ly2 CRT_CID pos) < SHADOW_OFF + 2 ^ 44)
  by (unfold shadow_addr, SHADOW_OFF; lia).
destruct (ct_Z_entry fxk W2 mem2 rg (frame_addr ly2 CRT_CID pos) R18 R19 R27 Fb1 ltac:(lia) F32 Fb3
  ltac:(intros a Ha; exact (proj1 (Ffr a ltac:(lia))))
  ltac:(intros a Ha; replace a with (shadow_addr (frame_addr ly2 CRT_CID pos) + (a - shadow_addr (frame_addr ly2 CRT_CID pos)))
          by lia; exact (proj1 (Fsh (a - shadow_addr (frame_addr ly2 CRT_CID pos)) ltac:(lia)))))
  as [HS SHOK].
pose proof HS as HS0.
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
assert (X18 : bv_unsigned (ew (TE regs rg []) (xr 18)) = shadow_addr (frame_addr ly2 CRT_CID pos)).
{ unfold xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
assert (X27 : bv_unsigned (ew (TE regs rg []) (xr 27)) = frame_addr ly2 CRT_CID pos).
{ unfold xr. rewrite (te_cur regs rg _ 27%bv 27) by reflexivity. rewrite R27. apply unsigned_lit_small. lia. }
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS WS).
paj_run_tok_x RUN HS HJ SHOK (2 ^ 63, 2 ^ 63).
{ (* Z's writes: the own frame's shadow (copy's seven bytes) and the own frame's first word *)
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 18) (shadow_addr (frame_addr ly2 CRT_CID pos)));
    [reflexivity | exact X18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists CRT_CID, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite ct_fb3. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 27) (frame_addr ly2 CRT_CID pos)); [reflexivity | exact X27 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists CRT_CID, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite ct_fb3. lia. }
  apply awr_ok_nil. }
(* after the run, at the `jal __asan_set_shadow_f5` (the `beqz s3` fell through: its condition is decided by
   s3's fact 4096 <= F, so no run of the stack path exists) *)
assert (Hwr : forall a, in_wrange (TE regs rg []) (ss_mem ss_Z) a ->
  (shadow_addr (frame_addr ly2 CRT_CID pos) + 28 <= a < shadow_addr (frame_addr ly2 CRT_CID pos) + 35) \/
  (frame_addr ly2 CRT_CID pos <= a < frame_addr ly2 CRT_CID pos + 8)).
{ intros a (rr & Hr & Ha). cbv [ss_Z ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ts_bv_some in Ha.
  - left. rewrite X18 in Ha. lia.
  - right. rewrite X27 in Ha. lia. }
assert (Kz : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((shadow_addr (frame_addr ly2 CRT_CID pos) + 28 <= a < shadow_addr (frame_addr ly2 CRT_CID pos) + 35) \/
     (frame_addr ly2 CRT_CID pos <= a < frame_addr ly2 CRT_CID pos + 8)) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha Hn; exact (ts_keep W2 _ (ss_mem ss_Z) mem2 (ms_mem ms) _ HFr Hwr a Ha Hn)).
assert (HMNz : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS (ms_mem ms)).
{ intros H0. exact (memnorm_frame_of SEGS (w_H W2) _ _
    (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_Z_OFF))) mem2 (YK11.seg_rom SEGS)) (ms_mem ms)
    (HMN H0) HS0 HF). }
prreg HS (10%bv : bv 5) Z10. prreg HS (11%bv : bv 5) Z11. prreg HS (1%bv : bv 5) Z1.
assert (KR : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 26; 27]%bv -> getr (ms_regs ms) r0 = getr rg r0).
{ intros r0 Hr0. cbv [In] in Hr0. repeat (destruct Hr0 as [<- | Hr0]; [ct_keep HS |]). destruct Hr0. }
assert (A10 : getr (ms_regs ms) 10 = w64 (shadow_addr (frame_addr ly2 CRT_CID pos))).
{ rewrite Z10. rewrite <- R18. te_close. }
assert (A11 : getr (ms_regs ms) 11 = w64 64) by (rewrite Z11; reflexivity).
assert (A1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + CRT_Z5_OFF))).
{ rewrite Z1. f_equal; try (vm_compute; reflexivity). }
assert (Asp : spZ (ms_regs ms) = sp0 + (sp1 - sp0)).
{ unfold spZ at 1. rewrite (KR 2%bv) by (cbv; tauto). rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HBRm : bregs (ms_regs ms) (frame_addr ly2 CRT_CID pos)).
{ refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
    crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
    crt_bregs_s11 := _ |}; rewrite KR by (cbv; tauto).
  - exact R2.
  - exact R3.
  - exact R4.
  - exact R8.
  - exact R9.
  - exact R18.
  - exact R20.
  - exact R19.
  - exact R23.
  - exact R26.
  - exact R27. }
assert (R22m : getr (ms_regs ms) 22 = w64 r) by (rewrite (KR 22%bv) by (cbv; tauto); exact R22).
pmkst HS.
(* __asan_set_shadow_f5's rule (the engine's YGcallMxmn.aj_set_shadow_at_xmR, at RZW; plain SRr, lifted by YA0nH.SRr_SRr') is over
   ajournal_xR: the journal rebased to the current depot and stepped back to WS after it (as ct_at_F's release) *)
pose proof (Crt102Kit.crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
eapply YSRrG.SRr'_bind.
{ apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  apply (YGcallMxmn.aj_set_shadow_at_xmR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) ENV
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    (SIGMA AS___asan_set_shadow_f5) 245 (SETSH fxk) W2 (ms_regs ms) (ms_mem ms) STKC sp0 [] ly
    (set_depot (st_depot S2) S) Hp W mem md
    [(CRT_CID, pos)] ly2 S2 Hp2 _ k CRT_CID pos (shadow_addr (frame_addr ly2 CRT_CID pos)) 64 (sp1 - sp0)
    (getr (ms_regs ms) 1) HJr (or_introl eq_refl) A10 A11 ltac:(lia) ltac:(lia) ltac:(rewrite ct_fb3; lia)
    Asp ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite (KR 3%bv) by (cbv; tauto); rewrite R3; exact Hgp)
    ltac:(rewrite (KR 4%bv) by (cbv; tauto); rewrite R4; exact Htp) eq_refl
    ltac:(rewrite A1; apply (ret_ok_codeptr_v (PI := PA)); [unfold CRT_Z5_OFF; lia | vm_compute; reflexivity])). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hf5 & Hkeep3 & HMN3).
eapply YCbqGwild.ajournal_xw_unbase0R in HJ3; [|exact Hinc].
rewrite A1.
pose proof HJ3 as (HAR3 & _).
(* the bytes both writes (the run's and the call's) left alone *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((shadow_addr (frame_addr ly2 CRT_CID pos) <= a < shadow_addr (frame_addr ly2 CRT_CID pos) + 64) \/
     (frame_addr ly2 CRT_CID pos <= a < frame_addr ly2 CRT_CID pos + 8)) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (Hkeep3 a Ha ltac:(intros Hc; apply Hn; left; exact Hc)).
  apply Kz; [exact Ha|]. intros [Hc | Hc]; apply Hn; [left; lia | right; exact Hc]. }
apply (ct_at_F fxk ly2 S2 Hp2 W2 mem3 md3 k pos regs3 r WS (HFZ' tt) HFK HJ3 HB).
- exact (ct_bregs_pres _ _ _ HBRm HP3).
- rewrite (ts_ap _ _ 22%bv HP3) by ts_cs. exact R22m.
- intros j Hj. pose proof (HSV j Hj) as V. eapply ts_vm_av; [|exact V].
  intros i Hi. apply K3; [lia|].
  unfold shadow_addr, SHADOW_OFF in *. intros [Hc | Hc]; lia.
- refine {| crt_frame_listed := Hin; crt_frame_flag_word := _; crt_frame_present := _ |}.
  + rewrite <- HFLW. apply ts_rdword_keep. intros j Hj. apply K3; [lia|]. intros [Hc | Hc]; [|lia].
    unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia.
  + intros a Ha. destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 mem3 md3 CRT_CID pos HAR3 Hin) as (_ & _ & Ffr3 & _).
    exact (proj1 (Ffr3 a Ha)).
- pose proof HJ as (_ & HLE2 & _).
  destruct (ct_doc_bytes ly2 S2 Hp2 W2 mem2 md2 _ HAR2 HLE2 ltac:(intros f Hf; rewrite HFR2; right; exact Hf))
    as (Hd0 & Hd1 & Hdb).
  destruct (ct_doc_bytes ly2 S2 Hp2 W2 mem3 md3 _ HAR3 HLE2 ltac:(intros f Hf; rewrite HFR2; right; exact Hf))
    as (_ & _ & Hdb3).
  destruct (ct_doc_frame ly2 S2 _ HLE2 ltac:(intros f Hf; rewrite HFR2; right; exact Hf))
    as (cid0 & pos0 & Hin0 & Hin0' & Hd2 & Hd3).
  apply (ct_qt_keep ly2 S2 S2 Hp2 W2 mem2 mem3 md3 r
    (fun a => (shadow_addr (frame_addr ly2 CRT_CID pos) <= a < shadow_addr (frame_addr ly2 CRT_CID pos) + 64) \/
              (frame_addr ly2 CRT_CID pos <= a < frame_addr ly2 CRT_CID pos + 8)) HQ HAR3 eq_refl (fun H => H)
    (fun i h H => H) K3).
  + intros a [Hc | Hc].
    * split; [|split].
      -- intros Hps. pose proof (@pa_segs_low _ _ PA a (crt_pst_img_A a Hps)) as Hlow.
         unfold kLowMemEnd, shadow_addr, SHADOW_OFF in *. lia.
      -- intros Hd. pose proof (proj2 (proj2 (proj2 (Hdb a Hd)))) as Happ.
         unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia.
      -- intros p n Hpn Hr.
         destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 p n HAR2 Hpn) as (_ & _ & _ & Happ & _).
         unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia.
    * split; [|split].
      -- intros Hps. exact (frm_img_x _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 CRT_CID pos a HAR2 Hin
           ltac:(rewrite ct_fb3; lia) (crt_pst_img_A a Hps)).
      -- intros Hd. rewrite HFR2 in Hin0'. cbn [app] in Hin0'.
         apply in_split in Hin0 as (l1 & l2 & El).
         pose proof (sep_frames_pos_x _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 (CRT_CID, pos) (cid0, pos0) [] l1 l2 HAR2
           ltac:(rewrite HFR2, El; reflexivity)) as Hdj.
         unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj. rewrite ct_fb3 in Hdj.
         pose proof (fs_frame_bytes_nonneg cid0). lia.
      -- intros p n Hpn Hr.
         pose proof (sep_block_frame_x _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 p n CRT_CID pos HAR2 Hpn Hin) as Hdj.
         unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite ct_fb3 in Hdj. lia.
  + intros a Ha. exact (proj1 (Hdb3 a Ha)).
  + lia.
  + lia.
- intros H0. exact (HMN3 (HMNz H0)).
Qed.

(* ---- J (+0x340): `mv a0, s4; jal pj_free` - the run and the call of the tpj_free_specX text at n = DOC_D
   (PRH_FnPj.v 908f34f0beaa), GIVEN copy's order list F and the class-24 bound at the join, its one room premise for a
   non-NULL argument (position-free). Its post is the state at +0x348 that ct_at_Z takes, with ct_qt0 (QT without its
   r = 0 position) and the text's POSITION TRANSFER: every position at Sc whose next events are prhPj_free_evs F
   advances exactly by them at S2. pj_free's post gives the blocks back (Lam' with Lamc ~ Dc ++ Lam', ablocks with
   Dc's removed) and the ledger at S2 with the same g_most / g_own_ran_out cells (the E sweep put them in prh_ledger):
   that is how QT's two cells cross the join. ---- *)
Lemma ct_J_call : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r (F : list (Z * Z)),
  JA fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget Sc [] ->
  pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc F ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
    (crt_cfg (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A) fxk CRT_J_OFF rg memc mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k,
       c2 = mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_Z_OFF))) mem2 (YK11.seg_rom SEGS)) md2 /\
       (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 k WS /\
          YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS) /\
       bregs regs2 (frame_addr ly2 CRT_CID pos) /\ getr regs2 22 = w64 r /\
       saved W2 mem2 /\ framed ly2 S2 W2 mem2 pos /\ ct_qt0 ly2 S2 Hp2 W2 mem2 r /\
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist Sc -> prh_run_at sm x os i (prhPj_free_evs F) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPj_free_evs F))%nat H0 hist' S2) /\
       (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r F HJA HC24 HHB HFO.
pose proof (crt_at_J_live HJA) as HL. pose proof (crt_at_J_frm_zero HJA) as HFZ.
pose proof (crt_at_J_fregs HJA) as HFK. pose proof (crt_at_J_bregs HJA) as HBR.
pose proof (crt_at_J_ret HJA) as R22. pose proof (crt_at_J_copy_fd HJA) as HFD.
pose proof (crt_at_J_r0 HJA) as Hr00. pose proof (crt_at_J_count HJA) as HCS.
(* frm_zero's Z.land / Z.shiftr body makes the unit's lia fail: kept behind a thunk for pj_free's fpre, whose fifth
   conjunct is the entry rounding mode of the arms' float state fxk; fregs_kept_x is not used here *)
assert (HFZ' : unit -> frm_zero (@YK11.fp_csr fxk)) by (intros _; exact HFZ). clear HFZ HFK.
destruct (crt_live_journal HL) as (WSJ & HJ & HBJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPA.
pose proof (crt_live_dx_apart HL) as HDA. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSP.
pose proof (crt_live_copy_open HL) as HRA. pose proof (crt_live_copy_hull HL) as HHV.
pose proof (crt_live_memnorm HL) as HMN.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK.
pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HROD.
pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof (crt_frame_listed HFRM) as Hin. pose proof (crt_frame_flag_word HFRM) as HFLW.
pose proof (crt_frame_present HFRM) as HFP. rewrite ct_fb3 in HFLW, HFP.
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HROD0 & HSHI & HRAC & HFZ0).
clear HFZ0.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof crt_stk_A as (HSE & _ & _ & _ & _ & _ & _ & _ & HSPF & _).
pose proof crt_stk_nonneg_A as (_ & _ & _ & HFRA & _ & _ & _ & _ & _ & HSPF0 & _).
pose proof crt_frame_A as (_ & _ & _ & _ & EFRA). unfold CRT_FRAME, CRT_ALIGN in EFRA.
pose proof ct_base as (Hb0 & Hb1 & Hb4 & HPCr).
destruct (ct_sp1_range Hal16 ltac:(lia)) as (Hsp1 & Hsp1m).
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _ & _ & HJst & _).
pose proof HLYc as (_ & _ & _ & _ & _ & EFc & _ & _ & Etopc & Eloc & Ehic & _).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (F32 & _ & Ffr & Fsh).
rewrite ct_fb3 in Fb2, Fb3, Ffr, Fsh.
unfold crt_cfg.
(* ---- J: `mv a0, s4; jal pj_free` - no region, the memory is unchanged ---- *)
assert (HS : st_ok_pi SEGS VAL (TE regs rg []) ss_J
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_J_OFF))) memc (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS WSJ).
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ cbv [ss_J ss_mem]. apply awr_ok_nil. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity]. clear HFr HG.
rewrite <- HF in HLED, HROD, HDOC, HFD, HFO, HRA, HHV, HSV, HFLW, HFP, HMN, HJst.
prreg HS (10%bv : bv 5) Z10. prreg HS (1%bv : bv 5) Z1.
assert (KR : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 26; 27]%bv -> getr (ms_regs ms) r0 = getr rg r0).
{ intros r0 Hr0. cbv [In] in Hr0. repeat (destruct Hr0 as [<- | Hr0]; [ct_keep HS |]). destruct Hr0. }
assert (A10 : getr (ms_regs ms) 10 = w64 (frame_addr lyc CRT_CID pos + CRT_OFF_COPY)).
{ rewrite Z10. rewrite <- R20. te_close. }
assert (A1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + CRT_Z_OFF))).
{ rewrite Z1. f_equal; try (vm_compute; reflexivity). }
assert (Asp : spZ (ms_regs ms) = sp0 + (sp1 - sp0)).
{ unfold spZ at 1. rewrite (KR 2%bv) by (cbv; tauto). rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HBRm : bregs (ms_regs ms) (frame_addr lyc CRT_CID pos)).
{ refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
    crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
    crt_bregs_s11 := _ |}; rewrite KR by (cbv; tauto).
  - exact R2.
  - exact R3.
  - exact R4.
  - exact R8.
  - exact R9.
  - exact R18.
  - exact R20.
  - exact R19.
  - exact R23.
  - exact R26.
  - exact R27. }
assert (R22m : getr (ms_regs ms) 22 = w64 r) by (rewrite (KR 22%bv) by (cbv; tauto); exact R22).
(* the callee's frame-pointer chain: s0 = the entry sp, the saved ra and s0 below it, the entry's chain above *)
assert (Hch1 : exists ch1, achain lyc (aview SEGS (w_H Wc) (ms_mem ms)) (sp0 + (sp1 - sp0)) (s0Z (ms_regs ms)) ch1).
{ replace (sp0 + (sp1 - sp0)) with sp1 by lia.
  assert (Hs0 : s0Z (ms_regs ms) = sp0).
  { unfold s0Z. rewrite (KR 8%bv) by (cbv; tauto). rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
  rewrite Hs0.
  destruct (Z_lt_le_dec sp0 (ly_top lyc - 16)) as [Hlt | Hge].
  - exists ((sp0, raZ regs, s0Z regs) :: ch).
    apply (achain_push lyc (aview SEGS (w_H W) mem) (aview SEGS (w_H Wc) (ms_mem ms)) sp0 (s0Z regs) (raZ regs) ch sp1).
    + apply (achain_ly_top ly lyc); [exact Etopc | exact Hch].
    + rewrite Etopc. lia.
    + intros a Ha. apply HJst; lia.
    + pose proof (HSV 0%nat ltac:(lia)) as V0. change (nth 0 CRT_SAVED 0%bv) with (1%bv : bv 5) in V0.
      replace (sp0 - 8 * (Z.of_nat 0 + 1)) with (sp0 - 8) in V0 by lia.
      apply (ct_rdword_of_vm SEGS) in V0; [exact V0|].
      pose proof (bv_unsigned_in_range 64 (getr regs 1)) as BR. change (bv_modulus 64) with (2 ^ 64) in BR. exact BR.
    + pose proof (HSV 1%nat ltac:(lia)) as V1. change (nth 1 CRT_SAVED 0%bv) with (8%bv : bv 5) in V1.
      replace (sp0 - 8 * (Z.of_nat 1 + 1)) with (sp0 - 16) in V1 by lia.
      apply (ct_rdword_of_vm SEGS) in V1; [exact V1|].
      pose proof (bv_unsigned_in_range 64 (getr regs 8)) as BR. change (bv_modulus 64) with (2 ^ 64) in BR. exact BR.
    + exact Hra4.
    + lia.
    + lia.
    + exact Hlt.
    + lia.
  - exists []. left. split; [right; left; exact Hge | reflexivity]. }
destruct Hch1 as (ch1 & Hch1).
(* THE REQUEST BOUND AT THIS CALL. pj_free makes no allocator request (its calls are fuzz_free only), so no request of
   it can exceed g_most and no refusal can set g_ran_out: tpj_free_specX's ledger post is true with the bound as it
   stands, and that is what makes citing it here legitimate. The bound is carried to the call explicitly
   (Crt102Model.v's cm_rqa_nonneg reads it at this site) and is not consumed. *)
pose proof (Crt102Model.cm_rqa_nonneg t most HRQA) as HRQ0.
eapply YSRrG.SRr'_bind.
{ (* the caller's journal is at crt_at_J's budget WSJ: the budgeted window call rule at the callee's empty budget,
     P := (fun WS1 => WS1 = []), at RZW (YCbqGwild.aj_call_xWb_spR); pj_free's post (fpostWmR at wle', the text's
     re-hiding form) by YCbqGwild.fpostW_xb_of_xR *)
  eapply (YCbqGwild.aj_call_xWb_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) RZW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc _ _ ms STKC sp0 []
    ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc _ kj WSJ STKPF 0 _ (sp1 - sp0) (getr (ms_regs ms) 1) ch1
    (fun WS1 => WS1 = []) _ HS eq_refl HJ Asp
    ltac:(lia) ltac:(lia) HSPF0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite (KR 3%bv) by (cbv; tauto); rewrite R3; exact Hgp)
    ltac:(rewrite (KR 4%bv) by (cbv; tauto); rewrite R4; exact Htp) eq_refl
    ltac:(rewrite A1; apply (ret_ok_codeptr_v (PI := PA)); [unfold CRT_Z_OFF; lia | vm_compute; reflexivity])
    ltac:(rewrite A1; rewrite unsigned_lit_small; [unfold CRT_Z_OFF; lia | unfold CRT_Z_OFF; lia]) Hch1).
  - (* the callee: the tpj_free_specX text at n = DOC_D, window 0, v = &copy *)
    intros HPRE1 HWIN1.
    assert (HSLOT : prhPj_slot B STKPF 0 lyc Sc Lamc Wc (ms_regs ms) (ms_mem ms)
      (frame_addr lyc CRT_CID pos + CRT_OFF_COPY)).
    { unfold prhPj_slot, CRT_OFF_COPY in *.
      split; [lia|].
      split; [right; right; left; exists CRT_CID, pos; split; [exact Hin|]; rewrite ct_fb3; lia|].
      split.
      { split; [lia|]. intros x Hx. apply (apresent_writable SEGS). exact (HFP x ltac:(lia)). }
      split.
      { unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd, ASAN_CEIL in *. lia. }
      split.
      { intros a Ha. split; [exact (proj2 (Ffr a ltac:(lia)))|]. rewrite Asp. lia. }
      split; [exact HRA | exact HHV]. }
    lazymatch type of HPRE1 with afn_pre_x _ _ _ _ _ _ _ _ _ _ ?mdj _ =>
    assert (HFPRE : fpre (fx := fxk) B ARx STKPF lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdj ch1)
    end.
    { split; [exact HPRE1|]. split; [exact HROD|]. split; [rewrite Asp, Ehic; lia|]. split.
      - unfold raZ. rewrite A1, unsigned_lit_small; unfold CRT_Z_OFF; lia.
      - exact (HFZ' tt). }
    eapply YSRrG.SRr'_mono.
    { apply (PJFREE fxk most ownc lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 0
        (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc F Lamc peakc cntc SIZE_MAXZ ranc
        HFPRE HCL HRL (fun _ => HC24) (fun _ => HHB) A10 HWIN1);
        [| exact CfParamsPreset.preset_head_wide | exact HLED].
      right. split; [unfold CRT_OFF_COPY; lia|]. split; [unfold CRT_OFF_COPY; lia|]. split; [exact HFO | exact HSLOT]. }
    intros W' c' _ Hpo. apply YCbqGwild.fpostW_xb_of_xR; [reflexivity | exact Hpo].
  - (* pj_free's footprint: copy's 56 bytes (a slot of the own frame) and Dc's blocks (taken since the entry) *)
    intros a Ha.
    rewrite (proj2 (Z.eqb_neq (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) 0) ltac:(unfold CRT_OFF_COPY; lia)) in Ha.
    apply inFP_cons in Ha as [Ha | (rr & Hrr & Ha)].
    + right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite ct_fb3. unfold CRT_OFF_COPY in Ha. lia.
    + right; left. unfold ablocks_fp, prhPj_hbl in Hrr. rewrite map_map in Hrr.
      apply in_map_iff in Hrr as ((a0 & k0) & <- & Hak). cbn [fst snd] in Ha.
      assert (HinL : In (a0, k0) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hak).
      pose proof (prh_ledger_blocks B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc SIZE_MAXZ ranc most ownc HLED) as HFB.
      rewrite Forall_forall in HFB. destruct (HFB (a0, k0) HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
      exists (a0 - cf_head), (k0 + cf_head). split; [exact Hab|]. split; [|exact Ha].
      intros Hold.
      destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & _ & _ & _ & _ & Hpw).
      pose proof (ct_pairwise_perm _ zdisjoint (fun x y H => ltac:(unfold zdisjoint in *; lia)) _ _
        (Permutation_map (fun b => (fst b, req_size (snd b))) HPA) Hpw) as Hpw'.
      rewrite map_app in Hpw'.
      pose proof (ct_pairwise_app_dup _ zdisjoint _ _ ((a0 - cf_head), req_size (k0 + cf_head)) Hpw'
        ltac:(apply (in_map (fun b => (fst b, req_size (snd b))) _ _ Hold))
        ltac:(apply (in_map (fun b => (fst b, req_size (snd b))) (ck_hblks Dc) (a0 - cf_head, k0 + cf_head));
              unfold ck_hblks; apply (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) Dc (a0, k0) Hak)))
        as Hself.
      unfold zdisjoint in Hself. cbn [fst snd] in Hself. change (@cf_head CfParams_preset) with 16 in *.
      pose proof (req_size_pos (k0 + 16) ltac:(lia)). lia. }
cbv beta. intros W2 c2 HWle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ2 & HJ1 & HX & HP & HQ).
subst WS1. rewrite app_nil_r in HJ2.
(* pj_free's post (the text's Q, PRH_FnPj.tpfP_Q) read through its named projections (tpfP_R), never by position: the
   room, THE HULL USE (frees keep both meters; not read past the call), the position transfer, the blocks and the
   ledger *)
destruct HQ as (HQ & HMN2).
apply PRH_FnPj.tpfP_R_of with (regs' := regs2) (md' := md2) in HQ. destruct HQ as (Lam' & HQR).
pose proof (PRH_FnPj.tpfP_room HQR) as HRL2. pose proof (PRH_FnPj.tpfP_pos HQR) as HTR.
pose proof (PRH_FnPj.tpfP_lam HQR) as HPerm'. pose proof (PRH_FnPj.tpfP_ablocks HQR) as HAbl'.
pose proof (PRH_FnPj.tpfP_ledger HQR) as HLED2. pose proof (PRH_FnPj.tpfP_zero HQR) as HZ.
pose proof (PRH_FnPj.tpfP_ccnt24 HQR) as HC24'.
rewrite A1.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & HFR2 & _).
pose proof HJ1 as (_ & HLY1 & _ & _ & _ & _ & _ & _ & K1st & K1blk & _ & K1frm & _).
assert (EF : forall cid p, frame_addr ly2 cid p = frame_addr lyc cid p).
{ intros cid p. unfold frame_addr. destruct HLY1 as (_ & _ & _ & _ & _ & EF2 & _). rewrite EF2. reflexivity. }
assert (EFL : flag_addr ly2 CRT_CID pos = flag_addr lyc CRT_CID pos).
{ unfold flag_addr. destruct HLY1 as (_ & _ & _ & _ & _ & EF2 & _). rewrite EF2. reflexivity. }
assert (Hin2 : In (CRT_CID, pos) (frames S2)) by (rewrite HFR2; left; reflexivity).
(* the callee's footprint, named *)
set (FP1 := (frame_addr lyc CRT_CID pos + CRT_OFF_COPY, frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 56)
  :: ablocks_fp (prhPj_hbl Dc)) in *.
assert (HnFP : forall a, ~ (frame_addr lyc CRT_CID pos + CRT_OFF_COPY <= a < frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 56) ->
  (forall a0 k0, In (a0, k0) Dc -> ~ (a0 - 16 <= a < a0 - 16 + req_size (k0 + 16))) ->
  ~ inFP (if frame_addr lyc CRT_CID pos + CRT_OFF_COPY =? 0 then [] else FP1) a).
{ intros a H1 H2 Hf.
  rewrite (proj2 (Z.eqb_neq (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) 0) ltac:(unfold CRT_OFF_COPY; lia)) in Hf.
  unfold FP1 in Hf. apply inFP_cons in Hf as [Hf | (rr & Hrr & Hf)]; [exact (H1 Hf)|].
  unfold ablocks_fp, prhPj_hbl in Hrr. rewrite map_map in Hrr.
  apply in_map_iff in Hrr as ((a0 & k0) & <- & Hak). cbn [fst snd] in Hf.
  change (@cf_head CfParams_preset) with 16 in Hf. exact (H2 a0 k0 Hak Hf). }
(* a Dc block meets neither the own frame nor a block that is not Dc's *)
assert (HDcF : forall a0 k0 cid p a, In (a0, k0) Dc -> In (cid, p) (frames Sc) ->
  frame_addr lyc cid p <= a < frame_addr lyc cid p + fs_frame_bytes cid ->
  ~ (a0 - 16 <= a < a0 - 16 + req_size (k0 + 16))).
{ intros a0 k0 cid p a Hak Hcp Ha Hr.
  assert (HinL : In (a0, k0) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hak).
  pose proof (prh_ledger_blocks B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc SIZE_MAXZ ranc most ownc HLED) as HFB.
  rewrite Forall_forall in HFB. destruct (HFB (a0, k0) HinL) as (_ & Hab & _). cbn [fst snd] in Hab.
  change (@cf_head CfParams_preset) with 16 in Hab.
  pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ cid p HARc Hab Hcp) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
apply YSRrG.SRr'_ret. exists ly2, S2, Hp2, regs2, mem2, md2, (kj + k1).
split; [first [reflexivity | rewrite <- A1; reflexivity]|].
split; [exists WSJ; split; [exact HJ2 | exact HBJ]|].
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
- rewrite EF. exact (ct_bregs_pres _ _ _ HBRm HP).
- rewrite (ts_ap _ _ 22%bv HP) by ts_cs. exact R22m.
- (* the saves: the real stack above the callee's window *)
  intros j Hj. pose proof (HSV j Hj) as V. eapply ts_vm_av; [|exact V].
  intros i Hi. apply K1st; lia.
- refine {| crt_frame_listed := Hin2; crt_frame_flag_word := _; crt_frame_present := _ |}.
  + rewrite EF, EFL, ct_fb3. rewrite <- HFLW. apply ts_rdword_keep. intros j Hj.
    apply (K1frm CRT_CID pos); [exact Hin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite ct_fb3; lia|].
    apply HnFP; [unfold CRT_OFF_COPY; lia|]. intros a0 k0 Hak.
    apply (HDcF a0 k0 CRT_CID pos); [exact Hak | exact Hin | rewrite ct_fb3; lia].
  + intros a Ha. destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 CRT_CID pos HAR2 Hin2) as (_ & _ & Ffr2 & _).
    exact (proj1 (Ffr2 a Ha)).
- (* QT's facts after pj_free, its r = 0 position aside *)
  destruct HCS as (cset & Hcs & Hcs0 & HR).
  assert (HPLam : Permutation Lam' Lam).
  { apply (Permutation_app_inv_l Dc). exact (Permutation_trans (Permutation_sym HPerm') HPL). }
  assert (HDL' : forall bk, In bk D -> In bk Lam').
  { intros bk Hbk. pose proof (Permutation_in _ HPerm' (HDL bk Hbk)) as H1. apply in_app_or in H1 as [H1 | H1];
      [exfalso; exact (HDA bk H1 Hbk) | exact H1]. }
  split; [exact HRL2|].
  exists Lam', peakc, cset, cntc, ranc, ownc.
  split; [exact HPLam|].
  split.
  { change (prhPj_hbl Dc) with (ck_hblks Dc) in HAbl'.
    apply (Permutation_app_inv_l (ck_hblks Dc)).
    exact (Permutation_trans (Permutation_sym HAbl') (Permutation_trans HPA (Permutation_app_comm _ _))). }
  split; [exact HPK|]. split; [exact Hcs|]. split; [exact Hcs0|]. split; [exact HLED2|].
  split.
  { (* the document: its blocks are Lam''s, and its bytes are outside pj_free's footprint *)
    pose proof (ct_nodeR_lblk SEGS t _ (prh_lin Lamc) (prh_lin Lam') doc D HDOC
      ltac:(intros x k Hx _; unfold prh_lin; exact (HDL' (x, k) Hx))) as HDOC1.
    pose proof HJ as (_ & HLE0 & _).
    destruct (ct_doc_frame lyc Sc _ HLE0 ltac:(intros f Hf; rewrite HFRc; right; exact Hf))
      as (cid0 & pos0 & Hin0 & Hin0c & Hd2 & Hd3).
    pose proof HJ2 as (_ & HLE2 & _).
    destruct (ct_doc_bytes ly2 S2 Hp2 W2 mem2 md2 _ HAR2 HLE2 ltac:(intros f Hf; rewrite HFR2; right; exact Hf))
      as (Hd0 & Hd1 & Hdb2).
    assert (Hdisj0 : frame_addr lyc cid0 pos0 + fs_frame_bytes cid0 <= frame_addr lyc CRT_CID pos \/
      frame_addr lyc CRT_CID pos + 512 <= frame_addr lyc cid0 pos0).
    { rewrite HFRc in Hin0c. apply in_split in Hin0 as (l1 & l2 & El).
      pose proof (sep_frames_pos_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc (CRT_CID, pos) (cid0, pos0) [] l1 l2 HARc
        ltac:(rewrite HFRc, El; reflexivity)) as Hdj.
      unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj. rewrite ct_fb3 in Hdj. lia. }
    apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) (ms_mem ms)) (mrestrict (w_H W2) mem2) (prh_lin Lam') doc D HDOC1).
    intros x [Hx | ((a, k) & Hb & Hx)].
    - split.
      + apply (mbyte_of_aview SEGS). apply (K1frm cid0 pos0); [rewrite HFRc; right; exact Hin0 |
          left; unfold in_zr, frame_rng; cbn [fst snd]; lia |].
        apply HnFP; [unfold CRT_OFF_COPY; lia|]. intros a0 k0 Hak.
        apply (HDcF a0 k0 cid0 pos0); [exact Hak | rewrite HFRc; right; exact Hin0 | lia].
      + intros _. apply (apresent_writable SEGS). exact (proj1 (Hdb2 x Hx)).
    - unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      assert (HinL : In (a, k) Lamc) by exact (HDL _ Hb).
      pose proof (prh_ledger_blocks B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc SIZE_MAXZ ranc most ownc HLED) as HFB.
      rewrite Forall_forall in HFB. destruct (HFB (a, k) HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
      pose proof (prh_ledger_blocks B ly2 S2 Hp2 W2 mem2 Lam' peakc cntc SIZE_MAXZ ranc most ownc HLED2) as HFB2.
      rewrite Forall_forall in HFB2. destruct (HFB2 (a, k) (HDL' _ Hb)) as (_ & Hab2 & _). cbn [fst snd] in Hab2.
      change (@cf_head CfParams_preset) with 16 in Hab, Hab2.
      assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
      replace x with (a - 16 + (x - (a - 16))) by lia.
      split.
      + apply (mbyte_of_aview SEGS). apply (K1blk (a - 16) (k + 16)); [exact Hab | exact Hab2 | lia |].
        apply HnFP.
        * pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hab Hin) as Hd.
          unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite ct_fb3 in Hd. unfold CRT_OFF_COPY. lia.
        * intros a0 k0 Hak.
          assert (HinL0 : In (a0, k0) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app;
            left; exact Hak).
          destruct (HFB (a0, k0) HinL0) as (_ & Hab0 & _). cbn [fst snd] in Hab0.
          change (@cf_head CfParams_preset) with 16 in Hab0.
          assert (Hne : (a0 - 16, k0 + 16) <> (a - 16, k + 16)).
          { intros E. injection E as E1 E2. assert (a0 = a) by lia. assert (k0 = k) by lia. subst a0 k0.
            exact (HDA _ Hak Hb). }
          pose proof (sep_blocks_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hab0 Hab Hne) as Hd.
          unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
      + intros _. apply (apresent_writable SEGS).
        destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hbb & _).
        exact (proj1 (Hbb (a - 16 + (x - (a - 16))) ltac:(lia))). }
  split; [exact HDL'|].
  (* r = 0 (crt_at_J states it; the r = 1 arm is dead under the text's prh_cons_from), then crt_at_J's arms in QT's
     order (crt_at_J states the r = 0 arm as `ranc = ran /\ cntc = ..`) *)
  split; [exact Hr00|].
  destruct HR as [HR1 | (Hr0 & Ho0 & Hra0 & Hc0 & _)]; [left; exact HR1 | right; exact (conj Hr0 (conj Ho0 (conj Hc0 Hra0)))].
- (* the position transfer pj_free's text gives: the EXACT advance by its own events *)
  exact HTR.
- intros H0. exact (HMN2 (HMN H0)).
Qed.

(* ---- THE r = 0 END POSITION. crt_at_J's r = 0 field (Crt102Glue.v 1f62ff8af3df) ties copy's blocks to tblk
   crt_tree_J UP TO PERMUTATION only (the model ties the live set to the run only up to permutation, and the reader's
   allocation order differs from tblk's pre-order, so no ordered block fact is available at any instance); with
   PresetReqAtNoMiss.fo_tblk that is a permutation of pj_free's request list against fo crt_tree_J, the model's HBulk.
   GIVEN the run premise for pj_free's own events, the position transfer lands at QT's end position: one bulk event advances by one; an empty order list makes no event, its permutation forces fo = [],
   and the model's HBulk [] is stepped over (prhPj_bulk_nil_pos). ---- *)
#[local] Notation ctJ := (crt_tree_J (t := t)).
Lemma ct_evs_J : crt_evs_J (t := t) = [PresetReqAt.HBulk (PresetReqAt.fo ctJ)].
Proof. unfold crt_evs_J, crt_tree_J. destruct t; reflexivity. Qed.
Lemma ct_r0_end : forall pre (F : list (Z * Z)),
  PresetReqAt.round_trip rp_sm t = pre ++ crt_evs_J (t := t) ->
  prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat (crt_evs_J (t := t)) ->
  Permutation (map (fun b => snd b + cf_head) F) (PresetReqAt.fo ctJ) ->
  forall S2 h, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length pre + length (prhPj_free_evs F))%nat
    rp_H0 h S2 -> ct_pos_end S2.
Proof.
intros pre F Epre Hrun Hperm S2 h HP.
rewrite ct_evs_J in Epre, Hrun.
assert (EL : (rp_i + length (PresetReqAt.round_trip rp_sm t))%nat = Datatypes.S (rp_i + length pre)%nat)
  by (rewrite Epre, length_app; cbn [length]; lia).
unfold ct_pos_end. rewrite EL.
destruct F as [|b F'].
- (* no blocks: fo crt_tree_J = [], and the model's HBulk [] is stepped over *)
  cbn [map] in Hperm. apply Permutation_nil in Hperm. rewrite Hperm in Hrun.
  cbn [prhPj_free_evs length] in HP. rewrite Nat.add_0_r in HP.
  apply (proj1 (prh_run_at_one rp_sm rp_x rp_os _ _)) in Hrun.
  exists h. exact (proj1 (prhPj_bulk_nil_pos rp_sm rp_x rp_os _ rp_H0 h S2 Hrun) HP).
- (* the one bulk event *)
  cbn [prhPj_free_evs length] in HP. exists h.
  replace (Datatypes.S (rp_i + length pre)) with (rp_i + length pre + 1)%nat by lia. exact HP.
Qed.

(* ---- THE TAIL, composed: J (+0x340) .. the `ret`, the statement the glue fixes. Every piece above is its own Qed
   lemma (ct_J_call, ct_r0_end, ct_at_Z, ct_at_F, ct_qt_keep); this script applies them. The r = 1 arm is DEAD
   (crt_at_J states r = 0: tcheck_round_trip_specX kills it under its entry premise prh_cons_from). The r = 0 arm reads
   copy's ORDERED free list Fc from crt_at_J (Crt102Glue.v 5f20c5d5048f): a free list is ordered, only the block list
   tblk is multiset-only, and the position after pj_free reads HBulk in order (cf_frees_follow / quar_fifo_cf), so
   the order is what makes pj_free's events the model's own. NO OPEN GOAL. ---- *)
Theorem crt102_tail : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  JA fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
    (crt_cfg (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A) fxk CRT_J_OFF rg memc mdc) QFA.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HJA.
pose proof (crt_at_J_frm_zero HJA) as HFZ. pose proof (crt_at_J_fregs HJA) as HFK.
destruct (crt_at_J_count HJA) as (cset & _ & _ & HR).
assert (HFZ' : unit -> frm_zero (@YK11.fp_csr fxk)) by (intros _; exact HFZ). clear HFZ.
(* from copy's order list, the class-24 bound and pj_free's hull budget at the join: ct_J_call, then ct_at_Z - once the
   r = 0 end position is had from the position transfer *)
assert (KONT : forall F,
  pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc F ->
  YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget Sc [] ->
  (forall S2, (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
      (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x os i H0 hist Sc -> prh_run_at sm x os i (prhPj_free_evs F) ->
      exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPj_free_evs F))%nat H0 hist' S2) ->
    r = 0 -> ct_pos_end S2) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
    (crt_cfg (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A) fxk CRT_J_OFF rg memc mdc) QFA).
{ intros F HFO HC24 HHB HEND.
  eapply YSRrG.SRr'_bind; [exact (ct_J_call fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r
    F HJA HC24 HHB HFO)|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k & -> & (WS2 & HJ2 & HB2) & HBR2 & R22' & HSV2 & HFR2 &
    HQ0 & HTR & HMN2).
  apply (ct_at_Z fxk ly2 S2 Hp2 W2 mem2 md2 k pos regs2 r WS2 (HFZ' tt) HFK HJ2 HB2 HBR2 R22' HSV2 HFR2); [|exact HMN2].
  split; [exact HQ0 | exact (HEND S2 HTR)]. }
pose proof (crt_at_J_r0 HJA) as Hr00.
destruct HR as [(Hr1 & _) | (Hr0 & _ & _ & _ & HPOS & HN & HM & (Fc & HFOc & HFc) & Hd)].
- (* r = 1: DEAD. crt_at_J states r = 0 (the text's r = 1 arm is dead under its entry premise prh_cons_from, kit tip
     dc6ee977244a), so the tail never sees an r = 1 state *)
  exfalso. rewrite Hr00 in Hr1. discriminate Hr1.
- (* r = 0: the class-24 bound comes from crt_pos's position (PresetRoomCounts.counts_of_room_pos_rl); copy's order list is
     crt_at_J's ORDERED free list Fc (its requests ARE fo crt_tree_J, in order), so pj_free's own events are the
     model's crt_evs_J and crt_pos's run premise supplies them; the position transfer carries crt_pos's position
     across pj_free, and ct_r0_end lands it at QT's end position. *)
  destruct (crt_pos_ex HPOS) as (pre & hist & HA).
  pose proof (crt_pos_split HA) as Epre. pose proof (crt_pos_room HA) as HRP.
  pose proof (crt_pos_run HA) as Hrun.
  assert (Hperm : Permutation (map (fun b => snd b + cf_head) Fc) (PresetReqAt.fo ctJ))
    by (rewrite HFc; apply Permutation_refl).
  assert (HRUN : prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat (prhPj_free_evs Fc)).
  { destruct Fc as [|b Fc'].
    - (* no blocks: pj_free makes no event *)
      exact (prhPj_free_evs_nil rp_sm rp_x rp_os _).
    - (* one bulk event, fo crt_tree_J's requests in order: the model's own *)
      change (prhPj_free_evs (b :: Fc')) with [PresetReqAt.HBulk (map (fun b0 => snd b0 + cf_head) (b :: Fc'))].
      rewrite HFc. rewrite ct_evs_J in Hrun. exact Hrun. }
  (* pj_free's hull budget (its fuzz_free calls' admission) from crt_pos's position in a run of at most 4 calls *)
  apply (KONT Fc HFOc (proj2 (PresetRoomCounts.counts_of_room_pos_rl rp_sm rp_x rp_os _ rp_H0 hist Sc HRP))
    (Crt102HullPos.hull_budget_nil_of_room_pos rp_sm rp_x rp_os _ rp_H0 hist Sc HOS4 HRP)).
  intros S2 HTR _. destruct (HTR _ _ _ _ _ _ HRP HRUN) as (h' & HP).
  exact (ct_r0_end pre Fc Epre Hrun Hperm S2 h' HP).
Qed.

End g.
End f.
End w.

(* THE ELABORATED BODIES of this file's Prop-bodied definitions (the amendment of 2026-10-29: `Print`,
   implicits on, notations off), printed on every build: none of ct_qt0 / ct_pos_end / ct_qt binds an FPState, so no
   class-implicit float state can resolve inside them. (The contract the tail cites, YGcallMxmn.aset_shadow_realizes_xm,
   is the engine's.) *)
Set Printing Implicit.
Unset Printing Notations.
Print ct_qt0.
Print ct_pos_end.
Print ct_qt.
Unset Printing Implicit.
Set Printing Notations.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqGcallW.v, with its module names changed; 482 of its 526 lines of code are new or changed and 767 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module names changed; 1639 of its 1698 lines of code are new or changed and 467 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsU.v, with its module paths and module names changed; 1141 of its 1186 lines of code are new or changed and 1653 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_R5.v; 792 of its 957 lines of code are new or changed and 1021 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c): the SECOND HALF of segment CA10 Free of the re-walk
   of check_no_overread (cno) against the kit's text tcheck_no_overread_specX: the three __wrap_free, CN_FRCUT (1084) ->
   CN_END (1108). Lane CnoA102f's sub-lane CnoA102fB (a Theorem Labs lane, #102 plan, the internal file PLAN-cno-caw-102.md 5.1 row CA10),
   re-fitted to the kit cut 7cdbb61b5fa0 by lane CnoABatch2.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   STATEMENT: cn_seg_frP of lib/A/Prog/Cno102A_F.v at cp := CfParamsPreset.CfParams_preset (Section variable CTX0
   only, no run-word list DW). A free of a live block can hide shadow again, so the stretch concludes SRr' SEGS RZ_cf
   (lib/Reusable/YA0nH.v: SRrG at wle' SEGS RZ_cf; RZ_cf of YGcfRehidePost.v) and the journal of its cuts holds its
   world conjunct at wle' SEGS RZ_cf: the cuts cn_at_fr / cn_at_end at cn_baseR .. (wle' SEGS RZ_cf) .. k 6, the
   journal at the wild budget 6; both carry `ownl <> 0 -> cn_cdead D`; the cuts carry g_most / g_own_ran_out in their
   ledger `.. ran (ci_most D) ownl`; under ownl = 0 cn_at_fr carries the copies non-NULL and cn_prog D (cn_C3 D ++
   cn_revs3 D o1 o2 o0 ++ cn_fpj D o1 o2 o0) S with ran = cn_ranz D o1 o2 o0, and cn_at_end asks the same with the frees'
   events cn_fevs in place of cn_fpj. Over the contract lib/A/Prog/Cno102A_Base.v (cn_pre read BY NAME, cn_pre_fpre /
   cn_pre_univ / cn_pre_ctx / cn_pre_pk24; cn_JR R D .. k wk the journal at a wild budget over a world relation R;
   cn_img's RELRO image rows cni_relro_seg / cni_errno_relro / cni_relro_top / cni_relro_eq) and the kit of the cut by
   path (lib/A/PRH_Base.v ef7c8ca98529: prh_univ_closure CTX0 with its clauses prh_univ_closure_site /
   prh_univ_closure_lit; lib/A/Prog/S1Ledger.v: prh_ledger_kept_aview; lib/Spec/PresetReqAt.v, PresetRun.v,
   PresetRoomPosKeep.v: room_pos_keep_free with the free's admits; lib/A/CfRoomLivePreset.v; the engine
   lib/Reusable/YCbqG.v / YCbqGwild.v: ajournal_xwR, ajournal_xw_fix1R, ajournal_x_execR, ajournal_xw_rebaseR /
   ajournal_xw_unbase0R; YG01.v admits_fix; YGcallMxmnKeep.v aj_free_at_x_ct_m_rh_keep with the call's admits;
   YGcallcf.v QMm_cf_of_room / arodata_ok_cf_of_journal_P; YGcfSecsStep.v secs_free_step; YSRrG.v SRrG_step /
   SRr'_bind / SRr'_ret), proved as cn_seg_fr in a Section matching its Section cf.
   THE CODE (DERIVED offsets inside cno, Listing_prog.v 7ed1529926bd at the cut 7cdbb61b5fa0, slots 472-477):
     1084 mv a0, s10 (= r1) ; 1088 jal __wrap_free ; 1092 ld a0, 40(s1) (= r2) ; 1096 jal __wrap_free ;
     1100 mv a0, s6 (= r3) ; 1104 jal __wrap_free ; 1108 = CN_END.
   THE PROOF: the six slots by hand steps over `@YK11.mkst fxk` configurations (fb_s_addi / fb_s_ld / fb_h_call: lane
   CnoA102r.CnoA5's h_addi / h_ld / h_call / r5_slot / f_addi / f_ld / r5_slot_ok / s_addi / s_ld / r5_pc4, proofs
   unchanged but the fb names, from lib/A/Prog/Cno102A_R5.v; stated over any world relation R by YSRrG.SRrG_step,
   since a step keeps the world, and used at
   wle' SEGS RZ_cf); each free by fb_free: YGcallMxmnKeep.aj_free_at_x_ct_m_rh_keep (a live copy) or
   Cno102_FKit.aj_free_null_at_cf_rh_keep (a NULL copy), each with the memnorm keep as its last conjunct, both from the
   primed row with the memnorm keep, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep, and both at the call memory's
   QMm_cf (YGcallcf.QMm_cf_of_room: the room from
   room_live_cf; arodata_ok_cf from the walk entry's read-only view, fpre's arodata_okP, across the journal from entry
   by YGcallcf.arodata_ok_cf_of_journal_P with the base's RELRO image rows and cni_ro_reads_nw; the hull admission
   cf_hull_ok S is fb_free's premise; QMm_cf asks no memnorm), the chain with the frame record at s0 = the entry sp
   pushed on the entry chain (fb_chain: achain_push, prh_univ_closure_site / prh_univ_closure_lit), P across the call
   by srr_inv_call.
   THE WILD BUDGET across a free: each copy's free is one of this function's FIXED-trace sites (its trace is in u_fix
   by prh_univ_closure's clauses), so the call's admits is YG01.admits_fix; a live copy's rule runs at the journal's
   budget WS and posts it at WS ++ [the trace], which YCbqG.ajournal_xw_fix1R drops again; a NULL copy's rule runs on
   the journal rebased to the current depot (YCbqGwild.ajournal_xw_rebaseR), with the depot keep
   YGcfAmx2.ipost_free_null_depot (through YGcfRoomStep.ipost_apath), and comes back by YCbqGwild.ajournal_xw_unbase0R
   with the journal's own ajxR_wild. So the journal stays at WS, within the cut's budget 6. A hand step runs the same
   rebase / ajournal_x_execR / unbase0 (fb_inv_md). The invariant fb_inv carried from free to free: the memory facts
   (fb_mem: the journal from entry at wle' SEGS RZ_cf, the frame, the saved words, the read-only view, the slot words,
   the ledger at (ci_most D) ownl) by the call's acall_kept_x clauses (fb_mem_keep: S1Ledger.prh_ledger_kept_aview
   with the clause that keeps every prh_pst byte, g_most / g_own_ran_out among them, so the ledger carries both cells
   across the free as it carries the other statics), the blocks (the copies leave ablocks), room_live_cf by
   YGcfRoomLive.RL_free_step at CfRoomLivePreset.preset_rl_b24_ok's bound. THE HULL: cn_at_fr carries
   PresetHullBudget.hull_budget S (cn_hrest_pf0 (ci_x D)) at the cut state S; a free keeps both secondary counts
   (YGcfSecsStep.secs_free_step, fb_free's post secs_same S S2), so PresetHullBudget.hull_budget_same carries the budget
   to every free's state, where PresetHullPay.hull_ok_of_budget gives the admission cf_hull_ok (fb_free's premise), and
   to CN_END, where it is cn_at_end's hull_budget S4 (cn_hF3 (ci_x D)) (cn_hrest_frees_split: pf0 is cn_hF3).
   THE CLASS-24 COUNT: ccnt24 S <= L24 + DRV at CN_FRCUT in every arm (fb_c24_cut), from the cut's blocks (the entry's
   plus at most the three copies of size + 16) and cn_pre's class-24 peak along the all-granted events
   (PresetRun.pkR_prefix at the prefix cn_C3); carried in fb_inv, it only falls across each free (fb_ccnt24_le).
   THE PROGRESS FACT (the post-implication form), under ownl = 0 only: fb_inv carries cn_prog D E0 S over the events
   made so far, with E0 ++
   one HFr (size + 16) per copy still to free = the text's whole list cn_C3 ++ cn_revs3 ++ cn_fevs. A live copy's
   free extends E0 by its HFr (fb_prog_fr: the live set by PresetReqAt.hlive_from_app and rm1 of the freed size, the
   position by prh_run_at_app_iff / prh_run_at_one and PresetRoomPosKeep.room_pos_keep_free at the free's admits); a
   NULL copy keeps it (fb_prog_null, room_pos_keep_free_null). Under ownl <> 0 the cuts carry no progress fact; the
   refusal's cn_cdead D (state-free) is carried from cn_at_fr to cn_at_end unchanged.
   SECTION HYPOTHESES (named arguments): AFREE (the primed free wrapper row with the memnorm keep,
   YGcfMallocComposeKeep.afree_realizes_cf_rh_keep, at every float state); PAL (PALib, the unit's image binding of B:
   pal_free = the jal target is the wrapper,
   pal_env = errno's place; owned by the kit, as Caw102A_WA3 / FuzzFree take it); IMG (the base's cn_img); HW (the kit's
   prh_head_wide, PRH_Base.v, the Section-hypothesis spelling the kit owner rules for walks: the ledger heads lie in their
   blocks). No other; no named premise.
   Numerals: offsets above (DERIVED); 32 / 40 (LENGTH: slot offsets at s1); 16 (LENGTH: the copy's pad); 192 / 208 / 32
   (LENGTH: the frame and the realignment); 8 / 16 (LENGTH: the frame record); 88 / 184 (LENGTH: the saved words' span);
   4 (COUNT: errno's bytes); 4096 / 16384 (LENGTH: the low page, ASTACK); 6 (COUNT: the cut's wild budget, prh_wk
   F_check_no_overread); register numbers and the listing's instruction words (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcallcf YGcallSx YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMx YGcallMxmn YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YGcfRoomStep YGcfAmx2.
(* the step relation over a world relation and its wle' instance (YA0nH), its step / bind lemmas (YSRrG); the re-hide
   zone, the primed free row, A14's secondary-count steps (used qualified) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YG0dcfR YGcfSecsStep.
(* the free row with the memnorm keep and its call rule (used qualified) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep YGcallMxmnKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger PvFdZeroR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetLiveBounds
  PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep PresetRun PresetReqAt PresetLiveSec PresetRoom
  PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset CfParamsPreset PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_StepKit Cno102_FKit
  Cno102A_Base Cno102A_F S1Ledger.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.


(* ==== 1. THE HAND STEPS over `@YK11.mkst fz` configurations: copied, with their proofs, from the step lemmas of
   lib/A/Prog/Cno102A_R5.v: h_addi / h_ld / h_call / r5_slot /
   f_addi / f_ld / r5_slot_ok / s_addi / s_ld, renamed with the prefix fb. Each step is stated over ANY world relation R
   (YSRrG.SRrG_step: a step keeps the world, so no law of R is used); the walk uses them at R := wle' SEGS RZ_cf, the
   relation of a stretch that crosses a free ==== *)
Section stp. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGSL := (@pa_segs _ L PI).
#[local] Notation BASEL := (@pa_val _ L PI A_TEXT).
#[local] Abbreviation hcfg regs pc mem md := (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGSL)) md).

Lemma fb_pc4 : forall k, 0 <= k -> k + 4 < 2 ^ 40 -> v_addi (Z_to_bv 64 (BASEL + k)) 4 = Z_to_bv 64 (BASEL + (k + 4)).
Proof.
intros k Hk0 Hk4. pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma fb_h_addi : forall (R : world SEGSL -> world SEGSL -> Prop) (W : world SEGSL) regs mem md Q w k k' (rd rs : bv 5)
  (imm : bv 12),
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRrG SEGSL R W (hcfg (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (BASEL + k') mem md') Q) ->
  SRrG SEGSL R W (hcfg regs (BASEL + k) mem md) Q.
Proof.
intros R W regs mem md Q w k k' rd rs imm Hpl Hdec Hrd Hk0 Hk4 -> HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
eapply (SRrG_step SEGSL R pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_addi SEGSL regs (Z_to_bv 64 (BASEL + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGSL)
             (Z_to_bv 32 w) rd rs imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (fb_pc4 k Hk0 Hk4). cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  exact (HK model' Hsame).
Qed.

Lemma fb_h_ld : forall (R : world SEGSL -> world SEGSL -> Prop) (W : world SEGSL) regs mem md Q w k k' (rd rs : bv 5)
  (imm : bv 12) a v,
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGSL (w_H W) mem) a = Some v ->
  (forall md', same_but_materialized md md' ->
     SRrG SEGSL R W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASEL + k') mem md') Q) ->
  SRrG SEGSL R W (hcfg regs (BASEL + k) mem md) Q.
Proof.
intros R W regs mem md Q w k k' rd rs imm a v Hpl Hdec Hrd Hk0 Hk4 -> Ha Ha0 Ha8 Hw HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (val_mem_of_rdword SEGSL (w_H W) mem a v Hw) as Hv.
apply val_mem_word_mem in Hv.
destruct (word_mem_ld SEGSL (mrestrict (w_H W) mem) a v Hv Ha0 Ha8) as (bs & Hbs & Hle).
eapply (SRrG_step SEGSL R pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_ld SEGSL regs (Z_to_bv 64 (BASEL + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGSL)
             (Z_to_bv 32 w) rd rs imm bs (Z_to_bv 64 v) (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec) by first [rewrite Ha; exact Hbs | exact Hle].
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (fb_pc4 k Hk0 Hk4). cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  exact (HK model' Hsame).
Qed.

(* `jal ra, s` at a PCall slot: the callee's entry with ra = the return slot *)
Lemma fb_h_call : forall (R : world SEGSL -> world SEGSL -> Prop) (W : world SEGSL) regs mem md Q k k' (s : asym),
  plookup pl_tpi k = Some (PCall s 1%bv) -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRrG SEGSL R W (hcfg (regupd regs 1%bv (Z_to_bv 64 (BASEL + k'))) (pa_sigma s) mem md') Q) ->
  SRrG SEGSL R W (hcfg regs (BASEL + k) mem md) Q.
Proof.
intros R W regs mem md Q k k' s Hpl Hk0 Hk4 -> HK.
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
pose proof Hpl as Hpl'. rewrite <- pl_tpi_eq in Hpl'.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert _ _ Hpl') as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hfw; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
lazymatch type of Hdec with context [Jal ?r ?im] => rename r into rdj; rename im into imm end.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd _]. apply reg_eqb_eq in Hrd. subst rdj.
apply Z.eqb_eq in Ht.
eapply (SRrG_step SEGSL R pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGSL regs (Z_to_bv 64 (BASEL + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGSL)
             (Z_to_bv 32 wz) 1%bv imm (pa_fetch_ok _ _ Hfw)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  reflexivity.
- intros model' Hsame. cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (bv_eqb (1%bv : bv 5) 0) with false by reflexivity. rewrite (fb_pc4 k Hk0 Hk4).
  replace (btgt (Z_to_bv 64 (BASEL + k)) (bv_signed imm)) with (Z_to_bv 64 (pa_sigma s)); [exact (HK model' Hsame)|].
  unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Ht. unfold zcanon.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, M64. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the slot checks: a closed boolean on the listing, decided by vm_compute in a closed lemma (no evar) *)
Definition fb_slot (k : Z) (f : instr -> bool) : bool :=
  match plookup pl_tpi k with
  | Some (PW w) => match decode_any (Z_to_bv 32 w) with Some (i, isz) => (isz =? 4) && f i | None => false end
  | _ => false
  end.
Definition fb_f_addi (rd rs : bv 5) (n : Z) (i : instr) : bool :=
  match i with OpImm ALU_ADD rd' rs' imm => bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? n) | _ => false end.
Definition fb_f_ld (rd rs : bv 5) (n : Z) (i : instr) : bool :=
  match i with Load SZ8 true rd' rs' imm => bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? n) | _ => false end.

Lemma fb_slot_ok : forall k f, fb_slot k f = true ->
  exists w i, plookup pl_tpi k = Some (PW w) /\ decode_any (Z_to_bv 32 w) = Some (i, 4%Z) /\ f i = true.
Proof.
intros k f H. unfold fb_slot in H.
destruct (plookup pl_tpi k) as [[w| | | | | ]|]; try discriminate H.
destruct (decode_any (Z_to_bv 32 w)) as [[i isz]|] eqn:Hd; [|discriminate H].
apply andb_prop in H as [Hz Hf]. apply Z.eqb_eq in Hz. subst isz. exists w, i. auto.
Qed.

Lemma fb_s_addi : forall (R : world SEGSL -> world SEGSL -> Prop) (W : world SEGSL) regs mem md Q k k' (rd rs : bv 5) n,
  fb_slot k (fb_f_addi rd rs n) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRrG SEGSL R W (hcfg (regupd regs rd (v_addi (getr regs rs) n)) (BASEL + k') mem md') Q) ->
  SRrG SEGSL R W (hcfg regs (BASEL + k) mem md) Q.
Proof.
intros R W regs mem md Q k k' rd rs n Hs Hrd Hk0 Hk4 Hk' HK.
destruct (fb_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf. lazymatch type of Hf with fb_f_addi _ _ _ (OpImm ?al _ _ _) = true => destruct al; try discriminate Hf end.
unfold fb_f_addi in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (fb_h_addi R W regs mem md Q w k _ _ _ _ Hpl Hdec Hrd Hk0 Hk4 eq_refl HK).
Qed.

Lemma fb_s_ld : forall (R : world SEGSL -> world SEGSL -> Prop) (W : world SEGSL) regs mem md Q k k' (rd rs : bv 5) n
  a v,
  fb_slot k (fb_f_ld rd rs n) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) n = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGSL (w_H W) mem) a = Some v ->
  (forall md', same_but_materialized md md' ->
     SRrG SEGSL R W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASEL + k') mem md') Q) ->
  SRrG SEGSL R W (hcfg regs (BASEL + k) mem md) Q.
Proof.
intros R W regs mem md Q k k' rd rs n a v Hs Hrd Hk0 Hk4 Hk' Ha Ha0 Ha8 Hw HK.
destruct (fb_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf.
lazymatch type of Hf with fb_f_ld _ _ _ (Load ?sz ?sg _ _ _) = true => destruct sz; try discriminate Hf; destruct sg; try discriminate Hf end.
unfold fb_f_ld in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (fb_h_ld R W regs mem md Q w k _ _ _ _ a v Hpl Hdec Hrd Hk0 Hk4 eq_refl Ha Ha0 Ha8 Hw HK).
Qed.
End stp.

(* ==== 2. image-free facts ==== *)
Lemma fb_land32 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. change (-32) with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod x 32 ltac:(lia)). change (2 ^ 5) with 32. lia.
Qed.

(* the realigned body sp (cn_S1) against the entry sp: 192 to 208 below it, 16-aligned *)
Lemma fb_s1 : forall sp0, sp0 mod 16 = 0 ->
  (Z.land (sp0 - 192) (-32) - sp0) mod 16 = 0 /\ sp0 - 208 <= Z.land (sp0 - 192) (-32) <= sp0 - 192.
Proof.
intros sp0 H. rewrite fb_land32.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D1. rewrite H, Z.add_0_r in D1.
pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (sp0 - 192) 32 ltac:(lia)) as M2.
set (t := sp0 / 16) in *. set (q := (sp0 - 192) / 32) in *. set (rr := (sp0 - 192) mod 32) in *.
split.
- replace (sp0 - 192 - rr - sp0) with ((2 * q - t) * 16) by lia. apply Z.mod_mul. lia.
- lia.
Qed.

(* the free call's trace: the chain record (fp, ra, s0) unwinds to its ra *)
Lemma fb_unwind : forall pc0 a r b ch, unwind_of_chain pc0 ((a, r, b) :: ch) = prh_trace pc0 r (spine ch).
Proof.
intros pc0 a r b ch. unfold unwind_of_chain, prh_trace, spine. f_equal. f_equal. cbn [flat_map]. f_equal.
induction ch as [|[[x y] z] t IH]; [reflexivity|]. cbn [flat_map map fst snd]. rewrite IH. reflexivity.
Qed.

(* ==== 3. THE SEGMENT, in Cno102A_F.v's Section cf, at the preset allocator parameters (the free row's call memory
   asks cf_hull_ok, the preset's admission field, which PresetHullPay.hull_ok_of_budget gives at CfParams_preset from a
   hull budget; Cno102A_E2-E4 bind it the same way) ==== *)
Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Instance CF_PL : PAListing A_prog_listing := PL_cno_A.
#[local] Instance CF_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the fixed re-hide zone of a stretch that crosses a free (YGcfRehidePost.v) *)
#[local] Notation RZ_cf := YGcfRehidePost.RZ_cf.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARcfx).
#[local] Notation STK := STK_check_no_overread.
Variable CTX0 : list (list Z).

(* ---- SECTION HYPOTHESES (named arguments) ---- *)
(* the free wrapper's primed runtime row at the cf instance with the memnorm keep (YGcfMallocComposeKeep.v
   afree_realizes_cf_rh_keep: YG0dcfR.v's afree_realizes_cf_rh, the realization over the re-hide zone RZ_cf, whose
   leaf also keeps memnorm), at every float state *)
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS B.
(* the unit's image binding of B (owned by the kit) *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
(* the base's image facts *)
Hypothesis IMG : cn_img B.
(* The kit's head width *)
Hypothesis HW : prh_head_wide.

Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs SEGS B.

(* ---- closed facts of the listing and the image tables ---- *)
Lemma fb_off : CN_OFF = 804. Proof. reflexivity. Qed.
Lemma fb_fp : pi_fp F_check_no_overread = true. Proof. vm_compute. reflexivity. Qed.
Lemma fb_stk : ASTACK + 208 <= STK. Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma fb_site1 : In (A_prog_base + CN_OFF + 1092) (pi_ret_sites F_check_no_overread RT_free).
Proof.
assert (H : existsb (Z.eqb (A_prog_base + CN_OFF + 1092)) (pi_ret_sites F_check_no_overread RT_free) = true)
  by (vm_compute; reflexivity).
apply existsb_exists in H as (x & Hx & E). apply Z.eqb_eq in E. rewrite E. exact Hx.
Qed.
Lemma fb_site2 : In (A_prog_base + CN_OFF + 1100) (pi_ret_sites F_check_no_overread RT_free).
Proof.
assert (H : existsb (Z.eqb (A_prog_base + CN_OFF + 1100)) (pi_ret_sites F_check_no_overread RT_free) = true)
  by (vm_compute; reflexivity).
apply existsb_exists in H as (x & Hx & E). apply Z.eqb_eq in E. rewrite E. exact Hx.
Qed.
Lemma fb_site3 : In (A_prog_base + CN_OFF + 1108) (pi_ret_sites F_check_no_overread RT_free).
Proof.
assert (H : existsb (Z.eqb (A_prog_base + CN_OFF + 1108)) (pi_ret_sites F_check_no_overread RT_free) = true)
  by (vm_compute; reflexivity).
apply existsb_exists in H as (x & Hx & E). apply Z.eqb_eq in E. rewrite E. exact Hx.
Qed.
(* the slots (Listing_prog.v 7ed1529926bd at the cut 7cdbb61b5fa0, lines 487-492, slots 472-477) *)
Lemma fb_sl1 : fb_slot (CN_OFF + 1084) (fb_f_addi 10%bv 26%bv 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fb_cl1 : plookup pl_tpi (CN_OFF + 1088) = Some (PCall AS___wrap_free 1%bv). Proof. vm_compute. reflexivity. Qed.
Lemma fb_sl2 : fb_slot (CN_OFF + 1092) (fb_f_ld 10%bv 9%bv 40) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fb_cl2 : plookup pl_tpi (CN_OFF + 1096) = Some (PCall AS___wrap_free 1%bv). Proof. vm_compute. reflexivity. Qed.
Lemma fb_sl3 : fb_slot (CN_OFF + 1100) (fb_f_addi 10%bv 22%bv 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fb_cl3 : plookup pl_tpi (CN_OFF + 1104) = Some (PCall AS___wrap_free 1%bv). Proof. vm_compute. reflexivity. Qed.

(* ---- small facts ---- *)
Lemma fb_find_seg : forall (segs : list Segment) a, in_img segs a -> find_segment segs a 1 <> None.
Proof.
intros segs a (sg & Hin & Hr). induction segs as [|s rest IH]; [destruct Hin|]. cbn.
destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E;
  [discriminate|].
destruct Hin as [<- | Hin]; [|exact (IH Hin)].
exfalso. apply andb_false_iff in E as [E|E]; apply Z.leb_gt in E; lia.
Qed.

(* an image byte is never hidden: its view is its raw byte *)
Lemma fb_aview_raw : forall (W W' : world SEGS) (m m' : word -> option byte) a, in_img SEGS a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a.
Proof.
intros W W' m m' a Hi Hm.
pose proof (@pa_segs_low _ _ PA a Hi) as Hlow. unfold kLowMemEnd in Hlow.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
assert (H0 : forall W0 : world SEGS, w_H W0 (Z_to_bv 64 a) = false).
{ intros W0. destruct (w_H W0 (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (w_Hoff W0 _ E) as Hn. rewrite Hu in Hn. exact (fb_find_seg _ a Hi Hn). }
unfold aview, mbyte, mrestrict. rewrite (H0 W), (H0 W'), Hm. reflexivity.
Qed.

Lemma fb_rs : forall regs l (x : bv 5) v, cn_regsat regs l -> In (x, v) l -> getr regs x = w64 v.
Proof. intros regs l x v H Hin. unfold cn_regsat in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.

Lemma fb_getr_upd : forall regs (x y : bv 5) v, bv_unsigned y <> bv_unsigned x -> getr (regupd regs x v) y = getr regs y.
Proof.
intros regs x y v H. unfold getr. destruct (bv_eqb y 0); [reflexivity|]. apply regupd_other.
intros E. apply H. rewrite E. reflexivity.
Qed.
Lemma fb_getr_same : forall regs (x : bv 5) v, bv_eqb x 0 = false -> getr (regupd regs x v) x = v.
Proof. intros regs x v H. unfold getr. rewrite H. apply regupd_same. Qed.

Lemma fb_ap_refl : forall regs, aregs_preserved regs regs.
Proof. intros regs r _. reflexivity. Qed.
Lemma fb_ap_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma fb_u5 : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) = n.
Proof.
intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
unfold acallee_saved in Hn. apply Z.mod_small. lia.
Qed.
Lemma fb_ap_upd : forall regs regs' (x : bv 5) v, (bv_unsigned x = 1 \/ bv_unsigned x = 10) ->
  aregs_preserved regs regs' -> aregs_preserved regs (regupd regs' x v).
Proof.
intros regs regs' x v Hx H r Hr. rewrite fb_getr_upd; [exact (H r Hr)|].
rewrite (fb_u5 r Hr). unfold acallee_saved in Hr. lia.
Qed.
Lemma fb_ap_get : forall regs regs' n (x : bv 5), aregs_preserved regs regs' -> acallee_saved n ->
  bv_unsigned x = n -> getr regs' x = getr regs x.
Proof.
intros regs regs' n x H Hn Hx. replace x with (Z_to_bv 5 n); [exact (H n Hn)|].
apply bv_eq. rewrite (fb_u5 n Hn). symmetry. exact Hx.
Qed.

Lemma fb_req_n : forall D, req_size (cn_size D + 16) = cn_size D + 16 /\ 16 <= cn_size D + 16.
Proof. intros D. unfold req_size, cn_size. destruct (Z.eqb_spec (Z.of_nat (length (ci_x D)) + 16) 0); lia. Qed.

Lemma fb_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

Lemma fb_pst_ok : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Proof. exact (cni_pst_ok B IMG). Qed.

(* ---- the room counts at the frees: the class-24 live count, RL_free_step's rl_b24_ok ---- *)
Lemma fb_blocks_snd : forall ly S, map snd (ablocks B ly S) = map snd (blocks S).
Proof. intros ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.
Lemma fb_rs_live : forall S, PresetRoom.rs_live (YGcfRoom.room_of_cf S) = map snd (blocks S).
Proof. intros S. reflexivity. Qed.
Lemma fb_ccnt24 : forall S,
  YGcfRoomLive.ccnt24 S = Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (map snd (blocks S))).
Proof. intros S. reflexivity. Qed.
(* a call that only removes blocks lowers the count *)
Lemma fb_ccnt24_le : forall ly S ly' S' l, Permutation (ablocks B ly S) (l ++ ablocks B ly' S') ->
  YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S.
Proof.
intros ly S ly' S' l H. rewrite !fb_ccnt24, <- (fb_blocks_snd ly S), <- (fb_blocks_snd ly' S').
rewrite (PresetReqAt.cnt_perm _ _ _ (Permutation_map snd H)), map_app, PresetReqAt.cnt_app. lia.
Qed.
Lemma fb_cblks_snd : forall D r1 r2 r3 b, In b (cn_cblks D r1 r2 r3) -> snd b = cn_size D + 16.
Proof.
intros D r1 r2 r3 b Hb. revert Hb. unfold cn_cblks, cn_cblk.
destruct (r1 =? 0), (r2 =? 0), (r3 =? 0); cbn [app In]; intros Hb;
  repeat (destruct Hb as [<- | Hb]; [reflexivity|]); destruct Hb.
Qed.
Lemma fb_cblks_len : forall D r1 r2 r3, (length (cn_cblks D r1 r2 r3) <= 3)%nat.
Proof. intros D r1 r2 r3. unfold cn_cblks, cn_cblk. destruct (r1 =? 0), (r2 =? 0), (r3 =? 0); cbn [app length]; lia. Qed.
(* at most three requests of size n added to L0 count no more than three *)
Lemma fb_cnt_copies : forall f n (l L0 : list Z), (forall z, In z l -> z = n) -> (length l <= 3)%nat ->
  (PresetReqAt.cnt f (l ++ L0) <= PresetReqAt.cnt f (n :: n :: n :: L0))%nat.
Proof.
intros f n l L0 Hl Hn.
assert (E : l = repeat n (length l)).
{ clear Hn. revert Hl. induction l as [|z l IH]; intros Hl; [reflexivity|]. cbn [length repeat].
  rewrite (Hl z (or_introl eq_refl)). f_equal. apply IH. intros y Hy. exact (Hl y (or_intror Hy)). }
rewrite E. revert Hn. generalize (length l) as m. intros m Hm.
destruct m as [|[|[|[|m]]]]; [| | | |lia]; unfold PresetReqAt.cnt; cbn [repeat app List.filter];
  destruct (f n); cbn [length]; lia.
Qed.
(* AT CN_FRCUT: the blocks are the entry's and the copies', and cn_pre bounds the class-24 count of the entry's live
   set with all three copies (the all-granted events' prefix cn_C3) *)
Lemma fb_c24_cut : forall D ly S r1 r2 r3, cn_pre (fx := fx) B ARcfx CTX0 D ->
  Permutation (ablocks B ly S) (cn_cblks D r1 r2 r3 ++ ablocks B (ci_ly D) (ci_S D)) ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros D ly S r1 r2 r3 HPRE HAB.
pose proof (cn_pre_pk24 (fx := fx) B ARcfx CTX0 D HPRE) as HPK.
rewrite <- cn_ck_cno_evs in HPK.
pose proof (PresetRun.pkR_prefix (PresetRoom.in_cls YG00.kBatchClass)
  (cn_C3 D ++ cn_revs3 D None None None ++ cn_fevs D None None None)
  (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D))) 3) as Hpf.
assert (Ehl : PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D)))
    (firstn 3 (cn_C3 D ++ cn_revs3 D None None None ++ cn_fevs D None None None)) =
  cn_size D + PresetReqAt.FUZZ_PAD :: cn_size D + PresetReqAt.FUZZ_PAD :: cn_size D + PresetReqAt.FUZZ_PAD ::
    map snd (blocks (ci_S D))) by reflexivity.
rewrite Ehl in Hpf.
assert (Hcc : (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass)
    (map snd (cn_cblks D r1 r2 r3) ++ map snd (blocks (ci_S D))) <=
  PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass)
    ((cn_size D + PresetReqAt.FUZZ_PAD)%Z :: (cn_size D + PresetReqAt.FUZZ_PAD)%Z ::
     (cn_size D + PresetReqAt.FUZZ_PAD)%Z :: map snd (blocks (ci_S D))))%nat).
{ apply fb_cnt_copies.
  - intros z Hz. apply in_map_iff in Hz as (b & <- & Hb). rewrite (fb_cblks_snd D r1 r2 r3 b Hb). reflexivity.
  - rewrite length_map. apply fb_cblks_len. }
rewrite fb_ccnt24, <- (fb_blocks_snd ly S), (PresetReqAt.cnt_perm _ _ _ (Permutation_map snd HAB)), map_app,
  (fb_blocks_snd (ci_ly D) (ci_S D)).
clear - HPK Hpf Hcc. lia.
Qed.

(* the entry sp and the body sp *)
Lemma fb_sp0 : forall D, cn_pre (fx := fx) B ARcfx CTX0 D ->
  cn_sp0 D mod 16 = 0 /\ YM05.alloc_ceiling + STK <= cn_sp0 D /\ cn_sp0 D <= ly_top (ci_ly D) /\
  ly_top (ci_ly D) <= 2 ^ 47 /\
  (cn_S1 D - cn_sp0 D) mod 16 = 0 /\ cn_sp0 D - 208 <= cn_S1 D <= cn_sp0 D - 192.
Proof.
intros D HPRE. pose proof (cn_pre_fpre (fx := fx) B ARcfx CTX0 D HPRE) as HF.
destruct HF as ((_ & _ & _ & _ & _ & Hstk0 & _) & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
change (spZ (ci_regs D)) with (cn_sp0 D) in *.
destruct (fb_s1 (cn_sp0 D) Hal16) as (M & L1 & L2).
unfold cn_S1. repeat split; lia.
Qed.

(* a copy (a block of the cut not among the entry's blocks): in the permutation's left part, so not in its right part *)
Lemma fb_not_entry : forall ly S Hp W mem md (L A : list (Z * Z)) x, ARcfx ly S Hp W mem md ->
  Permutation (ablocks B ly S) (L ++ A) -> In x L -> 0 < req_size (snd x) -> ~ In x A.
Proof.
intros ly S Hp W mem md L A x HAR HP HxL Hpos HxA.
assert (Hin : In x (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact HxL).
destruct x as [xb xn].
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md xb xn HAR Hin) as (_ & _ & _ & _ & _ & Hpw).
apply in_split in Hin as (a1 & a2 & Ea). apply in_split in HxL as (l1 & l2 & El).
rewrite Ea, El, <- app_assoc in HP. cbn [app] in HP.
apply Permutation_app_inv in HP.
assert (Hx2 : In (xb, xn) (a1 ++ a2)).
{ apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. right. exact HxA. }
set (f := fun b : Z * Z => (fst b, req_size (snd b))) in Hpw.
assert (Hd : zdisjoint (f (xb, xn)) (f (xb, xn))).
{ apply in_app_or in Hx2 as [H1|H1]; apply in_split in H1 as (b1 & b2 & Eb).
  - apply (pairwise_In2 zdisjoint (map f (ablocks B ly S)) _ _ (map f b1) (map f b2) (map f a2) Hpw).
    rewrite Ea, Eb, <- app_assoc. cbn [app]. repeat (rewrite map_app; cbn [map app]). reflexivity.
  - apply (pairwise_In2 zdisjoint (map f (ablocks B ly S)) _ _ (map f a1) (map f b1) (map f b2) Hpw).
    rewrite Ea, Eb. repeat (rewrite map_app; cbn [map app]). reflexivity. }
unfold zdisjoint, f in Hd. cbn [fst snd] in Hd, Hpos. lia.
Qed.

(* ---- the chain at a free call: the function's frame record (s0 = the entry sp) pushed on the entry chain; the call's
   trace is a FIXED one (in u_fix, by prh_univ_closure's clauses). Used at the frees only, so its journal is at
   wle' SEGS RZ_cf (cn_JR) ---- *)
Lemma fb_chain : forall D ly S Hp W mem md k regsT r0,
  cn_pre (fx := fx) B ARcfx CTX0 D ->
  cn_JR B ARcfx (wle' SEGS RZ_cf) D ly S Hp W mem md k 6 -> cn_saved D W mem ->
  spZ regsT = cn_S1 D -> s0Z regsT = cn_sp0 D -> raZ regsT = r0 -> 4096 <= r0 ->
  In r0 (pi_ret_sites F_check_no_overread RT_free) ->
  exists ch, chain_pre ly (aview SEGS (w_H W) mem) regsT ch /\
    In (call_trace ly (pc_free_ra0 (as_code B)) regsT ch) (as_universe B).
Proof.
intros D ly S Hp W mem md k regsT r0 HPRE HJ HSV Hsp Hs0 Hra Hr4 Hsite.
destruct (fb_sp0 D HPRE) as (Hal & Hc & Htop & Htop47 & Hm & Hs1a & Hs1b).
pose proof (cn_pre_fpre (fx := fx) B ARcfx CTX0 D HPRE) as HF.
destruct HF as ((_ & _ & Hra40 & _ & _ & Hstk0 & _ & Hch0 & _) & _).
pose proof (cn_pre_univ (fx := fx) B ARcfx CTX0 D HPRE) as HUNIV.
pose proof (cn_pre_ctx (fx := fx) B ARcfx CTX0 D HPRE) as HCTX.
pose proof Hstk0 as (_ & HSTK0 & _).
pose proof fb_stk as Hstk. assert (Has : ASTACK = 16384) by reflexivity.
destruct HJ as (WS & HJw & _). pose proof (ajxR_ly HJw) as Hly. pose proof (ajxR_hi HJw) as J1.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
unfold cn_saved in HSV. rewrite Forall_forall in HSV.
pose proof (HSV (184, 1%bv) ltac:(left; reflexivity)) as Sra.
pose proof (HSV (176, 8%bv) ltac:(right; left; reflexivity)) as Ss0.
cbn [fst snd] in Sra, Ss0.
replace (cn_sp0 D - 192 + 184) with (cn_sp0 D - 8) in Sra by lia.
replace (cn_sp0 D - 192 + 176) with (cn_sp0 D - 16) in Ss0 by lia.
change (bv_unsigned (getr (ci_regs D) 1%bv)) with (raZ (ci_regs D)) in Sra.
change (bv_unsigned (getr (ci_regs D) 8%bv)) with (s0Z (ci_regs D)) in Ss0.
assert (Hk : forall a, cn_sp0 D <= a < 2 ^ 64 ->
  aview SEGS (w_H W) mem a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
{ intros a Ha. apply J1; lia. }
assert (HU0 : In [pc_free_ra0 (as_code B)] (as_universe B)) by exact (proj1 HUNIV RT_free).
destruct (Z_lt_ge_dec (cn_sp0 D) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((cn_sp0 D, raZ (ci_regs D), s0Z (ci_regs D)) :: ci_ch D).
  assert (HA : achain ly (aview SEGS (w_H W) mem) (cn_S1 D) (cn_sp0 D)
    ((cn_sp0 D, raZ (ci_regs D), s0Z (ci_regs D)) :: ci_ch D)).
  { apply (achain_push ly (aview SEGS (w_H (ci_W D)) (ci_mem D))).
    - apply (achain_ly_top (ci_ly D) ly); [exact Etop | exact Hch0].
    - lia.
    - exact Hk.
    - exact Sra.
    - exact Ss0.
    - exact Hra40.
    - lia.
    - apply Z.mod_divide in Hal; [|lia]. destruct Hal as (t & Ht). apply Z.mod_divide; [lia|]. exists (2 * t). lia.
    - exact Hlt.
    - lia. }
  split.
  + apply (achain_chain_pre ly _ (cn_S1 D) (cn_sp0 D) _ regsT HA); [lia | exact Hs0 | lia].
  + unfold call_trace. destruct (frame0_ok ly regsT); [|exact HU0].
    rewrite fb_unwind. cbn [spine map fst snd]. rewrite Hra.
    exact (prh_univ_closure_site B CTX0 F_check_no_overread (raZ (ci_regs D) :: spine (ci_ch D)) RT_free r0
      HUNIV HCTX fb_fp Hsite).
- exists []. split.
  + unfold chain_pre. split; [lia|]. destruct (frame0_ok ly regsT); [|reflexivity].
    replace (bad_next (spZ regsT) (ly_top ly) (s0Z regsT)) with true; [reflexivity|]. symmetry.
    unfold bad_next. rewrite Hs0. apply orb_true_intro. left. apply orb_true_intro. right. apply Z.leb_le. lia.
  + unfold call_trace. destruct (frame0_ok ly regsT); [|exact HU0].
    rewrite fb_unwind. cbn [spine map]. rewrite Hra.
    exact (prh_univ_closure_lit B CTX0 F_check_no_overread RT_free r0 HUNIV Hsite).
Qed.

(* ---- what the walk carries from free to free: the memory part (fb_mem) and the block / room part. Both hold only
   at the frees, after cn_at_fr (whose journal spans the pj_free calls), so the journal is at wle' SEGS RZ_cf ---- *)
Definition fb_mem (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran r2 ownl : Z) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  cn_JR B ARcfx (wle' SEGS RZ_cf) D ly S Hp W mem md k 6 /\ cn_frame D ly S W mem /\ cn_saved D W mem /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
  rdword (aview SEGS (w_H W) mem) (cn_S1 D + 32) = Some (cn_F D) /\
  rdword (aview SEGS (w_H W) mem) (cn_S1 D + 40) = Some r2 /\
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl.
Definition fb_inv (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z) (L : list (Z * Z))
  (r2 ownl : Z) : Prop :=
  fb_mem D fxk ly S Hp W mem md k Lam peak cnt ran r2 ownl /\
  Permutation (ablocks B ly S) (L ++ ablocks B (ci_ly D) (ci_S D)) /\
  (forall b, In b L -> snd b = cn_size D + 16 /\ ~ In (fst b) Hp /\ ~ In b (ablocks B (ci_ly D) (ci_S D))) /\
  room_live_cf S /\ YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  (* under ownl = 0 (no copy refused): the events made since entry, E0, and one HFr per copy still to free make the
     text's whole list *)
  (ownl = 0 -> exists o1 o2 o0 E0, ran = cn_ranz D o1 o2 o0 /\ cn_prog D E0 S /\
     E0 ++ map (fun _ => PresetReqAt.HFr (cn_size D + 16)) L = cn_C3 D ++ cn_revs3 D o1 o2 o0 ++ cn_fevs D o1 o2 o0).

(* ---- the progress fact across one free (the base's post-implication cn_prog) ---- *)
Lemma fb_prog_fr : forall D E0 (S S2 : astate) n,
  cn_prog D E0 S ->
  Permutation (map snd (blocks S)) (n :: map snd (blocks S2)) ->
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
     nth_error (PresetRun.hruns sm x0 os) i = Some (PresetReqAt.HFr n) ->
     exists hist', PresetRoomPos.iface_room_pos sm x0 os (Datatypes.S i) H0 hist' S2) ->
  cn_prog D (E0 ++ [PresetReqAt.HFr n]) S2.
Proof.
intros D E0 S S2 n (HL & HP) Hsn HK. split.
- assert (E1 : forall s, PresetReqAt.hlive_from s [PresetReqAt.HFr n] = PresetReqAt.rm1 n s) by reflexivity.
  rewrite PresetReqAt.hlive_from_app, E1, (fb_rs_live S2). rewrite (fb_rs_live S) in HL.
  eapply Permutation_trans; [|apply PresetReqAtNoMiss.rm1_perm; exact HL].
  eapply Permutation_trans; [|apply PresetReqAtNoMiss.rm1_perm; apply Permutation_sym; exact Hsn].
  rewrite PresetReqAt.rm1_cons_eq. apply Permutation_refl.
- intros sm x0 os i H0 hist Hpos Hrun. apply prh_run_at_app_iff in Hrun as (R1 & R2).
  destruct (HP sm x0 os i H0 hist Hpos R1) as (h1 & P1).
  apply prh_run_at_one in R2. destruct (HK sm x0 os (i + length E0)%nat H0 h1 P1 R2) as (h2 & P2).
  exists h2. rewrite length_app. cbn [length].
  replace (i + (length E0 + 1))%nat with (Datatypes.S (i + length E0)) by lia. exact P2.
Qed.
Lemma fb_prog_null : forall D E0 (S S2 : astate),
  cn_prog D E0 S -> map snd (blocks S2) = map snd (blocks S) ->
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PresetRoomPos.iface_room_pos sm x0 os i H0 hist S2) ->
  cn_prog D E0 S2.
Proof.
intros D E0 S S2 (HL & HP) Hb HK. split.
- rewrite (fb_rs_live S2), Hb, <- (fb_rs_live S). exact HL.
- intros sm x0 os i H0 hist Hpos Hrun. destruct (HP sm x0 os i H0 hist Hpos Hrun) as (h & P1).
  exists h. exact (HK _ _ _ _ _ _ P1).
Qed.

(* a hand step materializes model pages only: the journal holds at the new model (at its budget WS: rebased to the
   current depot, YCbqG's ajournal_x_execR, and back, YCbqGwild's rebaseR / unbase0R with the journal's own ajxR_wild,
   all at wle' SEGS RZ_cf) *)
Lemma fb_inv_md : forall D fxk ly S Hp W mem md k Lam peak cnt ran L r2 ownl md',
  fb_inv D fxk ly S Hp W mem md k Lam peak cnt ran L r2 ownl -> same_but_materialized md md' ->
  fb_inv D fxk ly S Hp W mem md' k Lam peak cnt ran L r2 ownl.
Proof.
intros D fxk ly S Hp W mem md k Lam peak cnt ran L r2 ownl md' ((Hfz & Hfk & HJ & Hrest) & Hrest2) Hs.
split; [|exact Hrest2]. split; [exact Hfz|]. split; [exact Hfk|]. split; [|exact Hrest].
destruct HJ as (WS & HJw & HWB). exists WS. split; [|exact HWB].
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ0.
pose proof (ajournal_x_execR (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) (wle' SEGS RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  mem md' (fun _ => False) HJ0 (fun x _ => eq_refl) (fun x Hx => Hx) (fun x _ => eq_refl) Hs (fun a H => False_ind _ H))
  as HJ1.
exact (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 (ajxR_wild HJw)).
Qed.

(* ---- the memory part across one free call (the call rule's kept clauses, E the freed bytes) ---- *)
Lemma fb_mem_keep : forall D fxk ly S Hp W mem md k Lam peak cnt ran r2 ownl ly2 S2 W2 mem2 md2 k2 slo (E : Z -> Prop),
  cn_pre (fx := fx) B ARcfx CTX0 D ->
  fb_mem D fxk ly S Hp W mem md k Lam peak cnt ran r2 ownl ->
  cn_JR B ARcfx (wle' SEGS RZ_cf) D ly2 S2 Hp W2 mem2 md2 k2 6 ->
  frames S2 = frames S ->
  acall_kept_x SEGS B ly S W mem W2 mem2 slo (cn_S1 D) E ->
  (forall i, 0 <= i < 4 -> mem2 (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) ->
  (forall a, E a -> exists b m, In (b, m) (ablocks B ly S) /\ ~ In b Hp /\ b <= a < b + req_size m) ->
  (forall b, In b (ablocks B ly S) -> In (fst b) Hp -> In b (ablocks B ly2 S2)) ->
  fb_mem D fxk ly2 S2 Hp W2 mem2 md2 k2 Lam peak cnt ran r2 ownl.
Proof.
intros D fxk ly S Hp W mem md k Lam peak cnt ran r2 ownl ly2 S2 W2 mem2 md2 k2 slo E HPRE HM HJ2 Hfr2 HK Herr HE Hincl.
destruct HM as (Hfz & Hfk & HJ & HFR & HSV & HROD & HS32 & HS40 & HLED).
unfold acall_kept_x, acall_kept in HK. destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
destruct (fb_sp0 D HPRE) as (Hal & Hc & Htop & Htop47 & Hm & Hs1a & Hs1b).
pose proof fb_stk as Hstk. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HJ as (WSa & HJa & _). pose proof (ajxR_ar HJa) as HAR. pose proof (ajxR_ly HJa) as Hly.
pose proof HJ2 as (WSb & HJb & _). pose proof (ajxR_ar HJb) as HAR2. pose proof (ajxR_ly HJb) as Hly2.
pose proof Hly as (_ & _ & _ & _ & _ & LF & _). pose proof Hly2 as (_ & _ & _ & _ & _ & LF2 & _).
split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ2|].
split.
{ (* the frame *)
  unfold cn_frame in HFR |- *. destruct HFR as (Efr & Hnin & Hflag & Hpb & Hps).
  assert (Hin : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Efr; left; reflexivity).
  assert (Hin2 : In (CN_CID, ci_fpos D) (frames S2)) by (rewrite Hfr2; exact Hin).
  assert (EF2 : frame_addr ly2 CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F, frame_addr; rewrite LF2; reflexivity).
  assert (EF : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F, frame_addr; rewrite LF; reflexivity).
  pose proof (fs_frame_bytes_ok CN_CID ltac:(unfold CN_CID; lia)) as (Hfs & _).
  destruct (alx_frames _ _ _ LAWS ly2 S2 Hp W2 mem2 md2 CN_CID (ci_fpos D) HAR2 Hin2) as (_ & _ & Hp2 & Hs2).
  rewrite EF2 in Hp2, Hs2.
  split; [rewrite Hfr2; exact Efr|]. split; [exact Hnin|]. split.
  - replace (flag_addr ly2 CN_CID (ci_fpos D)) with (flag_addr ly CN_CID (ci_fpos D))
      by (unfold flag_addr; rewrite LF, LF2; reflexivity).
    rewrite <- Hflag. apply rdword_ext. intros j Hj.
    apply (K4 CN_CID (ci_fpos D)); [exact Hin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF; lia |].
    intros HEa. destruct (HE _ HEa) as (b & m & Hb & _ & Hbr).
    pose proof (sep_block_frame_x SEGS B ARcfx LAWS ly S Hp W mem md b m CN_CID (ci_fpos D) HAR Hb Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. lia.
  - split; [intros a Ha; exact (proj1 (Hp2 a Ha))|].
    intros a Ha. pose proof (proj1 (Hs2 (a - shadow_addr (cn_F D)) ltac:(lia))) as H.
    replace (shadow_addr (cn_F D) + (a - shadow_addr (cn_F D))) with a in H by lia. exact H. }
split.
{ (* the saved words: above the body sp *)
  unfold cn_saved in HSV |- *. rewrite Forall_forall in HSV |- *. intros p Hp0.
  assert (Ho : 88 <= fst p <= 184).
  { cbn in Hp0. repeat (destruct Hp0 as [<- | Hp0]; [cbn; lia|]). destruct Hp0. }
  rewrite <- (HSV p Hp0). apply rdword_ext. intros j Hj. apply K1; lia. }
split.
{ (* the read-only view: image bytes *)
  unfold arodata_okP in HROD |- *. intros a Hro Hno Her.
  rewrite (K3 a (fb_ro_img a Hro) Hno Her). exact (HROD a Hro Hno Her). }
split; [rewrite <- HS32; apply rdword_ext; intros j Hj; apply K1; lia|].
split; [rewrite <- HS40; apply rdword_ext; intros j Hj; apply K1; lia|].
(* the statics (image bytes; errno's bytes by the leaf's raw clause): the ledger's cells, g_most / g_own_ran_out
   among them *)
assert (HSTAT : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (fb_pst_ok a Ha) as (Himg & Hno).
  destruct (Z_le_gt_dec (as_errno B) a) as [E1|E1]; [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [E2|E2]|].
  + apply fb_aview_raw; [exact Himg|].
    pose proof (Herr (a - as_errno B) ltac:(lia)) as H. unfold w64 in H.
    replace (as_errno B + (a - as_errno B)) with a in H by lia. exact H.
  + apply K3; [exact Himg | exact Hno | lia].
  + apply K3; [exact Himg | exact Hno | lia]. }
(* the ledger: the statics, the heads (blocks with a base in Hp, never the freed block) *)
pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED) as HFa.
rewrite Forall_forall in HFa.
pose proof cf_head_nonneg as Hh0. unfold prh_head_wide in HW.
apply (prh_ledger_kept_aview B ly S Hp W mem ly2 S2 Hp W2 mem2 Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED).
- exact HSTAT.
- intros a k0 i Hin Hi. destruct (HFa (a, k0) Hin) as (Hk0 & Hab & Hhp & _). cbn [fst snd] in *.
  assert (Hreq : req_size (k0 + cf_head) = k0 + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
  apply (K2 (a - cf_head) (k0 + cf_head) i Hab); [rewrite Hreq; lia|].
  intros HEa. destruct (HE _ HEa) as (b & m & Hb & Hbn & Hbr).
  assert (Hne : (a - cf_head, k0 + cf_head) <> (b, m)) by (intros Eq; injection Eq as E1 _; apply Hbn; rewrite <- E1; exact Hhp).
  pose proof (sep_blocks_x SEGS B ARcfx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hb Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia.
- intros a k0 Hin Hab. destruct (HFa (a, k0) Hin) as (_ & _ & Hhp & _). exact (Hincl _ Hab Hhp).
- apply Permutation_refl.
Qed.

(* ---- ONE FREE: at the wrapper's entry (a0 = q, ra = the return site, sp = s1, s0 = the entry sp), back at the return
   site with the invariant, the callee-saved registers kept, both secondary counts kept and P. The free's trace is
   FIXED (fb_chain), so the call's admits is YG01.admits_fix and the journal comes back at its own budget WS. A free of
   a live block can hide shadow again: the stretch is SRr' SEGS RZ_cf and the journal's world conjunct is at
   wle' SEGS RZ_cf. The row's call memory asks QMm_cf: arodata_ok_cf from the walk entry's arodata_okP (fpre's) across
   the journal from entry (YGcallcf.arodata_ok_cf_of_journal_P, the base's RELRO image rows and cni_ro_reads_nw); the
   hull admission cf_hull_ok S is a premise. free_cf keeps st_secs' counts (YGcfSecsStep.secs_free_step), so the post
   carries secs_same S S2 ---- *)
Lemma fb_free : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regsT mem md k Lam peak cnt ran q L r2 ownl off,
  cn_pre (fx := fx) B ARcfx CTX0 D ->
  fb_inv D fxk ly S Hp W mem md k Lam peak cnt ran (cn_cblk D q ++ L) r2 ownl ->
  cf_hull_ok S ->
  getr regsT 2 = w64 (cn_S1 D) -> getr regsT 8 = w64 (cn_sp0 D) ->
  getr regsT 3 = getr (ci_regs D) 3 -> getr regsT 4 = getr (ci_regs D) 4 ->
  getr regsT 10 = w64 q -> getr regsT 1 = Z_to_bv 64 (BASE + (CN_OFF + off)) ->
  In (A_prog_base + CN_OFF + off) (pi_ret_sites F_check_no_overread RT_free) ->
  0 <= CN_OFF + off < 2 ^ 40 -> (CN_OFF + off) mod 2 = 0 ->
  P mem ->
  SRr' SEGS RZ_cf W (mkCfg (@YK11.mkst fxk regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) mem (YK11.seg_rom SEGS)) md)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k2,
       c2 = mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CN_OFF + off))) mem2 (YK11.seg_rom SEGS)) md2 /\
       fb_inv D fxk ly2 S2 Hp W2 mem2 md2 k2 Lam peak cnt ran L r2 ownl /\ aregs_preserved regsT regs2 /\
       YGcfSecsStep.secs_same S S2 /\ P mem2).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regsT mem md k Lam peak cnt ran q L r2 ownl off HPRE HI HHO R2 R8 R3 R4 R10
  R1 Hsite Hoff Hoff2 HPM.
destruct HI as (HM & HAB & HLf & HRL & HC24 & HPG).
pose proof HM as (Hfz & Hfk & HJ & HFR & HSV & HROD & HS32 & HS40 & HLED).
destruct (fb_sp0 D HPRE) as (Hal & Hc & Htop & Htop47 & Hm & Hs1a & Hs1b).
pose proof fb_stk as Hstk. assert (Has : ASTACK = 16384) by reflexivity.
pose proof asan_consts as (C1 & _).
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _).
assert (EBASE : BASE = A_prog_base) by exact (cni_base B IMG). assert (EAB : 4096 <= A_prog_base) by (unfold A_prog_base; lia).
pose proof (cn_pre_fpre (fx := fx) B ARcfx CTX0 D HPRE) as HF0.
destruct HF0 as ((_ & _ & _ & Hgp0 & Htp0 & _) & HRO0 & _).
pose proof HJ as (WS & HJw & HWB).
pose proof (ajxR_ar HJw) as HAR. pose proof (ajxR_qt HJw) as HQT.
assert (Hsp : spZ regsT = cn_S1 D) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regsT = cn_sp0 D) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
assert (Hraz : raZ regsT = BASE + (CN_OFF + off)) by (unfold raZ; rewrite R1; apply unsigned_lit_small; lia).
assert (Hsite' : In (BASE + (CN_OFF + off)) (pi_ret_sites F_check_no_overread RT_free)).
{ rewrite (cni_base B IMG). replace (A_prog_base + (CN_OFF + off)) with (A_prog_base + CN_OFF + off) by lia. exact Hsite. }
destruct (fb_chain D ly S Hp W mem md k regsT (BASE + (CN_OFF + off)) HPRE HJ HSV Hsp Hs0 Hraz ltac:(lia) Hsite')
  as (ch & Hchp & Htr).
(* the call memory's read-only RELRO bytes in the cf layer's value form: the walk entry's reader form (fpre's
   arodata_okP) across the journal from entry, with the base's RELRO image rows (the range in one segment, errno apart
   from it, its end in the address space, the read-only reads in non-writable segments, the listing's relro range =
   the cf layer's); no static is a read-only byte (cni_pst_rw: neither in the relro range nor in a non-writable
   segment, where cni_ro_reads_nw puts every read-only read); the journal's footprint is [], so it opens no sink *)
assert (HARO : arodata_ok_cf SEGS B mem).
{ destruct (cni_relro_eq B IMG) as (Elo & Ehi).
  apply (arodata_ok_cf_of_journal_P (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw (cni_relro_seg B IMG) (cni_errno_relro B IMG) (cni_relro_top B IMG)
    (cni_ro_reads_nw B IMG)).
  - intros a Ha Hpst. apply (cni_pst_rw B IMG a Hpst). unfold aro_addr_cf in Ha. destruct Ha as [Ha | Ha].
    + right. rewrite <- Elo, <- Ehi. exact Ha.
    + left. apply Exists_exists in Ha as (rr & Hrr & Har). unfold in_zr in Har.
      destruct (proj1 (Forall_forall _ _) (cni_ro_reads_nw B IMG) rr Hrr) as (_ & sg & Hsg & Hnw & Hlo & Hhi).
      exists sg. split; [exact Hsg|]. split; [exact Hnw | lia].
  - exact sink_closed_nil.
  - rewrite Elo, Ehi. exact HRO0. }
(* the call memory's room, hull admission and read-only bytes (QMm_cf, the free row's premise) *)
assert (HQM : QMm_cf SEGS B S mem)
  by exact (QMm_cf_of_room SEGS B ly S Hp W mem md (proj1 HAR) HQT (YGcfRoomLive.room_live_room S HRL) HHO HARO).
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + (CN_OFF + off)))) by exact (ret_ok_codeptr_v (CN_OFF + off) Hoff Hoff2).
assert (Hgp : getr regsT 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp0).
assert (Htp : getr regsT 4 = w64 (as_tp B)) by (rewrite R4; exact Htp0).
assert (Hsp' : spZ regsT = cn_sp0 D + (cn_S1 D - cn_sp0 D)) by lia.
assert (Hneg : cn_S1 D - cn_sp0 D <= 0) by lia.
assert (Hbud : ASTACK - (cn_S1 D - cn_sp0 D) <= STK) by lia.
assert (Hwin : cn_sp0 D + (cn_S1 D - cn_sp0 D) = cn_S1 D) by lia.
pose proof (universe_ok_of_ARcf SEGS B ly S Hp W mem md (proj1 HAR)) as HUOK.
pose proof (alloc_model_laws_x_cf B HUOK) as AMX.
(* the free's admits at S: its trace is a fixed one *)
pose proof (admits_fix _ _ S HUOK Htr) as HADM.
destruct (Z.eq_dec q 0) as [Hq0 | Hq0].
- (* free (NULL): the wrapper's PNull arm *)
  subst q. unfold cn_cblk in HAB, HLf, HPG. rewrite Z.eqb_refl in HAB, HLf, HPG. cbn [app] in HAB, HLf, HPG.
  assert (Hnz : ~ In 0 Hp).
  { intros H0. pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED) as HPm.
    apply (Permutation_in _ HPm) in H0. apply in_map_iff in H0 as ((a & k0) & Ea & Hin). cbn [fst] in Ea.
    pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED) as HFa.
    rewrite Forall_forall in HFa.
    destruct (HFa (a, k0) Hin) as (_ & Hab & _). cbn [fst snd] in Hab. rewrite Ea in Hab.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & _). lia. }
  (* free(NULL) keeps the depot (YGcfAmx2.ipost_free_null_depot on the returning path) *)
  assert (HDEP : forall trc S2, apath (free_cf PNull (call_trace ly (pc_free_ra0 (as_code B)) regsT ch) S) trc (tt, S2) ->
    st_depot S2 = st_depot S).
  { intros trc S2 Hpa. pose proof (YGcfRoomStep.ipost_apath _ _ _ _ (YGcfAmx2.ipost_free_null_depot _ S) Hpa) as Hd.
    cbn [snd] in Hd. exact Hd. }
  (* the NULL free's rule with the memnorm keep (the cf instance at wle' SEGS RZ_cf, from the primed row) runs at the
     empty budget: the journal rebased to the current depot, and back *)
  pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ0.
  eapply (SRr'_bind SEGS RZ_cf).
  { exact (aj_free_null_at_cf_rh_keep (fx := fxk) (rc := rc) (SK := SK) SEGS B prh_pst LAWS (@pa_segs_low _ _ PA)
      (pal_env B PAL) OWNLOW WFL AMX (AFREE fxk)
      W regsT mem STK (cn_sp0 D) [] (ci_ly D) (set_depot (st_depot S) (ci_S D)) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
      [(CN_CID, ci_fpos D)] ly S Hp md k (cn_S1 D - cn_sp0 D) (Z_to_bv 64 (BASE + (CN_OFF + off))) ch
      HJ0 R10 Hnz Hsp' Hm Hneg Hbud Hgp Htp R1 Hraw HQM Hchp HADM HDEP). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Eab & Hfr2 & HPREc &
    (trc & Hpath & Hgf & Hleaf) & HKEPT & Hmn).
  pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 (ajxR_wild HJw)) as HJ2w.
  assert (HJ2c : cn_JR B ARcfx (wle' SEGS RZ_cf) D ly2 S2 Hp W2 mem2 md2 (k + (st_nev S2 - st_nev S)) 6)
    by (exists WS; exact (conj HJ2w HWB)).
  destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & _ & _ & Herr & _).
  unfold cfg_at in Hc'. injection Hc' as _ _ Em2 _. subst mem'.
  apply SRr'_ret. exists ly2, S2, regs2, mem2, md2, (k + (st_nev S2 - st_nev S)).
  split; [reflexivity|].
  split; [|split; [exact HP2 | split; [exact (YGcfSecsStep.secs_free_step _ _ _ _ _ Hpath) |
    exact (PCALL mem mem2 Hmn HPM)]]].
  rewrite Hwin in HKEPT.
  split.
  { apply (fb_mem_keep D fxk ly S Hp W mem md k Lam peak cnt ran r2 ownl ly2 S2 W2 mem2 md2 _ _ (fun _ => False) HPRE HM
      HJ2c Hfr2 HKEPT Herr); [intros a [] | intros b Hb _; rewrite Eab; exact Hb]. }
  split; [rewrite Eab; exact HAB|].
  split; [exact HLf|].
  split.
  { exact (YGcfRoomLive.RL_free_step SEGS B ly S Hp W regsT mem md ch _ PNull _ trc (tt, S2)
      (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) (CfRoomLivePreset.preset_rl_b24_ok S HC24) HRL Hpath). }
  split.
  { refine (Z.le_trans _ _ _ (fb_ccnt24_le ly S ly2 S2 [] _) HC24). cbn [app]. rewrite Eab. apply Permutation_refl. }
  intros Ho0. destruct (HPG Ho0) as (o1 & o2 & o0 & E0 & Hran & Hprog & Heq).
  exists o1, o2, o0, E0. split; [exact Hran|]. split; [|exact Heq].
  apply (fb_prog_null D E0 S S2 Hprog).
  + rewrite <- (fb_blocks_snd ly2 S2), <- (fb_blocks_snd ly S), Eab; reflexivity.
  + intros sm x0 os i0 H0 hist0 Hpos0.
    exact (PresetRoomPosKeep.room_pos_keep_free_null SEGS B ly S Hp W regsT mem md ch sm x0 os i0 H0 hist0 _ trc S2
      (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) Htr Hpath Hpos0).
- (* a live copy: the wrapper's block arm *)
  unfold cn_cblk in HAB, HLf, HPG. rewrite (proj2 (Z.eqb_neq q 0) Hq0) in HAB, HLf, HPG. cbn [app] in HAB, HLf, HPG.
  destruct (HLf (q, cn_size D + 16) (or_introl eq_refl)) as (_ & Hnh & Hne). cbn [fst] in Hnh.
  assert (Hin : In (q, cn_size D + 16) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HAB)); left; reflexivity).
  eapply (SRr'_bind SEGS RZ_cf).
  { exact (YGcallMxmnKeep.aj_free_at_x_ct_m_rh_keep (fx := fxk) (rc := rc) (SK := SK) SEGS B prh_pst LAWS
      (@pa_segs_low _ _ PA) (pal_env B PAL) OWNLOW WFL AMX (AFREE fxk)
      W regsT mem STK (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)]
      ly S Hp md k q (cn_size D + 16) (cn_S1 D - cn_sp0 D) (Z_to_bv 64 (BASE + (CN_OFF + off))) ch
      HJw Hin Hnh R10 Hsp' Hm Hneg Hbud Hgp Htp R1 Hraw HQM Hchp HADM (fun H => False_ind _ (Hne H))). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Eab1 & Eab2) & Hfr2 & HPREc &
    Htrc & (qq & trc & Hqa & Hqin & Hpath & Hgf & Hleaf) & HKEPT & HMN).
  (* the journal after the call: the fixed trace leaves the budget *)
  pose proof (ajournal_xw_fix1R Htr HJ2) as HJ2f.
  assert (HJ2c : cn_JR B ARcfx (wle' SEGS RZ_cf) D ly2 S2 Hp W2 mem2 md2 (k + (st_nev S2 - st_nev S)) 6)
    by (exists WS; exact (conj HJ2f HWB)).
  destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & _ & _ & Herr & _).
  unfold cfg_at in Hc'. injection Hc' as _ _ Em2 _. subst mem'.
  pose proof (proj1 (fb_req_n D)) as Hreq.
  apply SRr'_ret. exists ly2, S2, regs2, mem2, md2, (k + (st_nev S2 - st_nev S)).
  split; [reflexivity|].
  split; [|split; [exact HP2 | split; [exact (YGcfSecsStep.secs_free_step _ _ _ _ _ Hpath) |
    exact (PCALL mem mem2 HMN HPM)]]].
  rewrite Hwin in HKEPT.
  assert (Hkeep : forall b, In b (ablocks B ly S) -> b <> (q, cn_size D + 16) -> In b (ablocks B ly2 S2)).
  { intros b Hb Hbq. rewrite Eab1 in Hb. rewrite Eab2. apply in_app_or in Hb as [Hb | [Hb | Hb]];
      [apply in_or_app; left; exact Hb | exfalso; exact (Hbq (eq_sym Hb)) | apply in_or_app; right; exact Hb]. }
  split.
  { apply (fb_mem_keep D fxk ly S Hp W mem md k Lam peak cnt ran r2 ownl ly2 S2 W2 mem2 md2 _ _ _ HPRE HM HJ2c Hfr2 HKEPT
      Herr).
    - intros a Ha. exists q, (cn_size D + 16). split; [exact Hin|]. split; [exact Hnh|]. rewrite Hreq in Ha |- *. exact Ha.
    - intros b Hb Hbp. apply (Hkeep b Hb). intros ->. exact (Hnh Hbp). }
  split.
  { rewrite Eab2. rewrite Eab1 in HAB.
    apply (Permutation_cons_inv (a := (q, cn_size D + 16))).
    exact (Permutation_trans (Permutation_middle l1 l2 (q, cn_size D + 16)) HAB). }
  split; [intros b Hb; exact (HLf b (or_intror Hb))|].
  split.
  { exact (YGcfRoomLive.RL_free_step SEGS B ly S Hp W regsT mem md ch _ qq _ trc (tt, S2)
      (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) (CfRoomLivePreset.preset_rl_b24_ok S HC24) HRL Hpath). }
  assert (Hmid : Permutation (l1 ++ (q, cn_size D + 16) :: l2) ((q, cn_size D + 16) :: l1 ++ l2))
    by (apply Permutation_sym, Permutation_middle).
  split.
  { refine (Z.le_trans _ _ _ (fb_ccnt24_le ly S ly2 S2 [(q, cn_size D + 16)] _) HC24).
    rewrite Eab1, Eab2. exact Hmid. }
  assert (Hqn : qq <> PNull) by (intros ->; cbn in Hqa; lia).
  intros Ho0. destruct (HPG Ho0) as (o1 & o2 & o0 & E0 & Hran & Hprog & Heq).
  exists o1, o2, o0, (E0 ++ [PresetReqAt.HFr (cn_size D + 16)]). split; [exact Hran|]. split.
  + apply (fb_prog_fr D E0 S S2 (cn_size D + 16) Hprog).
    * rewrite <- (fb_blocks_snd ly S), <- (fb_blocks_snd ly2 S2), Eab1, Eab2. exact (Permutation_map snd Hmid).
    * intros sm x0 os i0 H0 hist0 Hpos0 He0. eexists.
      exact (PresetRoomPosKeep.room_pos_keep_free SEGS B ly S Hp W regsT mem md ch sm x0 os i0 H0 hist0 qq
        (cn_size D + 16) _ trc S2 (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) Htrc Hqin Hqn Hpath Hpos0 He0).
  + rewrite <- app_assoc. exact Heq.
Qed.

(* the three frees' return sites, and their code offsets *)
Lemma fb_off_ok : forall off, In off [1092; 1100; 1108] -> 0 <= CN_OFF + off < 2 ^ 40 /\ (CN_OFF + off) mod 2 = 0.
Proof. intros off H. rewrite fb_off. cbn in H. destruct H as [<- | [<- | [<- | []]]]; split; first [lia | reflexivity]. Qed.

Ltac fb_ne := let E := fresh "E" in intros E; vm_compute in E; discriminate E.

(* ==== THE SEGMENT: a stretch that crosses three frees, so SRr' SEGS RZ_cf (Cno102A_F.v cn_seg_frP) ==== *)
Theorem cn_seg_fr : cn_seg_frP (fx := fx) (cp := CfParamsPreset.CfParams_preset) B CTX0.
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl HPRE HAT HPM.
destruct HAT as (HB & HRS & HSL & HC1 & HC2 & HC3 & HLED & Hpk & Hcn & HRL & HLam & HAB & Hown & Hr & HEV & HCD & HHB).
(* the hull admission at every state with the cut state's secondary counts (each free keeps them) *)
assert (HHO : forall S', YGcfSecsStep.secs_same S S' -> cf_hull_ok S')
  by (intros S' Hs; exact (PresetHullPay.hull_ok_of_budget S' _ (PresetHullBudget.hull_budget_same S S' _ Hs HHB))).
destruct HB as (Hfz & Hfk & HJ & HFR & HSV & R3 & R4 & HROD).
destruct (fb_sp0 D HPRE) as (Hal & Hc & Htop & Htop47 & Hm & Hs1a & Hs1b).
pose proof fb_stk as Hstk. assert (Has : ASTACK = 16384) by reflexivity.
pose proof asan_consts as (C1 & _).
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _).
pose proof (fb_req_n D) as (Hreq & Hn16).
(* the cut's registers *)
assert (G2 : getr regs 2 = w64 (cn_S1 D)) by (apply (fb_rs regs _ _ _ HRS); left; reflexivity).
assert (G8 : getr regs 8 = w64 (cn_sp0 D)) by (apply (fb_rs regs _ _ _ HRS); right; left; reflexivity).
assert (G9 : getr regs 9 = w64 (cn_S1 D)) by (apply (fb_rs regs _ _ _ HRS); right; right; left; reflexivity).
assert (G26 : getr regs 26 = w64 r1)
  by (apply (fb_rs regs _ _ _ HRS); apply in_or_app; right; right; right; left; reflexivity).
assert (G22 : getr regs 22 = w64 r3)
  by (apply (fb_rs regs _ _ _ HRS); apply in_or_app; right; right; left; reflexivity).
(* the slots *)
unfold cn_slots in HSL. rewrite Forall_forall in HSL.
pose proof (HSL (32, cn_F D) ltac:(right; left; reflexivity)) as S32.
pose proof (HSL (40, r2) ltac:(right; right; left; reflexivity)) as S40. cbn [fst snd] in S32, S40.
(* the invariant at the cut *)
pose proof HJ as (WS0 & HJ0w & _). pose proof (ajxR_ar HJ0w) as HAR.
assert (HI0 : fb_inv D fxk ly S Hp W mem md k Lam peak cnt ran (cn_cblks D r1 r2 r3) r2 ownl).
{ split; [repeat (split; [assumption|]); exact HLED|].
  split; [exact HAB|].
  split.
  - intros b Hb. pose proof Hb as Hb'.
    assert (Hcopy : forall q, cn_cpy B D ly S Hp q -> In b (cn_cblk D q) ->
      snd b = cn_size D + 16 /\ ~ In (fst b) Hp /\ ~ In b (ablocks B (ci_ly D) (ci_S D))).
    { intros q Hq Hbq. unfold cn_cblk in Hbq. destruct (Z.eqb_spec q 0) as [_ | Hq0]; [destruct Hbq|].
      destruct Hbq as [<- | []]. destruct Hq as [Hq | (Hin & Hnh)]; [contradiction|]. cbn [fst snd].
      split; [reflexivity|]. split; [exact Hnh|].
      apply (fb_not_entry ly S Hp W mem md (cn_cblks D r1 r2 r3) _ (q, cn_size D + 16) HAR HAB Hb').
      cbn [snd]. lia. }
    unfold cn_cblks in Hb. apply in_app_or in Hb as [Hb | Hb]; [exact (Hcopy r1 HC1 Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (Hcopy r2 HC2 Hb) | exact (Hcopy r3 HC3 Hb)].
  - split; [exact HRL|]. split; [exact (fb_c24_cut D ly S r1 r2 r3 HPRE HAB)|].
    intros Ho0. destruct (HEV Ho0) as (Hn1 & Hn2 & Hn3 & o1 & o2 & o0 & Hprog & Hran).
    exists o1, o2, o0, (cn_C3 D ++ cn_revs3 D o1 o2 o0 ++ cn_fpj D o1 o2 o0).
    split; [exact Hran|]. split; [exact Hprog|].
    unfold cn_cblks, cn_cblk.
    rewrite (proj2 (Z.eqb_neq r1 0) Hn1), (proj2 (Z.eqb_neq r2 0) Hn2), (proj2 (Z.eqb_neq r3 0) Hn3).
    cbn [app map].
    change (cn_fevs D o1 o2 o0) with
      (cn_fpj D o1 o2 o0 ++ repeat (PresetReqAt.HFr (cn_size D + PresetReqAt.FUZZ_PAD)) 3).
    rewrite <- !app_assoc. reflexivity. }
unfold cn_cblks in HI0.
(* ---- free 1 (1084 mv a0, s10; 1088 jal __wrap_free) ---- *)
unfold cn_cfg, cn_pc, CN_FRCUT, w64. replace (BASE + CN_OFF + 1084) with (BASE + (CN_OFF + 1084)) by lia.
apply (fb_s_addi (fz := fxk) (wle' SEGS RZ_cf) W regs mem md _ (CN_OFF + 1084) (CN_OFF + 1088) 10%bv 26%bv 0 fb_sl1
  eq_refl ltac:(rewrite fb_off; lia) ltac:(rewrite fb_off; lia) ltac:(lia)).
intros md1 Hm1.
apply (fb_h_call (fz := fxk) (wle' SEGS RZ_cf) W _ mem md1 _ (CN_OFF + 1088) (CN_OFF + 1092) AS___wrap_free fb_cl1
  ltac:(rewrite fb_off; lia) ltac:(rewrite fb_off; lia) ltac:(lia)).
intros md2 Hm2.
rewrite (pal_free B PAL).
set (regsA := regupd (regupd regs 10%bv (v_addi (getr regs 26%bv) 0)) 1%bv (Z_to_bv 64 (BASE + (CN_OFF + 1092)))).
assert (HPA : aregs_preserved regs regsA) by (apply fb_ap_upd; [left; reflexivity|]; apply fb_ap_upd; [right; reflexivity|];
  apply fb_ap_refl).
destruct (fb_off_ok 1092 ltac:(left; reflexivity)) as (Ho1 & Ho1').
eapply (SRr'_bind SEGS RZ_cf).
{ apply (fb_free P PLAW PCALL D fxk ly S Hp W regsA mem md2 k Lam peak cnt ran r1 (cn_cblk D r2 ++ cn_cblk D r3) r2
    ownl 1092 HPRE).
  - exact (fb_inv_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md2 HI0 (same_but_materialized_trans _ _ _ Hm1 Hm2)).
  - exact (HHO S (YGcfSecsStep.secs_same_refl S)).
  - rewrite (fb_ap_get regs regsA 2 2%bv HPA ltac:(left; reflexivity) eq_refl). exact G2.
  - rewrite (fb_ap_get regs regsA 8 8%bv HPA ltac:(unfold acallee_saved; lia) eq_refl). exact G8.
  - rewrite (fb_ap_get regs regsA 3 3%bv HPA ltac:(unfold acallee_saved; lia) eq_refl). exact R3.
  - rewrite (fb_ap_get regs regsA 4 4%bv HPA ltac:(unfold acallee_saved; lia) eq_refl). exact R4.
  - unfold regsA. rewrite fb_getr_upd by fb_ne. rewrite fb_getr_same by reflexivity.
    rewrite G26. unfold v_addi, w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - unfold regsA. rewrite fb_getr_same by reflexivity. reflexivity.
  - exact fb_site1.
  - exact Ho1.
  - exact Ho1'.
  - exact HPM. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md3 & k2 & -> & HI2 & HP2 & HSS2 & HPM2).
pose proof (fb_ap_trans _ _ _ HPA HP2) as HPB.
(* ---- free 2 (1092 ld a0, 40(s1); 1096 jal __wrap_free) ---- *)
assert (G9b : getr regs2 9 = w64 (cn_S1 D)) by (rewrite (fb_ap_get regs regs2 9 9%bv HPB ltac:(unfold acallee_saved; lia) eq_refl); exact G9).
pose proof HI2 as ((_ & _ & _ & _ & _ & _ & _ & H40 & _) & _).
apply (fb_s_ld (fz := fxk) (wle' SEGS RZ_cf) W2 regs2 mem2 md3 _ (CN_OFF + 1092) (CN_OFF + 1096) 10%bv 9%bv 40
  (cn_S1 D + 40) r2 fb_sl2
  eq_refl ltac:(rewrite fb_off; lia) ltac:(rewrite fb_off; lia) ltac:(lia)); [| lia | lia | exact H40 |].
{ rewrite G9b. unfold v_addi, w64. rewrite unsigned_lit_small by lia. reflexivity. }
intros md4 Hm4.
apply (fb_h_call (fz := fxk) (wle' SEGS RZ_cf) W2 _ mem2 md4 _ (CN_OFF + 1096) (CN_OFF + 1100) AS___wrap_free fb_cl2
  ltac:(rewrite fb_off; lia) ltac:(rewrite fb_off; lia) ltac:(lia)).
intros md5 Hm5.
rewrite (pal_free B PAL).
set (regsB := regupd (regupd regs2 10%bv (Z_to_bv 64 r2)) 1%bv (Z_to_bv 64 (BASE + (CN_OFF + 1100)))).
assert (HPB' : aregs_preserved regs regsB) by (apply fb_ap_upd; [left; reflexivity|]; apply fb_ap_upd; [right; reflexivity|];
  exact HPB).
destruct (fb_off_ok 1100 ltac:(right; left; reflexivity)) as (Ho2 & Ho2').
eapply (SRr'_bind SEGS RZ_cf).
{ apply (fb_free P PLAW PCALL D fxk ly2 S2 Hp W2 regsB mem2 md5 k2 Lam peak cnt ran r2 (cn_cblk D r3) r2 ownl 1100
    HPRE).
  - exact (fb_inv_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md5 HI2 (same_but_materialized_trans _ _ _ Hm4 Hm5)).
  - exact (HHO S2 HSS2).
  - rewrite (fb_ap_get regs regsB 2 2%bv HPB' ltac:(left; reflexivity) eq_refl). exact G2.
  - rewrite (fb_ap_get regs regsB 8 8%bv HPB' ltac:(unfold acallee_saved; lia) eq_refl). exact G8.
  - rewrite (fb_ap_get regs regsB 3 3%bv HPB' ltac:(unfold acallee_saved; lia) eq_refl). exact R3.
  - rewrite (fb_ap_get regs regsB 4 4%bv HPB' ltac:(unfold acallee_saved; lia) eq_refl). exact R4.
  - unfold regsB. rewrite fb_getr_upd by fb_ne. rewrite fb_getr_same by reflexivity. reflexivity.
  - unfold regsB. rewrite fb_getr_same by reflexivity. reflexivity.
  - exact fb_site2.
  - exact Ho2.
  - exact Ho2'.
  - exact HPM2. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md6 & k3 & -> & HI3 & HP3 & HSS3 & HPM3).
pose proof (fb_ap_trans _ _ _ HPB' HP3) as HPC.
(* ---- free 3 (1100 mv a0, s6; 1104 jal __wrap_free) ---- *)
apply (fb_s_addi (fz := fxk) (wle' SEGS RZ_cf) W3 regs3 mem3 md6 _ (CN_OFF + 1100) (CN_OFF + 1104) 10%bv 22%bv 0 fb_sl3
  eq_refl ltac:(rewrite fb_off; lia) ltac:(rewrite fb_off; lia) ltac:(lia)).
intros md7 Hm7.
apply (fb_h_call (fz := fxk) (wle' SEGS RZ_cf) W3 _ mem3 md7 _ (CN_OFF + 1104) (CN_OFF + 1108) AS___wrap_free fb_cl3
  ltac:(rewrite fb_off; lia) ltac:(rewrite fb_off; lia) ltac:(lia)).
intros md8 Hm8.
rewrite (pal_free B PAL).
set (regsC := regupd (regupd regs3 10%bv (v_addi (getr regs3 22%bv) 0)) 1%bv (Z_to_bv 64 (BASE + (CN_OFF + 1108)))).
assert (HPC' : aregs_preserved regs regsC) by (apply fb_ap_upd; [left; reflexivity|]; apply fb_ap_upd; [right; reflexivity|];
  exact HPC).
destruct (fb_off_ok 1108 ltac:(right; right; left; reflexivity)) as (Ho3 & Ho3').
rewrite <- (app_nil_r (cn_cblk D r3)) in HI3.
eapply (SRr'_bind SEGS RZ_cf).
{ apply (fb_free P PLAW PCALL D fxk ly3 S3 Hp W3 regsC mem3 md8 k3 Lam peak cnt ran r3 [] r2 ownl 1108 HPRE).
  - exact (fb_inv_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md8 HI3 (same_but_materialized_trans _ _ _ Hm7 Hm8)).
  - exact (HHO S3 (YGcfSecsStep.secs_same_trans _ _ _ HSS2 HSS3)).
  - rewrite (fb_ap_get regs regsC 2 2%bv HPC' ltac:(left; reflexivity) eq_refl). exact G2.
  - rewrite (fb_ap_get regs regsC 8 8%bv HPC' ltac:(unfold acallee_saved; lia) eq_refl). exact G8.
  - rewrite (fb_ap_get regs regsC 3 3%bv HPC' ltac:(unfold acallee_saved; lia) eq_refl). exact R3.
  - rewrite (fb_ap_get regs regsC 4 4%bv HPC' ltac:(unfold acallee_saved; lia) eq_refl). exact R4.
  - unfold regsC. rewrite fb_getr_upd by fb_ne. rewrite fb_getr_same by reflexivity.
    rewrite (fb_ap_get regs regs3 22 22%bv HPC ltac:(unfold acallee_saved; lia) eq_refl), G22.
    unfold v_addi, w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - unfold regsC. rewrite fb_getr_same by reflexivity. reflexivity.
  - exact fb_site3.
  - exact Ho3.
  - exact Ho3'.
  - exact HPM3. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md9 & k4 & -> & HI4 & HP4 & HSS4 & HPM4).
pose proof (fb_ap_trans _ _ _ HPC' HP4) as HPD.
(* ---- CN_END ---- *)
apply SRr'_ret. split; [|exact HPM4].
destruct HI4 as ((Hfz4 & Hfk4 & HJ4 & HFR4 & HSV4 & HROD4 & HS32' & _ & HLED4) & HAB4 & _ & HRL4 & _ & HPG4).
exists fxk, ly4, S4, Hp, regs4, mem4, md9, k4, Lam, peak, cnt, ran, r, ownl.
split.
{ unfold cn_cfg, cn_pc, CN_END, w64. f_equal. f_equal. f_equal. lia. }
split.
{ split; [exact Hfz4|]. split; [exact Hfk4|]. split; [exact HJ4|]. split; [exact HFR4|]. split; [exact HSV4|].
  split; [rewrite (fb_ap_get regs regs4 3 3%bv HPD ltac:(unfold acallee_saved; lia) eq_refl); exact R3|].
  split; [rewrite (fb_ap_get regs regs4 4 4%bv HPD ltac:(unfold acallee_saved; lia) eq_refl); exact R4|].
  exact HROD4. }
split.
{ unfold cn_regsat. rewrite Forall_forall. intros (x & v) Hx. cbn [fst snd].
  assert (Hx' : In (x, v) (cn_core D ++ [(21%bv, r); (22%bv, r3); (26%bv, r1)]))
    by (unfold cn_core in Hx |- *; cbn [app In] in Hx |- *; tauto).
  assert (Hcs : acallee_saved (bv_unsigned x)).
  { unfold cn_core in Hx. cbn [app In] in Hx.
    repeat (destruct Hx as [Ex | Hx]; [injection Ex as <- _;
      match goal with |- acallee_saved (bv_unsigned ?y) =>
        let n := eval vm_compute in (bv_unsigned y) in change (bv_unsigned y) with n end;
      unfold acallee_saved; lia |]).
    destruct Hx. }
  rewrite (fb_ap_get regs regs4 (bv_unsigned x) x HPD Hcs eq_refl). exact (fb_rs regs _ x v HRS Hx'). }
split; [exact HS32'|].
split; [exact HLED4|].
split; [exact HLam|].
split; [rewrite app_nil_l in HAB4; exact HAB4|].
split; [exact Hpk|].
split; [exact Hcn|].
split; [exact HRL4|].
split; [exact Hr|].
(* a refused copy: its cn_cdead D (state-free) carried; the hull budget last *)
split; [|split; [exact HCD|]].
- (* under ownl = 0: the three frees' HFr complete the events to the text's whole list *)
  intros Ho0. destruct (HPG4 Ho0) as (o1 & o2 & o0 & E0 & Hran & Hprog & Heq).
  exists o1, o2, o0. split; [|exact Hran].
  cbn [map] in Heq. rewrite app_nil_r in Heq. rewrite <- Heq. exact Hprog.
- (* the hull budget: the frees kept both counts, so the cut's budget over pf0 (= cn_hF3) holds at S4 *)
  rewrite (cn_hrest_frees_split (ci_x D)) in HHB.
  exact (PresetHullBudget.hull_budget_same S S4 _
    (YGcfSecsStep.secs_same_trans _ _ _ (YGcfSecsStep.secs_same_trans _ _ _ HSS2 HSS3) HSS4) HHB).
Qed.

End cf.

Print Assumptions cn_seg_fr.
Check cn_seg_fr.

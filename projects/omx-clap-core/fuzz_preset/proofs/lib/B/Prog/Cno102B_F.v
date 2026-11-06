(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 234 of its 303 lines of code are new or changed and 709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/PRW_WalkEnv.v, with its module paths and module names changed; 2314 of its 2391 lines of code are new or changed and 226 lines of the source are left out. *)
(* rule 24: no function proved
   rule 24: proves no function (kind: segment lemma)
   fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b):
   SEGMENT CB8 Free of the re-walk of check_no_overread (cno, entry B' 0x819f0 = slot 201 of the whole-program
   listing), and the call steps CB9 End needs. Lane CnoB102f (a Theorem Labs lane, #102 plan
   the internal file PLAN-cno-caw-102.md sections 5.0 / 5.2, row "CB8 Free | 0x81cd0 -> 0x81d04"); first proved on the
   exact-position contract (the #102 kit tip) by a first fit, re-fit to the kit's CUT
   a working branch 7cdbb61b5fa0 by sub-lane CutF8. The twin of image A''s lib/A/Prog/Cno102A_F.v.
   INPUTS (every path at the cut's blob, through the row's base 75415fdb6e76, except
   the two kit files named below):
     SHARED CONTRACT lib/B/Prog/Cno102B_Base.v 20c89a1d4da2 (lane CnoB102rR, the B' contract on the cut): every cut,
     cnb_pre / cnb_at_freeR / cnb_Q / cnb_ex_ret, the budgeted journal cnb_JR / cnb_baseR at the spent wild budget wk
     over a world relation, the
     event pieces cnb_C3 / cnb_revs3 / cnb_fevs / cnb_ranz (cnb_ck_cno_evs: C3 ++ revs3 ++ fevs = ck_cno_evs), the
     progress fact cnb_prog, the structs against the grants cnb_rd / cnb_rds3, the trees' free order cnb_fo, the
     refused copy's cnb_cdead, and the listing tables PL_cno_B. This file STATES CB8's exit cut (cnb_at_end /
     cnb_ex_end, CB9's start) and PROVES the call steps; nothing here re-states the contract.
     STEP KIT lib/B/Prog/Cno102B_Ro.v c1b5ec3f8fff (sub-lane CutRo, a working branch 77b925b222cc, by
     path): cnb_J_rebaseR / cnb_J_fixedR (the cut's journal across a fixed-trace step at the same wild budget, at
     the world relation of the cut: wle' at the re-hiding zone here) and the progress lemma cnb_prog_app that
     threads cnb_prog through the six frees.
     FREE KIT lib/A/Prog/Cno102_FKit.v 460df9d979c5 (the A' twin's re-fit on the cut, lane CnoABatch2,
     a working branch 695448b071a2, by path): pjf_fd_of_node (the ported tree lemmas) and
     aj_free_null_at_cf_rh_keep (free(NULL) over ajournal_xR at wle' segs RZ_cf, its PNull-only text from the primed
     free row with the keep, with the free's admission, the depot it keeps and the memnorm keep).
     lib/Prog/PvFdZeroR.v 4767f7407d9b: pv_fd_zeroR, the ONE home of `pj_rwR -> pj_zeroR -> pj_fdR n v []` in R form (a
     zero struct's order list, cnob_fos). lib/Prog/PvMain0.v is NOT Required: it fails on the pins102 targets.
     The kit texts at the cut: lib/A/PRH_FnPj.v 5aca5cbe2cfb (tpj_free_specX: no DW, prh_head_wide, position-free
     entry with the class-24 bound and the hull budget for v <> 0, the order list F of lib/A/PRH_PjOrder.v
     e5917626b82b, the position transfer as a post-implication over any run whose next events are prhPj_free_evs F;
     restated for the re-hiding move: it concludes SRr' segs RZ_cf with its post fpostWmR at wle' segs RZ_cf; its Q,
     with the hull use hull_used S S' [], is the kit's named tpfP_Q, read through tpfP_R_of), PRH_Base.v ef7c8ca98529
     (prh_univ_closure without DW, prh_head_wide / prh_head16; prh_ledger and its NAMED projections, never read by
     position), PRH_FnCheck.v c40cf3fdcd2a (tparse_noting_specX's Some arm: the tree's free order against pj_frees,
     carried to the free cut as cnb_fo), PRH_FnAlloc.v 4d8aeba047e5, PRH_FnReader.v f1ae32e3b2cd, PRH_Reader.v
     4266e709561a, lib/B/PRH_ImgB.v 3216eca68342, lib/A/CfParamsPreset.v b60d0f63c926, lib/Reusable/YGcfRoomLive.v
     edc1017de99c, lib/Spec/PresetRodata.v 4eb7e95e7e93, PresetRoomPos.v 943d62290e8e, PresetRoomPosKeep.v dc3f6bee1e0e
     (room_pos_keep_free at the free's admission / _free_null: the runtime frees' position step), the run model of
     record PresetRun.v 5ac818ab1fe6 (p1_tfree, ranout_refused) / PresetReqAt.v 43c958024221 / PresetReqAtNoMiss.v
     f949715d7a12 (rm1_perm / rmall_perm / rm1_mid).
     LISTING (the cut's): lib/B/Listing_prog.v c97cc46b3e13, lib/Reusable/YPsym.v b6f5a85d234d. lib/B/PAImg_prog.v is
     NOT Required; this file is PARAMETRIC over {PA : PAImg B_prog_listing} (owner 12:48Z) and uses the contract's
     PL_cno_B.
     ENGINE (the cut's P'' set): YGcallx.v fffbc375ffac, YGcallcf.v 8645fa6a514f, YC80x.v 14f84f225e8f (srr_inv_laws),
     YC1fPx.v 7814b594066f (paj_run_*_inv over ajournal_x), YSRrMemnorm.v 5ffa8525936b, YCbqG.v 219748197d6b
     (ajournal_xwR read through the ajxR_* projections; admits_ct_fix, ajx_budgetR), YCbqGwild.v 0c63874858e4
     (wbudget), YGcallMxmn.v (aset_shadow_realizes_xm / aj_set_shadow_at_xmR, their one home), YGcallMxmnKeep.v
     (aj_free_at_x_ct_m_rh_keep: the cf free rule under the re-hide over the keep row afree_realizes_cf_rh_keep of
     YGcfMallocComposeKeep.v, the journal at wle' segs RZ_cf, the conclusion SRr' segs RZ_cf, the memnorm keep last;
     the plain rule YGcallMxmn.aj_free_at_x_ct_m_rh exports no keep since part 3c), YGcfAmx2.v 8e1bfbb48426
     (ipost_free_null_depot), YGcfRoomStep.v 99f35090fcd0 (ipost_apath); PRW_StepKit.v 0df3991c13f4; YA0nH.v /
     YSRrG.v (SRr', wle', SRr'_bind / SRr'_mono), YGcfRehidePost.v (RZ_cf), YC1fPx.v's paj_run_x_invR,
     YCbqGcallW.v's aj_call_xWR, YGcfSecsStep.v (secs_free_step); lib/Spec/PresetHullBudget.v and
     lib/A/PresetHullPay.v (the threaded allocator hull budget).
   THE WILD BUDGET (the cut's P'' engine): every cut from the readings on carries the journal at the spent budget,
   cnb_JR D wk at wle' (wk = 6 = prh_wk F_check_no_overread at the free cut and at CB9's start). CB8's six callees are
   FIXED-trace (pj_free's text posts the empty-budget journal; each __wrap_free stores a fixed call trace, which
   YCbqG.ajournal_xw_fix1R drops from the budget), so the walk rebases the cut's journal to the empty-budget one from
   the entry with the current depot (the kit's cnb_J_rebaseR), runs the empty-budget rules and runner on it, and
   composes the result back onto the cut's journal at the same budget (the kit's cnb_J_fixedR): wk stays 6.
   THE SEGMENT (DERIVED byte offsets inside check_no_overread, cross-checked on Listing_prog.v by cnob_slots below):
     736 `li s8, 1`        the r = 1 join (CB7's exits; CnoB102r's, not this file's)
     740 CNB_FREE          CB8 start, `mv a0, s6`  (s8 = r)
     744 `jal pj_free`     d1 = F + 32   -> 748
     752 `jal pj_free`     d2 = F + 128  -> 756   (748 `mv a0, s5`)
     760 `jal pj_free`     d3 = F + 224  -> 764   (756 `mv a0, s4`)
     768 `jal __wrap_free` r1 = s9       -> 772   (764 `mv a0, s9`)
     776 `jal __wrap_free` r2 at s1 + 24 -> 780   (772 `ld a0, 0x18(s1)`)
     784 `jal __wrap_free` r3 at s1 + 16 -> 788   (780 `ld a0, 0x10(s1)`)
     788 CNB_END           CB9 start, `sb s10, 0x1a(s2)`
   WHAT THE SEGMENT DOES (plan section 4 point 9): pj_free frees the three readings' trees - on a SKIPPED reading the
   struct is the all-zero one CB3's memset left, so the text's `v <> 0 /\ pj_foR .. n v D F` arm is taken with
   D = F = [] through pv_fd_zeroR and PRH_PjOrder.pj_fdR_foR (pv_fd_zeroR's pj_rwR premise comes from prhPj_slot's own
   pj_rwR conjunct). Then free releases the three padded copies; on the ran-out path a copy is NULL, which is
   aj_free_null_at_cf_rh_keep's arm. The progress fact cnb_prog (the contract's, over the events since entry) is
   carried through the six frees when no copy was refused: pj_free's text transfers the position by its own events
   (prhPj_free_evs F), a live copy's free advances by its HFr event (the kit's PresetRoomPosKeep.room_pos_keep_free,
   Qed) and a NULL copy's keeps the position (room_pos_keep_free_null); the live set follows by rmall / rm1.
   THE ORDER, checked against the contract's cnb_fevs (= the model of record's p1_tfree o1 / o2 / o0 by the ranout
   cases, then three HFr (n + FUZZ_PAD); PresetRun.v 5ac818ab1fe6 :347-348, :370-387): CB8 frees d1, d2, d3 (pj_free;
   readings 1 / 2 / 3 parse into d1 = s6, d2 = s5, d3 = s4, the CB4-CB6 parse_noting calls), then r1, r2 (slot 24),
   r3 (slot 16) (__wrap_free). The ORDERS AGREE (cnob_fevs_eq, Qed). Per struct: an ACCEPTED reading's struct emits
   the model's HBulk (pj_frees (okof o) x) (HBulk [] when its tree holds no block, stepped over by
   prhPj_bulk_nil_pos); a REFUSED reading's zero struct emits nothing (p1_tfree's None arm), and so does a reading
   that ran out (PresetRun.ranout_refused) or was skipped after one ran out (the contract's cnb_rds3). The three HFr
   match the copies because the free cut's ownl = 0 arm states them non-NULL.
   THE CLASS-24 BOUND (formerly the named argument CNT24) is DERIVED at the free cut's state, on both arms of
   cnb_at_freeR (cnob_cnt24_free): the cut's progress fact gives the live set as the entry's advanced by the granted
   copies (ownl <> 0: cnb_cevs, a prefix of the all-granted events) or by the three copies and the readings at the
   grants o1 o2 o0 (ownl = 0: a sub-multiset of the all-granted ones, since a reading that ran out leaves nothing,
   PresetRun.ranout_pacc, and one that did not equals the all-granted one, PjGrammar.G7_1), so its class-24 count is
   at most cnb_pre's position-free pkR count over ck_cno_evs .. None None None (PresetRun.pkR_prefix,
   CfRoomLivePreset.preset_ccnt24). tpj_free_specX asks it at entry (v <> 0) and the runtime free's RL_free_step needs
   it; both posts state that ccnt24 never rises, so the bound at the cut carries all six frees.
   THE TREES' FREE ORDER (the former named premise PJF-TIE, CLOSED at the cut): when no copy was refused, the free
   cut's cnb_fo gives, for each filled struct d_k at the depth bound DOC_D, an order list F_k (PRH_PjOrder.pj_foR at
   the cut's memory and ledger list: the reader's OWN blocks of that tree) with `map (fun b => snd b + cf_head) F_k =
   pj_frees jr_strtod (okof o_k) x`, under CFHEAD-16 (cnob_fos_tie); a zeroed struct's F_k is [] (pv_fd_zeroR,
   prhPj_free_evs_nil's shape). cnb_seg_freeP takes NO premise beyond the contract's. The Section hypotheses are the
   texts (AFREE, the primed free row; HPJF, ASETSH), the image record (PAL, IMG; IMG's RELRO rows feed the runtime
   free's call memory fact), and the two cf_head facts (HWIDE: prh_head_wide, owner
   a Theorem Labs lane's preset_head_wide; HEAD16: prh_head16, owner the instance, reflexivity at CfParams_preset).
   THE REFUSED COPY (ownl <> 0): the free cut's cnb_cdead D reads only D; cnb_at_end carries it to CB9 for the post's
   outcome clause.
   BATCH 2 (the kit decff67d721f, kept at the cut): CB8 neither reads nor writes g_own_ran_out or g_most; both are fields
   of the ledger, so the cut's own value ownl and the input's bi_most D travel in the ledger through every call (the
   pj_free text carries them in its post's ledger; the runtime free keeps every program static, cnob_glob_keep), and
   the r fact over ownl is passed through unchanged.
   THE RE-HIDING MOVE: a free (pj_free frees the trees' blocks, __wrap_free the copies) can recycle a secondary and
   hide shadow again, so every walk of this file concludes SRr' segs RZ_cf (YA0nH.v: SRrG at wle' segs RZ_cf, the
   hidden set grows only inside the fixed zone RZ_cf) and every journal is at wle' segs RZ_cf: the free cut is
   cnb_at_freeR at wle' (parse_noting crossed), and cnob_fmid / cnb_at_end are restated at it. Journals are read
   through the ajxR_* projections only.
   THE HULL BUDGET (route (b)): the free cut carries hull_budget S (cnb_hrest_rd0 x), the suffix of the all-granted
   events still to pay; cnob_fmid carries the suffix named by the structs still to free (cnob_hrest: rd0 / pf1 /
   pf2 / pf0), cnb_at_end the one after the frees (cnb_hF3 = pf0, cnb_hrest_frees_split). pj_free takes `v <> 0 ->
   hull_budget S []` (hull_budget_nil) and uses nothing (hull_used S S' [], paid by hull_budget_app); a runtime
   free's admission cf_hull_ok S comes from the carried budget
   (PresetHullPay.hull_ok_of_budget), and free_cf keeps it (YGcfSecsStep.secs_free_step, hull_budget_same). The
   runtime free's call memory fact arodata_ok_cf comes from the cut's journal from entry and the entry fpre's
   arodata_okP (YGcallcf.arodata_ok_cf_of_journal_P, with the contract record's RELRO rows and its non-writable
   read ranges cnbi_ro_reads_nw); memnorm is no conjunct of QMm_cf.
   Numerals: the offsets above (DERIVED); 56 / 32 / 128 / 224 / 48 / 24 / 16 (LENGTH: struct and slot offsets); 6
   (COUNT: the spent wild budget, cnb_base's wk); register numbers (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality Sorted.
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
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre FCiface YGcallx YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoomKeep YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YGcfRoomStep YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YG0dcfR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger PvFdZeroR ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetRoom PresetRoomPos
  PresetRoomPosKeep PresetReqAt PresetReqAtNoMiss PresetRun PresetLiveBounds PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_PjOrder PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit Cno102_FKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base Cno102B_Ro.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- this segment's cut and the return sites of its six calls: DERIVED byte offsets inside check_no_overread ---- *)
Definition CNB_PJF1 : Z := 748.
Definition CNB_PJF2 : Z := 756.
Definition CNB_PJF3 : Z := 764.
Definition CNB_FR1 : Z := 772.
Definition CNB_FR2 : Z := 780.
Definition CNB_FR3 : Z := 788.
Definition CNB_END : Z := 788.

(* THE SLOT CHECK on the listing of record: the function's first word (`addi sp, sp, -0xa0`) and the fifteen slots
   184-198 of the segment - `li s8, 1`; three (`mv a0, s_k`; `jal pj_free`); (`mv a0, s9`; `jal __wrap_free`); two
   (`ld a0, off(s1)`; `jal __wrap_free`); and CB9's first store. This pins every offset above. *)
Lemma cnob_slots :
  map (fun k => nth_error B_prog_listing (CNB_SLOT + k))
      [0; 184; 185; 186; 187; 188; 189; 190; 191; 192; 193; 194; 195; 196; 197]%nat =
  [Some (PW 0xf6010113); Some (PW 0x100c13);
   Some (PW 0xb0513); Some (PCall AS_pj_free (1%bv : bv 5)); Some (PW 0xa8513); Some (PCall AS_pj_free (1%bv : bv 5));
   Some (PW 0xa0513); Some (PCall AS_pj_free (1%bv : bv 5));
   Some (PW 0xc8513); Some (PCall AS___wrap_free (1%bv : bv 5)); Some (PW 0x184b503); Some (PCall AS___wrap_free (1%bv : bv 5));
   Some (PW 0x104b503); Some (PCall AS___wrap_free (1%bv : bv 5)); Some (PW 0x1a90aa3)].
Proof. vm_compute. reflexivity. Qed.

(* ==== SMALL FACTS (image-free) ==== *)
(* the class count of a block list counts its sizes, so a permutation keeps it and a removal lowers it *)
Lemma cnob_filter_perm : forall (f : Z -> bool) l l', Permutation l l' ->
  Permutation (List.filter f l) (List.filter f l').
Proof.
intros f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; simpl.
- constructor.
- destruct (f x); [apply perm_skip; exact IH | exact IH].
- destruct (f x), (f y); first [apply perm_swap | apply Permutation_refl].
- eapply Permutation_trans; eassumption.
Qed.
Lemma cnob_ccnt_perm : forall c l l', Permutation l l' -> PresetRoom.ccnt c l = PresetRoom.ccnt c l'.
Proof.
intros c l l' H. unfold PresetRoom.ccnt. apply Permutation_length. apply cnob_filter_perm. exact H.
Qed.
Lemma cnob_ccnt_app : forall c l l', PresetRoom.ccnt c (l ++ l') = (PresetRoom.ccnt c l + PresetRoom.ccnt c l')%nat.
Proof. intros c l l'. unfold PresetRoom.ccnt. rewrite List.filter_app, List.length_app. reflexivity. Qed.
Lemma cnob_blocks_snd : forall B ly S, map snd (ablocks B ly S) = map snd (blocks S).
Proof. intros B ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.
Lemma cnob_ccnt24_ablocks : forall B ly S,
  YGcfRoomLive.ccnt24 S = Z.of_nat (PresetRoom.ccnt kBatchClass (map snd (ablocks B ly S))).
Proof. intros B ly S. unfold YGcfRoomLive.ccnt24. rewrite cnob_blocks_snd. reflexivity. Qed.
(* a padded copy's allocator block: none for a NULL copy *)
Definition cnob_cblk (n c : Z) : list (Z * Z) := if c =? 0 then [] else [(c, n)].
Lemma cnob_ccnt24_le : forall B ly S ly' S' l,
  Permutation (ablocks B ly S) (l ++ ablocks B ly' S') -> YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S.
Proof.
intros B ly S ly' S' l H. rewrite (cnob_ccnt24_ablocks B ly S), (cnob_ccnt24_ablocks B ly' S').
rewrite (cnob_ccnt_perm _ _ _ (Permutation_map snd H)), map_app, cnob_ccnt_app. lia.
Qed.

(* ==== THE IMAGE B' WALK CONTEXT: preset's CfParams, the room invariant of record, PrhImg prh_img_B (the kit's
   generated B' cells), the contract's listing tables; the PAImg instance is a PARAMETER (owner 12:48Z) ==== *)
Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Instance CF_cp : CfParams := CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Instance CF_RL : PrhRoomLive := prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Instance CF_PL : PAListing B_prog_listing := PL_cno_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* the walk's allocator relation, the cf instance (S1KitAlloc's ARxs, YGcallcf.v; FuzzFreeB.v:379) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Variable SK : YI16.sink_head.
#[local] Notation AJW := (ajournal_xw (SK := SK) SEGS B prh_pst ARcfx).
#[local] Notation STK := STK_check_no_overread.
(* after a free the walk's worlds are related by wle' at the fixed re-hiding zone (YA0nH.v, YGcfRehidePost.v), and
   every journal of this walk is at it *)
#[local] Notation WLE' := (wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ' := (ajournal_xR (SK := SK) SEGS B prh_pst ARcfx WLE').
Variable CTX0 : list (list Z).
(* the callee texts this segment crosses: the runtime free wrapper's primed row with the memnorm keep at its end
   configuration (YGcfMallocComposeKeep.v; P crosses each free by srr_inv_call on that keep) and the kit's pj_free *)
(* the texts hold at EVERY float state: the cut's state is the one the callees left (parse_noting reaches musl
   strtod), not this section's fx, so a call step takes the float state as a parameter *)
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS B.
Hypothesis HPJF : forall fz : YK11.FPState, tpj_free_specX (fx := fz) B ARcfx SK CTX0 DOC_D.
(* CB9 End only (the set_shadow_f5 call step below): the runtime __asan_set_shadow_f5 contract WITH the memnorm keep,
   the engine's YGcallMxmn.aset_shadow_realizes_xm (its one home), at every float state. Owner: the cf instance
   (YGcfNames.v aa_set_shadow_f5_cf's row at value 0xf5 plus the keep, as for every family-1 runtime row, and
   SIGMA AS___asan_set_shadow_f5 = cf_pc_set_shadow_f5). CB8 does not use it. *)
Hypothesis ASETSH : forall fz : YK11.FPState,
  YGcallMxmn.aset_shadow_realizes_xm (fx := fz) SEGS B ARcfx (SIGMA AS___asan_set_shadow_f5) 245.
(* THE TWO cf_head FACTS (the cut's texts take them from the walk). prh_head_wide (8 <= cf_head): tpj_free_specX's
   premise; owner a Theorem Labs lane's preset_head_wide (lib/A/CfParamsPreset.v). prh_head16 (cf_head = PresetReqAt.HEAD,
   CFHEAD-16): the guard of the free cut's cnb_fo (the trees' free order against pj_frees); owner the instance,
   reflexivity at CfParams_preset. *)
Hypothesis HWIDE : PRH_Base.prh_head_wide.
Hypothesis HEAD16 : PRH_Base.prh_head16.
(* the image binding of B at the listing (YC1fP.v PALibCore: errno, the free wrapper's pc, the .got objects) *)
Hypothesis PAL : PALibCore B.
(* the walk's image facts (the contract's record, closed by computation at the instance once PAImg_prog.v builds) *)
Hypothesis IMG : cnb_img B.
(* no program static is an errno byte: the contract's cnbi_pst_errno (Cno102B_Base.v 20c89a1d4da2 :183). The runtime
   free's keep (YCbq.v acall_kept's image clause, what YGcallMxmn.v aj_free_at_x_ct_m_rh gives) keeps an image byte that
   is no owned static AND no errno byte, and api_env puts errno in the image, so this is what carries the ledger's
   static cells (g_most and g_own_ran_out among them) across CB8's three __wrap_free calls. *)
Let CN_PST_ERRNO : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4) := cnbi_pst_errno B IMG.

Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs SEGS B.

(* ---- arodata_okP across the WHOLE segment, through the entry journal (at wle': every journal of this walk is after a
   free): the journal keeps every image byte that is no owned static, no errno byte and no prh_pst cell, and a
   read-only byte is no prh_pst cell by the contract's cnbi_pst_rw. This is what re-establishes cnb_base's last
   conjunct at the exit (CawA102's WA4 finding). ---- *)
Lemma cnob_arodata_J : forall STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k,
  AJ' STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W0) mem0) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
Proof.
intros STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k HJ HRO a Hro Hown Herr.
pose proof (ajxR_img HJ) as Himg.
assert (Hin : in_img SEGS a).
{ destruct Hro as [(sg & Hsg & _ & Hlo & Hhi) | Hrel];
  [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hrel)]. }
rewrite (Himg a Hin Hown Herr (fun HP => cnbi_pst_rw B IMG a HP Hro)
  (fp_spares_closed [] a sink_closed_nil)).
exact (HRO a Hro Hown Herr).
Qed.

(* ---- THE pj_free CALL STEP (offsets 744 / 752 / 760): at pj_free's entry, ra = the return site, a0 = v, the
   journal at (STK, sp0) and sp = s1 = sp0 + o, at wle'. The callee's text by aj_call_xWR at wle' segs RZ_cf, e1 = 0
   (the struct is in the caller's class-3 FAKE frame, not in its real-stack window, so the text's window argument is
   the empty one), the `v <> 0 /\ pj_foR` arm; the callee's fpre at the cut's float state fz (its frm_zero conjunct,
   FRM0-ENTRY, from the cut's cnb_base); the hull budget for v <> 0 (the caller's); P across the call by the
   m-form keep of fpostWmR. The post's Q is the kit's tpfP_Q (PRH_FnPj.v, tpj_free_specX's Q by name) at
   fail := SIZE_MAXZ. ---- *)
Lemma cnob_pjfree_call : forall (fz : YK11.FPState) STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W regs mem md k
    v Dt F Lam peak cnt ran most ownl ch raw
    (P : (word -> option byte) -> Prop),
  srr_inv_call SEGS P ->
  AJ' STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  (spZ regs - sp0) mod 16 = 0 -> spZ regs <= sp0 -> STK_pj_free DOC_D + (sp0 - spZ regs) <= STKa ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  getr regs 10 = w64 v ->
  achain ly (aview SEGS (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  spZ regs + 64 <= ly_stk_hi ly -> frm_zero (@YK11.fp_csr fz) ->
  prh_univ_closure B CTX0 -> room_live_cf S ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV -> PresetHullBudget.hull_budget S [] ->
  v <> 0 -> v < YM05.alloc_ceiling -> pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D v Dt F ->
  prhPj_slot B (STK_pj_free DOC_D) 0 ly S Lam W regs mem v ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most ownl ->
  fp_sub_x B STKa sp0 [] ((v, v + 56) :: ablocks_fp (prhPj_hbl Dt)) ly0 S0 own ly S ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 (SIGMA AS_pj_free)) mem (seg_rom SEGS)) md)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fz regs2 raw mem2 (seg_rom SEGS)) md2 /\
       AJ' STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJ' (STK_pj_free DOC_D + 0) (spZ regs + 0)
         ((v, v + 56) :: ablocks_fp (prhPj_hbl Dt)) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       aregs_preserved regs regs2 /\
       tpfP_Q B most ownl ly S Hp v Dt F Lam peak cnt SIZE_MAXZ ran ly2 S2 Hp2 W2 regs2 mem2 md2 /\
       P mem2).
Proof.
intros fz STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W regs mem md k v Dt F Lam peak cnt ran most ownl
  ch raw P PCALL HJ Hal Hle Hbud Hgp Htp Hra Hraw Hra4 HraC Ha0 Hch HROD Hshi Hfrm
  HUNIV HRL HC24 HHB Hv0 HvC HFO HSL HLED HFS HPM.
assert (HSTK0 : 0 <= STK_pj_free DOC_D) by (vm_compute; discriminate).
assert (Ev : (v =? 0) = false) by (apply Z.eqb_neq; exact Hv0).
eapply SRr'_mono.
{ eapply (aj_call_xWR (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) WLE' (wle'_refl SEGS _)
    (wle'_trans SEGS _) W regs mem (SIGMA AS_pj_free)
    STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp md k (STK_pj_free DOC_D) 0
    ((v, v + 56) :: ablocks_fp (prhPj_hbl Dt)) (spZ regs - sp0) raw ch
    (fQmn mem (tpfP_Q B most ownl ly S Hp v Dt F Lam peak cnt SIZE_MAXZ ran))).
  - exact HJ.
  - lia.
  - exact Hal.
  - lia.
  - exact HSTK0.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - replace (sp0 + (spZ regs - sp0)) with (spZ regs) by lia. exact Hch.
  - intros HPX HWIN.
    assert (HFP : fpre (fx := fz) B ARcfx (STK_pj_free DOC_D) ly S Hp W regs mem md ch).
    { split; [exact HPX|]. split; [exact HROD|]. split; [exact Hshi|].
      split; [unfold raZ; rewrite Hra; exact HraC | exact Hfrm]. }
    pose proof (HPJF fz most ownl ly S Hp W regs mem md ch 0 v Dt F Lam peak cnt
      SIZE_MAXZ ran HFP HUNIV HRL (fun _ => HC24) (fun _ => HHB) Ha0 HWIN
      (or_intror (conj Hv0 (conj HvC (conj HFO HSL)))) HWIDE HLED)
      as HT.
    rewrite Ev in HT. exact HT.
  - exact HFS. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HP2 & HK & HMN).
exists ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [reflexivity|]. split; [exact HJ2|].
split; [replace (sp0 + (spZ regs - sp0) + 0) with (spZ regs + 0) in HJ1 by lia; exact HJ1|].
split; [exact HK|].
destruct HMN as (HKK & HMN2).
split; [exact HKK|].
exact (PCALL _ _ HMN2 HPM).
Qed.

(* one run event at a position: the model's event there *)
Lemma cnob_run_at1 : forall sm x os i e, prh_run_at sm x os i [e] -> nth_error (PresetRun.hruns sm x os) i = Some e.
Proof.
intros sm x os i e H. unfold prh_run_at in H. cbn [length] in H. revert H.
generalize (PresetRun.hruns sm x os) as l. induction i as [|i IH]; intros l H.
- destruct l as [|a l]; cbn in H |- *; [discriminate H|]. injection H as ->. reflexivity.
- destruct l as [|a l]; cbn in H |- *; [discriminate H | exact (IH l H)].
Qed.

(* ---- the call memory's RELRO fact (QMm_cf's last conjunct) at a cut of this walk: the cut's journal from the entry
   keeps it from the entry fpre's arodata_okP (YGcallcf.arodata_ok_cf_of_journal_P), over the contract record's RELRO
   rows (the range in one segment, errno apart from it, its top inside the address space, the range of fpre's
   arodata_okP) and its non-writable read ranges (cnbi_ro_reads_nw); the program statics are no read-only byte
   (cnbi_pst_rw: neither a RELRO byte nor a byte of a read range's non-writable segment) and the entry journal's
   footprint is empty ---- *)
Lemma cnob_aro_cf : forall D wk ly S Hp W mem md k,
  cnb_pre (fx := fx) B ARcfx CTX0 D -> cnb_JR B ARcfx WLE' D wk ly S Hp W mem md k -> arodata_ok_cf SEGS B mem.
Proof.
intros D wk ly S Hp W mem md k HPRE (WS & HJ & _).
pose proof HPRE as (HFPRE & _). pose proof HFPRE as (_ & HROD0 & _).
destruct (cnbi_relro_eq B IMG) as (Elo & Ehi).
eapply (arodata_ok_cf_of_journal_P (SK := SK) SEGS B prh_pst ARcfx WLE');
  [exact HJ | exact (cnbi_relro_seg B IMG) | exact (cnbi_errno_relro B IMG) | exact (cnbi_relro_top B IMG)
  | exact (cnbi_ro_reads_nw B IMG) | | |].
- intros a Ha HP. apply (cnbi_pst_rw B IMG a HP). destruct Ha as [Ha | Ha].
  + right. rewrite <- Elo, <- Ehi. exact Ha.
  + left. pose proof (cnbi_ro_reads_nw B IMG) as RONW. unfold YGcfAroBridge.ro_reads_nw_t in RONW.
    rewrite Forall_forall in RONW. apply Exists_exists in Ha. destruct Ha as (rr & Hrr & Hin). unfold in_zr in Hin.
    destruct (RONW rr Hrr) as (_ & sg & Hsg & Hnw & Hlo & Hhi).
    exists sg. split; [exact Hsg|]. split; [exact Hnw | lia].
- exact sink_closed_nil.
- rewrite Elo, Ehi. exact HROD0.
Qed.

(* ---- THE __wrap_free CALL STEP (offsets 768 / 776 / 784): at the free wrapper's entry, a0 = c, ra = raw, the
   journal at wle'. YGcallMxmnKeep.v's aj_free_at_x_ct_m_rh_keep for a live copy (the cf free rule under the
   re-hide: the primed row with the keep, the tail call on call_trace), the kit's aj_free_null_at_cf_rh_keep for a
   NULL copy (free(NULL) at wle', its PNull-only text from the same row). The call trace is a
   FIXED one (In .. (u_fix (as_universe B)), cnob_trace_in), so it is admitted at every state (YCbqG.admits_ct_fix),
   and it leaves the free rule's budget [] ++ [trace] (YCbqG.ajournal_xw_fix1R): the journal stays at the empty
   budget; free(NULL) keeps the depot (YGcfAmx2.ipost_free_null_depot). QMm_cf comes from the room
   (YGcfRoomLive.room_live_room + QMm_cf_of_room), the caller's hull admission cf_hull_ok and the call memory's
   RELRO fact; the room after from
   RL_free_step at the class-24 bound (CfRoomLivePreset.preset_rl_b24_ok), both hull meters kept
   (YGcfSecsStep.secs_free_step), the run position after from the kit's PresetRoomPosKeep.room_pos_keep_free (a live
   copy, at its HFr event) / room_pos_keep_free_null (a NULL copy, no event), and P across the call from the keep
   (the keep rule's last conjunct). ---- *)
Lemma cnob_wfree_call : forall (fz : YK11.FPState) STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W regs mem md k c n raw ch
    (P : (word -> option byte) -> Prop),
  srr_inv_call SEGS P ->
  AJ' STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  (spZ regs - sp0) mod 16 = 0 -> spZ regs <= sp0 -> ASTACK + (sp0 - spZ regs) <= STKa ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 1 = raw -> YK0s.ret_ok raw ->
  getr regs 10 = w64 c ->
  (c = 0 /\ ~ In 0 Hp \/ c <> 0 /\ In (c, n) (ablocks B ly S) /\ ~ In (c, n) (ablocks B ly0 S0) /\ ~ In c Hp) ->
  room_live_cf S -> YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  cf_hull_ok S -> arodata_ok_cf SEGS B mem ->
  chain_pre ly (aview SEGS (w_H W) mem) regs ch ->
  In (call_trace ly (pc_free_ra0 (as_code B)) regs ch) (as_universe B) ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 (SIGMA AS___wrap_free)) mem (seg_rom SEGS)) md)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fz regs2 raw mem2 (seg_rom SEGS)) md2 /\
       AJ' STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp W2 mem2 md2 (k + (st_nev S2 - st_nev S)) /\
       aregs_preserved regs regs2 /\
       Permutation (ablocks B ly S) (cnob_cblk n c ++ ablocks B ly2 S2) /\
       frames S2 = frames S /\ YGcfSecsStep.secs_same S S2 /\
       acall_kept_x SEGS B ly S W mem W2 mem2 (spZ regs - ASTACK) (spZ regs)
         (fun a => c <> 0 /\ c <= a < c + req_size n) /\
       room_live_cf S2 /\ YGcfRoomLive.ccnt24 S2 <= YGcfRoomLive.ccnt24 S /\
       (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          prh_run_at sm x os i (if c =? 0 then [] else [PresetReqAt.HFr n]) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os
            (i + length (if (c =? 0)%Z then [] else [PresetReqAt.HFr n]))%nat H0 hist' S2) /\
       P mem2).
Proof.
intros fz STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W regs mem md k c n raw ch P PCALL
  HJ Hal Hle Hbud Hgp Htp Hra Hraw Ha0 Hc HRL HC24 HOK HARO Hch Htr HPM.
assert (Penv : api_env SEGS B) by (destruct PAL; assumption).
assert (Pfree : SIGMA AS___wrap_free = pc_wrap_free (as_code B)) by (destruct PAL; assumption).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_qt HJ) as HQT.
pose proof (YCbqG.admits_ct_fix (as_universe B) ly (pc_free_ra0 (as_code B)) regs ch S Htr) as Hadm.
(* QMm_cf at the call: the room, the hull admission and the RELRO fact of the call memory *)
assert (HQM : QMm_cf SEGS B S mem)
  by exact (QMm_cf_of_room SEGS B ly S Hp W mem md (proj1 HAR) HQT (YGcfRoomLive.room_live_room S HRL) HOK HARO).
pose proof (universe_ok_of_ARcf SEGS B ly S Hp W mem md (proj1 HAR)) as HUok.
pose proof (alloc_model_laws_x_cf B HUok) as AMX.
rewrite Pfree.
destruct Hc as [(Hc0 & H0hp) | (Hc0 & Hin & Hnew & Hnhp)].
- (* the NULL copy: the kit's cf rule at wle' over the keep row, whose last conjunct is the keep; the block list is
     unchanged and the call writes no client byte *)
  subst c.
  eapply SRr'_mono.
  { eapply (aj_free_null_at_cf_rh_keep (fx := fz) (SK := SK) SEGS B prh_pst LAWS (@pa_segs_low _ _ PA) Penv OWNLOW WFL
      AMX (AFREE fz)
      W regs mem STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp md k (spZ regs - sp0) raw ch);
      [exact HJ | exact Ha0 | exact H0hp | lia | exact Hal | lia | lia | exact Hgp | exact Htp | exact Hra | exact Hraw
      | exact HQM | exact Hch | exact Hadm |].
    intros trc0 S20 Hpth.
    exact (YGcfRoomStep.ipost_apath _ _ _ _ (YGcfAmx2.ipost_free_null_depot _ S) Hpth). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Eab & Hfr & HPREc &
    (trc & Hpath & Hgf & _) & HK & Hmn).
  assert (Hperm : Permutation (ablocks B ly S) (cnob_cblk n 0 ++ ablocks B ly2 S2))
    by (unfold cnob_cblk; cbn; rewrite Eab; apply Permutation_refl).
  exists ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
  split; [exact Hperm|].
  split; [exact Hfr|]. split; [exact (YGcfSecsStep.secs_free_step _ _ _ _ _ Hpath)|].
  split.
  { replace (spZ regs - ASTACK) with (sp0 + (spZ regs - sp0) - ASTACK) by lia.
    replace (spZ regs) with (sp0 + (spZ regs - sp0)) at 2 by lia.
    eapply acall_kept_x_mono_E; [exact HK|]. intros a []. }
  split.
  { change S2 with (snd (tt, S2)).
    eapply (YGcfRoomLive.RL_free_step SEGS B); [eapply acall_pre_x_xs_cf; exact HPREc |
      exact (CfRoomLivePreset.preset_rl_b24_ok S HC24) | exact HRL | exact Hpath]. }
  split; [exact (cnob_ccnt24_le B ly S ly2 S2 _ Hperm)|].
  split.
  { intros sm x os i H0 hist Hpos _. exists hist.
    assert (E0 : (i + length (if (0 =? 0)%Z then @nil PresetReqAt.hev else [PresetReqAt.HFr n]) = i)%nat)
      by (cbn; lia).
    rewrite E0.
    assert (HPcf : acall_pre_cf SEGS B ly S Hp W regs mem md ch) by (eapply acall_pre_x_xs_cf; exact HPREc).
    exact (PresetRoomPosKeep.room_pos_keep_free_null SEGS B ly S Hp W regs mem md ch sm x os i H0 hist _ trc S2
      HPcf Htr Hpath Hpos). }
  exact (PCALL _ _ Hmn HPM).
- (* a live copy: the cf free rule under the re-hide over the keep row, whose last conjunct is the keep *)
  eapply SRr'_mono.
  { eapply (YGcallMxmnKeep.aj_free_at_x_ct_m_rh_keep (fx := fz) (SK := SK) SEGS B prh_pst LAWS (@pa_segs_low _ _ PA)
      Penv OWNLOW WFL AMX (AFREE fz)
      W regs mem STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp md k c n (spZ regs - sp0) raw ch);
      [exact HJ | exact Hin | exact Hnhp | exact Ha0 | lia | exact Hal | lia | lia | exact Hgp | exact Htp | exact Hra
      | exact Hraw | exact HQM | exact Hch | exact Hadm |].
    intros H0 i Hi. exfalso. exact (Hnew H0). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & Hfr & HPREc & _ &
    (q & trc & Hq & Hqin & Hpath & Hgf & Hleaf) & HK & Hmn).
  assert (Hperm : Permutation (ablocks B ly S) (cnob_cblk n c ++ ablocks B ly2 S2)).
  { unfold cnob_cblk. rewrite (proj2 (Z.eqb_neq c 0) Hc0). cbn [app]. rewrite E1, E2.
    symmetry. apply Permutation_middle. }
  exists ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact (ajournal_xw_fix1R Htr HJ2)|]. split; [exact HP2|].
  split; [exact Hperm|].
  split; [exact Hfr|]. split; [exact (YGcfSecsStep.secs_free_step _ _ _ _ _ Hpath)|].
  split.
  { replace (spZ regs - ASTACK) with (sp0 + (spZ regs - sp0) - ASTACK) by lia.
    replace (spZ regs) with (sp0 + (spZ regs - sp0)) at 2 by lia.
    eapply acall_kept_x_mono_E; [exact HK|]. intros a Ha. split; [exact Hc0 | exact Ha]. }
  split.
  { change S2 with (snd (tt, S2)).
    eapply (YGcfRoomLive.RL_free_step SEGS B); [eapply acall_pre_x_xs_cf; exact HPREc |
      exact (CfRoomLivePreset.preset_rl_b24_ok S HC24) | exact HRL | exact Hpath]. }
  split; [exact (cnob_ccnt24_le B ly S ly2 S2 _ Hperm)|].
  split.
  { intros sm x os i H0 hist Hpos Hrun.
    rewrite (proj2 (Z.eqb_neq c 0) Hc0) in Hrun |- *. cbn [length].
    assert (Hqn : q <> PNull) by (intros ->; cbn in Hq; lia).
    assert (HPcf : acall_pre_cf SEGS B ly S Hp W regs mem md ch) by (eapply acall_pre_x_xs_cf; exact HPREc).
    replace (i + 1)%nat with (Datatypes.S i) by lia.
    eexists.
    exact (PresetRoomPosKeep.room_pos_keep_free SEGS B ly S Hp W regs mem md ch sm x os i H0 hist q n _ trc S2
      HPcf Hadm Hqin Hqn Hpath Hpos (cnob_run_at1 _ _ _ _ _ Hrun)). }
  exact (PCALL _ _ Hmn HPM).
Qed.

(* ---- THE SIX RETURN SITES, each a CLOSED top-level lemma (engine trap, lead 14:45Z: never discharge fpre's raZ
   bound with `pa_slot_lt_ceil_b .. ltac:(vm_compute; reflexivity)` inside a big proof - it ran away at 40 min /
   60 GB on the S3 walk; one closed lemma per slot, then `exact` it at the call site) ---- *)
Lemma cnob_ret_ok : forall off, 0 <= off < 2 ^ 40 ->
  match plookup pl_tpi off with Some _ => true | None => false end = true ->
  4096 <= bv_unsigned (Z_to_bv 64 (BASE + off)) /\ bv_unsigned (Z_to_bv 64 (BASE + off)) < YM05.alloc_ceiling.
Proof.
intros off Hoff Hlk.
pose proof (PRW_StepKit.pa_slot_lt_ceil_b off Hoff Hlk) as Hc.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _).
assert (Hsm : bv_unsigned (Z_to_bv 64 (BASE + off)) = BASE + off) by (apply unsigned_lit_small; lia).
rewrite Hsm. split; [|exact Hc].
rewrite (cnbi_base B IMG). unfold B_prog_base. lia.
Qed.
Ltac cnob_ret_tac := unfold cnb_pc; rewrite <- Z.add_assoc; apply cnob_ret_ok;
  [split; [vm_compute; discriminate | vm_compute; reflexivity] | vm_compute; reflexivity].
Lemma cnob_ret_pjf1 : 4096 <= bv_unsigned (Z_to_bv 64 (cnb_pc CNB_PJF1)) /\
  bv_unsigned (Z_to_bv 64 (cnb_pc CNB_PJF1)) < YM05.alloc_ceiling.
Proof. cnob_ret_tac. Qed.
Lemma cnob_ret_pjf2 : 4096 <= bv_unsigned (Z_to_bv 64 (cnb_pc CNB_PJF2)) /\
  bv_unsigned (Z_to_bv 64 (cnb_pc CNB_PJF2)) < YM05.alloc_ceiling.
Proof. cnob_ret_tac. Qed.
Lemma cnob_ret_pjf3 : 4096 <= bv_unsigned (Z_to_bv 64 (cnb_pc CNB_PJF3)) /\
  bv_unsigned (Z_to_bv 64 (cnb_pc CNB_PJF3)) < YM05.alloc_ceiling.
Proof. cnob_ret_tac. Qed.
Lemma cnob_ret_fr1 : 4096 <= bv_unsigned (Z_to_bv 64 (cnb_pc CNB_FR1)) /\
  bv_unsigned (Z_to_bv 64 (cnb_pc CNB_FR1)) < YM05.alloc_ceiling.
Proof. cnob_ret_tac. Qed.
Lemma cnob_ret_fr2 : 4096 <= bv_unsigned (Z_to_bv 64 (cnb_pc CNB_FR2)) /\
  bv_unsigned (Z_to_bv 64 (cnb_pc CNB_FR2)) < YM05.alloc_ceiling.
Proof. cnob_ret_tac. Qed.
Lemma cnob_ret_fr3 : 4096 <= bv_unsigned (Z_to_bv 64 (cnb_pc CNB_FR3)) /\
  bv_unsigned (Z_to_bv 64 (cnb_pc CNB_FR3)) < YM05.alloc_ceiling.
Proof. cnob_ret_tac. Qed.

(* ---- the symbolic entry state of one stretch, at the float state the cut carries ---- *)
Lemma cnob_entry : forall (fz : YK11.FPState) off rgs (W : world SEGS) regs mem,
  regions_wf rgs = true ->
  Forall (region_ok SEGS (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) rgs ->
  pairwise_disjoint (Eimg (Ereg regs [])) rgs ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS (CNB_OFF + off) sr_atoms rgs None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fz regs (Z_to_bv 64 (BASE + (CNB_OFF + off))) mem (YK11.seg_rom SEGS))).
Proof.
intros fz off rgs W regs mem Hwf Hok Hdisj.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact Hwf.
- exact Hok.
- exact Hdisj.
- unfold facts_ok; cbn; repeat split; try apply Forall_nil; try exact I.
Qed.
Lemma cnob_sh_nil : forall (W : world SEGS) regs mem,
  sh_ok SEGS (SLit SHADOW_OFF) [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof. intros. apply Forall_nil. Qed.
(* a stretch that writes nothing leaves the memory alone *)
Lemma cnob_frame_id : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) -> m' = m.
Proof.
intros E rs m m' HF Hro. apply functional_extensionality. intros y. apply HF.
intros (r & Hin & Ha). pose proof (Hro r Hin). lia.
Qed.
(* a register the stretch set from another register (`mv`), or left alone *)
Lemma cnob_ew_reg : forall regs n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat ->
  ew (Eimg (Ereg regs [])) n = getr regs rr.
Proof.
intros regs n rr Hn H32. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] n rr Hn).
Qed.
Lemma cnob_reg_of : forall (fz : YK11.FPState) (H : word -> bool) ss ms regs (rd rs : bv 5) n,
  st_ok_pi (fx := fz) SEGS VAL (Eimg (Ereg regs [])) ss (restrict H ms) ->
  sr_get (ss_regs ss) rd = SOff n 0 -> Z.of_nat n = bv_unsigned rs -> (n < 32)%nat ->
  getr (ms_regs ms) rd = getr regs rs.
Proof.
intros fz H ss ms regs rd rs n HS Hr Hn H32.
rewrite (st_ok_pi_restrict_reg (fx := fz) H _ ss ms rd HS), Hr.
rewrite (denot_lit_U _ (SOff n 0)), U_SOff, Z.add_0_r.
rewrite (cnob_ew_reg regs n rs Hn H32). unfold zcanon, M64.
rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 (getr regs rs)) as Hb;
  unfold bv_modulus in Hb; cbn in Hb; lia).
apply Z_to_bv_bv_unsigned.
Qed.

(* ==== BLOCK-LIST FACTS the free steps need ==== *)
(* a live block is not empty (the block law of YCbqG.v 219748197d6b, ARx_blocks_law: an empty one holds no hidden head) *)
Lemma cnob_blk_pos : forall ly S Hp W mem md p n, ARcfx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  0 < req_size n.
Proof.
intros ly S Hp W mem md p n HAR Hin.
destruct (Z_lt_le_dec 0 (req_size n)) as [Q|Q]; [exact Q|].
destruct (alx_shadow SEGS B ARcfx LAWS ly S Hp W mem md p n HAR Hin ltac:(intros h _ Hh; lia)) as [(_ & Q0 & _) _].
exfalso. revert Q Q0. unfold req_size. destruct (Z.eqb_spec n 0); cbv beta iota; intros; lia.
Qed.
(* the live blocks are pairwise disjoint and none is empty, so the list has no duplicate *)
Lemma cnob_ablocks_nodup : forall ly S Hp W mem md, ARcfx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
assert (Hpos : forall b, In b (ablocks B ly S) -> 0 < req_size (snd b)).
{ intros [p n] Hb. exact (cnob_blk_pos ly S Hp W mem md p n HAR Hb). }
destruct (ablocks B ly S) as [|b0 l0] eqn:El; [apply List.NoDup_nil|].
pose proof (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md (fst b0) (snd b0) HAR
  ltac:(rewrite El; left; destruct b0; reflexivity)) as (_ & _ & _ & _ & _ & Hsep).
rewrite El in Hsep. clear El.
revert Hsep Hpos. generalize (b0 :: l0) as l. clear b0 l0.
intros l. induction l as [|x l IH]; intros Hsep Hpos; [apply List.NoDup_nil|].
cbn [map pairwise] in Hsep. destruct Hsep as (Hx & Hl).
apply List.NoDup_cons.
- intros Hin. rewrite Forall_forall in Hx.
  pose proof (Hx (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) l x Hin)) as Hd.
  pose proof (Hpos x (or_introl eq_refl)). unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- apply IH; [exact Hl | intros b Hb; apply Hpos; right; exact Hb].
Qed.
Lemma cnob_nodup_app_disj : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 x Hnd Hin; [destruct Hin|].
inversion Hnd as [|? ? Hny Hnd']; subst. destruct Hin as [<-|Hin].
- intros H2. apply Hny. apply in_or_app. right. exact H2.
- exact (IH l2 x Hnd' Hin).
Qed.
(* no harness base is 0: each is the base of a live block (prh_hblock), and a live block is at 4096 or above *)
Lemma cnob_hp_no0 : forall ly S Hp W mem md Lam peak cnt fail ran most own, ARcfx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> ~ In 0 Hp.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own HAR HLED Hin.
assert (HH : Permutation Hp (map (fun ak => fst ak - cf_head) Lam)) by (eapply prh_ledger_heads; exact HLED).
assert (HB : Forall (fun ak => prh_hblock B ly S Hp W mem (fst ak) (snd ak)) Lam)
  by (eapply prh_ledger_blocks; exact HLED).
apply (Permutation_in _ HH) in Hin. apply in_map_iff in Hin as ([a k] & Ea & Hak). cbn [fst snd] in Ea.
rewrite Forall_forall in HB. destruct (HB (a, k) Hak) as (_ & Hblk & _). cbn [fst snd] in Hblk.
pose proof (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & H4096 & _). lia.
Qed.

(* ---- a struct of the fake frame is 8-aligned and writable (the pj_rwR conjunct of prhPj_slot, from the frame law
   alone): what pv_fd_zeroR asks of a zero struct ---- *)
Lemma cnob_rw : forall D ly S Hp W mem md off,
  ARcfx ly S Hp W mem md -> In (CNB_CID, bi_fpos D) (frames S) ->
  frame_addr ly CNB_CID (bi_fpos D) = cnb_F D ->
  0 <= off -> off + 56 <= fs_frame_bytes CNB_CID -> off mod 8 = 0 ->
  pj_rwR SEGS (rdW W mem) (cnb_F D + off).
Proof.
intros D ly S Hp W mem md off HAR Hin HF Hoff0 Hoff56 Hoff8.
pose proof (alx_frames SEGS B ARcfx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin) as (Hal32 & _ & Hby & _).
rewrite HF in Hal32, Hby.
split.
- assert (HF8 : cnb_F D mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 32);
    [exists 4; reflexivity | apply Z.mod_divide; [lia | exact Hal32]]. }
  rewrite Z.add_mod by lia. rewrite HF8, Hoff8. reflexivity.
- intros x Hx. apply apresent_writable. exact (proj1 (Hby x ltac:(lia))).
Qed.

(* ---- THE STRUCT SLOT: pj_free's premise prhPj_slot (PRH_FnPj.v 5aca5cbe2cfb) for a struct at offset off
   of the walk's class-3 FAKE frame. Everything but the two shadow conjuncts comes from the frame laws of ARx
   (YCbqG.v 219748197d6b ARx_frames_law: the frame is 32-aligned, in_app, every byte present and unowned; and
   ARx_sep_law: 4096 <= F and F + fs_frame_bytes <= YM05.alloc_ceiling), so the struct is below the allocator ceiling
   while the real stack is above it (astk_ok) - which is why no struct byte lies in the caller's stack window. The
   two shadow conjuncts are the cut's cnb_open (CB3's unpoison). ---- *)
Lemma cnob_slot : forall D ly S Hp W regs mem md Lam off,
  ARcfx ly S Hp W mem md ->
  In (CNB_CID, bi_fpos D) (frames S) ->
  frame_addr ly CNB_CID (bi_fpos D) = cnb_F D ->
  0 <= off -> off + 56 <= fs_frame_bytes CNB_CID -> off mod 8 = 0 ->
  spZ regs = cnb_S1 D -> astk_ok STK ly (cnb_sp0 D) -> cnb_sp0 D - 192 < cnb_S1 D ->
  cnb_open W mem (cnb_F D + off) ->
  prhPj_slot B (STK_pj_free DOC_D) 0 ly S Lam W regs mem (cnb_F D + off).
Proof.
intros D ly S Hp W regs mem md Lam off HAR Hin HF Hoff0 Hoff56 Hoff8 Hsp HSTK HS1 (HRA & HSH).
pose proof (alx_frames SEGS B ARcfx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin) as (Hal32 & Happ & Hby & _).
pose proof (alx_sep SEGS B ARcfx LAWS ly S Hp W mem md HAR) as (_ & Hsepf).
rewrite HF in Hal32, Happ, Hby.
rewrite Forall_forall in Hsepf.
destruct (Hsepf (CNB_CID, bi_fpos D) Hin) as (Hf4096 & Hfceil). cbn [fst snd] in Hf4096, Hfceil.
rewrite HF in Hf4096, Hfceil.
destruct Happ as (H4096 & Hband).
destruct HSTK as (Hsp16 & HSTK0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKs : STK_pj_free DOC_D + 192 <= STK_check_no_overread) by (vm_compute; discriminate).
assert (HFB : fs_frame_bytes CNB_CID = 512) by (vm_compute; reflexivity).
rewrite HFB in Hoff56, Hfceil, Hband, Hby.
(* every byte of the struct is a byte of the frame *)
assert (Hin56 : forall a, cnb_F D + off <= a < cnb_F D + off + 56 -> cnb_F D <= a < cnb_F D + 512) by lia.
split; [lia|].
split.
{ (* prhReader_at: the struct is inside a live frame *)
  right. right. left. exists CNB_CID, (bi_fpos D).
  split; [exact Hin|]. rewrite HF, HFB. lia. }
split.
{ (* pj_rwR: 8-aligned and writable *)
  split.
  - assert (HF8 : cnb_F D mod 8 = 0).
    { apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 32);
      [exists 4; reflexivity | apply Z.mod_divide; [lia | exact Hal32]]. }
    rewrite Z.add_mod by lia. rewrite HF8, Hoff8. reflexivity.
  - intros x Hx. apply apresent_writable. exact (proj1 (Hby x (Hin56 x Hx))). }
split.
{ (* amem_range: the frame is in the app band, which is below the shadow in low memory and below the allocator
     ceiling in high memory *)
  unfold amem_range. unfold kLowShadowBeg in Hband. unfold ASAN_CEIL in Hband.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd.
  destruct Hband as [Hlow | (Hhb & Hhi2)]; [left; lia | right; split; lia]. }
split; [|split; [exact HRA | exact HSH]].
intros a Ha. split.
- exact (proj2 (Hby a (Hin56 a Ha))).
- rewrite Hsp. lia.
Qed.

(* ---- THE CHAIN AT A CALL of this segment: the walk's own frame is a FRAME-POINTER frame (s0 = the entry sp, the
   saved ra and s0 at s0 - 8 / s0 - 16, cnb_saved's first two words), so the chain at the call is the entry's chain
   with this frame pushed (YCbq.v achain_push). When the entry sp is at the top of the stack the chain is empty and
   achain's own first disjunct gives it. The cut's journal is at wle' (every call of this walk is after a free). ---- *)
Lemma cnob_chain : forall D wk ly S Hp W mem md k,
  cnb_JR B ARcfx WLE' D wk ly S Hp W mem md k -> cnb_saved D W mem ->
  afn_pre_x SEGS B ARcfx STK (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_regs D) (bi_mem D) (bi_md D) (bi_ch D) ->
  cnb_S1 D <= cnb_sp0 D - 160 ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) (cnb_S1 D) (cnb_sp0 D) ch1 /\
    (ch1 = [] \/ ch1 = (cnb_sp0 D, raZ (bi_regs D), s0Z (bi_regs D)) :: bi_ch D).
Proof.
intros D wk ly S Hp W mem md k (WS & HJ & _) HSAVED HAFN HS1.
pose proof (ajxR_ly HJ) as Hlyle. pose proof (ajxR_hi HJ) as Hkeep. pose proof (ajxR_stk HJ) as HSTK.
pose proof HAFN as (HAR0 & Hra0 & Hra4 & _ & _ & HSTK0 & _ & HCH0 & _).
pose proof HSTK as (Hsp16 & HSTKge & Hceil & Hlo & Hhi & H47 & _ & Htop & Htop2).
pose proof HSTK0 as (_ & _ & Hceil0 & Hlo0 & Hhi0 & H470 & _ & Htop0 & Htop20).
pose proof Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HSAVED as HSV. unfold cnb_saved in HSV.
pose proof (Forall_inv HSV) as Hra. cbn [fst snd] in Hra.
pose proof (Forall_inv (Forall_inv_tail HSV)) as Hs0. cbn [fst snd] in Hs0.
assert (Hsp8 : cnb_sp0 D mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16); [exists 2; reflexivity|].
  apply Z.mod_divide; [lia | exact Hsp16]. }
destruct (Z_lt_le_dec (cnb_sp0 D) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((cnb_sp0 D, raZ (bi_regs D), s0Z (bi_regs D)) :: bi_ch D). split; [|right; reflexivity].
  eapply (achain_push ly (aview SEGS (w_H (bi_W D)) (bi_mem D)) (aview SEGS (w_H W) mem)).
  + eapply achain_ly_top; [exact Etop | exact HCH0].
  + lia.
  + intros a Ha. apply Hkeep; lia.
  + replace (cnb_sp0 D - 8) with (cnb_sp0 D - 160 + 152) by lia. exact Hra.
  + replace (cnb_sp0 D - 16) with (cnb_sp0 D - 160 + 144) by lia. exact Hs0.
  + exact Hra4.
  + lia.
  + exact Hsp8.
  + exact Hlt.
  + lia.
- exists []. split; [|left; reflexivity]. left. split; [right; left; lia | reflexivity].
Qed.

(* PRW_StepKit's closure (YF0v.v) turned zify's euclidean-division flag off; nothing above needs it, the shadow
   arithmetic from here on does (lia over `/ 8`), so it is reset here, once (lead: only where YF0v is new to the
   closure and lia breaks on division) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- fp_sub_x for a pj_free call: the struct is a byte of the walk's OWN class-3 frame, and each tree block is
   live now and not at the entry (the invariant's ablocks Permutation and its freshness clause), i.e. in_tmp_block ---- *)
Lemma cnob_fp_sub : forall D ly S X L off Dt,
  Permutation (ablocks B ly S) (X ++ ck_hblks L ++ ablocks B (bi_ly D) (bi_S D)) ->
  (forall a kk, In (a, kk) L -> ~ In (a - cf_head, kk + cf_head) (ablocks B (bi_ly D) (bi_S D))) ->
  frame_addr ly CNB_CID (bi_fpos D) = cnb_F D ->
  0 <= off -> off + 56 <= fs_frame_bytes CNB_CID ->
  (forall a kk, In (a, kk) Dt -> In (a, kk) L) ->
  fp_sub_x B STK (cnb_sp0 D) [] ((cnb_F D + off, cnb_F D + off + 56) :: ablocks_fp (prhPj_hbl Dt))
    (bi_ly D) (bi_S D) [(CNB_CID, bi_fpos D)] ly S.
Proof.
intros D ly S X L off Dt HpermB Hfresh HF Hoff0 Hoff56 Hsub a Ha.
rewrite inFP_cons in Ha. destruct Ha as [Hstruct | Hbl].
- right. right. left. exists (CNB_CID, bi_fpos D). split; [left; reflexivity|].
  unfold frame_rng, in_zr. cbn [fst snd]. rewrite HF. cbn in Hstruct. lia.
- right. left.
  assert (Hgen : forall L', (forall a' k', In (a', k') L' -> In (a', k') L) ->
     inFP (ablocks_fp (prhPj_hbl L')) a -> in_tmp_block (ablocks B (bi_ly D) (bi_S D)) (ablocks B ly S) a).
  { intros L'. induction L' as [|[ai ki] L' IH]; intros Hs Hin.
    - exfalso. exact (inFP_nil a Hin).
    - cbn [prhPj_hbl ablocks_fp map] in Hin. rewrite inFP_cons in Hin. cbn [fst snd] in Hin.
      destruct Hin as [Hh | Ht].
      + exists (ai - cf_head), (ki + cf_head).
        assert (Hin : In (ai - cf_head, ki + cf_head) (ck_hblks L)).
        { unfold ck_hblks. exact (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) _ (ai, ki)
            (Hs ai ki (or_introl eq_refl))). }
        split.
        { apply (Permutation_in _ (Permutation_sym HpermB)). apply in_or_app. right.
          apply in_or_app. left. exact Hin. }
        split; [exact (Hfresh ai ki (Hs ai ki (or_introl eq_refl))) | lia].
      + apply IH; [intros a' k' H'; exact (Hs a' k' (or_intror H')) | exact Ht]. }
  exact (Hgen Dt Hsub Hbl).
Qed.

(* ---- a struct stays OPEN when the shadow of the walk's frame is kept: both predicates read only shadow bytes of the
   struct, and for a struct at a multiple of 32 from 32 up to 400 in a 32-aligned 512-byte frame those are inside
   [shadow_addr F, shadow_addr F + 64) ---- *)
Lemma cnob_open_keep : forall F off (rd rd' : reader),
  F mod 32 = 0 -> 32 <= off -> off + 112 <= 512 -> off mod 32 = 0 ->
  (forall a, shadow_addr F <= a < shadow_addr F + 64 -> rd' a = rd a) ->
  range_addressable rd SHADOW_OFF (F + off) 56 /\ shadow_hull_vis rd (F + off) 56 ->
  range_addressable rd' SHADOW_OFF (F + off) 56 /\ shadow_hull_vis rd' (F + off) 56.
Proof.
intros F off rd rd' HF32 Hoff0 Hoff1 Hoff32 Hk (HRA & HSH).
apply Z.mod_divide in HF32 as [kf EF]; [|lia]. apply Z.mod_divide in Hoff32 as [jo Eo]; [|lia]. subst F off.
assert (EF8 : kf * 32 / 8 = 4 * kf) by (replace (kf * 32) with ((4 * kf) * 8) by ring; apply Z.div_mul; lia).
unfold shadow_addr in Hk |- *. rewrite EF8 in Hk. unfold SHADOW_OFF in *.
split.
- intros x Hx. destruct (HRA x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  unfold shadow_of_addr in Hs |- *. rewrite Hk; [exact Hs|].
  assert (Hq : 4 * kf + 4 * jo <= x / 8 <= 4 * kf + 4 * jo + 6).
  { split.
    - apply Z.div_le_lower_bound; [lia|]. lia.
    - assert (x / 8 < 4 * kf + 4 * jo + 7) by (apply Z.div_lt_upper_bound; [lia|]; lia). lia. }
  lia.
- intros sv Hs. rewrite Hk; [exact (HSH sv Hs)|].
  assert (E1 : (kf * 32 + jo * 32) / 8 = 4 * kf + 4 * jo)
    by (replace (kf * 32 + jo * 32) with ((4 * kf + 4 * jo) * 8) by ring; apply Z.div_mul; lia).
  assert (E2 : (kf * 32 + jo * 32 + 56 - 1) / 8 = 4 * kf + 4 * jo + 6)
    by (replace (kf * 32 + jo * 32 + 56 - 1) with ((4 * kf + 4 * jo + 6) * 8 + 7) by ring;
        rewrite Z.div_add_l by lia; change (7 / 8) with 0; ring).
  unfold shadow_addr, SHADOW_OFF in Hs. rewrite E1, E2 in Hs.
  assert (Hj : 1 <= jo <= 12) by lia.
  pose proof (Z.div_mod (2147450880 + (4 * kf + 4 * jo)) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (2147450880 + (4 * kf + 4 * jo)) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (2147450880 + (4 * kf + 4 * jo + 6)) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (2147450880 + (4 * kf + 4 * jo + 6)) 8 ltac:(lia)) as M2.
  split; lia.
Qed.

(* ---- a word the view keeps is read the same ---- *)
Lemma cnob_rdword_keep : forall (rd rd' : reader) a v,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk Hr. rewrite (rdword_ext rd rd' a Hk). exact Hr. Qed.

(* ---- CNB_END (CB9's start, offset 788): the three structs and the three copies freed. The registers the epilogue
   reads (sp = s1, s0 = the entry sp, s2 = F's shadow, s3 = s11 = F, s10 = -8, s8 = r), the fake-frame pointer at
   s1 + 48, and the state facts cnb_Q asks, at the current state; the ledger states g_most = bi_most D and
   g_own_ran_out = ownl, the value cnb_at_free holds (Batch 2: no separate own / most conjunct). The journal is at
   wle' (restated in place: CB8's frees and the readings before it can re-hide) and at the whole wild budget,
   cnb_base's wk = 6 = prh_wk F_check_no_overread (cnb_wk_total; CB8's six calls are fixed-trace, so they spend
   nothing). When no copy was refused (ownl = 0, the arm the text's position clause covers), the
   readings' grants and the progress fact over the whole of check_no_overread's events (cnb_C3 ++ cnb_revs3 ++
   cnb_fevs = ck_cno_evs, cnb_ck_cno_evs); the grants are existential, so the parameter list is unchanged. When one
   was (ownl <> 0), the refused copy is dead at a consumer run (cnb_cdead, from the free cut), for the post's outcome
   clause. LAST, the hull budget still to pay after the frees (cnb_hF3). ---- *)
Definition cnb_at_end (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z))
  (peak cnt ran r ownl : Z) : Prop :=
  cnb_baseR (fx := fx) B ARcfx WLE' D fxk ly S Hp W regs mem md k 6 /\
  cnb_regsat regs (cnb_core D ++ [(24%bv, r)]) /\
  rdword (aview SEGS (w_H W) mem) (cnb_S1 D + 48) = Some (cnb_F D) /\
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (bi_most D) ownl /\
  Permutation Lam (bi_Lam D) /\ Permutation (ablocks B ly S) (ablocks B (bi_ly D) (bi_S D)) /\
  bi_peak D <= peak /\ bi_cnt D <= cnt <= bi_cnt D + 3 * ck_ncalls (bi_x D) /\
  room_live_cf S /\ bytes_at W mem (bi_data D) (bi_x D) /\
  ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)) /\
  (ownl = 0 -> exists o1 o2 o0, cnb_prog D (cnb_C3 D ++ cnb_revs3 D o1 o2 o0 ++ cnb_fevs D o1 o2 o0) S /\
     ran = cnb_ranz D o1 o2 o0) /\
  (ownl <> 0 -> cnb_cdead D) /\
  PresetHullBudget.hull_budget S (cnb_hF3 (bi_x D)).
Definition cnb_ex_end (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r ownl,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_END) regs mem md /\
  cnb_at_end D fxk ly S Hp W regs mem md k Lam peak cnt ran r ownl.

(* ==== WHAT A pj_free OF ONE STRUCT KEEPS (from the call's inner journal at wle', YCbqG.v ajournal_xbR's frame and block
   clauses): the rest of the walk's frame, the frame's shadow, and every live block that is not one of the freed
   tree's blocks. The shadow arithmetic needs lia over `/ 8`: PRW_StepKit's closure (YF0v.v) turned zify's
   euclidean-division flag off, and nothing earlier in this file needs it, so it is reset here (lead 14:30Z / 15:0xZ:
   only where YF0v is new to the closure and lia breaks on division). ==== *)
Lemma cnob_pairwise_app : forall {X} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y Hp Hx Hy; [destruct Hx|].
cbn [app pairwise] in Hp. destruct Hp as (Hz & Hp). destruct Hx as [<- | Hx].
- rewrite Forall_forall in Hz. apply Hz. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Hp Hx Hy).
Qed.
Lemma cnob_pairwise_two : forall {X} (R : X -> X -> Prop) l x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y Hp Hx Hy Hne; [destruct Hx|].
cbn [pairwise] in Hp. destruct Hp as (Hz & Hp). rewrite Forall_forall in Hz.
destruct Hx as [<- | Hx], Hy as [<- | Hy].
- exfalso. exact (Hne eq_refl).
- left. exact (Hz y Hy).
- right. exact (Hz x Hx).
- exact (IH x y Hp Hx Hy Hne).
Qed.
(* the app band and the shadow band are apart: no byte of an in_app range is a byte of the shadow of an in_app frame *)
Lemma cnob_band : forall lo len F a,
  in_app lo len -> in_app F 512 -> lo <= a < lo + len -> ~ (shadow_addr F <= a < shadow_addr F + 64).
Proof.
intros lo len F a (Hlo & Hb) (HF & HbF) Ha Hs. unfold shadow_addr in Hs.
pose proof asan_consts as (C1 & _).
unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
destruct Hb as [Hb | (Hb1 & Hb2)], HbF as [HbF | (HbF1 & HbF2)]; lia.
Qed.
Lemma cnob_frame_keep : forall D ly S Hp W mem mdc STKc spc off Dt ly2 S2 Hp2 W2 mem2 md2 k1 a,
  ARcfx ly S Hp W mem mdc ->
  AJ' STKc spc
    ((cnb_F D + off, cnb_F D + off + 56) :: ablocks_fp (prhPj_hbl Dt)) ly S Hp W mem mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (CNB_CID, bi_fpos D) (frames S) -> frame_addr ly CNB_CID (bi_fpos D) = cnb_F D ->
  (forall b kk, In (b, kk) Dt -> In (b - cf_head, kk + cf_head) (ablocks B ly S)) ->
  (cnb_F D <= a < cnb_F D + 512 \/ shadow_addr (cnb_F D) <= a < shadow_addr (cnb_F D) + 64) ->
  ~ (cnb_F D + off <= a < cnb_F D + off + 56) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a.
Proof.
intros D ly S Hp W mem mdc STKc spc off Dt ly2 S2 Hp2 W2 mem2 md2 k1 a HAR HJ1 Hin HFA HDt Ha Hns.
pose proof (ajxR_frm HJ1) as K4.
pose proof (alx_frames SEGS B ARcfx LAWS ly S Hp W mem mdc CNB_CID (bi_fpos D) HAR Hin) as (_ & Happ & _).
assert (HFB : fs_frame_bytes CNB_CID = 512) by (vm_compute; reflexivity).
rewrite HFA, HFB in Happ.
pose proof (alx_sep SEGS B ARcfx LAWS ly S Hp W mem mdc HAR) as (Hsep & _).
apply (K4 CNB_CID (bi_fpos D) a Hin).
- unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFA, HFB.
  destruct Ha as [Ha|Ha]; [left; lia | right; change (512 / 8) with 64; lia].
- intros HinFP. rewrite inFP_cons in HinFP. destruct HinFP as [Hs | (rr & Hrr & Hra)]; [exact (Hns Hs)|].
  unfold ablocks_fp, prhPj_hbl in Hrr. rewrite map_map in Hrr. apply in_map_iff in Hrr as ([b kk] & Er & Hbk).
  subst rr. cbn [fst snd] in Hra.
  pose proof (HDt b kk Hbk) as Hblk.
  pose proof (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem mdc _ _ HAR Hblk) as (_ & _ & _ & Happb & _).
  destruct Ha as [Ha|Ha].
  + assert (Hzd : zdisjoint (b - cf_head, req_size (kk + cf_head))
                   (frame_addr ly CNB_CID (bi_fpos D), fs_frame_bytes CNB_CID)).
    { apply (cnob_pairwise_app zdisjoint _ _ _ _ Hsep).
      - apply in_map_iff. exists (b - cf_head, kk + cf_head). split; [reflexivity | exact Hblk].
      - apply in_map_iff. exists (CNB_CID, bi_fpos D). split; [reflexivity | exact Hin]. }
    unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite HFA, HFB in Hzd. lia.
  + exact (cnob_band _ _ _ a Happb Happ ltac:(lia) Ha).
Qed.
(* a live block that survives the call and is not one of the freed tree's blocks keeps its bytes; distinctness is by
   user address (the ledger's NoDup (map fst Lam)) *)
Lemma cnob_block_keep : forall D ly S Hp W mem mdc STKc spc off Dt ly2 S2 Hp2 W2 mem2 md2 k1 b' kk' a,
  ARcfx ly S Hp W mem mdc ->
  AJ' STKc spc
    ((cnb_F D + off, cnb_F D + off + 56) :: ablocks_fp (prhPj_hbl Dt)) ly S Hp W mem mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (CNB_CID, bi_fpos D) (frames S) -> frame_addr ly CNB_CID (bi_fpos D) = cnb_F D ->
  0 <= off -> off + 56 <= 512 ->
  (forall b kk, In (b, kk) Dt -> In (b - cf_head, kk + cf_head) (ablocks B ly S)) ->
  (forall b kk, In (b, kk) Dt -> b <> b') ->
  In (b' - cf_head, kk' + cf_head) (ablocks B ly S) -> In (b' - cf_head, kk' + cf_head) (ablocks B ly2 S2) ->
  0 <= kk' -> b' <= a < b' + kk' ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a.
Proof.
intros D ly S Hp W mem mdc STKc spc off Dt ly2 S2 Hp2 W2 mem2 md2 k1 b' kk' a HAR HJ1 Hin HFA Hoff0 Hoff56 HDt Hne
  Hb1 Hb2 Hkk Ha.
pose proof (ajxR_blk HJ1) as K2.
pose proof (alx_sep SEGS B ARcfx LAWS ly S Hp W mem mdc HAR) as (Hsep & _).
pose proof (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem mdc _ _ HAR Hb1) as (_ & _ & _ & _ & _ & Hsepb).
assert (Hcf : 0 <= cf_head) by (vm_compute; discriminate).
pose proof (req_size_pos (kk' + cf_head) ltac:(apply Z.add_nonneg_nonneg; [exact Hkk | exact Hcf])) as (Hrs1 & Hrs2).
assert (HFB : fs_frame_bytes CNB_CID = 512) by (vm_compute; reflexivity).
replace a with ((b' - cf_head) + (a - (b' - cf_head))) by lia.
apply (K2 (b' - cf_head) (kk' + cf_head) (a - (b' - cf_head)) Hb1 Hb2); [lia|].
replace (b' - cf_head + (a - (b' - cf_head))) with a by lia.
intros HinFP. rewrite inFP_cons in HinFP. destruct HinFP as [Hs | (rr & Hrr & Hra)].
- (* the freed struct is a frame byte, the block is not *)
  assert (Hzd : zdisjoint (b' - cf_head, req_size (kk' + cf_head))
                 (frame_addr ly CNB_CID (bi_fpos D), fs_frame_bytes CNB_CID)).
  { apply (cnob_pairwise_app zdisjoint _ _ _ _ Hsep).
    - apply in_map_iff. exists (b' - cf_head, kk' + cf_head). split; [reflexivity | exact Hb1].
    - apply in_map_iff. exists (CNB_CID, bi_fpos D). split; [reflexivity | exact Hin]. }
  unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite HFA, HFB in Hzd. lia.
- unfold ablocks_fp, prhPj_hbl in Hrr. rewrite map_map in Hrr. apply in_map_iff in Hrr as ([b kk] & Er & Hbk).
  subst rr. cbn [fst snd] in Hra.
  pose proof (HDt b kk Hbk) as Hblk. pose proof (Hne b kk Hbk) as Hbb.
  destruct (cnob_pairwise_two zdisjoint _ (b - cf_head, req_size (kk + cf_head)) (b' - cf_head, req_size (kk' + cf_head))
    Hsepb) as [Hzd | Hzd].
  + apply in_map_iff. exists (b - cf_head, kk + cf_head). split; [reflexivity | exact Hblk].
  + apply in_map_iff. exists (b' - cf_head, kk' + cf_head). split; [reflexivity | exact Hb1].
  + intros E. injection E as E1 _. lia.
  + unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. lia.
  + unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. lia.
Qed.

(* ==== THE PIECES OF A STEP: closed constants (vm_compute only on closed goals, lead 16:0xZ), and what a call keeps
   of the cut's registers, saved words and real-stack slots ==== *)
Lemma cnob_fb : fs_frame_bytes CNB_CID = 512.
Proof. vm_compute. reflexivity. Qed.
Lemma cnob_stk_pjf : STK_pj_free DOC_D + 192 <= STK_check_no_overread /\ 0 <= STK_pj_free DOC_D.
Proof. split; vm_compute; discriminate. Qed.
Lemma cnob_stk_free : ASTACK + 192 <= STK_check_no_overread.
Proof. vm_compute. discriminate. Qed.
Lemma cnob_cf_head : 0 <= cf_head.
Proof. vm_compute. discriminate. Qed.
Lemma cnob_F2_cons : forall {X Y} (R : X -> Y -> Prop) x y l1 l2,
  Forall2 R (x :: l1) (y :: l2) -> R x y /\ Forall2 R l1 l2.
Proof. intros X Y R x y l1 l2 H. inversion H; subst. split; assumption. Qed.
Lemma psc_preserved_reg_b : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
(* the callee-saved test on a closed register number (vm_compute on the closed number only) *)
Ltac cnob_cs := lazymatch goal with |- acallee_saved ?t =>
  let v := eval vm_compute in t in change t with v; unfold acallee_saved; lia end.
(* every register the cut names is callee-saved, so a call keeps the snapshot *)
Lemma cnob_regsat_keep : forall D r r1 regs regs2, aregs_preserved regs regs2 ->
  cnb_regsat regs (cnb_core D ++ [(24%bv, r); (25%bv, r1)]) ->
  cnb_regsat regs2 (cnb_core D ++ [(24%bv, r); (25%bv, r1)]).
Proof.
intros D r r1 regs regs2 HP HR. unfold cnb_regsat in *. rewrite Forall_forall in HR |- *.
intros [rr vv] Hi. pose proof (HR (rr, vv) Hi) as Hh. cbn [fst snd] in Hh |- *. rewrite <- Hh.
apply (psc_preserved_reg_b regs regs2 rr HP).
unfold cnb_core in Hi. cbn [app In] in Hi.
repeat (destruct Hi as [Hi | Hi]; [injection Hi as <- _; cnob_cs |]). destruct Hi.
Qed.

(* ==== THE RUN EVENTS OF CB8's SIX FREES, against the contract's cnb_fevs (the model of record's p1_tfree per
   reading, then the copies' three HFr) ==== *)
(* a struct's own run event at its pj_free, keyed on the struct's STATE as the model of record is (PresetRun.v
   5ac818ab1fe6 :347-348 p1_tfree): a FILLED struct (an accepted reading) emits HBulk of its tree's requests in
   pj_free's order (HBulk [] when its tree holds no block), a zeroed / refused struct emits NOTHING *)
Definition cnb_pjevs (st : cnb_st) (F : list (Z * Z)) : list PresetReqAt.hev :=
  match st with
  | Some _ => [PresetReqAt.HBulk (map (fun b => snd b + cf_head) F)]
  | None => []
  end.
(* the walk's form of a tree's events: pj_free's own (prhPj_free_evs F, none for an empty list), or, for a tree with
   no block, the model's empty bulk HBulk [], which the walk steps over (PRH_FnPj.prhPj_bulk_nil_pos) *)
Definition cnob_tree_evs (F : list (Z * Z)) (E : list PresetReqAt.hev) : Prop :=
  E = prhPj_free_evs F \/ (F = [] /\ E = [PresetReqAt.HBulk []]).
Lemma cnob_pjevs_tree : forall m lblk d v st F, pj_foR SEGS m lblk d v (cnb_Dof st) F -> cnob_tree_evs F (cnb_pjevs st F).
Proof.
intros m lblk d v st F H. destruct st as [p|]; cbn [cnb_pjevs cnb_Dof] in H |- *.
- destruct F as [|b F']; [right; split; reflexivity | left; reflexivity].
- left. destruct (pj_foR_fdR SEGS m lblk d v [] F H) as (_ & HP).
  pose proof (Permutation_nil (Permutation_sym HP)) as ->. reflexivity.
Qed.
(* the walk's form of the copies' events: one HFr of the copy's request per copy still to free that is not NULL *)
Definition cnob_cfree_evs (D : cnb_in) (cs : list Z) : list PresetReqAt.hev :=
  flat_map (fun c => if c =? 0 then [] else [PresetReqAt.HFr (cnb_size D + 16)]) cs.
(* the granted copies' events are the text's C3 when no copy is NULL *)
Lemma cnob_cevs_C3 : forall D r1 r2 r3, r1 <> 0 -> r2 <> 0 -> r3 <> 0 -> cnb_cevs D r1 r2 r3 = cnb_C3 D.
Proof.
intros D r1 r2 r3 H1 H2 H3. unfold cnb_cevs, cnb_cblks, cnb_cblk, cnb_C3.
rewrite (proj2 (Z.eqb_neq r1 0) H1), (proj2 (Z.eqb_neq r2 0) H2), (proj2 (Z.eqb_neq r3 0) H3). reflexivity.
Qed.
(* a reading that ran out left its struct zero (PresetRun.ranout_refused: the model refuses it) *)
Lemma cnob_rd_ro : forall D o st, cnb_ro D o = true -> cnb_rd D o st -> st = None.
Proof.
intros D o st Hro Hrd. destruct st as [[t Dd]|]; [|reflexivity]. cbn [cnb_rd] in Hrd.
unfold cnb_ro in Hro. rewrite (PresetRun.ranout_refused ReaderRes.jr_strtod (bi_x D) o Hro) in Hrd. discriminate Hrd.
Qed.
(* a reading's struct event is the model's p1_tfree at its grant: cnb_rd says which, the tree's free order (the free
   cut's cnb_fo, PJF-TIE closed at the cut) the list *)
Lemma cnob_rd_tfree : forall D o st F, cnb_rd D o st ->
  (forall t Dd, st = Some (t, Dd) ->
     map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o) (bi_x D)) ->
  cnb_pjevs st F = PresetRun.p1_tfree ReaderRes.jr_strtod (bi_x D) o.
Proof.
intros D o st F Hrd Htie. unfold PresetRun.p1_tfree.
destruct st as [[t Dd]|]; cbn [cnb_rd cnb_pjevs] in Hrd |- *; rewrite Hrd; [rewrite (Htie t Dd eq_refl)|]; reflexivity.
Qed.
(* THE ORDER: CB8's six frees (pj_free d1, d2, d3, then the copies r1, r2, r3) make exactly cnb_fevs *)
Lemma cnob_fevs_eq : forall D o1 o2 o0 st1 st2 st3 F1 F2 F3 r1 r2 r3,
  r1 <> 0 -> r2 <> 0 -> r3 <> 0 -> cnb_rds3 D o1 o2 o0 st1 st2 st3 ->
  (forall t Dd, st1 = Some (t, Dd) ->
     map (fun b => snd b + cf_head) F1 = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o1) (bi_x D)) ->
  (forall t Dd, st2 = Some (t, Dd) ->
     map (fun b => snd b + cf_head) F2 = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o2) (bi_x D)) ->
  (forall t Dd, st3 = Some (t, Dd) ->
     map (fun b => snd b + cf_head) F3 = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o0) (bi_x D)) ->
  cnb_pjevs st1 F1 ++ cnb_pjevs st2 F2 ++ cnb_pjevs st3 F3 ++ cnob_cfree_evs D [r1; r2; r3] = cnb_fevs D o1 o2 o0.
Proof.
intros D o1 o2 o0 st1 st2 st3 F1 F2 F3 r1 r2 r3 H1 H2 H3 (Hrd1 & Hrds) T1 T2 T3.
unfold cnob_cfree_evs, cnb_fevs. cbn [flat_map].
rewrite (proj2 (Z.eqb_neq r1 0) H1), (proj2 (Z.eqb_neq r2 0) H2), (proj2 (Z.eqb_neq r3 0) H3).
unfold PresetReqAt.FUZZ_PAD. cbn [repeat app].
destruct (cnb_ro D o1) eqn:E1; try rewrite E1 in Hrds.
- destruct Hrds as (-> & ->). rewrite (cnob_rd_ro D o1 st1 E1 Hrd1). reflexivity.
- destruct Hrds as (Hrd2 & Hrds3).
  destruct (cnb_ro D o2) eqn:E2; try rewrite E2 in Hrds3.
  + subst st3. rewrite (cnob_rd_ro D o2 st2 E2 Hrd2).
    rewrite (cnob_rd_tfree D o1 st1 F1 Hrd1 T1). cbn [cnb_pjevs app]. reflexivity.
  + rewrite (cnob_rd_tfree D o1 st1 F1 Hrd1 T1), (cnob_rd_tfree D o2 st2 F2 Hrd2 T2),
      (cnob_rd_tfree D o0 st3 F3 Hrds3 T3).
    rewrite <- !app_assoc. reflexivity.
Qed.

(* ---- CNT24 DERIVED when no copy was refused: the live set at the free cut is the entry's advanced by the three
   copies and the readings at the grants o1 o2 o0, a sub-multiset of the entry's advanced by the ALL-GRANTED copies
   and readings (a reading that ran out leaves nothing, PresetRun.ranout_pacc; one that did not is the all-granted
   one, PjGrammar.G7_1), so its class-24 count is at most cnb_pre's position-free pkR count over
   ck_cno_evs .. None None None (PresetRun.pkR_prefix) ---- *)
Lemma cnob_pacc_eq : forall x o, PresetRun.ranout ReaderRes.jr_strtod x o = false ->
  PresetReqAtNoMiss.pacc ReaderRes.jr_strtod x (PresetRun.okof o) = PresetReqAtNoMiss.pacc ReaderRes.jr_strtod x [].
Proof.
intros x [j|] H; [|reflexivity].
cbn [PresetRun.ranout PresetRun.okof] in H |- *. apply Nat.ltb_ge in H.
unfold PresetReqAtNoMiss.pacc, PresetReqAt.rtr. unfold PresetReqAt.rtr in H.
assert (Hu : forall i, (i < PjGrammar.ncalls ReaderRes.jr_strtod x)%nat -> nth i (PresetReqAt.okk j) true = true).
{ intros i Hi. apply PresetRun.okk_true. unfold PjGrammar.ncalls in Hi. lia. }
assert (H0 : forall i, (i < PjGrammar.ncalls ReaderRes.jr_strtod x)%nat -> nth i (@nil bool) true = true)
  by (intros i _; destruct i; reflexivity).
pose proof (f_equal fst (PjGrammar.G7_1 ReaderRes.jr_strtod x [] H0)) as Ej. cbn [fst] in Ej.
rewrite (PjGrammar.G7_1 ReaderRes.jr_strtod x (PresetReqAt.okk j) Hu). cbn [fst snd]. rewrite Ej. reflexivity.
Qed.
Lemma cnob_pacc_subm : forall x o,
  PresetReqAt.subm (PresetReqAtNoMiss.pacc ReaderRes.jr_strtod x (PresetRun.okof o))
    (PresetReqAtNoMiss.pacc ReaderRes.jr_strtod x []).
Proof.
intros x o. destruct (PresetRun.ranout ReaderRes.jr_strtod x o) eqn:E.
- rewrite (PresetRun.ranout_pacc ReaderRes.jr_strtod x o E). apply PresetReqAt.subm_nil.
- rewrite (cnob_pacc_eq x o E). apply PresetReqAt.subm_refl.
Qed.
Lemma cnob_subm_app_tail : forall a b X, PresetReqAt.subm a b -> PresetReqAt.subm (a ++ X) (b ++ X).
Proof.
intros a b X [d H]. exists d. eapply Permutation_trans; [apply Permutation_app_tail; exact H|].
rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.
Lemma cnob_revs3_subm : forall D o1 o2 o0 s,
  PresetReqAt.subm (PresetReqAt.hlive_from s (cnb_revs3 D o1 o2 o0)) (PresetReqAt.hlive_from s (cnb_revs3 D None None None)).
Proof.
intros D o1 o2 o0 s. set (pa := PresetReqAtNoMiss.pacc ReaderRes.jr_strtod (bi_x D) []).
assert (Hpe : forall o s', PresetReqAt.hlive_from s' (cnb_pe D o) =
    PresetReqAtNoMiss.pacc ReaderRes.jr_strtod (bi_x D) (PresetRun.okof o) ++ s')
  by (intros o s'; exact (proj2 (PresetReqAtNoMiss.parse_ok ReaderRes.jr_strtod (bi_x D) _ s'))).
assert (HN : PresetReqAt.hlive_from s (cnb_revs3 D None None None) = pa ++ pa ++ pa ++ s).
{ unfold cnb_revs3, cnb_ro. cbn [PresetRun.ranout].
  rewrite !PresetReqAt.hlive_from_app, !Hpe. reflexivity. }
rewrite HN. unfold cnb_revs3.
destruct (cnb_ro D o1) eqn:E1.
- rewrite app_nil_r, Hpe. unfold cnb_ro in E1. rewrite (PresetRun.ranout_pacc ReaderRes.jr_strtod _ o1 E1).
  cbn [app]. rewrite !app_assoc. apply PresetReqAt.subm_app_r.
- rewrite PresetReqAt.hlive_from_app, Hpe. unfold cnb_ro in E1. rewrite (cnob_pacc_eq _ o1 E1). fold pa.
  destruct (cnb_ro D o2) eqn:E2.
  + rewrite app_nil_r, Hpe. unfold cnb_ro in E2. rewrite (PresetRun.ranout_pacc ReaderRes.jr_strtod _ o2 E2).
    cbn [app]. rewrite (app_assoc pa pa (pa ++ s)). apply PresetReqAt.subm_app_r.
  + rewrite PresetReqAt.hlive_from_app, !Hpe. unfold cnb_ro in E2. rewrite (cnob_pacc_eq _ o2 E2). fold pa.
    apply cnob_subm_app_tail. apply cnob_pacc_subm.
Qed.
Lemma cnob_subm_perm : forall a a' b, Permutation a a' -> PresetReqAt.subm a' b -> PresetReqAt.subm a b.
Proof.
intros a a' b HP [d Hd]. exists d. eapply Permutation_trans; [exact Hd|].
apply Permutation_app_tail. symmetry. exact HP.
Qed.
(* the class-24 count of a live set below the entry's advanced by a PREFIX of the all-granted events is at most
   cnb_pre's position-free pkR count (PresetRun.pkR_prefix); the count premise is read off cnb_pre BY ITS TYPE *)
Lemma cnob_cnt24_sub : forall D (S : astate) j,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  PresetReqAt.subm (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D)))
       (firstn j (ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None))) ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros D S j HPRE Hsub.
assert (H24 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass)
    (PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D))) (ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None))
  <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ pose proof HPRE as H24. unfold cnb_pre in H24. cbv zeta in H24. ro_pick H24. }
pose proof (PresetRun.pkR_prefix (PresetRoom.in_cls YG00.kBatchClass)
  (ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None) (PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D))) j)
  as Hpre.
pose proof (PresetReqAt.subm_cnt (PresetRoom.in_cls YG00.kBatchClass) _ _ Hsub) as Hc.
apply CfRoomLivePreset.preset_ccnt24.
change (PresetRoom.in_cls 24) with (PresetRoom.in_cls YG00.kBatchClass).
clear - Hc Hpre H24. lia.
Qed.
(* CNT24 when no copy was refused (ownl = 0): the three copies and the readings at the grants o1 o2 o0 *)
Lemma cnob_cnt24_own0 : forall D (S : astate) r1 r2 r3 o1 o2 o0,
  cnb_pre (fx := fx) B ARcfx CTX0 D -> r1 <> 0 -> r2 <> 0 -> r3 <> 0 ->
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros D S r1 r2 r3 o1 o2 o0 HPRE H1 H2 H3 (Hlive & _).
rewrite (cnob_cevs_C3 D r1 r2 r3 H1 H2 H3) in Hlive.
apply (cnob_cnt24_sub D S (length (cnb_C3 D ++ cnb_revs3 D None None None)) HPRE).
rewrite <- (cnb_ck_cno_evs D None None None), app_assoc, firstn_app, Nat.sub_diag, firstn_all.
cbn [firstn]. rewrite app_nil_r.
eapply cnob_subm_perm; [exact Hlive|].
rewrite !PresetReqAt.hlive_from_app. apply cnob_revs3_subm.
Qed.
(* CNT24 when a copy was refused (ownl <> 0): only the granted copies' events, a prefix of the all-granted ones *)
Lemma cnob_cnt24_own1 : forall D (S : astate) r1 r2 r3,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_prog D (cnb_cevs D r1 r2 r3) S ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros D S r1 r2 r3 HPRE (Hlive & _).
apply (cnob_cnt24_sub D S (length (cnb_cblks D r1 r2 r3)) HPRE).
assert (E : firstn (length (cnb_cblks D r1 r2 r3)) (ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None) =
    cnb_cevs D r1 r2 r3).
{ rewrite <- (cnb_ck_cno_evs D None None None).
  unfold cnb_cevs, cnb_cblks, cnb_cblk, cnb_C3.
  destruct (r1 =? 0), (r2 =? 0), (r3 =? 0); reflexivity. }
rewrite E. eapply cnob_subm_perm; [exact Hlive | apply PresetReqAt.subm_refl].
Qed.
(* CNT24 at the free cut, on both arms of cnb_at_free *)
Lemma cnob_cnt24_free : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_at_freeR (fx := fx) B ARcfx WLE' D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3
    o1 o2 o0 ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HPRE HAT.
pose proof HAT as (_ & _ & _ & _ & _ & _ & HOWN0 & HOWN1 & _).
destruct (Z.eq_dec ownl 0) as [H0 | H0].
- destruct (HOWN0 H0) as (H1 & H2 & H3 & Hprog & _).
  exact (cnob_cnt24_own0 D S r1 r2 r3 o1 o2 o0 HPRE H1 H2 H3 Hprog).
- exact (cnob_cnt24_own1 D S r1 r2 r3 HPRE (proj1 (HOWN1 H0))).
Qed.

(* ---- the live set across a free: a bulk free removes the tree's requests, one HFr the copy's ---- *)
Lemma cnob_rmall_app : forall L L' R, Permutation L L' -> Permutation (PresetReqAt.rmall L (L' ++ R)) R.
Proof.
induction L as [|z L IH]; intros L' R HP.
- pose proof (Permutation_nil HP) as ->. apply Permutation_refl.
- rewrite PresetReqAt.rmall_cons.
  assert (Hin : In z L') by (apply (Permutation_in z HP); left; reflexivity).
  destruct (in_split z L' Hin) as (A & B0 & ->).
  eapply Permutation_trans.
  { apply PresetReqAtNoMiss.rmall_perm. rewrite <- app_assoc. cbn [app].
    exact (PresetReqAtNoMiss.rm1_mid z A (B0 ++ R)). }
  rewrite app_assoc. apply IH. exact (Permutation_cons_app_inv _ _ HP).
Qed.
Lemma cnob_live_pjf : forall (S S2 : astate) Dt F E,
  Permutation (map snd (blocks S)) (map (fun b => snd b + cf_head) Dt ++ map snd (blocks S2)) ->
  Permutation F Dt -> cnob_tree_evs F E ->
  Permutation (map snd (blocks S2)) (PresetReqAt.hlive_from (map snd (blocks S)) E).
Proof.
intros S S2 Dt F E HP HF [-> | (-> & ->)].
- destruct F as [|b F'].
  + pose proof (Permutation_nil HF) as ->. cbn [map app prhPj_free_evs PresetReqAt.hlive_from fold_left] in HP |- *.
    symmetry. exact HP.
  + cbn [prhPj_free_evs PresetReqAt.hlive_from fold_left PresetReqAt.hstep].
    symmetry. eapply Permutation_trans; [apply PresetReqAtNoMiss.rmall_perm; exact HP|].
    apply cnob_rmall_app. apply Permutation_map. exact HF.
- pose proof (Permutation_nil HF) as ->.
  cbn [map app PresetReqAt.hlive_from fold_left PresetReqAt.hstep PresetReqAt.rmall] in HP |- *.
  symmetry. exact HP.
Qed.
Lemma cnob_live_fr : forall (S S2 : astate) c n,
  Permutation (map snd (blocks S)) (map snd (cnob_cblk n c) ++ map snd (blocks S2)) ->
  Permutation (map snd (blocks S2)) (PresetReqAt.hlive_from (map snd (blocks S)) (if c =? 0 then [] else [PresetReqAt.HFr n])).
Proof.
intros S S2 c n HP. unfold cnob_cblk in HP. destruct (c =? 0); cbn [map app PresetReqAt.hlive_from fold_left PresetReqAt.hstep] in HP |- *.
- symmetry. exact HP.
- symmetry. eapply Permutation_trans; [apply PresetReqAtNoMiss.rm1_perm; exact HP|].
  rewrite PresetReqAt.rm1_cons_eq. apply Permutation_refl.
Qed.

(* ---- the progress fact across one free of CB8 (the kit's cnb_prog_app) ---- *)
Lemma cnob_prog_pjf : forall D E0 E (S S2 : astate) Dt F,
  cnb_prog D E0 S ->
  Permutation (map snd (blocks S)) (map (fun b => snd b + cf_head) Dt ++ map snd (blocks S2)) ->
  Permutation F Dt -> cnob_tree_evs F E ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i (prhPj_free_evs F) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPj_free_evs F))%nat H0 hist' S2) ->
  cnb_prog D (E0 ++ E) S2.
Proof.
intros D E0 E S S2 Dt F Hprog HP HF HT Hpost.
apply (cnb_prog_app D E0 E S S2 Hprog).
- change (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (blocks S2)).
  change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)).
  exact (cnob_live_pjf S S2 Dt F E HP HF HT).
- intros sm x os i H0 hist Hpos Hrun. destruct HT as [-> | (-> & ->)]; [exact (Hpost sm x os i H0 hist Hpos Hrun)|].
  pose proof (cnob_run_at1 _ _ _ _ _ Hrun) as He.
  pose proof (proj1 (prhPj_bulk_nil_pos sm x os i H0 hist S He) Hpos) as Hpos1.
  destruct (Hpost sm x os (Datatypes.S i) H0 hist Hpos1 (prhPj_run_at_nil sm x os (Datatypes.S i))) as (hist' & Hh).
  exists hist'. cbn [prhPj_free_evs length] in Hh |- *. replace (i + 1)%nat with (Datatypes.S i + 0)%nat by lia.
  exact Hh.
Qed.
Lemma cnob_prog_fr : forall D E0 (S S2 : astate) c n,
  cnb_prog D E0 S ->
  Permutation (map snd (blocks S)) (map snd (cnob_cblk n c) ++ map snd (blocks S2)) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     PRH_Base.prh_run_at sm x os i (if c =? 0 then [] else [PresetReqAt.HFr n]) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (if (c =? 0)%Z then [] else [PresetReqAt.HFr n]))%nat
       H0 hist' S2) ->
  cnb_prog D (E0 ++ (if c =? 0 then [] else [PresetReqAt.HFr n])) S2.
Proof.
intros D E0 S S2 c n Hprog HP Hpost.
apply (cnb_prog_app D E0 _ S S2 Hprog); [|exact Hpost].
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (blocks S2)).
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)).
exact (cnob_live_fr S S2 c n HP).
Qed.

(* ---- the hull suffix still to pay at a cut of the free phase, named by the structs still to free: the free cut's
   rd0 (three), then pf1 / pf2 / pf0 after pj_free 1 / 2 / 3 (the contract's stage suffixes, literal suffixes of
   cnb_hev_all x); the copies' frees pay nothing, so pf0 (= cnb_hF3) holds through them. Any longer list is rd0, so
   one pj_free always pays a (possibly empty) piece ---- *)
Definition cnob_hrest (D : cnb_in) (offs : list Z) : list PresetReqAt.hev :=
  match offs with
  | [] => cnb_hrest_pf0 (bi_x D)
  | [_] => cnb_hrest_pf2 (bi_x D)
  | [_; _] => cnb_hrest_pf1 (bi_x D)
  | _ => cnb_hrest_rd0 (bi_x D)
  end.
Lemma cnob_hrest_step : forall D off offs, exists E, cnob_hrest D (off :: offs) = E ++ cnob_hrest D offs.
Proof.
intros D off [|o1 [|o2 [|o3 offs]]]; cbn [cnob_hrest].
- eexists. exact (cnb_hrest_pf0_split (bi_x D)).
- eexists. exact (cnb_hrest_pf2_split (bi_x D)).
- eexists. exact (cnb_hrest_pf1_split (bi_x D)).
- exists []. reflexivity.
Qed.
(* a pj_free uses nothing (hull_used S S' []): the budget for the rest is left *)
Lemma cnob_hull_pj : forall D off offs (S S2 : astate),
  PresetHullBudget.hull_budget S (cnob_hrest D (off :: offs)) -> PresetHullBudget.hull_used S S2 [] ->
  PresetHullBudget.hull_budget S2 (cnob_hrest D offs).
Proof.
intros D off offs S S2 H U.
destruct (cnob_hrest_step D off offs) as (E & HE). rewrite HE in H.
exact (PresetHullBudget.hull_budget_app S S2 E (cnob_hrest D offs) H
  (PresetHullBudget.hull_used_infix S S2 [] [] E U)).
Qed.

(* ==== THE FREE PHASE INVARIANT: what holds at each of the seven cut points of CB8 (740, 748, 756, 764, 772, 780,
   788), with `offs` / `sts` the struct offsets and reading states STILL TO FREE, `Fs` their order lists, `Es` their
   events and `cs` the padded copies still to free; the class-24 count (CNT24, never raised by a free); and, when no
   copy was refused, the progress fact over the events E0 made since entry, with E0 ++ the events still to come =
   the whole of check_no_overread's events at the readings' grants. The journal is at wle' (restated in place: only
   cuts after a free use it); LAST, the hull budget still to pay (cnob_hrest). At 740 it is cnb_at_free's own
   content (cnob_fmid_of_free), at 788 it is CB9's start (cnob_end_of_fmid). ==== *)
Definition cnob_fmid (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (nr : nat) (r1 r2 r3 r ownl : Z) (offs : list Z) (sts : list cnb_st) (Fs : list (list (Z * Z)))
  (Es : list (list PresetReqAt.hev)) (cs : list Z) : Prop :=
  cnb_baseR (fx := fx) B ARcfx WLE' D fxk ly S Hp W regs mem md k 6 /\
  cnb_regsat regs (cnb_core D ++ [(24%bv, r); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\
  room_live_cf S /\ YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  (ownl = 0 -> exists o1 o2 o0 E0, ran = cnb_ranz D o1 o2 o0 /\ cnb_prog D E0 S /\
     E0 ++ concat Es ++ cnob_cfree_evs D cs = cnb_C3 D ++ cnb_revs3 D o1 o2 o0 ++ cnb_fevs D o1 o2 o0) /\
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (bi_most D) ownl /\
  bi_peak D <= peak /\ bi_cnt D <= cnt <= bi_cnt D + Z.of_nat nr * ck_ncalls (bi_x D) /\
  length offs = length sts /\
  Forall (fun off => 32 <= off /\ off + 112 <= fs_frame_bytes CNB_CID /\ off mod 8 = 0 /\ off mod 32 = 0) offs /\
  StronglySorted (fun a b => a + 56 <= b) offs /\
  Forall (fun off => cnb_open W mem (cnb_F D + off)) offs /\
  (* each tree still to free is FREEABLE with its order list (what tpj_free_specX takes), at the current ledger list *)
  Forall2 (fun p F => pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_F D + fst p) (cnb_Dof (snd p)) F)
    (combine offs sts) Fs /\
  Forall2 cnob_tree_evs Fs Es /\
  (* each padded copy still to free is NULL or no harness block; its block is in the ablocks Permutation below *)
  Forall (fun c => c <> 0 -> ~ In c Hp) cs /\
  Permutation Lam (flat_map cnb_Dof sts ++ bi_Lam D) /\
  Permutation (ablocks B ly S)
    (flat_map (cnb_cblk D) cs ++ ck_hblks (flat_map cnb_Dof sts) ++ ablocks B (bi_ly D) (bi_S D)) /\
  (forall a kk, In (a, kk) (flat_map cnb_Dof sts) ->
     ~ In (a - cf_head, kk + cf_head) (ablocks B (bi_ly D) (bi_S D))) /\
  PresetHullBudget.hull_budget S (cnob_hrest D offs).

(* each struct's tree has an order list at the free cut: a reading's tree is freeable by pjf_fd_of_node (depth <=
   MAXD < DOC_D), a skipped reading's zero struct by pv_fd_zeroR, and every freeable tree has one (pj_fdR_foR) *)
Lemma cnob_fos : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cnb_at_freeR (fx := fx) B ARcfx WLE' D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3
    o1 o2 o0 ->
  exists F1 F2 F3,
    pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_d1 D) (cnb_Dof st1) F1 /\
    pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_d2 D) (cnb_Dof st2) F2 /\
    pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_d3 D) (cnb_Dof st3) F3.
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HAT.
pose proof HAT as (HBASE & _ & _ & HMID & _).
pose proof HBASE as (_ & _ & HJ & HFRAME & _).
destruct HJ as (WS & HJ & _). pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hlyle.
pose proof HFRAME as (Hfrs & _).
pose proof Hlyle as (_ & _ & _ & _ & _ & LF & _).
assert (Hin : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HFA : frame_addr ly CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite LF; reflexivity).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd1 & Hd2 & Hd3 & _).
assert (HFB : fs_frame_bytes CNB_CID = 512) by (vm_compute; reflexivity).
assert (Hfd : forall off st, 0 <= off -> off + 56 <= fs_frame_bytes CNB_CID -> off mod 8 = 0 ->
  cnb_doc W mem Lam (cnb_F D + off) st -> pj_fdR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_F D + off) (cnb_Dof st)).
{ intros off st H0 H56 H8 Hd. destruct st as [[t Dd]|]; cbn [cnb_doc cnb_Dof] in Hd |- *.
  - destruct Hd as (Hnode & Hdep).
    exact (pjf_fd_of_node SEGS (rdW W mem) (prh_lin Lam) t DOC_D (cnb_F D + off) Dd
      ltac:(unfold DOC_D; lia) Hnode).
  - exact (PvFdZeroR.pv_fd_zeroR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_F D + off)
      (cnob_rw D ly S Hp W mem md off HAR Hin HFA H0 H56 H8) Hd). }
unfold cnb_d1, cnb_d2, cnb_d3 in Hd1, Hd2, Hd3 |- *.
rewrite HFB in Hfd.
destruct (pj_fdR_foR SEGS _ _ _ _ _ (Hfd 32 st1 ltac:(lia) ltac:(lia) eq_refl Hd1)) as (F1 & HF1).
destruct (pj_fdR_foR SEGS _ _ _ _ _ (Hfd 128 st2 ltac:(lia) ltac:(lia) eq_refl Hd2)) as (F2 & HF2).
destruct (pj_fdR_foR SEGS _ _ _ _ _ (Hfd 224 st3 ltac:(lia) ltac:(lia) eq_refl Hd3)) as (F3 & HF3).
exists F1, F2, F3. split; [exact HF1|]. split; [exact HF2 | exact HF3].
Qed.

(* ---- THE TREES' FREE ORDER AT THE FREE CUT (PJF-TIE, closed at the cut: tparse_noting_specX's Some arm states it
   and the readings carry it to the free cut as cnb_fo). For a FILLED struct, cnb_fo at the depth bound DOC_D (a
   reading's tree has depth <= MAXD < DOC_D, cnb_doc) gives an order list whose sizes are the model's pj_frees at the
   reading's grant, under CFHEAD-16 (the Section's HEAD16); a zeroed struct (cnb_fo = True) keeps the list it has.
   The order list F is chosen ONCE here, at the free cut, and moved across each earlier free by
   PRH_PjOrder.pj_foR_frame (cnob_pjf_step), so its tie, used once by cnob_fevs_eq, is never re-read. ---- *)
Lemma cnob_fo_one : forall D W mem Lam o d st G,
  cnb_doc W mem Lam d st -> pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D d (cnb_Dof st) G ->
  cnb_fo D W mem Lam o d st ->
  exists F, pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D d (cnb_Dof st) F /\
    (forall t Dd, st = Some (t, Dd) ->
       map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o) (bi_x D)).
Proof.
intros D W mem Lam o d st G Hdoc HG Hfo. destruct st as [[t Dd]|].
- cbn [cnb_doc] in Hdoc. destruct Hdoc as (_ & Hdep). cbn [cnb_fo cnb_Dof] in Hfo |- *.
  destruct (Hfo HEAD16 DOC_D ltac:(unfold DOC_D; lia)) as (F & HF & Ht).
  exists F. split; [exact HF|]. intros t' Dd' E. injection E as <- <-. exact Ht.
- exists G. split; [exact HG|]. intros t Dd E. discriminate E.
Qed.
Lemma cnob_fos_tie : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cnb_at_freeR (fx := fx) B ARcfx WLE' D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3
    o1 o2 o0 ->
  exists F1 F2 F3,
    pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_d1 D) (cnb_Dof st1) F1 /\
    pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_d2 D) (cnb_Dof st2) F2 /\
    pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_d3 D) (cnb_Dof st3) F3 /\
    (ownl = 0 ->
      (forall t Dd, st1 = Some (t, Dd) ->
         map (fun b => snd b + cf_head) F1 = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o1) (bi_x D)) /\
      (forall t Dd, st2 = Some (t, Dd) ->
         map (fun b => snd b + cf_head) F2 = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o2) (bi_x D)) /\
      (forall t Dd, st3 = Some (t, Dd) ->
         map (fun b => snd b + cf_head) F3 = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o0) (bi_x D))).
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HAT.
destruct (cnob_fos D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HAT)
  as (G1 & G2 & G3 & HG1 & HG2 & HG3).
pose proof HAT as (_ & _ & _ & HMID & _ & _ & HOWN0 & _).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd1 & Hd2 & Hd3 & _).
destruct (Z.eq_dec ownl 0) as [H0 | H0].
- destruct (HOWN0 H0) as (_ & _ & _ & _ & _ & _ & Hfo1 & Hfo2 & Hfo3).
  destruct (cnob_fo_one D W mem Lam o1 (cnb_d1 D) st1 G1 Hd1 HG1 Hfo1) as (F1 & HF1 & T1).
  destruct (cnob_fo_one D W mem Lam o2 (cnb_d2 D) st2 G2 Hd2 HG2 Hfo2) as (F2 & HF2 & T2).
  destruct (cnob_fo_one D W mem Lam o0 (cnb_d3 D) st3 G3 Hd3 HG3 Hfo3) as (F3 & HF3 & T3).
  exists F1, F2, F3. split; [exact HF1|]. split; [exact HF2|]. split; [exact HF3|].
  intros _. split; [exact T1|]. split; [exact T2 | exact T3].
- exists G1, G2, G3. split; [exact HG1|]. split; [exact HG2|]. split; [exact HG3|].
  intros E0. exfalso. exact (H0 E0).
Qed.

(* the cut CNB_FREE is the invariant with all three structs and all three copies still to free: the order lists F_k
   (cnob_fos_tie's: the reader's own, tied to the model's pj_frees when ownl = 0), the class-24 count (CNT24),
   under ownl = 0 the cut's progress fact with cnob_fevs_eq's equation, and the free cut's hull budget (its rd0
   suffix, the cut's last conjunct) *)
Lemma cnob_fmid_of_free : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3
    o1 o2 o0 F1 F2 F3,
  cnb_at_freeR (fx := fx) B ARcfx WLE' D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3
    o1 o2 o0 ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_d1 D) (cnb_Dof st1) F1 ->
  pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_d2 D) (cnb_Dof st2) F2 ->
  pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_d3 D) (cnb_Dof st3) F3 ->
  (ownl = 0 ->
    (forall t Dd, st1 = Some (t, Dd) ->
       map (fun b => snd b + cf_head) F1 = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o1) (bi_x D)) /\
    (forall t Dd, st2 = Some (t, Dd) ->
       map (fun b => snd b + cf_head) F2 = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o2) (bi_x D)) /\
    (forall t Dd, st3 = Some (t, Dd) ->
       map (fun b => snd b + cf_head) F3 = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o0) (bi_x D))) ->
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl
    [32; 128; 224] [st1; st2; st3] [F1; F2; F3] [cnb_pjevs st1 F1; cnb_pjevs st2 F2; cnb_pjevs st3 F3] [r1; r2; r3].
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 F1 F2 F3
  HAT HC24 HF1 HF2 HF3 HTIE.
pose proof HAT as (HBASE & HREG & HSLOTS & HMID & _ & _ & HOWN0 & _ & HHB).
pose proof HMID as (Hc1 & Hc2 & Hc3 & HLED & Hpk & Hcnt & HRL & _ & Ho1 & Ho2 & Ho3 & _ & _ & _ &
  HpermL & HpermB & Hfresh & _).
assert (HFB : fs_frame_bytes CNB_CID = 512) by (vm_compute; reflexivity).
unfold cnb_d1, cnb_d2, cnb_d3 in Ho1, Ho2, Ho3.
split; [exact HBASE|]. split; [exact HREG|]. split; [exact HSLOTS|]. split; [exact HRL|]. split; [exact HC24|].
split.
{ intros H0. destruct (HOWN0 H0) as (H1 & H2 & H3 & Hprog & Hran & Hrds & _).
  destruct (HTIE H0) as (T1 & T2 & T3).
  exists o1, o2, o0, (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0).
  split; [exact Hran|]. split; [exact Hprog|].
  rewrite (cnob_cevs_C3 D r1 r2 r3 H1 H2 H3).
  rewrite <- (cnob_fevs_eq D o1 o2 o0 st1 st2 st3 F1 F2 F3 r1 r2 r3 H1 H2 H3 Hrds T1 T2 T3).
  cbn [concat]. rewrite app_nil_r, <- !app_assoc. reflexivity. }
split; [exact HLED|]. split; [exact Hpk|]. split; [exact Hcnt|].
split; [reflexivity|].
split; [rewrite HFB; repeat (apply Forall_cons; [split; [lia | split; [lia | split; reflexivity]]|]); apply Forall_nil|].
split; [repeat (apply SSorted_cons; [|repeat (apply Forall_cons; [lia|]); apply Forall_nil]); apply SSorted_nil|].
split; [repeat (apply Forall_cons; [assumption|]); apply Forall_nil|].
split.
{ cbn [combine fst snd].
  apply Forall2_cons; [exact HF1|]. apply Forall2_cons; [exact HF2|]. apply Forall2_cons; [exact HF3|].
  apply Forall2_nil. }
split.
{ apply Forall2_cons; [exact (cnob_pjevs_tree _ _ _ _ _ _ HF1)|].
  apply Forall2_cons; [exact (cnob_pjevs_tree _ _ _ _ _ _ HF2)|].
  apply Forall2_cons; [exact (cnob_pjevs_tree _ _ _ _ _ _ HF3)|].
  apply Forall2_nil. }
split.
{ assert (Hcp : forall c, cnb_copy B D ly S Hp W mem c -> c <> 0 -> ~ In c Hp)
    by (intros c [Ec | (_ & Hnh & _)] Hc; [exfalso; exact (Hc Ec) | exact Hnh]).
  apply Forall_cons; [exact (Hcp r1 Hc1)|]. apply Forall_cons; [exact (Hcp r2 Hc2)|].
  apply Forall_cons; [exact (Hcp r3 Hc3)|]. apply Forall_nil. }
split.
{ cbn [flat_map]. rewrite !app_nil_r. repeat rewrite <- app_assoc. exact HpermL. }
split.
{ cbn [flat_map]. rewrite !app_nil_r. unfold cnb_cblks in HpermB.
  repeat rewrite <- app_assoc in HpermB |- *. exact HpermB. }
split; [cbn [flat_map]; rewrite !app_nil_r; exact Hfresh|].
cbn [cnob_hrest]. exact HHB.
Qed.

(* with nothing left to free, the invariant is CB9's start cut; nr <= 3 (at most three readings were made) turns
   the count into cnb_Q's `3 * ck_ncalls`, and the progress fact's events are the whole of ck_cno_evs' pieces; the
   refused copy's cnb_cdead is the free cut's (it reads only D); the hull suffix after the copies' frees is cnb_hF3
   (the contract's cnb_hrest_frees_split: pf0 = cnb_hF3; the three HFr pay nothing) *)
Lemma cnob_end_of_fmid : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl,
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] [] -> (nr <= 3)%nat ->
  bytes_at W mem (bi_data D) (bi_x D) ->
  ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)) ->
  (ownl <> 0 -> cnb_cdead D) ->
  cnb_at_end D fxk ly S Hp W regs mem md k Lam peak cnt ran r ownl.
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl HM Hnr Hbytes HR HCD.
assert (Hnc : 0 <= ck_ncalls (bi_x D)) by (unfold ck_ncalls; lia).
pose proof HM as (HBASE & HREG & HSLOTS & HRL & _ & HPROG & HLED & Hpk & Hcnt &
  _ & _ & _ & _ & _ & _ & _ & HpermL & HpermB & _ & HHB).
cbn [cnob_hrest] in HHB. rewrite (cnb_hrest_frees_split (bi_x D)) in HHB.
split; [exact HBASE|].
split.
{ unfold cnb_regsat in HREG |- *. rewrite Forall_forall in HREG |- *. intros x Hx.
  apply HREG. rewrite in_app_iff in Hx |- *. destruct Hx as [Hx | Hx]; [left; exact Hx|].
  right. cbn in Hx. cbn. tauto. }
split.
{ unfold cnb_slots in HSLOTS. exact (Forall_inv HSLOTS). }
split; [exact HLED|].
split; [cbn [flat_map] in HpermL; exact HpermL|].
split; [cbn [flat_map ck_hblks map app] in HpermB; exact HpermB|].
split; [exact Hpk|].
split; [clear - Hcnt Hnr Hnc; split; [lia | nia]|].
split; [exact HRL|]. split; [exact Hbytes|]. split; [exact HR|].
split; [|split; [exact HCD | exact HHB]].
intros H0. destruct (HPROG H0) as (o1 & o2 & o0 & E0 & Hran & Hprog & Heq).
exists o1, o2, o0. split; [|exact Hran].
unfold cnob_cfree_evs in Heq. cbn [concat flat_map] in Heq. rewrite !app_nil_r in Heq. rewrite <- Heq. exact Hprog.
Qed.

(* astk_ok reads only the layout's stack bounds and top, which layout_le keeps *)
Lemma cnob_astk_le : forall n ly ly' STKa sp, layout_le n ly ly' -> astk_ok STKa ly sp -> astk_ok STKa ly' sp.
Proof.
intros n ly ly' STKa sp Hle H. pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
unfold astk_ok, ly_bot in *. rewrite Etop, Elo, Ehi. exact H.
Qed.

(* ==== STEP (A): ONE pj_free CALL of the Free phase, from the callee's entry (a0 = the struct, ra = the return
   site) to its return, carrying the invariant from (off :: offs) (st :: sts) to offs sts ==== *)
Lemma cnob_nodup_first : forall (Lam A B0 : list (Z * Z)) b kk,
  List.NoDup (map fst Lam) -> Permutation Lam (A ++ B0) -> In (b, kk) B0 ->
  forall b0 kk0, In (b0, kk0) A -> b0 <> b.
Proof.
intros Lam A B0 b kk Hnd Hp Hb b0 kk0 Ha E. subst b0.
assert (Hnd' : List.NoDup (map fst (A ++ B0))) by (exact (Permutation_NoDup (Permutation_map fst Hp) Hnd)).
rewrite map_app in Hnd'.
apply (cnob_nodup_app_disj (map fst A) (map fst B0) b Hnd').
- exact (in_map fst A (b, kk0) Ha).
- exact (in_map fst B0 (b, kk) Hb).
Qed.
Lemma cnob_perm_cancel : forall (X A F E L2 : list (Z * Z)) L,
  Permutation L (A ++ L2) -> Permutation L (X ++ (A ++ F) ++ E) -> Permutation L2 (X ++ F ++ E).
Proof.
intros X A F E L2 L H1 H2.
apply (Permutation_app_inv_l A).
eapply Permutation_trans; [apply Permutation_sym; exact H1|].
eapply Permutation_trans; [exact H2|].
rewrite <- app_assoc. apply Permutation_app_swap_app.
Qed.

Lemma cnob_pjf_step : forall (fz : YK11.FPState) D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl
    off st offs sts F Fs E Es cs raw (P : (word -> option byte) -> Prop),
  srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fz ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl (off :: offs) (st :: sts) (F :: Fs)
    (E :: Es) cs ->
  getr regs 10 = w64 (cnb_F D + off) -> getr regs 1 = raw -> YK0s.ret_ok raw ->
  4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 (SIGMA AS_pj_free)) mem (YK11.seg_rom SEGS)) md)
    (fun W2 c2 => (exists ly2 S2 Hp2 regs2 mem2 md2 k2 Lam2,
        c2 = mkCfg (@YK11.mkst fz regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
        aregs_preserved regs regs2 /\
        cnob_fmid D fz ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl offs sts Fs Es cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fz D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl off st offs sts F Fs E Es cs raw P PCALL
  HPRE HM Ha0 Hra Hret Hra4 HraC HPM.
pose proof HM as (HBASE & HREG & HSLOTS & HRL & HC24 & HPROG & HLED & Hpk & Hcnt & Hlen & Hoffs & Hsort &
  Hopens & Hfos & Htevs & Hcps & HpermL & HpermB & Hfresh & HHB).
cbn [flat_map] in HpermL, HpermB, Hfresh. rewrite <- app_assoc in HpermL.
pose proof HBASE as (Hfrm & Hfreg & HJ & HFRAME & HSAVED & Hgp & Htp & HROD).
pose proof HFRAME as (Hfrs & Hnfr & Hflag & _ & _).
pose proof (cnb_J_rebaseR B ARcfx WLE' D 6 ly S Hp W mem md k HJ) as HJr.
pose proof (ajxR_ar HJr) as HAR. pose proof (ajxR_ly HJr) as Hlyle. pose proof (ajxR_stk HJr) as HSTK.
pose proof Hlyle as (_ & _ & _ & _ & _ & LF & _ & _ & _ & _ & Lshi & _).
pose proof HSTK as (Hsp16 & HSTKge & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
pose proof HPRE as (HFPRE & _ & HCL & _).
pose proof HFPRE as (HAFN & HROD0 & _).
pose proof HAFN as (_ & _ & _ & Hgp0 & Htp0 & _).
destruct (cnb_S1_bounds D Hsp16) as (HS1a & HS1b & HS132).
pose proof asan_consts as (C1 & _).
pose proof cnob_fb as HFB. pose proof cnob_stk_pjf as (HSTKp & HSTKp0). pose proof cnob_cf_head as Hcf.
assert (Hin : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HFA : frame_addr ly CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite LF; reflexivity).
pose proof (alx_frames SEGS B ARcfx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin) as (Hal32 & Happ & _).
rewrite HFA in Hal32, Happ. rewrite HFB in Happ.
pose proof (alx_sep SEGS B ARcfx LAWS ly S Hp W mem md HAR) as (_ & Hsepf).
rewrite Forall_forall in Hsepf. destruct (Hsepf (CNB_CID, bi_fpos D) Hin) as (HF4096 & HFceil).
cbn [fst snd] in HF4096, HFceil. rewrite HFA in HF4096, HFceil. rewrite HFB in HFceil.
pose proof (Forall_inv Hoffs) as (Hoffa & Hoffb & Hoff8 & Hoff32). rewrite HFB in Hoffb.
(* registers at the call *)
assert (Rof : forall rr vv, In (rr, vv) (cnb_core D ++ [(24%bv, r); (25%bv, r1)]) -> getr regs rr = w64 vv)
  by (intros rr vv Hi; unfold cnb_regsat in HREG; rewrite Forall_forall in HREG; exact (HREG (rr, vv) Hi)).
assert (R2 : getr regs 2 = w64 (cnb_S1 D)) by (apply Rof; unfold cnb_core; cbn [app In]; left; reflexivity).
assert (R8 : getr regs 8 = w64 (cnb_sp0 D)) by (apply Rof; unfold cnb_core; cbn [app In]; right; left; reflexivity).
assert (HspZ : spZ regs = cnb_S1 D) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0Z : s0Z regs = cnb_sp0 D) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
destruct (cnob_chain D 6 ly S Hp W mem md k HJ HSAVED HAFN HS1a) as (ch1 & Hch1 & _).
cbn [combine] in Hfos.
destruct (cnob_F2_cons _ _ _ _ _ Hfos) as (HFO & Hfos'). cbn [fst snd] in HFO.
destruct (cnob_F2_cons _ _ _ _ _ Htevs) as (HTE & Htevs').
pose proof (Forall_inv Hopens) as Hopen0.
assert (HSL := cnob_slot D ly S Hp W regs mem md Lam off HAR Hin HFA ltac:(lia) ltac:(rewrite HFB; lia) Hoff8
  HspZ (cnob_astk_le _ _ _ _ _ Hlyle HSTK) HS1b Hopen0).
assert (HDt : forall b kk, In (b, kk) (cnb_Dof st ++ flat_map cnb_Dof sts) ->
    In (b - cf_head, kk + cf_head) (ablocks B ly S)).
{ intros b kk Hbk. apply (Permutation_in _ (Permutation_sym HpermB)). apply in_or_app. right. apply in_or_app. left.
  unfold ck_hblks. exact (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) _ (b, kk) Hbk). }
assert (HFS := cnob_fp_sub D ly S (flat_map (cnb_cblk D) cs) (cnb_Dof st ++ flat_map cnb_Dof sts) off (cnb_Dof st)
  HpermB Hfresh HFA ltac:(lia) ltac:(rewrite HFB; lia) (fun a kk H => in_or_app _ _ _ (or_introl H))).
eapply SRr'_mono.
{ eapply (cnob_pjfree_call fz STK (cnb_sp0 D) (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D)
    (bi_md D) [(CNB_CID, bi_fpos D)] ly S Hp W regs mem md k (cnb_F D + off) (cnb_Dof st) F Lam peak cnt ran
    (bi_most D) ownl ch1 raw P PCALL HJr).
  - rewrite HspZ. lia.
  - rewrite HspZ. lia.
  - rewrite HspZ. lia.
  - rewrite Hgp. exact Hgp0.
  - rewrite Htp. exact Htp0.
  - exact Hra.
  - exact Hret.
  - exact Hra4.
  - exact HraC.
  - exact Ha0.
  - rewrite HspZ, Hs0Z. exact Hch1.
  - exact HROD.
  - rewrite HspZ, Lshi. lia.
  - exact Hfrm.
  - exact HCL.
  - exact HRL.
  - exact HC24.
  - exact (PresetHullBudget.hull_budget_nil S _ HHB).
  - lia.
  - lia.
  - exact HFO.
  - exact HSL.
  - exact HLED.
  - exact HFS.
  - exact HPM. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HP2 & HK & HPM2).
split; [|exact HPM2].
(* pj_free's post (tpfP_Q, the text's Q) read through the kit's named projections (tpfP_R_of, tpfP_R's fields) *)
apply tpfP_R_of in HK. destruct HK as (Lam2 & HKR).
pose proof (tpfP_room HKR) as HRL2. pose proof (tpfP_hull HKR) as HHU. pose proof (tpfP_pos HKR) as HPOS2.
pose proof (tpfP_lam HKR) as HpL. pose proof (tpfP_ablocks HKR) as HpB. pose proof (tpfP_ledger HKR) as HLED2.
pose proof (tpfP_ccnt24 HKR) as Hc24le.
exists ly2, S2, Hp2, regs2, mem2, md2, (k + k1), Lam2.
split; [reflexivity|]. split; [exact HP2|].
(* the state after the call *)
pose proof (ajxR_ar HJ2) as HAR2. pose proof (ajxR_ly HJ2) as Hlyle2. pose proof (ajxR_frs HJ2) as Hfrs2.
pose proof (cnb_J_fixedR B ARcfx WLE' D 6 ly S Hp W mem md k ly2 S2 Hp2 W2 mem2 md2 (k + k1) HJ HJ2) as HJ2w.
pose proof Hlyle2 as (_ & _ & _ & _ & _ & LF2 & _).
assert (HFA2 : frame_addr ly2 CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite LF2; reflexivity).
assert (Hin2 : In (CNB_CID, bi_fpos D) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp2 W2 mem2 md2 CNB_CID (bi_fpos D) HAR2 Hin2) as (_ & _ & Hby2 & Hsh2).
rewrite HFA2, HFB in Hby2, Hsh2.
pose proof (ajxR_hi HJ1) as K1.
(* a frame byte or a frame shadow byte that is not the freed struct is kept *)
assert (KF : forall a, (cnb_F D <= a < cnb_F D + 512 \/ shadow_addr (cnb_F D) <= a < shadow_addr (cnb_F D) + 64) ->
    ~ (cnb_F D + off <= a < cnb_F D + off + 56) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hns. exact (cnob_frame_keep D ly S Hp W mem md _ _ off (cnb_Dof st) ly2 S2 Hp2 W2 mem2 md2 k1 a HAR HJ1
    Hin HFA (fun b kk H => HDt b kk (in_or_app _ _ _ (or_introl H))) Ha Hns). }
(* a shadow byte of the frame is never a byte of the struct *)
assert (KS : forall a, shadow_addr (cnb_F D) <= a < shadow_addr (cnb_F D) + 64 ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KF; [right; exact Ha|]. intros Hs. exact (cnob_band (cnb_F D) 512 (cnb_F D) a Happ Happ ltac:(lia) Ha). }
(* a real-stack byte at or above s1 is kept *)
assert (KR : forall a, cnb_S1 D <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply K1; [lia | rewrite HspZ; lia]. }
(* the ledger's lists after the call *)
assert (Hnd : List.NoDup (map fst Lam)) by (apply NoDup_ListNoDup; eapply prh_ledger_nodup; exact HLED).
assert (HB0 : Forall (fun ak => prh_hblock B ly S Hp W mem (fst ak) (snd ak)) Lam) by (eapply prh_ledger_blocks; exact HLED).
rewrite Forall_forall in HB0.
assert (HLam2 : forall b kk, In (b, kk) (flat_map cnb_Dof sts) -> In (b, kk) Lam2).
{ intros b kk Hb. assert (HinL : In (b, kk) Lam).
  { apply (Permutation_in _ (Permutation_sym HpermL)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
  pose proof (Permutation_in _ HpL HinL) as H1. apply in_app_or in H1 as [H1 | H1]; [|exact H1].
  exfalso. exact (cnob_nodup_first Lam (cnb_Dof st) (flat_map cnb_Dof sts ++ bi_Lam D) b kk Hnd HpermL
    (in_or_app _ _ _ (or_introl Hb)) b kk H1 eq_refl). }
split.
{ (* cnb_baseR at wle' *)
  split; [exact Hfrm|]. split; [exact Hfreg|]. split; [exact HJ2w|].
  split.
  { split; [exact Hfrs2|]. split; [exact Hnfr|].
    split.
    { unfold flag_addr in Hflag |- *. rewrite LF2. rewrite LF in Hflag. rewrite HFB in Hflag |- *.
      eapply cnob_rdword_keep; [intros i Hi; apply KF; [left; lia | lia] | exact Hflag]. }
    split.
    { intros a Ha. rewrite HFB in Ha. exact (proj1 (Hby2 a Ha)). }
    { intros a Ha. rewrite HFB in Ha. replace a with (shadow_addr (cnb_F D) + (a - shadow_addr (cnb_F D))) by lia.
      apply (proj1 (Hsh2 (a - shadow_addr (cnb_F D)) ltac:(change (512 / 8) with 64; change (512 / 8) with 64 in Ha; lia))). } }
  split.
  { unfold cnb_saved in HSAVED |- *. rewrite Forall_forall in HSAVED |- *. intros p0 Hp0.
    assert (Hpb : 56 <= fst p0 <= 152) by (cbn in Hp0; repeat (destruct Hp0 as [<- | Hp0]; [cbn; lia|]); destruct Hp0).
    eapply cnob_rdword_keep; [intros i Hi; apply KR; lia | exact (HSAVED p0 Hp0)]. }
  split; [rewrite (psc_preserved_reg_b regs regs2 3%bv HP2 ltac:(cnob_cs)); exact Hgp|].
  split; [rewrite (psc_preserved_reg_b regs regs2 4%bv HP2 ltac:(cnob_cs)); exact Htp|].
  eapply cnob_arodata_J; [exact HJ2 | exact HROD0]. }
split; [exact (cnob_regsat_keep D r r1 regs regs2 HP2 HREG)|].
split.
{ unfold cnb_slots in HSLOTS |- *. rewrite Forall_forall in HSLOTS |- *. intros p0 Hp0.
  assert (Hpb : 16 <= fst p0 <= 48) by (cbn in Hp0; repeat (destruct Hp0 as [<- | Hp0]; [cbn; lia|]); destruct Hp0).
  eapply cnob_rdword_keep; [intros i Hi; apply KR; lia | exact (HSLOTS p0 Hp0)]. }
split; [exact HRL2|].
split; [clear - HC24 Hc24le; lia|].
split.
{ (* the progress fact: this struct's events are made (pj_free's exact advance, or the model's empty bulk stepped
     over), the rest is still to come *)
  intros H0. destruct (HPROG H0) as (o1 & o2 & o0 & E0 & Hran & Hprog & Heq).
  exists o1, o2, o0, (E0 ++ E). split; [exact Hran|].
  split.
  - assert (HpBs : Permutation (map snd (blocks S))
        (map (fun b => snd b + cf_head) (cnb_Dof st) ++ map snd (blocks S2))).
    { rewrite <- (cnob_blocks_snd B ly S), <- (cnob_blocks_snd B ly2 S2).
      replace (map (fun b => snd b + cf_head) (cnb_Dof st)) with (map snd (prhPj_hbl (cnb_Dof st)))
        by (unfold prhPj_hbl; rewrite map_map; reflexivity).
      rewrite <- map_app. apply Permutation_map. exact HpB. }
    exact (cnob_prog_pjf D E0 E S S2 (cnb_Dof st) F Hprog HpBs
      (proj2 (pj_foR_fdR SEGS _ _ _ _ _ _ HFO)) HTE HPOS2).
  - rewrite <- Heq. cbn [concat]. rewrite <- !app_assoc. reflexivity. }
split; [exact HLED2|].
split; [exact Hpk|]. split; [exact Hcnt|].
split; [cbn [length] in Hlen; lia|].
split; [exact (Forall_inv_tail Hoffs)|].
split; [exact (proj1 (StronglySorted_inv Hsort))|].
pose proof (StronglySorted_inv Hsort) as (_ & Hsort0). rewrite Forall_forall in Hsort0.
pose proof (Forall_inv_tail Hoffs) as Hoffs'. rewrite Forall_forall in Hoffs'.
split.
{ pose proof (Forall_inv_tail Hopens) as Ho'. rewrite Forall_forall in Ho' |- *. intros o Ho.
  destruct (Hoffs' o Ho) as (Hoa & Hob & _ & Hoc). rewrite HFB in Hob.
  exact (cnob_open_keep (cnb_F D) o (aview SEGS (w_H W) mem) (aview SEGS (w_H W2) mem2) Hal32 Hoa Hob Hoc KS (Ho' o Ho)). }
split.
{ (* the trees still to free: same bytes (footprint kept), and their blocks stay in the ledger list *)
  assert (Hgen : forall ps Fs0, (forall p, In p ps -> In (fst p) offs /\ In (snd p) sts) ->
     Forall2 (fun p F0 => pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D (cnb_F D + fst p) (cnb_Dof (snd p)) F0) ps Fs0 ->
     Forall2 (fun p F0 => pj_foR SEGS (rdW W2 mem2) (prh_lin Lam2) DOC_D (cnb_F D + fst p) (cnb_Dof (snd p)) F0)
       ps Fs0).
  { intros ps Fs0 Hps H. induction H as [|[o t] F0 ps1 Fs1 Hot H IH]; [apply Forall2_nil|].
    apply Forall2_cons; [|apply IH; intros p' Hp'; apply Hps; right; exact Hp'].
    destruct (Hps (o, t) (or_introl eq_refl)) as (Ho & Ht). cbn [fst snd] in Ho, Ht, Hot |- *.
    assert (HtD : forall b kk, In (b, kk) (cnb_Dof t) -> In (b, kk) (flat_map cnb_Dof sts))
      by (intros b kk Hbk; apply in_flat_map; exists t; split; [exact Ht | exact Hbk]).
    destruct (Hoffs' o Ho) as (Hoa & Hob & _ & _). rewrite HFB in Hob.
    pose proof (Hsort0 o Ho) as Hsep.
    apply (pj_foR_frame SEGS DOC_D (rdW W mem) (rdW W2 mem2) (prh_lin Lam) (prh_lin Lam2) (cnb_F D + o) (cnb_Dof t)
      F0 Hot).
    { intros b kk Hbk. unfold prh_lin. exact (HLam2 b kk (HtD b kk Hbk)). }
    intros x Hx. destruct Hx as [Hx | ((b, kk) & Hbk & Hx)].
    - (* the header: a frame byte after the freed struct *)
      split.
      + apply mbyte_of_aview. apply KF; [left; lia | lia].
      + intros _. apply apresent_writable. exact (proj1 (Hby2 x ltac:(lia))).
    - (* a block of the tree: a live block that is no block of the freed tree *)
      unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      assert (HbL : In (b, kk) Lam).
      { apply (Permutation_in _ (Permutation_sym HpermL)). apply in_or_app. right. apply in_or_app. left.
        exact (HtD b kk Hbk). }
      destruct (HB0 (b, kk) HbL) as (Hkk & Hblk & _). cbn [fst snd] in Hkk, Hblk.
      assert (Hne : forall b0 kk0, In (b0, kk0) (cnb_Dof st) -> b0 <> b)
        by (exact (cnob_nodup_first Lam (cnb_Dof st) (flat_map cnb_Dof sts ++ bi_Lam D) b kk Hnd HpermL
                     (in_or_app _ _ _ (or_introl (HtD b kk Hbk))))).
      assert (Hblk2 : In (b - cf_head, kk + cf_head) (ablocks B ly2 S2)).
      { pose proof (Permutation_in _ HpB Hblk) as H1. apply in_app_or in H1 as [H1 | H1]; [|exact H1].
        exfalso. unfold prhPj_hbl in H1. apply in_map_iff in H1 as ((b0, kk0) & E0 & H0). cbn [fst snd] in E0.
        injection E0 as E1 E2. apply (Hne b0 kk0 H0). lia. }
      pose proof (req_size_pos (kk + cf_head) (Z.add_nonneg_nonneg _ _ Hkk Hcf)) as (_ & Hrs).
      split.
      + apply mbyte_of_aview.
        exact (cnob_block_keep D ly S Hp W mem md _ _ off (cnb_Dof st) ly2 S2 Hp2 W2 mem2 md2 k1 b kk x HAR HJ1 Hin
          HFA ltac:(lia) ltac:(lia) (fun b0 kk0 H => HDt b0 kk0 (in_or_app _ _ _ (or_introl H))) Hne Hblk Hblk2 Hkk Hx).
      + intros _. apply apresent_writable.
        pose proof (alx_blocks SEGS B ARcfx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hblk2) as (_ & _ & _ & _ & Hpb2 & _).
        exact (proj1 (Hpb2 x ltac:(lia))). }
  assert (Hps : forall p, In p (combine offs sts) -> In (fst p) offs /\ In (snd p) sts).
  { intros [a b] Hab. cbn [fst snd]. split; [exact (in_combine_l _ _ _ _ Hab) | exact (in_combine_r _ _ _ _ Hab)]. }
  exact (Hgen (combine offs sts) Fs Hps Hfos'). }
split; [exact Htevs'|].
split.
{ (* the copies: no copy became a harness base (the call only removed harness blocks) *)
  rewrite Forall_forall in Hcps |- *.
  intros c Hc Hc0 Hin2'. apply (Hcps c Hc Hc0).
  assert (HH2 : Permutation Hp2 (map (fun ak => fst ak - cf_head) Lam2)) by (eapply prh_ledger_heads; exact HLED2).
  assert (HH : Permutation Hp (map (fun ak => fst ak - cf_head) Lam)) by (eapply prh_ledger_heads; exact HLED).
  apply (Permutation_in _ HH2) in Hin2'. apply in_map_iff in Hin2' as (ak & Eak & Hak).
  apply (Permutation_in _ (Permutation_sym HH)). apply in_map_iff. exists ak. split; [exact Eak|].
  apply (Permutation_in _ (Permutation_sym HpL)). apply in_or_app. right. exact Hak. }
split.
{ apply (Permutation_app_inv_l (cnb_Dof st)).
  eapply Permutation_trans; [apply Permutation_sym; exact HpL | exact HpermL]. }
split.
{ unfold ck_hblks at 1 in HpermB. rewrite map_app in HpermB. fold (ck_hblks (cnb_Dof st)) in HpermB.
  fold (ck_hblks (flat_map cnb_Dof sts)) in HpermB.
  exact (cnob_perm_cancel (flat_map (cnb_cblk D) cs) (ck_hblks (cnb_Dof st)) (ck_hblks (flat_map cnb_Dof sts))
    (ablocks B (bi_ly D) (bi_S D)) (ablocks B ly2 S2) (ablocks B ly S) HpB HpermB). }
split; [intros a kk Hak; exact (Hfresh a kk (in_or_app _ _ _ (or_intror Hak)))|].
(* the hull budget: pj_free used nothing, the rest of the suffix is left *)
exact (cnob_hull_pj D off offs S S2 HHB HHU).
Qed.

(* ==== STEP (B): ONE RUNTIME __wrap_free OF A PADDED COPY. Its pieces first: the call trace is in the universe (the
   three free sites are RT_free return sites of check_no_overread in the kit's generated B' cells), and the cells and the
   ledger the free does not touch are kept ==== *)
(* a membership in a closed list, decided by a boolean on the closed goal *)
Lemma cnob_in_of_b : forall (x : Z) (l : list Z), existsb (Z.eqb x) l = true -> In x l.
Proof.
intros x l H. apply existsb_exists in H as (y & Hy & Ey). apply Z.eqb_eq in Ey. subst. exact Hy.
Qed.
Lemma cnob_site_fr1 : In (B_prog_base + CNB_OFF + CNB_FR1) (pi_ret_sites F_check_no_overread RT_free).
Proof. apply cnob_in_of_b. vm_compute. reflexivity. Qed.
Lemma cnob_site_fr2 : In (B_prog_base + CNB_OFF + CNB_FR2) (pi_ret_sites F_check_no_overread RT_free).
Proof. apply cnob_in_of_b. vm_compute. reflexivity. Qed.
Lemma cnob_site_fr3 : In (B_prog_base + CNB_OFF + CNB_FR3) (pi_ret_sites F_check_no_overread RT_free).
Proof. apply cnob_in_of_b. vm_compute. reflexivity. Qed.
Lemma cnob_fp_cno : pi_fp F_check_no_overread = true.
Proof. vm_compute. reflexivity. Qed.
(* the call trace of a free from this frame is in the universe *)
Lemma cnob_trace_in : forall D regs ch1 r ly,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  (ch1 = [] \/ ch1 = (cnb_sp0 D, raZ (bi_regs D), s0Z (bi_regs D)) :: bi_ch D) ->
  raZ regs = r -> In r (pi_ret_sites F_check_no_overread RT_free) ->
  In (call_trace ly (pc_free_ra0 (as_code B)) regs ch1) (as_universe B).
Proof.
intros D regs ch1 r ly HPRE Hch Hra Hsite.
pose proof HPRE as (_ & _ & HCL & HCTX & _).
pose proof HCL as (Hpc0 & Hnil & _).
apply call_trace_in; [exact (Hpc0 RT_free)|].
rewrite call_trace_of_spine. rewrite Hra.
change (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun ra => if ra =? pc_free_ra0 (as_code B) then [] else [ra])
  (r :: spine ch1))) with (prh_trace (prh_pc0 B RT_free) r (spine ch1)).
destruct Hch as [-> | ->].
- exact (Hnil F_check_no_overread RT_free r Hsite).
- change (spine ((cnb_sp0 D, raZ (bi_regs D), s0Z (bi_regs D)) :: bi_ch D))
    with (raZ (bi_regs D) :: spine (bi_ch D)).
  exact (prh_univ_closure_site B CTX0 F_check_no_overread _ RT_free r HCL HCTX cnob_fp_cno Hsite).
Qed.
(* a value cell whose bytes the view keeps *)
Lemma cnob_cell_keep : forall (W W2 : world SEGS) mem mem2 a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) ->
  val_mem SEGS (rdW W mem) a n v -> val_mem SEGS (rdW W2 mem2) a n v.
Proof.
intros W W2 mem mem2 a n v Hk Hv. apply (pj_valR_frame SEGS (rdW W mem) (rdW W2 mem2) a n v Hv).
intros x Hx. apply mbyte_of_aview. exact (Hk x Hx).
Qed.
(* the runtime free keeps every program static (cnbi_pst_ok: an image byte no owned static; cnbi_pst_errno: no errno
   byte), through acall_kept's image clause *)
Lemma cnob_pst_keep : forall ly S (W W2 : world SEGS) mem mem2 slo shi E,
  acall_kept_x SEGS B ly S W mem W2 mem2 slo shi E ->
  forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a.
Proof.
intros ly S W W2 mem mem2 slo shi E HK a Ha.
pose proof HK as (_ & _ & K3 & _).
destruct (cnbi_pst_ok B IMG a Ha) as (Himg & Hown).
exact (K3 a Himg Hown (CN_PST_ERRNO a Ha)).
Qed.
(* each value cell of prh_glob / own / most is a program static *)
Lemma cnob_pst_at : forall x a z, In (a, z) prh_pst -> a <= x < a + z -> Exists (in_zr x) prh_pst.
Proof. intros x a z Hin Hx. apply Exists_exists. exists (a, z). split; [exact Hin | unfold in_zr; cbn [fst snd]; exact Hx]. Qed.
Ltac cnob_pst_cell := lazymatch goal with H : ?a <= ?x < ?a + Z.of_nat ?z |- Exists (in_zr ?x) _ =>
  apply (cnob_pst_at x a (Z.of_nat z)); [unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right]) | exact H]
end.
Lemma cnob_own_keep : forall (W W2 : world SEGS) mem mem2 o,
  (forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  prh_own W mem o -> prh_own W2 mem2 o.
Proof.
intros W W2 mem mem2 o Hk (G & Go). split; [|exact Go].
apply (cnob_cell_keep W W2 mem mem2 pi_g_own_ran_out pi_gz_own_ran_out o (fun x Hx => Hk x ltac:(cnob_pst_cell)) G).
Qed.
Lemma cnob_most_keep : forall (W W2 : world SEGS) mem mem2 m,
  (forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  prh_most W mem m -> prh_most W2 mem2 m.
Proof.
intros W W2 mem mem2 m Hk (G & Gm). split; [|exact Gm].
apply (cnob_cell_keep W W2 mem mem2 pi_g_most pi_gz_most m (fun x Hx => Hk x ltac:(cnob_pst_cell)) G).
Qed.
(* the statics' cells, g_most and g_own_ran_out among them (Batch 2: fields of prh_glob), survive a call that keeps
   every program static *)
Lemma cnob_glob_keep : forall (W W2 : world SEGS) mem mem2 live peak cnt fail ran most own,
  (forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  prh_glob W mem live peak cnt fail ran most own -> prh_glob W2 mem2 live peak cnt fail ran most own.
Proof.
intros W W2 mem mem2 live peak cnt fail ran most own Hk (G1 & G2 & G3 & G4 & G5 & Gm & Go & G8).
split; [apply (cnob_cell_keep W W2 mem mem2 pi_g_live pi_gz_live live (fun x Hx => Hk x ltac:(cnob_pst_cell)) G1)|].
split; [apply (cnob_cell_keep W W2 mem mem2 pi_g_peak pi_gz_peak peak (fun x Hx => Hk x ltac:(cnob_pst_cell)) G2)|].
split; [apply (cnob_cell_keep W W2 mem mem2 pi_g_count pi_gz_count cnt (fun x Hx => Hk x ltac:(cnob_pst_cell)) G3)|].
split; [apply (cnob_cell_keep W W2 mem mem2 pi_g_fail pi_gz_fail fail (fun x Hx => Hk x ltac:(cnob_pst_cell)) G4)|].
split; [apply (cnob_cell_keep W W2 mem mem2 pi_g_ran_out pi_gz_ran_out ran (fun x Hx => Hk x ltac:(cnob_pst_cell)) G5)|].
split; [exact (cnob_most_keep W W2 mem mem2 most Hk Gm)|].
split; [exact (cnob_own_keep W W2 mem mem2 own Hk Go)|].
exact G8.
Qed.
(* the ledger survives a call that keeps the statics, every harness block, and each block's head word; read through
   PRH_Base's named projections *)
Lemma cnob_ledger_keep : forall ly S Hp (W : world SEGS) mem ly2 S2 (W2 : world SEGS) mem2 Lam peak cnt fail ran
    most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  (forall a kk, In (a, kk) Lam -> In (a - cf_head, kk + cf_head) (ablocks B ly2 S2)) ->
  (forall a kk x, In (a, kk) Lam -> a - cf_head <= x < a - cf_head + Z.of_nat 8 ->
     aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) ->
  prh_ledger B ly2 S2 Hp W2 mem2 Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem ly2 S2 W2 mem2 Lam peak cnt fail ran most own HLED Hk Hb Hw.
assert (G : prh_glob W mem (Ledger.lsum Lam) peak cnt fail ran most own) by (eapply prh_ledger_glob; exact HLED).
assert (Nd : NoDup (map fst Lam)) by (eapply prh_ledger_nodup; exact HLED).
assert (Bl : Forall (fun ak => prh_hblock B ly S Hp W mem (fst ak) (snd ak)) Lam)
  by (eapply prh_ledger_blocks; exact HLED).
assert (Hh : Permutation Hp (map (fun ak => fst ak - cf_head) Lam)) by (eapply prh_ledger_heads; exact HLED).
split; [exact (cnob_glob_keep W W2 mem mem2 _ _ _ _ _ _ _ Hk G)|].
split; [exact Nd|]. split; [|exact Hh].
rewrite Forall_forall in Bl |- *. intros [a kk] Hak. destruct (Bl (a, kk) Hak) as (B1 & _ & B3 & B4 & B5).
cbn [fst snd] in *. split; [exact B1|]. split; [exact (Hb a kk Hak)|]. split; [exact B3|]. split; [exact B4|].
apply (cnob_cell_keep W W2 mem mem2 (a - cf_head) 8 kk (fun x Hx => Hw a kk x Hak ltac:(first [exact Hx | change (Z.of_nat 8) with 8 in Hx; exact Hx | idtac Hx; fail])) B5).
Qed.

Lemma cnob_wfr_step : forall (fz : YK11.FPState) D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl
    c cs raw (P : (word -> option byte) -> Prop),
  srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fz ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] (c :: cs) ->
  getr regs 10 = w64 c -> getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  In (bv_unsigned raw) (pi_ret_sites F_check_no_overread RT_free) ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 (SIGMA AS___wrap_free)) mem (YK11.seg_rom SEGS)) md)
    (fun W2 c2 => (exists ly2 S2 regs2 mem2 md2 k2,
        c2 = mkCfg (@YK11.mkst fz regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
        aregs_preserved regs regs2 /\
        cnob_fmid D fz ly2 S2 Hp W2 regs2 mem2 md2 k2 Lam peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fz D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl c cs raw P PCALL HPRE HM
  Ha0 Hra Hret Hra4 Hsite HPM.
pose proof HM as (HBASE & HREG & HSLOTS & HRL & HC24 & HPROG & HLED & Hpk & Hcnt & _ & _ & _ & _ & _ & _ &
  Hcps & HpermL & HpermB & _ & HHB).
cbn [flat_map ck_hblks map app] in HpermB.
pose proof HBASE as (Hfrm & Hfreg & HJ & HFRAME & HSAVED & Hgp & Htp & HROD).
pose proof HFRAME as (Hfrs & Hnfr & Hflag & _ & _).
pose proof (cnb_J_rebaseR B ARcfx WLE' D 6 ly S Hp W mem md k HJ) as HJr.
pose proof (ajxR_ar HJr) as HAR. pose proof (ajxR_ly HJr) as Hlyle. pose proof (ajxR_stk HJr) as HSTK.
pose proof Hlyle as (_ & _ & _ & _ & _ & LF & _).
pose proof HSTK as (Hsp16 & HSTKge & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
pose proof HPRE as (HFPRE & _ & HCL & _).
pose proof HFPRE as (HAFN & HROD0 & _).
pose proof HAFN as (_ & _ & _ & Hgp0 & Htp0 & _).
destruct (cnb_S1_bounds D Hsp16) as (HS1a & HS1b & HS132).
pose proof asan_consts as (C1 & _).
pose proof cnob_fb as HFB. pose proof cnob_stk_free as HSTKf. pose proof cnob_cf_head as Hcf.
assert (EA : ASTACK = 16384) by reflexivity.
assert (Hcf8 : 8 <= cf_head) by exact HWIDE.
assert (Hin : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HFA : frame_addr ly CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite LF; reflexivity).
pose proof (alx_sep SEGS B ARcfx LAWS ly S Hp W mem md HAR) as (Hsep & _).
assert (Rof : forall rr vv, In (rr, vv) (cnb_core D ++ [(24%bv, r); (25%bv, r1)]) -> getr regs rr = w64 vv)
  by (intros rr vv Hi; unfold cnb_regsat in HREG; rewrite Forall_forall in HREG; exact (HREG (rr, vv) Hi)).
assert (R2 : getr regs 2 = w64 (cnb_S1 D)) by (apply Rof; unfold cnb_core; cbn [app In]; left; reflexivity).
assert (R8 : getr regs 8 = w64 (cnb_sp0 D)) by (apply Rof; unfold cnb_core; cbn [app In]; right; left; reflexivity).
assert (HspZ : spZ regs = cnb_S1 D) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0Z : s0Z regs = cnb_sp0 D) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
destruct (cnob_chain D 6 ly S Hp W mem md k HJ HSAVED HAFN HS1a) as (ch1 & Hch1 & Hchs).
set (n := cnb_size D + 16).
assert (Hnd : List.NoDup (ablocks B ly S)) by exact (cnob_ablocks_nodup ly S Hp W mem md HAR).
(* the copy: NULL, or its runtime block (live now, not at the entry, no harness base) *)
assert (Hcopy : c = 0 /\ ~ In 0 Hp \/
   c <> 0 /\ In (c, n) (ablocks B ly S) /\ ~ In (c, n) (ablocks B (bi_ly D) (bi_S D)) /\ ~ In c Hp).
{ destruct (Z.eq_dec c 0) as [Ec | Ec].
  - left. split; [exact Ec | exact (cnob_hp_no0 ly S Hp W mem md Lam peak cnt SIZE_MAXZ ran _ _ HAR HLED)].
  - right. assert (Hcb : cnb_cblk D c = [(c, n)]) by (unfold cnb_cblk, n; rewrite (proj2 (Z.eqb_neq c 0) Ec); reflexivity).
    rewrite Hcb in HpermB.
    assert (HinR : In (c, n) (((c, n) :: flat_map (cnb_cblk D) cs) ++ ablocks B (bi_ly D) (bi_S D)))
      by (left; reflexivity).
    split; [exact Ec|]. split; [exact (Permutation_in _ (Permutation_sym HpermB) HinR)|].
    split.
    + apply (cnob_nodup_app_disj ((c, n) :: flat_map (cnb_cblk D) cs)); [|left; reflexivity].
      exact (Permutation_NoDup HpermB Hnd).
    + exact (Forall_inv Hcps Ec). }
(* the free's admission from the carried hull budget, and the call memory's RELRO fact *)
assert (HOK : cf_hull_ok S) by exact (PresetHullPay.hull_ok_of_budget S _ HHB).
pose proof (cnob_aro_cf D 6 ly S Hp W mem md k HPRE HJ) as HARO.
eapply SRr'_mono.
{ eapply (cnob_wfree_call fz STK (cnb_sp0 D) (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D)
    (bi_md D) [(CNB_CID, bi_fpos D)] ly S Hp W regs mem md k c n raw ch1 P PCALL HJr).
  - rewrite HspZ. lia.
  - rewrite HspZ. lia.
  - rewrite HspZ. lia.
  - rewrite Hgp. exact Hgp0.
  - rewrite Htp. exact Htp0.
  - exact Hra.
  - exact Hret.
  - exact Ha0.
  - exact Hcopy.
  - exact HRL.
  - exact HC24.
  - exact HOK.
  - exact HARO.
  - eapply achain_chain_pre; [exact Hch1 | rewrite HspZ; lia | exact Hs0Z | unfold raZ; rewrite Hra; exact Hra4].
  - exact (cnob_trace_in D regs ch1 (bv_unsigned raw) ly HPRE Hchs ltac:(unfold raZ; rewrite Hra; reflexivity) Hsite).
  - exact HPM. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HpB & Hfr2 & HSS & HK & HRL2 & Hc24le & HRP2 &
  HPM2).
split; [|exact HPM2].
exists ly2, S2, regs2, mem2, md2, (k + (st_nev S2 - st_nev S)).
split; [reflexivity|]. split; [exact HP2|].
pose proof (ajxR_ar HJ2) as HAR2. pose proof (ajxR_ly HJ2) as Hlyle2.
pose proof (cnb_J_fixedR B ARcfx WLE' D 6 ly S Hp W mem md k ly2 S2 Hp W2 mem2 md2 (k + (st_nev S2 - st_nev S)) HJ HJ2)
  as HJ2w.
pose proof Hlyle2 as (_ & _ & _ & _ & _ & LF2 & _).
assert (HFA2 : frame_addr ly2 CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite LF2; reflexivity).
assert (Hin2 : In (CNB_CID, bi_fpos D) (frames S2)) by (rewrite Hfr2; exact Hin).
pose proof (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp W2 mem2 md2 CNB_CID (bi_fpos D) HAR2 Hin2) as (_ & _ & Hby2 & Hsh2).
rewrite HFA2, HFB in Hby2, Hsh2.
pose proof HK as (K1 & K2 & _ & K4 & _).
(* the copy block is apart from the frame and from every other live block *)
assert (HcF : forall a, cnb_F D <= a < cnb_F D + 512 -> ~ (c <> 0 /\ c <= a < c + req_size n)).
{ intros a Ha (Hc0 & Hca). destruct Hcopy as [(Ec & _) | (_ & Hcin & _)]; [exact (Hc0 Ec)|].
  assert (Hzd : zdisjoint (c, req_size n) (frame_addr ly CNB_CID (bi_fpos D), fs_frame_bytes CNB_CID)).
  { apply (cnob_pairwise_app zdisjoint _ _ _ _ Hsep).
    - apply in_map_iff. exists (c, n). split; [reflexivity | exact Hcin].
    - apply in_map_iff. exists (CNB_CID, bi_fpos D). split; [reflexivity | exact Hin]. }
  unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite HFA, HFB in Hzd. lia. }
assert (KF : forall a, cnb_F D <= a < cnb_F D + 512 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (K4 CNB_CID (bi_fpos D) a Hin); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite HFA, HFB; lia|].
  exact (HcF a Ha). }
assert (KR : forall a, cnb_S1 D <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply K1; [lia | rewrite HspZ; lia]. }
assert (KP := cnob_pst_keep ly S W W2 mem mem2 _ _ _ HK).
split.
{ split; [exact Hfrm|]. split; [exact Hfreg|]. split; [exact HJ2w|].
  split.
  { split; [rewrite Hfr2; exact Hfrs|]. split; [exact Hnfr|].
    split.
    { unfold flag_addr in Hflag |- *. rewrite LF2. rewrite LF in Hflag. rewrite HFB in Hflag |- *.
      eapply cnob_rdword_keep; [intros i Hi; apply KF; lia | exact Hflag]. }
    split.
    { intros a Ha. rewrite HFB in Ha. exact (proj1 (Hby2 a Ha)). }
    { intros a Ha. rewrite HFB in Ha. replace a with (shadow_addr (cnb_F D) + (a - shadow_addr (cnb_F D))) by lia.
      apply (proj1 (Hsh2 (a - shadow_addr (cnb_F D)) ltac:(change (512 / 8) with 64; change (512 / 8) with 64 in Ha; lia))). } }
  split.
  { unfold cnb_saved in HSAVED |- *. rewrite Forall_forall in HSAVED |- *. intros p0 Hp0.
    assert (Hpb : 56 <= fst p0 <= 152) by (cbn in Hp0; repeat (destruct Hp0 as [<- | Hp0]; [cbn; lia|]); destruct Hp0).
    eapply cnob_rdword_keep; [intros i Hi; apply KR; lia | exact (HSAVED p0 Hp0)]. }
  split; [rewrite (psc_preserved_reg_b regs regs2 3%bv HP2 ltac:(cnob_cs)); exact Hgp|].
  split; [rewrite (psc_preserved_reg_b regs regs2 4%bv HP2 ltac:(cnob_cs)); exact Htp|].
  eapply cnob_arodata_J; [exact HJ2 | exact HROD0]. }
split; [exact (cnob_regsat_keep D r r1 regs regs2 HP2 HREG)|].
split.
{ unfold cnb_slots in HSLOTS |- *. rewrite Forall_forall in HSLOTS |- *. intros p0 Hp0.
  assert (Hpb : 16 <= fst p0 <= 48) by (cbn in Hp0; repeat (destruct Hp0 as [<- | Hp0]; [cbn; lia|]); destruct Hp0).
  eapply cnob_rdword_keep; [intros i Hi; apply KR; lia | exact (HSLOTS p0 Hp0)]. }
split; [exact HRL2|].
split; [clear - HC24 Hc24le; lia|].
split.
{ (* the progress fact: the copy's own event (none for a NULL copy), by the kit's keep rules; the rest is still to
     come *)
  intros H0. destruct (HPROG H0) as (o1 & o2 & o0 & E0 & Hran & Hprog & Heq).
  exists o1, o2, o0, (E0 ++ (if c =? 0 then [] else [PresetReqAt.HFr n])). split; [exact Hran|].
  split.
  - assert (HpBs : Permutation (map snd (blocks S)) (map snd (cnob_cblk n c) ++ map snd (blocks S2))).
    { rewrite <- (cnob_blocks_snd B ly S), <- (cnob_blocks_snd B ly2 S2), <- map_app.
      apply Permutation_map. exact HpB. }
    exact (cnob_prog_fr D E0 S S2 c n Hprog HpBs HRP2).
  - rewrite <- Heq. unfold cnob_cfree_evs. cbn [concat flat_map app]. rewrite <- app_assoc. reflexivity. }
split.
{ (* the ledger: every harness block survives (no harness base is the copy), its head word is kept *)
  assert (HB0 : Forall (fun ak => prh_hblock B ly S Hp W mem (fst ak) (snd ak)) Lam) by (eapply prh_ledger_blocks; exact HLED).
  rewrite Forall_forall in HB0.
  assert (Hnc : forall a kk, In (a, kk) Lam -> (a - cf_head, kk + cf_head) <> (c, n)).
  { intros a kk Hak E. pose proof (f_equal fst E) as E1. cbn [fst] in E1.
    destruct (HB0 (a, kk) Hak) as (_ & _ & Hhp & _). cbn [fst snd] in Hhp.
    rewrite E1 in Hhp. destruct Hcopy as [(Ec & Hn0) | (_ & _ & _ & Hnh)]; [rewrite Ec in Hhp; exact (Hn0 Hhp) | exact (Hnh Hhp)]. }
  apply (cnob_ledger_keep ly S Hp W mem ly2 S2 W2 mem2 Lam peak cnt SIZE_MAXZ ran (bi_most D) ownl HLED KP).
  - intros a kk Hak. destruct (HB0 (a, kk) Hak) as (_ & Hblk & _). cbn [fst snd] in Hblk.
    pose proof (Permutation_in _ HpB Hblk) as H1. apply in_app_or in H1 as [H1 | H1]; [|exact H1].
    exfalso. unfold cnob_cblk in H1. destruct (c =? 0); [destruct H1|].
    destruct H1 as [H1 | []]. exact (Hnc a kk Hak (eq_sym H1)).
  - intros a kk x Hak Hx. destruct (HB0 (a, kk) Hak) as (Hkk & Hblk & _). cbn [fst snd] in Hkk, Hblk.
    pose proof (req_size_pos (kk + cf_head) (Z.add_nonneg_nonneg _ _ Hkk Hcf)) as (_ & Hrs).
    replace x with ((a - cf_head) + (x - (a - cf_head))) by lia.
    apply (K2 (a - cf_head) (kk + cf_head) (x - (a - cf_head)) Hblk); [lia|].
    intros (Hc0 & Hcx). destruct Hcopy as [(Ec & _) | (_ & Hcin & _ & Hnh)]; [exact (Hc0 Ec)|].
    destruct (cnob_pairwise_two zdisjoint _ (a - cf_head, req_size (kk + cf_head)) (c, req_size n)
      (proj2 (proj2 (proj2 (proj2 (proj2 (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hblk))))))) as [Hzd | Hzd].
    + apply in_map_iff. exists (a - cf_head, kk + cf_head). split; [reflexivity | exact Hblk].
    + apply in_map_iff. exists (c, n). split; [reflexivity | exact Hcin].
    + intros E. pose proof (f_equal fst E) as E1. cbn [fst] in E1.
      destruct (HB0 (a, kk) Hak) as (_ & _ & Hhp & _). cbn [fst snd] in Hhp. rewrite E1 in Hhp. exact (Hnh Hhp).
    + unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. lia.
    + unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. lia. }
split; [exact Hpk|]. split; [exact Hcnt|].
split; [reflexivity|].
split; [apply Forall_nil|]. split; [apply SSorted_nil|]. split; [apply Forall_nil|]. split; [apply Forall2_nil|].
split; [apply Forall2_nil|].
split; [exact (Forall_inv_tail Hcps)|].
split; [exact HpermL|].
split.
{ cbn [flat_map ck_hblks map app]. apply (Permutation_app_inv_l (cnob_cblk n c)).
  eapply Permutation_trans; [apply Permutation_sym; exact HpB|].
  eapply Permutation_trans; [exact HpermB|].
  unfold cnob_cblk, cnb_cblk, n. rewrite <- app_assoc. apply Permutation_refl. }
split; [intros a kk []|].
(* the hull budget: free_cf keeps both meters *)
exact (PresetHullBudget.hull_budget_same S S2 _ HSS HHB).
Qed.

(* ==== THE STRETCHES: a stretch runs from a cut to a callee entry (the engine), then the step at the callee.
   What a run that writes nothing keeps of the invariant, and the two steps stated at a callee entry ==== *)
Definition cnob_kept_regs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.
Lemma cnob_fmid_run : forall D fxk ly S Hp W regs regs' mem md md' k Lam peak cnt ran nr r1 r2 r3 r ownl offs sts Fs Es
    cs,
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl offs sts Fs Es cs ->
  cnb_JR B ARcfx WLE' D 6 ly S Hp W mem md' k ->
  (forall rr, In rr cnob_kept_regs -> getr regs' rr = getr regs rr) ->
  cnob_fmid D fxk ly S Hp W regs' mem md' k Lam peak cnt ran nr r1 r2 r3 r ownl offs sts Fs Es cs.
Proof.
intros D fxk ly S Hp W regs regs' mem md md' k Lam peak cnt ran nr r1 r2 r3 r ownl offs sts Fs Es cs HM HJ' Hk.
destruct HM as (HBASE & HREG & REST). destruct HBASE as (H1 & H2 & _ & H4 & H5 & H6 & H7 & H8).
split; [|split; [|exact REST]].
- split; [exact H1|]. split; [exact H2|]. split; [exact HJ'|]. split; [exact H4|]. split; [exact H5|].
  split; [rewrite (Hk 3%bv ltac:(cbn; tauto)); exact H6|].
  split; [rewrite (Hk 4%bv ltac:(cbn; tauto)); exact H7 | exact H8].
- unfold cnb_regsat in *. rewrite Forall_forall in HREG |- *. intros [rr vv] Hi. cbn [fst snd].
  rewrite (Hk rr); [exact (HREG (rr, vv) Hi)|].
  unfold cnb_core in Hi. cbn [app In] in Hi. unfold cnob_kept_regs. cbn [In].
  repeat (destruct Hi as [Hi | Hi]; [injection Hi as <- _; tauto |]). destruct Hi.
Qed.
(* the six return sites are code pointers *)
Lemma cnob_retok : forall off, 0 <= CNB_OFF + off < 2 ^ 40 -> (CNB_OFF + off) mod 2 = 0 ->
  YK0s.ret_ok (Z_to_bv 64 (cnb_pc off)).
Proof. intros off H1 H2. unfold cnb_pc. rewrite <- Z.add_assoc. exact (ret_ok_codeptr_v _ H1 H2). Qed.

(* step (A) at a callee entry the run reached: the registers the cut names kept, a0 = the struct, ra = RET *)
Lemma cnob_pjf_at : forall fxk D ly S Hp W regs regs' mem md md' k Lam peak cnt ran nr r1 r2 r3 r ownl
    off st offs sts F Fs E Es cs RET (P : (word -> option byte) -> Prop),
  srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl (off :: offs) (st :: sts) (F :: Fs)
    (E :: Es) cs ->
  cnb_JR B ARcfx WLE' D 6 ly S Hp W mem md' k ->
  (forall rr, In rr cnob_kept_regs -> getr regs' rr = getr regs rr) ->
  getr regs' 10 = w64 (cnb_F D + off) -> getr regs' 1 = Z_to_bv 64 (cnb_pc RET) ->
  YK0s.ret_ok (Z_to_bv 64 (cnb_pc RET)) ->
  4096 <= bv_unsigned (Z_to_bv 64 (cnb_pc RET)) /\ bv_unsigned (Z_to_bv 64 (cnb_pc RET)) < YM05.alloc_ceiling ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxk regs' (Z_to_bv 64 (SIGMA AS_pj_free)) mem (YK11.seg_rom SEGS)) md')
    (fun W2 c2 => (exists ly2 S2 Hp2 regs2 mem2 md2 k2 Lam2,
        c2 = @cnb_cfg SEGS fxk (cnb_pc RET) regs2 mem2 md2 /\
        cnob_fmid D fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl offs sts Fs Es cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fxk D ly S Hp W regs regs' mem md md' k Lam peak cnt ran nr r1 r2 r3 r ownl off st offs sts F Fs E Es cs RET P
  PCALL HPRE HM HJ' Hk Ha0 Hra Hret (Hra4 & HraC) HPM.
pose proof (cnob_fmid_run D fxk ly S Hp W regs regs' mem md md' k Lam peak cnt ran nr r1 r2 r3 r ownl _ _ _ _ cs HM HJ'
  Hk) as HM'.
eapply SRr'_mono.
{ exact (cnob_pjf_step fxk D ly S Hp W regs' mem md' k Lam peak cnt ran nr r1 r2 r3 r ownl off st offs sts F Fs E Es cs
    (Z_to_bv 64 (cnb_pc RET)) P PCALL HPRE HM' Ha0 Hra Hret Hra4 HraC HPM). }
cbv beta. intros W2 c2 _ ((ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & Lam2 & -> & _ & HM2) & HPM2).
split; [|exact HPM2]. exists ly2, S2, Hp2, regs2, mem2, md2, k2, Lam2. split; [reflexivity | exact HM2].
Qed.

(* step (B) at a callee entry the run reached: the registers the cut names kept, a0 = the copy, ra = RET *)
Lemma cnob_wfr_at : forall fxk D ly S Hp W regs regs' mem md md' k Lam peak cnt ran nr r1 r2 r3 r ownl c cs RET
    (P : (word -> option byte) -> Prop),
  srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] (c :: cs) ->
  cnb_JR B ARcfx WLE' D 6 ly S Hp W mem md' k ->
  (forall rr, In rr cnob_kept_regs -> getr regs' rr = getr regs rr) ->
  getr regs' 10 = w64 c -> getr regs' 1 = Z_to_bv 64 (cnb_pc RET) ->
  YK0s.ret_ok (Z_to_bv 64 (cnb_pc RET)) -> 4096 <= bv_unsigned (Z_to_bv 64 (cnb_pc RET)) ->
  In (bv_unsigned (Z_to_bv 64 (cnb_pc RET))) (pi_ret_sites F_check_no_overread RT_free) ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxk regs' (Z_to_bv 64 (SIGMA AS___wrap_free)) mem (YK11.seg_rom SEGS)) md')
    (fun W2 c2 => (exists ly2 S2 Hp2 regs2 mem2 md2 k2 Lam2,
        c2 = @cnb_cfg SEGS fxk (cnb_pc RET) regs2 mem2 md2 /\
        cnob_fmid D fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fxk D ly S Hp W regs regs' mem md md' k Lam peak cnt ran nr r1 r2 r3 r ownl c cs RET P PCALL
  HPRE HM HJ' Hk Ha0 Hra Hret Hra4 Hsite HPM.
pose proof (cnob_fmid_run D fxk ly S Hp W regs regs' mem md md' k Lam peak cnt ran nr r1 r2 r3 r ownl _ _ _ _ _ HM HJ'
  Hk) as HM'.
eapply SRr'_mono.
{ exact (cnob_wfr_step fxk D ly S Hp W regs' mem md' k Lam peak cnt ran nr r1 r2 r3 r ownl c cs
    (Z_to_bv 64 (cnb_pc RET)) P PCALL HPRE HM' Ha0 Hra Hret Hra4 Hsite HPM). }
cbv beta. intros W2 c2 _ ((ly2 & S2 & regs2 & mem2 & md2 & k2 & -> & _ & HM2) & HPM2).
split; [|exact HPM2]. exists ly2, S2, Hp, regs2, mem2, md2, k2, Lam. split; [reflexivity | exact HM2].
Qed.

(* a register the run set to the image base plus a constant (the `jal`'s return address) *)
Lemma cnob_reg_base : forall (fz : YK11.FPState) (H : word -> bool) ss ms regs (rd : bv 5) c,
  st_ok_pi (fx := fz) SEGS VAL (Eimg (Ereg regs [])) ss (restrict H ms) ->
  sr_get (ss_regs ss) rd = SOff A_TEXT c -> 0 <= c < 2 ^ 40 ->
  getr (ms_regs ms) rd = Z_to_bv 64 (BASE + c).
Proof.
intros fz H ss ms regs rd c HS Hr Hc.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _).
rewrite (st_ok_pi_restrict_reg (fx := fz) H _ ss ms rd HS), Hr.
rewrite (denot_lit_U _ (SOff A_TEXT c)), U_SOff.
rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
rewrite unsigned_lit_small by lia. unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
Qed.
(* the same two readbacks over the run's END state, which is an st_ok at the callee's pc (setpc) *)
Lemma cnob_reg_of_c : forall (fz : YK11.FPState) (H : word -> bool) ss0 pc ms regs (rd rs : bv 5) n,
  st_ok (fx := fz) SEGS (Eimg (Ereg regs [])) (setpc ss0 pc) (restrict H ms) ->
  sr_get (ss_regs ss0) rd = SOff n 0 -> Z.of_nat n = bv_unsigned rs -> (n < 32)%nat ->
  getr (ms_regs ms) rd = getr regs rs.
Proof.
intros fz H ss0 pc ms regs rd rs n HS Hr Hn H32.
rewrite (st_ok_restrict_reg (fx := fz) SEGS H _ _ ms rd HS).
change (ss_regs (setpc ss0 pc)) with (ss_regs ss0). rewrite Hr.
rewrite (denot_lit_U _ (SOff n 0)), U_SOff, Z.add_0_r.
rewrite (cnob_ew_reg regs n rs Hn H32). unfold zcanon, M64.
rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 (getr regs rs)) as Hb;
  unfold bv_modulus in Hb; cbn in Hb; lia).
apply Z_to_bv_bv_unsigned.
Qed.
Lemma cnob_reg_base_c : forall (fz : YK11.FPState) (H : word -> bool) ss0 pc ms regs (rd : bv 5) c,
  st_ok (fx := fz) SEGS (Eimg (Ereg regs [])) (setpc ss0 pc) (restrict H ms) ->
  sr_get (ss_regs ss0) rd = SOff A_TEXT c -> 0 <= c < 2 ^ 40 ->
  getr (ms_regs ms) rd = Z_to_bv 64 (BASE + c).
Proof.
intros fz H ss0 pc ms regs rd c HS Hr Hc.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _).
rewrite (st_ok_restrict_reg (fx := fz) SEGS H _ _ ms rd HS).
change (ss_regs (setpc ss0 pc)) with (ss_regs ss0). rewrite Hr.
rewrite (denot_lit_U _ (SOff A_TEXT c)), U_SOff.
rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
rewrite unsigned_lit_small by lia. unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma cnob_reg_lit_c : forall (fz : YK11.FPState) (H : word -> bool) ss0 pc ms regs (rd : bv 5) v,
  st_ok (fx := fz) SEGS (Eimg (Ereg regs [])) (setpc ss0 pc) (restrict H ms) ->
  sr_get (ss_regs ss0) rd = SLit v -> getr (ms_regs ms) rd = Z_to_bv 64 v.
Proof.
intros fz H ss0 pc ms regs rd v HS Hr.
rewrite (st_ok_restrict_reg (fx := fz) SEGS H _ _ ms rd HS).
change (ss_regs (setpc ss0 pc)) with (ss_regs ss0). rewrite Hr. reflexivity.
Qed.
(* the registers the cut names, after a run that leaves them: each is its own atom in the run's state *)
Ltac cnob_kreg HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?rr = getr ?regs ?rr =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
    first [ apply (cnob_reg_of_c _ _ _ _ ms regs rr rr n HS); [vm_compute; reflexivity | vm_compute; reflexivity | lia]
          | fail 1 "cnob_kreg: the run's state does not hold register" rr "as its own atom" ] end.
Ltac cnob_kregs HS :=
  lazymatch goal with |- forall rr, In rr cnob_kept_regs -> getr ?r' rr = getr ?r0 rr =>
    apply (proj1 (Forall_forall (fun rr => getr r' rr = getr r0 rr) cnob_kept_regs));
    unfold cnob_kept_regs; repeat (apply Forall_cons; [cbv beta; cnob_kreg HS |]); apply Forall_nil end.

(* ---- the two loads of a copy from the s1 slots: the run's entry state carries the slot as a read-only region of
   atom 9 (s1), its word the copy (a plain variable, lead 12:xxZ: never SLit of a model term) ---- *)
Lemma cnob_aview_range : forall H mem a v, aview SEGS H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte SEGS (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.
Lemma cnob_rdword_range : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
pose proof (cnob_aview_range _ _ _ _ E0). pose proof (cnob_aview_range _ _ _ _ E1).
pose proof (cnob_aview_range _ _ _ _ E2). pose proof (cnob_aview_range _ _ _ _ E3).
pose proof (cnob_aview_range _ _ _ _ E4). pose proof (cnob_aview_range _ _ _ _ E5).
pose proof (cnob_aview_range _ _ _ _ E6). pose proof (cnob_aview_range _ _ _ _ E7).
lia.
Qed.
Definition cnob_slot_rg (o v : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) o (o + 8) o o [YP09.mkChunk o (CVal 8 (SLit v))].
Lemma cnob_slot_rg_ok : forall (W : world SEGS) regs mem o v,
  bv_unsigned (getr regs 9) + o + 8 <= 2 ^ 64 -> 0 <= o ->
  rdword (aview SEGS (w_H W) mem) (bv_unsigned (getr regs 9) + o) = Some v ->
  Forall (region_ok SEGS (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) [cnob_slot_rg o v].
Proof.
intros W regs mem o v Hhi Ho Hrd.
pose proof (cnob_rdword_range _ _ _ _ Hrd) as Hv.
assert (E9 : bv_unsigned (ew (Eimg (Ereg regs [])) 9) = bv_unsigned (getr regs 9))
  by (rewrite (cnob_ew_reg regs 9 9%bv eq_refl ltac:(lia)); reflexivity).
apply Forall_cons; [|apply Forall_nil].
unfold region_ok, cnob_slot_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E9. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Hb. unfold bv_modulus in Hb. cbn in Hb.
split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS _ _ _ o 8 (SLit v) v); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS _ _ _ _ Hrd).
Qed.

(* STRETCH 1: 740 `mv a0, s6`; 744 `jal pj_free` (d1 = F + 32) -> 748 *)
Lemma cnob_st_pjf1 : forall fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st offs sts F Fs E Es cs
    (P : (word -> option byte) -> Prop),
  srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl (32 :: offs) (st :: sts) (F :: Fs) (E :: Es)
    cs ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_FREE) regs mem md)
    (fun W2 c2 => (exists ly2 S2 Hp2 regs2 mem2 md2 k2 Lam2,
        c2 = @cnb_cfg SEGS fxk (cnb_pc CNB_PJF1) regs2 mem2 md2 /\
        cnob_fmid D fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl offs sts Fs Es cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st offs sts F Fs E Es cs P PLAW PCALL HPRE
  HM HPM.
pose proof HM as (HBASE & HREG & _).
pose proof HBASE as (_ & _ & HJ0 & _).
pose proof (cnb_J_rebaseR B ARcfx WLE' D 6 ly S Hp W mem md k HJ0) as HJ.
assert (R22 : getr regs 22 = w64 (cnb_d1 D)).
{ unfold cnb_regsat in HREG. rewrite Forall_forall in HREG. apply (HREG (22%bv, cnb_d1 D)).
  unfold cnb_core. cbn [app In]. repeat (first [left; reflexivity | right]). }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
pose proof (cnob_entry fxk CNB_FREE [] W regs mem eq_refl (Forall_nil _) I) as HS.
pose proof (cnob_sh_nil W regs mem) as SHOK.
pose (RUN := @paj_run_x_invR fxk rc SK _ CF_PL PA B prh_pst ARcfx _ LAWS P PLAW WLE' (wle'_refl SEGS _)
  (wle'_trans SEGS _)).
unfold SRr', cnb_cfg, cnb_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_invR RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- apply awr_ok_nil.
- assert (Emem : ms_mem ms = mem) by (eapply cnob_frame_id; [exact HF | intros rr []]).
  assert (Hk : forall rr, In rr cnob_kept_regs -> getr (ms_regs ms) rr = getr regs rr) by cnob_kregs HS.
  assert (A0 : getr (ms_regs ms) 10 = w64 (cnb_F D + 32)).
  { rewrite (cnob_reg_of_c _ _ _ _ ms regs 10%bv 22%bv 22 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(lia)). exact R22. }
  assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (cnb_pc CNB_PJF1)).
  { unfold cnb_pc. rewrite <- Z.add_assoc.
    apply (cnob_reg_base_c _ _ _ _ ms regs 1%bv (CNB_OFF + CNB_PJF1) HS ltac:(vm_compute; reflexivity)).
    split; vm_compute; [discriminate | reflexivity]. }
  pmkst HS. rewrite Emem in HJ, HPM |- *.
  apply (cnob_pjf_at fxk D ly S Hp W regs (ms_regs ms) mem md _ k Lam peak cnt ran nr r1 r2 r3 r ownl 32 st offs sts
    F Fs E Es cs CNB_PJF1 P PCALL HPRE HM (cnb_J_fixedR B ARcfx WLE' D 6 ly S Hp W mem md k _ _ _ _ _ _ _ HJ0 HJ) Hk A0 RA
    (cnob_retok CNB_PJF1 ltac:(split; vm_compute; [discriminate | reflexivity]) ltac:(vm_compute; reflexivity))
    cnob_ret_pjf1 HPM).
Qed.

(* STRETCH 2: 748 `mv a0, s5`; 752 `jal pj_free` (d2 = F + 128) -> 756 *)
Lemma cnob_st_pjf2 : forall fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st offs sts F Fs E Es cs
    (P : (word -> option byte) -> Prop),
  srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl (128 :: offs) (st :: sts) (F :: Fs)
    (E :: Es) cs ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_PJF1) regs mem md)
    (fun W2 c2 => (exists ly2 S2 Hp2 regs2 mem2 md2 k2 Lam2,
        c2 = @cnb_cfg SEGS fxk (cnb_pc CNB_PJF2) regs2 mem2 md2 /\
        cnob_fmid D fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl offs sts Fs Es cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st offs sts F Fs E Es cs P PLAW PCALL HPRE
  HM HPM.
pose proof HM as (HBASE & HREG & _).
pose proof HBASE as (_ & _ & HJ0 & _).
pose proof (cnb_J_rebaseR B ARcfx WLE' D 6 ly S Hp W mem md k HJ0) as HJ.
assert (R21 : getr regs 21 = w64 (cnb_d2 D)).
{ unfold cnb_regsat in HREG. rewrite Forall_forall in HREG. apply (HREG (21%bv, cnb_d2 D)).
  unfold cnb_core. cbn [app In]. repeat (first [left; reflexivity | right]). }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
pose proof (cnob_entry fxk CNB_PJF1 [] W regs mem eq_refl (Forall_nil _) I) as HS.
pose proof (cnob_sh_nil W regs mem) as SHOK.
pose (RUN := @paj_run_x_invR fxk rc SK _ CF_PL PA B prh_pst ARcfx _ LAWS P PLAW WLE' (wle'_refl SEGS _)
  (wle'_trans SEGS _)).
unfold SRr', cnb_cfg, cnb_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_invR RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- apply awr_ok_nil.
- assert (Emem : ms_mem ms = mem) by (eapply cnob_frame_id; [exact HF | intros rr []]).
  assert (Hk : forall rr, In rr cnob_kept_regs -> getr (ms_regs ms) rr = getr regs rr) by cnob_kregs HS.
  assert (A0 : getr (ms_regs ms) 10 = w64 (cnb_F D + 128)).
  { rewrite (cnob_reg_of_c _ _ _ _ ms regs 10%bv 21%bv 21 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(lia)). exact R21. }
  assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (cnb_pc CNB_PJF2)).
  { unfold cnb_pc. rewrite <- Z.add_assoc.
    apply (cnob_reg_base_c _ _ _ _ ms regs 1%bv (CNB_OFF + CNB_PJF2) HS ltac:(vm_compute; reflexivity)).
    split; vm_compute; [discriminate | reflexivity]. }
  pmkst HS. rewrite Emem in HJ, HPM |- *.
  apply (cnob_pjf_at fxk D ly S Hp W regs (ms_regs ms) mem md _ k Lam peak cnt ran nr r1 r2 r3 r ownl 128 st offs sts
    F Fs E Es cs CNB_PJF2 P PCALL HPRE HM (cnb_J_fixedR B ARcfx WLE' D 6 ly S Hp W mem md k _ _ _ _ _ _ _ HJ0 HJ) Hk A0 RA
    (cnob_retok CNB_PJF2 ltac:(split; vm_compute; [discriminate | reflexivity]) ltac:(vm_compute; reflexivity))
    cnob_ret_pjf2 HPM).
Qed.

(* STRETCH 3: 756 `mv a0, s4`; 760 `jal pj_free` (d3 = F + 224) -> 764 *)
Lemma cnob_st_pjf3 : forall fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st offs sts F Fs E Es cs
    (P : (word -> option byte) -> Prop),
  srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl (224 :: offs) (st :: sts) (F :: Fs)
    (E :: Es) cs ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_PJF2) regs mem md)
    (fun W2 c2 => (exists ly2 S2 Hp2 regs2 mem2 md2 k2 Lam2,
        c2 = @cnb_cfg SEGS fxk (cnb_pc CNB_PJF3) regs2 mem2 md2 /\
        cnob_fmid D fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl offs sts Fs Es cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st offs sts F Fs E Es cs P PLAW PCALL HPRE
  HM HPM.
pose proof HM as (HBASE & HREG & _).
pose proof HBASE as (_ & _ & HJ0 & _).
pose proof (cnb_J_rebaseR B ARcfx WLE' D 6 ly S Hp W mem md k HJ0) as HJ.
assert (R20 : getr regs 20 = w64 (cnb_d3 D)).
{ unfold cnb_regsat in HREG. rewrite Forall_forall in HREG. apply (HREG (20%bv, cnb_d3 D)).
  unfold cnb_core. cbn [app In]. repeat (first [left; reflexivity | right]). }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
pose proof (cnob_entry fxk CNB_PJF2 [] W regs mem eq_refl (Forall_nil _) I) as HS.
pose proof (cnob_sh_nil W regs mem) as SHOK.
pose (RUN := @paj_run_x_invR fxk rc SK _ CF_PL PA B prh_pst ARcfx _ LAWS P PLAW WLE' (wle'_refl SEGS _)
  (wle'_trans SEGS _)).
unfold SRr', cnb_cfg, cnb_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_invR RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- apply awr_ok_nil.
- assert (Emem : ms_mem ms = mem) by (eapply cnob_frame_id; [exact HF | intros rr []]).
  assert (Hk : forall rr, In rr cnob_kept_regs -> getr (ms_regs ms) rr = getr regs rr) by cnob_kregs HS.
  assert (A0 : getr (ms_regs ms) 10 = w64 (cnb_F D + 224)).
  { rewrite (cnob_reg_of_c _ _ _ _ ms regs 10%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(lia)). exact R20. }
  assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (cnb_pc CNB_PJF3)).
  { unfold cnb_pc. rewrite <- Z.add_assoc.
    apply (cnob_reg_base_c _ _ _ _ ms regs 1%bv (CNB_OFF + CNB_PJF3) HS ltac:(vm_compute; reflexivity)).
    split; vm_compute; [discriminate | reflexivity]. }
  pmkst HS. rewrite Emem in HJ, HPM |- *.
  apply (cnob_pjf_at fxk D ly S Hp W regs (ms_regs ms) mem md _ k Lam peak cnt ran nr r1 r2 r3 r ownl 224 st offs sts
    F Fs E Es cs CNB_PJF3 P PCALL HPRE HM (cnb_J_fixedR B ARcfx WLE' D 6 ly S Hp W mem md k _ _ _ _ _ _ _ HJ0 HJ) Hk A0 RA
    (cnob_retok CNB_PJF3 ltac:(split; vm_compute; [discriminate | reflexivity]) ltac:(vm_compute; reflexivity))
    cnob_ret_pjf3 HPM).
Qed.


(* the free sites as the bv value the call rule asks *)
Lemma cnob_site_at : forall off, In (B_prog_base + CNB_OFF + off) (pi_ret_sites F_check_no_overread RT_free) ->
  0 <= CNB_OFF + off < 2 ^ 40 ->
  In (bv_unsigned (Z_to_bv 64 (cnb_pc off))) (pi_ret_sites F_check_no_overread RT_free).
Proof.
intros off Hin Hoff. pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _).
unfold cnb_pc. rewrite unsigned_lit_small by lia. rewrite (cnbi_base B IMG). exact Hin.
Qed.

(* STRETCH 4: 764 `mv a0, s9`; 768 `jal __wrap_free` (the copy r1) -> 772 *)
Lemma cnob_st_fr1 : forall fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl cs
    (P : (word -> option byte) -> Prop),
  srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] (r1 :: cs) ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_PJF3) regs mem md)
    (fun W2 c2 => (exists ly2 S2 Hp2 regs2 mem2 md2 k2 Lam2,
        c2 = @cnb_cfg SEGS fxk (cnb_pc CNB_FR1) regs2 mem2 md2 /\
        cnob_fmid D fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl cs P PLAW PCALL HPRE HM HPM.
pose proof HM as (HBASE & HREG & _).
pose proof HBASE as (_ & _ & HJ0 & _).
pose proof (cnb_J_rebaseR B ARcfx WLE' D 6 ly S Hp W mem md k HJ0) as HJ.
assert (R25 : getr regs 25 = w64 r1).
{ unfold cnb_regsat in HREG. rewrite Forall_forall in HREG. apply (HREG (25%bv, r1)).
  apply in_or_app. right. right. left. reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
pose proof (cnob_entry fxk CNB_PJF3 [] W regs mem eq_refl (Forall_nil _) I) as HS.
pose proof (cnob_sh_nil W regs mem) as SHOK.
pose (RUN := @paj_run_x_invR fxk rc SK _ CF_PL PA B prh_pst ARcfx _ LAWS P PLAW WLE' (wle'_refl SEGS _)
  (wle'_trans SEGS _)).
unfold SRr', cnb_cfg, cnb_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_invR RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- apply awr_ok_nil.
- assert (Emem : ms_mem ms = mem) by (eapply cnob_frame_id; [exact HF | intros rr []]).
  assert (Hk : forall rr, In rr cnob_kept_regs -> getr (ms_regs ms) rr = getr regs rr) by cnob_kregs HS.
  assert (A0 : getr (ms_regs ms) 10 = w64 r1).
  { rewrite (cnob_reg_of_c _ _ _ _ ms regs 10%bv 25%bv 25 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(lia)). exact R25. }
  assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (cnb_pc CNB_FR1)).
  { unfold cnb_pc. rewrite <- Z.add_assoc.
    apply (cnob_reg_base_c _ _ _ _ ms regs 1%bv (CNB_OFF + CNB_FR1) HS ltac:(vm_compute; reflexivity)).
    split; vm_compute; [discriminate | reflexivity]. }
  pmkst HS. rewrite Emem in HJ, HPM |- *.
  apply (cnob_wfr_at fxk D ly S Hp W regs (ms_regs ms) mem md _ k Lam peak cnt ran nr r1 r2 r3 r ownl r1 cs
    CNB_FR1 P PCALL HPRE HM (cnb_J_fixedR B ARcfx WLE' D 6 ly S Hp W mem md k _ _ _ _ _ _ _ HJ0 HJ) Hk A0 RA
    (cnob_retok CNB_FR1 ltac:(split; vm_compute; [discriminate | reflexivity]) ltac:(vm_compute; reflexivity))
    (proj1 cnob_ret_fr1)
    (cnob_site_at CNB_FR1 cnob_site_fr1 ltac:(split; vm_compute; [discriminate | reflexivity])) HPM).
Qed.


(* STRETCH 5: 772 `ld a0, 24(s1)`; `jal __wrap_free` (the copy r2, the s1 slot 24) -> 780 *)
Lemma cnob_st_fr2 : forall fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl cs
    (P : (word -> option byte) -> Prop),
  srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] (r2 :: cs) ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_FR1) regs mem md)
    (fun W2 c2 => (exists ly2 S2 Hp2 regs2 mem2 md2 k2 Lam2,
        c2 = @cnb_cfg SEGS fxk (cnb_pc CNB_FR2) regs2 mem2 md2 /\
        cnob_fmid D fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl cs P PLAW PCALL HPRE HM HPM.
pose proof HM as (HBASE & HREG & HSLOTS & _).
pose proof HBASE as (_ & _ & HJ0 & _).
pose proof (cnb_J_rebaseR B ARcfx WLE' D 6 ly S Hp W mem md k HJ0) as HJ.
pose proof (ajxR_stk HJ) as HSTK.
pose proof HSTK as (Hsp16 & HSTKge & Hceil & Hlo & Hhi & H47 & _).
destruct (cnb_S1_bounds D Hsp16) as (HS1a & HS1b & _).
pose proof asan_consts as (C1 & _).
assert (R9 : getr regs 9 = w64 (cnb_S1 D)).
{ unfold cnb_regsat in HREG. rewrite Forall_forall in HREG. apply (HREG (9%bv, cnb_S1 D)).
  unfold cnb_core. cbn [app In]. repeat (first [left; reflexivity | right]). }
assert (HS9 : bv_unsigned (getr regs 9) = cnb_S1 D) by (rewrite R9; unfold w64; apply unsigned_lit_small; lia).
assert (Hrd : rdword (aview SEGS (w_H W) mem) (bv_unsigned (getr regs 9) + 24) = Some r2).
{ rewrite HS9. unfold cnb_slots in HSLOTS. rewrite Forall_forall in HSLOTS.
  exact (HSLOTS (24, r2) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
pose proof (cnob_entry fxk CNB_FR1 [cnob_slot_rg 24 r2] W regs mem eq_refl
  (cnob_slot_rg_ok W regs mem 24 r2 ltac:(rewrite HS9; lia) ltac:(lia) Hrd) (conj I I)) as HS.
pose proof (cnob_sh_nil W regs mem) as SHOK.
pose (RUN := @paj_run_x_invR fxk rc SK _ CF_PL PA B prh_pst ARcfx _ LAWS P PLAW WLE' (wle'_refl SEGS _)
  (wle'_trans SEGS _)).
unfold SRr', cnb_cfg, cnb_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_invR RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- assert (Emem : ms_mem ms = mem)
    by (eapply cnob_frame_id; [exact HF | intros rr Hin; cbn in Hin; destruct Hin as [<- | []]; cbn; lia]).
  assert (Hk : forall rr, In rr cnob_kept_regs -> getr (ms_regs ms) rr = getr regs rr) by cnob_kregs HS.
  assert (A0 : getr (ms_regs ms) 10 = w64 r2).
  { exact (cnob_reg_lit_c _ _ _ _ ms regs 10%bv r2 HS eq_refl). }
  assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (cnb_pc CNB_FR2)).
  { unfold cnb_pc. rewrite <- Z.add_assoc.
    apply (cnob_reg_base_c _ _ _ _ ms regs 1%bv (CNB_OFF + CNB_FR2) HS ltac:(vm_compute; reflexivity)).
    split; vm_compute; [discriminate | reflexivity]. }
  pmkst HS. rewrite Emem in HJ, HPM |- *.
  apply (cnob_wfr_at fxk D ly S Hp W regs (ms_regs ms) mem md _ k Lam peak cnt ran nr r1 r2 r3 r ownl r2 cs
    CNB_FR2 P PCALL HPRE HM (cnb_J_fixedR B ARcfx WLE' D 6 ly S Hp W mem md k _ _ _ _ _ _ _ HJ0 HJ) Hk A0 RA
    (cnob_retok CNB_FR2 ltac:(split; vm_compute; [discriminate | reflexivity]) ltac:(vm_compute; reflexivity))
    (proj1 cnob_ret_fr2)
    (cnob_site_at CNB_FR2 cnob_site_fr2 ltac:(split; vm_compute; [discriminate | reflexivity])) HPM).
Qed.

(* STRETCH 6: 780 `ld a0, 16(s1)`; `jal __wrap_free` (the copy r3, the s1 slot 16) -> 788 *)
Lemma cnob_st_fr3 : forall fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl cs
    (P : (word -> option byte) -> Prop),
  srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnob_fmid D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] (r3 :: cs) ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_FR2) regs mem md)
    (fun W2 c2 => (exists ly2 S2 Hp2 regs2 mem2 md2 k2 Lam2,
        c2 = @cnb_cfg SEGS fxk (cnb_pc CNB_FR3) regs2 mem2 md2 /\
        cnob_fmid D fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl [] [] [] [] cs) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl cs P PLAW PCALL HPRE HM HPM.
pose proof HM as (HBASE & HREG & HSLOTS & _).
pose proof HBASE as (_ & _ & HJ0 & _).
pose proof (cnb_J_rebaseR B ARcfx WLE' D 6 ly S Hp W mem md k HJ0) as HJ.
pose proof (ajxR_stk HJ) as HSTK.
pose proof HSTK as (Hsp16 & HSTKge & Hceil & Hlo & Hhi & H47 & _).
destruct (cnb_S1_bounds D Hsp16) as (HS1a & HS1b & _).
pose proof asan_consts as (C1 & _).
assert (R9 : getr regs 9 = w64 (cnb_S1 D)).
{ unfold cnb_regsat in HREG. rewrite Forall_forall in HREG. apply (HREG (9%bv, cnb_S1 D)).
  unfold cnb_core. cbn [app In]. repeat (first [left; reflexivity | right]). }
assert (HS9 : bv_unsigned (getr regs 9) = cnb_S1 D) by (rewrite R9; unfold w64; apply unsigned_lit_small; lia).
assert (Hrd : rdword (aview SEGS (w_H W) mem) (bv_unsigned (getr regs 9) + 16) = Some r3).
{ rewrite HS9. unfold cnb_slots in HSLOTS. rewrite Forall_forall in HSLOTS.
  exact (HSLOTS (16, r3) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
pose proof (cnob_entry fxk CNB_FR2 [cnob_slot_rg 16 r3] W regs mem eq_refl
  (cnob_slot_rg_ok W regs mem 16 r3 ltac:(rewrite HS9; lia) ltac:(lia) Hrd) (conj I I)) as HS.
pose proof (cnob_sh_nil W regs mem) as SHOK.
pose (RUN := @paj_run_x_invR fxk rc SK _ CF_PL PA B prh_pst ARcfx _ LAWS P PLAW WLE' (wle'_refl SEGS _)
  (wle'_trans SEGS _)).
unfold SRr', cnb_cfg, cnb_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_invR RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- assert (Emem : ms_mem ms = mem)
    by (eapply cnob_frame_id; [exact HF | intros rr Hin; cbn in Hin; destruct Hin as [<- | []]; cbn; lia]).
  assert (Hk : forall rr, In rr cnob_kept_regs -> getr (ms_regs ms) rr = getr regs rr) by cnob_kregs HS.
  assert (A0 : getr (ms_regs ms) 10 = w64 r3).
  { exact (cnob_reg_lit_c _ _ _ _ ms regs 10%bv r3 HS eq_refl). }
  assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (cnb_pc CNB_FR3)).
  { unfold cnb_pc. rewrite <- Z.add_assoc.
    apply (cnob_reg_base_c _ _ _ _ ms regs 1%bv (CNB_OFF + CNB_FR3) HS ltac:(vm_compute; reflexivity)).
    split; vm_compute; [discriminate | reflexivity]. }
  pmkst HS. rewrite Emem in HJ, HPM |- *.
  apply (cnob_wfr_at fxk D ly S Hp W regs (ms_regs ms) mem md _ k Lam peak cnt ran nr r1 r2 r3 r ownl r3 cs
    CNB_FR3 P PCALL HPRE HM (cnb_J_fixedR B ARcfx WLE' D 6 ly S Hp W mem md k _ _ _ _ _ _ _ HJ0 HJ) Hk A0 RA
    (cnob_retok CNB_FR3 ltac:(split; vm_compute; [discriminate | reflexivity]) ltac:(vm_compute; reflexivity))
    (proj1 cnob_ret_fr3)
    (cnob_site_at CNB_FR3 cnob_site_fr3 ltac:(split; vm_compute; [discriminate | reflexivity])) HPM).
Qed.

(* ---- THE SEGMENT STATEMENT (the contract's FORWARD form, the internal file lane-102.md :29-30): generic P with its runner laws and
   the call law (this segment crosses the kit's pj_free text and the runtime free; both posts carry the memnorm keep, so
   srr_inv_mn is NOT asked). It concludes SRr' segs RZ_cf: its frees can re-hide shadow. NO premise beyond the
   contract's: the trees' free order (the former PJF-TIE) is the free cut's cnb_fo (cnob_fos_tie), the class-24
   bound is DERIVED (cnob_cnt24_free). ---- *)
Definition cnb_seg_freeP : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_at_freeR (fx := fx) B ARcfx WLE' D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3
    o1 o2 o0 ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_FREE) regs mem md)
    (fun W' c' => cnb_ex_end D W' c' /\ P (ms_mem (cfg_ms c'))).

(* ---- the input bytes at the exit, from the entry: the caller's buffer is in a harness block, an image read-only
   range, or a live non-harness block at the entry (cnb_pre's prhReader_home); the walk's journal (FP = [], at wle')
   keeps every entry block still live (the exit's ablocks are the entry's) and every image byte that is no owned
   static, no errno byte and no program static (the block and image clauses read no world relation) ---- *)
Lemma cnob_bytes_exit : forall D ly S Hp W mem md k,
  cnb_pre (fx := fx) B ARcfx CTX0 D -> cnb_JR B ARcfx WLE' D 6 ly S Hp W mem md k ->
  Permutation (ablocks B ly S) (ablocks B (bi_ly D) (bi_S D)) ->
  bytes_at W mem (bi_data D) (bi_x D).
Proof.
intros D ly S Hp W mem md k HPRE HJ Hperm.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & HSRC & HHOME & HLED0 & _).
destruct HSRC as (Hbytes0 & _).
destruct HJ as (WS & HJ & _). pose proof (ajxR_blk HJ) as K2. pose proof (ajxR_img HJ) as K3.
pose proof cnob_cf_head as Hcf.
assert (HB0 : Forall (fun ak => prh_hblock B (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (fst ak) (snd ak))
  (bi_Lam D)) by (eapply prh_ledger_blocks; exact HLED0).
rewrite Forall_forall in HB0.
(* an image byte of a read-only range *)
assert (KI : forall x, in_roP SEGS pa_relro_lo pa_relro_hi x -> ~ Exists (in_zr x) (as_owned_static B) ->
    ~ (as_errno B <= x < as_errno B + 4) -> aview SEGS (w_H W) mem x = aview SEGS (w_H (bi_W D)) (bi_mem D) x).
{ intros x Hr Hown Herr. apply K3; [| exact Hown | exact Herr | exact (fun HP => cnbi_pst_rw B IMG x HP Hr)
    | exact (fp_spares_closed [] x sink_closed_nil)].
  destruct Hr as [(sg & Hsg & _ & Hlo & Hhi) | Hrel];
  [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img x Hrel)]. }
(* a byte of an entry block that is still live *)
assert (KB : forall b m x, In (b, m) (ablocks B (bi_ly D) (bi_S D)) -> 0 <= m -> b <= x < b + m ->
    aview SEGS (w_H W) mem x = aview SEGS (w_H (bi_W D)) (bi_mem D) x).
{ intros b m x Hbm Hm Hx. pose proof (req_size_pos m Hm) as (_ & Hrs).
  replace x with (b + (x - b)) by lia.
  apply (K2 b m (x - b) Hbm (Permutation_in _ (Permutation_sym Hperm) Hbm)); [lia|].
  intros Hf. exact (inFP_nil _ Hf). }
unfold bytes_at, garr8 in Hbytes0 |- *. intros j Hj. destruct (Hbytes0 j Hj) as (Hv & Hr). split; [|exact Hr].
apply (cnob_cell_keep (bi_W D) W (bi_mem D) mem (bi_data D + Z.of_nat j) 1 (nth j (bi_x D) 0)); [|exact Hv].
intros x Hx. change (Z.of_nat 1) with 1 in Hx.
assert (Hsz : 0 < cnb_size D) by (unfold cnb_size; lia).
assert (Hxin : bi_data D <= x < bi_data D + cnb_size D) by (unfold cnb_size; lia).
unfold PRH_FnReader.prhReader_home, kept_at, kept_img in HHOME.
destruct (HHOME Hsz) as [[(b & m & Hbm & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbm & _ & Hb1 & Hb2)].
- destruct (HB0 (b, m) Hbm) as (Hkk & Hblk & _). cbn [fst snd] in Hkk, Hblk.
  pose proof (req_size_pos (m + cf_head) (Z.add_nonneg_nonneg _ _ Hkk Hcf)) as (_ & Hrs).
  apply (KB (b - cf_head) (m + cf_head) x Hblk ltac:(lia)). lia.
- destruct (Hro x Hxin) as (Hr0 & Hown & Herr). exact (KI x Hr0 Hown Herr).
- destruct (Hro x Hxin) as (Hr0 & Hown & Herr & _). exact (KI x Hr0 Hown Herr).
- apply (KB b m x Hbm); lia.
Qed.

(* ==== CB8 FREE: THE SEGMENT LEMMA ==== *)
Lemma cnb_seg_free : cnb_seg_freeP.
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0
  HPRE HAT HPM.
pose proof HAT as (_ & _ & _ & _ & Hnr & HR & _ & HOWN1 & _).
assert (HCD : ownl <> 0 -> cnb_cdead D) by (intros H0; destruct (HOWN1 H0) as (_ & _ & _ & _ & Hcd); exact Hcd).
pose proof (cnob_cnt24_free D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0
  HPRE HAT) as HC24.
(* the order lists, tied to the model's pj_frees when no copy was refused (the free cut's cnb_fo) *)
destruct (cnob_fos_tie D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HAT)
  as (F1 & F2 & F3 & HF1 & HF2 & HF3 & HT).
pose proof (cnob_fmid_of_free D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3
  o1 o2 o0 F1 F2 F3 HAT HC24 HF1 HF2 HF3 HT) as HM0.
eapply SRr'_bind; [exact (cnob_st_pjf1 fxk D ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 _ _ _ _ _ _ _
  P PLAW PCALL HPRE HM0 HPM)|].
intros W1 c1 _ ((ly1 & S1 & Hp1 & regs1 & mem1 & md1 & k1 & Lam1 & -> & HM1) & HPM1).
eapply SRr'_bind; [exact (cnob_st_pjf2 fxk D ly1 S1 Hp1 W1 regs1 mem1 md1 k1 Lam1 peak cnt ran nr r1 r2 r3 r ownl st2
  _ _ _ _ _ _ _ P PLAW PCALL HPRE HM1 HPM1)|].
intros W2 c2 _ ((ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & Lam2 & -> & HM2) & HPM2).
eapply SRr'_bind; [exact (cnob_st_pjf3 fxk D ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Lam2 peak cnt ran nr r1 r2 r3 r ownl st3
  _ _ _ _ _ _ _ P PLAW PCALL HPRE HM2 HPM2)|].
intros W3 c3 _ ((ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & Lam3 & -> & HM3) & HPM3).
eapply SRr'_bind; [exact (cnob_st_fr1 fxk D ly3 S3 Hp3 W3 regs3 mem3 md3 k3 Lam3 peak cnt ran nr r1 r2 r3 r ownl _
  P PLAW PCALL HPRE HM3 HPM3)|].
intros W4 c4 _ ((ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & Lam4 & -> & HM4) & HPM4).
eapply SRr'_bind; [exact (cnob_st_fr2 fxk D ly4 S4 Hp4 W4 regs4 mem4 md4 k4 Lam4 peak cnt ran nr r1 r2 r3 r ownl _
  P PLAW PCALL HPRE HM4 HPM4)|].
intros W5 c5 _ ((ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & Lam5 & -> & HM5) & HPM5).
eapply SRr'_mono; [exact (cnob_st_fr3 fxk D ly5 S5 Hp5 W5 regs5 mem5 md5 k5 Lam5 peak cnt ran nr r1 r2 r3 r ownl _
  P PLAW PCALL HPRE HM5 HPM5)|].
intros W6 c6 _ ((ly6 & S6 & Hp6 & regs6 & mem6 & md6 & k6 & Lam6 & -> & HM6) & HPM6).
split; [|exact HPM6].
pose proof HM6 as ((_ & _ & HJ6 & _) & _).
pose proof HM6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpermB6 & _).
cbn [flat_map ck_hblks map app] in HpermB6.
pose proof (cnob_bytes_exit D ly6 S6 Hp6 W6 mem6 md6 k6 HPRE HJ6 HpermB6) as Hbytes.
exists fxk, ly6, S6, Hp6, regs6, mem6, md6, k6, Lam6, peak, cnt, ran, r, ownl.
split; [reflexivity|].
apply (cnob_end_of_fmid D fxk ly6 S6 Hp6 W6 regs6 mem6 md6 k6 Lam6 peak cnt ran nr r1 r2 r3 r ownl HM6 Hnr Hbytes);
  [|exact HCD].
destruct HR as [HR | (Hr0 & Ho0 & Hran0 & _)]; [left; exact HR | right; split; [exact Hr0 | split; assumption]].
Qed.

(* ==== CB9 END: THE set_shadow_f5 CALL STEP (plan 5.2 row "CB9 End | 0x81d04 -> ret 0x81e60", call 0x81d70).
   On the fake-frame arm (s11 <> 0) the code at 0x81d68 sets a1 = 0x40, a0 = s2 (the shadow of the walk's frame F) and
   calls __asan_set_shadow_f5, which returns to 0x81d74 (CNB_SSH_RET). This is the step at the callee's entry: the
   64 shadow bytes of F become 0xf5, every other byte is kept, the walk's journal and P cross. CB9 starts after the
   frees, so the journal is at wle' (restated in place; the call keeps the world, W2 = W, so the conclusion stays
   SRr, through the engine's YGcallMxmn.aj_set_shadow_at_xmR). The stretch that reaches it (the 21 shadow stores
   0x81d04-0x81d54 and the frame magic 0x81d60) waits for IMG_TOP_B. ==== *)
Definition CNB_SSH : Z := 896.
Definition CNB_SSH_RET : Z := 900.
Lemma cnob_ret_ssh : 4096 <= bv_unsigned (Z_to_bv 64 (cnb_pc CNB_SSH_RET)) /\
  bv_unsigned (Z_to_bv 64 (cnb_pc CNB_SSH_RET)) < YM05.alloc_ceiling.
Proof. cnob_ret_tac. Qed.
Lemma cnob_ssh_slot :
  map (fun k => nth_error B_prog_listing (CNB_SLOT + k)) [222; 223; 224; 225]%nat =
  [Some (PW 0x4000593); Some (PW 0x90513); Some (PCall AS___asan_set_shadow_f5 (1%bv : bv 5)); Some (PW 0x1f8db503)].
Proof. vm_compute. reflexivity. Qed.

Lemma cnob_setsh_call : forall (fz : YK11.FPState) STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W regs mem md k
    cid pos raw (P : (word -> option byte) -> Prop),
  srr_inv_call SEGS P ->
  AJ' STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  In (cid, pos) own -> fs_frame_bytes cid = 512 ->
  getr regs 10 = w64 (shadow_addr (frame_addr ly cid pos)) -> getr regs 11 = w64 64 ->
  (spZ regs - sp0) mod 16 = 0 -> spZ regs <= sp0 -> ESTACK + (sp0 - spZ regs) <= STKa ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 1 = raw -> YK0s.ret_ok raw ->
  P mem ->
  SRr SEGS W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 (SIGMA AS___asan_set_shadow_f5)) mem (YK11.seg_rom SEGS)) md)
    (fun W2 c2 => (W2 = W /\ exists regs2 mem2 md2,
        c2 = mkCfg (@YK11.mkst fz regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
        AJ' STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem2 md2 k /\
        aregs_preserved regs regs2 /\
        (forall i, 0 <= i < 64 -> aview SEGS (w_H W) mem2 (shadow_addr (frame_addr ly cid pos) + i) = Some 245) /\
        (forall a, 0 <= a < 2 ^ 64 ->
           ~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + 64) ->
           aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)) /\
      P (ms_mem (cfg_ms c2))).
Proof.
intros fz STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W regs mem md k cid pos raw P PCALL HJ Hown HFB Ha0 Ha1
  Hal Hle Hbud Hgp Htp Hra Hraw HPM.
assert (Penv : api_env SEGS B) by (destruct PAL; assumption).
eapply SRr_mono.
{ eapply (YGcallMxmn.aj_set_shadow_at_xmR (fx := fz) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) Penv
    WLE' (wle'_refl SEGS _) (wle'_trans SEGS _)
    (SIGMA AS___asan_set_shadow_f5) 245 (ASETSH fz) W regs mem STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp md k
    cid pos (shadow_addr (frame_addr ly cid pos)) 64 (spZ regs - sp0) raw HJ Hown Ha0 Ha1).
  - lia.
  - lia.
  - rewrite HFB. change (512 / 8) with 64. lia.
  - lia.
  - exact Hal.
  - lia.
  - lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Heff & Hfr & Hkeep).
split; [|exact (PCALL _ _ Hkeep HPM)].
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Heff | exact Hfr].
Qed.

End cf.

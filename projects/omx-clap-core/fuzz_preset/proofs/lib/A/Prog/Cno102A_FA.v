(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 967 of its 1043 lines of code are new or changed and 1914 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_Base.v, with its module paths and module names changed; 702 of its 797 lines of code are new or changed and 948 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_Ro.v, with its module paths and module names changed; 912 of its 1104 lines of code are new or changed and 605 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): CA10a, the FIRST
   HALF of segment CA10 Free of the re-walk of check_no_overread (cno): the three pj_free calls, CN_FREE (1060, A'
   0x81d28) -> CN_FRCUT (1084, A' 0x81d40), in the base's generic-P FORWARD form. Lane CnoA102f.CnoA102fA (sub-lane of
   CnoA102f, a Theorem Labs lane; plan, the internal file PLAN-cno-caw-102.md 5.1 row CA10; lane brief, the internal file lane-102.md); re-fitted to
   the kit's Batch 2, to the #102 kit, and to the kit's cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) (step
   CnoABatch2.CutFA); re-fitted to the free / realloc move: pj_free's run frees, so this run crosses a free and
   concludes SRr' SEGS RZ_cf (YA0nH.v: SRrG at wle' SEGS RZ_cf), its journals at wle' SEGS RZ_cf.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   THE STATEMENT (FIXED, not restated here): Cno102A_F.v cn_seg_pjfP (concluding SRr' SEGS RZ_cf), with the cuts
   cn_at_freeR (Cno102A_Base.v) and cn_pjm / cn_at_fr / cn_ex_fr (Cno102A_F.v), each at wle' SEGS RZ_cf (the
   run from entry already crossed the readings' parse_noting, which free). NO STATE PREMISE: the former PJF-TIE is
   closed; the free cut's ownl = 0 arm carries each struct's free-order tie cn_fo (the reading's, tparse_noting_specX's
   Some arm under CFHEAD-16), and its ownl <> 0 arm carries cn_cdead D, which cn_at_fr passes on
   (`ownl <> 0 -> cn_cdead D`).
   INPUTS (by path): lib/A/Prog/Cno102A_F.v (cn_pjm with its hull list cn_hrest_pjm and the step cn_hrest_pjm_step,
   cn_pjm_of_free, cn_fr_of_pjm, cn_fpj); lib/A/Prog/Cno102A_Base.v (cn_pre read by name: cn_pre_fpre / cn_pre_univ /
   cn_pre_pk24; cn_baseR / cn_JR, the base and the journal AT A WILD BUDGET wk over a world relation, here at
   wle' SEGS RZ_cf; cn_at_freeR and its hull conjunct, cn_fo, cn_cdead, cn_prog, cn_cevs / cn_C3 / cn_pe / cn_revs3 /
   cn_fevs, cn_rd / cn_rds3, cn_ck_cno_evs, cn_doc); the kit's texts: lib/A/PRH_FnPj.v
   (tpj_free_specX: no DW, prh_head_wide; post-implication, no position or run premise at entry,
   `(v <> 0 -> ccnt24 S <= L24 + DRV)`, the
   hull premise `(v <> 0 -> hull_budget S [])`, the order list F (pj_foR); it concludes SRr' segs RZ_cf at the post
   fpostWmR .. (wle' segs RZ_cf), whose inner Q has the hull use `hull_used S S' []`, the position transfer over
   prhPj_free_evs F and `ccnt24 S' <= ccnt24 S`, read by tpfP_R_of and tpfP_R's fields; prhPj_free_evs_supply_pjf,
   prhPj_free_evs_nil, prhPj_bulk_nil_pos),
   lib/A/PRH_PjOrder.v e5917626b82b (pj_foR, pj_fdR_foR, pj_foR_fdR, pj_foR_frame), lib/A/PRH_Base.v (fpre,
   fpostWmR / fpostWR / fQmn, prh_head_wide, prh_head16, prh_run_at, prh_run_at_app_iff, prh_run_at_one, the ledger
   projections), lib/A/PRH_Reader.v (pj_nodeR_frame, pj_zeroR_frame); the engine of the cut over a world relation R:
   lib/Reusable/YCbqG.v (the journals ajournal_xwR / ajournal_xR, read by their ajxR_ projections;
   ajournal_x_materializeR), YCbqGwild.v (ajournal_xw_rebaseR / ajournal_xw_unbase0R: a plain call at a journal with
   wild budget WS), YCbqGcallW.v (aj_call_xWR, fpostW_xR), YA0nH.v / YSRrG.v (SRr', wle', wle'_refl / wle'_trans,
   SRrG_step, SRr'_bind / SRr'_ret), YGcfRehidePost.v (RZ_cf); the hull kit lib/Spec/PresetHullBudget.v
   (hull_budget, hull_used, hull_budget_nil); the model lib/Spec/PresetRun.v (pkR_app, cnt_live_pkR, ranout_refused,
   ranout_pacc, okk_true, p1_tfree), PresetReqAt.v (hlive_from_app, subm, cnt_perm, rmall_drop), PresetReqAtNoMiss.v
   (pacc, parse_ok, rmall_perm), PjGrammar.v (G7_1), lib/A/CfRoomLivePreset.v (preset_ccnt24); kit
   lib/A/Prog/Cno102_FKit.v 16b038eac014 (pjf_fd_of_node, pjf_nodeR_lblk), lib/Prog/PvFdZeroR.v (pv_fd_zeroR);
   listing lib/A/Listing_prog.v (slots 201 + off / 4: PW mv a0,s9 at 1060; PCall AS_pj_free 1 at 1064 / 1072 / 1080;
   PW ld a0,48(s1) at 1068; PW mv a0,s3 at 1076). The hand steps, the frame chain and the frame keep are copied (prefix
   cfa_) from lane CnoA102r.CnoA678's lib/A/Prog/Cno102A_Ro.v (a working branch 8bc94560f61: cn_step /
   cn_hs_addi / cn_hs_ld / cn_hs_call / cn_chain / cn_open_keep / cn_entry_facts) and the post-state transfer follows
   lane CnoA102r.CnoApn's Cno102A_Rpn.v cn_pn_call.
   THE PROOF: cn_pjm_of_free; then three times [one instruction setting a0 (mv a0, s9 / ld a0, 48(s1) = d2 by cn_slots /
   mv a0, s3), the jal, ONE step lemma cfa_pjf_call]; then cn_fr_of_pjm. g_own_ran_out / g_most at ownl cross each call
   in the LEDGER (the text's ledger pre and post carry the same most := ci_most D, own := ownl) and the hand steps
   unchanged (they write no memory). cfa_pjf_call is the call of the kit's text at the callee's entry through
   YCbqGcallW.aj_call_xWR at R := wle' SEGS RZ_cf (window e = 0, o = cn_S1 D - cn_sp0 D, FP = the text's
   `(v, v + 56) :: ablocks_fp (prhPj_hbl D)`: v in the own class-3 frame, D's blocks new since entry), and the post
   moved back into cn_pjm for the remaining structs (the frame, its shadow and the real stack above s1 by the callee
   journal's frame and stack clauses, the other trees' blocks by its block clause, arodata_okP by its image clause with
   cn_img's cni_pst_rw); P across the call by srr_inv_call at fpostWmR's memnorm keep; the steps read memory only.
   The callee's fpre is built at the run's float state fxk, its frm_zero from cn_baseR. No fact here is moved by the
   world relation (every keep is a journal clause at the post's own world), so wle' costs nothing beyond the names.
   THE WILD BUDGET (the cut's journal, cn_JR at wk = 6 from the compare on): pj_free is a plain callee (fpostWmR, no
   wild site), so each call runs on the journal REBASED to the empty budget (YCbqGwild.ajournal_xw_rebaseR: the entry
   with its depot moved to the call state's) and comes back with YCbqGwild.ajournal_xw_unbase0R at the cut's own WS
   (the inclusion is the journal's ajxR_wild); WS and its wbudget [] 6 are unchanged across the three calls.
   THE HULL BUDGET the text asks at each call (`v <> 0 -> hull_budget S []`): from cn_pjm's last conjunct, the budget
   for the list cn_hrest_pjm D rest (the free cut's rd0 list, then one stage per pj_free done), by
   PresetHullBudget.hull_budget_nil; the call uses [] (its post's `hull_used S S' []`), and cn_hrest_pjm_step gives the
   next cut's budget from it. The hand steps keep the astate, so the conjunct rides through them. No allocator call
   is made here, so no admission (cf_hull_ok) is asked.
   THE EVENTS (f97c's progress form). Under ownl = 0 the free cut gives cn_prog D (cn_cevs ++ cn_revs3 o1 o2 o0) S
   (cn_cevs = cn_C3, the copies non-NULL), cn_rds3, and each struct's cn_fo; cn_fo at cf_head = PresetReqAt.HEAD (HH)
   and n := DOC_D (the tree's depth is at most MAXD by cn_doc) gives the order list F at CN_FREE with the model's
   pj_frees as its sizes (cfa_fo_tie). cfa_pjf_call posts, for any events E and grant o F is tied to (cfa_tie),
   cn_prog D E S -> cn_prog D (E ++ cfa_ev D o st) S': the live set by the text's ablocks permutation (rs_live =
   map snd blocks; the freed sizes are the model's HBulk, cfa_live_bulk), the position by the text's transfer
   (cfa_pos_ev: prhPj_free_evs_supply_pjf; a filled struct with no blocks is the model's HBulk [], stepped over by
   prhPj_bulk_nil_pos; a zero struct has F = [] and no event). The three cfa_ev are cn_fpj (cfa_fpj under cn_rds3: a
   reading that ran out left the zero struct, PresetRun.ranout_refused). Under ownl <> 0 the free cut's cn_cdead D is
   carried to CN_FRCUT (it names only the entry state).
   THE CLASS-24 BOUND the text asks at each call (v = the struct, never 0): from the free cut's live set in either arm
   (ownl = 0: cn_C3 ++ cn_revs3; ownl <> 0, the cut's refused arm: cn_cevs), a sub-multiset of a prefix of the
   all-granted list whose class-24 peak cn_pre bounds (cfa_cnt_free / cfa_cnt_cevs: a reading under grant o leaves
   nothing if it ran out, PresetRun.ranout_pacc, else the all-granted reading's blocks, PjGrammar.G7_1), then
   CfRoomLivePreset.preset_ccnt24 (cfa_c24); each call keeps it (its post's ccnt24 S' <= ccnt24 S).
   NAMED ARGUMENTS (Section hypotheses): IMG (the base's cn_img; cni_base for the return slots, cni_pst_rw for
   arodata_okP across the call; agreed by CnoA102f 14:5xZ); HPJFREE (the kit's text tpj_free_specX at B, ARcfx, CTX0,
   n := DOC_D, for any float state: the run is at fxk; owned by the kit); HH (PRH_Base.prh_head16, CFHEAD-16's walk
   hypothesis, PRH_Base.v :243-248: it opens cn_fo, and the text's prh_head_wide follows from it, cfa_hw; its instance
   witness at CfParams_preset is cn_head16_preset below, by reflexivity). No other.
   Numerals: 1060 .. 1084 (DERIVED offsets inside cno); 32 / 128 / 224 / 56 / 280 / 512 / 64 / 48 / 88 / 184 / 192 / 208
   (LENGTH: struct, frame, shadow and slot offsets); register numbers (WORD); 2 ^ 28 / 2 ^ 40 / 2 ^ 64 (LENGTH); 24 (the
   allocator class YG00.kBatchClass, by its definition); 8 (LENGTH: prh_head_wide's word). No ADDRESS. *)
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
(* the step relation over a world relation and its re-hide instance (SRr' at the zone RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger PvFdZeroR ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetLiveBounds
  PresetRoom PresetReqAt PresetReqAtNoMiss PresetRun PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_PjOrder
  PRH_FnAlloc PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit Cno102_FKit
  Cno102A_Base Cno102A_F.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YN01 YCbqGwild.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* MEASURED NEEDED (lead's 15:2xZ correction checked): without this reset the file fails at cfa_open_keep0's lia over
   Z.div (cb log build-20261029T153007Z, line 159 "No applicable tactic"); Cno102A_Ro.v carries the same reset *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ==== 1. pure helpers (Cno102A_Ro.v ro_* / cn_regsat_*, renamed) ==== *)
Lemma cfa_land32 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. replace (-32) with (Z.lnot (Z.ones 5)) by reflexivity.
assert (Hl : Z.land x (Z.lnot (Z.ones 5)) = Z.ldiff x (Z.ones 5)).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lnot_spec, Z.ldiff_spec by lia. reflexivity. }
rewrite Hl, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
rewrite Z.mod_eq by lia. lia.
Qed.

Lemma cfa_div8 : forall a, 8 * (a / 8) <= a < 8 * (a / 8) + 8.
Proof.
intros a. pose proof (Z.div_mod a 8 ltac:(lia)) as H1. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as H2.
revert H1 H2. generalize (a / 8) (a mod 8). intros q r H1 H2. lia.
Qed.

Lemma cfa_rdword_kept : forall (rd rd' : reader) lo hi x,
  (forall a, lo <= a < hi -> rd' a = rd a) -> lo <= x -> x + 8 <= hi -> rdword rd' x = rdword rd x.
Proof. intros rd rd' lo hi x Hk H1 H2. apply rdword_ext. intros kk Hkk. apply Hk. lia. Qed.

Lemma cfa_getr_same : forall regs (r : bv 5) v, bv_eqb r 0%bv = false -> getr (regupd regs r v) r = v.
Proof. intros regs r v H. apply getr_same. intros E. subst r. discriminate H. Qed.
Lemma cfa_getr_other : forall regs (r r' : bv 5) v, bv_eqb r' r = false -> getr (regupd regs r v) r' = getr regs r'.
Proof. intros regs r r' v H. apply getr_other. intros E. subst r'. rewrite bv_eqb_refl in H. discriminate H. Qed.
Ltac cfa_getr := repeat first [rewrite cfa_getr_same by reflexivity | rewrite cfa_getr_other by reflexivity].

Lemma cfa_vaddi0 : forall (x : word), v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma cfa_regsat_get : forall regs l (r : bv 5) v, cn_regsat regs l -> In (r, v) l -> getr regs r = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma cfa_regsat_kept : forall regs regs' l, cn_regsat regs l ->
  Forall (fun p : bv 5 * Z => getr regs' (fst p) = getr regs (fst p)) l -> cn_regsat regs' l.
Proof.
intros regs regs' l H K. unfold cn_regsat in *. rewrite Forall_forall in *. intros p Hp.
rewrite (K p Hp). exact (H p Hp).
Qed.
Lemma cfa_regsat_pres : forall regs regs' l, cn_regsat regs l -> aregs_preserved regs regs' ->
  Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p))) l -> cn_regsat regs' l.
Proof.
intros regs regs' l H HP HF. apply (cfa_regsat_kept regs regs' l H). rewrite Forall_forall in *.
intros [r v] Hin. cbn [fst]. specialize (HF (r, v) Hin). cbn [fst] in HF.
pose proof (HP (bv_unsigned r) HF) as E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma cfa_regsat_upd : forall regs l (r : bv 5) w, Forall (fun p : bv 5 * Z => bv_eqb (fst p) r = false) l ->
  cn_regsat regs l -> cn_regsat (regupd regs r w) l.
Proof.
intros regs l r w Hn H. apply (cfa_regsat_kept regs _ l H). rewrite Forall_forall in *.
intros p Hp. apply cfa_getr_other. exact (Hn p Hp).
Qed.
Lemma cfa_regsat_incl : forall regs l l', cn_regsat regs l -> incl l' l -> cn_regsat regs l'.
Proof.
intros regs l l' H Hi. unfold cn_regsat in *. apply Forall_forall. intros p Hp.
exact (proj1 (Forall_forall _ _) H p (Hi p Hp)).
Qed.
Ltac cfa_in := cbn [app In]; repeat (first [left; reflexivity | right]).
Ltac cfa_cs :=
  lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  unfold acallee_saved; lia.

(* two members of the two halves of a duplicate-free list differ *)
Lemma cfa_nodup_sep : forall (A : Type) (l1 l2 : list A) x y, List.NoDup (l1 ++ l2) -> In x l1 -> In y l2 -> x <> y.
Proof.
intros A l1. induction l1 as [|z l1 IH]; intros l2 x y H Hx Hy E; [destruct Hx|].
cbn [app] in H. apply NoDup_cons_iff in H as (Hn & Hd). destruct Hx as [<- | Hx].
- apply Hn. apply in_or_app. right. rewrite E. exact Hy.
- exact (IH l2 x y Hd Hx Hy E).
Qed.
Lemma cfa_nodup_fst : forall (l1 l2 l3 : list (Z * Z)) x y, List.NoDup (map fst ((l1 ++ l2) ++ l3)) ->
  In x l1 -> In y l2 -> fst x <> fst y.
Proof.
intros l1 l2 l3 x y H Hx Hy. rewrite <- app_assoc, !map_app in H.
apply (cfa_nodup_sep _ (map fst l1) (map fst l2 ++ map fst l3)); [exact H | apply in_map; exact Hx |].
apply in_or_app. left. apply in_map. exact Hy.
Qed.

(* a struct's opening is kept when the frame's 64 shadow bytes are (Cno102A_Ro.v cn_open_keep) *)
Lemma cfa_open_keep0 : forall (rd rd' : reader) F c, F mod 32 = 0 -> 0 <= F -> 32 <= c <= 224 ->
  c mod 8 = 0 ->
  (forall a, shadow_addr F <= a < shadow_addr F + 64 -> rd' a = rd a) ->
  range_addressable rd SHADOW_OFF (F + c) 56 /\ shadow_hull_vis rd (F + c) 56 ->
  range_addressable rd' SHADOW_OFF (F + c) 56 /\ shadow_hull_vis rd' (F + c) 56.
Proof.
intros rd rd' F c HF HF0 Hc Hc8 Hk (Hra & Hhv).
assert (Ef : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
set (f := F / 32) in *. clearbody f. subst F.
split.
- apply (range_addressable_agree rd rd' SHADOW_OFF (32 * f + c) 56); [|exact Hra].
  intros x Hx. apply Hk. unfold shadow_of_addr, shadow_addr, SHADOW_OFF. lia.
- intros s Hs. rewrite Hk; [apply Hhv; exact Hs|].
  assert (Ec : c = 8 * (c / 8)) by (pose proof (Z.div_mod c 8 ltac:(lia)); lia).
  set (c' := c / 8) in *. clearbody c'. subst c.
  assert (E0 : 32 * f / 8 = 4 * f) by (replace (32 * f) with ((4 * f) * 8) by lia; apply Z.div_mul; lia).
  assert (E1 : (32 * f + 8 * c') / 8 = 4 * f + c')
    by (replace (32 * f + 8 * c') with ((4 * f + c') * 8) by lia; apply Z.div_mul; lia).
  assert (E2 : (32 * f + 8 * c' + 56 - 1) / 8 = 4 * f + c' + 6).
  { replace (32 * f + 8 * c' + 56 - 1) with (7 + (4 * f + c' + 6) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  unfold shadow_addr, SHADOW_OFF in *. rewrite E1, E2 in Hs. rewrite E0.
  pose proof (cfa_div8 (2147450880 + (4 * f + c'))) as D1. pose proof (cfa_div8 (2147450880 + (4 * f + c' + 6))) as D2.
  revert Hs D1 D2. generalize ((2147450880 + (4 * f + c')) / 8) ((2147450880 + (4 * f + c' + 6)) / 8).
  intros q1 q2 Hs D1 D2. clear - Hs D1 D2 Hc. lia.
Qed.
Lemma cfa_open_keep : forall (rd rd' : reader) F x, F mod 32 = 0 -> 0 <= F -> F + 32 <= x <= F + 224 ->
  x mod 8 = 0 ->
  (forall a, shadow_addr F <= a < shadow_addr F + 64 -> rd' a = rd a) ->
  range_addressable rd SHADOW_OFF x 56 /\ shadow_hull_vis rd x 56 ->
  range_addressable rd' SHADOW_OFF x 56 /\ shadow_hull_vis rd' x 56.
Proof.
intros rd rd' F x HF HF0 Hx Hx8 Hk Ho. replace x with (F + (x - F)) in Ho |- * by lia.
apply (cfa_open_keep0 rd rd' F (x - F) HF HF0 ltac:(lia) ltac:(lia) Hk Ho).
Qed.

(* the listing's slots of this stretch (Listing_prog.v 7ed1529926bd at the cut, slot 201 + off / 4), closed facts *)
Lemma cfa_off_val : CN_OFF = 804.
Proof. reflexivity. Qed.
Lemma cfa_l1064 : plookup A_prog_tpi_cno (CN_OFF + 1064) = Some (PCall AS_pj_free 1%bv).
Proof. vm_compute. reflexivity. Qed.
Lemma cfa_l1072 : plookup A_prog_tpi_cno (CN_OFF + 1072) = Some (PCall AS_pj_free 1%bv).
Proof. vm_compute. reflexivity. Qed.
Lemma cfa_l1080 : plookup A_prog_tpi_cno (CN_OFF + 1080) = Some (PCall AS_pj_free 1%bv).
Proof. vm_compute. reflexivity. Qed.

(* the slot word at off and its decoding, each by vm_compute on a closed term (pj_set_seg_tail.v pjs_fd's form) *)
Ltac cfa_fd off Hl Hd :=
  let r := eval vm_compute in (plookup A_prog_tpi_cno (CN_OFF + off)) in
  lazymatch r with
  | Some (PW ?w) =>
      assert (Hl : plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w)) by (vm_compute; reflexivity);
      let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
      assert (Hd : decode_any (Z_to_bv 32 w) = d) by (vm_compute; reflexivity)
  end.

(* ==== 2. the hand steps over cn_cfg (Cno102A_Ro.v's cn_step .. cn_hs_call, renamed): memory read only ==== *)
Section stp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).

Lemma cfa_step : forall (W : world SEGS) fxk regs mem md regs' off off' Q,
  0 <= off < 2 ^ 29 -> 0 <= off' < 2 ^ 29 ->
  RiscvSemantics.step SEGS (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CN_OFF + off))) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxk regs' (Z_to_bv 64 (BASE + (CN_OFF + off'))) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) ->
  (forall X, SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc off') regs' mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md regs' off off' Q Ho Ho' Hst HK.
unfold cn_cfg, cn_pc, w64, SRr'. replace (BASE + CN_OFF + off) with (BASE + (CN_OFF + off)) by lia.
eapply (SRrG_step SEGS (wle' SEGS RZ_cf) pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk); exact Hst |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold cn_cfg, cn_pc, w64, SRr' in HK.
replace (BASE + CN_OFF + off') with (BASE + (CN_OFF + off')) in HK by lia. exact HK.
Qed.

Lemma cfa_pc4 : forall off, 0 <= off < 2 ^ 29 ->
  v_addi (Z_to_bv 64 (BASE + (CN_OFF + off))) 4 = Z_to_bv 64 (BASE + (CN_OFF + (off + 4))).
Proof.
intros off Ho. pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cfa_off_val as HO.
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma cfa_hs_addi : forall (W : world SEGS) fxk regs mem md Q off off' w rd rs imm,
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc off') (regupd regs rd (v_addi (getr regs rs) (bv_signed imm)))
     mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' w rd rs imm Hpl Hdec Hrd Ho -> HK.
apply (cfa_step W fxk regs mem md (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
rewrite (@step_addi fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm
  (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
rewrite Hrd, (cfa_pc4 off ltac:(lia)). reflexivity.
Qed.

Lemma cfa_hs_ld : forall (W : world SEGS) fxk regs mem md Q off off' w rd rs imm a v,
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + bv_signed imm = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall X, SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc off') (regupd regs rd (w64 v)) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' w rd rs imm a v Hpl Hdec Hrd Ho -> Ha Ha0 Ha8 Hv HK.
apply (cfa_step W fxk regs mem md (regupd regs rd (w64 v)) off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
pose proof (val_mem_of_rdword SEGS (w_H W) mem a v Hv) as Hvm.
destruct (YN01.word_mem_ld SEGS (mrestrict (w_H W) mem) a v Hvm Ha0 Ha8) as (bs & Hbs & Hbv).
assert (Eaddr : v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a) by (unfold v_addi; rewrite Ha; reflexivity).
rewrite (@step_ld fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm bs (Z_to_bv 64 v)
  (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec
  ltac:(rewrite Eaddr; exact Hbs) Hbv).
rewrite Hrd, (cfa_pc4 off ltac:(lia)). reflexivity.
Qed.

(* the PCall jal of a listing slot: pc = SIGMA s, ra = the next offset *)
Lemma cfa_hs_call : forall (W : world SEGS) fxk regs mem md Q off off' s,
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PCall s 1%bv) -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (SIGMA s) (regupd regs 1%bv (w64 (cn_pc off'))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' s Hpl Ho -> HK.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cfa_off_val as HO.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA A_prog_listing pa_cert (CN_OFF + off) (PCall s 1%bv) Hpl)
  as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + (CN_OFF + off))) as [wz|] eqn:Hf; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try (cbn in Hck; discriminate Hck).
apply andb_prop in Hck as (Hck & Hsig). apply andb_prop in Hck as (Hrd & _). apply Z.eqb_eq in Hsig.
assert (Erd : rd = 1%bv).
{ unfold bv_eqb in Hrd. apply Z.eqb_eq in Hrd. apply bv_eq. symmetry. exact Hrd. }
subst rd.
pose proof (pa_fetch_ok _ _ Hf) as Hfw.
unfold cn_cfg, cn_pc, w64, SRr'. replace (BASE + CN_OFF + off) with (BASE + (CN_OFF + off)) by lia.
eapply (SRrG_step SEGS (wle' SEGS RZ_cf) pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk);
  exact (@step_jal_link fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ 1%bv imm Hfw
           (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec) |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold cn_cfg, cn_pc, w64, SRr' in HK.
replace (BASE + CN_OFF + (off + 4)) with (BASE + (CN_OFF + (off + 4))) in HK by lia.
change (bv_eqb (1%bv : bv 5) 0%bv) with false. cbv iota.
rewrite (cfa_pc4 off ltac:(lia)).
replace (btgt (Z_to_bv 64 (BASE + (CN_OFF + off))) (bv_signed imm)) with (Z_to_bv 64 (SIGMA s)); [exact HK|].
unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Hsig.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ---- the six instructions of the stretch ---- *)
(* 1060  mv a0, s9 *)
Lemma cfa_mv_1060 : forall (W : world SEGS) fxk regs mem md Q,
  (forall X, SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc 1064) (regupd regs 10%bv (getr regs 25%bv)) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc 1060) regs mem md) Q.
Proof.
intros W fxk regs mem md Q HK.
cfa_fd 1060 Hl Hd.
eapply (cfa_hs_addi W fxk regs mem md Q 1060 1064 _ _ _ _ Hl Hd); [vm_compute; reflexivity | lia | reflexivity |].
intros X.
lazymatch goal with |- SRr' _ _ _ (cn_cfg _ _ (regupd _ ?rd (v_addi (getr _ ?rs) (bv_signed ?im))) _ _) _ =>
  replace rd with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
  replace rs with (25%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
  replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
rewrite cfa_vaddi0. exact (HK X).
Qed.

(* 1076  mv a0, s3 *)
Lemma cfa_mv_1076 : forall (W : world SEGS) fxk regs mem md Q,
  (forall X, SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc 1080) (regupd regs 10%bv (getr regs 19%bv)) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc 1076) regs mem md) Q.
Proof.
intros W fxk regs mem md Q HK.
cfa_fd 1076 Hl Hd.
eapply (cfa_hs_addi W fxk regs mem md Q 1076 1080 _ _ _ _ Hl Hd); [vm_compute; reflexivity | lia | reflexivity |].
intros X.
lazymatch goal with |- SRr' _ _ _ (cn_cfg _ _ (regupd _ ?rd (v_addi (getr _ ?rs) (bv_signed ?im))) _ _) _ =>
  replace rd with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
  replace rs with (19%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
  replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
rewrite cfa_vaddi0. exact (HK X).
Qed.

(* 1068  ld a0, 48(s1) *)
Lemma cfa_ld_1068 : forall (W : world SEGS) fxk regs mem md Q s1 v,
  getr regs 9%bv = w64 s1 -> 0 <= s1 -> s1 + 56 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) (s1 + 48) = Some v ->
  (forall X, SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc 1072) (regupd regs 10%bv (w64 v)) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc 1068) regs mem md) Q.
Proof.
intros W fxk regs mem md Q s1 v G9 H0 H64 Hv HK.
cfa_fd 1068 Hl Hd.
eapply (cfa_hs_ld W fxk regs mem md Q 1068 1072 _ _ _ _ (s1 + 48) v Hl Hd);
  [vm_compute; reflexivity | lia | reflexivity | | lia | lia | exact Hv |].
- lazymatch goal with |- bv_unsigned (getr _ ?rs) + bv_signed ?im = _ =>
    replace rs with (9%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 48 by (vm_compute; reflexivity) end.
  rewrite G9. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- intros X.
  lazymatch goal with |- SRr' _ _ _ (cn_cfg _ _ (regupd _ ?rd _) _ _) _ =>
    replace rd with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity) end.
  exact (HK X).
Qed.

(* 1064 / 1072 / 1080  jal pj_free *)
Lemma cfa_jal_pjf : forall (W : world SEGS) fxk regs mem md Q off,
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PCall AS_pj_free 1%bv) -> 0 <= off < 2 ^ 28 ->
  (forall X, SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (SIGMA AS_pj_free) (regupd regs 1%bv (w64 (cn_pc (off + 4)))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off Hpl Ho HK.
exact (cfa_hs_call W fxk regs mem md Q off (off + 4) AS_pj_free Hpl Ho eq_refl HK).
Qed.
End stp.

(* ==== 3. the segment ==== *)
Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
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
Variable B : asyms.
(* the walk's allocator relation, the cf instance (S1KitAlloc's ARxs, YGcallcf.v; FuzzFree.v:389, Caw102A_Base.v) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARcfx).
#[local] Notation STK := STK_check_no_overread.
Variable CTX0 : list (list Z).

(* ---- THE NAMED ARGUMENTS ---- *)
(* the base's image facts (Cno102A_Base.v cn_img): cni_base for the return slots, cni_pst_rw for arodata_okP *)
Hypothesis IMG : cn_img B.
(* The kit's text of pj_free (PRH_FnPj.v tpj_free_specX: no DW, prh_head_wide; post-implication, no position at entry; the
   hull premise `v <> 0 -> hull_budget S []`; its run frees, so it concludes SRr' segs RZ_cf at the post
   fpostWmR .. (wle' segs RZ_cf), whose inner Q has `hull_used S S' []` second) at n := DOC_D, for ANY float state
   (the run is at fxk) *)
Hypothesis HPJFREE : forall fz : YK11.FPState,
  tpj_free_specX (fx := fz) (PI := prh_img_A) (RL := CF_RL) B ARcfx SK CTX0 DOC_D.
(* CFHEAD-16, the walk's hypothesis in the text's own spelling (PRH_Base.v :243-248): it opens the free cut's
   cn_fo; discharged at CfParams_preset by reflexivity (cn_head16_preset, after the Section) *)
Hypothesis HH : PRH_Base.prh_head16.

(* pj_free's prh_head_wide (8 <= cf_head) from HH (cf_head = PresetReqAt.HEAD = 16) *)
Lemma cfa_hw : prh_head_wide.
Proof. pose proof HH as E. unfold PRH_Base.prh_head16 in E. unfold prh_head_wide. rewrite E. unfold PresetReqAt.HEAD. lia. Qed.

(* the laws of the cf relation (FuzzFree.v:405-406) *)
Lemma cfa_laws : AR_laws_x SEGS B ARcfx cf_head.
Proof. exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)). Qed.

Lemma cfa_stk_val : STK = 27424.
Proof. vm_compute. reflexivity. Qed.
Lemma cfa_stkf_bnd : 0 <= STK_pj_free DOC_D /\ STK_pj_free DOC_D + 208 <= STK.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* the facts of the entry the call uses (Cno102A_Ro.v cn_entry_facts) *)
Lemma cfa_entry_facts : forall D, cn_pre (fx := fx) B ARcfx CTX0 D ->
  cn_sp0 D mod 16 = 0 /\ YM05.alloc_ceiling <= ly_stk_lo (ci_ly D) /\ ly_stk_lo (ci_ly D) + STK <= cn_sp0 D /\
  cn_sp0 D <= ly_top (ci_ly D) /\ ly_top (ci_ly D) <= ly_stk_hi (ci_ly D) /\ ly_stk_hi (ci_ly D) <= 2 ^ 47 /\
  cn_sp0 D + 64 <= ly_stk_hi (ci_ly D) /\
  getr (ci_regs D) 3%bv = w64 (as_gp B) /\ getr (ci_regs D) 4%bv = w64 (as_tp B) /\ 4096 <= raZ (ci_regs D) /\
  achain (ci_ly D) (aview SEGS (w_H (ci_W D)) (ci_mem D)) (cn_sp0 D) (s0Z (ci_regs D)) (ci_ch D) /\
  ARcfx (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D).
Proof.
intros D HPRE. pose proof (cn_pre_fpre (fx := fx) B ARcfx CTX0 D HPRE) as HFP.
destruct HFP as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & HROD0 & HSTKHI & HRAC & _).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
unfold cn_sp0. do 11 (split; [first [assumption | lia] |]). exact HAR0.
Qed.

Lemma cfa_S1_facts : forall D, cn_sp0 D mod 16 = 0 ->
  cn_sp0 D - 208 <= cn_S1 D <= cn_sp0 D - 192 /\ cn_S1 D mod 32 = 0.
Proof. intros D H. unfold cn_S1. rewrite cfa_land32. lia. Qed.

(* the frame chain at a cno call state: s0 = the entry sp (Cno102A_Ro.v cn_chain); at a cut after a free (the base at
   wle' SEGS RZ_cf) *)
Lemma cfa_chain : forall D fxk ly S Hp W regs mem md k wk,
  cn_pre (fx := fx) B ARcfx CTX0 D ->
  cn_baseR (fx := fx) B ARcfx (wle' SEGS RZ_cf) D fxk ly S Hp W regs mem md k wk ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) (cn_S1 D) (cn_sp0 D) ch1.
Proof.
intros D fxk ly S Hp W regs mem md k wk HPRE HB.
destruct (cfa_entry_facts D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _ & _ & Hra40 & Hch0 & _).
pose proof cfa_stk_val as HSTKv.
destruct (cfa_S1_facts D Hal16) as (HS1a & HS1b).
destruct HB as (_ & _ & HJ & _ & HSV & _).
destruct HJ as (WS & HJ & _).
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_hi HJ) as F1.
assert (Etop : ly_top ly = ly_top (ci_ly D)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
destruct (Z_lt_le_dec (cn_sp0 D) (ly_top (ci_ly D) - 16)) as [Hlt|Hge].
- exists ((cn_sp0 D, raZ (ci_regs D), s0Z (ci_regs D)) :: ci_ch D).
  apply (achain_ly_top (ci_ly D) ly); [exact Etop|].
  pose proof (proj1 (Forall_forall _ _) HSV (184, 1%bv) ltac:(cfa_in)) as V1.
  pose proof (proj1 (Forall_forall _ _) HSV (176, 8%bv) ltac:(cfa_in)) as V8.
  cbn [fst snd] in V1, V8.
  apply (achain_push (ci_ly D) (aview SEGS (w_H (ci_W D)) (ci_mem D)) (aview SEGS (w_H W) mem) (cn_sp0 D)
    (s0Z (ci_regs D)) (raZ (ci_regs D)) (ci_ch D) (cn_S1 D) Hch0).
  + lia.
  + intros a Ha. apply F1; lia.
  + replace (cn_sp0 D - 8) with (cn_sp0 D - 192 + 184) by lia. exact V1.
  + replace (cn_sp0 D - 16) with (cn_sp0 D - 192 + 176) by lia. exact V8.
  + exact Hra40.
  + lia.
  + lia.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* the three return slots: code pointers below the ceiling (Cno102A_Ro.v cn_ro_ret_ok's form) *)
Definition cfa_rets : list Z := [1068; 1076; 1084].
Lemma cfa_ret_ok : forall ret, In ret cfa_rets ->
  4096 <= cn_pc ret < YM05.alloc_ceiling /\ YK0s.ret_ok (w64 (cn_pc ret)) /\ 0 <= ret < 2 ^ 28.
Proof.
intros ret Hin. pose proof (cni_base B IMG) as HB. pose proof cfa_off_val as HO.
assert (H : forall k, 0 <= k < 2 ^ 40 -> match plookup A_prog_tpi_cno k with Some _ => true | None => false end = true ->
  BASE + k < YM05.alloc_ceiling) by (intros kk Hk Hl; exact (@pa_slot_lt_ceil_b _ _ PL_cno_A PA kk Hk Hl)).
unfold cn_pc, w64. replace (BASE + CN_OFF + ret) with (BASE + (CN_OFF + ret)) by lia.
cbn [cfa_rets In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; (split; [split; [rewrite HB; vm_compute; discriminate | apply H;
  [rewrite HO; lia | vm_compute; reflexivity]] | split; [apply ret_ok_codeptr_v; [rewrite HO; lia | vm_compute; reflexivity] | lia]]).
Qed.

(* the journal at a wild budget, at the materialised model (YCbqG.ajournal_x_materializeR between a rebase and an
   unbase, at wle' SEGS RZ_cf: the step keeps the depot) *)
Lemma cfa_J_mat : forall D ly S Hp W mem md k wk X,
  cn_JR B ARcfx (wle' SEGS RZ_cf) D ly S Hp W mem md k wk ->
  cn_JR B ARcfx (wle' SEGS RZ_cf) D ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof.
intros D ly S Hp W mem md k wk X (WS & HJ & HBUD). exists WS. split; [|exact HBUD].
apply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (st_depot S) WS); [|exact (ajxR_wild HJ)].
exact (ajournal_x_materializeR SEGS B prh_pst ARcfx cfa_laws pa_segs_low (wle' SEGS RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X
  (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf)
     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
Qed.

(* cn_pjm at the materialised model, at a register file that keeps gp / tp *)
Lemma cfa_pjm_mat : forall D fxk ly S Hp W regs regs' mem md k Lam peak cnt ran ownl r1 r2 r3 rest X,
  cn_pjm (fx := fx) B D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest ->
  getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
  cn_pjm (fx := fx) B D fxk ly S Hp W regs' mem (with_vm_backing (m_vm_lazy md) X md) k Lam peak cnt ran ownl r1 r2 r3
    rest.
Proof.
intros D fxk ly S Hp W regs regs' mem md k Lam peak cnt ran ownl r1 r2 r3 rest X HM E3 E4.
destruct HM as ((Hz & Hk & HJ & HF & HSV & R3 & R4 & HRO) & HR). split; [|exact HR].
split; [exact Hz|]. split; [exact Hk|].
split; [exact (cfa_J_mat D ly S Hp W mem md k 6 X HJ)|].
split; [exact HF|]. split; [exact HSV|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact HRO.
Qed.

(* the same across the two steps before a call (a0 then ra written) *)
Lemma cfa_pjm_step2 : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest X1 X2 v ra,
  cn_pjm (fx := fx) B D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest ->
  cn_pjm (fx := fx) B D fxk ly S Hp W (regupd (regupd regs 10%bv v) 1%bv ra) mem
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X1 md)) X2 (with_vm_backing (m_vm_lazy md) X1 md))
    k Lam peak cnt ran ownl r1 r2 r3 rest.
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest X1 X2 v ra HM.
apply (cfa_pjm_mat D fxk ly S Hp W (regupd regs 10%bv v)).
- apply (cfa_pjm_mat D fxk ly S Hp W regs); [exact HM | cfa_getr; reflexivity | cfa_getr; reflexivity].
- cfa_getr. reflexivity.
- cfa_getr. reflexivity.
Qed.

(* ---- the model's side of the three pj_free (the cut's text, as f97c's: post-implication, no position at entry) ---- *)
(* a struct's pj_free event: the model's HBulk of pj_frees at the reading's grant o for a struct a reading filled,
   none for a zero struct (a refused or skipped reading); cfa_fpj below ties the three to the base's cn_fpj *)
Definition cfa_ev (D : cn_in) (o : option nat) (st : cn_st) : list PresetReqAt.hev :=
  match st with
  | Some _ => [PresetReqAt.HBulk (PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o) (ci_x D))]
  | None => []
  end.
(* the order list F of a filled struct has the model's pj_frees as its sizes (what the free cut's cn_fo gives at
   cf_head = HEAD, cfa_fo_tie) *)
Definition cfa_tie (D : cn_in) (o : option nat) (st : cn_st) (F : list (Z * Z)) : Prop :=
  forall t Dd, st = Some (t, Dd) ->
    map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o) (ci_x D).
(* the live requests a reading under grant o leaves (PresetReqAtNoMiss.pacc) *)
Definition cfa_pk (D : cn_in) (o : option nat) : list Z :=
  PresetReqAtNoMiss.pacc ReaderRes.jr_strtod (ci_x D) (PresetRun.okof o).

Lemma cfa_tie_none : forall D o st F, st = None -> cfa_tie D o st F.
Proof. intros D o st F -> t Dd E. discriminate E. Qed.

(* a made reading's struct: the event is the model's p1_tfree *)
Lemma cfa_ev_rd : forall D o st, cn_rd D o st -> cfa_ev D o st = PresetRun.p1_tfree ReaderRes.jr_strtod (ci_x D) o.
Proof.
intros D o [[t Dd]|] H; cbv beta iota delta [cn_rd] in H; cbv beta iota delta [cfa_ev PresetRun.p1_tfree];
  rewrite H; reflexivity.
Qed.

(* a reading that ran out leaves the zero struct (PresetRun.ranout_refused) *)
Lemma cfa_ro_none : forall D o st, cn_ro D o = true -> cn_rd D o st -> st = None.
Proof.
intros D o [[t Dd]|] Hro H; [|reflexivity].
cbv beta iota delta [cn_rd] in H. unfold cn_ro in Hro.
rewrite (PresetRun.ranout_refused ReaderRes.jr_strtod (ci_x D) o Hro) in H. discriminate H.
Qed.

(* the three pj_free events are the base's cn_fpj (the readings' ties cn_rds3) *)
Lemma cfa_fpj : forall D o1 o2 o0 st1 st2 st3, cn_rds3 D o1 o2 o0 st1 st2 st3 ->
  cn_fpj D o1 o2 o0 = cfa_ev D o1 st1 ++ cfa_ev D o2 st2 ++ cfa_ev D o0 st3.
Proof.
intros D o1 o2 o0 st1 st2 st3 H. unfold cn_rds3 in H. unfold cn_fpj.
assert (EN : forall o, cfa_ev D o None = []) by reflexivity.
destruct H as (H1 & H23).
destruct (cn_ro D o1) eqn:E1.
- destruct H23 as (-> & ->). rewrite (cfa_ro_none D o1 st1 E1 H1). reflexivity.
- destruct H23 as (H2 & H3). rewrite (cfa_ev_rd D o1 st1 H1).
  destruct (cn_ro D o2) eqn:E2; cbv iota in H3 |- *.
  + rewrite H3, (cfa_ro_none D o2 st2 E2 H2), !EN, !app_nil_r. reflexivity.
  + rewrite (cfa_ev_rd D o2 st2 H2), (cfa_ev_rd D o0 st3 H3). reflexivity.
Qed.

(* the copies' events when no copy was refused *)
Lemma cfa_cevs3 : forall D r1 r2 r3, r1 <> 0 -> r2 <> 0 -> r3 <> 0 -> cn_cevs D r1 r2 r3 = cn_C3 D.
Proof.
intros D r1 r2 r3 H1 H2 H3. unfold cn_cevs, cn_cblks, cn_cblk, cn_C3.
rewrite (proj2 (Z.eqb_neq r1 0) H1), (proj2 (Z.eqb_neq r2 0) H2), (proj2 (Z.eqb_neq r3 0) H3). reflexivity.
Qed.

(* ---- THE CLASS-24 BOUND at the free cut, position-free: the cut's live set (cn_prog) is a sub-multiset of a
   prefix of the all-granted list, whose peak cn_pre bounds (PresetRun.pkR_prefix's form) ---- *)
Lemma cfa_cnt_pre : forall f s P Q,
  (PresetReqAt.cnt f (PresetReqAt.hlive_from s P) <= PresetRun.pkR f s (P ++ Q))%nat.
Proof. intros f s P Q. rewrite PresetRun.pkR_app. pose proof (PresetRun.cnt_live_pkR f s P). lia. Qed.

Lemma cfa_subm_cons_r : forall z a b, PresetReqAt.subm a b -> PresetReqAt.subm a (z :: b).
Proof.
intros z a b (d & H). exists (z :: d). apply (Permutation_trans (perm_skip z H)). apply Permutation_middle.
Qed.

(* a reading under grant o leaves nothing (it ran out: PresetRun.ranout_pacc) or the all-granted reading's blocks
   (it did not: PjGrammar.G7_1, every allocation it makes is granted) *)
Lemma cfa_pk_sub : forall D o s, PresetReqAt.subm (cfa_pk D o ++ s) (cfa_pk D None ++ s).
Proof.
intros D o s. unfold cfa_pk.
destruct (PresetRun.ranout ReaderRes.jr_strtod (ci_x D) o) eqn:E.
- rewrite (PresetRun.ranout_pacc ReaderRes.jr_strtod (ci_x D) o E). cbn [app]. apply PresetReqAt.subm_app_r.
- destruct o as [j|]; [|apply PresetReqAt.subm_refl].
  assert (Hc : (PjGrammar.ncalls ReaderRes.jr_strtod (ci_x D) <= j)%nat).
  { cbv beta iota delta [PresetRun.ranout] in E. apply Nat.ltb_ge in E. exact E. }
  assert (EJ : PjGrammar.jr_run ReaderRes.jr_strtod (ci_x D) (PresetRun.okof (Some j)) =
               PjGrammar.jr_run ReaderRes.jr_strtod (ci_x D) (PresetRun.okof None)).
  { rewrite (PjGrammar.G7_1 ReaderRes.jr_strtod (ci_x D) (PresetRun.okof (Some j))).
    - symmetry. apply PjGrammar.G7_1. intros [|i] _; reflexivity.
    - intros i Hi. cbn [PresetRun.okof]. apply PresetRun.okk_true. lia. }
  unfold PresetReqAtNoMiss.pacc, PresetReqAt.rtr. rewrite EJ. apply PresetReqAt.subm_refl.
Qed.

Lemma cfa_cnt_revs : forall D o1 o2 o0 f s Q,
  (PresetReqAt.cnt f (PresetReqAt.hlive_from s (cn_revs3 D o1 o2 o0)) <=
   PresetRun.pkR f s (cn_revs3 D None None None ++ Q))%nat.
Proof.
intros D o1 o2 o0 f s Q.
assert (HPE : forall o s0, PresetReqAt.hlive_from s0 (cn_pe D o) = cfa_pk D o ++ s0)
  by (intros o s0; exact (proj2 (PresetReqAtNoMiss.parse_ok ReaderRes.jr_strtod (ci_x D) (PresetRun.okof o) s0))).
assert (ER : cn_revs3 D None None None = cn_pe D None ++ cn_pe D None ++ cn_pe D None) by reflexivity.
rewrite ER. unfold cn_revs3.
destruct (cn_ro D o1) eqn:E1; [|destruct (cn_ro D o2) eqn:E2]; cbv iota.
- (* reading 1 ran out *)
  rewrite app_nil_r, HPE.
  apply (Nat.le_trans _ (PresetReqAt.cnt f (cfa_pk D None ++ s))); [apply PresetReqAt.subm_cnt, cfa_pk_sub|].
  rewrite <- (HPE None s), <- app_assoc. apply cfa_cnt_pre.
- (* reading 2 ran out *)
  rewrite app_nil_r, PresetReqAt.hlive_from_app, !HPE.
  apply (Nat.le_trans _ (PresetReqAt.cnt f (cfa_pk D None ++ cfa_pk D None ++ s))).
  { apply PresetReqAt.subm_cnt. apply (PresetReqAt.subm_trans _ (cfa_pk D None ++ cfa_pk D o1 ++ s));
      [apply cfa_pk_sub | apply PresetReqAt.subm_app_head, cfa_pk_sub]. }
  assert (EQ2 : PresetReqAt.hlive_from s (cn_pe D None ++ cn_pe D None) = cfa_pk D None ++ cfa_pk D None ++ s)
    by (rewrite PresetReqAt.hlive_from_app, !HPE; reflexivity).
  rewrite <- EQ2.
  replace ((cn_pe D None ++ cn_pe D None ++ cn_pe D None) ++ Q) with
    ((cn_pe D None ++ cn_pe D None) ++ (cn_pe D None ++ Q)) by (rewrite <- !app_assoc; reflexivity).
  apply cfa_cnt_pre.
- (* no reading ran out before the third *)
  rewrite !PresetReqAt.hlive_from_app, !HPE.
  apply (Nat.le_trans _ (PresetReqAt.cnt f (cfa_pk D None ++ cfa_pk D None ++ cfa_pk D None ++ s))).
  { apply PresetReqAt.subm_cnt. apply (PresetReqAt.subm_trans _ (cfa_pk D None ++ cfa_pk D o2 ++ cfa_pk D o1 ++ s));
      [apply cfa_pk_sub | apply PresetReqAt.subm_app_head].
    apply (PresetReqAt.subm_trans _ (cfa_pk D None ++ cfa_pk D o1 ++ s));
      [apply cfa_pk_sub | apply PresetReqAt.subm_app_head, cfa_pk_sub]. }
  assert (EQ3 : PresetReqAt.hlive_from s (cn_pe D None ++ cn_pe D None ++ cn_pe D None) =
    cfa_pk D None ++ cfa_pk D None ++ cfa_pk D None ++ s)
    by (rewrite !PresetReqAt.hlive_from_app, !HPE; reflexivity).
  rewrite <- EQ3. apply cfa_cnt_pre.
Qed.

(* no copy refused: the copies, then the readings under their grants *)
Lemma cfa_cnt_free : forall D o1 o2 o0 f s,
  (PresetReqAt.cnt f (PresetReqAt.hlive_from s (cn_C3 D ++ cn_revs3 D o1 o2 o0)) <=
   PresetRun.pkR f s (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None))%nat.
Proof.
intros D o1 o2 o0 f s. rewrite <- (cn_ck_cno_evs D None None None).
rewrite PresetReqAt.hlive_from_app, PresetRun.pkR_app.
pose proof (cfa_cnt_revs D o1 o2 o0 f (PresetReqAt.hlive_from s (cn_C3 D)) (cn_fevs D None None None)). lia.
Qed.

(* a copy refused: the granted copies only, a sub-multiset of the three *)
Lemma cfa_cnt_cevs : forall D r1 r2 r3 f s,
  (PresetReqAt.cnt f (PresetReqAt.hlive_from s (cn_cevs D r1 r2 r3)) <=
   PresetRun.pkR f s (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None))%nat.
Proof.
intros D r1 r2 r3 f s. rewrite <- (cn_ck_cno_evs D None None None).
apply (Nat.le_trans _ (PresetReqAt.cnt f (PresetReqAt.hlive_from s (cn_C3 D)))); [|apply cfa_cnt_pre].
apply PresetReqAt.subm_cnt.
unfold cn_cevs, cn_cblks, cn_cblk, cn_C3, PresetReqAt.hlive_from.
destruct (r1 =? 0), (r2 =? 0), (r3 =? 0); cbn [app map repeat fold_left PresetReqAt.hstep];
  repeat (first [apply PresetReqAt.subm_cons | apply cfa_subm_cons_r]); apply PresetReqAt.subm_refl.
Qed.

(* the bound itself, from the cut's live set E and cn_pre's class-24 peak (CfRoomLivePreset.preset_ccnt24) *)
Lemma cfa_c24 : forall D E S, cn_pre (fx := fx) B ARcfx CTX0 D -> cn_prog D E S ->
  (forall f s, (PresetReqAt.cnt f (PresetReqAt.hlive_from s E) <=
     PresetRun.pkR f s (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None))%nat) ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros D E S HPRE HPG HB. destruct HPG as (HL & _).
pose proof (cn_pre_pk24 (fx := fx) B ARcfx CTX0 D HPRE) as H.
apply CfRoomLivePreset.preset_ccnt24.
rewrite (PresetReqAt.cnt_perm _ _ _ HL).
pose proof (HB (PresetRoom.in_cls 24) (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D)))) as Hb.
change YG00.kBatchClass with 24 in H. clear - Hb H. lia.
Qed.

(* ---- THE LIVE SET across one pj_free: its blocks leave the allocator's live requests (the ablocks permutation
   of the text's post, through rs_live = map snd (blocks S)), which is the model's HBulk of their sizes ---- *)
Lemma cfa_snd_ablocks : forall ly S, map snd (ablocks B ly S) = PresetRoom.rs_live (YGcfRoom.room_of_cf S).
Proof. intros ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.

Lemma cfa_live_bulk : forall (ly ly' : alayout) S S' (Dl F : list (Z * Z)) (X : list Z),
  Permutation (ablocks B ly S) (prhPj_hbl Dl ++ ablocks B ly' S') -> Permutation F Dl ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) X ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.rmall (map (fun b => snd b + cf_head) F) X).
Proof.
intros ly ly' S S' Dl F X HA HF HX.
apply (Permutation_map snd) in HA. rewrite map_app, !cfa_snd_ablocks in HA.
assert (EH : map snd (prhPj_hbl Dl) = map (fun b => snd b + cf_head) Dl)
  by (unfold prhPj_hbl; rewrite map_map; reflexivity).
rewrite EH in HA.
assert (ED : PresetReqAt.rmall (map (fun b => snd b + cf_head) F)
  (map (fun b => snd b + cf_head) Dl ++ PresetRoom.rs_live (YGcfRoom.room_of_cf S')) =
  PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
  by (apply PresetReqAt.rmall_drop; apply Permutation_map; exact (Permutation_sym HF)).
rewrite <- ED at 1.
apply Permutation_sym. apply PresetReqAtNoMiss.rmall_perm. exact (Permutation_trans (Permutation_sym HX) HA).
Qed.

(* THE POSITION across one pj_free: the text's transfer over prhPj_free_evs F is the transfer over the model's
   event cfa_ev (prhPj_free_evs_supply_pjf under the tie; the model's HBulk [] of a filled struct with no blocks
   stepped over by prhPj_bulk_nil_pos; a zero struct has F = [] and no event) *)
Lemma cfa_pos_ev : forall D o st F sm x0 os i H0 hist S0 S1,
  cfa_tie D o st F -> (st = None -> F = []) ->
  prh_run_at sm x0 os i (cfa_ev D o st) ->
  (forall i' H0' h, PresetRoomPos.iface_room_pos sm x0 os i' H0' h S0 ->
     prh_run_at sm x0 os i' (prhPj_free_evs F) ->
     exists h', PresetRoomPos.iface_room_pos sm x0 os (i' + length (prhPj_free_evs F))%nat H0' h' S1) ->
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist S0 ->
  exists h', PresetRoomPos.iface_room_pos sm x0 os (i + length (cfa_ev D o st))%nat H0 h' S1.
Proof.
intros D o st F sm x0 os i H0 hist S0 S1 HT HN HR HTX HP.
destruct st as [[t Dd]|].
- pose proof (HT t Dd eq_refl) as HF. unfold cfa_ev in HR |- *. cbv beta iota in HR |- *.
  rewrite <- HF in HR |- *.
  destruct F as [|b F'].
  + destruct (HTX i H0 hist HP (prhPj_free_evs_nil sm x0 os i)) as (h' & Hh').
    change (length (prhPj_free_evs [])) with 0%nat in Hh'. rewrite Nat.add_0_r in Hh'.
    cbn [map] in HR |- *.
    pose proof (proj1 (prh_run_at_one _ _ _ _ (PresetReqAt.HBulk [])) HR) as Hnth.
    exists h'. change (length [PresetReqAt.HBulk []]) with 1%nat. rewrite Nat.add_1_r.
    exact (proj1 (prhPj_bulk_nil_pos _ _ _ i _ _ _ Hnth) Hh').
  + exact (HTX i H0 hist HP HR).
- assert (EF : F = []) by exact (HN eq_refl). subst F.
  destruct (HTX i H0 hist HP (prhPj_free_evs_nil sm x0 os i)) as (h' & Hh'). exists h'. exact Hh'.
Qed.

(* the order list of a struct still to free at a cn_pjm state (PRH_PjOrder.pj_fdR_foR of its pj_fdR tree: the
   reading's tree by pjf_fd_of_node, the zero struct by pv_fd_zeroR) *)
Lemma cfa_pjm_fo : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest p st0,
  cn_pjm (fx := fx) B D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest -> In (p, st0) rest ->
  exists F, pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D p (cn_Dof st0) F.
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest p st0 HM Hin.
pose proof cfa_laws as LAWS.
destruct HM as (HB & _ & _ & _ & _ & _ & _ & _ & _ & HFA & _).
pose proof (proj1 (Forall_forall _ _) HFA (p, st0) Hin) as (Hpin & _ & Hpdoc). cbn [fst snd] in Hpin, Hpdoc.
pose proof HB as (_ & _ & HJ & HF & _).
destruct HJ as (WS & HJ & _). pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F, frame_addr; rewrite EF; reflexivity).
assert (EFB : fs_frame_bytes CN_CID = 512) by reflexivity.
destruct HF as (Hfrs & _).
assert (Hin3 : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames SEGS B ARcfx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin3) as (HF32 & _ & HFb & _).
rewrite EFa in HF32, HFb. rewrite EFB in HFb.
assert (Hpset : p = cn_F D + 32 \/ p = cn_F D + 128 \/ p = cn_F D + 224)
  by (unfold cn_d1, cn_d2, cn_d3 in Hpin; cbn [In] in Hpin; lia).
assert (Hrw : pj_rwR SEGS (rdW W mem) p).
{ split; [clear - HF32 Hpset; lia|]. intros x Hx. apply (apresent_writable SEGS).
  exact (proj1 (HFb x ltac:(clear - Hpset Hx; lia))). }
apply pj_fdR_foR.
destruct st0 as [[t Dd]|]; cbn [cn_doc cn_Dof] in Hpdoc |- *.
- destruct Hpdoc as (Hn & Hdep).
  apply (pjf_fd_of_node SEGS (rdW W mem) (prh_lin Lam) t DOC_D p Dd); [unfold DOC_D; lia | exact Hn].
- exact (PvFdZeroR.pv_fd_zeroR SEGS (rdW W mem) (prh_lin Lam) DOC_D p Hrw Hpdoc).
Qed.

(* the same, tied to the model's pj_frees when no copy was refused: the free cut's cn_fo at cf_head = HEAD (HH) and
   n := DOC_D (the tree's depth is at most MAXD, cn_doc) *)
Lemma cfa_fo_tie : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest p st o,
  cn_pjm (fx := fx) B D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest -> In (p, st) rest ->
  (ownl = 0 -> cn_fo D W mem Lam o p st) ->
  exists F, pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D p (cn_Dof st) F /\ (ownl = 0 -> cfa_tie D o st F).
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest p st o HM Hin HT.
destruct (cfa_pjm_fo D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 rest p st HM Hin) as (F0 & HF0).
destruct st as [[t Dd]|].
- destruct (Z.eq_dec ownl 0) as [E0|En].
  + pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HFA & _).
    pose proof (proj1 (Forall_forall _ _) HFA (p, Some (t, Dd)) Hin) as (_ & _ & Hpdoc).
    cbn [fst snd cn_doc] in Hpdoc. destruct Hpdoc as (_ & Hdep).
    pose proof (HT E0) as HT0. unfold cn_fo in HT0.
    destruct (HT0 HH DOC_D ltac:(unfold DOC_D; lia)) as (F & HF & HFe).
    exists F. split; [exact HF|]. intros _ t' Dd' _. exact HFe.
  + exists F0. split; [exact HF0|]. intros E0. contradiction.
- exists F0. split; [exact HF0|]. intros _. apply cfa_tie_none. reflexivity.
Qed.

(* ==== THE STEP LEMMA: one pj_free call, at the callee's entry (ra = ret), of the first struct still to free; its
   run frees, so it is at SRr' SEGS RZ_cf ==== *)
Lemma cfa_pjf_call : forall P, srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 d st rest ret F,
  cn_pre (fx := fx) B ARcfx CTX0 D -> In ret cfa_rets ->
  cn_pjm (fx := fx) B D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 ((d, st) :: rest) ->
  cn_regsat regs (cn_core D) -> getr regs 1%bv = w64 (cn_pc ret) -> getr regs 10%bv = w64 d -> P mem ->
  (* the struct's order list F at this memory, and the text's class-24 bound at this state *)
  pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D d (cn_Dof st) F ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  SRr' SEGS RZ_cf W (@cn_cfg SEGS fxk (SIGMA AS_pj_free) regs mem md) (fun W' c' =>
    exists ly' S' Hp' regs' mem' md' k' Lam',
      c' = @cn_cfg SEGS fxk (cn_pc ret) regs' mem' md' /\ aregs_preserved regs regs' /\
      cn_pjm (fx := fx) B D fxk ly' S' Hp' W' regs' mem' md' k' Lam' peak cnt ran ownl r1 r2 r3 rest /\
      (* the class-24 count does not rise (the text's last conjunct) *)
      YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S /\
      (* the events made: for any events E since entry and any grant o F is tied to, past the struct's model event *)
      (forall E o, cfa_tie D o st F -> cn_prog D E S -> cn_prog D (E ++ cfa_ev D o st) S') /\
      (* the order lists of the structs still to free, kept (PRH_PjOrder.pj_foR_frame) *)
      (forall p0 st0 F0, In (p0, st0) rest ->
         pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D p0 (cn_Dof st0) F0 ->
         pj_foR SEGS (rdW W' mem') (prh_lin Lam') DOC_D p0 (cn_Dof st0) F0) /\
      P mem').
Proof.
intros P PC D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 d st rest ret F
  HPRE Hret HM HC R1 R10 HPM Hfo HC24.
pose proof cfa_laws as LAWS.
destruct (cfa_entry_facts D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & Hgp0 & Htp0 & _ & _ & _).
pose proof cfa_stk_val as HSTKv. destruct cfa_stkf_bnd as (HSTKf0 & HSTKf1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (cfa_S1_facts D Hal16) as (HS1a & HS1b).
destruct (cfa_ret_ok ret Hret) as ((Hr0 & Hrc) & Hrok & Hr28).
pose proof (cn_pre_univ (fx := fx) B ARcfx CTX0 D HPRE) as HCL.
destruct HM as (HB & HSL & HC1 & HC2 & HC3 & HLED & Hpk & Hcnt & HRL & HFA & HND & HLam & HAB & HNEW & HHB).
destruct (cfa_chain D fxk ly S Hp W regs mem md k 6 HPRE HB) as (ch1 & Hch1).
pose proof HB as (Hz & Hk & HJ0 & HF & HSV & R3 & R4 & HROD).
(* the journal at the cut's wild budget WS (cn_JR at wk = 6, at wle' SEGS RZ_cf), read by its projections *)
destruct HJ0 as (WS & HJ & HBUD).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
assert (EFa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F, frame_addr; rewrite EF; reflexivity).
assert (EFB : fs_frame_bytes CN_CID = 512) by reflexivity.
destruct HF as (Hfrs & Hnin & Hflag & Hfpres & Hspres).
assert (Hin3 : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames SEGS B ARcfx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin3) as (HF32 & HFapp & HFb & HFs).
destruct (frames_bounds_x SEGS B ARcfx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin3) as (HF4096 & HFceil & _).
rewrite EFa in HF32, HFapp, HFb, HFs, HF4096, HFceil. rewrite EFB in HFapp, HFb, HFs, HFceil.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
(* ---- the struct d ---- *)
pose proof (Forall_inv HFA) as (Hdin & Hdop & Hddoc). pose proof (Forall_inv_tail HFA) as HFA'.
cbn [fst snd] in Hdin, Hdop, Hddoc.
assert (Hdset : d = cn_F D + 32 \/ d = cn_F D + 128 \/ d = cn_F D + 224)
  by (unfold cn_d1, cn_d2, cn_d3 in Hdin; cbn [In] in Hdin; lia).
assert (Hdd : cn_F D + 32 <= d /\ d + 56 <= cn_F D + 280 /\ d mod 32 = 0) by lia.
assert (Hd0 : 4096 <= d) by lia.
assert (Hdc : d < YM05.alloc_ceiling) by lia.
assert (Hne0 : (d =? 0) = false) by (apply Z.eqb_neq; lia).
assert (Hrw : pj_rwR SEGS (rdW W mem) d).
{ split; [lia|]. intros x Hx. apply (apresent_writable SEGS). exact (proj1 (HFb x ltac:(lia))). }
(* ---- the registers ---- *)
assert (Gsp : getr regs 2%bv = w64 (cn_S1 D)) by (apply (cfa_regsat_get regs (cn_core D)); [exact HC | unfold cn_core; cfa_in]).
assert (Gs0 : getr regs 8%bv = w64 (cn_sp0 D)) by (apply (cfa_regsat_get regs (cn_core D)); [exact HC | unfold cn_core; cfa_in]).
assert (Hsp : spZ regs = cn_S1 D) by (unfold spZ; rewrite Gsp; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = cn_sp0 D) by (unfold s0Z; rewrite Gs0; unfold w64; apply unsigned_lit_small; lia).
assert (Hraz : raZ regs = cn_pc ret) by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; lia).
(* ---- the trees: the one freed (cn_Dof st) and the rest ---- *)
assert (Hcons : cn_Dofs ((d, st) :: rest) = cn_Dof st ++ cn_Dofs rest) by reflexivity.
rewrite Hcons in HLam, HAB, HNEW.
assert (HinL : forall x, In x (cn_Dof st) -> In x Lam)
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym HLam)); apply in_or_app; left; apply in_or_app; left; exact Hx).
assert (HinR : forall x, In x (cn_Dofs rest) -> In x Lam)
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym HLam)); apply in_or_app; left; apply in_or_app; right; exact Hx).
assert (HDb : forall a0 k0, In (a0, k0) (cn_Dof st) ->
  0 <= k0 /\ In (a0 - cf_head, k0 + cf_head) (ablocks B ly S) /\
  ~ In (a0 - cf_head, k0 + cf_head) (ablocks B (ci_ly D) (ci_S D))).
{ intros a0 k0 Hak.
  pose proof (proj1 (Forall_forall _ _)
    (prh_ledger_blocks B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED) (a0, k0)
    (HinL _ Hak)) as (Hk0 & Hab & _).
  cbn [fst snd] in Hk0, Hab.
  split; [exact Hk0|]. split; [exact Hab|]. apply HNEW. apply in_or_app. left. exact Hak. }
(* prh_ledger's NoDup is stdpp's (S1Ledger.v :124-125); Stdlib's List.NoDup by NoDup_ListNoDup *)
pose proof (Permutation_NoDup (Permutation_map fst HLam)
  (proj1 (NoDup_ListNoDup _) (prh_ledger_nodup B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED)))
  as HNDP.
(* ---- the callee's footprint ---- *)
set (FPc := if d =? 0 then [] else (d, d + 56) :: ablocks_fp (prhPj_hbl (cn_Dof st))).
assert (HFPc : forall a, inFP FPc a -> (d <= a < d + 56) \/
  exists a0 k0, In (a0, k0) (cn_Dof st) /\ a0 - cf_head <= a < a0 - cf_head + req_size (k0 + cf_head)).
{ intros a Ha. unfold FPc in Ha. rewrite Hne0 in Ha. apply inFP_cons in Ha.
  destruct Ha as [Ha | (rr & Hr & Hra)]; [left; exact Ha|]. right.
  unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr. apply in_map_iff in Hr as ((a0 & k0) & <- & Hak).
  cbn [fst snd] in Hra. exists a0, k0. split; [exact Hak | lia]. }
assert (HSINK : ~ YI16.sink_open_fp FPc).
{ unfold FPc. rewrite Hne0. apply sink_closed_cons; [cbn [fst]; lia|]. apply sink_closed_ablocks_fp.
  apply Forall_forall. intros [b m] Hb. unfold prhPj_hbl in Hb. apply in_map_iff in Hb as ((a0 & k0) & E & Hak).
  cbn [fst snd] in E. injection E as <- <-.
  destruct (HDb a0 k0 Hak) as (_ & Hab & _).
  destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & _). cbn [fst]. lia. }
(* ---- THE CALL: pj_free is a plain callee (fpostWmR at wle' SEGS RZ_cf), run on the journal rebased to the empty
   budget, through the caller-window rule at R := wle' SEGS RZ_cf ---- *)
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJr.
unfold cn_cfg, w64.
eapply SRr'_bind.
{ unfold SRr'.
  eapply (@YCbqGcallW.aj_call_xWR fxk rc SK SEGS B prh_pst ARcfx cf_head LAWS pa_segs_low
    (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W regs mem (SIGMA AS_pj_free)
    STK (cn_sp0 D) [] (ci_ly D) (set_depot (st_depot S) (ci_S D)) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly S Hp md k (STK_pj_free DOC_D) 0 FPc (cn_S1 D - cn_sp0 D) (w64 (cn_pc ret)) ch1).
  - exact HJr.
  - rewrite Hsp. lia.
  - lia.
  - lia.
  - exact HSTKf0.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - exact R1.
  - exact Hrok.
  - unfold w64. rewrite unsigned_lit_small by lia. exact Hr0.
  - replace (cn_sp0 D + (cn_S1 D - cn_sp0 D)) with (cn_S1 D) by lia. rewrite Hs0. exact Hch1.
  - (* the callee: the kit's tpj_free_specX at v = d, D = the struct's blocks, window e = 0; its hull premise from the
       cut's hull conjunct (a budget for any list is one for []) *)
    intros HAFN HWIN.
    assert (HFP : fpre (fx := fxk) B ARcfx (STK_pj_free DOC_D) ly S Hp W regs mem md ch1).
    { split; [exact HAFN|]. split; [exact HROD|]. split; [rewrite Hsp, Eshi; lia|].
      split; [rewrite Hraz; exact Hrc | exact Hz]. }
    pose proof (HPJFREE fxk (ci_most D) ownl ly S Hp W regs mem md ch1 0 d (cn_Dof st) F Lam peak cnt SIZE_MAXZ ran
      HFP HCL HRL (fun _ => HC24) (fun _ => PresetHullBudget.hull_budget_nil S _ HHB) R10 HWIN) as HT.
    lazymatch type of HT with ?A -> _ -> _ => assert (HARM : A) end.
    { right. split; [lia|]. split; [exact Hdc|]. split; [exact Hfo|].
      split; [lia|].
      split; [right; right; left; exists CN_CID, (ci_fpos D); split; [exact Hin3|]; rewrite EFa, EFB; lia|].
      split; [exact Hrw|].
      split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
      split; [intros a Ha; split; [exact (proj2 (HFb a ltac:(lia))) | rewrite Hsp; lia]|].
      exact Hdop. }
    specialize (HT HARM cfa_hw HLED).
    unfold fpostWmR, fpostWR, SRr' in HT. unfold YCbqGcallW.fpostW_xR. exact HT.
  - (* the footprint: the struct in the own frame, the blocks new since entry *)
    intros a Ha. destruct (HFPc a Ha) as [Hw | (a0 & k0 & Hak & Hra)].
    + right; right; left. exists (CN_CID, ci_fpos D). split; [left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, EFB. lia.
    + right; left. destruct (HDb a0 k0 Hak) as (_ & Hab & Hnab).
      exists (a0 - cf_head), (k0 + cf_head). split; [exact Hab|]. split; [exact Hnab | lia]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & _ & HP2 & HK).
cbv beta delta [fQmn] in HK.
(* the text's inner Q, read through its named projections (PRH_FnPj.v tpfP_R_of: room, the hull use, the position
   transfer, the lists, the ledger, the class-24 count) *)
destruct HK as (HQ & HMN).
apply tpfP_R_of with (regs' := regs2) (md' := md2) in HQ. destruct HQ as (Lam' & HQR).
pose proof (tpfP_room HQR) as HRL2. pose proof (tpfP_hull HQR) as HHU2. pose proof (tpfP_pos HQR) as HPOS2.
pose proof (tpfP_lam HQR) as HpL. pose proof (tpfP_ablocks HQR) as HpA. pose proof (tpfP_ledger HQR) as HLED2.
pose proof (tpfP_ccnt24 HQR) as HC24'.
rewrite !Z.add_0_r in HJ1. replace (cn_sp0 D + (cn_S1 D - cn_sp0 D)) with (cn_S1 D) in HJ1 by lia.
pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_ly HJ1) as Hly1. pose proof (ajxR_frs HJ1) as Hfrs1.
pose proof (ajxR_hi HJ1) as G1. pose proof (ajxR_blk HJ1) as G2. pose proof (ajxR_img HJ1) as G3.
pose proof (ajxR_frm HJ1) as G4.
pose proof Hly1 as (_ & _ & _ & _ & _ & EF1 & _).
assert (Hin3' : In (CN_CID, ci_fpos D) (frames S2)) by (rewrite Hfrs1; exact Hin3).
assert (EFa2 : frame_addr ly2 CN_CID (ci_fpos D) = cn_F D) by (rewrite <- EFa; unfold frame_addr; rewrite EF1; reflexivity).
destruct (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp2 W2 mem2 md2 CN_CID (ci_fpos D) HAR2 Hin3') as (_ & _ & HFb2 & HFs2).
rewrite EFa2, EFB in HFb2, HFs2.
(* ---- what the callee's journal keeps ---- *)
assert (KFR : forall a, cn_F D <= a < cn_F D + 512 -> ~ (d <= a < d + 56) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hna. apply (G4 CN_CID (ci_fpos D) a Hin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, EFB. lia.
  - intros Hf. destruct (HFPc a Hf) as [Hw | (a0 & k0 & Hak & Hra)]; [exact (Hna Hw)|].
    destruct (HDb a0 k0 Hak) as (_ & Hab & _).
    apply (frame_not_block_x SEGS B ARcfx LAWS ly S Hp W mem md (CN_CID, ci_fpos D) (a0 - cf_head) (k0 + cf_head) a
      HAR Hin3 Hab); [|lia].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, EFB. lia. }
assert (KSH : forall a, shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (G4 CN_CID (ci_fpos D) a Hin3).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFa, EFB. change (512 / 8) with 64. lia.
  - intros Hf. unfold shadow_addr, SHADOW_OFF in Ha.
    destruct (HFPc a Hf) as [Hw | (a0 & k0 & Hak & Hra)]; [lia|].
    destruct (HDb a0 k0 Hak) as (_ & Hab & _).
    destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & Happ & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
assert (KST : forall a, cn_S1 D <= a < cn_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply G1; lia).
(* ---- the lists after the call ---- *)
assert (HLam' : Permutation Lam' (cn_Dofs rest ++ ci_Lam D)).
{ apply (Permutation_app_inv_l (cn_Dof st)). apply (Permutation_trans (Permutation_sym HpL)).
  pose proof HLam as HLam0. rewrite <- app_assoc in HLam0. exact HLam0. }
assert (HAB' : Permutation (ablocks B ly2 S2) (cn_cblks D r1 r2 r3 ++ ck_hblks (cn_Dofs rest) ++ ablocks B (ci_ly D) (ci_S D))).
{ apply (Permutation_app_inv_l (prhPj_hbl (cn_Dof st))). apply (Permutation_trans (Permutation_sym HpA)).
  apply (Permutation_trans HAB). unfold ck_hblks, prhPj_hbl. rewrite map_app. rewrite !app_assoc.
  apply Permutation_app_tail. apply Permutation_app_tail. apply Permutation_app_comm. }
(* ---- the copies: no copy is a block of the freed tree (its base is no harness head) ---- *)
assert (KC : forall r0, cn_cpy B D ly S Hp r0 -> cn_cpy B D ly2 S2 Hp2 r0).
{ intros r0 [H0 | (Hin & Hnh)]; [left; exact H0|]. right.
  pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED) as Hh1.
  split.
  - apply (Permutation_in _ HpA) in Hin. apply in_app_or in Hin as [Hin | Hin]; [|exact Hin].
    exfalso. unfold prhPj_hbl in Hin. apply in_map_iff in Hin as ((a0 & k0) & E & Hak). cbn [fst snd] in E.
    injection E as E1 _. apply Hnh. apply (Permutation_in _ (Permutation_sym Hh1)). apply in_map_iff.
    exists (a0, k0). split; [cbn [fst]; exact E1 | exact (HinL _ Hak)].
  - intros Hh2. apply Hnh.
    pose proof (prh_ledger_heads B ly2 S2 Hp2 W2 mem2 Lam' peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED2) as Hh2'.
    apply (Permutation_in _ Hh2') in Hh2. apply in_map_iff in Hh2 as ((a & kk) & Ea & Hak).
    apply (Permutation_in _ (Permutation_sym Hh1)). apply in_map_iff. exists (a, kk). split; [exact Ea|].
    apply (Permutation_in _ (Permutation_sym HpL)). apply in_or_app. right. exact Hak. }
(* ---- the other trees: their footprints kept, so their trees and their order lists are, over Lam' ---- *)
assert (KAG : forall p0 D1, cn_F D + 32 <= p0 -> p0 + 56 <= cn_F D + 280 -> (p0 + 56 <= d \/ d + 56 <= p0) ->
  (forall x, In x D1 -> In x (cn_Dofs rest)) -> pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (pj_footR p0 D1)).
{ intros p0 D1 Hq1 Hq2 Hdis Hinc x Hx. destruct Hx as [Hx | ((a & kk) & Hbk & Hx)].
  + split; [apply (mbyte_of_aview SEGS); apply KFR; lia|].
    intros _. apply (apresent_writable SEGS). exact (proj1 (HFb2 x ltac:(lia))).
  + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (Hinc _ Hbk) as HbR.
    pose proof (proj1 (Forall_forall _ _)
      (prh_ledger_blocks B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED) (a, kk)
      (HinR _ HbR)) as (Hk0 & Hab1 & _).
    cbn [fst snd] in Hk0, Hab1.
    assert (HbL2 : In (a, kk) Lam')
      by (apply (Permutation_in _ (Permutation_sym HLam')); apply in_or_app; left; exact HbR).
    pose proof (proj1 (Forall_forall _ _)
      (prh_ledger_blocks B ly2 S2 Hp2 W2 mem2 Lam' peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED2)
      (a, kk) HbL2) as (_ & Hab2 & _).
    cbn [fst snd] in Hab2.
    destruct (req_size_pos (kk + cf_head) (Z.add_nonneg_nonneg _ _ Hk0 Hh0)) as (_ & Hrq).
    split.
    * apply (mbyte_of_aview SEGS). replace x with ((a - cf_head) + (x - (a - cf_head))) by lia.
      apply (G2 _ _ _ Hab1 Hab2); [lia|].
      intros Hf. destruct (HFPc _ Hf) as [Hw | (a0 & k0 & Hak0 & Hra0)].
      -- apply (frame_not_block_x SEGS B ARcfx LAWS ly S Hp W mem md (CN_CID, ci_fpos D) (a - cf_head) (kk + cf_head)
           ((a - cf_head) + (x - (a - cf_head))) HAR Hin3 Hab1); [|lia].
         unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, EFB. lia.
      -- destruct (HDb a0 k0 Hak0) as (Hk00 & Hab0 & _).
         assert (Hne : a0 <> a) by exact (cfa_nodup_fst _ _ _ (a0, k0) (a, kk) HNDP Hak0 HbR).
         pose proof (sep_blocks_x SEGS B ARcfx LAWS ly S Hp W mem md (a0 - cf_head) (k0 + cf_head) (a - cf_head)
           (kk + cf_head) HAR Hab0 Hab1 ltac:(intros E; injection E as E1 _; lia)) as Hdj.
         unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. lia.
    * intros _. apply (apresent_writable SEGS).
      destruct (alx_blocks SEGS B ARcfx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (kk + cf_head) HAR2 Hab2)
        as (_ & _ & _ & _ & Hpr2 & _).
      exact (proj1 (Hpr2 x ltac:(lia))). }
assert (HDOC : forall p0 st0, cn_F D + 32 <= p0 -> p0 + 56 <= cn_F D + 280 -> (p0 + 56 <= d \/ d + 56 <= p0) ->
  (forall x, In x (cn_Dof st0) -> In x (cn_Dofs rest)) -> cn_doc W mem Lam p0 st0 -> cn_doc W2 mem2 Lam' p0 st0).
{ intros p0 st0 Hq1 Hq2 Hdis Hinc Hdoc. destruct st0 as [[t0 D1]|]; cbn [cn_doc cn_Dof] in Hdoc, Hinc |- *.
  - destruct Hdoc as (Hn & Hdep). split; [|exact Hdep].
    apply (pjf_nodeR_lblk SEGS t0 (rdW W2 mem2) (prh_lin Lam) (prh_lin Lam') p0 D1).
    { intros b kk Hb _. unfold prh_lin. apply (Permutation_in _ (Permutation_sym HLam')). apply in_or_app. left.
      exact (Hinc _ Hb). }
    exact (pj_nodeR_frame SEGS t0 (rdW W mem) (rdW W2 mem2) (prh_lin Lam) p0 D1 Hn (KAG p0 D1 Hq1 Hq2 Hdis Hinc)).
  - apply (pj_zeroR_frame SEGS (rdW W mem) (rdW W2 mem2) p0 Hdoc). intros x Hx. apply (mbyte_of_aview SEGS).
    apply KFR; lia. }
(* the structs still to free: in the frame, apart from d, their blocks rest's *)
assert (HRST : forall p0 st0, In (p0, st0) rest ->
  (p0 = cn_F D + 32 \/ p0 = cn_F D + 128 \/ p0 = cn_F D + 224) /\ p0 <> d /\
  (forall x, In x (cn_Dof st0) -> In x (cn_Dofs rest))).
{ intros p0 st0 Hin. pose proof (proj1 (Forall_forall _ _) HFA' (p0, st0) Hin) as (Hp0in & _ & _).
  cbn [fst] in Hp0in. split; [|split].
  - unfold cn_d1, cn_d2, cn_d3 in Hp0in. cbn [In] in Hp0in. clear - Hp0in. lia.
  - intros E. rewrite E in Hin. pose proof HND as HND0. cbn [map fst] in HND0. apply NoDup_cons_iff in HND0.
    destruct HND0 as (Hn & _). apply Hn. apply in_map_iff. exists (d, st0). split; [reflexivity | exact Hin].
  - intros x Hx. unfold cn_Dofs. apply in_concat. exists (cn_Dof st0). split; [|exact Hx].
    apply in_map_iff. exists (p0, st0). split; [reflexivity | exact Hin]. }
(* their order lists kept (PRH_PjOrder.pj_foR_frame), for the next calls' run premises *)
assert (KFO : forall p0 st0 F0, In (p0, st0) rest ->
  pj_foR SEGS (rdW W mem) (prh_lin Lam) DOC_D p0 (cn_Dof st0) F0 ->
  pj_foR SEGS (rdW W2 mem2) (prh_lin Lam') DOC_D p0 (cn_Dof st0) F0).
{ intros p0 st0 F0 Hin Hf0. destruct (HRST p0 st0 Hin) as (Hp0set & Hne & Hinc).
  apply (pj_foR_frame SEGS DOC_D (rdW W mem) (rdW W2 mem2) (prh_lin Lam) (prh_lin Lam') p0 (cn_Dof st0) F0 Hf0).
  - intros b kk Hb. unfold prh_lin. apply (Permutation_in _ (Permutation_sym HLam')). apply in_or_app. left.
    exact (Hinc _ Hb).
  - apply KAG; [clear - Hp0set Hdset; lia | clear - Hp0set Hdset; lia | clear - Hp0set Hne Hdset; lia | exact Hinc]. }
(* ---- THE EXIT ---- *)
apply SRr'_ret. exists ly2, S2, Hp2, regs2, mem2, md2, (k + k1), Lam'.
split; [reflexivity|].
split; [exact HP2|].
split; [|split; [exact HC24' | split; [| split; [exact KFO | exact (PC mem mem2 HMN HPM)]]]].
2: { (* the events made, past this struct's model event: the live set by its blocks leaving (cfa_live_bulk), the
       position by the text's transfer (cfa_pos_ev) *)
  intros E o HTIE HPG. destruct HPG as (HLE & HPE).
  assert (HFD : Permutation F (cn_Dof st)) by exact (proj2 (pj_foR_fdR _ _ _ _ _ _ _ Hfo)).
  assert (EF0 : st = None -> F = []).
  { intros ->. apply Permutation_nil. apply Permutation_sym. exact HFD. }
  unfold cn_prog. split.
  - rewrite PresetReqAt.hlive_from_app.
    destruct st as [[t Dd]|].
    + unfold cfa_ev. cbv beta iota. rewrite <- (HTIE t Dd eq_refl).
      exact (cfa_live_bulk ly ly2 S S2 _ F _ HpA HFD HLE).
    + pose proof (EF0 eq_refl) as ->. unfold cfa_ev. cbv beta iota.
      exact (cfa_live_bulk ly ly2 S S2 _ [] _ HpA HFD HLE).
  - intros sm x0 os i H0 hist HP0 HR.
    apply prh_run_at_app_iff in HR as (HR1 & HR2).
    destruct (HPE sm x0 os i H0 hist HP0 HR1) as (h1 & HP1).
    rewrite length_app, Nat.add_assoc.
    exact (cfa_pos_ev D o st F sm x0 os (i + length E) H0 h1 S S2 HTIE EF0 HR2 (HPOS2 sm x0 os) HP1). }
split.
{ (* cn_baseR at wle' SEGS RZ_cf *)
  split; [exact Hz|]. split; [exact Hk|].
  (* the caller's journal back at its own budget WS (YCbqGwild.ajournal_xw_unbase0R, by the journal's ajxR_wild) *)
  split.
  { exists WS. split; [|exact HBUD].
    exact (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 (ajxR_wild HJ)). }
  split.
  { split; [rewrite Hfrs1; exact Hfrs|]. split; [exact Hnin|].
    split; [|split].
    - assert (Efl : flag_addr ly2 CN_CID (ci_fpos D) = flag_addr ly CN_CID (ci_fpos D))
        by (unfold flag_addr; rewrite EF1; reflexivity).
      rewrite Efl, <- Hflag.
      apply (cfa_rdword_kept _ _ (cn_F D + 280) (cn_F D + 512)); [intros a Ha; apply KFR; lia | rewrite EFB; lia | rewrite EFB; lia].
    - intros a Ha. rewrite EFB in Ha. exact (proj1 (HFb2 a Ha)).
    - intros a Ha. rewrite EFB in Ha. change (512 / 8) with 64 in Ha.
      replace a with (shadow_addr (cn_F D) + (a - shadow_addr (cn_F D))) by lia.
      apply (proj1 (HFs2 (a - shadow_addr (cn_F D)) ltac:(change (512 / 8) with 64; lia))). }
  split.
  { unfold cn_saved in *. apply Forall_forall. intros [o rr] Hin.
    pose proof (proj1 (Forall_forall _ _) HSV (o, rr) Hin) as Hv. cbn [fst snd] in Hv |- *.
    assert (Ho : 88 <= o <= 184) by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
    rewrite <- Hv. apply (cfa_rdword_kept _ _ (cn_S1 D) (cn_sp0 D)); [exact KST | lia | lia]. }
  split; [exact (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) R3)|].
  split; [exact (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) R4)|].
  (* the read-only view, by the callee's journal: no read-only byte is a program static (cni_pst_rw) *)
  intros a Hro Hown Herr. rewrite <- (HROD a Hro Hown Herr). apply G3.
  + destruct Hro as [(sg & Hsg & _ & Hb) | Hrel]; [exists sg; split; [exact Hsg | exact Hb] | exact (pa_relro_img a Hrel)].
  + exact Hown.
  + exact Herr.
  + intros Hpst. exact (cni_pst_rw B IMG a Hpst Hro).
  + apply fp_spares_closed. exact HSINK. }
split.
{ (* cn_slots *)
  unfold cn_slots in *. apply Forall_forall. intros [o v] Hin.
  pose proof (proj1 (Forall_forall _ _) HSL (o, v) Hin) as Hv. cbn [fst snd] in Hv |- *.
  assert (Ho : 24 <= o <= 80) by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
  rewrite <- Hv. apply (cfa_rdword_kept _ _ (cn_S1 D) (cn_sp0 D)); [exact KST | lia | lia]. }
split; [exact (KC r1 HC1)|]. split; [exact (KC r2 HC2)|]. split; [exact (KC r3 HC3)|].
split; [exact HLED2|]. split; [exact Hpk|]. split; [exact Hcnt|]. split; [exact HRL2|].
split.
{ (* the structs still to free: open, their trees over Lam' *)
  apply Forall_forall. intros [p0 st0] Hin.
  pose proof (proj1 (Forall_forall _ _) HFA' (p0, st0) Hin) as (Hp0in & Hp0op & Hp0doc).
  cbn [fst snd] in Hp0in, Hp0op, Hp0doc |- *.
  destruct (HRST p0 st0 Hin) as (Hp0set & Hne & Hinc).
  split; [exact Hp0in|].
  split.
  - apply (cfa_open_keep _ _ (cn_F D) p0 HF32 ltac:(lia) ltac:(lia) ltac:(lia) KSH Hp0op).
  - apply HDOC; [lia | lia | lia | exact Hinc | exact Hp0doc]. }
split; [cbn [map fst] in HND; apply NoDup_cons_iff in HND; exact (proj2 HND)|].
split; [exact HLam'|]. split; [exact HAB'|].
split; [intros a kk Hak; apply HNEW; apply in_or_app; right; exact Hak|].
(* the hull budget at the next cut: pj_free used [] (the text's `hull_used S S2 []`), so the next cut's list is
   F.v's step from this one *)
eapply cn_hrest_pjm_step; [exact HHB | exact HHU2].
Qed.

(* ==== CA10a ==== *)
(* THE EVENTS (f97c's progress form): under ownl = 0 the free cut's live set and position are those after
   cn_cevs ++ cn_revs3 (= cn_C3 ++ cn_revs3, the copies non-NULL), each pj_free moves them past its struct's model
   event cfa_ev (the order list tied to pj_frees by the free cut's cn_fo, cfa_fo_tie), and the three events are cn_fpj
   (cfa_fpj under cn_rds3). Under ownl <> 0 the structs are zero (the cut's refused arm): no event, the live set
   cn_cevs's, and the cut's cn_cdead D goes on to CN_FRCUT. The class-24 bound the text asks at every call comes from
   the cut's live set in either arm (cfa_c24) and is kept by each call (its post's ccnt24 S' <= ccnt24 S); the hull
   budget rides in cn_pjm (cn_pjm_of_free reads the free cut's, cfa_pjf_call pays and steps it, cn_fr_of_pjm hands it
   to CN_FRCUT). The run crosses pj_free, so every bind is SRr'_bind at RZ_cf. *)
Theorem cn_seg_pjf : cn_seg_pjfP (fx := fx) B CTX0.
Proof.
intros P PL PC D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HPRE HAT HPM.
(* cn_at_freeR by position: its hull conjunct (last) is read by cn_pjm_of_free, not here *)
pose proof HAT as (_ & _ & _ & _ & _ & _ & HEV0 & HEVN & _).
destruct (cn_pjm_of_free (fx := fx) B D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3
  o1 o2 o0 HAT) as (HM & HR & Ho & Hr).
(* the free cut's three free-order ties (ownl = 0 arm, the base's cn_fo) *)
assert (HFO : ownl = 0 -> cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\
  cn_fo D W mem Lam o0 (cn_d3 D) st3).
{ intros E0. destruct (HEV0 E0) as (_ & _ & _ & _ & _ & _ & HFO1 & HFO2 & HFO3). exact (conj HFO1 (conj HFO2 HFO3)). }
(* the three order lists at CN_FREE, tied to the model's pj_frees when no copy was refused *)
destruct (cfa_fo_tie D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 _ (cn_d1 D) st1 o1 HM
  ltac:(cfa_in) (fun E => proj1 (HFO E))) as (F1 & HF1 & HT1).
destruct (cfa_fo_tie D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 _ (cn_d2 D) st2 o2 HM
  ltac:(cfa_in) (fun E => proj1 (proj2 (HFO E)))) as (F2 & HF2 & HT2).
destruct (cfa_fo_tie D fxk ly S Hp W regs mem md k Lam peak cnt ran ownl r1 r2 r3 _ (cn_d3 D) st3 o0 HM
  ltac:(cfa_in) (fun E => proj2 (proj2 (HFO E)))) as (F3 & HF3 & HT3).
(* the class-24 bound at CN_FREE, from the cut's live set in either arm *)
assert (HC24 : YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ destruct (Z.eq_dec ownl 0) as [E0|En].
  - destruct (HEV0 E0) as (Hr1 & Hr2 & Hr3 & HPG & _).
    rewrite (cfa_cevs3 D r1 r2 r3 Hr1 Hr2 Hr3) in HPG.
    exact (cfa_c24 D _ S HPRE HPG (cfa_cnt_free D o1 o2 o0)).
  - exact (cfa_c24 D _ S HPRE (proj1 (HEVN En)) (cfa_cnt_cevs D r1 r2 r3)). }
destruct (cfa_entry_facts D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _).
destruct (cfa_S1_facts D Hal16) as (HS1a & HS1b).
set (L0 := cn_core D ++ [(19%bv, cn_d3 D); (21%bv, r); (22%bv, r3); (25%bv, cn_d1 D); (26%bv, r1)]) in HR.
assert (HL0cs : Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p))) L0)
  by (unfold L0, cn_core; cbn [app]; repeat (apply Forall_cons; [cbn [fst]; cfa_cs|]); apply Forall_nil).
assert (HL0a : Forall (fun p : bv 5 * Z => bv_eqb (fst p) 10%bv = false) L0)
  by (unfold L0, cn_core; cbn [app]; repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil).
assert (HL0r : Forall (fun p : bv 5 * Z => bv_eqb (fst p) 1%bv = false) L0)
  by (unfold L0, cn_core; cbn [app]; repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil).
assert (HcoreL0 : incl (cn_core D) L0) by (unfold L0; intros x Hx; apply in_or_app; left; exact Hx).
pose proof asan_consts as (C1 & _). pose proof cfa_stk_val as HSTKv.
assert (HS1 : 0 <= cn_S1 D /\ cn_S1 D + 56 <= 2 ^ 64) by lia.
(* ---- 1060 mv a0, s9 ; 1064 jal pj_free ---- *)
change (cn_pc CN_FREE) with (cn_pc 1060).
apply cfa_mv_1060. intros X1.
rewrite (cfa_regsat_get regs L0 25%bv (cn_d1 D) HR ltac:(unfold L0, cn_core; cfa_in)).
apply (cfa_jal_pjf W fxk _ mem _ _ 1064 cfa_l1064 ltac:(lia)). intros X2.
change (1064 + 4) with 1068.
eapply SRr'_bind.
{ apply (cfa_pjf_call P PC D fxk ly S Hp W _ mem _ k Lam peak cnt ran ownl r1 r2 r3 (cn_d1 D) st1
    [(cn_d2 D, st2); (cn_d3 D, st3)] 1068 F1 HPRE ltac:(unfold cfa_rets; cfa_in)).
  - exact (cfa_pjm_step2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM).
  - apply (cfa_regsat_incl _ L0); [|exact HcoreL0].
    apply cfa_regsat_upd; [exact HL0r|]. apply cfa_regsat_upd; [exact HL0a|]. exact HR.
  - cfa_getr. reflexivity.
  - cfa_getr. reflexivity.
  - exact HPM.
  - exact HF1.
  - exact HC24. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & Lam2 & -> & HP2 & HM2 & HC2 & HPR2 & HKF2 & HPM2).
assert (HR2 : cn_regsat regs2 L0).
{ eapply (cfa_regsat_pres _ regs2 L0); [|exact HP2 | exact HL0cs].
  apply cfa_regsat_upd; [exact HL0r|]. apply cfa_regsat_upd; [exact HL0a|]. exact HR. }
(* ---- 1068 ld a0, 48(s1) (= d2, cn_slots) ; 1072 jal pj_free ---- *)
pose proof HM2 as (_ & HSL2 & _).
pose proof (proj1 (Forall_forall _ _) HSL2 (48, cn_d2 D) ltac:(cfa_in)) as Hs48. cbn [fst snd] in Hs48.
apply (cfa_ld_1068 W2 fxk regs2 mem2 md2 _ (cn_S1 D) (cn_d2 D)
  (cfa_regsat_get regs2 L0 9%bv (cn_S1 D) HR2 ltac:(unfold L0, cn_core; cfa_in)) ltac:(lia) ltac:(lia) Hs48).
intros X3.
apply (cfa_jal_pjf W2 fxk _ mem2 _ _ 1072 cfa_l1072 ltac:(lia)). intros X4.
change (1072 + 4) with 1076.
eapply SRr'_bind.
{ apply (cfa_pjf_call P PC D fxk ly2 S2 Hp2 W2 _ mem2 _ k2 Lam2 peak cnt ran ownl r1 r2 r3 (cn_d2 D) st2
    [(cn_d3 D, st3)] 1076 F2 HPRE ltac:(unfold cfa_rets; cfa_in)).
  - exact (cfa_pjm_step2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM2).
  - apply (cfa_regsat_incl _ L0); [|exact HcoreL0].
    apply cfa_regsat_upd; [exact HL0r|]. apply cfa_regsat_upd; [exact HL0a|]. exact HR2.
  - cfa_getr. reflexivity.
  - cfa_getr. reflexivity.
  - exact HPM2.
  - exact (HKF2 (cn_d2 D) st2 F2 ltac:(cfa_in) HF2).
  - clear - HC2 HC24. lia. }
cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & Lam4 & -> & HP4 & HM4 & HC4 & HPR4 & HKF4 & HPM4).
assert (HR4 : cn_regsat regs4 L0).
{ eapply (cfa_regsat_pres _ regs4 L0); [|exact HP4 | exact HL0cs].
  apply cfa_regsat_upd; [exact HL0r|]. apply cfa_regsat_upd; [exact HL0a|]. exact HR2. }
(* ---- 1076 mv a0, s3 ; 1080 jal pj_free ---- *)
apply cfa_mv_1076. intros X5.
rewrite (cfa_regsat_get regs4 L0 19%bv (cn_d3 D) HR4 ltac:(unfold L0, cn_core; cfa_in)).
apply (cfa_jal_pjf W4 fxk _ mem4 _ _ 1080 cfa_l1080 ltac:(lia)). intros X6.
change (1080 + 4) with 1084.
eapply SRr'_bind.
{ apply (cfa_pjf_call P PC D fxk ly4 S4 Hp4 W4 _ mem4 _ k4 Lam4 peak cnt ran ownl r1 r2 r3 (cn_d3 D) st3
    [] 1084 F3 HPRE ltac:(unfold cfa_rets; cfa_in)).
  - exact (cfa_pjm_step2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM4).
  - apply (cfa_regsat_incl _ L0); [|exact HcoreL0].
    apply cfa_regsat_upd; [exact HL0r|]. apply cfa_regsat_upd; [exact HL0a|]. exact HR4.
  - cfa_getr. reflexivity.
  - cfa_getr. reflexivity.
  - exact HPM4.
  - exact (HKF4 (cn_d3 D) st3 F3 ltac:(cfa_in) (HKF2 (cn_d3 D) st3 F3 ltac:(cfa_in) HF3)).
  - clear - HC4 HC2 HC24. lia. }
cbv beta. intros W6 c6 _ (ly6 & S6 & Hp6 & regs6 & mem6 & md6 & k6 & Lam6 & -> & HP6 & HM6 & _ & HPR6 & _ & HPM6).
assert (HR6 : cn_regsat regs6 L0).
{ eapply (cfa_regsat_pres _ regs6 L0); [|exact HP6 | exact HL0cs].
  apply cfa_regsat_upd; [exact HL0r|]. apply cfa_regsat_upd; [exact HL0a|]. exact HR4. }
(* ---- CN_FRCUT (1084) ---- *)
apply SRr'_ret. split; [|exact HPM6].
exists fxk, ly6, S6, Hp6, regs6, mem6, md6, k6, Lam6, peak, cnt, ran, r1, r2, r3, r, ownl.
split; [reflexivity|].
apply (cn_fr_of_pjm (fx := fx) B D fxk ly6 S6 Hp6 W6 regs6 mem6 md6 k6 Lam6 peak cnt ran r1 r2 r3 r ownl HM6);
  [|exact Ho | exact Hr | |].
- apply (cfa_regsat_incl _ L0 _ HR6). unfold L0. intros x Hx. apply in_app_or in Hx. apply in_or_app.
  destruct Hx as [Hx | Hx]; [left; exact Hx | right; cbn [In] in Hx |- *; tauto].
- (* no copy refused: the events made since entry, through the three pj_free *)
  intros E0. destruct (HEV0 E0) as (Hr1 & Hr2 & Hr3 & HPG & Hran & HRDS & _).
  split; [exact Hr1|]. split; [exact Hr2|]. split; [exact Hr3|].
  exists o1, o2, o0. split; [|exact Hran].
  pose proof (HPR6 _ o0 (HT3 E0) (HPR4 _ o2 (HT2 E0) (HPR2 _ o1 (HT1 E0) HPG))) as HPG6.
  rewrite (cfa_cevs3 D r1 r2 r3 Hr1 Hr2 Hr3), <- !app_assoc in HPG6.
  rewrite (cfa_fpj D o1 o2 o0 st1 st2 st3 HRDS). exact HPG6.
- (* a refused copy: the free cut's cn_cdead D (it names only the entry state) *)
  intros En. destruct (HEVN En) as (_ & _ & _ & _ & HCD). exact HCD.
Qed.

End cf.

(* HH's instance witness (an image / parameter premise names the lemma that closes it at the instance, as
   Cno102A_FT.v's cn_hw_preset): CFHEAD-16 holds at the preset allocator parameters (cf_head = 16 = HEAD) *)
Lemma cn_head16_preset : @PRH_Base.prh_head16 CfParamsPreset.CfParams_preset.
Proof. reflexivity. Qed.

Print Assumptions cn_seg_pjf.

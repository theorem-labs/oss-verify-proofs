(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 4213 of its 4307 lines of code are new or changed and 684 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): the walk sits at the world relation
   R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (the contract note, the internal file WLE-CONTRACT.md): the
   journals AJ / AJW are ajournal_xR / ajournal_xwR at R, every segment statement is YA0nH.SRr' SEGS RZ_cf, and the
   crossed callees meet the Kit's call rules at R: pj_set's text (SRr' with fpostWmR at wle') by crt102rw_postW0R,
   pj_write's (fpostFm) and parse_noting's (fpostFbm) as they stand, pj_string's plain text (SRr, fpostWm) by
   YA0nH.SRr_SRr' and the engine's YCbqGcallW.fpostW_x_R_lift, fuzz_alloc_ran_out's plain text by the Kit's
   crt102rw_lift_x, strlen's row by the engine's YGcallMxmn.aj_strlen_at_xromR. The
   texts' new premises: the run's length bound from the Section hypothesis HOS4, and parse_noting's hull budget from
   the run position (PresetHullPay.hull_budget_of_room_pos; one call's worth by crt102rw_hull_nt_rt). *)
(* base: commit 2fdcfd7be069 (post-landing line). kb round (brief
   the internal file wild-budget-kb-reshape.md): crt_live carries its budget kb (U, the G / K /
   O1 / W / reading states at 64 = prh_wk F_round_trip_text + prh_wk F_round_trip_text; after parse_noting, N and L0
   at 66 = prh_wk F_check_round_trip) and its journal at a budget WS with wbudget [] kb WS; the parse_noting call runs
   over the Kit's budgeted call rule crt102rw_call_b, and crt102rw_wild_budget_pn is RESTATED in the kb form and
   DISCHARGED here (crt102rw_wild_budget_pn_goal, Qed, from the text's entry room HWR0).
   The Step-1 ruling of the contract texts' owner (on 1409ad6e7e37): the four OPEN_K0_* goals close only at their
   SOURCES, in this file, as B' T3 does (Crt102B_T3U.v / Crt102B_T3S.v / Crt102B_T3O.v). pj_string's, pj_set's and
   pj_write's refused arms are refuted where each callee returns (crt102rw_at_U, crt102rw_G_taken, crt102rw_Wgo) by the
   callee text's own dead-arm conjunct, and copy's ordered free list is pj_set's FREEORD-COPY conjunct at K, carried K
   -> O1 -> W -> R -> N (crt102rw_copy_fo). The four Props are RETIRED and crt102_rw is Qed. *)
(* fuzz_preset, the walk of check_round_trip, Crt102Rewrite: image A' (asan 1be0f53d96cb9d6c, unstripped twin
   bff8519bbe3ea0e4). The head of the INLINED round_trip_rewrite (src-102/new/fuzz_preset.c sha256 c7b4007bba7bab3e,
   new:715-741) on check_round_trip's own class-3 fake frame, cuts U .. L0, with the infrastructure in Crt102Kit.v.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemmas of check_round_trip); the function-level
   lookup is the unit owner's (proof-index check_round_trip EXIT=0, an internal record of that lookup:
   only PLAIN lib/Prog and UBSAN lib/U/Prog proofs are released, concluding in SR).
   INPUTS OF RECORD: the rewrite's branch (cut from 8d89746aeafb), with the walk's base
   9912f952f0c3 merged; the walk's glue lib/A/Prog/Crt102Glue.v (the interface, unchanged by this file); the cut
   DESIGN.md (sha256 d05697dd088c; internal record); the listing, the internal file crt.A.s; the structure of the closed walk S10TxString.v (at commit
   a977ac095573; that file is not in this tree), whose S10Env.v is reused unchanged.
   THE CODE (A' check_round_trip + offsets, the internal file crt.A.s): U +0x1e4 (unpoison back / v, &doc->n and its inline check, doc->n,
   the STAMP literal) -> pj_string +0x24c -> G +0x250 -> pj_set +0x278 -> K +0x27c (s8 = seqz) -> O1 +0x280 (first
   out_of_memory: g_own_ran_out, fuzz_alloc_ran_out +0x290) -> +0x294 (beqz s8; &back spill) -> pj_write +0x2b0 -> W +0x2b4
   (s8 = saved, beqz; second out_of_memory's own-flag test, fuzz_alloc_ran_out +0x2c4) -> +0x2c8 (bnez; strlen +0x2d0) ->
   +0x2d4 (a1 = len, a0 = s8, a2 = &back; parse_noting +0x2e0) -> N +0x2e4 (s6 = snez) -> O2 (own flag; fuzz_alloc_ran_out
   +0x2f0) -> +0x2f4 (beqz) -> L0 +0x470.
   THE SEGMENTS (each Qed): crt102rw_at_U (U .. G, pj_string; its refused arm dead), crt102rw_G_taken (G .. K, pj_set;
   its res = -1 arm dead), crt102rw_atK (K), crt102rw_O1 (O1), crt102rw_Wgo (W0, pj_write; its refused arm dead),
   crt102rw_W2 (W), crt102rw_R712 (strlen), crt102rw_R724 (parse_noting), crt102rw_R740 (N .. L0), composed by
   crt102rw_chain (Qed) and stated by crt102_rw (Qed, at its continuation crt102rw_L0K).
   WHAT IS PROVED AND WHAT IS ASSUMED AT THE LANDING CUT (commit 7cdbb61b5fa0; measured on this
   file's build): every segment above is Qed; crt102rw_chain is a Qed implication from FIVE named Props:
   OPEN_K0_DEAD_PJSTRING, OPEN_K0_DEAD_PJSET, OPEN_K0_DEAD_PJWRITE, OPEN_K0_FREEORD_COPY (the texts', as before the cut),
   and crt102rw_wild_budget_pn, NEW at the cut: the parse_noting TWIN of Crt102Arms.arms_wild_budget and of
   Crt102B_RRT.crtb_wild_budget. The cut's tparse_noting_specX asks the room `wild_room (as_universe B) []
   (prh_wk F_parse_noting) (st_depot Sc)` (PRH_FnCheck.v:637) and posts a BUDGETED journal (fpostFbm .. (wbudget []
   (prh_wk F_parse_noting)), :648); the glue keeps crt_live_journal at AJ (budget []) and states no room, so the call
   lands only given, at every live call state, that room and the callee's journal `AJW .. WS1` (wbudget [] (prh_wk
   F_parse_noting) WS1) as AJ. MEASURED: nothing at the cut bounds WS1 to [] (the text's k is 2, :634-636). Route and
   owner: the kb re-shape (the contract texts), brief, the internal file wild-budget-kb-reshape.md. AT THE kb ROUND (this file's
   head note): crt102rw_wild_budget_pn is restated in the kb form and discharged here (crt102rw_wild_budget_pn_goal). AT
   THE STEP-1 RULING OF THE CONTRACT TEXTS' OWNER (this file's head note): the four OPEN_K0_* goals are proved at their
   sources and retired. RETIRED by the cut: OPEN_K0_SRC_CEIL (src_rd asks no `+ 8`, PRH_Base.v:1660; the call gives the
   new form from the live text block, crt102rw_R724) and OPEN_K0_UNIV_END (no DW).
   THE UNREACHABILITY ARGUMENTS:
   - the property abort of new:728 (`!set`, +0x6f8 from O1's `beqz s8`): O1 is entered with s8 = 1 on every state the
     chain builds - pj_set's granted arms give res = 0 (s8 = seqz res = 1). Its refused arm res = -1 is where `set = 0`
     would come from, and there the request bound holds: pj_set's key strdup and its grows ask at most RQA_crt t <= most
     (Crt102Model cm_rqa_key / cm_rqa_grow / cm_rqa_grow_keys), so prh_oks' third conjunct sets g_ran_out = 1 and O1's
    out_of_memory () = 1 jumps to X before the `beqz s8`; that arm is dead at its source (DEAD-PJSET, refuted in
    crt102rw_G_taken).
   - the inline shadow report crossed (U's check of &doc->n, +0x228 .. +0x22c, report +0x710): doc's 56 bytes are
     addressable at every state the journal from the entry reaches (ck_obj_home, Crt102Kit.v crt102rw_home_keep). No
     other inline check lies on U .. L0 (the shadow stores of U / X are split from the checks, the ss_SH pattern).
   - arms C4a (O1) and C4c (O2 / W's own-flag and fuzz_alloc_ran_out tests, FF fuzz_free (saved)): g_own_ran_out = 0 at
     every state (no crossed text writes it; prh_own from the ledger) and g_ran_out = 0 on the granted chain (pj_string's
     and pj_set's taken arms; pj_write unfailed so every grow was taken, crt102rw_putN_oktrue; parse_noting's OUTCOME
     clause at the reading's position gives ran' = 0), so every out_of_memory () the chain reaches returns 0. C4a / C4c are
     reached only from the refused arms of pj_string / pj_set / pj_write, each dead at its source (DEAD-PJSTRING /
     -PJSET / -PJWRITE, refuted where its callee returns); their join X -> J is Crt102Kit.v's crt102rw_at_X, Qed for
     any entry.
   THE REQUEST BOUNDS, cited at each call: pj_string Z.of_nat |STAMP| + 1 <= most (cm_rqa_stamp), pj_set 56 * cap2R
   (ck_members t) <= most and |MOD_AT| + 1 <= most (cm_rqa_grow / cm_rqa_key, cm_rqa_grow_keys), pj_write RQW (ck_crt_tree
   t) true <= most (cm_rqa_write, PJWRITE's premise), parse_noting RQ_pj_parse (wdoc (ck_crt_tree t) true) <= most
   (cm_rqa_read); no peak equality is leaned on.
   SECTION HYPOTHESES, each with its owner or source: LAWS (AR_laws_x at cf_head; the allocator engine's law set);
   zs_aligned (MARKED STAND-IN, owner: the contract texts; the unit's image binding of B); img_shadow_vis_x (MARKED
   STAND-IN, owner: the image row; discharged at ARx := YGcallcf.ARxs by img_shadow_vis_xs_A); HPRE .. H0FR
   (tcheck_round_trip_specX's premises, discharged by Crt102Top); PJSTR / PJSET / RANOUT / PJWRITE / PNOTING (the
   contract texts); STRLEN (the libc __wrap_strlen row astrlen_realizes_xrom); TAIL (Crt102Tail.v crt102_tail).
   VACUITY: This statement goes through prh_univ_closure, whose clause 4 is false on B' for data words; it is vacuous at
   its instance until the contract texts' batch lands the 4a / 4b split (4a: the code word stays a fixed In; 4b:
   inU (as_universe B) (prh_trace pc_free_ra0 r [w])) and removes DW.
   NUMERALS: 540 / 660 / 712 / 724 / 740 / 756 and the CRT cut-offset names (DERIVED: 4 * the slot inside check_round_trip);
   5392 (DERIVED: CRT_PC_A + CRT_O1_OFF); 1456 (DERIVED: the `lbu a0, -0x5b0(s9)` displacement against the flag object);
   254 / 243 / 315 and the atom indices 33 .. 63 (WORD: the symbolic engine's atom numbering; 254 = A_OBJ 13); register
   numbers 1 .. 27 (WORD); 56 (LENGTH: struct pj), 32 / 128 / 224 (LENGTH: back / v / copy offsets, the CRT_OFF names), 512 / 64 /
   504 (LENGTH: the class-3 frame, its shadow bytes, its flag slot), 24 / 56 / 72 / 80 / 88 / 112 (LENGTH: the s1 spill
   slots, the CRT_SP names), 240 / 224 (LENGTH: the realigned sp), 4096 / 2048 (LENGTH: ESTACK, the text bound), 27632 / 16480
   (DERIVED: STK budgets by computation), 8 / 16 (LENGTH: word, cf_head), 0x7fff8000 (WORD: ASan's shadow-mapping offset,
   SHADOW_OFF) and 268431360 (DERIVED: its eighth), 2 ^ 32 / 2 ^ 40 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 62 / 2 ^ 63 / 2 ^ 64
   (LENGTH: bounds). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss PresetFreeFo PresetRun PresetLiveSec PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_Supply PRH_PjOrder PresetCfnA.
(* pj_write's refused arm, refuted at its source from tpj_write_specX's DEAD-PJWRITE conjunct (crt102rw_Wgo) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Refute.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Crt102Glue Crt102Img Crt102Model Crt102Kit.
(* The re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the
   zone (YGcfRehidePost.RZ_cf); the hull budget from a run position (PresetHullPay) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal PresetSecTotalRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- A GRANTED READING'S OUTCOMES GIVE THE ALL-GRANTED FREE LIST, and THE ROOM COUNTS FROM A POSITION
   (Rtt102CmpPNA.v pn_ag_some / pn_ag_none / pn_jf_cont_agree / pn_jf_agree / pn_pj_frees_agree / pn_ok_upto_some /
   pn_pkR_bound / pn_firstn_add / pn_cnt_subm / pn_pkR_pos, commit 0d042ecb926, verbatim
   but for the names) ---- *)
Lemma crt102rw_ag_some : forall A Bt (m : PjGrammar.M A) (k : A -> PjGrammar.M Bt) ok a t ok0,
  PjGrammar.agrees m -> m [] = (Some a, t, ok0) ->
  PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jbind m k [])))) ->
  ok0 = [] /\ PjGrammar.ok_upto ok (PjGrammar.calls t) /\ m ok = (Some a, t, skipn (PjGrammar.calls t) ok) /\
  PjGrammar.ok_upto (skipn (PjGrammar.calls t) ok) (PjGrammar.calls (snd (fst (k a [])))).
Proof.
intros A Bt m k ok a t ok0 Hm E Hu.
assert (E0 : ok0 = []).
{ pose proof (PjGrammar.agrees_nil A m Hm) as N. rewrite E in N. cbn [fst snd] in N. congruence. }
subst ok0.
assert (Ht : snd (fst (PjGrammar.jbind m k [])) = t ++ snd (fst (k a []))).
{ unfold PjGrammar.jbind. rewrite E. cbv beta iota. destruct (k a []) as [[r t'] ok2]. reflexivity. }
rewrite Ht, PjGrammar.calls_app in Hu.
assert (Hut : PjGrammar.ok_upto ok (PjGrammar.calls t)) by (eapply PjGrammar.ok_upto_le; [exact Hu | lia]).
split; [reflexivity|]. split; [exact Hut|]. split.
- pose proof (proj1 (Hm ok)) as H. rewrite E in H. cbn [fst snd] in H. exact (H Hut).
- apply PjGrammar.ok_upto_skipn. exact Hu.
Qed.
Lemma crt102rw_ag_none : forall A Bt (m : PjGrammar.M A) (k : A -> PjGrammar.M Bt) ok t ok0,
  PjGrammar.agrees m -> m [] = (None, t, ok0) ->
  PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jbind m k [])))) ->
  PjGrammar.ok_upto ok (PjGrammar.calls t) /\ m ok = (None, t, skipn (PjGrammar.calls t) ok).
Proof.
intros A Bt m k ok t ok0 Hm E Hu.
assert (Hut : PjGrammar.ok_upto ok (PjGrammar.calls t)).
{ unfold PjGrammar.jbind in Hu. rewrite E in Hu. cbv beta iota in Hu. exact Hu. }
split; [exact Hut|].
pose proof (proj1 (Hm ok)) as H. rewrite E in H. cbn [fst snd] in H. exact (H Hut).
Qed.
Lemma crt102rw_jf_cont_agree : forall (sm : list Z -> Z * Z) f d o x ok,
  (forall d o n cap acc af y ok,
     PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jrl sm f d o n cap acc y [])))) ->
     PresetReqAt.jfl sm f d o n cap af y ok = PresetReqAt.jfl sm f d o n cap af y []) ->
  PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jr_cont (PjGrammar.jrl sm f) d o x [])))) ->
  PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d o x ok = PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d o x [].
Proof.
intros sm f d o x ok IHl Hu. revert Hu. unfold PresetReqAt.jf_cont, PjGrammar.jr_cont.
destruct (Nat.ltb PjGrammar.MAXD (S d)); [intros _; reflexivity|].
cbv zeta. destruct (PjGrammar.skip (tl x)) as [|c r].
- intros Hu. eapply IHl. exact Hu.
- destruct (c =? PjGrammar.closer o); [intros _; reflexivity|]. intros Hu. eapply IHl. exact Hu.
Qed.
Lemma crt102rw_jf_agree : forall (sm : list Z -> Z * Z) f,
  (forall d x ok, PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jrv sm f d x [])))) ->
     PresetReqAt.jfv sm f d x ok = PresetReqAt.jfv sm f d x []) /\
  (forall d o n cap acc af y ok,
     PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jrl sm f d o n cap acc y [])))) ->
     PresetReqAt.jfl sm f d o n cap af y ok = PresetReqAt.jfl sm f d o n cap af y []).
Proof.
intros sm f. induction f as [|f [IHv IHl]].
- split; intros; reflexivity.
- split.
  + intros d x ok Hu.
    pose proof (proj1 (proj1 (PjGrammar.agrees_fuel sm (S f)) d x ok) Hu) as Hag.
    cbn [PjGrammar.jrv] in Hu. revert Hu. cbn [PresetReqAt.jfv].
    destruct (PjGrammar.skip x) as [|b y]; [intros _; reflexivity|].
    destruct (b =? 123).
    { intros Hu. exact (crt102rw_jf_cont_agree sm f d true (b :: y) ok IHl Hu). }
    destruct (b =? 91).
    { intros Hu. exact (crt102rw_jf_cont_agree sm f d false (b :: y) ok IHl Hu). }
    intros _. rewrite Hag. reflexivity.
  + intros d o n cap acc af y ok Hu.
    cbn [PjGrammar.jrl] in Hu. cbn [PresetReqAt.jfl].
    destruct (PjGrammar.grow o n cap []) as [[[cap1|] tg] okg] eqn:Eg.
    * destruct (crt102rw_ag_some _ _ _ _ ok cap1 tg okg (PjGrammar.agrees_grow o n cap) Eg Hu) as (E0 & _ & Eg1 & Hu1).
      subst okg. rewrite Eg1. cbv beta iota zeta in Hu1 |- *.
      destruct (PjGrammar.jr_name o y []) as [[[[nm y1]|] tn] okn] eqn:En.
      -- destruct (crt102rw_ag_some _ _ _ _ _ (nm, y1) tn okn (PjGrammar.agrees_jr_name o y) En Hu1)
           as (E0n & _ & En1 & Hu2).
         subst okn. rewrite En1. cbv beta iota zeta in Hu2 |- *.
         destruct (PjGrammar.jrv sm f d y1 []) as [[[[v r]|] tv] okv] eqn:Ev.
         ++ destruct (crt102rw_ag_some _ _ _ _ _ (v, r) tv okv (proj1 (PjGrammar.agrees_fuel sm f) d y1) Ev Hu2)
              as (E0v & Hut & Ev1 & Hu3).
            subst okv.
            pose proof (IHv d y1 (skipn (PjGrammar.calls tn) (skipn (PjGrammar.calls tg) ok))) as Hv.
            rewrite Ev in Hv. cbn [fst snd] in Hv. rewrite (Hv Hut), Ev1. cbv beta iota zeta in Hu3 |- *.
            revert Hu3. destruct (PjGrammar.skip r) as [|c r1]; [intros _; reflexivity|].
            destruct (c =? 44); [|intros _; reflexivity]. intros Hu3. eapply IHl. exact Hu3.
         ++ destruct (crt102rw_ag_none _ _ _ _ _ tv okv (proj1 (PjGrammar.agrees_fuel sm f) d y1) Ev Hu2) as (Hut & Ev1).
            pose proof (IHv d y1 (skipn (PjGrammar.calls tn) (skipn (PjGrammar.calls tg) ok))) as Hv.
            rewrite Ev in Hv. cbn [fst snd] in Hv. rewrite (Hv Hut), Ev1. reflexivity.
      -- destruct (crt102rw_ag_none _ _ _ _ _ tn okn (PjGrammar.agrees_jr_name o y) En Hu1) as (_ & En1).
         rewrite En1. reflexivity.
    * destruct (crt102rw_ag_none _ _ _ _ ok tg okg (PjGrammar.agrees_grow o n cap) Eg Hu) as (_ & Eg1).
      rewrite Eg1. reflexivity.
Qed.
Lemma crt102rw_pj_frees_agree : forall (sm : list Z -> Z * Z) x ok, PjGrammar.ok_upto ok (PjGrammar.ncalls sm x) ->
  PresetReqAt.pj_frees sm ok x = PresetReqAt.pj_frees sm [] x.
Proof.
intros sm x ok Hu. unfold PresetReqAt.pj_frees. apply (proj1 (crt102rw_jf_agree sm _)).
unfold PjGrammar.ncalls in Hu. rewrite PjGrammar.jr_run_eq in Hu. cbn [snd] in Hu.
unfold PjGrammar.jr_value in Hu. exact Hu.
Qed.
Lemma crt102rw_ok_upto_some : forall (sm : list Z -> Z * Z) x ok t tr, PjGrammar.jr_run sm x ok = (Some t, tr) ->
  PjGrammar.ok_upto ok (PjGrammar.ncalls sm x).
Proof.
intros sm x ok t tr E.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls sm x)) as [H | (j & Hj & Hf & Hu)]; [exact H|].
exfalso. destruct (PjGrammar.G7_2 sm x ok j Hj Hf Hu) as [H0 _]. rewrite E in H0. discriminate H0.
Qed.
Lemma crt102rw_pkR_bound : forall f s es (Bd : nat),
  (forall j, (j <= length es)%nat -> (PresetReqAt.cnt f (PresetReqAt.hlive_from s (firstn j es)) <= Bd)%nat) ->
  (PresetRun.pkR f s es <= Bd)%nat.
Proof.
intros f s es. revert s. induction es as [|e r IH]; intros s Bd H.
- cbn [PresetRun.pkR]. exact (H 0%nat (Nat.le_0_l _)).
- cbn [PresetRun.pkR]. apply Nat.max_lub.
  + exact (H 0%nat (Nat.le_0_l _)).
  + apply IH. intros j Hj. exact (H (Datatypes.S j) ltac:(cbn [length]; lia)).
Qed.
Lemma crt102rw_firstn_add : forall {X : Type} (l : list X) i j, firstn i l ++ firstn j (skipn i l) = firstn (i + j) l.
Proof.
intros X l. induction l as [|a l IH]; intros i j.
- rewrite skipn_nil, !firstn_nil. reflexivity.
- destruct i as [|i]; cbn [firstn skipn app Nat.add]; [reflexivity|]. f_equal. apply IH.
Qed.
Lemma crt102rw_cnt_subm : forall f a b, PresetReqAt.subm a b -> (PresetReqAt.cnt f a <= PresetReqAt.cnt f b)%nat.
Proof.
intros f a b [d Hd]. rewrite (PresetReqAt.cnt_perm f _ _ Hd), PresetReqAt.cnt_app. lia.
Qed.
Lemma crt102rw_pkR_pos : forall sm x os i H0 hist S E f Bn,
  PresetRoomPos.iface_room_pos sm x os i H0 hist S -> prh_run_at sm x os i E ->
  (Z.of_nat (length x) <= PresetReqAt.MAXB -> forall k,
     Z.of_nat (PresetReqAt.cnt f (PresetReqAt.hlive (firstn k (PresetRun.hruns sm x os)))) <= Bn) ->
  0 <= Bn ->
  Z.of_nat (PresetRun.pkR f (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E) <= Bn + 3.
Proof.
intros sm x os i H0 hist S E f Bn ((d & Hd & Hp) & _) Hrun HB HB0.
set (Hr := PresetRun.hruns sm x os) in *.
set (L := PresetRoom.rs_live (YGcfRoom.room_of_cf S)) in *.
assert (HM : forall k, Z.of_nat (PresetReqAt.cnt f (PresetReqAt.hlive (firstn k Hr))) <= Bn).
{ intros k. destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [Hx | Hx]; [exact (HB Hx k)|].
  assert (E0 : Hr = []) by (unfold Hr; apply PresetRoomCounts.iface_hruns_big; lia).
  rewrite E0, firstn_nil. change (PresetReqAt.cnt f (PresetReqAt.hlive [])) with 0%nat. lia. }
assert (Hbd : (PresetRun.pkR f L E <= Z.to_nat Bn + 3)%nat).
{ apply crt102rw_pkR_bound. intros j Hj.
  set (A := PresetReqAt.hlive (firstn i Hr)).
  assert (S1 : PresetReqAt.subm (PresetReqAt.hlive_from L (firstn j E))
                 (PresetReqAt.hlive_from (A ++ d) (firstn j E))).
  { apply PresetReqAt.hlive_from_mono. exists []. rewrite app_nil_r. exact (Permutation_sym Hp). }
  pose proof (PresetReqAt.hlive_from_le (firstn j E) A d) as S2.
  pose proof (crt102rw_cnt_subm f _ _ (PresetReqAt.subm_trans _ _ _ S1 S2)) as C1.
  rewrite PresetReqAt.cnt_app in C1.
  pose proof (PresetLiveSec.cnt_le_len f d) as C2.
  assert (Ej : firstn j E = firstn j (skipn i Hr)).
  { unfold prh_run_at in Hrun. fold Hr in Hrun. rewrite <- Hrun at 1.
    rewrite firstn_firstn, Nat.min_l by exact Hj. reflexivity. }
  assert (EA : PresetReqAt.hlive_from A (firstn j E) = PresetReqAt.hlive (firstn (i + j) Hr)).
  { unfold A, PresetReqAt.hlive. rewrite <- PresetReqAt.hlive_from_app, Ej, crt102rw_firstn_add. reflexivity. }
  rewrite EA in C1.
  pose proof (HM (i + j)%nat) as C3.
  lia. }
lia.
Qed.

(* ---- ONE CALL'S WORTH FOR AN INFIX OF round_trip (the hull premise of parse_noting's text,
   paid at the run position by PresetHullPay.hull_budget_of_room_pos): round_trip's secondary count and requests
   (PresetSecTotalRun.NT_round_trip) are inside one call's NCALL / TREQ_CALL, so any infix's counts are inside
   NCALL / TCALL (TCALL = TREQ_CALL + SEC_MAP_OVH * NCALL, PresetSecTotalRun.tsec_treq) ---- *)
Lemma crt102rw_hull_nt_rt : forall sm x t P Eg Q, Z.of_nat (length x) <= PresetReqAt.MAXB ->
  fst (PjGrammar.jr_run sm x []) = Some t -> PresetReqAt.round_trip sm t = P ++ Eg ++ Q ->
  Z.of_nat (PresetSecTotal.nsec Eg) <= PresetSecTotal.NCALL /\ PresetSecTotal.tsec Eg <= PresetSecTotal.TCALL.
Proof.
intros sm x t P Eg Q Hx Ht E.
destruct (PresetSecTotalRun.NT_round_trip sm x t Hx Ht) as [N T].
pose proof PresetSecTotalRun.consts_nn as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
rewrite E, !PresetSecTotal.nsec_app, !Nat2Z.inj_add in N. rewrite E, !PresetSecTotalRun.treq_app in T.
pose proof (PresetSecTotalRun.treq_nn P). pose proof (PresetSecTotalRun.treq_nn Q).
pose proof (PresetSecTotalRun.treq_nn Eg). pose proof (PresetSecTotalRun.tsec_treq Eg).
split.
- unfold PresetSecTotal.NCALL. lia.
- unfold PresetSecTotal.TCALL, PresetSecTotal.TREQ_CALL, PresetSecTotal.NCALL in *.
  unfold PresetSecTotal.SEC_MAP_OVH in *. lia.
Qed.

(* ======================================================================================================== *)
(* PART 2, image A': the segment cut of the inlined round_trip_rewrite, U .. X. *)
Section crtA. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation STKC := (@STK_check_round_trip prh_img_A).

(* the image's cut points are Crt102Img.v's (CRT_PC_A, CRT_*_OFF, the jal sites CRT_*_CALL); this slice adds only the
   end of the fourteen unpoison stores, its own segment boundary (DERIVED: 4 * the slot inside the function) *)
Definition crt102rw_U2_OFF : Z := 540.   (* +0x21c *)

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* The re-hiding move: the world relation of every journal below, the glue's crt_live_journal's
   and QF's, R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (Crt102Kit.v's PART 2 notations) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* the callee's journal at the empty budget (YCbqG.v ajournal_xR at RZW) *)
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (YCbqG.v ajournal_xwR at RZW; AJ is it at WS = []) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the two MARKED STAND-INS Crt102Kit.v's crt_cstr_img takes (S10TxState.v:141, :143, verbatim) *)
(* MARKED STAND-IN (the image binding of B; owner: the contract texts; ARcf gives it by amc_syms / aso_zshadow, YG0f.v:191) *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN (owner: the image row; FuzzStrdup.v's img_shadow_vis_cf restated over ARx) *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.

(* ---- a callee whose text concludes in the caller-window post at window 0 over R (PRH_Base.fpostWR, the R form of
   fpostW; pj_set's text at wle', pj_string's lifted by YCbqGcallW.fpostW_x_R_lift) meets the call rule's float form
   over R (YCbqG.v apost_base_xFR; its float state is the caller's). It is the R form of the plain
   crt102rw_postW0 it replaces ---- *)
Lemma crt102rw_postW0R : forall (fxk : YK11.FPState) STK FP rgc lyc Sc Hpc Wc memc mdc Q W' c',
  frm_zero (@YK11.fp_csr fxk) ->
  fpostWR (fx := fxk) B ARx SK RZW STK 0 FP rgc lyc Sc Hpc Wc memc mdc Q W' c' ->
  apost_base_xFR (fx := fxk) (SK := SK) SEGS B PST ARx RZW STK FP rgc lyc Sc Hpc Wc memc mdc Q W' c'.
Proof.
intros fxk STK FP rgc lyc Sc Hpc Wc memc mdc Q W' c' HFZ (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & _ & HP & HQ).
exists fxk, ly', S', Hp', regs', mem', md', k. rewrite !Z.add_0_r in HJ.
split; [exact Hc|]. split; [exact HFZ|]. split; [intros r _; reflexivity|].
split; [exact HJ|]. split; [exact HP | exact HQ].
Qed.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z)
  (CTX0 : list (list Z)).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (CRT_sp1 (regs := regs)).
#[local] Notation liveA := (crt_live (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (most := most)).
#[local] Notation atJ := (crt_at_J (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation atX := (crt_at_X (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation QFa := (QF (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgA := (crt_cfg (rc := rc) (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A)).
#[local] Notation bregsA := (crt_bregs (regs := regs)).
#[local] Notation dregsA := (crt_dregs (regs := regs) (doc := doc)).
#[local] Notation atU := (crt_at_U (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation atL0 := (crt_at_L0 (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).

(* ---- the text's premises this slice reads (Crt102Top.v discharges them from tcheck_round_trip_specX's) ---- *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis H0MN : YAkMemnorm.memnorm SEGS mem.
Hypothesis H0CL : prh_univ_closure B CTX0.
Hypothesis H0CTX : prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch).
Hypothesis H0READ : ck_read x = Some t.
Hypothesis H0LENX : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis H0KM : kept_img B CRT_MOD_AT_A (Z.of_nat (length ck_MOD_AT) + 1).
Hypothesis H0KS : kept_img B CRT_STAMP_A (Z.of_nat (length ck_STAMP) + 1).
Hypothesis H0WL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis H0WL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis H0CNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis H0LED : prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0.
Hypothesis H0RAN : ran = 0.
Hypothesis H0RQA : RQA_crt t <= most.
Hypothesis H0LIVE : blocks_bytes S + LIVE_check_round_trip t <= LIVE_MAX.
Hypothesis H0RQ : RQ_crt t + cf_head < cf_malloc_max.
Hypothesis H0FR : Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_round_trip.
(* the text's wild room at entry (PRH_FnCheck.v:1366, kb round): read only by crt102rw_wild_budget_pn_goal *)
Hypothesis HWR0 : YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_round_trip) (st_depot S).
(* THE RUN HAS AT MOST 4 CALLS (DRAFT; tcheck_round_trip_specX's own premise, PRH_FnCheck.v:2363,
   which Crt102Top passes): pj_string's, pj_set's and pj_write's texts take it, and parse_noting's hull budget is paid
   from it at the run position (PresetHullPay.hull_budget_of_room_pos); the callees' rp_os is the walk's *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

(* ---- the callee texts (the contract texts at caa965672d21 by path on base 33ff96ae153c: PRH_FnPj 79e2637972c6,
   PRH_FnAlloc ec27f8c6dd04, PRH_FnWriter 5e80aa3d7978, PRH_FnCheck 22cddcb1e58a), each at every float state (their
   walks are generic in fx), at the caller's universe closure ---- *)
Hypothesis PJSTR : forall fxk : YK11.FPState, PRH_FnPj.tpj_string_specX (fx := fxk) B ARx SK CTX0.
Hypothesis PJSET : forall fxk : YK11.FPState, PRH_FnPj.tpj_set_specX (fx := fxk) B ARx SK CTX0 DOC_D.
Hypothesis RANOUT : forall fxk : YK11.FPState, PRH_FnAlloc.tfuzz_alloc_ran_out_specX (fx := fxk) B ARx SK.
Hypothesis PJWRITE : forall fxk : YK11.FPState, PRH_FnWriter.tpj_write_specX (fx := fxk) B ARx SK CTX0 DOC_D.
Hypothesis PNOTING : forall fxk : YK11.FPState, tparse_noting_specX (fx := fxk) B ARx SK CTX0.
(* THE LIBC ROW for __wrap_strlen, as a Section hypothesis (FuzzStrdup.v carries its strlen row the
   same way): YGcallMxmn.v's astrlen_realizes_xrom, the arodata_okP text with the memnorm keep (crt_live's last
   conjunct needs it after the call at +0x2d0), the form Crt102Loops.v takes for strcmp *)
Hypothesis STRLEN : forall fxq : YK11.FPState,
  @YGcallMxmn.astrlen_realizes_xrom fxq SEGS B ARx RLO RHI (SIGMA AS___wrap_strlen).

(* ---- the join: Crt102Tail.v's crt102_tail, the single lemma every arm ends in ---- *)
Hypothesis TAIL : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  atJ fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_J_OFF rg memc mdc) QFa.

(* a register a run did not write keeps its start value (Crt102Kit.v's crt102rw_keep, section-local there) *)
Ltac crt102rw_kr HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* ---- the frame's two unpoisoned locals: zero shadow bytes 4 .. 10 (back) and 16 .. 22 (v) make each 56-byte window
   addressable, and the frame's shadow is present, so each hull is visible ---- *)
Lemma crt102rw_open_locals : forall (Wc : world SEGS) memc F,
  0 <= F -> F mod 32 = 0 -> F + 512 <= YM05.alloc_ceiling ->
  (forall o, 4 <= o <= 10 \/ 16 <= o <= 22 -> aview SEGS (w_H Wc) memc (shadow_addr F + o) = Some 0) ->
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc (shadow_addr F + i)) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + CRT_OFF_V) 56 /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) (F + CRT_OFF_BACK) 56 /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) (F + CRT_OFF_V) 56.
Proof.
intros Wc memc F HF0 F32 HF Hz HPs.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite F32, Z.add_0_r in DF.
assert (EB : forall j, (F + j * 8) / 8 = F / 8 + j).
{ intros j. rewrite DF. replace (32 * (F / 32) + j * 8) with ((4 * (F / 32) + j) * 8) by lia. rewrite Z.div_mul by lia.
  replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. rewrite Z.div_mul by lia. lia. }
unfold CRT_OFF_BACK, CRT_OFF_V.
split; [|split; [|split]].
- apply zero_shadow_range; [rewrite DF; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia;
    apply Z.mod_mul; lia | reflexivity |].
  intros i Hi. change (56 / 8) with 7 in Hi. unfold shadow_of_addr.
  replace (F + 32) with (F + 4 * 8) by lia. rewrite EB.
  replace (SHADOW_OFF + (F / 8 + 4) + i) with (shadow_addr F + (4 + i)) by (unfold shadow_addr; lia). apply Hz. lia.
- apply zero_shadow_range; [rewrite DF; replace (32 * (F / 32) + 128) with ((4 * (F / 32) + 16) * 8) by lia;
    apply Z.mod_mul; lia | reflexivity |].
  intros i Hi. change (56 / 8) with 7 in Hi. unfold shadow_of_addr.
  replace (F + 128) with (F + 16 * 8) by lia. rewrite EB.
  replace (SHADOW_OFF + (F / 8 + 16) + i) with (shadow_addr F + (16 + i)) by (unfold shadow_addr; lia). apply Hz. lia.
- intros s Hs.
  assert (F8 : F / 8 = 4 * (F / 32)) by (symmetry; apply Z.div_unique with 0; lia).
  assert (A1 : shadow_addr (F + 32) = shadow_addr F + 4).
  { unfold shadow_addr. assert ((F + 32) / 8 = F / 8 + 4) by (symmetry; apply Z.div_unique with 0; lia). lia. }
  assert (A2 : shadow_addr (F + 32 + 56 - 1) = shadow_addr F + 10).
  { unfold shadow_addr. assert ((F + 32 + 56 - 1) / 8 = F / 8 + 10) by (symmetry; apply Z.div_unique with 7; lia). lia. }
  rewrite A1, A2 in Hs.
  assert (Hm : shadow_addr F = 4 * (SHADOW_OFF / 4 + F / 32)) by (unfold shadow_addr, SHADOW_OFF in *; lia).
  pose proof (Z.div_mod (shadow_addr F + 4) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr F + 4) 8 ltac:(lia)).
  pose proof (Z.div_mod (shadow_addr F + 10) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr F + 10) 8 ltac:(lia)).
  replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
  apply crt102rw_apresent_vis. apply HPs. lia.
- intros s Hs.
  assert (F8 : F / 8 = 4 * (F / 32)) by (symmetry; apply Z.div_unique with 0; lia).
  assert (A1 : shadow_addr (F + 128) = shadow_addr F + 16).
  { unfold shadow_addr. assert ((F + 128) / 8 = F / 8 + 16) by (symmetry; apply Z.div_unique with 0; lia). lia. }
  assert (A2 : shadow_addr (F + 128 + 56 - 1) = shadow_addr F + 22).
  { unfold shadow_addr. assert ((F + 128 + 56 - 1) / 8 = F / 8 + 22) by (symmetry; apply Z.div_unique with 7; lia). lia. }
  rewrite A1, A2 in Hs.
  assert (Hm : shadow_addr F = 4 * (SHADOW_OFF / 4 + F / 32)) by (unfold shadow_addr, SHADOW_OFF in *; lia).
  pose proof (Z.div_mod (shadow_addr F + 16) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr F + 16) 8 ltac:(lia)).
  pose proof (Z.div_mod (shadow_addr F + 22) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr F + 22) 8 ltac:(lia)).
  replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
  apply crt102rw_apresent_vis. apply HPs. lia.
Qed.

(* ---- U2 (+0x21c): doc's member count read through &doc->n after its inline check, spilled with &doc->n at s1 + 0x50 /
   0x58; regions: the two spill words (written) and doc->n (read, atom 64); the shadow base in s10 ---- *)
Definition crt102rw_ssU2 : sstate := mkSS (CRT_PC_A + crt102rw_U2_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 80 96 80 96 [];
    YP09.mkRegion (Some (xr 21)) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 64 0))] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 21, mkAF 4096 (2 ^ 47 - 64) 3); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF 0 (2 ^ 64 - 1) 0)] [] []).
Lemma crt102rw_U2_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg n,
  getr rg 9 = w64 sp1 -> getr rg 21 = w64 doc -> getr rg 26 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 -> sp1 + 96 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= doc -> doc + 64 <= sp1 -> doc mod 8 = 0 -> 0 <= n < 2 ^ 64 ->
  (forall o, 80 <= o < 96 -> apresent (w_H Wc) memc (sp1 + o)) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (doc + 40) 8 n ->
  @st_ok_pi SEGS VAL fxk (TE regs rg [w64 n]) crt102rw_ssU2
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + crt102rw_U2_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SOff (xr 26) 0) [] (TE regs rg [w64 n]) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg n R9 R21 R26 H1 H2 H3 H4 H5 H6 Hn HP Vn.
set (E := TE regs rg [w64 n]).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X21 : bv_unsigned (ew E (xr 21)) = doc).
{ unfold E, xr. rewrite (te_cur regs rg _ 21%bv 21) by reflexivity. rewrite R21. apply unsigned_lit_small. lia. }
assert (X26 : bv_unsigned (ew E (xr 26)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E64 : ew E 64 = w64 n) by exact (te_more_lt regs rg [w64 n] 0 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = n) by (rewrite E64; apply unsigned_lit_small; lia).
split.
- apply (@ts_st_ok fxk).
  all: try change (TE regs rg [w64 n]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | |constructor].
      intros o Ho. cbn [YP09.r_wlo YP09.r_whi] in Ho. apply (apresent_writable SEGS). apply HP. lia.
    * apply (ts_rok E _ (xr 21) doc); [exact X21 | lia | lia | intros o Ho; cbn in Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 40 8 (SOff 64 0) n);
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact Vn.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X21.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X21, X26, X64.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1. repeat split; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* reading a final symbolic state back (the call-entry form, st_ok of the post-jal state) *)
Lemma crt102rw_chunk_vm_ok : forall (fxk : YK11.FPState) E ss (H : word -> bool) ms0 i r k b o (n : N) e v,
  @st_ok SEGS fxk E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some r ->
  YP09.r_base r = Some k -> bv_unsigned (ew E k) = b ->
  In (YP09.mkChunk o (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms0)) (b + o) (N.to_nat n) v.
Proof.
intros fxk E ss H ms0 i r k b o n e v HS Hi Hb Hk Hc He Hv Hn.
pose proof (@st_ok_mem_ok SEGS fxk E ss (restrict H ms0) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as Hr.
pose proof (region_ok_chunk SEGS E _ r _ Hr Hc) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck. rewrite Hk in Hck.
exact (val_of_chunk_ok SEGS E _ b o n e v Hck He Hv Hn).
Qed.

(* ---- a block the walk holds beyond the entry's is a live allocator block that was not live at entry (the sep law:
   no live block occurs twice) ---- *)
Definition crt102rw_zz_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma crt102rw_count2 : forall (l : list (Z * Z)) z, (2 <= count_occ crt102rw_zz_dec l z)%nat ->
  exists la lb lc, l = la ++ z :: lb ++ z :: lc.
Proof.
intros l z. induction l as [|y l IH]; intros H; cbn in H; [lia|].
destruct (crt102rw_zz_dec y z) as [<-|Hne].
- assert (H1 : (1 <= count_occ crt102rw_zz_dec l y)%nat) by lia.
  apply count_occ_In in H1. apply in_split in H1 as (lb & lc & ->). exists [], lb, lc. reflexivity.
- destruct (IH H) as (la & lb & lc & ->). exists (y :: la), lb, lc. reflexivity.
Qed.
Lemma crt102rw_fresh : forall lyc Sc Hpc Wc memc mdc Dx a k,
  ARx lyc Sc Hpc Wc memc mdc -> Permutation (ablocks B lyc Sc) (ablocks B ly S ++ ck_hblks Dx) -> In (a, k) Dx ->
  0 <= k ->
  In (a - cf_head, k + cf_head) (ablocks B lyc Sc) /\ ~ In (a - cf_head, k + cf_head) (ablocks B ly S).
Proof.
intros lyc Sc Hpc Wc memc mdc Dx a k HAR HP Hin Hk.
assert (Hh : In (a - cf_head, k + cf_head) (ck_hblks Dx)) by (unfold ck_hblks; apply (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Dx (a, k)); exact Hin).
split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hh|].
intros H0. pose proof (proj1 (Permutation_count_occ crt102rw_zz_dec _ _) HP (a - cf_head, k + cf_head)) as Hc.
rewrite count_occ_app in Hc.
pose proof (proj1 (count_occ_In crt102rw_zz_dec _ _) H0).
pose proof (proj1 (count_occ_In crt102rw_zz_dec _ _) Hh).
destruct (crt102rw_count2 (ablocks B lyc Sc) (a - cf_head, k + cf_head) ltac:(lia)) as (la & lb & lc & El).
destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HAR) as (Hsep & _). rewrite El in Hsep.
apply pairwise_app_l in Hsep as [Hsep _]. rewrite map_app in Hsep. apply pairwise_app_l in Hsep as [_ Hsep].
cbn [map pairwise] in Hsep. destruct Hsep as (Hf & _). rewrite map_app, Forall_app in Hf. destruct Hf as (_ & Hf).
cbn [map] in Hf. inversion Hf as [|? ? Hd _]. unfold zdisjoint in Hd. cbv beta in Hd. cbn [fst snd] in Hd.
assert (Hk16 : 0 <= k + cf_head) by (pose proof (@cf_head_nonneg CfParams_preset); lia).
pose proof (req_size_pos (k + cf_head) Hk16) as Hrs. change (@cf_head CfParams_preset) with 16 in *. lia.
Qed.


(* ---- the head of the blocks held is not among the rest (its allocator block would occur twice: the sep law) ---- *)
Lemma crt102rw_dx_head_fresh : forall lyc Sc Hpc Wc memc mdc xb Dr,
  ARx lyc Sc Hpc Wc memc mdc -> Permutation (ablocks B lyc Sc) (ablocks B ly S ++ ck_hblks (xb :: Dr)) -> 0 <= snd xb ->
  ~ In xb Dr.
Proof.
intros lyc Sc Hpc Wc memc mdc xb Dr HAR HP Hk Hin.
set (h := (fst xb - cf_head, snd xb + cf_head)).
assert (Hh2 : (2 <= count_occ crt102rw_zz_dec (ck_hblks (xb :: Dr)) h)%nat).
{ cbn [ck_hblks map]. unfold ck_hblks in *. cbn [count_occ]. fold h.
  destruct (crt102rw_zz_dec h h) as [_|C]; [|exfalso; exact (C eq_refl)].
  assert (Hm : In h (map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Dr))
    by (apply (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Dr xb); exact Hin).
  pose proof (proj1 (count_occ_In crt102rw_zz_dec _ _) Hm). lia. }
pose proof (proj1 (Permutation_count_occ crt102rw_zz_dec _ _) HP h) as Hc. rewrite count_occ_app in Hc.
destruct (crt102rw_count2 (ablocks B lyc Sc) h ltac:(lia)) as (la & lb & lc & El).
destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HAR) as (Hsep & _). rewrite El in Hsep.
apply pairwise_app_l in Hsep as [Hsep _]. rewrite map_app in Hsep. apply pairwise_app_l in Hsep as [_ Hsep].
cbn [map pairwise] in Hsep. destruct Hsep as (Hf & _). rewrite map_app, Forall_app in Hf. destruct Hf as (_ & Hf).
cbn [map] in Hf. inversion Hf as [|? ? Hd _]. unfold zdisjoint in Hd. cbv beta in Hd. unfold h in Hd. cbn [fst snd] in Hd.
change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (snd xb + 16) ltac:(lia)). lia.
Qed.


(* ---- the ledger over a memory that agrees with it everywhere ---- *)
Lemma crt102rw_ledger_agree : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 mem2' L pk cn fl rn mo ow,
  prh_ledger B ly2 S2 Hp2 W2 mem2 L pk cn fl rn mo ow ->
  (forall xw, mrestrict (w_H W2) mem2' xw = mrestrict (w_H W2) mem2 xw) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2' L pk cn fl rn mo ow.
Proof.
intros ly2 S2 Hp2 W2 mem2 mem2' L pk cn fl rn mo ow HL Hm.
apply (S1Ledger.prh_ledger_kept_aview B ly2 S2 Hp2 W2 mem2 ly2 S2 Hp2 W2 mem2' L pk cn fl rn mo ow HL).
- intros a _. apply aview_eq_of. apply Hm.
- intros a k i _ _. apply aview_eq_of. apply Hm.
- intros a k _ Hab. exact Hab.
- apply Permutation_refl.
Qed.

(* ---- a call footprint over the hulls of blocks Dt: each byte is in one block's allocator window ---- *)
Lemma crt102rw_fp_hull : forall Dt a0, inFP (ablocks_fp (PRH_FnPj.prhPj_hbl Dt)) a0 ->
  exists bb kb, In (bb, kb) Dt /\ bb - cf_head <= a0 < bb - cf_head + req_size (kb + cf_head).
Proof.
intros Dt a0 ((b & e) & Hb & Hab). unfold ablocks_fp, PRH_FnPj.prhPj_hbl in Hb.
rewrite map_map, in_map_iff in Hb. destruct Hb as ((bb & kb) & Eb & Hbb). cbn [fst snd] in Eb. injection Eb as <- <-.
exists bb, kb. split; [exact Hbb|]. try unfold in_zr in Hab. cbn [fst snd] in Hab.
assert (Eh : @cf_head CfParams_preset = 16) by reflexivity. rewrite Eh. lia.
Qed.

(* ---- the blocks held, after a call whose post is in the pj texts' block form ---- *)
Lemma crt102rw_blocks_step : forall lyc Sc ly2 S2 Lamc Lam2 Dx D1 Do Lr other,
  Permutation Lamc (Dx ++ Lam) -> Permutation (ablocks B lyc Sc) (ablocks B ly S ++ ck_hblks Dx) ->
  Permutation Dx D1 -> Permutation Lamc (D1 ++ Lr) -> Permutation Lam2 (Do ++ Lr) ->
  Permutation (ablocks B lyc Sc) (PRH_FnPj.prhPj_hbl Lamc ++ other) ->
  Permutation (ablocks B ly2 S2) (PRH_FnPj.prhPj_hbl Lam2 ++ other) ->
  Permutation Lam2 (Do ++ Lam) /\ Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Do).
Proof.
intros lyc Sc ly2 S2 Lamc Lam2 Dx D1 Do Lr other HPL HPB HD1 HPLr HPLo Ho1 Ho2.
assert (ELr : Permutation Lr Lam).
{ apply (Permutation_app_inv_l D1). apply (Permutation_trans (Permutation_sym HPLr)).
  apply (Permutation_trans HPL). apply Permutation_app_tail. exact HD1. }
split; [apply (Permutation_trans HPLo); apply Permutation_app_head; exact ELr|].
unfold ck_hblks, PRH_FnPj.prhPj_hbl in *.
set (f := fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) in *.
assert (E1 : Permutation (ablocks B ly S) (map f Lam ++ other)).
{ apply (Permutation_app_inv_l (map f Dx)).
  apply (Permutation_trans (Permutation_app_comm _ _)). apply (Permutation_trans (Permutation_sym HPB)).
  apply (Permutation_trans Ho1). rewrite app_assoc, <- map_app. apply Permutation_app_tail. apply Permutation_map. exact HPL. }
apply (Permutation_trans Ho2).
apply (Permutation_trans (Permutation_app_tail other (Permutation_map f (Permutation_trans HPLo (Permutation_app_head Do ELr))))).
rewrite map_app, <- app_assoc.
apply (Permutation_trans (Permutation_app_head (map f Do) (Permutation_sym E1))).
apply Permutation_app_comm.
Qed.

(* ---- the blocks held after a call are apart from the document's: old ones by crt_live, new ones were not live ---- *)
Lemma crt102rw_apart_step : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc Do {kbg : nat},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (forall a' k', In (a', k') Do -> In (a', k') Dx \/ ~ In (a' - cf_head, k' + cf_head) (ablocks B lyc Sc)) ->
  forall bk, In bk Do -> ~ In bk D.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc Do kbg HL HDo (a' & k') Hb HinD.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof (crt_side_doc_blocks (crt_live_side HL)) as HDL.
pose proof (crt_live_dx_apart HL) as HAP.
destruct (HDo a' k' Hb) as [Hx | Hn]; [exact (HAP _ Hx HinD)|].
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a' k' _ _ HLED (HDL _ HinD)) as (_ & Hab & _).
exact (Hn Hab).
Qed.

(* ---- a held block's allocator window is off the document's footprint ---- *)
Lemma crt102rw_hull_off_doc : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc bb kb y {kbg : nat},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> In (bb, kb) Dx ->
  bb - cf_head <= y < bb - cf_head + req_size (kb + cf_head) -> ~ pj_footR doc D y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc bb kb y kbg HL Hb Hy.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof (crt_side_doc_blocks (crt_live_side HL)) as HDL.
pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_live_dx_apart HL) as HAP.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HPRE as ((HAR & _) & _).
pose proof HTREE as (_ & _ & _ & _ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR HLYc) as (_ & Efa & _).
assert (HbL : In (bb, kb) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc bb kb _ _ HLED HbL) as (Hk0 & Hab & _).
intros [Hf | ((b & kb2) & Hb2 & Hf)].
- assert (Hfin' : In (cid, pos') (frames Sc)) by (rewrite HFRc; apply in_or_app; right; exact Hfin).
  pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ cid pos' HARc Hab Hfin') as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (Efa cid pos') in Hd. lia.
- destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb2 _ _ HLED (HDL _ Hb2)) as (Hk2 & Hab2 & _).
  assert (Hne : (bb - cf_head, kb + cf_head) <> (b - cf_head, kb2 + cf_head)).
  { intros E. injection E as E1 E2. assert (bb = b) by lia. assert (kb = kb2) by lia. subst.
    exact (HAP _ Hb Hb2). }
  pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hab Hab2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold pj_holdsR in Hf. cbn [fst snd] in Hf.
  change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb2 + 16) ltac:(lia)). lia.
Qed.

(* ---- an image byte is off a tree rooted in check_round_trip's frame whose blocks are harness blocks ---- *)
Lemma crt102rw_img_off_foot : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off Dt y {kbg : nat},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (forall bk, In bk Dt -> In bk Lamc) -> 0 <= off -> off + 56 <= 512 -> in_img SEGS y ->
  ~ pj_footR (frame_addr lyc CRT_CID pos + off) Dt y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off Dt y kbg HL HDt Ho0 Ho1 Hi
  [Hf | ((b & kb) & Hb & Hf)].
- destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof HJ as (HARc & _).
  destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & _).
  assert (Hy : frame_addr lyc CRT_CID pos <= y < frame_addr lyc CRT_CID pos + fs_frame_bytes CRT_CID)
    by (rewrite crt102rw_fb; lia).
  apply (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
    (or_intror (or_introl (ex_intro _ CRT_CID (ex_intro _ pos (conj Hin Hy))))))).
  exact Hi.
- destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
  pose proof HJ as (HARc & _).
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDt _ Hb)) as (Hk0 & Hab & _).
  unfold pj_holdsR in Hf. cbn [fst snd] in Hf.
  assert (Hy : b - cf_head <= y < b - cf_head + req_size (kb + cf_head)).
  { change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb + 16) ltac:(lia)). lia. }
  apply (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
    (or_introl (ex_intro _ (b - cf_head) (ex_intro _ (kb + cf_head) (conj Hab Hy)))))).
  exact Hi.
Qed.

(* ---- a header read twice gives one capacity ---- *)
Lemma crt102rw_hdr_cap_det : forall m p ty num str kids keys n cap ty' num' str' kids' keys' n' cap',
  pj_hdrR SEGS m p ty num str kids keys n cap -> pj_hdrR SEGS m p ty' num' str' kids' keys' n' cap' -> cap = cap'.
Proof.
intros m p ty num str kids keys n cap ty' num' str' kids' keys' n' cap' (_ & _ & _ & _ & _ & _ & _ & H1)
  (_ & _ & _ & _ & _ & _ & _ & H2).
exact (cm_rd_u64_det SEGS m (p + 48) cap cap' H1 H2).
Qed.

(* ---- a header in a frame of Sc, off a callee's footprint, survives the call (the journal keeps frame bytes) ---- *)
Lemma crt102rw_hdr_call : forall lyc Sc Hpc Wc memc mdc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 p ty num str kids keys n cap,
  ARx lyc Sc Hpc Wc memc mdc ->
  AJ STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= p /\
     p + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) ->
  (forall a, inFP FP1 a -> ~ (p <= a < p + 56)) ->
  pj_hdrR SEGS (mrestrict (w_H Wc) memc) p ty num str kids keys n cap ->
  pj_hdrR SEGS (mrestrict (w_H W2) mem2) p ty num str kids keys n cap.
Proof.
intros lyc Sc Hpc Wc memc mdc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 p ty num str kids keys n cap HARc HJ1
  (cid & pos' & Hfin & Hfa1 & Hfa2) HFP Hh.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
apply (pj_hdrR_frame SEGS _ _ p ty num str kids keys n cap Hh).
apply crt102rw_agree_of_aview. intros y Hy.
assert (Hyf : frame_addr lyc cid pos' <= y < frame_addr lyc cid pos' + fs_frame_bytes cid) by lia.
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc Hfin) as (? & ? & _).
pose proof (YM05.alloc_ceiling_val).
split; [lia|].
split; [exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
          (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos' (conj Hfin Hyf)))))))|].
apply (G4 cid pos' y Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros Hf; exact (HFP y Hf Hy)].
Qed.

(* ---- AN ORDERED FREE LIST ACROSS A CALL (Crt102Kit.crt102rw_tree_call for PRH_PjOrder.pj_foR; the same proof as
   Crt102Loops.cl_fo_call): a node in a fake frame of Sc whose blocks are harness blocks before and after, off the
   callee's footprint, keeps its order list (the journal keeps frame bytes and live blocks off FP) ---- *)
Lemma crt102rw_fo_call : forall lyc Sc Hpc Wc memc mdc (kj : Z) STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p d Dt Ft {WS1 : list (list Z)},
  ARx lyc Sc Hpc Wc memc mdc ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  forall {mo1 ow1 mo2 ow2 : Z},
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc mo1 ow1 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 mo2 ow2 ->
  (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= p /\
     p + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) ->
  (forall bk, In bk Dt -> In bk Lamc) -> (forall bk, In bk Dt -> In bk Lam2) ->
  (forall a, inFP FP1 a -> ~ pj_footR p Dt a) ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) d p Dt Ft ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) d p Dt Ft.
Proof.
intros lyc Sc Hpc Wc memc mdc kj STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p d Dt Ft
  WS1 HARc HJ1 mo1 ow1 mo2 ow2 HLc HLED2 (cid & pos' & Hfin' & Hfa1 & Hfa2) HDL HDL2 HFPd HND.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _).
apply (PRH_PjOrder.pj_foR_frame SEGS d (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) (prh_lin Lam2)
  p Dt Ft HND); [intros x0 k0 H0; exact (HDL2 _ H0)|].
apply crt102rw_agree_of_aview. intros y Hy.
assert (HnFP : ~ inFP FP1 y) by (intros Hf; exact (HFPd y Hf Hy)).
assert (Hyc : (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
                 frame_addr lyc cid0 pos0 <= y < frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) \/
              (exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ In (p0, n0) (ablocks B ly2 S2) /\
                 p0 <= y < p0 + req_size n0)).
{ destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
  - left. exists cid, pos'. split; [exact Hfin'|]. lia.
  - right. unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
    destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLc (HDL _ Hb)) as (Hk0 & Hab & _).
    destruct (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 b kb _ _ HLED2 (HDL2 _ Hb)) as (_ & Hab2 & _).
    exists (b - cf_head), (kb + cf_head). split; [exact Hab|]. split; [exact Hab2|].
    change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb + 16) ltac:(lia)). lia. }
assert (Himg : ~ in_img SEGS y).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_intror (or_introl (ex_intro _ cid0 (ex_intro _ pos0 (conj Hin0 Hy0))))))).
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_introl (ex_intro _ p0 (ex_intro _ n0 (conj Hab Hy0)))))). }
assert (Hyr : 0 <= y < 2 ^ 64).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid0 pos0 HARc Hin0) as (? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia.
  - destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & ? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia. }
split; [exact Hyr|]. split; [exact Himg|].
destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & Hab2 & Hy0)].
- apply (G4 cid0 pos0 y Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnFP].
- replace y with (p0 + (y - p0)) by lia. apply (G2 p0 n0 (y - p0) Hab Hab2); [lia|]. replace (p0 + (y - p0)) with y by lia.
  exact HnFP.
Qed.

(* ---- G (+0x250): pj_string has returned. The state both arms share: the live state with v's 56 bytes as pj_string
   left them, the frame registers, s6 = v, s8 = shadow (&doc->n), the two spills, the two open locals, copy's tree, and
   (last) copy's ORDERED free list, carried from crt_at_U_copy_fo: the landing cut's tpj_set_specX takes it as its
   ordered entry premise (PRH_FnPj.v:1002-1004) ---- *)
Definition crt102rw_Gst (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Db Dx Lamc : list (Z * Z)) (peakc cntc ranc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveA (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 ranc /\
  dregsA rg (frame_addr lyc CRT_CID pos) /\
  getr rg 22 = w64 (frame_addr lyc CRT_CID pos + CRT_OFF_V) /\ getr rg 24 = w64 (shadow_addr (doc + PJ_OFF_N)) /\
  t = PjTree.JObj ms /\
  crt_spill (regs := regs) Wc memc CRT_SP_PN (doc + PJ_OFF_N) /\
  crt_spill (regs := regs) Wc memc CRT_SP_N (Z.of_nat (length ms)) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  crt_copy_tree (rc := rc) (L := A_prog_listing) (PA := PA) Wc memc Lamc (frame_addr lyc CRT_CID pos) t Db /\
  Permutation (map (fun b => snd b + cf_head) Db) (PresetReqAtNoMiss.tblk t) /\
  (* CAP: copy's header capacity is the parsed object's (crt_at_U's header-cap conjunct, produced by Crt102Arms) *)
  (exists num str kids keys n, pj_hdrR SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) 6
     num str kids keys n (Z.of_nat (PresetReqAt.ncap (length ms)))) /\
  (forall a' k, In (a', k) Db -> ~ In (a' - cf_head, k + cf_head) (ablocks B ly S)) /\
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
  Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
  cntc = ck_cnt2 cnt t + 1 /\
  (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
     exists F0, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) nn
       (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db F0 /\
     map (fun b => snd b + cf_head) F0 = PresetReqAt.fo (PjTree.JObj ms)).

(* the refused arm: a0 = -1, v zeroed with type 4, its strdup refused under the request bound so g_ran_out = 1 *)
(* ---- O1 (+0x280), the first out_of_memory (): reached from G's refused arm (s8 = 0) and from K (s8 = seqz res).
   The state: the live state (own = 0: no text this slice crosses writes g_own_ran_out), the frame registers, s8 = the
   set flag, the two open locals, copy freeable at DOC_D over the blocks held, the count with pj_set's charge, and
   the request bound's consequence `ranc = 0 -> set = 1`. GO is what the go branch (ranc = 0) needs beyond it. ---- *)
Definition crt102rw_O1st (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dx Lamc : list (Z * Z)) (peakc cntc ranc : Z)
  (rg : bvmap 5 word) (sv : Z) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveA (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 ranc /\
  dregsA rg (frame_addr lyc CRT_CID pos) /\ getr rg 24 = w64 sv /\ (sv = 0 \/ sv = 1) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dx /\
  (exists cset, 0 <= cset <= 3 /\ (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst ms) -> cset = 0) /\
     cnt <= cntc <= cnt + ck_crt_count t cset) /\
  (ranc = 0 -> sv = 1).

(* the own flag's cell: O1's `auipc s9; lbu a0, -0x5b0(s9)` is the listing's PHi / PLdHi pair on listing object
   A_OBJ 13 (Listing_prog.v slots 1348-1349), whose value is PRH_Img's pi_g_own_ran_out (A' 0x5dd540, checked against
   the twin's symtab and by decoding the pair: 0x82af0 + 0x55b000 - 0x5b0) *)
Lemma crt102rw_own_cell : VAL (A_OBJ 13) = pi_g_own_ran_out /\ (A_TEXT <= A_OBJ 13 < A_LIM)%nat /\
  pi_gz_own_ran_out = 1%nat /\ 0 <= VAL (A_OBJ 13) < 2 ^ 64.
Proof.
split; [vm_compute; reflexivity|].
split; [split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity|].
split; [vm_compute; reflexivity | split; [vm_compute; intros H; discriminate H | vm_compute; reflexivity]].
Qed.

Definition crt102rw_ssO1 : sstate := mkSS (CRT_PC_A + CRT_O1_OFF) cur_atoms
  [ YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ] None
  (mkFacts [] [] []).
Lemma crt102rw_O1_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg,
  prh_own Wc memc 0 ->
  @st_ok_pi SEGS VAL fxk (TE regs rg []) crt102rw_ssO1
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_O1_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg (Hv & _).
pose proof crt102rw_own_cell as (Ec & Hi & Ez & V13).
set (E := TE regs rg []).
assert (X13 : bv_unsigned (ew E (A_OBJ 13)) = VAL (A_OBJ 13)).
{ unfold E. rewrite te_img by exact Hi. apply unsigned_lit_small. lia. }
split; [|unfold sh_ok; apply Forall_nil].
apply (@ts_st_ok fxk).
all: try change (TE regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (A_OBJ 13) (VAL (A_OBJ 13))); [exact X13 | lia | lia | intros o Ho; cbn in Ho; lia |].
  constructor; [|constructor].
  apply (ts_chunk E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
  rewrite Ez in Hv. rewrite Z.add_0_r, Ec. exact Hv.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

(* fuzz_alloc_ran_out's return site in check_round_trip (+0x294; DERIVED: 4 * the slot inside the function) *)
Definition crt102rw_O1R_OFF : Z := 660.

(* the go branch's continuation, at fuzz_alloc_ran_out's return (+0x294) with a0 = 0: the state the O1 run and the
   call leave, related to O1's entry by the run's (no write) agreement and the call's journal (empty footprint, the
   allocator state unchanged), so a caller that knows more of O1's entry state can carry it over *)
Definition crt102rw_O1go (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (kj pos : Z) (Dx Lamc : list (Z * Z)) (peakc cntc : Z) : Prop :=
  forall (fx' : YK11.FPState) ly2 W2 mem2 md2 k1 regs2 memm mdm,
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' ->
  liveA (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat ly2 Sc Hpc W2 mem2 md2 (kj + k1) pos Dx Lamc peakc cntc 0 0 ->
  dregsA regs2 (frame_addr lyc CRT_CID pos) -> getr regs2 22 = w64 1 -> getr regs2 24 = w64 1 ->
  getr regs2 10 = w64 0 -> getr regs2 25 = w64 (VAL 315) -> frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos ->
  (forall xw, mrestrict (w_H Wc) memm xw = mrestrict (w_H Wc) memc xw) -> ARx lyc Sc Hpc Wc memm mdm ->
  AJ (@STK_fuzz_alloc_ran_out prh_img_A) sp1 [] lyc Sc Hpc Wc memm mdm [] ly2 Sc Hpc W2 mem2 md2 k1 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 ->
  pj_fdR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dx ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfgA fx' crt102rw_O1R_OFF regs2 mem2 md2) QFa.

Lemma crt102rw_O1 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ranc rg sv,
  crt102rw_O1st fxk lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ranc rg sv ->
  (* g_ran_out is clear here: the refusals that could set it (pj_string's, pj_set's) are dead at their sources
     (refuted in crt102rw_at_U / crt102rw_G_taken), so ARM C4a (out_of_memory () = 1 at +0x29c / +0x290) is unreachable
     from this state: g_own_ran_out = 0 (no crossed text writes it) and g_ran_out = 0 *)
  ranc = 0 ->
  (ranc = 0 -> crt102rw_O1go fxk lyc Sc Hpc Wc memc kj pos Dx Lamc peakc cntc) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_O1_OFF rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ranc rg sv
  (HFZ & HFK & HL & HDR & R24 & Hsv & HRAb & HRAv & HFD & HCNT & Hset) Eran0 HGO.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_sp (crt_dregs_bregs HDR)) as R2.
pose proof (crt_bregs_gp (crt_dregs_bregs HDR)) as R3.
pose proof (crt_bregs_tp (crt_dregs_bregs HDR)) as R4.
pose proof (crt_bregs_s0 (crt_dregs_bregs HDR)) as R8.
pose proof (crt_bregs_s1 (crt_dregs_bregs HDR)) as R9.
pose proof (crt_bregs_s2 (crt_dregs_bregs HDR)) as R18.
pose proof (crt_bregs_s4 (crt_dregs_bregs HDR)) as R20.
pose proof (crt_bregs_s3 (crt_dregs_bregs HDR)) as R19.
pose proof (crt_bregs_s7 (crt_dregs_bregs HDR)) as R23.
pose proof (crt_bregs_s10 (crt_dregs_bregs HDR)) as R26.
pose proof (crt_bregs_s11 (crt_dregs_bregs HDR)) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt102rw_sp HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof crt102rw_stkc as ESTK.
pose proof (YM05.alloc_ceiling_val) as Hcv.
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (crt102rw_O1_entry fxk Wc memc rg ltac:(eapply PRH_Base.prh_ledger_own; exact HLED)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
pose proof HMNc as HPM.
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
pose (BR := @YSRrG.paj_branchR fxk rc A_prog_listing PA RZW).
unfold crt_cfg.
paj_run_tok_x_inv (RUN WS_HJ) HS HJ SHOK HPM (0, 0).
{ cbv [crt102rw_ssO1 ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (Hm0 : forall xw, mrestrict (w_H Wc) (ms_mem ms) xw = mrestrict (w_H Wc) memc xw).
{ intros xw. apply HFr. intros (r & Hr & Ha). cbv [crt102rw_ssO1 ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ pos Dx Lamc peakc cntc 0 ranc HL HJ HB_HJ
  (fun xw _ => Hm0 xw) HPM) as HL1.
assert (KR1 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26; 27]%bv -> getr (ms_regs ms) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
prreg HS (1%bv : bv 5) Q1. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
assert (X25 : getr (ms_regs ms) 25 = w64 (VAL 315)).
{ rewrite Q25. apply te_img. split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity. }
assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + crt102rw_O1R_OFF))) by (rewrite Q1; vm_compute; reflexivity).
assert (X22 : getr (ms_regs ms) 22 = w64 1) by (rewrite Q22; reflexivity).
assert (HBR1 : bregsA (ms_regs ms) F).
{ refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
            crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
            crt_bregs_s11 := _ |}; rewrite !KR1 by (cbv; tauto); assumption. }
assert (HE2 : bv_unsigned (ew (TE regs rg []) 2) = sp0) by (rewrite (te_entry regs rg [] 2%bv 2) by reflexivity; reflexivity).
assert (HSTKr : @STK_fuzz_alloc_ran_out prh_img_A = 0) by (vm_compute; reflexivity).
destruct (crt_live_journal HL1) as (WS_HJ1 & HJ1 & HB_HJ1). pose proof (crt_live_side HL1) as HSD1.
pose proof (crt_live_lam_perm HL1) as HPL1. pose proof (crt_live_blocks_perm HL1) as HPB1.
pose proof (crt_live_dx_apart HL1) as HAP1.
pose proof (crt_side_ledger HSD1) as HLED1. pose proof (crt_side_peak HSD1) as Hpk1.
pose proof (crt_side_room HSD1) as HROOM1. pose proof (crt_side_arodata HSD1) as HRO1.
pose proof (crt_side_doc HSD1) as HND1. pose proof (crt_side_doc_blocks HSD1) as HDL1.
clear HF HG HFr.
refine (crt102rw_call LAWS HPRE fxk (@STK_fuzz_alloc_ran_out prh_img_A) [] crt102rw_O1R_OFF (SIGMA AS_fuzz_alloc_ran_out) Wc
  (TE regs rg []) _ ms _ lyc Sc Hpc kj pos Dx Lamc peakc cntc 0 ranc _ HFZ HS eq_refl eq_refl HE2 HL1 HBR1 X1 _ _ _ _ _ _ _).
- unfold crt102rw_O1R_OFF. lia.
- reflexivity.
- lia.
- lia.
- intros a Hfa. exfalso. exact (inFP_nil a Hfa).
- (* the callee: fuzz_alloc_ran_out's text *)
  intros ch1 HPRE1. apply (crt102rw_lift_x fxk); [exact HFZ|]. eapply SRr_mono.
  + exact (RANOUT fxk lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 Lamc peakc cntc SIZE_MAXZ ranc most 0 HPRE1 HLED1).
  + intros W' c' _ HPo. exact HPo.
- (* the return at +0x294 *)
  intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP
    ((Hroomk & Ra0 & EHp & ES & Eab & HLED2) & HMNk).
  pose proof (Hroomk HROOM1) as HROOM2.
  assert (HFK3 : fregs_kept_x fx fx') by (intros r0 Hr0; rewrite (HFK2 r0 Hr0); exact (HFK r0 Hr0)).
  subst S2 Hp2.
  pose proof (crt102rw_side_call LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dx Lamc peakc cntc 0 ranc _ _
    ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc cntc 0 ranc HL1 HJc (Forall_nil _) (fun a Hf => False_ind _ (inFP_nil a Hf))
    HLED2 ltac:(lia) HROOM2 HDL1) as HSD2.
  assert (HPB2 : Permutation (ablocks B ly2 Sc) (ablocks B ly S ++ ck_hblks Dx)) by (rewrite Eab; exact HPB1).
  pose proof (crt102rw_live_call LAWS HPRE lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dx Lamc peakc cntc 0 ranc _ _
    ly2 Sc Hpc W2 mem2 md2 k1 Dx Lamc peakc cntc 0 ranc HL1 HJe HJc ltac:(lia)
    (fun a Hf => False_ind _ (inFP_nil a Hf)) HSD2 HPL1 HPB2 HAP1 HMNk) as HL2.
  destruct (crt102rw_call_keep LAWS HPRE lyc Sc Hpc Wc (ms_mem ms) _ kj pos _ _ ly2 Sc Hpc W2 mem2 md2 k1 HJ1 HJc
    (fun a Hf => False_ind _ (inFP_nil a Hf))) as (EF2 & KS2 & KSH2).
  fold F in EF2, KSH2.
  assert (HBR2 : bregsA regs2 F).
  { pose proof (crt_bregs_sp HBR1) as Q2'. pose proof (crt_bregs_gp HBR1) as Q3'.
    pose proof (crt_bregs_tp HBR1) as Q4'. pose proof (crt_bregs_s0 HBR1) as Q8'.
    pose proof (crt_bregs_s1 HBR1) as Q9'. pose proof (crt_bregs_s2 HBR1) as Q18'.
    pose proof (crt_bregs_s4 HBR1) as Q20'. pose proof (crt_bregs_s3 HBR1) as Q19'.
    pose proof (crt_bregs_s7 HBR1) as Q23'. pose proof (crt_bregs_s10 HBR1) as Q26'.
    pose proof (crt_bregs_s11 HBR1) as Q27'.
    refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
              crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
              crt_bregs_s11 := _ |};
    [ rewrite (ts_ap (ms_regs ms) regs2 2%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 3%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 4%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 8%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 9%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 18%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 20%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 19%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 23%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 26%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms) regs2 27%bv HP) by ts_cs ];
    assumption. }
  assert (X22' : getr regs2 22 = w64 1) by (rewrite (ts_ap (ms_regs ms) regs2 22%bv HP) by ts_cs; exact X22).
  assert (HAGm : forall X, pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) X).
  { intros X y _. assert (E : mrestrict (w_H Wc) (ms_mem ms) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y))
      by apply Hm0.
    split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
  assert (HDx : forall bk, In bk Dx -> In bk Lamc).
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL1)). apply in_or_app. left. exact Hbk. }
  assert (HcF : exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= F + CRT_OFF_COPY /\
    F + CRT_OFF_COPY + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0).
  { exists CRT_CID, pos. split; [exact Hin|]. rewrite crt102rw_fb. fold F. unfold CRT_OFF_COPY. lia. }
  pose proof (crt102rw_fd_call LAWS lyc Sc Hpc Wc (ms_mem ms) _ kj _ _ ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc cntc ranc
    Lamc peakc cntc ranc (F + CRT_OFF_COPY) DOC_D Dx (proj1 HJ1) HJc HLED1 HLED2 HcF HDx HDx
    (fun a Hf => False_ind _ (inFP_nil a Hf))
    (crt102rw_fdR_frame SEGS DOC_D _ _ (prh_lin Lamc) _ Dx HFD (HAGm _))) as HFD2.
  assert (HRA0 : forall off, range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + off) 56 ->
    range_addressable (aview SEGS (w_H Wc) (ms_mem ms)) SHADOW_OFF (F + off) 56).
  { intros off H. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact H].
    intros y _. apply aview_eq_of. apply Hm0. }
  destruct (crt102rw_local_keep Wc W2 (ms_mem ms) mem2 F CRT_OFF_BACK ltac:(lia) F32 Fb2 KSH2
    ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) as (LB1 & _).
  destruct (crt102rw_local_keep Wc W2 (ms_mem ms) mem2 F CRT_OFF_V ltac:(lia) F32 Fb2 KSH2
    ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)) as (LV1 & _).
  pose proof (LB1 (HRA0 _ HRAb)) as HRAb2. pose proof (LV1 (HRA0 _ HRAv)) as HRAv2.
  pose proof (prh_ledger_bounds B ly2 Sc Hpc W2 mem2 Lamc peakc cntc SIZE_MAXZ ranc _ _ HLED2) as (_ & _ & _ & _ & Hran01).
  destruct (crt_live_journal HL2) as (WS_HJ2 & HJ2 & HB_HJ2). pose proof (crt_live_memnorm HL2) as HPM2.
  pose (RUNTO2 := @paj_run_to_x_inv fx' rc SK A_prog_listing PL PA B PST ARx _ LAWS
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
    (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
  destruct Hran01 as [Er0 | Er1].
  + (* ran = 0: out_of_memory () = 0 (own was 0), the go branch; the request bound gave set = 1 *)
    subst ranc. pose proof (Hset eq_refl) as Esv. subst sv.
    assert (X24' : getr regs2 24 = w64 1).
    { rewrite (ts_ap (ms_regs ms) regs2 24%bv HP) by ts_cs. rewrite (KR1 24%bv) by (cbv; tauto). exact R24. }
    assert (X25' : getr regs2 25 = w64 (VAL 315)) by (rewrite (ts_ap (ms_regs ms) regs2 25%bv HP) by ts_cs; exact X25).
    assert (HDR2 : dregsA regs2 F).
    { refine {| crt_dregs_bregs := HBR2; crt_dregs_s5 := _ |}.
      rewrite (ts_ap (ms_regs ms) regs2 21%bv HP) by ts_cs. rewrite (KR1 21%bv) by (cbv; tauto).
      exact R21. }
    exact (HGO eq_refl fx' ly2 W2 mem2 md2 k1 regs2 (ms_mem ms) _ HFZ2 HFK3 HL2 HDR2 X22' X24' Ra0 X25' EF2 Hm0 (proj1 HJ1) HJc
      HRAb2 HRAv2 HFD2).
  + (* ran = 1 is not this state (Eran0) *)
    exfalso. lia.
Qed.

(* ---- tree_vis of harness blocks (Crt102Arms.v crt_tree_vis_keep, commit e731fa2c71f, VERBATIM
   but for the name: the walk base's Crt102Arms.v blob is at the old ledger arity and does not build here) ---- *)
Lemma crt102rw_tree_vis_keep : forall lyt St Hpt Wt memt mdt Lamc peakc cntc failc ranc mostc ownc Dt,
  ARx lyt St Hpt Wt memt mdt -> prh_ledger B lyt St Hpt Wt memt Lamc peakc cntc failc ranc mostc ownc ->
  (forall bk, In bk Dt -> In bk Lamc) ->
  (forall a k, In (a, k) Dt -> 4096 <= a /\ 0 <= k < 2 ^ 32 /\ (a + k + 7) / 8 * 8 <= YM05.alloc_ceiling /\
     amem_range a ((a + k + 7) / 8 * 8 - a)) ->
  PRH_FnWriter.prhWriter_tree_vis Wt memt Dt.
Proof.
intros lyt St Hpt Wt memt mdt Lamc peakc cntc failc ranc mostc ownc Dt HAR HL HDt HP a k Hin.
destruct (HP a k Hin) as (H4096 & Hk & Hceil & Hamr).
pose proof (proj1 (Forall_forall _ _)
  (prh_ledger_blocks B lyt St Hpt Wt memt Lamc peakc cntc failc ranc mostc ownc HL) (a, k) (HDt _ Hin))
  as (Hk0 & Hab & Hhp & H16 & _).
cbn [fst snd] in Hk0, Hab, Hhp, H16.
assert (Hh0 : @cf_head CfParams_preset = 16) by reflexivity.
destruct (alx_blocks SEGS B ARx LAWS lyt St Hpt Wt memt mdt _ _ HAR Hab) as (_ & _ & _ & _ & Hpres & _).
assert (Hrq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (alx_hshadow SEGS B ARx LAWS lyt St Hpt Wt memt mdt _ _ HAR Hab Hhp) as [Hbs Hhull].
rewrite Hrq in Hbs, Hhull, Hpres. replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia.
replace (k + cf_head - cf_head) with k in Hbs, Hhull by lia.
split; [exact H4096|]. split; [exact Hk|]. split; [exact Hceil|]. split; [exact Hamr|].
split; [exact (block_shadow_range (aview SEGS (w_H Wt) memt) SHADOW_OFF a k a k Hbs ltac:(lia) ltac:(lia))|].
split; [intros Hkp; apply Hhull; lia|].
intros xt Hx. destruct (Z_lt_le_dec xt (a + k)) as [Hlt|Hge].
- destruct (proj1 (Hpres xt ltac:(lia))) as (Hh & bb & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
- apply (alx_blocks_tail SEGS B ARx LAWS lyt St Hpt Wt memt mdt _ _ xt HAR Hab). rewrite Hrq.
  replace (a - cf_head + (k + cf_head)) with (a + k) by lia. lia.
Qed.

(* ---- a harness block below 2 ^ 32 bytes meets tree_vis's per-block premises (alx_blocks: 16-aligned, below the
   ceiling, application memory; the ceiling is page-aligned, so the rounded end stays below it) ---- *)
Lemma crt102rw_blk_vis : forall lyt St Hpt Wt memt mdt Lt pk cn fl rn mo ow a k,
  ARx lyt St Hpt Wt memt mdt -> prh_ledger B lyt St Hpt Wt memt Lt pk cn fl rn mo ow -> In (a, k) Lt -> k < 2 ^ 32 ->
  4096 <= a /\ 0 <= k < 2 ^ 32 /\ (a + k + 7) / 8 * 8 <= YM05.alloc_ceiling /\ amem_range a ((a + k + 7) / 8 * 8 - a).
Proof.
intros lyt St Hpt Wt memt mdt Lt pk cn fl rn mo ow a k HAR HLED Hin Hk32.
destruct (prh_ledger_hblock B lyt St Hpt Wt memt Lt pk cn fl rn a k mo ow HLED Hin) as (Hk0 & Hab & _).
destruct (alx_blocks SEGS B ARx LAWS lyt St Hpt Wt memt mdt _ _ HAR Hab) as (P16 & B4096 & Bce & Bapp & _).
change (@cf_head CfParams_preset) with 16 in *.
assert (Hrs : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hrs in Bce, Bapp.
pose proof (@YM05.alloc_ceiling_value rc) as ((Cl & Ch) & C4096).
pose proof (Z.div_mod (a + k + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + k + 7) 8 ltac:(lia)).
assert (Hc8 : YM05.alloc_ceiling mod 8 = 0).
{ apply Z.mod_divide in C4096; [|lia]. destruct C4096 as [q Hq]. rewrite Hq. replace (q * 4096) with ((512 * q) * 8) by lia.
  apply Z.mod_mul. lia. }
assert (Hup : (a + k + 7) / 8 * 8 <= YM05.alloc_ceiling).
{ pose proof (Z.div_mod YM05.alloc_ceiling 8 ltac:(lia)). lia. }
split; [lia|]. split; [lia|]. split; [exact Hup|].
unfold in_app, amem_range, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *.
destruct Bapp as (_ & [Hlo | (Hhb & Hhi)]).
- left. lia.
- right. lia.
Qed.

(* ---- the bytes of harness blocks of nonnegative sizes are nonnegative ---- *)
Lemma crt102rw_bsum_nonneg : forall L, (forall a k, In (a, k) L -> 0 <= k) -> 0 <= YCbq.bsum (ck_hblks L).
Proof.
intros L H. rewrite cm_bsum_hblks. assert (0 <= Ledger.lsum L).
{ induction L as [|[a k] L IH]; cbn [Ledger.lsum]; [lia|].
  pose proof (H a k (or_introl eq_refl)). assert (0 <= Ledger.lsum L) by (apply IH; intros a' k' Hk; apply (H a' k'); right; exact Hk).
  lia. }
pose proof (@cf_head_nonneg CfParams_preset). nia.
Qed.

(* ---- an unfailed run of puts took every grow: a refused or injected grow fails the writer, and a failed writer stays
   failed ---- *)
Lemma crt102rw_putN_oktrue : forall P ok st, 0 <= WriterApp.w_cnt st < 2 ^ 64 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) = 0 ->
  forall i, (i < PRH_FnWriter.prhWriter_k ok st P)%nat -> nth i ok true = true.
Proof.
induction P as [|b P IH]; intros ok st Hc Hf i Hi.
- unfold PRH_FnWriter.prhWriter_k in Hi. cbn [PRH_FnWriter.prhWriter_putN] in Hi. lia.
- unfold PRH_FnWriter.prhWriter_k in Hi. cbn [PRH_FnWriter.prhWriter_putN] in Hf, Hi.
  destruct (PRH_FnWriter.prhWriter_grows st b) eqn:Eg.
  + unfold PRH_FnWriter.prhWriter_put1 in Hf, Hi. rewrite Eg in Hf, Hi.
    destruct (WriterApp.w_cnt st =? WriterApp.w_fail st) eqn:Ef.
    { exfalso. rewrite cm_wput_failed in Hf by (cbn; lia). cbn in Hf. discriminate Hf. }
    destruct (hd true ok) eqn:Eh.
    * set (st1 := WriterApp.mkW 0 (WriterApp.w_text st ++ b)
               (WriterSpec.newcap (WriterApp.w_cap st) (PRH_FnWriter.prhWriter_need st b))
               ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st)
               (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (PRH_FnWriter.prhWriter_need st b)])) in *.
      assert (Hc1 : 0 <= WriterApp.w_cnt st1 < 2 ^ 64) by (unfold st1; cbn; apply Z.mod_pos_bound; lia).
      destruct (cm_wput P (tl ok) st1 Hc1) as (l & El & _).
      rewrite El in Hi. assert (Ec1 : WriterApp.w_calls st1 = WriterApp.w_calls st ++
        [WriterSpec.newcap (WriterApp.w_cap st) (PRH_FnWriter.prhWriter_need st b)]) by reflexivity.
      rewrite Ec1 in Hi. rewrite !length_app in Hi. cbn [length] in Hi.
      destruct i as [|j].
      { rewrite cm_nth_hd. exact Eh. }
      rewrite cm_nth_tl. apply (IH (tl ok) st1 Hc1 Hf j).
      unfold PRH_FnWriter.prhWriter_k. rewrite El. rewrite length_app. lia.
    * exfalso. rewrite cm_wput_failed in Hf by (cbn; lia). cbn in Hf. discriminate Hf.
  + unfold PRH_FnWriter.prhWriter_grows in Eg. destruct (WriterApp.w_failed st =? 0) eqn:E0; cbn [andb] in Eg.
    * apply Z.ltb_ge in Eg. apply Z.eqb_eq in E0.
      assert (Ep : WriterApp.put1 st b = WriterApp.mkW 0 (WriterApp.w_text st ++ b) (WriterApp.w_cap st)
                     (WriterApp.w_cnt st) (WriterApp.w_fail st) (WriterApp.w_calls st)).
      { unfold WriterApp.put1. rewrite E0. cbn [negb Z.eqb].
        unfold PRH_FnWriter.prhWriter_need in Eg. rewrite (proj2 (Z.leb_le _ _) Eg). reflexivity. }
      rewrite Ep in Hf, Hi.
      apply (IH ok (WriterApp.mkW 0 (WriterApp.w_text st ++ b) (WriterApp.w_cap st) (WriterApp.w_cnt st) (WriterApp.w_fail st)
        (WriterApp.w_calls st)) ltac:(cbn; lia) Hf i). unfold PRH_FnWriter.prhWriter_k. cbn [WriterApp.w_calls]. exact Hi.
    * exfalso. assert (Ep : WriterApp.put1 st b = st) by (unfold WriterApp.put1; rewrite E0; reflexivity).
      rewrite Ep, cm_wput_failed in Hf by (apply Z.eqb_neq; exact E0). apply Z.eqb_neq in E0. exact (E0 Hf).
Qed.

(* ---- g_fail_at = SIZE_MAX stays SIZE_MAX through a run of puts (an injected failure sets it to SIZE_MAX) ---- *)
Lemma crt102rw_putN_fail : forall P ok st, WriterApp.w_fail st = SIZE_MAXZ ->
  WriterApp.w_fail (PRH_FnWriter.prhWriter_putN ok st P) = SIZE_MAXZ.
Proof.
induction P as [|b P IH]; intros ok st Hf; cbn [PRH_FnWriter.prhWriter_putN]; [exact Hf|].
destruct (PRH_FnWriter.prhWriter_grows st b) eqn:Eg; apply IH.
- unfold PRH_FnWriter.prhWriter_put1. rewrite Eg.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [reflexivity|]. destruct (hd true ok); exact Hf.
- unfold WriterApp.put1. destruct (negb (WriterApp.w_failed st =? 0)); [exact Hf|].
  destruct (_ <=? WriterApp.w_cap st); [exact Hf|]. destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [reflexivity | exact Hf].
Qed.

(* ---- an unfailed run of puts is the all-granted run: its outcomes ok answered every grow it made with true ---- *)
Lemma crt102rw_putN_ok_nil : forall P ok st, 0 <= WriterApp.w_cnt st < 2 ^ 64 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) = 0 ->
  PRH_FnWriter.prhWriter_putN ok st P = PRH_FnWriter.prhWriter_putN [] st P /\
  PRH_FnWriter.prhWriter_evs ok st P = PRH_FnWriter.prhWriter_evs [] st P.
Proof.
induction P as [|b P IH]; intros ok st Hc Hf; [split; reflexivity|].
cbn [PRH_FnWriter.prhWriter_putN PRH_FnWriter.prhWriter_evs] in Hf |- *.
destruct (PRH_FnWriter.prhWriter_grows st b) eqn:Eg.
- destruct (WriterApp.w_cnt st =? WriterApp.w_fail st) eqn:Ef.
  { exfalso. unfold PRH_FnWriter.prhWriter_put1 in Hf. rewrite Eg, Ef in Hf.
    rewrite cm_wput_failed in Hf by (cbn; lia). cbn in Hf. discriminate Hf. }
  destruct (hd true ok) eqn:Eh.
  + set (st1 := WriterApp.mkW 0 (WriterApp.w_text st ++ b)
             (WriterSpec.newcap (WriterApp.w_cap st) (PRH_FnWriter.prhWriter_need st b))
             ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st)
             (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (PRH_FnWriter.prhWriter_need st b)])).
    assert (Ep : PRH_FnWriter.prhWriter_put1 true st b = st1)
      by (unfold PRH_FnWriter.prhWriter_put1; rewrite Eg, Ef; reflexivity).
    assert (Hc1 : 0 <= WriterApp.w_cnt st1 < 2 ^ 64) by (unfold st1; cbn; apply Z.mod_pos_bound; lia).
    cbn [hd tl]. rewrite Ep in Hf |- *. destruct (IH (tl ok) st1 Hc1 Hf) as (E1 & E2).
    cbn [orb negb]. rewrite E1, E2. split; reflexivity.
  + exfalso. unfold PRH_FnWriter.prhWriter_put1 in Hf. rewrite Eg, Ef in Hf.
    rewrite cm_wput_failed in Hf by (cbn; lia). cbn in Hf. discriminate Hf.
- unfold PRH_FnWriter.prhWriter_grows in Eg. destruct (WriterApp.w_failed st =? 0) eqn:E0; cbn [andb] in Eg.
  + apply Z.ltb_ge in Eg. apply Z.eqb_eq in E0.
    assert (Ep : WriterApp.put1 st b = WriterApp.mkW 0 (WriterApp.w_text st ++ b) (WriterApp.w_cap st)
                   (WriterApp.w_cnt st) (WriterApp.w_fail st) (WriterApp.w_calls st)).
    { unfold WriterApp.put1. rewrite E0. cbn [negb Z.eqb].
      unfold PRH_FnWriter.prhWriter_need in Eg. rewrite (proj2 (Z.leb_le _ _) Eg). reflexivity. }
    rewrite Ep in Hf |- *.
    exact (IH ok (WriterApp.mkW 0 (WriterApp.w_text st ++ b) (WriterApp.w_cap st) (WriterApp.w_cnt st)
      (WriterApp.w_fail st) (WriterApp.w_calls st)) ltac:(cbn; lia) Hf).
  + exfalso. assert (Ep : WriterApp.put1 st b = st) by (unfold WriterApp.put1; rewrite E0; reflexivity).
    rewrite Ep, cm_wput_failed in Hf by (apply Z.eqb_neq; exact E0). apply Z.eqb_neq in E0. exact (E0 Hf).
Qed.

(* ---- the rewritten tree is the model's copy_set ---- *)
Lemma crt102rw_copy_set : forall ms, ck_crt_tree (PjTree.JObj ms) = PresetReqAt.copy_set ms.
Proof. intros ms. rewrite cm_crt_tree_obj. unfold PresetReqAt.copy_set. rewrite cm_MOD_KEY, cm_MOD_VAL. reflexivity. Qed.

(* ---- set_evs is pj_string's one event and then pj_set's ---- *)
Lemma crt102rw_set_evs_len : forall ms,
  length (PresetReqAt.set_evs ms) =
  Datatypes.S (length (PRH_FnPj.prhPj_set_evs ms ck_MOD_AT (Z.of_nat (length ms)) (Z.of_nat (PresetReqAt.ncap (length ms))))).
Proof.
intros ms. unfold PresetReqAt.set_evs, PRH_FnPj.prhPj_set_evs. rewrite cm_MOD_KEY, PRH_FnPj.prhPj_mfind_mod, !Nat2Z.id.
reflexivity.
Qed.

(* ---- the three words U and G spilled that L0 reads back: shadow (&doc->n), &doc->n, doc->n ---- *)
Definition crt102rw_spills (Wc : world SEGS) (memc : word -> option byte) (ms : list (list Z * PjTree.jv)) : Prop :=
  crt_spill (regs := regs) Wc memc CRT_SP_SHN (shadow_addr (doc + PJ_OFF_N)) /\
  crt_spill (regs := regs) Wc memc CRT_SP_PN (doc + PJ_OFF_N) /\
  crt_spill (regs := regs) Wc memc CRT_SP_N (Z.of_nat (length ms)).
Lemma crt102rw_spills_keep : forall (Wc W2 : world SEGS) memc mem2 ms,
  (forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  crt102rw_spills Wc memc ms -> crt102rw_spills W2 mem2 ms.
Proof.
intros Wc W2 memc mem2 ms KS (V1 & V2 & V3).
split; [|split]; apply (crt102rw_spill_keep HPRE Wc W2 memc mem2); try exact KS;
  unfold CRT_SP_SHN, CRT_SP_PN, CRT_SP_N; try lia; assumption.
Qed.
Lemma crt102rw_spills_agree : forall (Wc : world SEGS) memc mem2 ms,
  (forall xw, mrestrict (w_H Wc) mem2 xw = mrestrict (w_H Wc) memc xw) ->
  crt102rw_spills Wc memc ms -> crt102rw_spills Wc mem2 ms.
Proof.
intros Wc memc mem2 ms Hm. apply crt102rw_spills_keep. intros a _. apply aview_eq_of. apply Hm.
Qed.

(* a spill word off the one word a run wrote (the &back word at s1 + 0x38) is kept *)
Lemma crt102rw_spill_agree : forall (Wc : world SEGS) memc mem2 off v,
  (forall xw : word, ~ (sp1 + 56 <= bv_unsigned xw < sp1 + 64) ->
     mrestrict (w_H Wc) mem2 xw = mrestrict (w_H Wc) memc xw) ->
  0 <= off -> off + 8 <= 240 -> (off + 8 <= 56 \/ 64 <= off) ->
  crt_spill (regs := regs) Wc memc off v -> crt_spill (regs := regs) Wc mem2 off v.
Proof.
intros Wc memc mem2 off v Hm Ho0 Ho1 Ho2 H. unfold crt_spill in *.
pose proof (crt102rw_sp HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2 _ 8 _); [|exact H].
intros i Hi. apply aview_eq_of. apply Hm. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma crt102rw_spills_agree1 : forall (Wc : world SEGS) memc mem2 ms,
  (forall xw : word, ~ (sp1 + 56 <= bv_unsigned xw < sp1 + 64) ->
     mrestrict (w_H Wc) mem2 xw = mrestrict (w_H Wc) memc xw) ->
  crt102rw_spills Wc memc ms -> crt102rw_spills Wc mem2 ms.
Proof.
intros Wc memc mem2 ms Hm (V1 & V2 & V3).
split; [|split]; apply (crt102rw_spill_agree Wc memc mem2); try exact Hm;
  unfold CRT_SP_SHN, CRT_SP_PN, CRT_SP_N; try lia; assumption.
Qed.


(* the go state's symbolic entry: a0 = 0 and s8 = 1 pinned (`bnez a0` and `beqz s8` are then decided), the spill word
   s1 + 0x38 (written: &back) *)
Definition crt102rw_ssW0 : sstate :=
  mkSS (CRT_PC_A + crt102rw_O1R_OFF) (sr_set (sr_set cur_atoms 10%bv (SLit 0)) 24%bv (SLit 1))
    [ YP09.mkRegion (Some (xr 9)) 56 64 56 64 [] ] None (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma crt102rw_W0_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg,
  getr rg 10 = w64 0 -> getr rg 24 = w64 1 -> getr rg 9 = w64 sp1 -> 2 ^ 46 <= sp1 -> sp1 + 96 <= 2 ^ 47 ->
  sp1 mod 32 = 0 -> (forall o, 56 <= o < 64 -> apresent (w_H Wc) memc (sp1 + o)) ->
  @st_ok_pi SEGS VAL fxk (TE regs rg []) crt102rw_ssW0
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + crt102rw_O1R_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg R10 R24 R9 H1 H2 H3 HP.
set (E := TE regs rg []).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
split; [|unfold sh_ok; apply Forall_nil].
unfold crt102rw_ssW0. apply (@ts_st_ok fxk).
all: try change (TE regs rg []) with E.
- apply regs_ok_pin; [apply regs_ok_pin; [apply te_regs_ok | intros X; discriminate X | exact R10] |
    intros X; discriminate X | exact R24].
- reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | |constructor].
  intros o Ho. cbn [YP09.r_wlo YP09.r_whi] in Ho. apply (apresent_writable SEGS). apply HP. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9.
  change (2 ^ 5) with 32. split; [|exact I]. lia.
Qed.

(* ---- THE GO STATE (+0x294, the first fuzz_alloc_ran_out returned 0): s8 = set = 1, a0 = 0; copy holds the rewritten
   tree; the next step is `bnez a0` (not taken), `beqz s8` (not taken: the abort of new:728 is unreachable), then
   pj_write (&copy, 1) at +0x2b0 ---- *)
(* ---- the run's consumption window moves with the position ---- *)
Lemma crt102rw_cons_shift : forall sm xx os i a b,
  PRH_Base.prh_cons_from sm xx os i (a + b) -> PRH_Base.prh_cons_from sm xx os (i + a) b.
Proof.
intros sm xx os i a b H j e Hj He. rewrite <- Nat.add_assoc in He |- *. apply (H (a + j)%nat e); [lia | exact He].
Qed.

(* ---- the room position at W: pj_string's and pj_set's events done ---- *)
Lemma crt102rw_pos_W : forall ms pre hist S',
  rp_sm = ReaderRes.jr_strtod ->
  PresetReqAt.round_trip rp_sm t = pre ++ crt_evs_U (rp_sm := rp_sm) ms ->
  prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat (crt_evs_U (rp_sm := rp_sm) ms) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length pre)%nat (length (crt_evs_U (rp_sm := rp_sm) ms)) ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
    (rp_i + length pre + 1 + length (PRH_FnPj.prhPj_set_evs ms ck_MOD_AT (Z.of_nat (length ms))
       (Z.of_nat (PresetReqAt.ncap (length ms)))))%nat rp_H0 hist S' ->
  crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t) S'
    (crt_evs_W (rp_sm := rp_sm) ms).
Proof.
intros ms pre hist S' Esm Ert Hrun Hcons Hpos.
assert (EU : crt_evs_U (rp_sm := rp_sm) ms = PresetReqAt.set_evs ms ++ crt_evs_W (rp_sm := rp_sm) ms).
{ unfold crt_evs_U, crt_evs_W, crt_evs_L0, PresetReqAt.rw_evs. rewrite <- !app_assoc. reflexivity. }
rewrite EU in Ert, Hrun, Hcons.
refine {| crt_pos_strtod := Esm; crt_pos_ex := _ |}.
exists (pre ++ PresetReqAt.set_evs ms), hist.
refine {| crt_pos_split := _; crt_pos_room := _; crt_pos_run := _; crt_pos_cons := _ |}.
{ rewrite Ert, app_assoc. reflexivity. }
{ rewrite app_length, crt102rw_set_evs_len.
  replace (rp_i + (length pre + Datatypes.S _))%nat with
    (rp_i + length pre + 1 + length (PRH_FnPj.prhPj_set_evs ms ck_MOD_AT (Z.of_nat (length ms))
       (Z.of_nat (PresetReqAt.ncap (length ms)))))%nat by lia. exact Hpos. }
{ rewrite app_length, crt102rw_set_evs_len.
  pose proof (proj2 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) Hrun)) as H2. rewrite crt102rw_set_evs_len in H2.
  replace (rp_i + (length pre + Datatypes.S _))%nat with (rp_i + length pre + Datatypes.S
    (length (PRH_FnPj.prhPj_set_evs ms ck_MOD_AT (Z.of_nat (length ms)) (Z.of_nat (PresetReqAt.ncap (length ms))))))%nat
    by lia. exact H2. }
{ rewrite app_length, crt102rw_set_evs_len.
  rewrite app_length, crt102rw_set_evs_len in Hcons.
  replace (rp_i + (length pre + Datatypes.S _))%nat with (rp_i + length pre + Datatypes.S
    (length (PRH_FnPj.prhPj_set_evs ms ck_MOD_AT (Z.of_nat (length ms)) (Z.of_nat (PresetReqAt.ncap (length ms))))))%nat
    by lia. exact (crt102rw_cons_shift _ _ _ _ _ _ Hcons). }
Qed.

(* the position after pj_write's granted events: the reading's and L0's events are next *)
Lemma crt102rw_pos_P : forall ms pre hist S',
  rp_sm = ReaderRes.jr_strtod ->
  PresetReqAt.round_trip rp_sm t = pre ++ crt_evs_W (rp_sm := rp_sm) ms ->
  prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat (crt_evs_W (rp_sm := rp_sm) ms) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length pre)%nat (length (crt_evs_W (rp_sm := rp_sm) ms)) ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
    (rp_i + length pre + length (PresetReqAt.w_evs (PresetReqAt.copy_set ms) true))%nat rp_H0 hist S' ->
  crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t) S'
    (PresetReqAt.parse_evs rp_sm (WriterValue.wdoc (PresetReqAt.copy_set ms) true) [] ++ crt_evs_L0 ms).
Proof.
intros ms pre hist S' Esm Ert Hrun Hcons Hpos.
unfold crt_evs_W in Ert, Hrun, Hcons.
apply prh_run_at_app_iff in Hrun as [_ Hrun].
rewrite length_app in Hcons.
refine {| crt_pos_strtod := Esm; crt_pos_ex := _ |}.
exists (pre ++ PresetReqAt.w_evs (PresetReqAt.copy_set ms) true), hist.
refine {| crt_pos_split := _; crt_pos_room := _; crt_pos_run := _; crt_pos_cons := _ |}.
{ rewrite Ert, <- app_assoc. reflexivity. }
{ rewrite length_app, Nat.add_assoc. exact Hpos. }
{ rewrite length_app, Nat.add_assoc. exact Hrun. }
{ rewrite length_app, Nat.add_assoc. apply crt102rw_cons_shift. exact Hcons. }
Qed.

(* ---- THE NEXT SLICE'S ENTRY (Crt102Loops, agreed shape = the glue's crt_at_L0): the walk from L0 (+0x470) on ---- *)
Definition crt102rw_L0K : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rc,
  atL0 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rc ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_L0_OFF rg memc mdc) QFa.

(* ---- copy's ORDERED FREE LIST after the rewrite (FREEORD-COPY): tpj_set_specX's result order on its granted
   arms (PRH_FnPj.v:1104-1129 present key, :1155-1176 appended), produced at K (crt102rw_G_taken) and carried
   K -> O1 -> W -> R -> N to L0 (crt102rw_Wgo_goal, crt102rw_Wst, crt102rw_Rst, crt102rw_Nst), the A' twin of B' T3's
   crt3_copy_fo (Crt102B_T3Base.v). Its text is the conclusion of the retired OPEN_K0_FREEORD_COPY ---- *)
Definition crt102rw_copy_fo (Wc : world SEGS) (memc : word -> option byte) (Lamc : list (Z * Z)) (p : Z)
  (Dc : list (Z * Z)) : Prop :=
  exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D p Dc Fc /\
    map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (crt_tree_J (t := t)).

(* ---- val's ordered free list (tpj_set_specX's FREEORD-COPY premise on val): v is pj_string's node, ONE block
   (a, 21), and 21 + HEAD = 37 = tblk (JStr STAMP), so PRH_PjOrder.pj_free_fo gives its order list with fo's request
   (Crt102B_T3S.v crt3s_stamp_fo) ---- *)
Lemma crt102rw_stamp_fo : forall (Wc : world SEGS) (memc : word -> option byte) (Lamc : list (Z * Z)) (w a0 : Z),
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) w (PjTree.JStr ck_STAMP)
    [(a0, Z.of_nat (length ck_STAMP) + 1)] ->
  forall nv, (PjTree.depth (PjTree.JStr ck_STAMP) <= nv)%nat ->
  exists Fw, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) nv w
      [(a0, Z.of_nat (length ck_STAMP) + 1)] Fw /\
    map (fun b => snd b + cf_head) Fw = PresetReqAt.fo (PjTree.JStr ck_STAMP).
Proof.
intros Wc memc Lamc w a0 HN nv Hnv. change (@cf_head CfParams_preset) with PresetReqAt.HEAD.
apply (PRH_PjOrder.pj_free_fo SEGS _ _ _ _ _ HN); [|exact Hnv].
vm_compute. reflexivity.
Qed.

(* the walk from the go state through pj_write, strlen, parse_noting and O2 to L0, stated as a goal: the segments
   before it take it as a premise, and crt102rw_Wgo proves it from crt102rw_W2_goal (composed in crt102rw_chain) *)
Definition crt102rw_Wgo_goal : Prop := crt102rw_L0K -> forall (fx' : YK11.FPState) ly3 S3 Hp3 W3 mem3 md3 kj3 pos regs3 Do Lam3 peak3 cnt3 (c : nat) ms,
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' ->
  liveA (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat ly3 S3 Hp3 W3 mem3 md3 kj3 pos Do Lam3 peak3 cnt3 0 0 ->
  dregsA regs3 (frame_addr ly3 CRT_CID pos) -> getr regs3 22 = w64 1 -> getr regs3 24 = w64 1 ->
  getr regs3 10 = w64 0 -> getr regs3 25 = w64 (VAL 315) ->
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (frame_addr ly3 CRT_CID pos + CRT_OFF_BACK) 56 ->
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (frame_addr ly3 CRT_CID pos + CRT_OFF_V) 56 ->
  t = PjTree.JObj ms ->
  pj_nodeR SEGS (mrestrict (w_H W3) mem3) (prh_lin Lam3) (frame_addr ly3 CRT_CID pos + CRT_OFF_COPY) (ck_crt_tree t) Do ->
  (forall a k, In (a, k) Do -> 0 <= k < 2 ^ 32) ->
  Permutation (map (fun b => snd b + cf_head) Do) (PresetReqAtNoMiss.tblk (ck_crt_tree t)) ->
  (PjTree.depth (ck_crt_tree t) <= DOC_D)%nat ->
  crt102rw_copy_fo W3 mem3 Lam3 (frame_addr ly3 CRT_CID pos + CRT_OFF_COPY) Do ->
  crt102rw_spills W3 mem3 ms ->
  YCbq.bsum (ck_hblks Do) <= LIVE_round_trip_text t false + LIVE_round_trip_text t true +
    PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
    PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) ->
  cnt3 = ck_cnt2 cnt t + 1 + Z.of_nat c -> (c <= 3)%nat -> (In ck_MOD_AT (map fst ms) -> c = 0%nat) ->
  crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t) S3
    (crt_evs_W (rp_sm := rp_sm) ms) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W3 (cfgA fx' crt102rw_O1R_OFF regs3 mem3 md3) QFa.

(* ==== THE READING, W .. L0: helpers. The view lemmas and the live state across a window of the real stack are
   Crt102Loops.v's (cl_writable_mono / cl_agree / cl_ra_keep / cl_hull_keep /
   cl_blk_low / cl_ro_low / cl_live_keep / cl_sarg / cl_strcmp_call), verbatim but for the names and this Section's
   sp / doc lemmas (crt102rw_sp, crt102rw_doc_home); the string facts of a harness block are Rtt102CmpLib.v's (at commit
   2fb8f5740fe7, a file not in this tree: rcl_garr8_aview / rcl_first_byte / rcl_hull_sub / rcl_tail_in_block /
   rcl_hblk_str / rcl_nodeR_bytes / rcl_wdoc_nz / rcl_read_back), the same way. ==== *)
Lemma crt102rw_writable_mono : forall (H : word -> bool) m m' a,
  (forall z, apresent H m z -> apresent H m' z) ->
  writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H m') a.
Proof.
intros H m m' a Hpm Hw. unfold writable_at, wview, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:EH; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- assert (Hpa : apresent H m a).
  { split; [exact EH|]. exists b. exact Em. }
  destruct (Hpm a Hpa) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma crt102rw_agree : forall (H : word -> bool) m m' (X : Z -> Prop),
  (forall z, X z -> aview SEGS H m' z = aview SEGS H m z) ->
  (forall z, apresent H m z -> apresent H m' z) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H m') X.
Proof.
intros H m m' X Hv Hpm z Hz. split.
- exact (mbyte_of_aview SEGS H H m m' z (Hv z Hz)).
- apply crt102rw_writable_mono. exact Hpm.
Qed.
Lemma crt102rw_ra_keep : forall (rd rd' : reader) p n,
  (forall z, SHADOW_OFF <= z < kHighMemBeg -> rd' z = rd z) -> 0 <= p -> p + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF p n -> range_addressable rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n Hk H0 H1 Hr z Hz. destruct (Hr z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite Hk; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *.
assert (0 <= z / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.
Lemma crt102rw_hull_keep : forall (rd rd' : reader) p n,
  (forall z, SHADOW_OFF <= z < kHighMemBeg -> rd' z = rd z) -> 0 <= p -> p + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis rd p n -> shadow_hull_vis rd' p n.
Proof.
intros rd rd' p n Hk H0 H1 H2 Hh z Hz. rewrite Hk; [exact (Hh z Hz)|].
unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *.
assert (0 <= p / 8) by (apply Z.div_pos; lia).
assert ((p + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (Hlo : 0x7fff8000 / 8 <= (0x7fff8000 + p / 8) / 8) by (apply Z.div_le_mono; lia).
assert ((0x7fff8000 + (p + n - 1) / 8) / 8 * 8 <= 0x7fff8000 + (p + n - 1) / 8).
{ pose proof (Z.mul_div_le (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). lia. }
change (0x7fff8000 / 8) with 268431360 in Hlo. lia.
Qed.
Lemma crt102rw_blk_low : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc a k,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> In (a, k) Lamc ->
  0 <= k /\ 4096 + cf_head <= a /\ a + k <= YM05.alloc_ceiling.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc a k HAR HL Hin.
destruct (prh_ledger_hblock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & Hb & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hb) as (_ & B1 & B2 & _).
change (@cf_head CfParams_preset) with 16 in *.
assert (k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia). lia.
Qed.
Lemma crt102rw_ro_low : forall a, in_roP SEGS RLO RHI a -> 0 <= a < kLowMemEnd.
Proof.
intros a Hro. apply pa_segs_low.
destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* THE LIVE STATE ACROSS A CHANGE CONFINED TO A WINDOW OF THE REAL STACK below s1 + 0x70 (a runtime row's 2 * ESTACK
   window): everything crt_live reads lies below the ceiling, in the thirteen saved words, or at s1 + 0x70 *)
Lemma crt102rw_live_keep : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc lo hi
    {kbg : nat} {WS : list (list Z)},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS ->
  YCbqGwild.wbudget [] kbg WS ->
  YM05.alloc_ceiling <= lo -> hi <= sp1 + CRT_SP_F ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc') ->
  liveA kbg lyc Sc Hpc Wc memc' mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc lo hi kbg WS HL HJ' HB' Hlo Hhi Hav Hpr
  Hmn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt102rw_sp HPRE) as (H16 & Hsp0 & H47 & Hs1 & Hs32 & _). unfold CRT_SP_F in Hhi.
pose proof (crt102rw_doc_home LAWS HPRE HTREE) as (Hd1 & Hd2 & _).
assert (Hlow : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hav; lia. }
assert (Hhigh : forall a, sp1 + 112 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hav; lia. }
assert (Hsh : forall z, SHADOW_OFF <= z < kHighMemBeg -> aview SEGS (w_H Wc) memc' z = aview SEGS (w_H Wc) memc z).
{ intros z Hz. apply Hlow. unfold SHADOW_OFF in Hz. lia. }
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl. pose proof (crt_live_blocks_perm HL) as HPb.
pose proof (crt_live_dx_apart HL) as HDx. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFR. pose proof (crt_live_fspill HL) as HSF.
pose proof (crt_live_copy_open HL) as HRC. pose proof (crt_live_copy_hull HL) as HHC.
pose proof (crt_side_ledger HSD) as HLD. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _).
refine {| crt_live_journal := ex_intro _ WS (conj HJ' HB'); crt_live_side := _; crt_live_lam_perm := HPl;
          crt_live_blocks_perm := HPb; crt_live_dx_apart := HDx; crt_live_saved := _;
          crt_live_frame := _; crt_live_fspill := _; crt_live_copy_open := _;
          crt_live_copy_hull := _; crt_live_memnorm := Hmn |}.
- refine {| crt_side_ledger := _; crt_side_peak := Hpk; crt_side_room := HRL;
            crt_side_arodata := _; crt_side_doc := _; crt_side_doc_blocks := HDL |}.
  + apply (prh_ledger_kept_aview B lyc Sc Hpc Wc memc); [exact HLD | | | auto | apply Permutation_refl].
    * intros a Ha. apply Hlow. pose proof (pst_in_img_A a Ha) as Hi. pose proof (pa_segs_low a Hi). lia.
    * intros a k i Hin Hi. destruct (crt102rw_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
      apply Hlow. change (@cf_head CfParams_preset) with 16 in *. lia.
  + intros a Hro Ho He. rewrite Hlow; [exact (HRO a Hro Ho He)|].
    pose proof (crt102rw_ro_low a Hro). lia.
  + apply (pj_nodeR_frame SEGS t _ _ (prh_lin Lamc) doc D HDOC). apply crt102rw_agree; [|exact Hpr].
    intros z [Hz | (b & Hb & Hz)]; apply Hlow.
    * lia.
    * destruct b as [a k]. unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
      destruct (crt102rw_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD (HDL _ Hb)) as (_ & Ha & Hk).
      change (@cf_head CfParams_preset) with 16 in *. lia.
- intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc'); [|exact (HSV j Hj)].
  intros i Hi. apply Hhigh. lia.
- pose proof (crt_frame_listed HFR) as Hin. pose proof (crt_frame_flag_word HFR) as Hrd.
  pose proof (crt_frame_present HFR) as Hfp.
  refine {| crt_frame_listed := Hin; crt_frame_flag_word := _; crt_frame_present := _ |}.
  + destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as (F1 & F2 & _).
    rewrite <- Hrd. apply ts_rdword_keep. intros j Hj. apply Hlow. change (fs_frame_bytes CRT_CID) with 512 in *. lia.
  + intros a Ha. apply Hpr. exact (Hfp a Ha).
- apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc'); [|exact HSF].
  intros i Hi. apply Hhigh. unfold CRT_SP_F. lia.
- destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFR))
    as (F1 & F2 & _).
  change (fs_frame_bytes CRT_CID) with 512 in F2.
  apply (crt102rw_ra_keep (aview SEGS (w_H Wc) memc)); [exact Hsh | unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact HRC].
- destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFR))
    as (F1 & F2 & _).
  change (fs_frame_bytes CRT_CID) with 512 in F2.
  apply (crt102rw_hull_keep (aview SEGS (w_H Wc) memc)); [exact Hsh | unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | lia | exact HHC].
Qed.

(* ---- a string argument of a runtime row (Crt102Loops.v cl_sarg) ---- *)
Definition crt102rw_sarg (Wc : world SEGS) (m : word -> option byte) (p k : Z) : Prop :=
  4096 <= p /\ 0 <= k /\ k + 1 < 2 ^ 32 /\ p + k + 1 <= YM05.alloc_ceiling /\
  first_byte SEGS Wc m p (k + 1) 0 k /\
  (forall a, p <= a < p + k + 1 -> aview SEGS (w_H Wc) m a <> None) /\
  (p + (k + 1) + 8 <= kLowMemEnd - 1 \/ (kHighMemBeg + 15 <= p /\ p + (k + 1) + 8 <= kHighMemEnd - 1)) /\
  range_addressable (aview SEGS (w_H Wc) m) SHADOW_OFF p (k + 1) /\ shadow_hull_vis (aview SEGS (w_H Wc) m) p (k + 1) /\
  (forall a, p + k < a < p + k - (p + k) mod 8 + 8 -> aview SEGS (w_H Wc) m a <> None).

(* ---- A strlen FROM check_round_trip AT THE REALIGNED sp: YGcallMxmn.v's aj_strlen_at_xrom over the libc row STRLEN
   (Crt102Loops.v cl_strcmp_call's shape, one string). The continuation receives the live state at the callee's
   memory (crt102rw_live_keep over strlen's 2 * ESTACK window below s1), the kept registers, a0 = the length ---- *)
Lemma crt102rw_strlen_call : forall (fxk : YK11.FPState) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ownc ranc
    (off px kx : Z) {kbg : nat},
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS___wrap_strlen ->
  liveA kbg lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  bregsA (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  getr (ms_regs ms) 10 = w64 px -> crt102rw_sarg Wc (ms_mem ms) px kx ->
  (forall regs2 mem2 md2,
     liveA kbg lyc Sc Hpc Wc mem2 md2 kj pos Dx Lamc peakc cntc ownc ranc ->
     aregs_preserved (ms_regs ms) regs2 -> getr regs2 10 = w64 kx ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
        aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a) ->
     (forall a, apresent (w_H Wc) (ms_mem ms) a -> apresent (w_H Wc) mem2 a) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
       (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + off))) mem2 (YK11.seg_rom SEGS)) md2)
       QFa) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFa.
Proof.
intros fxk Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ownc ranc off px kx kbg HS Hrv Hpcs HL HBR Hra Hoff
  Hoff2 X10 SX HK.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof (crt102rw_sp HPRE) as (Hs16 & Hsc & Hs47 & Hs1 & Hs32 & _).
destruct (crt102rw_ret off Hoff Hoff2) as (Hr1 & Hr2 & Hr3).
pose proof crt102rw_stkc as HSTKC.
set (o := sp1 - sp0).
assert (Hsp1 : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hspz : spZ (ms_regs ms) = sp0 + o) by (unfold o; lia).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct SX as (X4 & Xk0 & Xk32 & Xce & Xfb & Xvis & Xam & Xra & Xhv & Xtl).
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS Hrv). cbn [ss_pc setpc]. rewrite Hpcs.
(* strlen's rule over R (the engine's YGcallMxmn.aj_strlen_at_xromR, at RZW) is over ajournal_xR: the journal rebased to the current depot
   (YCbqGwild.ajournal_xw_rebaseR) and stepped back to its budget after it (YCbqGwild.ajournal_xw_unbase0R); its
   plain conclusion is lifted by YA0nH.SRr_SRr' *)
pose proof (crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply YA0nH.SRr_SRr'.
  refine (@YGcallMxmn.aj_strlen_at_xromR fxk rc SK SEGS B PST ARx RLO RHI cf_head LAWS (@pa_segs_low rc A_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) (SIGMA AS___wrap_strlen) (STRLEN fxk) Wc (ms_regs ms) (ms_mem ms) STKC sp0 []
    ly (set_depot (st_depot Sc) S) Hp W mem md [(CRT_CID, pos)]
    lyc Sc Hpc mdc kj px kx o (getr (ms_regs ms) 1) HJr X10 _ Xk0 Xk32 _ Hspz _ _ _ _ _ eq_refl _ Xfb _ _ _ Xra Xhv Xtl HRO).
  all: try (unfold o in *; lia).
  all: first [ rewrite R3; exact Hgp | rewrite R4; exact Htp
             | rewrite Hra; apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2]
             | (intros a Ha; split; [apply Xvis; lia | rewrite Hspz; unfold o; lia])
             | (first [unfold YGcallMx.amem_range8 | unfold YGcfStr.amem_range8]; exact Xam) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hv & Hfr & Hpr2 & Hmn).
eapply YCbqGwild.ajournal_xw_unbase0R in HJ2; [|exact Hinc].
replace (sp0 + o) with sp1 in Hfr by (unfold o; lia).
pose proof (crt_live_memnorm HL) as HMNc.
assert (HL2 : liveA kbg lyc Sc Hpc Wc mem2 md2 kj pos Dx Lamc peakc cntc ownc ranc).
{ apply (crt102rw_live_keep lyc Sc Hpc Wc (ms_mem ms) mem2 mdc md2 kj kj pos Dx Lamc peakc cntc ownc ranc
    (sp1 - 2 * ESTACK) sp1 HL HJ2 HB_HJ); [lia | unfold CRT_SP_F; lia | exact Hfr | exact Hpr2 |].
  intros H0. exact (Hmn (HMNc H0)). }
rewrite Hra. exact (HK regs2 mem2 md2 HL2 HP Hv Hfr Hpr2).
Qed.

(* ---- A fuzz_alloc_ran_out () FROM check_round_trip (the O1 call's argument, crt102rw_O1, factored): the text
   (RANOUT) reads g_ran_out into a0 and changes nothing of the allocator state; the continuation receives the live
   state at the callee's memory (the same S, Hp, ledger), the callee's journal, a0 = g_ran_out, the kept registers,
   and the views kept above s1 and on the frame's shadow ---- *)
Lemma crt102rw_ranout_call : forall (fxk : YK11.FPState) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ranc off
    {kbg : nat},
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_fuzz_alloc_ran_out ->
  bv_unsigned (ew E 2) = sp0 ->
  liveA kbg lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc 0 ranc ->
  bregsA (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  (forall (fx' : YK11.FPState) ly2 W2 regs2 mem2 md2 k1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     liveA kbg ly2 Sc Hpc W2 mem2 md2 (kj + k1) pos Dx Lamc peakc cntc 0 ranc ->
     AJ (@STK_fuzz_alloc_ran_out prh_img_A) sp1 [] lyc Sc Hpc Wc (ms_mem ms) mdc [] ly2 Sc Hpc W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 -> getr regs2 10 = w64 ranc ->
     frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos ->
     (forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a) ->
     (forall a, shadow_addr (frame_addr lyc CRT_CID pos) <= a < shadow_addr (frame_addr lyc CRT_CID pos) + 64 ->
        aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfgA fx' off regs2 mem2 md2) QFa) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFa.
Proof.
intros fxk Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ranc off kbg HFZ HS Hrv Hpcs HE2 HL1 HBR1 X1 Hoff Hoff2
  HGO.
destruct (crt_live_journal HL1) as (WS_HJ1 & HJ1 & HB_HJ1). pose proof (crt_live_side HL1) as HSD1.
pose proof (crt_live_lam_perm HL1) as HPL1. pose proof (crt_live_blocks_perm HL1) as HPB1.
pose proof (crt_live_dx_apart HL1) as HAP1.
pose proof (crt_side_ledger HSD1) as HLED1. pose proof (crt_side_peak HSD1) as Hpk1.
pose proof (crt_side_room HSD1) as HROOM1. pose proof (crt_side_arodata HSD1) as HRO1.
pose proof (crt_side_doc HSD1) as HND1. pose proof (crt_side_doc_blocks HSD1) as HDL1.
assert (HSTKr : @STK_fuzz_alloc_ran_out prh_img_A = 0) by (vm_compute; reflexivity).
pose proof crt102rw_stkc as ESTK.
refine (crt102rw_call LAWS HPRE fxk (@STK_fuzz_alloc_ran_out prh_img_A) [] off (SIGMA AS_fuzz_alloc_ran_out) Wc
  E ss ms _ lyc Sc Hpc kj pos Dx Lamc peakc cntc 0 ranc _ HFZ HS Hrv Hpcs HE2 HL1 HBR1 X1 Hoff Hoff2 _ _ _ _ _).
- lia.
- lia.
- intros a Hfa. exfalso. exact (inFP_nil a Hfa).
- intros ch1 HPRE1. apply (crt102rw_lift_x fxk); [exact HFZ|]. eapply SRr_mono.
  + exact (RANOUT fxk lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 Lamc peakc cntc SIZE_MAXZ ranc most 0 HPRE1 HLED1).
  + intros W' c' _ HPo. exact HPo.
- intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP
    ((Hroomk & Ra0 & EHp & ES & Eab & HLED2) & HMNk).
  pose proof (Hroomk HROOM1) as HROOM2.
  subst S2 Hp2.
  pose proof (crt102rw_side_call LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dx Lamc peakc cntc 0 ranc _ _
    ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc cntc 0 ranc HL1 HJc (Forall_nil _) (fun a Hf => False_ind _ (inFP_nil a Hf))
    HLED2 ltac:(lia) HROOM2 HDL1) as HSD2.
  assert (HPB2 : Permutation (ablocks B ly2 Sc) (ablocks B ly S ++ ck_hblks Dx)) by (rewrite Eab; exact HPB1).
  pose proof (crt102rw_live_call LAWS HPRE lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dx Lamc peakc cntc 0 ranc _ _
    ly2 Sc Hpc W2 mem2 md2 k1 Dx Lamc peakc cntc 0 ranc HL1 HJe HJc ltac:(lia)
    (fun a Hf => False_ind _ (inFP_nil a Hf)) HSD2 HPL1 HPB2 HAP1 HMNk) as HL2.
  destruct (crt102rw_call_keep LAWS HPRE lyc Sc Hpc Wc (ms_mem ms) _ kj pos _ _ ly2 Sc Hpc W2 mem2 md2 k1 HJ1 HJc
    (fun a Hf => False_ind _ (inFP_nil a Hf))) as (EF2 & KS2 & KSH2).
  exact (HGO fx' ly2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HL2 HJc HP Ra0 EF2 KS2 KSH2).
Qed.

(* ---- the bytes of a live ledger block across a call whose footprint misses it (ajournal_x's block clause) ---- *)
Lemma crt102rw_bytes_call : forall lyc Sc Hpc Wc memc mdc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 q k l,
  AJ STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  forall {mo1 ow1 mo2 ow2 : Z},
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc mo1 ow1 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 mo2 ow2 ->
  In (q, k) Lamc -> In (q, k) Lam2 -> Z.of_nat (length l) <= k ->
  (forall a, inFP FP1 a -> ~ (q <= a < q + k)) ->
  bytes_at Wc memc q l -> bytes_at W2 mem2 q l.
Proof.
intros lyc Sc Hpc Wc memc mdc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 q k l
  HJ1 mo1 ow1 mo2 ow2 HLED HLED2 Hin Hin2 Hl HFP Hb.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
destruct (prh_ledger_hblock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED Hin) as (Hk0 & Hab & _).
destruct (prh_ledger_hblock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED2 Hin2) as (_ & Hab2 & _).
unfold bytes_at, garr8 in *. intros j Hj. destruct (Hb j Hj) as (Hv & Hr). split; [|exact Hr].
apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 1 _); [|exact Hv].
intros i Hi. assert (Ei : i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r.
change (@cf_head CfParams_preset) with 16 in *.
assert (Er : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
replace (q + Z.of_nat j) with (q - 16 + (16 + Z.of_nat j)) by lia.
apply (G2 (q - 16) (k + 16) (16 + Z.of_nat j) Hab Hab2); [rewrite Er; lia|].
replace (q - 16 + (16 + Z.of_nat j)) with (q + Z.of_nat j) by lia. intros Hf. exact (HFP _ Hf ltac:(lia)).
Qed.

(* ---- bytes under a memory equal through the restriction ---- *)
Lemma crt102rw_bytes_agree : forall (Wc : world SEGS) memc memc' p l,
  (forall xw, mrestrict (w_H Wc) memc' xw = mrestrict (w_H Wc) memc xw) ->
  bytes_at Wc memc p l -> bytes_at Wc memc' p l.
Proof.
intros Wc memc memc' p l Hm Hb. unfold bytes_at, garr8 in *. intros j Hj. destruct (Hb j Hj) as (Hv & Hr).
split; [|exact Hr]. apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc' _ 1 _); [|exact Hv].
intros i _. apply aview_eq_of. apply Hm.
Qed.

(* ---- the string facts of a NUL-terminated text in a live harness block of the ledger (Rtt102CmpLib.v
   rcl_garr8_aview / rcl_first_byte / rcl_hull_sub / rcl_tail_in_block / rcl_hblk_str, verbatim but the names; the
   head is the preset's, cf_head = 16) ---- *)
Lemma crt102rw_garr8_aview : forall (Wc : world SEGS) m p l j, garr8 SEGS (mrestrict (w_H Wc) m) p l -> (j < length l)%nat ->
  aview SEGS (w_H Wc) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros Wc m p l j H Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.
Lemma crt102rw_first_byte : forall (Wc : world SEGS) m p l, bytes_at Wc m p (l ++ [0]) -> Forall (fun c => 0 < c < 256) l ->
  first_byte SEGS Wc m p (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
intros Wc m p l Hg Hnz. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (crt102rw_garr8_aview Wc m p (l ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn [length]; lia).
    rewrite app_nth1 by lia. reflexivity.
  + rewrite Forall_nth in Hnz. pose proof (Hnz (Z.to_nat i) 0 ltac:(lia)) as Hc. lia.
- intros _. rewrite (crt102rw_garr8_aview Wc m p (l ++ [0]) (length l) Hg) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma crt102rw_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma crt102rw_tail_in_block : forall lyc Sc Hpc Wc memc mdc b n p m s0 a,
  ARx lyc Sc Hpc Wc memc mdc -> In (b, n) (ablocks B lyc Sc) -> b + req_size n = p + m -> b <= p ->
  (forall x0, b <= x0 < b + req_size n -> apresent (w_H Wc) memc x0) -> p <= s0 -> s0 < p + m ->
  s0 < a < s0 - s0 mod 8 + 8 -> aview SEGS (w_H Wc) memc a <> None.
Proof.
intros lyc Sc Hpc Wc memc mdc b n p m s0 a HAR Hin Hend Hbp Hpr Hps Hsm Ha.
destruct (Z_lt_le_dec a (p + m)) as [Hl|Hl].
- assert (Hb : b <= a < b + req_size n) by lia.
  exact (crt102rw_apresent_vis _ memc a (Hpr a Hb)).
- apply (alx_blocks_tail _ _ _ LAWS lyc Sc Hpc Wc memc mdc b n a HAR Hin). rewrite Hend.
  pose proof (Z.div_mod s0 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound s0 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (p + m + 7) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + m + 7) 8 ltac:(lia)) as M2.
  set (k1 := s0 / 8) in *. set (r1 := s0 mod 8) in *. set (k2 := (p + m + 7) / 8) in *.
  set (r2 := (p + m + 7) mod 8) in *. lia.
Qed.
Lemma crt102rw_hblk_str : forall lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc q capw n,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> In (q, capw) Lamc ->
  0 <= n -> n < capw ->
  0 < q /\ q + n + 1 <= 2 ^ 63 /\ q + n < YM05.alloc_ceiling /\
  YGcfStr.amem_range8 q (n + 1) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF q (n + 1) /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) q (n + 1) /\
  (forall a, q + n < a < q + n - (q + n) mod 8 + 8 -> aview SEGS (w_H Wc) memc a <> None).
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc q capw n HAR HL Hin Hn0 Hlt.
assert (HW : 8 <= @cf_head CfParams_preset) by (change (@cf_head CfParams_preset) with 16; lia).
pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc HL) (q, capw) Hin) as Hb.
cbn [fst snd] in Hb. destruct Hb as (Hk0 & Hab & Hhp & H16 & _).
assert (Hreq : req_size (capw + cf_head) = capw + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (capw + cf_head) 0); lia).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc (q - cf_head) (capw + cf_head) HAR Hab)
  as (_ & H4096 & Hceil & Happ & Hpr & _).
rewrite Hreq in Hceil, Happ.
destruct (alx_hshadow _ _ _ LAWS lyc Sc Hpc Wc memc mdc (q - cf_head) (capw + cf_head) HAR Hab Hhp) as [Hbs Hhu].
rewrite Hreq in Hbs, Hhu. replace (q - cf_head + cf_head) with q in Hbs, Hhu by lia.
replace (capw + cf_head - cf_head) with capw in Hbs, Hhu by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof YM05.alloc_ceiling_lt as Hc47.
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ unfold YGcfStr.amem_range8. unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ.
  destruct Happ as (_ & [Hlo | (Hhb & Hhe)]).
  - left. rewrite C5. lia.
  - right. apply Z.mod_divide in H16; [|lia]. destruct H16 as [aq Haq].
    assert (EK : kHighMemBeg = 16 * (kHighMemBeg / 16)) by (rewrite C3; reflexivity).
    set (kb := kHighMemBeg / 16) in *. rewrite C4. lia. }
split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
split; [apply (crt102rw_hull_sub _ q capw q (n + 1)); [apply Hhu; lia | lia | lia | lia]|].
intros a Ha. apply (crt102rw_tail_in_block lyc Sc Hpc Wc memc mdc (q - cf_head) (capw + cf_head) q capw (q + n) a HAR Hab);
  [rewrite Hreq; lia | lia | exact (fun x0 Hx => proj1 (Hpr x0 Hx)) | lia | lia | exact Ha].
Qed.
(* a byte list in memory whose bytes are positive is a list of nonzero bytes (garr8 bounds each below 256) *)
Lemma crt102rw_text_nz : forall (Wc : world SEGS) m q l, bytes_at Wc m q (l ++ [0]) -> Forall (fun c => 0 < c) l ->
  Forall (fun c => 0 < c < 256) l.
Proof.
intros Wc m q l Hb Hpos. apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) Hpos c Hc) as H0.
destruct (In_nth l c 0 Hc) as (j & Hj & Ej).
assert (Hj' : (j < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
unfold bytes_at, garr8 in Hb. destruct (Hb j Hj') as (_ & Hr).
rewrite (app_nth1 l [0%Z] 0%Z Hj) in Hr. rewrite Ej in Hr. cbv beta in H0. lia.
Qed.

(* the text pj_write left at q, as a strlen argument *)
Lemma crt102rw_text_sarg : forall lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc q capw l,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> In (q, capw) Lamc ->
  Z.of_nat (length l) < capw -> capw < 2 ^ 32 -> bytes_at Wc memc q (l ++ [0]) -> Forall (fun c => 0 < c < 256) l ->
  crt102rw_sarg Wc memc q (Z.of_nat (length l)).
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc q capw l HAR HL Hin Hlt H32 Hb Hnz.
destruct (crt102rw_hblk_str lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc q capw (Z.of_nat (length l))
  HAR HL Hin ltac:(lia) Hlt) as (Hq0 & Hq63 & Hqc & Ham & Hra & Hhv & Htl).
destruct (crt102rw_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL Hin) as (Hk & Hq4 & Hqk).
unfold crt102rw_sarg. change (@cf_head CfParams_preset) with 16 in Hq4.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (crt102rw_first_byte Wc memc q l Hb Hnz)|].
split.
{ intros a Ha. replace a with (q + Z.of_nat (Z.to_nat (a - q))) by lia.
  unfold bytes_at in Hb. rewrite (crt102rw_garr8_aview Wc memc q (l ++ [0]) (Z.to_nat (a - q)) Hb)
    by (rewrite length_app; cbn [length]; lia). discriminate. }
split; [unfold YGcfStr.amem_range8 in Ham; exact Ham|]. split; [exact Hra|]. split; [exact Hhv | exact Htl].
Qed.

(* ---- back (F + 0x20) as parse_noting's out place: in the class-3 frame, writable, addressable, its shadow hull inside
   the frame's 64 shadow bytes (Rtt102CmpPNA.v pn_back_ok for a 512-byte frame) ---- *)
Lemma crt102rw_back_ok : forall lyc Sc Hpc Wc memc mdc kj pos (regsc : bvmap 5 word) STK1 {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 ->
  YM05.alloc_ceiling <= spZ regsc - STK1 ->
  ck_out_ok B STK1 lyc Sc Wc regsc memc (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos regsc STK1 WS HJ HRA Hstk.
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr lyc CRT_CID pos) in *. unfold CRT_OFF_BACK in *.
apply Z.mod_divide in F32; [|lia]. destruct F32 as [f Ef].
split.
{ exists CRT_CID, pos. split; [exact Hin|]. rewrite crt102rw_fb. lia. }
split; [lia|]. split; [lia|]. split.
{ unfold amem_range. unfold in_app, kLowShadowBeg, ASAN_CEIL in Fb3.
  destruct Fb3 as (_ & [Hlo | (Hhb & Hhe)]); [left; rewrite C5; lia | right; rewrite C4; split; lia]. }
split.
{ intros a Ha. destruct (Ffr a ltac:(lia)) as (Hpa & Hno).
  split; [apply (apresent_writable SEGS); exact Hpa|]. split; [exact Hno | lia]. }
split; [exact HRA|].
intros _ s0 Hs.
assert (E0 : F / 8 = 4 * f) by (rewrite Ef; symmetry; apply (Z.div_unique _ _ _ 0); lia).
assert (E1 : (F + 32) / 8 = 4 * f + 4) by (rewrite Ef; symmetry; apply (Z.div_unique _ _ _ 0); lia).
assert (E2 : (F + 32 + 56 - 1) / 8 = 4 * f + 10) by (rewrite Ef; symmetry; apply (Z.div_unique _ _ _ 7); lia).
unfold shadow_addr in Hs, Fsh. rewrite E1, E2 in Hs. rewrite E0 in Fsh.
assert (Hr : SHADOW_OFF + 4 * f <= s0 < SHADOW_OFF + 4 * f + 64).
{ pose proof (Z.div_mod (SHADOW_OFF + (4 * f + 4)) 8 ltac:(lia)) as DA.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * f + 4)) 8 ltac:(lia)) as MA.
  pose proof (Z.div_mod (SHADOW_OFF + (4 * f + 10)) 8 ltac:(lia)) as DB.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * f + 10)) 8 ltac:(lia)) as MB.
  set (qa := (SHADOW_OFF + (4 * f + 4)) / 8) in *.
  set (qb := (SHADOW_OFF + (4 * f + 10)) / 8) in *.
  set (ra := (SHADOW_OFF + (4 * f + 4)) mod 8) in *.
  set (rb := (SHADOW_OFF + (4 * f + 10)) mod 8) in *.
  unfold SHADOW_OFF in *. lia. }
destruct (Fsh (s0 - (SHADOW_OFF + 4 * f)) ltac:(lia)) as (Hps & _).
assert (Es : SHADOW_OFF + 4 * f + (s0 - (SHADOW_OFF + 4 * f)) = s0) by lia.
rewrite Es in Hps. exact (crt102rw_apresent_vis _ _ _ Hps).
Qed.

(* ---- a tree's footprint agrees across a call whose footprint misses it (Crt102Kit.v crt102rw_tree_call's argument,
   stated as the agreement, so pj_foR / pj_fdR frame by it too) ---- *)
Lemma crt102rw_foot_call : forall lyc Sc Hpc Wc memc mdc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p Dt,
  ARx lyc Sc Hpc Wc memc mdc ->
  AJ STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  forall {mo1 ow1 mo2 ow2 : Z},
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc mo1 ow1 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 mo2 ow2 ->
  (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= p /\
     p + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) ->
  (forall bk, In bk Dt -> In bk Lamc) -> (forall bk, In bk Dt -> In bk Lam2) ->
  (forall a, inFP FP1 a -> ~ pj_footR p Dt a) ->
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (pj_footR p Dt).
Proof.
intros lyc Sc Hpc Wc memc mdc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p Dt
  HARc HJ1 mo1 ow1 mo2 ow2 HLED HLED2 (cid & pos' & Hfin' & Hfa1 & Hfa2) HDL HDL2 HFPD.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _).
apply crt102rw_agree_of_aview. intros y Hy.
assert (Hyc : (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
                 frame_addr lyc cid0 pos0 <= y < frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) \/
              (exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ In (p0, n0) (ablocks B ly2 S2) /\
                 p0 <= y < p0 + req_size n0)).
{ destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
  - left. exists cid, pos'. split; [exact Hfin'|]. lia.
  - right. unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
    destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb)) as (Hk0 & Hab & _).
    destruct (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 b kb _ _ HLED2 (HDL2 _ Hb)) as (_ & Hab2 & _).
    exists (b - cf_head), (kb + cf_head). split; [exact Hab|]. split; [exact Hab2|].
    change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb + 16) ltac:(lia)). lia. }
assert (Himg : ~ in_img SEGS y).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_intror (or_introl (ex_intro _ cid0 (ex_intro _ pos0 (conj Hin0 Hy0))))))).
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_introl (ex_intro _ p0 (ex_intro _ n0 (conj Hab Hy0)))))). }
assert (Hyr : 0 <= y < 2 ^ 64).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid0 pos0 HARc Hin0) as (? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia.
  - destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & ? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia. }
split; [exact Hyr|]. split; [exact Himg|].
assert (HnFP : ~ inFP FP1 y) by (intros Hf; exact (HFPD y Hf Hy)).
destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & Hab2 & Hy0)].
- apply (G4 cid0 pos0 y Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnFP].
- replace y with (p0 + (y - p0)) by lia. apply (G2 p0 n0 (y - p0) Hab Hab2); [lia|]. replace (p0 + (y - p0)) with y by lia.
  exact HnFP.
Qed.
(* agreement through a memory equal under the restriction *)
Lemma crt102rw_agree_eq : forall (H : word -> bool) m m' X, (forall xw, mrestrict H m' xw = mrestrict H m xw) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H m') X.
Proof.
intros H m m' X Hm y _. assert (E : mrestrict H m' (Z_to_bv 64 y) = mrestrict H m (Z_to_bv 64 y)) by apply Hm.
split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw.
Qed.

(* ---- the own flag's region (O1's, crt102rw_ssO1) at W (+0x2b4), a0 free; and at N (+0x2e4) with a0 pinned to v ---- *)
Definition crt102rw_ssOwnW : sstate := mkSS (CRT_PC_A + CRT_W_OFF) (sr_set cur_atoms 25%bv (SOff (A_OBJ 13) 1456))
  [ YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ] None
  (mkFacts [] [] []).
Lemma crt102rw_ownW_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg,
  prh_own Wc memc 0 -> getr rg 25 = w64 (VAL 315) ->
  @st_ok_pi SEGS VAL fxk (TE regs rg []) crt102rw_ssOwnW
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_W_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg (Hv & _) R25.
pose proof crt102rw_own_cell as (Ec & Hi & Ez & V13).
set (E := TE regs rg []).
assert (X13 : bv_unsigned (ew E (A_OBJ 13)) = VAL (A_OBJ 13)).
{ unfold E. rewrite te_img by exact Hi. apply unsigned_lit_small. lia. }
assert (E315 : ew E 315 = Z_to_bv 64 (VAL 315)).
{ unfold E. apply te_img. split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity. }
split; [|unfold sh_ok; apply Forall_nil].
unfold crt102rw_ssOwnW. apply (@ts_st_ok fxk).
all: try change (TE regs rg []) with E.
- apply regs_ok_pin; [apply te_regs_ok | intros X; discriminate X |].
  rewrite R25. apply bv_eq. rewrite denot_SOff. try unfold E. rewrite (te_img regs rg [] (A_OBJ 13) Hi). vm_compute. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (A_OBJ 13) (VAL (A_OBJ 13))); [exact X13 | lia | lia | intros o Ho; cbn in Ho; lia |].
  constructor; [|constructor].
  apply (ts_chunk E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
  rewrite Ez in Hv. rewrite Z.add_0_r, Ec. exact Hv.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.
Definition crt102rw_ssOwnN (v : Z) : sstate :=
  mkSS (CRT_PC_A + CRT_N_OFF) (sr_set (sr_set cur_atoms 10%bv (SLit v)) 25%bv (SOff (A_OBJ 13) 1456))
  [ YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ] None
  (mkFacts [] [] []).
Lemma crt102rw_ownN_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg v,
  prh_own Wc memc 0 -> getr rg 10 = w64 v -> getr rg 25 = w64 (VAL 315) ->
  @st_ok_pi SEGS VAL fxk (TE regs rg []) (crt102rw_ssOwnN v)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_N_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg v (Hv & _) R10 R25.
pose proof crt102rw_own_cell as (Ec & Hi & Ez & V13).
set (E := TE regs rg []).
assert (X13 : bv_unsigned (ew E (A_OBJ 13)) = VAL (A_OBJ 13)).
{ unfold E. rewrite te_img by exact Hi. apply unsigned_lit_small. lia. }
assert (E315 : ew E 315 = Z_to_bv 64 (VAL 315)).
{ unfold E. apply te_img. split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity. }
split; [|unfold sh_ok; apply Forall_nil].
unfold crt102rw_ssOwnN. apply (@ts_st_ok fxk).
all: try change (TE regs rg []) with E.
- apply regs_ok_pin; [apply regs_ok_pin; [apply te_regs_ok | intros X; discriminate X | exact R10] |
    intros X; discriminate X |].
  rewrite R25. apply bv_eq. rewrite denot_SOff. try unfold E. rewrite (te_img regs rg [] (A_OBJ 13) Hi). vm_compute. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (A_OBJ 13) (VAL (A_OBJ 13))); [exact X13 | lia | lia | intros o Ho; cbn in Ho; lia |].
  constructor; [|constructor].
  apply (ts_chunk E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
  rewrite Ez in Hv. rewrite Z.add_0_r, Ec. exact Hv.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.
(* a0 pinned at a return site (the branch after it is then decided by the engine) *)
Definition crt102rw_ssP (off v : Z) : sstate :=
  mkSS (CRT_PC_A + off) (sr_set cur_atoms 10%bv (SLit v)) [] None (mkFacts [] [] []).
Lemma crt102rw_P_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg off v, getr rg 10 = w64 v ->
  @st_ok_pi SEGS VAL fxk (TE regs rg []) (crt102rw_ssP off v)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + off))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg off v R10.
split; [|unfold sh_ok; apply Forall_nil].
unfold crt102rw_ssP. apply (@ts_st_ok fxk).
- apply regs_ok_pin; [apply te_regs_ok | intros X; discriminate X | exact R10].
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.
(* strlen's return site (+0x2d4): the &back spill at s1 + 0x38 as a chunk (the `ld a2, 0x38(s1)` reads it) *)
Definition crt102rw_ssS : sstate := mkSS (CRT_PC_A + 724) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32))] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma crt102rw_S_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg F,
  getr rg 9 = w64 sp1 -> 2 ^ 46 <= sp1 -> sp1 + 96 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  getr rg 27 = w64 F -> 0 <= F -> F + 512 <= 2 ^ 47 ->
  crt_spill (regs := regs) Wc memc CRT_SP_BACK (F + CRT_OFF_BACK) ->
  @st_ok_pi SEGS VAL fxk (TE regs rg []) crt102rw_ssS
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + 724))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg F R9 H1 H2 H3 R27 HF0 HF1 VBK.
unfold crt_spill, CRT_SP_BACK, CRT_OFF_BACK in VBK.
set (E := TE regs rg []).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (W27 : ew E (xr 27) = w64 F).
{ unfold E, xr. rewrite (te_cur regs rg _ 27%bv 27) by reflexivity. exact R27. }
split; [|unfold sh_ok; apply Forall_nil].
unfold crt102rw_ssS. apply (@ts_st_ok fxk).
all: try change (TE regs rg []) with E.
- apply te_regs_ok.
- reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | intros o Ho; cbn in Ho; lia |].
  constructor; [|constructor].
  apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
  rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9.
  change (2 ^ 5) with 32. split; [|exact I]. lia.
Qed.

(* ---- W (+0x2b4): pj_write (&copy, 1) has returned its text q <> 0. The state the rest of the slice needs: the live
   state over the buffer and copy's blocks, the registers, the two locals open, copy's tree and its facts, the four
   spills, the text and its buffer, the writer run's facts (L0's), the room used, the room position after w_evs ---- *)
Definition crt102rw_Wst (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Do Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (c : nat) (q cap : Z) (ok : list bool) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveA (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos ((q, cap) :: Do) Lamc peakc cntc 0 0 /\
  dregsA rg (frame_addr lyc CRT_CID pos) /\
  getr rg 10 = w64 q /\ getr rg 22 = w64 1 /\ getr rg 25 = w64 (VAL 315) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  t = PjTree.JObj ms /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) (ck_crt_tree t) Do /\
  Permutation (map (fun b => snd b + cf_head) Do) (PresetReqAtNoMiss.tblk (ck_crt_tree t)) /\
  (PjTree.depth (ck_crt_tree t) <= DOC_D)%nat /\
  crt102rw_copy_fo Wc memc Lamc (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Do /\
  crt102rw_spills Wc memc ms /\
  crt_spill (regs := regs) Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) /\
  q <> 0 /\ Z.of_nat (length (WriterValue.wdoc (ck_crt_tree t) true)) < cap /\ cap < 2 ^ 32 /\
  bytes_at Wc memc q (WriterValue.wdoc (ck_crt_tree t) true ++ [0]) /\
  (c <= 3)%nat /\ (In ck_MOD_AT (map fst ms) -> c = 0%nat) /\
  prh_oks ok (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ
    (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
       (WriterValue.wdpieces (ck_crt_tree t) true))
    (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
       (WriterValue.wdpieces (ck_crt_tree t) true)) most 0 0 /\
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true)) = 0 /\
  cap = WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true)) /\
  cntc = WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true)) /\
  YCbq.bsum (ck_hblks ((q, cap) :: Do)) <= LIVE_round_trip_text t false + LIVE_round_trip_text t true +
    PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
    PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) +
    PRH_FnWriter.LIVE_pj_write (ck_crt_tree t) true /\
  crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t) Sc
    (PresetReqAt.parse_evs rp_sm (WriterValue.wdoc (PresetReqAt.copy_set ms) true) [] ++ crt_evs_L0 ms).

Definition crt102rw_W2_goal : Prop :=
  crt102rw_L0K -> forall fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc rg ms c q cap ok,
  crt102rw_Wst fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc rg ms c q cap ok ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_W_OFF rg memc mdc) QFa.

(* ---- THE READING STATE at the return sites +0x2c8 / +0x2d4 (fuzz_alloc_ran_out's, strlen's): the W state with the
   text q in s8 (x24); a0 the site's ---- *)
Definition crt102rw_Rst (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Do Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (c : nat) (q cap : Z) (ok : list bool) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveA (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos ((q, cap) :: Do) Lamc peakc cntc 0 0 /\
  dregsA rg (frame_addr lyc CRT_CID pos) /\
  getr rg 24 = w64 q /\ getr rg 22 = w64 1 /\ getr rg 25 = w64 (VAL 315) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  t = PjTree.JObj ms /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) (ck_crt_tree t) Do /\
  Permutation (map (fun b => snd b + cf_head) Do) (PresetReqAtNoMiss.tblk (ck_crt_tree t)) /\
  (PjTree.depth (ck_crt_tree t) <= DOC_D)%nat /\
  crt102rw_copy_fo Wc memc Lamc (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Do /\
  crt102rw_spills Wc memc ms /\
  crt_spill (regs := regs) Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) /\
  q <> 0 /\ Z.of_nat (length (WriterValue.wdoc (ck_crt_tree t) true)) < cap /\ cap < 2 ^ 32 /\
  bytes_at Wc memc q (WriterValue.wdoc (ck_crt_tree t) true ++ [0]) /\
  (c <= 3)%nat /\ (In ck_MOD_AT (map fst ms) -> c = 0%nat) /\
  prh_oks ok (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ
    (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
       (WriterValue.wdpieces (ck_crt_tree t) true))
    (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
       (WriterValue.wdpieces (ck_crt_tree t) true)) most 0 0 /\
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true)) = 0 /\
  cap = WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true)) /\
  cntc = WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true)) /\
  YCbq.bsum (ck_hblks ((q, cap) :: Do)) <= LIVE_round_trip_text t false + LIVE_round_trip_text t true +
    PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
    PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) +
    PRH_FnWriter.LIVE_pj_write (ck_crt_tree t) true /\
  crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t) Sc
    (PresetReqAt.parse_evs rp_sm (WriterValue.wdoc (PresetReqAt.copy_set ms) true) [] ++ crt_evs_L0 ms).
Definition crt102rw_G712 : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc rg ms c q cap ok,
  crt102rw_Rst fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc rg ms c q cap ok -> getr rg 10 = w64 0 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk 712 rg memc mdc) QFa.

(* ---- W (+0x2b4 .. +0x2c4): `mv s8, a0; beqz a0` (q <> 0: not taken), the first flag test of the second
   out_of_memory () (`lbu a0, -0x5b0(s9)`: g_own_ran_out = 0, no crossed text writes it), `jal fuzz_alloc_ran_out`; at
   its return (+0x2c8) a0 = g_ran_out = 0 (pj_write was granted) ---- *)
Lemma crt102rw_W2 : crt102rw_G712 -> crt102rw_W2_goal.
Proof.
intros HG712 HL0K fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc rg ms c q cap ok HW.
pose proof HW as (HFZ & HFK & HL & HDR & R10 & R22 & R25 & HRAb & HRAv & Et & HNo & HTBo & Hdepc & HFO & HSP & VBACK & Hq0 &
  Hlen & Hcap32 & Hbytes & Hc3 & Hcin & Hoks & Hwf & Ecap & Ecnt & HBS & HPOS).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_sp (crt_dregs_bregs HDR)) as R2.
pose proof (crt_bregs_gp (crt_dregs_bregs HDR)) as R3.
pose proof (crt_bregs_tp (crt_dregs_bregs HDR)) as R4.
pose proof (crt_bregs_s0 (crt_dregs_bregs HDR)) as R8.
pose proof (crt_bregs_s1 (crt_dregs_bregs HDR)) as R9.
pose proof (crt_bregs_s2 (crt_dregs_bregs HDR)) as R18.
pose proof (crt_bregs_s4 (crt_dregs_bregs HDR)) as R20.
pose proof (crt_bregs_s3 (crt_dregs_bregs HDR)) as R19.
pose proof (crt_bregs_s7 (crt_dregs_bregs HDR)) as R23.
pose proof (crt_bregs_s10 (crt_dregs_bregs HDR)) as R26.
pose proof (crt_bregs_s11 (crt_dregs_bregs HDR)) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt102rw_sp HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof crt102rw_stkc as ESTK.
pose proof (YM05.alloc_ceiling_val) as Hcv.
set (F := frame_addr lyc CRT_CID pos) in *.
assert (HqL : In (q, cap) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
destruct (crt102rw_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ) HLED HqL) as (Hcap0 & Hq4096 & Hqc).
destruct (crt102rw_ownW_entry fxk Wc memc rg ltac:(eapply PRH_Base.prh_ledger_own; exact HLED) R25) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
pose proof HMNc as HPM.
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
pose (BR := @YSRrG.paj_branchR fxk rc A_prog_listing PA RZW).
unfold crt_cfg.
paj_run_tok_x_inv (RUN WS_HJ) HS HJ SHOK HPM (0, 0).
{ cbv [crt102rw_ssOwnW ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (Hm0 : forall xw, mrestrict (w_H Wc) (ms_mem ms0) xw = mrestrict (w_H Wc) memc xw).
{ intros xw. apply HFr. intros (r & Hr & Ha). cbv [crt102rw_ssOwnW ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
clear HF HG HFr.
psrr_branch_tok RUN BR HS SHOK (0, 0).
- (* beqz a0 taken: a0 = q, a live block's address, is not 0 *)
  exfalso. rewrite branch_eq_U, !ts_U0, U_SLit in Hc.
  assert (A42 : ew (TE regs rg []) 42 = getr rg 10) by (apply (te_cur regs rg [] 10%bv 10); reflexivity).
  rewrite A42, R10 in Hc. apply Z.eqb_eq in Hc. unfold w64 in Hc.
  assert (Hq64 : 0 <= q < 2 ^ 64) by (pose proof (@cf_head_nonneg CfParams_preset); pose proof YM05.alloc_ceiling_lt; lia).
  rewrite unsigned_lit_small in Hc by lia.
  unfold zcanon, M64 in Hc. rewrite Z.mod_0_l in Hc by lia. lia.
- (* not taken: the flag test and the call *)
  paj_run_tok_x_inv (RUN WS_HJ) HS HJ SHOK HPM (0, 0).
  { cbv [crt102rw_ssOwnW ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  assert (Hm01 : forall xw, mrestrict (w_H Wc) (ms_mem ms1) xw = mrestrict (w_H Wc) memc xw).
  { intros xw. rewrite <- (Hm0 xw). apply HFr. intros (r & Hr & Ha). vm_compute in Hr. destruct Hr as [<- | []].
    cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc memc (ms_mem ms1) mdc _ kj _ pos ((q, cap) :: Do) Lamc peakc
    cntc 0 0 HL HJ HB_HJ (fun xw _ => Hm01 xw) HPM) as HL1.
  assert (KR1 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 26; 27]%bv ->
    getr (ms_regs ms1) r = getr rg r).
  { intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
  prreg HS (1%bv : bv 5) Q1. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  assert (X25 : getr (ms_regs ms1) 25 = w64 (VAL 315)).
  { rewrite Q25. rewrite (te_img regs rg [] 254) by (split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity).
    vm_compute. reflexivity. }
  assert (X1 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + 712))) by (rewrite Q1; vm_compute; reflexivity).
  assert (X24 : getr (ms_regs ms1) 24 = w64 q).
  { rewrite Q24. assert (A : ew (TE regs rg []) 42 = getr rg 10) by te_close. rewrite A. exact R10. }
  assert (HBR1 : bregsA (ms_regs ms1) F).
  { refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
              crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
              crt_bregs_s11 := _ |}; rewrite !KR1 by (cbv; tauto); assumption. }
  assert (HE2 : bv_unsigned (ew (TE regs rg []) 2) = sp0) by (rewrite (te_entry regs rg [] 2%bv 2) by reflexivity; reflexivity).
  destruct (crt_live_journal HL1) as (WS_HJ1 & HJ1 & HB_HJ1). pose proof (crt_live_side HL1) as HSD1.
  pose proof (crt_live_lam_perm HL1) as HPL1. pose proof (crt_live_blocks_perm HL1) as HPB1.
  pose proof (crt_live_dx_apart HL1) as HAP1.
  pose proof (crt_side_ledger HSD1) as HLED1. pose proof (crt_side_doc_blocks HSD1) as HDL1.
  clear HF HG HFr.
  apply (crt102rw_ranout_call fxk Wc (TE regs rg []) _ ms1 _ lyc Sc Hpc _ pos ((q, cap) :: Do) Lamc peakc cntc 0 712
    HFZ HS eq_refl eq_refl HE2 HL1 HBR1 X1 ltac:(lia) ltac:(reflexivity)).
  intros fx' ly2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HL2 HJc HP Ra0 EF2 KS2 KSH2.
  assert (HFK3 : fregs_kept_x fx fx') by (intros r0 Hr0; rewrite (HFK2 r0 Hr0); exact (HFK r0 Hr0)).
  destruct (crt_live_journal HL2) as (WS_HJ2 & HJ2 & HB_HJ2). pose proof (crt_live_side HL2) as HSD2.
  pose proof (crt_side_ledger HSD2) as HLED2. pose proof (crt_side_doc_blocks HSD2) as HDL2.
  assert (HDR2 : dregsA regs2 F).
  { refine {| crt_dregs_bregs := {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _;
                crt_bregs_s1 := _; crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _;
                crt_bregs_s10 := _; crt_bregs_s11 := _ |}; crt_dregs_s5 := _ |};
    [ rewrite (ts_ap (ms_regs ms1) regs2 2%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 3%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 4%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 8%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 9%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 18%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 20%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 19%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 23%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 26%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 27%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 21%bv HP) by ts_cs ];
    rewrite !KR1 by (cbv; tauto); assumption. }
  assert (X24' : getr regs2 24 = w64 q) by (rewrite (ts_ap (ms_regs ms1) regs2 24%bv HP) by ts_cs; exact X24).
  assert (X22' : getr regs2 22 = w64 1)
    by (rewrite (ts_ap (ms_regs ms1) regs2 22%bv HP) by ts_cs; rewrite (KR1 22%bv) by (cbv; tauto); exact R22).
  assert (X25' : getr regs2 25 = w64 (VAL 315))
    by (rewrite (ts_ap (ms_regs ms1) regs2 25%bv HP) by ts_cs; exact X25).
  assert (HRA1 : forall off, range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + off) 56 ->
    range_addressable (aview SEGS (w_H Wc) (ms_mem ms1)) SHADOW_OFF (F + off) 56).
  { intros off H. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact H].
    intros y _. apply aview_eq_of. apply Hm01. }
  destruct (crt102rw_local_keep Wc W2 (ms_mem ms1) mem2 F CRT_OFF_BACK ltac:(lia) F32 Fb2 KSH2
    ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) as (LB2 & _).
  destruct (crt102rw_local_keep Wc W2 (ms_mem ms1) mem2 F CRT_OFF_V ltac:(lia) F32 Fb2 KSH2
    ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)) as (LV2 & _).
  assert (HDo : forall bk, In bk Do -> In bk Lamc).
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). right. apply in_or_app. left. exact Hbk. }
  assert (HAGm : forall X, pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)) X).
  { intros X y _. assert (E : mrestrict (w_H Wc) (ms_mem ms1) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y))
      by apply Hm01.
    split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
  assert (HcF : exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= F + CRT_OFF_COPY /\
    F + CRT_OFF_COPY + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0).
  { exists CRT_CID, pos. split; [exact Hin|]. rewrite crt102rw_fb. fold F. unfold CRT_OFF_COPY. lia. }
  pose proof (crt102rw_tree_call LAWS lyc Sc Hpc Wc (ms_mem ms1) _ kj _ _ ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc cntc 0
    Lamc peakc cntc 0 (F + CRT_OFF_COPY) (ck_crt_tree t) Do (proj1 HJ1) HJc HLED1 HLED2 HcF HDo HDo
    (fun a Hf => False_ind _ (inFP_nil a Hf))
    (pj_nodeR_frame SEGS _ _ _ (prh_lin Lamc) _ Do HNo (HAGm _))) as HNo2.
  (* copy's ORDERED free list, the same way (the run wrote nothing of it, the call's footprint is empty) *)
  assert (HFO2 : crt102rw_copy_fo W2 mem2 Lamc (F + CRT_OFF_COPY) Do).
  { destruct HFO as (Fc & HFc & HFce). exists Fc. split; [|exact HFce].
    exact (crt102rw_fo_call lyc Sc Hpc Wc (ms_mem ms1) _ kj _ _ ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc cntc 0
      Lamc peakc cntc 0 (F + CRT_OFF_COPY) DOC_D Do Fc (proj1 HJ1) HJc HLED1 HLED2 HcF HDo HDo
      (fun a Hf => False_ind _ (inFP_nil a Hf))
      (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Do Fc HFc (fun a k Hk => HDo (a, k) Hk)
        (HAGm _))). }
  pose proof (crt102rw_spills_keep Wc W2 (ms_mem ms1) mem2 ms KS2 (crt102rw_spills_agree Wc memc (ms_mem ms1) ms Hm01 HSP))
    as HSP2.
  pose proof (crt102rw_spill_keep HPRE Wc W2 (ms_mem ms1) mem2 CRT_SP_BACK (F + CRT_OFF_BACK) KS2
    ltac:(unfold CRT_SP_BACK; lia) ltac:(unfold CRT_SP_BACK; lia)
    (crt102rw_spill_keep HPRE Wc Wc memc (ms_mem ms1) CRT_SP_BACK _ (fun a _ => aview_eq_of _ _ _ _ _ (Hm01 _))
      ltac:(unfold CRT_SP_BACK; lia) ltac:(unfold CRT_SP_BACK; lia) VBACK)) as VBACK2.
  pose proof (crt102rw_bytes_call lyc Sc Hpc Wc (ms_mem ms1) _ _ _ ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc cntc 0
    Lamc peakc cntc 0 q cap (WriterValue.wdoc (ck_crt_tree t) true ++ [0]) HJc HLED1 HLED2 HqL HqL
    ltac:(rewrite length_app; cbn [length]; lia)
    (fun a Hf => False_ind _ (inFP_nil a Hf)) (crt102rw_bytes_agree Wc memc (ms_mem ms1) q _ Hm01 Hbytes)) as Hbytes2.
  apply (HG712 fx' ly2 Sc Hpc W2 mem2 md2 (kj + k1) pos Do Lamc peakc cntc regs2 ms c q cap ok); [|exact Ra0].
  unfold crt102rw_Rst. rewrite EF2.
  split; [exact HFZ2|]. split; [exact HFK3|]. split; [exact HL2|]. split; [exact HDR2|].
  split; [exact X24'|]. split; [exact X22'|]. split; [exact X25'|].
  split; [exact (LB2 (HRA1 _ HRAb))|]. split; [exact (LV2 (HRA1 _ HRAv))|]. split; [exact Et|].
  split; [exact HNo2|]. split; [exact HTBo|]. split; [exact Hdepc|]. split; [exact HFO2|]. split; [exact HSP2|].
  split; [exact VBACK2|].
  split; [exact Hq0|]. split; [exact Hlen|]. split; [exact Hcap32|]. split; [exact Hbytes2|].
  split; [exact Hc3|]. split; [exact Hcin|]. split; [exact Hoks|]. split; [exact Hwf|].
  split; [exact Ecap|]. split; [exact Ecnt|]. split; [exact HBS | exact HPOS].
Qed.

Definition crt102rw_G724 : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc rg ms c q cap ok,
  crt102rw_Rst fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc rg ms c q cap ok ->
  getr rg 10 = w64 (Z.of_nat (length (WriterValue.wdoc (ck_crt_tree t) true))) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk 724 rg memc mdc) QFa.

(* ---- +0x2c8 .. +0x2d0: `bnez a0` (g_ran_out = 0: not taken), `mv a0, s8`, `jal __wrap_strlen` (STRLEN, the libc
   row): the text q is NUL-terminated at q + len, len = |wdoc (ck_crt_tree t) true| (pj_write's bytes_at,
   no NUL inside by pj_wf), inside its harness block (q, cap) ---- *)
Lemma crt102rw_R712 : crt102rw_G724 -> crt102rw_G712.
Proof.
intros HG724 fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc rg ms c q cap ok HR R10.
pose proof HR as (HFZ & HFK & HL & HDR & R24 & R22 & R25 & HRAb & HRAv & Et & HNo & HTBo & Hdepc & HFO & HSP & VBACK & Hq0 &
  Hlen & Hcap32 & Hbytes & Hc3 & Hcin & Hoks & Hwf & Ecap & Ecnt & HBS & HPOS).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_sp (crt_dregs_bregs HDR)) as R2.
pose proof (crt_bregs_gp (crt_dregs_bregs HDR)) as R3.
pose proof (crt_bregs_tp (crt_dregs_bregs HDR)) as R4.
pose proof (crt_bregs_s0 (crt_dregs_bregs HDR)) as R8.
pose proof (crt_bregs_s1 (crt_dregs_bregs HDR)) as R9.
pose proof (crt_bregs_s2 (crt_dregs_bregs HDR)) as R18.
pose proof (crt_bregs_s4 (crt_dregs_bregs HDR)) as R20.
pose proof (crt_bregs_s3 (crt_dregs_bregs HDR)) as R19.
pose proof (crt_bregs_s7 (crt_dregs_bregs HDR)) as R23.
pose proof (crt_bregs_s10 (crt_dregs_bregs HDR)) as R26.
pose proof (crt_bregs_s11 (crt_dregs_bregs HDR)) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt102rw_sp HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof crt102rw_stkc as ESTK.
pose proof (YM05.alloc_ceiling_val) as Hcv.
set (F := frame_addr lyc CRT_CID pos) in *.
assert (HqL : In (q, cap) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
destruct (crt102rw_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ) HLED HqL) as (Hcap0 & Hq4096 & Hqc).
pose proof (cm_in_intro x t H0READ H0LENX H0WL0 H0WL1) as HIN.
destruct (crt102rw_P_entry fxk Wc memc rg 712 0 R10) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
pose proof HMNc as HPM.
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
unfold crt_cfg.
paj_run_tok_x_inv (RUN WS_HJ) HS HJ SHOK HPM (0, 0).
{ cbv [crt102rw_ssP ss_mem]. apply awr_ok_nil. }
assert (Hm01 : forall xw, mrestrict (w_H Wc) (ms_mem ms0) xw = mrestrict (w_H Wc) memc xw).
{ intros xw. apply HFr. intros (r & Hr & _). cbv [crt102rw_ssP ss_mem In] in Hr. destruct Hr. }
pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc memc (ms_mem ms0) mdc _ kj _ pos ((q, cap) :: Do) Lamc peakc
  cntc 0 0 HL HJ HB_HJ (fun xw _ => Hm01 xw) HPM) as HL1.
assert (KR1 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + 724))) by (rewrite Q1; vm_compute; reflexivity).
assert (X10 : getr (ms_regs ms0) 10 = w64 q).
{ rewrite Q10. assert (A : ew (TE regs rg []) 56 = getr rg 24) by te_close. rewrite A. exact R24. }
assert (HBR1 : bregsA (ms_regs ms0) F).
{ refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
            crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
            crt_bregs_s11 := _ |}; rewrite !KR1 by (cbv; tauto); assumption. }
destruct (crt_live_journal HL1) as (WS_HJ1 & HJ1 & HB_HJ1). pose proof (crt_live_side HL1) as HSD1.
pose proof (crt_side_ledger HSD1) as HLED1.
clear HF HG HFr.
(* the text as strlen's argument *)
pose proof (crt102rw_bytes_agree Wc memc (ms_mem ms0) q _ Hm01 Hbytes) as Hb1.
pose proof (cm_wdoc_pos _ (ck_crt_tree t) true (cm_in_crt_wf x t HIN)) as Hpos.
pose proof (crt102rw_text_sarg lyc Sc Hpc Wc (ms_mem ms0) _ Lamc peakc cntc SIZE_MAXZ 0 most 0 q cap
  (WriterValue.wdoc (ck_crt_tree t) true) (proj1 HJ1) HLED1 HqL Hlen Hcap32 Hb1 (crt102rw_text_nz Wc _ q _ Hb1 Hpos))
  as SARG.
apply (crt102rw_strlen_call fxk Wc (TE regs rg []) _ ms0 _ lyc Sc Hpc _ pos ((q, cap) :: Do) Lamc peakc cntc 0 0 724 q
  _ HS eq_refl eq_refl HL1 HBR1 X1 ltac:(lia) ltac:(reflexivity) X10 SARG).
intros regs2 mem2 md2 HL2 HP Ra0 Hfr Hpr2.
pose proof YM05.alloc_ceiling_lt as Hc47. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hlow : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. rewrite (Hfr a ltac:(lia) ltac:(lia)). apply aview_eq_of. apply Hm01. }
assert (Hhigh : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. rewrite (Hfr a ltac:(lia) ltac:(lia)). apply aview_eq_of. apply Hm01. }
assert (Hpr3 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem2 a).
{ intros a Ha. apply Hpr2. destruct Ha as [Hh [b Hb]]. split; [exact Hh|]. exists b.
  pose proof (Hm01 (Z_to_bv 64 a)) as E. unfold mrestrict in E. rewrite Hh in E. rewrite E. exact Hb. }
assert (HDR2 : dregsA regs2 F).
{ refine {| crt_dregs_bregs := {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _;
              crt_bregs_s1 := _; crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _;
              crt_bregs_s10 := _; crt_bregs_s11 := _ |}; crt_dregs_s5 := _ |};
  [ rewrite (ts_ap (ms_regs ms0) regs2 2%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 3%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 4%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 8%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 9%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 18%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 20%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 19%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 23%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 26%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 27%bv HP) by ts_cs
  | rewrite (ts_ap (ms_regs ms0) regs2 21%bv HP) by ts_cs ];
  rewrite !KR1 by (cbv; tauto); assumption. }
assert (X24' : getr regs2 24 = w64 q)
  by (rewrite (ts_ap (ms_regs ms0) regs2 24%bv HP) by ts_cs; rewrite (KR1 24%bv) by (cbv; tauto); exact R24).
assert (X22' : getr regs2 22 = w64 1)
  by (rewrite (ts_ap (ms_regs ms0) regs2 22%bv HP) by ts_cs; rewrite (KR1 22%bv) by (cbv; tauto); exact R22).
assert (X25' : getr regs2 25 = w64 (VAL 315))
  by (rewrite (ts_ap (ms_regs ms0) regs2 25%bv HP) by ts_cs; rewrite (KR1 25%bv) by (cbv; tauto); exact R25).
assert (HRA2 : forall off, 0 <= off -> off + 56 <= 512 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + off) 56 ->
  range_addressable (aview SEGS (w_H Wc) mem2) SHADOW_OFF (F + off) 56).
{ intros off Ho1 Ho2 H. apply (crt102rw_ra_keep (aview SEGS (w_H Wc) memc)); [|lia|lia|exact H].
  intros z Hz. apply Hlow. unfold SHADOW_OFF, kHighMemBeg in Hz. lia. }
assert (HNo2 : pj_nodeR SEGS (mrestrict (w_H Wc) mem2) (prh_lin Lamc) (F + CRT_OFF_COPY) (ck_crt_tree t) Do).
{ apply (pj_nodeR_frame SEGS _ _ _ (prh_lin Lamc) _ Do HNo). apply crt102rw_agree; [|exact Hpr3].
  intros z [Hz | ((a0 & k0) & Hb & Hz)]; apply Hlow.
  - unfold CRT_OFF_COPY in Hz. lia.
  - unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
    assert (Hb' : In (a0, k0) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); right; apply in_or_app; left; exact Hb).
    destruct (crt102rw_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ1) HLED1 Hb') as (_ & Ha & Hk).
    change (@cf_head CfParams_preset) with 16 in *. lia. }
(* copy's ORDERED free list, the same way: strlen wrote below s1 only *)
assert (HFO2 : crt102rw_copy_fo Wc mem2 Lamc (F + CRT_OFF_COPY) Do).
{ destruct HFO as (Fc & HFc & HFce). exists Fc. split; [|exact HFce].
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Do Fc HFc).
  { intros a0 k0 Hb. unfold prh_lin. apply (Permutation_in _ (Permutation_sym HPL)). right. apply in_or_app. left.
    exact Hb. }
  apply crt102rw_agree; [|exact Hpr3].
  intros z [Hz | ((a0 & k0) & Hb & Hz)]; apply Hlow.
  - unfold CRT_OFF_COPY in Hz. lia.
  - unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
    assert (Hb' : In (a0, k0) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); right; apply in_or_app; left; exact Hb).
    destruct (crt102rw_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ1) HLED1 Hb') as (_ & Ha & Hk).
    change (@cf_head CfParams_preset) with 16 in *. lia. }
pose proof (crt102rw_spills_keep Wc Wc memc mem2 ms Hhigh HSP) as HSP2.
pose proof (crt102rw_spill_keep HPRE Wc Wc memc mem2 CRT_SP_BACK (F + CRT_OFF_BACK) Hhigh
  ltac:(unfold CRT_SP_BACK; lia) ltac:(unfold CRT_SP_BACK; lia) VBACK) as VBACK2.
assert (Hbytes2 : bytes_at Wc mem2 q (WriterValue.wdoc (ck_crt_tree t) true ++ [0])).
{ unfold bytes_at, garr8 in *. intros j Hj. destruct (Hbytes j Hj) as (Hv & Hr0). split; [|exact Hr0].
  apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2 _ 1 _); [|exact Hv].
  intros i Hi. apply Hlow. rewrite length_app in Hj. cbn [length] in Hj.
  pose proof (@cf_head_nonneg CfParams_preset). lia. }
apply (HG724 fxk lyc Sc Hpc Wc mem2 md2 kj pos Do Lamc peakc cntc regs2 ms c q cap ok); [|exact Ra0].
unfold crt102rw_Rst.
split; [exact HFZ|]. split; [exact HFK|]. split; [exact HL2|]. split; [exact HDR2|].
split; [exact X24'|]. split; [exact X22'|]. split; [exact X25'|].
split; [exact (HRA2 CRT_OFF_BACK ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) HRAb)|].
split; [exact (HRA2 CRT_OFF_V ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) HRAv)|]. split; [exact Et|].
split; [exact HNo2|]. split; [exact HTBo|]. split; [exact Hdepc|]. split; [exact HFO2|]. split; [exact HSP2|].
split; [exact VBACK2|].
split; [exact Hq0|]. split; [exact Hlen|]. split; [exact Hcap32|]. split; [exact Hbytes2|].
split; [exact Hc3|]. split; [exact Hcin|]. split; [exact Hoks|]. split; [exact Hwf|].
split; [exact Ecap|]. split; [exact Ecnt|]. split; [exact HBS | exact HPOS].
Qed.

(* ---- THE STATE AT N (+0x2e4), parse_noting returned 0: the reading of pj_write's text was granted and gave back the
   rewritten tree at back over fresh blocks Dback; the room position is past the reading's events (L0's events next) ---- *)
Definition crt102rw_Nst (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Do Dback Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (c : nat) (q cap : Z) (ok okr : list bool)
  (tr : list PjGrammar.ev) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveA (prh_wk F_check_round_trip) lyc Sc Hpc Wc memc mdc kj pos (Dback ++ (q, cap) :: Do) Lamc peakc cntc 0 0 /\
  dregsA rg (frame_addr lyc CRT_CID pos) /\
  getr rg 10 = w64 0 /\ getr rg 24 = w64 q /\ getr rg 25 = w64 (VAL 315) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  t = PjTree.JObj ms /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) (ck_crt_tree t) Do /\
  Permutation (map (fun b => snd b + cf_head) Do) (PresetReqAtNoMiss.tblk (ck_crt_tree t)) /\
  (PjTree.depth (ck_crt_tree t) <= DOC_D)%nat /\
  crt102rw_copy_fo Wc memc Lamc (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Do /\
  crt102rw_spills Wc memc ms /\
  crt_spill (regs := regs) Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) /\
  q <> 0 /\ (c <= 3)%nat /\ (In ck_MOD_AT (map fst ms) -> c = 0%nat) /\
  prh_oks ok (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ
    (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
       (WriterValue.wdpieces (ck_crt_tree t) true))
    (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
       (WriterValue.wdpieces (ck_crt_tree t) true)) most 0 0 /\
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true)) = 0 /\
  cap = WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true)) /\
  PjGrammar.jr_run ReaderRes.jr_strtod (WriterValue.wdoc (ck_crt_tree t) true) okr = (Some (ck_crt_tree t), tr) /\
  prh_oks okr (WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true))) SIZE_MAXZ (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 0 /\
  cntc = WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
    (WriterValue.wdpieces (ck_crt_tree t) true)) + Z.of_nat (PjGrammar.calls tr) /\
  Z.of_nat (PjGrammar.calls tr) = ck_ncalls (WriterValue.wdoc (ck_crt_tree t) true) /\
  crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t) Sc (crt_evs_L0 ms) /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) (ck_crt_tree t) Dback /\
  Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk (ck_crt_tree t)) /\
  (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
   map (fun b => snd b + cf_head) Fb = PresetReqAt.fo (ck_crt_tree t)).
Definition crt102rw_G740 : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Do Dback Lamc peakc cntc rg ms c q cap ok okr tr,
  crt102rw_Nst fxk lyc Sc Hpc Wc memc mdc kj pos Do Dback Lamc peakc cntc rg ms c q cap ok okr tr ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_N_OFF rg memc mdc) QFa.

(* UNIV-END is RETIRED by the landing cut (commit 7cdbb61b5fa0): tparse_noting_specX no longer
   takes `In (text + len) DW` (the run-word list DW is gone; the closure's clause 4b holds the cursor free traces at
   every word), so the parse_noting call at +0x2e0 owes no membership of q + len.
   SRC-CEIL is RETIRED by the landing cut too: the cut's src_rd (PRH_Base.v:1652-1663) asks `p + |l| <= alloc_ceiling`
   (its third conjunct, :1660) with NO `+ 8`, and this site needs ONLY that new form: every reader of a src_rd window
   reads [p, p + len) only (src_rd's own comment, PRH_Base.v:1653-1659), and nothing at the site reads q + len. The
   call state gives it at EVERY len, len = 0
   included: the text lies in the LIVE harness block (q, cap) (In (q, cap) Lamc, with len < cap), and
   crt102rw_hblk_str gives q + len < alloc_ceiling from that block. So the old OPEN_K0_SRC_CEIL (`q + len + 8 <=
   alloc_ceiling`) is no longer read and is deleted; AR_laws_x field 24 alx_blocks_ceil8 is not used.
   THE WILD BUDGET AT parse_noting, the parse_noting TWIN of Crt102Arms.arms_wild_budget (and of
   Crt102B_RRT.crtb_wild_budget), RESTATED AT THE kb RE-SHAPE (brief
   the internal file wild-budget-kb-reshape.md, on the contract texts). The cut's tparse_noting_specX asks
   the room `wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot Sc)` (PRH_FnCheck.v:637) and posts
   fpostFbm .. (wbudget [] (prh_wk F_parse_noting)) (:648); through the Kit's budgeted call rule crt102rw_call_b
   (YCbqGwild.aj_call_xbF) the caller's journal after the call is at WS0 ++ WS1, WS0 the live state's budget and
   `wbudget [] (prh_wk F_parse_noting) WS1` the call's, and the callee's journal stays at WS1 (the Kit's call lemmas
   take it at any budget). The glue's crt_live now carries its budget kb and its journal at a budget WS with
   `wbudget [] kb WS`, so this Prop states, at every live state at a kb that leaves the call its 2 (kb + 2 <= 66 =
   prh_wk F_check_round_trip: the call state is at kb = 64, the brief's table), the room the text asks and the landing
   of the composed journal at kb + 2. It is a premise of crt102rw_R724 and crt102rw_chain, and it is DISCHARGED below
   by crt102rw_wild_budget_pn_goal (Qed) from the text's entry room HWR0 (YCbqGwild.ajournal_xw_room, wild_room_le,
   wbudget_app). *)
Definition crt102rw_wild_budget_pn : Prop :=
  forall (kb : nat) lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc,
  liveA kb lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (kb + prh_wk F_parse_noting <= prh_wk F_check_round_trip)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot Sc) /\
  (forall ly2 S2 Hp2 W2 mem2 md2 k1 (WS0 WS1 : list (list Z)),
     YCbqGwild.wbudget [] kb WS0 ->
     YCbqGwild.wbudget [] (prh_wk F_parse_noting) WS1 ->
     AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) (WS0 ++ WS1) ->
     exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS /\
       YCbqGwild.wbudget [] (kb + prh_wk F_parse_noting) WS).

(* ---- THE WILD BUDGET AT parse_noting, DISCHARGED (kb round): from the text's entry room HWR0 (PRH_FnCheck.v:1366).
   The room: the live state's journal is at a budget WS with wfresh [] WS <= kb, so the entry room 66 leaves
   66 - wfresh [] WS >= 66 - kb >= 2 at Sc (YCbqGwild.ajournal_xw_room, wild_room_le). The landing: the call rule's
   journal at WS0 ++ WS1 is at the budget kb + 2 (YCbqGwild.wbudget_app). ---- *)
Lemma crt102rw_wild_budget_pn_goal : crt102rw_wild_budget_pn.
Proof using HWR0.
unfold crt102rw_wild_budget_pn. intros kb lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc HL Hkb.
destruct (crt_live_journal HL) as (WS & HJ & HB). unfold YCbqGwild.wbudget in HB. split.
- apply (YCbqGwild.wild_room_le _ _ (prh_wk F_check_round_trip - YCbqGwild.wfresh [] WS)); [clear - HB Hkb; lia|].
  eapply YCbqGwild.ajournal_xw_roomR; [exact HJ | exact HWR0 | clear - HB Hkb; lia].
- intros ly2 S2 Hp2 W2 mem2 md2 k1 WS0 WS1 HB0 HB1 HJ2. exists (WS0 ++ WS1). split; [exact HJ2|].
  exact (YCbqGwild.wbudget_app [] kb (prh_wk F_parse_noting) WS0 WS1 HB0 HB1).
Qed.

(* the brief's arithmetic at the parse_noting call (prh_wk F_check_round_trip = 66 = 32 + 32 + 2, PRH_Base.v:151-160):
   the call state's 64 = prh_wk F_round_trip_text + prh_wk F_round_trip_text leaves the call its 2, and lands at 66 *)
Lemma crt102rw_kb_pn :
  (prh_wk F_round_trip_text + prh_wk F_round_trip_text + prh_wk F_parse_noting <= prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.

(* ---- +0x2d4 .. +0x2e0: `mv a1, a0; mv a0, s8; ld a2, 0x38(s1)` (&back), `jal parse_noting` (q, len, &back), and
   parse_noting's return at N (+0x2e4). THE OUTCOME, GRANTED: the text's own OUTCOME clause at the reading's position
   (crt_pos: the run's next events are the reading's, in the consumer window) and g_fail_at = SIZE_MAX give
   g_ran_out = 0 and the all-granted reading, which is the rewritten tree (PjRoundTrip.G9); its refused arm (rc = -1)
   is refuted here, so C4c (O2's out_of_memory () = 1) is unreachable from this cut. The call's wild room and the
   landing of the caller's journal at the budget 66 are crt102rw_wild_budget_pn, the first premise ---- *)
Lemma crt102rw_R724 : crt102rw_wild_budget_pn -> crt102rw_G740 -> crt102rw_G724.
Proof.
intros HWB HG740 fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc rg ms c q cap ok HR R10.
pose proof HR as (HFZ & HFK & HL & HDR & R24 & R22 & R25 & HRAb & HRAv & Et & HNo & HTBo & Hdepc & HFO & HSP & VBACK & Hq0 &
  Hlen & Hcap32 & Hbytes & Hc3 & Hcin & Hoks & Hwf & Ecap & Ecnt & HBS & HPOS).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_sp (crt_dregs_bregs HDR)) as R2.
pose proof (crt_bregs_gp (crt_dregs_bregs HDR)) as R3.
pose proof (crt_bregs_tp (crt_dregs_bregs HDR)) as R4.
pose proof (crt_bregs_s0 (crt_dregs_bregs HDR)) as R8.
pose proof (crt_bregs_s1 (crt_dregs_bregs HDR)) as R9.
pose proof (crt_bregs_s2 (crt_dregs_bregs HDR)) as R18.
pose proof (crt_bregs_s4 (crt_dregs_bregs HDR)) as R20.
pose proof (crt_bregs_s3 (crt_dregs_bregs HDR)) as R19.
pose proof (crt_bregs_s7 (crt_dregs_bregs HDR)) as R23.
pose proof (crt_bregs_s10 (crt_dregs_bregs HDR)) as R26.
pose proof (crt_bregs_s11 (crt_dregs_bregs HDR)) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt102rw_sp HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof crt102rw_stkc as ESTK.
pose proof (YM05.alloc_ceiling_val) as Hcv. pose proof YM05.alloc_ceiling_lt as Hc47.
set (F := frame_addr lyc CRT_CID pos) in *.
assert (HqL : In (q, cap) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
destruct (crt102rw_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ) HLED HqL) as (Hcap0 & Hq4096 & Hqc).
change (@cf_head CfParams_preset) with 16 in Hq4096.
pose proof (cm_in_intro x t H0READ H0LENX H0WL0 H0WL1) as HIN.
destruct (crt102rw_S_entry fxk Wc memc rg F R9 ltac:(lia) ltac:(lia) Hs1a R27 ltac:(lia) ltac:(lia) VBACK) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
pose proof HMNc as HPM.
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
unfold crt_cfg.
paj_run_tok_x_inv (RUN WS_HJ) HS HJ SHOK HPM (0, 0).
{ cbv [crt102rw_ssS ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (Hm01 : forall xw, mrestrict (w_H Wc) (ms_mem ms0) xw = mrestrict (w_H Wc) memc xw).
{ intros xw. apply HFr. intros (r & Hr & Ha). vm_compute in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc memc (ms_mem ms0) mdc _ kj _ pos ((q, cap) :: Do) Lamc peakc
  cntc 0 0 HL HJ HB_HJ (fun xw _ => Hm01 xw) HPM) as HL1.
assert (KR1 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
set (tb := WriterValue.wdoc (ck_crt_tree t) true) in *.
set (len := Z.of_nat (length tb)) in *.
assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + 740))) by (rewrite Q1; vm_compute; reflexivity).
assert (X10 : getr (ms_regs ms0) 10 = w64 q).
{ rewrite Q10. assert (A : ew (TE regs rg []) 56 = getr rg 24) by te_close. rewrite A. exact R24. }
assert (X11 : getr (ms_regs ms0) 11 = w64 len).
{ rewrite Q11. assert (A : ew (TE regs rg []) 42 = getr rg 10) by te_close. rewrite A. exact R10. }
assert (X12 : getr (ms_regs ms0) 12 = w64 (F + CRT_OFF_BACK)).
{ rewrite Q12. assert (A : ew (TE regs rg []) 59 = getr rg 27) by te_close. rewrite A, R27. unfold w64.
  rewrite unsigned_lit_small by lia. unfold CRT_OFF_BACK. reflexivity. }
assert (HBR1 : bregsA (ms_regs ms0) F).
{ refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
            crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
            crt_bregs_s11 := _ |}; rewrite !KR1 by (cbv; tauto); assumption. }
assert (HE2 : bv_unsigned (ew (TE regs rg []) 2) = sp0) by (rewrite (te_entry regs rg [] 2%bv 2) by reflexivity; reflexivity).
destruct (crt_live_journal HL1) as (WS_HJ1 & HJ1 & HB_HJ1). pose proof (crt_live_side HL1) as HSD1.
pose proof (crt_live_lam_perm HL1) as HPL1. pose proof (crt_live_blocks_perm HL1) as HPB1.
pose proof (crt_live_dx_apart HL1) as HAP1. pose proof (crt_live_memnorm HL1) as HMN1.
pose proof (crt_side_ledger HSD1) as HLED1. pose proof (crt_side_peak HSD1) as Hpk1.
pose proof (crt_side_room HSD1) as HROOM1. pose proof (crt_side_arodata HSD1) as HRO1.
pose proof (crt_side_doc HSD1) as HND1. pose proof (crt_side_doc_blocks HSD1) as HDL1.
clear HF HG HFr.
(* the call's facts *)
assert (HSTKp : 0 <= @STK_parse_noting prh_img_A /\ @STK_parse_noting prh_img_A + 240 <= STKC)
  by (rewrite ESTK; split; vm_compute; discriminate).
pose proof (cm_in_wlen_crt x t HIN) as (_ & _ & Hw40).
fold tb len in Hw40.
assert (Hb8 : (F + CRT_OFF_BACK) mod 8 = 0).
{ apply Z.mod_divide in F32; [|lia]. destruct F32 as [f Ef]. apply Z.mod_divide; [lia|].
  exists (4 * f + 4). unfold CRT_OFF_BACK. lia. }
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 H0LED) as (_ & _ & Hcntg & _).
set (cw := ck_cnt2 cnt t + 1 + Z.of_nat c) in *.
set (Pw := WriterValue.wdpieces (ck_crt_tree t) true) in *.
destruct (cm_pjw_cnt ok cw SIZE_MAXZ (ck_crt_tree t) true) as (Ewc & Hwc1 & Hwc2).
{ unfold cw. pose proof (cm_cnt_write x t ms (Z.of_nat c) cnt HIN Et ltac:(lia) ltac:(lia)). lia. }
{ unfold cw. pose proof (cm_cnt_write x t ms (Z.of_nat c) cnt HIN Et ltac:(lia) ltac:(lia)). lia. }
pose proof (cm_pjw_k_le ok cw SIZE_MAXZ (ck_crt_tree t) true ltac:(unfold cw; pose proof (cm_cnt_write x t ms (Z.of_nat c) cnt HIN Et ltac:(lia) ltac:(lia)); lia)) as Hk.
fold Pw in Ewc, Hwc1, Hwc2, Hk.
set (st' := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cw SIZE_MAXZ) Pw) in *.
pose proof (cm_cnt_noting x t ms (Z.of_nat c) cnt (Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cw SIZE_MAXZ) Pw))
  HIN Et ltac:(lia) ltac:(lia) ltac:(lia)) as Hcn.
fold tb in Hcn.
assert (Hncb : Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tb) <= 2 * len + 2).
{ pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod tb []) as G. unfold PjGrammar.ncalls in *. unfold len. lia. }
(* the reading's position and its next events (crt_pos at the call state: the cut's run, split) *)
pose proof (crt_pos_strtod HPOS) as Esm.
destruct (crt_pos_ex HPOS) as (pre & hist & HPOSa).
pose proof (crt_pos_split HPOSa) as Ert. pose proof (crt_pos_room HPOSa) as Hpos.
pose proof (crt_pos_run HPOSa) as Hrun0. pose proof (crt_pos_cons HPOSa) as Hcons0.
assert (Ecs : PresetReqAt.copy_set ms = ck_crt_tree t) by (rewrite Et; reflexivity).
rewrite Ecs in Hrun0, Hcons0, Ert. fold tb in Hrun0, Hcons0, Ert.
pose proof Hrun0 as HrunP. apply prh_run_at_app_iff in HrunP as [HrunP HrunL].
pose proof Hcons0 as HconsP. rewrite length_app in HconsP. apply prh_cons_from_app_iff in HconsP as [HconsP HconsL].
rewrite Esm in Hpos, HrunP, HconsP.
(* the text's room counts from that position *)
assert (HRSEC : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
{ unfold PresetLiveBounds.DRV.
  apply (crt102rw_pkR_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length pre)%nat rp_H0 hist Sc _ _ PresetLiveBounds.LSEC
    Hpos HrunP).
  - intros Hx k0. exact (PresetLiveSec.live_sec ReaderRes.jr_strtod rp_x rp_os k0 Hx).
  - rewrite PresetLiveBounds.LSEC_value. lia. }
assert (HR24 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tb [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ unfold PresetLiveBounds.DRV.
  apply (crt102rw_pkR_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length pre)%nat rp_H0 hist Sc _ _ PresetLiveBounds.L24
    Hpos HrunP).
  - intros Hx k0. exact (PresetLiveSec.live_c24 ReaderRes.jr_strtod rp_x rp_os k0 Hx).
  - rewrite PresetLiveBounds.L24_value. lia. }
(* the room: the check's blocks within LIVE_check_round_trip (Crt102Model's cm_live_read) *)
assert (Hroomr : blocks_bytes Sc + PRH_FnPj.LIVE_pj_parse tb <= LIVE_MAX).
{ apply (cm_live_read t (blocks_bytes S) (blocks_bytes Sc) H0LIVE).
  rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPB), bsum_app. lia. }
assert (Hfr : Z.of_nat (length (frames Sc)) <= ck_FRAMES_CAP - FR_parse_noting).
{ pose proof HJ1 as (_ & _ & _ & _ & _ & HFRc & _). rewrite HFRc. cbn [app length].
  assert (Hcap : ck_FRAMES_CAP - FR_check_round_trip + 1 <= ck_FRAMES_CAP - FR_parse_noting) by (vm_compute; discriminate).
  lia. }
pose proof (crt102rw_bytes_agree Wc memc (ms_mem ms0) q _ Hm01 Hbytes) as Hb1.
destruct (crt102rw_hblk_str lyc Sc Hpc Wc (ms_mem ms0) _ Lamc peakc cntc SIZE_MAXZ 0 most 0 q cap len (proj1 HJ1) HLED1 HqL
  ltac:(lia) Hlen) as (Hq0' & Hq63 & Hqc' & HAMRq & HRAq & HHVq & _).
assert (HRAb1 : range_addressable (aview SEGS (w_H Wc) (ms_mem ms0)) SHADOW_OFF (F + CRT_OFF_BACK) 56).
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAb]. intros y _. apply aview_eq_of. apply Hm01. }
(* the call's wild room and the caller's landing: crt102rw_wild_budget_pn at the call state (kb = 64) *)
destruct (HWB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL1 crt102rw_kb_pn) as [HWRpn HLANDpn].
assert (Hspz1 : spZ (ms_regs ms0) = sp1)
  by (unfold spZ; rewrite (KR1 2%bv) by (cbv; tauto); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the budgeted call rule (the callee's text posts its journal at wbudget [] (prh_wk F_parse_noting)) *)
refine (crt102rw_call_b LAWS HPRE fxk (@STK_parse_noting prh_img_A) [(F + CRT_OFF_BACK, F + CRT_OFF_BACK + 56)] 740
  (SIGMA AS_parse_noting) Wc (TE regs rg []) _ ms0 _ lyc Sc Hpc _ pos ((q, cap) :: Do) Lamc peakc cntc 0 0
  (prh_wk F_parse_noting) _ HFZ HS eq_refl eq_refl HE2 HL1 HBR1 X1 _ _ (proj1 HSTKp) (proj2 HSTKp) _ _ _).
- lia.
- reflexivity.
- (* the callee's footprint: back, inside the check's own class-3 frame *)
  intros a0 Hfa. apply inFP_cons in Hfa as [Hfa | Hfa]; [|exfalso; exact (inFP_nil a0 Hfa)].
  right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite crt102rw_fb. try unfold in_zr in Hfa. cbn [fst snd] in Hfa.
  fold F. unfold CRT_OFF_BACK in Hfa. lia.
- (* the callee: parse_noting's text (q, len, &back) *)
  intros ch1 HPRE1. eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
  + apply (PNOTING fxk most 0 lyc Sc Hpc Wc (ms_regs ms0) (ms_mem ms0) _ ch1 q tb (F + CRT_OFF_BACK) Lamc peakc cntc
      SIZE_MAXZ 0 HPRE1).
    * exact (HMN1 H0MN).
    * exact H0CL.
    * exact X10.
    * exact X11.
    * exact X12.
    * exact Hw40.
    * lia.
    * lia.
    * (* src_rd at q: the text's bytes, the block's bounds. Its third conjunct at the landing cut is the NEW form
         `q + |tb| <= alloc_ceiling` (PRH_Base.v:1660, no `+ 8`), and the site needs only it (no read at q + len). At
         every len, len = 0 included, the text's block (q, cap) is live (HqL) with len < cap (Hlen), and that block
         gives q + len < alloc_ceiling (crt102rw_hblk_str, Hqc') *)
      split.
      { unfold bytes_at in Hb1 |- *. apply garr8_app in Hb1 as [H0 _]. exact H0. }
      split; [lia|]. split; [unfold len in Hqc'; lia|]. split.
      { unfold YGcfStr.amem_range8 in HAMRq. unfold amem_range. lia. }
      split.
      { intros x0 Hx. apply HRAq. lia. }
      intros Hpos0. apply (crt102rw_hull_sub _ q (len + 1) q len); [exact HHVq | lia | lia | exact Hpos0].
    * (* prhReader_home by its first arm: kept_at in the ledger's harness block (q, cap) *)
      left. left. exists q, cap. split; [exact HqL | lia].
    * exact (cm_in_maxrun_crt x t HIN).
    * exact Hb8.
    * apply (crt102rw_back_ok lyc Sc Hpc Wc (ms_mem ms0) _ _ pos (ms_regs ms0) _ HJ1 HRAb1).
      unfold spZ. rewrite (KR1 2%bv) by (cbv; tauto). rewrite R2. unfold w64. rewrite unsigned_lit_small by lia.
      assert (Hsp : @STK_parse_noting prh_img_A <= 27632) by (vm_compute; discriminate). lia.
    * reflexivity.
    * exact HLED1.
    * rewrite Ecnt. fold st'. rewrite Ewc. lia.
    * exact Hroomr.
    * exact (cm_rq_read t H0RQ).
    * (* THE REQUEST BOUND AT THE parse_noting CALL: RQ_pj_parse tb is a term of RQA_crt t <= most *)
      exact (cm_rqa_read t most H0RQA).
    * exact Hfr.
    * unfold ck_frm0. exact HFZ.
    * exact HROOM1.
    * (* THE WILD ROOM the cut's text asks (PRH_FnCheck.v:637): crt102rw_wild_budget_pn *)
      exact HWRpn.
    * exact HRSEC.
    * exact HR24.
    * (* THE HULL BUDGET (the text's DRAFT premise, PRH_FnCheck.v:661): the reading's
         all-granted events are an infix of round_trip (crt_pos_split), so within one call's worth
         (crt102rw_hull_nt_rt); paid at the run position with the run's length bound HOS4
         (PresetHullPay.hull_budget_of_room_pos) *)
      pose proof Ert as Ert'. rewrite Esm in Ert'.
      destruct (crt102rw_hull_nt_rt ReaderRes.jr_strtod x t pre _ _ ltac:(unfold PresetReqAt.MAXB; lia) H0READ Ert')
        as (HNh & HTh).
      exact (PresetHullPay.hull_budget_of_room_pos ReaderRes.jr_strtod rp_x rp_os (rp_i + length pre)%nat rp_H0 hist Sc
        _ HOS4 Hpos HNh HTh).
  + (* the text's BUDGETED post (fpostFbm .. (wbudget [] (prh_wk F_parse_noting)), :648) is the budgeted call rule's
       callee post (fpostFbm unfolds to YCbqGwild.apost_base_xbFR at wle') *)
    intros W' c' _ HPo. exact HPo.
- (* the return at N (+0x2e4) *)
  intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS0 WS1 HFZ2 HFK2 HB0 HB1 HJe0 HJc HP (HQ & HMNk).
  (* the caller's journal at the budget 64 + 2 = prh_wk F_check_round_trip (crt102rw_wild_budget_pn's landing) *)
  pose proof (HLANDpn ly2 S2 Hp2 W2 mem2 md2 k1 WS0 WS1 HB0 HB1 HJe0) as HJe.
  destruct HQ as (_ & HRL2 & Lam' & peak' & cnt' & fail' & ran' & okr & res & tr & Hrun & _ & _ & Hout & Hoksr & Hcnt' &
    Hfa & Hpk' & _ & _ & _ & Hread & _ & HL2 & Hres).
  assert (HFK3 : fregs_kept_x fx fx') by (intros r0 Hr0; rewrite (HFK2 r0 Hr0); exact (HFK r0 Hr0)).
  (* THE OUTCOME, GRANTED *)
  assert (Hfc : SIZE_MAXZ < cntc \/ cntc + ck_ncalls tb <= SIZE_MAXZ).
  { right. unfold ck_ncalls. rewrite Ecnt, Ewc.
    unfold cw, len in *. assert (ES : SIZE_MAXZ = 2 ^ 64 - 1) by reflexivity. lia. }
  destruct (Hout ReaderRes.jr_strtod rp_x rp_os (rp_i + length pre)%nat rp_H0 hist Hpos HrunP HconsP Hfc)
    as (E0 & Hjr0 & _ & hist3 & Hpos3).
  destruct (Hread E0 Hfc) as (Eres & Ecalls).
  pose proof (cm_read_crt x t true HIN) as Ecr. fold tb in Ecr. rewrite Ecr in Eres. subst res. subst ran'.
  assert (Efail : fail' = SIZE_MAXZ).
  { destruct Hfa as [Fa1 Fa2]. destruct (Z_lt_le_dec SIZE_MAXZ (cntc + Z.of_nat (PjGrammar.calls tr))) as [Hgt | Hle].
    - rewrite Fa1 by (rewrite Ecnt, Ewc; unfold SIZE_MAXZ in *; lia). reflexivity.
    - apply Fa2. lia. }
  subst fail'.
  (* the Some arm at the landing cut: back's tree and, beside it, its capacities (CAP, pj_ncapR), not read here *)
  destruct Hres as (R10' & D' & HLD & _ & _ & HrdD & HfoD & HnewD & HabD & HnodeD & _).
  pose proof (cm_in_crt_wf x t HIN) as Hwfc.
  assert (Ertr : PresetReqAt.rtr ReaderRes.jr_strtod okr tb = PresetReqAt.rtr ReaderRes.jr_strtod [] tb).
  { unfold PresetReqAt.rtr. rewrite Hrun, Hjr0. reflexivity. }
  assert (Efrees : PresetReqAt.pj_frees ReaderRes.jr_strtod okr tb = PresetReqAt.fo (ck_crt_tree t)).
  { rewrite (crt102rw_pj_frees_agree ReaderRes.jr_strtod tb okr (crt102rw_ok_upto_some _ _ _ _ _ Hrun)).
    exact (PresetFreeFo.pj_frees_wdoc_t ReaderRes.jr_strtod (ck_crt_tree t) true Hwfc). }
  assert (HHEAD : @cf_head CfParams_preset = PresetReqAt.HEAD) by reflexivity.
  (* the live state after the call: back's blocks D' on top of the check's *)
  assert (HFP0 : Forall (fun r => 0 < fst r) [(F + CRT_OFF_BACK, F + CRT_OFF_BACK + 56)])
    by (constructor; [cbn [fst]; unfold CRT_OFF_BACK; lia | constructor]).
  assert (HFPD : forall a, inFP [(F + CRT_OFF_BACK, F + CRT_OFF_BACK + 56)] a -> ~ pj_footR doc D a).
  { intros a0 Hf. apply inFP_cons in Hf as [Hf | Hf]; [|exfalso; exact (inFP_nil a0 Hf)].
    try unfold in_zr in Hf. cbn [fst snd] in Hf.
    exact (crt102rw_local_off_doc LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms0) _ _ pos _ Lamc peakc cntc 0 0 CRT_OFF_BACK a0
      HL1 ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) ltac:(fold F; unfold CRT_OFF_BACK in *; lia)). }
  assert (HFP3 : forall a, inFP [(F + CRT_OFF_BACK, F + CRT_OFF_BACK + 56)] a ->
    a < YM05.alloc_ceiling /\ in_app a 1 /\ ~ (F + 504 <= a < F + 512)).
  { intros a0 Hf. apply inFP_cons in Hf as [Hf | Hf]; [|exfalso; exact (inFP_nil a0 Hf)].
    try unfold in_zr in Hf. cbn [fst snd] in Hf. unfold CRT_OFF_BACK in Hf.
    split; [lia|]. split; [apply (in_app_sub _ _ _ _ Fb3); lia | lia]. }
  assert (Hpk2 : peakc <= peak') by (rewrite Hpk'; lia).
  assert (HDL3 : forall bk, In bk D -> In bk Lam').
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HLD)). apply in_or_app. right. exact (HDL1 _ Hbk). }
  pose proof (crt102rw_side_call LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms0) _ _ pos ((q, cap) :: Do) Lamc peakc cntc 0 0
    _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lam' peak' cnt' 0 0 HL1 HJc HFP0 HFPD HL2 Hpk2 HRL2 HDL3) as HSD2.
  assert (HPL2 : Permutation Lam' ((D' ++ (q, cap) :: Do) ++ Lam)).
  { rewrite <- app_assoc. eapply Permutation_trans; [exact HLD|]. apply Permutation_app_head. exact HPL1. }
  assert (HPB2 : Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks (D' ++ (q, cap) :: Do))).
  { eapply Permutation_trans; [exact HabD|]. eapply Permutation_trans; [apply Permutation_app_tail; exact HPB1|].
    unfold ck_hblks. rewrite map_app. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
  assert (HrelD : forall a' k', In (a', k') (D' ++ (q, cap) :: Do) ->
    In (a', k') ((q, cap) :: Do) \/ ~ In (a' - cf_head, k' + cf_head) (ablocks B lyc Sc)).
  { intros a' k' Hx. apply in_app_or in Hx as [Hx | Hx]; [right; exact (HnewD a' k' Hx) | left; exact Hx]. }
  pose proof (crt102rw_apart_step lyc Sc Hpc Wc (ms_mem ms0) _ _ pos ((q, cap) :: Do) Lamc peakc cntc 0 0 _ HL1 HrelD)
    as HAP2.
  pose proof (crt102rw_live_call LAWS HPRE lyc Sc Hpc Wc (ms_mem ms0) _ _ pos ((q, cap) :: Do) Lamc peakc cntc 0 0 _ _
    ly2 S2 Hp2 W2 mem2 md2 k1 (D' ++ (q, cap) :: Do) Lam' peak' cnt' 0 0 HL1 HJe HJc (proj1 HSTKp) HFP3 HSD2 HPL2 HPB2
    HAP2 HMNk) as HL3.
  destruct (crt102rw_call_keep LAWS HPRE lyc Sc Hpc Wc (ms_mem ms0) _ _ pos _ _ ly2 S2 Hp2 W2 mem2 md2 k1 HJ1 HJc
    (fun a0 Hf => conj (proj1 (HFP3 a0 Hf)) (proj1 (proj2 (HFP3 a0 Hf))))) as (EF2 & KS2 & KSH2).
  fold F in EF2, KSH2.
  (* the registers the callee keeps *)
  assert (HDR2 : dregsA regs2 F).
  { refine {| crt_dregs_bregs := {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _;
                crt_bregs_s1 := _; crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _;
                crt_bregs_s10 := _; crt_bregs_s11 := _ |}; crt_dregs_s5 := _ |};
    [ rewrite (ts_ap (ms_regs ms0) regs2 2%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 3%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 4%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 8%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 9%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 18%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 20%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 19%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 23%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 26%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 27%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs2 21%bv HP) by ts_cs ];
    rewrite !KR1 by (cbv; tauto); assumption. }
  assert (X24' : getr regs2 24 = w64 q)
    by (rewrite (ts_ap (ms_regs ms0) regs2 24%bv HP) by ts_cs; rewrite (KR1 24%bv) by (cbv; tauto); exact R24).
  assert (X25' : getr regs2 25 = w64 (VAL 315))
    by (rewrite (ts_ap (ms_regs ms0) regs2 25%bv HP) by ts_cs; rewrite (KR1 25%bv) by (cbv; tauto); exact R25).
  (* the locals open, the spills, copy's tree: off back, which is all the call writes *)
  assert (HRAv1 : range_addressable (aview SEGS (w_H Wc) (ms_mem ms0)) SHADOW_OFF (F + CRT_OFF_V) 56).
  { apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAv]. intros y _. apply aview_eq_of. apply Hm01. }
  destruct (crt102rw_local_keep Wc W2 (ms_mem ms0) mem2 F CRT_OFF_BACK ltac:(lia) F32 Fb2 KSH2
    ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) as (LB2 & _).
  destruct (crt102rw_local_keep Wc W2 (ms_mem ms0) mem2 F CRT_OFF_V ltac:(lia) F32 Fb2 KSH2
    ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)) as (LV2 & _).
  assert (HDo : forall bk, In bk Do -> In bk Lamc).
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL1)). right. apply in_or_app. left. exact Hbk. }
  assert (HDo2 : forall bk, In bk Do -> In bk Lam').
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HLD)). apply in_or_app. right. exact (HDo _ Hbk). }
  assert (HAGm : forall X, pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms0)) X).
  { intros X y _. assert (E : mrestrict (w_H Wc) (ms_mem ms0) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y))
      by apply Hm01.
    split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
  assert (HcF : exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= F + CRT_OFF_COPY /\
    F + CRT_OFF_COPY + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0).
  { exists CRT_CID, pos. split; [exact Hin|]. rewrite crt102rw_fb. fold F. unfold CRT_OFF_COPY. lia. }
  assert (HFPoff : forall a, inFP [(F + CRT_OFF_BACK, F + CRT_OFF_BACK + 56)] a -> ~ pj_footR (F + CRT_OFF_COPY) Do a).
  { intros a0 Hf. apply inFP_cons in Hf as [Hf | Hf]; [|exfalso; exact (inFP_nil a0 Hf)].
    try unfold in_zr in Hf. cbn [fst snd] in Hf.
    exact (crt102rw_local_off_tree LAWS lyc Sc Hpc Wc (ms_mem ms0) _ _ pos _ Lamc peakc cntc 0 0 CRT_OFF_BACK
      (F + CRT_OFF_COPY) Do a0 HL1 HDo ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)
      ltac:(right; unfold CRT_OFF_BACK, CRT_OFF_COPY; lia) ltac:(fold F; unfold CRT_OFF_BACK in *; lia)). }
  pose proof (crt102rw_tree_call LAWS lyc Sc Hpc Wc (ms_mem ms0) _ kj _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc 0
    Lam' peak' cnt' 0 (F + CRT_OFF_COPY) (ck_crt_tree t) Do (proj1 HJ1) HJc HLED1 HL2 HcF HDo HDo2 HFPoff
    (pj_nodeR_frame SEGS _ _ _ (prh_lin Lamc) _ Do HNo (HAGm _))) as HNo2.
  (* copy's ORDERED free list, the same way (parse_noting's footprint is back, off copy) *)
  assert (HFO2 : crt102rw_copy_fo W2 mem2 Lam' (F + CRT_OFF_COPY) Do).
  { destruct HFO as (Fc & HFc & HFce). exists Fc. split; [|exact HFce].
    exact (crt102rw_fo_call lyc Sc Hpc Wc (ms_mem ms0) _ kj _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc 0
      Lam' peak' cnt' 0 (F + CRT_OFF_COPY) DOC_D Do Fc (proj1 HJ1) HJc HLED1 HL2 HcF HDo HDo2 HFPoff
      (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Do Fc HFc (fun a k Hk => HDo (a, k) Hk)
        (HAGm _))). }
  pose proof (crt102rw_spills_keep Wc W2 (ms_mem ms0) mem2 ms KS2 (crt102rw_spills_agree Wc memc (ms_mem ms0) ms Hm01 HSP))
    as HSP2.
  pose proof (crt102rw_spill_keep HPRE Wc W2 (ms_mem ms0) mem2 CRT_SP_BACK (F + CRT_OFF_BACK) KS2
    ltac:(unfold CRT_SP_BACK; lia) ltac:(unfold CRT_SP_BACK; lia)
    (crt102rw_spill_keep HPRE Wc Wc memc (ms_mem ms0) CRT_SP_BACK _ (fun a _ => aview_eq_of _ _ _ _ _ (Hm01 _))
      ltac:(unfold CRT_SP_BACK; lia) ltac:(unfold CRT_SP_BACK; lia) VBACK)) as VBACK2.
  (* back's blocks against tblk (the all-granted reading's rd_blocks, PresetFreeFo.rd_blocks_wdoc, fo_tblk) *)
  assert (HTBb : Permutation (map (fun b => snd b + cf_head) D') (PresetReqAtNoMiss.tblk (ck_crt_tree t))).
  { pose proof (HrdD HHEAD) as H1. rewrite Ertr in H1.
    eapply Permutation_trans; [exact H1|].
    eapply Permutation_trans; [exact (PresetFreeFo.rd_blocks_wdoc ReaderRes.jr_strtod (ck_crt_tree t) true Hwfc)|].
    apply PresetReqAtNoMiss.fo_tblk. }
  apply (HG740 fx' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Do D' Lam' peak' cnt' regs2 ms c q cap ok okr tr).
  unfold crt102rw_Nst. rewrite EF2.
  split; [exact HFZ2|]. split; [exact HFK3|]. split; [exact HL3|]. split; [exact HDR2|].
  split; [exact R10'|]. split; [exact X24'|]. split; [exact X25'|].
  split; [exact (LB2 HRAb1)|]. split; [exact (LV2 HRAv1)|]. split; [exact Et|].
  split; [exact HNo2|]. split; [exact HTBo|]. split; [exact Hdepc|]. split; [exact HFO2|]. split; [exact HSP2|].
  split; [exact VBACK2|].
  split; [exact Hq0|]. split; [exact Hc3|]. split; [exact Hcin|]. split; [exact Hoks|]. split; [exact Hwf|].
  split; [exact Ecap|]. split; [exact Hrun|].
  split; [rewrite Ecnt in Hoksr; exact Hoksr|].
  split; [rewrite Hcnt', Ecnt; reflexivity|].
  split; [exact Ecalls|].
  split.
  { refine {| crt_pos_strtod := Esm; crt_pos_ex := _ |}.
    exists (pre ++ PresetReqAt.parse_evs rp_sm tb []), hist3.
    refine {| crt_pos_split := _; crt_pos_room := _; crt_pos_run := _; crt_pos_cons := _ |}.
    { rewrite Ert, app_assoc. reflexivity. }
    { rewrite length_app, Nat.add_assoc. rewrite Esm. exact Hpos3. }
    { rewrite length_app, Nat.add_assoc. exact HrunL. }
    { rewrite length_app, Nat.add_assoc. exact HconsL. } }
  split; [exact HnodeD|]. split; [exact HTBb|].
  destruct (HfoD HHEAD DOC_D Hdepc) as (Fb & HF1 & HF2).
  exists Fb. split; [exact HF1 | rewrite HF2; exact Efrees].
Qed.

(* ---- N (+0x2e4) .. L0 (+0x470): `snez s6, a0` (rc = 0: s6 = 0), the second out_of_memory (): `lbu a0, -0x5b0(s9)`
   (g_own_ran_out = 0), `jal fuzz_alloc_ran_out` (g_ran_out = 0: the reading was granted), `beqz a0` -> L0. Arm C4c
   (+0x2f8, fuzz_free (saved)) is not reached from here ---- *)
Lemma crt102rw_R740 : crt102rw_L0K -> crt102rw_G740.
Proof.
intros HL0K fxk lyc Sc Hpc Wc memc mdc kj pos Do Dback Lamc peakc cntc rg ms c q cap ok okr tr HN.
pose proof HN as (HFZ & HFK & HL & HDR & R10 & R24 & R25 & HRAb & HRAv & Et & HNo & HTBo & Hdepc & (Fc & HFc & HFce) & HSP &
  VBACK & Hq0 &
  Hc3 & Hcin & Hoks & Hwf & Ecap & Hrunr & Hoksr & Ecnt & Ecalls & HPOS & HNb & HTBb & HFb).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_sp (crt_dregs_bregs HDR)) as R2.
pose proof (crt_bregs_gp (crt_dregs_bregs HDR)) as R3.
pose proof (crt_bregs_tp (crt_dregs_bregs HDR)) as R4.
pose proof (crt_bregs_s0 (crt_dregs_bregs HDR)) as R8.
pose proof (crt_bregs_s1 (crt_dregs_bregs HDR)) as R9.
pose proof (crt_bregs_s2 (crt_dregs_bregs HDR)) as R18.
pose proof (crt_bregs_s4 (crt_dregs_bregs HDR)) as R20.
pose proof (crt_bregs_s3 (crt_dregs_bregs HDR)) as R19.
pose proof (crt_bregs_s7 (crt_dregs_bregs HDR)) as R23.
pose proof (crt_bregs_s10 (crt_dregs_bregs HDR)) as R26.
pose proof (crt_bregs_s11 (crt_dregs_bregs HDR)) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt102rw_sp HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof crt102rw_stkc as ESTK.
pose proof (YM05.alloc_ceiling_val) as Hcv.
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (crt102rw_ownN_entry fxk Wc memc rg 0 ltac:(eapply PRH_Base.prh_ledger_own; exact HLED) R10 R25) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
pose proof HMNc as HPM.
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
unfold crt_cfg.
paj_run_tok_x_inv (RUN WS_HJ) HS HJ SHOK HPM (0, 0).
{ cbv [crt102rw_ssOwnN ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (Hm01 : forall xw, mrestrict (w_H Wc) (ms_mem ms0) xw = mrestrict (w_H Wc) memc xw).
{ intros xw. apply HFr. intros (r & Hr & Ha). vm_compute in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc memc (ms_mem ms0) mdc _ kj _ pos (Dback ++ (q, cap) :: Do)
  Lamc peakc cntc 0 0 HL HJ HB_HJ (fun xw _ => Hm01 xw) HPM) as HL1.
assert (KR1 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
prreg HS (1%bv : bv 5) Q1. prreg HS (22%bv : bv 5) Q22.
assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + 756))) by (rewrite Q1; vm_compute; reflexivity).
assert (X22 : getr (ms_regs ms0) 22 = w64 0) by (rewrite Q22; reflexivity).
assert (HBR1 : bregsA (ms_regs ms0) F).
{ refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
            crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
            crt_bregs_s11 := _ |}; rewrite !KR1 by (cbv; tauto); assumption. }
assert (HE2 : bv_unsigned (ew (TE regs rg []) 2) = sp0) by (rewrite (te_entry regs rg [] 2%bv 2) by reflexivity; reflexivity).
destruct (crt_live_journal HL1) as (WS_HJ1 & HJ1 & HB_HJ1). pose proof (crt_live_side HL1) as HSD1.
pose proof (crt_live_lam_perm HL1) as HPL1.
pose proof (crt_side_ledger HSD1) as HLED1. pose proof (crt_side_doc_blocks HSD1) as HDL1.
clear HF HG HFr.
apply (crt102rw_ranout_call fxk Wc (TE regs rg []) _ ms0 _ lyc Sc Hpc _ pos (Dback ++ (q, cap) :: Do) Lamc peakc cntc 0
  756 HFZ HS eq_refl eq_refl HE2 HL1 HBR1 X1 ltac:(lia) ltac:(reflexivity)).
intros fx' ly2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HL2 HJc HP Ra0 EF2 KS2 KSH2.
assert (HFK3 : fregs_kept_x fx fx') by (intros r0 Hr0; rewrite (HFK2 r0 Hr0); exact (HFK r0 Hr0)).
destruct (crt_live_journal HL2) as (WS_HJ2 & HJ2 & HB_HJ2). pose proof (crt_live_side HL2) as HSD2.
pose proof (crt_live_memnorm HL2) as HMN2.
pose proof (crt_side_ledger HSD2) as HLED2.
assert (KP : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv ->
  getr regs2 r = getr (ms_regs ms0) r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [apply (ts_ap (ms_regs ms0) regs2 _ HP); ts_cs |]). destruct Hr. }
(* +0x2f4: `beqz a0` with g_ran_out = 0 pinned: taken, to L0 *)
destruct (crt102rw_P_entry fx' W2 mem2 regs2 756 0 Ra0) as [HS2 SHOK2].
assert (HEI2 : img_env VAL A_LIM (TE regs regs2 [])) by apply te_env.
pose (RUNTO := @crt_run_to_xw_inv fx' rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
unfold crt_cfg.
paj_run_to_tok_x_inv (RUNTO WS_HJ2) HS2 HJ2 SHOK2 HMN2 (0, 0) (CRT_PC_A + CRT_L0_OFF).
{ cbv [crt102rw_ssP ss_mem]. apply awr_ok_nil. }
assert (Hm23 : forall xw, mrestrict (w_H W2) (ms_mem ms1) xw = mrestrict (w_H W2) mem2 xw).
{ intros xw. apply HFr. intros (r & Hr & _). cbv [crt102rw_ssP ss_mem In] in Hr. destruct Hr. }
pose proof (crt102rw_live_run LAWS HPRE HTREE ly2 Sc Hpc W2 mem2 (ms_mem ms1) md2 _ (kj + k1) _ pos (Dback ++ (q, cap) :: Do)
  Lamc peakc cntc 0 0 HL2 HJ2 HB_HJ2 (fun xw _ => Hm23 xw) HMN2) as HL3.
assert (KR3 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv ->
  getr (ms_regs ms1) r = getr regs2 r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS2 |]). destruct Hr. }
clear HF HG HFr.
pmkst HS2.
lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
  change n with (CRT_PC_A + CRT_L0_OFF) end.
(* the memory at L0 against the N state: the two runs wrote nothing, the call's footprint is empty *)
destruct (crt_live_journal HL3) as (WS_HJ3 & HJ3 & HB_HJ3). pose proof (crt_live_side HL3) as HSD3.
pose proof (crt_side_ledger HSD3) as HLED3.
assert (HcF : forall off, 0 <= off -> off + 56 <= 512 -> exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
  frame_addr lyc cid0 pos0 <= F + off /\ F + off + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0).
{ intros off H1 H2. exists CRT_CID, pos. split; [exact Hin|]. rewrite crt102rw_fb. fold F. lia. }
assert (HDo : forall bk, In bk Do -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. right.
  right. exact Hbk. }
assert (HDb : forall bk, In bk Dback -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. left. exact Hbk. }
assert (AGF : forall off Dt, 0 <= off -> off + 56 <= 512 -> (forall bk, In bk Dt -> In bk Lamc) ->
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) (ms_mem ms1)) (pj_footR (F + off) Dt)).
{ intros off Dt Ho1 Ho2 HDt y Hy.
  destruct (crt102rw_agree_eq (w_H Wc) memc (ms_mem ms0) (pj_footR (F + off) Dt) Hm01 y Hy) as (A1 & A2).
  destruct (crt102rw_foot_call lyc Sc Hpc Wc (ms_mem ms0) _ _ _ ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc cntc 0
    Lamc peakc cntc 0 (F + off) Dt (proj1 HJ1) HJc HLED1 HLED2 (HcF off Ho1 Ho2) HDt HDt
    (fun a0 Hf => False_ind _ (inFP_nil a0 Hf)) y Hy) as (B1 & B2).
  destruct (crt102rw_agree_eq (w_H W2) mem2 (ms_mem ms1) (pj_footR (F + off) Dt) Hm23 y Hy) as (C1' & C2').
  split; [rewrite C1', B1, A1; reflexivity | intros Hw; exact (C2' (B2 (A2 Hw)))]. }
assert (Hlow : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. rewrite (aview_eq_of _ _ _ _ _ (Hm23 _)), (KS2 a Ha). apply aview_eq_of. apply Hm01. }
assert (Hsh : forall a, shadow_addr F <= a < shadow_addr F + 64 ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. rewrite (aview_eq_of _ _ _ _ _ (Hm23 _)), (KSH2 a Ha). apply aview_eq_of. apply Hm01. }
destruct (crt102rw_local_keep Wc W2 memc (ms_mem ms1) F CRT_OFF_BACK ltac:(lia) F32 Fb2 Hsh
  ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) as (LB3 & _).
destruct (crt102rw_local_keep Wc W2 memc (ms_mem ms1) F CRT_OFF_V ltac:(lia) F32 Fb2 Hsh
  ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)) as (LV3 & _).
pose proof (crt102rw_spills_keep Wc W2 memc (ms_mem ms1) ms Hlow HSP) as (VSH & VPN & VN).
pose proof (crt102rw_spill_keep HPRE Wc W2 memc (ms_mem ms1) CRT_SP_BACK (F + CRT_OFF_BACK) Hlow
  ltac:(unfold CRT_SP_BACK; lia) ltac:(unfold CRT_SP_BACK; lia) VBACK) as VBACK3.
assert (HNo3 : pj_nodeR SEGS (mrestrict (w_H W2) (ms_mem ms1)) (prh_lin Lamc) (F + CRT_OFF_COPY) (ck_crt_tree t) Do)
  by exact (pj_nodeR_frame SEGS _ _ _ (prh_lin Lamc) _ Do HNo
    (AGF CRT_OFF_COPY Do ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) HDo)).
assert (HNb3 : pj_nodeR SEGS (mrestrict (w_H W2) (ms_mem ms1)) (prh_lin Lamc) (F + CRT_OFF_BACK) (ck_crt_tree t) Dback)
  by exact (pj_nodeR_frame SEGS _ _ _ (prh_lin Lamc) _ Dback HNb
    (AGF CRT_OFF_BACK Dback ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) HDb)).
pose proof (crt102rw_home_keep LAWS HPRE HTREE _ _ _ _ _ _ _ _ HJ3) as (_ & _ & HRAdoc).
pose proof (crt102rw_doc_home LAWS HPRE HTREE) as (_ & _ & _ & Hd8).
assert (Ecw : crt_cw (t := t) (cnt := cnt) (Z.of_nat c) = ck_cnt2 cnt t + 1 + Z.of_nat c)
  by (unfold crt_cw; rewrite cm_cnt2_eq; lia).
pose proof (cm_in_intro x t H0READ H0LENX H0WL0 H0WL1) as HIN.
apply (HL0K fx' ly2 Sc Hpc W2 (ms_mem ms1) _ (kj + k1) pos Do (Dback ++ (q, cap) :: Do) Lamc peakc cntc (ms_regs ms1) ms
  (Z.of_nat c) q 0).
assert (EJ : crt_tree_J (t := t) = ck_crt_tree t) by (unfold crt_tree_J; rewrite Et; reflexivity).
refine {| crt_at_L0_obj := _; crt_at_L0_frm_zero := _; crt_at_L0_fregs := _; crt_at_L0_live := _;
          crt_at_L0_dregs := _; crt_at_L0_saved := _; crt_at_L0_flag := _; crt_at_L0_sp_back := _;
          crt_at_L0_sp_shn := _; crt_at_L0_sp_pn := _; crt_at_L0_sp_n := _; crt_at_L0_doc_align := _;
          crt_at_L0_doc_open := _; crt_at_L0_back_open := _; crt_at_L0_v_open := _;
          crt_at_L0_cset_range := _; crt_at_L0_cset_mod := _; crt_at_L0_copy := _;
          crt_at_L0_copy_fd := _; crt_at_L0_copy_tblk := _; crt_at_L0_copy_fo := _;
          crt_at_L0_copy_depth := _; crt_at_L0_outcome := _ |}.
{ exact Et. }
{ exact HFZ2. }
{ exact HFK3. }
{ exact HL3. }
{ rewrite EF2.
  refine {| crt_dregs_bregs := {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _;
                crt_bregs_s1 := _; crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _;
                crt_bregs_s10 := _; crt_bregs_s11 := _ |}; crt_dregs_s5 := _ |};
  rewrite !KR3 by (cbv; tauto); rewrite !KP by (cbv; tauto); rewrite !KR1 by (cbv; tauto); assumption. }
{ rewrite KR3, KP, KR1 by (cbv; tauto). exact R24. }
{ rewrite KR3, KP by (cbv; tauto). rewrite X22. rewrite (proj2 (Z.eqb_neq q 0) Hq0). reflexivity. }
{ rewrite EF2. exact VBACK3. }
{ exact VSH. }
{ exact VPN. }
{ exact VN. }
{ exact Hd8. }
{ exact HRAdoc. }
{ rewrite EF2. exact (LB3 HRAb). }
{ rewrite EF2. exact (LV3 HRAv). }
{ lia. }
{ intros Hi. rewrite (Hcin Hi). reflexivity. }
{ rewrite EF2. exact HNo3. }
{ rewrite EF2.
  apply (crt102rw_fdR_mono SEGS _ _ (PjTree.depth (ck_crt_tree t))); [exact Hdepc|].
  exact (crt102rw_nodeR_fdR SEGS _ _ _ _ _ HNo3). }
{ rewrite EJ. exact HTBo. }
{ (* FREEORD-COPY at N (crt102rw_Nst's copy-order field, from pj_set's result order at K), framed to L0 *)
  rewrite EF2, EJ.
  exists Fc. rewrite EJ in HFce. split; [|exact HFce].
  exact (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) (F + CRT_OFF_COPY) Do Fc HFc
    (fun a k Hk => HDo (a, k) Hk) (AGF CRT_OFF_COPY Do ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) HDo)). }
{ rewrite EJ. exact Hdepc. }
{ rewrite EF2. unfold crt_wP, crt_tb, crt_tc. rewrite Ecw.
  exists ok. cbv zeta.
  split; [exact Hoks|].
  right. split; [exact Hq0|]. split; [exact Hwf|].
  exists okr, (Some (ck_crt_tree t)), tr.
  split; [exact Hrunr|]. split; [exact Hoksr|]. split; [exact Ecnt|].
  split; [intros _; split; [symmetry; exact (cm_read_crt x t true HIN) | exact Ecalls]|].
  split; [reflexivity|]. split; [exact HPOS|].
  exists Dback. split; [rewrite <- Ecap; reflexivity|]. split; [exact HNb3|]. split; [exact HTBb|].
  destruct HFb as (Fb & HFb1 & HFb2). exists Fb. split; [|exact HFb2].
  exact (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) (F + CRT_OFF_BACK) Dback Fb HFb1
    (fun a k Hk => HDb (a, k) Hk) (AGF CRT_OFF_BACK Dback ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) HDb)). }
Qed.

Lemma crt102rw_Wgo : crt102rw_W2_goal -> crt102rw_Wgo_goal.
Proof.
intros HW2 HL0K fx' ly3 S3 Hp3 W3 mem3 md3 kj3 pos regs3 Do Lam3 peak3 cnt3 c ms HFZ HFK HL HBR R22 R24 R10 R25
  HRAb HRAv Et HNo Hsz HTBo Hdepc HFOW HSP HBSo Ecnt Hc3 Hcin HPOSW.
pose proof (crt_pos_strtod HPOSW) as Esm.
destruct (crt_pos_ex HPOSW) as (pre & hist3 & HPOSWa).
pose proof (crt_pos_split HPOSWa) as Ert. pose proof (crt_pos_room HPOSWa) as Hpos.
pose proof (crt_pos_run HPOSWa) as Hrun. pose proof (crt_pos_cons HPOSWa) as Hcons.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_sp (crt_dregs_bregs HBR)) as R2.
pose proof (crt_bregs_gp (crt_dregs_bregs HBR)) as R3.
pose proof (crt_bregs_tp (crt_dregs_bregs HBR)) as R4.
pose proof (crt_bregs_s0 (crt_dregs_bregs HBR)) as R8.
pose proof (crt_bregs_s1 (crt_dregs_bregs HBR)) as R9.
pose proof (crt_bregs_s2 (crt_dregs_bregs HBR)) as R18.
pose proof (crt_bregs_s4 (crt_dregs_bregs HBR)) as R20.
pose proof (crt_bregs_s3 (crt_dregs_bregs HBR)) as R19.
pose proof (crt_bregs_s7 (crt_dregs_bregs HBR)) as R23.
pose proof (crt_bregs_s10 (crt_dregs_bregs HBR)) as R26.
pose proof (crt_bregs_s11 (crt_dregs_bregs HBR)) as R27.
pose proof (crt_dregs_s5 HBR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt102rw_sp HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof crt102rw_stkc as ESTK.
pose proof (YM05.alloc_ceiling_val) as Hcv.
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
set (F := frame_addr ly3 CRT_CID pos) in *.
destruct (crt102rw_W0_entry fx' W3 mem3 regs3 R10 R24 R9 ltac:(lia) ltac:(lia) Hs1a
  ltac:(intros o Ho; apply Hpres3; lia)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs regs3 [])) by apply te_env.
pose proof HMNc as HPM.
pose (RUN := @crt_run_xw_inv fx' rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
assert (X9 : bv_unsigned (ew (TE regs regs3 []) (xr 9)) = sp1).
{ unfold xr. rewrite (te_cur regs regs3 _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
unfold crt_cfg.
paj_run_tok_x_inv (RUN WS_HJ) HS HJ SHOK HPM (2 ^ 63, 2 ^ 63).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 9) sp1); [reflexivity | exact X9 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
  apply awr_ok_nil. }
(* the run's one write: &back at s1 + 0x38 *)
assert (Hags : forall xw : word, ~ (sp1 + 56 <= bv_unsigned xw < sp1 + 64) ->
  mrestrict (w_H W3) (ms_mem ms0) xw = mrestrict (w_H W3) mem3 xw).
{ intros xw Hn. apply HFr. intros (r & Hr & Ha). apply Hn. cbv [crt102rw_ssW0 ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X9 in Ha. lia. }
assert (Hag : forall xw : word, ~ crt102rw_wr (regs := regs) F (bv_unsigned xw) ->
  mrestrict (w_H W3) (ms_mem ms0) xw = mrestrict (w_H W3) mem3 xw).
{ intros xw Hn. apply Hags. intros Hw. apply Hn. right. lia. }
pose proof (crt102rw_live_run LAWS HPRE HTREE ly3 S3 Hp3 W3 mem3 (ms_mem ms0) md3 _ kj3 _ pos Do Lam3 peak3 cnt3 0 0
  HL HJ HB_HJ Hag HPM) as HL0.
assert (KR0 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 25; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr regs3 r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (22%bv : bv 5) Q22.
assert (VBACK : crt_spill (regs := regs) W3 (ms_mem ms0) CRT_SP_BACK (F + CRT_OFF_BACK)).
{ unfold crt_spill, CRT_SP_BACK, CRT_OFF_BACK.
  refine (crt102rw_chunk_vm_ok fx' _ _ (w_H W3) ms0 0 _ (xr 9) sp1 56 8%N (SOff 59 32) (F + 32) HS eq_refl eq_refl X9
    ltac:(cbn; tauto) _ _ ltac:(cbn; lia)).
  - cbn [sv_denot]. assert (A59 : ew (TE regs regs3 []) 59 = getr regs3 27) by te_close. rewrite A59, R27. unfold w64.
    rewrite unsigned_lit_small by lia. reflexivity.
  - cbn. lia. }
assert (X10 : getr (ms_regs ms0) 10 = w64 (F + CRT_OFF_COPY)).
{ rewrite Q10. assert (A : ew (TE regs regs3 []) 52 = getr regs3 20) by te_close. rewrite A. exact R20. }
assert (X11 : getr (ms_regs ms0) 11 = w64 1) by (rewrite Q11; reflexivity).
assert (X22 : getr (ms_regs ms0) 22 = w64 1) by (rewrite Q22; reflexivity).
assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + CRT_W_OFF))) by (rewrite Q1; vm_compute; reflexivity).
assert (HBR0 : bregsA (ms_regs ms0) F).
{ refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
            crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
            crt_bregs_s11 := _ |}; rewrite !KR0 by (cbv; tauto); assumption. }
assert (HE2 : bv_unsigned (ew (TE regs regs3 []) 2) = sp0) by (rewrite (te_entry regs regs3 [] 2%bv 2) by reflexivity; reflexivity).
destruct (crt_live_journal HL0) as (WS_HJ0 & HJ0 & HB_HJ0). pose proof (crt_live_side HL0) as HSD0.
pose proof (crt_live_lam_perm HL0) as HPL0. pose proof (crt_live_blocks_perm HL0) as HPB0.
pose proof (crt_live_dx_apart HL0) as HAP0. pose proof (crt_live_saved HL0) as HSV0.
pose proof (crt_live_frame HL0) as HFRM0. pose proof (crt_live_fspill HL0) as HSPF0.
pose proof (crt_live_copy_open HL0) as HCR0. pose proof (crt_live_copy_hull HL0) as HCH0.
pose proof (crt_live_memnorm HL0) as HMN0.
pose proof (crt_side_ledger HSD0) as HLED0. pose proof (crt_side_peak HSD0) as Hpk0.
pose proof (crt_side_room HSD0) as HROOM0. pose proof (crt_side_arodata HSD0) as HRO0.
pose proof (crt_side_doc HSD0) as HND0. pose proof (crt_side_doc_blocks HSD0) as HDL0.
pose proof HJ0 as (HAR0 & _).
pose proof (cm_in_intro x t H0READ H0LENX H0WL0 H0WL1) as HIN.
assert (HDo3 : forall bk, In bk Do -> In bk Lam3).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL0)). apply in_or_app. left. exact Hbk. }
(* copy's tree at the call (the run wrote only the &back word) *)
assert (HNo0 : pj_nodeR SEGS (mrestrict (w_H W3) (ms_mem ms0)) (prh_lin Lam3) (F + CRT_OFF_COPY) (ck_crt_tree t) Do).
{ apply (pj_nodeR_frame SEGS _ (mrestrict (w_H W3) mem3) _ (prh_lin Lam3) _ Do HNo). intros y Hy.
  destruct (crt102rw_foot_nw LAWS HPRE ly3 S3 Hp3 W3 mem3 md3 kj3 pos Do Lam3 peak3 cnt3 0 0 Do (F + CRT_OFF_COPY) y HL HDo3
    ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy) as (Hy1 & Hy2).
  assert (E : mrestrict (w_H W3) (ms_mem ms0) (Z_to_bv 64 y) = mrestrict (w_H W3) mem3 (Z_to_bv 64 y)).
  { apply Hag. rewrite unsigned_lit_small by lia. exact Hy2. }
  split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
(* copy's ORDERED free list at the call, the same way *)
assert (HFO0 : crt102rw_copy_fo W3 (ms_mem ms0) Lam3 (F + CRT_OFF_COPY) Do).
{ destruct HFOW as (Fc & HFc & HFce). exists Fc. split; [|exact HFce].
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D (mrestrict (w_H W3) mem3) _ (prh_lin Lam3) (prh_lin Lam3) _ Do Fc HFc
    (fun a k Hk => HDo3 (a, k) Hk)). intros y Hy.
  destruct (crt102rw_foot_nw LAWS HPRE ly3 S3 Hp3 W3 mem3 md3 kj3 pos Do Lam3 peak3 cnt3 0 0 Do (F + CRT_OFF_COPY) y HL HDo3
    ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy) as (Hy1 & Hy2).
  assert (E : mrestrict (w_H W3) (ms_mem ms0) (Z_to_bv 64 y) = mrestrict (w_H W3) mem3 (Z_to_bv 64 y)).
  { apply Hag. rewrite unsigned_lit_small by lia. exact Hy2. }
  split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
assert (HTV : PRH_FnWriter.prhWriter_tree_vis W3 (ms_mem ms0) Do).
{ apply (crt102rw_tree_vis_keep ly3 S3 Hp3 W3 (ms_mem ms0) _ Lam3 peak3 cnt3 SIZE_MAXZ 0 most 0 Do HAR0 HLED0 HDo3).
  intros a0 k0 Hk0. exact (crt102rw_blk_vis ly3 S3 Hp3 W3 (ms_mem ms0) _ Lam3 peak3 cnt3 SIZE_MAXZ 0 most 0 a0 k0 HAR0 HLED0
    (HDo3 _ Hk0) (proj2 (Hsz a0 k0 Hk0))). }
(* its run events: the rewrite's w_evs (copy_set ms) true, all granted (g_fail_at = SIZE_MAX) *)
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 H0LED) as (_ & _ & Hcntg & _).
destruct (cm_pjw_nofail_crt x t ms (Z.of_nat c) cnt HIN Et ltac:(lia) ltac:(lia)) as (Hc64 & Hnf).
rewrite <- Ecnt in Hc64, Hnf.
assert (HRUNw : prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat
  (PRH_FnWriter.prhWriter_pjw_evs [] cnt3 SIZE_MAXZ (WriterValue.wdpieces (ck_crt_tree t) (negb (1 =? 0))))).
{ change (negb (1 =? 0)) with true. rewrite Et, crt102rw_copy_set.
  rewrite (@PRH_Supply.prhWriter_pjw_evs_w_evs CfParams_preset (PresetReqAt.copy_set ms) true cnt3 SIZE_MAXZ
    ltac:(reflexivity) Hc64 Hnf).
  unfold crt_evs_W in Hrun. exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) Hrun)). }
(* its consumer window: the rewrite's w_evs (copy_set ms) true, the first piece of crt_pos's window *)
assert (HCONSw : PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length pre)%nat
  (length (PRH_FnWriter.prhWriter_pjw_evs [] cnt3 SIZE_MAXZ (WriterValue.wdpieces (ck_crt_tree t) (negb (1 =? 0)))))).
{ change (negb (1 =? 0)) with true. rewrite Et, crt102rw_copy_set.
  rewrite (@PRH_Supply.prhWriter_pjw_evs_w_evs CfParams_preset (PresetReqAt.copy_set ms) true cnt3 SIZE_MAXZ
    ltac:(reflexivity) Hc64 Hnf).
  unfold crt_evs_W in Hcons. rewrite length_app in Hcons.
  exact (proj1 (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _) Hcons)). }
(* pj_write's text is keyed on ReaderRes.jr_strtod (no rp_sm binder): its position, run and window at that key,
   by crt_pos's strtod tie Esm *)
pose proof Hpos as Hposj. rewrite Esm in Hposj, HRUNw, HCONSw.
(* the room: the copy's blocks within the bound Crt102Model's cm_live_write takes *)
assert (Hroomw : blocks_bytes S3 + PRH_FnWriter.LIVE_pj_write (ck_crt_tree t) (negb (1 =? 0)) <= LIVE_MAX).
{ change (negb (1 =? 0)) with true. apply (cm_live_write t (blocks_bytes S) (blocks_bytes S3) H0LIVE).
  rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPB0), bsum_app. lia. }
assert (Hfr : Z.of_nat (length (frames S3)) < fs_frames 0).
{ pose proof HJ as (_ & _ & _ & _ & _ & HFRc & _). rewrite HFRc. cbn [app length].
  assert (Hcap : ck_FRAMES_CAP - FR_check_round_trip + 1 < fs_frames 0) by (vm_compute; reflexivity). lia. }
pose proof (cm_in_wlen_crt x t HIN) as (_ & Hwm & _).
assert (HSTKw : 0 <= @STK_pj_write prh_img_A DOC_D /\ @STK_pj_write prh_img_A DOC_D + 240 <= STKC)
  by (rewrite ESTK; split; vm_compute; discriminate).
clear HF HG HFr.
refine (crt102rw_call LAWS HPRE fx' (@STK_pj_write prh_img_A DOC_D) [] CRT_W_OFF (SIGMA AS_pj_write) W3 (TE regs regs3 [])
  _ ms0 _ ly3 S3 Hp3 kj3 pos Do Lam3 peak3 cnt3 0 0 _ HFZ HS eq_refl eq_refl HE2 HL0 HBR0 X1 _ _ (proj1 HSTKw)
  (proj2 HSTKw) _ _ _).
- unfold CRT_W_OFF. lia.
- reflexivity.
- intros a0 Hfa. exfalso. exact (inFP_nil a0 Hfa).
- intros ch1 HPRE1. eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
  + refine (PJWRITE fx' rp_x rp_os _ rp_H0 hist3 most 0 ly3 S3 Hp3 W3 (ms_regs ms0) (ms_mem ms0) _ ch1
      (F + CRT_OFF_COPY) 1 (ck_crt_tree t) Do Lam3 peak3 cnt3 SIZE_MAXZ 0 HPRE1 H0CL HROOM0 Hposj HOS4 HCONSw X10 X11
      ltac:(lia) HLED0 HRUNw HNo0 _ HCR0 HTV (fun a0 k0 Hk0 => HDo3 (a0, k0) Hk0) Hdepc
      ltac:(assert (Z.of_nat DOC_D <= 2 ^ 31 - 1) by (vm_compute; discriminate); lia) Hfr ltac:(change (negb (1 =? 0)) with true; exact Hwm)
      (cm_rq_wmax t H0RQ) Hroomw).
    right; right. exists CRT_CID, pos. split; [exact Hin|]. rewrite crt102rw_fb. fold F. unfold CRT_OFF_COPY. lia.
  + intros W' c' _ HPo. exact HPo.
- (* the return at W (+0x2b4) *)
  intros fx4 ly4 S4 Hp4 W4 regs4 mem4 md4 k4 HFZ4 HFK4 HJe HJc HP HQ.
  change (negb (1 =? 0)) with true in HQ.
  destruct HQ as ((ok & ran' & q & Lam4 & peak4 & HQ') & HMN4). cbv zeta in HQ'.
  destruct HQ' as (Hoks & Rq & HROOM4 & Hgrw & Hposw & HNo4 & HTV4 & HLED4 & Harmw).
  assert (HFK5 : fregs_kept_x fx fx4) by (intros r0 Hr0; rewrite (HFK4 r0 Hr0); exact (HFK r0 Hr0)).
  destruct (crt102rw_call_keep LAWS HPRE ly3 S3 Hp3 W3 (ms_mem ms0) _ _ pos _ _ ly4 S4 Hp4 W4 mem4 md4 k4 HJ0 HJc
    (fun a0 Hf => False_ind _ (inFP_nil a0 Hf))) as (EF4 & KS4 & KSH4).
  fold F in EF4, KSH4.
  assert (Hcw : 0 <= WriterApp.w_cnt (WriterApp.w0 cnt3 SIZE_MAXZ) < 2 ^ 64) by (cbn; lia).
  pose proof (crt102rw_putN_fail (WriterValue.wdpieces (ck_crt_tree t) true) ok (WriterApp.w0 cnt3 SIZE_MAXZ) eq_refl)
    as Efl.
  rewrite Efl in HLED4.
  (* the registers the callee keeps *)
  assert (HDR4 : dregsA regs4 F).
  { refine {| crt_dregs_bregs := {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _;
                crt_bregs_s1 := _; crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _;
                crt_bregs_s10 := _; crt_bregs_s11 := _ |}; crt_dregs_s5 := _ |};
    [ rewrite (ts_ap (ms_regs ms0) regs4 2%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 3%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 4%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 8%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 9%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 18%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 20%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 19%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 23%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 26%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 27%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms0) regs4 21%bv HP) by ts_cs ];
    rewrite !KR0 by (cbv; tauto); assumption. }
  assert (X22' : getr regs4 22 = w64 1) by (rewrite (ts_ap (ms_regs ms0) regs4 22%bv HP) by ts_cs; exact X22).
  assert (X25' : getr regs4 25 = w64 (VAL 315))
    by (rewrite (ts_ap (ms_regs ms0) regs4 25%bv HP) by ts_cs; rewrite (KR0 25%bv) by (cbv; tauto); exact R25).
  (* the two locals stay open: the run wrote the &back word only, the call's footprint is empty *)
  assert (HRAb0 : range_addressable (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF (F + CRT_OFF_BACK) 56).
  { apply (range_addressable_agree (aview SEGS (w_H W3) mem3)); [|exact HRAb].
    intros y Hy. unfold CRT_OFF_BACK in Hy. unfold shadow_of_addr. apply aview_eq_of. apply Hags.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold SHADOW_OFF. lia. }
  assert (HRAv0 : range_addressable (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF (F + CRT_OFF_V) 56).
  { apply (range_addressable_agree (aview SEGS (w_H W3) mem3)); [|exact HRAv].
    intros y Hy. unfold CRT_OFF_V in Hy. unfold shadow_of_addr. apply aview_eq_of. apply Hags.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold SHADOW_OFF. lia. }
  destruct (crt102rw_local_keep W3 W4 (ms_mem ms0) mem4 F CRT_OFF_BACK ltac:(lia) F32 Fb2 KSH4
    ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) as (LB4 & _).
  destruct (crt102rw_local_keep W3 W4 (ms_mem ms0) mem4 F CRT_OFF_V ltac:(lia) F32 Fb2 KSH4
    ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)) as (LV4 & _).
  (* the spills *)
  pose proof (crt102rw_spills_keep W3 W4 (ms_mem ms0) mem4 ms KS4 (crt102rw_spills_agree1 W3 mem3 (ms_mem ms0) ms Hags HSP))
    as HSP4.
  pose proof (crt102rw_spill_keep HPRE W3 W4 (ms_mem ms0) mem4 CRT_SP_BACK (F + CRT_OFF_BACK) KS4
    ltac:(unfold CRT_SP_BACK; lia) ltac:(unfold CRT_SP_BACK; lia) VBACK) as VBACK4.
  (* copy's tree, read at the call's end *)
  pose proof (crt_side_doc_blocks HSD0) as HDLx.
  assert (HDL4 : forall bk, In bk D -> In bk Lam3) by exact HDLx.
  assert (Hc3' : 0 <= Z.of_nat c <= 3) by lia.
  destruct (cm_pjw_nofail_crt x t ms (Z.of_nat c) cnt HIN Et Hc3' ltac:(lia)) as (Hc64' & _).
  subst cnt3.
  destruct Harmw as [(Hwf0 & Hq0 & Hqfr & ELam & Epk & HPBw & Hlenw & Hbytes) |
                     (Hwf1 & Eq0 & ELam & HPBw & Hpkw)].
  + (* GRANTED: pj_write returned its text q over the fresh block (q, cap) *)
    subst Lam4.
    set (st' := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
      (WriterValue.wdpieces (ck_crt_tree t) true)) in *.
    pose proof (crt102rw_putN_oktrue _ ok _ Hcw Hwf0) as Hall.
    (* g_ran_out stays 0: every grow was taken *)
    assert (Eran : ran' = 0).
    { destruct Hoks as (_ & [Hr | (_ & i0 & Hi0 & Hni0 & _)] & _); [exact Hr|].
      unfold prh_refused in Hni0. rewrite (Hall i0 Hi0) in Hni0. discriminate Hni0. }
    subst ran'.
    assert (Hpk4 : peak3 <= peak4) by (rewrite Epk; lia).
    pose proof (crt102rw_side_call LAWS HPRE HTREE ly3 S3 Hp3 W3 (ms_mem ms0) _ _ pos Do Lam3 peak3 _ 0 0 _ _
      ly4 S4 Hp4 W4 mem4 md4 k4 ((q, WriterApp.w_cap st') :: Lam3) peak4 (WriterApp.w_cnt st') 0 0 HL0 HJc
      (Forall_nil _) (fun a0 Hf => False_ind _ (inFP_nil a0 Hf)) HLED4 Hpk4 HROOM4
      (fun bk Hbk => or_intror (HDL4 bk Hbk))) as HSD4.
    assert (HPB4 : Permutation (ablocks B ly4 S4) (ablocks B ly S ++ ck_hblks ((q, WriterApp.w_cap st') :: Do))).
    { eapply Permutation_trans; [exact HPBw|]. eapply Permutation_trans; [apply perm_skip; exact HPB0|].
      unfold ck_hblks. cbn [map fst snd]. apply Permutation_middle. }
    assert (HrelDo : forall a' k', In (a', k') ((q, WriterApp.w_cap st') :: Do) ->
      In (a', k') Do \/ ~ In (a' - cf_head, k' + cf_head) (ablocks B ly3 S3)).
    { intros a' k' [Ex | Hx]; [injection Ex as <- <-; right; exact Hqfr | left; exact Hx]. }
    pose proof (crt102rw_apart_step ly3 S3 Hp3 W3 (ms_mem ms0) _ _ pos Do Lam3 peak3 _ 0 0 _ HL0 HrelDo) as HAP4.
    pose proof (crt102rw_live_call LAWS HPRE ly3 S3 Hp3 W3 (ms_mem ms0) _ _ pos Do Lam3 peak3 _ 0 0 _ _
      ly4 S4 Hp4 W4 mem4 md4 k4 ((q, WriterApp.w_cap st') :: Do) ((q, WriterApp.w_cap st') :: Lam3) peak4
      (WriterApp.w_cnt st') 0 0 HL0 HJe HJc ltac:(lia) (fun a0 Hf => False_ind _ (inFP_nil a0 Hf)) HSD4
      (perm_skip _ HPL0) HPB4 HAP4 HMN4) as HL4.
    (* the position after pj_write's granted events *)
    assert (Hgr : prh_granted ok (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ
      (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
        (WriterValue.wdpieces (ck_crt_tree t) true))).
    { intros i0 Hi0 Hf0. rewrite (Hall i0 Hi0) in Hf0. discriminate Hf0. }
    destruct (Hposw Hgr) as (hist4 & Hpos4). rewrite <- Esm in Hpos4.
    destruct (crt102rw_putN_ok_nil _ ok _ Hcw Hwf0) as (Enil1 & Enil2).
    assert (Elen : length (PRH_FnWriter.prhWriter_pjw_evs ok (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ
        (WriterValue.wdpieces (ck_crt_tree t) true)) = length (PresetReqAt.w_evs (PresetReqAt.copy_set ms) true)).
    { unfold PRH_FnWriter.prhWriter_pjw_evs. cbv zeta. rewrite Enil1, Enil2.
      change (PRH_FnWriter.prhWriter_evs [] (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
          (WriterValue.wdpieces (ck_crt_tree t) true) ++
        (if (WriterApp.w_failed (PRH_FnWriter.prhWriter_putN [] (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
               (WriterValue.wdpieces (ck_crt_tree t) true)) =? 0) ||
             (WriterApp.w_cap (PRH_FnWriter.prhWriter_putN [] (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ)
               (WriterValue.wdpieces (ck_crt_tree t) true)) =? 0)
         then [] else [PresetReqAt.HFr (WriterApp.w_cap (PRH_FnWriter.prhWriter_putN []
           (WriterApp.w0 (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ) (WriterValue.wdpieces (ck_crt_tree t) true)) + cf_head)]))
        with (PRH_FnWriter.prhWriter_pjw_evs [] (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ
          (WriterValue.wdpieces (ck_crt_tree t) true)).
      replace (ck_crt_tree t) with (PresetReqAt.copy_set ms) by (rewrite Et; symmetry; apply crt102rw_copy_set).
      rewrite (@PRH_Supply.prhWriter_pjw_evs_w_evs CfParams_preset (PresetReqAt.copy_set ms) true _ SIZE_MAXZ
        ltac:(reflexivity) Hc64 Hnf).
      reflexivity. }
    rewrite Elen in Hpos4.
    pose proof (crt102rw_pos_P ms pre hist4 S4 Esm Ert Hrun Hcons Hpos4) as HPOS4.
    (* copy's tree in the state after the call: over the ledger with the text's block at its head *)
    assert (HNo5 : pj_nodeR SEGS (mrestrict (w_H W4) mem4) (prh_lin ((q, WriterApp.w_cap st') :: Lam3))
        (F + CRT_OFF_COPY) (ck_crt_tree t) Do).
    { apply (crt102rw_nodeR_lblk SEGS _ _ _ _ _ _ HNo4). intros a0 k0 Hk0. right. exact (HDo3 (a0, k0) Hk0). }
    pose proof (cm_pjw_cap_crt x t ok (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ HIN Hwf0) as (Hcap0 & Hcap32).
    pose proof (cm_in_wlen_crt x t HIN) as (_ & _ & Hw40).
    pose proof (cm_pjw_cap ok (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ (ck_crt_tree t) true
      ltac:(assert (2 ^ 40 <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia); lia) Hwf0) as (_ & Hcapl).
    (* copy's ORDERED free list after the call: the call's footprint is empty (crt102rw_fo_call) *)
    assert (HFO5 : crt102rw_copy_fo W4 mem4 ((q, WriterApp.w_cap st') :: Lam3) (F + CRT_OFF_COPY) Do).
    { assert (HcF0 : exists cid0 pos0, In (cid0, pos0) (frames S3) /\ frame_addr ly3 cid0 pos0 <= F + CRT_OFF_COPY /\
        F + CRT_OFF_COPY + 56 <= frame_addr ly3 cid0 pos0 + fs_frame_bytes cid0).
      { exists CRT_CID, pos. split; [exact Hin|]. rewrite crt102rw_fb. fold F. unfold CRT_OFF_COPY. lia. }
      destruct HFO0 as (Fc & HFc & HFce). exists Fc. split; [|exact HFce].
      exact (crt102rw_fo_call ly3 S3 Hp3 W3 (ms_mem ms0) _ kj3 _ _ ly4 S4 Hp4 W4 mem4 md4 k4 Lam3 peak3 _ 0
        ((q, WriterApp.w_cap st') :: Lam3) peak4 (WriterApp.w_cnt st') 0 (F + CRT_OFF_COPY) DOC_D Do Fc HAR0 HJc HLED0
        HLED4 HcF0 HDo3 (fun bk Hbk => or_intror (HDo3 bk Hbk)) (fun a0 Hf => False_ind _ (inFP_nil a0 Hf)) HFc). }
    apply (HW2 HL0K fx4 ly4 S4 Hp4 W4 mem4 md4 (kj3 + k4) pos Do ((q, WriterApp.w_cap st') :: Lam3) peak4 (WriterApp.w_cnt st')
      regs4 ms c q (WriterApp.w_cap st') ok).
    unfold crt102rw_Wst. rewrite EF4.
    split; [exact HFZ4|]. split; [exact HFK5|]. split; [exact HL4|]. split; [exact HDR4|].
    split; [exact Rq|]. split; [exact X22'|]. split; [exact X25'|].
    split; [exact (LB4 HRAb0)|]. split; [exact (LV4 HRAv0)|]. split; [exact Et|].
    split; [exact HNo5|]. split; [exact HTBo|]. split; [exact Hdepc|]. split; [exact HFO5|]. split; [exact HSP4|].
    split; [exact VBACK4|]. split; [exact Hq0|]. split; [exact Hlenw|]. split; [exact Hcap32|].
    split; [exact Hbytes|]. split; [exact Hc3|]. split; [exact Hcin|]. split; [exact Hoks|].
    split; [exact Hwf0|]. split; [reflexivity|]. split; [reflexivity|].
    split; [|exact HPOS4].
    unfold st' in *. unfold ck_hblks in *. cbn [map fst snd YCbq.bsum fold_right]. unfold YCbq.bsum in HBSo. lia.
  + (* REFUSED: DEAD AT ITS SOURCE. tpj_write_specX's DEAD-PJWRITE conjunct (prh_granted, PRH_FnWriter.v:820, Hgrw)
       says every false outcome is the chosen failure; the writer's window lies below g_fail_at = SIZE_MAX (the count
       plus the writer's calls, Crt102Model.cm_cnt_write / cm_pjw_k_le), so no grow failed
       (PRH_Refute.prh_refute_pj_write_failed) and the failed flag is 0 *)
    exfalso. apply Hwf1.
    pose proof (cm_cnt_write x t ms (Z.of_nat c) cnt HIN Et ltac:(lia) ltac:(lia)) as (Hw0 & Hw1).
    pose proof (cm_pjw_k_le ok (ck_cnt2 cnt t + 1 + Z.of_nat c) SIZE_MAXZ (ck_crt_tree t) true ltac:(lia)) as Hk.
    assert (ES : SIZE_MAXZ = 2 ^ 64 - 1) by reflexivity.
    apply (PRH_Refute.prh_refute_pj_write_failed ok _ SIZE_MAXZ _); [lia | lia | left; lia | exact Hgrw].
Qed.


(* ---- K (+0x27c): pj_set has returned; s8 = seqz a0, then O1. The state: the live state over the blocks the call left,
   the frame registers, a0 = res, the two locals open, copy freeable at DOC_D, the count with pj_set's charge c, and the
   two outcomes (res = 0, or res = -1 with g_ran_out = 1: the request bound) ---- *)
Definition crt102rw_ssK (v : Z) : sstate :=
  mkSS (CRT_PC_A + CRT_K_OFF) (sr_set cur_atoms 10%bv (SLit v)) [] None (mkFacts [] [] []).
Lemma crt102rw_K_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg v, getr rg 10 = w64 v ->
  @st_ok_pi SEGS VAL fxk (TE regs rg []) (crt102rw_ssK v)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_K_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg v R10.
split; [|unfold sh_ok; apply Forall_nil].
unfold crt102rw_ssK. apply (@ts_st_ok fxk).
- apply regs_ok_pin; [apply te_regs_ok | intros X; discriminate X | exact R10].
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.

Lemma crt102rw_atK : forall fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc ranc rg res c ms,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  liveA (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc 0 ranc ->
  dregsA rg (frame_addr lyc CRT_CID pos) -> getr rg 10 = w64 res ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 ->
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Do ->
  t = PjTree.JObj ms -> cntc = ck_cnt2 cnt t + 1 + Z.of_nat c -> (c <= 3)%nat ->
  (In ck_MOD_AT (map fst ms) -> c = 0%nat) ->
  (* the GRANTED outcome only: pj_set's res = -1 arm is dead at its source (refuted in crt102rw_G_taken) *)
  res = 0 -> ranc = 0 ->
  crt102rw_O1go fxk lyc Sc Hpc Wc memc kj pos Do Lamc peakc cntc ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_K_OFF rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Do Lamc peakc cntc ranc rg res c ms HFZ HFK HL HDR R10 HRAb HRAv HFD Et Ecnt
  Hc3 Hcin Er Eran HGO.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_bregs_sp (crt_dregs_bregs HDR)) as R2.
pose proof (crt_bregs_gp (crt_dregs_bregs HDR)) as R3.
pose proof (crt_bregs_tp (crt_dregs_bregs HDR)) as R4.
pose proof (crt_bregs_s0 (crt_dregs_bregs HDR)) as R8.
pose proof (crt_bregs_s1 (crt_dregs_bregs HDR)) as R9.
pose proof (crt_bregs_s2 (crt_dregs_bregs HDR)) as R18.
pose proof (crt_bregs_s4 (crt_dregs_bregs HDR)) as R20.
pose proof (crt_bregs_s3 (crt_dregs_bregs HDR)) as R19.
pose proof (crt_bregs_s7 (crt_dregs_bregs HDR)) as R23.
pose proof (crt_bregs_s10 (crt_dregs_bregs HDR)) as R26.
pose proof (crt_bregs_s11 (crt_dregs_bregs HDR)) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof HMNc as HPM.
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof (cm_in_intro x t H0READ H0LENX H0WL0 H0WL1) as HIN.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
unfold crt_cfg.
(* res = 0: s8 = 1 *)
  subst res.
  assert (Rv : getr rg 10 = w64 0) by exact R10.
  destruct (crt102rw_K_entry fxk Wc memc rg (0) Rv) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
  paj_run_to_tok_x_inv (RUNTO WS_HJ) HS HJ SHOK HPM (0, 0) (CRT_PC_A + CRT_O1_OFF).
  { cbv [crt102rw_ssK ss_mem]. apply awr_ok_nil. }
  assert (Hm : forall xw, mrestrict (w_H Wc) (ms_mem ms0) xw = mrestrict (w_H Wc) memc xw).
  { intros xw. apply HFr. intros (r & Hr & _). cbv [crt102rw_ssK ss_mem In] in Hr. destruct Hr. }
  assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
  { intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
  prreg HS (24%bv : bv 5) Q24.
  pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc memc (ms_mem ms0) mdc _ kj _ pos Do Lamc peakc cntc 0 ranc
    HL HJ HB_HJ (fun xw _ => Hm xw) HPM) as HL1.
  clear HF HG HFr.
  pmkst HS.
  change (BASE + 5392) with (BASE + (CRT_PC_A + CRT_O1_OFF)).
  assert (HAG : forall X, pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms0)) X).
  { intros X y _. assert (E : mrestrict (w_H Wc) (ms_mem ms0) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y))
      by apply Hm.
    split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
  apply (crt102rw_O1 fxk lyc Sc Hpc Wc (ms_mem ms0) _ kj pos Do Lamc peakc cntc ranc (ms_regs ms0) 1); [| exact Eran |].
  + unfold crt102rw_O1st. fold F.
    split; [exact HFZ|]. split; [exact HFK|]. split; [exact HL1|].
    split; [refine {| crt_dregs_bregs := {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _;
                        crt_bregs_s0 := _; crt_bregs_s1 := _; crt_bregs_s2 := _; crt_bregs_s4 := _;
                        crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _; crt_bregs_s11 := _ |};
                      crt_dregs_s5 := _ |}; rewrite !KR by (cbv; tauto); assumption|].
    split; [rewrite Q24; reflexivity|].
    split; [right; reflexivity|].
    split; [apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAb]; intros y _; apply aview_eq_of; apply Hm|].
    split; [apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAv]; intros y _; apply aview_eq_of; apply Hm|].
    split; [exact (crt102rw_fdR_frame SEGS DOC_D _ _ (prh_lin Lamc) _ Do HFD (HAG _))|].
    split.
    { exists (Z.of_nat c). split; [lia|]. split; [intros ms' Et' Hin'; rewrite Et in Et'; injection Et' as <-; rewrite (Hcin Hin'); reflexivity|].
      rewrite (cm_cnt_obj cnt t ms (Z.of_nat c) Et). rewrite Ecnt, cm_cnt2_eq.
      pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true). pose proof (cm_tcalls_nonneg t).
      pose proof (cm_wcalls_nonneg (ck_crt_tree t) true). pose proof (cm_tcalls_nonneg (ck_crt_tree t)). lia. }
    intros _; reflexivity.
  + intros Er0 fx' ly2 W2 mem2 md2 k1 regs2 memm mdm HFZ2 HFK2 HL2 HBR2 X22 X24 Ra0 X25 EF2 Hmm HARm HJc HRAb2 HRAv2 HFD2.
    exact (HGO fx' ly2 W2 mem2 md2 k1 regs2 memm mdm HFZ2 HFK2 HL2 HBR2 X22 X24 Ra0 X25 EF2
      (fun xw => eq_trans (Hmm xw) (Hm xw)) HARm HJc HRAb2 HRAv2 HFD2).
Qed.

(* ---- the symbolic entry at G: the spill word s1 + 0x48 (written) ---- *)
Definition crt102rw_ssG : sstate := mkSS (CRT_PC_A + CRT_G_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 72 80 72 80 [] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma crt102rw_G_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg,
  getr rg 9 = w64 sp1 -> 2 ^ 46 <= sp1 -> sp1 + 96 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall o, 72 <= o < 80 -> apresent (w_H Wc) memc (sp1 + o)) ->
  @st_ok_pi SEGS VAL fxk (TE regs rg []) crt102rw_ssG
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_G_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg R9 H1 H2 H3 HP.
set (E := TE regs rg []).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
split; [|unfold sh_ok; apply Forall_nil].
apply (@ts_st_ok fxk).
all: try change (TE regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | |constructor].
  intros o Ho. cbn [YP09.r_wlo YP09.r_whi] in Ho. apply (apresent_writable SEGS). apply HP. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9.
  change (2 ^ 5) with 32. split; [|exact I]. lia.
Qed.

(* the taken arm: a0 = 0, v is JStr STAMP over one fresh block, the position advanced past pj_string's strdup *)
Lemma crt102rw_G_taken : crt102rw_Wgo_goal -> crt102rw_L0K ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a pre hist,
  crt102rw_Gst fxk lyc Sc Hpc Wc memc mdc kj pos Db ((a, Z.of_nat (length ck_STAMP) + 1) :: Db) Lamc peakc cntc 0 rg ms ->
  getr rg 10 = w64 0 ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_V)
    (PjTree.JStr ck_STAMP) [(a, Z.of_nat (length ck_STAMP) + 1)] ->
  PresetReqAt.round_trip rp_sm t = pre ++ crt_evs_U (rp_sm := rp_sm) ms ->
  prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat (crt_evs_U (rp_sm := rp_sm) ms) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length pre)%nat (length (crt_evs_U (rp_sm := rp_sm) ms)) ->
  rp_sm = ReaderRes.jr_strtod ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length pre + 1)%nat rp_H0 hist Sc ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_G_OFF rg memc mdc) QFa.
Proof.
intros HWGO HL0K fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ab pre hist
  (HFZ & HFK & HL & HDR & R22 & R24 & Et & VPN & VN & HRAb & HRAv & HHVb & HHVv & HCT & HTB & HCAPh & HDbf & HDbl & HDbn
   & Hcnt & HFOg) R10 HNDv Ert Hrun Hcons Esm Hpos.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_sp (crt_dregs_bregs HDR)) as R2.
pose proof (crt_bregs_gp (crt_dregs_bregs HDR)) as R3.
pose proof (crt_bregs_tp (crt_dregs_bregs HDR)) as R4.
pose proof (crt_bregs_s0 (crt_dregs_bregs HDR)) as R8.
pose proof (crt_bregs_s1 (crt_dregs_bregs HDR)) as R9.
pose proof (crt_bregs_s2 (crt_dregs_bregs HDR)) as R18.
pose proof (crt_bregs_s4 (crt_dregs_bregs HDR)) as R20.
pose proof (crt_bregs_s3 (crt_dregs_bregs HDR)) as R19.
pose proof (crt_bregs_s7 (crt_dregs_bregs HDR)) as R23.
pose proof (crt_bregs_s10 (crt_dregs_bregs HDR)) as R26.
pose proof (crt_bregs_s11 (crt_dregs_bregs HDR)) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt102rw_sp HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof crt102rw_stkc as ESTK.
pose proof (YM05.alloc_ceiling_val) as Hcv.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (crt102rw_G_entry fxk Wc memc rg R9 ltac:(lia) ltac:(lia) Hs1a ltac:(intros o Ho; apply Hpres1; lia)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
pose proof HMNc as HPM.
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
pose (BR := @YSRrG.paj_branchR fxk rc A_prog_listing PA RZW).
unfold crt_cfg.
assert (X9 : bv_unsigned (ew (TE regs rg []) (xr 9)) = sp1).
{ unfold xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
paj_run_tok_x_inv (RUN WS_HJ) HS HJ SHOK HPM (2 ^ 63, 2 ^ 63).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 9) sp1); [reflexivity | exact X9 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
  apply awr_ok_nil. }
(* the run's one write: the spill word s1 + 0x48 *)
assert (Hags : forall xw : word, ~ (sp1 + 72 <= bv_unsigned xw < sp1 + 80) ->
  mrestrict (w_H Wc) (ms_mem ms0) xw = mrestrict (w_H Wc) memc xw).
{ intros xw Hn. apply HFr. intros (r & Hr & Ha). apply Hn. cbv [crt102rw_ssG ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X9 in Ha. lia. }
assert (Hag : forall xw : word, ~ crt102rw_wr (regs := regs) F (bv_unsigned xw) ->
  mrestrict (w_H Wc) (ms_mem ms0) xw = mrestrict (w_H Wc) memc xw).
{ intros xw Hn. apply Hags. intros Hw. apply Hn. right. lia. }
pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc memc (ms_mem ms0) mdc _ kj _ pos ((ab, Z.of_nat (length ck_STAMP) + 1) :: Db) Lamc peakc cntc 0 0
  HL HJ HB_HJ Hag HPM) as HL1.
assert (KR1 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
clear HF HG HFr.
psrr_branch_tok RUN BR HS SHOK (2 ^ 63, 2 ^ 63).
- (* a0 = 0: pj_string took its strdup; to pj_set (&copy, MOD_AT, &v) *)
  paj_run_tok_x_inv (RUN WS_HJ) HS HJ SHOK HPM (2 ^ 63, 2 ^ 63).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 9) sp1); [reflexivity | exact X9 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
    apply awr_ok_nil. }
  assert (Hag2s : forall xw : word, ~ (sp1 + 72 <= bv_unsigned xw < sp1 + 80) ->
    mrestrict (w_H Wc) (ms_mem ms1) xw = mrestrict (w_H Wc) (ms_mem ms0) xw).
  { intros xw Hn. apply HFr. intros (r & Hr & Ha). apply Hn.
    assert (X41 : bv_unsigned (ew (TE regs rg []) 41) = sp1) by exact X9.
    vm_compute in Hr. destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha.
    rewrite ts_bv_some, X41 in Ha. lia. }
  assert (Hag12s : forall xw : word, ~ (sp1 + 72 <= bv_unsigned xw < sp1 + 80) ->
    mrestrict (w_H Wc) (ms_mem ms1) xw = mrestrict (w_H Wc) memc xw).
  { intros xw Hn. rewrite (Hag2s xw Hn). exact (Hags xw Hn). }
  assert (Hag2' : forall xw : word, ~ crt102rw_wr (regs := regs) F (bv_unsigned xw) ->
    mrestrict (w_H Wc) (ms_mem ms1) xw = mrestrict (w_H Wc) (ms_mem ms0) xw).
  { intros xw Hn. apply Hag2s. intros Hw. apply Hn. right. lia. }
  pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms0) (ms_mem ms1) _ _ kj _ pos
    ((ab, Z.of_nat (length ck_STAMP) + 1) :: Db) Lamc peakc cntc 0 0 HL1 HJ HB_HJ Hag2' HPM) as HL2.
  assert (KR2 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv ->
    getr (ms_regs ms1) r = getr rg r).
  { intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  (* the three spills at the pj_set call: G's `sd s8, 0x48(s1)` wrote shadow (&doc->n) (the run's chunk), the other two
     are outside the run's one written word *)
  assert (HSP1 : crt102rw_spills Wc (ms_mem ms1) ms).
  { split; [|split].
    - unfold crt_spill, CRT_SP_SHN.
      refine (crt102rw_chunk_vm_ok fxk _ _ (w_H Wc) ms1 0 _ (xr 9) sp1 72 8%N (SOff 56 0) (shadow_addr (doc + PJ_OFF_N))
        HS eq_refl eq_refl X9 ltac:(cbn; tauto) _ _ ltac:(cbn; lia)).
      + cbn [sv_denot]. assert (A56 : ew (TE regs rg []) 56 = getr rg 24) by te_close. rewrite A56, R24, Z.add_0_r.
        unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
      + pose proof (crt102rw_doc_home LAWS HPRE HTREE) as (Hd1 & Hd2 & _). pose proof (YM05.alloc_ceiling_val).
        unfold shadow_addr, SHADOW_OFF, PJ_OFF_N. cbn.
        split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ].
        assert ((doc + 40) / 8 <= 2 ^ 60) by (apply Z.div_le_upper_bound; lia). lia.
    - unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms1) _ 8 _); [|exact VPN].
      intros i0 Hi0. apply aview_eq_of. apply Hag12s. unfold CRT_SP_PN. rewrite unsigned_lit_small by lia. lia.
    - unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms1) _ 8 _); [|exact VN].
      intros i0 Hi0. apply aview_eq_of. apply Hag12s. unfold CRT_SP_N. rewrite unsigned_lit_small by lia. lia. }
  clear HF HG HFr.
  set (n0 := Z.of_nat (length ck_STAMP) + 1) in *.
  set (o := F + CRT_OFF_COPY) in *. set (v := F + CRT_OFF_V) in *.
  destruct (crt_live_journal HL2) as (WS_HJ2 & HJ2 & HB_HJ2). pose proof (crt_live_side HL2) as HSD2.
  pose proof (crt_live_lam_perm HL2) as HPL2. pose proof (crt_live_blocks_perm HL2) as HPB2.
  pose proof (crt_live_dx_apart HL2) as HAP2. pose proof (crt_live_saved HL2) as HSV2.
  pose proof (crt_live_frame HL2) as HFRM2. pose proof (crt_live_fspill HL2) as HSPF2.
  pose proof (crt_live_copy_open HL2) as HCR2. pose proof (crt_live_copy_hull HL2) as HCH2.
  pose proof (crt_live_memnorm HL2) as HMN2.
  pose proof (crt_side_ledger HSD2) as HLED2. pose proof (crt_side_peak HSD2) as Hpk2.
  pose proof (crt_side_room HSD2) as HROOM2. pose proof (crt_side_arodata HSD2) as HRO2.
  pose proof (crt_side_doc HSD2) as HND2. pose proof (crt_side_doc_blocks HSD2) as HDL2.
  pose proof HJ2 as (HAR2 & _).
  pose proof (cm_in_intro x t H0READ H0LENX H0WL0 H0WL1) as HIN.
  assert (X10 : getr (ms_regs ms1) 10 = w64 o).
  { rewrite Q10. assert (A : ew (TE regs rg []) 52 = getr rg 20) by te_close. rewrite A. exact R20. }
  assert (X12 : getr (ms_regs ms1) 12 = w64 v).
  { rewrite Q12. assert (A : ew (TE regs rg []) 54 = getr rg 22) by te_close. rewrite A. exact R22. }
  assert (X11 : getr (ms_regs ms1) 11 = w64 CRT_MOD_AT_A).
  { rewrite Q11. unfold CRT_MOD_AT_A, CRT_MOD_AT_OFF.
    assert (H243 : bv_unsigned (ew (TE regs rg []) 243) = VAL (A_OBJ 2)) by (apply HEI0; vm_compute; lia).
    rewrite H243. reflexivity. }
  assert (X1 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + CRT_K_OFF))) by (rewrite Q1; vm_compute; reflexivity).
  assert (HBR2 : bregsA (ms_regs ms1) F).
  { refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
              crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
              crt_bregs_s11 := _ |}; rewrite !KR2 by (cbv; tauto); assumption. }
  assert (HE2 : bv_unsigned (ew (TE regs rg []) 2) = sp0) by (rewrite (te_entry regs rg [] 2%bv 2) by reflexivity; reflexivity).
  assert (Hsp1 : spZ (ms_regs ms1) = sp1) by (unfold spZ; rewrite (KR2 2%bv) by (cbv; tauto); rewrite R2; apply unsigned_lit_small; lia).
  (* the trees at the call: the runs wrote only the spill word s1 + 0x48 *)
  assert (HDx : forall bk, In bk ((ab, n0) :: Db) -> In bk Lamc).
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hbk. }
  assert (HDb : forall bk, In bk Db -> In bk Lamc) by (intros bk Hbk; apply HDx; right; exact Hbk).
  assert (HAGt : forall p0 Dt, (forall bk, In bk Dt -> In bk Lamc) -> F <= p0 -> p0 + 56 <= F + 512 ->
    pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)) (pj_footR p0 Dt)).
  { intros p0 Dt HDt Hp1 Hp2 y Hy.
    destruct (crt102rw_foot_nw LAWS HPRE lyc Sc Hpc Wc memc mdc kj pos ((ab, n0) :: Db) Lamc peakc cntc 0 0 Dt p0 y HL HDt
      Hp1 Hp2 Hy) as (Hy1 & Hy2).
    assert (E : mrestrict (w_H Wc) (ms_mem ms1) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
    { apply Hag12s. rewrite unsigned_lit_small by lia. intros Hw. apply Hy2. right. lia. }
    split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
  pose proof (pj_nodeR_frame SEGS t _ _ (prh_lin Lamc) o Db HCT
    (HAGt o Db HDb ltac:(unfold o, CRT_OFF_COPY; lia) ltac:(unfold o, CRT_OFF_COPY; lia))) as HNDo.
  (* copy's ORDERED free list at the call (the G state's last conjunct), framed by the same agreement: tpj_set_specX's
     ordered entry premise (PRH_FnPj.v:1002-1004) *)
  assert (HFOo : cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
    exists F0, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) (ms_mem ms1)) (prh_lin Lamc) nn o Db F0 /\
      map (fun b => snd b + cf_head) F0 = PresetReqAt.fo (PjTree.JObj ms)).
  { intros Hhd nn Hd. destruct (HFOg Hhd nn Hd) as (F0 & HF0 & HFm). exists F0. split; [|exact HFm].
    exact (PRH_PjOrder.pj_foR_frame SEGS nn _ _ (prh_lin Lamc) (prh_lin Lamc) o Db F0 HF0 (fun a k Hk => HDb (a, k) Hk)
      (HAGt o Db HDb ltac:(unfold o, CRT_OFF_COPY; lia) ltac:(unfold o, CRT_OFF_COPY; lia))). }
  assert (HDw : forall bk, In bk [(ab, n0)] -> In bk Lamc) by (intros bk [<- | []]; apply HDx; left; reflexivity).
  pose proof (pj_nodeR_frame SEGS (PjTree.JStr ck_STAMP) _ _ (prh_lin Lamc) v [(ab, n0)] HNDv
    (HAGt v [(ab, n0)] HDw ltac:(unfold v, CRT_OFF_V; lia) ltac:(unfold v, CRT_OFF_V; lia))) as HNDw.
  (* the copy's header *)
  pose proof HNDo as HNDo'. rewrite Et in HNDo'. cbn [pj_nodeR] in HNDo'.
  destruct HNDo' as (_ & _ & num & str & kids & keys & n & cap & Hhdr & Es & En & Hnc & Hcap & Di & ED & Hmems).
  assert (Hcap54 : cap <= 2 ^ 54).
  { destruct Hcap as [(Hc0 & _) | (Hc0 & Lk & _)]; [lia|].
    destruct (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms1) Lamc peakc cntc SIZE_MAXZ 0 kids (56 * cap) _ _ HLED2 Lk)
      as (Hk0 & Hab & _).
    destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms1) _ _ _ HAR2 Hab) as (_ & B4096 & Bce & _).
    change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (56 * cap + 16) ltac:(lia)). lia. }
  (* CAP (carried in the G state from crt_at_U's header-cap conjunct): the G-state header, framed to the call (O1's
     spill only) *)
  assert (Ecap : cap = Z.of_nat (PresetReqAt.ncap (length ms))).
  { destruct HCAPh as (num0 & str0 & kids0 & keys0 & n00 & Hh0).
    assert (Hh1 : pj_hdrR SEGS (mrestrict (w_H Wc) (ms_mem ms1)) o 6 num0 str0 kids0 keys0 n00
                   (Z.of_nat (PresetReqAt.ncap (length ms)))).
    { apply (pj_hdrR_frame SEGS _ _ o 6 num0 str0 kids0 keys0 n00 _ Hh0). intros y Hy.
      assert (E : mrestrict (w_H Wc) (ms_mem ms1) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
      { apply Hag12s. rewrite unsigned_lit_small by (unfold o, CRT_OFF_COPY in Hy; lia). unfold o, CRT_OFF_COPY in Hy. lia. }
      split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
    exact (crt102rw_hdr_cap_det _ o 6 num str kids keys n cap 6 num0 str0 kids0 keys0 n00 _ Hhdr Hh1). }
  (* the room: copy's blocks within round_trip_text (doc, 0)'s room, v's block pj_string's *)
  assert (Hroom : blocks_bytes Sc + PRH_FnPj.LIVE_pj_set n cap (Z.of_nat (length ck_MOD_AT)) <= LIVE_MAX).
  { apply (cm_live_set t (blocks_bytes S) (blocks_bytes Sc) H0LIVE); [|rewrite En, Et; reflexivity].
    rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPB2), bsum_app.
    replace (ck_hblks ((ab, n0) :: Db)) with (ck_hblks [(ab, n0)] ++ ck_hblks Db) by reflexivity.
    rewrite bsum_app, (cm_stamp_block ab).
    pose proof (cm_copy_room_rtt t Db (cm_in_wf x t HIN) HDbl HDbn). pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & _). lia. }
  (* the run events: pj_set's own list, the model's set_evs tail at the parsed object's capacity *)
  assert (HRUNk : prh_run_at rp_sm rp_x rp_os (rp_i + length pre + 1)%nat
    (PRH_FnPj.prhPj_set_evs ms ck_MOD_AT n cap)).
  { rewrite cm_MOD_KEY, Nat.add_1_r. apply (PRH_FnPj.prhPj_set_evs_supply rp_sm rp_x rp_os _ ms n cap En Ecap).
    unfold crt_evs_U, PresetReqAt.rw_evs in Hrun. rewrite <- !app_assoc in Hrun.
    exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) Hrun)). }
  (* its consumer window: set_evs's tail, after pj_string's strdup, the first piece of crt_pos's window *)
  assert (HCONSk : PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length pre + 1)%nat
    (length (PRH_FnPj.prhPj_set_evs ms ck_MOD_AT n cap))).
  { rewrite cm_MOD_KEY, Nat.add_1_r, En, Ecap.
    unfold PRH_FnPj.prhPj_set_evs. rewrite PRH_FnPj.prhPj_mfind_mod, !Nat2Z.id.
    unfold crt_evs_U, PresetReqAt.rw_evs in Hcons. rewrite <- !app_assoc, length_app in Hcons.
    apply (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _)) in Hcons as [Hc1 _].
    unfold PresetReqAt.set_evs in Hc1. change (length (?a :: ?l)) with (length [a] + length l)%nat in Hc1.
    pose proof (proj2 (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _) Hc1)) as Hc2.
    cbn [length] in Hc2. rewrite Nat.add_1_r in Hc2. exact Hc2. }
  (* pj_set's text is keyed on ReaderRes.jr_strtod (no rp_sm binder): its position, run and window at that key, by
     crt_pos's strtod tie Esm *)
  pose proof Hpos as Hposk0. pose proof HRUNk as HRUNk'. rewrite Esm in Hposk0, HRUNk', HCONSk.
  (* the slots, the apartness, the key's bytes *)
  assert (HRAv1 : range_addressable (aview SEGS (w_H Wc) (ms_mem ms1)) SHADOW_OFF v 56).
  { apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAv].
    intros y Hy. unfold v, CRT_OFF_V in Hy. unfold shadow_of_addr. apply aview_eq_of. apply Hag12s.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold SHADOW_OFF. lia. }
  assert (HHVv1 : shadow_hull_vis (aview SEGS (w_H Wc) (ms_mem ms1)) v 56).
  { intros s0 Hs0. pose proof (HHVv s0 Hs0) as Hv0. intros E0. apply Hv0. rewrite <- E0. symmetry.
    apply aview_eq_of. apply Hag12s. unfold v, CRT_OFF_V, shadow_addr, SHADOW_OFF in *.
    rewrite unsigned_lit_small by lia. lia. }
  assert (HCRo : range_addressable (aview SEGS (w_H Wc) (ms_mem ms1)) SHADOW_OFF o 56) by exact HCR2.
  assert (HCHo : shadow_hull_vis (aview SEGS (w_H Wc) (ms_mem ms1)) o 56) by exact HCH2.
  assert (HSTKs : @STK_pj_set prh_img_A DOC_D + 240 <= STKC /\ 0 <= @STK_pj_set prh_img_A DOC_D)
    by (rewrite crt102rw_stkc; split; vm_compute; discriminate).
  pose proof (crt102rw_frame_slot LAWS HPRE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos (@STK_pj_set prh_img_A DOC_D) 0
    CRT_OFF_COPY (ms_regs ms1) Lamc HJ2 Hsp1 ltac:(lia) ltac:(lia) ltac:(unfold CRT_OFF_COPY; lia)
    ltac:(unfold CRT_OFF_COPY; lia) ltac:(reflexivity) HCRo HCHo) as Hslo.
  pose proof (crt102rw_frame_slot LAWS HPRE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos (@STK_pj_set prh_img_A DOC_D) 0
    CRT_OFF_V (ms_regs ms1) Lamc HJ2 Hsp1 ltac:(lia) ltac:(lia) ltac:(unfold CRT_OFF_V; lia)
    ltac:(unfold CRT_OFF_V; lia) ltac:(reflexivity) HRAv1 HHVv1) as Hslv.
  assert (Hdisj : forall bk, In bk [(ab, n0)] -> ~ In bk Db).
  { intros bk [<- | []]. exact (crt102rw_dx_head_fresh lyc Sc Hpc Wc (ms_mem ms1) _ (ab, n0) Db HAR2 HPB2
      ltac:(cbn [snd]; unfold n0; lia)). }
  assert (HwoffD : forall x0, v <= x0 < v + 56 -> ~ pj_footR o Db x0).
  { intros x0 Hx0. exact (crt102rw_local_off_tree LAWS lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0 CRT_OFF_V
      o Db x0 HL2 HDb ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)
      ltac:(right; unfold o, CRT_OFF_V, CRT_OFF_COPY; lia) ltac:(fold F; unfold v in Hx0; lia)). }
  assert (Hapart : pj_apartR [(ab, n0)] o).
  { intros b x0 Hb Hh Hx0. apply (crt102rw_local_off_blocks LAWS lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0
      CRT_OFF_COPY [(ab, n0)] x0 HL2 HDw ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia)
      ltac:(fold F; unfold o in Hx0; lia)).
    exists b. split; [exact Hb | exact Hh]. }
  assert (Hkoff : forall x0, CRT_MOD_AT_A <= x0 < CRT_MOD_AT_A + Z.of_nat (length ck_MOD_AT) + 1 ->
    ~ pj_footR o Db x0 /\ ~ pj_footR v [(ab, n0)] x0).
  { intros x0 Hx0. pose proof H0KM as (_ & _ & Hro).
    destruct (Hro x0 ltac:(lia)) as (Hr & _). pose proof (crt102rw_ro_img _ Hr) as Hi.
    split.
    - exact (crt102rw_img_off_foot lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0 CRT_OFF_COPY Db x0 HL2 HDb
        ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hi).
    - exact (crt102rw_img_off_foot lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0 CRT_OFF_V [(ab, n0)] x0 HL2
        HDw ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) Hi). }
  pose proof (prh_ledger_bounds B lyc Sc Hpc Wc (ms_mem ms1) Lamc peakc cntc SIZE_MAXZ 0 _ _ HLED2) as (_ & _ & Hcnt0 & _).
  pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran _ _ H0LED) as (_ & _ & Hcntg & _).
  pose proof (cm_cnt_string_set x t ms cnt HIN Et ltac:(lia)) as (Hc2a & Hc2b).
  set (FPk := (o, o + 56) :: (v, v + 56) :: ablocks_fp (PRH_FnPj.prhPj_hbl (Db ++ [(ab, n0)]))).
  refine (crt102rw_call LAWS HPRE fxk (@STK_pj_set prh_img_A DOC_D) FPk CRT_K_OFF (SIGMA AS_pj_set) Wc
    (TE regs rg []) _ ms1 _ lyc Sc Hpc kj pos ((ab, n0) :: Db) Lamc peakc cntc 0 0 _ HFZ HS eq_refl eq_refl HE2 HL2 HBR2 X1
    _ _ _ _ _ _ _).
  + unfold CRT_K_OFF. lia.
  + reflexivity.
  + lia.
  + lia.
  + (* the callee's footprint: copy's and v's windows (the frame's locals) and the blocks of both trees (fresh) *)
    intros a0 Hfa. unfold FPk in Hfa.
    apply inFP_cons in Hfa as [Hfa | Hfa].
    { right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite crt102rw_fb. try unfold in_zr in Hfa. cbn [fst snd] in Hfa.
      unfold o, CRT_OFF_COPY in Hfa. lia. }
    apply inFP_cons in Hfa as [Hfa | Hfa].
    { right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite crt102rw_fb. try unfold in_zr in Hfa. cbn [fst snd] in Hfa.
      unfold v, CRT_OFF_V in Hfa. lia. }
    right; left. destruct Hfa as ((b & e) & Hb & Hab). unfold ablocks_fp, PRH_FnPj.prhPj_hbl in Hb.
    rewrite map_map, in_map_iff in Hb. destruct Hb as ((bb & kb) & Eb & Hbb). cbn [fst snd] in Eb. injection Eb as <- <-.
    assert (Hbx : In (bb, kb) ((ab, n0) :: Db)).
    { apply in_app_or in Hbb as [Hbb | Hbb]; [right; exact Hbb | left; destruct Hbb as [<- | []]; reflexivity]. }
    pose proof (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms1) Lamc peakc cntc SIZE_MAXZ 0 bb kb _ _ HLED2 (HDx _ Hbx))
      as (Hk0 & _).
    destruct (crt102rw_fresh lyc Sc Hpc Wc (ms_mem ms1) _ ((ab, n0) :: Db) bb kb HAR2 HPB2 Hbx Hk0) as (Hin1 & Hnin1).
    exists (bb - cf_head), (kb + cf_head). split; [exact Hin1|]. split; [exact Hnin1|].
    try unfold in_zr in Hab. cbn [fst snd] in Hab. change (@cf_head CfParams_preset) with 16 in *. lia.
  + (* the callee: pj_set's text at the call's binders, window d = 0, dd = DOC_D *)
    intros ch1 HPRE1.
    pose proof HPRE1 as ((_ & _ & _ & _ & _ & Hstk1 & _) & _).
    pose proof Hstk1 as (Hal1 & Hstk01 & Hceil1 & Hslo1 & Hshi1 & H471 & Hbot1 & Htop1 & Htop21).
    eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    * refine (PJSET fxk rp_x rp_os (rp_i + length pre + 1)%nat rp_H0 hist most 0 lyc Sc Hpc Wc (ms_regs ms1) (ms_mem ms1) _
        ch1 0 o CRT_MOD_AT_A v ms (PjTree.JStr ck_STAMP) Db [(ab, n0)] num str kids keys n cap ck_MOD_AT Lamc peakc cntc
        SIZE_MAXZ 0 HPRE1 H0CL HROOM2 Hposk0 HOS4 HCONSk X10 X11 X12 _ _ Hhdr Hcap54 Hslo HNDw Hslv _ Hdisj HwoffD Hapart
        _ _ _
        _ Hkoff HLED2 _ (cm_rq_key t H0RQ) (cm_rq_grow t H0RQ n cap ltac:(rewrite En, Et; reflexivity)) Hroom _ HFOo _
        HRUNk').
      ++ unfold fwin. split; [lia|]. split; [reflexivity|]. split; [lia|]. intros a0 Ha0. lia.
      ++ rewrite <- Et. exact HNDo.
      ++ unfold v, CRT_OFF_V. lia.
      ++ pose proof (cm_in_depth_doc x t HIN) as Hd. rewrite Et in Hd. lia.
      ++ cbn [PjTree.depth]. unfold DOC_D. lia.
      ++ exact (crt_cstr_modat_A LAWS zs_aligned img_shadow_vis_x lyc Sc Hpc Wc (ms_mem ms1) _ HAR2 HRO2 H0KM).
      ++ right; right; exact H0KM.
      ++ unfold SIZE_MAXZ. lia.
      ++ rewrite <- Et. exact HTB.
      ++ reflexivity.
    * (* the text's post at wle' (fpostWmR at RZW), window 0: the call rule's float form at RZW *)
      intros W' c' _ HPo. exact (crt102rw_postW0R fxk _ _ _ _ _ _ _ _ _ _ _ _ HFZ HPo).
  + (* the return at K *)
    intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP
      ((HROOMs & Lam' & peak' & fail' & ran' & res & c & ok & Lr & Do & Ra0 & HLEDk & Hoks & Hfa &
        HPLr & HPLo & Hblk & Hzw & Hposk & Hnoref & Hdeadk & Harms) & HMNk).
    assert (HFK3 : fregs_kept_x fx fx') by (intros r0 Hr0; rewrite (HFK2 r0 Hr0); exact (HFK r0 Hr0)).
    assert (Efail : fail' = SIZE_MAXZ).
    { destruct Hfa as (Hf1 & Hf2). destruct (Z_le_gt_dec cntc SIZE_MAXZ) as [Hle|Hgt];
        [destruct (Z_lt_ge_dec SIZE_MAXZ (cntc + Z.of_nat c)) as [Hlt|Hge] |].
      - rewrite (Hf1 ltac:(lia)). reflexivity.
      - exact (Hf2 ltac:(lia)).
      - unfold SIZE_MAXZ in *. lia. }
    subst fail'.
    pose proof HJ2 as (HAR2' & _).
    (* the call's footprint: copy's and v's windows (the frame's locals) and the hulls of the two trees' blocks *)
    assert (HFPw : forall a0, inFP FPk a0 ->
      (o <= a0 < o + 56) \/ (v <= a0 < v + 56) \/
      exists bb kb, In (bb, kb) ((ab, n0) :: Db) /\ bb - cf_head <= a0 < bb - cf_head + req_size (kb + cf_head)).
    { intros a0 Hf. unfold FPk in Hf. apply inFP_cons in Hf as [Hf | Hf].
      { left. try unfold in_zr in Hf. cbn [fst snd] in Hf. exact Hf. }
      apply inFP_cons in Hf as [Hf | Hf].
      { right; left. try unfold in_zr in Hf. cbn [fst snd] in Hf. exact Hf. }
      right; right. destruct (crt102rw_fp_hull _ a0 Hf) as (bb & kb & Hbb & Hy).
      exists bb, kb. split; [|exact Hy]. apply in_app_or in Hbb as [Hbb | [<- | []]]; [right; exact Hbb | left; reflexivity]. }
    assert (Hhull : forall bb kb y, In (bb, kb) ((ab, n0) :: Db) -> bb - cf_head <= y < bb - cf_head + req_size (kb + cf_head) ->
      4096 <= y < YM05.alloc_ceiling /\ in_app y 1 /\ ~ (F <= y < F + 512)).
    { intros bb kb y Hbb Hy.
      destruct (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms1) Lamc peakc cntc SIZE_MAXZ 0 bb kb _ _ HLED2 (HDx _ Hbb))
        as (Hk0 & Hab & _).
      destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms1) _ _ _ HAR2 Hab) as (_ & B4096 & Bce & Bapp & _).
      pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms1) _ _ _ CRT_CID pos HAR2 Hab Hin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite crt102rw_fb in Hd. fold F in Hd.
      change (@cf_head CfParams_preset) with 16 in *.
      pose proof (req_size_pos (kb + 16) ltac:(lia)).
      split; [lia|]. split; [apply (in_app_sub _ _ _ _ Bapp); lia | lia]. }
    assert (HFPa : forall a0, inFP FPk a0 -> a0 < YM05.alloc_ceiling /\ in_app a0 1).
    { intros a0 Hf. destruct (HFPw a0 Hf) as [Hw | [Hw | (bb & kb & Hbb & Hy)]].
      - unfold o, CRT_OFF_COPY in Hw. split; [lia|]. apply (in_app_sub _ _ _ _ Fb3); lia.
      - unfold v, CRT_OFF_V in Hw. split; [lia|]. apply (in_app_sub _ _ _ _ Fb3); lia.
      - destruct (Hhull bb kb a0 Hbb Hy) as (H1 & H2 & _). split; [lia | exact H2]. }
    assert (HFP3 : forall a0, inFP FPk a0 -> a0 < YM05.alloc_ceiling /\ in_app a0 1 /\ ~ (F + 504 <= a0 < F + 512)).
    { intros a0 Hf. destruct (HFPa a0 Hf) as (H1 & H2). split; [exact H1|]. split; [exact H2|].
      destruct (HFPw a0 Hf) as [Hw | [Hw | (bb & kb & Hbb & Hy)]].
      - unfold o, CRT_OFF_COPY in Hw. lia.
      - unfold v, CRT_OFF_V in Hw. lia.
      - destruct (Hhull bb kb a0 Hbb Hy) as (_ & _ & H3). lia. }
    assert (HFP0 : Forall (fun r => 0 < fst r) FPk).
    { unfold FPk. constructor; [cbn [fst]; unfold o, CRT_OFF_COPY; lia|]. constructor; [cbn [fst]; unfold v, CRT_OFF_V; lia|].
      apply Forall_forall. intros (b0 & e0) Hb0. unfold ablocks_fp, PRH_FnPj.prhPj_hbl in Hb0.
      rewrite map_map, in_map_iff in Hb0. destruct Hb0 as ((bb & kb) & Eb & Hbb). cbn [fst snd] in Eb |- *. injection Eb as <- <-.
      assert (Hbb' : In (bb, kb) ((ab, n0) :: Db))
        by (apply in_app_or in Hbb as [Hbb | [<- | []]]; [right; exact Hbb | left; reflexivity]).
      destruct (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms1) Lamc peakc cntc SIZE_MAXZ 0 bb kb _ _ HLED2 (HDx _ Hbb'))
        as (Hk0 & Hab & _).
      destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms1) _ _ _ HAR2 Hab) as (_ & B4096 & _).
      change (@cf_head CfParams_preset) with 16 in *. lia. }
    assert (HFPD : forall a0, inFP FPk a0 -> ~ pj_footR doc D a0).
    { intros a0 Hf. destruct (HFPw a0 Hf) as [Hw | [Hw | (bb & kb & Hbb & Hy)]].
      - exact (crt102rw_local_off_doc LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0 CRT_OFF_COPY a0
          HL2 ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) ltac:(fold F; unfold o in Hw; lia)).
      - exact (crt102rw_local_off_doc LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0 CRT_OFF_V a0
          HL2 ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) ltac:(fold F; unfold v in Hw; lia)).
      - exact (crt102rw_hull_off_doc lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0 bb kb a0 HL2 Hbb Hy). }
    destruct (crt102rw_call_keep LAWS HPRE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ _ ly2 S2 Hp2 W2 mem2 md2 k1 HJ2 HJc HFPa)
      as (EF2 & KS2 & KSH2).
    fold F in EF2, KSH2.
    (* the blocks held after the call *)
    destruct Hblk as (other & Ho1 & Ho2).
    assert (HD1 : Permutation ((ab, n0) :: Db) (Db ++ [(ab, n0)])) by apply Permutation_cons_append.
    assert (HPLr' : Permutation Lamc ((Db ++ [(ab, n0)]) ++ Lr)) by (rewrite <- app_assoc; exact HPLr).
    destruct (crt102rw_blocks_step lyc Sc ly2 S2 Lamc Lam' ((ab, n0) :: Db) (Db ++ [(ab, n0)]) Do Lr other HPL2 HPB2 HD1
      HPLr' HPLo Ho1 Ho2) as (HPL3 & HPB3).
    (* the document's blocks stay held: they are in Lamc and apart from what pj_set touched *)
    assert (HDL3 : forall bk, In bk D -> In bk Lam').
    { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL3)). apply in_or_app. right.
      pose proof (Permutation_in _ HPL2 (HDL2 _ Hbk)) as Hx. apply in_app_or in Hx as [Hx | Hx]; [|exact Hx].
      exfalso. exact (HAP2 _ Hx Hbk). }
    assert (HrelDo : forall a' k', In (a', k') Do ->
      In (a', k') ((ab, n0) :: Db) \/ ~ In (a' - cf_head, k' + cf_head) (ablocks B lyc Sc)).
    { intros a' k' Hk'.
      destruct Harms as [(Hin1 & Ec & Er & Epk & (i0 & vi & Di0 & Dr & Hi0 & Hlt & HNi & HPD & HPDo) & HNo) |
                        [(Hnin & Hnf & Ec & Hoks2 & Er & Epk & (Dold & Dnew & Dr & a2 & HPD & HPDo & Hnew & Hshape) & HNo) |
                         (Hnin & Hc1 & Hokc & Hoks2 & Er & Epk & (Dold & Dnew & Dr & HPD & HPDo & Hnew & Hshape) & HFDo & HNo)]].
      - left. pose proof (Permutation_in _ HPDo Hk') as Hx. apply in_app_or in Hx as [Hx | [<- | []]]; [|left; reflexivity].
        right. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. exact Hx.
      - pose proof (Permutation_in _ HPDo Hk') as Hx. rewrite in_app_iff in Hx. destruct Hx as [Hx | [Ex | Hx]].
        + destruct (Hnew a' k' (in_or_app _ _ _ (or_introl Hx))) as [Ho | Hn]; [|right; exact Hn].
          left; right. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. left. exact Ho.
        + assert (Hx2 : In (a', k') (Dnew ++ [(a2, Z.of_nat (length ck_MOD_AT) + 1)]))
            by (apply in_or_app; right; left; exact Ex).
          destruct (Hnew a' k' Hx2) as [Ho | Hn]; [|right; exact Hn].
          left; right. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. left. exact Ho.
        + rewrite in_app_iff in Hx. destruct Hx as [Hx | [<- | []]]; [|left; left; reflexivity].
          left; right. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. exact Hx.
      - pose proof (Permutation_in _ HPDo Hk') as Hx. apply in_app_or in Hx as [Hx | Hx].
        + right. exact (Hnew a' k' Hx).
        + left; right. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. exact Hx. }
    pose proof (crt102rw_apart_step lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0 Do HL2 HrelDo) as HAP3.
    assert (Hpk3 : peakc <= peak').
    { destruct Harms as [(_ & _ & _ & Epk & _) | [(_ & _ & _ & _ & _ & Epk & _) | (_ & _ & _ & _ & _ & Epk & _)]];
        rewrite Epk; lia. }
    pose proof (crt102rw_side_call LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0 _ _
      ly2 S2 Hp2 W2 mem2 md2 k1 Lam' peak' (cntc + Z.of_nat c) 0 ran' HL2 HJc HFP0 HFPD HLEDk Hpk3 HROOMs HDL3) as HSD3.
    pose proof (crt102rw_live_call LAWS HPRE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ Lamc peakc cntc 0 0 _ _
      ly2 S2 Hp2 W2 mem2 md2 k1 Do Lam' peak' (cntc + Z.of_nat c) 0 ran' HL2 HJe HJc ltac:(lia) HFP3 HSD3 HPL3 HPB3 HAP3 HMNk)
      as HL3.
    (* the registers *)
    assert (HDR3 : dregsA regs2 F).
    { refine {| crt_dregs_bregs := {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _;
                  crt_bregs_s1 := _; crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _;
                  crt_bregs_s10 := _; crt_bregs_s11 := _ |}; crt_dregs_s5 := _ |};
      [ rewrite (ts_ap (ms_regs ms1) regs2 2%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 3%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 4%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 8%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 9%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 18%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 20%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 19%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 23%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 26%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 27%bv HP) by ts_cs
      | rewrite (ts_ap (ms_regs ms1) regs2 21%bv HP) by ts_cs ];
      rewrite !KR2 by (cbv; tauto); assumption. }
    (* the two locals stay open *)
    assert (HRAb1 : range_addressable (aview SEGS (w_H Wc) (ms_mem ms1)) SHADOW_OFF (F + CRT_OFF_BACK) 56).
    { apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAb].
      intros y Hy. unfold CRT_OFF_BACK in Hy. unfold shadow_of_addr. apply aview_eq_of. apply Hag12s.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold SHADOW_OFF. lia. }
    destruct (crt102rw_local_keep Wc W2 (ms_mem ms1) mem2 F CRT_OFF_BACK ltac:(lia) F32 Fb2 KSH2
      ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) as (LB1 & _).
    destruct (crt102rw_local_keep Wc W2 (ms_mem ms1) mem2 F CRT_OFF_V ltac:(lia) F32 Fb2 KSH2
      ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)) as (LV1 & _).
    (* copy freeable at DOC_D *)
    pose proof (cm_in_depth_doc x t HIN) as Hdep. rewrite Et in Hdep.
    assert (HFDo : pj_fdR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') DOC_D o Do).
    { destruct Harms as [(_ & _ & _ & _ & _ & HNo) | [(_ & _ & _ & _ & _ & _ & _ & HNo) | (_ & _ & _ & _ & _ & _ & _ & HFDo & _)]].
      - apply (crt102rw_fdR_mono SEGS _ _ (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))));
          [|first [exact (crt102rw_nodeR_fdR SEGS _ _ _ _ _ HNo) | exact (crt102rw_nodeR_fdR SEGS _ _ _ _ _ (proj1 HNo))]].
        pose proof (cm_set_depth ms ck_MOD_AT (PjTree.JStr ck_STAMP)). cbn [PjTree.depth] in *. unfold DOC_D in *. lia.
      - apply (crt102rw_fdR_mono SEGS _ _ (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))));
          [|first [exact (crt102rw_nodeR_fdR SEGS _ _ _ _ _ HNo) | exact (crt102rw_nodeR_fdR SEGS _ _ _ _ _ (proj1 HNo))]].
        pose proof (cm_set_depth ms ck_MOD_AT (PjTree.JStr ck_STAMP)). cbn [PjTree.depth] in *. unfold DOC_D in *. lia.
      - apply (crt102rw_fdR_mono SEGS _ _ (PjTree.depth (PjTree.JObj ms))); [exact Hdep | exact HFDo]. }
    (* the outcome: res = 0, or res = -1 with g_ran_out = 1. THE REQUEST BOUND: the key's strdup and grow's kids / keys
       reallocs are within g_most (Crt102Model.cm_rqa_key / cm_rqa_grow / cm_rqa_grow_keys at RQA_crt t <= most), so a
       refusal among them sets g_ran_out - prh_oks' third conjunct, which is true of the merged alloc.c exactly under
       that bound *)
    pose proof (cm_rqa_key t most H0RQA) as Hrq_key. pose proof (cm_rqa_grow t most H0RQA) as Hrq_grow.
    pose proof (cm_rqa_grow_keys t most H0RQA) as Hrq_keys.
    assert (Hc3 : (c <= 3)%nat).
    { pose proof (cm_set_trace_len n cap ck_MOD_AT) as Ht.
      destruct Harms as [(_ & Ec & _) | [(_ & _ & Ec & _) | (_ & Hc1 & _)]];
        [lia | rewrite Ec, Ht; destruct (n =? cap); lia | rewrite Ht in Hc1; destruct (n =? cap); lia]. }
    assert (Hcin : In ck_MOD_AT (map fst ms) -> c = 0%nat).
    { intros Hin1. destruct Harms as [(_ & Ec & _) | [(Hnin & _) | (Hnin & _)]]; [exact Ec | exfalso; exact (Hnin Hin1) |
        exfalso; exact (Hnin Hin1)]. }
    rewrite <- EF2 in HDR3.
    destruct (Z.eq_dec res 0) as [Er0 | Ern].
    2:{ (* res = -1 (pj_set's "absent, the c-th allocation failed" arm): DEAD AT ITS SOURCE. tpj_set_specX's
         DEAD-PJSET conjunct (PRH_FnPj.v:1046, Hdeadk) gives res = 0 when the call's window lies below the chosen
         failure: g_fail_at = SIZE_MAX and g_count + |trace| <= g_count + 3 is below it (Crt102Model.cm_set_trace_len,
         cm_cnt_string_set) *)
      exfalso. apply Ern. apply Hdeadk. right. rewrite cm_set_trace_len. unfold SIZE_MAXZ.
      destruct (n =? cap); lia. }
    (* res = 0: the granted arms leave g_ran_out as it was (0): the present arm makes no call, the absent-taken arm's
       calls were all taken (prh_oks' second conjunct) *)
    assert (Eran : ran' = 0).
    { destruct Hoks as (_ & [Hr | (_ & i0 & Hi0 & Hni0 & _)] & _); [exact Hr|].
      destruct Harms as [(_ & Ec & _) | [(_ & _ & _ & Hall & _) | (_ & _ & _ & _ & Er & _)]];
        [lia | unfold prh_refused in Hni0; rewrite (Hall i0 Hi0) in Hni0; discriminate Hni0 |
         rewrite Er0 in Er; discriminate Er]. }
    apply (crt102rw_atK fx' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Do Lam' peak' (cntc + Z.of_nat c) ran' regs2 res c ms
      HFZ2 HFK3 HL3 HDR3 Ra0); rewrite ?EF2.
    * exact (LB1 HRAb1).
    * exact (LV1 HRAv1).
    * exact HFDo.
    * exact Et.
    * lia.
    * exact Hc3.
    * exact Hcin.
    * exact Er0.
    * exact Eran.
    * (* THE GO BRANCH (res = 0, ran' = 0) *)
      intros fx3 ly3 W3 mem3 md3 k3 regs3 memm mdm HFZ3 HFK4 HL4 HBR4 X22g X24g Ra0g X25g EF3 Hmm HARm HJg HRAb4
        HRAv4 HFD4.
      (* copy's tree at the go state: arms 1 / 2 (res = 0) give it at K; O1's run wrote nothing, the call's footprint is
         empty *)
      assert (HNoK : pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') o (ck_crt_tree t) Do).
      { rewrite Et, cm_crt_tree_obj.
        destruct Harms as [(_ & _ & _ & _ & _ & HNo) | [(_ & _ & _ & _ & _ & _ & _ & HNo) | (_ & _ & _ & _ & Er & _)]];
          [first [exact HNo | exact (proj1 HNo)] | first [exact HNo | exact (proj1 HNo)] | rewrite Er0 in Er; discriminate Er]. }
      assert (HAGm : pj_agreeR SEGS (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memm) (pj_footR o Do)).
      { intros y _. assert (E : mrestrict (w_H W2) memm (Z_to_bv 64 y) = mrestrict (w_H W2) mem2 (Z_to_bv 64 y)) by apply Hmm.
        split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
      pose proof (pj_nodeR_frame SEGS _ _ _ (prh_lin Lam') o Do HNoK HAGm) as HNoM.
      pose proof (crt_side_ledger (crt_live_side HL4)) as HLED4.
      assert (HDo3 : forall bk, In bk Do -> In bk Lam')
        by (intros bk Hbk; apply (Permutation_in _ (Permutation_sym HPL3)); apply in_or_app; left; exact Hbk).
      assert (HcF2 : exists cid0 pos0, In (cid0, pos0) (frames S2) /\ frame_addr ly2 cid0 pos0 <= o /\
        o + 56 <= frame_addr ly2 cid0 pos0 + fs_frame_bytes cid0).
      { exists CRT_CID, pos. destruct (crt_live_journal HL3) as (WS_HJ3 & HJ3 & HB_HJ3).
        destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ3) as (Hin3 & _).
        split; [exact Hin3|]. rewrite crt102rw_fb, EF2. unfold o, CRT_OFF_COPY. lia. }
      pose proof (crt102rw_tree_call LAWS ly2 S2 Hp2 W2 memm mdm (kj + k1) _ _ ly3 S2 Hp2 W3 mem3 md3 k3 Lam' peak'
        (cntc + Z.of_nat c) ran' Lam' peak' (cntc + Z.of_nat c) 0 o (ck_crt_tree t) Do HARm HJg
        (crt102rw_ledger_agree _ _ _ _ _ _ _ _ _ _ _ _ _ HLEDk Hmm) HLED4 HcF2 HDo3 HDo3
        (fun a0 Hf => False_ind _ (inFP_nil a0 Hf)) HNoM) as HNo3.
      (* copy's ORDERED free list at the go state (FREEORD-COPY): tpj_set_specX's result order on the granted arms
         (PRH_FnPj.v:1104-1129 / :1155-1176), at val = pj_string's node (crt102rw_stamp_fo; MOD_KEY has no special
         character) and nn := DOC_D, framed over O1's run (no write) and fuzz_alloc_ran_out's empty footprint as copy's
         tree just above *)
      assert (HFO3 : crt102rw_copy_fo W3 mem3 Lam' o Do).
      { assert (EJ : crt_tree_J (t := t) = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))
          by (unfold crt_tree_J; rewrite Et, <- cm_crt_tree_obj; reflexivity).
        assert (HdepJ : (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) <= DOC_D)%nat)
          by (pose proof (cm_set_depth ms ck_MOD_AT (PjTree.JStr ck_STAMP)); cbn [PjTree.depth] in *; unfold DOC_D in *;
              lia).
        assert (HHD : @cf_head CfParams_preset = PresetReqAt.HEAD) by reflexivity.
        pose proof (crt102rw_stamp_fo Wc (ms_mem ms1) Lamc v ab HNDw) as HFW.
        assert (HFOK : exists Fk, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') DOC_D o Do Fk /\
          map (fun b => snd b + cf_head) Fk =
            PresetReqAt.fo (PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))).
        { destruct Harms as [(_ & _ & _ & _ & _ & _ & _ & HFOa) | [(_ & _ & _ & _ & _ & _ & _ & _ & _ & HFOa) |
                            (_ & _ & _ & _ & Er & _)]].
          - exact (HFOa HHD HFW DOC_D HdepJ).
          - exact (HFOa HHD HFW ltac:(vm_compute; reflexivity) DOC_D HdepJ).
          - rewrite Er0 in Er; discriminate Er. }
        destruct HFOK as (Fk & HFk & HFke). exists Fk. split; [|rewrite EJ; exact HFke].
        exact (crt102rw_fo_call ly2 S2 Hp2 W2 memm mdm (kj + k1) _ _ ly3 S2 Hp2 W3 mem3 md3 k3 Lam' peak'
          (cntc + Z.of_nat c) ran' Lam' peak' (cntc + Z.of_nat c) 0 o DOC_D Do Fk HARm HJg
          (crt102rw_ledger_agree _ _ _ _ _ _ _ _ _ _ _ _ _ HLEDk Hmm) HLED4 HcF2 HDo3 HDo3
          (fun a0 Hf => False_ind _ (inFP_nil a0 Hf))
          (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lam') (prh_lin Lam') o Do Fk HFk (fun a k Hk => HDo3 (a, k) Hk)
             HAGm)). }
      (* the sizes of copy's blocks *)
      assert (Hsz : forall a0 k0, In (a0, k0) Do -> 0 <= k0 < 2 ^ 32).
      { intros a0 k0 Hk0.
        destruct Harms as [(_ & _ & _ & _ & (i0 & vi & Di0 & Dr & Hi0 & Hlt & HNi & HPD & HPDo) & _) |
                          [(_ & _ & _ & _ & _ & _ & (Dold & Dnew & Dr & a2 & HPD & HPDo & Hnew & Hshape) & _) |
                           (_ & _ & _ & _ & Er & _)]]; [| | rewrite Er0 in Er; discriminate Er].
        - pose proof (Permutation_in _ HPDo Hk0) as Hx. apply in_app_or in Hx as [Hx | [Ex | []]].
          + apply (cm_db_small x t Db HIN HDbl a0 k0). apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app.
            right. exact Hx.
          + injection Ex as <- <-. unfold n0. cbn. lia.
        - pose proof (Permutation_in _ HPDo Hk0) as Hx. rewrite in_app_iff in Hx.
          destruct Hx as [Hx | [Ex | Hx]].
          + destruct Hshape as [(_ & _ & ->) | (Encap & _ & k' & y' & ->)]; [destruct Hx|].
            pose proof (cm_grow_small x t HIN) as (G1 & G2). rewrite Et, cm_members_obj, <- En, Encap in G1, G2.
            destruct Hx as [Ex | [Ex | []]]; injection Ex as <- <-; lia.
          + injection Ex as <- <-. cbn. lia.
          + rewrite in_app_iff in Hx. destruct Hx as [Hx | [Ex | []]].
            * apply (cm_db_small x t Db HIN HDbl a0 k0). apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app.
              right. exact Hx.
            * injection Ex as <- <-. unfold n0. cbn. lia. }
      destruct (Hposk Er0) as (hist' & Hpos3). rewrite <- Esm in Hpos3. rewrite En, Ecap in Hpos3.
      subst ran'.
      rewrite ?EF2 in HBR4, HRAb4, HRAv4.
      assert (EF4 : frame_addr ly3 CRT_CID pos = F) by (rewrite EF3; exact EF2).
      (* the three spills at the go state: kept by the pj_set call and by fuzz_alloc_ran_out's *)
      pose proof (crt102rw_spills_keep Wc W2 (ms_mem ms1) mem2 ms KS2 HSP1) as HSP2.
      pose proof (crt102rw_spills_agree W2 mem2 memm ms Hmm HSP2) as HSP2m.
      pose proof HJg as (_ & _ & _ & _ & _ & _ & _ & _ & KSg & _).
      assert (HSP3 : crt102rw_spills W3 mem3 ms).
      { apply (crt102rw_spills_keep W2 W3 memm mem3 ms); [|exact HSP2m]. intros a0 Ha0. apply KSg; lia. }
      (* copy's blocks against tblk of the rewritten tree (pj_set's granted arms, at val = pj_string's node) *)
      assert (HTBv : Permutation (map (fun b => snd b + cf_head) [(ab, n0)]) (PresetReqAtNoMiss.tblk (PjTree.JStr ck_STAMP)))
        by (vm_compute; apply Permutation_refl).
      assert (HTBo : Permutation (map (fun b => snd b + cf_head) Do) (PresetReqAtNoMiss.tblk (ck_crt_tree t))).
      { rewrite Et, cm_crt_tree_obj.
        destruct Harms as [(_ & _ & _ & _ & _ & _ & HTo & _) | [(_ & _ & _ & _ & _ & _ & _ & _ & HTo & _) |
                          (_ & _ & _ & _ & Er & _)]].
        - exact (HTo HTBv).
        - exact (HTo eq_refl HTBv ltac:(vm_compute; reflexivity)).
        - rewrite Er0 in Er; discriminate Er. }
      (* the bytes copy's blocks occupy: rtt (doc, 0)'s copy, the stamp moved in, pj_set's key and grown arrays *)
      assert (HBSo : YCbq.bsum (ck_hblks Do) <= LIVE_round_trip_text t false + LIVE_round_trip_text t true +
        PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
        PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT))).
      { pose proof (cm_copy_room_rtt t Db (cm_in_wf x t HIN) HDbl HDbn) as HRdb.
        pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & N3 & N4 & N5 & N6).
        assert (Hnn : forall L, (forall bk, In bk L -> In bk Lamc) -> 0 <= YCbq.bsum (ck_hblks L)).
        { intros L HL0. apply crt102rw_bsum_nonneg. intros a0 k0 Hk0.
          exact (proj1 (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms1) Lamc peakc cntc SIZE_MAXZ 0 a0 k0 _ _ HLED2
            (HL0 _ Hk0))). }
        assert (Ew : YCbq.bsum (ck_hblks [(ab, n0)]) = PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)))
          by (rewrite cm_bsum_hblks; unfold PRH_FnPj.LIVE_pj_string, n0; cbn [Ledger.lsum length]; lia).
        assert (Emem : ck_members t = Z.of_nat (length ms)) by (rewrite Et; apply cm_members_obj).
        destruct Harms as [(_ & _ & _ & _ & (i0 & vi & Di0 & Dr & Hi0 & Hlt & HNi & HPD & HPDo) & _) |
                          [(_ & _ & _ & _ & _ & _ & (Dold & Dnew & Dr & a2 & HPD & HPDo & Hnew & Hshape) & _) |
                           (_ & _ & _ & _ & Er & _)]].
        - rewrite (cm_bsum_hblks_perm _ _ HPDo), cm_bsum_hblks_app, Ew.
          rewrite (cm_bsum_hblks_perm _ _ HPD), cm_bsum_hblks_app in HRdb.
          assert (0 <= YCbq.bsum (ck_hblks Di0)).
          { apply Hnn. intros bk Hbk. apply HDb. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. left. exact Hbk. }
          lia.
        - rewrite (cm_bsum_hblks_perm _ _ HPDo).
          replace (Dnew ++ (a2, Z.of_nat (length ck_MOD_AT) + 1) :: Dr ++ [(ab, n0)])
            with (Dnew ++ [(a2, Z.of_nat (length ck_MOD_AT) + 1)] ++ Dr ++ [(ab, n0)]) by reflexivity.
          rewrite !cm_bsum_hblks_app, Ew.
          rewrite (cm_bsum_hblks_perm _ _ HPD), cm_bsum_hblks_app in HRdb.
          assert (0 <= YCbq.bsum (ck_hblks Dold)).
          { apply Hnn. intros bk Hbk. apply HDb. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. left. exact Hbk. }
          assert (Ek : YCbq.bsum (ck_hblks [(a2, Z.of_nat (length ck_MOD_AT) + 1)]) = Z.of_nat (length ck_MOD_AT) + 1 + 16)
            by (rewrite cm_bsum_hblks; cbn [Ledger.lsum length]; change (@cf_head CfParams_preset) with 16; lia).
          rewrite Ek. unfold PRH_FnPj.LIVE_pj_set in *. rewrite Z.eqb_refl in *. change (@cf_head CfParams_preset) with 16 in *.
          assert (Hg0 : 0 <= PRH_FnReader.LIVE_grow 6 (ck_members t)).
          { unfold PRH_FnReader.LIVE_grow, cap2R. rewrite Emem. destruct (Z.of_nat (length ms) =? 0); cbn; lia. }
          destruct Hshape as [(_ & _ & ->) | (Encap & _ & k' & y' & ->)].
          + change (YCbq.bsum (ck_hblks [])) with 0. lia.
          + assert (Ecm : cap = ck_members t) by (rewrite Emem, <- En; lia).
            rewrite cm_bsum_hblks. cbn [Ledger.lsum length]. unfold PRH_FnReader.LIVE_grow. rewrite Ecm. cbn. lia.
        - rewrite Er0 in Er; discriminate Er. }
      assert (Hdepc : (PjTree.depth (ck_crt_tree t) <= DOC_D)%nat).
      { rewrite Et, cm_crt_tree_obj. pose proof (cm_set_depth ms ck_MOD_AT (PjTree.JStr ck_STAMP)).
        cbn [PjTree.depth] in *. unfold DOC_D in *. lia. }
      apply (HWGO HL0K fx3 ly3 S2 Hp2 W3 mem3 md3 (kj + k1 + k3) pos regs3 Do Lam' peak' (cntc + Z.of_nat c) c ms
        HFZ3 HFK4 HL4); rewrite ?EF4.
      -- exact HBR4.
      -- exact X22g.
      -- exact X24g.
      -- exact Ra0g.
      -- exact X25g.
      -- exact HRAb4.
      -- exact HRAv4.
      -- exact Et.
      -- exact HNo3.
      -- exact Hsz.
      -- exact HTBo.
      -- exact Hdepc.
      -- exact HFO3.
      -- exact HSP3.
      -- exact HBSo.
      -- lia.
      -- exact Hc3.
      -- exact Hcin.
      -- exact (crt102rw_pos_W ms pre hist' S2 Esm Ert Hrun Hcons Hpos3).
- (* a0 <> 0 is not this arm *)
  exfalso. rewrite branch_eq_U, !ts_U0, U_SLit in Hc.
  assert (A42 : ew (TE regs rg []) 42 = getr rg 10) by (apply (te_cur regs rg [] 10%bv 10); reflexivity).
  rewrite A42, R10 in Hc. vm_compute in Hc. discriminate.
Qed.

Lemma crt102rw_at_U : crt102rw_Wgo_goal -> crt102rw_L0K ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms,
  atU fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_U_OFF rg memc mdc) QFa.
Proof.
intros HWGO HL0K fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms HU.
pose proof (crt_at_U_live HU) as HL. pose proof (crt_at_U_frm_zero HU) as HFZ.
pose proof (crt_at_U_fregs HU) as HFK. pose proof (crt_at_U_dregs HU) as HDR.
pose proof (crt_at_U_obj HU) as Et. pose proof (crt_at_U_tree_ok HU) as HTOK.
pose proof (crt_at_U_copy HU) as HCT. pose proof (crt_at_U_db_fresh HU) as HDbf.
pose proof (crt_at_U_db_lsz HU) as HDbl. pose proof (crt_at_U_db_nlive HU) as HDbn.
pose proof (crt_at_U_cnt HU) as HCNTc. pose proof (crt_at_U_pos HU) as HPOSU.
pose proof (crt_at_U_copy_tblk HU) as HTBLK. pose proof (crt_at_U_copy_cap HU) as HCAPU.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_sp (crt_dregs_bregs HDR)) as R2.
pose proof (crt_bregs_gp (crt_dregs_bregs HDR)) as R3.
pose proof (crt_bregs_tp (crt_dregs_bregs HDR)) as R4.
pose proof (crt_bregs_s0 (crt_dregs_bregs HDR)) as R8.
pose proof (crt_bregs_s1 (crt_dregs_bregs HDR)) as R9.
pose proof (crt_bregs_s2 (crt_dregs_bregs HDR)) as R18.
pose proof (crt_bregs_s4 (crt_dregs_bregs HDR)) as R20.
pose proof (crt_bregs_s3 (crt_dregs_bregs HDR)) as R19.
pose proof (crt_bregs_s7 (crt_dregs_bregs HDR)) as R23.
pose proof (crt_bregs_s10 (crt_dregs_bregs HDR)) as R26.
pose proof (crt_bregs_s11 (crt_dregs_bregs HDR)) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt102rw_sp HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof (crt102rw_doc_home LAWS HPRE HTREE) as (Hd1 & Hd2 & Hd3 & Hd4).
pose proof (YM05.alloc_ceiling_val) as Hcv.
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (crt102rw_SH_entry (regs := regs) fxk (CRT_PC_A + CRT_U_OFF) Wc memc rg F R18 ltac:(lia) ltac:(lia)
  (fun i Hi => proj1 (Fsh i Hi))) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
assert (X18 : bv_unsigned (ew (TE regs rg []) (xr 18)) = shadow_addr F).
{ unfold xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
pose proof HMNc as HPM.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
unfold crt_cfg.
(* ---- U1: the fourteen unpoison stores ---- *)
paj_run_to_tok_x_inv (RUNTO WS_HJ) HS HJ SHOK HPM (2 ^ 63, 2 ^ 63) (CRT_PC_A + crt102rw_U2_OFF).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 18) (shadow_addr F)); [reflexivity | exact X18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists CRT_CID, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite crt102rw_fb. change (512 / 8) with 64.
    fold F. lia. }
  apply awr_ok_nil. }
pmkst HS.
set (WSH := ss_mem (crt102rw_ssSH (CRT_PC_A + CRT_U_OFF))) in *.
assert (Hwr : forall a, in_wrange (TE regs rg []) WSH a -> shadow_addr F + 4 <= a < shadow_addr F + 23).
{ intros a (r & Hr & Ha). cbv [WSH crt102rw_ssSH ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X18 in Ha. lia. }
assert (Hag : forall xw : word, ~ crt102rw_wr (regs := regs) F (bv_unsigned xw) ->
  mrestrict (w_H Wc) (ms_mem ms0) xw = mrestrict (w_H Wc) memc xw).
{ intros xw Hn. apply HFr. intros Hw. apply Hn. left. exact (Hwr _ Hw). }
pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc memc (ms_mem ms0) mdc _ kj _ pos Db Lamc peakc cntc 0 ran HL HJ HB_HJ Hag HPM)
  as HL1.
(* the zero shadow of back and v *)
assert (Z0 : forall o, 4 <= o <= 10 \/ 16 <= o <= 22 -> aview SEGS (w_H Wc) (ms_mem ms0) (shadow_addr F + o) = Some 0).
{ intros o Ho. apply crt102rw_vm1_zero.
  refine (crt102rw_chunk_vm _ _ (w_H Wc) ms0 0 _ (xr 18) (shadow_addr F) o 1%N (SLit 0) 0 HS eq_refl eq_refl X18 _
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  cbn [YP09.r_chunks]. assert (Ho' : o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/ o = 9 \/ o = 10 \/ o = 16 \/ o = 17 \/
    o = 18 \/ o = 19 \/ o = 20 \/ o = 21 \/ o = 22) by lia.
  repeat (destruct Ho' as [-> | Ho']; [cbn; tauto|]). subst o. cbn; tauto. }
destruct (crt102rw_ff LAWS _ _ _ _ _ _ _ _ HJ) as (_ & _ & _ & _ & _ & Ffr1 & Fsh1).
destruct (crt102rw_open_locals Wc (ms_mem ms0) F ltac:(lia) F32 Fb2 Z0 (fun i Hi => proj1 (Fsh1 i Hi)))
  as (HRAb & HRAv & HHVb & HHVv).
assert (KR : forall r : bv 5, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS |]). destruct Hr. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
pose proof (crt_side_doc (crt_live_side HL1)) as HND1.
rewrite Et in HND1. cbn [pj_nodeR] in HND1.
destruct HND1 as (_ & _ & dnum & dstr & dkids & dkeys & dn & dcap & (_ & _ & _ & _ & _ & _ & (Hdn0 & Vdn) & _) & _ & Edn & _).
subst dn.
clear HF HG HFr.
destruct (crt102rw_U2_entry fxk Wc (ms_mem ms0) (ms_regs ms0) (Z.of_nat (length ms))
  ltac:(rewrite (KR 9%bv) by (cbv; tauto); exact R9) ltac:(rewrite (KR 21%bv) by (cbv; tauto); exact R21)
  ltac:(rewrite (KR 26%bv) by (cbv; tauto); exact R26) ltac:(lia) ltac:(lia) Hs1a ltac:(lia) ltac:(lia) Hd4 Hdn0
  ltac:(intros o Ho; apply Hpres1; pose proof crt102rw_stkc; lia) Vdn) as [HS2 SHOK2].
assert (HEI2 : img_env VAL A_LIM (TE regs (ms_regs ms0) [w64 (Z.of_nat (length ms))])) by apply te_env.
paj_run_tok_x_inv (RUN WS_HJ) HS2 HJ SHOK2 HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ (* the inline check of &doc->n (A' +0x228 .. +0x22c, the report at +0x710): doc's 56 bytes are addressable at every
     state the journal from the entry reaches (its home is a live fake frame of the entry) *)
  cbn [ms_mem mkst restrict]. rewrite !U_SOff.
  assert (A26 : ew (TE regs (ms_regs ms0) [w64 (Z.of_nat (length ms))]) (xr 26) = getr (ms_regs ms0) 26)
    by (unfold xr; apply (te_cur regs (ms_regs ms0) _ 26%bv 26); reflexivity).
  assert (A53 : ew (TE regs (ms_regs ms0) [w64 (Z.of_nat (length ms))]) 53 = getr (ms_regs ms0) 21) by te_close.
  rewrite A26, A53, (KR 26%bv), (KR 21%bv) by (cbv; tauto). rewrite R26, R21. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !YP0m.zcanon_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
  destruct (crt102rw_home_keep LAWS HPRE HTREE _ _ _ _ _ _ _ _ HJ) as (_ & _ & Hra).
  exact (range_addressable_sub _ SHADOW_OFF doc 56 (doc + 40) 8 Hra ltac:(lia) ltac:(lia)). }
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  assert (X9 : bv_unsigned (ew (TE regs (ms_regs ms0) [w64 (Z.of_nat (length ms))]) (xr 9)) = sp1).
  { unfold xr. rewrite (te_cur regs (ms_regs ms0) _ 9%bv 9) by reflexivity. rewrite (KR 9%bv) by (cbv; tauto).
    rewrite R9. apply unsigned_lit_small. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 9) sp1); [reflexivity | exact X9 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. pose proof crt102rw_stkc. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* the registers at the jal *)
assert (KR2 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv ->
  getr (ms_regs ms1) r = getr rg r).
{ intros r Hr. rewrite <- (KR r) by (cbv [In] in Hr |- *; tauto). cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [crt102rw_kr HS2 |]). destruct Hr. }
assert (HBR2 : bregsA (ms_regs ms1) F).
{ refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
            crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
            crt_bregs_s11 := _ |}; rewrite !KR2 by (cbv; tauto); assumption. }
set (E1 := TE regs (ms_regs ms0) [w64 (Z.of_nat (length ms))]) in *.
assert (X9 : bv_unsigned (ew E1 (xr 9)) = sp1).
{ unfold E1, xr. rewrite (te_cur regs (ms_regs ms0) _ 9%bv 9) by reflexivity. rewrite (KR 9%bv) by (cbv; tauto).
  rewrite R9. apply unsigned_lit_small. lia. }
assert (E53 : ew E1 53 = w64 doc).
{ assert (A : ew E1 53 = getr (ms_regs ms0) 21) by (unfold E1; te_close). rewrite A, (KR 21%bv) by (cbv; tauto). exact R21. }
assert (E58 : ew E1 58 = w64 SHADOW_OFF).
{ assert (A : ew E1 58 = getr (ms_regs ms0) 26) by (unfold E1; te_close). rewrite A, (KR 26%bv) by (cbv; tauto). exact R26. }
assert (E59 : ew E1 59 = w64 F).
{ assert (A : ew E1 59 = getr (ms_regs ms0) 27) by (unfold E1; te_close). rewrite A, (KR 27%bv) by (cbv; tauto). exact R27. }
assert (E64 : ew E1 64 = w64 (Z.of_nat (length ms))) by exact (te_more_lt regs (ms_regs ms0) _ 0 ltac:(lia)).
(* the run's writes: the two spill words *)
assert (Hwr2 : forall a, in_wrange E1 (ss_mem crt102rw_ssU2) a -> sp1 + 80 <= a < sp1 + 96).
{ intros a (r & Hr & Ha). cbv [crt102rw_ssU2 ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; [|lia].
  rewrite ts_bv_some, X9 in Ha. lia. }
assert (Hag2 : forall xw : word, ~ crt102rw_wr (regs := regs) F (bv_unsigned xw) ->
  mrestrict (w_H Wc) (ms_mem ms1) xw = mrestrict (w_H Wc) (ms_mem ms0) xw).
{ intros xw Hn. apply HFr. intros Hw. apply Hn. right. pose proof (Hwr2 _ Hw). lia. }
pose proof (crt102rw_live_run LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms0) (ms_mem ms1) _ _ kj _ pos Db Lamc peakc cntc
  0 ran HL1 HJ HB_HJ Hag2 HPM) as HL2.
prreg HS2 (10%bv : bv 5) Q10. prreg HS2 (11%bv : bv 5) Q11. prreg HS2 (1%bv : bv 5) Q1. prreg HS2 (24%bv : bv 5) Q24.
prreg HS2 (22%bv : bv 5) Q22.
fold E1 in Q10, Q11, Q24, Q22.
assert (X10 : getr (ms_regs ms1) 10 = w64 (F + CRT_OFF_V)).
{ rewrite Q10, E59. unfold w64, CRT_OFF_V. rewrite unsigned_lit_small by lia. reflexivity. }
assert (X22 : getr (ms_regs ms1) 22 = w64 (F + CRT_OFF_V)).
{ rewrite Q22, E59. unfold w64, CRT_OFF_V. rewrite unsigned_lit_small by lia. reflexivity. }
assert (X11 : getr (ms_regs ms1) 11 = w64 CRT_STAMP_A).
{ rewrite Q11. unfold CRT_STAMP_A, CRT_STAMP_OFF.
  assert (H243 : bv_unsigned (ew E1 243) = VAL (A_OBJ 2)) by (apply HEI2; vm_compute; lia).
  rewrite H243. reflexivity. }
assert (X24 : getr (ms_regs ms1) 24 = w64 (shadow_addr (doc + PJ_OFF_N))).
{ rewrite Q24, alu_add, alu_srl, E53, E58. unfold v_add, v_srl, w64.
  assert (Ud : bv_unsigned (Z_to_bv 64 doc) = doc) by (apply unsigned_lit_small; lia).
  rewrite Ud.
  assert (U1 : bv_unsigned (Z_to_bv 64 (doc + 40)) = doc + 40) by (apply unsigned_lit_small; lia).
  assert (U3 : bv_unsigned (Z_to_bv 64 3) = 3) by reflexivity.
  rewrite U1, U3. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (U2 : bv_unsigned (Z_to_bv 64 ((doc + 40) / 8)) = (doc + 40) / 8)
    by (apply unsigned_lit_small; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (U4 : bv_unsigned (Z_to_bv 64 SHADOW_OFF) = SHADOW_OFF) by reflexivity.
  rewrite U2, U4. unfold shadow_addr, PJ_OFF_N. f_equal. lia. }
assert (X1 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + CRT_G_OFF))) by (rewrite Q1; vm_compute; reflexivity).
(* the two spills *)
assert (VPN : crt_spill (regs := regs) Wc (ms_mem ms1) CRT_SP_PN (doc + PJ_OFF_N)).
{ unfold crt_spill, CRT_SP_PN, PJ_OFF_N.
  refine (crt102rw_chunk_vm_ok fxk _ _ (w_H Wc) ms1 0 _ (xr 9) sp1 80 8%N (SOff 53 40) (doc + 40) HS2 eq_refl eq_refl
    ltac:(rewrite ew_ewset_other by (unfold xr; lia); exact X9) ltac:(cbn; tauto) _ ltac:(cbn; lia) ltac:(cbn; lia)).
  cbn [sv_denot]. rewrite ew_ewset_other by lia. rewrite E53. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (VN : crt_spill (regs := regs) Wc (ms_mem ms1) CRT_SP_N (Z.of_nat (length ms))).
{ unfold crt_spill, CRT_SP_N.
  refine (crt102rw_chunk_vm_ok fxk _ _ (w_H Wc) ms1 0 _ (xr 9) sp1 88 8%N (SOff 64 0) (Z.of_nat (length ms)) HS2 eq_refl
    eq_refl ltac:(rewrite ew_ewset_other by (unfold xr; lia); exact X9) ltac:(cbn; tauto) _ ltac:(cbn; lia) ltac:(cbn; lia)).
  cbn [sv_denot]. rewrite ew_ewset_other by lia. rewrite E64, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
(* ---- pj_string (&v, STAMP) at +0x24c: a0 = v = F + 0x80, a1 = STAMP, the window d = 0 (v is a local of the class-3
   frame, not of the caller window) ---- *)
destruct (crt_live_journal HL2) as (WS_HJ2 & HJ2 & HB_HJ2). pose proof (crt_live_side HL2) as HSD2.
pose proof (crt_live_lam_perm HL2) as HPL2. pose proof (crt_live_blocks_perm HL2) as HPB2.
pose proof (crt_live_dx_apart HL2) as HAP2. pose proof (crt_live_saved HL2) as HSV2.
pose proof (crt_live_frame HL2) as HFRM2. pose proof (crt_live_fspill HL2) as HSPF2.
pose proof (crt_live_copy_open HL2) as HCR2. pose proof (crt_live_copy_hull HL2) as HCH2.
pose proof (crt_live_memnorm HL2) as HMN2.
pose proof (crt_side_ledger HSD2) as HLED2. pose proof (crt_side_peak HSD2) as Hpk2.
pose proof (crt_side_room HSD2) as HROOM2. pose proof (crt_side_arodata HSD2) as HRO2.
pose proof (crt_side_doc HSD2) as HND2. pose proof (crt_side_doc_blocks HSD2) as HDL2.
pose proof HJ2 as (HAR2 & _).
pose proof (crt_pos_strtod HPOSU) as Esm.
destruct (crt_pos_ex HPOSU) as (pre & hist & HPOSUa).
pose proof (crt_pos_split HPOSUa) as Ert. pose proof (crt_pos_room HPOSUa) as Hpos.
pose proof (crt_pos_run HPOSUa) as Hrun. pose proof (crt_pos_cons HPOSUa) as Hcons.
pose proof (cm_in_intro x t H0READ H0LENX H0WL0 H0WL1) as HIN.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 80 <= a < sp1 + 96) ->
  aview SEGS (w_H Wc) (ms_mem ms1) a = aview SEGS (w_H Wc) (ms_mem ms0) a).
{ intros a Ha Hn. apply aview_eq_of. apply HFr. intros Hw. apply Hn. pose proof (Hwr2 _ Hw) as Hw'.
  rewrite unsigned_lit_small in Hw' by lia. exact Hw'. }
assert (HRAv1 : range_addressable (aview SEGS (w_H Wc) (ms_mem ms1)) SHADOW_OFF (F + CRT_OFF_V) 56).
{ apply (range_addressable_agree (aview SEGS (w_H Wc) (ms_mem ms0))); [|exact HRAv].
  intros y Hy. unfold CRT_OFF_V in Hy. unfold shadow_of_addr. apply K2; unfold SHADOW_OFF; lia. }
assert (HHVv1 : shadow_hull_vis (aview SEGS (w_H Wc) (ms_mem ms1)) (F + CRT_OFF_V) 56).
{ intros s0 Hs0. rewrite K2; [exact (HHVv s0 Hs0) | |]; unfold CRT_OFF_V, shadow_addr, SHADOW_OFF in *; lia. }
assert (HRAb1 : range_addressable (aview SEGS (w_H Wc) (ms_mem ms1)) SHADOW_OFF (F + CRT_OFF_BACK) 56).
{ apply (range_addressable_agree (aview SEGS (w_H Wc) (ms_mem ms0))); [|exact HRAb].
  intros y Hy. unfold CRT_OFF_BACK in Hy. unfold shadow_of_addr. apply K2; unfold SHADOW_OFF; lia. }
assert (HHVb1 : shadow_hull_vis (aview SEGS (w_H Wc) (ms_mem ms1)) (F + CRT_OFF_BACK) 56).
{ intros s0 Hs0. rewrite K2; [exact (HHVb s0 Hs0) | |]; unfold CRT_OFF_BACK, shadow_addr, SHADOW_OFF in *; lia. }
assert (HE2 : bv_unsigned (ew (ewset E1 512 w) 2) = sp0).
{ rewrite ew_ewset_other by lia. unfold E1. rewrite (te_entry regs (ms_regs ms0) _ 2%bv 2) by reflexivity. reflexivity. }
assert (Hsp1 : spZ (ms_regs ms1) = sp1) by (unfold spZ; rewrite (KR2 2%bv) by (cbv; tauto); rewrite R2; apply unsigned_lit_small; lia).
assert (HSTKs : @STK_pj_string prh_img_A = 16480) by (vm_compute; reflexivity).
pose proof crt102rw_stkc as ESTK.
assert (Hstamp0 : 0 < CRT_STAMP_A) by (vm_compute; reflexivity).
(* the stamp's bytes are image bytes, v's are the frame's: the two windows are apart *)
assert (Happ : CRT_STAMP_A + Z.of_nat (length ck_STAMP) + 1 <= F + CRT_OFF_V \/ F + CRT_OFF_V + 56 <= CRT_STAMP_A).
{ destruct (Z_le_gt_dec (CRT_STAMP_A + Z.of_nat (length ck_STAMP) + 1) (F + CRT_OFF_V)) as [Hle|Hgt]; [left; exact Hle|].
  destruct (Z_le_gt_dec (F + CRT_OFF_V + 56) CRT_STAMP_A) as [Hle'|Hgt']; [right; exact Hle'|]. exfalso.
  pose proof H0KS as (_ & _ & Hro).
  set (y := Z.max CRT_STAMP_A (F + CRT_OFF_V)).
  assert (Hy1 : CRT_STAMP_A <= y < CRT_STAMP_A + (Z.of_nat (length ck_STAMP) + 1)) by (unfold y; lia).
  assert (Hy2 : frame_addr lyc CRT_CID pos <= y < frame_addr lyc CRT_CID pos + fs_frame_bytes CRT_CID)
    by (rewrite crt102rw_fb; fold F; unfold y, CRT_OFF_V in *; lia).
  destruct (Hro y Hy1) as (Hr & _).
  pose proof (crt102rw_ro_img _ Hr) as Hi.
  apply (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms1) _ y HAR2
    (or_intror (or_introl (ex_intro _ CRT_CID (ex_intro _ pos (conj Hin Hy2))))))).
  exact Hi. }
(* the room: copy's blocks are within round_trip_text (doc, 0)'s room *)
assert (Hroom : blocks_bytes Sc + PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) <= LIVE_MAX).
{ apply (cm_live_string t (blocks_bytes S) (blocks_bytes Sc) H0LIVE).
  rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPB2), bsum_app.
  pose proof (cm_copy_room_rtt t Db (cm_in_wf x t HIN) HDbl HDbn). pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & _). lia. }
(* the run events: round_trip's rewrite opens with pj_string's strdup (prhPj_string_evs_supply) *)
pose proof (prh_ledger_bounds B lyc Sc Hpc Wc (ms_mem ms1) Lamc peakc cntc SIZE_MAXZ ran _ _ HLED2) as (_ & _ & Hcnt0 & _).
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran _ _ H0LED) as (_ & _ & Hcntg & _).
assert (Hcnt2 : 0 <= ck_cnt2 cnt t < 2 ^ 64 - 1 /\ ck_cnt2 cnt t + 1 + 3 < 2 ^ 64 - 1).
{ apply (cm_cnt_string_set x t ms cnt HIN Et). lia. }
assert (Ecnt2 : cntc = ck_cnt2 cnt t) by (rewrite cm_cnt2_eq; exact HCNTc).
assert (HRUNs : prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat
  (PRH_FnPj.prhPj_string_evs (Z.of_nat (length ck_STAMP)) cntc SIZE_MAXZ)).
{ rewrite cm_MOD_VAL. apply (PRH_FnPj.prhPj_string_evs_supply rp_sm rp_x rp_os _ ms); [reflexivity | |].
  - unfold SIZE_MAXZ. lia.
  - unfold crt_evs_U, PresetReqAt.rw_evs in Hrun. rewrite <- !app_assoc in Hrun.
    exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) Hrun)). }
(* its consumer window: the strdup's one event, the head of the window crt_pos carries *)
assert (HCONSs : PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length pre)%nat
  (length (PRH_FnPj.prhPj_string_evs (Z.of_nat (length ck_STAMP)) cntc SIZE_MAXZ))).
{ assert (Hne0 : cntc <> SIZE_MAXZ) by (unfold SIZE_MAXZ; lia).
  unfold PRH_FnPj.prhPj_string_evs. rewrite (proj2 (Z.eqb_neq cntc SIZE_MAXZ) Hne0).
  unfold crt_evs_U, PresetReqAt.rw_evs in Hcons. rewrite <- !app_assoc, length_app in Hcons.
  apply (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _)) in Hcons as [Hc1 _].
  unfold PresetReqAt.set_evs in Hc1. change (length (?a :: ?l)) with (length [a] + length l)%nat in Hc1.
  exact (proj1 (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _) Hc1)). }
(* pj_string's text is keyed on ReaderRes.jr_strtod (no rp_sm binder): its position, run and window at that key,
   by crt_pos's strtod tie Esm *)
pose proof Hpos as Hposs. pose proof HRUNs as HRUNs'. rewrite Esm in Hposs, HRUNs', HCONSs.
set (v := F + CRT_OFF_V) in *.
refine (crt102rw_call LAWS HPRE fxk (@STK_pj_string prh_img_A) [(v, v + 56)] CRT_G_OFF (SIGMA AS_pj_string) Wc
  (ewset E1 512 w) _ ms1 _ lyc Sc Hpc kj pos Db Lamc peakc cntc 0 ran _ HFZ HS2 eq_refl eq_refl HE2 HL2 HBR2 X1 _ _ _ _ _ _ _).
- unfold CRT_G_OFF. lia.
- reflexivity.
- lia.
- lia.
- (* the callee's footprint: v's window, a local of the frame this function took *)
  intros a Hfa. apply inFP_cons in Hfa as [Hfa | Hfa]; [|exfalso; exact (inFP_nil a Hfa)].
  right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite crt102rw_fb. fold F. unfold v, CRT_OFF_V in Hfa. lia.
- (* the callee: pj_string's text at the call's binders, window d = 0 *)
  intros ch1 HPRE1.
  pose proof HPRE1 as ((_ & _ & _ & _ & _ & Hstk1 & _) & _).
  pose proof Hstk1 as (Hal1 & Hstk01 & Hceil1 & Hslo1 & Hshi1 & H471 & Hbot1 & Htop1 & Htop21).
  eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
  + (* pj_string's text is plain (SRr, fpostWm at wle; the contract text's deliberate form): lifted to SRr' *)
    apply YA0nH.SRr_SRr'.
    refine (PJSTR fxk rp_x rp_os (rp_i + length pre)%nat rp_H0 hist lyc Sc Hpc Wc (ms_regs ms1) (ms_mem ms1) _ ch1
      0 v CRT_STAMP_A ck_STAMP Lamc peakc cntc SIZE_MAXZ ran most 0 HPRE1 H0CL HROOM2 Hposs HOS4 HCONSs X10 X11 _ _ _ _ _ _
      HLED2 (fun _ => Hroom) HRUNs').
    * unfold fwin. split; [lia|]. split; [reflexivity|]. split; [lia|]. intros a0 Ha0. lia.
    * exact (crt102rw_frame_slot LAWS HPRE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos (@STK_pj_string prh_img_A) 0 CRT_OFF_V
        (ms_regs ms1) Lamc HJ2 Hsp1 ltac:(lia) ltac:(lia) ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)
        ltac:(reflexivity) HRAv1 HHVv1).
    * unfold v, CRT_OFF_V. lia.
    * unfold prh_head_wide. change (@cf_head CfParams_preset) with 16. lia.
    * right. split; [lia|]. split.
      { exact (crt_cstr_stamp_A LAWS zs_aligned img_shadow_vis_x lyc Sc Hpc Wc (ms_mem ms1) _ HAR2 HRO2 H0KS). }
      split; [right; right; exact H0KS|]. exact Happ.
    * exact (cm_rq_stamp t H0RQ).
  + (* its post, window 0, lifted to RZW (YCbqGcallW.fpostW_x_R_lift at YA0nH.wle_wle'), in the call rule's float form *)
    intros W' c' _ HPo. apply (crt102rw_postW0R fxk); [exact HFZ|].
    exact (YCbqGcallW.fpostW_x_R_lift (fx := fxk) (SK := SK) SEGS B PST ARx RZW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ HPo).
- (* the return at G *)
  intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP
    ((HROOMs & a & HAPo & Hgra & Hposa & Hok & Hnok) & HMNk).
  assert (HFK3 : fregs_kept_x fx fx') by (intros r0 Hr0; rewrite (HFK2 r0 Hr0); exact (HFK r0 Hr0)).
  pose proof (crt_bregs_sp HBR2) as Q2. pose proof (crt_bregs_gp HBR2) as Q3.
  pose proof (crt_bregs_tp HBR2) as Q4. pose proof (crt_bregs_s0 HBR2) as Q8.
  pose proof (crt_bregs_s1 HBR2) as Q9. pose proof (crt_bregs_s2 HBR2) as Q18.
  pose proof (crt_bregs_s4 HBR2) as Q20. pose proof (crt_bregs_s3 HBR2) as Q19.
  pose proof (crt_bregs_s7 HBR2) as Q23. pose proof (crt_bregs_s10 HBR2) as Q26.
  pose proof (crt_bregs_s11 HBR2) as Q27.
  assert (Q21 : getr (ms_regs ms1) 21 = w64 doc) by (rewrite (KR2 21%bv) by (cbv; tauto); exact R21).
  assert (HFPa : forall a0, inFP [(v, v + 56)] a0 -> a0 < YM05.alloc_ceiling /\ in_app a0 1).
  { intros a0 Hf. apply inFP_cons in Hf as [Hf | Hf]; [|exfalso; exact (inFP_nil a0 Hf)].
    try unfold in_zr in Hf. cbn [fst snd] in Hf. unfold v, CRT_OFF_V in Hf.
    split; [lia|]. apply (in_app_sub _ _ _ _ Fb3); lia. }
  assert (HFP3 : forall a0, inFP [(v, v + 56)] a0 -> a0 < YM05.alloc_ceiling /\ in_app a0 1 /\ ~ (F + 504 <= a0 < F + 512)).
  { intros a0 Hf. destruct (HFPa a0 Hf) as (H1 & H2). split; [exact H1|]. split; [exact H2|].
    apply inFP_cons in Hf as [Hf | Hf]; [|exfalso; exact (inFP_nil a0 Hf)].
    try unfold in_zr in Hf. cbn [fst snd] in Hf. unfold v, CRT_OFF_V in Hf. lia. }
  assert (HFP0 : Forall (fun r => 0 < fst r) [(v, v + 56)]) by (repeat constructor; cbn [fst]; unfold v, CRT_OFF_V; lia).
  assert (HFPD : forall a0, inFP [(v, v + 56)] a0 -> ~ pj_footR doc D a0).
  { intros a0 Hf. apply inFP_cons in Hf as [Hf | Hf]; [|exfalso; exact (inFP_nil a0 Hf)].
    try unfold in_zr in Hf. cbn [fst snd] in Hf.
    exact (crt102rw_local_off_doc LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos Db Lamc peakc cntc 0 ran CRT_OFF_V a0
      HL2 ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) ltac:(fold F; unfold v in Hf; lia)). }
  assert (HDb : forall bk, In bk Db -> In bk Lamc).
  { intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hbk. }
  assert (HFPC : forall a0, inFP [(v, v + 56)] a0 -> ~ pj_footR (F + CRT_OFF_COPY) Db a0).
  { intros a0 Hf. apply inFP_cons in Hf as [Hf | Hf]; [|exfalso; exact (inFP_nil a0 Hf)].
    try unfold in_zr in Hf. cbn [fst snd] in Hf.
    exact (crt102rw_local_off_tree LAWS lyc Sc Hpc Wc (ms_mem ms1) _ kj pos Db Lamc peakc cntc 0 ran CRT_OFF_V
      (F + CRT_OFF_COPY) Db a0 HL2 HDb ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)
      ltac:(right; fold F; unfold CRT_OFF_V, CRT_OFF_COPY; lia) ltac:(fold F; unfold v in Hf; lia)). }
  destruct (crt102rw_call_keep LAWS HPRE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos _ _ ly2 S2 Hp2 W2 mem2 md2 k1 HJ2 HJc HFPa)
    as (EF2 & KS2 & KSH2).
  fold F in EF2, KSH2.
  assert (HDR3 : dregsA regs2 F).
  { refine {| crt_dregs_bregs := {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _;
                crt_bregs_s1 := _; crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _;
                crt_bregs_s10 := _; crt_bregs_s11 := _ |}; crt_dregs_s5 := _ |};
    [ rewrite (ts_ap (ms_regs ms1) regs2 2%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 3%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 4%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 8%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 9%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 18%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 20%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 19%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 23%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 26%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 27%bv HP) by ts_cs
    | rewrite (ts_ap (ms_regs ms1) regs2 21%bv HP) by ts_cs ];
    assumption. }
  assert (X22' : getr regs2 22 = w64 (F + CRT_OFF_V)) by (rewrite (ts_ap (ms_regs ms1) regs2 22%bv HP) by ts_cs; exact X22).
  assert (X24' : getr regs2 24 = w64 (shadow_addr (doc + PJ_OFF_N)))
    by (rewrite (ts_ap (ms_regs ms1) regs2 24%bv HP) by ts_cs; exact X24).
  pose proof (crt102rw_spill_keep HPRE Wc W2 (ms_mem ms1) mem2 CRT_SP_PN (doc + PJ_OFF_N) KS2
    ltac:(unfold CRT_SP_PN; lia) ltac:(unfold CRT_SP_PN; lia) VPN) as VPN3.
  pose proof (crt102rw_spill_keep HPRE Wc W2 (ms_mem ms1) mem2 CRT_SP_N (Z.of_nat (length ms)) KS2
    ltac:(unfold CRT_SP_N; lia) ltac:(unfold CRT_SP_N; lia) VN) as VN3.
  destruct (crt102rw_local_keep Wc W2 (ms_mem ms1) mem2 F CRT_OFF_BACK ltac:(lia) F32 Fb2 KSH2
    ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) as (LB1 & LB2).
  destruct (crt102rw_local_keep Wc W2 (ms_mem ms1) mem2 F CRT_OFF_V ltac:(lia) F32 Fb2 KSH2
    ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)) as (LV1 & LV2).
  (* copy's tree at the call: the two runs of U wrote only the frame's shadow and the spills *)
  assert (HCT1 : crt_copy_tree (rc := rc) (L := A_prog_listing) (PA := PA) Wc (ms_mem ms1) Lamc F t Db).
  { unfold crt_copy_tree in *.
    apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)) (prh_lin Lamc) _ Db HCT).
    intros y Hy.
    destruct (crt102rw_foot_nw LAWS HPRE lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0 ran Db (F + CRT_OFF_COPY) y HL HDb
      ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy) as (Hy1 & Hy2).
    assert (E : mrestrict (w_H Wc) (ms_mem ms1) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
    { rewrite (Hag2 (Z_to_bv 64 y)) by (rewrite unsigned_lit_small by lia; exact Hy2).
      apply Hag. rewrite unsigned_lit_small by lia. exact Hy2. }
    split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
  (* copy's ORDERED free list at the call (crt_at_U_copy_fo), framed by the same agreement *)
  assert (HFO1 : cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
    exists F0, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) (ms_mem ms1)) (prh_lin Lamc) nn (F + CRT_OFF_COPY) Db F0 /\
      map (fun b => snd b + cf_head) F0 = PresetReqAt.fo (PjTree.JObj ms)).
  { intros Hhd nn Hd. destruct (crt_at_U_copy_fo HU Hhd Hd) as (F0 & HF0 & HFm). exists F0. split; [|exact HFm].
    apply (PRH_PjOrder.pj_foR_frame SEGS nn (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms1)) (prh_lin Lamc)
      (prh_lin Lamc) _ Db F0 HF0 (fun a k Hk => HDb (a, k) Hk)).
    intros y Hy.
    destruct (crt102rw_foot_nw LAWS HPRE lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc 0 ran Db (F + CRT_OFF_COPY) y HL HDb
      ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy) as (Hy1 & Hy2).
    assert (E : mrestrict (w_H Wc) (ms_mem ms1) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
    { rewrite (Hag2 (Z_to_bv 64 y)) by (rewrite unsigned_lit_small by lia; exact Hy2).
      apply Hag. rewrite unsigned_lit_small by lia. exact Hy2. }
    split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
  assert (Hcne : cntc <> SIZE_MAXZ) by (unfold SIZE_MAXZ; lia).
  assert (Hcm : (cntc + 1) mod 2 ^ 64 = cntc + 1) by (apply Z.mod_small; lia).
  pose proof (cm_rqa_stamp t most H0RQA) as Hrqs.
  assert (HSTK0 : 0 <= @STK_pj_string prh_img_A) by lia.
  assert (HcF : exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= F + CRT_OFF_COPY /\
    F + CRT_OFF_COPY + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0).
  { exists CRT_CID, pos. split; [exact Hin|]. rewrite crt102rw_fb. fold F. unfold CRT_OFF_COPY. lia. }
  (* CAP carried from U (crt_at_U's header-cap conjunct) to the G state: copy's header is untouched by U's runs (the frame's shadow and
     the spills) and off pj_string's footprint *)
  assert (HCAPg : exists num str kids keys n, pj_hdrR SEGS (mrestrict (w_H W2) mem2) (F + CRT_OFF_COPY) 6
    num str kids keys n (Z.of_nat (PresetReqAt.ncap (length ms)))).
  { pose proof HCT as HCTo. unfold crt_copy_tree in HCTo. rewrite Et in HCTo. cbn [pj_nodeR] in HCTo.
    destruct HCTo as (_ & _ & num & str & kids & keys & n & cap & Hh & _).
    pose proof (HCAPU 6 num str kids keys n cap Hh) as Ec.
    rewrite Ec in Hh. exists num, str, kids, keys, n.
    apply (crt102rw_hdr_call lyc Sc Hpc Wc (ms_mem ms1) _ _ _ ly2 S2 Hp2 W2 mem2 md2 k1 _ _ _ _ _ _ _ _ HAR2 HJc HcF).
    { intros a0 Hf Ha0. apply inFP_cons in Hf as [Hf | Hf]; [|exact (inFP_nil a0 Hf)].
      try unfold in_zr in Hf. cbn [fst snd] in Hf. unfold v, CRT_OFF_V, CRT_OFF_COPY in *. lia. }
    apply (pj_hdrR_frame SEGS _ _ _ 6 num str kids keys n _ Hh). intros y Hy.
    assert (Hyr : 0 <= y < 2 ^ 64 /\ ~ crt102rw_wr (regs := regs) F y).
    { split; [unfold CRT_OFF_COPY in Hy; lia|].
      apply (crt102rw_nw_app HPRE); [lia | lia | apply (in_app_sub _ _ _ _ Fb3); unfold CRT_OFF_COPY in Hy; lia |
        unfold CRT_OFF_COPY in Hy; lia]. }
    assert (E : mrestrict (w_H Wc) (ms_mem ms1) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
    { rewrite (Hag2 (Z_to_bv 64 y)) by (rewrite unsigned_lit_small by lia; apply Hyr).
      apply Hag. rewrite unsigned_lit_small by lia. apply Hyr. }
    split; [unfold mbyte; rewrite E; reflexivity|]. intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
  destruct HAPo as [(Ecf & _) | [(Hne & Ea & EHp & Eab & _ & _ & HLEDr) |
    (Hne & Ha16 & Ham & Hnin & EHp & Eab & Hra & Hhv & Hbytes & HLEDt)]]; [exfalso; exact (Hcne Ecf) | |].
  + (* REFUSED (a = 0 at cnt <> fail): DEAD AT ITS SOURCE. tpj_string_specX's DEAD-PJSTRING conjunct
       `(cnt <> fail -> a <> 0)` (PRH_FnPj.v:1275, Hgra) at fail = SIZE_MAX, with g_count below it (Hcne) *)
    exfalso. exact (Hgra Hcne Ea).
  + (* TAKEN: v = JStr STAMP over one fresh block, the position one event further *)
    rewrite Hcm in HLEDt.
    assert (Ha' : a <> 0) by (pose proof (@cf_head_nonneg CfParams_preset); lia).
    destruct (Hok Ha') as (Ha0' & HNDv).
    set (n := Z.of_nat (length ck_STAMP) + 1) in *.
    set (pk' := Z.max peakc (Ledger.lsum Lamc + n)) in *.
    assert (HPB3 : Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks ((a, n) :: Db))).
    { rewrite Eab. cbn [ck_hblks map fst snd]. unfold ck_hblks in HPB2 |- *. cbn [map fst snd].
      apply (Permutation_trans (Permutation_app_tail _ HPB2)). rewrite <- app_assoc.
      apply Permutation_app_head. cbn [app]. apply Permutation_sym. apply Permutation_cons_append. }
    assert (HPL3 : Permutation ((a, n) :: Lamc) (((a, n) :: Db) ++ Lam)) by (cbn [app]; apply perm_skip; exact HPL2).
    assert (HAP3 : forall bk, In bk ((a, n) :: Db) -> ~ In bk D).
    { intros bk [<- | Hbk]; [|exact (HAP2 bk Hbk)]. intros HinD. apply Hnin.
      apply (in_map fst _ (a, n)). exact (HDL2 _ HinD). }
    assert (HDL3 : forall bk, In bk D -> In bk ((a, n) :: Lamc)) by (intros bk Hbk; right; exact (HDL2 _ Hbk)).
    pose proof (crt102rw_side_call LAWS HPRE HTREE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos Db Lamc peakc cntc 0 ran _ _
      ly2 S2 Hp2 W2 mem2 md2 k1 ((a, n) :: Lamc) pk' (cntc + 1) 0 ran HL2 HJc HFP0 HFPD HLEDt
      ltac:(unfold pk'; lia) HROOMs HDL3) as HSD3.
    pose proof (crt102rw_live_call LAWS HPRE lyc Sc Hpc Wc (ms_mem ms1) _ kj pos Db Lamc peakc cntc 0 ran _ _
      ly2 S2 Hp2 W2 mem2 md2 k1 ((a, n) :: Db) ((a, n) :: Lamc) pk' (cntc + 1) 0 ran HL2 HJe HJc HSTK0 HFP3 HSD3 HPL3
      HPB3 HAP3 HMNk) as HL3.
    pose proof (crt102rw_tree_call LAWS lyc Sc Hpc Wc (ms_mem ms1) _ kj _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc ran
      ((a, n) :: Lamc) pk' (cntc + 1) ran (F + CRT_OFF_COPY) t Db HAR2 HJc HLED2 HLEDt
      HcF HDb (fun bk Hbk => or_intror (HDb bk Hbk)) HFPC HCT1) as HCT3.
    assert (HFO3 : cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
      exists F0, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin ((a, n) :: Lamc)) nn (F + CRT_OFF_COPY) Db F0 /\
        map (fun b => snd b + cf_head) F0 = PresetReqAt.fo (PjTree.JObj ms)).
    { intros Hhd nn Hd. destruct (HFO1 Hhd nn Hd) as (F0 & HF0 & HFm). exists F0. split; [|exact HFm].
      exact (crt102rw_fo_call lyc Sc Hpc Wc (ms_mem ms1) _ kj _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc ran
        ((a, n) :: Lamc) pk' (cntc + 1) ran (F + CRT_OFF_COPY) nn Db F0 HAR2 HJc HLED2 HLEDt
        HcF HDb (fun bk Hbk => or_intror (HDb bk Hbk)) HFPC HF0). }
    destruct (Hposa (or_introl Ha')) as (hist' & Hpos'). rewrite <- Esm in Hpos'.
    unfold PRH_FnPj.prhPj_string_evs in Hpos'. rewrite (proj2 (Z.eqb_neq cntc SIZE_MAXZ) Hcne) in Hpos'.
    cbn [length] in Hpos'.
    rewrite H0RAN in HL3.
    apply (crt102rw_G_taken HWGO HL0K fx' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Db ((a, n) :: Lamc) pk' (cntc + 1) regs2 ms a pre
      hist'); [| exact Ha0' | rewrite EF2; exact HNDv | exact Ert | exact Hrun | exact Hcons | exact Esm | exact Hpos'].
    unfold crt102rw_Gst. rewrite EF2.
    split; [exact HFZ2|]. split; [exact HFK3|]. split; [exact HL3|]. split; [exact HDR3|].
    split; [exact X22'|]. split; [exact X24'|]. split; [exact Et|]. split; [exact VPN3|]. split; [exact VN3|].
    split; [exact (LB1 HRAb1)|]. split; [exact (LV1 HRAv1)|]. split; [exact (LB2 HHVb1)|]. split; [exact (LV2 HHVv1)|].
    split; [exact HCT3|]. split; [exact HTBLK|]. split; [exact HCAPg|]. split; [exact HDbf|]. split; [exact HDbl|].
    split; [exact HDbn|]. split; [lia | exact HFO3].
Qed.
(* ==== THE CHAIN. Every segment is Qed above, and crt102rw_chain composes them, Qed. Its premises:
   - crt102rw_wild_budget_pn (THE WILD BUDGET at parse_noting, the parse_noting twin of Crt102Arms.arms_wild_budget and
     Crt102B_RRT.crtb_wild_budget), DISCHARGED by crt102rw_wild_budget_pn_goal at the kb re-shape, brief
     the internal file wild-budget-kb-reshape.md;
   - crt102rw_L0K, not open: the next slice's entry (Crt102Loops), the chain's continuation at L0.
   RETIRED, each by its content proved AT ITS SOURCE (the Step-1 ruling of the contract texts' owner on 1409ad6e7e37;
   the B' T3 twins, Crt102B_T3U.v / Crt102B_T3S.v / Crt102B_T3O.v):
   - OPEN_K0_DEAD_PJSTRING: pj_string's refused arm at +0x24c is refuted in crt102rw_at_U by tpj_string_specX's
     DEAD-PJSTRING conjunct (PRH_FnPj.v:1275).
   - OPEN_K0_DEAD_PJSET: pj_set's res = -1 arm at +0x278 is refuted in crt102rw_G_taken by tpj_set_specX's DEAD-PJSET
     conjunct (PRH_FnPj.v:1046).
   - OPEN_K0_DEAD_PJWRITE: pj_write's refused arm at +0x2b0 is refuted in crt102rw_Wgo by tpj_write_specX's
     DEAD-PJWRITE conjunct (prh_granted, PRH_FnWriter.v:820) and PRH_Refute.prh_refute_pj_write_failed.
   - OPEN_K0_FREEORD_COPY: copy's ordered free list is tpj_set_specX's FREEORD-COPY conjunct at K
     (PRH_FnPj.v:1122-1129 / :1168-1176), carried K -> O1 -> W -> R -> N by crt102rw_copy_fo.
   - (UNIV-END and SRC-CEIL were RETIRED by the landing cut: the text no longer takes them.) ==== *)
Lemma crt102rw_chain : crt102rw_wild_budget_pn -> crt102rw_L0K ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms,
  atU fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_U_OFF rg memc mdc) QFa.
Proof.
intros HWB HL0K.
exact (crt102rw_at_U (crt102rw_Wgo (crt102rw_W2 (crt102rw_R712 (crt102rw_R724 HWB (crt102rw_R740 HL0K))))) HL0K).
Qed.
(* the slice, unconditional but for its continuation at L0: Qed, the wild budget by crt102rw_wild_budget_pn_goal *)
Lemma crt102_rw : forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms,
  atU fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ->
  crt102rw_L0K ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_U_OFF rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms HU HL0K.
exact (crt102rw_chain crt102rw_wild_budget_pn_goal HL0K fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms HU).
Qed.

End g.
End f.
End crtA.

(* The four OPEN_K0_* goals are proved at their sources (crt102rw_chain's note): the slice is a constant (Qed) *)
Check crt102_rw.
Print Assumptions crt102_rw.
Print Assumptions crt102rw_chain.
(* kb round: the parse_noting wild budget is a constant (Qed) *)
Check crt102rw_wild_budget_pn_goal.
Print Assumptions crt102rw_wild_budget_pn_goal.

(* the FPState elaboration check (the walk owner's rule): implicits on, notations off - every FPState argument of the
   exported statements must be the contract's entry fx or a boundary's own named float state *)
Set Printing Implicit.
Unset Printing Notations.
Check @crt102rw_chain.
Print crt102rw_L0K.
Print crt102rw_Wgo_goal.
Print crt102rw_Wst.
Print crt102rw_Rst.
Print crt102rw_Nst.
Print crt102rw_wild_budget_pn.
Print crt102rw_copy_fo.
Set Printing Notations.
Unset Printing Implicit.

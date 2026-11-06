(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 474 of its 523 lines of code are new or changed and 879 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move):
   the composition re-fit to the text on this base (lib/A/PRH_FnCheck.v tcheck_round_trip_specX): its conclusion is at
   the step relation YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf, and it takes the new entry premise `(length rp_os <= 4)%nat`
   (after ck_frm0, before the wild room). crt_B_under binds it in the text's place (HOS4 in every intro list), every
   seam (J / X / C / L3 / L0 / W / U / M) is at SRr' (CRT_B_AT_J / _U / _W restated, the glue's CRT_B_AT_X / _C / _L3 /
   _L0 already are), HOS4 is handed to the rows that take it (T8 crt102_tail_B after HTREE, T7 crtB_T7 last, T4
   crtB_T4 by assumption, T3 crt102b_seg_T3 after HRQ, T2 crtb_rrt by name), and crt102_topB_of's post bridge reads
   the text's `SRr' segs RZ_cf .. (fpostFbm ..)` through YSRrG.SRr'_mono and YCbqGwild.apost_base_xbFR. The six
   callee texts that take a CTX0 (RTT, PJFREE, PJSTR, PJSET, PJW, PNOTING) are Section hypotheses at the contract's one
   CTX0 (a Section Variable), not at every CTX0: every seam uses them only there. The text below this note describes
   the kb round on the earlier base and is kept for its record. *)
(* fuzz_preset, slice Crt102TopB: THE B' COMPOSITION of the walk of check_round_trip (fuzz_preset.c new:772-781,
   round_trip_rewrite new:715-769 inlined) into the contract text
   tcheck_round_trip_specX (lib/A/PRH_FnCheck.v 8feca2000b76:1326), image B' (asan-ubsan pin d663f82d7f488d30, unstripped
   twin c90d4fa54d43160b), at PA := PI_prog_B, PI := prh_img_B, L := B_prog_listing, ci := CfImg_B. The B' twin of
   lib/A/Prog/Crt102Top.v (9e3b33aeea6d at the A' kb head a54cc6d36c2c): the same shape, the B' rows in place of the
   A' slices.

   STATUS AT THE kb ROUND (the kb Glue c580eb0fe37c, on this branch with the A' kb head a54cc6d36c2c merged into the B'
   lane 01ab5fb67d43): THE CONTRACT IS Qed, crt102_topB (generic in B) and crt102_topB_TfibB (B := YD2l.TfibB). Every
   piece is its own Qed lemma:
   - crt102_topB_J   the J seam (+0x348 .. ret), by Crt102TailB.crt102_tail_B (row T8).
   - crt102_topB_X   the X seam (+0x30c), by Crt102XB.cb_at_X_B with its TAIL := crt102_topB_J.
   - crt102_topB_C   the C seam, by Crt102B_T7_top.crtB_T7 (row T7, CRT_B_SEG_T7) at crt102_topB_X.
   - crt102_topB_L3  the L3 seam, by Crt102B_T6.crtB_T6 (row T6, CRT_B_SEG_T6) at crt102_topB_C.
   - crt102_topB_L0  the L0 seam, by Crt102B_T5.crtB_T5 (row T5, CRT_B_SEG_T5) at crt102_topB_L3 / _C.
   - crt102_topB_W   the W seam (+0x2a4), by Crt102B_T4.crtB_T4 (row T4, L0 -> W) at crt102_topB_L0. T4 proves its
                     parse_noting call itself (t4_goal_pn, restated in the kb form, Qed as t4_goal_pn_holds from PN) and
                     its pj_write call (t4_goal_pjw from PJW).
   - crt102_topB_U   the U seam (+0x1ec), by Crt102B_T3.crt102b_seg_T3 (row T3, STMT_X -> STMT_W -> STMT_U) at
                     crt102_topB_X and crt102_topB_W.
   - crt102_topB_M   the M seam (+0x194) = T1's continuation Crt102EntryB.crt102eb_cont, by Crt102B_RRT.crtb_rrt (row
                     T2's segment lemma, Qed at the kb round) with TAIL := crt102_topB_J and REWR := crt102_topB_U.
                     crtb_rrt is crtb_at_M with both its premises discharged in T2: the bridge (copy's free order and
                     cap word from the cut's own conjuncts) and crtb_wild_budget (restated in the kb form there,
                     crtb_wild_budget_goal).
   - crt102_topB_of  CRT_B_SEAM_M -> the contract, generic in B and in the text's a_mod_at / a_stamp: the entry by
                     Crt102EntryB.crt102_entry_B_cf (row T1, at PI_prog_B), whose continuation IS CRT_B_SEAM_M's body
                     (THE T1 -> T2 JOIN), and the post bridge QF -> the text's budgeted post.
   - crt102_topB     THE CONTRACT at B', generic in B, at the text's instance of its two string addresses
                     (a_mod_at := CRT_MOD_AT_B, a_stamp := CRT_STAMP_B, Crt102ImgB.v, pa_val of the B listing).
   - crt102_topB_TfibB  the same at THE B' INSTANCE B := YD2l.TfibB, with T1's four image stand-ins and BOK DISCHARGED
                     in its script (Section a below). IMGVIS stays (it reads ARx).
   THE BUDGET AT EVERY SITE (the Glue's G4 values, forced; each checked by computation, crt102_topB_kb_* at the end of
   this file): M 0 (T1: no wild call; wbudget [] 0 []) -> rtt1 0 + 32 -> rtt2 32 + 32 = U_B 64 (T2) -> W_B 64 (T3:
   pj_string / pj_set / fuzz_alloc_ran_out add []) -> L0_B 64 + 2 = 66 by parse_noting (T4) -> L3_B / C_B 66 (T5,
   T6) -> X_B 66 (T7) -> J_B 66 (X) -> QF 66 (T8). Every site is an IDENTITY but TWO STEP UPS, both 64 -> 66, 64 < 66
   and 64 <> 66 (crt102_topB_kb_step_lt / _ne), both by crt_live monotonicity (wbudget is an upper bound: only room
   is given up, and from J_B / L0_B on nothing asks for room): (1) C3 in T2 (t not an object, after rtt2), the live
   state at 64 entering J_B at 66 (Crt102B_RRT.crtb_live_mono, the twin of Crt102Arms.arms_live_mono, A''s one step);
   (2) T4's failed-write arm (crt4_lane_Wr, pj_write's a0 = 0), which skips parse_noting, W_B at 64 -> O2 -> L0_B at
   66 (Crt102KitB.cb4_live_mono). A' has no twin of (2): its rewrite refutes that arm at its source. Nothing depends
   on an identity at either site. C1 / C2 (rtt's r = 1 arm), T3's X exit (C4a) and T4's FF -> X exit are refuted at
   their source and build no boundary, so they need no step.
   RETIRED AT THE kb ROUND, each only after its content was proved in the kb form; no statement was weakened:
   - CRT_B_WILD_BUDGET, the named antecedent (T2's crtb_wild_budget under the text's premises). As stated before the
     round it asked rtt's budgeted journals AJW .. WS1 back as the unbudgeted AJ, which nothing proves (the only
     budgeted call rule, YCbqGwild.aj_call_xbF_sp, lands at AJW .. (WS0 ++ WS1)). The kb Glue states crt_live's
     journal at a budget, T2 restates crtb_wild_budget in that form (the twin of Crt102Arms.arms_wild_budget: room
     at the call and the landing at kb + 32) and proves it, crtb_wild_budget_goal, from the text's entry room.
   - the Record CRT_B_OPEN, its one field crt_B_open_t4_pn (Crt102B_T4.t4_goal_pn, the parse_noting call at +0x2e8),
     and CRT_B_SEAM_OPEN. As stated before the round t4_goal_pn asked the unbudgeted post fpostFm and no room, which
     the text does not give (it takes the room and posts fpostFbm .. (wbudget [] (prh_wk F_parse_noting))). T4
     restates it in the kb form (the room premise and the text's budgeted post) and proves it, t4_goal_pn_holds, from
     PN; the room at the call comes from the live state's journal at 64 and the text's entry room (T4's HWR0), and
     crtB_T4 no longer takes the goal.
   - crt102_topB_open / crt102_topB_open_TfibB: without the Record they are crt102_topB / crt102_topB_TfibB.
     CONSUMERS USE crt102_topB / crt102_topB_TfibB.
   BEFORE THE kb ROUND (the B' lane's commits up to 01ab5fb67d43; their commit messages carry the record):
   the rows were taken by path from their owners' cut re-fits (T2, T3, T4, T5 / T6 / T7), the open set shrank from
   five fields to one, and the contract theorems were Aborted at
   CRT_B_WILD_BUDGET. At the kb round every B' row file was re-fit on this branch to the kb Glue (the inputs below).
   THE LEAVES: Crt102B_T56_strcmp.v (crtB_T5_TfibB, crtB_T6_TfibB) and Crt102B_T7_strcmp.v (crtB_T7_strcmp) discharge
   STRCMP by PSstrRo.ps_strcmp_xrom_B and BOK by YD2l.TfibB_ok at B := YD2l.TfibB, ARx := ARcf SEGS TfibB, and nothing
   imports them. THIS FILE CITES THE LEAVES AND DOES NOT REQUIRE THEM OR PSstrRo: Requiring PSstrRo loads K / K5
   LiaTuning, whose global `Ltac lia ::=` silently changed crtB_T6's argument list in the T6 row's measurement. STRCMP /
   ASTRCMP stay Section hypotheses here, dischargeable on the cut base.
   THE SPLIT'S SHADOWING RULE, for every file that took the import line (T3's analysis, the walk's owner, 12:24Z): the moved
   names and a row's local names intersect in exactly BASE / PST / RHI / RLO / SEGS / SIGMA / VAL; both sides declare
   them `#[local] Notation` with identical right-hand sides, and a local notation is not exported by Require Import, so
   every use binds as before. No other moved name has a local twin in the rows checked (T2, T3, T5, T6, T7).
   BEFORE THE kb ROUND, THE OPEN SET AT THE ROWS' CUT RE-FITS (the walk's owner, 11:10Z - 11:54Z), kept for its record: the
   lane took T2's and T3's re-fits by path, and the Record shrank from five fields to two (then to one at T4's):
     CLOSED at T2's re-fit (commit 5bb3ae83ef19; pins102 rc=0, Crt102B_RRT.vo 17.77 s,
       log, the internal file zf-fuzz-preset-5bb3ae83ef.build-20261030T074349Z.log): crt_B_open_copy_fo, by the cut's tround_trip_text_specX
       FREEORD-COPY conjunct, the read-back free order (PRH_FnCheck.v:1290-1293); crt_B_open_copy_cap, by pj_ncapR's
       first object conjunct (PRH_Reader.v:247) via crtb_n48_keep and Crt102Glue.crt_copy_cap_of_ncap48. Both goals are deleted there.
     CLOSED at T3's re-fit (commit f3c3dd073e22; pins102 rc=0 wall=480, log
       the internal file zf-fuzz-preset-f3c3dd073e.build-20261030T074850Z.log): crt_B_open_t3_O1. crt102b_seg_T3 : STMT_X -> STMT_W ->
       STMT_U (Crt102B_T3.v:238) is Qed, with no Abort / admit / Axiom in the five files; its waits closed by the callee
       texts' own clauses (tpj_string_specX `cnt <> fail -> a <> 0`, PRH_FnPj.v:1275; tpj_set_specX's window clause,
       :1046; tpj_set's result free order, :1104 / :1156).
     NOT THE SAME OBLIGATION, BUT A CHAIN: crt_B_open_copy_fo (CRT_B_GOAL_COPY_FO: copy's free order after rtt1, for
       the ORIGINAL tree t, RHS PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t false)) feeds the U field
       crt_at_U_B_copy_fo (Crt102Glue.v, RHS PresetReqAt.fo (PjTree.JObj ms), t = JObj ms), which tpj_set_specX's
       ordered entry premise reads; T3's W field crt_at_W_B_copy_fo (after pj_set, for crt_tree_J, RHS
       PresetReqAt.fo crt_tree_J) is produced from tpj_set's post and so CONSUMES the U field (T3U crt3U_fo0_keep,
       framed U -> S). THE BRIDGE between the two spellings is in the composition at T2's re-fit, provable from what the
       cut carries, with no text change: Crt102B_RRT.crtb_fo_of_frees (:781-790 at 5bb3ae83ef19) rewrites the pj_frees
       form to fo t by PresetFreeFo.pj_frees_wdoc_t ReaderRes.jr_strtod t false (Spec/PresetFreeFo.v
       75c11ade43e4) under pj_wf ReaderRes.jr_strtod t, which it takes from Crt102Model.cm_in_wf x t HIN (:1842), and
       crt_at_U_B_copy_fo is built from that at :1439. The A' twin is Crt102Arms.arms_fo_of_frees.
   THE kb ROUTE (the unit owner's one round after the cut's landing; brief, the internal file wild-budget-kb-reshape.md):
     one new crt_live parameter kb; its journal `exists WS, AJW .. WS /\ wbudget [] kb WS`; QF = fpostFbm B ARx SK (wbudget
     [] (prh_wk F_check_round_trip)) STKC [] regs ly S Hp W mem md (fQmn mem QT); crt_B_under takes the text's wild_room
     (as_universe B) [] (prh_wk F_check_round_trip) (st_depot S); the room at any boundary is wild_room [] (66 - kb)
     (st_depot Sc), by YCbqGwild.ajournal_xw_room and wild_room_le. WHY kb CANNOT BE ONE CONSTANT: rtt2 needs 32 left,
     parse_noting needs 2 left and the final post needs wbudget [] 66, and no single bound gives all three. WHY THE
     ROUTE IS SOUND: prh_wk F_check_round_trip = 66 = 32 + 32 + 2 (PRH_Base.v prh_wk), and pj_string / pj_set / pj_write
     / the libc and frame calls have no wild site, so their old posts add [] (YCbqGwild.apost_base_xbF_of_x).
   VACUITY, the walk owner's sentence, to travel with every green result, UPDATED AT THE LANDING CUT: this statement goes
     through prh_univ_closure. Its clause 4 was false on B' for data words until the 4a / 4b split (4a: the code word
     stays a fixed In; 4b: inU (as_universe B) (prh_trace pc_free_ra0 r [w])); the cut 7cdbb61b5fa0 carries the split
     and removes DW, and the closure is now SATISFIABLE at the B' instance: PRH_Witness.prh_univ_closure_witness_B
     (lib/A/PRH_Witness.v:285-293) proves @prh_univ_closure prh_img_B B CfImg_B [[0x815c8]] for every B with
     as_code B = YF0l.Tfib_code and as_universe B = YCej.Tfib_universe, and YD2l.TfibB has both by its fields
     (`prh_univ_closure_witness_B YD2l.TfibB eq_refl eq_refl` checks; Print Assumptions: closed under the global
     context; a separate check on the branch head, first measured at row T2). This file discharges no
     universe fact: the text's prh_univ_closure B CTX0 is a pass-through premise, and the witness is cited, not used.

   THE STATEMENT. crt_B_under is ALL of tcheck_round_trip_specX's binders and premises at B' (PRH_FnCheck.v
   8feca2000b76:1326-1390, the text's order: its wild room :1366 after ck_frm0, its last premise astack_up_x :1390
   after prh_cons_from), in front of a conclusion K at the binders K reads. Like the text it has no rp_sm binder and no
   `rp_sm = ReaderRes.jr_strtod` premise (the text keys on ReaderRes.jr_strtod); a row or glue predicate that still
   takes rp_sm gets ReaderRes.jr_strtod. No other definition here restates the text's premises: every boundary and
   every row statement is taken by its own name (the glue's crt_at_*_B Records and CRT_B_AT_X / _C / _L3 / _L0, T1's
   crt102eb_cont, T3's CRT3_*, T2's crtb_rtt_Q / crtb_rtt_Q_k0 and crtb_wild_budget), and crt102_topB_of hands the
   text's own premises to crt_B_under, so a premise there that is not the text's does not typecheck. The stretch
   statements J / U / W (the cuts the glue gives no statement for) are CRT_B_AT_J / _U / _W below, the glue's
   CRT_B_AT_X form over crt_at_J_B / crt_at_U_B / crt_at_W_B.

   SECTION HYPOTHESES (each with its owner; only those the proofs use):
     LAWS  (AR_laws_x at cf_head)          engine fold (YCbqG); at ARcf YGcallcf.AR_laws_x_cf. Every row's.
     ASM3 / OWNLOW / AMS                   T1's: the frame-class lane (astack_malloc_realizes_xm 3); engine
                                           (ARx_owned_low_law); the libc row (__asan_memset, OSet).
     RTT   (tround_trip_text_specX)        the contract text, at the contract's one CTX0 and every float state; T2's.
     ASFX / FFLX / SFX                     T8's (aj_flag_store_x's three): engine (YG0dcf astack_free_law_cf,
                                           AR_flag_law_ok_cf / AR_client_img_law_ok_cf, YGcallScf stack_free_x_any).
     FFLP                                  T8's (AR_flag_law_ok_cf's first conjunct).
     SETSH (__asan_set_shadow_f5, 0xf5)    T8's: the frame-class lane.
     PJFREE (tpj_free_specX)               the contract text; T8's and T7's.
     BOK   (asyms_ok B)                    MARKED STAND-IN (image B's start-up record); T5's / T7's.
                                           T3's ZSA (zero-shadow ranges 8-aligned) is NOT a hypothesis here: it is
                                           BOK's aso_zshadow (crt102_topB_zsa).
     IMGVIS (image band's shadow present under ARx, [cf_img_lo, cf_img_top) at CfImg_B)  MARKED STAND-IN
                                           (img_shadow_vis_cf at CfImg_B); T5's / T7's text; T3's IMGV
                                           (Crt102B_T3Base.crt3_img_shadow_vis_B SEGS ARx) is the same Prop by
                                           unfolding.
     PJSTR / PJSET (tpj_string / tpj_set)  the contract texts; T3's HPJS / HPJSET.
     RANOUT (tfuzz_alloc_ran_out_specX)    the contract text; T4's FRO.
     STRLEN / STRCMP (astrlen / astrcmp_realizes_xrom at __wrap_strlen / __wrap_strcmp)  the libc rows; T4's ASTRLEN,
                                           T5's / T6's ASTRCMP, T7's STRCMP. Dischargeable on the cut base by
                                           the libc row's ps_strcmp_xrom_B / ps_strlen_xrom_B (lib/AU/PSstrRo.v
                                           45e63604063e:67 / :76 at commit ebb41f4e9efa, at
                                           its ARc): lib/Reusable/YF0m.v f82202ebccdf and lib/A/PSstrlen.v d2c60d9c2c9f
                                           are on this base at that commit's blobs; lib/Reusable/YGcfStrRo.v,
                                           lib/A/PSstrcmp.v / PSstrRo.v and lib/AU/PSstrlen.v / PSstrcmp.v / PSstrRo.v
                                           are not, so both stay hypotheses here.
     SAME (tsame_specX DOC_D) / FFREE (tfuzz_free_specX)  the contract texts; T6's / T7's.
     PJW (tpj_write_specX DOC_D)          the contract text; T4's PJW (pj_write at +0x2b8, its refusal arm dead in
                                           the cut's text). ALX_CEIL8 is gone: since the cut's src_rd no T4 lemma uses it.
     PNOTING (tparse_noting_specX)        the contract text, at the contract's one CTX0 and every float state; T4's PN
                                           (kb round: T4 proves its parse_noting call, t4_goal_pn in the kb form, from it).
     PAL, pal_uar_img, pal_stack_malloc3, pal_pst_static  MARKED STAND-INS (the image binding of B); T1's
                                           (pal_uar_img at IMG_LO_B / IMG_TOP_B); PAL also gives T8's ENV (pal_env).
                                           Their B' witnesses at YD2l.TfibB are another hand's (Crt102PALibCheckB /
                                           Crt102AF0lCheckB, commit 076d171ebe7b) and are bound
                                           in a TfibB section after this file.
   The text's own premises are not hypotheses: crt_B_under binds them. T3's image facts HB_base / HB_segs / HB_relro
   are CrtImgB102.HB_base_cf / HB_segs_cf / HB_relro_cf (closed at PI_prog_B).

   INPUTS OF RECORD (this branch: the B' lane 01ab5fb67d43 with the A' kb head
   a54cc6d36c2c merged; the B' image witnesses lib/B/Prog/Crt102PALibCheckB.v 1e3119b16a13 / Crt102AF0lCheckB.v
   308247543f0d, lib/B/PALibB.v 5baa19c890f7 and the cut's lib/Reusable/YD2l.v 95803a8b9493 / YCej.v 71ae24321ba4;
   only Section a, the TfibB instance, reads them; the generic sections read none):
   - the glue Crt102Glue.v dd7e849ea932 (the kb Glue c580eb0fe37c, blob 9432a16a13f5, with the lane's host-path
     scrub: CODE-EQUAL to it); the kit Crt102Kit.v 5c6804569429 (the A' kb head's, CODE-EQUAL; its image-free AJW
     runners serve the B' rows); the split's Crt102Img.v f40d6bb6768c, Crt102ImgB.v 312cb05235c8, CrtImgB102.v
     4c2ff1cf5283; the contract texts PRH_FnCheck.v 8feca2000b76 (kit text 4b8f95c0455c: astack_up_x appended), PRH_FnPj.v
     5aca5cbe2cfb, PRH_FnWriter.v d89d3c67b78c, PRH_FnAlloc.v 4d8aeba047e5, PRH_FnEx.v be1dd5ecaaf6, PRH_Base.v
     ef7c8ca98529; the engine's lib/Reusable/YCbqGwild.v 0c63874858e4 and YGcallStackUp.v 136e8c774182;
     lib/B/Listing_prog.v c97cc46b3e13, lib/B/PAImg_prog.v 15fab93fe702, lib/AU/CfImgB.v 519c583c9080,
     lib/Reusable/YImgTop.v d2a97d3111ce; the cut's lib/B/Prog/PLB102.v b350d20c840f, lib/Spec/PresetFreeFo.v
     75c11ade43e4, lib/Spec/PresetRoomCounts.v e7bf70e17551.
   - the B' rows, RE-FIT TO THE kb GLUE ON THIS BRANCH (their blobs: this branch's commit messages), each from the
     owner's lint-clean blob of record (every owner cleared the re-fit, recorded by the walk's owner 17:10Z - 17:16Z):
     T1 Crt102EntryB.v; T2 lib/A/Prog/Crt102B_RRT.v from 1896953741b4 (8d9dd8df94d8); T3
     Crt102B_T3*.v from the scrub 2af9ca0b2c9c; T4 Crt102B_T4.v from a83ec5803824
     (f3b229fd6b02); T5 / T6 Crt102B_T5*.v / _T6*.v from the one T5 / T6 head (01ab's blobs); T7
     Crt102B_T7*.v from the host-path fix fcb97dbe96a5; T8 lib/A/Prog/Crt102TailB.v, X Crt102XB.v and the kit
     Crt102KitB.v (this lane's). The leaves Crt102B_T56_strcmp.v / Crt102B_T7_strcmp.v are unedited.
   - build route pins102: the internal file zfb-targets.85055e6079bccb28.sh, FACTS 8f3e7e1a07f1,
     PAU pau-preset-102.
   - rule 24: proves function check_round_trip (B' composition). proof-index check_round_trip and the B' addresses
     0x82828 / 0x82870: exit 4, the released proofs are plain / ubsan only; the second-agent check: CONFIRM
     (recorded in commit 09469fb2a29b's message); released-branch git grep exit 1; the lane's
     record RULE24.md (sha256 96ef6f3404f0; internal record) (COMPLETE: no #102 walk of check_round_trip
     outside this lane). Written new.

   NUMERALS. ADDRESS: none (the two string addresses are Crt102Img's CRT_MOD_AT_B / CRT_STAMP_B, pa_val of the listing;
   every code address is pa_sigma of the listing or a CRT_*_OFF_B of Crt102Img). LENGTH, as the text states them:
   3 * 2 ^ 20, 3, 56, 54, 2 ^ 62 - 2 ^ 30, 10 (the a0 register index), 8 (the zero-shadow granule, BOK's), 48 (copy's
   cap word, T2's goal). WORD: 0 (the flags at entry). BUDGET COUNT: 0, 64, 66 (the kb table at the end of this file,
   each checked against prh_wk by computation). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YCbqGcallW YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
(* the text's last premise (astack_up_x, kit text 4b8f95c0455c), named qualified in crt_B_under *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
(* the re-hiding move's step relation (YA0nH.SRr'), its mono rule (YSRrG.SRr'_mono)
   and preset's zone (YGcfRehidePost.RZ_cf), used qualified; all three are already in Crt102Glue's closure *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_FnEx PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env Crt102Glue Crt102Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* the rows and the B' instance lemmas, all used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102TailB Crt102B_RRT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require CrtImgB102 Crt102EntryB Crt102XB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102B_T3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102B_T4 Crt102B_T5 Crt102B_T6 Crt102B_T7_top.
(* the B' instance's record and its image witnesses (Section a) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102PALibCheckB Crt102AF0lCheckB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
(* image A's PI_prog_A is also a global instance here (through Crt102Img); the B' record instance is made the first
   choice inside this section, as Crt102B_RRT.v does *)
#[local] Existing Instance PAImg_prog.PI_prog_B | 0.
#[local] Existing Instance PAImg_prog.PL_prog_B | 0.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Notation PA := (PAImg_prog.PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation CFG := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).
(* the text's instance of its two string arguments at B' (Crt102Img.v, pa_val of the B listing) *)
#[local] Notation MODB := (CRT_MOD_AT_B (PA := PA)).
#[local] Notation STAMPB := (CRT_STAMP_B (PA := PA)).

Section f.
(* B and ARx are Context, so every use of this file's names outside the Section names them *)
Context {B : asyms}.
Context {ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop}.

(* ---- THE STRETCH STATEMENTS at image B' for the cuts the glue gives no statement for (J, U, W), in the glue's
   CRT_B_AT_X form, and the open set. The contract's binders are Variables in the order crt_B_under's K takes them,
   so each statement below is a function of exactly those binders. ---- *)
Section s.
Variables (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (Lam : list (Z * Z))
  (peak cnt ran most : Z).
#[local] Notation QFB := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).

(* J (+0x348), the join: crt_at_J_B *)
Definition CRT_B_AT_J : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  crt_at_J_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA) (B := B)
    (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
    (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
    (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)
    fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_J_OFF_B rg memc mdc) QFB.

(* U (+0x1ec), the head of the inlined round_trip_rewrite: crt_at_U_B *)
Definition CRT_B_AT_U : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms,
  crt_at_U_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA) (B := B)
    (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
    (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
    (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)
    fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_U_OFF_B rg memc mdc) QFB.

(* W (+0x2a4 = the glue's CRT_W0_OFF_B, pj_write's argument set-up): crt_at_W_B *)
Definition CRT_B_AT_W : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset,
  crt_at_W_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA) (B := B)
    (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
    (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
    (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)
    fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_W0_OFF_B rg memc mdc) QFB.
End s.

(* ---- tcheck_round_trip_specX's binders and premises at B', ALL OF THEM, in the text's order (PRH_FnCheck.v
   8feca2000b76:1326-1390, keyed on ReaderRes.jr_strtod: no rp_sm binder, no rp_sm premise), in front of a conclusion K
   at the binders K reads. kb round: the text's wild room (:1366) is in its place after ck_frm0, and its last premise
   astack_up_x (:1390, kit text 4b8f95c0455c) after prh_cons_from. crt102_topB_of hands the text's own premises to it,
   so a premise here that is not the text's does not typecheck there. ---- *)
Definition crt_B_under (CTX0 : list (list Z)) (a_mod_at a_stamp : Z)
  (K : list Z -> list (option nat * option nat * option nat) -> nat -> list Z ->
       alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model ->
       Z -> PjTree.jv -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
    (Lam : list (Z * Z)) (peak cnt ran most : Z),
  fpre (fx := fx) (PA := PA) B ARx STKC ly S Hp W regs mem md ch ->
  YAkMemnorm.memnorm SEGS mem ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch) ->
  getr regs 10 = w64 doc ->
  ck_tree_ok (PA := PA) ly S Lam W mem doc t D ->
  ck_read x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  kept_img (PA := PA) B a_mod_at (Z.of_nat (length ck_MOD_AT) + 1) ->
  kept_img (PA := PA) B a_stamp (Z.of_nat (length ck_STAMP) + 1) ->
  PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x) -> PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 -> cnt < 2 ^ 62 - 2 ^ 30 ->
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (PresetReqAt.round_trip ReaderRes.jr_strtod t) ->
  ran = 0 ->
  RQA_crt t <= most ->
  blocks_bytes S + LIVE_check_round_trip t <= LIVE_MAX -> RQ_crt t + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_round_trip ->
  room_live_cf S -> PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S -> ck_frm0 (fx := fx) ->
  (length rp_os <= 4)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_round_trip) (st_depot S) ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (PresetReqAt.round_trip ReaderRes.jr_strtod t)) ->
  YGcallStackUp.astack_up_x SEGS ly W (spZ regs) mem ->
  K rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most.

(* ---- THE SEAMS, each a stretch statement under the text's premises: J / U / W are this file's statements, X / C /
   L3 / L0 the glue's (CRT_B_AT_X / _C / _L3 / _L0) at the B' cut offsets, M T1's continuation
   crt102eb_cont (by name; it takes the binders in K's order) ---- *)
Definition CRT_B_SEAM_J (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_B_under CTX0 a_mod_at a_stamp CRT_B_AT_J.
Definition CRT_B_SEAM_U (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_B_under CTX0 a_mod_at a_stamp CRT_B_AT_U.
Definition CRT_B_SEAM_W (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_B_under CTX0 a_mod_at a_stamp CRT_B_AT_W.
Definition CRT_B_SEAM_X (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_B_under CTX0 a_mod_at a_stamp
    (fun rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most =>
     CRT_B_AT_X (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
       (CRT_PC := CRT_PC_B) (CRT_X_OFF := CRT_X_OFF_B) (B := B) (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x)
       (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs)
       (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran)
       (most := most)).
Definition CRT_B_SEAM_C (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_B_under CTX0 a_mod_at a_stamp
    (fun rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most =>
     CRT_B_AT_C (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
       (CRT_PC := CRT_PC_B) (CRT_C_OFF := CRT_C_OFF_B) (B := B) (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x)
       (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs)
       (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran)
       (most := most)).
Definition CRT_B_SEAM_L3 (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_B_under CTX0 a_mod_at a_stamp
    (fun rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most =>
     CRT_B_AT_L3 (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
       (CRT_PC := CRT_PC_B) (CRT_L3_OFF := CRT_L3_OFF_B) (B := B) (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x)
       (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs)
       (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran)
       (most := most)).
Definition CRT_B_SEAM_L0 (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_B_under CTX0 a_mod_at a_stamp
    (fun rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most =>
     CRT_B_AT_L0 (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
       (CRT_PC := CRT_PC_B) (CRT_L0_OFF := CRT_L0_OFF_B) (B := B) (ARx := ARx) (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x)
       (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs)
       (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran)
       (most := most)).
Definition CRT_B_SEAM_M (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_B_under CTX0 a_mod_at a_stamp (@Crt102EntryB.crt102eb_cont fx rc SK RL PA B ARx).
(* ---- SECTION HYPOTHESES, each with its owner (header) ---- *)
(* the allocator laws at the cf instance's head (engine fold, YCbqG; at ARcf YGcallcf.AR_laws_x_cf); every row's *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* T1's: frame class 3 with the memnorm keep (the frame-class lane), the owned-low law (engine), __asan_memset (OSet)
   at the listing's own pc (the libc row) *)
Hypothesis ASM3 : YGcallMxmn.astack_malloc_realizes_xm (fx := fx) SEGS B ARx 3.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis AMS : YGcallMxmn.aintrin_realizes_xm (fx := fx) SEGS B ARx OSet (SIGMA AS___asan_memset).
(* THE CONTRACT'S UNIVERSE CONTEXT: the one CTX0 the contract is stated at. The callee texts below that take a
   CTX0 (RTT, PJFREE, PJSTR, PJSET, PJW, PNOTING) are assumed at this CTX0 only, the only one every seam uses *)
Variable CTX0 : list (list Z).
(* T2's: round_trip_text's contract text (it has its own walk), at the contract's CTX0 and every float state *)
Hypothesis RTT : forall fxk : YK11.FPState,
  @tround_trip_text_specX fxk rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0.
(* T8's (Crt102TailB): the inline release, exactly the three hypotheses of YGcallSx.v's aj_flag_store_x (engine:
   ASFX = YG0dcf.v astack_free_law_cf, FFLX = AR_flag_law_ok_cf / AR_client_img_law_ok_cf, SFX = YGcallScf.v
   stack_free_x_any) *)
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
(* T8's: the frame's flag byte is present (at ARcf AR_flag_law_ok_cf's first conjunct) *)
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
(* T8's: __asan_set_shadow_f5 at the poison value 0xf5 (the frame-class lane) *)
Hypothesis SETSH : forall fxk : YK11.FPState,
  YGcallMxmn.aset_shadow_realizes_xm (fx := fxk) SEGS B ARx (SIGMA AS___asan_set_shadow_f5) 245.
(* T8's and T7's: pj_free's contract text, at the contract's CTX0 and every float state *)
Hypothesis PJFREE : forall fxk : YK11.FPState,
  @PRH_FnPj.tpj_free_specX fxk rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0 DOC_D.
(* T5's / T7's: MARKED STAND-IN, image B's start-up record *)
Hypothesis BOK : asyms_ok B.
(* T5's / T7's, verbatim: MARKED STAND-IN (img_shadow_vis_cf at CfImg_B) *)
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* T3's HPJS / HPJSET: pj_string's / pj_set's contract texts, at the contract's CTX0 and every float state *)
Hypothesis PJSTR : forall fxq : YK11.FPState,
  @PRH_FnPj.tpj_string_specX fxq rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0.
Hypothesis PJSET : forall fxq : YK11.FPState,
  @PRH_FnPj.tpj_set_specX fxq rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0 DOC_D.
(* T4's FRO: fuzz_alloc_ran_out's contract text *)
Hypothesis RANOUT : forall fxq : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_ran_out_specX fxq rc CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK.
(* the libc rows: __wrap_strlen (T4's ASTRLEN) and __wrap_strcmp (T5's / T6's ASTRCMP, T7's STRCMP) *)
Hypothesis STRLEN : forall fxk : YK11.FPState,
  YGcallMxmn.astrlen_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strlen).
Hypothesis STRCMP : forall fxk : YK11.FPState,
  YGcallMxmn.astrcmp_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
(* T6's / T7's: same (n = DOC_D) and fuzz_free's contract texts *)
Hypothesis SAME : forall fxk : YK11.FPState,
  @PRH_FnEx.tsame_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK DOC_D.
Hypothesis FFREE : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_free_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK.
(* T4's PJW: pj_write's contract text, at the contract's CTX0 and every float state *)
Hypothesis PJW : forall fxk : YK11.FPState,
  @PRH_FnWriter.tpj_write_specX fxk rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0 DOC_D.
(* T4's PN (kb round: T4 proves t4_goal_pn, restated in the kb form, from it): parse_noting's contract text, at the
   contract's CTX0 and every float state *)
Hypothesis PNOTING : forall fxk : YK11.FPState,
  @tparse_noting_specX fxk rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0.

(* T3's ZSA (the image's zero-shadow ranges are granule-aligned) is BOK's aso_zshadow, not a hypothesis *)
Lemma crt102_topB_zsa : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Proof.
intros q m Hin. pose proof BOK as Hz. apply aso_zshadow in Hz. rewrite Forall_forall in Hz.
destruct (Hz (q, m) Hin) as (_ & _ & H1 & H2 & _). split; [exact H1 | exact H2].
Qed.

(* ---- T1's image stand-ins (the image binding of B), for generic B; their B' witnesses at YD2l.TfibB are
   bound after this file (header) ---- *)
Section p.
(* MARKED STAND-IN (T1's PAL; also T8's ENV through pal_env) *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PA) B.
(* MARKED STAND-IN (T1's pal_uar_img, at B''s bounds) *)
Hypothesis pal_uar_img : IMG_LO_B <= as_uar_cell B /\ as_uar_cell B + 4 <= IMG_TOP_B.
(* MARKED STAND-IN (T1's pal_stack_malloc3) *)
Hypothesis pal_stack_malloc3 : SIGMA AS___asan_stack_malloc_3 = pc_stack_malloc (as_code B) 3.
(* MARKED STAND-IN (T1's pal_pst_static) *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

(* ---- THE J SEAM, CLOSED: row T8, Crt102TailB.crt102_tail_B (its ENV is PAL's pal_env) ---- *)
Lemma crt102_topB_J : forall a_mod_at a_stamp, CRT_B_SEAM_J CTX0 a_mod_at a_stamp.
Proof.
intros a_mod_at a_stamp. unfold CRT_B_SEAM_J, crt_B_under.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
unfold CRT_B_AT_J.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HJB.
exact (@Crt102TailB.crt102_tail_B fx rc CfImg_B SK RL B ARx LAWS (pal_env (PI := PA) B PAL) OWNLOW
  ASFX FFLX SFX FFLP SETSH CTX0 PJFREE ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D
  Lam peak cnt ran most HPRE HCL HTREE HOS4 fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HJB).
Qed.

(* ---- THE X SEAM, CLOSED: Crt102XB.cb_at_X_B, its TAIL the J seam ---- *)
Lemma crt102_topB_X : forall a_mod_at a_stamp, CRT_B_SEAM_X CTX0 a_mod_at a_stamp.
Proof.
intros a_mod_at a_stamp. unfold CRT_B_SEAM_X, crt_B_under.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
pose proof (crt102_topB_J a_mod_at a_stamp rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HJ.
cbv beta. unfold CRT_B_AT_X.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HX.
exact (@Crt102XB.cb_at_X_B fx rc SK RL B ARx LAWS ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D
  Lam peak cnt ran most HPRE HTREE HJ fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HX).
Qed.

(* ---- THE C SEAM, CLOSED: row T7, Crt102B_T7_top.crtB_T7 (CRT_B_SEG_T7 : X -> C) at the X seam ---- *)
Lemma crt102_topB_C : CRT_B_SEAM_C CTX0 MODB STAMPB.
Proof.
unfold CRT_B_SEAM_C, crt_B_under.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
pose proof (crt102_topB_X MODB STAMPB rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HX.
cbv beta in HX |- *.
exact (@Crt102B_T7_top.crtB_T7 fx rc CfImg_B RL SK B ARx ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc
  t D Lam peak cnt ran most CTX0 LAWS HPRE HTREE HRAN HCL HCTX HKM HKS BOK IMGVIS FFREE PJFREE STRCMP HOS4
  HX).
Qed.

(* ---- THE L3 SEAM, CLOSED: row T6, Crt102B_T6.crtB_T6 (CRT_B_SEG_T6 : C -> L3) at the C seam ---- *)
Lemma crt102_topB_L3 : CRT_B_SEAM_L3 CTX0 MODB STAMPB.
Proof.
unfold CRT_B_SEAM_L3, crt_B_under.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
pose proof (crt102_topB_C rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HC.
cbv beta in HC |- *.
exact (@Crt102B_T6.crtB_T6 fx rc RL SK B ARx LAWS ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HTREE HREAD STRCMP SAME HC).
Qed.

(* ---- THE L0 SEAM, CLOSED: row T5, Crt102B_T5.crtB_T5 (CRT_B_SEG_T5 : L3 -> C -> L0) at the L3 and C seams ---- *)
Lemma crt102_topB_L0 : CRT_B_SEAM_L0 CTX0 MODB STAMPB.
Proof.
unfold CRT_B_SEAM_L0, crt_B_under.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
pose proof (crt102_topB_C rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HC.
pose proof (crt102_topB_L3 rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HL3.
cbv beta in HC, HL3 |- *.
exact (@Crt102B_T5.crtB_T5 fx rc RL SK B ARx LAWS ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HTREE HMN HREAD HLENX HWL0 HWL1 HCNT HLED HRQA HKM BOK IMGVIS STRCMP HL3 HC).
Qed.

(* ---- THE W SEAM, CLOSED (kb round): row T4, Crt102B_T4.crtB_T4 (L0 -> W) at the L0 seam. T4 proves its
   parse_noting call itself (t4_goal_pn, restated in the kb form: the room premise and the text's budgeted post, Qed
   as t4_goal_pn_holds from PN), with the room derived at the call from the live state's journal at kb 64 and the
   text's entry room HWR (HWR0 there); pj_write's text PJW where T4_GOAL_PJW stood ---- *)
Lemma crt102_topB_W : CRT_B_SEAM_W CTX0 MODB STAMPB.
Proof.
unfold CRT_B_SEAM_W, crt_B_under.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
pose proof (crt102_topB_L0 rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HL0.
cbv beta in HL0.
apply @Crt102B_T4.crtB_T4 with (fx := fx) (rc := rc) (ci := CfImg_B) (RL := RL) (SK := SK) (B := B) (ARx := ARx)
  (rp_sm := ReaderRes.jr_strtod) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (ch := ch) (doc := doc) (t := t)
  (D := D) (x := x) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most) (CTX0 := CTX0).
all: first [exact HL0 | exact RANOUT | exact STRLEN | assumption].
Qed.

(* ---- THE U SEAM, CLOSED: row T3, Crt102B_T3.crt102b_seg_T3 : STMT_X -> STMT_W -> STMT_U, at the X seam and the W
   seam. T3's image facts are CrtImgB102's, closed at PI_prog_B; its ZSA is crt102_topB_zsa; its IMGV is IMGVIS by
   unfolding; its Section variable rp_sm is ReaderRes.jr_strtod. ---- *)
Lemma crt102_topB_U : CRT_B_SEAM_U CTX0 MODB STAMPB.
Proof.
unfold CRT_B_SEAM_U, crt_B_under.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
pose proof (crt102_topB_X MODB STAMPB rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HX.
pose proof (crt102_topB_W rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HW.
cbv beta in HX, HW.
exact (@Crt102B_T3.crt102b_seg_T3 fx rc CfImg_B RL SK PA CrtImgB102.HB_base_cf CrtImgB102.HB_segs_cf
  CrtImgB102.HB_relro_cf B ARx LAWS crt102_topB_zsa IMGVIS CTX0 PJSTR PJSET RANOUT
  ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HCL HTREE HREAD HLENX HWL0 HWL1 HKM HKS HCNT HRAN HLIVE HRQ HOS4 HX HW).
Qed.


(* ---- THE M SEAM, CLOSED (kb round): T1's continuation crt102eb_cont, by row T2's segment lemma Crt102B_RRT.crtb_rrt
   (Qed at the kb round) with TAIL := the J seam and REWR := the U seam. crtb_rrt is crtb_at_M with its two premises
   discharged in T2: the bridge (rtt1's post in the text's form crtb_rtt_Q -> crtb_rtt_Q_k0, conjunct by conjunct, the
   copy arm's free order and cap word from the cut's own conjuncts) and crtb_wild_budget, RESTATED IN THE kb FORM
   there (the twin of Crt102Arms.arms_wild_budget) and proved, crtb_wild_budget_goal, from the text's entry room (T2's
   HWR0 := HWR here). T2's HUP0 is the text's last premise (astack_up_x at the entry sp), which T2 hands to both
   round_trip_text calls ---- *)
Lemma crt102_topB_M : CRT_B_SEAM_M CTX0 MODB STAMPB.
Proof.
unfold CRT_B_SEAM_M, crt_B_under.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
pose proof (crt102_topB_J MODB STAMPB rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HJ.
pose proof (crt102_topB_U rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HU.
cbv beta in HJ, HU. unfold Crt102EntryB.crt102eb_cont.
intros fxk lyc Sc Hpc Wc memc mdc kj pos rg HFZ HFK HL HDR HZ HPOS.
apply @Crt102B_RRT.crtb_rrt with (fx := fx) (rc := rc) (ci := CfImg_B) (SK := SK) (RL := RL) (B := B) (ARx := ARx)
  (LAWS := LAWS) (CTX0 := CTX0) (RTT := RTT)
  (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W)
  (regs := regs) (mem := mem) (md := md) (ch := ch) (doc := doc) (t := t) (D := D) (x := x) (Lam := Lam)
  (peak := peak) (cnt := cnt) (ran := ran) (most := most) (HOS4 := HOS4) (TAIL := HJ) (REWR := HU)
  (fxk := fxk) (lyc := lyc) (Sc := Sc) (Hpc := Hpc) (Wc := Wc) (memc := memc) (mdc := mdc) (kj := kj) (pos := pos)
  (rg := rg).
all: first [exact HFZ | exact HFK | exact HL | exact HDR | exact HZ | exact HPOS | assumption].
Qed.


(* ---- THE COMPOSITION: entry .. M by row T1 (Crt102EntryB.crt102_entry_B_cf at PI_prog_B), whose continuation is
   the M seam (THE T1 -> T2 JOIN), then the post: QF is the text's BUDGETED post (kb round: fpostFbm .. (wbudget []
   (prh_wk F_check_round_trip)) of fQmn mem QT, the journal at the same budget WS), and QT is the text's post by
   unfolding; the inner memnorm keep is dropped (Crt102Top.crt102_top_of's bridge at B') ---- *)
Lemma crt102_topB_of : forall a_mod_at a_stamp,
  CRT_B_SEAM_M CTX0 a_mod_at a_stamp ->
  tcheck_round_trip_specX (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) (PI := prh_img_B) (RL := RL)
    (L := B_prog_listing) (PA := PA) B ARx SK CTX0 a_mod_at a_stamp.
Proof.
intros a_mod_at a_stamp SM. unfold tcheck_round_trip_specX.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
pose proof (SM rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc
  t D x Lam peak cnt ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA
  HLIVE HRQ HFRM HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0) as HM.
eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
{ exact (@Crt102EntryB.crt102_entry_B_cf fx rc SK RL B ARx LAWS PAL pal_uar_img pal_stack_malloc3 pal_pst_static
    ASM3 OWNLOW AMS rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D Lam peak cnt ran most
    HPRE H10 HTREE HLED HRUN HFRM HROOM HIFC HFRM0 HCONS HM). }
intros W' c' _ HQ. unfold QF, fpostFbm, fpostFb, YCbqGwild.apost_base_xbFR in HQ |- *.
destruct HQ as (fx2 & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HFZ' & HFK' & HPW & HJW & Hpr &
  [[HQT _] Hm]).
exists fx2, ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact HFZ'|]. split; [exact HFK'|]. split; [exact HPW|]. split; [exact HJW|].
split; [exact Hpr|]. split; [exact HQT | exact Hm].
Qed.

(* ---- THE CONTRACT AT B', generic in B, at the text's instance of its two string addresses: Qed (kb round). The M
   seam owes nothing: its wild budget is crtb_wild_budget_goal (T2) and the parse_noting call's is T4's own, both from
   the text's entry room; the Record CRT_B_OPEN (its one field t4_pn) and the antecedent CRT_B_WILD_BUDGET are retired
   after their kb-form content was proved, and with them crt102_topB_open, which without the Record is this
   statement. ---- *)
Theorem crt102_topB :
  tcheck_round_trip_specX (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) (PI := prh_img_B) (RL := RL)
    (L := B_prog_listing) (PA := PA) B ARx SK CTX0 MODB STAMPB.
Proof.
exact (crt102_topB_of MODB STAMPB crt102_topB_M).
Qed.

End p.
End f.

(* ======================================================================================================== *)
(* ---- THE B' INSTANCE OF B: YD2l.TfibB, the B' asan-ubsan image's generated record (lib/Reusable/YD2l.v
   0d0bc856b447, TfibB_syms : YF0m.TfibSyms TfibB), on the lane head 15ae54c1afac. T1's four image stand-ins and BOK
   are discharged here, not assumed:
     PAL               Crt102PALibCheckB.crt102_PAL_TfibB (= PALibB.exvi_eh_palib, lib/B/PALibB.v 5baa19c890f7), which
                       also gives T8's ENV (pal_env);
     pal_uar_img       Crt102PALibCheckB.crt102_uar_img_TfibB (by computation, at IMG_LO_B / IMG_TOP_B as T1 states it);
     pal_stack_malloc3 Crt102AF0lCheckB.crt102_stack_malloc3_TfibB (by computation on the listing and TfibB's code);
     pal_pst_static    Crt102PALibCheckB.crt102_pst_static_TfibB (at YD2l.TfibB_syms, by computation over prh_pst);
     BOK               YD2l.TfibB_ok (asyms_ok TfibB, Qed in YD2l.v), so T3's ZSA (crt102_topB_zsa) is closed too.
   ARx stays free: the allocator-side hypotheses keep their owners (header), and IMGVIS stays a MARKED STAND-IN
   (it reads ARx). ---- *)
Section a.
Context {ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop}.
#[local] Notation TB := (YD2l.TfibB).
(* the Section hypotheses of Section f, at B := TfibB; owners as there (header); the CTX0-taking texts at the
   contract's one CTX0, as in Section f *)
Hypothesis LAWS : AR_laws_x SEGS TB ARx cf_head.
Hypothesis ASM3 : YGcallMxmn.astack_malloc_realizes_xm (fx := fx) SEGS TB ARx 3.
Hypothesis OWNLOW : ARx_owned_low_law SEGS TB ARx.
Hypothesis AMS : YGcallMxmn.aintrin_realizes_xm (fx := fx) SEGS TB ARx OSet (SIGMA AS___asan_memset).
Variable CTX0 : list (list Z).
Hypothesis RTT : forall fxk : YK11.FPState,
  @tround_trip_text_specX fxk rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA TB ARx SK CTX0.
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TB ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned TB ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
Hypothesis SETSH : forall fxk : YK11.FPState,
  YGcallMxmn.aset_shadow_realizes_xm (fx := fxk) SEGS TB ARx (SIGMA AS___asan_set_shadow_f5) 245.
Hypothesis PJFREE : forall fxk : YK11.FPState,
  @PRH_FnPj.tpj_free_specX fxk rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA TB ARx SK CTX0 DOC_D.
(* MARKED STAND-IN (it reads ARx, which stays free) *)
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis PJSTR : forall fxq : YK11.FPState,
  @PRH_FnPj.tpj_string_specX fxq rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA TB ARx SK CTX0.
Hypothesis PJSET : forall fxq : YK11.FPState,
  @PRH_FnPj.tpj_set_specX fxq rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA TB ARx SK CTX0 DOC_D.
Hypothesis RANOUT : forall fxq : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_ran_out_specX fxq rc CfParams_preset prh_img_B RL B_prog_listing PA TB ARx SK.
Hypothesis STRLEN : forall fxk : YK11.FPState,
  YGcallMxmn.astrlen_realizes_xrom (fx := fxk) SEGS TB ARx RLO RHI (SIGMA AS___wrap_strlen).
Hypothesis STRCMP : forall fxk : YK11.FPState,
  YGcallMxmn.astrcmp_realizes_xrom (fx := fxk) SEGS TB ARx RLO RHI (SIGMA AS___wrap_strcmp).
Hypothesis SAME : forall fxk : YK11.FPState,
  @PRH_FnEx.tsame_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA TB ARx SK DOC_D.
Hypothesis FFREE : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_free_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA TB ARx SK.
Hypothesis PJW : forall fxk : YK11.FPState,
  @PRH_FnWriter.tpj_write_specX fxk rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA TB ARx SK CTX0 DOC_D.
Hypothesis PNOTING : forall fxk : YK11.FPState,
  @tparse_noting_specX fxk rc CfImg_B CfParams_preset prh_img_B RL B_prog_listing PA TB ARx SK CTX0.

(* ---- THE CONTRACT AT THE B' INSTANCE (B := TfibB, the strings at CRT_MOD_AT_B / CRT_STAMP_B), with T1's four image
   stand-ins and BOK discharged by the witnesses: Qed (kb round), as crt102_topB. IMGVIS is the one stand-in left
   (header). crt102_topB_open_TfibB, the same statement modulo the retired Record, is retired with it. ---- *)
Theorem crt102_topB_TfibB :
  tcheck_round_trip_specX (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) (PI := prh_img_B) (RL := RL)
    (L := B_prog_listing) (PA := PA) TB ARx SK CTX0 MODB STAMPB.
Proof.
(* the composition at B := TfibB: each Section hypothesis of the seams by this Section's own of the same type, each
   image stand-in and BOK by its witness *)
eapply @crt102_topB_of with (B := TB) (ARx := ARx).
all: try first [ exact Crt102PALibCheckB.crt102_PAL_TfibB | exact Crt102PALibCheckB.crt102_uar_img_TfibB
  | exact Crt102AF0lCheckB.crt102_stack_malloc3_TfibB | exact Crt102PALibCheckB.crt102_pst_static_TfibB
  | exact YD2l.TfibB_ok | assumption ].
eapply @crt102_topB_M with (B := TB) (ARx := ARx).
all: first [ exact Crt102PALibCheckB.crt102_PAL_TfibB | exact Crt102PALibCheckB.crt102_uar_img_TfibB
  | exact Crt102AF0lCheckB.crt102_stack_malloc3_TfibB | exact Crt102PALibCheckB.crt102_pst_static_TfibB
  | exact YD2l.TfibB_ok | assumption ].
Qed.
End a.
End w.

(* ---- THE BUDGET AT EVERY SITE (kb round), each by computation on prh_wk (PRH_Base.v): the budget into a boundary
   plus what the stretch spends is the boundary's kb, by IDENTITY at every site but two; the two STEP UPS (row T2's
   C3 into J_B, row T4's failed-write arm into L0_B) are both 64 -> 66, where 64 < 66 and 64 <> 66, by crt_live
   monotonicity (Crt102B_RRT.crtb_live_mono / Crt102KitB.cb4_live_mono, the twins of Crt102Arms.arms_live_mono). ---- *)
Lemma crt102_topB_kb_M : (0 = 0)%nat.
Proof. exact eq_refl. Qed.
Lemma crt102_topB_kb_rtt1 : (0 + prh_wk F_round_trip_text = prh_wk F_round_trip_text)%nat.
Proof. exact eq_refl. Qed.
Lemma crt102_topB_kb_rtt2_U : (prh_wk F_round_trip_text + prh_wk F_round_trip_text = 64)%nat.
Proof. exact eq_refl. Qed.
Lemma crt102_topB_kb_pn_L0 :
  (prh_wk F_round_trip_text + prh_wk F_round_trip_text + prh_wk F_parse_noting = prh_wk F_check_round_trip)%nat.
Proof. exact eq_refl. Qed.
Lemma crt102_topB_kb_QF : (prh_wk F_check_round_trip = 66)%nat.
Proof. exact eq_refl. Qed.
Lemma crt102_topB_kb_step_lt : (prh_wk F_round_trip_text + prh_wk F_round_trip_text < prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.
Lemma crt102_topB_kb_step_ne : (prh_wk F_round_trip_text + prh_wk F_round_trip_text <> prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.

(* ---- the FPState and IMAGE elaboration check (the walk owner's rule and its amendment, 2026-10-29; the image-B rule of
   the kb round): theorems by `Check @`, with implicits shown, so every carried hypothesis of the two tops is printed
   as its binder; every Prop-bodied definition of this file by `Print`, implicits on and notations off, so the body is
   read. The class position of every FPState-taking constant must hold the Section's `fx`; a bound `fxk` may appear
   only as an explicit argument (crt_cfg .. fxk, inside the glue's crt_at_* bodies) or as a hypothesis's own binder.
   Every PAImg position must hold PAImg_prog.PI_prog_B, every listing B_prog_listing, every PrhImg prh_img_B, every
   CfImg CfImg_B: never image A's PI_prog_A / A_prog_listing / prh_img_A / CfImg_A. ---- *)
Set Printing Implicit.
Check @crt102_topB.
Check @crt102_topB_TfibB.
Check @crt102_topB_zsa.
Check @crt102_topB_J.
Check @crt102_topB_X.
Check @crt102_topB_C.
Check @crt102_topB_L3.
Check @crt102_topB_L0.
Check @crt102_topB_W.
Check @crt102_topB_U.
Check @crt102_topB_M.
Check @crt102_topB_of.
Unset Printing Notations.
Print CRT_B_AT_J.
Print CRT_B_AT_U.
Print CRT_B_AT_W.
Print crt_B_under.
Print CRT_B_SEAM_J.
Print CRT_B_SEAM_U.
Print CRT_B_SEAM_W.
Print CRT_B_SEAM_X.
Print CRT_B_SEAM_C.
Print CRT_B_SEAM_L3.
Print CRT_B_SEAM_L0.
Print CRT_B_SEAM_M.
Set Printing Notations.
Unset Printing Implicit.

(* every exported name resolves to the compiled constant of THIS file (Locate against the .vo, not a text search) *)
Locate crt102_topB.
Locate crt102_topB_TfibB.
Locate crt102_topB_zsa.
Locate crt102_topB_J.
Locate crt102_topB_X.
Locate crt102_topB_C.
Locate crt102_topB_L3.
Locate crt102_topB_L0.
Locate crt102_topB_W.
Locate crt102_topB_U.
Locate crt102_topB_M.
Locate crt102_topB_of.
Locate crt_B_under.

Print Assumptions crt102_topB.
Print Assumptions crt102_topB_TfibB.
Print Assumptions crt102_topB_J.
Print Assumptions crt102_topB_X.
Print Assumptions crt102_topB_C.
Print Assumptions crt102_topB_L3.
Print Assumptions crt102_topB_L0.
Print Assumptions crt102_topB_W.
Print Assumptions crt102_topB_U.
Print Assumptions crt102_topB_M.
Print Assumptions crt102_topB_of.
Print Assumptions crt102_topB_kb_step_lt.
Print Assumptions crt102_topB_kb_step_ne.
(* RETIRED NAMES (kb round): no constant of this name exists any more *)
Fail Check crt102_topB_open.
Fail Check crt102_topB_open_TfibB.
Fail Check CRT_B_OPEN.
Fail Check CRT_B_SEAM_OPEN.
Fail Check CRT_B_WILD_BUDGET.

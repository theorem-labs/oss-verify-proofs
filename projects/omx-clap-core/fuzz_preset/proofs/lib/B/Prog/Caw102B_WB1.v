(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the HEAD HALF of the image-B (fuzz_reply.asan-ubsan) TOP segment of
   fuzz_reply's drain and the composed TOP.  TOP (lib/B/W_drain_cx.v dr_top_stmt, DI 0x833c0 -> DI / DEND / DRB 0)
   is split at B's slot-found point 0x83524 (lib/B/W_drain_topb_cx.v A_dr_slot, a Theorem Labs lane, FROZEN):
     head  DI 0x833c0 -> DT2 0x83524 at the grown state dgrow s1: the round's growth (cap - used < 4096 tested
           as `(cap - used) >> 12 != 0` at 0x833e4; realloc #1 at 0x83410 through arealloc_cf_rule, whose forced
           success refutes the failure arm `beqz a0 -> 0x83fa8`), then source_of's scan over g_s 0x83498 ..
           0x834cc, which finds slot j at the `beq a1,a4` of 0x834c0 (the not-found exit 0x834d0 is refuted from
           DMEM's asrc_at at dHA (open = 1, fd = hs_fd) with DSAME / DBASE's hs_fd = re_fd, and aothers_at for the
           slots before j);
     tail  DT2 -> DI (EINTR) / DEND / DRB 0, a Theorem Labs lane's dr_toptail_stmt.
   0x83524 is reached only from that beq (0x83520 is `j 0x83574`), and between 0x833c0 and 0x83524 the code writes
   only s3, s7, a0-a6 and (at realloc) ra, so DI's dregs_top holds at the seam unchanged.
   dr_top_of composes the two halves: the tail's EINTR continuation at dclr sg is dr_top_stmt's at
   dclr (dgrow s1), because ds_eintr (dgrow s1) reduces to ds_eintr s1. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_drain_tophead.v, with its module paths and module names changed; 2374 of its 2506 lines of code are new or changed and 4077 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/read_members.v, with its module paths and module names changed; 598 of its 674 lines of code are new or changed and 2430 lines of the source are left out. *)
(* fuzz_preset, image B' (asan-ubsan, harness fix #102: pin sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b):
   check_as_written's segment WB1 (row R7-2 of the #102 re-walk; the NULL arm, NEW in #102) in the continuation
   form of lib/B/Prog/Caw102B.v (re-fitted to the f97c re-keyed base by the #102 re-walk for
   B', CawGWB1; plan, the internal file PLAN-cno-caw-102.md section 5.4, row WB1).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   rule-24 CONFIRM: a checker (record R24Lookup), plan, the internal file PLAN-cno-caw-102.md section 2: the proof index's lookup of
   check_as_written rc=0, no walk keyed to B' caw 0x81f78 or the #102 pins.
   THE SEGMENT (B' pcs): cut_mal at 0x81fbc `jal __wrap_malloc` (a0 = size + 1), the call, the return site 0x81fc0
   `beqz a0`:
     - a0 <> 0 (the scratch): beqz not taken, cut_ev at 0x81fc4 (caw_K_ev), the malloc event made (caw_prog at caw_ev1);
     - a0 = 0 (expected()'s noted(), new:85-88): 0x81ff0 `auipc a0` (the listing's PHi .. 10), 0x81ff4 `addi s1, zero, 1`,
       0x81ff8 `sb s1, -0x270(a0)` (g_own_ran_out := 1), 0x81ffc `j` 0x82058 = cut_end with r = 1, own = 1 and no event
       made (cut_end's left arm: caw_prog at [] and the text's OUTCOME exclusion caw_dead C; caw_K_end).
   No report / trap site and no abort edge lies in 0x81fbc .. 0x81ffc (the B' listing, Listing_prog.v c97cc46b3e13
   slots 572-588: one PCall, the branch, auipc / addi / sb / j): nothing to refute here. The UBSan pointer-overflow
   trap 0x8207c is WB0's (refuted there); the abort tail 0x82080 is WB5's.
   On the kit's cut of the #102 batch, preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) (prepared at preset-tree-at-2026-10-30T02-53-02Z.tsv (sha256 477c088a7ad3; internal record) on the batch tip preset-tree-at-2026-10-30T02-01-18Z.tsv (sha256 a12cae64b2b5; internal record)).
   BASE OF RECORD (statements, not edited here): this row's lib/B/Prog/Caw102B.v, statements of blob 5a8082469eb1
   (caw_pre: the text's 25 premises at that blob, 27 now with the hull budget and HPOS (Caw102B.v:139-165), read BY NAME through caw_pre_fpre .. caw_pre_frm0;
   caw_cnt, the conjunction of the two count premises (caw_pre_cnt); caw_prog, caw_ev1, caw_evs, caw_dead,
   caw_run_at_nth; cut_mal / caw_K_mal, cut_ev / caw_K_ev, cut_end / caw_K_end; caw_ledger (the LAST conjunct of every
   cut); caw_req, caw_hblock, caw_chain, caw_scr_new), on the kit's cut of the #102 batch,
   preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) (PRH_FnCheck.v c40cf3fdcd2a tcheck_as_written_specX :832-902, PRH_Base.v ef7c8ca98529, PRH_Refute.v
   23f7a37f01c9).
   Every base name with an implicit float state in a statement of this file gets the entry's, `(fx := fx)`.
   STEP-2 RE-FIT (the free / realloc re-hiding move; statements of lib/B/Prog/Caw102B.v blob c0ad2b208b9a): the
   malloc's call rule is the keep twin YGcallMxmnKeep.aj_malloc_x_ct_m_keep over amalloc_realizes_x_xs_keep, so
   AMALLOC is YGcfMallocComposeKeep.amalloc_realizes_cf_keep. The twin asks QMm_cf at the call memory: cf_hull_ok by
   PresetHullPay.hull_ok_of_budget from cut_mal's new last conjunct (hull_budget S3 [HMal; HFr]); arodata_ok_cf by
   YGcfAroBridge.arodata_ok_cf_of_P from caw_pre's reader form carried to the call memory by the journal's image clause
   (ajx_img), which asks Hpst_rw and the cf layer's five relro rows (six new Section hypotheses, in Caw102B_WB2.v's
   spelling). cut_ev's new last conjunct hull_budget S2 [HFr] by PresetHullBudget.hull_budget_app with
   hull_used_of_call (YGcfSecsStep.secs_malloc_step). caw_WB1's statement inside the section is unchanged.
   WHAT CHANGED (vs the P'' file of the caw102b universe trial, blob 9d006284ad1e), and why:
   the batch text c40cf3fdcd2a.
   - NO RUN-WORD LIST (:841): prh_univ_closure takes CTX0 only (PRH_Base.v :1203) and cawB has no c_DW, so w1_trace
     drops its DW binder and the malloc's trace HTR is read off caw_pre_univ at c_CTX0 C alone.
   - THE ROOM COUNTS ARE ENTRY PREMISES (:862-863): caw_pre now has 27 conjuncts (the hull budget and HPOS follow, Caw102B.v:139-165); caw_WB1 still takes caw_cnt C right
     after caw_pre (the top supplies caw_pre_cnt). NO STATEMENT CHANGE.
   - caw_pre IS READ BY NAME: the positional destruct (it would now mis-bind: ck_frm0 moved by four) is replaced by the
     base's projections caw_pre_fpre .. caw_pre_frm0, under the same hypothesis names.
   - THE OUTCOME (:879-888): cut_end's r = 1 arm carries caw_dead C, proved at the NULL arm. At an entry position i
     under the run hypothesis (the scratch pair caw_evs C, the consumer window prh_cons_from .. i 2), cut_mal's
     caw_prog C [] S3 on the empty run puts the run at position i at S3, the malloc's OWN input state; the malloc
     post's granted NULL path (apath (malloc_cf (size + 1) tr S3) trc (PNull, S2) with gflag trc = true) is the left
     disjunct of PRH_Refute.prh_granted_null S3; Wf_cf (as_universe B) S3 is the call's ARx (ARx_wf_law_xs, the Wf law
     the malloc rule is given); PRH_Refute.prh_refute_at (k = 2, e = HMal (size + 1), the run's event at i by
     caw_run_at_nth) refutes it. PRH_Refute Requires PresetCfnA / ZImage: this file builds on the pins102 route only.
   EARLIER (the f97c re-key, vs the decff-era Qed file proved on Caw102B.v e05942cc29e1): f97c's tcheck_as_written_specX
   binds no run position at entry and states the position in the post-implication form, so the base dropped
   caw_room_evs / caw_room_pos / caw_rpos and cawB's position fields, and each cut carries the progress fact
   caw_prog C E S for the events E made since entry.
   - THE STATEMENT: caw_WB1 lost `caw_room_pos C ->` and took `caw_cnt C ->` right after `caw_pre (fx := fx) B C ->`.
   - THE ROOM COUNTS: RL_malloc_step needs rl_sec_ok / rl_b24_ok at the call state S3; the decff file read them off the
     run position (Caw102B_Rl.caw_rl_ok; Caw102B_Rl leaves the Require closure). Now: cut_mal's ablocks B ly3 S3 =
     ablocks B (c_ly C) (c_S C) keeps every request size (map snd (blocks _)), so sec_cnt / ccnt24 at S3 are the
     entry's (w1_cnt_keep), and caw_cnt C bounds those by LSEC + DRV / L24 + DRV; the parameter conjuncts are closed
     facts at CfParams_preset (w1_counts, vm_compute on closed goals; the A' WA0's wa0_counts).
   - THE PROGRESS FACT: from cut_mal's caw_prog C [] S3 at any entry position i (the empty run): the NULL arm's
     caw_prog C [] S2 by room_pos_keep_alloc_null (position i + 0); cut_ev's caw_prog C (caw_ev1 C) S2 by
     room_pos_keep_alloc with the event HMal (size + 1) read off the run by caw_run_at_nth (i + 1 = S i).
   - FRM0-ENTRY: fpre's destruct names its new last conjunct; this segment builds no callee fpre (the malloc is the
     journal rule aj_malloc_x_ct_m), and caw_base's frm_zero at both exits is cut_mal's (float state fx).
   INPUTS, BY PATH (blobs as the kit's cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) carries them): this row's lib/B/Prog/Caw102B.v, statements of blob
   5a8082469eb1; the call rule lib/Reusable/YGcallMxmnKeep.v (aj_malloc_x_ct_m_keep over amalloc_realizes_x_xs_keep:
   YGcallMxmn.aj_malloc_x_ct_m, YGcallx.aj_malloc_x_ct verbatim, plus the memnorm keep); lib/Reusable/YGcallcf.v 8645fa6a514f (amalloc_realizes_x_xs, QM_cf_of_room,
   alloc_model_laws_x_cf, ARx_wf_law_xs, the ARcfx laws); lib/Reusable/YG01.v 845507e218b0 (admits_fix);
   lib/Reusable/YCbqG.v 219748197d6b (the journal's ajx_ projections, ajournal_xw_fix1); lib/Reusable/YGcfRoomLive.v
   edc1017de99c (sec_cnt, ccnt24, rl_sec_ok, rl_b24_ok, RL_malloc_step); lib/Spec/PresetLiveBounds.v f78da450d5f6
   (LSEC, L24, DRV); lib/Spec/PresetRoomPos.v 943d62290e8e (iface_room_pos); lib/Spec/PresetRoomPosKeep.v dc3f6bee1e0e
   (room_pos_keep_alloc / room_pos_keep_alloc_null); lib/A/PRH_Refute.v 23f7a37f01c9 (prh_granted_null, prh_refute_at);
   lib/Spec/PresetSite17.v 74734062f6b7 (is_alloc); lib/A/Prog/S1Ledger.v 8cf15eeb6311 (prh_ledger_kept_aview,
   prh_lblocks_kept, prh_blocks_bytes_ablocks); lib/A/PRH_Base.v ef7c8ca98529 (prh_pst, prh_glob / prh_ledger with most
   and own, prh_own, prh_most, the ledger's named projections, fpre with frm_zero, prh_run_at, prh_cons_from,
   prh_univ_closure); lib/B/PRH_ImgB.v 3216eca68342; the listing lib/B/Listing_prog.v c97cc46b3e13
   (the pins102 listing, the same as blob 8bcc2c9e7809 but its header); the engine
   YC1fPx.v 7814b594066f (paj_run_x_inv, paj_run_to_x_inv, paj_run_to_x_m_inv), YC80x.v 14f84f225e8f; YSRrMemnorm.v
   5ffa8525936b (srr_inv_call); PRW_StepKit.v 0df3991c13f4 (pa_slot_lt_ceil_b, st_ok_region_nth, field_of_region);
   YG0dcf.v 63c0f054c76a (amalloc_realizes_cf).
   FORM: generic P, abstract (srr_inv_laws for the runs, srr_inv_call across the malloc); PARAMETRIC over
   {PA : PAImg B_prog_listing}; the allocator relation ARcfx; YM05.alloc_ceiling by name; no positional destruct of
   AR_laws_x (its fields by name: alx_blocks, alx_img, alx_layout_ok, blk_img_x, sep_blocks_x).
   THE PROOF: seat 1 at cut_mal (atom 2 = the entry sp, sp the term SOff 2 (-80), Caw102B_WB3.v's seat at B); the jal
   by paj_run_tok_x_inv; the call by aj_malloc_x_ct_m_keep at QMm_cf (QM_cf_of_room from qtight, room_live_cf and the
   hull budget; arodata_ok_cf through the relro rows, STEP-2 RE-FIT above), the
   blocks bound from caw_pre's LIVE_check_as_written, the trace at the generated return site pi_ret_caw_malloc, the
   empty chain by caw_chain; P across the call by srr_inv_call. The room after the call by RL_malloc_step with its
   live-set premises from caw_cnt (w1_counts, above); the progress fact by room_pos_keep_alloc / room_pos_keep_alloc_null
   (above). The ledger (cut_mal's, own 0) across the call by prh_ledger_kept_aview (its statics, g_most and
   g_own_ran_out among them, are image bytes off the owned statics and errno; the heads lie in entry blocks, apart from
   the new block by sep_blocks_x). At the return site:
     - a0 <> 0: the branch (psrr_branch_tok), its taken side refuted by a0 = res >= 4096; cut_ev with scr = res and
       caw_prog at caw_ev1, the ledger unchanged (own 0; the run is read-only);
     - a0 = 0: a seat with a0 pinned to 0, the static's one-byte writable region at A_OBJ 13 (its atom fact the
       generated address) and the listing's alias row (SOff (A_HI 10) (-624), SOff (A_OBJ 13) 0); the run to cut_end by
       the mixed-write runner paj_run_to_x_m_inv (the byte is a prh_pst byte); g_own_ran_out = 1 read off the run's
       final region (chunk CVal 1 (SLit 1), the `sb`) by PRW_StepKit.field_of_region; the ledger at own 1 by
       w1_ledger_own (the five statics' cells, g_most's (w1_most_off_own) and the heads lie off the one byte); cut_end's
       left arm with caw_prog at [] and caw_dead C (PRH_Refute.prh_refute_at at the malloc's input state S3, above).
   Section hypotheses (callee text and image facts, each discharged at PI_prog_B or by its owner; the report lists
   them): AMALLOC (the malloc wrapper's runtime row with the memnorm keep, amalloc_realizes_cf_keep), PAL (the unit's
   image binding of B; owner a Theorem Labs lane), Hpst, Hpst_img (as Caw102B_WB3.v), Hpst_wr (S1ImgB.pst_writable_B), Hmal (the
   generated return site), Hown_obj (as Caw102B_WB4.v), Hown_hi (the listing's alias row, PAImg_prog.v's
   B_alias_hints_ok), Hpst_rw and Hrelro_seg / Herrno_relro / Hrelro_top / Hrelro_eq / Hro_reads_nw (as Caw102B_WB2.v;
   lib/AU/CfAroPresetB.v) (image facts: owner the instantiation at PI_prog_B, Caw102B_Img.v). The room counts are
   caw_cnt C, a premise of caw_WB1 that the top discharges from caw_pre (caw_pre_cnt).
   Numerals: 72 (DERIVED: the malloc's return site, 4 * the slot inside the function, CAWB_RET), 2292 (DERIVED:
   AF_cawB + 72 as the engine prints it), 80 (LENGTH: the frame), 8 / 16 / 24 / 32 / 56 / 64 / 72 (LENGTH: the frame's
   words off the entry sp, Caw102B.v), 16 (DERIVED: cf_head), -624 / 10 / 13 (DERIVED: the listing's alias row: the
   store's offset, the auipc's hi index, g_own_ran_out's object index), 1 (LENGTH: the static's width; WORD: the stored
   value), 26800 / 16384 (DERIVED by computation: STK_check_as_written, ASTACK), 32 (DERIVED: the engine's atom
   numbering), 2 ^ 31 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (WORD / LENGTH bounds), register numbers (WORD). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
(* the keep-carrying malloc rule and its contract (part 3c took the memnorm keep out of the plain rule's post) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Caw102B.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Refute.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the malloc's return site (B' 0x81fc0, `beqz a0`): DERIVED, 4 * the slot inside the function *)
Definition CAWB_RET : Z := 72.

(* ---- seat 1 (cut_mal): the entry sp as atom 2, sp the term SOff 2 (-80) (Caw102B_WB3.v's w3_sr80 / w3_facts) ---- *)
Definition w1_sr80 : list sv := sr_set sr_atoms 2%bv (SOff 2 (- CAWB_FRAME)).
Definition w1_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
(* the registers seat 1's run (the jal) leaves at their seat values: all but ra and sp *)
Definition w1_kl : list (bv 5) := [3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* ---- the NULL arm's seat: g_own_ran_out (A_OBJ 13), one byte, writable, no chunk; its value the generated address
   (the engine's shadow-safety check sh_static_ok bounds a writable window by its base atom's fact); the listing's alias
   row of the store's auipc base (Listing_prog.v c97cc46b3e13, B_alias_hints: (SOff (A_HI 10) (-624), SOff (A_OBJ 13) 0))
   ---- *)
Definition w1_own_rg : YP09.region := YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 1 [].
Definition w1_own_facts : facts :=
  mkFacts [(A_OBJ 13, mkAF (@pi_g_own_ran_out prh_img_B) (@pi_g_own_ran_out prh_img_B) 0)] []
    [(SOff (A_HI 10) (-624), SOff (A_OBJ 13) 0)].
(* the registers the return-site runs never write before their exits (sp, gp, tp, s0, s2 .. s11) *)
Definition w1_kept : list (bv 5) := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition w1_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Section bld. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGSz := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VALz := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation BASEz := (@pa_val _ B_prog_listing PA A_TEXT).

Definition w1_E (regs : bvmap 5 word) (sp0 : Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) [Z_to_bv 64 SHADOW_OFF]).
Lemma w1_getr_upd_other : forall regs (r r' : bv 5) w, r' <> r -> getr (regupd regs r w) r' = getr regs r'.
Proof.
intros regs r r' w Hne. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other by (intros Heq; apply Hne; symmetry; exact Heq). reflexivity.
Qed.
Lemma w1_getr_upd_same : forall regs (r : bv 5) w, bv_eqb r 0 = false -> getr (regupd regs r w) r = w.
Proof. intros regs r w H. unfold getr, regupd. rewrite H. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma w1_E_reg : forall regs sp0 n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv ->
  ew (w1_E regs sp0) n = getr regs r.
Proof.
intros regs sp0 n r Hn Hr. pose proof (u5_range r) as Hu. unfold w1_E.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat _ _ n r Hn).
apply w1_getr_upd_other. exact Hr.
Qed.
Lemma w1_E_sp : forall regs sp0, ew (w1_E regs sp0) 2 = Z_to_bv 64 sp0.
Proof.
intros regs sp0. unfold w1_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl). apply w1_getr_upd_same. reflexivity.
Qed.
Lemma w1_regs_ok : forall regs sp0, spZ regs = sp0 - CAWB_FRAME -> CAWB_FRAME <= sp0 < 2 ^ 64 ->
  regs_ok (w1_E regs sp0) w1_sr80 regs.
Proof.
intros regs sp0 Hsp Hsp0 r'.
pose proof (regs_ok_Eimg_Ereg (L := B_prog_listing) (PI := PA) (regupd regs 2%bv (Z_to_bv 64 sp0))
  [Z_to_bv 64 SHADOW_OFF] r') as H.
fold (w1_E regs sp0) in H.
unfold w1_sr80, sr_set. change (bv_eqb 2%bv 0%bv) with false. cbv iota.
unfold getr, regupd, sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact H|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx 2%bv)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'.
  cbn [sv_denot]. rewrite w1_E_sp. unfold spZ in Hsp. unfold CAWB_FRAME in *.
  rewrite unsigned_lit_small by lia.
  unfold getr in Hsp. change (bv_eqb 2%bv 0%bv) with false in Hsp. cbv iota in Hsp.
  apply bv_eq. rewrite unsigned_lit_small by lia. lia.
- apply Nat.eqb_neq in Hi.
  unfold reg_get in *. rewrite bvmap_get_set_other in H by (intros Heq; apply Hi; rewrite Heq; reflexivity).
  exact H.
Qed.
Lemma w1_st_ok : forall (W : world SEGSz) regs mem pc sp0,
  spZ regs = sp0 - CAWB_FRAME -> 2 ^ 46 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  st_ok_pi SEGSz VALz (w1_E regs sp0) (mkSS pc w1_sr80 [] None w1_facts)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASEz + pc)) mem (YK11.seg_rom SEGSz))).
Proof.
intros W regs mem pc sp0 Hsp Hr Ha.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply w1_regs_ok; [exact Hsp | unfold CAWB_FRAME; lia].
- reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. exact I.
- unfold facts_ok, w1_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite w1_E_sp, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia.
Qed.
Lemma w1_E_agree : forall regs sp0,
  env_agree 32 (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) [Z_to_bv 64 SHADOW_OFF]) (w1_E regs sp0).
Proof. intros regs sp0. unfold w1_E. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma w1_regs_kept : forall E ss (ms : machine_state) regs sp0,
  st_ok SEGSz E ss ms -> E = w1_E regs sp0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) w1_kl = true ->
  forall r, In r w1_kl -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms regs sp0 HS -> Hl r Hr.
rewrite (regs_kept_of_st_ok SEGSz _ ss ms (regupd regs 2%bv (Z_to_bv 64 sp0)) _ w1_kl HS (w1_E_agree regs sp0) Hl r Hr).
apply w1_getr_upd_other. intros ->. cbn [In w1_kl] in Hr.
repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr.
Qed.
End bld.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation STK := (STK_check_as_written (PI := prh_img_B)).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the room counts RL_malloc_step asks at the call state, from caw_cnt (the top's caw_pre_cnt) ---- *)
(* sec_cnt and ccnt24 read only the request sizes, map snd (blocks _), which ablocks keeps: equal blocks, equal counts *)
Lemma w1_cnt_keep : forall (B : asyms) ly S ly' S', ablocks B ly' S' = ablocks B ly S ->
  YGcfRoomLive.sec_cnt S' = YGcfRoomLive.sec_cnt S /\ YGcfRoomLive.ccnt24 S' = YGcfRoomLive.ccnt24 S.
Proof.
intros B ly S ly' S' E. apply (f_equal (map snd)) in E. unfold ablocks in E. rewrite !map_map in E.
change (map snd (blocks S') = map snd (blocks S)) in E.
unfold YGcfRoomLive.sec_cnt, YGcfRoomLive.ccnt24. rewrite E. split; reflexivity.
Qed.
(* RL_malloc_step's live-set premises at the bounds caw_cnt states; the parameter conjuncts are closed facts at
   CfParams_preset (the A' WA0's wa0_counts) *)
Lemma w1_counts : forall S,
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  YGcfRoomLive.rl_sec_ok (cp := CfParams_preset) (PresetLiveBounds.LSEC + PresetLiveBounds.DRV) S /\
  YGcfRoomLive.rl_b24_ok (PresetLiveBounds.L24 + PresetLiveBounds.DRV) S.
Proof.
intros S C1 C2. split; split;
  [exact C1 | apply Z.ltb_lt; vm_compute; reflexivity | exact C2 | apply Z.leb_le; vm_compute; reflexivity].
Qed.

(* ---- the return-site seats: every register its own atom, atom 32 the shadow base (Caw102B_WB4.v's cawO_E0) ---- *)
Definition w1_E0 (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Lemma w1_E0_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (w1_E0 regs) n = getr regs r.
Proof.
intros regs n r Hn. pose proof (u5_range r) as Hu. unfold w1_E0.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma w1_E0_agree : forall regs, env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) (w1_E0 regs).
Proof. intros regs. unfold w1_E0. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* no region (the a0 <> 0 arm) *)
Lemma w1_seat0 : forall (W : world SEGS) regs mem pc,
  st_ok_pi SEGS VAL (w1_E0 regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold w1_E0. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- split; [exact I | split; exact I].
Qed.
(* the static's writable byte and the alias row (the a0 = 0 arm) *)
Lemma w1_seat_own : forall (W : world SEGS) regs mem pc,
  writable_at SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 13)) -> VAL (A_OBJ 13) = pi_g_own_ran_out ->
  VAL (A_HI 10) + (-624) = VAL (A_OBJ 13) ->
  st_ok_pi SEGS VAL (w1_E0 regs) (mkSS pc sr_atoms [w1_own_rg] None w1_own_facts)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros W regs mem pc Hw Hown Hal. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold w1_E0. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, w1_own_rg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  pose proof (@pa_val_range _ _ PA (A_OBJ 13)) as HR.
  assert (Hb : base_val (w1_E0 regs) (Some (A_OBJ 13)) = VAL (A_OBJ 13)).
  { cbn [base_val]. unfold w1_E0. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    apply unsigned_lit_small. exact HR. }
  rewrite Hb. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. replace (VAL (A_OBJ 13) + o) with (VAL (A_OBJ 13)) by lia. exact Hw.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- unfold facts_ok, w1_own_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I|]].
  + split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. unfold w1_E0.
    rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite unsigned_lit_small by (apply pa_val_range). rewrite Hown.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  + split; [|exact I].
    cbn [sv_denot]. unfold w1_E0.
    rewrite !Eimg_img by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
    rewrite !unsigned_lit_small by (apply pa_val_range).
    rewrite Hal, Z.add_0_r. reflexivity.
Qed.

(* a stretch whose write windows lie inside [lo, hi) keeps every view outside it (Caw102B_WB0.v caw_keep_out) *)
Lemma w1_keep_out : forall E' rs (Wx : world SEGS) m m' lo hi,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  (forall a, in_wrange E' rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros E' rs Wx m m' lo hi HF Hw a Ha Hn.
unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros Hin. apply Hn. exact (Hw a Hin).
Qed.

(* a callee-saved register across a call (Caw102B_WB3.v w3_pres_r) *)
Lemma w1_pres_r : forall regs regs' (r : bv 5), aregs_preserved regs regs' ->
  In (bv_unsigned r) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr regs' r = getr regs r.
Proof.
intros regs regs' r H Hr. assert (Hc : acallee_saved (bv_unsigned r)) by (unfold acallee_saved; cbn [In] in Hr; lia).
pose proof (H _ Hc) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

Section f.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Abbreviation LEDGER := (prh_ledger B).
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.

(* ---- Section hypotheses: the callee text and the image facts this segment uses ---- *)
(* callee text: the malloc wrapper's runtime row with the memnorm keep at the leaf (YGcfMallocComposeKeep.v), at every
   float state *)
Hypothesis AMALLOC : forall fz, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fz) SEGS B.
(* image facts, discharged at PI_prog_B: the unit's image binding of B (pal_malloc, pal_env); alloc.c's and the
   harness's statics are image bytes, off the owned statics and errno, writable (S1ImgB.v pst_in_img_B / pst_writable_B
   at PI_prog_B; Hpst as Caw102B_WB3.v); the malloc's return site is the generated pi_ret_caw_malloc (B' 0x81fc0);
   13 = g_own_ran_out in listing d42e123915ae (as Caw102B_WB4.v); the store's auipc base is the listing's alias row
   (SOff (A_HI 10) (-624), SOff (A_OBJ 13) 0) of B_alias_hints (PAImg_prog.v B_alias_hints_ok) *)
Hypothesis PAL : PALib B.
Hypothesis Hpst : forall a, Exists (in_zr a) prh_pst ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis Hpst_img : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
Hypothesis Hpst_wr : forall (m : word -> option byte) a, Exists (in_zr a) prh_pst -> writable_at SEGS m a.
Hypothesis Hmal : BASE + (AF_cawB + CAWB_RET) = pi_ret_caw_malloc.
Hypothesis Hown_obj : VAL (A_OBJ 13) = pi_g_own_ran_out.
Hypothesis Hown_hi : VAL (A_HI 10) + (-624) = VAL (A_OBJ 13).
(* alloc.c's statics are not read-only image bytes: arodata_okP crosses the journal to the malloc's call memory *)
Hypothesis Hpst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.
(* the cf layer's relro rows at the image (what arodata_ok_cf, the malloc's call memory premise, asks) *)
Hypothesis Hrelro_seg : YG0ncf.relro_seg_t SEGS.
Hypothesis Herrno_relro : YG0ncf.errno_relro_t B.
Hypothesis Hrelro_top : cf_relro_hi <= 2 ^ 64.
Hypothesis Hrelro_eq : cf_relro_lo = @pa_relro_lo _ _ PA /\ cf_relro_hi = @pa_relro_hi _ _ PA.
Hypothesis Hro_reads_nw : YGcfAroBridge.ro_reads_nw_t SEGS.

Lemma w1_pst_ok : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Proof. intros a Ha. exact (conj (Hpst_img a Ha) (proj1 (Hpst a Ha))). Qed.

(* g_own_ran_out's byte is a prh_pst byte (PRH_Base.v's Batch-1 row, the seventh) *)
Lemma w1_own_pst : forall a, pi_g_own_ran_out <= a < pi_g_own_ran_out + 1 -> Exists (in_zr a) prh_pst.
Proof.
intros a Ha. unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
assert (E1 : Z.of_nat pi_gz_own_ran_out = 1) by (vm_compute; reflexivity). rewrite E1. exact Ha.
Qed.

(* g_most's cells are prh_pst bytes (PRH_Base.v's Batch-1 row, the sixth) *)
Lemma w1_most_pst : forall k, 0 <= k < Z.of_nat pi_gz_most -> Exists (in_zr (pi_g_most + k)) prh_pst.
Proof.
intros k Hk. unfold prh_pst. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* g_most's cells lie off g_own_ran_out's byte (prh_img_B's generated addresses, by computation) *)
Lemma w1_most_off_own : forall k, 0 <= k < Z.of_nat pi_gz_most ->
  ~ (pi_g_own_ran_out <= pi_g_most + k < pi_g_own_ran_out + 1).
Proof.
intros k Hk.
lazymatch eval vm_compute in pi_g_own_ran_out with ?v => assert (Eo : pi_g_own_ran_out = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in pi_g_most with ?v => assert (Em : pi_g_most = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in (Z.of_nat pi_gz_most) with ?v =>
  assert (Wm : Z.of_nat pi_gz_most = v) by (vm_compute; reflexivity) end.
rewrite Eo, Em. rewrite Wm in Hk. lia.
Qed.

(* a listing slot's pc is at or above kImgLo (Caw102B_WB4.v cawO_text_lo) *)
Lemma w1_text_lo : forall ly S Hp (W : world SEGS) mem md k, ARcfx ly S Hp W mem md -> 0 <= k < 2 ^ 40 ->
  match plookup (@pl_tpi _ PL_caw_B) k with Some _ => true | None => false end = true ->
  kImgLo <= BASE + k.
Proof.
intros ly S Hp W mem md k HAR Hk40 Hk.
destruct (plookup (@pl_tpi _ PL_caw_B) k) as [e|] eqn:He; [|discriminate Hk].
pose proof (@pa_B_ok _ _ PA) as HB. rewrite <- (@pl_tpi_eq _ PL_caw_B) in He.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma B_prog_listing pa_cert k e He) as [Hc _].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs;
  [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & _).
rewrite unsigned_lit_small in Hlo by lia.
destruct (alx_img SEGS B ARcfx LAWS ly S Hp W mem md HAR) as [Hsg _].
destruct (Hsg sg Hin) as [Hsg1 _].
destruct (lo_img ly (alx_layout_ok SEGS B ARcfx LAWS ly S Hp W mem md HAR)) as [Hi _].
lia.
Qed.

(* the malloc's trace: the empty chain's (s0 = rc), pc0-filtered, at the generated return site (Caw102B_WB3.v
   w3_trace's form) *)
Lemma w1_trace : forall CTX0 ly (regs : bvmap 5 word), prh_univ_closure B CTX0 ->
  raZ regs = pi_ret_caw_malloc -> In (call_trace ly (pc_malloc_ra0 (as_code B)) regs []) (as_universe B).
Proof.
intros CTX0 ly regs (H1 & H2 & _) Hra. unfold call_trace.
destruct (frame0_ok ly regs); [|exact (H1 RT_malloc)].
assert (Hr : In (raZ regs) (pi_ret_sites F_check_as_written RT_malloc)).
{ rewrite Hra. unfold pi_ret_caw_malloc. vm_compute. left. reflexivity. }
pose proof (H2 F_check_as_written RT_malloc (raZ regs) Hr) as H.
unfold prh_trace in H. unfold unwind_of_chain. cbn [flat_map prh_pc0] in H |- *. exact H.
Qed.

(* the ledger across a store to g_own_ran_out's one byte, at the byte's new value own': the five statics' cells and
   g_most's lie off it (prh_img_B's generated addresses, by computation) and so do the heads (they lie in allocator
   blocks, which hold no image byte, and the byte is an image byte) *)
Lemma w1_ledger_own : forall ly S Hp (W : world SEGS) mem md mem' Lam peak cnt fail ran most own own',
  ARcfx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pi_g_own_ran_out <= a < pi_g_own_ran_out + 1) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prh_own W mem' own' ->
  LEDGER ly S Hp W mem' Lam peak cnt fail ran most own'.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own own' HAR HL HK HO.
assert (Himg : in_img SEGS pi_g_own_ran_out) by (apply Hpst_img; apply w1_own_pst; lia).
pose proof (@pa_segs_low _ _ PA _ Himg) as Hlow.
(* the statics' cells, computed *)
lazymatch eval vm_compute in pi_g_own_ran_out with ?v => assert (Eo : pi_g_own_ran_out = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in pi_g_live with ?v => assert (El : pi_g_live = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in pi_g_peak with ?v => assert (Ep : pi_g_peak = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in pi_g_count with ?v => assert (Ec : pi_g_count = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in pi_g_fail with ?v => assert (Ef : pi_g_fail = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in pi_g_ran_out with ?v => assert (Er : pi_g_ran_out = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in (Z.of_nat pi_gz_live) with ?v => assert (Wl : Z.of_nat pi_gz_live = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in (Z.of_nat pi_gz_peak) with ?v => assert (Wp : Z.of_nat pi_gz_peak = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in (Z.of_nat pi_gz_count) with ?v => assert (Wc : Z.of_nat pi_gz_count = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in (Z.of_nat pi_gz_fail) with ?v => assert (Wf : Z.of_nat pi_gz_fail = v) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in (Z.of_nat pi_gz_ran_out) with ?v => assert (Wr : Z.of_nat pi_gz_ran_out = v) by (vm_compute; reflexivity) end.
(* the heads: each lies in an allocator block, which holds no image byte *)
assert (Hhd : forall a kk i, In (a, kk) Lam -> 0 <= i < 8 ->
  mbyte SEGS (mrestrict (w_H W) mem') (a - cf_head + i) = mbyte SEGS (mrestrict (w_H W) mem) (a - cf_head + i)).
{ intros a kk i Hin Hi. apply (mbyte_of_aview SEGS).
  destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a kk HL Hin) as (Hk0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in *.
  destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4096 & Hcb & _).
  rewrite caw_req in Hcb by lia.
  pose proof asan_consts as (C1 & _).
  apply HK; [lia|]. intros Ho.
  apply (blk_img_x SEGS B ARcfx LAWS ly S Hp W mem md (a - 16) (kk + 16) (a - 16 + i) HAR Hab);
    [rewrite caw_req by lia; lia|].
  replace (a - 16 + i) with pi_g_own_ran_out by lia. exact Himg. }
split.
- (* the statics: prh_glob at own' *)
  unfold prh_glob.
  split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem');
    [intros kk Hkk; apply HK; rewrite ?Wl, ?El, ?Eo in *; lia
    | exact (prh_ledger_live B ly S Hp W mem Lam peak cnt fail ran most own HL)]|].
  split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem');
    [intros kk Hkk; apply HK; rewrite ?Wp, ?Ep, ?Eo in *; lia
    | exact (prh_ledger_peak B ly S Hp W mem Lam peak cnt fail ran most own HL)]|].
  split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem');
    [intros kk Hkk; apply HK; rewrite ?Wc, ?Ec, ?Eo in *; lia
    | exact (prh_ledger_count B ly S Hp W mem Lam peak cnt fail ran most own HL)]|].
  split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem');
    [intros kk Hkk; apply HK; rewrite ?Wf, ?Ef, ?Eo in *; lia
    | exact (prh_ledger_fail B ly S Hp W mem Lam peak cnt fail ran most own HL)]|].
  split; [apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem');
    [intros kk Hkk; apply HK; rewrite ?Wr, ?Er, ?Eo in *; lia
    | exact (prh_ledger_ran B ly S Hp W mem Lam peak cnt fail ran most own HL)]|].
  split.
  { destruct (prh_ledger_most B ly S Hp W mem Lam peak cnt fail ran most own HL) as (Vm & Rm). split; [|exact Rm].
    apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact Vm].
    intros kk Hkk. pose proof (w1_most_pst kk Hkk) as Hq.
    pose proof (@pa_segs_low _ _ PA _ (Hpst_img _ Hq)) as Hlq. unfold kLowMemEnd in Hlq.
    apply HK; [lia | exact (w1_most_off_own kk Hkk)]. }
  split; [exact HO|].
  exact (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HL).
- (* the harness blocks: unchanged but their heads, which the store does not touch *)
  exact (S1Ledger.prh_lblocks_kept B ly S Hp W mem ly S Hp W mem' Lam (proj2 HL) Hhd (fun a k _ H => H)
    (Permutation_refl Hp)).
Qed.

(* WB1 (0x81fbc, cut_mal): the malloc of the scratch and its return-site branch; the NULL arm stores 1 to
   g_own_ran_out and goes to the epilogue with r = 1 and the OUTCOME's exclusion caw_dead C. The room counts at entry
   are caw_cnt C (after caw_pre; the top supplies caw_pre_cnt) *)
Lemma caw_WB1 : forall C P Q, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  caw_pre (fx := fx) B C -> caw_cnt C -> caw_K_ev (fx := fx) B C P Q -> caw_K_end (fx := fx) B C P Q ->
  caw_K_mal (fx := fx) B C P Q.
Proof.
intros C P Q PLAW PCALL Hpre HCNT KEV KEND ly3 S3 Hp3 W3 regs3 mem3 md3 k Hcut HPM.
destruct Hcut as ((Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM) & R9 & R18 & R10 & (Vp & Vend) & Vdep &
  Eab & Efr & Hpos & HL & HHB).
(* caw_pre read BY NAME (the base's projections), never positionally *)
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as (HPRE & HROD & HTOP & HRAZ & HFRM0).
pose proof (caw_pre_mn (fx := fx) B C Hpre) as HMN. pose proof (caw_pre_univ (fx := fx) B C Hpre) as HUNIV.
pose proof (caw_pre_r10 (fx := fx) B C Hpre) as H10. pose proof (caw_pre_r11 (fx := fx) B C Hpre) as H11.
pose proof (caw_pre_r12 (fx := fx) B C Hpre) as H12. pose proof (caw_pre_r13 (fx := fx) B C Hpre) as H13.
pose proof (caw_pre_rc (fx := fx) B C Hpre) as Hrc. pose proof (caw_pre_doc (fx := fx) B C Hpre) as Hdoc.
pose proof (caw_pre_size (fx := fx) B C Hpre) as Hsz. pose proof (caw_pre_data0 (fx := fx) B C Hpre) as Hd0.
pose proof (caw_pre_data62 (fx := fx) B C Hpre) as Hd62. pose proof (caw_pre_src (fx := fx) B C Hpre) as HSRC.
pose proof (caw_pre_inblk (fx := fx) B C Hpre) as HINB. pose proof (caw_pre_case (fx := fx) B C Hpre) as HCASE.
pose proof (caw_pre_tree (fx := fx) B C Hpre) as HTREE. pose proof (caw_pre_ledger (fx := fx) B C Hpre) as HL0.
pose proof (caw_pre_ran (fx := fx) B C Hpre) as Hran. pose proof (caw_pre_live (fx := fx) B C Hpre) as HMAX.
pose proof (caw_pre_max (fx := fx) B C Hpre) as HMAL. pose proof (caw_pre_frames (fx := fx) B C Hpre) as HFR.
pose proof (caw_pre_room (fx := fx) B C Hpre) as HROOM0. pose proof (caw_pre_frm0 (fx := fx) B C Hpre) as HFRM.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK = 26800) by (vm_compute; reflexivity).
assert (Has : ASTACK = 16384) by reflexivity.
assert (EAF : AF_cawB = 2220) by (vm_compute; reflexivity).
unfold caw_J in HJ. unfold caw_saved in HSV.
unfold c_sp in *. unfold CAWB_FRAME in Hsp.
set (sp0 := spZ (c_regs C)) in *.
assert (Rsp : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
assert (Hsz0 : 0 <= c_size C) by (unfold c_size; lia).
pose proof (@pa_B_ok _ _ PA) as HBok.
(* the journal read BY NAME (YCbqG's ajx_ projections), never positionally *)
pose proof (ajx_ar HJ) as HAR3. pose proof (ajx_ly HJ) as Hly3.
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (ajx_qt HJ) as HQT3.
(* ==== seat 1 at +68 (cut_mal): jal __wrap_malloc ==== *)
assert (HS : st_ok_pi SEGS VAL (w1_E regs3 sp0) (mkSS (AF_cawB + CAWB_MAL) w1_sr80 [] None w1_facts)
  (restrict (w_H W3) (YK11.mkst regs3 (Z_to_bv 64 (BASE + (AF_cawB + CAWB_MAL))) mem3 (YK11.seg_rom SEGS)))).
{ apply w1_st_ok; [unfold CAWB_FRAME; exact Hsp | exact Rsp | exact Hal16]. }
set (E := w1_E regs3 sp0) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold w1_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (RUNTOm := @paj_run_to_x_m_inv fx rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS w1_pst_ok P PLAW).
pose (BR := @paj_branch fx rc B_prog_listing PA).
unfold caw_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM w1_span.
{ intros a (rg & Hin & _). destruct Hin. }
rename ms into ms1.
assert (Emem : ms_mem ms1 = mem3).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hin & _). destruct Hin. }
clear HF HFr HG.
assert (E2 : ew E 2 = Z_to_bv 64 sp0) by (subst E; apply w1_E_sp).
assert (U2 : bv_unsigned (ew E 2) = sp0) by (rewrite E2; apply unsigned_lit_small; lia).
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2.
rewrite U2 in F2.
assert (Hspc : spZ (ms_regs ms1) = sp0 + -80) by (unfold spZ; rewrite F2; apply unsigned_lit_small; lia).
assert (KR1 : forall r, In r w1_kl -> getr (ms_regs ms1) r = getr regs3 r).
{ intros r Hr. lazymatch type of HS with st_ok _ _ ?ss _ =>
    exact (w1_regs_kept E ss (restrict (w_H W3) ms1) regs3 sp0 HS eq_refl ltac:(vm_compute; reflexivity) r Hr) end. }
(* the call's premises *)
pose proof (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HAR)) as HUok.
pose proof (alloc_model_laws_x_cf B HUok) as AMX.
(* the call memory's QMm_cf: the room, cf_hull_ok from cut_mal's hull budget (PresetHullPay.hull_ok_of_budget),
   arodata_ok_cf from the reader form at the call memory (the journal's image clause carries the entry's) through the
   bridge at the relro rows *)
assert (HQM : QMm_cf SEGS B S3 (ms_mem ms1)).
{ destruct (QM_cf_of_room SEGS B _ _ _ _ _ _ (proj1 HAR3) HQT3 (YGcfRoomLive.room_live_room S3 HROOM)
    (PresetHullPay.hull_ok_of_budget _ _ HHB)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 _)))))).
  pose proof Hrelro_eq as [ERL ERH].
  apply (YGcfAroBridge.arodata_ok_cf_of_P SEGS B W3 (ms_mem ms1) Hrelro_seg Herrno_relro Hrelro_top Hro_reads_nw).
  rewrite ERL, ERH. intros a Hro Hn He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro as [(sg & Hin & _ & Hr) | Hr];
        [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]).
  rewrite (ajx_img HJ a Hia Hn He (fun Hx => Hpst_rw a Hx Hro) (fp_spares_closed _ _ sink_closed_nil)).
  exact (HROD a Hro Hn He). }
assert (Hbb : blocks_bytes S3 + (c_size C + 1) <= LIVE_MAX).
{ rewrite (S1Ledger.prh_blocks_bytes_ablocks B ly3 S3), Eab, <- (S1Ledger.prh_blocks_bytes_ablocks B (c_ly C) (c_S C)).
  unfold LIVE_check_as_written in HMAX. lia. }
pose proof (w1_text_lo ly3 S3 Hp3 W3 _ _ (AF_cawB + CAWB_RET) HAR3 ltac:(unfold CAWB_RET; lia)
  ltac:(vm_compute; reflexivity)) as Hlo.
unfold kImgLo in Hlo.
assert (Hra1 : raZ (ms_regs ms1) = BASE + (AF_cawB + CAWB_RET)).
{ unfold raZ. rewrite F1, unsigned_lit_small by (unfold CAWB_RET in *; lia). unfold CAWB_RET. lia. }
(* the malloc's trace is a FIXED one of the universe (P'' set: the call rule asks `admits`, YG01.admits_fix, and its
   post carries the trace in the journal's wild budget, which ajournal_xw_fix1 drops again) *)
assert (HTR : In (call_trace ly3 (pc_malloc_ra0 (as_code B)) (ms_regs ms1) []) (as_universe B)).
{ apply (w1_trace (c_CTX0 C) ly3 (ms_regs ms1) HUNIV). rewrite Hra1. exact Hmal. }
(* ==== the malloc (+68) by the runtime row, with the memnorm keep (YGcallMxmnKeep's aj_malloc_x_ct_m_keep) ==== *)
eapply SRr_bind.
{ eapply (YGcallMxmnKeep.aj_malloc_x_ct_m_keep (fx := fx) (SK := SK) SEGS B prh_pst ARcfx QM_cf (QMm_cf SEGS B)
    malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)) xs_cf LAWS (@pa_segs_low _ _ PA) (pal_env B PAL)
    (ARx_owned_low_law_xs SEGS B LAWS_cf) (ARx_wf_law_xs SEGS B) AMX (QMQ_cf SEGS B) (ARx_xs_law_xs SEGS B)
    (YGcallMxmnKeep.amalloc_realizes_x_xs_keep (fx := fx) SEGS B (AMALLOC fx))
    W3 E _ ms1 STK sp0 [] (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) [] ly3 S3 Hp3 _ k
    (c_size C + 1) (-80) (ew E 2) (Z_to_bv 64 (BASE + 2292)) [] HS (pal_malloc B PAL) eq_refl HJ).
  - rewrite (KR1 10%bv ltac:(cbv [In w1_kl]; right; right; right; right; left; reflexivity)). exact R10.
  - lia.
  - exact Hbb.
  - exact (st_ok_restrict_reg SEGS (w_H W3) E _ ms1 2%bv HS).
  - reflexivity.
  - exact U2.
  - reflexivity.
  - lia.
  - rewrite Has, HSTK. lia.
  - rewrite (KR1 3%bv ltac:(cbv [In w1_kl]; left; reflexivity)), (Hk 3%bv ltac:(left; reflexivity)). exact Hgp.
  - rewrite (KR1 4%bv ltac:(cbv [In w1_kl]; right; left; reflexivity)), (Hk 4%bv ltac:(right; left; reflexivity)). exact Htp.
  - exact F1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - exact HQM.
  - apply (caw_chain _ _ _ (c_rc C)).
    + rewrite Hra1. unfold CAWB_RET in *. lia.
    + rewrite (KR1 8%bv ltac:(cbv [In w1_kl]; right; right; left; reflexivity)). exact R8.
    + exact Hrc.
    + rewrite Hspc. lia.
    + rewrite Etop. lia.
  - exact (admits_fix _ _ _ HUok HTR). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & H10r & Hfr2 & Hpre2 & Hun2 &
  (p & trc & Hpath & Hg & Hleaf & Hpn & Hpa) & Harms & HMN2).
assert (HPM2 : P mem2) by exact (PCALL _ _ HMN2 HPM).
clear HPM HMN2 Hleaf.
(* the hull: the call uses the scratch's malloc (PresetHullBudget.hull_used_of_call, any return value); cut_mal's
   budget of the scratch pair pays it, the free's part is left for cut_ev *)
assert (HHB2 : PresetHullBudget.hull_budget S2 [PresetReqAt.HFr (c_size C + 1)])
  by exact (PresetHullBudget.hull_budget_app S3 S2 [PresetReqAt.HMal (c_size C + 1)]
    [PresetReqAt.HFr (c_size C + 1)] HHB
    (PresetHullBudget.hull_used_of_call _ _ _ _ (YGcfSecsStep.secs_malloc_step _ _ _ _ _ Hpath))).
(* the journal after the call: the fixed trace leaves the budget; then read BY NAME *)
pose proof (ajournal_xw_fix1 HTR HJ2) as HJ2f. clear HJ2. rename HJ2f into HJ2.
pose proof (ajx_ar HJ2) as HAR2. pose proof (ajx_ly HJ2) as Hly2.
pose proof (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ Hpre2) as Hpre2c.
(* the room after the malloc: a8's keep; its live-set premises at the call state S3, whose blocks are the entry's
   (cut_mal), from caw_cnt C (w1_cnt_keep, w1_counts) *)
pose proof (w1_cnt_keep B (c_ly C) (c_S C) ly3 S3 Eab) as (Ksec & K24).
pose proof HCNT as (Hcsec & Hc24).
pose proof (w1_counts S3 ltac:(rewrite Ksec; exact Hcsec) ltac:(rewrite K24; exact Hc24)) as RLOK.
assert (HRL2 : room_live_cf S2).
{ change S2 with (snd (p, S2)).
  exact (YGcfRoomLive.RL_malloc_step SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre2c (proj1 RLOK) (proj2 RLOK) HROOM Hpath). }
(* the callee-saved registers across the call *)
assert (KR2 : forall r, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs3 r).
{ intros r Hr. rewrite (w1_pres_r _ _ r HP2).
  - apply KR1. cbn [In w1_kl] in Hr |- *. tauto.
  - cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; repeat (first [left; reflexivity | right]) |]).
    destruct Hr. }
assert (Hsp2 : spZ regs2 = sp0 - 80).
{ unfold spZ. rewrite (w1_pres_r _ _ 2%bv HP2 ltac:(vm_compute; left; reflexivity)). unfold spZ in Hspc. lia. }
(* the frame above the call's stack window is kept across the call (both arms' acall_kept_x, first clause) *)
assert (KF : forall E0 : Z -> Prop, acall_kept_x SEGS B ly3 S3 W3 (ms_mem ms1) W2 mem2 (sp0 + -80 - ASTACK) (sp0 + -80) E0 ->
  forall a, sp0 - 80 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros E0 (K1 & _) a Ha. rewrite <- Emem. apply K1; [rewrite HSTK in Hslo; lia | lia]. }
rewrite <- Emem in HL. unfold caw_ledger in HL.
destruct Harms as [(Hres0 & Eab2 & Hkept & _ & _) | (Hres4 & Eab2 & Hkept)].
- (* ==== a0 = 0: noted (), g_own_ran_out := 1, r = 1 ==== *)
  subst res.
  assert (Hpn0 : p = PNull) by (apply (proj2 Hpn); reflexivity).
  subst p.
  pose proof (KF _ Hkept) as KF2.
  destruct Hkept as (_ & K2 & K3 & _).
  (* the ledger after the call: nothing it reads moved (its statics, g_most and g_own_ran_out among them, are image
     bytes off the owned statics and errno) *)
  assert (HL2 : LEDGER ly2 S2 Hp3 W2 mem2 (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0).
  { apply (S1Ledger.prh_ledger_kept_aview B ly3 S3 Hp3 W3 (ms_mem ms1) ly2 S2 Hp3 W2 mem2 _ _ _ _ _ _ _ HL).
    - intros a Ha. destruct (Hpst a Ha) as [Ho He]. exact (K3 a (Hpst_img a Ha) Ho He).
    - intros a kk i Hin Hi.
      destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a kk HL Hin) as (Hk0 & Hab & _).
      change (@cf_head CfParams_preset) with 16 in *.
      apply (K2 (a - 16) (kk + 16) i Hab); [rewrite caw_req by lia; lia | cbv beta; tauto].
    - intros a kk _ Hab. rewrite Eab2. exact Hab.
    - apply Permutation_refl. }
  (* the progress fact: no event; cut_mal's position i + 0 at S3, and a NULL malloc keeps it *)
  assert (Hpos2 : caw_prog C [] S2).
  { intros sm x0 os i H0 hist Hp0 Hrun.
    destruct (Hpos sm x0 os i H0 hist Hp0 Hrun) as (hist' & Hp3').
    exists hist'.
    exact (PresetRoomPosKeep.room_pos_keep_alloc_null SEGS B _ _ _ _ _ _ _ _ sm x0 os _ H0 hist' (c_size C + 1) _ trc
      S2 Hpre2c ltac:(clear - Hsz0 HMAL; lia) Hbb HTR Hpath Hp3'). }
  (* THE OUTCOME's exclusion (caw_dead): at an entry position i under the run hypothesis, cut_mal's position on the
     empty run is i at S3, the malloc's own input state, where the granted NULL path is refused by P8
     (PRH_Refute.prh_refute_at: k = 2, the run's event at i is HMal (size + 1), an allocation) *)
  assert (Hdead : caw_dead C).
  { intros sm x0 os i H0 hist Hp0 Hrun Hcons.
    destruct (Hpos sm x0 os i H0 hist Hp0 ltac:(unfold PRH_Base.prh_run_at; reflexivity)) as (hist' & Hp3').
    cbn [length] in Hp3'. rewrite Nat.add_0_r in Hp3'.
    apply (PRH_Refute.prh_refute_at (as_universe B) sm x0 os i 2 (PresetReqAt.HMal (c_size C + 1)) H0 hist' S3
      Hcons (Nat.lt_0_succ 1) (caw_run_at_nth _ _ _ _ _ _ Hrun) eq_refl Hp3' (ARx_wf_law_xs SEGS B _ _ _ _ _ _ HAR3)).
    (* the left disjunct of prh_granted_null S3: the malloc post's path, its NULL, and its gflag *)
    left. do 4 eexists. exact (conj Hpath Hg). }
  (* the seat at the return site +72: a0 pinned to 0, the static's byte, the alias row *)
  assert (Hw : writable_at SEGS (mrestrict (w_H W2) mem2) (VAL (A_OBJ 13))).
  { apply Hpst_wr. apply w1_own_pst. rewrite Hown_obj. lia. }
  pose proof (w1_seat_own W2 regs2 mem2 (AF_cawB + CAWB_RET) Hw Hown_obj Hown_hi) as HS0.
  set (E3 := w1_E0 regs2) in HS0.
  pose proof (st_ok_pi_pin_reg' (L := B_prog_listing) (PI := PA) E3 _ _ 10%bv 0 HS0
    ltac:(cbn [ms_regs restrict YK11.mkst]; rewrite H10r; reflexivity) eq_refl) as HS3.
  clear HS0.
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; unfold w1_E0; apply Eimg_env).
  assert (SHOK3 : sh_ok SEGS (SOff 32 0) [] E3 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
  lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst _ ?raw _ _ |} _ =>
    change raw with (Z_to_bv 64 (BASE + (AF_cawB + CAWB_RET))) end.
  (* beqz a0 taken (a0 = 0), auipc, addi s1, zero, 1, sb s1 -> g_own_ran_out, j; stop at +224 *)
  paj_run_to_tok_x_inv RUNTOm HS3 HJ2 SHOK3 HPM2 w1_span (AF_cawB + CAWB_END).
  { intros a (rg & Hin & Ha). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val w1_own_rg] in Ha.
    rewrite (HEI3 (A_OBJ 13) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Hown_obj in Ha.
    right. apply w1_own_pst. lia. }
  (* the memory: only g_own_ran_out's byte changed *)
  assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ (pi_g_own_ran_out <= a < pi_g_own_ran_out + 1) ->
    aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
  { apply (w1_keep_out _ _ W2 mem2 (ms_mem ms) pi_g_own_ran_out (pi_g_own_ran_out + 1) HFr).
    intros a (rg & Hin & Ha). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val w1_own_rg] in Ha.
    rewrite (HEI3 (A_OBJ 13) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Hown_obj in Ha. lia. }
  clear HF HFr HG.
  assert (Himg : in_img SEGS pi_g_own_ran_out) by (apply Hpst_img; apply w1_own_pst; lia).
  pose proof (@pa_segs_low _ _ PA _ Himg) as Hlow. unfold kLowMemEnd in Hlow.
  (* the ledger's own at +224: the run's region at A_OBJ 13 holds s1 = 1 (the `sb`), so g_own_ran_out holds 1 *)
  pose proof (PRW_StepKit.st_ok_region_nth SEGS _ _ _ 0 _ HS3 eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
  assert (Uo13 : bv_unsigned (ew E3 (A_OBJ 13)) = VAL (A_OBJ 13))
    by exact (HEI3 (A_OBJ 13) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (Vown : val_mem SEGS (rdW W2 (ms_mem ms)) (VAL (A_OBJ 13) + 0) (N.to_nat 1) 1).
  { apply (PRW_StepKit.field_of_region SEGS _ _ (A_OBJ 13) (VAL (A_OBJ 13)) _ _ _ _ _ 0 1 (SLit 1) 1 Hreg).
    - exact Uo13.
    - cbn. left. reflexivity.
    - reflexivity.
    - split; [lia | reflexivity].
    - unfold Z.le. discriminate. }
  assert (HOWN4 : prh_own W2 (ms_mem ms) 1).
  { split; [|right; reflexivity]. rewrite <- Hown_obj. rewrite Z.add_0_r in Vown.
    change (N.to_nat 1) with 1%nat in Vown.
    assert (Egz : pi_gz_own_ran_out = 1%nat) by (vm_compute; reflexivity). rewrite Egz. exact Vown. }
  (* the ledger at +224, own 1: everything else it reads lies off the byte *)
  assert (HL4 : LEDGER ly2 S2 Hp3 W2 (ms_mem ms) (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 1)
    by exact (w1_ledger_own ly2 S2 Hp3 W2 mem2 md2 (ms_mem ms) _ _ _ _ _ _ _ 1 HAR2 HL2 KO HOWN4).
  (* the frame: kept across the call, and off the static's byte *)
  assert (KF4 : forall a, sp0 - 80 <= a < sp0 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. rewrite KO by lia. exact (KF2 a Ha). }
  destruct HSV as (V1 & V2 & V3 & V4).
  lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
    rewrite (st_ok_pi_restrict_mkst (L := B_prog_listing) (PI := PA) (w_H W2) E3 _ msn HS3 eq_refl) end.
  cbn [ss_pc].
  prreg HS3 (9%bv : bv 5) Q9.
  lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
    assert (KN : forall rr, In rr w1_kept -> getr (ms_regs msn) rr = getr regs2 rr)
    by (eapply (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PA) E3 _ (restrict (w_H W2) msn) regs2
        [Z_to_bv 64 SHADOW_OFF]); [exact HS3 | exact (w1_E0_agree regs2) | vm_compute; reflexivity]);
    lazymatch goal with |- context [Z_to_bv 64 (?b + ?pc)] =>
      change (Z_to_bv 64 (b + pc)) with (Z_to_bv 64 (BASE + (AF_cawB + CAWB_END))) end;
    apply (KEND fx ly2 S2 Hp3 W2 (ms_regs msn) (ms_mem msn) _ (k + (st_nev S2 - st_nev S3)) 1 1); [|exact HPM2]
  end.
  unfold cut_end, caw_base, caw_saved, caw_J.
  split; [|split; [|split; [left; split; [reflexivity | split; [reflexivity | split; [exact Hpos2 | exact Hdead]]] |
    split; [rewrite Eab2; exact Eab | exact HL4]]]].
  + split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ2|].
    split; [intros rr Hr; rewrite (KN rr ltac:(unfold w1_kept; cbn [In] in Hr |- *; tauto)),
      (KR2 rr ltac:(cbn [In] in Hr |- *; tauto)); apply Hk; exact Hr|].
    split; [unfold spZ; rewrite (KN 2%bv ltac:(left; reflexivity)); unfold spZ in Hsp2; change (c_sp C) with sp0;
      unfold CAWB_FRAME; lia|].
    split; [rewrite (KN 8%bv ltac:(cbn; tauto)), (KR2 8%bv ltac:(cbn; tauto)); exact R8|].
    split; [change (c_sp C) with sp0;
      split; [|split; [|split]]; (eapply val_mem_kept; [intros kk Hkk; apply KF4; cbn in Hkk; lia | eassumption])|].
    split; [exact EHp | exact HRL2].
  + rewrite Q9. reflexivity.
- (* ==== a0 = res >= 4096: the scratch, beqz not taken, cut_ev ==== *)
  assert (Hpnn : p <> PNull) by (intros E0; apply Hpn in E0; lia).
  assert (Hscr : caw_scr B C ly2 S2 res) by (split; [exact Hres4 | rewrite Eab2, Eab; reflexivity]).
  assert (Hnew : ~ In (res, c_size C + 1) (ablocks B (c_ly C) (c_S C)))
    by exact (caw_scr_new B C ly2 S2 Hp3 W2 mem2 md2 res HAR2 Hscr Hsz0).
  assert (Hres2 : In (res, c_size C + 1) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR2 Hres2) as (_ & Hr4096 & Hrcb & _).
  rewrite caw_req in Hrcb by lia.
  pose proof (KF _ Hkept) as KF2.
  destruct Hkept as (_ & K2 & K3 & _).
  (* the ledger after the call: the heads lie in entry blocks, apart from the new block *)
  assert (HL2 : LEDGER ly2 S2 Hp3 W2 mem2 (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0).
  { apply (S1Ledger.prh_ledger_kept_aview B ly3 S3 Hp3 W3 (ms_mem ms1) ly2 S2 Hp3 W2 mem2 _ _ _ _ _ _ _ HL).
    - intros a Ha. destruct (Hpst a Ha) as [Ho He]. exact (K3 a (Hpst_img a Ha) Ho He).
    - intros a kk i Hin Hi.
      destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a kk HL Hin) as (Hk0 & Hab & _).
      change (@cf_head CfParams_preset) with 16 in *.
      assert (Hab2 : In (a - 16, kk + 16) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; left; exact Hab).
      assert (Ne : (a - 16, kk + 16) <> (res, c_size C + 1)) by (intros X; apply Hnew; rewrite <- Eab, <- X; exact Hab).
      pose proof (sep_blocks_x SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ _ _ HAR2 Hab2 Hres2 Ne) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite !caw_req in D by lia.
      apply (K2 (a - 16) (kk + 16) i Hab); [rewrite caw_req by lia; lia | cbv beta; rewrite caw_req by lia; lia].
    - intros a kk _ Hab. rewrite Eab2. apply in_or_app. left. exact Hab.
    - apply Permutation_refl. }
  (* the progress fact: the event HMal (size + 1) at the entry position i (caw_run_at_nth); cut_mal's position i + 0
     at S3 (the empty run), and the malloc moves it to S i = i + 1 *)
  assert (Hpos2 : caw_prog C (caw_ev1 C) S2).
  { intros sm x0 os i H0 hist Hp0 Hrun.
    destruct (Hpos sm x0 os i H0 hist Hp0 ltac:(unfold PRH_Base.prh_run_at; reflexivity)) as (hist' & Hp3').
    cbn [length] in Hp3'. rewrite Nat.add_0_r in Hp3'.
    exists hist'. unfold caw_ev1. cbn [length]. rewrite Nat.add_1_r.
    exact (PresetRoomPosKeep.room_pos_keep_alloc SEGS B _ _ _ _ _ _ _ _ sm x0 os i H0 hist' (c_size C + 1) _ trc p S2
      Hpre2c ltac:(clear - Hsz0 HMAL; lia) Hbb HTR Hpath Hpnn Hp3' (caw_run_at_nth _ _ _ _ _ _ Hrun)). }
  (* the seat at the return site +72 *)
  pose proof (w1_seat0 W2 regs2 mem2 (AF_cawB + CAWB_RET)) as HS3.
  set (E3 := w1_E0 regs2) in HS3.
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; unfold w1_E0; apply Eimg_env).
  assert (SHOK3 : sh_ok SEGS (SOff 32 0) [] E3 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
  assert (U10 : U E3 (SOff 10 0) = res).
  { apply U_atom; [subst E3; rewrite (w1_E0_reg regs2 10 10%bv eq_refl); exact H10r | lia]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst _ ?raw _ _ |} _ =>
    change raw with (Z_to_bv 64 (BASE + (AF_cawB + CAWB_RET))) end.
  psrr_branch_tok RUN BR HS3 SHOK3 w1_span.
  { (* taken: a0 = 0, but a0 = res >= 4096 *)
    exfalso. rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. lia. }
  (* not taken: to +76 *)
  paj_run_to_tok_x_inv RUNTO HS3 HJ2 SHOK3 HPM2 w1_span (AF_cawB + CAWB_EV).
  { intros a (rg & Hin & _). destruct Hin. }
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM3 end.
  clear HF HFr HG.
  destruct HSV as (V1 & V2 & V3 & V4).
  lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
    rewrite (st_ok_pi_restrict_mkst (L := B_prog_listing) (PI := PA) (w_H W2) E3 _ msn HS3 eq_refl) end.
  cbn [ss_pc].
  lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
    assert (KN : forall rr, In rr (10%bv :: 9%bv :: w1_kept) -> getr (ms_regs msn) rr = getr regs2 rr)
    by (eapply (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PA) E3 _ (restrict (w_H W2) msn) regs2
        [Z_to_bv 64 SHADOW_OFF]); [exact HS3 | exact (w1_E0_agree regs2) | vm_compute; reflexivity]);
    lazymatch goal with |- context [Z_to_bv 64 (?b + ?pc)] =>
      change (Z_to_bv 64 (b + pc)) with (Z_to_bv 64 (BASE + (AF_cawB + CAWB_EV))) end;
    apply (KEV fx ly2 S2 Hp3 W2 (ms_regs msn) (ms_mem msn) _ (k + (st_nev S2 - st_nev S3)) res); [|exact HPM2];
    rewrite EM3 in HJ2 |- *
  end.
  unfold cut_ev, caw_base, caw_saved, caw_J, caw_ex3.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Hscr | split; [rewrite Hfr2; exact Efr | ]]]]]]]].
  + split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ2|].
    split; [intros rr Hr; rewrite (KN rr ltac:(unfold w1_kept; cbn [In] in Hr |- *; tauto)),
      (KR2 rr ltac:(cbn [In] in Hr |- *; tauto)); apply Hk; exact Hr|].
    split; [unfold spZ; rewrite (KN 2%bv ltac:(right; right; left; reflexivity)); unfold spZ in Hsp2;
      change (c_sp C) with sp0; unfold CAWB_FRAME; lia|].
    split; [rewrite (KN 8%bv ltac:(cbn; tauto)), (KR2 8%bv ltac:(cbn; tauto)); exact R8|].
    split; [change (c_sp C) with sp0;
      split; [|split; [|split]]; (eapply val_mem_kept; [intros kk Hkk; apply KF2; cbn in Hkk; lia | eassumption])|].
    split; [exact EHp | exact HRL2].
  + rewrite (KN 9%bv ltac:(right; left; reflexivity)), (KR2 9%bv ltac:(cbn; tauto)). exact R9.
  + rewrite (KN 18%bv ltac:(cbn; tauto)), (KR2 18%bv ltac:(cbn; tauto)). exact R18.
  + rewrite (KN 10%bv ltac:(left; reflexivity)). exact H10r.
  + change (c_sp C) with sp0.
    split; (eapply val_mem_kept; [intros kk Hkk; apply KF2; cbn in Hkk; lia | eassumption]).
  + change (c_sp C) with sp0.
    eapply val_mem_kept; [intros kk Hkk; apply KF2; cbn in Hkk; lia | eassumption].
  + split; [exact Hpos2 | split; [exact HL2 | exact HHB2]].
Qed.

End f.
End d.

Print Assumptions caw_WB1.

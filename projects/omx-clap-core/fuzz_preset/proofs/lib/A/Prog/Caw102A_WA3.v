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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module paths and module names changed; 1294 of its 1360 lines of code are new or changed and 460 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A' (ASan build): SEGMENT WA3 (lane CawA102, h-rw-pre-5,
   prover CawA102WA3; re-proved on the caw_pst base by CawA102R.CawRWA3; re-proved on the Batch-2 ledger base by
   CawA102R.CawDWA3; re-fitted to the f97c re-keyed base by CawA102R.CawGWA3; re-fitted to the batch base by
   CawA102R.KWA3). PROVES caw_wa3_holds : caw_seg_WA3R (fx := fx) B SK CTX0 P (YA0nH.wle' segs YGcfRehidePost.RZ_cf)
   (Caw102A_Base.v), the stretch from the cut CAW_PC_R (+128) to the cut CAW_PC_OOM (+252), at the cf
   instance with cp := CfParams_preset (CawA102 13:5xZ), for an abstract P with srr_inv_laws (PLAW) and srr_inv_call
   (PCALL): the stretch crosses __wrap_free, by the keep-carrying free rule under the re-hide
   (YGcallMxmnKeep.aj_free_x_ct_m_rh_keep, its memnorm keep the last conjunct), so past the free the run is at wle'
   (YC1fPx's R runners, caw_branchR for the branch, the cut caw_at_AR, the continuation caw_k_OOMR); the free's call
   memory QMm_cf from the room, the hull budget caw_at_R carries (PresetHullPay.hull_ok_of_budget) and the cut's
   reader form through YGcfAroBridge.arodata_ok_cf_of_P at caw_img's relro rows.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   BASE OF RECORD (ready for the #102 integration; as at the batch-prep base, lib/A/Prog/Caw102A_Base.v),
   on the kit's cut (lib/A/PRH_FnCheck.v
   c40cf3fdcd2a, tcheck_as_written_specX :832-902; on this tree :1313-1402; lib/A/PRH_Base.v). WHAT CHANGED AND WHY:
   (1) the batch text has no run-word list DW (prh_univ_closure CTX0, PRH_Base.v :1225; prh_univ_closure_lit without
   its DW argument, :1255), so the base's Section variable DW is gone, and with it this file's `Variable DW`: every
   base name and this file's own cuts (caw_at_A, caw_at_C, caw_at_LX, caw_at_L) drop the DW argument;
   (2) the room counts are the text's entry premises (PRH_FnCheck.v:1343-1344), caw_pre's 23rd / 24th conjuncts, so (with the hull
   budget and HPOS after them) ck_frm0 moved by four, 23rd to 27th: every positional destruct of caw_pre in this file is
   now its NAMED projection (caw_pre_fpre, caw_pre_univ, caw_pre_rc, caw_pre_size, caw_pre_data0, caw_pre_data62,
   caw_pre_ledger); caw_carry still carries caw_cnt D (the top supplies it by caw_pre_cnt), which the free's RL_free_step reads;
   (3) the text's new OUTCOME conjunct (PRH_FnCheck.v:1379-1388) and the base's caw_dead touch no cut of this stretch (caw_at_OOM is
   unchanged, Caw102A_Base.v:617-622; caw_at_R now ends with the free's hull budget, :607). Beyond DW, the stretch's lemmas end
   at caw_k_OOMR, SRrG at RW (caw_wa3_holds : caw_seg_WA3R .. P RW); caw_call / caw_lx / caw_loop take the hull budget.
   THE IMAGE: A' = asan pin sha256 1be0f53d96cb9d6c, parametric over {PA : PAImg A_prog_listing} (the base's caw_img).
   THE INPUTS, each BY PATH as first fitted at a working branch a5641d45bc36 (= the tree of record
   #102 integration commit 41b333e9dba0, bound to the kit f97c8b2f046b, + one statements commit; blob ids at that
   commit; the batch base's own blobs are named in BASE OF RECORD above):
   - the shared statements lib/A/Prog/Caw102A_Base.v deec9ccf853b and the frame-state kit Caw102A_Kit.v 3d241a90402d
     (not edited here); the base header's input list (listing d42e123915ae lib/A/Listing_prog.v 7ed1529926bd; the
     kit f97c8b2f046b as the #102 integration commit carries it: lib/A/PRH_Base.v fdb45545469b (prh_ledger with most and own, its NAMED
     projections prh_ledger_blocks / prh_ledger_heads; prh_run_at; fpre with frm_zero (fp_csr fx) last, FRM0-ENTRY),
     PRH_FnCheck.v 9ecd8eb167c6, PRH_FnEx.v 45ddb7a7d5ae, PRH_Img.v 934516a622e8, lib/Spec/PresetRun.v 5ac818ab1fe6,
     PresetReqAt.v 43c958024221; the engine set of record from the engine commit 8a01e111a410: YC80x.v
     14f84f225e8f, YC1fPx.v 7814b594066f, YCbn.v 720e5b8bc8b0, YGcallx.v 7e1faf965c0d, YGcallcf.v 6d2b13c24437,
     YSRrMemnorm.v 5ffa8525936b, lib/Spec/PresetRodata.v 4eb7e95e7e93, lib/Spec/PjGrammar.v 5d4026de2876);
   - lib/Reusable/YGcallMxmn.v b47cf7942c3d (engine commit 8a01e111a410) and YGcallMxmnKeep.v: aj_free_x_ct_m_rh_keep, the free rule with the memnorm keep as
     its last conjunct; P crosses the call by PCALL from that keep;
   - lib/A/Prog/S1Ledger.v 8cf15eeb6311 (prh_ledger_kept_aview, at most own), lib/Reusable/YGcfRoomLive.v 2094cd3ced43
     (ccnt24, rl_b24_ok, RL_free_step :1429, room_live_room), lib/A/CfRoomLivePreset.v d0e5e47dcb02 (preset_rl_b24_ok:
     its closed batch-room conjunct at L24 + DRV + 1), lib/Spec/PresetRoomPosKeep.v 4377d5b0def1 (room_pos_keep_free),
     lib/Spec/PresetLiveBounds.v f78da450d5f6 (L24, DRV), lib/Spec/PresetRoom.v 0b749d72634f (ccnt), lib/Reusable/YG0d.v
     4cb085950f75 (ablocks). lib/A/PresetCfnA.v is NOT Required.
   - PORTED (statements and proofs, image-free): origin/cold/h-hpreset-7-walk-H2H5 1934271f1f4 lib/A/Prog/H2CawPure.v
     af16a877672b (the suffix lemmas, caw_read_V, caw_skip_cons / caw_skip_end, caw_ws_mask, caw_ws_big), H2CawBase.v
     f20e6e557cb1 (caw_chain, caw_split_last, caw_blk_disj, caw_scr_new, caw_scr_not_hp, caw_kregs_st; caw_ledger_free's
     idea), H2CawR.v 134b752d22a2 (caw_aregs).
   WHAT CHANGED ON THIS BASE (a5641d45bc36, Caw102A_Base.v deec9ccf853b; last green at the decff-era base 14b5c794bf92,
   Caw102A_Base.v e7a40f4137aa) AND WHY: the f97c text (PRH_FnCheck.v 9ecd8eb167c6) binds no run position at entry, so
   the base dropped caw_in's rp_* fields, caw_room_evs / caw_pre_room_evs / caw_room_evs_nth / caw_rpos_at / caw_rpos
   and the entry iface_room_pos premise; each cut carries instead THE PROGRESS FACT caw_prog D E S (for any run position
   i at the entry state whose next events are E, a position i + length E at S): caw_ev1 D = [HMal (size + 1)] at
   caw_at_R, caw_evs D = [HMal (size + 1); HFr (size + 1)] at caw_at_OOM. This file follows it: its own cuts caw_at_L /
   caw_at_LX / caw_at_C carry caw_prog D (caw_ev1 D) and caw_at_A / caw_fin_oom caw_prog D (caw_evs D); the hand steps
   keep it as is; __wrap_free steps it: a run at caw_evs D = caw_ev1 D ++ [HFr (size + 1)] splits (caw_run_at_app), the
   cut's caw_prog at caw_ev1 gives the position i + 1 at the free's entry state, caw_run_at_nth reads the event HFr
   (size + 1) there, room_pos_keep_free moves it to S (i + 1) = i + 2. THE ROOM COUNT: the free's room_live_cf keep
   (RL_free_step) needs rl_b24_ok at the free's entry state; the decff-era proof read the class-24 count off the exact
   position (counts_of_room_pos, ported as caw_hruns_big / caw_ccnt24_of_room_pos, both REMOVED here). Now it comes from
   caw_carry's caw_cnt D (ccnt24 (cw_S D) <= L24 + DRV at entry; at the batch base the text's own entry premise,
   caw_pre_c24, which the top passes as caw_pre_cnt) and the scratch's
   malloc: caw_scr's ablocks = the entry's ++ [(scr, size + 1)], so ccnt24 grows by at most 1 (caw_ccnt24_app), and
   rl_b24_ok (L24 + DRV + 1) holds with preset_rl_b24_ok's closed batch-room conjunct. caw_carry's second conjunct
   caw_cnt D crosses every step unchanged. FRM0-ENTRY (fpre's new last conjunct) touches no step here: the file
   builds no callee fpre (the free is the journal rule YGcallMxmnKeep.aj_free_x_ct_m_rh_keep) and every fpre destruct ends in `_`.
   THE CODE (the A' twin's disassembly in the internal file check_as_written.A_new.s of the plan, the internal file PLAN-cno-caw-102.md; DERIVED byte
   offsets from the entry, listing
   offset CAW_OFF + o; the engine's own stops, measured by its run on the listing):
     +128 R   ld a1 <- p (sp + 8), ld s1 <- end (sp + 16), bgeu a1, s1 (+136): p >= end (rest = []) -> +232; else
              li a2, 32; a3 = CAW_WS_MASK (lui / addiw / slli); mv a0, a1 -> +160.
     +160 L   the inlined ex_ws loop: srli a4, a0, 3; add a4, a4, s2; lb a4 (the shadow byte); +172 bnez a4 -> +212
              (andi a5, a0, 7; +216 blt a5, a4 -> +176; +220 jal __asan_report_load1); +176 lbu a4, 0(a1); +180
              bltu a2, a4 -> +228 (above 32); srl / andi / +192 beqz -> +228 (not whitespace); addi a1 / a0; +204
              bne a1, s1 -> +160; +208 j +224: mv a1, s1.
     +228 LX  sd a1, 8(sp); +232 ld s2, 8(sp); ld a0, 32(sp) (the scratch); +240 jal __wrap_free (ra = +244).
     +244 A   beq s2, s1 -> +328 (lw s2, 40(sp): want = differs; j +252); else +248 li s2, -1; +252 = CAW_PC_OOM.
   THE PROOF: one lemma per stretch, each ending in caw_k_OOMR's continuation at RW: caw_after (+244), caw_call (the free, at the
   callee entry), caw_lx (+228), caw_loop (+160, induction on size - j), caw_wa3_holds (+128). The free is
   aj_free_x_ct_m_rh_keep at the cf instance (QM_cf from room_live_room and the hull budget, the trace through prh_univ_closure_lit at the return
   site BASE + CAW_OFF + 244 of pi_ret_sites F_check_as_written RT_free, the empty chain: s0 = rc); after it: ablocks the
   entry's (caw_split_last), caw_prog at caw_evs (above), room_live_cf by RL_free_step at L24 + DRV + 1 (above), the
   cut's ledger at most own = 0 by caw_ledger_free (prh_ledger_kept_aview through the NAMED projections prh_ledger_blocks
   / prh_ledger_heads: the statics kept as image bytes (cwi_pst_img) off the owned statics and errno (pal_pst_ok), the
   Lam heads in entry blocks apart from the scratch), the read-only view by the call's image clause.
   want: p reaches end exactly when PjGrammar.skip rest = [] (the loop's invariant skip rest = skip (skipn j x)); then
   ck_read x = Some u (caw_read_V) and want = differs (caw_want's Some arm); otherwise want = -1 and ck_read x = None
   (caw_read_V and prhex_V's determinism).
   REFUTED REPORT SITE: +220 `jal __asan_report_load1` (the loop's shadow test). The engine folds the test's slow path
   (+212 andi, +216 blt, +220) into the obligation `range_addressable SHADOW_OFF p 1` (YCbn.v tok_load / tok_branch_pi; the
   runner lemma YC80x.v SRr_run_pi_tok_AJx_inv, sym_run_pi_tok_sound); caw_loop discharges it from src_rd's
   range_addressable over [data, data + size) (caw_at_R) by range_addressable_sub, so +220 is never reached.
  SECTION HYPOTHESES (owners): PAL (the unit's image binding of B, as lib/A/Prog/FuzzFree.v; owner a Theorem Labs lane); pal_pst_ok is
  NOT a hypothesis (a Theorem Labs lane, as WA2): a Let from caw_img's cwi_pst_ok / cwi_pst_errno; AFREE (the free wrapper's
   runtime row YGcfMallocComposeKeep.afree_realizes_cf_rh_keep at every float state; owner a Theorem Labs lane); CWI (caw_img of PA; owner
   the instantiation file Caw102A_Img.v, by computation where B is bound [a Theorem Labs lane]); P, PLAW, PCALL (the generic-P form; the
   top instantiates P := caw_mn D). No new hypothesis: the room count is the base's caw_cnt, read from caw_carry (the
   text's entry premises at the batch base, caw_pre_cnt). Every base name with an fx binder, caw_pre, caw_carry,
   caw_at_X .. caw_at_END,
   caw_k_X .. caw_k_END, caw_seg_WA3, is stated at the entry state, (fx := fx) (lead 16:4xZ).
   NUMERALS: 128 .. 328 DERIVED offsets inside the function, 2680 / 2748 / 2764 / 2772 the listing offsets CAW_OFF + 160 /
   228 / 244 / 252 (each checked by lia from CAW_OFF_val); 80, 72, 64, 48, 40, 32, 16, 8, 4 LENGTHs (the frame and its
   slots, word and int widths); 25712 DERIVED (STK_check_as_written, vm_compute); 16384 LENGTH (ASTACK); 32 WORD (the
   space byte, the loop's bound); CAW_WS_MASK DERIVED (the value the engine computes for a3); 2 ^ 31, 2 ^ 44, 2 ^ 46,
   2 ^ 47, 2 ^ 64 the bounds; atom numbers 2, 8 .. 35, 512, 513 DERIVED (the engine's numbering); register numbers WORD;
   1 / 2 the counts of one / two run events. No ADDRESS literal: A_prog_base enters only through cwi_base. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YGcfRoomPre YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
(* the free under the re-hide with the memnorm keep (part 3c took the keep out of the plain rules' posts) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep PresetLiveBounds PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Caw102A_Base Caw102A_Kit.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== 1. THE MODEL SIDE: pure lemmas, PORTED from origin/cold/h-hpreset-7-walk-H2H5 1934271f1f4
   lib/A/Prog/H2CawPure.v (blob af16a877672b), statements and proofs unchanged (image-free) ======== *)
Lemma cawp_sfx_trans : forall x y z : list Z,
  (exists p, x = p ++ y) -> (exists q, y = q ++ z) -> exists p, x = p ++ z.
Proof. intros x y z [p ->] [q ->]. exists (p ++ q). apply app_assoc. Qed.

Lemma cawp_sfx_cons : forall b (y z : list Z), (exists p, y = p ++ z) -> exists p, b :: y = p ++ z.
Proof. intros b y z [p ->]. exists (b :: p). reflexivity. Qed.

Lemma cawp_skip_sfx : forall x, exists p, x = p ++ PjGrammar.skip x.
Proof.
  induction x as [|b r IH]; cbn [PjGrammar.skip].
  - exists []. reflexivity.
  - destruct (PjGrammar.ws b).
    + apply cawp_sfx_cons. exact IH.
    + exists []. reflexivity.
Qed.

Lemma cawp_tl_sfx : forall x : list Z, exists p, x = p ++ tl x.
Proof. intros [|b r]; [exists []|exists [b]]; reflexivity. Qed.

Lemma cawp_skipn_sfx : forall k (x : list Z), exists p, x = p ++ skipn k x.
Proof. intros k x. exists (firstn k x). symmetry. apply firstn_skipn. Qed.

Lemma cawp_string_sfx : forall z ok s r t ok', PjGrammar.jr_string z ok = (Some (s, r), t, ok') ->
  exists p, z = p ++ r.
Proof.
  intros z ok s r t ok' H. pose proof (PjGrammar.jr_string_spec z ok) as Hs. rewrite H in Hs.
  cbv beta iota in Hs. destruct Hs as (q & _ & Hd & _ & _).
  destruct (PjGrammar.decode_stop z s r Hd) as (q' & _ & Hr & _). rewrite Hr.
  apply cawp_skipn_sfx.
Qed.

Lemma cawp_lit_sfx : forall w v x ok u r t ok', PjGrammar.lit w v x ok = (Some (u, r), t, ok') ->
  exists p, x = p ++ r.
Proof.
  intros w v x ok u r t ok' H. unfold PjGrammar.lit in H.
  destruct (PjGrammar.prefixb w x); cbv beta iota in H; [|unfold PjGrammar.jrefuse in H; discriminate].
  unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r. apply cawp_skipn_sfx.
Qed.

Lemma cawp_number_sfx : forall sm x ok u r t ok', PjGrammar.jr_number sm x ok = (Some (u, r), t, ok') ->
  exists p, x = p ++ r.
Proof.
  intros sm x ok u r t ok' H. unfold PjGrammar.jr_number in H. cbv beta zeta in H.
  destruct (skipn _ x) as [|c z] eqn:Ez; cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
  destruct (negb (PjGrammar.digit c)); cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
  destruct ((c =? 48) && _); cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
  destruct (PjGrammar.span PjGrammar.numch z) as [a r'] eqn:Es. cbv beta iota in H.
  apply PjGrammar.jbind_some in H as (a0 & t1 & ok1 & t2 & _ & H & _). cbv beta in H.
  destruct (PjGrammar.whole sm _); cbv beta iota in H; [|unfold PjGrammar.jrefuse in H; discriminate].
  unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r.
  apply (cawp_sfx_trans x (c :: z) r').
  - rewrite <- Ez. apply cawp_skipn_sfx.
  - apply cawp_sfx_cons. rewrite (PjGrammar.span_app _ _ _ _ Es). exists a. reflexivity.
Qed.

Lemma cawp_name_sfx : forall o y ok nm y1 t ok', PjGrammar.jr_name o y ok = (Some (nm, y1), t, ok') ->
  exists p, y = p ++ y1.
Proof.
  intros o y ok nm y1 t ok' H. unfold PjGrammar.jr_name in H. destruct o; cbv beta iota in H.
  - pose proof (cawp_skip_sfx y) as Hy.
    destruct (PjGrammar.skip y) as [|b z]; cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
    destruct (b =? 34); cbv beta iota in H; [|unfold PjGrammar.jrefuse in H; discriminate].
    apply PjGrammar.jbind_some in H as ([nm0 r] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
    pose proof (cawp_string_sfx _ _ _ _ _ _ Hs) as Hz.
    pose proof (cawp_skip_sfx r) as Hr.
    destruct (PjGrammar.skip r) as [|c r1]; cbv beta iota in H.
    + apply PjGrammar.jbind_some in H as (? & ? & ? & ? & _ & H & _). cbv beta in H.
      unfold PjGrammar.jrefuse in H. discriminate.
    + destruct (c =? 58); cbv beta iota in H.
      * unfold PjGrammar.jret in H. injection H as _ Hy1 _ _. subst y1.
        apply (cawp_sfx_trans y (b :: z) r1); [exact Hy|]. apply cawp_sfx_cons.
        apply (cawp_sfx_trans z r r1); [exact Hz|]. apply (cawp_sfx_trans r (c :: r1) r1); [exact Hr|].
        exists [c]. reflexivity.
      * apply PjGrammar.jbind_some in H as (? & ? & ? & ? & _ & H & _). cbv beta in H.
        unfold PjGrammar.jrefuse in H. discriminate.
  - unfold PjGrammar.jret in H. injection H as _ Hy1 _ _. subst y1. exists []. reflexivity.
Qed.

Lemma cawp_cont_sfx : forall loop d o x ok v r t ok',
  (forall o' n cap acc y ok1 v1 r1 t1 ok2, loop (S d) o' n cap acc y ok1 = (Some (v1, r1), t1, ok2) ->
     exists p, y = p ++ r1) ->
  PjGrammar.jr_cont loop d o x ok = (Some (v, r), t, ok') -> exists p, x = p ++ r.
Proof.
  intros loop d o x ok v r t ok' HL H. unfold PjGrammar.jr_cont in H. cbv beta in H.
  destruct (Nat.ltb PjGrammar.MAXD (S d)); cbv beta iota zeta in H; [unfold PjGrammar.jrefuse in H; discriminate|].
  assert (Hx : exists p, x = p ++ PjGrammar.skip (tl x)).
  { apply (cawp_sfx_trans x (tl x)); [apply cawp_tl_sfx|apply cawp_skip_sfx]. }
  destruct (PjGrammar.skip (tl x)) as [|c r0]; cbv beta iota in H.
  - exact (cawp_sfx_trans _ _ _ Hx (HL _ _ _ _ _ _ _ _ _ _ H)).
  - destruct (c =? PjGrammar.closer o); cbv beta iota in H.
    + unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r.
      apply (cawp_sfx_trans x (c :: r0) r0); [exact Hx|]. exists [c]. reflexivity.
    + exact (cawp_sfx_trans _ _ _ Hx (HL _ _ _ _ _ _ _ _ _ _ H)).
Qed.

Lemma cawp_suffix_fuel : forall sm f,
  (forall d x ok v r t ok', PjGrammar.jrv sm f d x ok = (Some (v, r), t, ok') -> exists p, x = p ++ r) /\
  (forall d o n cap acc y ok v r t ok', PjGrammar.jrl sm f d o n cap acc y ok = (Some (v, r), t, ok') ->
     exists p, y = p ++ r).
Proof.
  intros sm f. induction f as [|f [IHv IHl]].
  - split; intros; cbn [PjGrammar.jrv PjGrammar.jrl] in *; unfold PjGrammar.jrefuse in *; discriminate.
  - split.
    + intros d x ok v r t ok' H. cbn [PjGrammar.jrv] in H.
      pose proof (cawp_skip_sfx x) as Hx.
      destruct (PjGrammar.skip x) as [|b y]; cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
      apply (cawp_sfx_trans x (b :: y) r); [exact Hx|].
      destruct (b =? 123); cbv beta iota in H.
      { exact (cawp_cont_sfx _ _ _ _ _ _ _ _ _ (IHl (S d)) H). }
      destruct (b =? 91); cbv beta iota in H.
      { exact (cawp_cont_sfx _ _ _ _ _ _ _ _ _ (IHl (S d)) H). }
      destruct (b =? 34); cbv beta iota in H.
      { apply PjGrammar.jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
        unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r.
        apply cawp_sfx_cons. exact (cawp_string_sfx _ _ _ _ _ _ Hs). }
      destruct (b =? 116); cbv beta iota in H; [exact (cawp_lit_sfx _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 102); cbv beta iota in H; [exact (cawp_lit_sfx _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 110); cbv beta iota in H; [exact (cawp_lit_sfx _ _ _ _ _ _ _ _ H)|].
      exact (cawp_number_sfx _ _ _ _ _ _ _ H).
    + intros d o n cap acc y ok v r t ok' H. cbn [PjGrammar.jrl] in H.
      apply PjGrammar.jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply PjGrammar.jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply PjGrammar.jbind_some in H as ([v0 r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      apply (cawp_sfx_trans y y1 r); [exact (cawp_name_sfx _ _ _ _ _ _ _ En)|].
      apply (cawp_sfx_trans y1 r0 r); [exact (IHv _ _ _ _ _ _ _ Ev)|].
      pose proof (cawp_skip_sfx r0) as Hr0.
      destruct (PjGrammar.skip r0) as [|c r1]; cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate|].
      apply (cawp_sfx_trans r0 (c :: r1) r); [exact Hr0|].
      apply (cawp_sfx_trans (c :: r1) r1 r); [exists [c]; reflexivity|].
      destruct (c =? 44); cbv beta iota in H; [exact (IHl _ _ _ _ _ _ _ _ _ _ _ H)|].
      destruct (c =? PjGrammar.closer o); cbv beta iota in H; [|unfold PjGrammar.jrefuse in H; discriminate].
      unfold PjGrammar.jret in H. injection H as _ Hr _ _. subst r. exists []. reflexivity.
Qed.

Lemma cawp_jrv_suffix : forall sm f d x ok v r t ok',
  PjGrammar.jrv sm f d x ok = (Some (v, r), t, ok') -> exists p, x = p ++ r.
Proof. intros sm f. exact (proj1 (cawp_suffix_fuel sm f)). Qed.

Lemma cawp_skipn_app : forall p r : list Z, skipn (length p) (p ++ r) = r.
Proof. induction p as [|a p IH]; intros r; [reflexivity|exact (IH r)]. Qed.

Lemma cawp_V_sfx : forall d x v r, PRH_FnEx.prhex_V d x = Some (v, r) -> exists p, x = p ++ r.
Proof.
  intros d x v r H. unfold PRH_FnEx.prhex_V, PjGrammar.jr_value in H.
  destruct (PjGrammar.jrv ReaderRes.jr_strtod _ _ x []) as [[res t] ok'] eqn:E. cbn [fst] in H. subst res.
  exact (cawp_jrv_suffix _ _ _ _ _ _ _ _ _ E).
Qed.

(* ex_value's rest pointer: the rest r is the last length r bytes of x *)
Lemma caw_V_suffix : forall d x v r, PRH_FnEx.prhex_V d x = Some (v, r) ->
  skipn (length x - length r)%nat x = r.
Proof.
  intros d x v r H. destruct (cawp_V_sfx d x v r H) as [p ->].
  rewrite length_app. replace (length p + length r - length r)%nat with (length p) by lia.
  apply cawp_skipn_app.
Qed.

Lemma caw_V_len : forall d x v r, PRH_FnEx.prhex_V d x = Some (v, r) -> (length r <= length x)%nat.
Proof. intros d x v r H. destruct (cawp_V_sfx d x v r H) as [p ->]. rewrite length_app. lia. Qed.

(* ck_read through prhex_V 0: a tree exactly when the value reading succeeds and only whitespace follows *)
Lemma caw_read_V : forall x t, PRH_FnCheck.ck_read x = Some t <->
  exists r, PRH_FnEx.prhex_V 0 x = Some (t, r) /\ PjGrammar.skip r = [].
Proof.
  intros x t. unfold PRH_FnCheck.ck_read, PRH_FnEx.prhex_V, PjGrammar.json_read, PjGrammar.jr_run. cbv beta.
  change (Z.to_nat 0) with 0%nat.
  destruct (PjGrammar.jr_value ReaderRes.jr_strtod 0 x []) as [[[[t' r]|] tr] ok']; cbn [fst].
  - split.
    + intros H. exists r. destruct (PjGrammar.skip r) as [|b r1]; [|discriminate H].
      injection H as ->. split; reflexivity.
    + intros (r0 & H & Hs). injection H as -> ->. rewrite Hs. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros (r0 & H & _). discriminate H.
Qed.

(* the inlined ex_ws loop (fuzz_preset.c:103-107): one step of PjGrammar.skip over skipn i x, and its end *)
Lemma cawp_skipn_nth : forall i (x : list Z), (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
  induction i as [|i IH]; intros [|b x] H; cbn [length] in H; try lia.
  - reflexivity.
  - exact (IH x ltac:(lia)).
Qed.

Lemma caw_skip_cons : forall i x, (i < length x)%nat ->
  PjGrammar.skip (skipn i x) =
  if PjGrammar.ws (nth i x 0) then PjGrammar.skip (skipn (S i) x) else skipn i x.
Proof. intros i x H. rewrite (cawp_skipn_nth i x H). reflexivity. Qed.

Lemma caw_skip_end : forall x, PjGrammar.skip (skipn (length x) x) = [].
Proof. induction x as [|b x IH]; [reflexivity|exact IH]. Qed.

(* the machine's whitespace test: the mask (DERIVED: the value the engine computes for a3 from `lui a0, 0x800;
   addiw a0, a0, 0x13; slli a3, a0, 9`) shifted right by c, low bit, for c <= 32; no byte above 32 is whitespace *)
Definition CAW_WS_MASK : Z := 4294977024.
Lemma caw_ws_mask : forall c, 0 <= c <= 32 ->
  Z.land (Z.shiftr CAW_WS_MASK c) 1 = if PjGrammar.ws c then 1 else 0.
Proof.
  intros c Hc. unfold CAW_WS_MASK.
  replace c with (Z.of_nat (Z.to_nat c)) by lia.
  assert (Hn : (Z.to_nat c <= 32)%nat) by lia.
  revert Hn. generalize (Z.to_nat c) as n. intros n Hn. clear Hc.
  do 33 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma caw_ws_big : forall c, 32 < c -> PjGrammar.ws c = false.
Proof.
  intros c Hc. unfold PjGrammar.ws.
  rewrite (proj2 (Z.eqb_neq c 32)), (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 10)),
    (proj2 (Z.eqb_neq c 13)) by lia.
  reflexivity.
Qed.

(* ======== the live class-24 count after one new block: the entry's count plus at most 1 (the scratch's malloc adds
   one block to ablocks, which keeps every request size; YGcfRoomLive.ccnt24 counts the class-24 request sizes) ======== *)
Lemma caw_ccnt24_app : forall (B : asyms) ly S ly' S' (x : Z * Z),
  ablocks B ly' S' = ablocks B ly S ++ [x] -> YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S + 1.
Proof.
intros B ly S ly' S' x E. apply (f_equal (map snd)) in E. unfold ablocks in E. rewrite map_app, !map_map in E.
change (map snd (blocks S') = map snd (blocks S) ++ [snd x]) in E.
unfold YGcfRoomLive.ccnt24, PresetRoom.ccnt. rewrite E, filter_app, length_app.
lazymatch goal with |- context [List.filter ?f [?y]] => cbn [List.filter]; destruct (f y); cbn [length]; lia end.
Qed.

(* ======== 2. the stages' tactics ======== *)
(* the write premise of a run whose regions are read-only *)
Ltac caw_nowr := let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn in Hin; repeat (destruct Hin as [<- | Hin]; [cbn in Hr; lia|]); destruct Hin.
(* after a read-only run: EM : the new machine memory = the old one *)
Ltac caw_ro0 HF HFr HG EM :=
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM end;
  clear HF HFr HG.
Ltac caw_ro HF HFr HG EM :=
  let Em := fresh "Em" in
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Em end;
  clear HF HFr HG; rewrite EM in Em; clear EM; rename Em into EM.

(* the engine's shadow span (cgif's convention) *)
Definition CAW_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* a frame stage's facts: atom 2 is the entry sp, 16-aligned, in the stack band *)
Definition caw_G : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

Lemma caw_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.

(* the callee-saved registers are preserved when sp, s0, s1, s2 are and the others never moved
   (PORTED from 1934271f1f4 lib/A/Prog/H2CawR.v caw_aregs) *)
Ltac caw_inbv := repeat (first [left; apply bv_eq; reflexivity | right]).
Lemma caw_aregs : forall (regs regs' : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
  aregs_preserved regs regs'.
Proof.
intros regs regs' H r Hr. unfold acallee_saved in Hr.
assert (E : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct E as [-> | E]; [apply H; caw_inbv |]). subst r. apply H; caw_inbv.
Qed.

(* chain_pre with the empty chain: s0 holds rc (an int, sign-extended), never a frame pointer above sp
   (PORTED from 1934271f1f4 lib/A/Prog/H2CawBase.v caw_chain) *)
Lemma caw_chain : forall ly rd regs rc0, 4096 <= raZ regs -> getr regs 8 = w64 rc0 -> - 2 ^ 31 <= rc0 < 2 ^ 31 ->
  2 ^ 31 <= spZ regs -> ly_top ly <= 2 ^ 47 -> chain_pre ly rd regs [].
Proof.
intros ly rd regs rc0 Hra Hs0 Hrc Hsp Htop. split; [exact Hra|].
destruct (frame0_ok ly regs); [|reflexivity].
replace (bad_next (spZ regs) (ly_top ly) (s0Z regs)) with true; [reflexivity|]. symmetry.
unfold bad_next, s0Z. rewrite Hs0. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64).
destruct (Z_le_gt_dec 0 rc0) as [Hp|Hn].
- rewrite Z.mod_small by lia. apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
- replace (rc0 mod 2 ^ 64) with (rc0 + 2 ^ 64) by (rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia;
    rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
  apply orb_true_intro. left. apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

(* the free's trace with the empty chain: [pc0] or the filtered [pc0; ra] (prh_trace), both in the closure *)
Lemma caw_trace : forall ly pc0 regs (U : list (list Z)), In [pc0] U -> In (prh_trace pc0 (raZ regs) []) U ->
  In (call_trace ly pc0 regs []) U.
Proof.
intros ly pc0 regs U H1 H2. unfold call_trace. destruct (frame0_ok ly regs); [|exact H1].
exact H2.
Qed.

(* a list with x last and x nowhere else, split around x (PORTED from H2CawBase.v caw_split_last) *)
Lemma caw_split_last : forall (l l1 l2 : list (Z * Z)) x, l ++ [x] = l1 ++ x :: l2 -> ~ In x l -> l1 = l /\ l2 = [].
Proof.
induction l as [|y l IH]; intros l1 l2 x E Hn.
- destruct l1 as [|z l1]; cbn in E.
  + inversion E. split; reflexivity.
  + inversion E as [[Ez E2]]. destruct l1; discriminate.
- destruct l1 as [|z l1]; cbn in E.
  + inversion E; subst. exfalso. apply Hn. left. reflexivity.
  + inversion E as [[Ey E2]]. subst z.
    destruct (IH l1 l2 x E2 (fun H => Hn (or_intror H))) as [-> ->]. split; reflexivity.
Qed.

(* the 4-byte differs word as the engine reads it back: lw sign-extends 0 / 1 to themselves *)
Lemma caw_sext01 : forall dl, dl = 0 \/ dl = 1 ->
  zcanon (bv_swrap 32 (dl mod 2 ^ Z.of_N 32)) = dl.
Proof. intros dl [-> | ->]; vm_compute; reflexivity. Qed.

(* p == end exactly when the rest after the value is all whitespace; then ck_read reads the value *)
Lemma caw_skip_nil_of_len : forall (r : list Z), Z.of_nat (length r) = 0 -> r = [].
Proof. intros [|b r] H; [reflexivity | cbn [length] in H; lia]. Qed.

(* ======== 3. THE SEGMENT: the image parametric over PA, the cf allocator at CfParams_preset (CawA102 13:5xZ: a
   segment may bind cp := CfParams_preset when a room lemma needs it; CfRoomLivePreset.preset_rl_b24_ok does) ======== *)
Section wa3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instances CW_PrhImg CW_PAListing CW_RL.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* instance bindings, as lib/A/Prog/FuzzFree.v takes them (owner a Theorem Labs lane: the unit's image binding of B) *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
(* the free wrapper's runtime row under the re-hide, with the memnorm keep at the leaf (YGcfMallocComposeKeep.v), at
   every float state: the free runs at the cut's float state fy, which ex_value set *)
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) segs B.
(* the image facts of PA (Caw102A_Base.v caw_img; owner: the instantiation file, by computation) *)
Hypothesis CWI : caw_img (PA := PA) B.
(* the statics are off the owned statics and errno: the base's cwi_pst_ok / cwi_pst_errno (no Section hypothesis) *)
Let pal_pst_ok : forall a, Exists (in_zr a) prh_pst ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) :=
  fun a Ha => conj (proj2 (cwi_pst_ok CWI a Ha)) (cwi_pst_errno CWI a Ha).
(* the memory invariant: the runner laws, and the call law (the stretch crosses __wrap_free) *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Hypothesis PCALL : srr_inv_call segs P.

Let LAWS_cf : AR_laws_cf segs B := AR_laws_ok_cf segs B.
Let LAWS : AR_laws_x segs B (ARcfx B) cf_head := AR_laws_x_xs segs B LAWS_cf.
(* the world relation past a free (the re-hide's zone) *)
#[local] Abbreviation RW := (YA0nH.wle' segs YGcfRehidePost.RZ_cf).
(* an SRr run whose post is an SRrG fact at RW is an SRrG run at RW (wle is inside RW) *)
Lemma caw_lift : forall W c (Q : world segs -> config -> Prop),
  SRr segs W c (fun W' c' => YA0nH.SRrG segs RW W' c' Q) -> YA0nH.SRrG segs RW W c Q.
Proof.
intros W c Q H.
apply (YA0nH.SRrG_bind segs RW (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf) W c _ Q
  (YA0nH.SRr_SRrG segs RW (YA0nH.wle_wle' segs YGcfRehidePost.RZ_cf) W c _ H)).
intros W' c' _ H'. exact H'.
Qed.
(* YC1fP.paj_branch over any world relation R (a branch takes no step: the case split on its condition) *)
Lemma caw_branchR : forall (fz : YK11.FPState) (R : world segs -> world segs -> Prop) W E ss ms md Q c a b,
  st_ok_pi (fx := fz) segs VAL E ss (restrict (w_H W) ms) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = true ->
   st_ok_pi (fx := fz) segs VAL E (add_cond ss (mkAC c a b)) (restrict (w_H W) ms) ->
   YA0nH.SRrG segs R W (mkCfg ms md) Q) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = false ->
   st_ok_pi (fx := fz) segs VAL E (add_cond ss (mkAC (neg_bc c) a b)) (restrict (w_H W) ms) ->
   YA0nH.SRrG segs R W (mkCfg ms md) Q) ->
  YA0nH.SRrG segs R W (mkCfg ms md) Q.
Proof.
intros fz R W E ss ms md Q c a b HS HT HF.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply HT; [reflexivity|]. pose proof (st_ok_add_cond segs E _ _ c a b HS Hb) as H. destruct ss; exact H.
- apply HF; [reflexivity|]. pose proof (st_ok_add_cond_neg segs E _ _ c a b HS Hb) as H. destruct ss; exact H.
Qed.

(* the entry sp: in the stack band, 16-aligned (fpre's astk_ok) *)
Lemma caw_sp0_band : forall D, caw_pre (fx := fx) B CTX0 D ->
  2 ^ 46 <= cw_sp0 D <= 2 ^ 47 /\ cw_sp0 D mod 16 = 0.
Proof.
intros D Hpre. pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (HAFN & _).
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). unfold cw_sp0. split; [lia | exact Hal16].
Qed.

(* the callee-saved registers the engine leaves alone (PORTED from H2CawBase.v caw_kregs_st, at the record D) *)
Lemma caw_kregs_st : forall (fz : YK11.FPState) D (H : word -> bool) E ss ms regs sp0 vals,
  st_ok_pi (fx := fz) segs VAL E ss (restrict H ms) ->
  env_agree 32 (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = true ->
  caw_kregs D regs -> caw_kregs D (ms_regs ms).
Proof.
intros fz D H E ss ms regs sp0 vals HS HA Hl Hk r Hr.
assert (Hne : r <> 2%bv).
{ intros ->. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
pose proof (regs_kept_of_st_ok_pi (fx := fz) (L := A_prog_listing) (PI := PA) E ss (restrict H ms) _ _ _ HS HA Hl r Hr) as X.
cbn [restrict ms_regs] in X. rewrite X. rewrite caw_getr_upd_other by exact Hne. exact (Hk r Hr).
Qed.

(* p2: where the inlined ex_ws loop leaves p (the bytes after the value, whitespace skipped) *)
Definition caw_p2 (D : caw_in) (rest : list Z) : Z :=
  cw_data D + cw_size D - Z.of_nat (length (PjGrammar.skip rest)).
Lemma caw_skip_len : forall r : list Z, (length (PjGrammar.skip r) <= length r)%nat.
Proof. induction r as [|b r IH]; [cbn; lia|]. cbn. destruct (PjGrammar.ws b); cbn; lia. Qed.

(* ---- the cut at the return site of the free (+244): the scratch is freed (the entry's blocks; both run events made:
   caw_prog at caw_evs, as caw_at_OOM), s1 = end, s2 = p2; the ledger at most own = 0 ---- *)
Definition caw_at_A (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) (u : PjTree.jv) (rest : list Z)
  (dl : Z) : Prop :=
  caw_carry (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ caw_prog D (caw_evs D) S3 /\
  getr regs3 8 = w64 (cw_rc D) /\ getr regs3 9 = w64 (cw_data D + cw_size D) /\
  getr regs3 18 = w64 (caw_p2 D rest) /\ prhex_V 0 (cw_x D) = Some (u, rest) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 40) 4 dl /\ (dl = 0 \/ dl = 1) /\ (dl = 1 <-> cw_rc D = 0 /\ cw_t D <> u) /\
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) /\
  caw_ledger B D ly3 S3 Hp3 W3 mem3 0.
(* caw_at_A over a world relation R: caw_carryR R in place of caw_carry (its body caw_at_A's; the free's cut is at
   wle') *)
Definition caw_at_AR (R : world segs -> world segs -> Prop) (D : caw_in) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k : Z) (u : PjTree.jv) (rest : list Z) (dl : Z) : Prop :=
  caw_carryR (fx := fx) B SK CTX0 R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ caw_prog D (caw_evs D) S3 /\
  getr regs3 8 = w64 (cw_rc D) /\ getr regs3 9 = w64 (cw_data D + cw_size D) /\
  getr regs3 18 = w64 (caw_p2 D rest) /\ prhex_V 0 (cw_x D) = Some (u, rest) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 40) 4 dl /\ (dl = 0 \/ dl = 1) /\ (dl = 1 <-> cw_rc D = 0 /\ cw_t D <> u) /\
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) /\
  caw_ledger B D ly3 S3 Hp3 W3 mem3 0.
Lemma caw_at_A_R_wle : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k u rest dl,
  caw_at_A D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k u rest dl =
  caw_at_AR (@wle segs) D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k u rest dl.
Proof. reflexivity. Qed.

(* the OOM cut from a run's end state past the free (at RW): the carry's memory facts at the same memory, the journal,
   registers *)
Lemma caw_fin_oom : forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k regs' mem' md' k' want,
  caw_carryR (fx := fx) B SK CTX0 RW D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k -> caw_prog D (caw_evs D) S3 ->
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) -> caw_ledger B D ly3 S3 Hp3 W3 mem3 0 ->
  mem' = mem3 -> caw_JR B SK RW D ly3 S3 Hp3 W3 mem' md' k' ->
  caw_kregs D regs' -> spZ regs' = cw_sp0 D - CAW_FRAME ->
  getr regs' 8 = w64 (cw_rc D) -> getr regs' 18 = w64 want -> caw_want D want ->
  caw_k_OOMR (fx := fx) B SK CTX0 P RW Q D -> P mem' ->
  YA0nH.SRrG segs RW W3 (caw_cfg fy CAW_PC_OOM regs' mem' md') (caw_QP P Q).
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k regs' mem' md' k' want HC HRP Eab HL -> HJ Hkr Hsp R8 R18 HW HK HPM.
apply (HK fy ly3 S3 Hp3 W3 regs' mem3 md' k' want); [|exact HPM].
destruct HC as (Hpre & Hcnt & Hfl & _ & _ & _ & HSV & EHp & HRL & HROD).
split; [|split; [exact HRP | split; [exact R8 | split; [exact R18 | split; [exact HW | split; [exact Eab | exact HL]]]]]].
split; [exact Hpre|]. split; [exact Hcnt|]. split; [exact Hfl|]. split; [exact HJ|]. split; [exact Hkr|].
split; [exact Hsp|]. split; [exact HSV|]. split; [exact EHp|]. split; [exact HRL | exact HROD].
Qed.

(* ======== STAGE A (+244 -> +252), past the free at RW: `beq s2, s1`; equal: `lw s2, 40(sp)` (want = differs); else
   `li s2, -1` ======== *)
Lemma caw_after : forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k u rest dl,
  caw_at_AR RW D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k u rest dl -> caw_k_OOMR (fx := fx) B SK CTX0 P RW Q D -> P mem3 ->
  YA0nH.SRrG segs RW W3 (caw_cfg fy 244 regs3 mem3 md3) (caw_QP P Q).
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k u rest dl HA HK HPM.
destruct HA as (HC & HRP & R8 & R9 & R18 & HV & V40 & Hdl & Hdlu & Eab & HL).
pose proof HC as (Hpre & Hcnt & Hfl & HJ & Hkr & Hsp & HSV & EHp & HRL & HROD).
destruct (caw_sp0_band D Hpre) as (Rsp & Hal16).
pose proof (caw_pre_rc (fx := fx) B CTX0 D Hpre) as Hrc. pose proof (caw_pre_size (fx := fx) B CTX0 D Hpre) as Hsz.
pose proof (caw_pre_data0 (fx := fx) B CTX0 D Hpre) as Hd0. pose proof (caw_pre_data62 (fx := fx) B CTX0 D Hpre) as Hd62.
pose proof (caw_V_len 0 (cw_x D) u rest HV) as Hrl.
pose proof (caw_skip_len rest) as Hsk.
assert (Hp2 : cw_data D <= caw_p2 D rest <= cw_data D + cw_size D) by (unfold caw_p2, cw_size in *; lia).
assert (Hsz0 : 0 <= cw_size D) by (unfold cw_size; lia).
set (sp0 := cw_sp0 D) in *.
assert (HS : st_ok_pi (fx := fy) segs VAL (caw_Ee regs3 sp0 [dl])
  (mkSS (CAW_OFF + 244) caw_sr80 [caw_fregion_e [(-40, 4%N)] 0 0] None caw_G)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + 244))) mem3 (YK11.seg_rom segs)))).
{ apply (caw_st_ok_e (fz := fy)).
  - vm_compute. reflexivity.
  - cbn. lia.
  - exact Hsp.
  - unfold CAW_FRAME. lia.
  - intros o Ho. lia.
  - cbn [caw_vals_ok]. replace (sp0 + -40) with (sp0 - 40) by lia.
    change (N.to_nat 4) with 4%nat. change (8 * Z.of_N 4) with 32. change (Z.of_N 4) with 4.
    split; [exact V40|]. split; [destruct Hdl as [-> | ->]; lia|]. split; [lia | exact I].
  - unfold facts_ok, caw_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite caw_Ee_sp, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
set (E := caw_Ee regs3 sp0 [dl]) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_Ee; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (E8 : ew E 8 = getr regs3 8) by (subst E; exact (caw_Ee_reg regs3 sp0 [dl] 8 8%bv eq_refl ltac:(discriminate))).
assert (E9 : ew E 9 = getr regs3 9) by (subst E; exact (caw_Ee_reg regs3 sp0 [dl] 9 9%bv eq_refl ltac:(discriminate))).
assert (E18 : ew E 18 = getr regs3 18) by (subst E; exact (caw_Ee_reg regs3 sp0 [dl] 18 18%bv eq_refl ltac:(discriminate))).
assert (E33 : ew E 33 = Z_to_bv 64 dl) by (subst E; exact (caw_Ee_val regs3 sp0 [dl] 0 ltac:(lia))).
assert (E2 : ew E 2 = Z_to_bv 64 sp0) by (subst E; apply caw_Ee_sp).
assert (U18 : U E (SOff 18 0) = caw_p2 D rest) by (apply U_atom; [rewrite E18; exact R18 | lia]).
assert (U9 : U E (SOff 9 0) = cw_data D + cw_size D) by (apply U_atom; [rewrite E9; exact R9 | lia]).
assert (U33 : U E (SOff 33 0) = dl) by (apply U_atom; [exact E33 | destruct Hdl as [-> | ->]; lia]).
pose (RUN := paj_run_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW RW (YA0nH.wle'_refl segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (RUNTO := paj_run_to_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW RW (YA0nH.wle'_refl segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (BR := caw_branchR fy RW).
unfold caw_cfg, caw_pc. rewrite <- Z.add_assoc.
unfold caw_JR in HJ.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CAW_Bspan.
{ caw_nowr. }
caw_ro0 HF HFr HG EM.
psrr_branch_tok RUN BR HS SHOK CAW_Bspan.
- (* +244 beq taken, p2 == end: the rest after the value is all whitespace; +328 `lw s2, 40(sp)`, `j +252` *)
  rewrite branch_eq_U, U18, U9 in Hc. apply Z.eqb_eq in Hc.
  assert (Hsk0 : PjGrammar.skip rest = []) by (apply caw_skip_nil_of_len; unfold caw_p2 in Hc; lia).
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CAW_Bspan (CAW_OFF + 252).
  { caw_nowr. }
  caw_ro HF HFr HG EM.
  lazymatch goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
    assert (R18' : getr (ms_regs m) 18 = w64 dl);
    [ rewrite (st_ok_pi_restrict_reg (fx := fy) _ _ _ _ 18%bv HS);
      lazymatch goal with |- context [sr_get ?sr 18%bv] =>
        let t' := eval vm_compute in (sr_get sr 18%bv) in change (sr_get sr 18%bv) with t' end;
      rewrite denot_lit_U, U_SExt, U33; unfold w64; f_equal; exact (caw_sext01 dl Hdl)
    | ];
    pmkst HS;
    replace (BASE + 2772) with (caw_pc CAW_PC_OOM) by (unfold caw_pc, CAW_PC_OOM; rewrite CAW_OFF_val; lia);
    refine (caw_fin_oom Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k (ms_regs m) (ms_mem m) d _ dl HC HRP Eab HL EM HJ
      _ _ _ R18' _ HK HPM)
  end.
  + exact (caw_kregs_st fy D (w_H W3) E _ _ regs3 sp0 [dl] HS (caw_Ee_agree regs3 sp0 [dl])
      ltac:(vm_compute; reflexivity) Hkr).
  + apply (caw_sp_st (fz := fy) (w_H W3) E _ _ sp0 HS eq_refl E2). unfold CAW_FRAME. lia.
  + rewrite (caw_reg_st (fz := fy) (w_H W3) E _ _ 8%bv 8 _ HS eq_refl eq_refl). rewrite E8. exact R8.
  + right. exists u. split; [apply caw_read_V; exists rest; split; [exact HV | exact Hsk0]|].
    split; [exact Hdl | exact Hdlu].
- (* +244 beq not taken, p2 <> end: `li s2, -1`; the reading of x was refused (ck_read x = None) *)
  rewrite branch_eq_U, U18, U9 in Hc. apply Z.eqb_neq in Hc.
  assert (HN : ck_read (cw_x D) = None).
  { destruct (ck_read (cw_x D)) as [t'|] eqn:Er; [|reflexivity]. exfalso.
    apply caw_read_V in Er as (r' & HV' & Hs'). rewrite HV in HV'. injection HV' as _ Er. subst r'.
    apply Hc. unfold caw_p2. rewrite Hs'. cbn [length Z.of_nat]. lia. }
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CAW_Bspan (CAW_OFF + 252).
  { caw_nowr. }
  caw_ro HF HFr HG EM.
  lazymatch goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
    assert (R18' : getr (ms_regs m) 18 = w64 (-1));
    [ rewrite (st_ok_pi_restrict_reg (fx := fy) _ _ _ _ 18%bv HS);
      lazymatch goal with |- context [sr_get ?sr 18%bv] =>
        let t' := eval vm_compute in (sr_get sr 18%bv) in change (sr_get sr 18%bv) with t' end;
      cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !unsigned_lit; reflexivity
    | ];
    pmkst HS;
    replace (BASE + 2772) with (caw_pc CAW_PC_OOM) by (unfold caw_pc, CAW_PC_OOM; rewrite CAW_OFF_val; lia);
    refine (caw_fin_oom Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k (ms_regs m) (ms_mem m) d _ (-1) HC HRP Eab HL EM HJ
      _ _ _ R18' _ HK HPM)
  end.
  + exact (caw_kregs_st fy D (w_H W3) E _ _ regs3 sp0 [dl] HS (caw_Ee_agree regs3 sp0 [dl])
      ltac:(vm_compute; reflexivity) Hkr).
  + apply (caw_sp_st (fz := fy) (w_H W3) E _ _ sp0 HS eq_refl E2). unfold CAW_FRAME. lia.
  + rewrite (caw_reg_st (fz := fy) (w_H W3) E _ _ 8%bv 8 _ HS eq_refl eq_refl). rewrite E8. exact R8.
  + left. split; [exact HN | reflexivity].
Qed.


(* ======== the facts the free call reads, and what crosses it ======== *)
Lemma caw_val_mem_move : forall m m' a n v, val_mem segs m a n v ->
  (forall k, (k < n)%nat -> mbyte segs m' (a + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) -> val_mem segs m' a n v.
Proof. intros m m' a n v H HM k Hk. rewrite HM by exact Hk. exact (H k Hk). Qed.

(* a callee-saved register crosses a call (aregs_preserved) *)
Lemma caw_pres_reg : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r Hp Hz. pose proof (Hp _ Hz) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X. Qed.
Ltac caw_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.
Lemma caw_kregs_pres : forall D regs regs', aregs_preserved regs regs' -> caw_kregs D regs -> caw_kregs D regs'.
Proof.
intros D regs regs' Hp Hk r Hr. rewrite <- (Hk r Hr). apply caw_pres_reg; [exact Hp|].
cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [caw_cs|]). destruct Hr.
Qed.

(* two different blocks of a state are apart (PORTED from H2CawBase.v caw_blk_disj) *)
Lemma caw_blk_disj : forall ly S Hp W mem md p n q m, ARcfx B ly S Hp W mem md ->
  In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
  p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S Hp W mem md p n q m HAR H1 H2 Hne.
pose proof (sep_blocks_x segs B (ARcfx B) LAWS ly S Hp W mem md p n q m HAR H1 H2 Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

(* the scratch is a new block: not one of entry's (PORTED from H2CawBase.v caw_scr_new, at the record D) *)
Lemma caw_scr_new : forall D ly3 S3 Hp3 W3 mem3 md3 scr, ARcfx B ly3 S3 Hp3 W3 mem3 md3 -> caw_scr B D ly3 S3 scr ->
  0 <= cw_size D -> ~ In (scr, cw_size D + 1) (ablocks B (cw_ly D) (cw_S D)).
Proof.
intros D ly3 S3 Hp3 W3 mem3 md3 scr HAR (Hs4 & E) Hn Hin.
assert (Hin' : In (scr, cw_size D + 1) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
pose proof (pairwise_In2 zdisjoint _ (scr, req_size (cw_size D + 1)) (scr, req_size (cw_size D + 1))
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l1) (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
  ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as Dj.
unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite caw_req in Dj by lia. lia.
Qed.

(* the scratch's base is no harness head (PORTED from H2CawBase.v caw_scr_not_hp; the ledger by its NAMED projections) *)
Lemma caw_scr_not_hp : forall D ly3 S3 Hp3 W3 mem3 md3 scr, caw_pre (fx := fx) B CTX0 D ->
  ARcfx B ly3 S3 Hp3 W3 mem3 md3 -> caw_scr B D ly3 S3 scr -> ~ In scr (cw_Hp D).
Proof.
intros D ly3 S3 Hp3 W3 mem3 md3 scr Hpre HAR Hscr Hin.
pose proof (caw_pre_ledger (fx := fx) B CTX0 D Hpre) as HL0.
assert (Hn0 : 0 <= cw_size D) by (unfold cw_size; lia).
pose proof (caw_scr_new D ly3 S3 Hp3 W3 mem3 md3 scr HAR Hscr Hn0) as Hnew.
pose proof (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ HL0) as HP.
pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL0) as HF.
apply (Permutation_in _ HP) in Hin.
apply in_map_iff in Hin as ([a kk] & Ea & HinL). cbn [fst] in Ea.
destruct (proj1 (Forall_forall _ _) HF _ HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hab, Hk0.
change (@cf_head CfParams_preset) with 16 in *.
destruct Hscr as (H4 & E).
assert (Hin1 : In (a - 16, kk + 16) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; left; exact Hab).
assert (Hin2 : In (scr, cw_size D + 1) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (Z.eq_dec (kk + 16) (cw_size D + 1)) as [Eq | Ne].
- apply Hnew. replace scr with (a - 16) by lia. rewrite <- Eq. exact Hab.
- assert (Ne' : (a - 16, kk + 16) <> (scr, cw_size D + 1)) by (intros X; injection X; lia).
  pose proof (caw_blk_disj _ _ _ _ _ _ _ _ _ _ HAR Hin1 Hin2 Ne') as Dj. rewrite !caw_req in Dj by lia. lia.
Qed.

(* the cut's ledger after the scratch's free (H2CawBase.v caw_ledger_free's idea, through S1Ledger.prh_ledger_kept_aview
   at most own and the ledger's NAMED projections): the statics, g_most and g_own_ran_out among them, are image bytes
   (cwi_pst_img) off the owned statics and errno (pal_pst_ok); the heads of Lam lie in entry blocks, apart from the
   scratch *)
Lemma caw_ledger_free : forall D ly3 S3 Hp3 W3 mem3 md3 ly4 S4 W4 mem4 scr own,
  caw_pre (fx := fx) B CTX0 D -> ARcfx B ly3 S3 Hp3 W3 mem3 md3 -> caw_scr B D ly3 S3 scr ->
  caw_ledger B D ly3 S3 Hp3 W3 mem3 own ->
  ablocks B ly4 S4 = ablocks B (cw_ly D) (cw_S D) ->
  (forall b m i, In (b, m) (ablocks B ly3 S3) -> 0 <= i < req_size m -> ~ scr <= b + i < scr + req_size (cw_size D + 1) ->
     aview segs (w_H W4) mem4 (b + i) = aview segs (w_H W3) mem3 (b + i)) ->
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ as_errno B <= a < as_errno B + 4 ->
     aview segs (w_H W4) mem4 a = aview segs (w_H W3) mem3 a) ->
  caw_ledger B D ly4 S4 Hp3 W4 mem4 own.
Proof.
intros D ly3 S3 Hp3 W3 mem3 md3 ly4 S4 W4 mem4 scr own Hpre HAR Hscr HL Eab K2 K3.
unfold caw_ledger in HL |- *.
pose proof (caw_pre_ledger (fx := fx) B CTX0 D Hpre) as HL0.
assert (Hn0 : 0 <= cw_size D) by (unfold cw_size; lia).
pose proof (caw_scr_new D ly3 S3 Hp3 W3 mem3 md3 scr HAR Hscr Hn0) as Hnew.
pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL0) as HF.
pose proof Hscr as (H4 & E3).
apply (prh_ledger_kept_aview B ly3 S3 Hp3 W3 mem3 ly4 S4 Hp3 W4 mem4 _ _ _ _ _ _ _ HL).
- intros a Ha. destruct (pal_pst_ok a Ha) as [H1 H2]. apply K3; [exact (cwi_pst_img CWI a Ha) | exact H1 | exact H2].
- intros a k i HinL Hi.
  destruct (proj1 (Forall_forall _ _) HF _ HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hab, Hk0.
  change (@cf_head CfParams_preset) with 16 in *.
  assert (Hab3 : In (a - 16, k + 16) (ablocks B ly3 S3)) by (rewrite E3; apply in_or_app; left; exact Hab).
  assert (Hin2 : In (scr, cw_size D + 1) (ablocks B ly3 S3)) by (rewrite E3; apply in_or_app; right; left; reflexivity).
  assert (Ne : (a - 16, k + 16) <> (scr, cw_size D + 1)) by (intros X; apply Hnew; rewrite <- X; exact Hab).
  pose proof (caw_blk_disj _ _ _ _ _ _ _ _ _ _ HAR Hab3 Hin2 Ne) as Dj.
  apply (K2 (a - 16) (k + 16) i Hab3); rewrite !caw_req in * by lia; lia.
- intros a k HinL _. destruct (proj1 (Forall_forall _ _) HF _ HinL) as (_ & Hab & _). cbn [fst snd] in Hab.
  rewrite Eab. exact Hab.
- apply Permutation_refl.
Qed.

(* the read-only view crosses any change that keeps the image off the owned statics and errno *)
Lemma caw_arod_kept : forall (W : world segs) mem (W' : world segs) mem',
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W) mem) ->
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ as_errno B <= a < as_errno B + 4 ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W') mem').
Proof.
intros W mem W' mem' H K a Ha H1 H2. rewrite (K a); [exact (H a Ha H1 H2) | | exact H1 | exact H2].
destruct Ha as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)].
Qed.

(* the caller's saved words and the frame survive the free: they lie above its stack window *)
Lemma caw_saved_kept : forall D (W : world segs) mem (W' : world segs) mem', caw_saved D W mem ->
  (forall a, cw_sp0 D - 32 <= a < cw_sp0 D -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  caw_saved D W' mem'.
Proof.
intros D W mem W' mem' (V1 & V2 & V3 & V4) K. unfold caw_saved.
split; [|split; [|split]];
  [apply (caw_val_mem_move _ _ _ _ _ V1) | apply (caw_val_mem_move _ _ _ _ _ V2)
  | apply (caw_val_mem_move _ _ _ _ _ V3) | apply (caw_val_mem_move _ _ _ _ _ V4)];
  intros kk Hkk; apply (mbyte_of_aview segs); apply K; lia.
Qed.

(* the free's return site is check_as_written's __wrap_free site (PRH_Img.v's generated table, through cwi_base) *)
Lemma caw_site : BASE = A_prog_base -> In (BASE + 2764) (pi_ret_sites F_check_as_written RT_free).
Proof.
intros ->. assert (Hb : existsb (Z.eqb (A_prog_base + 2764)) (pi_ret_sites F_check_as_written RT_free) = true)
  by (vm_compute; reflexivity).
apply existsb_exists in Hb as (x & Hx & Hxe). apply Z.eqb_eq in Hxe. rewrite Hxe. exact Hx.
Qed.

(* ---- the cut at the call of __wrap_free (+240, ra = +244): the frame read back, a0 = scr, s2 = p2; the ledger at most
   own = 0 ---- *)
Definition caw_at_C (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k scr : Z) (u : PjTree.jv) (rest : list Z)
  (dl : Z) : Prop :=
  caw_carry (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  caw_prog D (caw_ev1 D) S3 /\
  getr regs3 1 = Z_to_bv 64 (caw_pc 244) /\ getr regs3 8 = w64 (cw_rc D) /\
  getr regs3 9 = w64 (cw_data D + cw_size D) /\ getr regs3 10 = w64 scr /\ getr regs3 18 = w64 (caw_p2 D rest) /\
  prhex_V 0 (cw_x D) = Some (u, rest) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 40) 4 dl /\ (dl = 0 \/ dl = 1) /\ (dl = 1 <-> cw_rc D = 0 /\ cw_t D <> u) /\
  caw_scr B D ly3 S3 scr /\
  caw_ledger B D ly3 S3 Hp3 W3 mem3 0.

(* ======== STAGE C: the call of __wrap_free (YGcallMxmnKeep.aj_free_x_ct_m_rh_keep at the cf instance: the free under
   the re-hide, with the memnorm keep), then stage A at RW ======== *)
Lemma caw_call : forall Q D fy ly3 S3 Hp3 W3 md k scr u rest dl E ss ms,
  st_ok (fx := fy) segs E ss (restrict (w_H W3) ms) -> ss_pc ss = SIGMA AS___wrap_free -> ss_resv ss = None ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 (- CAW_FRAME)) -> ew E 2 = Z_to_bv 64 (cw_sp0 D) ->
  caw_at_C D fy ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) md k scr u rest dl ->
  PresetHullBudget.hull_budget S3 [PresetReqAt.HFr (cw_size D + 1)] ->
  caw_k_OOMR (fx := fx) B SK CTX0 P RW Q D -> P (ms_mem ms) ->
  YA0nH.SRrG segs RW W3 (mkCfg ms md) (caw_QP P Q).
Proof.
intros Q D fy ly3 S3 Hp3 W3 md k scr u rest dl E ss ms HS Hpc Hrv Hsp2 E2 HC0 HHB HK HPM.
destruct HC0 as (HC & HRPa & R1 & R8 & R9 & R10 & R18 & HV & V40 & Hdl & Hdlu & Hscr & HPS).
pose proof HC as (Hpre & Hcnt & Hfl & HJ & Hkr & Hsp & HSV & EHp & HRL & HROD).
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as HFPRE. pose proof (caw_pre_univ (fx := fx) B CTX0 D Hpre) as HUNIV.
pose proof (caw_pre_rc (fx := fx) B CTX0 D Hpre) as Hrc. pose proof (caw_pre_size (fx := fx) B CTX0 D Hpre) as Hsz.
pose proof (caw_pre_data0 (fx := fx) B CTX0 D Hpre) as Hd0. pose proof (caw_pre_data62 (fx := fx) B CTX0 D Hpre) as Hd62.
pose proof HFPRE as (HAFN & _).
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold caw_J in HJ.
(* the journal read BY NAME (YCbqG's ajx_ projections), never positionally *)
pose proof (ajx_ar HJ) as HAR3. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_k HJ) as Hk0.
pose proof (ajx_qt HJ) as HQT3.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (HSTK : STK_check_as_written = 25712) by (vm_compute; reflexivity).
assert (Hsz0 : 0 <= cw_size D) by (unfold cw_size; lia).
pose proof (@pa_B_ok _ _ PA) as HBASE.
pose proof (cwi_base CWI) as EB.
assert (Hraw : caw_pc 244 = BASE + 2764) by (unfold caw_pc; rewrite CAW_OFF_val; lia).
pose proof Hscr as [Hs4 Eab3].
assert (Hscrb : In (scr, cw_size D + 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
assert (Hnew : ~ In (scr, cw_size D + 1) (ablocks B (cw_ly D) (cw_S D)))
  by exact (caw_scr_new D ly3 S3 Hp3 W3 (ms_mem ms) md scr HAR3 Hscr Hsz0).
assert (Hnhp : ~ In scr Hp3) by (rewrite EHp; exact (caw_scr_not_hp D ly3 S3 Hp3 W3 (ms_mem ms) md scr Hpre HAR3 Hscr)).
(* the class-24 count at the free's entry state: the entry's (caw_carry's caw_cnt D) plus the scratch *)
pose proof Hcnt as (_ & Hc0).
assert (Hc3 : YGcfRoomLive.ccnt24 S3 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1)
  by (pose proof (caw_ccnt24_app B (cw_ly D) (cw_S D) ly3 S3 _ Eab3) as X; clear - X Hc0; lia).
rewrite HSTK in Hslo.
set (sp0 := cw_sp0 D) in *.
assert (Esp0 : sp0 = spZ (cw_regs D)) by reflexivity.
assert (Rsp : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
assert (HspZ : spZ (ms_regs ms) = sp0 - 80) by (rewrite Hsp; unfold CAW_FRAME; lia).
assert (Hraz : raZ (ms_regs ms) = BASE + 2764) by (unfold raZ; rewrite R1, Hraw; apply unsigned_lit_small; lia).
(* the free's trace is a FIXED one of the universe (P'' set: the call rule asks `admits`, YG01.admits_fix, and its
   post carries the trace in the journal's wild budget, which ajournal_xw_fix1R drops again) *)
assert (HTRf : In (call_trace ly3 (pc_free_ra0 (as_code B)) (ms_regs ms) []) (as_universe B)).
{ apply caw_trace.
  + exact (proj1 HUNIV RT_free).
  + rewrite Hraz. exact (prh_univ_closure_lit B CTX0 F_check_as_written RT_free _ HUNIV (caw_site EB)). }
eapply (YA0nH.SRrG_bind segs RW (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)).
{ eapply (YGcallMxmnKeep.aj_free_x_ct_m_rh_keep (fx := fy) (SK := SK) segs B prh_pst LAWS (@pa_segs_low _ _ PA)
    (pal_env B PAL) (ARx_owned_low_law_xs segs B LAWS_cf) (ARx_wf_law_xs segs B)
    (alloc_model_laws_x_cf B (universe_ok_of_ARcf segs B _ _ _ _ _ _ (proj1 HAR3))) (AFREE fy)
    W3 E ss ms STK_check_as_written sp0 [] (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_md D) [] ly3 S3 Hp3 md k
    scr (cw_size D + 1) (- CAW_FRAME) (ew E 2) (Z_to_bv 64 (caw_pc 244)) [] HS).
  - rewrite Hpc. exact (pal_free B PAL).
  - exact Hrv.
  - apply (ajournal_xwR_mono (SK := SK) segs B prh_pst _ (@wle segs) RW (YA0nH.wle_wle' segs YGcfRehidePost.RZ_cf)).
    exact HJ.
  - exact Hscrb.
  - exact Hnhp.
  - exact R10.
  - exact Hsp2.
  - reflexivity.
  - rewrite E2. apply unsigned_lit_small. lia.
  - reflexivity.
  - unfold CAW_FRAME. lia.
  - rewrite HSTK. change ASTACK with 16384. unfold CAW_FRAME. lia.
  - rewrite (Hkr 3%bv ltac:(left; reflexivity)). exact Hgp.
  - rewrite (Hkr 4%bv ltac:(right; left; reflexivity)). exact Htp.
  - exact R1.
  - rewrite Hraw. apply (ret_ok_codeptr_v (L := A_prog_listing) (PI := PA)); [lia | reflexivity].
  - (* the call memory's QMm_cf: the room, cf_hull_ok from the cut's hull budget, arodata_ok_cf from the cut's reader
       form through the bridge at caw_img's relro rows *)
    destruct (QM_cf_of_room segs B ly3 S3 Hp3 W3 (ms_mem ms) md (proj1 HAR3) HQT3 (YGcfRoomLive.room_live_room S3 HRL)
      (PresetHullPay.hull_ok_of_budget _ _ HHB)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 _)))))).
    destruct (cwi_relro_eq CWI) as [ERL ERH].
    apply (YGcfAroBridge.arodata_ok_cf_of_P segs B W3 (ms_mem ms) (cwi_relro_seg CWI) (cwi_errno_relro CWI)
      (cwi_relro_top CWI) (cwi_ro_reads_nw CWI)).
    rewrite ERL, ERH. exact HROD.
  - apply (caw_chain _ _ _ (cw_rc D)); [rewrite Hraz, EB; unfold A_prog_base; lia | exact R8 | exact Hrc | rewrite HspZ; lia | rewrite Etop; lia].
  - exact (admits_fix _ _ _ (universe_ok_of_ARcf segs B _ _ _ _ _ _ (proj1 HAR3)) HTRf).
  - intros Hin. exfalso. exact (Hnew Hin). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Eab3' & Eab2) & Hfr2 & HPRE2
  & Htr2 & (q & trc & Hq & Hqin & Hpath & Hg & Hleaf) & Hkept & Hmn).
unfold acall_kept_x, acall_kept in Hkept. destruct Hkept as (K1 & K2 & K3 & K4 & K5 & K6).
(* the journal after the call: the fixed trace leaves the budget *)
pose proof (ajournal_xw_fix1R HTRf HJ2) as HJ2f. clear HJ2. rename HJ2f into HJ2.
assert (Eab0 : ablocks B ly2 S2 = ablocks B (cw_ly D) (cw_S D)).
{ rewrite Eab3 in Eab3'. destruct (caw_split_last _ _ _ _ Eab3' Hnew) as [-> ->]. rewrite Eab2, app_nil_r. reflexivity. }
assert (HPREcf := acall_pre_x_xs_cf segs B _ _ _ _ _ _ _ _ HPRE2).
assert (Hq0 : q <> PNull) by (intros E0; rewrite E0 in Hq; cbn in Hq; lia).
assert (KF : forall a, sp0 - 80 <= a < sp0 -> aview segs (w_H W2) mem2 a = aview segs (w_H W3) (ms_mem ms) a)
  by (intros a Ha; apply K1; [lia | change ASTACK with 16384; lia]).
apply (caw_after Q D fy ly2 S2 Hp3 W2 regs2 mem2 md2 (k + (st_nev S2 - st_nev S3)) u rest dl);
  [| exact HK | exact (PCALL _ _ Hmn HPM)].
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
- split; [exact Hpre|]. split; [exact Hcnt|]. split; [exact Hfl|]. split; [exact HJ2|].
  split; [exact (caw_kregs_pres D _ _ HP2 Hkr)|].
  split; [unfold spZ; rewrite (caw_pres_reg _ _ 2%bv HP2 ltac:(caw_cs)); exact Hsp|].
  split; [apply (caw_saved_kept D W3 (ms_mem ms)); [exact HSV | intros a Ha; apply KF; lia]|].
  split; [exact EHp|].
  split.
  { exact (YGcfRoomLive.RL_free_step segs B ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) md []
      (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1) q _ trc (tt, S2) HPREcf
      (conj Hc3 (proj2 (CfRoomLivePreset.preset_rl_b24_ok (cw_S D) Hc0))) HRL Hpath). }
  exact (caw_arod_kept W3 (ms_mem ms) W2 mem2 HROD K3).
- (* the free's event HFr (size + 1) after the scratch's malloc: caw_prog at caw_evs = caw_ev1 ++ [HFr (size + 1)]; the
     cut's caw_prog at caw_ev1 gives the position i + 1 at S3, the free moves it to S (i + 1) = i + 2 *)
  intros rsm rx ros ri rH0 rhist Hp0 Hrun.
  change (caw_evs D) with (caw_ev1 D ++ [PresetReqAt.HFr (cw_size D + 1)]) in Hrun.
  destruct (caw_run_at_app rsm rx ros ri _ _ Hrun) as (Hr1 & Hr2).
  destruct (HRPa rsm rx ros ri rH0 rhist Hp0 Hr1) as (hist & HRPos).
  pose proof (caw_run_at_nth rsm rx ros _ _ [] Hr2) as HEVfr.
  exists (hist ++ YGcfRoom.freed_cf S3 q).
  replace (ri + length (caw_evs D))%nat with (Datatypes.S (ri + length (caw_ev1 D)))
    by (unfold caw_evs, caw_ev1; cbn [length]; rewrite !(Nat.add_comm ri); reflexivity).
  exact (PresetRoomPosKeep.room_pos_keep_free segs B ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) md [] _ _ _ _ _ hist q
    (cw_size D + 1) _ trc S2 HPREcf Htr2 Hqin Hq0 Hpath HRPos HEVfr).
- rewrite (caw_pres_reg _ _ 8%bv HP2 ltac:(caw_cs)). exact R8.
- rewrite (caw_pres_reg _ _ 9%bv HP2 ltac:(caw_cs)). exact R9.
- rewrite (caw_pres_reg _ _ 18%bv HP2 ltac:(caw_cs)). exact R18.
- exact HV.
- apply (caw_val_mem_move _ _ _ _ _ V40). intros kk Hkk. apply (mbyte_of_aview segs). apply KF. lia.
- exact Hdl.
- exact Hdlu.
- exact Eab0.
- (* the cut's ledger at most own = 0: the statics (g_most and g_own_ran_out among them) image bytes off the owned
     statics and errno, kept by the free's image clause; the Lam heads in entry blocks apart from the scratch *)
  apply (caw_ledger_free D ly3 S3 Hp3 W3 (ms_mem ms) md ly2 S2 W2 mem2 scr 0 Hpre HAR3 Hscr HPS Eab0).
  + intros b m i Hb Hi Hn. exact (K2 b m i Hb Hi Hn).
  + exact K3.
Qed.


(* ======== helpers for the stages that end in a run: registers and bytes read off the run's end state ======== *)
Lemma caw_reg_off : forall (fz : YK11.FPState) (H : word -> bool) E ss ms (r : bv 5) n z v,
  st_ok_pi (fx := fz) segs VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n z ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 -> getr (ms_regs ms) r = Z_to_bv 64 (v + z).
Proof.
intros fz H E ss ms r n z v HS Hsr Hv Hv0 Hvz.
rewrite (st_ok_pi_restrict_reg (fx := fz) (L := A_prog_listing) (PI := PA) H E ss ms r HS), Hsr, denot_lit_U.
rewrite (U_atom_off E n v z Hv Hv0 Hvz). reflexivity.
Qed.
Lemma caw_reg_ok : forall (fz : YK11.FPState) (H : word -> bool) E ss ms (r : bv 5) n v,
  st_ok (fx := fz) segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = v ->
  getr (ms_regs ms) r = v.
Proof.
intros fz H E ss ms r n v HS Hsr Hv.
rewrite (st_ok_restrict_reg (fx := fz) segs H E ss ms r HS), Hsr.
cbn [sv_denot]. rewrite Hv, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma caw_kregs_st_ok : forall (fz : YK11.FPState) D (H : word -> bool) E ss ms regs sp0 vals,
  st_ok (fx := fz) segs E ss (restrict H ms) ->
  env_agree 32 (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = true ->
  caw_kregs D regs -> caw_kregs D (ms_regs ms).
Proof.
intros fz D H E ss ms regs sp0 vals HS HA Hl Hk r Hr.
assert (Hne : r <> 2%bv).
{ intros ->. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
pose proof (regs_kept_of_st_ok (fx := fz) segs E ss (restrict H ms) _ _ _ HS HA Hl r Hr) as X.
cbn [restrict ms_regs] in X. rewrite X. rewrite caw_getr_upd_other by exact Hne. exact (Hk r Hr).
Qed.
Lemma caw_sp_of_reg : forall regs E sp0, getr regs 2 = sv_denot E (SOff 2 (- CAW_FRAME)) -> ew E 2 = Z_to_bv 64 sp0 ->
  CAW_FRAME <= sp0 < 2 ^ 64 -> spZ regs = sp0 - CAW_FRAME.
Proof.
intros regs E sp0 Hr E2 Hsp. unfold spZ. rewrite Hr.
change (bv_unsigned (sv_denot E (SOff 2 (- CAW_FRAME)))) with (U E (SOff 2 (- CAW_FRAME))).
unfold CAW_FRAME in *. rewrite U_SOff, E2, unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* a byte the run did not write: the view is the old one *)
Lemma caw_aview_frame : forall E rs (H : word -> bool) m m' a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' a HF Ha Hw. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact Hw.
Qed.

(* ---- the cut at the loop's exit (+228, `sd a1, 8(sp)`): a1 = p2; the ledger at most own = 0 ---- *)
Definition caw_at_LX (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k scr : Z) (u : PjTree.jv) (rest : list Z)
  (dl : Z) : Prop :=
  caw_carry (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  caw_prog D (caw_ev1 D) S3 /\
  getr regs3 8 = w64 (cw_rc D) /\ getr regs3 9 = w64 (cw_data D + cw_size D) /\ getr regs3 11 = w64 (caw_p2 D rest) /\
  prhex_V 0 (cw_x D) = Some (u, rest) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 72) 8 (cw_data D + cw_size D - Z.of_nat (length rest)) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 48) 8 scr /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 40) 4 dl /\ (dl = 0 \/ dl = 1) /\ (dl = 1 <-> cw_rc D = 0 /\ cw_t D <> u) /\
  caw_scr B D ly3 S3 scr /\
  caw_ledger B D ly3 S3 Hp3 W3 mem3 0.

(* ======== STAGE LX (+228 -> the call +240): `sd a1, 8(sp); ld s2, 8(sp); ld a0, 32(sp); jal __wrap_free` ======== *)
Lemma caw_lx : forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl,
  caw_at_LX D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl ->
  PresetHullBudget.hull_budget S3 [PresetReqAt.HFr (cw_size D + 1)] ->
  caw_k_OOMR (fx := fx) B SK CTX0 P RW Q D -> P mem3 ->
  YA0nH.SRrG segs RW W3 (caw_cfg fy 228 regs3 mem3 md3) (caw_QP P Q).
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl HX HHB HK HPM.
destruct HX as (HC & HRPa & R8 & R9 & R11 & HV & V72 & V48 & V40 & Hdl & Hdlu & Hscr & HPS).
pose proof HC as (Hpre & Hcnt & Hfl & HJ & Hkr & Hsp & HSV & EHp & HRL & HROD).
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as HFPRE.
pose proof (caw_pre_rc (fx := fx) B CTX0 D Hpre) as Hrc. pose proof (caw_pre_size (fx := fx) B CTX0 D Hpre) as Hsz.
pose proof (caw_pre_data0 (fx := fx) B CTX0 D Hpre) as Hd0. pose proof (caw_pre_data62 (fx := fx) B CTX0 D Hpre) as Hd62.
pose proof HFPRE as (HAFN & _).
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold caw_J in HJ.
pose proof (ajx_ar HJ) as HAR3. pose proof (ajx_pres HJ) as Hpres3.
assert (HSTK : STK_check_as_written = 25712) by (vm_compute; reflexivity).
rewrite HSTK in Hslo, Hpres3.
pose proof (caw_V_len 0 (cw_x D) u rest HV) as Hrl.
pose proof (caw_skip_len rest) as Hsk.
assert (Hsz0 : 0 <= cw_size D) by (unfold cw_size; lia).
assert (Hp2 : cw_data D <= caw_p2 D rest <= cw_data D + cw_size D) by (unfold caw_p2, cw_size in *; lia).
pose proof Hscr as [Hs4 Eab3].
assert (Hscrb : In (scr, cw_size D + 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR3 Hscrb) as (_ & _ & Hscrc & _).
rewrite caw_req in Hscrc by lia.
destruct (caw_sp0_band D Hpre) as (_ & Hal16').
set (pold := cw_data D + cw_size D - Z.of_nat (length rest)) in *.
set (sp0 := cw_sp0 D) in *.
assert (Esp0 : sp0 = spZ (cw_regs D)) by reflexivity.
assert (Rsp : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
assert (HS : st_ok_pi (fx := fy) segs VAL (caw_Ee regs3 sp0 [pold; scr])
  (mkSS (CAW_OFF + 228) caw_sr80 [caw_fregion_e [(-72, 8%N); (-48, 8%N)] (-72) (-64)] None caw_G)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + 228))) mem3 (YK11.seg_rom segs)))).
{ apply (caw_st_ok_e (fz := fy)).
  - vm_compute. reflexivity.
  - cbn. lia.
  - exact Hsp.
  - unfold CAW_FRAME. lia.
  - intros o Ho. apply (apresent_writable segs). apply Hpres3. lia.
  - cbn [caw_vals_ok]. replace (sp0 + -72) with (sp0 - 72) by lia. replace (sp0 + -48) with (sp0 - 48) by lia.
    change (N.to_nat 8) with 8%nat. change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8.
    split; [exact V72|]. split; [unfold pold, cw_size in *; lia|]. split; [lia|].
    split; [exact V48|]. split; [lia|]. split; [lia | exact I].
  - unfold facts_ok, caw_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite caw_Ee_sp, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
set (E := caw_Ee regs3 sp0 [pold; scr]) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_Ee; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (E8 : ew E 8 = getr regs3 8) by (subst E; exact (caw_Ee_reg regs3 sp0 _ 8 8%bv eq_refl ltac:(discriminate))).
assert (E9 : ew E 9 = getr regs3 9) by (subst E; exact (caw_Ee_reg regs3 sp0 _ 9 9%bv eq_refl ltac:(discriminate))).
assert (E11 : ew E 11 = getr regs3 11) by (subst E; exact (caw_Ee_reg regs3 sp0 _ 11 11%bv eq_refl ltac:(discriminate))).
assert (E34 : ew E 34 = Z_to_bv 64 scr) by (subst E; exact (caw_Ee_val regs3 sp0 [pold; scr] 1 ltac:(lia))).
assert (E2 : ew E 2 = Z_to_bv 64 sp0) by (subst E; apply caw_Ee_sp).
assert (NW : forall a, ~ (sp0 - 72 <= a < sp0 - 64) ->
  ~ in_wrange E [caw_fregion_e [(-72, 8%N); (-48, 8%N)] (-72) (-64)] a).
{ intros a Ha (r & Hin & Hr). destruct Hin as [<- | []]. unfold caw_fregion_e in Hr.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E2, unsigned_lit_small in Hr by lia. lia. }
pose (RUN := paj_run_x_inv (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW).
apply caw_lift.
unfold caw_cfg, caw_pc. rewrite <- Z.add_assoc.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CAW_Bspan.
{ intros a (r & Hin & Hr). destruct Hin as [<- | []]. unfold caw_fregion_e in Hr.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E2, unsigned_lit_small in Hr by lia.
  left. rewrite HSTK. lia. }
(* at the call: memory changed only in [sp0 - 72, sp0 - 64) *)
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 72 <= a < sp0 - 64) ->
  aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem3 a)
  by (intros a Ha Hn; exact (caw_aview_frame E _ (w_H W3) mem3 (ms_mem ms) a HFr Ha (NW a Hn))).
assert (KI : forall a, in_img segs a -> aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem3 a).
{ intros a Ha. pose proof (@pa_segs_low _ _ PA a Ha) as Hlow. apply KV; lia. }
apply SRr_ret. cbv beta.
refine (caw_call Q D fy ly3 S3 Hp3 W3 _ k scr u rest dl E _ _ HS eq_refl eq_refl _ E2 _ HHB HK HPM).
{ rewrite (st_ok_restrict_reg (fx := fy) segs _ _ _ _ 2%bv HS). reflexivity. }
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]].
- split; [exact Hpre|]. split; [exact Hcnt|]. split; [exact Hfl|]. split; [exact HJ|].
  split; [exact (caw_kregs_st_ok fy D (w_H W3) E _ _ regs3 sp0 [pold; scr] HS (caw_Ee_agree regs3 sp0 [pold; scr])
    ltac:(vm_compute; reflexivity) Hkr)|].
  split.
  { apply (caw_sp_of_reg _ E sp0); [| exact E2 | unfold CAW_FRAME; lia].
    rewrite (st_ok_restrict_reg (fx := fy) segs _ _ _ _ 2%bv HS). reflexivity. }
  split; [apply (caw_saved_kept D W3 mem3); [exact HSV | intros a Ha; apply KV; lia]|].
  split; [exact EHp|]. split; [exact HRL|].
  exact (caw_arod_kept W3 mem3 W3 (ms_mem ms) HROD (fun a Ha _ _ => KI a Ha)).
- exact HRPa.
- rewrite (st_ok_restrict_reg (fx := fy) segs _ _ _ _ 1%bv HS).
  lazymatch goal with |- context [sr_get ?sr 1%bv] =>
    let t' := eval vm_compute in (sr_get sr 1%bv) in change (sr_get sr 1%bv) with t' end.
  etransitivity; [exact (codeptr_val (L := A_prog_listing) (PI := PA) E 2764 HEI)|]. unfold caw_pc. rewrite CAW_OFF_val.
  f_equal. lia.
- rewrite (caw_reg_ok fy (w_H W3) E _ _ 8%bv 8 _ HS eq_refl eq_refl), E8. exact R8.
- rewrite (caw_reg_ok fy (w_H W3) E _ _ 9%bv 9 _ HS eq_refl eq_refl), E9. exact R9.
- rewrite (caw_reg_ok fy (w_H W3) E _ _ 10%bv 34 _ HS eq_refl eq_refl), E34. reflexivity.
- rewrite (caw_reg_ok fy (w_H W3) E _ _ 18%bv 11 _ HS eq_refl eq_refl), E11. exact R11.
- exact HV.
- apply (caw_val_mem_move _ _ _ _ _ V40). intros kk Hkk. apply (mbyte_of_aview segs). apply KV; lia.
- exact Hdl.
- exact Hdlu.
- exact Hscr.
- (* the store `sd a1, 8(sp)` is a frame byte: every image byte (the prh_pst rows, g_most and g_own_ran_out among
     them) and every Lam head (in a block, below the frame) is kept, so the ledger at most own = 0 is *)
  unfold caw_ledger in HPS |- *.
  apply (prh_ledger_kept_aview B ly3 S3 Hp3 W3 mem3 ly3 S3 Hp3 W3 (ms_mem ms) _ _ _ _ _ _ _ HPS).
  + intros a Ha. exact (KI a (cwi_pst_img CWI a Ha)).
  + intros a kk i HinL Hi.
    pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HPS) as HF3.
    destruct (proj1 (Forall_forall _ _) HF3 _ HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hab, Hk0.
    change (@cf_head CfParams_preset) with 16 in *.
    destruct (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR3 Hab) as (_ & Hb4 & Hbc & _).
    rewrite caw_req in Hbc by lia. apply KV; lia.
  + intros a kk _ Hab. exact Hab.
  + apply Permutation_refl.
Qed.


(* ======== THE LOOP (+160 .. +224): the inlined ex_ws (fuzz_preset.c:103-107) with its ASan shadow test ======== *)
(* one turn's symbolic state at the loop head: every register its own atom, the byte at a1 = p the extra atom 32; the
   shadow base is s2 (atom 18, the engine's Bx), the cursor a0 (atom 10) *)
Definition caw_ssL : sstate :=
  mkSS (CAW_OFF + 160) sr_atoms [YP09.mkRegion (Some 11%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
    (mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)] [] []).
Definition caw_LE (regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs [Z_to_bv 64 c]).
Lemma caw_LE_reg : forall regs c n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  ew (caw_LE regs c) n = getr regs r.
Proof.
intros regs c n r Hn H32. unfold caw_LE. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma caw_LE_byte : forall regs c, ew (caw_LE regs c) 32 = Z_to_bv 64 c.
Proof.
intros regs c. unfold caw_LE. rewrite Eimg_low by (unfold A_TEXT; lia).
replace 32%nat with (32 + 0)%nat by lia. rewrite ew_Ereg_extra. reflexivity.
Qed.
Lemma caw_LE_ext : forall regs c w0 w1 n, (n < 512)%nat ->
  ew (ewset (ewset (caw_LE regs c) 512 w0) 513 w1) n = ew (caw_LE regs c) n.
Proof. intros regs c w0 w1 n Hn. rewrite !ew_ewset_other by lia. reflexivity. Qed.
Lemma caw_LE_agree : forall regs c w0 w1,
  env_agree 32 (Ereg regs [Z_to_bv 64 c]) (ewset (ewset (caw_LE regs c) 512 w0) 513 w1).
Proof.
intros regs c w0 w1. split; [|reflexivity].
intros i Hi. rewrite caw_LE_ext by lia. unfold caw_LE. apply Eimg_low. unfold A_TEXT. lia.
Qed.
(* the registers a turn leaves alone *)
Lemma caw_L_kept : forall (fz : YK11.FPState) (H : word -> bool) regs c w0 w1 ss ms (l : list (bv 5)),
  st_ok_pi (fx := fz) segs VAL (ewset (ewset (caw_LE regs c) 512 w0) 513 w1) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) l = true ->
  forall r, In r l -> getr (ms_regs ms) r = getr regs r.
Proof.
intros fz H regs c w0 w1 ss ms l HS Hl r Hr.
pose proof (regs_kept_of_st_ok_pi (fx := fz) (L := A_prog_listing) (PI := PA) _ ss (restrict H ms) regs
  [Z_to_bv 64 c] l HS (caw_LE_agree regs c w0 w1) Hl r Hr) as X.
cbn [restrict ms_regs] in X. exact X.
Qed.
Definition caw_LKEPT : list (bv 5) := [2; 3; 4; 8; 9; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Ltac caw_inl := unfold caw_LKEPT; cbn [In]; repeat (first [left; reflexivity | right]).
(* the turn's whitespace test: (mask >> c) & 1, for c <= 32 *)
Lemma caw_U_bit : forall E c, ew E 13 = Z_to_bv 64 CAW_WS_MASK -> ew E 32 = Z_to_bv 64 c -> 0 <= c <= 32 ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SOff 13 0) (SOff 32 0)) (SLit 1)) = if PjGrammar.ws c then 1 else 0.
Proof.
intros E c H13 H32 Hc.
assert (Hl : Z.land c 63 = c).
{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (Hb : 0 <= Z.shiftr CAW_WS_MASK c <= CAW_WS_MASK).
{ rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)) as Hp.
  split; [apply Z.div_pos; unfold CAW_WS_MASK; lia|]. apply Z.div_le_upper_bound; [lia|]. unfold CAW_WS_MASK. nia. }
assert (Ui : U E (SAlu ALU_SRL (SOff 13 0) (SOff 32 0)) = Z.shiftr CAW_WS_MASK c).
{ rewrite U_SAlu, (U_atom E 13 CAW_WS_MASK H13 ltac:(unfold CAW_WS_MASK; lia)), (U_atom E 32 c H32 ltac:(lia)).
  cbn [zalu_raw]. rewrite Hl. apply zcanon_id. unfold M64, CAW_WS_MASK in *. lia. }
rewrite U_SAlu, Ui, U_SLit. rewrite (zcanon_id 1) by (unfold M64; lia). cbn [zalu_raw].
rewrite caw_ws_mask by lia. destruct (PjGrammar.ws c); apply zcanon_id; unfold M64; lia.
Qed.

(* ---- the cut at the loop head (+160): a0 = a1 = p = data + j, every byte of [data + size - |rest|, p) whitespace; the
   ledger at most own = 0 ---- *)
Definition caw_at_L (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k scr : Z) (u : PjTree.jv) (rest : list Z)
  (dl j : Z) : Prop :=
  caw_carry (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  caw_prog D (caw_ev1 D) S3 /\
  getr regs3 8 = w64 (cw_rc D) /\ getr regs3 9 = w64 (cw_data D + cw_size D) /\ getr regs3 18 = w64 SHADOW_OFF /\
  getr regs3 10 = w64 (cw_data D + j) /\ getr regs3 11 = w64 (cw_data D + j) /\
  getr regs3 12 = w64 32 /\ getr regs3 13 = w64 CAW_WS_MASK /\
  prhex_V 0 (cw_x D) = Some (u, rest) /\ cw_size D - Z.of_nat (length rest) <= j < cw_size D /\
  PjGrammar.skip rest = PjGrammar.skip (skipn (Z.to_nat j) (cw_x D)) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 72) 8 (cw_data D + cw_size D - Z.of_nat (length rest)) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 48) 8 scr /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 40) 4 dl /\ (dl = 0 \/ dl = 1) /\ (dl = 1 <-> cw_rc D = 0 /\ cw_t D <> u) /\
  src_rd W3 mem3 (cw_data D) (cw_x D) /\ caw_scr B D ly3 S3 scr /\
  caw_ledger B D ly3 S3 Hp3 W3 mem3 0.

(* the LX cut from a turn's exit state: memory and allocator state the turn's entry's, a1 = p2 *)
Lemma caw_lx_of_turn : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl j regs' md' p,
  caw_at_L D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl j ->
  caw_J B SK D ly3 S3 Hp3 W3 mem3 md' k ->
  (forall r, In r caw_LKEPT -> getr regs' r = getr regs3 r) ->
  getr regs' 11 = w64 p -> p = caw_p2 D rest ->
  caw_at_LX D fy ly3 S3 Hp3 W3 regs' mem3 md' k scr u rest dl.
Proof.
intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl j regs' md' p HL0 HJ KP R11 ->.
destruct HL0 as (HC & HRPa & R8 & R9 & R18 & R10 & R11o & R12 & R13 & HV & Hj & Hskip & V72 & V48 & V40 & Hdl & Hdlu
  & HSRC & Hscr & HPS).
pose proof HC as (Hpre & Hcnt & Hfl & _ & Hkr & Hsp & HSV & EHp & HRL & HROD).
split; [|split; [exact HRPa|]].
- split; [exact Hpre|]. split; [exact Hcnt|]. split; [exact Hfl|]. split; [exact HJ|].
  split; [intros r Hr; rewrite (KP r); [exact (Hkr r Hr)|];
    cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [caw_inl|]); destruct Hr|].
  split; [unfold spZ; rewrite (KP 2%bv ltac:(caw_inl)); exact Hsp|].
  split; [exact HSV|]. split; [exact EHp|]. split; [exact HRL | exact HROD].
- split; [rewrite (KP 8%bv ltac:(caw_inl)); exact R8|].
  split; [rewrite (KP 9%bv ltac:(caw_inl)); exact R9|].
  split; [exact R11|]. split; [exact HV|]. split; [exact V72|]. split; [exact V48|]. split; [exact V40|].
  split; [exact Hdl|]. split; [exact Hdlu|]. split; [exact Hscr | exact HPS].
Qed.

(* the loop: induction on the bytes left (size - j); each turn reads the byte at p (its shadow test folded by the engine
   into the obligation `range_addressable SHADOW_OFF p 1`, discharged from src_rd: the report site +220 is never
   reached), then exits to +228 (a byte above 32, or not whitespace, or p + 1 = end) or goes round at p + 1 *)
Lemma caw_loop : forall n Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl j,
  (Z.to_nat (cw_size D - j) <= n)%nat ->
  caw_at_L D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl j ->
  PresetHullBudget.hull_budget S3 [PresetReqAt.HFr (cw_size D + 1)] ->
  caw_k_OOMR (fx := fx) B SK CTX0 P RW Q D -> P mem3 ->
  YA0nH.SRrG segs RW W3 (caw_cfg fy 160 regs3 mem3 md3) (caw_QP P Q).
Proof.
induction n as [|n IH]; intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl j Hn HL0 HHB HK HPM.
{ exfalso. destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _). lia. }
pose proof HL0 as HL1.
destruct HL0 as (HC & HRPa & R8 & R9 & R18 & R10 & R11 & R12 & R13 & HV & Hj & Hskip & V72 & V48 & V40 & Hdl & Hdlu
  & HSRC & Hscr & HPS).
pose proof HC as (Hpre & Hcnt & Hfl & HJ & Hkr & Hsp & HSV & EHp & HRL & HROD).
pose proof (caw_pre_rc (fx := fx) B CTX0 D Hpre) as Hrc. pose proof (caw_pre_size (fx := fx) B CTX0 D Hpre) as Hsz.
pose proof (caw_pre_data0 (fx := fx) B CTX0 D Hpre) as Hd0. pose proof (caw_pre_data62 (fx := fx) B CTX0 D Hpre) as Hd62.
pose proof HSRC as (HBY & Hd4096 & Hdceil & _ & HRA & _).
pose proof asan_consts as (C1 & _).
pose proof (caw_V_len 0 (cw_x D) u rest HV) as Hrl.
pose proof (caw_skip_len rest) as Hsk.
assert (Hjn : (Z.to_nat j < length (cw_x D))%nat) by (unfold cw_size in Hj; lia).
set (c := nth (Z.to_nat j) (cw_x D) 0).
destruct (HBY (Z.to_nat j) Hjn) as [HVc HRc]. fold c in HVc, HRc.
replace (cw_data D + Z.of_nat (Z.to_nat j)) with (cw_data D + j) in HVc by (unfold cw_size in *; lia).
assert (Hp : 4096 <= cw_data D + j < 2 ^ 47 - 1) by (unfold cw_size in *; lia).
set (E := caw_LE regs3 c).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew E n = getr regs3 r)
  by (intros n0 r Hn0 H32; subst E; exact (caw_LE_reg regs3 c n0 r Hn0 H32)).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; apply caw_LE_byte).
assert (U10 : U E (SOff 10 0) = cw_data D + j) by (apply U_atom; [rewrite (ER 10%nat 10%bv eq_refl ltac:(lia)); exact R10 | lia]).
assert (U11 : U E (SOff 11 0) = cw_data D + j) by (apply U_atom; [rewrite (ER 11%nat 11%bv eq_refl ltac:(lia)); exact R11 | lia]).
assert (U18 : U E (SOff 18 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (ER 18%nat 18%bv eq_refl ltac:(lia)); exact R18 | unfold SHADOW_OFF; lia]).
assert (U32 : U E (SOff 32 0) = c) by (apply U_atom; [exact E32 | lia]).
assert (HS : st_ok_pi (fx := fy) segs VAL E caw_ssL
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + 160))) mem3 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold caw_ssL. apply pa_entry_st_ok_full.
  - subst E. unfold caw_LE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (bv_unsigned (ew E 11)) with (U E (SOff 11 0)) || rewrite (ER 11%nat 11%bv eq_refl ltac:(lia)).
    rewrite ?U11.
    rewrite ?R11, ?unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (cw_data D + j) 0 1 (SOff 32 0) c).
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + rewrite Z.add_0_r. exact HVc.
  - exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok].
    split; [|split; [|split; [|exact I]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    + change (bv_unsigned (ew E 10)) with (U E (SOff 10 0)) || rewrite (ER 10%nat 10%bv eq_refl ltac:(lia)).
      rewrite ?U10, ?R10, ?unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    + change (bv_unsigned (ew E 18)) with (U E (SOff 18 0)) || rewrite (ER 18%nat 18%bv eq_refl ltac:(lia)).
      rewrite ?U18, ?R18, ?unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.pow_0_r, Z.mod_1_r.
      unfold SHADOW_OFF; lia.
    + rewrite E32, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_LE; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 18 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := paj_run_x_inv (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW).
pose (BR := paj_branch (fx := fy) (L := A_prog_listing) (PI := PA)).
assert (EXIT : forall regs' md' p, caw_J B SK D ly3 S3 Hp3 W3 mem3 md' k ->
  (forall r, In r caw_LKEPT -> getr regs' r = getr regs3 r) -> getr regs' 11 = w64 p -> p = caw_p2 D rest ->
  P mem3 -> YA0nH.SRrG segs RW W3 (caw_cfg fy 228 regs' mem3 md') (caw_QP P Q)).
{ intros regs' md' p HJ' KP R11' Ep HPM'.
  exact (caw_lx Q D fy ly3 S3 Hp3 W3 regs' mem3 md' k scr u rest dl
    (caw_lx_of_turn D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl j regs' md' p HL1 HJ' KP R11' Ep) HHB HK HPM'). }
apply caw_lift.
unfold caw_cfg, caw_pc. rewrite <- Z.add_assoc.
unfold caw_J in HJ.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CAW_Bspan.
- (* THE REPORT SITE +220 REFUTED: the turn's one obligation, the shadow of its byte p, from src_rd *)
  cbn [ms_mem mkst]. rewrite U18, U10. eapply range_addressable_sub; [exact HRA | unfold cw_size in *; lia | unfold cw_size in *; lia].
- caw_nowr.
- caw_ro0 HF HFr HG EM.
  set (E' := ewset (ewset E 512 w) 513 w0) in *.
  assert (EE : forall n, (n < 512)%nat -> ew E' n = ew E n) by (intros n0 Hn0; subst E'; rewrite !ew_ewset_other by lia; reflexivity).
  assert (U12' : U E' (SOff 12 0) = 32) by (apply U_atom; [rewrite EE, (ER 12%nat 12%bv eq_refl) by lia; exact R12 | lia]).
  assert (U32' : U E' (SOff 32 0) = c) by (apply U_atom; [rewrite EE by lia; exact E32 | lia]).
  (* +180 `bltu a2, a4`: 32 < c, not whitespace *)
  psrr_branch_tok RUN BR HS SHOK CAW_Bspan.
  + rewrite branch_ltu_U, U12', U32' in Hc. apply Z.ltb_lt in Hc.
    pose proof (caw_ws_big c Hc) as Hws.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CAW_Bspan (CAW_OFF + 228).
    { caw_nowr. }
    caw_ro HF HFr HG EM.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
      pmkst HS;
      replace (BASE + 2748) with (caw_pc 228) by (unfold caw_pc; rewrite CAW_OFF_val; lia);
      rewrite EM in HJ, HPM |- *;
      apply SRr_ret; cbv beta;
      apply (EXIT (ms_regs m) d (cw_data D + j) HJ);
      [ exact (caw_L_kept fy (w_H W3) regs3 c w w0 _ _ caw_LKEPT HS ltac:(vm_compute; reflexivity))
      | rewrite (caw_reg_off fy (w_H W3) E' _ _ 11%bv 11 0 (cw_data D + j) HS eq_refl
          ltac:(rewrite EE, (ER 11%nat 11%bv eq_refl) by lia; exact R11) ltac:(lia) ltac:(lia)), Z.add_0_r;
        reflexivity
      | unfold caw_p2; rewrite Hskip, (caw_skip_cons _ _ Hjn); fold c; rewrite Hws, length_skipn; unfold cw_size in *; lia
      | exact HPM ]
    end.
  + rewrite branch_ltu_U, U12', U32' in Hc. apply Z.ltb_ge in Hc.
    assert (Hc32 : 0 <= c <= 32) by lia. clear Hc.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM CAW_Bspan.
    { caw_nowr. }
    caw_ro HF HFr HG EM.
    assert (Ubit : U E' (SAlu ALU_AND (SAlu ALU_SRL (SOff 13 0) (SOff 32 0)) (SLit 1)) = if PjGrammar.ws c then 1 else 0).
    { apply caw_U_bit; [rewrite EE, (ER 13%nat 13%bv eq_refl) by lia; exact R13 | rewrite EE by lia; exact E32 | exact Hc32]. }
    (* +192 `beqz a4`: c is not whitespace *)
    psrr_branch_tok RUN BR HS SHOK CAW_Bspan.
    * rewrite branch_eq_U, Ubit, U_SLit in Hc. apply Z.eqb_eq in Hc.
      assert (Hws : PjGrammar.ws c = false) by (destruct (PjGrammar.ws c); [vm_compute in Hc; discriminate | reflexivity]).
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CAW_Bspan (CAW_OFF + 228).
      { caw_nowr. }
      caw_ro HF HFr HG EM.
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
        pmkst HS;
        replace (BASE + 2748) with (caw_pc 228) by (unfold caw_pc; rewrite CAW_OFF_val; lia);
        rewrite EM in HJ, HPM |- *;
        apply SRr_ret; cbv beta;
        apply (EXIT (ms_regs m) d (cw_data D + j) HJ);
        [ exact (caw_L_kept fy (w_H W3) regs3 c w w0 _ _ caw_LKEPT HS ltac:(vm_compute; reflexivity))
        | rewrite (caw_reg_off fy (w_H W3) E' _ _ 11%bv 11 0 (cw_data D + j) HS eq_refl
            ltac:(rewrite EE, (ER 11%nat 11%bv eq_refl) by lia; exact R11) ltac:(lia) ltac:(lia)), Z.add_0_r;
          reflexivity
        | unfold caw_p2; rewrite Hskip, (caw_skip_cons _ _ Hjn); fold c; rewrite Hws, length_skipn; unfold cw_size in *; lia
        | exact HPM ]
      end.
    * rewrite branch_eq_U, Ubit, U_SLit in Hc. apply Z.eqb_neq in Hc.
      assert (Hws : PjGrammar.ws c = true) by (destruct (PjGrammar.ws c); [reflexivity | exfalso; apply Hc; reflexivity]).
      clear Hc.
      assert (Hskip' : PjGrammar.skip rest = PjGrammar.skip (skipn (S (Z.to_nat j)) (cw_x D)))
        by (rewrite Hskip, (caw_skip_cons _ _ Hjn); fold c; rewrite Hws; reflexivity).
      paj_run_tok_x_inv RUN HS HJ SHOK HPM CAW_Bspan.
      { caw_nowr. }
      caw_ro HF HFr HG EM.
      assert (U11p : U E' (SOff 11 1) = cw_data D + j + 1)
        by (apply U_atom_off; [rewrite EE, (ER 11%nat 11%bv eq_refl) by lia; exact R11 | lia | lia]).
      assert (U9' : U E' (SOff 9 0) = cw_data D + cw_size D)
        by (apply U_atom; [rewrite EE, (ER 9%nat 9%bv eq_refl) by lia; exact R9 | unfold cw_size in *; lia]).
      (* +204 `bne a1, s1`: p + 1 <> end, round again *)
      psrr_branch_tok RUN BR HS SHOK CAW_Bspan.
      -- rewrite branch_ne_U, U11p, U9' in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CAW_Bspan (CAW_OFF + 160).
         { caw_nowr. }
         caw_ro HF HFr HG EM.
         lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
           pmkst HS;
           replace (BASE + 2680) with (caw_pc 160) by (unfold caw_pc; rewrite CAW_OFF_val; lia);
           rewrite EM in HJ, HPM |- *;
           pose proof (caw_L_kept fy (w_H W3) regs3 c w w0 _ _ caw_LKEPT HS ltac:(vm_compute; reflexivity)) as KP;
           apply SRr_ret; cbv beta;
           refine (IH Q D fy ly3 S3 Hp3 W3 (ms_regs m) mem3 d k scr u rest dl (j + 1) _ _ HHB HK HPM)
         end.
         { unfold cw_size in *. lia. }
         split; [|split; [exact HRPa|]].
         { split; [exact Hpre|]. split; [exact Hcnt|]. split; [exact Hfl|]. split; [exact HJ|].
           split; [intros r Hr; rewrite (KP r); [exact (Hkr r Hr)|];
             cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [caw_inl|]); destruct Hr|].
           split; [unfold spZ; rewrite (KP 2%bv ltac:(caw_inl)); exact Hsp|].
           split; [exact HSV|]. split; [exact EHp|]. split; [exact HRL | exact HROD]. }
         split; [rewrite (KP 8%bv ltac:(caw_inl)); exact R8|].
         split; [rewrite (KP 9%bv ltac:(caw_inl)); exact R9|].
         split; [rewrite (KP 18%bv ltac:(caw_inl)); exact R18|].
         split.
         { rewrite (caw_reg_off fy (w_H W3) E' _ _ 10%bv 10 1 (cw_data D + j) HS eq_refl
             ltac:(rewrite EE, (ER 10%nat 10%bv eq_refl) by lia; exact R10) ltac:(lia) ltac:(lia)).
           unfold w64. f_equal. lia. }
         split.
         { rewrite (caw_reg_off fy (w_H W3) E' _ _ 11%bv 11 1 (cw_data D + j) HS eq_refl
             ltac:(rewrite EE, (ER 11%nat 11%bv eq_refl) by lia; exact R11) ltac:(lia) ltac:(lia)).
           unfold w64. f_equal. lia. }
         split; [rewrite (KP 12%bv ltac:(caw_inl)); exact R12|].
         split; [rewrite (KP 13%bv ltac:(caw_inl)); exact R13|].
         split; [exact HV|]. split; [unfold cw_size in *; lia|].
         split; [rewrite Hskip'; f_equal; f_equal; unfold cw_size in *; lia|].
         split; [exact V72|]. split; [exact V48|]. split; [exact V40|]. split; [exact Hdl|]. split; [exact Hdlu|].
         split; [exact HSRC|]. split; [exact Hscr | exact HPS].
      -- (* p + 1 = end: `j +224`, `mv a1, s1`: p2 = end *)
         rewrite branch_ne_U, U11p, U9' in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CAW_Bspan (CAW_OFF + 228).
         { caw_nowr. }
         caw_ro HF HFr HG EM.
         lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
           pmkst HS;
           replace (BASE + 2748) with (caw_pc 228) by (unfold caw_pc; rewrite CAW_OFF_val; lia);
           rewrite EM in HJ, HPM |- *;
           apply SRr_ret; cbv beta;
           apply (EXIT (ms_regs m) d (cw_data D + cw_size D) HJ);
           [ exact (caw_L_kept fy (w_H W3) regs3 c w w0 _ _ caw_LKEPT HS ltac:(vm_compute; reflexivity))
           | rewrite (caw_reg_off fy (w_H W3) E' _ _ 11%bv 9 0 (cw_data D + cw_size D) HS eq_refl
               ltac:(rewrite EE, (ER 9%nat 9%bv eq_refl) by lia; exact R9) ltac:(unfold cw_size in *; lia)
               ltac:(unfold cw_size in *; lia)), Z.add_0_r;
             reflexivity
           | unfold caw_p2; rewrite Hskip';
             replace (S (Z.to_nat j)) with (length (cw_x D)) by (unfold cw_size in *; lia);
             rewrite caw_skip_end; cbn [length Z.of_nat]; lia
           | exact HPM ]
         end.
Qed.


(* ======== STAGE R (+128 -> the loop head +160 / the call +240), and THE SEGMENT (at RW: it frees the scratch) ======== *)
Lemma caw_wa3_holds : caw_seg_WA3R (fx := fx) B SK CTX0 P RW.
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl HR HK HPM.
destruct HR as (HC & HRPa & R8 & R9 & R18 & HV & V72 & V64 & V48 & V40 & Hdl & Hdlu & HSRC & Hscr & HPS & HHB).
pose proof HC as (Hpre & Hcnt & Hfl & HJ & Hkr & Hsp & HSV & EHp & HRL & HROD).
pose proof (caw_pre_rc (fx := fx) B CTX0 D Hpre) as Hrc. pose proof (caw_pre_size (fx := fx) B CTX0 D Hpre) as Hsz.
pose proof (caw_pre_data0 (fx := fx) B CTX0 D Hpre) as Hd0. pose proof (caw_pre_data62 (fx := fx) B CTX0 D Hpre) as Hd62.
pose proof asan_consts as (C1 & _).
pose proof (caw_V_len 0 (cw_x D) u rest HV) as Hrl.
pose proof (caw_V_suffix 0 (cw_x D) u rest HV) as Hsfx.
assert (Hsz0 : 0 <= cw_size D) by (unfold cw_size; lia).
pose proof Hscr as [Hs4 Eab3].
unfold caw_J in HJ.
pose proof (ajx_ar HJ) as HAR3.
assert (Hscrb : In (scr, cw_size D + 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR3 Hscrb) as (_ & _ & Hscrc & _).
rewrite caw_req in Hscrc by lia.
destruct (caw_sp0_band D Hpre) as (Rsp & Hal16).
set (pold := cw_data D + cw_size D - Z.of_nat (length rest)) in *.
set (pend := cw_data D + cw_size D) in *.
set (sp0 := cw_sp0 D) in *.
assert (HS : st_ok_pi (fx := fy) segs VAL (caw_Ee regs3 sp0 [pold; pend; scr])
  (mkSS (CAW_OFF + 128) caw_sr80 [caw_fregion_e [(-72, 8%N); (-64, 8%N); (-48, 8%N)] 0 0] None caw_G)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + 128))) mem3 (YK11.seg_rom segs)))).
{ apply (caw_st_ok_e (fz := fy)).
  - vm_compute. reflexivity.
  - cbn. lia.
  - exact Hsp.
  - unfold CAW_FRAME. lia.
  - intros o Ho. lia.
  - cbn [caw_vals_ok]. replace (sp0 + -72) with (sp0 - 72) by lia. replace (sp0 + -64) with (sp0 - 64) by lia.
    replace (sp0 + -48) with (sp0 - 48) by lia.
    change (N.to_nat 8) with 8%nat. change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8.
    split; [exact V72|]. split; [unfold pold, pend, cw_size in *; lia|]. split; [lia|].
    split; [exact V64|]. split; [unfold pend, cw_size in *; lia|]. split; [lia|].
    split; [exact V48|]. split; [lia|]. split; [lia | exact I].
  - unfold facts_ok, caw_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite caw_Ee_sp, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
set (E := caw_Ee regs3 sp0 [pold; pend; scr]) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_Ee; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (E8 : ew E 8 = getr regs3 8) by (subst E; exact (caw_Ee_reg regs3 sp0 _ 8 8%bv eq_refl ltac:(discriminate))).
assert (E18 : ew E 18 = getr regs3 18) by (subst E; exact (caw_Ee_reg regs3 sp0 _ 18 18%bv eq_refl ltac:(discriminate))).
assert (E33 : ew E 33 = Z_to_bv 64 pold) by (subst E; exact (caw_Ee_val regs3 sp0 [pold; pend; scr] 0 ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 pend) by (subst E; exact (caw_Ee_val regs3 sp0 [pold; pend; scr] 1 ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 scr) by (subst E; exact (caw_Ee_val regs3 sp0 [pold; pend; scr] 2 ltac:(lia))).
assert (E2 : ew E 2 = Z_to_bv 64 sp0) by (subst E; apply caw_Ee_sp).
assert (U33 : U E (SOff 33 0) = pold) by (apply U_atom; [exact E33 | unfold pold, pend, cw_size in *; lia]).
assert (U34 : U E (SOff 34 0) = pend) by (apply U_atom; [exact E34 | unfold pend, cw_size in *; lia]).
pose (RUN := paj_run_x_inv (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW).
pose (BR := paj_branch (fx := fy) (L := A_prog_listing) (PI := PA)).
apply caw_lift.
unfold caw_cfg, caw_pc. rewrite <- Z.add_assoc.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CAW_Bspan.
{ caw_nowr. }
caw_ro0 HF HFr HG EM.
(* +136 `bgeu a1, s1`: p >= end, the value read the whole text (rest = []) *)
psrr_branch_tok RUN BR HS SHOK CAW_Bspan.
- rewrite branch_geu_U, U33, U34 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Er : rest = []) by (destruct rest as [|b r]; [reflexivity | unfold pold, pend in Hc; cbn [length] in Hc; lia]).
  clear Hc. subst rest.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM CAW_Bspan.
  { caw_nowr. }
  caw_ro HF HFr HG EM.
  apply SRr_ret. cbv beta.
  refine (caw_call Q D fy ly3 S3 Hp3 W3 _ k scr u [] dl E _ _ HS eq_refl eq_refl _ E2 _ HHB HK HPM).
  { rewrite (st_ok_restrict_reg (fx := fy) segs _ _ _ _ 2%bv HS). reflexivity. }
  rewrite EM in HJ |- *.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]].
  + split; [exact Hpre|]. split; [exact Hcnt|]. split; [exact Hfl|]. split; [exact HJ|].
    split; [exact (caw_kregs_st_ok fy D (w_H W3) E _ _ regs3 sp0 [pold; pend; scr] HS
      (caw_Ee_agree regs3 sp0 [pold; pend; scr]) ltac:(vm_compute; reflexivity) Hkr)|].
    split.
    { apply (caw_sp_of_reg _ E sp0); [| exact E2 | unfold CAW_FRAME; lia].
      rewrite (st_ok_restrict_reg (fx := fy) segs _ _ _ _ 2%bv HS). reflexivity. }
    split; [exact HSV|]. split; [exact EHp|]. split; [exact HRL | exact HROD].
  + exact HRPa.
  + rewrite (st_ok_restrict_reg (fx := fy) segs _ _ _ _ 1%bv HS).
    lazymatch goal with |- context [sr_get ?sr 1%bv] =>
      let t' := eval vm_compute in (sr_get sr 1%bv) in change (sr_get sr 1%bv) with t' end.
    etransitivity; [exact (codeptr_val (L := A_prog_listing) (PI := PA) E 2764 HEI)|]. unfold caw_pc. rewrite CAW_OFF_val.
    f_equal. lia.
  + rewrite (caw_reg_ok fy (w_H W3) E _ _ 8%bv 8 _ HS eq_refl eq_refl), E8. exact R8.
  + rewrite (caw_reg_ok fy (w_H W3) E _ _ 9%bv 34 _ HS eq_refl eq_refl), E34. reflexivity.
  + rewrite (caw_reg_ok fy (w_H W3) E _ _ 10%bv 35 _ HS eq_refl eq_refl), E35. reflexivity.
  + rewrite (caw_reg_ok fy (w_H W3) E _ _ 18%bv 33 _ HS eq_refl eq_refl), E33. reflexivity.
  + exact HV.
  + exact V40.
  + exact Hdl.
  + exact Hdlu.
  + exact Hscr.
  + exact HPS.
- (* p < end: `li a2, 32`, the mask, `mv a0, a1`, to the loop head +160 at j = size - |rest| *)
  rewrite branch_geu_U, U33, U34 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hr0 : (0 < length rest)%nat) by (unfold pold, pend in Hc; lia). clear Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CAW_Bspan (CAW_OFF + 160).
  { caw_nowr. }
  caw_ro HF HFr HG EM.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
    pmkst HS;
    replace (BASE + 2680) with (caw_pc 160) by (unfold caw_pc; rewrite CAW_OFF_val; lia);
    rewrite EM in HJ, HPM |- *;
    apply SRr_ret; cbv beta;
    refine (caw_loop _ Q D fy ly3 S3 Hp3 W3 (ms_regs m) mem3 d k scr u rest dl (cw_size D - Z.of_nat (length rest))
      (Nat.le_refl _) _ HHB HK HPM)
  end.
  split; [|split; [exact HRPa|]].
  { split; [exact Hpre|]. split; [exact Hcnt|]. split; [exact Hfl|]. split; [exact HJ|].
    split; [exact (caw_kregs_st fy D (w_H W3) E _ _ regs3 sp0 [pold; pend; scr] HS
      (caw_Ee_agree regs3 sp0 [pold; pend; scr]) ltac:(vm_compute; reflexivity) Hkr)|].
    split; [apply (caw_sp_st (fz := fy) (w_H W3) E _ _ sp0 HS eq_refl E2); unfold CAW_FRAME; lia|].
    split; [exact HSV|]. split; [exact EHp|]. split; [exact HRL | exact HROD]. }
  split; [rewrite (caw_reg_st (fz := fy) (w_H W3) E _ _ 8%bv 8 _ HS eq_refl eq_refl), E8; exact R8|].
  split; [rewrite (caw_reg_st (fz := fy) (w_H W3) E _ _ 9%bv 34 _ HS eq_refl eq_refl), E34; reflexivity|].
  split; [rewrite (caw_reg_st (fz := fy) (w_H W3) E _ _ 18%bv 18 _ HS eq_refl eq_refl), E18; exact R18|].
  split; [rewrite (caw_reg_st (fz := fy) (w_H W3) E _ _ 10%bv 33 _ HS eq_refl eq_refl), E33;
    unfold w64; f_equal; unfold pold, pend; lia|].
  split; [rewrite (caw_reg_st (fz := fy) (w_H W3) E _ _ 11%bv 33 _ HS eq_refl eq_refl), E33;
    unfold w64; f_equal; unfold pold, pend; lia|].
  split; [rewrite (st_ok_pi_restrict_reg (fx := fy) _ _ _ _ 12%bv HS);
    lazymatch goal with |- context [sr_get ?sr 12%bv] =>
      let t' := eval vm_compute in (sr_get sr 12%bv) in change (sr_get sr 12%bv) with t' end; reflexivity|].
  split; [rewrite (st_ok_pi_restrict_reg (fx := fy) _ _ _ _ 13%bv HS);
    lazymatch goal with |- context [sr_get ?sr 13%bv] =>
      let t' := eval vm_compute in (sr_get sr 13%bv) in change (sr_get sr 13%bv) with t' end; reflexivity|].
  split; [exact HV|]. split; [unfold cw_size in *; lia|].
  split.
  { replace (Z.to_nat (cw_size D - Z.of_nat (length rest))) with (length (cw_x D) - length rest)%nat
      by (unfold cw_size; lia).
    rewrite Hsfx. reflexivity. }
  split; [exact V72|]. split; [exact V48|]. split; [exact V40|]. split; [exact Hdl|]. split; [exact Hdlu|].
  split; [exact HSRC|]. split; [exact Hscr | exact HPS].
Qed.

End wa3.

Check caw_wa3_holds.
Print Assumptions caw_wa3_holds.

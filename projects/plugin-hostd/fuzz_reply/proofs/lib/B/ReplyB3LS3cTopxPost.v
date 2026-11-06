(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v, with its module paths and module names changed; 485 of its 594 lines of code are new or changed and 1118 lines of the source are left out. *)
(* The image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3cTopxPost.v at
   1318828167d3 (sha256 d082a8478f54; internal record), row G-BLS-drain:
   the same texts and lemmas under the same names over lib/B's records.
   proves no function (kind: invariant lemma).
   PORTED: tx_rm_rr_cost, tx_rm_cnl_cost and the six texts of Section tx (TX_LS_event_step, TX_LS_drain_step,
   TX_LS_cnl_pre, TX_LS_rm_cnl_pre, TX_LS_exit_end, TX_LS_exit_end_d), word for word apart from the swaps below, with
   A's Section variables in A's order; every plug of A's file: tx_LS_event_step_plug, tx_LS_drain_step_plug,
   tx_LS_cnl_pre_plug, tx_LS_rm_cnl_pre_plug (at LSx := lib/B/ReplyB3LS3c.v fr_LS3c B CALL_ROOM_B, from
   lib/B/ReplyB3LS3cArms.v / ReplyB3LS3Arms.v), tx_LSo, tx_LS_exit_end_d_plug (lib/B/ReplyB3LS3o.v LS_exit_end3_x,
   fr_live_post3), tx_LS_event_step_plug_o (fr_OUT's event rule is lib/B/ReplyLSBo.v fr_OUT_event_step_b: A's
   fr_OUT_event_step_p without its unused fr_LS3 premise, with `131072 <= OM`, from bo_OUT_MAX4_ev and OUT_MAX4 <= OM),
   tx_LS_cnl_pre_plug_o, tx_LS_rm_cnl_pre_plug_o; and all of Section vac, incl. tx_two_events_escapes (at
   CALL_ROOM_B := YCfn_cf.CALL_ROOM_B).  Every plug takes `YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B` first.
   The plugs are stated at B top_x's own texts (lib/B/W_LLVMFuzzerTestOneInput_top_x.v; the B cutover's re-point,
   a Theorem Labs lane 10:58Z), which now include TX_LS_cnl_pre's sixth conjunct `AREC * capb (hs_held h'') (hs_expected h'') <
   2 ^ 32`; tx_LS_exit_end_d_plug keeps A's TX_LS_exit_end_d text written out (see its comment).
   KF-COUNT B step 3 (a Theorem Labs lane 09:35Z / 10:31Z; s5-r1d's KF-METER-PATTERN): the plugs are generic in an implicit
   meter {MT : ameter_ops} (per-lemma binder; Section vac stays at ameter_triv).  tx_LS_event_step_plug,
   tx_LS_drain_step_plug and tx_LS_event_step_plug_o are generic under their own names (their texts have no meter
   conjunct).  Each plug whose text ends in a meter conjunct has a generic version without it, and keeps its name at
   ameter_triv as a corollary that supplies the conjunct by I: tx_LS_cnl_pre_plug_m -> tx_LS_cnl_pre_plug,
   tx_LS_rm_cnl_pre_plug_m -> tx_LS_rm_cnl_pre_plug, tx_LS_exit_end_d_plug_m -> tx_LS_exit_end_d_plug (its mo_le
   XN_LIB conclusion), tx_LS_cnl_pre_plug_o_m -> tx_LS_cnl_pre_plug_o, tx_LS_rm_cnl_pre_plug_o_m ->
   tx_LS_rm_cnl_pre_plug_o.
   A -> B SWAPS (as lib/B/ReplyB3LS3Arms.v's header lists them):
   - lib/A AB1v -> lib/B YB1v; Reusable YE01 + lib/A AE2k -> lib/B YE01 YE2k; lib/A ACfn -> lib/B YCfn (Required only:
     A's LLVMF_STK is YCfn.LLVMF_STK, as lib/B/W_LLVMFuzzerTestOneInput_top_x.v:381); lib/A W_* -> lib/B W_* (W_rep,
     W_contract, W_sites, W_frame, _cut, _cut_x, W_journal_x), then ReplyGuardB; the drain arm's model (dr_pick, dr_e0,
     dr_step, dr_k', dr_at_op) from lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v;
   - lib/A W_LLVMFuzzerTestOneInput_exit's lx_exit_cost / lx_rf_run -> lib/B/W_bx_defs.v :273 / :154 (Required only,
     cited qualified as B's top_x does; the texts are A's);
   - A's lib/A/ReplyRINV.v copies ev_evt / ev_step / rm_at -> lib/B/ReplyLSBArms.v's copies; rm_rr_ok / rm_mk ->
     lib/B/ReplyB3LS3Arms.v Section rm_copies; rm_rr_tr -> ReplyLSBArms.v's copy; fr_RINV -> lib/B/ReplyRINVB.v;
   - lib/A ReplyLSDrain3 / ReplyLS3Arms (dr3_epre, dr3_hpre, dr3_epost, dr3_hpost, ls3_kh, ls3_hn, ls3_dpost,
     ls3_cpost, fr_LS3_cnl_pre_p, fr_LS3_rm_cnl_pre_p) -> lib/B/ReplyB3LS3Arms.v; ReplyLS3 (ls3_cx, ls3_m, ls3_ly, ls3_S)
     -> lib/B/ReplyB3LS3.v; ReplyLS3c / ReplyLSCntL -> lib/B/ReplyB3LS3c.v / ReplyB3LSCntL.v; ReplyLS3o's fr_OUT ->
     lib/B/ReplyLSBo.v fr_OUT (Required only, cited qualified);
   - ACfn_cf.CALL_ROOM (2 ^ 33) -> the Section variable CALL_ROOM_B (lib/B/ReplyLSB.v's ruling).  The plugs whose B
     lemmas read the room take lib/B/ReplyB3LS3.v's premise `YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B` first; tx_sat7 is at
     CALL_ROOM_B := YCfn_cf.CALL_ROOM_B (2 ^ 33, A's value), as lib/B/ReplyB3LS3.v fr_LS3_sat;
   - CfParamsReply.fr_MMAX stays lib/A/CfParamsReply.v's (lib/B/ReplyB3LS3Arms.v's MMAX, the one B's top_x states).
   A's header follows, its plug list replaced by the one above. *)
(* top_x's five free-post-state LS rules in the restated texts top_x adopts (a Theorem Labs lane's ruling after a Theorem Labs lane's
   vacuity finding, a working branch 2a368424fed lib/A/TopxVacuity.v topx_two_events_false),
   in top_x's FAMILY form: each TX_<row> is top_x's Hypothesis text over top_x's Variables, with ONLY the premises
   B1c's proved restatement adds, appended after top_x's premises, and top_x's own conclusion.
   - Argument order after the Section (the Variables each text uses, in declaration order):
       TX_LS_event_step TfibB MT LSx;  TX_LS_drain_step / TX_LS_cnl_pre / TX_LS_rm_cnl_pre TfibB MT LSx RINV;
       TX_LS_exit_end TfibB MT XN_LIB fr_live_post fr_surv NP fr_FP LSx ARX G (and {SK : sink_head});
       TX_LS_exit_end_d the same without NP.
     top_x fixes ARX (its Definition) and G (G_fr_c TfibB); here they are Variables, instantiated by W8.
   - The drain rows name B1c's predicates dr3_epre / dr3_hpre / dr3_epost / dr3_hpost and ls3_kh / ls3_hn / ls3_dpost /
     ls3_cpost: W8 copies their texts with the rows. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_bx_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT drain_b_c send_line_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv
  SlotDrain3Aux SlotPass2Aux relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3Base ReplyB3LS3 ReplyB3LSCntL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3c ReplyB3LS3Arms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLSBo.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3LS3o.
Import ListNotations.
(* the remove arm notions lib/B/ReplyLSBArms.v copied are _remove.v's (s5-r1d's cutover, lib/B/ReplyLSBI.v),
   pinned here; the event arm's ev_* stay ReplyLSBArms.v's copies until a Theorem Labs lane's _arm_event.v re-fit *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_drain_defs_x W_LLVMFuzzerTestOneInput_arm_event.
Local Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Local Notation rm_rr_tr := W_LLVMFuzzerTestOneInput_remove.rm_rr_tr.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the texts of A's arm's rm_rr_cost / rm_cnl_cost (A's lib/A/W_LLVMFuzzerTestOneInput_remove.v Section rmw, MT) with
   MT a parameter; on B the same texts are lib/B/W_LLVMFuzzerTestOneInput_remove.v's, and lib/B/ReplyLSBArms.v /
   ReplyB3Base.v have them as rm_rr_cost MT / rm_cnl_cost at MT := ameter_triv *)
Definition tx_rm_rr_cost (MT : ameter_ops) (m : lmod) (h : hsrc) : Z := tr_cost MT (rm_rr_tr m h).
Definition tx_rm_cnl_cost (MT : ameter_ops) (E H : hlist) : Z := cnl_cost MT E H.

(* ================================================================== the five texts *)
Section tx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable TfibB : asyms.
Variable MT : ameter_ops.
Variable XN_LIB : Z -> Z.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable NP : astate -> Prop.
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable G : list (Z * Z).

(* B top_x :576 LS_event_step; added (A's ReplyLS3cArms.v:91 fr_LS3c_event_step_p): binders ly1 ly2 q and the six
   premises after top_x's five; last, KF-COUNT F5's `0 <= t < OPS_MAX` (the event arm's call passes it) *)
Definition TX_LS_event_step : Prop :=
  forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSx cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks TfibB ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks TfibB ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks TfibB ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3.

(* B top_x :368 LS_drain_step; added (A's ReplyLS3cArms.v:118 fr_LS3c_drain_step_p): binders ly1 h1 E' H' and the
   twenty premises after top_x's five *)
Definition TX_LS_drain_step : Prop :=
  forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) -> dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 -> ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.

(* B top_x :350 LS_cnl_pre; added (A's ReplyLS3Arms.v:841 fr_LS3_cnl_pre_p): binders e' cap' out' and the nine
   premises after top_x's ten *)
Definition TX_LS_cnl_pre : Prop :=
  forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  LSx cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  dr3_epre (nth j (lm_es m) dr_e0) -> dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h''))
    (hl_recs (hs_expected h'')) /\
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
  AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.

(* B top_x :506 LS_rm_cnl_pre; added (A's ReplyLS3Arms.v:1025 fr_LS3_rm_cnl_pre_p): binders ly out2 (after top_x's)
   and the two premises after top_x's five *)
Definition TX_LS_rm_cnl_pre : Prop :=
  forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSx cx t m ly0 S0 -> RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le MT S0 S ((tx_rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S) (input_blks cx ++ model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok MT S ((tx_rm_cnl_cost MT) (hs_expected h1) (hs_held h1)).

(* B top_x :278 LS_exit_end; added (A's ReplyLS3o.v:1063 LS_exit_end3_x): the three premises after top_x's seven
   (relay_finish's final capacity, the loop's t bound, and fr_surv itself); its LS is fr_LS3c /\ fr_OUT *)
Definition TX_LS_exit_end : Prop :=
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  ajournal_gx_x segs TfibB [] ARX G 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\ NP (stack_free_state 1 fpos S') /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
(* the same without top_x's NP conclusion (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d): the exit walk takes NP from the threaded room
   invariant), which is what LS_exit_end3_x concludes *)
Definition TX_LS_exit_end_d : Prop :=
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  ajournal_gx_x segs TfibB [] ARX G 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
End tx.

(* ================================================================== the plugs *)
Section plug.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable CALL_ROOM_B : Z.

(* each plug below is stated at B top_x's own text (lib/B/W_LLVMFuzzerTestOneInput_top_x.v; the B cutover's re-point,
   a Theorem Labs lane 10:58Z) at its LSx, RINV := fr_RINV, TfibB := B, MT generic (a `_m` lemma, the text without its meter
   conjunct) or MT := ameter_triv (its corollary, the whole text); the TX_* text it used to have is equal to it up to
   unfolding *)
(* top_x :819 LS_event_step *)
Lemma tx_LS_event_step_plug {MT : ameter_ops} : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  (fr_LS3c B CALL_ROOM_B) cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  (fr_LS3c B CALL_ROOM_B) cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3.
Proof. intros HCR. intros. eapply fr_LS3c_event_step_p; eassumption. Qed.

(* top_x :510 LS_drain_step *)
Lemma tx_LS_drain_step_plug {MT : ameter_ops} : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  (fr_LS3c B CALL_ROOM_B) cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> fr_RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_kh (nth j (lm_es m) dr_e0) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h1 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost m j h e' h1 -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  (fr_LS3c B CALL_ROOM_B) cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof. intros HCR. intros. eapply fr_LS3c_drain_step_p; eassumption. Qed.

(* top_x :479 LS_cnl_pre *)
Lemma tx_LS_cnl_pre_plug_m {MT : ameter_ops} : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  (fr_LS3c B CALL_ROOM_B) cx t m ly S -> fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  W_rep.AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Proof.
  intros HCR.
  intros cx t m ly S ly' S' si h j h'' e' cap' out' HLS HRI Hpick Hj Hfd Heof Hmo Hec Hmap Hheld Ht HO Hepre Hhpre
    Hcap0 HP Hcap' Hepost Hhpost.
  exact (fr_LS3_cnl_pre_p B CALL_ROOM_B HCR cx t m ly S ly' S' si h j h'' e' cap' out' (proj1 HLS) HRI Hpick Hj Hfd
    Heof Hmo Hec Hmap Hheld Ht HO Hepre Hhpre Hcap0 HP Hcap' Hepost Hhpost).
Qed.
Lemma tx_LS_cnl_pre_plug : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  (fr_LS3c B CALL_ROOM_B) cx t m ly S -> fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le ameter_triv S S' (dr_cost ameter_triv (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  mo_ok ameter_triv S' (cnl_cost ameter_triv (hs_expected h'') (hs_held h'')) /\
  W_rep.AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Proof.
  intros HCR cx t m ly S ly' S' si h j h'' e' cap' out' HLS HRI Hpick Hj Hfd Heof Hmo Hec Hmap Hheld Ht HO Hepre Hhpre
    Hcap0 HP Hcap' Hepost Hhpost.
  destruct (tx_LS_cnl_pre_plug_m HCR cx t m ly S ly' S' si h j h'' e' cap' out' HLS HRI Hpick Hj Hfd Heof Hmo Hec Hmap
    Hheld Ht HO Hepre Hhpre Hcap0 HP Hcap' Hepost Hhpost) as (C1 & C2 & C3 & C4 & C6).
  exact (conj C1 (conj C2 (conj C3 (conj C4 (conj I C6))))).
Qed.

(* top_x :703 LS_rm_cnl_pre *)
Lemma tx_LS_rm_cnl_pre_plug_m {MT : ameter_ops} : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  (fr_LS3c B CALL_ROOM_B) cx t m ly0 S0 -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)).
Proof.
  intros HCR.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 HLS HRI Hat Hrr Hmo Hpos Hfr.
  exact (fr_LS3_rm_cnl_pre_p B CALL_ROOM_B HCR cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 (proj1 HLS) HRI
    Hat Hrr Hmo Hpos Hfr).
Qed.
Lemma tx_LS_rm_cnl_pre_plug : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  (fr_LS3c B CALL_ROOM_B) cx t m ly0 S0 -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le ameter_triv S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost ameter_triv) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok ameter_triv S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost ameter_triv) (hs_expected h1) (hs_held h1)).
Proof.
  intros HCR cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 HLS HRI Hat Hrr Hmo Hpos Hfr.
  exact (conj (tx_LS_rm_cnl_pre_plug_m HCR cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 HLS HRI Hat Hrr Hmo
    Hpos Hfr) I).
Qed.

(* LS := fr_LS3c /\ fr_OUT (the exit's LS; lib/B/ReplyLSBo.v) *)
Definition tx_LSo (OM : Z) : lfcx -> Z -> lmod -> alayout -> astate -> Prop :=
  fun cx t m ly S => fr_LS3c B CALL_ROOM_B cx t m ly S /\ ReplyLSBo.fr_OUT OM cx t m ly S.

(* A's TX_LS_exit_end_d text, written out at LSx := tx_LSo OM, fr_live_post := fr_live_post3 OM (NOT top_x's
   LS_exit_end :353: top_x's text drops this text's fr_surv premise and adds fr_hblks / NoDup premises, so at a free
   fr_surv it is not provable here; at B's instance it is lib/B/ReplyB3LS3e.v's LS_exit_end3e at LSI) *)
Lemma tx_LS_exit_end_d_plug_m {MT : ameter_ops} : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall OM, ReplyLSBo.OUT_MAX4 <= OM ->
  forall (XN_LIB : Z -> Z) fr_surv fr_FP ARX G,
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  (tx_LSo OM) cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  ajournal_gx_x segs B [] ARX G 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' ->
  (ReplyB3LS3o.fr_live_post3 OM) (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem'.
Proof.
  intros HCR OM HOM XN_LIB fr_surv fr_FP ARX G.
  intros cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out (HLS & HOU) HP HP' Hfr Hmo HC HJ Hcap Ht HSURV.
  eapply ReplyB3LS3o.LS_exit_end3_x; eassumption.
Qed.
Lemma tx_LS_exit_end_d_plug : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall OM, ReplyLSBo.OUT_MAX4 <= OM ->
  forall XN_LIB fr_surv fr_FP ARX G,
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  (tx_LSo OM) cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le ameter_triv S3 S' C -> C <= W_bx_defs.lx_exit_cost ameter_triv m ->
  ajournal_gx_x segs B [] ARX G 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' ->
  (ReplyB3LS3o.fr_live_post3 OM) (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le ameter_triv (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Proof.
  intros HCR OM HOM XN_LIB fr_surv fr_FP ARX G.
  intros cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out HL HP HP' Hfr Hmo HC HJ Hcap Ht HSURV.
  destruct (tx_LS_exit_end_d_plug_m HCR OM HOM XN_LIB fr_surv fr_FP ARX G cx t m ly3 S3 rest ly' S' W' mem' md' fpos
    k' C cap out HL HP HP' Hfr Hmo HC HJ Hcap Ht HSURV) as (E1 & E2).
  exact (conj E1 (conj E2 I)).
Qed.

(* the rows at LS := fr_LS3c /\ fr_OUT, where the texts' premises suffice; fr_OUT's event rule is lib/B/ReplyLSBo.v
   fr_OUT_event_step_b (A's fr_OUT_event_step_p without its unused fr_LS3 premise, with `131072 <= OM`) *)
Lemma tx_LS_event_step_plug_o {MT : ameter_ops} : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall OM, ReplyLSBo.OUT_MAX4 <= OM ->
  forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  (tx_LSo OM) cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  (tx_LSo OM) cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3.
Proof.
  intros HCR OM HOM.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q (HLS & HOU) HE M1 M2 M3 Hk HO Hc0 Hm HRR Hf Ht.
  split; [exact (tx_LS_event_step_plug HCR cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HLS HE M1 M2 M3 Hk HO Hc0
    Hm HRR Hf Ht)|].
  pose proof ReplyLSBo.bo_OUT_MAX4_ev as H131.
  eapply ReplyLSBo.fr_OUT_event_step_b; try eassumption. lia.
Qed.
Lemma tx_LS_cnl_pre_plug_o_m {MT : ameter_ops} : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall OM, forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  (tx_LSo OM) cx t m ly S -> fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  W_rep.AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Proof.
  intros HCR OM. intros cx t m ly S ly' S' si h j h'' e' cap' out' (HLS & _).
  exact (tx_LS_cnl_pre_plug_m HCR cx t m ly S ly' S' si h j h'' e' cap' out' HLS).
Qed.
Lemma tx_LS_cnl_pre_plug_o : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall OM, forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  (tx_LSo OM) cx t m ly S -> fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le ameter_triv S S' (dr_cost ameter_triv (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  mo_ok ameter_triv S' (cnl_cost ameter_triv (hs_expected h'') (hs_held h'')) /\
  W_rep.AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Proof.
  intros HCR OM cx t m ly S ly' S' si h j h'' e' cap' out' HLS HRI Hpick Hj Hfd Heof Hmo Hec Hmap Hheld Ht HO Hepre
    Hhpre Hcap0 HP Hcap' Hepost Hhpost.
  destruct (tx_LS_cnl_pre_plug_o_m HCR OM cx t m ly S ly' S' si h j h'' e' cap' out' HLS HRI Hpick Hj Hfd Heof Hmo Hec
    Hmap Hheld Ht HO Hepre Hhpre Hcap0 HP Hcap' Hepost Hhpost) as (C1 & C2 & C3 & C4 & C6).
  exact (conj C1 (conj C2 (conj C3 (conj C4 (conj I C6))))).
Qed.
Lemma tx_LS_rm_cnl_pre_plug_o_m {MT : ameter_ops} : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall OM, forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  (tx_LSo OM) cx t m ly0 S0 -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)).
Proof.
  intros HCR OM. intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 (HLS & _).
  exact (tx_LS_rm_cnl_pre_plug_m HCR cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 HLS).
Qed.
Lemma tx_LS_rm_cnl_pre_plug_o : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall OM, forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  (tx_LSo OM) cx t m ly0 S0 -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le ameter_triv S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost ameter_triv) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok ameter_triv S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost ameter_triv) (hs_expected h1) (hs_held h1)).
Proof.
  intros HCR OM cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 HLS HRI Hat Hrr Hmo Hpos Hfr.
  exact (conj (tx_LS_rm_cnl_pre_plug_o_m HCR OM cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 HLS HRI Hat Hrr
    Hmo Hpos Hfr) I).
Qed.
End plug.

(* ================================================================== a8's argument no longer goes through *)
Section vac.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Notation MT := ameter_triv.

(* (a) a8's proof instantiates S1 := S (2a368424fed TopxVacuity.v:146); TX's malloc premise rules that out *)
Lemma tx_a8_instance_blocked : forall ly ly1 (S : astate) q n, ablocks B ly1 S <> ablocks B ly S ++ [(q, n)].
Proof.
  intros ly ly1 S q n H. apply (f_equal (@length _)) in H. unfold ablocks in H.
  rewrite length_app, !length_map in H. cbn [length] in H. lia.
Qed.

(* (b) for ANY LSx, TX's premises fix S3's live bytes: the start's, plus g_out's change (the event buffer is malloc'd
   and freed), so S3 is not arbitrary *)
Lemma tx_event_S3_bytes : forall ly S (S1 S2 S3 : astate) (ly1 ly2 ly3 : alayout) q n cap out cap' out',
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, n)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) /\
     Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, n) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  blocks_bytes S3 = blocks_bytes S + bsum (aout_blks cap' out') - bsum (aout_blks cap out).
Proof.
  intros ly S S1 S2 S3 ly1 ly2 ly3 q n cap out cap' out' Hm (rest & HR1 & HR2) (l1 & l2 & Hf2 & Hf3).
  rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly S), Hf3.
  assert (E1 : bsum (ablocks B ly1 S1) = bsum (ablocks B ly S) + n) by (rewrite Hm, bsum_app, bsum_cons, bsum_nil; cbn [snd]; lia).
  rewrite (bsum_perm _ _ HR1), bsum_app in E1.
  assert (E2 : bsum (ablocks B ly2 S2) = bsum l1 + n + bsum l2) by (rewrite Hf2, bsum_app, bsum_cons; cbn [snd]; lia).
  rewrite (bsum_perm _ _ HR2), bsum_app in E2.
  rewrite bsum_app. lia.
Qed.

(* (c) a8's two-events shape (2a368424fed TopxVacuity.v:122-141), byte for byte, with its LS_event_step replaced by
   B top_x's LS_event_step text (:819), written out at TfibB := B (as A's ReplyLS3cTopxPost.v at s5-r1d ce7d0d0bf8c) *)
Definition tx_two_events_shape : Prop :=
  forall (LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (RINV : lfcx -> Z -> lmod -> Prop),
  (forall cx t m e v out',
     RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
     ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
     RINV cx (t + 1) (ev_step cx m e v out')) ->
  (forall cx t m ly S e,
     LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
     re_len e < CfParamsReply.fr_MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT (re_len e))) ->
  (forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
   LSx cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
   mo_le MT S S1 (mo_malloc MT (re_len e)) ->
   mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
   mo_le MT S2 S3 (mo_free MT) ->
   0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
   ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
   (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
      Permutation (ablocks B ly2 S2)
        (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
   (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
   0 <= t < OPS_MAX ->
   LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3) ->
  forall cx t m ly S e v out' e',
  LSx cx t m ly S -> RINV cx t m ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  ev_evt cx (ev_step cx m e v out') e' ->
  False.

(* the witness: lib/B/ReplyB3LS3.v fr_LS3_sat's first-head state (sat3) with the input byte 7 (an event op) *)
Definition tx_cx7 : lfcx :=
  LFCX (c_ly (ls3_cx B)) (c_S (ls3_cx B)) (c_W (ls3_cx B)) (c_regs (ls3_cx B)) (c_mem (ls3_cx B)) (c_md (ls3_cx B))
    (c_p (ls3_cx B)) (c_n (ls3_cx B)) [Z_to_bv 8 7] (c_M (ls3_cx B)).
Lemma tx_sat7 : fr_LS3c B YCfn_cf.CALL_ROOM_B tx_cx7 0 (ls3_m B) ls3_ly ls3_S.
Proof.
  assert (EA : ablocks B ls3_ly ls3_S = input_blks tx_cx7 ++ model_blks (ls3_m B) ++ []) by reflexivity.
  split.
  - exists [], 0.
    assert (Hbb : blocks_bytes ls3_S = 1 + ATABLE + APARTIAL) by (vm_compute; reflexivity).
    assert (Hin : bsum (input_blks tx_cx7) = 1) by reflexivity.
    assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
    assert (HS : c_S tx_cx7 = ls3_S) by reflexivity.
    assert (Hn : c_n tx_cx7 = 1) by reflexivity.
    assert (HC : YCfn_cf.CALL_ROOM_B = 8589934592) by reflexivity.
    assert (HL : LIVE_MAX = 17179869184) by reflexivity.
    assert (En : npend (ls3_m B) = 0) by reflexivity.
    assert (Ek : kk tx_cx7 (ls3_m B) = 0) by reflexivity.
    assert (Eo : nopen (lm_hs (ls3_m B)) = 1) by reflexivity.
    assert (Ep : PHI3 (ls3_m B) = ATABLE + APARTIAL + E_ENT + K0) by reflexivity.
    rewrite EA, HS, Hbb, Hn, Hin, Hrest, HC, HL, En, Ek, Eo, Ep.
    split; [apply Permutation_refl|].
    unfold W_OPEN, MB_K, MB_C, ATABLE, APARTIAL, E_ENT, K0.
    refine (conj _ (conj _ (conj _ (conj eq_refl (conj _ _))))); lia.
  - unfold fr_CNT. rewrite EA, !cnt_sec_app, cnt_sec_nil.
    assert (En : npend (ls3_m B) = 0) by reflexivity.
    split; [unfold SEC0; lia | split; [| rewrite En; lia]].
    intros c. rewrite !cnt_cls_app, cnt_cls_nil. unfold CLS0. lia.
Qed.
Lemma tx_evt_nil7 : forall m, ev_len tx_cx7 m = 0 -> ev_evt tx_cx7 m [].
Proof.
  intros m H. unfold ev_evt. rewrite H. cbn [length Z.of_nat].
  refine (conj _ (conj _ (conj _ _))); [lia | intros i Hi; lia | intros Hin; destruct Hin | intros Hl; lia].
Qed.

(* the escape: at LSx := fr_LS3c B YCfn_cf.CALL_ROOM_B (top_x's LS_event_step by its plug), RINV := True, the hypotheses
   of a8's theorem all hold at the witness, so the shape does not prove False *)
Theorem tx_two_events_escapes : ~ tx_two_events_shape.
Proof.
  intros H.
  refine (H (fr_LS3c B YCfn_cf.CALL_ROOM_B) (fun _ _ _ => True) _ _
    (tx_LS_event_step_plug B YCfn_cf.CALL_ROOM_B (Z.le_refl _))
    tx_cx7 0 (ls3_m B) ls3_ly ls3_S [] 0 0 [] tx_sat7 I _ _ _ _ _ _).
  - intros. exact I.
  - intros cx t m ly S e HL _ (He & _).
    pose proof (fr_LS3_room B YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly S (proj1 HL)) as Hroom.
    pose proof (fr_LS3_k B YCfn_cf.CALL_ROOM_B cx t m ly S (proj1 HL)) as Hk.
    destruct HL as ((rest & e0 & _ & _ & _ & Hc & _) & _).
    assert (Hk0 : 0 <= lm_k m) by (unfold kk in Hk; lia).
    assert (Hl : ev_len cx m <= c_n cx).
    { unfold ev_len. destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); lia. }
    assert (HW : CfParamsReply.fr_MMAX = 1072693248) by reflexivity.
    assert (HCR : YCfn_cf.CALL_ROOM_B = 8589934592) by reflexivity.
    unfold re_len, ROOM_SPARE in *. refine (conj _ (conj _ (mo_ok_triv _ _))); lia.
  - change (0 <= 0 < 1). lia.
  - reflexivity.
  - reflexivity.
  - apply tx_evt_nil7. reflexivity.
  - lia.
  - apply tx_evt_nil7.
    assert (Ek : lm_k (ev_step tx_cx7 (ls3_m B) [] 0 0) = 1) by reflexivity.
    unfold ev_len. rewrite Ek. reflexivity.
Qed.
End vac.

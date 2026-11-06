(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: arm 7 (op_event) of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput
   (fuzz_reply.asan 0x845b4 .. 0x84b2c), the segment ARM_event of W_LLVMFuzzerTestOneInput_cut.v, in the form of the
   cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites) and lib/A/ACf5.v (a segment between cut
   points). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_event.v, with its module paths and module names changed; 441 of its 545 lines of code are new or changed and 2738 lines of the source are left out. *)
(* proves no function (kind: invariant lemma): the image-B texts of ten LS premises of the entry walk of
   fuzz_reply's LLVMFuzzerTestOneInput, and their proofs at LS := ReplyLSB.fr_LS B CR where the twin gives them *)
(* The B twin of LS is lib/B/ReplyLSB.v fr_LS (fdb3ee1c6ff, sha256
   5320df77a474 (internal record); the same blob on the B driver branch at 61e610e6176): fr_LS v2's
   text over lib/B's records, with ACfn_cf.CALL_ROOM replaced by the Section variable CALL_ROOM_B (here CR).  The B
   driver fixes it: lib/B/YCfn_cf.v CALL_ROOM_B = 2 ^ 33 (61e610e6176).

   THE TEXTS.  Each premise is a Definition `<name>_T` over the arm's Section variables (B, MT, MMAX, LSx, RINV, in
   that order of declaration; a text names only the ones it uses), so the B arm / top can state it verbatim as a
   Hypothesis with LS -> LSx, and the top closes it by the lemma below at its instance.  The consumer sites:
     B top lib/B/W_LLVMFuzzerTestOneInput_top_x.v (61e610e6176): the arms are still Section hypotheses there
       (:155 SEG_PRO, :157 ARM_write, :160 ARM_remove, :161 ARM_gone, :163 ARM_event, :168 SEG_EXIT); each B arm
       that replaces one takes its LS premises, as A's top_x does (a working branch e7f37cec90b
       lib/A/W_LLVMFuzzerTestOneInput_top_x.v :245 LS_write_room, :289 LS_event_malloc, :338 LS_pro_oa, :454
       LS_rf_room, :491 LS_rm_rr_pre, :573 LS_gone_rig); lib/B/YCfn_cf.v :52-58 names the six;
     B ARM_event (a working branch 556f92b5b9f lib/B/W_LLVMFuzzerTestOneInput_event_x.v :211,
       :214, :220, :225; used at :1761, :2138, :2509, :2767).
   THE ROOM.  fr_LS gives, at every cut point, blocks_bytes S + CR <= LIVE_MAX + LS_OVER (LS_OVER = 66 * 2 ^ 26 +
   23935: the potential's bound 65 * kk + 6000 * 4 + 2 ^ 26 with kk < 2 ^ 26), so a premise asking for R bytes
   above the live bytes holds when LS_OVER + R <= CR.  Each lemma takes exactly that as `HCR`, with its own R, and
   `<name>_B` instantiates it at CR := YCfn_cf.CALL_ROOM_B = 2 ^ 33 (4,160,725,633 to spare over LS_OVER).

   COPIES.  The arm notions this file used to copy are lib/B's arm files' own definitions now, pinned by the Local
   Notations below the Requires (the same bodies; lib/B/ReplyLSBI.v's header lists the cutover): wr_k1 .. wr_pick
   (lib/B/W_LLVMFuzzerTestOneInput_write.v :205-222), rm_kb / rm_ent / rm_at / rm_rr_tr / rm_rr_cost (_remove.v
   :122-146), gn_more / gn_id / gn_pair_ok / gn_pairs (_gone_base.v :361-439) and op_add's charge oa_cost (W_op_add.v
   :147).  Still copied: the event arm's ev_cons2 .. ev_step (B lib/B/W_LLVMFuzzerTestOneInput_arm_event.v 556f92b5b9f :497-505, :1453-1470, the
   same bodies as this tree's _arm_event.v), until a Theorem Labs lane's re-fit of B's _arm_event.v lands (a Theorem Labs lane's ruling,
   2026-10-30); and what has no lib/B definition: the measure helpers fr_LS needs that ReplyLSB.v did not port (A
   lib/A/ReplyLS.v f57b3e2d0ca :106-116, :172-177, :186-217, :429-433), C3's peak measures
   (a working branch 0ca4481bf91 lib/A/W_contract.v :58-71 tr_peak / tr_net, :370 lp_tr,
   :1525-1526 ge_room, :1586-1592 gse_room) and the exit's relay_finish room over them (A _exit.v e7f37cec90b
   :201-207): B's W_contract.v and W_bx_defs.v state ge_room, gse_room and lx_rf_room in the sum form (tr_alloc) and
   have no tr_peak, tr_net or lp_tr. *)
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
(* the meter record (YC5d) and its one instance ameter_triv (Reusable/YCbp.v :17-18), as lib/B/ReplyDriverCfB.v
   Imports them: B's driver passes this ameter_triv *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr RelayRunF send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c
  relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB.
(* the arm notions: lib/B's arm files, Required only and pinned by the Local Notations below, so no other name of
   theirs enters this file's scope *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  W_op_add W_LLVMFuzzerTestOneInput_write W_LLVMFuzzerTestOneInput_remove
  W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation zsum l := (fold_right Z.add 0 l).
Local Notation wr_k1 := W_LLVMFuzzerTestOneInput_write.wr_k1.
Local Notation wr_rem := W_LLVMFuzzerTestOneInput_write.wr_rem.
Local Notation wr_c := W_LLVMFuzzerTestOneInput_write.wr_c.
Local Notation wr_n := W_LLVMFuzzerTestOneInput_write.wr_n.
Local Notation wr_k2 := W_LLVMFuzzerTestOneInput_write.wr_k2.
Local Notation wr_x := W_LLVMFuzzerTestOneInput_write.wr_x.
Local Notation wr_pick := W_LLVMFuzzerTestOneInput_write.wr_pick.
Local Notation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Local Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Local Notation rm_rr_tr := W_LLVMFuzzerTestOneInput_remove.rm_rr_tr.
Local Notation rm_rr_cost := W_LLVMFuzzerTestOneInput_remove.rm_rr_cost.
Local Notation gn_id := W_LLVMFuzzerTestOneInput_gone_base.gn_id.
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.
Local Notation oa_cost := W_op_add.oa_cost.

(* ================================================================== C3's peak measures (copies, see the header) *)
(* copied from a working branch 0ca4481bf91 lib/A/W_contract.v:58-64 *)
Definition tr_peak {P : Type} (tr : list (RelayRunT.rev P)) : Z :=
fold_right (fun ev acc =>
  match ev with
  | RelayRunT.RMalloc n => Z.max 0 (n + acc)
  | RelayRunT.RFree k _ => Z.max 0 (acc - k)
  | RelayRunT.RRealloc k n _ => Z.max 0 (Z.max n (n - k + acc))
  end) 0 tr.
(* copied from 0ca4481bf91 lib/A/W_contract.v:66-71 *)
Definition tr_net {P : Type} (tr : list (RelayRunT.rev P)) : Z :=
fold_right (fun ev acc =>
  match ev with
  | RelayRunT.RMalloc n => n
  | RelayRunT.RFree k _ => - k
  | RelayRunT.RRealloc k n _ => n - k
  end + acc) 0 tr.
(* copied from 0ca4481bf91 lib/A/W_contract.v:370 *)
Definition lp_tr (l : hlist) (n : Z) := ListTr.list_push_tra RelayRunF.adr0 (hl_n l) (hl_cap l) n.
(* copied from 0ca4481bf91 lib/A/W_contract.v:1525-1526 (ge_room, C3 text) over B's ge_tr *)
Definition ge_room_c3 (MMAX bb : Z) (c : ctl) (mx no cap XL : Z) : Prop :=
  tr_max (ge_tr c mx no cap XL) < MMAX /\ bb + tr_peak (ge_tr c mx no cap XL) <= LIVE_MAX.
(* copied from 0ca4481bf91 lib/A/W_contract.v:1586-1592 (gse_room, C3 text) over B's ge_* *)
Fixpoint gse_room_c3 (MMAX bb : Z) (c : ctl) (mx no cap : Z) (xs : list (list byte)) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => ge_room_c3 MMAX bb c mx no cap (Z.of_nat (length x)) /\
      gse_room_c3 MMAX (bb + tr_net (ge_tr c mx no cap (Z.of_nat (length x))) - (Z.of_nat (length x) + 1))
        (ge_ctl c (Z.of_nat (length x))) mx
        (ge_no c no (Z.of_nat (length x))) (ge_cap c mx no cap (Z.of_nat (length x))) xs'
  end.

(* ================================================================== the exit's relay_finish room, C3 form (a copy) *)
(* copied from e7f37cec90b lib/A/W_LLVMFuzzerTestOneInput_exit.v :201-207 with gse_room read in C3's peak form
   (gse_room_c3 above), the arm's Section MMAX the first argument; lib/B/W_bx_defs.v :167 lx_rf_room is the sum form *)
Fixpoint lx_rf_room_c3 (MMAX bb : Z) (c : ctl) (O : list byte) (mx no cap : Z) (es : list rentry) : Prop :=
  match es with
  | [] => True
  | e :: es' => let r := gse_run c O mx no cap (gse_keys e) in
      gse_room_c3 MMAX bb c mx no cap (gse_keys e) /\
      lx_rf_room_c3 MMAX (bb + gse_cap r) (gse_c r) (gse_O r) mx (gse_no r) (gse_cap r) es'
  end.

(* ================================================================== the event arm's model (a copy) *)
Section copies.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the event arm: copied from a working branch 556f92b5b9f
   lib/B/W_LLVMFuzzerTestOneInput_arm_event.v :497-505 and :1453-1470 (a Theorem Labs lane's B ARM_event); kept until
   a Theorem Labs lane's re-fit of B's _arm_event.v (see the header) *)
Definition ev_cons2 (cx : lfcx) (m : lmod) : Z := Z.min (c_n cx - lm_k m - 1) 2.
Definition ev_u16 (cx : lfcx) (m : lmod) : Z :=
  (if 1 <=? c_n cx - lm_k m - 1 then in_byte cx (lm_k m + 1) else 0)
  + 256 * (if 2 <=? c_n cx - lm_k m - 1 then in_byte cx (lm_k m + 2) else 0).
Definition ev_len (cx : lfcx) (m : lmod) : Z :=
  if 2 <=? c_n cx - lm_k m - 1 then Z.min (ev_u16 cx m) (c_n cx - lm_k m - 1 - 2) else 0.
Definition ev_k1 (cx : lfcx) (m : lmod) : Z := lm_k m + 1 + ev_cons2 cx m.
Definition ev_k2 (cx : lfcx) (m : lmod) : Z := ev_k1 cx m + ev_len cx m.
Definition ev_evt (cx : lfcx) (m : lmod) (e : list byte) : Prop :=
  Z.of_nat (length e) <= ev_len cx m /\
  (forall i, 0 <= i < Z.of_nat (length e) ->
     nth (Z.to_nat i) e (Z_to_bv 8 0) = nth (Z.to_nat (ev_k1 cx m + i)) (c_pl cx) (Z_to_bv 8 0)) /\
  ~ In (Z_to_bv 8 0) e /\
  (Z.of_nat (length e) < ev_len cx m ->
     nth (Z.to_nat (ev_k1 cx m + Z.of_nat (length e))) (c_pl cx) (Z_to_bv 8 0) = Z_to_bv 8 0).
Definition ev_ctl (c : ctl) (e : list byte) (v : Z) : ctl :=
  CTL (ct_cl (sl_ctl c (re_len e))) (ct_br (sl_ctl c (re_len e))) (ct_dd (sl_ctl c (re_len e)))
      (ct_ei (sl_ctl c (re_len e))) v.
Definition ev_step (cx : lfcx) (m : lmod) (e : list byte) (v out' : Z) : lmod :=
  LM (ev_k2 cx m) (lm_hs m) (lm_G m) (lm_es m) (ev_ctl (lm_c m) e v)
     (sl_O (lm_c m) (lm_O m) (e ++ [Z_to_bv 8 0])) (lm_mx m)
     (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out'
     (lm_gn m) (lm_nfd m).
End copies.

(* ================================================================== THE TEXTS *)
(* KF-COUNT #6: each text that ended in a meter conjunct (mo_ok MT S cost) states it no longer; at a counting meter
   the LS instance proves it from its count clause.  LS_event_free_T, whose whole conclusion is that conjunct, stays
   for bt_event_free at ameter_triv (B's v2 top, ReplyBTop.v / ReplyBTopLifts.v) *)
Section texts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* (1) LS_write_room, C3 PEAK form: list_push's own room premise (0ca4481bf91 W_contract.v:397 lp_spec, `blocks_bytes
   S + tr_peak (lp_tr l (Z.of_nat (length x))) <= LIVE_MAX`) at l := hs_pending h, |x| = wr_n; the request bound and
   the meter conjunct are A's (e7f37cec90b top_x.v :245-248, with WR_MMAX := MMAX: A's WR_MMAX is fr_MMAX) *)
Definition LS_write_room_T : Prop := forall cx t m si h ly S,
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < MMAX) /\
  blocks_bytes S + tr_peak (lp_tr (hs_pending h) (wr_n cx m)) <= LIVE_MAX.
(* (1') LS_write_room in A's SUM form (e7f37cec90b top_x.v :245-248, verbatim but WR_MMAX := MMAX): what A's write
   arm keeps (C3 draft: it converts to lp_spec's peak premise by lp_tr_peak_le); it implies (1), bt_write_room_peak *)
Definition LS_write_room_sum_T : Prop := forall cx t m si h ly S,
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX.

(* (2) LS_event_malloc: a Theorem Labs lane's text (556f92b5b9f _event_x.v :211-213), verbatim *)
Definition LS_event_malloc_T : Prop := forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  re_len e < MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX.

(* (3) LS_rm_rr_pre, C3 PEAK form (the C3 draft's edit of e7f37cec90b top_x.v :491-499: tr_alloc -> tr_peak, the
   `lm_cap m < MMAX` and `4 * Z.max` conjuncts dropped, as rr_spec loses them at 0ca4481bf91 W_contract.v:1356) *)
Definition LS_rm_rr_pre_T : Prop := forall cx t m ly S si h j0,
  LSx cx t m ly S -> RINV cx t m -> rm_at cx m si h j0 ->
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (rm_rr_tr m h) < MMAX /\ blocks_bytes S + tr_peak (rm_rr_tr m h) <= LIVE_MAX.
(* (3p) the same with the three PROPOSED premises A's proof takes (lib/A/ReplyTrPeak.v fr_LS_rm_rr_pre_c3p,
   ReplyLSRrPre.v fr_LS_rm_rr_pre_124): the cut's t range (A _remove.v rm_regs_base :358), the entry's unfinished
   line within APARTIAL (aentry_ok, through HREL :2356), and the model blocks' sizes not negative (rr_blks_pos :2155) *)
Definition LS_rm_rr_pre_p_T : Prop := forall cx t m ly S si h j0,
  LSx cx t m ly S -> RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX -> Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (rm_rr_tr m h) < MMAX /\ blocks_bytes S + tr_peak (rm_rr_tr m h) <= LIVE_MAX.

(* (4) HLSRIG = GN_LS_rig, C3 PEAK form (e7f37cec90b _gone_base.v :616-622 with the C3 draft's rig edit, as rig_spec
   at 0ca4481bf91 W_contract.v:1479) *)
Definition GN_LS_rig_T : Prop := forall cx t m ly S hs,
  LSx cx t m ly S -> RINV cx t m -> gn_pairs m hs ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs in
  tr_max tr < MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX.
(* (4p) the same with the PROPOSED premises of A's proof (lib/A/ReplyLS3cTopxRig.v fr_LS3_gone_rig_c1 / _c2p: the
   gone arm holds them at A gone_p3.v:995 and from GRG's amodel_at) *)
Definition GN_LS_rig_p_T : Prop := forall cx t m ly S hs,
  LSx cx t m ly S -> RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs in
  tr_max tr < MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX.

(* (5) LS_rf_room, C3 form (e7f37cec90b top_x.v :454-455 with gse_room in C3's peak form) *)
Definition LS_rf_room_T : Prop := forall cx t m ly S,
  LSx cx t m ly S -> lx_rf_room_c3 MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).

(* (7) LS_event_free: a Theorem Labs lane's text (556f92b5b9f _event_x.v :220-224), verbatim *)
Definition LS_event_free_T : Prop := forall cx t m ly S (S1 S2 : astate) e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_ok MT S2 (mo_free MT).

(* (8) LS_event_relay, RELAXED form: A's text (e7f37cec90b top_x.v :265-273 = lib/A/ReplyLSEvent3.v
   fr_LS_event_relay_r, the C3 / C2 relaxation): send_line's own room premises (sl_maxr, sl_alloc) in place of
   k4's capacity form (sl_cap < MMAX, 2 * sl_cap), plus the two facts the arm holds at its call (the cut's
   `lm_O m = []`, malloc's block).  It needs B's re_spec relaxed the same way (A W_contract.v re_spec :1036-1037
   at 88557c15170) *)
Definition LS_event_relay_T : Prop := forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX.

(* (9) LS_event_step, PROPOSED frame form (lib/A/ReplyLSEvent3.v fr_LS_event_step_p): k4's text plus the cursor and
   the cleared O (the cut's registers), 0 <= lm_cap m (aout_at), and the three callees' block relations (malloc's
   rule post, relay_event's re_post Permutation pair, free's rule post) *)
Definition LS_event_step_T : Prop :=
  forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSx cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  LSx cx (t + 1) (ev_step cx m e v out') ly3 S3.
End texts.

(* (6) LS_pro_oa: A's ARx text (e7f37cec90b top_x.v :338-342) over B's lf_base_x (61e610e6176 cut_x.v :179) and the
   top's Section variables, with op_add's charge W_op_add.oa_cost *)
Section pro_text.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
Variable G : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world (@pa_segs _ fr_prog_listing PB_fr) -> (word -> option byte) ->
  Model -> Prop.
Definition LS_pro_oa_T : Prop := forall cx Hp (S2 : astate) pos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARx cx Hp ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX.
End pro_text.

(* ================================================================== the measure helpers (A ReplyLS.v, f57b3e2d0ca) *)
Section helpers.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma bt_zsum_map_nonneg : forall {X} (g : X -> Z) l, (forall x, 0 <= g x) -> 0 <= zsum (map g l).
Proof. intros X g l H. induction l as [|a l IH]; cbn; [lia | specialize (H a); lia]. Qed.
Lemma bt_zsum_map_elem : forall {X} (g : X -> Z) l i y, (forall x, 0 <= g x) -> nth_error l i = Some y ->
  g y <= zsum (map g l).
Proof.
  intros X g l. induction l as [|a l IH]; intros i y H Hi; destruct i as [|i]; cbn in Hi; try discriminate.
  - injection Hi as ->. cbn. pose proof (bt_zsum_map_nonneg g l H). lia.
  - cbn. specialize (IH i y H Hi). specialize (H a). lia.
Qed.
Lemma bt_nth_some_error : forall (hs : list (option hsrc)) i h, nth i hs None = Some h ->
  nth_error hs i = Some (Some h).
Proof.
  intros hs i h H. destruct (Nat.lt_ge_cases i (length hs)) as [Hl|Hl].
  - rewrite (nth_error_nth' hs None Hl). rewrite H. reflexivity.
  - rewrite (nth_overflow hs None Hl) in H. discriminate.
Qed.
Lemma bt_hl_bytes_nonneg : forall l, 0 <= hl_bytes l.
Proof. intros l. unfold hl_bytes. apply bt_zsum_map_nonneg. intros r. lia. Qed.
Lemma bt_slot_pend_nonneg : forall o, 0 <= slot_pend o.
Proof. intros [h|]; cbn; lia. Qed.
Lemma bt_slot_held_nonneg : forall o, 0 <= slot_held o.
Proof. intros [h|]; cbn; [apply bt_hl_bytes_nonneg | lia]. Qed.
Lemma bt_slot_vsl_nonneg : forall o, 0 <= slot_vsl o.
Proof. intros [h|]; cbn; unfold vsl, AREC; lia. Qed.
Lemma bt_slot_npend_nonneg : forall o, 0 <= slot_npend o.
Proof. intros [h|]; cbn; unfold hl_n; lia. Qed.
Lemma bt_entry_held_nonneg : forall e, 0 <= entry_held e.
Proof. intros e. unfold entry_held. apply bt_zsum_map_nonneg. intros k. lia. Qed.
Lemma bt_nopen_le4 : forall hs, length hs = 4%nat -> nopen hs <= 4.
Proof.
  intros hs Hl. unfold nopen. destruct hs as [|a [|b [|c [|d [|e hs']]]]]; cbn in Hl; try discriminate.
  destruct a, b, c, d; cbn; lia.
Qed.
Lemma bt_PHI_ge : forall m, bsum (model_blks m) <= PHI m.
Proof.
  intros m. unfold PHI, pend_bytes, held_bytes, vslack, W_P, W_H.
  pose proof (bt_zsum_map_nonneg slot_pend (lm_hs m) bt_slot_pend_nonneg).
  pose proof (bt_zsum_map_nonneg slot_held (lm_hs m) bt_slot_held_nonneg).
  pose proof (bt_zsum_map_nonneg entry_held (lm_es m) bt_entry_held_nonneg).
  pose proof (bt_zsum_map_nonneg slot_vsl (lm_hs m) bt_slot_vsl_nonneg). lia.
Qed.
Lemma bt_npend_nonneg : forall m, 0 <= npend m.
Proof. intros m. apply bt_zsum_map_nonneg. exact bt_slot_npend_nonneg. Qed.
Lemma bt_npend_slot : forall m si h, nth si (lm_hs m) None = Some h -> hl_n (hs_pending h) <= npend m.
Proof.
  intros m si h Hh. unfold npend. exact (bt_zsum_map_elem slot_npend (lm_hs m) si (Some h) bt_slot_npend_nonneg
    (bt_nth_some_error _ _ _ Hh)).
Qed.
End helpers.

(* ================================================================== the room fr_LS gives *)
Definition LS_OVER : Z := 66 * 2 ^ 26 + 23935.
Lemma LS_OVER_val : LS_OVER = 4429208959.
Proof. reflexivity. Qed.
(* at the B driver's call room 2 ^ 33, 4,160,725,633 bytes are left above LS_OVER *)
Lemma CALL_ROOM_B_spare : YCfn_cf.CALL_ROOM_B - LS_OVER = 4160725633.
Proof. reflexivity. Qed.
Lemma fr_MMAX_val : fr_MMAX = 1072693248.
Proof. reflexivity. Qed.

Section room.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma bt_LS_room : forall CR cx t m ly S, fr_LS B CR cx t m ly S -> blocks_bytes S + CR <= LIVE_MAX + LS_OVER.
Proof.
  intros CR cx t m ly S (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app.
  pose proof (bt_PHI_ge m). pose proof (bt_nopen_le4 _ Hl). pose proof (bt_npend_nonneg m).
  assert (Hk : kk cx m <= c_n cx) by (unfold kk; lia).
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  unfold LS_OVER, MB_K, MB_C, APARTIAL in *. lia.
Qed.
(* the input consumed is never negative under LS *)
Lemma bt_LS_k : forall CR cx t m ly S, fr_LS B CR cx t m ly S -> 0 <= kk cx m.
Proof. intros CR cx t m ly S (rest & e0 & _ & _ & _ & _ & _ & Hnp & _). pose proof (bt_npend_nonneg m). lia. Qed.
(* the live bytes under LS, to the byte: the input, the rest and the potential *)
Lemma bt_LS_bb : forall CR cx t m ly S, fr_LS B CR cx t m ly S ->
  blocks_bytes S + CR <= LIVE_MAX + MB_K * kk cx m + APARTIAL * 4 + MB_C.
Proof.
  intros CR cx t m ly S (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app.
  pose proof (bt_PHI_ge m). pose proof (bt_nopen_le4 _ Hl). pose proof (bt_npend_nonneg m).
  unfold MB_K, MB_C, APARTIAL in *. lia.
Qed.
End room.

(* ================================================================== (1) LS_write_room *)
(* list_push's peak is within A's summed room (0ca4481bf91 lib/A/W_tr_peak.v lp_tr_peak_le, without its
   0 <= hl_cap premise: a growth happens only at hl_cap = hl_n >= 0) *)
Lemma bt_lp_tr_peak_le : forall l n, 0 <= n ->
  tr_peak (lp_tr l n) <= (if lp_grow l then lp_vbytes l else 0) + (n + 1).
Proof.
  intros l n Hn. assert (H0 : 0 <= hl_n l) by (unfold hl_n; lia).
  unfold lp_tr, lp_grow, lp_vbytes, ListTr.list_push_tra, grow_cap, AREC.
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [E|E]; [destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0]|];
    cbv beta iota; cbn [app tr_peak fold_right]; lia.
Qed.
Section wr_facts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* A ReplyLS.v wr_facts *)
Lemma bt_wr_facts : forall cx m, 0 < wr_n cx m ->
  lm_k m + 3 + wr_n cx m <= wr_k2 cx m <= c_n cx /\ Z.of_nat (length (wr_x cx m)) <= wr_n cx m.
Proof.
  intros cx m Hn. split.
  - revert Hn. unfold wr_k2, wr_n, wr_c, wr_rem, wr_k1. destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); intros; lia.
  - unfold wr_x. rewrite length_firstn. lia.
Qed.
End wr_facts.
(* the room write needs above LS_OVER: its push of at most 8 kk + 128 vector bytes and wr_n + 1 copy bytes, with
   kk + wr_n < 2 ^ 26 (A ReplyLS.v fr_LS_write_room's arithmetic) *)
Definition R_write : Z := 536871106.
Lemma R_write_val : R_write = 8 * 2 ^ 26 + 194.
Proof. reflexivity. Qed.

Section write.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma bt_write_room_sum : forall CR, LS_OVER + R_write <= CR ->
  LS_write_room_sum_T fr_MMAX (fr_LS B CR).
Proof.
  intros CR HCR cx t m si h ly S H (_ & _ & Hh) Hn.
  pose proof LS_OVER_val as HO. assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  pose proof (bt_LS_bb B CR cx t m ly S H) as Hroom. pose proof (bt_LS_k B CR cx t m ly S H) as Hk0.
  destruct H as (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  pose proof (bt_npend_slot m si h Hh) as Hs. pose proof (bt_wr_facts cx m Hn) as ((W1 & W2) & _).
  set (l := hs_pending h) in *.
  assert (Hn0 : 0 <= hl_n l) by (unfold hl_n; lia).
  assert (Hv : lp_grow l = true -> lp_vbytes l <= 32 * hl_n l + 128).
  { unfold lp_grow, lp_vbytes, grow_cap, AREC. intros G. apply Z.eqb_eq in G. rewrite G, Z.eqb_refl.
    destruct (Z.eqb_spec (hl_cap l) 0); lia. }
  pose proof fr_MMAX_val as HW.
  split.
  - intros G. specialize (Hv G). unfold kk in *. lia.
  - destruct (lp_grow l) eqn:G; [specialize (Hv eq_refl) |];
      unfold R_write, MB_K, MB_C, APARTIAL, kk in *; lia.
Qed.
Lemma bt_write_room_peak : forall MMAX (LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  LS_write_room_sum_T MMAX LSx -> LS_write_room_T MMAX LSx.
Proof.
  intros MMAX LSx H cx t m si h ly S HL Hp Hn.
  destruct (H cx t m si h ly S HL Hp Hn) as (H1 & H2). split; [exact H1|].
  pose proof (bt_lp_tr_peak_le (hs_pending h) (wr_n cx m) ltac:(lia)). lia.
Qed.
Lemma bt_write_room : forall CR, LS_OVER + R_write <= CR ->
  LS_write_room_T fr_MMAX (fr_LS B CR).
Proof. intros CR HCR. exact (bt_write_room_peak _ _ (bt_write_room_sum CR HCR)). Qed.
End write.

(* ================================================================== the event arm's arithmetic (A ReplyLSEvent3.v) *)
Lemma bt_n_le : forall mx rem, (if negb (mx =? 0) && (mx <? rem) then mx else rem) <= rem.
Proof. intros mx rem. destruct (Z.ltb_spec mx rem); destruct (mx =? 0); cbn [negb andb]; lia. Qed.
Lemma bt_fin_run_le : forall fuel mx no cap rem, sl_fin_run fuel mx no cap rem <= Z.max cap (2 * (no + rem)).
Proof.
  induction fuel as [|f IH]; intros mx no cap rem; cbn [sl_fin_run]; [lia|].
  destruct (rem <=? 0); [lia|].
  pose proof (bt_n_le mx rem) as Hn.
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
  destruct (cap <? no + n).
  - pose proof (IH mx (no + n) ((no + n) * 2) (rem - n)). lia.
  - pose proof (IH mx (no + n) cap (rem - n)). lia.
Qed.
Lemma bt_max_run_le : forall fuel mx no cap rem, sl_max_run fuel mx no cap rem <= Z.max 0 (2 * (no + rem)).
Proof.
  induction fuel as [|f IH]; intros mx no cap rem; cbn [sl_max_run]; [lia|].
  destruct (rem <=? 0); [lia|].
  pose proof (bt_n_le mx rem) as Hn.
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
  destruct (cap <? no + n).
  - pose proof (IH mx (no + n) ((no + n) * 2) (rem - n)). lia.
  - pose proof (IH mx (no + n) cap (rem - n)). lia.
Qed.
Lemma bt_alloc_run_le : forall fuel mx no cap rem,
  sl_alloc_run fuel mx no cap rem <= Z.max 0 (4 * (no + rem) - 2 * Z.max cap 0).
Proof.
  induction fuel as [|f IH]; intros mx no cap rem; cbn [sl_alloc_run]; [lia|].
  destruct (rem <=? 0); [lia|].
  pose proof (bt_n_le mx rem) as Hn.
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
  destruct (Z.ltb_spec cap (no + n)).
  - pose proof (IH mx (no + n) ((no + n) * 2) (rem - n)). lia.
  - pose proof (IH mx (no + n) cap (rem - n)). lia.
Qed.
Lemma bt_cap_le : forall c mx no cap len, sl_cap c mx no cap len <= Z.max cap (2 * (no + len)).
Proof.
  intros c mx no cap len. rewrite sl_cap_fin. destruct (sl_live c len); [apply bt_fin_run_le | lia].
Qed.
Lemma bt_maxr_le : forall c mx no cap len, sl_maxr c mx no cap len <= Z.max 0 (2 * (no + len)).
Proof.
  intros c mx no cap len. unfold sl_maxr. destruct (sl_live c len); [apply bt_max_run_le | lia].
Qed.
Lemma bt_alloc_le : forall c mx no cap len, sl_alloc c mx no cap len <= Z.max 0 (4 * (no + len) - 2 * Z.max cap 0).
Proof.
  intros c mx no cap len. unfold sl_alloc. destruct (sl_live c len); [apply bt_alloc_run_le | lia].
Qed.
Section ev_facts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition bt_pfx (m : lmod) : list (Z * Z) :=
  (lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks (lm_hs m)).
Lemma bt_model_blks : forall m, model_blks m = bt_pfx m ++ aout_blks (lm_cap m) (lm_out m).
Proof. intros m. unfold model_blks, bt_pfx. cbn [app]. rewrite app_assoc. reflexivity. Qed.
Lemma bt_bsum_aout : forall c o, bsum (aout_blks c o) <= Z.max 0 c.
Proof. intros c o. unfold aout_blks. destruct (Z.eqb_spec c 0); cbv beta iota; rewrite ?bsum_cons, ?bsum_nil; cbn [snd]; lia. Qed.
Lemma bt_bsum_aout_eq : forall c o, 0 <= c -> bsum (aout_blks c o) = c.
Proof. intros c o Hc. unfold aout_blks. destruct (Z.eqb_spec c 0); cbv beta iota; rewrite ?bsum_cons, ?bsum_nil; cbn [snd]; lia. Qed.
Lemma bt_ev_k2 : forall cx m e, 0 <= lm_k m < c_n cx -> ev_evt cx m e ->
  lm_k m + 1 + Z.of_nat (length e) <= ev_k2 cx m <= c_n cx.
Proof.
  intros cx m e Hk (He & _). unfold ev_k2, ev_k1, ev_cons2. unfold ev_len in *.
  destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); lia.
Qed.
Lemma bt_ev_len_le : forall cx m, 0 <= lm_k m -> ev_len cx m <= c_n cx - lm_k m - 3 \/ ev_len cx m = 0.
Proof. intros cx m Hk. unfold ev_len. destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); lia. Qed.
End ev_facts.

Section ev_bb.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma bt_malloc_bb : forall ly S (ly1 : alayout) (S1 : astate) q n,
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, n)] -> blocks_bytes S1 = blocks_bytes S + n.
Proof.
  intros ly S ly1 S1 q n Hm.
  rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S), Hm, bsum_app, bsum_cons, bsum_nil.
  cbn [snd]. lia.
Qed.
End ev_bb.

Ltac bt_perm_lia :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hn" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

(* the event line is at most the bytes left after the op byte and the two length bytes *)
Section ev_len.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma bt_re_len_le : forall CR cx t m ly S e, fr_LS B CR cx t m ly S -> ev_evt cx m e ->
  0 <= lm_k m /\ 1 <= re_len e < 2 ^ 26.
Proof.
  intros CR cx t m ly S e H (He & _).
  pose proof (bt_LS_k B CR cx t m ly S H) as Hk.
  destruct H as (rest & e0 & _ & _ & _ & Hc & _).
  assert (Hk0 : 0 <= lm_k m) by (unfold kk in Hk; lia).
  pose proof (bt_ev_len_le cx m Hk0) as Hl.
  assert (HL : re_len e = Z.of_nat (length e) + 1) by reflexivity.
  split; [exact Hk0 | lia].
Qed.
End ev_len.

(* ================================================================== (2) LS_event_malloc, (7) LS_event_free *)
Definition R_ev_malloc : Z := 67108864.
Definition R_ev_relay : Z := 335544320.
Lemma R_ev_val : R_ev_malloc = 2 ^ 26 /\ R_ev_relay = 5 * 2 ^ 26.
Proof. split; reflexivity. Qed.

Section event.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Context {MT : ameter_ops}.
Lemma bt_event_malloc : forall CR, LS_OVER + R_ev_malloc <= CR -> forall RINV,
  LS_event_malloc_T fr_MMAX (fr_LS B CR) RINV.
Proof.
  intros CR HCR RINV cx t m ly S e H _ HE.
  pose proof (bt_LS_room B CR cx t m ly S H) as Hroom.
  pose proof (bt_re_len_le B CR cx t m ly S e H HE) as (_ & Hr).
  pose proof fr_MMAX_val as HW.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  refine (conj _ _); unfold R_ev_malloc in *; lia.
Qed.
(* meter-only (its whole conclusion is mo_ok): at ameter_triv, for B's v2 top (ReplyBTop.v, ReplyBTopLifts.v) *)
Lemma bt_event_free : forall CR RINV, LS_event_free_T ameter_triv (fr_LS B CR) RINV.
Proof. intros CR RINV cx t m ly S S1 S2 e _ _ _ _ _. exact I. Qed.

(* ================================================================== (8) LS_event_relay, relaxed *)
Lemma bt_event_relay : forall CR, LS_OVER + R_ev_relay <= CR -> forall RINV,
  LS_event_relay_T B MT fr_MMAX (fr_LS B CR) RINV.
Proof.
  intros CR HCR RINV cx t m ly S S1 e ly1 q H _ HE _ HO Hm.
  pose proof (bt_LS_room B CR cx t m ly S H) as Hroom.
  pose proof (bt_re_len_le B CR cx t m ly S e H HE) as (_ & Hr).
  pose proof (bt_malloc_bb B ly S ly1 S1 q (re_len e) Hm) as Hbb.
  pose proof (bt_maxr_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hmx.
  pose proof (bt_alloc_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hal.
  assert (Hno : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  pose proof fr_MMAX_val as HW.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  refine (conj _ _); unfold R_ev_relay in *; lia.
Qed.

(* ================================================================== (9) LS_event_step, proposed frame form *)
Lemma bt_event_step : forall CR, LS_event_step_T B MT (fr_LS B CR).
Proof.
  intros CR cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q H HE _ _ _ Hk HO Hc0 Hm (restR & HR1 & HR2)
    (l1 & l2 & Hf2 & Hf3).
  pose proof (bt_ev_k2 cx m e Hk HE) as Hk2.
  pose proof (bt_cap_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hcb.
  destruct H as (rest & e0 & HP & HR & HEn & Hc & Hl & Hnp & HM).
  set (cap' := sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in *.
  assert (EM' : model_blks (ev_step cx m e v out') = bt_pfx m ++ aout_blks cap' out')
    by (rewrite bt_model_blks; reflexivity).
  exists rest, e0. split; [| split; [exact HR | split; [exact HEn | split; [exact Hc | split]]]].
  - rewrite Hf3, EM'. rewrite Hf2 in HR2. rewrite Hm in HR1. rewrite bt_model_blks in HP.
    clear - HP HR1 HR2. bt_perm_lia.
  - exact Hl.
  - assert (En : npend (ev_step cx m e v out') = npend m) by reflexivity.
    assert (Ek' : kk cx (ev_step cx m e v out') = Z.min (ev_k2 cx m) (c_n cx)) by reflexivity.
    assert (Ek : kk cx m = Z.min (lm_k m) (c_n cx)) by reflexivity.
    assert (Eo : nopen (lm_hs (ev_step cx m e v out')) = nopen (lm_hs m)) by reflexivity.
    assert (EP : PHI (ev_step cx m e v out') =
                 PHI m - bsum (aout_blks (lm_cap m) (lm_out m)) + bsum (aout_blks cap' out')).
    { unfold PHI. rewrite EM', bt_model_blks, !bsum_app.
      change (pend_bytes (ev_step cx m e v out')) with (pend_bytes m).
      change (held_bytes (ev_step cx m e v out')) with (held_bytes m).
      change (vslack (ev_step cx m e v out')) with (vslack m). lia. }
    pose proof (bt_bsum_aout cap' out') as Hnew.
    pose proof (bt_bsum_aout_eq (lm_cap m) (lm_out m) Hc0) as Hold.
    assert (Hno : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
    assert (HL : re_len e = Z.of_nat (length e) + 1) by reflexivity.
    rewrite En, Ek', Eo, EP. rewrite Ek in Hnp, HM. unfold MB_K, MB_C, APARTIAL in *.
    split; lia.
Qed.
End event.

(* ================================================================== (6) LS_pro_oa *)
Definition R_pro_oa : Z := 6896.
Lemma R_pro_oa_val : R_pro_oa = APARTIAL + ATABLE.
Proof. reflexivity. Qed.
Section pro.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Context {MT : ameter_ops}.
(* at fr_live_pre := the driver's form (YCfn_cf.fr_live_pre_b with CALL_ROOM_B read as CR); names no LS *)
Lemma bt_pro_oa : forall CR, R_pro_oa <= CR -> forall XM_LIB RLO RHI LIBROOM NP G ARx,
  LS_pro_oa_T B MT XM_LIB RLO RHI (fun S0 => blocks_bytes S0 + CR <= LIVE_MAX) LIBROOM NP G ARx.
Proof.
  intros CR HCR XM_LIB RLO RHI LIBROOM NP G ARx cx Hp S2 pos (_ & Hpre) _ _ _ Hbb.
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hlive & _). cbv beta in Hlive.
  rewrite Hbb. pose proof R_pro_oa_val. unfold APARTIAL, ATABLE in *. lia.
Qed.
End pro.

(* ================================================================== the instances at the B driver's room *)
Lemma R_write_fits : LS_OVER + R_write <= YCfn_cf.CALL_ROOM_B.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma R_ev_malloc_fits : LS_OVER + R_ev_malloc <= YCfn_cf.CALL_ROOM_B.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma R_ev_relay_fits : LS_OVER + R_ev_relay <= YCfn_cf.CALL_ROOM_B.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma R_pro_oa_fits : R_pro_oa <= YCfn_cf.CALL_ROOM_B.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Context {MT : ameter_ops}.
Local Notation LSB := (fr_LS B YCfn_cf.CALL_ROOM_B).
Lemma LS_write_room_B : LS_write_room_T fr_MMAX LSB.
Proof. exact (bt_write_room B _ R_write_fits). Qed.
Lemma LS_write_room_sum_B : LS_write_room_sum_T fr_MMAX LSB.
Proof. exact (bt_write_room_sum B _ R_write_fits). Qed.
Lemma LS_event_malloc_B : forall RINV, LS_event_malloc_T fr_MMAX LSB RINV.
Proof. exact (bt_event_malloc B _ R_ev_malloc_fits). Qed.
Lemma LS_event_free_B : forall RINV, LS_event_free_T ameter_triv LSB RINV.
Proof. exact (bt_event_free B _). Qed.
Lemma LS_event_relay_B : forall RINV, LS_event_relay_T B MT fr_MMAX LSB RINV.
Proof. exact (bt_event_relay B _ R_ev_relay_fits). Qed.
Lemma LS_event_step_B : LS_event_step_T B MT LSB.
Proof. exact (bt_event_step B _). Qed.
Lemma LS_pro_oa_B : forall XM_LIB RLO RHI LIBROOM NP G ARx,
  LS_pro_oa_T B MT XM_LIB RLO RHI YCfn_cf.fr_live_pre_b LIBROOM NP G ARx.
Proof. exact (bt_pro_oa B _ R_pro_oa_fits). Qed.
End inst.

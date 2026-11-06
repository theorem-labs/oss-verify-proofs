(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: fr_RINV, a concrete definition of the loop's relational invariant RINV of the
   entry walk of fuzz_reply's LLVMFuzzerTestOneInput (lib/A/W_LLVMFuzzerTestOneInput_cut.v:534, the Section variable
   `RINV : lfcx -> Z -> lmod -> Prop` that lcut carries at every cut point), and, below it, each model rule over RINV
   that a W8 segment takes as a Section hypothesis, restated with RINV := fr_RINV (the `_obl` definitions).  The last
   section proves the obligations that read fr_RINV alone or step only the cursor and the flags; the rest are open.
   The shape is the plain proof's (lib/Prog/SlotInv.v:253-314): relay_at's pairing of the relay's entries with the
   open harness sources (Forall2 pair_ok es hj, NoDup (map snd hj), every slot outside hj closed, the entries' fds
   distinct and in [FIRST_FD, FIRST_FD + nfd)), pair_ok's model clauses, LI's input-cost bound
   (slot_cost es hj <= k, k <= n < INPUT_MAX) and globals_at's link between g_gone and the controller's flags.
   What differs from the plain LI, and why:
   - The COUNTING invariant `2 * nfd <= t + 1 + nopen` replaces the plain `0 <= nfd <= t + 1` (SlotInv.v:309).  The
     plain bound allows nfd = 512 at t = 511, so it does not give op_add's `nfd < OPS_MAX` (a Theorem Labs lane's ruling on
     a Theorem Labs lane's finding).  Every operation keeps the counting invariant (fuzz_reply.c:577-593: op_add raises g_nfd
     only when it opens a slot; :619-631: op_remove closes the slot it removes; no other operation opens or closes a
     slot), and with t < OPS_MAX and a free slot it gives nfd <= 257.  The plain bound follows from it and the
     fd clauses (nopen <= nfd, since the open slots' fds are distinct and in [100, 100 + nfd)).
   - No upper bound on t and no `k <= n`.  Most RI_* rules step `RINV cx t m -> RINV cx (t + 1) m'` with no
     `t < OPS_MAX` premise and, for the small arms, no `lm_k m < c_n cx` premise, so a t- or k-bound in RINV would
     make those rules false.  The input-cost bound is therefore split into `cost <= k` (k only grows) and
     `cost <= n` (the rules that raise the cost all carry `lm_k m < c_n cx`).
   - pair_ok's src_at (memory) is amodel_at's slot here; pair_ok keeps the model slot `nth (snd p) (lm_hs m) None =
     Some (fst p)`.  pair_ok's t-bounds on the pending list (SlotInv.v:261-262) are allocator room, which the
     A-proof keeps in LS (LS_write_room, LS_drain_pre); they are not here.
   - The cost counts the relay's unfinished line by its bytes, `length (re_U e)`, where SlotInv.v:56 counts
     `re_used e`: the two are equal under aentry_ok (W_rep.v:125), but the arms' rules see only the model, and W7's
     drain fixes re_U, not re_used (dr_step_ok, W_LLVMFuzzerTestOneInput_drain.v:559).
   - The entries' model facts that aentry_ok (W_rep.v:120-135) states in memory and that RINV-only rules read
     (RI_pads, RI_pair, RI_rm_cnlr_eof, the exit's end matching) are fr_entry_ok.
   The `_obl` definitions are grouped by segment file, each with the rule's file:line.  Rules on atop's head (head,
   drain, small, write, exit, add) are read off the segment files (Required below); rules that exist only on a hand
   branch are stated over verbatim copies of that branch's model notions (each block names the branch, file and line
   it copies; replace the block by a Require when the branch merges).  A rule that is false against fr_RINV has an
   `_obl` (verbatim) and a `_fix_obl` (the amended text, with the premise the arm already holds).  The last section
   proves every rule of W_LLVMFuzzerTestOneInput_top.v (SEG_HEAD's, ARM_add's, the small arms') in the form that
   holds. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
RelayRunT drain_b_c gestures_end_b_c relay_remove_b_c relay_instance_gone_b_c SlotInv.
(* the plain proof's drain lemmas the drain step's proof uses: SlotReads (lines' bytes, upds_same_set), SlotDrain3
   (drain3_ecap: the expected list's capacity), SlotPass2Aux (p2_pair_cost: a drained row's cost) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotReads SlotDrain3 SlotPass2Aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_drain W_LLVMFuzzerTestOneInput_event W_LLVMFuzzerTestOneInput_exit
W_LLVMFuzzerTestOneInput_add.
(* the gone arm's rules GN_RI_read / step / end and its model names, and the remove arm's model names, cited below;
   Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------- the arms' model names, cited
   This file used to copy them; they are the segment files' own definitions (meet 29956454065), so the _obl /
   _holds statements below and the rules of W_LLVMFuzzerTestOneInput_top_x.v name the same constants.  The
   abbreviations keep the short names for this file and for the files that Import it. *)
Notation ev_k2 := W_LLVMFuzzerTestOneInput_event.ev_k2.
Notation ev_evt := W_LLVMFuzzerTestOneInput_event.ev_evt.
Notation ev_ctl := W_LLVMFuzzerTestOneInput_event.ev_ctl.
Notation ev_step := W_LLVMFuzzerTestOneInput_event.ev_step.
Notation rm_set_nth := W_LLVMFuzzerTestOneInput_remove.rm_set_nth.
Notation rm_k' := W_LLVMFuzzerTestOneInput_remove.rm_k'.
Notation rm_kb := W_LLVMFuzzerTestOneInput_remove.rm_kb.
Notation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Notation rm_mk := W_LLVMFuzzerTestOneInput_remove.rm_mk.
Notation rm_cev := W_LLVMFuzzerTestOneInput_remove.rm_cev.
Notation rm_rr_ok := W_LLVMFuzzerTestOneInput_remove.rm_rr_ok.
Notation rm_A1 := W_LLVMFuzzerTestOneInput_remove.rm_A1.
Notation rm_cnl_ok := W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok.
Notation rm_cshe_ok := W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok.
Notation gn_more := W_LLVMFuzzerTestOneInput_gone_base.gn_more.
Notation gn_id := W_LLVMFuzzerTestOneInput_gone_base.gn_id.
Notation gn_kq := W_LLVMFuzzerTestOneInput_gone_base.gn_kq.
Notation gn_e0 := W_LLVMFuzzerTestOneInput_gone_base.gn_e0.
Notation gn_hj0 := W_LLVMFuzzerTestOneInput_gone_base.gn_hj0.
Notation gn_q0 := W_LLVMFuzzerTestOneInput_gone_base.gn_q0.
Notation gn_find := W_LLVMFuzzerTestOneInput_gone_base.gn_find.
Notation gn_src := W_LLVMFuzzerTestOneInput_gone_base.gn_src.
Notation gn_reads := W_LLVMFuzzerTestOneInput_gone_base.gn_reads.
Notation gn_pre := W_LLVMFuzzerTestOneInput_gone_base.gn_pre.
Notation gn_setn := W_LLVMFuzzerTestOneInput_gone_base.gn_setn.
Notation gn_set := W_LLVMFuzzerTestOneInput_gone_base.gn_set.
Notation gn_pair_ok := W_LLVMFuzzerTestOneInput_gone_base.gn_pair_ok.
Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.
Notation gn_after_rig := W_LLVMFuzzerTestOneInput_gone_base.gn_after_rig.
Notation gn_cnl_ok := W_LLVMFuzzerTestOneInput_gone_base.gn_cnl_ok.
Notation gn_cshe_ok := W_LLVMFuzzerTestOneInput_gone_base.gn_cshe_ok.
Notation gn_at1 := W_LLVMFuzzerTestOneInput_gone_base.gn_at1.
Notation gn_run := W_LLVMFuzzerTestOneInput_gone_base.gn_run.
Notation gn_run0 := W_LLVMFuzzerTestOneInput_gone_base.gn_run0.
Notation gn_run_skip := W_LLVMFuzzerTestOneInput_gone_base.gn_run_skip.
Notation gn_run_call := W_LLVMFuzzerTestOneInput_gone_base.gn_run_call.
Notation gn_run_next := W_LLVMFuzzerTestOneInput_gone_base.gn_run_next.

Section rinv.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* _cut's Section w parameters that a rule below names (RI_pro's lf_base, the gone arm's joint rules); fr_RINV
   itself names none of them *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.

(* ================================================================== fr_RINV *)
(* The cost of one relay entry and the source it is paired with: the bytes the controller may still be sent for
   them (the gesture ends of the held keys, keys_total = |text| + 5 each), the worker's bytes not yet read (the
   pending stream) and the relay's unfinished line when it keeps it (re_skip = 0).  SlotInv.v:55-56 pair_cost, with
   length (re_U e) for re_used e (see the header). *)
Definition fr_pair_cost (e : rentry) (p : hsrc * nat) : Z :=
  gestures_end_b_c.keys_total (re_keys e) + Z.of_nat (length (pending_stream (fst p))) +
  (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0).
(* SlotInv.v:58-59 slot_cost *)
Definition fr_cost (es : list rentry) (hj : list (hsrc * nat)) : Z :=
  fold_right Z.add 0 (map (fun q => fr_pair_cost (fst q) (snd q)) (combine es hj)).

(* One relay entry e and the open harness source p = (h, slot) with the same fd, after t operations: the model
   clauses of SlotInv.v:253-263 pair_ok. *)
Definition fr_pair_ok (m : lmod) (t : Z) (e : rentry) (p : hsrc * nat) : Prop :=
  let h := fst p in
  (* SlotInv.v:256 (src_at at g_s + 96 * slot, a slot < 4): the source is the model's slot *)
  (snd p < 4)%nat /\ nth (snd p) (lm_hs m) None = Some h /\
  (* SlotInv.v:257: the entry follows the source's fd (op_add's relay_add(g_s[i].fd), fuzz_reply.c:581, :590) *)
  hs_fd h = re_fd e /\
  (* SlotInv.v:258: while the relay reads the source, its unfinished line is the reference splitter's
     (relay.c's buffer and fuzz_reply.c:217-240 reference_feed see the same bytes) *)
  (re_eof e = 0 -> re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h))) /\
  (* SlotInv.v:259: the relay holds a key for exactly the gestures the harness holds open (fuzz_reply.c:49-51) *)
  same_set (drain_b_c.keys_texts (re_keys e)) (texts (hs_held h)) /\ NoDup (texts (hs_held h)) /\
  (* SlotInv.v:260: between operations check_no_loss has emptied the expected list (fuzz_reply.c:607, :627) *)
  hl_recs (hs_expected h) = [] /\
  (* SlotInv.v:263: the capacities the list growth keeps in range *)
  SlotInv.ecap_ok (hl_cap (hs_expected h)) /\ hl_cap (hs_held h) < 2 ^ 24 /\
  (* SlotInv.v:262: the worker's unread bytes, at most one write of fuzz_take(fuzz_u16) per operation
     (fuzz_reply.c:705-707); with t < OPS_MAX at a drain this keeps the expected list's capacity ecap_ok *)
  Z.of_nat (length (pending_stream h)) <= SlotInv.WRITE_MAX * t /\
  (* the pending list's read offset (W_rep.v:104-105 asrc_at): the drain model reads from it *)
  0 <= hs_off h.

(* The model facts of one relay entry (W_rep.v:120-135 aentry_ok, model clauses; SlotInv's relay_at:269
   entry_ok): eof is a flag, the struct's two 4-byte paddings, one key per held gesture text, and skip is a flag. *)
Definition fr_entry_ok (e : rentry) : Prop :=
  (re_eof e = 0 \/ re_eof e = 1) /\
  length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\
  NoDup (drain_b_c.keys_texts (re_keys e)) /\
  (re_skip e = 0 \/ re_skip e = 1).

(* (1) the counting invariant after t operations.  fuzz_reply.c:681, :684: the prologue's op_add opens slot 0 with
   g_nfd = 1 (2 * 1 <= 0 + 1 + 1); :581: an op_add that opens a slot raises g_nfd and the open count by one (both
   sides + 2); :630 (source_reset, :537 memset): op_remove closes one slot (the right side - 1 + 1); every other
   operation, and an op_add with no free slot (:577-578), keeps both counts (the right side + 1).  amodel_at's
   g_nfd range (_cut.v:305) is restated because RINV-only rules read the fds' range (RI_src, RI_pads). *)
Definition fr_count (t : Z) (m : lmod) : Prop :=
  2 * lm_nfd m <= t + 1 + nopen (lm_hs m) /\ 0 <= lm_nfd m <= OPS_MAX.

(* (2) the relay's table is exactly the open slots, each once (SlotInv.v:265-276 relay_at, model clauses).
   fuzz_reply.c:581, :590: op_add appends the entry of the fd FIRST_FD + g_nfd (FIRST_FD = 100, :117) for the slot it
   opens; :624, :630: op_remove removes the picked slot's entry (relay_remove) and closes the slot (source_reset);
   drain (:604), relay_instance_gone (:642) and the default arm (:733-737) keep the table's fds; pick (:550-561)
   returns only an open slot. *)
Definition fr_relay (cx : lfcx) (t : Z) (m : lmod) : Prop :=
  length (lm_hs m) = 4%nat /\
  NoDup (map re_fd (lm_es m)) /\
  Forall (fun e => 100 <= re_fd e < 100 + lm_nfd m) (lm_es m) /\
  Forall fr_entry_ok (lm_es m) /\
  exists hj : list (hsrc * nat),
    (* each entry with its source, in the relay's table order *)
    Forall2 (fr_pair_ok m t) (lm_es m) hj /\
    (* each slot at most once *)
    NoDup (map snd hj) /\
    (* a slot no entry follows is closed (SlotInv.v:274-275: its 96 bytes zero; here the model's None) *)
    (forall i, (i < 4)%nat -> SlotInv.slot_open hj i = false -> nth i (lm_hs m) None = None) /\
    (* the input-cost bound (SlotInv.v:313 slot_cost <= k, and k <= n, :300) *)
    fr_cost (lm_es m) hj <= lm_k m /\ fr_cost (lm_es m) hj <= c_n cx.

(* the controller's flags against g_gone (SlotInv.v:240 globals_at): until the default arm (fuzz_reply.c:733-737)
   the controller is connected (g_client = CLIENT_FD = 3), not broken and its sends not dead; after it, one of the
   three says so *)
Definition fr_gone (m : lmod) : Prop :=
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).

(* the relational invariant after t operations.  The input bound is SlotInv.v:300's ss_n E < INPUT_MAX (the
   contract's 0 < n < 2 ^ 26, _cut.v:160), restated because the cost bound reads it in RINV-only rules.
   KEEP UNCONSTRAINED: fr_RINV reads only lm_es, lm_hs, lm_k, lm_nfd, lm_gn and lm_c's ct_cl / ct_br / ct_dd.  ARM_remove's
   RI_rm_step (_remove.v, any out2 and errno ev5) and ARM_drain's RI_drain_step (_drain.v, any ev') quantify over the
   output buffer and errno, so they are satisfiable only while fr_RINV says nothing about lm_out, lm_cap, lm_O,
   lm_mx, ct_ei, ctl's errno field or the stream.  A clause added on any of those makes those arms unsatisfiable:
   re-check RI_rm_step and RI_drain_step in the same change.  The clauses fr_pair_ok's pending bound
   (pending <= WRITE_MAX * t), its offset (0 <= hs_off) and fr_entry_ok's skip flag read only lm_hs's sources and
   lm_es's entries, not out / errno, so RI_rm_step and RI_drain_step stay satisfiable (both are proved below:
   RI_rm_step_holds, RI_drain_step_fix_holds). *)
Definition fr_RINV (cx : lfcx) (t : Z) (m : lmod) : Prop :=
  fr_count t m /\ fr_relay cx t m /\ c_n cx < 2 ^ 26 /\ fr_gone m.

(* ================================================================== the obligations, by segment file *)

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_head.v (atop) *)
(* _head.v:389 RI_head_nout (owner: W8 lane, SEG_HEAD; _top.v:103 passes it) *)
Definition RI_head_nout_obl : Prop := forall cx t m, fr_RINV cx t m -> fr_RINV cx t (lm_clear_O m).
(* _head.v:1003 RI_head_skip (_top.v:105) *)
Definition RI_head_skip_obl : Prop := forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> fr_RINV cx t m -> fr_RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_drain.v (atop) *)
(* _drain.v:584 RI_drain_skip *)
Definition RI_drain_skip_obl : Prop := forall cx t m si h,
  fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  fr_RINV cx (t + 1) (dr_skip m (dr_k' cx m)).
(* _drain.v:625 RI_drain_step.  FALSE against fr_RINV as stated, at fr_pair_ok's two capacity clauses for the drained
   slot.  (1) ecap_ok of the expected list (k <= 22, capacity <= 2 ^ 25): with no bound on t, fr_RINV's pending bound
   (WRITE_MAX * t) and the cost (< 2 ^ 26) allow a stream of 2 ^ 25 + 1 NUL bytes, which is 2 ^ 25 + 1 empty lines
   (RelayModel.step), so pushes_run's doubling (drain_b_c.push_cap) leaves drain_b_c.ds_ecap fin = 2 ^ 26, which
   dr_step_ok makes the new capacity.  With `0 <= t < OPS_MAX` (the arm holds it: lregs_base) the pending bound gives
   at most 65535 * 511 < 2 ^ 25 bytes, and SlotDrain3.drain3_ecap gives ecap_ok.  (2) the held list's capacity
   < 2 ^ 24: dr_step_ok bounds it by 2 * (n_held + count_begin) only, and fr_RINV does not bound n_held + count_begin
   below 2 ^ 23 (key texts of 1-3 bytes give 2 ^ 23 held keys at cost < 2 ^ 26).  The arm holds
   `hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22` (LS_cnl_pre's conclusion at
   check_no_loss), which closes it.  RI_drain_step_fix_obl below is the rule with those two premises
   (RI_drain_step_fix_holds). *)
Definition RI_drain_step_obl : Prop := forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
  fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  fr_RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
(* the amended rule: the two premises the arm holds (lregs_base's t bound; LS_cnl_pre's held / begin bound) *)
Definition RI_drain_step_fix_obl : Prop := forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
  0 <= t < OPS_MAX ->
  fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
  fr_RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
(* _drain.v:634 RI_src *)
Definition RI_src_obl : Prop := forall cx t m si h,
  fr_RINV cx t m -> dr_pick cx m si h ->
  hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31.
(* _drain.v:638 RI_fds *)
Definition RI_fds_obl : Prop := forall cx t m i1 i2 h1 h2,
  fr_RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
(* _drain.v:642 RI_pair *)
Definition RI_pair_obl : Prop := forall cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
  (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
  length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat.
(* _drain.v:649 RI_pads (dropped on W8's drain join, s4) *)
Definition RI_pads_obl : Prop := forall cx t m,
  fr_RINV cx t m -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (lm_es m) /\
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) (lm_es m).
(* W8's drain join (s4) _drain.v:712 RI_gone (the same text as the event arm's RI_event_live) *)
Definition RI_gone_obl : Prop := forall cx t m,
  fr_RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_small.v (atop) *)
(* At the walk's choice: _small.v:446, :449, :452, :454 (a4's restated forms; _top.v:134-142) *)
(* _small.v:446 RI_close *)
Definition RI_close_obl : Prop := forall cx t m i, fr_RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_RINV cx (t + 1) (sm_close cx m i).
(* _small.v:449 RI_eintr *)
Definition RI_eintr_obl : Prop := forall cx t m i, fr_RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_RINV cx (t + 1) (sm_eintr cx m i).
(* _small.v:452 RI_sendmax *)
Definition RI_sendmax_obl : Prop := forall cx t m, fr_RINV cx t m ->
  fr_RINV cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
(* _small.v:454 RI_default *)
Definition RI_default_obl : Prop := forall cx t m, fr_RINV cx t m -> fr_RINV cx (t + 1) (sm_default cx m (sm_dg cx m)).

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_write.v (atop) *)
(* _write.v:182 RI_write_skip *)
Definition RI_write_skip_obl : Prop := forall cx t m,
  fr_RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
  fr_RINV cx (t + 1) (wr_skip m (wr_k2 cx m)).
(* _write.v:188 RI_write_push *)
Definition RI_write_push_obl : Prop := forall cx t m si h l' d ev,
  fr_RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  0 <= ev < 2 ^ 32 ->
  fr_RINV cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev).

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_exit.v (atop) *)
(* _exit.v:763 RI_exit_slots *)
Definition RI_exit_slots_obl : Prop := forall cx t m, fr_RINV cx t m ->
  forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None).
(* _exit.v:766 RI_exit_ends *)
Definition RI_exit_ends_obl_v1 : Prop := forall cx t m, fr_RINV cx t m -> (0 < length (lm_es m))%nat ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
(* MOVED: RI_exit_ends_obl_v1 above is the text before commit 3f40808c334, false for fr_RINV: ReplyRINV_a12.v's
   RI_exit_ends_obl_false, RI_exit_ends_obl_false_nul refute its copy RI_exit_ends_unrestated, equal to the _v1
   text (ReplyRINV_a12_audit.v (sha256 dc91213d303a; internal record)).
   RI_exit_ends_obl is commit 3f40808c334's restated rule (top_x's text, with the arm's premise) at RINV := fr_RINV;
   ReplyRINV_a12.v's RI_exit_ends_holds proves it *)
Definition RI_exit_ends_obl : Prop := forall cx t m, fr_RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_pro.v *)
(* commit a7e2bf5856c _pro.v:203 pro_m, copied: the model at the first head *)
Definition pro_m (q T' : Z) (pj : list byte) (c : ctl) (O : list byte) (cap out : Z) : lmod :=
  LM 0 [Some (oa_new_src 100 q pj); None; None; None] T' [ra_new 100] c O 0 cap out 0 1.
(* pro-a2 _pro.v:205 RI_pro *)
Definition RI_pro_obl : Prop := forall cx q T' pj c O cap out,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  fr_RINV cx 0 (pro_m q T' pj c O cap out).

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_add.v (atop) *)
(* _add.v:495 RI_add_pre (_top.v:113).  FALSE against fr_RINV, and against every RINV the other rules allow: no
   premise bounds t, and the rules that step t -> t + 1 with no t premise (RI_close, RI_default, RI_drain_skip, ...)
   force RINV to hold at every t of a reachable model, where op_add / op_remove pairs drive g_nfd past OPS_MAX
   (e.g. t = 1022, nfd = 512, one slot free).  The arm holds 0 <= t < OPS_MAX (lregs_D, _cut.v:379). *)
Definition RI_add_pre_obl : Prop := forall cx t m,
  fr_RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) <> None ->
  (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)) /\ lm_nfd m < OPS_MAX.
Definition RI_add_pre_fix_obl : Prop := forall cx t m, 0 <= t < OPS_MAX ->
  fr_RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) <> None ->
  (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)) /\ lm_nfd m < OPS_MAX.
(* _add.v:498 RI_add_open (_top.v:116).  FALSE against fr_RINV for the same reason: fr_count's g_nfd <= OPS_MAX
   (which RI_src / RI_pads need for the fds' 2 ^ 31 bound) is kept by g_nfd + 1 only when t < OPS_MAX. *)
Definition RI_add_open_obl : Prop := forall cx t m i q pj ev,
  fr_RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  Z.of_nat (length pj) = APARTIAL -> 0 <= ev < 2 ^ 32 ->
  fr_RINV cx (t + 1) (ad_open m i q pj ev).
Definition RI_add_open_fix_obl : Prop := forall cx t m i q pj ev, 0 <= t < OPS_MAX ->
  fr_RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  Z.of_nat (length pj) = APARTIAL -> 0 <= ev < 2 ^ 32 ->
  fr_RINV cx (t + 1) (ad_open m i q pj ev).
(* _add.v:502 RI_add_none (_top.v:120) *)
Definition RI_add_none_obl : Prop := forall cx t m,
  fr_RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None -> fr_RINV cx (t + 1) (ad_none m).

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_event.v *)
(* the event arm's model names are W_LLVMFuzzerTestOneInput_event.v's own (ev_k2 :998, ev_evt :1000, ev_ctl :1010,
   ev_step :1013 at meet 29956454065; this file Imports it), cited at the top of the file *)
(* event-c-omx-reader _event.v:1024 RI_event_live *)
Definition RI_event_live_obl : Prop := forall cx t m,
  fr_RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).
(* event-c-omx-reader _event.v:1029 RI_event_step *)
Definition RI_event_step_obl : Prop := forall cx t m e v out',
  fr_RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  fr_RINV cx (t + 1) (ev_step cx m e v out').

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_remove.v *)
(* the remove arm's model names are W_LLVMFuzzerTestOneInput_remove.v's own (rm_set_nth :278, rm_k' :314, rm_kb :315,
   rm_ent :316, rm_at :320, rm_mk :326, rm_cev :332, rm_rr_ok :338, rm_A1 :2722, rm_cnl_ok :2724, rm_cshe_ok :3914 at
   meet 29956454065), cited at the top of the file; rm_capb is lib/A/W_check_no_loss.v:59 capb, copied (that file
   is a 3,700-line walk) *)
Definition rm_capb (H E : hlist) : Z :=
  Z.max 8 (Z.max (hl_cap H) (2 * (hl_n H + Z.of_nat (count_begin (texts E))))).
(* RiRestate's commit 250502f7048 RI_rm_src (W_LLVMFuzzerTestOneInput_remove_x.v:159, top_x.v:697): the slot
   relay_remove drains starts with no expected records (RI_src's first conjunct, at rm_at's slot) *)
Definition RI_rm_src_obl : Prop := forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 -> hl_recs (hs_expected h) = [].
(* remove-s2 _remove.v:455 RI_rm_found *)
Definition RI_rm_found_obl : Prop := forall cx t m si h,
  fr_RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 4 ->
  pick (lm_hs m) (rm_kb cx m) = Some si -> nth si (lm_hs m) None = Some h ->
  exists j, (j < length (lm_es m))%nat /\ re_fd (rm_ent m j) = hs_fd h.
(* remove-s2 _remove.v:1942 RI_rm_rr_fds (the text of _drain.v:638 RI_fds) *)
Definition RI_rm_rr_fds_obl : Prop := forall cx t m i1 i2 h1 h2,
  fr_RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
(* remove-s2 _remove.v:1949 RI_rm_rr_pair *)
Definition RI_rm_rr_pair_obl : Prop := forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 -> re_eof (rm_ent m j0) = 0 ->
  re_skip (rm_ent m j0) = hs_overlong h /\ (re_skip (rm_ent m j0) = 0 -> bzs (re_U (rm_ent m j0)) = bzs (hs_W h)).
(* remove-s2 _remove.v:2591 RI_rm_cnl_pre *)
Definition RI_rm_cnl_pre_obl_v1 : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * rm_capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
(* MOVED: RI_rm_cnl_pre_obl_v1 above is the text before commit 3f40808c334, false for fr_RINV: ReplyRINV_a12.v's
   RI_rm_cnl_pre_obl_false refutes its copy RI_rm_cnl_pre_unrestated, equal to the _v1 text (ReplyRINV_a12_audit.v (sha256 dc91213d303a; internal record)).
   RI_rm_cnl_pre_obl is commit 3f40808c334's restated rule (top_x's text, with the arm's premise) at RINV := fr_RINV;
   ReplyRINV_a12.v's RI_rm_cnl_pre_holds proves it *)
Definition RI_rm_cnl_pre_obl : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * rm_capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
(* remove-s2 _remove.v:3506 RI_rm_cnlr_eof *)
Definition RI_rm_cnlr_eof_obl : Prop := forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 -> 0 <= re_eof (rm_ent m j0) <= 1.
(* remove-s2 _remove.v:3759 RI_rm_cshe_pre *)
Definition RI_rm_cshe_pre_obl_v1 : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
(* MOVED: RI_rm_cshe_pre_obl_v1 above is the text before commit 3f40808c334, false for fr_RINV: ReplyRINV_a12.v's
   RI_rm_cshe_pre_obl_false refutes its copy RI_rm_cshe_pre_unrestated, equal to the _v1 text (ReplyRINV_a12_audit.v (sha256 dc91213d303a; internal record)).
   RI_rm_cshe_pre_obl is commit 3f40808c334's restated rule (top_x's text, with the arm's premise) at RINV := fr_RINV;
   ReplyRINV_a12.v's RI_rm_cshe_pre_holds proves it *)
Definition RI_rm_cshe_pre_obl : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H') ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
(* remove-s2 _remove.v:4863 RI_rm_csd *)
Definition RI_rm_csd_obl_v1 : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  rm_A1 m h1 + cc = Z.of_nat (length O2).
(* MOVED: RI_rm_csd_obl_v1 above is the text before commit 3f40808c334, false for fr_RINV: ReplyRINV_a12.v's
   RI_rm_csd_obl_false refutes its copy RI_rm_csd_unrestated, equal to the _v1 text (ReplyRINV_a12_audit.v (sha256 dc91213d303a; internal record)).
   RI_rm_csd_obl is commit 3f40808c334's restated rule (top_x's text, with the arm's premise) at RINV := fr_RINV;
   ReplyRINV_a12.v's RI_rm_csd_holds proves it *)
Definition RI_rm_csd_obl : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  0 <= lm_gn m <= 1 ->
  rm_A1 m h1 + cc = Z.of_nat (length O2).
(* remove-s2 _remove.v:5393 RI_rm_step (proved below: RI_rm_step_holds) *)
Definition RI_rm_step_obl : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  fr_RINV cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2).

(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_gone*.v *)
(* ---------------------------------------------------------------- W_LLVMFuzzerTestOneInput_gone*.v *)
(* The gone arm's rules GN_RI_read / GN_RI_step / GN_RI_end are the W_LLVMFuzzerTestOneInput_gone_base.v texts at
   RINV := fr_RINV (below), and MMAX is that file's Section variable.  GN_RI_pairs / GN_RI_fds keep their copied
   text, the same word for word.  The gone model names (gn_more .. gn_at1, gn_cnl_ok, gn_run) are
   W_LLVMFuzzerTestOneInput_gone_base.v's own (meet 29956454065 :342-:496), cited at the top of the file:
   gn_cnl_ok there carries REQ5(b) `hl_cap (hs_held h) <= hl_cap H'` last, and gn_run calls it.
   ReplyRINV_gone.v proves RI_gone_pairs / RI_gone_read over them. *)
Variable MMAX : Z.
(* gone-a4 _gone_base.v:694 GN_RI_pairs (HPAIRS, _gone.v:107, _gone_p3.v:167) *)
Definition GN_RI_pairs_obl : Prop := forall cx t m, fr_RINV cx t m -> exists hs, gn_pairs m hs.
(* gone-a4 _gone_base.v:696 GN_RI_fds (HFDS, _gone.v:108, _gone_p3.v:168) *)
Definition GN_RI_fds_obl : Prop := forall cx t m i1 i2 h1 h2,
  fr_RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
(* _gone_base.v:573 GN_RI_read (commit 6a2e02357a4; RIR, _gone.v:85, _gone_p4.v:603), at RINV := fr_RINV.  Its
   text adds gn_rig_ok (_gone_base.v:448, rig_post's per-entry relation) after gn_after_rig; commit dc16e01b163's
   text, without it, was false against fr_RINV (the drained slot's source was free). *)
Definition GN_RI_read_obl : Prop := W_LLVMFuzzerTestOneInput_gone_base.GN_RI_read fr_RINV.
(* _gone_base.v GN_RI_step (commit a39b599f92e; RIstep, _gone_p5.v), joint with LS, at RINV := fr_RINV:
   gn_rig_ok as for GN_RI_read, gn_op and the entries' NUL-free / key-length clause after RINV, the start state's
   capacity, entry-representation and pending-offset clauses (gdone carries them), W_contract.v's cnl_room /
   cnl_cost in place of commit dc16e01b163's Section variables, and the callee posts' block relation (it takes B) *)
Definition GN_RI_step_obl : Prop := W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step B MT LS fr_RINV MMAX.
(* _gone_base.v GN_RI_end (commit a39b599f92e; RIend, _gone_p5.v), joint with LS, at RINV := fr_RINV: gn_rig_ok,
   gn_op, the entries' clause, lm_gn m = 0 \/ lm_gn m = 1 (commit d3a30b1562c), the start state's clauses (as
   GN_RI_step) and the block relation added *)
Definition GN_RI_end_obl : Prop := W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B MT LS fr_RINV.

(* ================================================================== proofs
   The obligations fr_RINV meets.  RI_pro: fr_RINV holds at the first head (it is not vacuous).  Every rule of
   W_LLVMFuzzerTestOneInput_top.v in its true form: RI_head_nout, RI_head_skip (SEG_HEAD); RI_add_pre_fix,
   RI_add_open_fix, RI_add_none (ARM_add); RI_close, RI_eintr, RI_sendmax, RI_default (the small arms).  ARM_remove's
   step: RI_rm_step.  ARM_drain's step with the arm's two premises: RI_drain_step_fix.  The relay-fd projections:
   RI_fds, RI_src, RI_pads, RI_rm_found, RI_rm_cnlr_eof; the flags: RI_gone. *)
Lemma fr_Forall2_r : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
Lemma fr_Forall2_comb : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In (x, y) (combine l1 l2) /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
(* two entries of the table with the same fd are one row, so their sources are one *)
Lemma fr_comb_inj : forall (Y : Type) (es : list rentry) (hj : list Y), List.NoDup (map re_fd es) ->
  forall e1 p1 e2 p2, In (e1, p1) (combine es hj) -> In (e2, p2) (combine es hj) -> re_fd e1 = re_fd e2 ->
  p1 = p2.
Proof.
  intros Y es. induction es as [|x es IH]; intros hj Hnd e1 p1 e2 p2 H1 H2 Hf; [destruct H1|].
  destruct hj as [|y hj]; [destruct H1|]. cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Hx Hnd].
  cbn [combine In] in H1, H2.
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - injection E1 as <- <-. injection E2 as <- <-. reflexivity.
  - injection E1 as <- <-. exfalso. apply Hx. rewrite Hf. apply in_map. eapply in_combine_l. exact H2.
  - injection E2 as <- <-. exfalso. apply Hx. rewrite <- Hf. apply in_map. eapply in_combine_l. exact H1.
  - exact (IH hj Hnd e1 p1 e2 p2 H1 H2 Hf).
Qed.
(* an open slot is some entry's source *)
Lemma fr_pair_of_open : forall m t hj i h, Forall2 (fr_pair_ok m t) (lm_es m) hj ->
  (forall i, (i < 4)%nat -> SlotInv.slot_open hj i = false -> nth i (lm_hs m) None = None) ->
  (i < 4)%nat -> nth i (lm_hs m) None = Some h ->
  exists e p, In (e, p) (combine (lm_es m) hj) /\ fr_pair_ok m t e p /\ snd p = i /\ fst p = h.
Proof.
  intros m t hj i h HF Hcl Hi Hh.
  destruct (SlotInv.slot_open hj i) eqn:Ho; [|rewrite (Hcl i Hi Ho) in Hh; discriminate Hh].
  unfold SlotInv.slot_open in Ho. apply existsb_exists in Ho as (x & Hx & Hxi).
  apply Nat.eqb_eq in Hxi. subst x. apply in_map_iff in Hx as (p & Hpi & Hp).
  destruct (fr_Forall2_comb _ _ _ _ _ HF p Hp) as (e & Hin & HR).
  exists e, p. split; [exact Hin|]. split; [exact HR|]. split; [exact Hpi|].
  destruct HR as (_ & Hn & _). rewrite Hpi, Hh in Hn. injection Hn as Ef. exact (eq_sym Ef).
Qed.

Lemma RI_head_nout_holds : RI_head_nout_obl.
Proof. intros cx t m H. exact H. Qed.

(* the first head's model satisfies fr_RINV from the input's length range alone: the core of RI_pro_holds, which
   the ARx top's RI_pro (lf_base_x in place of lf_base, ReplyTopXRI.v) reaches through the same conjunct *)
Lemma RI_pro_core : forall cx q T' pj c O cap out,
  0 <= c_n cx < 2 ^ 26 -> ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 ->
  fr_RINV cx 0 (pro_m q T' pj c O cap out).
Proof.
  intros cx q T' pj c O cap out Hn Hcl Hbr Hdd.
  split; [|split; [|split]].
  - unfold fr_count, pro_m, nopen, OPS_MAX. cbn. lia.
  - unfold fr_relay, pro_m. cbn [lm_hs lm_es lm_nfd lm_k].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok. cbn.
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
    exists [(oa_new_src 100 q pj, 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok. cbn.
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; split; [reflexivity | intros _; reflexivity]|].
      split; [intros y; split; intros []|]. split; [apply NoDup_ListNoDup; constructor|]. split; [reflexivity|].
      split; [left; reflexivity|]. split; [lia|]. split; [unfold SlotInv.WRITE_MAX; lia | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *;
        first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost. cbn. lia.
  - exact (proj2 Hn).
  - unfold fr_gone, pro_m. cbn [lm_gn lm_c]. split; intros H; [auto | discriminate H].
Qed.

Lemma RI_pro_holds : RI_pro_obl.
Proof.
  intros cx q T' pj c O cap out HB _ Hcl Hbr Hdd _.
  apply (RI_pro_core cx q T' pj c O cap out); [|exact Hcl | exact Hbr | exact Hdd].
  destruct HB as (_ & _ & _ & _ & _ & Hn & _). destruct Hn as [(Hz & _) | (Hn & _)]; lia.
Qed.

Lemma fr_in4 : forall s, (s < 4)%nat -> In s [0; 1; 2; 3]%nat.
Proof. intros s Hs. destruct s as [|[|[|[|s]]]]; cbn; first [tauto | lia]. Qed.
Lemma RI_add_pre_fix_holds : RI_add_pre_fix_obl.
Proof.
  intros cx t m Ht ((HC & Hnfd) & HR & _ & _) _ Hfree.
  destruct HR as (Hlen & _ & Hrng & _ & hj & HF & HNDs & _ & _ & _).
  assert (Hi : exists i, (i < 4)%nat /\ nth i (lm_hs m) None = None).
  { unfold oa_first in Hfree. rewrite !ad_os_nth in Hfree.
    destruct (nth 0 (lm_hs m) None) eqn:E0; [|exists 0%nat; split; [lia | exact E0]].
    destruct (nth 1 (lm_hs m) None) eqn:E1; [|exists 1%nat; split; [lia | exact E1]].
    destruct (nth 2 (lm_hs m) None) eqn:E2; [|exists 2%nat; split; [lia | exact E2]].
    destruct (nth 3 (lm_hs m) None) eqn:E3; [|exists 3%nat; split; [lia | exact E3]].
    exfalso. apply Hfree. reflexivity. }
  destruct Hi as (i & Hi4 & Hin).
  (* the free slot leaves at most three open *)
  assert (Hop : nopen (lm_hs m) <= 3).
  { clear - Hlen Hi4 Hin. unfold nopen.
    destruct (lm_hs m) as [|o0 [|o1 [|o2 [|o3 [|o4 hs']]]]]; cbn in Hlen; try discriminate Hlen.
    destruct o0, o1, o2, o3; destruct i as [|[|[|[|i]]]]; cbn in Hin |- *; try discriminate Hin; lia. }
  split; [|split].
  - (* the entries' sources are distinct open slots, none of them the free one *)
    rewrite (Forall2_length HF).
    assert (Hinc : incl (map snd hj) (List.filter (fun y => negb (Nat.eqb y i)) [0; 1; 2; 3]%nat)).
    { intros y Hy. apply in_map_iff in Hy as (p & <- & Hp).
      destruct (fr_Forall2_r _ _ _ _ _ HF p Hp) as (e & _ & HRp).
      destruct HRp as (Hs4 & Hsn & _).
      apply filter_In. split; [exact (fr_in4 _ Hs4)|].
      apply negb_true_iff, Nat.eqb_neq. intros E. rewrite E, Hin in Hsn. discriminate Hsn. }
    apply NoDup_ListNoDup in HNDs.
    pose proof (NoDup_incl_length HNDs Hinc) as Hle. rewrite length_map in Hle.
    destruct i as [|[|[|[|i]]]]; cbn in Hle; lia.
  - intros Hx. apply in_map_iff in Hx as (e & Hfd & He).
    rewrite Forall_forall in Hrng. specialize (Hrng e He). lia.
  - unfold OPS_MAX in *. lia.
Qed.

Lemma RI_src_holds : RI_src_obl.
Proof.
  intros cx t m si h ((_ & Hnfd) & HR & _ & _) (_ & Hsi & Hh).
  destruct HR as (_ & _ & Hrng & _ & hj & HF & _ & Hcl & _).
  destruct (fr_pair_of_open m t hj si h HF Hcl Hsi Hh) as (e & p & Hin & HRp & _ & <-).
  destruct HRp as (_ & _ & Hfd & _ & _ & Hnd & Hexp & _).
  split; [exact Hexp|]. split; [exact Hnd|].
  assert (He : In e (lm_es m)) by (eapply in_combine_l; exact Hin).
  rewrite Forall_forall in Hrng. specialize (Hrng e He).
  unfold OPS_MAX in Hnfd. rewrite Hfd. lia.
Qed.

(* RI_src_holds's first conjunct, at rm_at's slot (rm_at carries si < 4 and the slot's source) *)
Lemma RI_rm_src_holds : RI_rm_src_obl.
Proof.
  intros cx t m si h j0 (_ & HR & _ & _) (_ & _ & _ & _ & Hsi & Hh & _).
  destruct HR as (_ & _ & _ & _ & hj & HF & _ & Hcl & _).
  destruct (fr_pair_of_open m t hj si h HF Hcl Hsi Hh) as (e & p & _ & HRp & _ & <-).
  destruct HRp as (_ & _ & _ & _ & _ & _ & Hexp & _). exact Hexp.
Qed.

Lemma RI_fds_holds : RI_fds_obl.
Proof.
  intros cx t m i1 i2 h1 h2 (_ & HR & _) Hi1 Hi2 Hne Hh1 Hh2 Hf.
  destruct HR as (_ & Hnd & _ & _ & hj & HF & _ & Hcl & _). apply NoDup_ListNoDup in Hnd.
  destruct (fr_pair_of_open m t hj i1 h1 HF Hcl Hi1 Hh1) as (e1 & p1 & Hin1 & HR1 & Hs1 & Hf1).
  destruct (fr_pair_of_open m t hj i2 h2 HF Hcl Hi2 Hh2) as (e2 & p2 & Hin2 & HR2 & Hs2 & Hf2).
  apply Hne. rewrite <- Hs1, <- Hs2. f_equal.
  apply (fr_comb_inj _ (lm_es m) hj Hnd e1 p1 e2 p2 Hin1 Hin2).
  destruct HR1 as (_ & _ & E1 & _). destruct HR2 as (_ & _ & E2 & _).
  rewrite <- E1, <- E2, Hf1, Hf2. exact Hf.
Qed.
Lemma RI_rm_rr_fds_holds : RI_rm_rr_fds_obl.
Proof. exact RI_fds_holds. Qed.
Lemma GN_RI_fds_holds : GN_RI_fds_obl.
Proof. exact RI_fds_holds. Qed.

Lemma RI_pads_holds : RI_pads_obl.
Proof.
  intros cx t m ((_ & Hnfd) & HR & _ & _). destruct HR as (_ & _ & Hrng & Hent & _).
  unfold OPS_MAX in Hnfd. split.
  - eapply Forall_impl; [|exact Hent]. intros e (_ & H1 & H2 & _). split; [exact H1 | exact H2].
  - eapply Forall_impl; [|exact Hrng]. intros e He. cbv beta in He. lia.
Qed.

Lemma RI_gone_holds : RI_gone_obl.
Proof. intros cx t m (_ & _ & _ & HG). exact HG. Qed.
Lemma RI_event_live_holds : RI_event_live_obl.
Proof. exact RI_gone_holds. Qed.

Lemma RI_rm_cnlr_eof_holds : RI_rm_cnlr_eof_obl.
Proof.
  intros cx t m si h j0 (_ & HR & _ & _) (_ & _ & _ & _ & _ & _ & Hj & _).
  destruct HR as (_ & _ & _ & Hent & _). rewrite Forall_forall in Hent.
  assert (He : In (rm_ent m j0) (lm_es m)) by (unfold rm_ent; apply nth_In; exact Hj).
  destruct (Hent _ He) as ([E | E] & _); rewrite E; lia.
Qed.

Lemma RI_rm_found_holds : RI_rm_found_obl.
Proof.
  intros cx t m si h (_ & HR & _ & _) _ _ _ _ Hh.
  destruct HR as (Hlen & _ & _ & _ & hj & HF & _ & Hcl & _).
  assert (Hsi : (si < 4)%nat).
  { destruct (Nat.lt_ge_cases si 4) as [H | H]; [exact H|].
    rewrite nth_overflow in Hh by lia. discriminate Hh. }
  destruct (fr_pair_of_open m t hj si h HF Hcl Hsi Hh) as (e & p & Hin & HRp & _ & Hfst).
  assert (He : In e (lm_es m)) by (eapply in_combine_l; exact Hin).
  apply (In_nth (lm_es m) e relay_remove_b_c.no_entry) in He as (j & Hj & Hnj).
  exists j. split; [exact Hj|]. unfold rm_ent. rewrite Hnj.
  destruct HRp as (_ & _ & Hfd & _). rewrite <- Hfd, Hfst. reflexivity.
Qed.

(* ---- the steps that keep the table and the open slots: SEG_HEAD's `continue` and op_add with no free slot *)
Lemma fr_pair_ok_mono : forall m m' t t' e p, lm_hs m' = lm_hs m -> t <= t' ->
  fr_pair_ok m t e p -> fr_pair_ok m' t' e p.
Proof.
  intros m m' t t' e p E Ht (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  rewrite <- E in H2. unfold SlotInv.WRITE_MAX in H10.
  repeat (split; [assumption|]). split; [unfold SlotInv.WRITE_MAX; lia | exact H11].
Qed.
Lemma fr_Forall2_impl : forall (T1 T2 : Type) (R R' : T1 -> T2 -> Prop) l1 l2,
  (forall x y, R x y -> R' x y) -> Forall2 R l1 l2 -> Forall2 R' l1 l2.
Proof. intros T1 T2 R R' l1 l2 H HF. induction HF; constructor; auto. Qed.
Lemma fr_Forall2_map : forall (T1 T2 T3 : Type) (R : T1 -> T2 -> Prop) (R' : T1 -> T3 -> Prop) (g : T2 -> T3) l1 l2,
  (forall x y, R x y -> R' x (g y)) -> Forall2 R l1 l2 -> Forall2 R' l1 (map g l2).
Proof. intros T1 T2 T3 R R' g l1 l2 H HF. induction HF; cbn [map]; constructor; auto. Qed.
(* an operation that keeps the slots, the table and g_nfd, moves the cursor forward and keeps the flags' link *)
Lemma fr_step_k : forall cx t m m', fr_RINV cx t m ->
  lm_hs m' = lm_hs m -> lm_es m' = lm_es m -> lm_nfd m' = lm_nfd m -> lm_k m <= lm_k m' -> fr_gone m' ->
  fr_RINV cx (t + 1) m'.
Proof.
  intros cx t m m' ((HC & Hnfd) & HR & Hn & _) Ehs Ees Enfd Hk HG.
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  split; [|split; [|split; [exact Hn | exact HG]]].
  - unfold fr_count. rewrite Ehs, Enfd. lia.
  - unfold fr_relay. rewrite Ehs, Ees, Enfd.
    split; [exact Hlen|]. split; [exact Hnd|]. split; [exact Hrng|]. split; [exact Hent|].
    exists hj.
    split; [exact (fr_Forall2_impl _ _ _ _ _ _ (fun e p => fr_pair_ok_mono m m' t (t + 1) e p Ehs ltac:(lia)) HF)|].
    split; [exact HNDs|]. split; [exact Hcl|]. split; [lia | exact Hcn].
Qed.

(* _head.v:1003: `continue` (an op that picks, no open source, op <> 1) consumes the input bytes only *)
Lemma RI_head_skip_holds : RI_head_skip_obl.
Proof.
  intros cx t m _ _ _ _ _ _ H. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold lm_set_k, hd_k'. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* _add.v:502: op_add with no closed slot consumes the op byte only (fuzz_reply.c:577-578) *)
Lemma RI_add_none_holds : RI_add_none_obl.
Proof.
  intros cx t m H _ _. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold ad_none. cbn [lm_k]. lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* _small.v:452 / :454: two steps that change only the cursor and the controller's flags *)
Lemma RI_sendmax_holds : RI_sendmax_obl.
Proof.
  intros cx t m H. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold sm_sendmax, sm_kn. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.
Lemma RI_default_holds : RI_default_obl.
Proof.
  intros cx t m H. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold sm_default, sm_kn. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
  - unfold fr_gone, sm_default; cbn [lm_gn lm_c ct_cl ct_br ct_dd].
    split; [intros Hg; discriminate Hg|]. intros _. destruct (sm_dg cx m); [left | right; right]; reflexivity.
Qed.

(* ---- the small arms' slot updates (fuzz_reply.c:712-713 `s->closed = 1`, :721-722 `s->eintr = 1`) *)
Lemma fr_upd_hs_length : forall i f l, length (upd_hs i f l) = length l.
Proof.
  intros i f l. revert i. induction l as [|o l IH]; intros [|i]; cbn [upd_hs length].
  - reflexivity.
  - reflexivity.
  - destruct o; reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma fr_upd_hs_nth : forall i f l j,
  nth j (upd_hs i f l) None = if Nat.eqb j i then option_map f (nth j l None) else nth j l None.
Proof.
  intros i f l. revert i. induction l as [|o l IH]; intros i j.
  - destruct i as [|i], j as [|j]; cbn; try reflexivity. destruct (Nat.eqb j i); reflexivity.
  - destruct i as [|i], j as [|j]; cbn.
    + destruct o; reflexivity.
    + destruct o; reflexivity.
    + reflexivity.
    + apply IH.
Qed.
Lemma fr_upd_hs_nopen : forall i f l, nopen (upd_hs i f l) = nopen l.
Proof.
  intros i f l. unfold nopen. f_equal. revert i. induction l as [|o l IH]; intros [|i].
  - reflexivity.
  - reflexivity.
  - destruct o; reflexivity.
  - cbn [upd_hs]. destruct o; cbn [List.filter length]; rewrite IH; reflexivity.
Qed.
(* the fields of a source that fr_pair_ok and fr_cost read *)
Definition fr_hkeep (h' h : hsrc) : Prop :=
  hs_fd h' = hs_fd h /\ hs_overlong h' = hs_overlong h /\ hs_W h' = hs_W h /\ hs_held h' = hs_held h /\
  hs_expected h' = hs_expected h /\ pending_stream h' = pending_stream h /\ hs_off h' = hs_off h.
Definition fr_upd_pair (f : hsrc -> hsrc) (i : nat) (p : hsrc * nat) : hsrc * nat :=
  if Nat.eqb (snd p) i then (f (fst p), snd p) else p.
Lemma fr_pair_upd : forall f i m m' t e p, (forall h, fr_hkeep (f h) h) ->
  lm_hs m' = upd_hs i f (lm_hs m) -> fr_pair_ok m t e p -> fr_pair_ok m' (t + 1) e (fr_upd_pair f i p).
Proof.
  intros f i m m' t e [h j] Hf Ehs Hp.
  destruct Hp as (Hj & Hn & Hfd & Hre & Hss & Hnd & Hexp & Hec & Hhc & Hpe & Hoff). cbn [fst snd] in *.
  unfold SlotInv.WRITE_MAX in Hpe.
  unfold fr_upd_pair. cbn [fst snd].
  destruct (Nat.eqb j i) eqn:Eji.
  - apply Nat.eqb_eq in Eji. subst i. destruct (Hf h) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    unfold fr_pair_ok. cbn [fst snd]. rewrite Ehs, fr_upd_hs_nth, Nat.eqb_refl, Hn. cbn [option_map].
    rewrite F1, F2, F3, F4, F5, F6, F7.
    refine (conj Hj (conj eq_refl (conj Hfd (conj Hre (conj Hss (conj Hnd (conj Hexp (conj Hec
      (conj Hhc (conj _ Hoff)))))))))).
    unfold SlotInv.WRITE_MAX. lia.
  - unfold fr_pair_ok. cbn [fst snd]. rewrite Ehs, fr_upd_hs_nth, Eji.
    refine (conj Hj (conj Hn (conj Hfd (conj Hre (conj Hss (conj Hnd (conj Hexp (conj Hec
      (conj Hhc (conj _ Hoff)))))))))).
    unfold SlotInv.WRITE_MAX. lia.
Qed.
Lemma fr_cost_map : forall (g : hsrc * nat -> hsrc * nat),
  (forall p, pending_stream (fst (g p)) = pending_stream (fst p)) ->
  forall es hj, fr_cost es (map g hj) = fr_cost es hj.
Proof.
  intros g Hg es. unfold fr_cost. induction es as [|e es IH]; intros [|p hj];
    cbn [map combine fold_right fst snd]; try reflexivity.
  rewrite IH. unfold fr_pair_cost. rewrite Hg. reflexivity.
Qed.
(* an operation that updates one slot's flags in place *)
Lemma fr_step_upd : forall f i cx t m m', (forall h, fr_hkeep (f h) h) -> fr_RINV cx t m ->
  lm_hs m' = upd_hs i f (lm_hs m) -> lm_es m' = lm_es m -> lm_nfd m' = lm_nfd m -> lm_k m <= lm_k m' ->
  fr_gone m' -> fr_RINV cx (t + 1) m'.
Proof.
  intros f i cx t m m' Hf ((HC & Hnfd) & HR & Hn & _) Ehs Ees Enfd Hk HG.
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  assert (Esnd : map snd (map (fr_upd_pair f i) hj) = map snd hj).
  { rewrite List.map_map. apply List.map_ext. intros [h j]. unfold fr_upd_pair. cbn [fst snd].
    destruct (Nat.eqb j i); reflexivity. }
  split; [|split; [|split; [exact Hn | exact HG]]].
  - unfold fr_count. rewrite Ehs, Enfd, fr_upd_hs_nopen. lia.
  - unfold fr_relay. rewrite Ees, Enfd.
    split; [rewrite Ehs, fr_upd_hs_length; exact Hlen|].
    split; [exact Hnd|]. split; [exact Hrng|]. split; [exact Hent|].
    exists (map (fr_upd_pair f i) hj).
    split; [exact (fr_Forall2_map _ _ _ _ _ _ _ _ (fun e p => fr_pair_upd f i m m' t e p Hf Ehs) HF)|].
    split; [rewrite Esnd; exact HNDs|].
    split.
    { intros j Hj Ho. unfold SlotInv.slot_open in Ho. rewrite Esnd in Ho.
      rewrite Ehs, fr_upd_hs_nth, (Hcl j Hj Ho). destruct (Nat.eqb j i); reflexivity. }
    rewrite fr_cost_map.
    + split; [lia | exact Hcn].
    + intros [h j]. unfold fr_upd_pair. cbn [fst snd]. destruct (Nat.eqb j i).
      * exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (Hf h))))))).
      * reflexivity.
Qed.

(* _small.v:446: close sets the picked slot's flag *)
Lemma RI_close_holds : RI_close_obl.
Proof.
  intros cx t m i H _. apply (fr_step_upd upd_closed i cx t m _).
  - intros h. unfold fr_hkeep. repeat split; reflexivity.
  - exact H.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold sm_close, sm_kn. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.
(* _small.v:449: eintr sets the picked slot's flag *)
Lemma RI_eintr_holds : RI_eintr_obl.
Proof.
  intros cx t m i H _. apply (fr_step_upd upd_eintr i cx t m _).
  - intros h. unfold fr_hkeep. repeat split; reflexivity.
  - exact H.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold sm_eintr, sm_kn. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* ---- op_add opening slot i (fuzz_reply.c:577-593): the source fd 100 + g_nfd, the relay's entry for it *)
Lemma fr_nopen_set : forall hs i x, nth i hs None = None -> (i < length hs)%nat ->
  nopen (ad_set_nth i (Some x) hs) = nopen hs + 1.
Proof.
  intros hs i x. unfold nopen. revert i. induction hs as [|o hs IH]; intros [|i] Hn Hi;
    cbn [length] in Hi; try lia.
  - cbn [nth] in Hn. subst o. cbn [ad_set_nth List.filter length]. lia.
  - cbn [nth] in Hn. pose proof (IH i Hn ltac:(lia)) as Hih.
    destruct o; cbn [ad_set_nth List.filter length]; lia.
Qed.
Lemma fr_nodup_snoc : forall (T : Type) (l : list T) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
  intros T l x. induction l as [|a l IH]; intros Hnd Hx; cbn [app].
  - constructor; [intros [] | constructor].
  - apply NoDup_cons_iff in Hnd as [Ha Hnd]. constructor.
    + intros Hin. apply in_app_or in Hin as [Hin | [Hin | []]]; [exact (Ha Hin)|].
      subst a. apply Hx. left. reflexivity.
    + apply IH; [exact Hnd|]. intros Hin. apply Hx. right. exact Hin.
Qed.
Lemma fr_cost_snoc : forall es hj e p, length es = length hj ->
  fr_cost (es ++ [e]) (hj ++ [p]) = fr_cost es hj + fr_pair_cost e p.
Proof.
  unfold fr_cost. induction es as [|e0 es IH]; intros [|p0 hj] e p Hl; cbn [length] in Hl; try discriminate Hl.
  - cbn [app combine map fold_right fst snd]. lia.
  - cbn [app combine map fold_right fst snd]. rewrite IH by lia. lia.
Qed.
(* _add.v:498 with the arm's 0 <= t < OPS_MAX *)
Lemma RI_add_open_fix_holds : RI_add_open_fix_obl.
Proof.
  intros cx t m i q pj ev Ht HRI Hop Hfirst _ _.
  pose proof (RI_add_pre_fix_holds cx t m Ht HRI Hop ltac:(rewrite Hfirst; discriminate)) as (_ & _ & Hlt).
  destruct HRI as ((HC & Hnfd) & HR & Hn & HG).
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  pose proof (ad_first_lt _ _ Hfirst) as Hi4.
  assert (Hfree : nth i (lm_hs m) None = None).
  { pose proof (ad_first_zero _ _ Hfirst) as Hz. rewrite ad_os_nth in Hz.
    destruct (nth i (lm_hs m) None); [discriminate Hz | reflexivity]. }
  assert (Hil : (i < length (lm_hs m))%nat) by (rewrite Hlen; exact Hi4).
  (* no entry of the table follows slot i *)
  assert (Hnot : forall p, In p hj -> snd p <> i).
  { intros p Hp E. destruct (fr_Forall2_r _ _ _ _ _ HF p Hp) as (e & _ & HRp).
    destruct HRp as (_ & Hsn & _). rewrite E, Hfree in Hsn. discriminate Hsn. }
  split; [|split; [|split; [exact Hn|]]].
  - unfold fr_count, ad_open. cbn [lm_nfd lm_hs].
    rewrite (fr_nopen_set _ _ _ Hfree Hil). unfold OPS_MAX in *. lia.
  - unfold fr_relay, ad_open. cbn [lm_hs lm_es lm_nfd lm_k].
    split; [rewrite ad_set_nth_length; exact Hlen|].
    split.
    { apply NoDup_ListNoDup. rewrite List.map_app. cbn [map]. apply fr_nodup_snoc.
      - exact (proj1 (NoDup_ListNoDup _) Hnd).
      - intros Hx. apply in_map_iff in Hx as (e & Hfd & He). rewrite Forall_forall in Hrng.
        specialize (Hrng e He). cbn [re_fd ra_new] in Hfd. lia. }
    split.
    { apply Forall_app. split.
      - eapply Forall_impl; [|exact Hrng]. intros e He. cbv beta in *. lia.
      - constructor; [cbn [re_fd ra_new]; lia | constructor]. }
    split.
    { apply Forall_app. split; [exact Hent|].
      constructor; [|constructor]. unfold fr_entry_ok. cbn [re_eof re_pad1 re_pad2 re_keys re_skip ra_new].
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
    exists (hj ++ [(oa_new_src (100 + lm_nfd m) q pj, i)]).
    split.
    { apply Forall2_app.
      - eapply fr_Forall2_impl; [|exact HF]. intros e p Hp.
        assert (Hne : i <> snd p).
        { intros E. destruct Hp as (_ & Hsn & _). rewrite <- E, Hfree in Hsn. discriminate Hsn. }
        destruct Hp as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
        unfold fr_pair_ok. cbn [lm_hs]. rewrite (ad_set_nth_other _ i (snd p) _ _ _ Hne).
        unfold SlotInv.WRITE_MAX in *.
        refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
          (conj _ H11)))))))))). lia.
      - constructor; [|constructor].
        unfold fr_pair_ok. cbn [fst snd lm_hs].
        rewrite (ad_set_nth_same _ i _ _ _ Hil).
        split; [exact Hi4|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros _; split; [reflexivity | intros _; reflexivity]|].
        split; [intros y; split; intros []|].
        split; [apply NoDup_ListNoDup; constructor|].
        split; [reflexivity|]. split; [left; reflexivity|].
        split; [change (0 < 2 ^ 24); lia|].
        split; [change (0 <= SlotInv.WRITE_MAX * (t + 1)); unfold SlotInv.WRITE_MAX; lia | change (0 <= 0); lia]. }
    split.
    { apply NoDup_ListNoDup. rewrite List.map_app. cbn [map snd]. apply fr_nodup_snoc.
      - exact (proj1 (NoDup_ListNoDup _) HNDs).
      - intros Hin. apply in_map_iff in Hin as (p & Hpi & Hp). exact (Hnot p Hp Hpi). }
    split.
    { intros j Hj Ho. unfold SlotInv.slot_open in Ho. rewrite List.map_app, existsb_app in Ho.
      cbn [map snd existsb] in Ho. apply orb_false_iff in Ho as [Ho1 Ho2].
      rewrite orb_false_r in Ho2. apply Nat.eqb_neq in Ho2.
      rewrite (ad_set_nth_other _ i j _ _ _ (not_eq_sym Ho2)). exact (Hcl j Hj Ho1). }
    rewrite fr_cost_snoc by exact (Forall2_length HF).
    assert (H0 : fr_pair_cost (ra_new (100 + lm_nfd m)) (oa_new_src (100 + lm_nfd m) q pj, i) = 0)
      by reflexivity.
    rewrite H0. split; lia.
  - unfold fr_gone, ad_open, ad_set_ev. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. exact HG.
Qed.

(* ---- ARM_remove's step (fuzz_reply.c:619-631): relay_remove drops the entry j0 of slot si's fd, moving the
   table's last entry into its place (relay_remove_b_c.remove_at), and source_reset closes slot si *)
Lemma fr_rm_set_nth_length : forall (T : Type) n (x : T) l, length (rm_set_nth n x l) = length l.
Proof.
  intros T n x l. revert n. induction l as [|y l IH]; intros [|n]; cbn [rm_set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma fr_rm_set_nth_same : forall (T : Type) n (x : T) l d, (n < length l)%nat -> nth n (rm_set_nth n x l) d = x.
Proof.
  intros T n x l. revert n. induction l as [|y l IH]; intros [|n] d Hn; cbn [length] in Hn; try lia;
    cbn [rm_set_nth nth]; [reflexivity | apply IH; lia].
Qed.
Lemma fr_rm_set_nth_other : forall (T : Type) n p (x : T) l d, n <> p -> nth p (rm_set_nth n x l) d = nth p l d.
Proof.
  intros T n. induction n as [|n IH]; intros [|p] x l d Hnp; destruct l as [|y l];
    cbn [rm_set_nth nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.
Lemma fr_nopen_clear : forall hs i x, nth i hs None = Some x -> (i < length hs)%nat ->
  nopen (rm_set_nth i None hs) + 1 = nopen hs.
Proof.
  intros hs i x. unfold nopen. revert i. induction hs as [|o hs IH]; intros [|i] Hn Hi;
    cbn [length] in Hi; try lia.
  - cbn [nth] in Hn. subst o. cbn [rm_set_nth List.filter length]. lia.
  - cbn [nth] in Hn. pose proof (IH i Hn ltac:(lia)) as Hih.
    destruct o; cbn [rm_set_nth List.filter length]; lia.
Qed.
(* remove_at i l is l without its i-th element, up to order *)
Lemma fr_split_nth : forall (T : Type) (l : list T) i d, (i < length l)%nat ->
  l = firstn i l ++ nth i l d :: skipn (S i) l.
Proof.
  intros T l. induction l as [|x l IH]; intros [|i] d Hi; cbn [length] in Hi; try lia.
  - reflexivity.
  - cbn [firstn nth skipn app]. f_equal. apply IH. lia.
Qed.
Lemma fr_remove_perm : forall (T : Type) (l : list T) i d, (i < length l)%nat ->
  Permutation l (nth i l d :: relay_remove_b_c.remove_at i l).
Proof.
  intros T l i d Hi. unfold relay_remove_b_c.remove_at.
  destruct (List.rev l) as [|a r] eqn:Er.
  - apply (f_equal (@length T)) in Er. rewrite length_rev in Er. cbn [length] in Er. lia.
  - assert (El : l = List.rev r ++ [a]) by (rewrite <- (rev_involutive l), Er; reflexivity).
    subst l. rewrite length_app in Hi. cbn [length] in Hi.
    cbv beta iota zeta.
    destruct (Nat.eqb i (length (List.rev r))) eqn:Ei; cbv iota.
    + apply Nat.eqb_eq in Ei. rewrite app_nth2 by lia. rewrite Ei, Nat.sub_diag. cbn [nth].
      apply Permutation_sym, Permutation_cons_append.
    + apply Nat.eqb_neq in Ei. rewrite app_nth1 by lia.
      rewrite (fr_split_nth _ (List.rev r) i d ltac:(lia)) at 1.
      rewrite <- app_assoc, <- app_comm_cons.
      eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
      apply perm_skip, Permutation_app_head, Permutation_sym, Permutation_cons_append.
Qed.
Lemma fr_combine_app : forall (X Y : Type) (a : list X) (b : list Y) c d, length a = length b ->
  combine (a ++ c) (b ++ d) = combine a b ++ combine c d.
Proof.
  intros X Y a. induction a as [|x a IH]; intros [|y b] c d Hl; cbn [length] in Hl; try discriminate Hl.
  - reflexivity.
  - cbn [app combine]. f_equal. apply IH. lia.
Qed.
Lemma fr_combine_rev : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  List.rev (combine l1 l2) = combine (List.rev l1) (List.rev l2).
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] Hl; cbn [length] in Hl; try discriminate Hl.
  - reflexivity.
  - cbn [combine List.rev]. rewrite IH by lia. rewrite fr_combine_app by (rewrite !length_rev; lia).
    reflexivity.
Qed.
Lemma fr_combine_firstn : forall (X Y : Type) n (l1 : list X) (l2 : list Y),
  combine (firstn n l1) (firstn n l2) = firstn n (combine l1 l2).
Proof.
  intros X Y n. induction n as [|n IH]; intros l1 l2; [reflexivity|].
  destruct l1 as [|x l1], l2 as [|y l2]; cbn [firstn combine]; try reflexivity.
  f_equal. apply IH.
Qed.
Lemma fr_combine_skipn : forall (X Y : Type) n (l1 : list X) (l2 : list Y),
  combine (skipn n l1) (skipn n l2) = skipn n (combine l1 l2).
Proof.
  intros X Y n. induction n as [|n IH]; intros l1 l2; [reflexivity|].
  destruct l1 as [|x l1], l2 as [|y l2]; cbn [skipn combine].
  - reflexivity.
  - reflexivity.
  - destruct (skipn n l1); reflexivity.
  - apply IH.
Qed.
(* the table and its sources lose the same row *)
Lemma fr_combine_remove : forall (X Y : Type) i (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  combine (relay_remove_b_c.remove_at i l1) (relay_remove_b_c.remove_at i l2) =
  relay_remove_b_c.remove_at i (combine l1 l2).
Proof.
  intros X Y i l1 l2 Hl. unfold relay_remove_b_c.remove_at.
  rewrite (fr_combine_rev _ _ l1 l2 Hl).
  assert (Hr : length (List.rev l1) = length (List.rev l2)) by (rewrite !length_rev; exact Hl).
  destruct (List.rev l1) as [|a1 r1], (List.rev l2) as [|a2 r2]; cbn [length] in Hr; try discriminate Hr.
  - reflexivity.
  - cbn [combine]. assert (Hr' : length r1 = length r2) by lia.
    rewrite (fr_combine_rev _ _ r1 r2 Hr').
    assert (E1 : length (combine (List.rev r1) (List.rev r2)) = length (List.rev r1))
      by (rewrite length_combine, !length_rev; lia).
    assert (E2 : length (List.rev r2) = length (List.rev r1)) by (rewrite !length_rev; lia).
    rewrite E1, E2.
    destruct (Nat.eqb i (length (List.rev r1))); [reflexivity|].
    rewrite fr_combine_app by (rewrite !length_firstn, !length_rev; lia). cbn [combine].
    rewrite fr_combine_firstn, fr_combine_skipn. reflexivity.
Qed.
Lemma fr_F2_nth : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2, Forall2 R l1 l2 ->
  forall i d1 d2, (i < length l1)%nat -> R (nth i l1 d1) (nth i l2 d2).
Proof.
  intros T1 T2 R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros [|i] d1 d2 Hi; cbn [length] in Hi;
    try lia; cbn [nth]; [exact Hxy | apply IH; lia].
Qed.
Lemma fr_combine_of_F2 : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2, Forall2 R l1 l2 ->
  forall q, In q (combine l1 l2) -> R (fst q) (snd q).
Proof.
  intros T1 T2 R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros q Hq; cbn [combine In] in Hq;
    [destruct Hq|].
  destruct Hq as [<- | Hq]; [exact Hxy | exact (IH q Hq)].
Qed.
Lemma fr_F2_of_combine : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2, length l1 = length l2 ->
  (forall q, In q (combine l1 l2) -> R (fst q) (snd q)) -> Forall2 R l1 l2.
Proof.
  intros T1 T2 R l1. induction l1 as [|x l1 IH]; intros [|y l2] Hl Hq; cbn [length] in Hl; try discriminate Hl.
  - constructor.
  - constructor.
    + exact (Hq (x, y) (or_introl eq_refl)).
    + apply IH; [lia | intros q Hin; apply Hq; right; exact Hin].
Qed.
Lemma fr_sum_perm : forall (T : Type) (f : T -> Z) l l', Permutation l l' ->
  fold_right Z.add 0 (map f l) = fold_right Z.add 0 (map f l').
Proof. intros T f l l' H. induction H; cbn [map fold_right]; lia. Qed.
Lemma fr_keys_total_nonneg : forall ks, 0 <= gestures_end_b_c.keys_total ks.
Proof. unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right]; lia. Qed.
Lemma fr_pair_cost_nonneg : forall e p, 0 <= fr_pair_cost e p.
Proof.
  intros e p. unfold fr_pair_cost. pose proof (fr_keys_total_nonneg (re_keys e)).
  destruct (re_skip e =? 0); lia.
Qed.
(* the controller's flags against g_gone (fr_gone's text) through the sends: send_line keeps g_client and
   g_send_dead, and sets g_client_broken only from g_send_dead when the send is not off (send_off: closed, broken or
   empty; W_contract.v sl_ctl, dr_ctl; send_line_c.v:21) *)
Definition fr_ctl_ok (gn : Z) (c : ctl) : Prop :=
  (gn = 0 -> ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0) /\ (gn = 1 -> ct_cl c = -1 \/ ct_br c = 1 \/ ct_dd c = 1).
Lemma fr_ctl_step : forall gn c c', ct_cl c' = ct_cl c -> ct_dd c' = ct_dd c ->
  (ct_br c' = ct_br c \/ (ct_br c' = ct_dd c /\ ct_br c <> 1)) -> fr_ctl_ok gn c -> fr_ctl_ok gn c'.
Proof.
  intros gn c c' E1 E2 E3 (G0 & G1). unfold fr_ctl_ok. rewrite E1, E2. split.
  - intros Hg. destruct (G0 Hg) as (A1 & A2 & A3).
    destruct E3 as [E3 | (E3 & _)]; rewrite E3; [exact (conj A1 (conj A2 A3)) | exact (conj A1 (conj A3 A3))].
  - intros Hg. destruct (G1 Hg) as [A1 | [A2 | A3]]; [left; exact A1 | | right; right; exact A3].
    destruct E3 as [E3 | (_ & N)]; [right; left; rewrite E3; exact A2 | contradiction].
Qed.
Lemma fr_ctl_sl : forall gn c len, fr_ctl_ok gn c -> fr_ctl_ok gn (sl_ctl c len).
Proof.
  intros gn c len Hc. apply (fr_ctl_step gn c); [reflexivity | reflexivity | | exact Hc].
  unfold sl_ctl. cbn [ct_br].
  destruct (send_line_c.send_off (ct_cl c) (ct_br c) len) eqn:E; [left; reflexivity|].
  right. split; [reflexivity|]. unfold send_line_c.send_off in E.
  apply orb_false_iff in E as [E _]. apply orb_false_iff in E as [_ E]. apply Z.eqb_neq in E. exact E.
Qed.
Lemma fr_ctl_dr : forall gn c h ev, fr_ctl_ok gn c -> fr_ctl_ok gn (dr_ctl c h ev).
Proof.
  intros gn c h ev Hc. apply (fr_ctl_step gn c); [reflexivity | reflexivity | | exact Hc].
  unfold dr_ctl. cbn [ct_br].
  destruct (send_line_c.send_off (ct_cl c) (ct_br c) (dr_tot h)) eqn:E; [left; reflexivity|].
  right. split; [reflexivity|]. unfold send_line_c.send_off in E.
  apply orb_false_iff in E as [E _]. apply orb_false_iff in E as [_ E]. apply Z.eqb_neq in E. exact E.
Qed.
Lemma fr_ctl_sends : forall gn mx Bs c O cap c' O' cap', fr_ctl_ok gn c ->
  sl_sends mx c O cap Bs = (c', O', cap') -> fr_ctl_ok gn c'.
Proof.
  intros gn mx Bs. induction Bs as [|Bl r IH]; intros c O cap c' O' cap' Hc Hs; cbn [sl_sends] in Hs.
  - assert (E : c = c') by exact (f_equal (fun q => fst (fst q)) Hs). subst c'. exact Hc.
  - exact (IH _ _ _ c' O' cap' (fr_ctl_sl gn c _ Hc) Hs).
Qed.

(* remove-s2 _remove.v:5393: the counting invariant loses one open slot and gains one operation; the pairing
   loses slot si's row (the row at j0: slot si holds entry j0's fd, open slots' fds are distinct); the cost drops
   by that row's; the flags pass through drain's and the gesture ends' sends.  out2, ev5, O2 and cap2 are not
   read. *)
Lemma RI_rm_step_holds : RI_rm_step_obl.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HRI Hat Hrr _ _.
  pose proof HRI as ((HC & Hnfd) & HR & Hn & HG).
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  destruct Hat as (_ & _ & _ & _ & Hsi & Hh & Hj0 & Hfd0 & _).
  pose proof (Forall2_length HF) as Hlh.
  assert (Hj0h : (j0 < length hj)%nat) by lia.
  assert (Hk : lm_k m <= rm_k' cx m) by (unfold rm_k'; destruct (lm_k m + 1 <? c_n cx); lia).
  (* the row at j0 is slot si's *)
  assert (Hs0 : snd (nth j0 hj (h, si)) = si).
  { pose proof (fr_F2_nth _ _ _ _ _ HF j0 relay_remove_b_c.no_entry (h, si) Hj0) as (H4 & Hn0 & Hf0 & _).
    destruct (Nat.eq_dec (snd (nth j0 hj (h, si))) si) as [E | Ne]; [exact E | exfalso].
    apply (RI_fds_holds cx t m _ si _ h HRI H4 Hsi Ne Hn0 Hh). rewrite Hf0. exact Hfd0. }
  pose proof (fr_remove_perm _ hj j0 (h, si) Hj0h) as Hperm.
  pose proof (fr_remove_perm _ (lm_es m) j0 relay_remove_b_c.no_entry Hj0) as Hperm_es.
  (* no other row follows slot si *)
  assert (HNDs2 : List.NoDup (map snd (nth j0 hj (h, si) :: relay_remove_b_c.remove_at j0 hj))).
  { assert (Hpm : Permutation (map snd hj) (map snd (nth j0 hj (h, si) :: relay_remove_b_c.remove_at j0 hj)))
      by (apply Permutation_map; exact Hperm).
    eapply Permutation_NoDup; [exact Hpm | exact (proj1 (NoDup_ListNoDup _) HNDs)]. }
  cbn [map] in HNDs2. apply NoDup_cons_iff in HNDs2 as [Hni HNDs2].
  assert (Hother : forall y, In y (relay_remove_b_c.remove_at j0 hj) -> snd y <> si).
  { intros y Hy E. apply Hni. rewrite Hs0, <- E. apply in_map. exact Hy. }
  (* the new table and its sources, row by row *)
  assert (Hcomb : combine (relay_remove_b_c.remove_at j0 (lm_es m)) (relay_remove_b_c.remove_at j0 hj) =
                  relay_remove_b_c.remove_at j0 (combine (lm_es m) hj)) by exact (fr_combine_remove _ _ j0 _ _ Hlh).
  assert (HjC : (j0 < length (combine (lm_es m) hj))%nat) by (rewrite length_combine; lia).
  pose proof (fr_remove_perm _ (combine (lm_es m) hj) j0 (relay_remove_b_c.no_entry, (h, si)) HjC) as HpermC.
  assert (HlenR : length (relay_remove_b_c.remove_at j0 (lm_es m)) = length (relay_remove_b_c.remove_at j0 hj)).
  { pose proof Hperm as L1. pose proof Hperm_es as L2.
    apply Permutation_length in L1. apply Permutation_length in L2. cbn [length] in L1, L2. lia. }
  assert (HF' : Forall2 (fr_pair_ok (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) (t + 1))
                  (relay_remove_b_c.remove_at j0 (lm_es m)) (relay_remove_b_c.remove_at j0 hj)).
  { apply fr_F2_of_combine; [exact HlenR|]. intros [qe qp] Hq.
    assert (Hq0 : In (qe, qp) (combine (lm_es m) hj)).
    { rewrite Hcomb in Hq. eapply Permutation_in; [apply Permutation_sym; exact HpermC | right; exact Hq]. }
    pose proof (fr_combine_of_F2 _ _ _ _ _ HF (qe, qp) Hq0) as Hpq. cbn [fst snd] in Hpq |- *.
    assert (Hqp : In qp (relay_remove_b_c.remove_at j0 hj)) by (eapply in_combine_r; exact Hq).
    assert (Hsq : si <> snd qp) by (intros E; exact (Hother qp Hqp (eq_sym E))).
    destruct Hpq as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
    unfold fr_pair_ok. cbn [rm_mk lm_hs]. rewrite (fr_rm_set_nth_other _ si (snd qp) _ _ _ Hsq).
    unfold SlotInv.WRITE_MAX in *.
    refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
      (conj _ H11)))))))))). lia. }
  assert (Hnd' : NoDup (map re_fd (relay_remove_b_c.remove_at j0 (lm_es m)))).
  { apply NoDup_ListNoDup.
    assert (Hpm : Permutation (map re_fd (lm_es m))
                    (map re_fd (nth j0 (lm_es m) relay_remove_b_c.no_entry :: relay_remove_b_c.remove_at j0 (lm_es m))))
      by (apply Permutation_map; exact Hperm_es).
    assert (X : List.NoDup (map re_fd (nth j0 (lm_es m) relay_remove_b_c.no_entry ::
                                        relay_remove_b_c.remove_at j0 (lm_es m))))
      by (eapply Permutation_NoDup; [exact Hpm | exact (proj1 (NoDup_ListNoDup _) Hnd)]).
    cbn [map] in X. apply NoDup_cons_iff in X as [_ X]. exact X. }
  assert (HFa : forall P : rentry -> Prop, Forall P (lm_es m) -> Forall P (relay_remove_b_c.remove_at j0 (lm_es m))).
  { intros P HP. rewrite Forall_forall in HP |- *. intros x Hx. apply HP.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm_es | right; exact Hx]. }
  (* the cost drops by the removed row's *)
  assert (Hcr : fr_cost (relay_remove_b_c.remove_at j0 (lm_es m)) (relay_remove_b_c.remove_at j0 hj)
                <= fr_cost (lm_es m) hj).
  { unfold fr_cost. rewrite Hcomb.
    rewrite (fr_sum_perm _ (fun q => fr_pair_cost (fst q) (snd q)) _ _ HpermC). cbn [map fold_right].
    pose proof (fr_pair_cost_nonneg (fst (nth j0 (combine (lm_es m) hj) (relay_remove_b_c.no_entry, (h, si))))
      (snd (nth j0 (combine (lm_es m) hj) (relay_remove_b_c.no_entry, (h, si))))). lia. }
  split; [|split; [|split; [exact Hn|]]].
  - unfold fr_count, rm_mk. cbn [lm_nfd lm_hs].
    pose proof (fr_nopen_clear _ _ _ Hh ltac:(lia)) as Hop. lia.
  - unfold fr_relay. cbn [rm_mk lm_hs lm_es lm_nfd lm_k].
    split; [rewrite fr_rm_set_nth_length; exact Hlen|].
    split; [exact Hnd'|]. split; [exact (HFa _ Hrng)|]. split; [exact (HFa _ Hent)|].
    exists (relay_remove_b_c.remove_at j0 hj).
    split; [exact HF'|]. split; [exact (proj2 (NoDup_ListNoDup _) HNDs2)|].
    split.
    { intros j Hj Ho. destruct (Nat.eq_dec j si) as [-> | Ne].
      - apply fr_rm_set_nth_same. lia.
      - rewrite (fr_rm_set_nth_other _ si j _ _ _ (not_eq_sym Ne)). apply (Hcl j Hj).
        destruct (SlotInv.slot_open hj j) eqn:Eo; [exfalso | reflexivity].
        unfold SlotInv.slot_open in Eo, Ho. apply existsb_exists in Eo as (x & Hx & Hxj).
        apply Nat.eqb_eq in Hxj. subst x. apply in_map_iff in Hx as (y & Hyj & Hy).
        assert (Hy' : In y (nth j0 hj (h, si) :: relay_remove_b_c.remove_at j0 hj))
          by (eapply Permutation_in; [exact Hperm | exact Hy]).
        destruct Hy' as [Ey | Hy'].
        + apply Ne. rewrite <- Hyj, <- Ey. exact Hs0.
        + assert (Ht : existsb (Nat.eqb j) (map snd (relay_remove_b_c.remove_at j0 hj)) = true).
          { apply existsb_exists. exists j. split; [|apply Nat.eqb_refl].
            apply in_map_iff. exists y. split; [exact Hyj | exact Hy']. }
          rewrite Ho in Ht. discriminate Ht. }
    split; lia.
  - change (fr_ctl_ok (lm_gn m) c2).
    destruct Hrr as [_ Hs]. eapply fr_ctl_sends; [|exact Hs].
    destruct (re_eof (rm_ent m j0) =? 0); [apply fr_ctl_dr; exact HG | exact HG].
Qed.

(* ---- ARM_drain's step (fuzz_reply.c:596-609): drain(r) feeds the picked source's pending bytes through the relay's
   entry j (W_LLVMFuzzerTestOneInput_drain.set_nth j e'), check_no_loss empties its expected list (slot si's source
   becomes set_exp_held h' E' H') *)
Lemma fr_Forall_dset : forall (T : Type) (P : T -> Prop) j x l, Forall P l -> P x ->
  Forall P (W_LLVMFuzzerTestOneInput_drain.set_nth j x l).
Proof.
  intros T P j x l. revert j. induction l as [|a l IH]; intros [|j] Hl Hx;
    cbn [W_LLVMFuzzerTestOneInput_drain.set_nth].
  - constructor.
  - constructor.
  - apply Forall_cons_iff in Hl as [_ Hl]. constructor; [exact Hx | exact Hl].
  - apply Forall_cons_iff in Hl as [Ha Hl]. constructor; [exact Ha | exact (IH j Hl Hx)].
Qed.
Lemma fr_dset_map_eq : forall (T U : Type) (f : T -> U) j x l d, (j < length l)%nat -> f x = f (nth j l d) ->
  map f (W_LLVMFuzzerTestOneInput_drain.set_nth j x l) = map f l.
Proof.
  intros T U f j x l d. revert j. induction l as [|a l IH]; intros [|j] Hj Hf; cbn [length] in Hj; try lia;
    cbn [W_LLVMFuzzerTestOneInput_drain.set_nth map nth] in Hf |- *.
  - rewrite Hf. reflexivity.
  - rewrite (IH j ltac:(lia) Hf). reflexivity.
Qed.
Lemma fr_F2_lift : forall (T1 T2 : Type) (R R' : T1 -> T2 -> Prop) (Q : T2 -> Prop) d2 l1 l2,
  Forall2 R l1 l2 -> (forall a b, Q b -> R a b -> R' a b) ->
  (forall k, (k < length l2)%nat -> Q (nth k l2 d2)) -> Forall2 R' l1 l2.
Proof.
  intros T1 T2 R R' Q d2 l1 l2 H HQ. induction H as [|a b l1 l2 Hab _ IH]; intros Hk; constructor.
  - apply HQ; [exact (Hk 0%nat ltac:(cbn [length]; lia)) | exact Hab].
  - apply IH. intros k Hkl. exact (Hk (S k) ltac:(cbn [length]; lia)).
Qed.
Lemma fr_F2_dset : forall (T1 T2 : Type) (R R' : T1 -> T2 -> Prop) (Q : T2 -> Prop) d2 j x y l1 l2,
  Forall2 R l1 l2 -> R' x y -> (forall a b, Q b -> R a b -> R' a b) ->
  (forall k, k <> j -> (k < length l2)%nat -> Q (nth k l2 d2)) ->
  Forall2 R' (W_LLVMFuzzerTestOneInput_drain.set_nth j x l1) (W_LLVMFuzzerTestOneInput_drain.set_nth j y l2).
Proof.
  intros T1 T2 R R' Q d2 j x y l1 l2 H Hxy HQ. revert j.
  induction H as [|a b l1 l2 Hab Hrest IH]; intros [|j] Hk; cbn [W_LLVMFuzzerTestOneInput_drain.set_nth].
  - constructor.
  - constructor.
  - constructor; [exact Hxy|]. apply (fr_F2_lift _ _ R R' Q d2 l1 l2 Hrest HQ).
    intros k Hkl. exact (Hk (S k) ltac:(lia) ltac:(cbn [length]; lia)).
  - constructor.
    + apply HQ; [exact (Hk 0%nat ltac:(lia) ltac:(cbn [length]; lia)) | exact Hab].
    + apply IH. intros k Hkn Hkl. exact (Hk (S k) ltac:(lia) ltac:(cbn [length]; lia)).
Qed.
Lemma fr_nopen_dset : forall hs i x y, nth i hs None = Some y -> (i < length hs)%nat ->
  nopen (W_LLVMFuzzerTestOneInput_drain.set_nth i (Some x) hs) = nopen hs.
Proof.
  intros hs i x y. unfold nopen. revert i. induction hs as [|o hs IH]; intros [|i] Hn Hi;
    cbn [length] in Hi; try lia.
  - cbn [nth] in Hn. subst o. reflexivity.
  - cbn [nth] in Hn. pose proof (IH i Hn ltac:(lia)) as Hih.
    destruct o; cbn [W_LLVMFuzzerTestOneInput_drain.set_nth List.filter length]; lia.
Qed.
Lemma fr_cost_dset : forall es hj j e' p' d1 d2, length es = length hj -> (j < length es)%nat ->
  fr_cost (W_LLVMFuzzerTestOneInput_drain.set_nth j e' es) (W_LLVMFuzzerTestOneInput_drain.set_nth j p' hj) +
  fr_pair_cost (nth j es d1) (nth j hj d2) = fr_cost es hj + fr_pair_cost e' p'.
Proof.
  unfold fr_cost. induction es as [|e es IH]; intros [|p hj] [|j] e' p' d1 d2 Hl Hj; cbn [length] in Hl, Hj;
    try lia.
  - cbn [W_LLVMFuzzerTestOneInput_drain.set_nth combine map fold_right nth fst snd]. lia.
  - cbn [W_LLVMFuzzerTestOneInput_drain.set_nth combine map fold_right nth fst snd].
    pose proof (IH hj j e' p' d1 d2 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma fr_bzs_line : forall l, SlotReads.zrange l -> bzs (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|z l IH]; intros Hl; [reflexivity|]. apply Forall_cons_iff in Hl as [Hz Hl].
  unfold bzs in *. cbn [map]. rewrite SlotReads.bz_lit by exact Hz. f_equal. apply IH. exact Hl.
Qed.
Lemma fr_bzs_lines : forall Ls, Forall SlotReads.zrange Ls -> map bzs (map (map (Z_to_bv 8)) Ls) = Ls.
Proof.
  induction Ls as [|l Ls IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [H1 H2]. cbn [map].
  rewrite fr_bzs_line by exact H1. f_equal. apply IH. exact H2.
Qed.
(* the entry with re_used replaced by its line's length: SlotInv.pair_cost of it is fr_pair_cost *)
Definition fr_ru (e : rentry) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (Z.of_nat (length (re_U e))) (re_cap e) (re_hp e)
     (re_kh e) (re_pad2 e) (re_keys e) (re_U e) (re_junk e).

(* _drain.v:625 with the arm's two premises: the counting invariant keeps its open count (slot si stays open); row j
   (slot si's) takes the drained entry and source; its cost does not grow (SlotPass2Aux.p2_pair_cost); its expected
   list's capacity is ecap_ok (SlotDrain3.drain3_ecap, from pending <= WRITE_MAX * t < 2 ^ 25); its held list's
   capacity stays < 2 ^ 24 (the premise); the flags pass through drain's send (dr_ctl).  out', O', cap', ev' and LB
   are not read. *)
Lemma RI_drain_step_fix_holds : RI_drain_step_fix_obl.
Proof.
  intros cx t m si h j e' h' c' O' cap' out' ev' LB E' H' Ht HRI Hat Hpick Hj Hfdj Heof Hok Hcb.
  pose proof HRI as ((HC & Hnfd) & HR & Hn & HG).
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  destruct Hpick as (_ & Hsi & Hh).
  (* dr_step_ok (commit bb9dae5d905 _drain.v:549) has drain's paddings / capacity facts before check_no_loss's half *)
  destruct Hok as (Ofd & Oeof & _ & _ & _ & Oskip & _ & _ & OND & OSS & Ohfd & _ & _ & OHP & Ooff & OST & Oexp &
    Oheld & OS2 & OW2 & _ & Oc' & _ & _ & Opad1 & Opad2 & Oecap & OE0 & _ & OEcap & OHND & OHt & OHcap).
  pose proof (Forall2_length HF) as Hlh.
  assert (Hjh : (j < length hj)%nat) by lia.
  assert (Hk : lm_k m <= dr_k' cx m) by (unfold dr_k'; destruct (lm_k m + 1 <? c_n cx); lia).
  (* the row at j is slot si's *)
  pose proof (fr_F2_nth _ _ _ _ _ HF j dr_e0 (h, si) Hj) as Hp0.
  assert (Hs0 : snd (nth j hj (h, si)) = si).
  { destruct Hp0 as (H4 & Hn0 & Hf0 & _).
    destruct (Nat.eq_dec (snd (nth j hj (h, si))) si) as [E | Ne]; [exact E | exfalso].
    apply (RI_fds_holds cx t m _ si _ h HRI H4 Hsi Ne Hn0 Hh). rewrite Hf0. exact Hfdj. }
  assert (Ep0 : nth j hj (h, si) = (h, si)).
  { destruct Hp0 as (_ & Hn0 & _). rewrite Hs0, Hh in Hn0. injection Hn0 as Ef.
    apply injective_projections; [exact (eq_sym Ef) | exact Hs0]. }
  rewrite Ep0 in Hp0.
  destruct Hp0 as (_ & _ & _ & Hre & Hss & _ & Hexp0 & Hec & Hhc & Hpe & Hoff).
  cbn [fst snd] in Hre, Hss, Hexp0, Hec, Hhc, Hpe, Hoff.
  destruct (Hre Heof) as (S1 & W1).
  (* the other rows follow other slots *)
  assert (Hoth : forall k, k <> j -> (k < length hj)%nat -> snd (nth k hj (h, si)) <> si).
  { intros k Hkj Hkl E. apply Hkj.
    pose proof (proj1 (NoDup_ListNoDup _) HNDs) as ND.
    pose proof (proj1 (NoDup_nth (map snd hj) (snd (h, si))) ND) as ND'.
    apply ND'; [rewrite length_map; exact Hkl | rewrite length_map; exact Hjh |].
    rewrite !map_nth. rewrite Hs0. exact E. }
  (* entry j's skip flag, and so the sources' overlong flags *)
  pose proof Hent as Hent'. rewrite Forall_forall in Hent'.
  pose proof Hrng as Hrng'. rewrite Forall_forall in Hrng'.
  assert (He : In (nth j (lm_es m) dr_e0) (lm_es m)) by (apply nth_In; exact Hj).
  destruct (Hent' _ He) as (_ & _ & _ & _ & Hsk).
  assert (O1 : hs_overlong h = 0 \/ hs_overlong h = 1) by (rewrite <- S1; exact Hsk).
  assert (Hsk' : re_skip e' = 0 \/ re_skip e' = 1).
  { rewrite Oskip. match goal with |- context [if ?b then _ else _] => destruct b end; [right | left]; reflexivity. }
  assert (O2 : hs_overlong h' = 0 \/ hs_overlong h' = 1) by (rewrite <- OS2; exact Hsk').
  (* the expected list after the drain holds exactly the drained lines *)
  assert (Etx : texts (hs_expected h') = dr_lines h).
  { unfold texts.
    replace (map (fun r => bzs (snd r)) (hl_recs (hs_expected h')))
      with (map bzs (map snd (hl_recs (hs_expected h')))) by (rewrite List.map_map; reflexivity).
    rewrite Oexp, Hexp0. cbn [map app]. apply fr_bzs_lines.
    exact (proj1 (SlotReads.lines_range (bzs (pending_stream h)) (hs_state h) (SlotReads.zrange_bzs (hs_W h))
      (SlotReads.zrange_bzs (pending_stream h)))). }
  (* its capacity is ecap_ok: at most 65535 * 511 < 2 ^ 25 pending bytes *)
  assert (Hecap : SlotInv.ecap_ok (hl_cap E')).
  { rewrite OEcap, Oecap. unfold dr_fin.
    apply SlotDrain3.drain3_ecap; [exact Hoff | exact Hec |].
    assert (P25 : 2 ^ 25 = 33554432) by reflexivity.
    unfold hl_n. rewrite Hexp0. cbn [length]. unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia. }
  (* row j's cost does not grow *)
  assert (Hpc : fr_pair_cost e' (set_exp_held h' E' H', si) <= fr_pair_cost (nth j (lm_es m) dr_e0) (h, si))
    by exact (SlotPass2Aux.p2_pair_cost (fr_ru (nth j (lm_es m) dr_e0)) (fr_ru e') h h' si S1 W1 O1 eq_refl
                OS2 OW2 O2 eq_refl OST OHP OND OSS).
  pose proof (fr_cost_dset (lm_es m) hj j e' (set_exp_held h' E' H', si) dr_e0 (h, si) Hlh Hj) as Hcd.
  rewrite Ep0 in Hcd.
  split; [|split; [|split; [exact Hn|]]].
  - unfold fr_count, dr_step. cbn [lm_nfd lm_hs].
    rewrite (fr_nopen_dset _ _ _ _ Hh ltac:(lia)). lia.
  - unfold fr_relay, dr_step. cbn [lm_hs lm_es lm_nfd lm_k].
    split; [rewrite W_LLVMFuzzerTestOneInput_drain.set_nth_length; exact Hlen|].
    split; [rewrite (fr_dset_map_eq _ _ re_fd j e' (lm_es m) dr_e0 Hj Ofd); exact Hnd|].
    split.
    { apply fr_Forall_dset; [exact Hrng|]. cbv beta. rewrite Ofd. exact (Hrng' _ He). }
    split.
    { apply fr_Forall_dset; [exact Hent|]. unfold fr_entry_ok.
      split; [rewrite Oeof, Heof; destruct (hs_closed h =? 1); [right | left]; reflexivity|].
      split; [exact Opad1|]. split; [exact Opad2|]. split; [exact OND | exact Hsk']. }
    exists (W_LLVMFuzzerTestOneInput_drain.set_nth j (set_exp_held h' E' H', si) hj).
    split.
    { apply (fr_F2_dset _ _ (fr_pair_ok m t) _ (fun b => snd b <> si) (h, si)); [exact HF | | |].
      - (* the drained row *)
        unfold fr_pair_ok. cbn [fst snd lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_drain.set_nth_same _ si (Some (set_exp_held h' E' H')) (lm_hs m) None
          ltac:(lia)).
        refine (conj Hsi (conj eq_refl (conj _ (conj _ (conj _ (conj OHND (conj OE0 (conj Hecap
          (conj _ (conj _ _)))))))))).
        + cbn [hs_fd set_exp_held]. rewrite Ohfd, Ofd. exact (eq_sym Hfdj).
        + intros _. split; [exact OS2 | exact OW2].
        + change (same_set (drain_b_c.keys_texts (re_keys e')) (texts H')).
          rewrite OHt, Oheld, Etx. intros y. rewrite (OSS y).
          exact (SlotReads.upds_same_set (dr_lines h) _ _ Hss y).
        + change (hl_cap H' < 2 ^ 24).
          assert (P22 : 2 ^ 22 = 4194304) by reflexivity. assert (P24 : 2 ^ 24 = 16777216) by reflexivity.
          rewrite Oheld in OHcap, Hcb. lia.
        + unfold pending_stream. cbn [hs_pending hs_off set_exp_held]. rewrite OHP. cbn [length].
          unfold SlotInv.WRITE_MAX. lia.
        + cbn [hs_off set_exp_held]. rewrite Ooff. lia.
      - (* the other rows *)
        intros a b Hb Hab. cbv beta in Hb.
        destruct Hab as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
        unfold fr_pair_ok. cbn [lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_drain.set_nth_other _ si (snd b) _ _ _ (not_eq_sym Hb)).
        unfold SlotInv.WRITE_MAX in *.
        refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
          (conj _ H11)))))))))). lia.
      - intros k Hkj Hkl. exact (Hoth k Hkj Hkl). }
    split.
    { rewrite (fr_dset_map_eq _ _ snd j (set_exp_held h' E' H', si) hj (h, si) Hjh ltac:(rewrite Ep0; reflexivity)).
      exact HNDs. }
    split.
    { intros i Hi Ho.
      assert (Ho' : SlotInv.slot_open hj i = false).
      { unfold SlotInv.slot_open in *.
        rewrite (fr_dset_map_eq _ _ snd j (set_exp_held h' E' H', si) hj (h, si) Hjh
          ltac:(rewrite Ep0; reflexivity)) in Ho. exact Ho. }
      assert (Hne : si <> i).
      { intros E. subst i. rewrite (Hcl si Hi Ho') in Hh. discriminate Hh. }
      rewrite (W_LLVMFuzzerTestOneInput_drain.set_nth_other _ si i _ _ _ Hne). exact (Hcl i Hi Ho'). }
    split; lia.
  - change (fr_ctl_ok (lm_gn m) c'). rewrite Oc'. apply fr_ctl_dr. exact HG.
Qed.
End rinv.

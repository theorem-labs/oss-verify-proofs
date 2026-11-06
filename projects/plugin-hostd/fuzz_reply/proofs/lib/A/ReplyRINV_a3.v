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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV.v, with its module names changed; 137 of its 221 lines of code are new or changed and 1107 lines of the source are left out. *)
(* plugin-hostd/fuzz_reply image A, TOPX group RI-a: five model rules of the entry loop's invariant RINV, proved at
   RINV := fr_RINV (lib/A/ReplyRINV.v:227).  Each lemma concludes ReplyRINV.v's `_obl` text.  That text is token for
   token the Section hypothesis of the same name in W_LLVMFuzzerTestOneInput_top_x.v (a working branch
   bb9dae5d905) after the renaming RINV <-> fr_RINV, with the premises in the same order and no lf_base:
     RI_write_skip_holds  : RI_write_skip_obl  (ReplyRINV.v:317, top_x.v:226; _write.v:182)
     RI_write_push_holds  : RI_write_push_obl  (ReplyRINV.v:322, top_x.v:232; _write.v:188)
     RI_event_step_holds  : RI_event_step_obl  (ReplyRINV.v:392, top_x.v:275; _event.v:1029 on event-c-omx-reader)
     RI_drain_skip_holds  : RI_drain_skip_obl  (ReplyRINV.v:242, top_x.v:364; _drain.v:584)
     RI_pair_holds        : RI_pair_obl        (ReplyRINV.v:283, top_x.v:384; _drain.v:642)
   In four of the five rows every name resolves to the same constant in both texts (_cut.v, _write.v, _drain.v,
   Prog/HarnessRep.v, RelayRep.v, ListRep.v, whose definitions are the same at atop 5ab58d26200 and integ
   bb9dae5d905), so top_x's hypothesis is the `_holds` lemma itself.  The exception is
   RI_event_step: in the `_obl`, ev_evt and ev_step are ReplyRINV.v's copies (ReplyRINV.v:330-345), and in top_x they
   are W_LLVMFuzzerTestOneInput_event.v's (:998-1020).  The two have the same text, so RI_event_step_x below states
   top_x's text with _event.v's constants and follows from RI_event_step_holds by conversion.
   The Section below has ReplyRINV.v's Section rinv shape (the same Context and Variables), so each lemma generalizes
   as ReplyRINV.v's own `_holds` do.  The proofs use ReplyRINV.v's lemmas (fr_step_k, fr_ctl_sl, RI_fds_holds,
   fr_F2_nth, fr_Forall2_map, fr_Forall2_r) and the helpers below.
   - RI_write_skip, RI_event_step, RI_drain_skip: the step keeps the slots, the relay table and g_nfd, moves the
     cursor forward (the input bytes are unsigned, so fuzz_u16 and fuzz_take never move it back) and keeps the
     controller flags' link to g_gone (relay_event's send_line keeps it: fr_ctl_sl).
   - RI_write_push (fuzz_reply.c:705-707, list_push of fuzz_take(fuzz_u16) bytes onto the picked source's pending
     list): only slot si's source changes, and only its pending list.  Its unread stream grows by at most the
     wr_n <= 65535 = WRITE_MAX pushed bytes, so fr_pair_ok's bound pending <= WRITE_MAX * t steps to t + 1; the cost
     grows by at most wr_n, and wr_k2 = wr_k1 + wr_c + wr_n >= k + 1 + wr_n, with wr_k2 <= n.
   - RI_pair: the relay row j with the picked source's fd is slot si's row (open slots' fds are distinct:
     RI_fds_holds), so fr_pair_ok's re_eof = 0 clause gives the skip and line facts, and fr_entry_ok the pads. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section rinv_a3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ReplyRINV.v Section rinv's variables (ReplyRINV.v:131-137); the five lemmas name none of them *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.

(* ---- the input cursor: the program reads bytes as unsigned values in [0, 256) *)
Lemma a3_in_byte_range : forall cx i, 0 <= in_byte cx i < 256.
Proof.
  intros cx i. unfold in_byte.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) (c_pl cx) (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.

(* ARM_write's cursor (_write.v:176-185): the op and pick bytes, fuzz_u16's two bytes, then fuzz_take's n bytes, with
   0 <= n <= 65535 and the whole run inside the input *)
Lemma a3_wr_k : forall cx m, 0 <= lm_k m < c_n cx ->
  lm_k m + 1 <= wr_k1 cx m /\ wr_k1 cx m <= c_n cx /\ 0 <= wr_c cx m /\ 0 <= wr_n cx m <= SlotInv.WRITE_MAX /\
  wr_k2 cx m = wr_k1 cx m + wr_c cx m + wr_n cx m /\ wr_k1 cx m + wr_c cx m + wr_n cx m <= c_n cx.
Proof.
  intros cx m Hk.
  assert (K1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  pose proof (a3_in_byte_range cx (wr_k1 cx m)) as B1.
  pose proof (a3_in_byte_range cx (wr_k1 cx m + 1)) as B2.
  assert (HU : 0 <= wr_u cx m <= 65535).
  { unfold wr_u. destruct (2 <=? wr_rem cx m); [lia|]. destruct (wr_rem cx m =? 1); lia. }
  assert (HR : wr_rem cx m = c_n cx - wr_k1 cx m) by reflexivity.
  assert (HC : wr_c cx m = Z.min 2 (wr_rem cx m)) by reflexivity.
  assert (HN : wr_n cx m = Z.min (wr_u cx m) (wr_rem cx m - wr_c cx m)) by reflexivity.
  unfold wr_k2, SlotInv.WRITE_MAX. lia.
Qed.

(* fuzz_take's bytes: at most n of them *)
Lemma a3_wr_x_len : forall cx m, 0 <= wr_n cx m -> Z.of_nat (length (wr_x cx m)) <= wr_n cx m.
Proof. intros cx m Hn. unfold wr_x. rewrite length_firstn. lia. Qed.

(* ---- RI_write_skip (_write.v:182): no source picked, or fuzz_take took no byte: only the cursor moves *)
Lemma RI_write_skip_holds : RI_write_skip_obl.
Proof.
  intros cx t m H Hk _ _. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold wr_skip. cbn [lm_k]. pose proof (a3_wr_k cx m Hk). lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* ---- RI_event_step (_event.v:1029): relay_event sends the event line; the slots, the table and g_nfd stay *)
Lemma RI_event_step_holds : RI_event_step_obl.
Proof.
  intros cx t m e v out' H Hk _ _ _ _. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold ev_step, ev_k2, ev_k1, ev_len, ev_cons2, ev_u16. cbn [lm_k].
    pose proof (a3_in_byte_range cx (lm_k m + 1)). pose proof (a3_in_byte_range cx (lm_k m + 2)).
    destruct (Z.leb_spec 1 (c_n cx - lm_k m - 1)); destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); lia.
  - destruct H as (_ & _ & _ & HG). pose proof (fr_ctl_sl (lm_gn m) (lm_c m) (re_len e) HG) as X.
    unfold fr_gone, ev_step, ev_ctl. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. exact X.
Qed.

(* top_x.v:275's RI_event_step at RINV := fr_RINV, verbatim, with its ev_evt / ev_step (W_LLVMFuzzerTestOneInput_event.v,
   the same text as ReplyRINV.v's copies) *)
Lemma RI_event_step_x : forall cx t m e v out',
  fr_RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  W_LLVMFuzzerTestOneInput_event.ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  fr_RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_event.ev_step cx m e v out').
Proof. exact RI_event_step_holds. Qed.

(* ---- RI_drain_skip (_drain.v:584): no relay entry to drain for the picked source: only the cursor moves *)
Lemma RI_drain_skip_holds : RI_drain_skip_obl.
Proof.
  intros cx t m si h H _ _ _. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold dr_skip, dr_k'. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* ---- RI_pair (_drain.v:642): the relay row with the picked source's fd is that source's row *)
Lemma RI_pair_holds : RI_pair_obl.
Proof.
  intros cx t m si h j HRI (_ & Hsi & Hh) Hj Hfdj Heof.
  pose proof HRI as (_ & HR & _).
  destruct HR as (_ & _ & _ & Hent & hj & HF & _ & _ & _).
  pose proof (fr_F2_nth _ _ _ _ _ HF j dr_e0 (h, si) Hj) as Hp0.
  assert (Hs0 : snd (nth j hj (h, si)) = si).
  { destruct Hp0 as (H4 & Hn0 & Hf0 & _).
    destruct (Nat.eq_dec (snd (nth j hj (h, si))) si) as [E | Ne]; [exact E | exfalso].
    apply (RI_fds_holds cx t m _ si _ h HRI H4 Hsi Ne Hn0 Hh). rewrite Hf0. exact Hfdj. }
  assert (Ep0 : nth j hj (h, si) = (h, si)).
  { destruct Hp0 as (_ & Hn0 & _). rewrite Hs0, Hh in Hn0. injection Hn0 as Ef.
    apply injective_projections; [exact (eq_sym Ef) | exact Hs0]. }
  rewrite Ep0 in Hp0.
  destruct Hp0 as (_ & _ & _ & Hre & _). cbn [fst snd] in Hre.
  destruct (Hre Heof) as (S1 & W1).
  rewrite Forall_forall in Hent.
  assert (He : In (nth j (lm_es m) dr_e0) (lm_es m)) by (apply nth_In; exact Hj).
  destruct (Hent _ He) as (_ & P1 & P2 & _).
  split; [exact S1|]. split; [exact W1|]. split; [exact P1 | exact P2].
Qed.

(* ---- RI_write_push (_write.v:188): list_push onto slot si's pending list *)
(* the pushed record extends the unread stream by at most its bytes (an empty list's stream starts at hs_off) *)
Lemma a3_pending_push : forall h l' x d, hl_recs l' = hl_recs (hs_pending h) ++ [(d, x)] ->
  (length (pending_stream (set_pending h l')) <= length (pending_stream h) + length x)%nat.
Proof.
  intros h l' x d E. unfold pending_stream, set_pending. cbn [hs_pending hs_off]. rewrite E.
  destruct (hl_recs (hs_pending h)) as [|r rs]; cbn [app].
  - cbn [map concat snd length]. rewrite app_nil_r, length_skipn. lia.
  - rewrite List.map_app, concat_app, !length_app. cbn [map concat snd]. rewrite app_nil_r. lia.
Qed.
(* list_push changes no open count (slot si stays open) *)
Lemma a3_nopen_wset : forall hs i x y, nth i hs None = Some y -> (i < length hs)%nat ->
  nopen (W_LLVMFuzzerTestOneInput_write.set_nth i (Some x) hs) = nopen hs.
Proof.
  intros hs i x y. unfold nopen. revert i. induction hs as [|o hs IH]; intros [|i] Hn Hi;
    cbn [length] in Hi; try lia.
  - cbn [nth] in Hn. subst o. reflexivity.
  - cbn [nth] in Hn. pose proof (IH i Hn ltac:(lia)) as Hih.
    destruct o; cbn [W_LLVMFuzzerTestOneInput_write.set_nth List.filter length]; lia.
Qed.
(* the pairing after the push: slot si's row takes the pushed source, the other rows stay *)
Definition a3_wpair (l' : hlist) (si : nat) (p : hsrc * nat) : hsrc * nat :=
  if Nat.eqb (snd p) si then (set_pending (fst p) l', snd p) else p.
(* the cost grows by at most the growth w of slot si's unread stream (one row follows slot si) *)
Lemma a3_cost_wpair : forall l' si w es hj, 0 <= w ->
  (forall p, In p hj -> snd p = si ->
     Z.of_nat (length (pending_stream (set_pending (fst p) l'))) <= Z.of_nat (length (pending_stream (fst p))) + w) ->
  List.NoDup (map snd hj) ->
  fr_cost es (map (a3_wpair l' si) hj) <= fr_cost es hj + w.
Proof.
  intros l' si w es. unfold fr_cost. induction es as [|e es IH]; intros hj Hw0 Hw Hnd; [cbn; lia|].
  destruct hj as [|p hj]; [cbn; lia|].
  cbn [map combine fold_right fst snd]. cbn [map] in Hnd.
  apply NoDup_cons_iff in Hnd as [Hp Hnd].
  assert (Eg : a3_wpair l' si p = if Nat.eqb (snd p) si then (set_pending (fst p) l', snd p) else p)
    by reflexivity.
  rewrite Eg. destruct (Nat.eqb (snd p) si) eqn:E.
  - apply Nat.eqb_eq in E.
    assert (Et : map (a3_wpair l' si) hj = hj).
    { transitivity (map (fun q => q) hj); [|apply map_id].
      apply map_ext_in. intros q Hq. unfold a3_wpair.
      destruct (Nat.eqb (snd q) si) eqn:Eq; [|reflexivity].
      apply Nat.eqb_eq in Eq. exfalso. apply Hp. rewrite E, <- Eq. apply in_map. exact Hq. }
    rewrite Et. pose proof (Hw p (or_introl eq_refl) E) as Hb.
    unfold fr_pair_cost. cbn [fst]. lia.
  - pose proof (IH hj Hw0 (fun q Hq => Hw q (or_intror Hq)) Hnd). lia.
Qed.

Lemma RI_write_push_holds : RI_write_push_obl.
Proof.
  intros cx t m si h l' d ev HRI Hk _ (_ & Hsi & Hh) Hn Hrecs _ _.
  pose proof HRI as ((HC & Hnfd) & HR & Hcn26 & HG).
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  pose proof (a3_wr_k cx m Hk) as (K1 & K1n & Kc & (Kn0 & KnW) & K2 & K2n).
  pose proof (a3_wr_x_len cx m Kn0) as Hx.
  pose proof (a3_pending_push h l' (wr_x cx m) d Hrecs) as Hpp.
  assert (Hsil : (si < length (lm_hs m))%nat) by (rewrite Hlen; exact Hsi).
  (* a row that follows slot si has h as its source *)
  assert (Hrow : forall e p, fr_pair_ok m t e p -> snd p = si -> fst p = h).
  { intros e p Hp E. destruct Hp as (_ & Hn0 & _). rewrite E, Hh in Hn0. injection Hn0 as Ef.
    exact (eq_sym Ef). }
  assert (Esnd : map snd (map (a3_wpair l' si) hj) = map snd hj).
  { rewrite List.map_map. apply List.map_ext. intros [h0 j0]. unfold a3_wpair. cbn [fst snd].
    destruct (Nat.eqb j0 si); reflexivity. }
  split; [|split; [|split; [exact Hcn26|]]].
  - unfold fr_count, wr_push. cbn [lm_nfd lm_hs].
    rewrite (a3_nopen_wset _ _ _ _ Hh Hsil). lia.
  - unfold fr_relay, wr_push. cbn [lm_hs lm_es lm_nfd lm_k].
    split; [rewrite W_LLVMFuzzerTestOneInput_write.set_nth_length; exact Hlen|].
    split; [exact Hnd|]. split; [exact Hrng|]. split; [exact Hent|].
    exists (map (a3_wpair l' si) hj).
    split.
    { apply (fr_Forall2_map _ _ _ (fr_pair_ok m t)); [|exact HF].
      intros e [h0 j0] Hp. unfold a3_wpair. cbn [fst snd].
      destruct (Nat.eqb j0 si) eqn:Ej.
      - (* slot si's row: the pushed source *)
        apply Nat.eqb_eq in Ej. subst j0.
        assert (E0 : h0 = h) by exact (Hrow e (h0, si) Hp eq_refl). subst h0.
        destruct Hp as (H1 & _ & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
        cbn [fst snd] in H1, H3, H4, H5, H6, H7, H8, H9, H10, H11.
        unfold fr_pair_ok. cbn [fst snd lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_write.set_nth_same _ si _ (lm_hs m) None Hsil).
        refine (conj H1 (conj eq_refl (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
          (conj _ H11)))))))))).
        unfold SlotInv.WRITE_MAX in *. lia.
      - (* the other rows *)
        apply Nat.eqb_neq in Ej.
        destruct Hp as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
        cbn [fst snd] in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11.
        unfold fr_pair_ok. cbn [fst snd lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_write.set_nth_other _ si j0 _ _ None (not_eq_sym Ej)).
        unfold SlotInv.WRITE_MAX in *.
        refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
          (conj _ H11)))))))))). lia. }
    split; [rewrite Esnd; exact HNDs|].
    split.
    { intros i Hi Ho. unfold SlotInv.slot_open in Ho. rewrite Esnd in Ho.
      pose proof (Hcl i Hi Ho) as Hc0.
      assert (Hne : si <> i) by (intros E; subst i; rewrite Hh in Hc0; discriminate Hc0).
      rewrite (W_LLVMFuzzerTestOneInput_write.set_nth_other _ si i _ _ None Hne). exact Hc0. }
    assert (Hcw : fr_cost (lm_es m) (map (a3_wpair l' si) hj) <= fr_cost (lm_es m) hj + wr_n cx m).
    { apply a3_cost_wpair; [lia | | exact (proj1 (NoDup_ListNoDup _) HNDs)].
      intros p Hp E. destruct (fr_Forall2_r _ _ _ _ _ HF p Hp) as (e & _ & HRp).
      rewrite (Hrow e p HRp E). lia. }
    split; lia.
  - unfold fr_gone, wr_push, set_ev. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. exact HG.
Qed.

End rinv_a3.

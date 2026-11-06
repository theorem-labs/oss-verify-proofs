(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_event_x.v; 149 of its 219 lines of code are new or changed and 2573 lines of the source are left out. *)
(* WIP (a Theorem Labs lane's FREE-PIECES row B1c, a Theorem Labs lane): the event arm's two post-state LS rules at the instance
   LS := fr_LS B (lib/A/ReplyLS.v), RINV := fr_RINV (lib/A/ReplyRINV.v), MT := ameter_triv, MMAX := WR_MMAX.
   The arm is a working branch 1172d6d9065 lib/A/W_LLVMFuzzerTestOneInput_event.v:
   LS_event_relay :1034 and LS_event_step :1045.  Both tie their post-state (S1, S3) to S only by mo_le, which is True
   at ameter_triv, so as stated neither is provable for an LS that bounds live bytes.  Each is proved below at a
   PROPOSED text that keeps every premise and conclusion of the arm's text and adds premises the arm holds at its
   call (each named beside it, with the arm line or the callee post clause, all at 1172d6d9065):
   - lm_O m = [] and 0 <= lm_k m < c_n cx: the cut's registers, lregs_P1 :285 (HO, Hk at :1825);
   - 0 <= lm_cap m: amodel_at's aout_at (HMOD, :1824; HAO :2329), W_rep.v:177-178 (cap = 0 \/ 0 < cap);
   - malloc: W_journal.v:767 amalloc_cf_rule `ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]` (arm :2014 Hblq,
     n = slen + 1 = re_len e by :1965 Hrelen);
   - relay_event: W_contract.v:1048-1049 re_post `exists rest, Permutation (ablocks B ly S) (aout_blks cap out ++ rest)
     /\ Permutation (ablocks B ly' S') (aout_blks (sl_cap c mx no cap (re_len e)) out' ++ rest)` (arm :2363 HPERM5);
   - free: W_journal.v:789 afree_cf_rule `exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\
     ablocks B ly2 S2 = l1 ++ l2` (arm :2724, pa = q, n = slen + 1).
   LS_event_relay's first two conjuncts also need lm_cap m < MMAX (Hcap), which neither fr_LS nor fr_RINV gives and
   which the entry contract does not give either (g_capout is static across runs).  fr_LS_event_relay_Hcap_needed
   shows Hcap is exactly what is missing: the conclusion's first conjunct implies it.  The arm consumes those two
   conjuncts only as relay_event's re_spec premises (W_contract.v:1066-1067, arm :2361), and relay_event's proof
   (a working branch 378aa2733e7 W_relay_event.v:571-572) uses them only to derive send_line's sl_spec premises
   (W_contract.v:903-904: sl_maxr < MMAX, blocks_bytes S + sl_alloc <= LIVE_MAX).  fr_LS_event_relay_r proves that
   RELAXED pair (no lm_cap bound): with O cleared, every growth request (no + n) * 2 is at most 2 * re_len e.
   ev_evt / ev_step / ev_k2 are ReplyRINV.v's copies (ReplyRINV.v:330-345), the same text as the arm's :997-1016;
   ev_k1 / ev_len are the worktree's _event.v, the same text as the arm's :246-253. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.

(* ------------------------------------------------------------------ send_line's capacity and requests *)
(* a round sends n <= rem bytes *)
Lemma ev3_n_le : forall mx rem, (if negb (mx =? 0) && (mx <? rem) then mx else rem) <= rem.
Proof. intros mx rem. destruct (Z.ltb_spec mx rem); destruct (mx =? 0); cbn [negb andb]; lia. Qed.

(* the final capacity: the old one, or a request (no' + n) * 2 with no' + n <= no + rem *)
Lemma ev3_fin_run_le : forall fuel mx no cap rem, sl_fin_run fuel mx no cap rem <= Z.max cap (2 * (no + rem)).
Proof.
  induction fuel as [|f IH]; intros mx no cap rem; cbn [sl_fin_run]; [lia|].
  destruct (rem <=? 0); [lia|].
  pose proof (ev3_n_le mx rem) as Hn.
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
  destruct (cap <? no + n).
  - pose proof (IH mx (no + n) ((no + n) * 2) (rem - n)). lia.
  - pose proof (IH mx (no + n) cap (rem - n)). lia.
Qed.
(* the largest request *)
Lemma ev3_max_run_le : forall fuel mx no cap rem, sl_max_run fuel mx no cap rem <= Z.max 0 (2 * (no + rem)).
Proof.
  induction fuel as [|f IH]; intros mx no cap rem; cbn [sl_max_run]; [lia|].
  destruct (rem <=? 0); [lia|].
  pose proof (ev3_n_le mx rem) as Hn.
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
  destruct (cap <? no + n).
  - pose proof (IH mx (no + n) ((no + n) * 2) (rem - n)). lia.
  - pose proof (IH mx (no + n) cap (rem - n)). lia.
Qed.
(* the sum of the requests: each growth more than doubles the capacity, so the sum is at most twice the last *)
Lemma ev3_alloc_run_le : forall fuel mx no cap rem,
  sl_alloc_run fuel mx no cap rem <= Z.max 0 (4 * (no + rem) - 2 * Z.max cap 0).
Proof.
  induction fuel as [|f IH]; intros mx no cap rem; cbn [sl_alloc_run]; [lia|].
  destruct (rem <=? 0); [lia|].
  pose proof (ev3_n_le mx rem) as Hn.
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
  destruct (Z.ltb_spec cap (no + n)).
  - pose proof (IH mx (no + n) ((no + n) * 2) (rem - n)). lia.
  - pose proof (IH mx (no + n) cap (rem - n)). lia.
Qed.
Lemma ev3_cap_le : forall c mx no cap len, sl_cap c mx no cap len <= Z.max cap (2 * (no + len)).
Proof.
  intros c mx no cap len. rewrite sl_cap_fin. destruct (sl_live c len); [apply ev3_fin_run_le | lia].
Qed.
Lemma ev3_maxr_le : forall c mx no cap len, sl_maxr c mx no cap len <= Z.max 0 (2 * (no + len)).
Proof.
  intros c mx no cap len. unfold sl_maxr. destruct (sl_live c len); [apply ev3_max_run_le | lia].
Qed.
Lemma ev3_alloc_le : forall c mx no cap len, sl_alloc c mx no cap len <= Z.max 0 (4 * (no + len) - 2 * Z.max cap 0).
Proof.
  intros c mx no cap len. unfold sl_alloc. destruct (sl_live c len); [apply ev3_alloc_run_le | lia].
Qed.

(* Hcap is the weakest premise on lm_cap: LS_event_relay's first conjunct implies it (send_line never shrinks a
   capacity, W_contract.v sl_fin_ge) *)
Lemma fr_LS_event_relay_Hcap_needed : forall c mx no cap len, sl_cap c mx no cap len < MMAX -> cap < MMAX.
Proof.
  intros c mx no cap len H. assert (HW : WR_MMAX = 1072693248) by reflexivity.
  destruct (Z.ltb_spec cap 0) as [Hc|Hc]; [lia|].
  rewrite sl_cap_fin in H. destruct (sl_live c len); [|lia].
  pose proof (sl_fin_ge (Z.to_nat len) mx no cap len Hc). lia.
Qed.

(* ------------------------------------------------------------------ the model's out buffer and the cursor *)
Definition ev3_pfx (m : lmod) : list (Z * Z) :=
  (lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks (lm_hs m)).
Lemma ev3_model_blks : forall m, model_blks m = ev3_pfx m ++ aout_blks (lm_cap m) (lm_out m).
Proof. intros m. unfold model_blks, ev3_pfx. cbn [app]. rewrite app_assoc. reflexivity. Qed.
Lemma ev3_bsum_aout : forall c o, bsum (aout_blks c o) <= Z.max 0 c.
Proof. intros c o. unfold aout_blks. destruct (Z.eqb_spec c 0); cbv beta iota; rewrite ?bsum_cons, ?bsum_nil; cbn [snd]; lia. Qed.
Lemma ev3_bsum_aout_eq : forall c o, 0 <= c -> bsum (aout_blks c o) = c.
Proof. intros c o Hc. unfold aout_blks. destruct (Z.eqb_spec c 0); cbv beta iota; rewrite ?bsum_cons, ?bsum_nil; cbn [snd]; lia. Qed.

Section ev3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the event consumes its op byte, the two length bytes fuzz_u16 reads, and the ev_len bytes strnlen scans *)
Lemma ev3_k2 : forall cx m e, 0 <= lm_k m < c_n cx -> ev_evt cx m e ->
  lm_k m + 1 + Z.of_nat (length e) <= ev_k2 cx m <= c_n cx.
Proof.
  intros cx m e Hk (He & _). unfold ev_k2, ev_k1, ev_cons2. unfold ev_len in *.
  destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); lia.
Qed.
Lemma ev3_len_le : forall cx m, 0 <= lm_k m -> 0 <= c_n cx -> ev_len cx m <= c_n cx.
Proof. intros cx m Hk Hn. unfold ev_len. destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); lia. Qed.

(* what LS gives at any cut point, to the byte: the model is under PHI, and PHI under 66 * 2^26 + 24000 *)
Lemma ev3_room : forall cx t m ly S, fr_LS B cx t m ly S -> blocks_bytes S + 62 * 2 ^ 26 - 24000 <= LIVE_MAX.
Proof.
  intros cx t m ly S (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app.
  pose proof (PHI_ge m). pose proof (nopen_le4 _ Hl). pose proof (npend_nonneg m).
  assert (Hk : kk cx m <= c_n cx) by (unfold kk; lia).
  assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  unfold MB_K, MB_C, APARTIAL in *. lia.
Qed.
Lemma ev3_malloc_bb : forall ly S (ly1 : alayout) (S1 : astate) q n,
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, n)] -> blocks_bytes S1 = blocks_bytes S + n.
Proof.
  intros ly S ly1 S1 q n Hm.
  rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S), Hm, bsum_app, bsum_cons, bsum_nil.
  cbn [snd]. lia.
Qed.

Ltac ev3_perm_lia :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hn" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

(* ================================================================== LS_event_relay, PROPOSED text with Hcap
   1172d6d9065 _event.v:1034, plus: lm_O m = [] (lregs_P1 :285, HO), malloc's block (W_journal.v:766, Hblq), and
   the ONE extra hypothesis Hcap : lm_cap m < MMAX that fr_LS v2 + fr_RINV do not give *)
Lemma fr_LS_event_relay_p : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  forall (Hcap : lm_cap m < MMAX),
  sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < MMAX /\
  blocks_bytes S1 + 2 * sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Proof.
  intros cx t m ly S S1 e ly1 q H _ (He & _) _ HO Hm Hcap.
  pose proof (ev3_room cx t m ly S H) as Hroom. pose proof (fr_LS_k B cx t m ly S H) as Hk.
  pose proof (ev3_malloc_bb ly S ly1 S1 q (re_len e) Hm) as Hbb.
  destruct H as (rest & e0 & _ & _ & _ & Hc & _).
  assert (Hk0 : 0 <= lm_k m) by (unfold kk in Hk; lia).
  pose proof (ev3_len_le cx m Hk0 ltac:(lia)) as Hl.
  pose proof (ev3_cap_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hcb.
  assert (Hno : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  assert (HL : re_len e = Z.of_nat (length e) + 1) by reflexivity.
  assert (HW : WR_MMAX = 1072693248) by reflexivity.
  refine (conj _ (conj _ I)); lia.
Qed.

(* ================================================================== LS_event_relay, RELAXED conjuncts
   The same premises without Hcap, concluding send_line's own room premises (1172d6d9065 W_contract.v:873-874,
   sl_spec) in place of the capacity bound re_spec (W_contract.v:1036-1037) asks for.  Needs re_spec's two premises
   relaxed to these, and pb_relay_event (378aa2733e7 W_relay_event.v:571-572) to pass them through. *)
Lemma fr_LS_event_relay_r : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Proof.
  intros cx t m ly S S1 e ly1 q H _ (He & _) _ HO Hm.
  pose proof (fr_LS_room B cx t m ly S H) as Hroom. pose proof (fr_LS_k B cx t m ly S H) as Hk.
  pose proof (ev3_malloc_bb ly S ly1 S1 q (re_len e) Hm) as Hbb.
  destruct H as (rest & e0 & _ & _ & _ & Hc & _).
  assert (Hk0 : 0 <= lm_k m) by (unfold kk in Hk; lia).
  pose proof (ev3_len_le cx m Hk0 ltac:(lia)) as Hl.
  pose proof (ev3_maxr_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hmx.
  pose proof (ev3_alloc_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hal.
  assert (Hno : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  assert (HL : re_len e = Z.of_nat (length e) + 1) by reflexivity.
  assert (HW : WR_MMAX = 1072693248) by reflexivity.
  unfold ROOM_SPARE in Hroom. refine (conj _ (conj _ I)); lia.
Qed.

(* ================================================================== LS_event_step, PROPOSED text
   1172d6d9065 _event.v:1045, plus: the cursor and the cleared O (lregs_P1 :285, Hk / HO), 0 <= lm_cap m (aout_at,
   W_rep.v:177-178), and the three callees' block relations (W_journal.v:767 malloc, W_contract.v:1048-1049
   relay_event, W_journal.v:789 free).  The out buffer may move and grow to sl_cap; the growth is at most
   2 * re_len e (O was empty), paid by MB_K = 65 per byte of the 1 + 2 + ev_len input bytes the event consumes. *)
Lemma fr_LS_event_step_p : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_LS B cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  fr_LS B cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q H HE _ _ _ Hk HO Hc0 Hm (restR & HR1 & HR2)
    (l1 & l2 & Hf2 & Hf3).
  pose proof (ev3_k2 cx m e Hk HE) as Hk2.
  pose proof (ev3_cap_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hcb.
  destruct H as (rest & e0 & HP & HR & HEn & Hc & Hl & Hnp & HM).
  set (cap' := sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in *.
  assert (EM' : model_blks (ev_step cx m e v out') = ev3_pfx m ++ aout_blks cap' out')
    by (rewrite ev3_model_blks; reflexivity).
  exists rest, e0. split; [| split; [exact HR | split; [exact HEn | split; [exact Hc | split]]]].
  - rewrite Hf3, EM'. rewrite Hf2 in HR2. rewrite Hm in HR1. rewrite ev3_model_blks in HP.
    clear - HP HR1 HR2. ev3_perm_lia.
  - exact Hl.
  - assert (En : npend (ev_step cx m e v out') = npend m) by reflexivity.
    assert (Ek' : kk cx (ev_step cx m e v out') = Z.min (ev_k2 cx m) (c_n cx)) by reflexivity.
    assert (Ek : kk cx m = Z.min (lm_k m) (c_n cx)) by reflexivity.
    assert (Eo : nopen (lm_hs (ev_step cx m e v out')) = nopen (lm_hs m)) by reflexivity.
    assert (EP : PHI (ev_step cx m e v out') =
                 PHI m - bsum (aout_blks (lm_cap m) (lm_out m)) + bsum (aout_blks cap' out')).
    { unfold PHI. rewrite EM', ev3_model_blks, !bsum_app.
      change (pend_bytes (ev_step cx m e v out')) with (pend_bytes m).
      change (held_bytes (ev_step cx m e v out')) with (held_bytes m).
      change (vslack (ev_step cx m e v out')) with (vslack m). lia. }
    pose proof (ev3_bsum_aout cap' out') as Hnew.
    pose proof (ev3_bsum_aout_eq (lm_cap m) (lm_out m) Hc0) as Hold.
    assert (Hno : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
    assert (HL : re_len e = Z.of_nat (length e) + 1) by reflexivity.
    rewrite En, Ek', Eo, EP. rewrite Ek in Hnp, HM. unfold MB_K, MB_C, APARTIAL in *.
    split; lia.
Qed.
End ev3.

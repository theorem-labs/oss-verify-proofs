(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the REST segment of fuzz_reply's drain ASan walk (fuzz_reply.asan
   0x83a4c .. 0x83ab4): s->used = |W| - p, the move-down of the incomplete line to the buffer's start
   (__asan_memmove at 0x83a68) and the long-line reset (s->used = 0, s->skip = 1), back to the outer loop's head.
   The statement is W_drain_cx.v's dr_rest_stmt; the Section header below is that file's, verbatim. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_rest.v; 392 of its 508 lines of code are new or changed and 2177 lines of the source are left out. *)
(* The live bytes fuzz_reply's drain (ASan walk, fuzz_reply.asan 0x830dc .. 0x83de4) leaves: from W_contract.v
   dr_post, blocks_bytes S' <= blocks_bytes S + tr_alloc (dr_tr ..), for the caller that bounds the allocator's live
   bytes across the call (relay_instance_gone's RigTop).  dr_post's two Permutations over one rest reduce it to the
   blocks of the relay entry, the harness source and g_out (blocks_bytes = bsum ablocks); their sizes after the call
   are functions of drain_fin (dr_post), and a potential argument over drain_run (W_drain_model.v's round equations)
   bounds them: every growth (buffer, held array, expected array, g_out) and every new block (a held key, an
   expected text) is a request of the trace, every free drops a block.  The model needs only the signs and the
   round invariants the entry representations give (aentry_ok, asrc_at, aout_at: dr_spec's own premises).
   The Section header is W_drain_cx.v's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- Sizes: a list of byte texts as blocks of |text| + 1 bytes. ---- *)
Definition lsz {A : Type} (l : list (list A)) : Z := fold_right (fun x acc => Z.of_nat (length x) + 1 + acc) 0 l.

Lemma lsz_nil : forall A, @lsz A [] = 0.
Proof. reflexivity. Qed.

Lemma lsz_cons : forall A (x : list A) l, lsz (x :: l) = Z.of_nat (length x) + 1 + lsz l.
Proof. reflexivity. Qed.

Lemma lsz_app : forall A (l1 l2 : list (list A)), lsz (l1 ++ l2) = lsz l1 + lsz l2.
Proof. intros A l1 l2. induction l1 as [|x l1 IH]; cbn [app]; [reflexivity|]. rewrite !lsz_cons, IH. lia. Qed.

Lemma lsz_nonneg : forall A (l : list (list A)), 0 <= lsz l.
Proof. intros A l. induction l as [|x l IH]; [cbn; lia|]. rewrite lsz_cons. lia. Qed.

Lemma lsz_perm : forall A (l1 l2 : list (list A)), Permutation l1 l2 -> lsz l1 = lsz l2.
Proof. intros A l1 l2 HP. induction HP; rewrite ?lsz_cons; lia. Qed.

Lemma lsz_map : forall A C (g : list A -> list C) l, (forall x, length (g x) = length x) -> lsz (map g l) = lsz l.
Proof.
intros A C g l Hg. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !lsz_cons, IH, Hg. reflexivity.
Qed.

(* ---- tr_alloc over the pieces of a trace. ---- *)
Lemma tal_app : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)), tr_alloc (t1 ++ t2) = tr_alloc t1 + tr_alloc t2.
Proof.
intros t1 t2. unfold tr_alloc. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma tal_nil : tr_alloc ([] : list (RelayRunT.rev YO0i.sptr)) = 0.
Proof. reflexivity. Qed.

Lemma tal_malloc : forall n (t : list (RelayRunT.rev YO0i.sptr)), tr_alloc (RelayRunT.RMalloc n :: t) = n + tr_alloc t.
Proof. reflexivity. Qed.

Lemma tal_realloc : forall k n a (t : list (RelayRunT.rev YO0i.sptr)),
  tr_alloc (RelayRunT.RRealloc k n a :: t) = n + tr_alloc t.
Proof. reflexivity. Qed.

Lemma tal_free : forall n a (t : list (RelayRunT.rev YO0i.sptr)), tr_alloc (RelayRunT.RFree n a :: t) = tr_alloc t.
Proof. intros n a t. unfold tr_alloc at 1. cbn [fold_right]. reflexivity. Qed.

(* ---- One growth of s->buf. ---- *)
Lemma dl_grow : forall cap used j b, 0 <= cap ->
  fst (snd (drain_b_c.grow_tr cap used j b)) - cap <= tr_alloc (fst (drain_b_c.grow_tr cap used j b)).
Proof.
intros cap used j b Hc. unfold drain_b_c.grow_tr.
destruct (cap - used <? 4096); cbn [fst snd]; [|rewrite tal_nil; lia].
destruct (Z.eqb_spec cap 0); cbn beta iota; [rewrite tal_malloc | rewrite tal_realloc]; rewrite tal_nil; lia.
Qed.

(* ---- send_line: each growth requests the new capacity. ---- *)
Lemma dl_sl_cap_indep : forall f mx no cap rem j o j' o',
  fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) = fst (snd (send_line_b_c.sl_run f mx no cap rem j' o')).
Proof.
induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [send_line_b_c.sl_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
match goal with |- context [Z.ltb cap ?x] => destruct (Z.ltb cap x) end; cbn [fst snd]; apply IH.
Qed.

Lemma dl_sl_run : forall f mx no cap rem j o, 0 <= cap ->
  fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) - cap <= tr_alloc (fst (send_line_b_c.sl_run f mx no cap rem j o)) /\
  cap <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
- cbn [fst snd]. rewrite tal_nil. lia.
- destruct (rem <=? 0); [cbn [fst snd]; rewrite tal_nil; lia|].
  match goal with |- context [Z.ltb cap ?x] => destruct (Z.ltb_spec cap x) as [Hlt|Hge] end.
  + match goal with |- context [send_line_b_c.sl_run f ?a1 ?a2 ?a3 ?a4 ?a5 ?a6] =>
      assert (Hc' : 0 <= a3) by lia; destruct (IH a1 a2 a3 a4 a5 a6 Hc') as [I1 I2] end.
    cbn [fst snd]. destruct (cap =? 0); cbn beta iota; [rewrite tal_malloc | rewrite tal_realloc]; lia.
  + apply IH. exact Hc.
Qed.

Lemma dl_send : forall live mx no cap len j o, 0 <= cap ->
  send_line_b_c.send_line_cap live mx no cap len - cap <= tr_alloc (send_line_b_c.send_line_tr live mx no cap len j o) /\
  cap <= send_line_b_c.send_line_cap live mx no cap len.
Proof.
intros live mx no cap len j o Hc. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
destruct live; [|rewrite tal_nil; lia].
rewrite (dl_sl_cap_indep _ mx no cap len 0 RelayRunF.adr0 j o). exact (dl_sl_run _ mx no cap len j o Hc).
Qed.

(* ---- gesture_seen: a begin not held grows the array and adds a key, an end held frees one. ---- *)
Lemma dl_seen : forall H ka l j ha ks, 0 <= ka ->
  lsz (seen_arr H l) + snd (fst (drain_b_c.seen_tr H ka l j ha ks)) <=
  lsz H + ka + tr_alloc (fst (fst (drain_b_c.seen_tr H ka l j ha ks))) /\
  0 <= snd (fst (drain_b_c.seen_tr H ka l j ha ks)).
Proof.
intros H ka l j ha ks Hk. unfold drain_b_c.seen_tr, seen_arr.
destruct (gesture l) as [[kd x]|]; [|cbn [fst snd]; rewrite tal_nil; lia].
destruct kd; destruct (index_of x H) as [n|] eqn:Ei; cbn [fst snd]; try (rewrite tal_nil; lia).
- assert (Hc : 0 <= (Z.of_nat (length H) + 1) * 8) by lia.
  destruct (ka =? 0); cbn beta iota; [rewrite tal_malloc | rewrite tal_realloc]; rewrite tal_malloc, tal_nil;
  rewrite lsz_app, lsz_cons, lsz_nil; lia.
- rewrite tal_free, tal_nil.
  destruct (index_of_some x H n Ei) as (a & b & -> & <-).
  pose proof (lsz_perm _ _ _ (swap_remove_perm [] a x b)) as P. rewrite lsz_cons in P. lia.
Qed.

(* ---- The relay's lines: send_line then gesture_seen for each. ---- *)
Lemma dl_lines : forall live mx ls no cap H ka j o ha ks, 0 <= cap -> 0 <= ka ->
  fst (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))) +
  lsz (snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))))) +
  snd (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) <=
  cap + lsz H + ka + tr_alloc (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) /\
  cap <= fst (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))) /\
  0 <= snd (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))).
Proof.
intros live mx ls. induction ls as [|l r IH]; intros no cap H ka j o ha ks Hc Hk; cbn [drain_b_c.lines_run].
- cbn [fst snd]. rewrite tal_nil. lia.
- destruct (dl_send live mx no cap (Z.of_nat (length l) + 1) j o Hc) as [S1 S2].
  match goal with |- context [drain_b_c.seen_tr H ka l ?jj ha ks] =>
    destruct (dl_seen H ka l jj ha ks Hk) as [N1 N2] end.
  match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 ?a3 ?a4 r ?a5 ?a6 ?a7 ?a8] =>
    destruct (IH a1 a2 a3 a4 a5 a6 a7 a8 ltac:(lia) N2) as (I1 & I2 & I3) end.
  cbn [fst snd]. rewrite !tal_app. lia.
Qed.

(* ---- reference_feed's pushes: the grown array (128 or 32 cap) and each text (|l| + 1). ---- *)
Lemma dl_pushes : forall ls n cap j v rs, 0 <= cap ->
  16 * snd (fst (drain_b_c.pushes_run n cap ls j v rs)) + lsz ls <=
  16 * cap + tr_alloc (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) /\
  0 <= snd (fst (drain_b_c.pushes_run n cap ls j v rs)).
Proof.
induction ls as [|l r IH]; intros n cap j v rs Hc; cbn [drain_b_c.pushes_run].
- cbn [fst snd]. rewrite tal_nil, lsz_nil. lia.
- assert (Hpc : 0 <= drain_b_c.push_cap n cap /\ 16 * drain_b_c.push_cap n cap - 16 * cap <=
    tr_alloc (if n =? cap then (if cap =? 0 then [RelayRunT.RMalloc 128]
      else [RelayRunT.RRealloc (16 * cap) (32 * cap) v]) else [] : list (RelayRunT.rev YO0i.sptr))).
  { unfold drain_b_c.push_cap. destruct (n =? cap); [destruct (Z.eqb_spec cap 0)|]; cbn beta iota;
    rewrite ?tal_malloc, ?tal_realloc, ?tal_nil; lia. }
  match goal with |- context [drain_b_c.pushes_run ?a1 ?a2 r ?a3 ?a4 ?a5] =>
    destruct (IH a1 a2 a3 a4 a5 (proj1 Hpc)) as [I1 I2] end.
  cbn [fst snd]. split; [|exact I2].
  assert (TP : tr_alloc (ListTr.list_push_tra v n cap (Z.of_nat (length l))) =
    tr_alloc (if n =? cap then (if cap =? 0 then [RelayRunT.RMalloc 128]
      else [RelayRunT.RRealloc (16 * cap) (32 * cap) v]) else [] : list (RelayRunT.rev YO0i.sptr)) +
    (Z.of_nat (length l) + 1))
    by (unfold ListTr.list_push_tra; rewrite tal_app, tal_malloc, tal_nil; lia).
  rewrite !tal_app, TP, lsz_cons.
  destruct Hpc as [_ Hpc]. lia.
Qed.

(* ---- The round model's potential: the sizes of the blocks a drain round can grow. ---- *)
Definition dphi (s : drain_b_c.dstate) : Z :=
  drain_b_c.ds_cap s + drain_b_c.ds_ka s + lsz (drain_b_c.ds_H s) + 16 * drain_b_c.ds_ecap s + drain_b_c.ds_ocap s.

Definition dinv (s : drain_b_c.dstate) : Prop :=
  (drain_b_c.ds_cap s = 0 \/ drain_b_c.ds_cap s = 8192 \/ drain_b_c.ds_cap s = 16384) /\
  ulen s <= 6000 /\ ulen s <= drain_b_c.ds_cap s /\
  0 <= drain_b_c.ds_ka s /\ 0 <= drain_b_c.ds_ecap s /\ 0 <= drain_b_c.ds_ocap s /\
  dwf s /\ dstrict s /\ Forall (fun r => (1 <= length r)%nat) (drain_b_c.ds_pend s).

Lemma dl_alloc_ddrop : forall s a, tr_alloc (ddrop s a) = 0.
Proof. intros s a. unfold ddrop, ListTr.list_drop_tra. destruct (dwhole s); reflexivity. Qed.

Lemma dl_round : forall live mx g j a,
  0 <= drain_b_c.ds_ka g -> 0 <= drain_b_c.ds_ecap g -> 0 <= drain_b_c.ds_ocap g ->
  dphi (dnext live mx g) + lsz (dref g) <=
  dphi g + tr_alloc (fst (fst (dpush g j a)) ++ ddrop g a ++ fst (fst (dlines live mx g j a))) /\
  drain_b_c.ds_ocap g <= drain_b_c.ds_ocap (dnext live mx g) /\
  0 <= drain_b_c.ds_ka (dnext live mx g) /\ 0 <= drain_b_c.ds_ecap (dnext live mx g).
Proof.
intros live mx g j a Hka Hec Hoc.
rewrite !tal_app, dl_alloc_ddrop.
destruct (dl_pushes (dref g) (drain_b_c.ds_en g) (drain_b_c.ds_ecap g) j (drain_b_c.da_ev a) (drain_b_c.da_erecs a) Hec)
  as (P1 & P2).
pose proof (dl_lines live mx (drl g) (drain_b_c.ds_no g) (drain_b_c.ds_ocap g) (drain_b_c.ds_H g) (drain_b_c.ds_ka g)
  (j + RelayRunF.nretF (fst (fst (dpush g j a))) + RelayRunF.nretF (ddrop g a)) (drain_b_c.da_out a) (drain_b_c.da_hp a)
  (drain_b_c.da_keys a) Hoc Hka) as (L1 & L2 & L3).
rewrite lines_run_m in L1, L2, L3. rewrite pushes_run_m in P1, P2.
unfold dpush, dlines.
unfold dphi, dnext. cbn [drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_H drain_b_c.ds_ecap drain_b_c.ds_ocap].
lia.
Qed.

(* ---- The pending bytes split at the round's n (W_drain_dropb_cx.v dm_ps / dm_ps_whole / dm_ps_next). ---- *)
Lemma dl_ps : forall s, dwf s -> 0 <= dnum s ->
  pstream s = ddata s ++ prest (drain_b_c.ds_pend s) (drain_b_c.ds_off s + dnum s).
Proof.
  intros s (W0 & _) N0. unfold pstream, ddata, dhead.
  destruct (drain_b_c.ds_pend s) as [|r rs]; cbn [prest].
  - rewrite skipn_nil, firstn_nil. reflexivity.
  - rewrite app_assoc. f_equal.
    rewrite <- (firstn_skipn (Z.to_nat (dnum s)) (skipn (Z.to_nat (drain_b_c.ds_off s)) r)) at 1. f_equal.
    rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma dl_ps_next : forall live mx s,
  pstream (dnext live mx s) = prest (drain_b_c.ds_pend s) (drain_b_c.ds_off s + dnum s).
Proof.
  intros live mx s. unfold pstream, dnext. cbn [drain_b_c.ds_pend drain_b_c.ds_off].
  destruct (dwhole s) eqn:W; [|reflexivity].
  unfold dwhole, dhead in W. apply Z.eqb_eq in W. unfold dtail.
  revert W. destruct (drain_b_c.ds_pend s) as [|r rs]; intros W; cbn [prest] in W |- *; [reflexivity|].
  rewrite W, Nat2Z.id, skipn_all. destruct rs as [|r1 rs]; reflexivity.
Qed.

Lemma dl_fut : forall live mx g, dwf g -> 0 <= dnum g ->
  lsz (lines (drain_b_c.ds_ref g) (pstream g)) =
  lsz (dref g) + lsz (lines (drain_b_c.ds_ref (dnext live mx g)) (pstream (dnext live mx g))).
Proof.
intros live mx g W N. rewrite (dl_ps g W N), lines_app, lsz_app, dl_ps_next. reflexivity.
Qed.

(* ---- The round invariant across a data round. ---- *)
Lemma dl_chunk_u : forall u sk d, Z.of_nat (length (fst (fst (chunk u sk d)))) <= 6000.
Proof.
intros u sk d. unfold chunk. destruct (scan sk u d) as [[sk' r] ls].
destruct (Nat.ltb LINE_LIMIT (length r)) eqn:E; cbn [fst].
- clear E. cbn [length]. lia.
- apply Nat.ltb_ge in E. apply Nat2Z.inj_le in E.
  assert (HL : Z.of_nat LINE_LIMIT = 6000) by (vm_compute; reflexivity).
  rewrite HL in E. exact E.
Qed.

Lemma dl_strict_next : forall live mx g, dwf g -> 0 < dnum g ->
  Forall (fun r => (1 <= length r)%nat) (drain_b_c.ds_pend g) ->
  dstrict (dnext live mx g) /\ Forall (fun r => (1 <= length r)%nat) (drain_b_c.ds_pend (dnext live mx g)).
Proof.
intros live mx g (W0 & W1) N HF. unfold dstrict, dnext, dwhole, dtail.
cbn [drain_b_c.ds_pend drain_b_c.ds_off].
unfold dnum, dhead in *.
destruct (drain_b_c.ds_pend g) as [|r0 rs] eqn:PE; [cbn [length] in N; lia|].
specialize (W1 r0 rs eq_refl).
destruct (Z.eqb_spec (drain_b_c.ds_off g + dnum g) (Z.of_nat (length r0))) as [E|E];
  unfold dnum, dhead in E; rewrite PE in E.
- rewrite (proj2 (Z.eqb_eq _ _) E). inversion HF as [|x xs Hx Hxs]; subst.
  split; [|exact Hxs]. intros r rs' Er. subst rs. inversion Hxs as [|y ys Hy Hys]; subst. lia.
- rewrite (proj2 (Z.eqb_neq _ _) E). split; [|exact HF].
  intros r rs' Er. injection Er as <- <-. lia.
Qed.

(* ---- drain_run: the potential after the run, plus the lines pushed, is at most the potential before plus the
   bytes the trace requests; g_capout only grows. ---- *)
Lemma dl_run : forall f live mx s j a, dinv s -> (dneed s <= f)%nat ->
  dphi (fst (snd (drain_b_c.drain_run f live mx s j a))) + lsz (lines (drain_b_c.ds_ref s) (pstream s)) <=
  dphi s + tr_alloc (fst (drain_b_c.drain_run f live mx s j a)) /\
  drain_b_c.ds_ocap s <= drain_b_c.ds_ocap (fst (snd (drain_b_c.drain_run f live mx s j a))).
Proof.
induction f as [|f IH]; intros live mx s j a HI HN; [unfold dneed in HN; lia|].
pose proof HI as (Hc & Hu & Huc & Hka & Hec & Hoc & Hwf & Hst & Hne).
assert (Hu0 : 0 <= ulen s) by (unfold ulen; lia).
destruct (grow_room (drain_b_c.ds_cap s) (ulen s) Hc ltac:(lia) Huc) as (Hroom & Hgc).
assert (HR : 4096 <= drain_b_c.ds_cap (dgrow s) - ulen (dgrow s)) by exact Hroom.
rewrite (drun_grow f live mx s j a HR). cbn [fst snd].
assert (G1 : gcap (drain_b_c.ds_cap s) (ulen s) - drain_b_c.ds_cap s <=
  tr_alloc (fst (drain_b_c.grow_tr (drain_b_c.ds_cap s) (ulen s) j (drain_b_c.da_buf a)))).
{ rewrite <- (gcap_eq (drain_b_c.ds_cap s) (ulen s) j (drain_b_c.da_buf a)). apply dl_grow. lia. }
rewrite tal_app.
change (pstream s) with (pstream (dgrow s)). change (drain_b_c.ds_ref s) with (drain_b_c.ds_ref (dgrow s)).
change (drain_b_c.ds_ocap s) with (drain_b_c.ds_ocap (dgrow s)).
assert (Pg : dphi (dgrow s) = dphi s + (gcap (drain_b_c.ds_cap s) (ulen s) - drain_b_c.ds_cap s))
  by (unfold dphi, dgrow; cbn [drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_H drain_b_c.ds_ecap drain_b_c.ds_ocap]; lia).
assert (HIg : dinv (dgrow s)).
{ unfold dinv, dgrow, ulen, dwf, dstrict in *.
  cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_off
       drain_b_c.ds_pend] in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact Hwf|]. split; [exact Hst | exact Hne]. }
assert (HNg : dneed (dgrow s) = dneed s) by reflexivity.
generalize (j + RelayRunF.nretF (fst (drain_b_c.grow_tr (drain_b_c.ds_cap s) (ulen s) j (drain_b_c.da_buf a))))%nat as j1.
generalize (agrow s j a) as a1.
revert Pg HR HIg HNg. generalize (dgrow s) as g. intros g Pg HR HIg HNg a1 j1.
clear Hc Hu Huc Hka Hec Hoc Hwf Hst Hne Hroom Hgc.
pose proof HIg as (Hc & Hu & Huc & Hka & Hec & Hoc & Hwf & Hst & Hne).
destruct (drain_b_c.ds_eintr g) eqn:EI.
- rewrite (drun_eintr f live mx g j1 a1 HR EI).
  assert (HIc : dinv (dclr g)) by (unfold dinv, dclr, ulen, dwf, dstrict in *; cbn in *; tauto).
  destruct (IH live mx (dclr g) j1 a1 HIc ltac:(pose proof (dneed_dclr g EI); lia)) as (I1 & I2).
  change (dphi (dclr g)) with (dphi g) in I1. change (pstream (dclr g)) with (pstream g) in I1.
  change (drain_b_c.ds_ref (dclr g)) with (drain_b_c.ds_ref g) in I1.
  change (drain_b_c.ds_ocap (dclr g)) with (drain_b_c.ds_ocap g) in I2.
  split; lia.
- destruct (drain_b_c.ds_pend g) as [|r0 rs] eqn:PE.
  + rewrite (drun_end f live mx g j1 a1 HR EI PE). cbn [fst snd].
    unfold pstream. rewrite PE. cbn [prest]. change (lines (drain_b_c.ds_ref g) []) with (@nil (list Z)).
    rewrite lsz_nil, tal_nil. split; lia.
  + assert (Hpe : drain_b_c.ds_pend g <> []) by (rewrite PE; discriminate).
    rewrite (drun_data f live mx g j1 a1 HR EI Hpe Hst). cbn [fst snd].
    pose proof (dnum_pos g Hst HR Hpe) as NP.
    destruct (dl_round live mx g j1 a1 Hka Hec Hoc) as (R1 & R2 & R3 & R4).
    destruct (dneed_dnext live mx g HR Hpe Hwf Hst EI) as (DN & DW).
    destruct (dl_strict_next live mx g Hwf NP ltac:(rewrite PE; exact Hne)) as (ST2 & NE2).
    assert (HIn : dinv (dnext live mx g)).
    { unfold dinv. split; [exact Hc|].
      assert (U2 : ulen (dnext live mx g) <= 6000) by (unfold ulen, dnext, dchunk; cbn [drain_b_c.ds_u]; apply dl_chunk_u).
      split; [exact U2|].
      split; [change (drain_b_c.ds_cap (dnext live mx g)) with (drain_b_c.ds_cap g);
        assert (Hu0' : 0 <= ulen g) by (unfold ulen; lia); clear - U2 HR Hc Hu0'; lia|].
      split; [exact R3|]. split; [exact R4|]. split; [lia|].
      split; [exact DW|]. split; [exact ST2 | exact NE2]. }
    match goal with |- context [drain_b_c.drain_run f live mx (dnext live mx g) ?jj ?aa] =>
      destruct (IH live mx (dnext live mx g) jj aa HIn ltac:(lia)) as (I1 & I2) end.
    rewrite (dl_fut live mx g Hwf ltac:(lia)).
    rewrite !tal_app in *. split; lia.
Qed.

(* ---- The whole drain from its entry state. ---- *)
Lemma dl_pstream_init : forall NO CAP e h,
  pstream (drain_b_c.drain_init NO CAP e h) = bzs (pending_stream h).
Proof.
intros NO CAP e h. unfold pstream, prest, pending_stream, drain_b_c.drain_init.
cbn [drain_b_c.ds_pend drain_b_c.ds_off].
destruct (hl_recs (hs_pending h)) as [|r rs]; cbn [map]; [reflexivity|].
unfold bzs. rewrite map_app, concat_map, map_map. f_equal.
generalize (Z.to_nat (hs_off h)) as n. generalize (snd r) as l. clear.
induction l as [|x l IH]; intros [|n]; cbn; try reflexivity. apply IH.
Qed.

Lemma dl_drain : forall live mx no cap e h, dinv (drain_b_c.drain_init no cap e h) ->
  dphi (drain_b_c.drain_fin live mx no cap e h) + lsz (lines (hs_state h) (bzs (pending_stream h))) <=
  dphi (drain_b_c.drain_init no cap e h) + tr_alloc (drain_b_c.drain_tr live mx no cap e h 0 drain_b_c.dadr0) /\
  cap <= drain_b_c.ds_ocap (drain_b_c.drain_fin live mx no cap e h).
Proof.
intros live mx no cap e h HI. unfold drain_b_c.drain_fin, drain_b_c.drain_tr, drain_b_c.drain_go.
pose proof (dl_pstream_init no cap e h) as PS.
assert (HN : (dneed (drain_b_c.drain_init no cap e h) <= S (S (length (pending_stream h))))%nat).
{ unfold dneed. rewrite PS. unfold bzs. rewrite length_map.
  destruct (drain_b_c.ds_eintr (drain_b_c.drain_init no cap e h)); cbn [Nat.b2n]; lia. }
destruct (dl_run _ live mx _ 0 drain_b_c.dadr0 HI HN) as (A1 & A2).
rewrite PS in A1. exact (conj A1 A2).
Qed.


(* the arithmetic of dr_post_live, over opaque quantities *)
Lemma dl_arith : forall (live : bool) (capF kaF HF ecapF ocapF L T capE kaE HE ecapE cap pc pend expd heldc held rest
  Ap : Z),
  capF + kaF + HF + 16 * ecapF + ocapF + L <= capE + kaE + HE + 16 * ecapE + cap + T ->
  cap <= ocapF -> 0 <= pend ->
  capF + kaF + HF + (Ap + (16 * pc + 0) + (16 * ecapF + (expd + L)) + (16 * heldc + held) +
    ((if live then ocapF else cap) + rest)) <=
  capE + kaE + HE + (Ap + (16 * pc + pend) + (16 * ecapE + expd) + (16 * heldc + held) + (cap + rest)) + T.
Proof. intros live capF kaF HF ecapF ocapF L T capE kaE HE ecapE cap pc pend expd heldc held rest Ap H1 H2 H3.
destruct live; lia. Qed.


(* ---- The potential at the entry state (rewritten field by field: one reflexivity on the whole sum makes the kernel
   unfold Z.add). ---- *)
Lemma dl_phi_unf : forall s, dphi s = drain_b_c.ds_cap s + drain_b_c.ds_ka s + lsz (drain_b_c.ds_H s) +
  16 * drain_b_c.ds_ecap s + drain_b_c.ds_ocap s.
Proof. reflexivity. Qed.

Lemma dl_phi_init : forall no cap e h, dphi (drain_b_c.drain_init no cap e h) =
  re_cap e + drain_b_c.ent_ka e + lsz (drain_b_c.keys_texts (re_keys e)) + 16 * hl_cap (hs_expected h) + cap.
Proof.
intros no cap e h. rewrite dl_phi_unf.
change (drain_b_c.ds_cap (drain_b_c.drain_init no cap e h)) with (re_cap e).
change (drain_b_c.ds_ka (drain_b_c.drain_init no cap e h)) with (drain_b_c.ent_ka e).
change (drain_b_c.ds_H (drain_b_c.drain_init no cap e h)) with (drain_b_c.keys_texts (re_keys e)).
change (drain_b_c.ds_ecap (drain_b_c.drain_init no cap e h)) with (hl_cap (hs_expected h)).
change (drain_b_c.ds_ocap (drain_b_c.drain_init no cap e h)) with cap.
reflexivity.
Qed.

(* ---- The blocks' bytes (W_rep.v aentry_blks / asrc_blks / alist_blks, W_rep.v aout_blks). ---- *)
Lemma dl_bs_keys : forall ks,
  bsum (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks) = lsz (drain_b_c.keys_texts ks).
Proof.
unfold drain_b_c.keys_texts. induction ks as [|k ks IH]; [reflexivity|].
cbn [map]. rewrite bsum_cons, IH, lsz_cons. unfold bzs. rewrite length_map. cbn [snd]. lia.
Qed.

Lemma dl_bs_entry : forall e,
  bsum (aentry_blks e) = re_cap e + drain_b_c.ent_ka e + lsz (drain_b_c.keys_texts (re_keys e)).
Proof.
intros e. unfold aentry_blks. rewrite !bsum_app, dl_bs_keys.
assert (B1 : bsum (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) = re_cap e)
  by (destruct (Z.eqb_spec (re_cap e) 0); unfold bsum; cbn; lia).
assert (B2 : bsum (if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) = drain_b_c.ent_ka e)
  by (unfold drain_b_c.ent_ka; destruct (re_hp e =? 0); unfold bsum; cbn; lia).
rewrite B1, B2. lia.
Qed.

Lemma dl_bs_recs : forall rs : list (Z * list byte),
  bsum (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) rs) = lsz (map snd rs).
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map]. rewrite bsum_cons, IH, lsz_cons. cbn [snd]. lia.
Qed.

Lemma dl_bs_list : forall l, bsum (alist_blks l) = AREC * hl_cap l + lsz (map snd (hl_recs l)).
Proof.
intros l. unfold alist_blks. rewrite bsum_app, dl_bs_recs.
destruct (Z.eqb_spec (hl_cap l) 0) as [E|E]; unfold bsum at 1; cbn; [rewrite E|]; lia.
Qed.

Lemma dl_bs_src : forall h, bsum (asrc_blks h) =
  APARTIAL + bsum (alist_blks (hs_pending h)) + bsum (alist_blks (hs_expected h)) + bsum (alist_blks (hs_held h)).
Proof. intros h. unfold asrc_blks. rewrite bsum_cons, !bsum_app. cbn [snd]. lia. Qed.

Lemma dl_bs_out : forall cap out, bsum (aout_blks cap out) = cap.
Proof. intros cap out. unfold aout_blks. destruct (Z.eqb_spec cap 0); unfold bsum; cbn; lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) ->
  p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
  aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- The round invariant at drain's entry, from dr_spec's own premises at the same arguments. ---- *)
Lemma dl_init_inv : forall ly S (W : world SEGS) mem HA e h c O mx no cap out,
  aentry_ok B ly S W mem e -> asrc_at B ly S W mem HA h -> aout_at B RG ly S W mem c O mx no cap out ->
  dinv (drain_b_c.drain_init no cap e h).
Proof.
intros ly S W mem HA e h c O mx no cap out HE HS HO.
destruct HE as (_ & _ & _ & _ & _ & Hcap & HUl & HUa & _ & Hbuf & _ & Hhp & _ & _ & _).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & Hpo & _ & _ & _ & _ & _ & _ &
  Hexp & _ & _).
destruct Hpend as (_ & _ & _ & _ & _ & _ & _ & _ & Hrecs).
destruct Hexp as (_ & _ & _ & _ & Hen & _).
destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hout).
unfold dinv, drain_b_c.drain_init, ulen, dwf, dstrict.
cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_off
     drain_b_c.ds_pend].
assert (LU : Z.of_nat (length (bzs (re_U e))) = re_used e) by (unfold bzs; rewrite length_map; exact HUl).
unfold APARTIAL in HUa. unfold hl_n in Hen.
split; [exact Hcap|]. split; [lia|].
split; [destruct Hbuf as [(Hc0 & _ & Hu0)|(Hcp & _)]; destruct Hcap as [Hc|[Hc|Hc]]; lia|].
split.
{ unfold drain_b_c.ent_ka. destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [lia|].
  destruct Hhp as [(Hz' & _)|(_ & _ & _ & Hk8 & _)]; [contradiction | lia]. }
split; [lia|]. split; [destruct Hout as [(Hc & _)|(Hc & _)]; lia|].
destruct Hpo as [(HR & HO0)|(r & rs & HR & HO0)]; rewrite HR in Hrecs |- *; cbn [map].
- split; [split; [lia | intros r' rs' Hc; discriminate Hc]|].
  split; [intros r' rs' Hc; discriminate Hc | constructor].
- split; [split; [lia | intros r' rs' Hc; injection Hc as <- <-; unfold bzs; rewrite length_map; lia]|].
  split; [intros r' rs' Hc; injection Hc as <- <-; unfold bzs; rewrite length_map; lia|].
  change (bzs (snd r) :: map (fun r0 => bzs (snd r0)) rs) with (map (fun r0 => bzs (snd r0)) (r :: rs)).
  apply Forall_map. eapply Forall_impl; [|exact Hrecs]. cbv beta. intros x (_ & _ & _ & Hx).
  unfold bzs. rewrite length_map. exact (Hx eq_refl).
Qed.


(* ---- The live bytes from dr_post's block facts. ---- *)
Lemma dl_bytes : forall ly S ly' S' e h e' h' cap out cap' out' rest (live : bool) mx no,
  dinv (drain_b_c.drain_init no cap e h) ->
  Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) ->
  Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) ->
  cap' = (if live then drain_b_c.ds_ocap (drain_b_c.drain_fin live mx no cap e h) else cap) ->
  re_cap e' = drain_b_c.ds_cap (drain_b_c.drain_fin live mx no cap e h) ->
  drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H (drain_b_c.drain_fin live mx no cap e h) ->
  drain_b_c.ent_ka e' = drain_b_c.ds_ka (drain_b_c.drain_fin live mx no cap e h) ->
  hl_cap (hs_expected h') = drain_b_c.ds_ecap (drain_b_c.drain_fin live mx no cap e h) ->
  hl_recs (hs_pending h') = [] -> hl_cap (hs_pending h') = hl_cap (hs_pending h) -> hs_held h' = hs_held h ->
  map snd (hl_recs (hs_expected h')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (lines (hs_state h) (bzs (pending_stream h))) ->
  blocks_bytes S' <= blocks_bytes S + tr_alloc (drain_b_c.drain_tr live mx no cap e h 0 drain_b_c.dadr0).
Proof.
intros ly S ly' S' e h e' h' cap out cap' out' rest live mx no HI Hperm Hperm' Hcp Hcap' HKT HKA Hecap Hpend Hpc
  Hheld Hexp.
rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), (bsum_perm _ _ Hperm').
rewrite !bsum_app, !dl_bs_entry, !dl_bs_src, !dl_bs_list, !dl_bs_out.
rewrite Hpend, Hpc, Hheld, Hexp, Hecap, HKT, HKA, Hcap', Hcp. rewrite lsz_nil, lsz_app.
rewrite (lsz_map _ _ (map (Z_to_bv 8)) _ ltac:(intros x; apply length_map)).
pose proof (lsz_nonneg _ (map snd (hl_recs (hs_pending h)))) as LP.
destruct (dl_drain live mx no cap e h HI) as (M1 & M2).
rewrite dl_phi_init, dl_phi_unf in M1.
unfold AREC.
exact (dl_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 M2 LP).
Qed.

(* ---- drain's live bytes: every block the call leaves beyond the entry's was requested by its trace. ---- *)
Lemma dr_post_live : forall regs ly S W mem md SA HA e h c O mx no cap out W' c',
  dr_post B MT RG regs ly S W mem md SA HA e h c O mx no cap out W' c' ->
  aentry_ok B ly S W mem e -> asrc_at B ly S W mem HA h -> aout_at B RG ly S W mem c O mx no cap out ->
  exists ly' S' regs' mem' md' k, c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
    @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (spZ regs) (dr_fp SA e h cap out)
      ly S W mem md [] ly' S' W' mem' md' k /\
    blocks_bytes S' <= blocks_bytes S + tr_alloc (dr_tr c mx no cap e h).
Proof.
intros regs ly S W mem md SA HA e h c O mx no cap out W' c' HP HE HS HO.
pose proof (dl_init_inv ly S W mem HA e h c O mx no cap out HE HS HO) as HI.
destruct HP as (ly' & S' & regs' & mem' & md' & k & e' & h' & out' & ev' & LB & rest & HP).
cbv zeta in HP.
destruct HP as (Hc' & HJ & _ & _ & _ & Hperm & Hperm' & _ & _ & _ & _ & _ & _ & Hcap' & _ & _ & HKT & HKA & _ &
  _ & _ & _ & _ & Hecap & _ & _ & _ & _ & Hpend & _ & _ & Hpc & _ & _ & Hexp & _ & Hheld & _).
exists ly', S', regs', mem', md', k. split; [exact Hc'|]. split; [exact HJ|].
exact (dl_bytes ly S ly' S' e h e' h' cap out _ out' rest (dr_live c h) mx no HI Hperm Hperm' eq_refl Hcap' HKT HKA
  Hecap Hpend Hpc Hheld Hexp).
Qed.

End c.
End b.
End a.

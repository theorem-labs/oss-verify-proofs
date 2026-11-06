(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT DROP of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x835ac .. 0x836bc / 0x83a4c, 3 call sites), the statement W_drain_cx.v dr_drop_stmt.
   The Section header below is W_drain_cx.v's, verbatim.

   DE 0x835ac is the byte loop left: the round's n bytes sit in the relay's buffer after s->used and the
   reference splitter has taken them.  This segment is fuzz_recv's tail and the relay's first memchr
   (relay.c:202-204, fuzz_reply.c:262-272):
     0x835b8  h->pending_off += n                                      (sd 0x835c0)
     0x83600  pending_off == v[0].n ?  list_drop(&h->pending, 0) inlined:
                free(v[0].s)                      (CALL free 0x83618, AFREE, the live-state rule)
                memmove(v, v + 16, 16 (pend.n-1)) (CALL __asan_memmove 0x83648, AMEMMOVE)
                h->pending.n -= 1                 (sw 0x83654)
                h->pending_off = 0                (sd 0x83664)
     0x83668  n < 0 and n == 0 refuted (DE carries 0 < dnum s1 and the round's cap bound)
              s->used += n                        (sd 0x83684)
              memchr(s->buf, 0, s->used)          (CALL memchr 0x836a4, AMEMCHR)
     found -> DLL p = 0, q the NUL (0x836bc);  none -> DLR p = 0 (0x83a48 mv s10,s8; 0x83a4c).
   The two arms of the first test join at 0x83668; the segment is three stages over the intermediate cut
   DQ at that join (drop_keep, drop_whole, drop_tail), as the plain proof's read_tail_keep /
   read_tail_drop / read_tail (lib/Prog/drain_b.v:5780, 7169, 7375).
   The pure model lemmas dm_* below are this file's own copies. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_drop.v, with its module names changed; 93 of its 140 lines of code are new or changed and 4468 lines of the source are left out. *)
(* The relay / reference agreement at a line of fuzz_reply's drain (ASan walk, fuzz_reply.asan 0x830dc ..
   0x83de4): when the relay's buffer dW s1 holds a line [p, q) that the relay sends (s->skip clear at p and the
   line within LINE_LIMIT), the reference splitter's lines of the round, dref s1, are not empty.  The argument
   is the plain proof's J1 maintenance (released lib/Prog/drain_b.v; RelayModel.v chunk_ok): under J1 the
   relay's chunk relays exactly the reference's lines, drl s1 = dref s1, and drl s1 holds the line [p, q)
   (W_drain_tr.v tr_drl_split at S q and tr_drlp_line).  Closed lemmas: no Section variables. *)
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
W_drain_cx W_drain_rest_model W_drain_tr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* under J1 the relay's chunk relays the reference's lines (RelayModel.v chunk_ok) *)
Lemma dr_ref_drl : forall s1, J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
  dref s1 = drl s1.
Proof.
intros s1 HJ.
pose proof (chunk_ok (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) (ddata s1) HJ) as H.
unfold dref, drl, dchunk. revert H.
destruct (RelayModel.chunk (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (ddata s1)) as [[u' sk'] ls].
intros [H _]. exact (eq_sym H).
Qed.

Lemma dr_ref_line : forall s1 p q, J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
  dbound s1 p -> dskp s1 p = false -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> (q - p <= LINE_LIMIT)%nat -> dref s1 <> [].
Proof.
intros s1 p q HJ HB HK HPQ HQ HNZ HL.
assert (HU : nozero (drain_b_c.ds_u s1)) by (destruct HJ as (_ & _ & _ & HU); exact HU).
assert (HB' : dbound s1 (S q)).
{ split; [clear - HPQ; lia|]. right. replace (S q - 1)%nat with q by (clear; lia). exact HQ. }
rewrite (dr_ref_drl s1 HJ), (tr_drl_split s1 (S q) HU HB'), (tr_drlp_line s1 p q HB HPQ HQ HNZ HK HL).
intro E. apply app_eq_nil in E as [E _]. apply app_eq_nil in E as [_ E]. discriminate E.
Qed.

(* ---- The request trace's meter and send_line's budget (W_contract.v sl_cost / sl_alloc / sl_maxr): drain's
   dbud is over the trace, sl_spec over the sl_* rounds; both walk send_line_b_c.sl_run, so they are equal. ---- *)
Section sl.
Variable MT : ameter_ops.

Lemma dr_tr_cost_cons : forall {P : Type} (e : RelayRunT.rev P) t, tr_cost MT (e :: t) = tr_cost MT [e] + tr_cost MT t.
Proof. intros P e t. unfold tr_cost. cbn [fold_right]. ring. Qed.

Lemma dr_tr_alloc_cons : forall {P : Type} (e : RelayRunT.rev P) t, tr_alloc (e :: t) = tr_alloc [e] + tr_alloc t.
Proof. intros P e t. unfold tr_alloc. cbn [fold_right]. ring. Qed.

Lemma dr_tr_cost_app : forall {P : Type} (t1 t2 : list (RelayRunT.rev P)),
  tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2.
Proof.
intros P t1 t2. induction t1 as [|e t1 IH].
- change (tr_cost MT t2 = 0 + tr_cost MT t2). ring.
- rewrite <- app_comm_cons, dr_tr_cost_cons, IH, (dr_tr_cost_cons e t1). ring.
Qed.

Lemma dr_tr_alloc_app : forall {P : Type} (t1 t2 : list (RelayRunT.rev P)),
  tr_alloc (t1 ++ t2) = tr_alloc t1 + tr_alloc t2.
Proof.
intros P t1 t2. induction t1 as [|e t1 IH].
- change (tr_alloc t2 = 0 + tr_alloc t2). ring.
- rewrite <- app_comm_cons, dr_tr_alloc_cons, IH, (dr_tr_alloc_cons e t1). ring.
Qed.

Lemma dr_tr_max_nonneg : forall {P : Type} (t : list (RelayRunT.rev P)), 0 <= tr_max t.
Proof.
intros P t. induction t as [|e t IH]; [change (0 <= 0); lia|].
destruct e as [n|n a|k n a];
  [change (0 <= Z.max n (tr_max t)) | change (0 <= tr_max t) | change (0 <= Z.max n (tr_max t))]; lia.
Qed.

Lemma dr_tr_max_app : forall {P : Type} (t1 t2 : list (RelayRunT.rev P)),
  tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
intros P t1 t2. pose proof (dr_tr_max_nonneg t2) as H2. induction t1 as [|e t1 IH].
- change (tr_max t2 = Z.max 0 (tr_max t2)). lia.
- destruct e as [n|n a|k n a].
  + change (Z.max n (tr_max (t1 ++ t2)) = Z.max (Z.max n (tr_max t1)) (tr_max t2)). rewrite IH. lia.
  + change (tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2)). exact IH.
  + change (Z.max n (tr_max (t1 ++ t2)) = Z.max (Z.max n (tr_max t1)) (tr_max t2)). rewrite IH. lia.
Qed.

(* send_line's rounds: the trace's meter is the sl_* rounds' (one realloc of (no + n) * 2 per growth) *)
Lemma dr_sl_run_cost : forall f mx no cap rem j o,
  tr_cost MT (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_cost_run MT f mx no cap rem.
Proof.
induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_cost_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
match goal with |- context [Z.ltb cap ?x] => destruct (Z.ltb cap x) end; cbn [fst].
- match goal with |- context [send_line_b_c.sl_run f ?a1 ?a2 ?a3 ?a4 ?a5 ?a6] =>
    rewrite <- (IH a1 a2 a3 a4 a5 a6) end.
  destruct (cap =? 0); reflexivity.
- apply IH.
Qed.

Lemma dr_sl_run_alloc : forall f mx no cap rem j o,
  tr_alloc (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_alloc_run f mx no cap rem.
Proof.
induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_alloc_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
match goal with |- context [Z.ltb cap ?x] => destruct (Z.ltb cap x) end; cbn [fst].
- match goal with |- context [send_line_b_c.sl_run f ?a1 ?a2 ?a3 ?a4 ?a5 ?a6] =>
    rewrite <- (IH a1 a2 a3 a4 a5 a6) end.
  destruct (cap =? 0); reflexivity.
- apply IH.
Qed.

Lemma dr_sl_run_max : forall f mx no cap rem j o,
  tr_max (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_max_run f mx no cap rem.
Proof.
induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_max_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
match goal with |- context [Z.ltb cap ?x] => destruct (Z.ltb cap x) end; cbn [fst].
- match goal with |- context [send_line_b_c.sl_run f ?a1 ?a2 ?a3 ?a4 ?a5 ?a6] =>
    rewrite <- (IH a1 a2 a3 a4 a5 a6) end.
  destruct (cap =? 0); reflexivity.
- apply IH.
Qed.

Lemma dr_sl_tr_cost : forall live mx no cap len j o,
  tr_cost MT (send_line_b_c.send_line_tr live mx no cap len j o) =
  (if live then sl_cost_run MT (Z.to_nat len) mx no cap len else 0).
Proof. intros live mx no cap len j o. unfold send_line_b_c.send_line_tr. destruct live; [apply dr_sl_run_cost | reflexivity]. Qed.

Lemma dr_sl_tr_alloc : forall live mx no cap len j o,
  tr_alloc (send_line_b_c.send_line_tr live mx no cap len j o) =
  (if live then sl_alloc_run (Z.to_nat len) mx no cap len else 0).
Proof. intros live mx no cap len j o. unfold send_line_b_c.send_line_tr. destruct live; [apply dr_sl_run_alloc | reflexivity]. Qed.

Lemma dr_sl_tr_max : forall live mx no cap len j o,
  tr_max (send_line_b_c.send_line_tr live mx no cap len j o) =
  (if live then sl_max_run (Z.to_nat len) mx no cap len else 0).
Proof. intros live mx no cap len j o. unfold send_line_b_c.send_line_tr. destruct live; [apply dr_sl_run_max | reflexivity]. Qed.

(* the same, in sl_spec's currency at a controller c *)
Lemma dr_sl_tr_cost_c : forall c mx no cap len j o,
  tr_cost MT (send_line_b_c.send_line_tr (sl_live c len) mx no cap len j o) = sl_cost MT c mx no cap len.
Proof. intros c mx no cap len j o. unfold sl_cost. apply dr_sl_tr_cost. Qed.

Lemma dr_sl_tr_alloc_c : forall c mx no cap len j o,
  tr_alloc (send_line_b_c.send_line_tr (sl_live c len) mx no cap len j o) = sl_alloc c mx no cap len.
Proof. intros c mx no cap len j o. unfold sl_alloc. apply dr_sl_tr_alloc. Qed.

Lemma dr_sl_tr_max_c : forall c mx no cap len j o,
  tr_max (send_line_b_c.send_line_tr (sl_live c len) mx no cap len j o) = sl_maxr c mx no cap len.
Proof. intros c mx no cap len j o. unfold sl_maxr. apply dr_sl_tr_max. Qed.

End sl.

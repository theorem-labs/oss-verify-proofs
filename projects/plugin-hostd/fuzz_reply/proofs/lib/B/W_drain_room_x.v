(* Image B (fuzz_reply.asan-ubsan) twin of lib/A/W_drain_room_x.v (a working branch d22cbdbd553): the room round's
   bookkeeping at an allocator call of the drain walks over ARx (DR_x, 2026-10-30), one text for every B stage that calls the
   allocator (gesture_seen's add / free, drop, lines).  Moved verbatim from lib/B/W_drain_gs.v's Section rk (a working branch
   56eb8efeca9, B slice D's own copy of A's): W_drain_cx_x.v's dbud_x carries
   the room rp_RM at MT_rk's charge of the requests still owed plus kr, and the live counts plus their peak
   tr_peakP + 2; at a call the head request's room and count premise come from it (gs_rm_take, gs_cnt_call), and the
   counts after the call for the three request kinds (gs_cnt_malloc, gs_cnt_realloc, gs_cnt_free, through gs_cnt_step).
   They read only the room record RP, MT_rk, tr_cost, tr_peakP, cnt_ok(_pk), acnt and Permutation: no walk state. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
(* the count names (acnt, zb, tr_peakP): lib/B/ReplyCnt.v, before the kit so that the kit's names come last *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).

Section rk.
Variable RP : roomp.

(* MT_rk's charge over an append, and it charges every request 1 or 2 *)
Lemma gs_rk_app : forall (t1 t2 : dtrace), tr_cost MT_rk (t1 ++ t2) = tr_cost MT_rk t1 + tr_cost MT_rk t2.
Proof.
intros t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma gs_rk_nonneg : forall (t : dtrace), 0 <= tr_cost MT_rk t.
Proof.
intros t. induction t as [|ev t IH]; [unfold tr_cost; cbn; lia|].
replace (ev :: t) with ([ev] ++ t) by reflexivity. rewrite (gs_rk_app [ev] t).
assert (0 <= tr_cost MT_rk [ev]) by (destruct ev; unfold tr_cost; cbn; lia). lia.
Qed.

(* a call's room: the budget of the requests t1 ++ t2 still owed covers c <= MT_rk's charge of t1, and then the
   budget of t2 *)
Lemma gs_rm_take : forall S (t1 t2 : dtrace) (kr c : nat),
(c <= Z.to_nat (tr_cost MT_rk t1))%nat ->
rp_RM RP S (Z.to_nat (tr_cost MT_rk (t1 ++ t2)) + kr) ->
rp_RM RP S (c + (Z.to_nat (tr_cost MT_rk t2) + kr)).
Proof.
intros S t1 t2 kr c Hc H. refine (RMM_of RP S _ _ _ H).
rewrite (gs_rk_app t1 t2).
pose proof (gs_rk_nonneg t1). pose proof (gs_rk_nonneg t2).
rewrite Z2Nat.inj_add by lia. lia.
Qed.

(* a call's count premise: the live counts, from the cut's counts plus the peak of what is still owed *)
Lemma gs_cnt_call : forall (t : dtrace) l,
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P t) + 2)%nat) l -> cnt_ok RP l.
Proof. intros t l H. unfold cnt_ok. revert H. apply cnt_ok_pk_mono. intros P. lia. Qed.

(* the counts after a call: the live counts change by at most the peak's drop *)
Lemma gs_cnt_step : forall (t t' : dtrace) l l',
(forall P, Z.of_nat (acnt P l') + tr_peakP P t' <= Z.of_nat (acnt P l) + tr_peakP P t) ->
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P t) + 2)%nat) l ->
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P t') + 2)%nat) l'.
Proof.
intros t t' l l' H. apply cnt_ok_pk_mono. intros P. specialize (H P).
pose proof (tr_peakP_nonneg _ P t). pose proof (tr_peakP_nonneg _ P t'). lia.
Qed.

(* malloc / strndup / realloc(NULL, n): one block more *)
Lemma gs_cnt_malloc : forall n (t : dtrace) l l' res,
Permutation l' ((res, n) :: l) ->
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P (RelayRunT.RMalloc n :: t)) + 2)%nat) l ->
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P t) + 2)%nat) l'.
Proof.
intros n t l l' res HP. apply gs_cnt_step. intros P.
rewrite (acnt_perm P _ _ HP), acnt_cons. cbn [snd tr_peakP]. unfold zb. destruct (P n); lia.
Qed.

(* realloc(p, n) of the live block (p, k): the old block replaced by the new one *)
Lemma gs_cnt_realloc : forall k n (a : RelayRunT.addr YO0i.sptr) (t : dtrace) l1 l2 l' p res,
Permutation l' ((res, n) :: l1 ++ l2) ->
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P (RelayRunT.RRealloc k n a :: t)) + 2)%nat) (l1 ++ (p, k) :: l2) ->
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P t) + 2)%nat) l'.
Proof.
intros k n a t l1 l2 l' p res HP. apply gs_cnt_step. intros P.
rewrite (acnt_perm P _ _ HP), acnt_cons, !acnt_app, acnt_cons. cbn [snd tr_peakP]. unfold zb.
destruct (P n), (P k); lia.
Qed.

(* free of the live block (p, k) *)
Lemma gs_cnt_free : forall k (a : RelayRunT.addr YO0i.sptr) (t : dtrace) l1 l2 p,
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P (RelayRunT.RFree k a :: t)) + 2)%nat) (l1 ++ (p, k) :: l2) ->
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P t) + 2)%nat) (l1 ++ l2).
Proof.
intros k a t l1 l2 p. apply gs_cnt_step. intros P.
rewrite !acnt_app, acnt_cons. cbn [snd tr_peakP]. unfold zb. destruct (P k); lia.
Qed.
End rk.

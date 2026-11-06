(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the ASan walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan 0x82d98 .. 0x82e50 / 0x82f44), against the frozen segment interface
   lib/A/W_relay_instance_gone_cx.v (rig_top_stmt).  The Section-hypothesis block is that file's (commit
   92dac370558), verbatim.
   Layout: the tracks' pure trace lemmas, then the generic Section: its hypotheses, the statements of the lemma
   tracks, and their proofs (drain's
   model and budget, drain's live bytes, the relay representation across drain, GLIVE, GIN / GOUT at the key loop's
   start, the snprintf / strlen calls), then the walk itself: top_p1 (0x82d98 -> drain -> 0x82dd0), top_p2
   (0x82dd0 -> snprintf, strlen, the nheld test -> RGI / RGE) and rig_top_proof.
   C3 (475b8a2b569, the peak form): drain's room is the peak of its trace, a prefix of the remaining trace (top_room);
   drain's live bytes are bounded in the NET form, blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr ..) (dr_bytes:
   the potential td_pot now weighs the pending texts too, which drain frees as it reads them), and tb_core carries
   gbud's peak room across the drain step with tr_peak_app.
   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the RIG_x round): over any allocator relation
   ARx with its laws and the room record RP, at W_relay_instance_gone_cx.v's generic Section c (its list copied
   verbatim).  The statements of the lemma tracks now sit inside that Section, after its hypotheses.  Every journal is
   ajournal_gx_x with its head sets; the laws are AR_laws_x's.  THE ROOM at the drain call: gbud's room over the
   remaining trace grest i splits at the drain (tr_cost MT_rk is additive and nonnegative), so drain gets
   rp_RM RP S (Z.to_nat (dr_cost MT_rk ..) + dr_kr ..) with dr_kr the rest's MT_rk count plus gxkr, and its post's
   rp_RM RP S' dr_kr is gbud's room after the drain (top_room / top_budget).  THE COUNTS: drain's count premise dr_pk is
   within gbud's (tr_peakP of a prefix), and after the drain the live counts move by exactly tr_netP of drain's trace
   (stmt_dr_cnt, RR's lib/A/W_rr_m_dcnt.v rmc_dr_cnt), which tr_peakP_app turns into gbud's count bound over the rest
   (tb_core).  The fake frame is only 32-aligned in a generic state (alx_frames): ts_ra, ts_hull and the shadow seat
   tp_seat2 read that alignment (F's shadow address is 4-aligned). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_gestures_end W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rig_tail W_rr_tail W_rr_scan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require SnpNarrowSites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tr_cnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_rr_m_dcnt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b gestures_end_b RelayCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel RelayKeys send_line_b_c ListTr RelayRunT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require printf_facts_c.
(* route R (Section wR at the end): drain's R spec (W_contract_xR.v dr_spec_xR) and the step relation SRrG (YA0nH) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



(* ---------------------------------------------------------------- a trace's sizes and its measures *)

(* A request with its address forgotten: two traces of the same sizes have the same measures. *)
Definition tb_er (ev : RelayRunT.rev YO0i.sptr) : RelayRunT.rev YO0i.sptr :=
  match ev with
  | RelayRunT.RMalloc n => RelayRunT.RMalloc n
  | RelayRunT.RFree n _ => RelayRunT.RFree n ga0
  | RelayRunT.RRealloc k n _ => RelayRunT.RRealloc k n ga0
  end.
Definition tb_sh (t1 t2 : list (RelayRunT.rev YO0i.sptr)) : Prop := map tb_er t1 = map tb_er t2.
(* every size a request asks for is nonnegative *)
Definition tb_nn (t : list (RelayRunT.rev YO0i.sptr)) : Prop :=
  Forall (fun ev => match ev with
                    | RelayRunT.RMalloc n => 0 <= n
                    | RelayRunT.RFree _ _ => True
                    | RelayRunT.RRealloc _ n _ => 0 <= n
                    end) t.

Lemma tb_sh_app : forall a1 a2 b1 b2, tb_sh a1 a2 -> tb_sh b1 b2 -> tb_sh (a1 ++ b1) (a2 ++ b2).
Proof. intros a1 a2 b1 b2 Ha Hb. unfold tb_sh in *. rewrite !map_app, Ha, Hb. reflexivity. Qed.

Lemma tb_sh_cons : forall x1 x2 t1 t2, tb_er x1 = tb_er x2 -> tb_sh t1 t2 -> tb_sh (x1 :: t1) (x2 :: t2).
Proof. intros x1 x2 t1 t2 Hx Ht. unfold tb_sh in *. cbn [map]. rewrite Hx, Ht. reflexivity. Qed.

Lemma tb_sh_trans : forall t1 t2 t3, tb_sh t1 t2 -> tb_sh t2 t3 -> tb_sh t1 t3.
Proof. intros t1 t2 t3 H1 H2. unfold tb_sh in *. rewrite H1. exact H2. Qed.

Lemma tb_sh_sym : forall t1 t2, tb_sh t1 t2 -> tb_sh t2 t1.
Proof. intros t1 t2 H. unfold tb_sh in *. symmetry. exact H. Qed.

Lemma tb_sh_meas : forall MT t1 t2, tb_sh t1 t2 -> tr_cost MT t1 = tr_cost MT t2 /\ tr_max t1 = tr_max t2.
Proof.
  intros MT t1. induction t1 as [|x t1 IH]; intros [|y t2] H; unfold tb_sh in H; cbn [map] in H;
    try discriminate H; [split; reflexivity|].
  injection H as Hx Ht. destruct (IH t2 Ht) as (E1 & E3).
  unfold tr_cost, tr_max in *. cbn [fold_right].
  destruct x as [n|n a|k n a], y as [n'|n' a'|k' n' a']; cbn [tb_er] in Hx; try discriminate Hx;
    inversion Hx; subst; rewrite E1, E3; split; reflexivity.
Qed.

(* C3: the peak and the net change read the sizes only (W_tr_peak.v tr_sz_measures) *)
Lemma tb_sh_sz : forall t, tr_sz (map tb_er t) = tr_sz t.
Proof. induction t as [|x t IH]; [reflexivity|]. unfold tr_sz in *. cbn [map]. rewrite IH. destruct x; reflexivity. Qed.

Lemma tb_sh_pn : forall t1 t2, tb_sh t1 t2 -> tr_peak t1 = tr_peak t2 /\ tr_net t1 = tr_net t2.
Proof.
  intros t1 t2 H. unfold tb_sh in H.
  assert (Es : tr_sz t1 = tr_sz t2) by (rewrite <- (tb_sh_sz t1), <- (tb_sh_sz t2), H; reflexivity).
  destruct (tr_sz_measures t1 t2 Es) as (P & N & _). split; assumption.
Qed.

(* the room round's count measures (ReplyCnt.tr_peakP, W_tr_cnt.v tr_netP) read the sizes only too *)
Lemma tb_er_cnt : forall P t,
  ReplyCnt.tr_peakP P (map tb_er t) = ReplyCnt.tr_peakP P t /\ tr_netP P (map tb_er t) = tr_netP P t.
Proof.
  intros P t. induction t as [|[n|n a|k n a] t [IH1 IH2]]; [split; reflexivity| | |];
    cbn [map tb_er ReplyCnt.tr_peakP]; rewrite IH1; (split; [reflexivity|]); rewrite !tr_netP_cons, IH2; reflexivity.
Qed.

Lemma tb_sh_cnt : forall t1 t2, tb_sh t1 t2 -> forall P,
  ReplyCnt.tr_peakP P t1 = ReplyCnt.tr_peakP P t2 /\ tr_netP P t1 = tr_netP P t2.
Proof.
  intros t1 t2 H P. unfold tb_sh in H. destruct (tb_er_cnt P t1) as [A1 B1]. destruct (tb_er_cnt P t2) as [A2 B2].
  rewrite <- A1, <- A2, <- B1, <- B2, H. split; reflexivity.
Qed.

(* MT_rk (W_contract_x.v) charges every request 1 or 2: its cost is nonnegative for any trace *)
Lemma tb_rk_nn : forall (t : list (RelayRunT.rev YO0i.sptr)), 0 <= tr_cost MT_rk t.
Proof.
  induction t as [|x t IH]; [cbn; lia|]. unfold tr_cost, MT_rk in *. cbn [fold_right mo_malloc mo_free] in *.
  destruct x; lia.
Qed.

Lemma tb_max_nn : forall (t : list (RelayRunT.rev YO0i.sptr)), 0 <= tr_max t.
Proof.
  induction t as [|x t IH]; [cbn; lia|]. unfold tr_max in *. cbn [fold_right].
  destruct x; lia.
Qed.

Lemma tb_cost_app : forall MT (a b : list (RelayRunT.rev YO0i.sptr)),
  tr_cost MT (a ++ b) = tr_cost MT a + tr_cost MT b.
Proof. intros MT a b. induction a as [|x a IH]; [reflexivity|]. unfold tr_cost in *. cbn [app fold_right]. rewrite IH. lia. Qed.

Lemma tb_max_app : forall (a b : list (RelayRunT.rev YO0i.sptr)), tr_max (a ++ b) = Z.max (tr_max a) (tr_max b).
Proof.
  intros a b. induction a as [|x a IH]; [cbn [app]; pose proof (tb_max_nn b); change (tr_max []) with 0; lia|].
  unfold tr_max in *. cbn [app fold_right]. rewrite IH. destruct x; lia.
Qed.

Lemma tb_nn_meas : forall MT t, ameter_laws MT -> tb_nn t -> 0 <= tr_cost MT t.
Proof.
  intros MT t ML. induction t as [|x t IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [Hx H]. pose proof (IH H) as C.
  unfold tr_cost in *. cbn [fold_right]. pose proof (mo_free_nonneg MT ML) as F.
  destruct x as [n|n a|k n a]; cbn in Hx; [pose proof (mo_malloc_nonneg MT ML n Hx) | | pose proof (mo_malloc_nonneg MT ML n Hx)];
    lia.
Qed.

Lemma tb_nn_app : forall a b, tb_nn a -> tb_nn b -> tb_nn (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.

(* ---------------------------------------------------------------- send_line and gesture_end *)

Lemma tb_sl_sh : forall f mx no cap rem j o j' o',
  tb_sh (fst (send_line_b_c.sl_run f mx no cap rem j o)) (fst (send_line_b_c.sl_run f mx no cap rem j' o')).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [send_line_b_c.sl_run]; [reflexivity|].
  destruct (rem <=? 0); [reflexivity|].
  match goal with |- context [if cap <? ?x then _ else _] => destruct (cap <? x) end; cbn [fst]; [|apply IH].
  apply tb_sh_cons; [destruct (cap =? 0); reflexivity | apply IH].
Qed.

Lemma tb_sl_nn : forall f mx no cap rem j o, 0 <= mx -> 0 <= no ->
  tb_nn (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hmx Hno; cbn [send_line_b_c.sl_run]; [constructor|].
  destruct (Z.leb_spec rem 0) as [Hr|Hr]; [constructor|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  assert (Hn : 0 < n) by (unfold n; destruct (Z.eqb_spec mx 0); destruct (Z.ltb_spec mx rem); cbn; lia).
  destruct (cap <? no + n); cbn [fst]; [|apply IH; lia].
  apply Forall_cons; [destruct (cap =? 0); cbn; lia | apply IH; lia].
Qed.

Lemma tb_send_sh : forall live mx NO CAP LEN j o j' o',
  tb_sh (send_line_b_c.send_line_tr live mx NO CAP LEN j o) (send_line_b_c.send_line_tr live mx NO CAP LEN j' o').
Proof. intros. unfold send_line_b_c.send_line_tr. destruct live; [apply tb_sl_sh | reflexivity]. Qed.

Lemma tb_send_nn : forall live mx NO CAP LEN j o, 0 <= mx -> 0 <= NO ->
  tb_nn (send_line_b_c.send_line_tr live mx NO CAP LEN j o).
Proof. intros. unfold send_line_b_c.send_line_tr. destruct live; [apply tb_sl_nn; assumption | constructor]. Qed.

Lemma tb_ge_sh : forall live mx NO CAP XL j o j' o',
  tb_sh (gesture_end_b_c.gesture_end_tr live mx NO CAP XL j o) (gesture_end_b_c.gesture_end_tr live mx NO CAP XL j' o').
Proof. intros. unfold gesture_end_b_c.gesture_end_tr. apply tb_sh_app; apply tb_send_sh. Qed.

Lemma tb_ge_nn : forall live mx NO CAP XL j o, 0 <= mx -> 0 <= NO -> 0 <= XL ->
  tb_nn (gesture_end_b_c.gesture_end_tr live mx NO CAP XL j o).
Proof. intros. unfold gesture_end_b_c.gesture_end_tr. apply tb_nn_app; apply tb_send_nn; lia. Qed.

(* ---------------------------------------------------------------- the key run (gestures_end_b_c.keys_end_run) *)

(* a dead key run frees each key and sends nothing *)
Lemma tb_ker_false : forall mx no cap xks j o,
  keys_end_run false mx no cap xks j o = (map (fun xk => RelayRunT.RFree (fst xk + 1) (snd xk)) xks, (cap, o)).
Proof.
  intros mx no cap xks. revert no cap. induction xks as [|[xl ka] r IH]; intros no cap j o; [reflexivity|].
  cbn [keys_end_run]. rewrite IH. reflexivity.
Qed.

(* its sizes read the keys' lengths, and g_nout / g_capout only when it is live *)
Lemma tb_ker_sh : forall live mx xks xks' no cap no' cap' j o j' o',
  map fst xks = map fst xks' -> (live = true -> no = no' /\ cap = cap') ->
  tb_sh (fst (keys_end_run live mx no cap xks j o)) (fst (keys_end_run live mx no' cap' xks' j' o')).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros [|[xl' ka'] r'] no cap no' cap' j o j' o' E L;
    cbn [map fst] in E; try discriminate E; [reflexivity|].
  injection E as <- E. cbn [keys_end_run fst].
  apply tb_sh_app.
  - destruct live; [destruct (L eq_refl) as [<- <-]; apply tb_ge_sh | reflexivity].
  - apply tb_sh_cons; [reflexivity|]. apply IH; [exact E|].
    intros Hl. destruct (L Hl) as [<- <-]. split; reflexivity.
Qed.

Lemma tb_ker_nn : forall live mx xks no cap j o, 0 <= mx -> 0 <= no -> Forall (fun x => 0 <= fst x) xks ->
  tb_nn (fst (keys_end_run live mx no cap xks j o)).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o Hmx Hno HF; [constructor|].
  apply Forall_cons_iff in HF as [Hx HF]. cbn [fst] in Hx. cbn [keys_end_run fst].
  apply tb_nn_app; [apply tb_ge_nn; lia|]. apply Forall_cons; [exact I|]. apply IH; [lia | lia | exact HF].
Qed.

(* ---------------------------------------------------------------- drain (drain_b_c.drain_run) *)

Lemma tb_grow_sh : forall c u j b j' b',
  tb_sh (fst (drain_b_c.grow_tr c u j b)) (fst (drain_b_c.grow_tr c u j' b')).
Proof. intros. unfold drain_b_c.grow_tr. destruct (c - u <? 4096); [destruct (c =? 0)|]; reflexivity. Qed.

Lemma tb_grow_nn : forall c u j b, 0 <= c ->
  tb_nn (fst (drain_b_c.grow_tr c u j b)) /\ 0 <= fst (snd (drain_b_c.grow_tr c u j b)).
Proof.
  intros c u j b Hc. unfold drain_b_c.grow_tr.
  destruct (c - u <? 4096); [destruct (Z.eqb_spec c 0)|]; cbn [fst snd];
    (split; [unfold tb_nn; repeat constructor; cbn; lia | lia]).
Qed.

Lemma tb_seen_sh : forall H ka l j ha ks j' ha' ks',
  tb_sh (fst (fst (drain_b_c.seen_tr H ka l j ha ks))) (fst (fst (drain_b_c.seen_tr H ka l j' ha' ks'))).
Proof.
  intros. unfold drain_b_c.seen_tr.
  destruct (RelayModel.gesture l) as [[g x]|]; [|reflexivity].
  destruct g; (match goal with |- context [match ?m with Some _ => _ | None => _ end] => destruct m end); cbn [fst];
    try reflexivity; destruct (ka =? 0); reflexivity.
Qed.

Lemma tb_seen_nn : forall H ka l j ha ks, tb_nn (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof.
  intros. unfold drain_b_c.seen_tr, tb_nn.
  destruct (RelayModel.gesture l) as [[g x]|]; [|constructor].
  destruct g; (match goal with |- context [match ?m with Some _ => _ | None => _ end] => destruct m end); cbn [fst].
  - constructor.
  - constructor; [destruct (ka =? 0); cbn; lia|]. constructor; [cbn; lia | constructor].
  - constructor; [exact I | constructor].
  - constructor.
Qed.

Lemma tb_lines_sh : forall ls live mx no cap H ka j o ha ks j' o' ha' ks',
  tb_sh (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))
        (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j' o' ha' ks'))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks j' o' ha' ks'; cbn [drain_b_c.lines_run fst];
    [reflexivity|].
  match goal with |- context [drain_b_c.seen_tr H ka l ?j1 ha ks] =>
    match goal with |- context [drain_b_c.seen_tr H ka l ?j2 ha' ks'] =>
      pose proof (tb_seen_sh H ka l j1 ha ks j2 ha' ks') as T1;
      rewrite <- (proj1 (relay_instance_gone_b.gsh_seen H ka l j1 ha ks j2 ha' ks')) end end.
  apply tb_sh_app; [apply tb_send_sh|]. apply tb_sh_app; [exact T1|]. apply IH.
Qed.

Lemma tb_lines_nn : forall ls live mx no cap H ka j o ha ks, 0 <= mx -> 0 <= no ->
  tb_nn (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks Hmx Hno; cbn [drain_b_c.lines_run fst];
    [constructor|].
  apply tb_nn_app; [apply tb_send_nn; lia|]. apply tb_nn_app; [apply tb_seen_nn|]. apply IH; lia.
Qed.

Lemma tb_push_sh : forall ls n cap j v rs j' v' rs',
  tb_sh (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) (fst (fst (drain_b_c.pushes_run n cap ls j' v' rs'))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs j' v' rs'; cbn [drain_b_c.pushes_run fst]; [reflexivity|].
  apply tb_sh_app; [|apply IH].
  unfold ListTr.list_push_tra. destruct (n =? cap); [destruct (cap =? 0)|]; reflexivity.
Qed.

Lemma tb_push_nn : forall ls n cap j v rs, 0 <= n -> tb_nn (fst (fst (drain_b_c.pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs Hn; cbn [drain_b_c.pushes_run fst]; [constructor|].
  apply tb_nn_app; [|apply IH; lia].
  unfold ListTr.list_push_tra. apply tb_nn_app; [|unfold tb_nn; repeat constructor; cbn; lia].
  unfold tb_nn. destruct (Z.eqb_spec n cap); [destruct (Z.eqb_spec cap 0)|]; repeat constructor; cbn; lia.
Qed.

Lemma tb_drain_sh : forall f live mx s j a j' a',
  tb_sh (fst (drain_b_c.drain_run f live mx s j a)) (fst (drain_b_c.drain_run f live mx s j' a')).
Proof.
  induction f as [|f IH]; intros live mx s j a j' a'; cbn [drain_b_c.drain_run]; [reflexivity|].
  pose proof (tb_grow_sh (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) j'
                (drain_b_c.da_buf a')) as TG.
  rewrite (relay_instance_gone_b.gsh_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j'
             (drain_b_c.da_buf a') j (drain_b_c.da_buf a)).
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst]. apply tb_sh_app; [exact TG | apply IH].
  - destruct (drain_b_c.ds_pend s) as [|r0 rs]; [exact TG|].
    match goal with |- context [if (?x <=? 0) then _ else _] => destruct (x <=? 0) end; [exact TG|].
    match goal with |- context [RelayModel.chunk ?u ?sk ?d] => destruct (RelayModel.chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [drain_b_c.pushes_run ?n ?c ?ls ?j1 (drain_b_c.da_ev a) ?r1] =>
      match goal with |- context [drain_b_c.pushes_run n c ls ?j2 (drain_b_c.da_ev a') ?r2] =>
        pose proof (tb_push_sh ls n c j1 (drain_b_c.da_ev a) r1 j2 (drain_b_c.da_ev a') r2) as TP;
        rewrite (relay_instance_gone_b.gsh_pushes ls n c j2 (drain_b_c.da_ev a') r2 j1 (drain_b_c.da_ev a) r1) end end.
    match goal with
    |- context [drain_b_c.lines_run live mx ?n0 ?c0 ?H0 ?k0 rl ?J1 (drain_b_c.da_out a) (drain_b_c.da_hp a) (drain_b_c.da_keys a)] =>
      match goal with
      |- context [drain_b_c.lines_run live mx n0 c0 H0 k0 rl ?J2 (drain_b_c.da_out a') (drain_b_c.da_hp a') (drain_b_c.da_keys a')] =>
        pose proof (tb_lines_sh rl live mx n0 c0 H0 k0 J1 (drain_b_c.da_out a) (drain_b_c.da_hp a) (drain_b_c.da_keys a)
                      J2 (drain_b_c.da_out a') (drain_b_c.da_hp a') (drain_b_c.da_keys a')) as TL;
        rewrite <- (proj1 (relay_instance_gone_b.gsh_lines rl live mx n0 c0 H0 k0 J1 (drain_b_c.da_out a)
                             (drain_b_c.da_hp a) (drain_b_c.da_keys a) J2 (drain_b_c.da_out a') (drain_b_c.da_hp a')
                             (drain_b_c.da_keys a')));
        revert TL;
        destruct (drain_b_c.lines_run live mx n0 c0 H0 k0 rl J1 (drain_b_c.da_out a) (drain_b_c.da_hp a)
                    (drain_b_c.da_keys a)) as [[t1 [[oc' H'] ka']] [[o' ha'] ks']];
        destruct (drain_b_c.lines_run live mx n0 c0 H0 k0 rl J2 (drain_b_c.da_out a') (drain_b_c.da_hp a')
                    (drain_b_c.da_keys a')) as [[t2 [[oc2 H2] ka2]] [[o2 ha2] ks2]]
      end end.
    cbn [fst snd]. intros TL.
    apply tb_sh_app; [exact TG|]. apply tb_sh_app; [exact TP|].
    apply tb_sh_app; [match goal with |- tb_sh (if ?b then _ else _) _ => destruct b end; reflexivity|].
    apply tb_sh_app; [exact TL | apply IH].
Qed.

Lemma tb_drain_nn : forall f live mx s j a, 0 <= mx -> 0 <= drain_b_c.ds_cap s -> 0 <= drain_b_c.ds_no s ->
  0 <= drain_b_c.ds_en s -> tb_nn (fst (drain_b_c.drain_run f live mx s j a)).
Proof.
  induction f as [|f IH]; intros live mx s j a Hmx Hc Hno Hen; cbn [drain_b_c.drain_run]; [constructor|].
  destruct (tb_grow_nn (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) Hc)
    as [G1 G2].
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst]. apply tb_nn_app; [exact G1|]. apply IH; cbn [drain_b_c.ds_cap drain_b_c.ds_no drain_b_c.ds_en]; lia.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs]; [exact G1|].
    match goal with |- context [if (?x <=? 0) then _ else _] => destruct (x <=? 0) end; [exact G1|].
    match goal with |- context [RelayModel.chunk ?u ?sk ?d] => destruct (RelayModel.chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [drain_b_c.pushes_run ?n ?c ?ls ?j1 ?v1 ?r1] =>
      pose proof (tb_push_nn ls n c j1 v1 r1 Hen) as TP end.
    match goal with |- context [drain_b_c.lines_run live mx ?n0 ?c0 ?H0 ?k0 rl ?J1 ?o1 ?h1 ?ks1] =>
      pose proof (tb_lines_nn rl live mx n0 c0 H0 k0 J1 o1 h1 ks1 Hmx Hno) as TL; revert TL;
      destruct (drain_b_c.lines_run live mx n0 c0 H0 k0 rl J1 o1 h1 ks1) as [[t1 [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [fst snd]. intros TL.
    apply tb_nn_app; [exact G1|]. apply tb_nn_app; [exact TP|].
    apply tb_nn_app; [match goal with |- tb_nn (if ?b then _ else _) => destruct b end; unfold tb_nn; repeat constructor|].
    apply tb_nn_app; [exact TL|]. apply IH; cbn [drain_b_c.ds_cap drain_b_c.ds_no drain_b_c.ds_en]; lia.
Qed.

Lemma tb_dtr_sh : forall live mx NO CAP e h j a j' a',
  tb_sh (drain_b_c.drain_tr live mx NO CAP e h j a) (drain_b_c.drain_tr live mx NO CAP e h j' a').
Proof. intros. unfold drain_b_c.drain_tr, drain_b_c.drain_go. apply tb_drain_sh. Qed.

Lemma tb_dtr_nn : forall live mx NO CAP e h j a, 0 <= mx -> 0 <= re_cap e -> 0 <= NO ->
  tb_nn (drain_b_c.drain_tr live mx NO CAP e h j a).
Proof.
  intros. unfold drain_b_c.drain_tr, drain_b_c.drain_go.
  apply tb_drain_nn; cbn [drain_b_c.drain_init drain_b_c.ds_cap drain_b_c.ds_no drain_b_c.ds_en]; unfold hl_n; lia.
Qed.

(* ---------------------------------------------------------------- the run over the table (gone_run) *)

Lemma tb_gone_sh : forall lv mx pre ps no cap nm j o nm' j' o',
  tb_sh (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o))))
        (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm' j' o')))).
Proof.
  intros lv mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o nm' j' o'; [reflexivity|].
  rewrite !relay_instance_gone_b_lem.rig_gone_run_cons. cbv zeta. cbn [fst snd].
  assert (LD : forall nm0 j0 o0,
    length (drain_b_c.da_keys (relay_remove_b_c.after_drain_adr lv mx no cap e (fst hj) j0
                                 (drain_b_c.drain_start nm0 o0 e (fst hj)))) =
    length (drain_b_c.ds_H (relay_remove_b_c.after_drain lv mx no cap e (fst hj)))).
  { intros nm0 j0 o0. apply relay_instance_gone_b.gsh_after. unfold drain_b_c.drain_start.
    cbn [drain_b_c.da_keys]. rewrite length_map. reflexivity. }
  match goal with |- tb_sh ?L ?R =>
    match L with context [keys_end_run lv mx ?n0 ?c0 ?x1 ?j1 ?o1] =>
      match R with context [keys_end_run lv mx n0 c0 ?x2 ?j2 ?o2] =>
        assert (XE : map fst x1 = map fst x2)
          by (rewrite (relay_instance_gone_b.gsh_xks _ _ _ (LD nm j o)),
                      (relay_instance_gone_b.gsh_xks _ _ _ (LD nm' j' o')); reflexivity);
        pose proof (tb_ker_sh lv mx x1 x2 n0 c0 n0 c0 j1 o1 j2 o2 XE (fun _ => conj eq_refl eq_refl)) as TK;
        rewrite (gestures_end_b.p3b_ker_cap lv mx x1 x2 n0 c0 j1 o1 j2 o2 XE)
      end end end.
  rewrite (relay_instance_gone_b.gsh_xks _ _ _ (LD nm j o)), (relay_instance_gone_b.gsh_xks _ _ _ (LD nm' j' o')).
  apply tb_sh_app; [destruct (re_eof e =? 0); [apply tb_dtr_sh | reflexivity]|].
  apply tb_sh_app; [exact TK | apply IH].
Qed.

Lemma tb_fold_nn : forall (l : list Z), Forall (fun x => 0 <= x) l -> 0 <= fold_right (fun xl acc => xl + 5 + acc) 0 l.
Proof. induction 1; cbn [fold_right]; lia. Qed.

Lemma tb_gone_nn : forall lv mx pre ps no cap nm j o, 0 <= mx -> 0 <= no ->
  Forall (fun p => 0 <= re_cap (fst p)) ps ->
  tb_nn (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))).
Proof.
  intros lv mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o Hmx Hno HF; [constructor|].
  apply Forall_cons_iff in HF as [He HF]. cbn [fst] in He.
  rewrite relay_instance_gone_b_lem.rig_gone_run_cons. cbv zeta. cbn [fst snd].
  pose proof (proj1 (RelayCap.after_drain_le lv mx no cap e (fst hj))) as HN.
  assert (XN : forall (xs : list (list Z * RelayRunT.addr YO0i.sptr)),
    Forall (fun x => 0 <= fst x) (map (fun x => (Z.of_nat (length (fst x)), snd x)) xs)).
  { intros xs. apply Forall_map. apply Forall_forall. intros x _. cbn [fst]. lia. }
  apply tb_nn_app; [destruct (re_eof e =? 0); [apply tb_dtr_nn; lia | constructor]|].
  apply tb_nn_app; [apply tb_ker_nn; [lia | lia | apply XN]|].
  apply IH; [lia | | exact HF].
  apply Z.add_nonneg_nonneg; [lia|]. apply tb_fold_nn. apply Forall_map. apply XN.
Qed.

(* a dead run's drains and key runs do not read g_nout *)
Lemma tb_ad_false : forall mx no no' cap e h j a,
  drain_b_c.ds_H (relay_remove_b_c.after_drain false mx no cap e h) =
    drain_b_c.ds_H (relay_remove_b_c.after_drain false mx no' cap e h) /\
  relay_remove_b_c.after_drain_adr false mx no cap e h j a = relay_remove_b_c.after_drain_adr false mx no' cap e h j a /\
  (if re_eof e =? 0 then drain_b_c.drain_tr false mx no cap e h j a else []) =
    (if re_eof e =? 0 then drain_b_c.drain_tr false mx no' cap e h j a else []).
Proof.
  intros mx no no' cap e h j a. unfold relay_remove_b_c.after_drain, relay_remove_b_c.after_drain_adr.
  destruct (re_eof e =? 0); [|split; [reflexivity | split; reflexivity]].
  destruct (relay_instance_gone_b_lem.rig_drain_false mx no no' cap e h j a) as (E1 & E2 & E3 & _).
  split; [exact (f_equal drain_b_c.ds_H (eq_sym E2))|].
  unfold drain_b_c.drain_adr in E3. split; [exact (eq_sym E3) | exact (eq_sym E1)].
Qed.

Lemma tb_gone_false : forall mx pre ps no no' cap nm j o,
  fst (fst (fst (relay_instance_gone_b_c.gone_run false mx no cap pre ps nm j o))) =
  fst (fst (fst (relay_instance_gone_b_c.gone_run false mx no' cap pre ps nm j o))).
Proof.
  intros mx pre ps. induction ps as [|[e hj] r IH]; intros no no' cap nm j o; [reflexivity|].
  rewrite !relay_instance_gone_b_lem.rig_gone_run_cons. cbv zeta. cbn [fst snd].
  destruct (tb_ad_false mx no no' cap e (fst hj) j (drain_b_c.drain_start nm o e (fst hj))) as (AH & AA & AT).
  rewrite !tb_ker_false. cbn [fst snd].
  rewrite AH, AA, AT, !RelayCap.after_drain_dead.
  f_equal. f_equal. apply IH.
Qed.

(* ---------------------------------------------------------------- the stream's liveness *)

(* a send of len bytes is live when a one-byte send is and len <> 0 *)
Lemma tb_live_len : forall c len, sl_live c len = sl_live c 1 && negb (len =? 0).
Proof.
  intros [cl br dd ei ev] len. unfold sl_live, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct (cl <? 0), (br =? 1), (len =? 0), (dd =? 0); reflexivity.
Qed.

(* a send, and drain's flags update, keep the liveness of a one-byte send *)
Lemma tb_live_ctl : forall c len, sl_live (sl_ctl c len) 1 = sl_live c 1.
Proof.
  intros [cl br dd ei ev] len. unfold sl_live, sl_ctl, send_line_c.send_live, send_line_c.send_off.
  cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  destruct (cl <? 0); [reflexivity|]. destruct (br =? 1) eqn:Eb; [cbn; rewrite Eb; reflexivity|].
  destruct (len =? 0); cbn; [rewrite Eb; reflexivity|].
  destruct (Z.eqb_spec dd 0) as [->|Hd]; [reflexivity|]. destruct (dd =? 1); reflexivity.
Qed.

Lemma tb_live_drctl : forall c h ev, sl_live (dr_ctl c h ev) 1 = sl_live c 1.
Proof.
  intros [cl br dd ei ev0] h ev. unfold sl_live, dr_ctl, send_line_c.send_live, send_line_c.send_off.
  cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  destruct (cl <? 0); [reflexivity|]. destruct (br =? 1) eqn:Eb; [cbn; rewrite Eb; reflexivity|].
  destruct (dr_tot h =? 0); cbn; [rewrite Eb; reflexivity|].
  destruct (Z.eqb_spec dd 0) as [->|Hd]; [reflexivity|]. destruct (dd =? 1); reflexivity.
Qed.

Lemma tb_sends_live : forall mx Bs c O cap, sl_live (fst (fst (sl_sends mx c O cap Bs))) 1 = sl_live c 1.
Proof.
  intros mx Bs. induction Bs as [|x Bs IH]; intros c O cap; [reflexivity|].
  cbn [sl_sends]. rewrite IH. apply tb_live_ctl.
Qed.

(* rig_rel's stream keeps the liveness of a one-byte send *)
Lemma tb_rel_live : forall pre mx ps qs c O cap c2 O2 cap2,
  rig_rel pre mx c O cap ps qs c2 O2 cap2 -> sl_live c2 1 = sl_live c 1.
Proof.
  intros pre mx ps. induction ps as [|[e [h jj]] r IH]; intros [|[e' h'] q] c O cap c2 O2 cap2 H;
    cbn [rig_rel] in H; try contradiction.
  - destruct H as (-> & _ & _). reflexivity.
  - destruct H as (e1 & ev & LB & H). cbv zeta in H. destruct H as (_ & _ & H).
    match type of H with context [sl_sends ?m ?c1 ?O1 ?cp1 ?Bs] =>
      pose proof (tb_sends_live m Bs c1 O1 cp1) as SL; destruct (sl_sends m c1 O1 cp1 Bs) as [[c3 O3] cap3] end.
    rewrite (IH _ _ _ _ _ _ _ H). cbn [fst] in SL. rewrite SL.
    destruct (re_eof e =? 0); [apply tb_live_drctl | reflexivity].
Qed.

(* ---------------------------------------------------------------- the key sends (sl_sends over ge_bytes) *)

Lemma tb_slO_live : forall c O x, sl_live c 1 = true -> sl_O c O x = O ++ x.
Proof.
  intros c O x L. unfold sl_O. rewrite tb_live_len, L.
  destruct x as [|b x]; cbn; [rewrite app_nil_r|]; reflexivity.
Qed.

Lemma tb_slO_dead : forall c O x, sl_live c 1 = false -> sl_O c O x = O.
Proof. intros c O x L. unfold sl_O. rewrite tb_live_len, L. reflexivity. Qed.

Lemma tb_slcap_live : forall c mx no cap len, sl_live c 1 = true ->
  sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx no cap len.
Proof.
  intros c mx no cap len L. unfold sl_cap. rewrite tb_live_len, L.
  destruct (Z.eqb_spec len 0) as [->|Hl]; reflexivity.
Qed.

Lemma tb_slcap_dead : forall c mx no cap len, sl_live c 1 = false -> sl_cap c mx no cap len = cap.
Proof. intros c mx no cap len L. unfold sl_cap. rewrite tb_live_len, L. reflexivity. Qed.

Lemma tb_ge_bytes_cons : forall k Er, ge_bytes (k :: Er) = key_text k :: gesture_end_c.END5 :: ge_bytes Er.
Proof. reflexivity. Qed.

(* the sends of the keys Er: a live stream grows by every key and its " end\0", to the key run's g_capout; a dead
   one keeps g_capout *)
Lemma tb_sends : forall mx Er c O cap,
  (sl_live c 1 = true ->
     Z.of_nat (length (snd (fst (sl_sends mx c O cap (ge_bytes Er))))) =
       Z.of_nat (length O) + fold_right (fun xl acc => xl + 5 + acc) 0 (map (fun k => Z.of_nat (length (key_text k))) Er) /\
     forall xks j o, map fst xks = map (fun k => Z.of_nat (length (key_text k))) Er ->
       snd (sl_sends mx c O cap (ge_bytes Er)) = fst (snd (keys_end_run true mx (Z.of_nat (length O)) cap xks j o))) /\
  (sl_live c 1 = false -> snd (sl_sends mx c O cap (ge_bytes Er)) = cap).
Proof.
  intros mx Er. induction Er as [|k Er IH]; intros c O cap.
  - cbn [ge_bytes map concat sl_sends fst snd fold_right].
    split; [intros _; split; [lia | intros [|x xks] j o E; [reflexivity | discriminate E]] | reflexivity].
  - rewrite tb_ge_bytes_cons. cbn [sl_sends].
    change (Z.of_nat (length gesture_end_c.END5)) with 5.
    set (x := key_text k). set (XL := Z.of_nat (length x)).
    set (c1 := sl_ctl c XL). set (O1 := sl_O c O x). set (cap1 := sl_cap c mx (Z.of_nat (length O)) cap XL).
    assert (LC1 : sl_live c1 1 = sl_live c 1) by apply tb_live_ctl.
    assert (LC2 : sl_live (sl_ctl c1 5) 1 = sl_live c 1) by (rewrite tb_live_ctl; exact LC1).
    destruct (IH (sl_ctl c1 5) (sl_O c1 O1 gesture_end_c.END5) (sl_cap c1 mx (Z.of_nat (length O1)) cap1 5))
      as [IHt IHf].
    rewrite LC2 in IHt, IHf.
    split.
    + intros L. destruct (IHt L) as [IL IC].
      assert (L1 : sl_live c1 1 = true) by (rewrite LC1; exact L).
      assert (EO1 : Z.of_nat (length O1) = Z.of_nat (length O) + XL)
        by (unfold O1; rewrite (tb_slO_live c O x L), length_app; unfold XL; lia).
      assert (EO : Z.of_nat (length (sl_O c1 O1 gesture_end_c.END5)) = Z.of_nat (length O) + XL + 5).
      { rewrite (tb_slO_live c1 O1 gesture_end_c.END5 L1), length_app.
        change (length gesture_end_c.END5) with 5%nat. lia. }
      split.
      * rewrite IL, EO. cbn [map fold_right]. unfold XL, x. lia.
      * intros [|[xl ka] xks] j o E; [discriminate E|]. cbn [map fst] in E. injection E as Exl E.
        rewrite (IC xks 0%nat ga0 E), EO. cbn [keys_end_run fst snd].
        rewrite (tb_slcap_live c1 mx _ _ 5 L1), EO1. unfold cap1. rewrite (tb_slcap_live c mx _ cap XL L).
        rewrite Exl. fold x. fold XL.
        apply gestures_end_b.p3b_ker_cap. reflexivity.
    + intros L. rewrite (IHf L). unfold cap1.
      rewrite (tb_slcap_dead c1 mx _ _ 5 ltac:(rewrite LC1; exact L)). apply tb_slcap_dead. exact L.
Qed.

(* ---------------------------------------------------------------- the keys ended (geik against RelayKeys.gei) *)

Lemma tb_nth_map : forall {X Y} (f : X -> Y) (l : list X) d d' n, f d = d' -> nth n (map f l) d' = f (nth n l d).
Proof. intros X Y f l d d' n <-. apply map_nth. Qed.

Lemma tb_geik : forall f pre n ks,
  map (fun k => bzs (key_text k)) (fst (geik_loop f pre n ks)) =
  fst (RelayKeys.gei_loop f pre n (map (fun k => bzs (key_text k)) ks)).
Proof.
  induction f as [|f IH]; intros pre n ks; cbn [geik_loop RelayKeys.gei_loop]; [reflexivity|].
  rewrite length_map. destruct (Nat.ltb n (length ks)) eqn:Hl; [|reflexivity].
  rewrite (tb_nth_map (fun k => bzs (key_text k)) ks (0, [], []) [] n eq_refl). cbv beta.
  destruct (RelayKeys.has_prefix pre (bzs (key_text (nth n ks (0, [], []))))).
  - replace (RelayKeys.swap_remove [] n (map (fun k => bzs (key_text k)) ks))
      with (map (fun k => bzs (key_text k)) (RelayKeys.swap_remove (0, [], []) n ks))
      by (rewrite (relay_instance_gone_b_lem.rig_swap_map (fun k => bzs (key_text k)) (0, [], []) n ks)
            by (apply Nat.ltb_lt; exact Hl); reflexivity).
    pose proof (IH pre n (RelayKeys.swap_remove (0, [], []) n ks)) as E1. revert E1.
    destruct (geik_loop f pre n (RelayKeys.swap_remove (0, [], []) n ks)) as [Ea Ka].
    destruct (RelayKeys.gei_loop f pre n (map (fun k => bzs (key_text k)) (RelayKeys.swap_remove (0, [], []) n ks)))
      as [Et Kt].
    cbn [fst map]. intros E1. rewrite E1. reflexivity.
  - exact (IH pre (S n) ks).
Qed.

Lemma tb_geik_lens : forall pre ks,
  map (fun x => Z.of_nat (length x)) (fst (RelayKeys.gei pre (drain_b_c.keys_texts ks))) =
  map (fun k => Z.of_nat (length (key_text k))) (fst (geik pre ks)).
Proof.
  intros pre ks. unfold RelayKeys.gei, geik, drain_b_c.keys_texts. rewrite length_map, <- tb_geik, map_map.
  apply map_ext. intros k. unfold bzs. rewrite length_map. reflexivity.
Qed.

(* ---------------------------------------------------------------- the run's head entry *)

Lemma tb_skipn_combine : forall {X Y} i (l1 : list X) (l2 : list Y),
  combine (skipn i l1) (skipn i l2) = skipn i (combine l1 l2).
Proof.
  intros X Y i. induction i as [|i IH]; intros [|x l1] [|y l2]; cbn [skipn combine]; try reflexivity.
  - destruct (skipn i l1); reflexivity.
  - apply IH.
Qed.

Lemma tb_forall_combine : forall {X Y} (P : X -> Prop) (l1 : list X) (l2 : list Y),
  Forall P l1 -> Forall (fun p => P (fst p)) (combine l1 l2).
Proof.
  intros X Y P l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [combine]; try constructor.
  - apply Forall_cons_iff in H as [Hx _]. exact Hx.
  - apply Forall_cons_iff in H as [_ H]. exact (IH l2 H).
Qed.

Lemma tb_forall_skipn : forall {X} (P : X -> Prop) n (l : list X), Forall P l -> Forall P (skipn n l).
Proof.
  intros X P n. induction n as [|n IH]; intros [|x l] H; cbn [skipn]; try exact H.
  apply Forall_cons_iff in H as [_ H]. exact (IH l H).
Qed.

(* the head entry of the run: its drain's trace, its key run, the run over the entries after it *)
Lemma tb_split : forall lv mx pre e hj r no cap,
  let s := relay_remove_b_c.after_drain lv mx no cap e (fst hj) in
  let xls := map (fun x => Z.of_nat (length x)) (fst (RelayKeys.gei pre (drain_b_c.ds_H s))) in
  exists td K R,
    fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ((e, hj) :: r) (fun _ => ga0) 0 ga0))) =
      td ++ K ++ R /\
    tb_sh td (if re_eof e =? 0 then drain_b_c.drain_tr lv mx no cap e (fst hj) 0 drain_b_c.dadr0 else []) /\
    (forall xks j o, map fst xks = xls ->
       tb_sh K (fst (keys_end_run lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) xks j o))) /\
    (forall j o, tb_sh R (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx
       (drain_b_c.ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 xls)
       (fst (snd (keys_end_run lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (map (fun xl => (xl, ga0)) xls) 0 ga0)))
       pre r (fun _ => ga0) j o))))).
Proof.
  intros lv mx pre e hj r no cap. cbv zeta.
  rewrite relay_instance_gone_b_lem.rig_gone_run_cons. cbv zeta. cbn [fst snd].
  set (s := relay_remove_b_c.after_drain lv mx no cap e (fst hj)).
  assert (LD : length (drain_b_c.da_keys (relay_remove_b_c.after_drain_adr lv mx no cap e (fst hj) 0
                 (drain_b_c.drain_start (fun _ => ga0) ga0 e (fst hj)))) = length (drain_b_c.ds_H s)).
  { apply relay_instance_gone_b.gsh_after. unfold drain_b_c.drain_start. cbn [drain_b_c.da_keys].
    rewrite length_map. reflexivity. }
  pose proof (relay_instance_gone_b.gsh_xks pre _ _ LD) as XE.
  set (xls := map (fun x => Z.of_nat (length x)) (fst (RelayKeys.gei pre (drain_b_c.ds_H s)))) in *.
  eexists _, _, _. split; [reflexivity|]. split; [|split].
  - destruct (re_eof e =? 0); [apply tb_dtr_sh | reflexivity].
  - intros xks j o E. apply tb_ker_sh; [rewrite XE, E; reflexivity | intros _; split; reflexivity].
  - intros j o. rewrite XE.
    match goal with |- tb_sh ?L _ => match L with context [keys_end_run lv mx ?n0 ?c0 ?x1 ?j1 ?o1] =>
      rewrite (gestures_end_b.p3b_ker_cap lv mx x1 (map (fun xl => (xl, ga0)) xls) n0 c0 j1 o1 0%nat ga0)
        by (rewrite XE, map_map; cbn [fst]; symmetry; apply map_id) end end.
    apply tb_gone_sh.
Qed.

(* drain's own liveness against the run's: equal when a line is relayed, irrelevant when none is *)
Lemma tb_drain_go : forall c lv mx no cap e h,
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  sl_live c 1 = lv ->
  forall j a, drain_b_c.drain_go (dr_live c h) mx no cap e h j a = drain_b_c.drain_go lv mx no cap e h j a.
Proof.
  intros c lv mx no cap e h IV ER L j a.
  destruct (Z.eq_dec (dr_tot h) 0) as [T0|TP].
  - assert (LS : RelayModel.lines (hs_state h) (bzs (pending_stream h)) = []).
    { apply relay_instance_gone_b_lem.rig_wn_nil. unfold dr_tot, dr_lines in T0. lia. }
    exact (proj2 (relay_instance_gone_b_lem.rig_drain_model lv mx no cap e h IV ER) LS (dr_live c h) j a).
  - unfold dr_live. rewrite tb_live_len, L. replace (dr_tot h =? 0) with false by (symmetry; apply Z.eqb_neq; exact TP).
    rewrite andb_true_r. reflexivity.
Qed.

Lemma tb_xls_nn : forall (Hs : list (list Z)), Forall (fun x => 0 <= x) (map (fun x => Z.of_nat (length x)) Hs).
Proof. intros Hs. apply Forall_map, Forall_forall. intros x _. lia. Qed.

(* drain's relation: the held keys it leaves and the bytes it relays *)
Lemma tb_drrel : forall c mx no cap e h e1 h1 LB, dr_rel c mx no cap e h e1 h1 LB ->
  drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H (dr_fin c mx no cap e h) /\
  bzs LB = RelayModel.with_nul (dr_lines h).
Proof.
  intros c mx no cap e h e1 h1 LB H. unfold dr_rel in H. cbv zeta in H.
  destruct H as (_ & _ & _ & _ & _ & _ & KT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                 & HLB).
  split; [exact KT | exact HLB].
Qed.


(* ---- Track D's pure lemmas (no section context): the plain drain model's net change of the live bytes (C3). ---- *)

(* the bytes of texts held one per block of |text| + 1 bytes (keys, list records) *)
Definition td_lw {A : Type} (ls : list (list A)) : Z := fold_right (fun l acc => Z.of_nat (length l) + 1 + acc) 0 ls.

Lemma td_lw_one : forall {A} (x : list A), td_lw [x] = Z.of_nat (length x) + 1.
Proof. intros A x. unfold td_lw. cbn [fold_right]. lia. Qed.

Lemma td_lw_cons : forall {A} (x : list A) ls, td_lw (x :: ls) = Z.of_nat (length x) + 1 + td_lw ls.
Proof. reflexivity. Qed.

Lemma td_lw_app : forall {A} (l1 l2 : list (list A)), td_lw (l1 ++ l2) = td_lw l1 + td_lw l2.
Proof.
  intros A l1 l2. induction l1 as [|x l1 IH]; cbn [app]; [reflexivity|]. rewrite !td_lw_cons, IH. lia.
Qed.

Lemma td_lw_perm : forall {A} (l1 l2 : list (list A)), Permutation l1 l2 -> td_lw l1 = td_lw l2.
Proof. intros A l1 l2 HP. induction HP; rewrite ?td_lw_cons in *; lia. Qed.

Lemma td_lw_nonneg : forall {A} (ls : list (list A)), 0 <= td_lw ls.
Proof. intros A ls. induction ls as [|x ls IH]; [unfold td_lw; cbn [fold_right]; lia | rewrite td_lw_cons; lia]. Qed.

Lemma td_lw_map : forall {A A'} (f : A -> A') ls, td_lw (map (map f) ls) = td_lw ls.
Proof.
  intros A A' f ls. induction ls as [|x ls IH]; [reflexivity|]. cbn [map]. rewrite !td_lw_cons, IH, length_map.
  reflexivity.
Qed.

(* the harness list's texts as drain_init reads them (bzs of each) weigh what their records do *)
Lemma td_lw_pend : forall (rs : list (Z * list byte)), td_lw (map (fun r => bzs (snd r)) rs) = td_lw (map snd rs).
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. cbn [map]. rewrite !td_lw_cons, IH. unfold bzs. rewrite length_map.
  reflexivity.
Qed.

(* the buffer's growth (relay.c:178-194) *)
Lemma td_grow : forall c used j b, 0 <= c ->
  0 <= fst (snd (drain_b_c.grow_tr c used j b)) /\
  fst (snd (drain_b_c.grow_tr c used j b)) - c <= tr_net (fst (drain_b_c.grow_tr c used j b)).
Proof.
  intros c used j b Hc. unfold drain_b_c.grow_tr.
  destruct (c - used <? 4096); cbn [fst snd]; [|unfold tr_net; cbn [fold_right]; lia].
  destruct (Z.eqb_spec c 0); unfold tr_net; cbn [fold_right]; lia.
Qed.

(* send_line's g_out growth (fuzz_send): the capacity does not depend on the addresses, and moves by the requests'
   net change *)
Lemma td_sl_run_cap : forall f mx no cap rem j o j' o',
  fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) = fst (snd (send_line_b_c.sl_run f mx no cap rem j' o')).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [send_line_b_c.sl_run]; [reflexivity|].
  destruct (rem <=? 0); [reflexivity|].
  destruct (cap <? _); cbn [fst snd]; apply IH.
Qed.

Lemma td_sl_run : forall f mx no cap rem j o, 0 <= cap ->
  0 <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) /\
  fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) - cap <= tr_net (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run]; [cbn; unfold tr_net; cbn; lia|].
  destruct (rem <=? 0); [cbn; unfold tr_net; cbn; lia|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  destruct (Z.ltb_spec cap (no + n)) as [X|X]; cbn [fst snd].
  - match goal with |- context [send_line_b_c.sl_run f mx (no + n) ?c (rem - n) ?jj ?oo] =>
      destruct (IH mx (no + n) c (rem - n) jj oo ltac:(lia)) as [I1 I2] end.
    split; [exact I1|]. change (tr_net (?a :: ?t)) with (tr_net ([a] ++ t)). rewrite tr_net_app.
    destruct (Z.eqb_spec cap 0); unfold tr_net at 1; cbn [fold_right]; lia.
  - apply IH. exact Hc.
Qed.

Lemma td_send : forall live mx no cap len j o, 0 <= cap ->
  0 <= send_line_b_c.send_line_cap live mx no cap len /\
  send_line_b_c.send_line_cap live mx no cap len - cap <= tr_net (send_line_b_c.send_line_tr live mx no cap len j o).
Proof.
  intros live mx no cap len j o Hc. unfold send_line_b_c.send_line_cap, send_line_b_c.send_line_tr.
  destruct live; [|unfold tr_net; cbn; lia].
  rewrite (td_sl_run_cap _ mx no cap len 0 _ j o). exact (td_sl_run _ mx no cap len j o Hc).
Qed.

(* gesture_seen: a new key grows the array and allocates the key; an ended key is freed *)
Lemma td_seen : forall H ka l j ha ks, 0 <= ka ->
  0 <= snd (fst (drain_b_c.seen_tr H ka l j ha ks)) /\
  snd (fst (drain_b_c.seen_tr H ka l j ha ks)) + td_lw (RelayKeys.seen_arr H l) <=
    ka + td_lw H + tr_net (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof.
  intros H ka l j ha ks Hk. unfold drain_b_c.seen_tr, RelayKeys.seen_arr.
  destruct (RelayModel.gesture l) as [[[|] x]|]; [| |cbn; unfold tr_net; cbn; lia].
  - destruct (RelayKeys.index_of x H) as [n|] eqn:E; [cbn; unfold tr_net; cbn; lia|].
    cbn [fst snd]. pose proof (td_lw_app H [x]) as A1. pose proof (td_lw_one x) as A2.
    destruct (Z.eqb_spec ka 0); unfold tr_net; cbn [fold_right]; lia.
  - destruct (RelayKeys.index_of x H) as [n|] eqn:E; [|cbn; unfold tr_net; cbn; lia].
    destruct (RelayKeys.index_of_some x H n E) as (a & b & HH & Ha). subst H n.
    rewrite (td_lw_perm _ _ (RelayKeys.swap_remove_perm [] a x b)). cbn [fst snd].
    rewrite td_lw_cons. unfold tr_net; cbn [fold_right]. lia.
Qed.

(* the lines relayed in one round: g_out, the held array and the held keys *)
Lemma td_lines_run : forall rl live mx no cap H ka j o ha ks, 0 <= cap -> 0 <= ka ->
  let p := drain_b_c.lines_run live mx no cap H ka rl j o ha ks in
  0 <= fst (fst (snd (fst p))) /\ 0 <= snd (snd (fst p)) /\
  fst (fst (snd (fst p))) + snd (snd (fst p)) + td_lw (snd (fst (snd (fst p)))) <=
    cap + ka + td_lw H + tr_net (fst (fst p)).
Proof.
  induction rl as [|l r IH]; intros live mx no cap H ka j o ha ks Hc Hk; cbv zeta;
    cbn [drain_b_c.lines_run fst snd]; [unfold tr_net; cbn; lia|].
  pose proof (td_send live mx no cap (Z.of_nat (length l) + 1) j o Hc) as [S1 S2].
  match goal with |- context [drain_b_c.seen_tr H ka l ?jj ha ks] =>
    pose proof (td_seen H ka l jj ha ks Hk) as [K1 K2] end.
  match goal with |- context [drain_b_c.lines_run live mx ?no' ?cap' ?H' ?ka' r ?j' ?o' ?ha' ?ks'] =>
    destruct (IH live mx no' cap' H' ka' j' o' ha' ks' ltac:(lia) ltac:(lia)) as (I1 & I2 & I3) end.
  rewrite !tr_net_app. lia.
Qed.

(* reference_feed's pushes onto the expected list: the vector's growth (net: 128 bytes from none, else 16 cap -> 32 cap)
   and one record of |l| + 1 bytes per line *)
Lemma td_push_tra : forall v N CAP m, tr_net (ListTr.list_push_tra v N CAP m) =
  (if N =? CAP then (if CAP =? 0 then 128 else 16 * CAP) else 0) + (m + 1).
Proof.
  intros v N CAP m. unfold ListTr.list_push_tra. rewrite tr_net_app.
  destruct (N =? CAP); [destruct (CAP =? 0)|]; unfold tr_net; cbn [fold_right]; lia.
Qed.

Lemma td_pushes : forall ls n cap j v rs, 0 <= cap ->
  0 <= snd (fst (drain_b_c.pushes_run n cap ls j v rs)) /\
  AREC * snd (fst (drain_b_c.pushes_run n cap ls j v rs)) + td_lw ls <=
    AREC * cap + tr_net (fst (fst (drain_b_c.pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs Hc; cbn [drain_b_c.pushes_run fst snd];
    [unfold td_lw, tr_net; cbn; lia|].
  match goal with |- context [drain_b_c.pushes_run (n + 1) ?pc r ?jj ?vv ?rr] =>
    assert (PC : 0 <= pc /\ AREC * pc <= AREC * cap + (if n =? cap then (if cap =? 0 then 128 else 16 * cap) else 0))
      by (unfold drain_b_c.push_cap, AREC; destruct (Z.eqb_spec n cap); [destruct (Z.eqb_spec cap 0)|]; lia);
    destruct (IH (n + 1) pc jj vv rr (proj1 PC)) as [I1 I2] end.
  rewrite tr_net_app, td_push_tra, td_lw_cons.
  split; [exact I1|]. lia.
Qed.

(* the weight of drain's state: s->buf, s->held and the held keys, the expected list's vector, g_out, and the pending
   texts (each freed when read whole: C3's net form counts that free) *)
Definition td_pot (s : drain_b_c.dstate) : Z :=
  drain_b_c.ds_cap s + drain_b_c.ds_ka s + td_lw (drain_b_c.ds_H s) + AREC * drain_b_c.ds_ecap s + drain_b_c.ds_ocap s +
  td_lw (drain_b_c.ds_pend s).

(* td_pot's sum, at any state and at drain_init (instantiated rather than unfolded at drain's final state, so the
   kernel never compares drain_run's unfolding) *)
Lemma td_pot_eq : forall s, td_pot s =
  drain_b_c.ds_cap s + drain_b_c.ds_ka s + td_lw (drain_b_c.ds_H s) + AREC * drain_b_c.ds_ecap s + drain_b_c.ds_ocap s +
  td_lw (drain_b_c.ds_pend s).
Proof. reflexivity. Qed.

Lemma td_pot_init : forall no cap e h, td_pot (drain_b_c.drain_init no cap e h) =
  re_cap e + drain_b_c.ent_ka e + td_lw (drain_b_c.keys_texts (re_keys e)) + AREC * hl_cap (hs_expected h) + cap +
  td_lw (map (fun r => bzs (snd r)) (hl_recs (hs_pending h))).
Proof. reflexivity. Qed.

(* drain's rounds (the fuel and invariant of relay_instance_gone_b_lem.rig_dr_lines): the potential plus the records
   of the reference lines still to push moves by at most the rounds' net change *)
Lemma td_run : forall f live mx s j a,
  relay_instance_gone_b_lem.dr_inv s ->
  (length (relay_instance_gone_b_lem.dr_rest s) + (if drain_b_c.ds_eintr s then 2 else 1) <= f)%nat ->
  0 <= drain_b_c.ds_ka s -> 0 <= drain_b_c.ds_ecap s -> 0 <= drain_b_c.ds_ocap s ->
  td_pot (fst (snd (drain_b_c.drain_run f live mx s j a))) +
    td_lw (RelayModel.lines (drain_b_c.ds_ref s) (relay_instance_gone_b_lem.dr_rest s)) <=
  td_pot s + tr_net (fst (drain_b_c.drain_run f live mx s j a)).
Proof.
  induction f as [|f IH]; intros live mx [c u sk H ka ei pd off rf en ec no oc] j a INV FU KA EC OC;
    [destruct ei; cbn [drain_b_c.ds_eintr] in FU; lia|].
  unfold relay_instance_gone_b_lem.dr_inv in INV. unfold relay_instance_gone_b_lem.dr_rest in FU |- *.
  cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_eintr
       drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap drain_b_c.ds_no
       drain_b_c.ds_ocap] in INV, FU, KA, EC, OC |- *.
  destruct INV as (J & HC & HP).
  pose proof J as (Jk & Jw & Jl & Jz).
  pose proof (relay_instance_gone_b_lem.rig_ll_z _ Jl) as UL'.
  assert (UL'' : 0 <= Z.of_nat (length u) <= 6000) by (clear - UL'; lia).
  pose proof (relay_instance_gone_b_lem.rig_grow c (Z.of_nat (length u)) j (drain_b_c.da_buf a) HC UL'') as [G1 G2].
  pose proof (td_grow c (Z.of_nat (length u)) j (drain_b_c.da_buf a) ltac:(lia)) as [G3 G4].
  cbn [drain_b_c.drain_run drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
       drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap
       drain_b_c.ds_no drain_b_c.ds_ocap].
  set (cp := fst (snd (drain_b_c.grow_tr c (Z.of_nat (length u)) j (drain_b_c.da_buf a)))) in *.
  set (tg := fst (drain_b_c.grow_tr c (Z.of_nat (length u)) j (drain_b_c.da_buf a))) in *.
  destruct ei; cbv beta iota in FU.
  - (* EINTR: the growth only *)
    match goal with |- context [drain_b_c.drain_run f live mx (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc) ?jj ?aa] =>
      assert (IV : relay_instance_gone_b_lem.dr_inv (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc))
        by (unfold relay_instance_gone_b_lem.dr_inv;
            cbn [drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_ref drain_b_c.ds_cap drain_b_c.ds_pend drain_b_c.ds_off];
            split; [exact J|]; split; [lia|exact HP]);
      pose proof (IH live mx (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc) jj aa IV
                    ltac:(unfold relay_instance_gone_b_lem.dr_rest;
                          cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_eintr]; lia)
                    KA EC OC) as E end.
    unfold relay_instance_gone_b_lem.dr_rest in E.
    cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref] in E. cbn [fst snd]. rewrite tr_net_app.
    unfold td_pot in E |- *.
    cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend] in E |- *.
    lia.
  - destruct pd as [|r0 rs].
    + (* nothing pending: the growth only, no line left *)
      cbn [relay_instance_gone_b_lem.dr_rest_of fst snd].
      assert (Z0 : td_lw (RelayModel.lines rf []) = 0) by reflexivity.
      unfold td_pot. cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend]. lia.
    + (* a data round: d read, its reference lines pushed, its relayed lines sent and seen *)
      destruct HP as [HO HF].
      match goal with |- context [Z.min ?x ?y <=? 0] => remember (Z.min x y) as nn eqn:Enn end.
      assert (NP : 0 < nn) by (rewrite Enn; lia).
      assert (NL : nn <= Z.of_nat (length r0) - off) by (rewrite Enn; lia).
      destruct (Z.leb_spec nn 0) as [X|X]; [lia|]. clear X.
      set (d := firstn (Z.to_nat nn) (skipn (Z.to_nat off) r0)) in *.
      pose proof (RelayModel.chunk_ok u sk rf d J) as CK.
      destruct (RelayModel.chunk u sk d) as [[u' sk'] rl] eqn:ECH.
      destruct CK as [Erl J'].
      set (PEND := if off + nn =? Z.of_nat (length r0) then rs else r0 :: rs) in *.
      set (OFF := if off + nn =? Z.of_nat (length r0) then 0 else off + nn) in *.
      assert (RS : relay_instance_gone_b_lem.dr_rest_of (r0 :: rs) off =
                   d ++ relay_instance_gone_b_lem.dr_rest_of PEND OFF /\
                   relay_instance_gone_b_lem.dr_pend_ok PEND OFF).
      { unfold PEND, OFF, d. cbn [relay_instance_gone_b_lem.dr_rest_of].
        destruct (Z.eqb_spec (off + nn) (Z.of_nat (length r0))) as [W|W].
        - split.
          + rewrite firstn_all2 by (rewrite length_skipn; lia). f_equal.
            destruct rs as [|r1 rs1]; reflexivity.
          + destruct rs as [|r1 rs1]; [exact I|]. inversion HF as [|? ? HF1 HF2]; subst.
            cbn [relay_instance_gone_b_lem.dr_pend_ok]. split; [lia | exact HF2].
        - split.
          + cbn [relay_instance_gone_b_lem.dr_rest_of].
            replace (Z.to_nat (off + nn)) with (Z.to_nat nn + Z.to_nat off)%nat by lia.
            rewrite <- skipn_skipn, app_assoc, firstn_skipn. reflexivity.
          + cbn [relay_instance_gone_b_lem.dr_pend_ok]. split; [lia | exact HF]. }
      destruct RS as [RS1 RS2].
      assert (IVG : forall H' ka' en' ec' no' oc',
                 relay_instance_gone_b_lem.dr_inv
                   (drain_b_c.DS cp u' sk' H' ka' false PEND OFF (RelayModel.feed rf d) en' ec' no' oc')).
      { intros. unfold relay_instance_gone_b_lem.dr_inv.
        cbn [drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_ref drain_b_c.ds_cap drain_b_c.ds_pend drain_b_c.ds_off].
        split; [exact J'|]. split; [lia | exact RS2]. }
      assert (FUG : forall H' ka' en' ec' no' oc',
                 (length (relay_instance_gone_b_lem.dr_rest
                            (drain_b_c.DS cp u' sk' H' ka' false PEND OFF (RelayModel.feed rf d) en' ec' no' oc')) +
                  (if drain_b_c.ds_eintr
                        (drain_b_c.DS cp u' sk' H' ka' false PEND OFF (RelayModel.feed rf d) en' ec' no' oc')
                   then 2 else 1) <= f)%nat).
      { assert (DL : length d = Z.to_nat nn)
          by (unfold d; rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
        intros. unfold relay_instance_gone_b_lem.dr_rest. cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_eintr].
        rewrite RS1, length_app in FU. lia. }
      match goal with |- context [drain_b_c.pushes_run en ec (RelayModel.lines rf d) ?jj ?vv ?rr] =>
        pose proof (td_pushes (RelayModel.lines rf d) en ec jj vv rr EC) as [P1 P2] end.
      match goal with |- context [drain_b_c.lines_run live mx no oc H ka rl ?j3 ?o3 ?h3 ?k3] =>
        pose proof (td_lines_run rl live mx no oc H ka j3 o3 h3 k3 OC KA) as LR;
        destruct (drain_b_c.lines_run live mx no oc H ka rl j3 o3 h3 k3) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] end.
      cbn [fst snd] in LR |- *. destruct LR as (L1 & L2 & L3).
      match goal with |- context [drain_b_c.drain_run f live mx (drain_b_c.DS _ _ _ _ _ _ _ _ _ ?en' ?ec' ?no' _) ?jj ?aa] =>
        pose proof (IH live mx _ jj aa (IVG H1 ka1 en' ec' no' oc1) (FUG H1 ka1 en' ec' no' oc1) L2 P1 L1) as E end.
      unfold relay_instance_gone_b_lem.dr_rest in E.
      cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref] in E.
      rewrite RS1, RelayModel.lines_app, td_lw_app, !tr_net_app.
      (* the head text, freed when read whole (list_drop), leaves the pending texts' weight *)
      match goal with |- context [tr_net (if ?b then ListTr.list_drop_tra ?x ?y else [])] =>
        assert (TDN : td_lw PEND <= td_lw (r0 :: rs) + tr_net (if b then ListTr.list_drop_tra x y else []))
          by (unfold PEND; destruct b; unfold ListTr.list_drop_tra, tr_net; cbn [fold_right]; rewrite ?td_lw_cons; lia) end.
      unfold td_pot in E |- *.
      cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend] in E |- *.
      lia.
Qed.

(* drain_go from drain_init: the reference lines of the pending stream are all pushed (dr_inv / dr_rest, the premises
   of relay_instance_gone_b_lem.rig_drain_model) *)
Lemma td_drain : forall live mx no cap e h,
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  0 <= drain_b_c.ent_ka e -> 0 <= hl_cap (hs_expected h) -> 0 <= cap ->
  td_pot (drain_b_c.drain_fin live mx no cap e h) + td_lw (RelayModel.lines (hs_state h) (bzs (pending_stream h))) <=
    td_pot (drain_b_c.drain_init no cap e h) + tr_net (drain_b_c.drain_tr live mx no cap e h 0 drain_b_c.dadr0).
Proof.
  intros live mx no cap e h IV ER KA EC OC.
  assert (FU : (length (relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h)) +
                (if drain_b_c.ds_eintr (drain_b_c.drain_init no cap e h) then 2 else 1)
                <= S (S (length (pending_stream h))))%nat).
  { rewrite ER. unfold bzs. rewrite length_map. destruct (drain_b_c.ds_eintr _); lia. }
  pose proof (td_run (S (S (length (pending_stream h)))) live mx (drain_b_c.drain_init no cap e h) 0 drain_b_c.dadr0
                IV FU KA EC OC) as E.
  rewrite ER in E. change (drain_b_c.ds_ref (drain_b_c.drain_init no cap e h)) with (hs_state h) in E.
  unfold drain_b_c.drain_fin, drain_b_c.drain_tr, drain_b_c.drain_go. exact E.
Qed.

(* the bytes of the blocks W_rep.v represents an entry, a source and g_out over *)
Lemma td_bsum_keys : forall ks,
  bsum (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks) = td_lw (drain_b_c.keys_texts ks).
Proof.
  intros ks. unfold drain_b_c.keys_texts. induction ks as [|k ks IH]; [reflexivity|].
  cbn [map]. rewrite bsum_cons, td_lw_cons, IH. cbn [snd]. unfold bzs. rewrite length_map. reflexivity.
Qed.

Lemma td_bsum_recs : forall (rs : list (Z * list byte)),
  bsum (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) rs) = td_lw (map snd rs).
Proof.
  intros rs. induction rs as [|r rs IH]; [reflexivity|]. cbn [map]. rewrite bsum_cons, td_lw_cons, IH. reflexivity.
Qed.

Lemma td_bsum_entry : forall e,
  bsum (aentry_blks e) = re_cap e + drain_b_c.ent_ka e + td_lw (drain_b_c.keys_texts (re_keys e)).
Proof.
  intros e. unfold aentry_blks, drain_b_c.ent_ka. rewrite !bsum_app, td_bsum_keys.
  destruct (Z.eqb_spec (re_cap e) 0); destruct (Z.eqb_spec (re_hp e) 0); cbn [bsum fold_right snd]; lia.
Qed.

Lemma td_bsum_list : forall l, bsum (alist_blks l) = AREC * hl_cap l + td_lw (map snd (hl_recs l)).
Proof.
  intros l. unfold alist_blks. rewrite bsum_app, td_bsum_recs. unfold AREC.
  destruct (Z.eqb_spec (hl_cap l) 0); cbn [bsum fold_right snd]; lia.
Qed.

Lemma td_bsum_src : forall h, bsum (asrc_blks h) =
  APARTIAL + bsum (alist_blks (hs_pending h)) + bsum (alist_blks (hs_expected h)) + bsum (alist_blks (hs_held h)).
Proof. intros h. unfold asrc_blks. rewrite bsum_cons, !bsum_app. cbn [snd]. lia. Qed.

Lemma td_bsum_out : forall cap out, bsum (aout_blks cap out) = cap.
Proof. intros cap out. unfold aout_blks. destruct (Z.eqb_spec cap 0); cbn [bsum fold_right snd]; lia. Qed.


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
(* the program statics of the generic journal (YCbqG.ajournal_x's image clause exempts them) *)
Variable PST : list (Z * Z).
(* the allocator relation, its third argument the head set Hp *)
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'): W_relay_instance_gone_cx.v
   Section c's list, verbatim (its literals' facts at the cx's glit_at_x).  Each is either the AR walk's (AR-free,
   verbatim), its _x twin, or an instance fact that the instance supplies where RIG_x is plugged (top_x); the AR
   re-derivation was deleted (W_relay_instance_gone.v's header says why). ---- *)
(* the instance's laws, over ARx *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling; W_journal_x.v range_addressable_of_block_hp0_x) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MLAW : ameter_laws MT.
(* the frame twins' hypotheses (W_frame_x.v), in place of ML / SMP: the image cover IMGC (frm_off_imgP_x); a live
   block's size is non-negative (W_kit_x.v's BLKN); the owned-low law OWNLOW, the model invariant WFx with its law WFL,
   and the two facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
(* the fake frame's laws over ARx: __asan_stack_malloc_1 (class 1), the release's flag store and frame free *)
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 1.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
(* the live-state meter does not see the fake frame: its seat and release are set_fs's of the state (Reusable/YG01.v
   stack_free_state); TOP's proofs do not use it *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HGRIG : gx_ok SEGS B (G_RIG B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x82d58 (kept at 72(sp), listing A_HI 44) and 0x82d74
   (s6, A_HI 45).  The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges
   both by vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH44 : VAL (A_HI 44) = rg_nsrc RG + RIG_HI_NSRC.
Hypothesis HH45 : VAL (A_HI 45) = rg_src RG + RIG_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are image bytes (so apart from the frames, the fake frame's shadow and the stack).  The pinned
   placement decides both by vm_compute at fr_globals, as W7's W_drain_cx.v HRGD / HGSB. *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime (W_gesture_end.v's HROMO form): rom_view survives the stack
   allocator's calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RIG B RG).
(* the allocator instance's granule-tail fact (W7's ALLOC_TAIL over ARx, as W_drain_cx_x.v states it; there a theorem
   of the laws, alloc_tail_x): a held key is represented over its |text| + 1 bytes (ruling (A)); a word read of a
   key to the end of its last granule is visible *)
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the runtime entries relay_instance_gone calls, at their SIGMA pcs, over ARx (W_sites_x.v / W_contract_x.v /
   W_journal_x.v Section hc; the free rule at the room record RP).  snprintf: a Theorem Labs lane's statement at fuzz_reply's
   addresses (W_sites.v asnprintf_realizes, its twin W_sites_x.v asnprintf_realizes_x), which the snprintf chain
   (commit 9067b7156f9, lib/A/RT_pf_vf.v snprintf_chain_ok, through a Theorem Labs lane's evt -> SRr bridge) discharges. *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis ASNPRINTF : asnprintf_realizes_x B ARx (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
(* the program functions relay_instance_gone calls (W7's drain, W4's gesture_end), by their published _x room specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GE : ge_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gesture_end).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* snprintf's stack-protector cells (see the header): the GOT word, a fact of every ARx state (at ARi0: the AR fact
   of lib/A/AE22.v got_canary_of_AR); the canary, image bytes *)
Hypothesis HGOTG : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  rdword (aview SEGS (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
(* the canary's bytes are image bytes (seg_rom SEGS at FR_GUARD .. + 8 is Some 0), so aview reads them in EVERY state
   through mbyte's seg_rom fallback: aguard_ok's second half needs nothing carried (a Theorem Labs lane's ruling; a Theorem Labs lane's
   pin measurement).  PB_fr decides it by vm_compute. *)
Hypothesis HCANR : forall a, FR_GUARD <= a < FR_GUARD + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None.
(* the two literals of the snprintf call and " end\0" (.str.4, A_lit_end5 = A_OBJ 31), in the cx's glit_at_x form
   over ARx (W_relay_instance_gone_cx.v: bytes, in_rom, ashp_x, the granule's tail) *)
Hypothesis HLIT20 : glit_at_x ARx 20 (RIG_FMT ++ [0]).
Hypothesis HLIT21 : glit_at_x ARx 21 (RelayModel.K_GESTURE ++ [0]).
(* the two literals lie in .rodata below the GOT word FR_GOT_GUARD = 0x9e658, |"%s %d "| + 1 = 7 and
   |"param_gesture"| + 1 + 8 = 22 bytes: the location premises M1 / M3 of the narrowed asnprintf_realizes_x
   (W_sites_x.v), which this abstract placement does not fix.  PB_fr decides it by vm_compute: SnpNarrowSites.v
   HLITGOT_PB_fr, whose statement is this text at PI := PB_fr (commit 2f48fc47493's hypothesis, carried here). *)
Hypothesis HLITGOT : VAL (A_OBJ 20) + 7 <= FR_GOT_GUARD /\ VAL (A_OBJ 21) + 22 <= FR_GOT_GUARD.
Hypothesis HLIT31 : glit_at_x ARx 31 ([32; 101; 110; 100] ++ [0]).
(* The program statics PST hold no byte this walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x, the literals and " end\0"), and no byte of the
   relay's and the output's global cells (G_RIG, and the cells of HRGP that G_RIG does not name: g_src, g_nsrc,
   g_capsrc, g_send_max, g_client, g_send_dead).  At PST := [] both hold trivially (the template's PSTR / PSTC /
   PSTO, lib/A/W_relay_finish_h.v). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a,
(inG (G_RIG B RG) a \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
 rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ Exists (in_zr a) PST.

(* ======================================================================================================
   The statements of TOP's lemma tracks (inside the Section: they read its variables, not its hypotheses).
   ====================================================================================================== *)
Definition A_rig_pd : Z := AF_fr_relay_instance_gone + 0x1a4.    (* 0x82dd0, after the drain step *)

(* What TOP keeps of entry i's drain (drain's post, dr_post_x, at the callee's final state ly2 S2 W2 m2): the
   conjuncts the walk uses, named.  rest is dr_post_x's: the live blocks drain does not own. *)
Definition DRK (cx : gcx) (i : nat) (c2 : ctl) (O2 : list byte) (cap2 out2 : Z)
  (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
  (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (m2 : word -> option byte) : Prop :=
let e := gnth cx i in
let h := fst (ghj cx i) in
let no := Z.of_nat (length O2) in
let fin := dr_fin c2 (gxmx cx) no cap2 e h in
let live := dr_live c2 h in
let cap' := if live then drain_b_c.ds_ocap fin else cap2 in
exists (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) (rest : list (Z * Z)),
apres_kept B W1 m1 W2 m2 /\
mo_le MT S1 S2 (dr_cost MT c2 (gxmx cx) no cap2 e h) /\
Permutation (ablocks B ly1 S1) (aentry_blks e ++ asrc_blks h ++ aout_blks cap2 out2 ++ rest) /\
Permutation (ablocks B ly2 S2) (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) /\
garr8 SEGS (arm W2 m2) (gSA cx i) (bzs (entry_bytes e')) /\ awr W2 m2 (gSA cx i) AENT /\
aentry_ok B ly2 S2 W2 m2 e' /\
dr_rel c2 (gxmx cx) no cap2 e h e' h' LB /\
asrc_at B ly2 S2 W2 m2 (gslot RG cx i) h' /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (gslot RG cx i <= a < gslot RG cx i + ASRC) -> abyte_kept W1 m1 W2 m2 a) /\
aout_at B RG ly2 S2 W2 m2 (dr_ctl c2 h ev') (if live then O2 ++ LB else O2) (gxmx cx) (if live then no + dr_tot h else no)
  cap' out'.

(* GTOPM: inside entry i after its drain step (drained when open: gdrained), before its keys; GIN's facts at
   n = 0, ks = re_keys e1, Ed = [] less the prefix, its shadow, the measure and the budget. *)
Definition GTOPM (cx : gcx) (i : nat) (qd : list (rentry * hsrc)) (cB : ctl) (OB : list byte) (capB : Z)
  (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (c1 : ctl) (O1 : list byte) (cap1 out1 : Z)
  (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
let e := gnth cx i in
let h := fst (ghj cx i) in
let open := re_eof e =? 0 in
(i < length (gxes cx))%nat /\ length qd = i /\
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd cB OB capB /\
gdrained cx cB OB capB e h e1 h1 ev LB c1 O1 cap1 /\
arelay_at B RG ly1 S1 W1 m1 (gxG0 cx) (map fst qd ++ e1 :: skipn (S i) (gxes cx)) /\
aout_at B RG ly1 S1 W1 m1 c1 O1 (gxmx cx) (Z.of_nat (length O1)) cap1 out1 /\
(forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
   asrc_at B ly1 S1 W1 m1 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
(open = true -> asrc_at B ly1 S1 W1 m1 (gslot RG cx i) h1) /\
Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly1 S1 W1 m1 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
   abyte_kept (gxW cx) (gxmem cx) W1 m1 a) /\
Permutation (ablocks B ly1 S1)
  ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ e1 :: skipn (S i) (gxes cx))) ++
   gdone_srcs (firstn i (gps cx)) qd ++ (if open then asrc_blks h1 else []) ++ rig_srcs (skipn (S i) (gps cx)) ++
   aout_blks cap1 out1 ++ gxrest cx).

(* the budget after the drain step: entry i's key run, then the entries after it *)
Definition gtop_bud (cx : gcx) (e1 : rentry) (c1 : ctl) (O1 : list byte) (cap1 : Z) (i : nat) (ly1 : alayout)
  (S1 : astate) (spent : Z) : Prop :=
let Er := fst (geik (gpre cx) (re_keys e1)) in
let '(_, O3, cap3) := sl_sends (gxmx cx) c1 O1 cap1 (ge_bytes Er) in
gbud B MT RP MMAX cx ly1 S1 spent (gkrest cx (Z.of_nat (length O1)) cap1 Er ++ grest cx (S i) (Z.of_nat (length O3)) cap3).

(* THE ROOM drain leaves (dr_spec_x's kr at TOP's call): the MT_rk count of the requests after entry i's drain (the
   rest of grest i) on top of the entry's budget gxkr *)
Definition dr_kr (cx : gcx) (i : nat) (c2 : ctl) (no2 cap2 : Z) : nat :=
(Z.to_nat (tr_cost MT_rk (grest cx i no2 cap2) - dr_cost MT_rk c2 (gxmx cx) no2 cap2 (gnth cx i) (fst (ghj cx i))) +
 gxkr cx)%nat.

(* ---------------------------------------------------------------- statements of TOP's lemma tracks *)

(* B1. drain's model invariant at entry i's drain, from the relay entry and the harness source (W_contract.v
   dr_src_ok, W_rep.v aentry_ok): the premises of lib/Prog/relay_instance_gone_b_lem.v rig_drain_model. *)
Definition stmt_dr_inv_of : Prop :=
forall ly S W mem e h j no cap,
aentry_ok B ly S W mem e -> dr_src_ok B RG ly S W mem e h j ->
relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) /\
relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h).

(* B2. drain's room at entry i (dr_spec_x's budget premises: the meter, and the room round's room and count), from
   GOUT i's budget. *)
Definition stmt_top_room : Prop :=
forall cx i qd c2 O2 cap2 spent ly1 S1,
let e := gnth cx i in let h := fst (ghj cx i) in let no2 := Z.of_nat (length O2) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> length qd = i -> re_eof e = 0 ->
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd c2 O2 cap2 ->
(ct_cl c2 = 3 \/ ct_cl c2 = -1) -> (ct_br c2 = 0 \/ ct_br c2 = 1) -> (ct_dd c2 = 0 \/ ct_dd c2 = 1) ->
0 <= cap2 -> 0 <= gxmx cx <= 255 ->
relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no2 cap2 e h) ->
relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no2 cap2 e h) = bzs (pending_stream h) ->
gbud B MT RP MMAX cx ly1 S1 spent (grest cx i no2 cap2) ->
tr_max (dr_tr c2 (gxmx cx) no2 cap2 e h) < MMAX /\
blocks_bytes S1 + tr_peak (dr_tr c2 (gxmx cx) no2 cap2 e h) <= LIVE_MAX /\
mo_ok MT S1 (dr_cost MT c2 (gxmx cx) no2 cap2 e h) /\
rp_RM RP S1 (Z.to_nat (dr_cost MT_rk c2 (gxmx cx) no2 cap2 e h) + dr_kr cx i c2 no2 cap2) /\
cnt_ok_pk RP (dr_pk c2 (gxmx cx) no2 cap2 e h) (ablocks B ly1 S1).

(* B3. the budget across the drain step: GOUT i's budget, the drain's charge, room and count change (open) or
   nothing (not open), gives the budget of entry i's key run followed by the entries after it (gtop_bud). *)
Definition stmt_top_budget : Prop :=
forall cx i qd c2 O2 cap2 spent ly1 S1 ly2 S2 e1 h1 ev LB c1 O1 cap1,
let e := gnth cx i in let h := fst (ghj cx i) in let no2 := Z.of_nat (length O2) in
let open := re_eof e =? 0 in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> length qd = i ->
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd c2 O2 cap2 ->
(ct_cl c2 = 3 \/ ct_cl c2 = -1) -> (ct_br c2 = 0 \/ ct_br c2 = 1) -> (ct_dd c2 = 0 \/ ct_dd c2 = 1) ->
0 <= cap2 -> 0 <= gxmx cx <= 255 ->
gbud B MT RP MMAX cx ly1 S1 spent (grest cx i no2 cap2) ->
gdrained cx c2 O2 cap2 e h e1 h1 ev LB c1 O1 cap1 ->
(open = true ->
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no2 cap2 e h) /\
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no2 cap2 e h) = bzs (pending_stream h) /\
  mo_le MT S1 S2 (dr_cost MT c2 (gxmx cx) no2 cap2 e h) /\
  blocks_bytes S2 <= blocks_bytes S1 + tr_net (dr_tr c2 (gxmx cx) no2 cap2 e h) /\
  rp_RM RP S2 (dr_kr cx i c2 no2 cap2) /\
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) =
     Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) + tr_netP P (dr_tr c2 (gxmx cx) no2 cap2 e h))) ->
(open = false -> mo_le MT S1 S2 0 /\ blocks_bytes S2 <= blocks_bytes S1 /\
  rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (grest cx i no2 cap2)) + gxkr cx) /\ ablocks B ly2 S2 = ablocks B ly1 S1) ->
gtop_bud cx e1 c1 O1 cap1 i ly2 S2 (spent + (if open then dr_cost MT c2 (gxmx cx) no2 cap2 e h else 0)).

(* D. drain's live bytes: what drain leaves of its entry, source and output (DRK's Permutations, dr_rel, the
   output capacity) holds at most its request trace's net change (tr_net, C3) more than it found. *)
Definition stmt_dr_bytes : Prop :=
forall ly S W mem ly' S' c mx no cap out out' e h e' h' LB rest HA,
let fin := dr_fin c mx no cap e h in
let cap' := if dr_live c h then drain_b_c.ds_ocap fin else cap in
aentry_ok B ly S W mem e -> asrc_at B ly S W mem HA h -> 0 <= cap -> 0 <= mx <= 255 -> 0 <= no ->
relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) ->
Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) ->
dr_rel c mx no cap e h e' h' LB ->
blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr c mx no cap e h).

(* D'. drain's live counts (the room round): over the blocks drain's post names, the count of the blocks whose size
   satisfies P moves by exactly the net count tr_netP P of drain's trace.  The RR family's model lemma, its text:
   lib/A/W_rr_m_dcnt.v rmc_dr_cnt (a Theorem Labs lane's RR_x round); TOP takes it as this statement and rig_top_proof plugs
   rmc_dr_cnt in. *)
Definition stmt_dr_cnt : Prop :=
forall c mx no cap out out' e h e' h' LB (P : Z -> bool),
let fin := dr_fin c mx no cap e h in
let cap' := if dr_live c h then drain_b_c.ds_ocap fin else cap in
relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
(re_hp e = 0 \/ re_kh e <> 0) -> (re_hp e' = 0 \/ re_kh e' <> 0) -> 0 <= cap ->
dr_rel c mx no cap e h e' h' LB ->
Z.of_nat (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out')) =
Z.of_nat (ReplyCnt.acnt P (aentry_blks e ++ asrc_blks h ++ aout_blks cap out)) + tr_netP P (dr_tr c mx no cap e h).

(* C1. the relay after entry i's drain (open entry): GOUT i at the drain's entry state, drain's journal and DRK
   give GTOPM at drain's final state. *)
Definition stmt_top_rep_open : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 sp1 ly2 S2 Hp2 W2 m2 md2 k2,
let e := gnth cx i in let h := fst (ghj cx i) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof e = 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x sp1 (dr_fp (gSA cx i) e h cap2 out2)
  ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2 ->
alloc_ceiling <= sp1 - DRAIN_STK_x ->
DRK cx i c2 O2 cap2 out2 ly1 S1 W1 m1 ly2 S2 W2 m2 ->
exists e1 h1 ev LB out1,
let no2 := Z.of_nat (length O2) in
let live := dr_live c2 h in
let c1 := dr_ctl c2 h ev in
let O1 := if live then O2 ++ LB else O2 in
let cap1 := if live then drain_b_c.ds_ocap (dr_fin c2 (gxmx cx) no2 cap2 e h) else cap2 in
GTOPM cx i qd c2 O2 cap2 e1 h1 ev LB c1 O1 cap1 out1 ly2 S2 W2 m2.

(* C2. the same step for an entry already closed (no drain): GOUT i gives GTOPM at the same state. *)
Definition stmt_top_rep_closed : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof (gnth cx i) <> 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
GTOPM cx i qd c2 O2 cap2 (gnth cx i) (fst (ghj cx i)) 0 [] c2 O2 cap2 out2 ly1 S1 W1 m1.

(* C3. GOUT and GTOPM survive a memory change that keeps every byte below alloc_ceiling outside the fake frame
   (1, fpos) and its shadow (in_frames), and keeps present bytes present: the walk's stores to the stack and to
   F's shadow, snprintf's write into F + 32 .. F + 80, and the runtime calls' scratch. *)
Definition stmt_gout_kept : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 m1' fpos,
GBASE B ARx MT RP MMAX RG cx ->
ARx ly1 S1 Hp1 W1 m1 md1 -> In (1, fpos) (frames S1) ->
(forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a -> aview SEGS (w_H W1) m1' a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m1' a) ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1'.
Definition stmt_gtopm_kept : Prop :=
forall cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 m1' fpos,
GBASE B ARx MT RP MMAX RG cx ->
ARx ly1 S1 Hp1 W1 m1 md1 -> In (1, fpos) (frames S1) ->
(forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a -> aview SEGS (w_H W1) m1' a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m1' a) ->
GTOPM cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 W1 m1 ->
GTOPM cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 W1 m1'.

(* C4. what drain's contract asks of entry i (open) at TOP's call, from GOUT i (dr_spec_x's memory premises). *)
Definition stmt_top_drain_pre : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1,
let e := gnth cx i in let h := fst (ghj cx i) in let j := snd (ghj cx i) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof e = 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
In (gxG0 cx, ATABLE) (ablocks B ly1 S1) /\ gxG0 cx <= gSA cx i /\ gSA cx i + AENT <= gxG0 cx + ATABLE /\
garr8 SEGS (arm W1 m1) (gSA cx i) (bzs (entry_bytes e)) /\ awr W1 m1 (gSA cx i) AENT /\
aentry_ok B ly1 S1 W1 m1 e /\ dr_src_ok B RG ly1 S1 W1 m1 e h j /\
(exists rest, Permutation (ablocks B ly1 S1) ((gxG0 cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks cap2 out2 ++ rest)).

(* C5. drain's footprint lies in TOP's (gse_callS_x's footprint premise at the drain call): every byte drain may
   write is a byte of the journal's footprint that is in a live block now, or a byte of a block made since the
   entry. *)
Definition stmt_dr_fp_in : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1,
let e := gnth cx i in let h := fst (ghj cx i) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof e = 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
forall a, inFP (dr_fp (gSA cx i) e h cap2 out2) a ->
(inFP (gFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
in_tmp_block (ablocks B (gxly cx) (gxS cx)) (ablocks B ly1 S1) a.

(* L1. GLIVE and the loop's frame slots survive a stretch of the walk that writes only (P) the scratch below sp,
   the slots 32(sp) and 88(sp), the prefix buffer F + 32 .. F + 80 and F's shadow, keeps present bytes present and
   carries the journal (the run's own journal at the new memory). *)
Definition stmt_live_kept : Prop :=
forall cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 Hp2 m2 md2 (P : Z -> Prop),
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> g_lslots RG cx F W1 m1 ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp2 W1 m2 md2 k1 ->
(forall a, P a -> (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (gsp1 cx + 32 <= a < gsp1 cx + 40) \/
   (gsp1 cx + 88 <= a < gsp1 cx + 96) \/ (F + 32 <= a < F + 80) \/ (shadow_addr F <= a < shadow_addr F + 16)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
GLIVE B PST ARx RG cx F FL ly1 S1 W1 m2 md2 k1 /\ g_lslots RG cx F W1 m2.

(* L2. GLIVE and the loop's frame slots across the drain call at 0x82dcc: the caller's journal at the call, drain's
   journal (at G_DR, from sp = gsp1, footprint dr_fp: block bytes only), drain's apres_kept and the composed journal
   (gse_callS_x's) give GLIVE at drain's final state. *)
Definition stmt_live_drain : Prop :=
forall cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 SA e h cap out ly2 S2 Hp2 W2 m2 md2 k2 Hp3 k3,
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> g_lslots RG cx F W1 m1 ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (gsp1 cx) (dr_fp SA e h cap out)
  ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2 ->
(forall a, inFP (dr_fp SA e h cap out) a -> exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) ->
apres_kept B W1 m1 W2 m2 ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly2 S2 Hp3 W2 m2 md2 k3 ->
GLIVE B PST ARx RG cx F FL ly2 S2 W2 m2 md2 k3 /\ g_lslots RG cx F W2 m2.

(* G1. entry i's key loop starts (nheld = S r > 0): GTOPM, the budget after the drain step, the prefix and its zero
   shadow in the fake frame give GIN at n = 0, ks = re_keys e1, nothing ended (Ed = []), the stream (c1, O1, cap1). *)
Definition stmt_gin_top : Prop :=
forall cx i r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx ->
GTOPM cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 W1 m1 ->
gtop_bud cx e1 c1 O1 cap1 i ly1 S1 spent ->
re_nheld e1 = Z.of_nat (S r) ->
garr8 SEGS (arm W1 m1) (F + 32) (gpre cx ++ [0]) ->
garr8 SEGS (arm W1 m1) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] ->
exists ks f, GIN B MT RP MMAX RG cx i 0 r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks [] f c1 O1 cap1 out1 spent ly1 S1 W1 m1.

(* G2. entry i holds no key (nheld <= 0): GTOPM and the budget give GOUT (S i). *)
Definition stmt_gout_top : Prop :=
forall cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx ->
GTOPM cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 W1 m1 ->
gtop_bud cx e1 c1 O1 cap1 i ly1 S1 spent ->
re_nheld e1 <= 0 ->
exists qd', GOUT B MT RP MMAX RG cx (S i) qd' c1 O1 cap1 out1 spent ly1 S1 W1 m1.

(* ---- the two runtime calls of TOP: snprintf (F + 32, 48, "%s %d ", "param_gesture", id) at 0x82e04 and
   strlen (F + 32) at 0x82e0c, over the walk's journal (own = [(1, fpos)], the fake frame F). ---- *)
(* S1. the snprintf call at 0x82e04 *)
Definition stmt_snp_call : Prop :=
forall W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F id idv (Post : world SEGS -> config -> Prop),
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (F + 32) -> getr regsT 11 = w64 48 -> getr regsT 12 = w64 (VAL (A_OBJ 20)) ->
getr regsT 13 = w64 (VAL (A_OBJ 21)) -> getr regsT 14 = w64 idv -> idv mod 2 ^ 32 = id mod 2 ^ 32 -> - 2 ^ 31 <= id < 2 ^ 31 ->
frame_addr lyc 1 fpos = F ->
(forall o, 4 <= o < 10 -> aview SEGS (w_H W) memT (shadow_addr F + o) = Some 0) ->
rom_view SEGS W memT ->
(forall regs2 mem2 md2,
   ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W mem2 md2 k ->
   aregs_preserved regsT regs2 ->
   getr regs2 10 = w64 (Z.of_nat (length (relay_instance_gone_b_c.instance_prefix id))) ->
   garr8 SEGS (arm W mem2) (F + 32) (relay_instance_gone_b_c.instance_prefix id ++ [0]) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 80) -> ~ (sp0 - 224 - 3 * ESTACK <= a < sp0 - 224) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
   SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_snprintf)) memT (seg_rom SEGS)) mdc) Post.

(* S2. the strlen call at 0x82e0c *)
Definition stmt_strlen_call : Prop :=
forall W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F (pre : list Z) (Post : world SEGS -> config -> Prop),
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (F + 32) -> frame_addr lyc 1 fpos = F ->
garr8 SEGS (arm W memT) (F + 32) (pre ++ [0]) -> ~ In 0 pre -> (length pre <= 47)%nat ->
(forall o, 4 <= o < 10 -> aview SEGS (w_H W) memT (shadow_addr F + o) = Some 0) ->
rom_view SEGS W memT ->
(forall regs2 mem2 md2,
   ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W mem2 md2 k ->
   aregs_preserved regsT regs2 -> getr regs2 10 = w64 (Z.of_nat (length pre)) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 224 - 2 * ESTACK <= a < sp0 - 224) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
   SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Post) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_strlen)) memT (seg_rom SEGS)) mdc) Post.

(* ---- small helpers shared by the tracks below ---- *)
(* a byte of a garr8 string, as aview reads it *)
Lemma tp_garr8_aview : forall H mem a l j, garr8 SEGS (mrestrict H mem) a l -> (j < length l)%nat ->
aview SEGS H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof. intros H mem a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (aview_of_val_mem1 SEGS H mem _ _ Hv Hr). Qed.
(* a journal keeps the top of the stack layout (its layout_le clause) *)
Lemma tp_ly_top : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* the state at a journal's end is an ARx state (ajournal_gx_AR_x with the arguments inferred) *)
Lemma tj_AR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ARx ly' S' Hp' W' mem' md'.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
(* W_gestures_end.v's gse_pres over ajournal_gx_x: the journal's stack window is present at its end *)
Lemma tj_pres : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & _) & _) a Ha.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.
(* a live block's size is nonnegative and its blocks are distinct (gse_nodup_x at this Section's laws) *)
Lemma tj_nodup : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof. exact (gse_nodup_x B ARx LAWS BLKN). Qed.
(* ---- W_rig_top_bud ---- *)

(* ---------------------------------------------------------------- B1: drain's model invariant *)

Lemma dr_inv_of : stmt_dr_inv_of.
Proof.
  unfold stmt_dr_inv_of. intros ly S W mem e h j no cap HE HS.
  destruct HE as (_ & HSK & _ & _ & _ & HCAP & HUL & HUM & HUZ & _).
  destruct HS as (_ & HA & _ & _ & HOV & HUW & _).
  destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _ & _ & _ & _ & HPD & _).
  destruct HPL as (_ & _ & _ & _ & _ & _ & _ & _ & HPF).
  apply relay_instance_gone_b_lem.rig_dinit; [exact HSK | exact HOV | exact HUW | unfold APARTIAL in HUM; lia |
    exact HUZ | lia | exact HPD |].
  eapply Forall_impl; [|exact HPF]. intros r (_ & _ & _ & Hr). exact (Hr eq_refl).
Qed.

(* ---------------------------------------------------------------- the budget's head entry *)

(* GOUT i's budget at entry i: the run from entry i on is entry i's head (drain, key run) and the rest *)
Lemma tb_grest_cons : forall cx i no cap, (i < length (gxes cx))%nat -> length (gxhs cx) = length (gxes cx) ->
  grest cx i no cap =
  fst (fst (fst (relay_instance_gone_b_c.gone_run (sl_live (gxc cx) 1) (gxmx cx) no cap (gpre cx)
     ((gnth cx i, ghj cx i) :: combine (skipn (S i) (gxes cx)) (skipn (S i) (gxhs cx))) (fun _ => ga0) 0 ga0))).
Proof.
  intros cx i no cap Hi HL. unfold grest, relay_instance_gone_b_c.relay_instance_gone_tr.
  rewrite !tb_skipn_combine, (relay_instance_gone_b_lem.rig_skipn_combine (gxes cx) (gxhs cx) i
    relay_remove_b_c.no_entry relay_instance_gone_b_c.no_hj Hi HL).
  reflexivity.
Qed.

(* the budget after entry i's drain, from the three pieces of the run's head: the drain's trace td (charged), the
   key run K and the rest R, given what the drain left (s: the held keys, g_capout, g_nout when live); the room
   round: the room left for K ++ R, and the live counts moved by td's net count *)
Lemma tb_core : forall cx i e1 c1 O1 cap1 ly1 S1 ly2 S2 spent td K R s,
  gbud B MT RP MMAX cx ly1 S1 spent (td ++ K ++ R) ->
  (forall xks j o, map fst xks = map (fun x => Z.of_nat (length x)) (fst (RelayKeys.gei (gpre cx) (drain_b_c.ds_H s))) ->
     tb_sh K (fst (keys_end_run (sl_live (gxc cx) 1) (gxmx cx) (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) xks j o))) ->
  (forall j o, tb_sh R (fst (fst (fst (relay_instance_gone_b_c.gone_run (sl_live (gxc cx) 1) (gxmx cx)
     (drain_b_c.ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0
        (map (fun x => Z.of_nat (length x)) (fst (RelayKeys.gei (gpre cx) (drain_b_c.ds_H s)))))
     (fst (snd (keys_end_run (sl_live (gxc cx) 1) (gxmx cx) (drain_b_c.ds_no s) (drain_b_c.ds_ocap s)
        (map (fun xl => (xl, ga0)) (map (fun x => Z.of_nat (length x)) (fst (RelayKeys.gei (gpre cx) (drain_b_c.ds_H s)))))
        0 ga0)))
     (gpre cx) (combine (skipn (S i) (gxes cx)) (skipn (S i) (gxhs cx))) (fun _ => ga0) j o))))) ->
  drain_b_c.ds_H s = drain_b_c.keys_texts (re_keys e1) ->
  drain_b_c.ds_ocap s = cap1 ->
  (sl_live (gxc cx) 1 = true -> drain_b_c.ds_no s = Z.of_nat (length O1)) ->
  sl_live c1 1 = sl_live (gxc cx) 1 ->
  mo_le MT S1 S2 (tr_cost MT td) -> blocks_bytes S2 <= blocks_bytes S1 + tr_net td -> 0 <= tr_cost MT td ->
  rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (K ++ R)) + gxkr cx) ->
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) = Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) + tr_netP P td) ->
  gtop_bud cx e1 c1 O1 cap1 i ly2 S2 (spent + tr_cost MT td).
Proof.
  intros cx i e1 c1 O1 cap1 ly1 S1 ly2 S2 spent td K R s HG TK TR FH FC FN FL HMO HBB HCN HRM HCNT.
  set (xls := map (fun x => Z.of_nat (length x)) (fst (RelayKeys.gei (gpre cx) (drain_b_c.ds_H s)))) in *.
  set (Er := fst (geik (gpre cx) (re_keys e1))).
  assert (XL : xls = map (fun k => Z.of_nat (length (key_text k))) Er)
    by (unfold xls, Er; rewrite FH; apply tb_geik_lens).
  unfold gtop_bud. fold Er.
  pose proof (tb_sends (gxmx cx) Er c1 O1 cap1) as [ST SF].
  destruct (sl_sends (gxmx cx) c1 O1 cap1 (ge_bytes Er)) as [[c3 O3] cap3] eqn:ES. cbn [fst snd] in ST, SF.
  (* the key run *)
  assert (SKR : tb_sh K (gkrest cx (Z.of_nat (length O1)) cap1 Er)).
  { assert (E' : map fst (map (fun k => (Z.of_nat (length (key_text k)), ga0)) Er) = xls)
      by (rewrite map_map, XL; reflexivity).
    apply (tb_sh_trans _ _ _ (TK _ 0%nat ga0 E')). unfold gkrest.
    apply tb_ker_sh; [reflexivity|]. intros L. split; [exact (FN L) | exact FC]. }
  (* the entries after entry i *)
  assert (SR : tb_sh R (grest cx (S i) (Z.of_nat (length O3)) cap3)).
  { specialize (TR 0%nat ga0). rewrite FC in TR.
    assert (EX : map fst (map (fun xl => (xl, ga0)) xls) = map (fun k => Z.of_nat (length (key_text k))) Er)
      by (rewrite map_map; cbn [fst]; rewrite map_id; exact XL).
    unfold grest, relay_instance_gone_b_c.relay_instance_gone_tr.
    destruct (sl_live (gxc cx) 1) eqn:LVE.
    - destruct (ST FL) as [SL SC].
      rewrite (SC (map (fun xl => (xl, ga0)) xls) 0%nat ga0 EX), SL, <- XL, <- (FN eq_refl). exact TR.
    - rewrite (SF FL). rewrite tb_ker_false in TR. cbn [fst snd] in TR.
      apply (tb_sh_trans _ _ _ TR). rewrite (tb_gone_false (gxmx cx) (gpre cx) _ _ (Z.of_nat (length O3)) cap1).
      unfold tb_sh. reflexivity. }
  (* the measures: the peak of the run after the drain, from the peak of the run with it (tr_peak_app) and the
     drain's net change; the room round's room (MT_rk's count of K ++ R) and counts (tr_peakP_app) the same way *)
  unfold gbud in HG |- *. destruct HG as (M & SP & C & A & X & RM & CNT).
  set (GK := gkrest cx (Z.of_nat (length O1)) cap1 Er) in *.
  set (GR := grest cx (S i) (Z.of_nat (length O3)) cap3) in *.
  destruct (tb_sh_meas MT _ _ SKR) as (CK & XK). destruct (tb_sh_meas MT _ _ SR) as (CR & XR).
  destruct (tb_sh_meas MT_rk _ _ SKR) as (CKr & _). destruct (tb_sh_meas MT_rk _ _ SR) as (CRr & _).
  destruct (tb_sh_pn _ _ SKR) as (PK & NK). destruct (tb_sh_pn _ _ SR) as (PR & _).
  pose proof (tb_cost_app MT td (K ++ R)) as E1. pose proof (tb_cost_app MT K R) as E2.
  pose proof (tb_cost_app MT GK GR) as E3.
  pose proof (tb_cost_app MT_rk K R) as E2r. pose proof (tb_cost_app MT_rk GK GR) as E3r.
  rewrite !tr_peak_app in A. rewrite !tb_max_app in X.
  rewrite tr_peak_app, tb_max_app, <- PK, <- PR, <- NK, <- XK, <- XR.
  split; [exact (mo_le_trans MT MLAW _ _ _ _ _ M HMO)|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [rewrite E3r, <- CKr, <- CRr, <- E2r; exact HRM|].
  refine (cnt_ok_pk_mono RP _ _ _ _ _ CNT). intros P. cbv beta.
  destruct (tb_sh_cnt _ _ SKR P) as [QK NQK]. destruct (tb_sh_cnt _ _ SR P) as [QR _].
  rewrite !tr_peakP_app, <- QK, <- QR, <- NQK.
  pose proof (HCNT P) as HC.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P td). pose proof (ReplyCnt.tr_peakP_nonneg _ P K).
  pose proof (ReplyCnt.tr_peakP_nonneg _ P R).
  lia.
Qed.

(* ---------------------------------------------------------------- B2: drain's room *)

Lemma top_room : stmt_top_room.
Proof.
  unfold stmt_top_room. intros cx i qd c2 O2 cap2 spent ly1 S1. cbv zeta.
  intros HB Hi Hq EO HR Hcl Hbr Hdd Hc2 Hmx IV ER HG.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & HREL & _ & _ & HLEN & _ & _ & _ & _ & _ & HMOK & _).
  destruct HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEOK & _).
  pose proof (tb_rel_live _ _ _ _ _ _ _ _ _ _ HR) as LV.
  pose proof (tb_split (sl_live (gxc cx) 1) (gxmx cx) (gpre cx) (gnth cx i) (ghj cx i)
                (combine (skipn (S i) (gxes cx)) (skipn (S i) (gxhs cx))) (Z.of_nat (length O2)) cap2) as SP.
  cbv zeta in SP. destruct SP as (td & K & R & EQ & TD & TK & TR).
  rewrite (tb_grest_cons cx i _ _ Hi HLEN), EQ in HG.
  pose proof (tb_drain_go c2 (sl_live (gxc cx) 1) (gxmx cx) _ _ _ _ IV ER LV) as DG.
  assert (TRE : dr_tr c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i)) =
                drain_b_c.drain_tr (sl_live (gxc cx) 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i)
                  (fst (ghj cx i)) 0 drain_b_c.dadr0).
  { unfold dr_tr, drain_b_c.drain_tr. rewrite DG. reflexivity. }
  rewrite (proj2 (Z.eqb_eq _ _) EO), <- TRE in TD. destruct (tb_sh_meas MT _ _ TD) as (TC & TM).
  destruct (tb_sh_pn _ _ TD) as (TP & _).
  assert (CN : 0 <= tr_cost MT td).
  { rewrite TC. destruct IV as (_ & IC & _). cbn [drain_b_c.drain_init drain_b_c.ds_cap] in IC.
    apply (tb_nn_meas MT _ MLAW). unfold dr_tr. apply tb_dtr_nn; lia. }
  (* the key run and the entries after entry i ask nonnegative sizes *)
  set (s := relay_remove_b_c.after_drain (sl_live (gxc cx) 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i)
              (fst (ghj cx i))) in *.
  pose proof (proj1 (RelayCap.after_drain_le (sl_live (gxc cx) 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i)
                       (fst (ghj cx i)))) as HN. fold s in HN.
  set (xls := map (fun x => Z.of_nat (length x)) (fst (RelayKeys.gei (gpre cx) (drain_b_c.ds_H s)))) in *.
  assert (NK : 0 <= tr_cost MT K).
  { assert (E' : map fst (map (fun xl => (xl, ga0)) xls) = xls) by (rewrite map_map; cbn [fst]; apply map_id).
    destruct (tb_sh_meas MT _ _ (TK _ 0%nat ga0 E')) as (C1 & _). rewrite C1.
    apply (tb_nn_meas MT _ MLAW). apply tb_ker_nn; [lia | lia|].
    apply Forall_map. cbn [fst]. apply tb_xls_nn. }
  assert (NR : 0 <= tr_cost MT R).
  { destruct (tb_sh_meas MT _ _ (TR 0%nat ga0)) as (C1 & _). rewrite C1.
    apply (tb_nn_meas MT _ MLAW). apply tb_gone_nn; [lia | |].
    - pose proof (tb_fold_nn xls (tb_xls_nn _)). lia.
    - apply (tb_forall_combine (fun e' => 0 <= re_cap e')), tb_forall_skipn.
      eapply Forall_impl; [|exact HEOK]. intros e' (_ & _ & _ & _ & _ & HC & _). lia. }
  unfold gbud in HG. destruct HG as (M & SP & C & A & X & RM & CNT).
  destruct (tb_sh_meas MT_rk _ _ TD) as (TCr & _).
  rewrite !tb_cost_app in C. rewrite tr_peak_app in A. rewrite !tb_max_app in X.
  unfold dr_kr. rewrite (tb_grest_cons cx i _ _ Hi HLEN), EQ.
  unfold dr_cost. rewrite <- TC, <- TP, <- TM, <- TCr.
  split; [lia|]. split; [lia|].
  split; [apply (mok_station MT (gxS cx) S1 (tr_cost MT (gtr cx)) spent (tr_cost MT td) MLAW HMOK M CN); lia|].
  (* the room round: drain's MT_rk count and the rest's split gbud's room; drain's count peak is the head's *)
  split.
  { refine (RMM_of RP S1 _ _ _ RM). pose proof (tb_cost_app MT_rk td (K ++ R)).
    pose proof (tb_rk_nn td). pose proof (tb_rk_nn (K ++ R)). lia. }
  refine (cnt_ok_pk_mono RP _ _ _ _ _ CNT). intros P. unfold dr_pk. cbv beta.
  destruct (tb_sh_cnt _ _ TD P) as [QP _]. rewrite <- QP, (tr_peakP_app _ P td (K ++ R)).
  pose proof (ReplyCnt.tr_peakP_nonneg _ P td). lia.
Qed.

(* ---------------------------------------------------------------- B3: the budget across the drain step *)

Lemma top_budget : stmt_top_budget.
Proof.
  unfold stmt_top_budget. intros cx i qd c2 O2 cap2 spent ly1 S1 ly2 S2 e1 h1 ev LB c1 O1 cap1. cbv zeta.
  intros HB Hi Hq HR Hcl Hbr Hdd Hc2 Hmx HG HD HOP HCL.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _).
  pose proof (tb_rel_live _ _ _ _ _ _ _ _ _ _ HR) as LV.
  pose proof (tb_split (sl_live (gxc cx) 1) (gxmx cx) (gpre cx) (gnth cx i) (ghj cx i)
                (combine (skipn (S i) (gxes cx)) (skipn (S i) (gxhs cx))) (Z.of_nat (length O2)) cap2) as SP.
  cbv zeta in SP. destruct SP as (td & K & R & EQ & TD & TK & TR).
  rewrite (tb_grest_cons cx i _ _ Hi HLEN), EQ in HG.
  unfold gdrained in HD. cbv zeta in HD. destruct HD as (Ec1 & EO1 & Ecap1 & HDR).
  destruct (Z.eq_dec (re_eof (gnth cx i)) 0) as [EO|EO].
  - (* open: drain's charge *)
    pose proof (proj2 (Z.eqb_eq _ _) EO) as EB.
    rewrite EB in TD, Ec1, EO1, Ecap1, HDR, HOP |- *. cbn [andb] in EO1, Ecap1.
    destruct (HOP eq_refl) as (IV & ER & HMO & HBB & HRM & HCNT). clear HOP HCL.
    pose proof (tb_drain_go c2 (sl_live (gxc cx) 1) (gxmx cx) _ _ _ _ IV ER LV) as DG.
    assert (FIN : dr_fin c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i)) =
                  relay_remove_b_c.after_drain (sl_live (gxc cx) 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i)
                    (fst (ghj cx i))).
    { rewrite (RelayCap.after_drain_fin _ _ _ _ _ _ EO). unfold dr_fin, drain_b_c.drain_fin. rewrite DG. reflexivity. }
    assert (TRE : dr_tr c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i)) =
                  drain_b_c.drain_tr (sl_live (gxc cx) 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i)
                    (fst (ghj cx i)) 0 drain_b_c.dadr0).
    { unfold dr_tr, drain_b_c.drain_tr. rewrite DG. reflexivity. }
    assert (CN : 0 <= dr_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i))).
    { destruct IV as (_ & IC & _). cbn [drain_b_c.drain_init drain_b_c.ds_cap] in IC.
      apply (tb_nn_meas MT _ MLAW). unfold dr_tr. apply tb_dtr_nn; lia. }
    rewrite <- TRE in TD. destruct (tb_sh_meas MT _ _ TD) as (TC & _). destruct (tb_sh_pn _ _ TD) as (_ & TN).
    destruct (tb_sh_meas MT_rk _ _ TD) as (TCr & _).
    destruct (tb_drrel _ _ _ _ _ _ _ _ _ HDR) as [KT HLB].
    (* the room drain's post leaves is the MT_rk count of K ++ R on top of gxkr; the counts moved by td's *)
    unfold dr_kr in HRM. rewrite (tb_grest_cons cx i _ _ Hi HLEN), EQ in HRM.
    assert (HRM' : rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (K ++ R)) + gxkr cx)).
    { refine (RMM_of RP S2 _ _ _ HRM). unfold dr_cost. rewrite <- TCr.
      pose proof (tb_cost_app MT_rk td (K ++ R)). lia. }
    assert (HCNT' : forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) =
      Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) + tr_netP P td).
    { intros P. rewrite (HCNT P). destruct (tb_sh_cnt _ _ TD P) as [_ QN]. rewrite QN. reflexivity. }
    unfold dr_cost in HMO, CN |- *. rewrite <- TC in HMO, CN |- *. rewrite <- TN in HBB.
    apply (tb_core cx i e1 c1 O1 cap1 ly1 S1 ly2 S2 spent td K R _ HG TK TR);
      [| | | | exact HMO | exact HBB | exact CN | exact HRM' | exact HCNT'].
    + rewrite KT, FIN. reflexivity.
    + destruct (dr_live c2 (fst (ghj cx i))) eqn:DL; rewrite Ecap1.
      * rewrite FIN. reflexivity.
      * rewrite <- FIN. unfold dr_fin. rewrite DL. apply RelayCap.drain_ocap_dead.
    + intros L. rewrite <- FIN. unfold dr_fin.
      rewrite (proj1 (relay_instance_gone_b_lem.rig_drain_model _ _ _ _ _ _ IV ER)).
      rewrite EO1. destruct (dr_live c2 (fst (ghj cx i))) eqn:DL.
      * rewrite length_app, Nat2Z.inj_add. f_equal. f_equal.
        rewrite <- (length_map bz LB). change (map bz LB) with (bzs LB). rewrite HLB. reflexivity.
      * unfold dr_live in DL. rewrite tb_live_len, LV, L in DL. cbn [andb] in DL.
        apply negb_false_iff, Z.eqb_eq in DL. unfold dr_tot, dr_lines in DL. lia.
    + rewrite Ec1, tb_live_drctl. exact LV.
  - (* not open: no charge *)
    pose proof (proj2 (Z.eqb_neq _ _) EO) as EB.
    rewrite EB in TD, Ec1, EO1, Ecap1, HDR, HCL |- *. cbn [andb] in EO1, Ecap1.
    destruct (HCL eq_refl) as (HMO & HBB & HRM & HAB). clear HOP HCL.
    try match goal with |- context [if false then ?x else 0] => change (if false then x else 0) with 0 end.
    destruct HDR as [-> ->]. subst c1 O1 cap1.
    destruct (tb_sh_meas MT _ _ TD) as (TC & _). destruct (tb_sh_pn _ _ TD) as (_ & TN). cbn in TC, TN.
    destruct (tb_sh_meas MT_rk _ _ TD) as (TCr & _).
    assert (TCr0 : tr_cost MT_rk td = 0) by (rewrite TCr; reflexivity).
    rewrite (tb_grest_cons cx i _ _ Hi HLEN), EQ in HRM.
    assert (HRM' : rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (K ++ R)) + gxkr cx)).
    { refine (RMM_of RP S2 _ _ _ HRM). pose proof (tb_cost_app MT_rk td (K ++ R)). lia. }
    assert (HCNT' : forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) =
      Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) + tr_netP P td).
    { intros P. rewrite HAB. destruct (tb_sh_cnt _ _ TD P) as [_ QN]. rewrite QN. change (tr_netP P []) with 0. lia. }
    replace (spent + 0) with (spent + tr_cost MT td) by lia.
    rewrite (RelayCap.after_drain_init _ _ _ _ _ _ EO) in TK, TR.
    apply (tb_core cx i (gnth cx i) c2 O2 cap2 ly1 S1 ly2 S2 spent td K R _ HG TK TR); try reflexivity.
    + exact LV.
    + rewrite TC. exact HMO.
    + rewrite TN. lia.
    + lia.
    + exact HRM'.
    + exact HCNT'.
Qed.

(* ---- W_rig_top_bytes ---- *)

(* the held array's size (aentry_ok: re_kh >= 8 when s->held is set) and the expected list's capacity
   (alist_at: n <= cap) are nonnegative *)
Lemma td_ka_nonneg : forall ly S W mem e, aentry_ok B ly S W mem e -> 0 <= drain_b_c.ent_ka e.
Proof using Type.
  intros ly S W mem e HE. unfold aentry_ok in HE.
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHP & _).
  unfold drain_b_c.ent_ka.
  destruct HHP as [(E0 & _)|(E0 & _ & _ & K8 & _)]; destruct (Z.eqb_spec (re_hp e) 0); lia.
Qed.

Lemma td_ecap_nonneg : forall ly S W mem HA h, asrc_at B ly S W mem HA h -> 0 <= hl_cap (hs_expected h).
Proof using Type.
  intros ly S W mem HA h HS. unfold asrc_at in HS.
  destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEX & _).
  unfold alist_at in HEX. destruct HEX as (_ & _ & _ & _ & [HN _] & _). unfold hl_n in HN. lia.
Qed.

(* D. drain's live bytes *)
Lemma dr_bytes : stmt_dr_bytes.
Proof using Type.
  unfold stmt_dr_bytes. intros ly S W mem ly' S' c mx no cap out out' e h e' h' LB rest HA. cbv zeta.
  intros HE HS Hcap Hmx Hno IV ER P1 P2 REL.
  pose proof (td_ka_nonneg ly S W mem e HE) as KA.
  pose proof (td_ecap_nonneg ly S W mem HA h HS) as EC.
  pose proof (td_drain (dr_live c h) mx no cap e h IV ER KA EC Hcap) as D.
  (* a dead drain keeps g_capout *)
  assert (OC : (if dr_live c h then drain_b_c.ds_ocap (dr_fin c mx no cap e h) else cap) =
               drain_b_c.ds_ocap (dr_fin c mx no cap e h)).
  { unfold dr_fin. destruct (dr_live c h); [reflexivity|].
    destruct (relay_instance_gone_b_lem.rig_drain_false mx no no cap e h 0 drain_b_c.dadr0) as (_ & _ & _ & X).
    symmetry. exact X. }
  rewrite OC in P2.
  destruct REL as (_ & _ & _ & R4 & _ & _ & R7 & R8 & _ & _ & R11 & _ & _ & _ & _ & R16 & _ & _ & R19 & _ & _ & R22 &
                   _ & R24 & _).
  rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B ly S), (bsum_perm _ _ P1), (bsum_perm _ _ P2), !bsum_app.
  rewrite !td_bsum_entry, !td_bsum_src, !td_bsum_list, !td_bsum_out.
  assert (Z0 : td_lw (map snd (hl_recs (hs_pending h'))) = 0) by (rewrite R16; reflexivity).
  rewrite R4, R7, R8, R11, R19, R22, R24, td_lw_app, td_lw_map.
  pose proof (td_pot_eq (drain_b_c.drain_fin (dr_live c h) mx no cap e h)) as PF.
  pose proof (td_pot_init no cap e h) as PI0.
  (* the pending texts drain_init reads weigh what h's pending records do; drain's final pending texts weigh >= 0 *)
  pose proof (td_lw_pend (hl_recs (hs_pending h))) as LWP.
  pose proof (td_lw_nonneg (drain_b_c.ds_pend (drain_b_c.drain_fin (dr_live c h) mx no cap e h))) as NPF.
  unfold dr_fin, dr_tr, dr_lines.
  (* drain's final state, its trace's net change and the reference lines' records as opaque values, and only the
     facts the sum needs: no hypothesis is converted through drain_run (its kernel unfolding is costly) *)
  clear - D Z0 PF PI0 LWP NPF. revert D PF PI0 NPF.
  generalize (drain_b_c.drain_fin (dr_live c h) mx no cap e h) as F.
  generalize (tr_net (drain_b_c.drain_tr (dr_live c h) mx no cap e h 0 drain_b_c.dadr0)) as T.
  generalize (td_lw (RelayModel.lines (hs_state h) (bzs (pending_stream h)))) as L.
  intros L T F D PF PI0 NPF. unfold AREC in *. lia.
Qed.

(* ---- W_rig_top_rep ---- *)

(* ---- list helpers ---- *)
Lemma tc_firstn_S : forall {A : Type} (l : list A) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros A l. induction l as [|x l IH]; intros i d Hi; [cbn in Hi; lia|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. rewrite (IH i d) by (cbn in Hi; lia). reflexivity.
Qed.
Lemma tc_len_gps : forall cx, length (gxhs cx) = length (gxes cx) -> length (gps cx) = length (gxes cx).
Proof. intros cx HL. unfold gps. rewrite length_combine, HL. lia. Qed.
Lemma tc_gps_nth : forall cx i, length (gxhs cx) = length (gxes cx) ->
  nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i).
Proof. intros cx i HL. unfold gps, gnth, ghj. apply combine_nth. symmetry. exact HL. Qed.
Lemma tc_skipn_es : forall cx i, (i < length (gxes cx))%nat -> skipn i (gxes cx) = gnth cx i :: skipn (S i) (gxes cx).
Proof. intros cx i Hi. unfold gnth. apply skipn_nth. exact Hi. Qed.
Lemma tc_skipn_gps : forall cx i, length (gxhs cx) = length (gxes cx) -> (i < length (gxes cx))%nat ->
  skipn i (gps cx) = (gnth cx i, ghj cx i) :: skipn (S i) (gps cx).
Proof.
intros cx i HL Hi. rewrite (skipn_nth (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj))
  by (rewrite tc_len_gps by exact HL; exact Hi).
rewrite tc_gps_nth by exact HL. reflexivity.
Qed.
Lemma tc_firstn_gps : forall cx i, length (gxhs cx) = length (gxes cx) -> (i < length (gxes cx))%nat ->
  firstn (S i) (gps cx) = firstn i (gps cx) ++ [(gnth cx i, ghj cx i)].
Proof.
intros cx i HL Hi. rewrite (tc_firstn_S (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj))
  by (rewrite tc_len_gps by exact HL; exact Hi).
rewrite tc_gps_nth by exact HL. reflexivity.
Qed.
Lemma tc_rig_slots_app : forall l1 l2, rig_slots (l1 ++ l2) = rig_slots l1 ++ rig_slots l2.
Proof. intros l1 l2. unfold rig_slots. rewrite map_app, concat_app. reflexivity. Qed.
Lemma tc_rig_srcs_cons : forall p l,
  rig_srcs (p :: l) = (if re_eof (fst p) =? 0 then asrc_blks (fst (snd p)) else []) ++ rig_srcs l.
Proof. intros p l. reflexivity. Qed.
Lemma tc_slot_lt4 : forall cx i, GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof (gnth cx i) = 0 ->
  (snd (ghj cx i) < 4)%nat.
Proof.
intros cx i HB Hi He. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & HDRS0 & _).
rewrite Forall_forall in HDRS0.
assert (Hin : In (nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj)) (gps cx))
  by (apply nth_In; rewrite tc_len_gps by exact HLEN; exact Hi).
rewrite tc_gps_nth in Hin by exact HLEN.
pose proof (HDRS0 _ Hin) as Hd. cbn [fst snd] in Hd. exact (proj1 (Hd He)).
Qed.

(* ---- keeping bytes ---- *)
(* writability survives a step whose hidden set shrinks and that keeps the byte present if it was *)
Lemma tc_wr_kept : forall (W W' : world SEGS) (m m' : word -> option byte) a,
  hsub (w_H W') (w_H W) -> (apresent (w_H W) m a -> apresent (w_H W') m' a) ->
  writable_at SEGS (arm W m) a -> writable_at SEGS (arm W' m') a.
Proof.
intros W W' m m' a Hs Hp Hw. unfold arm, writable_at, wview, mrestrict in *. revert Hw.
destruct (w_H W' (Z_to_bv 64 a)) eqn:E'.
- rewrite (Hs _ E'). intros Hw. exact Hw.
- destruct (w_H W (Z_to_bv 64 a)) eqn:E.
  + intros Hw. destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; intros Hw.
    * destruct (Hp (conj E (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
    * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* the representation's global cells are image bytes *)
Definition tc_glob (a : Z) : Prop :=
  rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4 \/
  rg_s RG <= a < rg_s RG + 4 * ASRC \/
  rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
  rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
  rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
  rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/ as_errno B <= a < as_errno B + 4.
Lemma tc_glob_img : rg_place B RG -> forall a, tc_glob a -> in_img SEGS a.
Proof.
intros RGP a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
assert (GI : forall x l, In (x, l) (G_RIG B RG) -> x <= a < x + l -> in_img SEGS a).
{ intros x l Hxl Hx. apply (proj1 (HGRIG a ltac:(unfold inG; apply Exists_exists; exists (x, l); split;
    [exact Hxl | unfold in_zr; cbn [fst snd]; lia]))). }
assert (RI : rg_rng RG a -> in_img SEGS a) by (intros Hr; exact (proj1 (RGIMG a Hr))).
unfold rg_rng in RI. unfold tc_glob in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]].
- apply RI. tauto.
- apply RI. tauto.
- exact (proj1 (HRGI a ltac:(tauto))).
- apply RI. tauto.
- exact (proj1 (HRGI a ltac:(tauto))).
- apply (GI (rg_nout RG) 8); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- apply (GI (rg_capout RG) 8); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- apply (GI (rg_out RG) 8); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- exact (proj1 (HRGI a ltac:(tauto))).
- apply (GI (rg_client_broken RG) 1); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- exact (proj1 (HRGI a ltac:(tauto))).
- apply (GI (rg_send_eintr RG) 1); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- apply (GI (as_errno B) 4); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
Qed.

(* A memory change that keeps every byte below alloc_ceiling outside the fake frame (1, fpos) and its shadow, and
   keeps present bytes present, keeps every byte of a live block and every image byte. *)
Lemma tc_keep_frame : forall ly S Hp W m md m' fpos,
  ARx ly S Hp W m md -> In (1, fpos) (frames S) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly [(1, fpos)] a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  forall a, tinb B ly S a \/ in_img SEGS a -> abyte_kept W m W m' a.
Proof.
intros ly S Hp W m md m' fpos HAR Hfin HK HP a Ha.
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in *.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
split; [|unfold arm; apply writable_kept; apply HP].
set (F := frame_addr ly 1 fpos) in *.
assert (Hnf : forall x, ~ (F <= x < F + 128) -> ~ (shadow_addr F <= x < shadow_addr F + 16) ->
  ~ in_frames ly [(1, fpos)] x).
{ intros x N1 N2 (cid & pos & Hin & Hr). destruct Hin as [Heq | []]. injection Heq as <- <-.
  change (fs_frame_bytes 1) with 128 in Hr. change (128 / 8) with 16 in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
  fold F in Hr. tauto. }
assert (SF : shadow_addr F = 2147450880 + F / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
destruct Ha as [(p & n & Hin & Ha) | Hi].
- destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hin) as (_ & Hp4 & Hpc & Happ & _ & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ p n 1 fpos HAR Hin Hfin) as Hd.
  change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  apply HK; [lia|]. apply Hnf; [lia|].
  intros Hs. rewrite SF in Hs. apply (fshadow_not_app F 16 p (req_size n) a); [lia | lia | exact Happ | lia | lia].
- pose proof (pa_segs_low a Hi) as Hl. rewrite C5 in Hl.
  apply HK; [lia|]. apply Hnf.
  + intros Hx. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR _) Hi). right. left. exists 1, fpos.
    split; [exact Hfin|]. change (fs_frame_bytes 1) with 128. fold F. lia.
  + rewrite SF. assert (0 <= F / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* aothers_at survives when the first 8 bytes of every slot but ji are kept, and slot ji passes at the end *)
Lemma tc_aothers_kept : forall W m W' m' (j : nat) fd (ji : nat),
  aothers_at RG W m j fd ->
  (forall i, (i < 4)%nat -> i <> ji -> forall a, rg_s RG + ASRC * Z.of_nat i <= a < rg_s RG + ASRC * Z.of_nat i + 8 ->
     abyte_kept W m W' m' a) ->
  (ji <> j -> exists f o, val_mem SEGS (arm W' m') (rg_s RG + ASRC * Z.of_nat ji) 4 f /\
     val_mem SEGS (arm W' m') (rg_s RG + ASRC * Z.of_nat ji + 4) 4 o /\ (o = 0 \/ f mod 2 ^ 32 <> fd mod 2 ^ 32)) ->
  aothers_at RG W' m' j fd.
Proof.
intros W m W' m' j fd ji HO HK Hji i Hi Hij. destruct (Nat.eq_dec i ji) as [-> | Hne]; [exact (Hji Hij)|].
destruct (HO i Hi Hij) as (f & o & V1 & V2 & Ho). exists f, o. split; [|split; [|exact Ho]].
- apply (akept_vm W m); [intros x Hx; apply (HK i Hi Hne); cbn in Hx; lia | exact V1].
- apply (akept_vm W m); [intros x Hx; apply (HK i Hi Hne); cbn in Hx; lia | exact V2].
Qed.

(* the representation predicates GOUT and GTOPM read, across such a memory change *)
Lemma tc_kept_pack : forall cx ly1 S1 Hp1 W1 m1 md1 m1' fpos,
  GBASE B ARx MT RP MMAX RG cx -> ARx ly1 S1 Hp1 W1 m1 md1 -> In (1, fpos) (frames S1) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a -> aview SEGS (w_H W1) m1' a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m1' a) ->
  (forall G es, arelay_at B RG ly1 S1 W1 m1 G es -> arelay_at B RG ly1 S1 W1 m1' G es) /\
  (forall c O mx no cap out, aout_at B RG ly1 S1 W1 m1 c O mx no cap out -> aout_at B RG ly1 S1 W1 m1' c O mx no cap out) /\
  (forall (j : nat) h, (j < 4)%nat -> asrc_at B ly1 S1 W1 m1 (rg_s RG + ASRC * Z.of_nat j) h ->
     asrc_at B ly1 S1 W1 m1' (rg_s RG + ASRC * Z.of_nat j) h) /\
  (forall e h j, dr_src_ok B RG ly1 S1 W1 m1 e h j -> dr_src_ok B RG ly1 S1 W1 m1' e h j) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W1 m1' a).
Proof.
intros cx ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP.
pose proof (tc_keep_frame ly1 S1 Hp1 W1 m1 md1 m1' fpos HAR Hfin HK HP) as KA.
pose proof HB as (_ & _ & _ & RGP & _).
assert (KG : forall a, tc_glob a -> abyte_kept W1 m1 W1 m1' a) by (intros a Ha; apply KA; right; exact (tc_glob_img RGP a Ha)).
assert (KS : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W1 m1' a)
  by (intros a Ha; apply KG; unfold tc_glob; tauto).
assert (AKS : forall (j : nat) h, (j < 4)%nat -> asrc_at B ly1 S1 W1 m1 (rg_s RG + ASRC * Z.of_nat j) h ->
  asrc_at B ly1 S1 W1 m1' (rg_s RG + ASRC * Z.of_nat j) h).
{ intros j h Hj HS. apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m1' _ _ HS); [|exact (tl_asrc_blks B _ _ _ _ _ _ HS)].
  intros r Hr a Ha. destruct (tl_asrc_fp B _ _ _ _ _ _ HS r Hr a Ha) as [Hg | Hb]; [|exact (KA a (or_introl Hb))].
  apply KS. unfold ASRC in *. lia. }
split.
{ intros G es HR. apply (arelay_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m1' _ _ HR); [|exact (tl_arelay_blks B RG _ _ _ _ _ _ HR)].
  intros r Hr a Ha. destruct (tl_arelay_fp B RG _ _ _ _ _ _ HR r Hr a Ha) as [Hg | Hb]; [|exact (KA a (or_introl Hb))].
  apply KG. unfold tc_glob. tauto. }
split.
{ intros c O mx no cap out HO. apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m1' _ _ _ _ _ _ HO);
    [|exact (tl_aout_blks B RG _ _ _ _ _ _ _ _ _ _ HO)].
  intros r Hr a Ha. destruct (tl_aout_fp B RG _ _ _ _ _ _ _ _ _ _ HO r Hr a Ha) as [Hg | Hb]; [|exact (KA a (or_introl Hb))].
  apply KG. unfold tc_glob. tauto. }
split; [exact AKS|].
split; [|exact KS].
intros e h j (Hj & HS & Hoth & R). split; [exact Hj|]. split; [exact (AKS j h Hj HS)|].
split; [|exact R].
apply (tc_aothers_kept W1 m1 W1 m1' j (re_fd e) j Hoth); [|intros Hc; exfalso; exact (Hc eq_refl)].
intros i' Hi' _ a Ha. apply KS. unfold ASRC in *. lia.
Qed.

Lemma gout_kept : stmt_gout_kept.
Proof.
unfold stmt_gout_kept. intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP HG.
destruct (tc_kept_pack cx ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP) as (KR & KO & KS & KD & KB).
destruct HG as (Hle & Hlq & Hrel & Hrly & Hout & Hsrc & Hdrs & Hgs & Hperm & Hbud).
split; [exact Hle|]. split; [exact Hlq|]. split; [exact Hrel|].
split; [exact (KR _ _ Hrly)|]. split; [exact (KO _ _ _ _ _ _ Hout)|].
split.
{ intros i' Hi' He. unfold gslot. apply KS; [|exact (Hsrc i' Hi' He)].
  apply (tc_slot_lt4 cx i' HB); [lia | exact He]. }
split.
{ eapply Forall_impl; [|exact Hdrs]. intros p Hp He. exact (KD _ _ _ (Hp He)). }
split.
{ intros a Ha Hnj. exact (tl_kept_trans _ W1 W1 _ m1 m1' a (Hgs a Ha Hnj) (KB a Ha)). }
split; [exact Hperm | exact Hbud].
Qed.

Lemma gtopm_kept : stmt_gtopm_kept.
Proof.
unfold stmt_gtopm_kept. intros cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP HG.
destruct (tc_kept_pack cx ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP) as (KR & KO & KS & KD & KB).
unfold GTOPM in HG |- *. cbv zeta in HG |- *.
destruct HG as (Hi & Hlq & Hrel & Hgd & Hrly & Hout & Hsrc & Hopen & Hdrs & Hgs & Hperm).
split; [exact Hi|]. split; [exact Hlq|]. split; [exact Hrel|]. split; [exact Hgd|].
split; [exact (KR _ _ Hrly)|]. split; [exact (KO _ _ _ _ _ _ Hout)|].
split.
{ intros i' Hi' He. unfold gslot. apply KS; [|exact (Hsrc i' Hi' He)].
  apply (tc_slot_lt4 cx i' HB); [lia | exact He]. }
split.
{ intros Ho. unfold gslot. apply KS; [|exact (Hopen Ho)].
  apply (tc_slot_lt4 cx i HB); [exact Hi | exact (proj1 (Z.eqb_eq _ _) Ho)]. }
split.
{ eapply Forall_impl; [|exact Hdrs]. intros p Hp He. exact (KD _ _ _ (Hp He)). }
split.
{ intros a Ha Hnj. exact (tl_kept_trans _ W1 W1 _ m1 m1' a (Hgs a Ha Hnj) (KB a Ha)). }
exact Hperm.
Qed.

Lemma top_rep_closed : stmt_top_rep_closed.
Proof.
unfold stmt_top_rep_closed. intros cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 HB Hi Heof HG.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _).
destruct HG as (Hle & Hlq & Hrel & Hrly & Hout & Hsrc & Hdrs & Hgs & Hperm & Hbud).
assert (Eo : (re_eof (gnth cx i) =? 0) = false) by (apply Z.eqb_neq; exact Heof).
pose proof (tc_skipn_es cx i Hi) as ES.
pose proof (tc_skipn_gps cx i HLEN Hi) as EP.
pose proof (tc_firstn_gps cx i HLEN Hi) as EF.
unfold GTOPM. cbv zeta. rewrite Eo.
split; [exact Hi|]. split; [exact Hlq|]. split; [exact Hrel|].
split; [unfold gdrained; cbv zeta; rewrite Eo; repeat split; reflexivity|].
split; [rewrite <- ES; exact Hrly|].
split; [exact Hout|]. split; [exact Hsrc|].
split; [intros Hc; discriminate Hc|].
split; [rewrite EP in Hdrs; exact (Forall_inv_tail Hdrs)|].
split.
{ intros a Ha Hnj. apply Hgs; [exact Ha|]. intros j Hj. apply Hnj. rewrite EF, tc_rig_slots_app.
  apply in_or_app. left. exact Hj. }
rewrite <- ES. rewrite EP, tc_rig_srcs_cons in Hperm. cbn [fst snd] in Hperm. rewrite Eo in Hperm. exact Hperm.
Qed.

(* ---- the bytes a representation reads lie in its own blocks (W_rig_tail.v tl_*_fp, with the block named) ---- *)
Lemma tc_alist_fp_blk : forall ly S W m LA l lines, alist_at B ly S W m LA l lines ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  (LA <= a < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m LA l lines HL r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; lia|]. right.
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app, tl_recs_len in Ha.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (hl_v l, AREC * hl_cap l). split.
  + unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + cbn [fst snd]. pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as Hrq.
    unfold hl_n, AREC in *. revert Ha Hj Hn Hc Hrq. clear. intros. lia.
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
  rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
  exists (fst q, Z.of_nat (length (snd q)) + 1). split.
  + unfold alist_blks. apply in_or_app. right. apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
  + cbn [fst snd]. pose proof (req_size_pos (Z.of_nat (length (snd q)) + 1) ltac:(lia)). lia.
Qed.
Lemma tc_asrc_fp_blk : forall ly S W m HA h, asrc_at B ly S W m HA h ->
  forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r ->
  (HA <= a < HA + ASRC) \/ exists b, In b (asrc_blks h) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m HA h HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Ha. lia.
- right. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  exists (hs_partial h, APARTIAL). split; [left; reflexivity|]. cbn [fst snd].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (tc_alist_fp_blk ly S W m (HA + 16) _ false Hpend r Hr a Ha) as [H | (b & Hb & Hab)];
      [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
    unfold asrc_blks. right. apply in_or_app. left. exact Hb.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (tc_alist_fp_blk ly S W m (HA + 64) _ true Hexp r Hr a Ha) as [H | (b & Hb & Hab)];
        [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
      unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    * destruct (tc_alist_fp_blk ly S W m (HA + 80) _ true Hheld r Hr a Ha) as [H | (b & Hb & Hab)];
        [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
      unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma tc_aentry_fp_blk : forall ly S W m e, aentry_ok B ly S W m e ->
  forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
  exists b, In b (aentry_blks e) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m e HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (re_buf e, re_cap e). split.
  + unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + cbn [fst snd]. pose proof (req_size_pos (re_cap e) ltac:(lia)). lia.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, tl_key_ptrs_len in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. cbn [length] in Ha. lia.
    * exists (re_hp e, re_kh e). split.
      -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz).
         left. reflexivity.
      -- cbn [fst snd]. pose proof (req_size_pos (re_kh e) ltac:(lia)). unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    exists (key_addr k, Z.of_nat (length (key_text k)) + 1). split.
    * unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    * cbn [fst snd]. pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)). lia.
Qed.

(* ---- block lists: permutations by counting, distinctness by NoDup ---- *)
Definition tc_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma tc_cnt_cons : forall (a x : Z * Z) l,
  count_occ tc_dec (a :: l) x = ((if tc_dec a x then 1 else 0) + count_occ tc_dec l x)%nat.
Proof. intros a x l. cbn [count_occ]. destruct (tc_dec a x); lia. Qed.
Lemma tc_cnt_nil : forall x, count_occ tc_dec [] x = 0%nat.
Proof. reflexivity. Qed.
Ltac tc_perm := apply (proj2 (Permutation_count_occ tc_dec _ _)); intros ?x;
  repeat (rewrite count_occ_app || rewrite tc_cnt_cons || rewrite tc_cnt_nil); lia.
Lemma tc_nodup_disj : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros l1 l2 x HN H1 H2. induction l1 as [|a l1 IH]; [destruct H1|].
inversion HN as [|a' l' Hna HN']; subst. destruct H1 as [-> | H1].
- apply Hna. apply in_or_app. right. exact H2.
- exact (IH HN' H1).
Qed.
Lemma tc_skipn_combine : forall {X Y : Type} (l1 : list X) (l2 : list Y) n,
  skipn n (combine l1 l2) = combine (skipn n l1) (skipn n l2).
Proof.
intros X Y l1. induction l1 as [|x l1 IH]; intros l2 n; destruct n as [|n]; try reflexivity.
destruct l2 as [|y l2]; cbn [combine skipn].
- destruct (skipn n l1); reflexivity.
- apply IH.
Qed.
Lemma tc_srcs_in : forall p l b, In p l -> re_eof (fst p) = 0 -> In b (asrc_blks (fst (snd p))) -> In b (rig_srcs l).
Proof.
intros p l b Hp He Hb. unfold rig_srcs. apply in_concat. exists (asrc_blks (fst (snd p))). split; [|exact Hb].
apply in_map_iff. exists p. rewrite (proj2 (Z.eqb_eq _ _) He). split; [reflexivity | exact Hp].
Qed.
Lemma tc_slots_in : forall p l, In p l -> re_eof (fst p) = 0 -> In (snd (snd p)) (rig_slots l).
Proof.
intros p l Hp He. unfold rig_slots. apply in_concat. exists [snd (snd p)]. split; [|left; reflexivity].
apply in_map_iff. exists p. rewrite (proj2 (Z.eqb_eq _ _) He). split; [reflexivity | exact Hp].
Qed.
Lemma tc_rig_slots_cons : forall p l,
  rig_slots (p :: l) = (if re_eof (fst p) =? 0 then [snd (snd p)] else []) ++ rig_slots l.
Proof. intros p l. reflexivity. Qed.
Lemma tc_in_firstn_gps : forall cx i i', length (gxhs cx) = length (gxes cx) -> (i' < i)%nat -> (i <= length (gxes cx))%nat ->
  In (gnth cx i', ghj cx i') (firstn i (gps cx)).
Proof.
intros cx i i' HL Hi' Hi.
assert (H : In (nth i' (firstn i (gps cx)) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj)) (firstn i (gps cx)))
  by (apply nth_In; rewrite length_firstn, tc_len_gps by exact HL; lia).
rewrite nth_firstn in H. destruct (Nat.ltb_spec i' i) as [_|Hc]; [|lia]. rewrite tc_gps_nth in H by exact HL. exact H.
Qed.
Lemma tc_done_blks : forall cx qd i i' b, length (gxhs cx) = length (gxes cx) -> length qd = i ->
  (i <= length (gxes cx))%nat -> (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  In b (asrc_blks (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  In b (gdone_srcs (firstn i (gps cx)) qd).
Proof.
intros cx qd i i' b HL Hlq Hle Hi' He Hb. unfold gdone_srcs. apply in_concat.
eexists. split; [|exact Hb]. apply in_map_iff.
exists (nth i' (combine (firstn i (gps cx)) qd)
  ((relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj), (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
split; [|apply nth_In; rewrite length_combine, length_firstn, tc_len_gps by exact HL; lia].
rewrite combine_nth by (rewrite length_firstn, tc_len_gps by exact HL; lia).
rewrite nth_firstn. destruct (Nat.ltb_spec i' i) as [_|Hc]; [|lia]. rewrite tc_gps_nth by exact HL.
cbn [fst snd]. rewrite (proj2 (Z.eqb_eq _ _) He). reflexivity.
Qed.

(* ---- the relay's three cells are none of the bytes drain may change ---- *)
Lemma tc_zall_nth : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; [cbn in Hj; lia|].
destruct H as [Hb Hl]. destruct j as [|j]; [exact Hb|]. apply IH; [exact Hl | cbn in Hj; lia].
Qed.
Lemma tc_zpw_nth : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
  zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; [cbn in Hj; lia|]. destruct H as [Ha Hl].
destruct i as [|i]; destruct j as [|j]; try lia.
- cbn [nth]. apply tc_zall_nth; [exact Ha | cbn in Hj; lia].
- cbn [nth]. apply IH; [exact Hl | lia | cbn in Hj; lia].
Qed.
Ltac tc_dj i j :=
  let D := fresh "D" in
  pose proof (tc_zpw_nth _ i j (0, 0) HRGP ltac:(lia) ltac:(cbn [length]; lia)) as D;
  unfold zdisj in D; cbn [nth fst snd] in D.
Ltac tc_lia_one := match goal with
  | [ Hg : _ <= ?a < _, Ha : _ <= ?a < _, D : _ \/ _ |- False ] => clear - Hg Ha D; lia
  end.
Lemma tc_rel_glob : rg_place B RG -> forall a,
  (rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG (G_DR B RG) a.
Proof.
intros RGP a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _). unfold rg_rng in RGIMG.
destruct Ha as [Ha | [Ha | Ha]].
- destruct (RGIMG a ltac:(tauto)) as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  tc_dj 1%nat 2%nat. tc_dj 2%nat 6%nat. tc_dj 2%nat 7%nat. tc_dj 2%nat 8%nat. tc_dj 2%nat 10%nat. tc_dj 2%nat 12%nat.
  tc_dj 2%nat 14%nat.
  intros Hg. unfold inG, G_DR, G_SL in Hg.
  repeat (apply Exists_cons in Hg; destruct Hg as [Hg | Hg]; [unfold in_zr in Hg; cbn [fst snd] in Hg; tc_lia_one | ]).
  apply Exists_nil in Hg. exact Hg.
- destruct (RGIMG a ltac:(tauto)) as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  tc_dj 1%nat 3%nat. tc_dj 3%nat 6%nat. tc_dj 3%nat 7%nat. tc_dj 3%nat 8%nat. tc_dj 3%nat 10%nat. tc_dj 3%nat 12%nat.
  tc_dj 3%nat 14%nat.
  intros Hg. unfold inG, G_DR, G_SL in Hg.
  repeat (apply Exists_cons in Hg; destruct Hg as [Hg | Hg]; [unfold in_zr in Hg; cbn [fst snd] in Hg; tc_lia_one | ]).
  apply Exists_nil in Hg. exact Hg.
- destruct (HRGI a ltac:(tauto)) as (I1 & I2). split; [exact I1|]. split; [exact I2|].
  tc_dj 1%nat 4%nat. tc_dj 4%nat 6%nat. tc_dj 4%nat 7%nat. tc_dj 4%nat 8%nat. tc_dj 4%nat 10%nat. tc_dj 4%nat 12%nat.
  tc_dj 4%nat 14%nat.
  split; [intros He; tc_lia_one|].
  intros Hg. unfold inG, G_DR, G_SL in Hg.
  repeat (apply Exists_cons in Hg; destruct Hg as [Hg | Hg]; [unfold in_zr in Hg; cbn [fst snd] in Hg; tc_lia_one | ]).
  apply Exists_nil in Hg. exact Hg.
Qed.

Lemma tc_aout_no : forall ly S W m c O mx no cap out, aout_at B RG ly S W m c O mx no cap out ->
  aout_at B RG ly S W m c O mx (Z.of_nat (length O)) cap out.
Proof.
intros ly S W m c O mx no cap out H.
pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hno & _).
rewrite Hno. exact H.
Qed.

(* ---- entry i's drain step, open entry: GOUT i, drain's journal and DRK give GTOPM at drain's final state ---- *)
Section tc_open.
Variables (cx : gcx) (i : nat) (qd : list (rentry * hsrc)) (c2 : ctl) (O2 : list byte) (cap2 out2 spent : Z)
  (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (sp1 : Z)
  (ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS) (m2 : word -> option byte) (md2 : Model) (k2 : Z)
  (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) (rest : list (Z * Z)).
Local Notation oE := (gnth cx i).
Local Notation oH := (fst (ghj cx i)).
Local Notation oJ := (snd (ghj cx i)).
Local Notation oSA := (gSA cx i).
Local Notation ocap := (if dr_live c2 (fst (ghj cx i))
  then drain_b_c.ds_ocap (dr_fin c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i))) else cap2).
Local Notation oA := (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2).
Local Notation oXt := (concat (map aentry_blks (map fst qd)) ++ concat (map aentry_blks (skipn (S i) (gxes cx))) ++
  gdone_srcs (firstn i (gps cx)) qd ++ rig_srcs (skipn (S i) (gps cx)) ++ gxrest cx).
Local Notation oX := ((gxG0 cx, ATABLE) :: oXt).
Hypothesis HB : GBASE B ARx MT RP MMAX RG cx.
Hypothesis Hi : (i < length (gxes cx))%nat.
Hypothesis Heof : re_eof (gnth cx i) = 0.
Hypothesis HG : GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
Hypothesis HAR1 : ARx ly1 S1 Hp1 W1 m1 md1.
Hypothesis HJ : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x sp1
  (dr_fp (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2) ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2.
Hypothesis D1 : apres_kept B W1 m1 W2 m2.
Hypothesis D3 : Permutation (ablocks B ly1 S1) (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2 ++ rest).
Hypothesis D4 : Permutation (ablocks B ly2 S2) (aentry_blks e' ++ asrc_blks h' ++ aout_blks ocap out' ++ rest).
Hypothesis D5 : garr8 SEGS (arm W2 m2) (gSA cx i) (bzs (entry_bytes e')).
Hypothesis D6 : aentry_ok B ly2 S2 W2 m2 e'.
Hypothesis D7 : dr_rel c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i)) e' h' LB.
Hypothesis D8 : asrc_at B ly2 S2 W2 m2 (gslot RG cx i) h'.
Hypothesis D9 : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (gslot RG cx i <= a < gslot RG cx i + ASRC) ->
  abyte_kept W1 m1 W2 m2 a.
Hypothesis D10 : aout_at B RG ly2 S2 W2 m2 (dr_ctl c2 (fst (ghj cx i)) ev')
  (if dr_live c2 (fst (ghj cx i)) then O2 ++ LB else O2) (gxmx cx)
  (if dr_live c2 (fst (ghj cx i)) then Z.of_nat (length O2) + dr_tot (fst (ghj cx i)) else Z.of_nat (length O2)) ocap out'.

Lemma tc_o_eo : (re_eof (gnth cx i) =? 0) = true.
Proof. apply Z.eqb_eq. exact Heof. Qed.
Lemma tc_o_len : length (gxhs cx) = length (gxes cx).
Proof. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _). exact HLEN. Qed.
Lemma tc_o_fd : re_fd e' = re_fd (gnth cx i) /\ hs_fd h' = hs_fd (fst (ghj cx i)).
Proof.
pose proof D7 as D. unfold dr_rel in D. cbv zeta in D.
destruct D as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F13 & _). exact (conj F1 F13).
Qed.
Lemma tc_o_AR2 : ARx ly2 S2 Hp2 W2 m2 md2.
Proof. exact (tj_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). Qed.

Lemma tc_o_P1 : Permutation (ablocks B ly1 S1) (oA ++ oX).
Proof.
destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & Hperm & _).
rewrite (tc_skipn_es cx i Hi), (tc_skipn_gps cx i tc_o_len Hi), tc_rig_srcs_cons in Hperm.
cbn [fst snd] in Hperm. rewrite tc_o_eo in Hperm. cbv beta iota in Hperm.
eapply Permutation_trans; [exact Hperm|].
rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.
Lemma tc_o_P2 : Permutation (ablocks B ly1 S1) (oA ++ rest).
Proof. rewrite <- !app_assoc. exact D3. Qed.
Lemma tc_o_PX : Permutation oX rest.
Proof. apply (Permutation_app_inv_l oA). exact (Permutation_trans (Permutation_sym tc_o_P1) tc_o_P2). Qed.
Lemma tc_o_ND : List.NoDup (oA ++ oX).
Proof. exact (Permutation_NoDup tc_o_P1 (tj_nodup _ _ _ _ _ _ HAR1)). Qed.
Lemma tc_o_inX : forall b, In b oX -> In b (ablocks B ly1 S1) /\ In b (ablocks B ly2 S2) /\ ~ In b oA.
Proof.
intros b Hb. split; [apply (Permutation_in _ (Permutation_sym tc_o_P1)); apply in_or_app; right; exact Hb|].
split.
- apply (Permutation_in _ (Permutation_sym D4)). apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
  exact (Permutation_in _ tc_o_PX Hb).
- intros HA. exact (tc_nodup_disj _ _ b tc_o_ND HA Hb).
Qed.
Lemma tc_o_inA : forall c, In c oA -> In c (ablocks B ly1 S1).
Proof. intros c Hc. apply (Permutation_in _ (Permutation_sym tc_o_P1)). apply in_or_app. left. exact Hc. Qed.
Lemma tc_o_table : In (gxG0 cx, ATABLE) (ablocks B ly1 S1) /\ gxG0 cx <= oSA /\ oSA + AENT <= gxG0 cx + ATABLE.
Proof.
destruct HG as (_ & Hlq & _ & Hrly & _). pose proof Hrly as (_ & _ & _ & _ & _ & _ & Hl16 & HGin & _).
split; [exact HGin|].
rewrite length_app, length_map, length_skipn, Hlq in Hl16. unfold gSA, AENT, ATABLE. lia.
Qed.

(* every byte of a block of oX outside the entry's 56 bytes is kept *)
Lemma tc_o_KB : forall b a, In b oX -> fst b <= a < fst b + req_size (snd b) -> ~ (oSA <= a < oSA + AENT) ->
  abyte_kept W1 m1 W2 m2 a.
Proof.
intros [p n] a Hb Ha Hsa. destruct (tc_o_inX _ Hb) as (H1 & H2 & HnA). cbn [fst snd] in Ha.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n tc_o_AR2 H2) as (_ & Hp4 & Hpc & _ & Hpo & _).
pose proof asan_consts as (C1 & _).
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
split.
- replace a with (p + (a - p)) by lia. rewrite (F2 p n (a - p) H1 H2 ltac:(lia)).
  + replace (p + (a - p)) with a by lia. apply Hag. rewrite unsigned_lit_small by lia. intros HGa.
    assert (Hgr : inG (G_RIG B RG) a) by (unfold G_RIG, inG; apply Exists_cons_tl; exact HGa).
    refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a tc_o_AR2 _) (proj1 (HGRIG a Hgr))).
    left. exists p, n. split; [exact H2 | lia].
  + replace (p + (a - p)) with a by lia. intros (r & Hr & Hra). unfold dr_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | Hr]; [cbn [fst snd] in Hra; lia|].
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hc). cbn [fst snd] in Hra.
    assert (Hne : (p, n) <> (q, m)) by (intros Heq; rewrite Heq in HnA; exact (HnA Hc)).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ p n q m HAR1 H1 (tc_o_inA _ Hc) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- intros _. apply apresent_writable. exact (proj1 (Hpo a ltac:(lia))).
Qed.
(* a block of oX other than the table is apart from the entry's 56 bytes *)
Lemma tc_o_KBt : forall b a, In b oXt -> fst b <= a < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros b a Hb Ha. apply (tc_o_KB b a (or_intror Hb) Ha).
destruct tc_o_table as (HT & HS1 & HS2).
assert (HbX : In b oX) by (right; exact Hb).
pose proof (proj1 (tc_o_inX b HbX)) as Hb1.
assert (Hne : b <> (gxG0 cx, ATABLE)).
{ intros ->. pose proof (NoDup_app_remove_l _ _ tc_o_ND) as HN. inversion HN as [|x l Hx _]; subst. exact (Hx Hb). }
destruct b as [p n].
pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ p n (gxG0 cx) ATABLE HAR1 Hb1 HT Hne) as Hd.
pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
unfold zdisjoint in Hd. cbn [fst snd] in Hd, Ha. lia.
Qed.
Lemma tc_o_fp_spares : forall a, fp_spares (dr_fp oSA oE oH cap2 out2) a.
Proof.
intros a Ho. exfalso. destruct Ho as (r & Hr & H0). unfold dr_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in H0. destruct tc_o_table as (HT & HS1 & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 HT) as (_ & Hp4 & _). lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hc). cbn [fst snd] in H0.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ q m HAR1 (tc_o_inA _ Hc)) as (_ & Hp4 & _). lia.
Qed.
(* an image byte drain may not change, and off the program statics, is kept *)
Lemma tc_o_KG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros a Hi' Ho He Hps Hg. split.
- exact (gse_keep_img_x B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Hi' Ho He Hps (tc_o_fp_spares a) Hg).
- destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
  pose proof HJi as (_ & _ & _ & Hwle & _).
  apply (tc_wr_kept W1 W2 m1 m2 a Hwle). exact (D1 a Hi' Ho He).
Qed.

(* the slots: entry i's slot is none of the other open entries' *)
Lemma tc_o_slots : forall j, In j (rig_slots (firstn i (gps cx))) \/ In j (rig_slots (skipn (S i) (gps cx))) -> j <> oJ.
Proof.
intros j Hj ->. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HND & _).
rewrite <- (firstn_skipn i (gps cx)), tc_rig_slots_app, (tc_skipn_gps cx i tc_o_len Hi), tc_rig_slots_cons in HND.
cbn [fst snd] in HND. rewrite tc_o_eo in HND. cbv beta iota in HND. cbn [app] in HND.
apply NoDup_ListNoDup in HND. apply (NoDup_remove_2 _ _ _ HND). apply in_or_app. exact Hj.
Qed.
Lemma tc_o_slot_lt4 : (oJ < 4)%nat.
Proof. exact (tc_slot_lt4 cx i HB Hi Heof). Qed.

(* ---- the conjuncts of GTOPM ---- *)
Lemma tc_o_arelay : arelay_at B RG ly2 S2 W2 m2 (gxG0 cx) (map fst qd ++ e' :: skipn (S i) (gxes cx)).
Proof.
pose proof HB as (_ & _ & _ & RGP & _).
destruct HG as (Hle & Hlq & _ & Hrly & _).
rewrite (tc_skipn_es cx i Hi) in Hrly.
destruct Hrly as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
assert (KR : forall a, (rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4) -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. destruct (tc_rel_glob RGP a Ha) as (K1 & K2 & K3 & K4).
  exact (tc_o_KG a K1 K2 K3 (PSTG a ltac:(tauto)) K4). }
assert (EL : length (map fst qd ++ e' :: skipn (S i) (gxes cx)) = length (map fst qd ++ gnth cx i :: skipn (S i) (gxes cx)))
  by (rewrite !length_app; reflexivity).
destruct tc_o_table as (HT & HS1 & HS2).
split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; left; cbn in Hx; lia | exact R1]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; left; lia | exact R2]|].
split; [rewrite EL; apply (akept_vm W1 m1); [intros x Hx; apply KR; right; left; cbn in Hx; lia | exact R3]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; right; left; lia | exact R4]|].
split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; right; right; cbn in Hx; lia | exact R5]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; right; right; lia | exact R6]|].
split; [rewrite EL; exact R7|].
split; [exact (proj1 (proj2 (tc_o_inX _ (or_introl eq_refl))))|].
assert (L56 : forall x, aentry_ok B ly1 S1 W1 m1 x -> length (entry_bytes x) = 56%nat)
  by (intros x (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len x P1 P2)).
assert (LE' : length (entry_bytes e') = 56%nat)
  by (destruct D6 as (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len e' P1 P2)).
rewrite Forall_forall in R10.
assert (LE : length (entry_bytes (gnth cx i)) = 56%nat) by (apply L56, R10, in_or_app; right; left; reflexivity).
assert (LP : length (concat (map entry_bytes (map fst qd))) = (56 * i)%nat).
{ rewrite relay_instance_gone_b_lem.rigl_concat_len; [rewrite length_map, Hlq; lia|].
  apply Forall_forall. intros x Hx. apply L56, R10, in_or_app. left. exact Hx. }
split.
{ destruct R9 as (T & T1 & T2 & T3). exists T.
  split; [rewrite EL; exact T1|].
  rewrite map_app, concat_app in T2, T3 |- *. cbn [map concat] in T2, T3 |- *.
  rewrite !length_app, LE, LP in T2.
  split; [rewrite !length_app, LE', LP; exact T2|].
  unfold bzs in T3 |- *. rewrite !map_app in T3 |- *. rewrite <- !app_assoc in T3 |- *.
  apply garr8_app in T3 as (T3a & T3b). apply garr8_app in T3b as (T3b & T3c).
  rewrite !length_map, LP in T3b. rewrite !length_map, LP, LE in T3c.
  apply garr8_app. rewrite !length_map, LP. split.
  - apply (akept_garr8 W1 m1); [|exact T3a]. intros x Hx. rewrite length_map, LP in Hx.
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
    apply (tc_o_KB (gxG0 cx, ATABLE) x (or_introl eq_refl)); cbn [fst snd]; unfold gSA, AENT, ATABLE in *; lia.
  - apply garr8_app. rewrite !length_map, LE'. split.
    + replace (gxG0 cx + Z.of_nat (56 * i)) with (gSA cx i) by (unfold gSA, AENT; lia). exact D5.
    + apply (akept_garr8 W1 m1); [|exact T3c]. intros x Hx. rewrite length_app, !length_map in Hx.
      pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
      apply (tc_o_KB (gxG0 cx, ATABLE) x (or_introl eq_refl)); cbn [fst snd]; unfold gSA, AENT, ATABLE in *; lia. }
split.
{ apply Forall_forall. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | [<- | Hx]].
  - assert (Hok : aentry_ok B ly1 S1 W1 m1 x) by (apply R10, in_or_app; left; exact Hx).
    assert (Hbl : forall b, In b (aentry_blks x) -> In b oXt).
    { intros b Hb. apply in_or_app. left. apply in_concat. exists (aentry_blks x). split; [apply in_map; exact Hx | exact Hb]. }
    apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 x Hok).
    + intros r Hr a Ha. destruct (tc_aentry_fp_blk _ _ _ _ x Hok r Hr a Ha) as (b & Hb & Hab).
      exact (tc_o_KBt b a (Hbl b Hb) Hab).
    + intros b Hb. exact (proj1 (proj2 (tc_o_inX b (or_intror (Hbl b Hb))))).
  - exact D6.
  - assert (Hok : aentry_ok B ly1 S1 W1 m1 x) by (apply R10, in_or_app; right; right; exact Hx).
    assert (Hbl : forall b, In b (aentry_blks x) -> In b oXt).
    { intros b Hb. apply in_or_app. right. apply in_or_app. left. apply in_concat. exists (aentry_blks x).
      split; [apply in_map; exact Hx | exact Hb]. }
    apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 x Hok).
    + intros r Hr a Ha. destruct (tc_aentry_fp_blk _ _ _ _ x Hok r Hr a Ha) as (b & Hb & Hab).
      exact (tc_o_KBt b a (Hbl b Hb) Hab).
    + intros b Hb. exact (proj1 (proj2 (tc_o_inX b (or_intror (Hbl b Hb))))). }
(* arelay_at's last conjunct (W8's W_rep): the fds as before (drain keeps re_fd); no block of the drained entry e' is
   the table, because the table is in rest (tc_o_PX) and drain's post lists e''s blocks beside rest without repetition
   (D4, AR's NoDup of the live blocks) *)
destruct R11 as [R11 R12]. split.
{ rewrite !map_app in R11 |- *. cbn [map] in R11 |- *. rewrite (proj1 tc_o_fd). exact R11. }
apply Forall_app in R12 as [G1 G2]. apply Forall_cons_iff in G2 as [_ G4].
apply Forall_app. split; [exact G1|]. apply Forall_cons; [|exact G4].
intros b Hb Eb. subst b.
pose proof (Permutation_NoDup D4 (tj_nodup _ _ _ _ _ _ tc_o_AR2)) as ND2.
apply (tc_nodup_disj _ _ (gxG0 cx, ATABLE) ND2 Hb).
apply in_or_app. right. apply in_or_app. right. exact (Permutation_in _ tc_o_PX (in_eq _ _)).
Qed.

Lemma tc_o_done : forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  asrc_at B ly2 S2 W2 m2 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
Proof.
intros i' Hi' He. destruct HG as (Hle & Hlq & _ & _ & _ & Hsrc & _).
pose proof (Hsrc i' Hi' He) as HS.
assert (Hj4 : (snd (ghj cx i') < 4)%nat) by (apply (tc_slot_lt4 cx i' HB); [lia | exact He]).
assert (Hji : snd (ghj cx i') <> oJ).
{ apply tc_o_slots. left. apply (tc_slots_in (gnth cx i', ghj cx i')); [|exact He].
  apply tc_in_firstn_gps; [exact tc_o_len | exact Hi' | lia]. }
assert (Hji' : Z.of_nat (snd (ghj cx i')) <> Z.of_nat oJ) by lia.
pose proof tc_o_slot_lt4 as HJ4.
unfold gslot in *.
apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HS).
- intros r Hr a Ha. destruct (tc_asrc_fp_blk _ _ _ _ _ _ HS r Hr a Ha) as [Hsl | (b & Hb & Hab)].
  + apply D9; unfold ASRC in *; lia.
  + apply (tc_o_KBt b a); [|exact Hab]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact (tc_done_blks cx qd i i' b tc_o_len Hlq ltac:(lia) Hi' He Hb).
- intros b Hb. assert (HbX : In b oX).
  { right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact (tc_done_blks cx qd i i' b tc_o_len Hlq ltac:(lia) Hi' He Hb). }
  exact (proj1 (proj2 (tc_o_inX b HbX))).
Qed.

Lemma tc_o_later : Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly2 S2 W2 m2 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)).
Proof.
destruct HG as (_ & _ & _ & Hrly & _ & _ & Hdrs & _).
rewrite (tc_skipn_gps cx i tc_o_len Hi) in Hdrs.
pose proof (Forall_inv Hdrs) as Hd0. cbn [fst snd] in Hd0. destruct (Hd0 Heof) as (_ & _ & _ & Hfd0 & _).
apply Forall_inv_tail in Hdrs.
rewrite (tc_skipn_es cx i Hi) in Hrly. pose proof Hrly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rok & (R11 & _)).
rewrite map_app in R11. cbn [map] in R11. apply NoDup_ListNoDup in R11. apply NoDup_remove_2 in R11.
pose proof tc_o_slot_lt4 as HJ4.
rewrite Forall_forall in Hdrs |- *. intros [ep [hp jp]] Hp He. cbn [fst snd] in He |- *.
destruct (Hdrs _ Hp He) as (Hj & HS & Hoth & R). cbn [fst snd] in Hj, HS, Hoth, R.
assert (Hji : jp <> oJ) by (apply tc_o_slots; right; exact (tc_slots_in (ep, (hp, jp)) _ Hp He)).
assert (Hji' : Z.of_nat jp <> Z.of_nat oJ) by lia.
assert (Hfd : re_fd ep <> re_fd (gnth cx i)).
{ intros Heq. apply R11. apply in_or_app. right. rewrite <- Heq. apply in_map.
  unfold gps in Hp. rewrite tc_skipn_combine in Hp. exact (in_combine_l _ _ _ _ Hp). }
(* aothers_at compares fds mod 2^32 (W7's s7): both fds lie in [0, 2^31) by aentry_ok (BRigTop's B fix, ported) *)
assert (HepIn : In ep (skipn (S i) (gxes cx))).
{ pose proof Hp as Hp'. unfold gps in Hp'. rewrite tc_skipn_combine in Hp'. exact (in_combine_l _ _ _ _ Hp'). }
assert (Hfdb : 0 <= re_fd ep < 2 ^ 31 /\ 0 <= re_fd (gnth cx i) < 2 ^ 31).
{ rewrite Forall_forall in Rok. split.
  - destruct (Rok ep ltac:(apply in_or_app; right; right; exact HepIn)) as (_ & _ & _ & _ & Hb & _). exact Hb.
  - destruct (Rok (gnth cx i) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & Hb & _). exact Hb. }
assert (Hbl : forall b, In b (asrc_blks hp) -> In b oXt).
{ intros b Hb. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  exact (tc_srcs_in (ep, (hp, jp)) _ b Hp He Hb). }
split; [exact Hj|]. split.
- apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HS).
  + intros r Hr a Ha. destruct (tc_asrc_fp_blk _ _ _ _ _ _ HS r Hr a Ha) as [Hsl | (b & Hb & Hab)].
    * apply D9; [unfold ASRC in Hsl |- *; lia | unfold gslot, ASRC in Hsl |- *; lia].
    * exact (tc_o_KBt b a (Hbl b Hb) Hab).
  + intros b Hb. exact (proj1 (proj2 (tc_o_inX b (or_intror (Hbl b Hb))))).
- split; [|exact R].
  apply (tc_aothers_kept W1 m1 W2 m2 jp (re_fd ep) oJ Hoth).
  + intros i'' Hi'' Hne a Ha. assert (Z.of_nat i'' <> Z.of_nat oJ) by lia.
    apply D9; [unfold ASRC in Ha |- *; lia | unfold gslot, ASRC in Ha |- *; lia].
  + intros _. exists (hs_fd h'), (hs_open h').
    pose proof D8 as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & _). unfold gslot in V1, V2.
    split; [exact V1|]. split; [exact V2|]. right. rewrite (proj2 tc_o_fd), Hfd0, !(Z.mod_small _ (2 ^ 32)) by lia.
    intros Heq. exact (Hfd (eq_sym Heq)).
Qed.

Lemma tc_o_gtopm : GTOPM cx i qd c2 O2 cap2 e' h' ev' LB (dr_ctl c2 (fst (ghj cx i)) ev')
  (if dr_live c2 (fst (ghj cx i)) then O2 ++ LB else O2) ocap out' ly2 S2 W2 m2.
Proof.
pose proof HG as (Hle & Hlq & Hrel & _ & _ & _ & _ & Hgs & _).
unfold GTOPM. cbv zeta. rewrite tc_o_eo. cbv beta iota.
split; [exact Hi|]. split; [exact Hlq|]. split; [exact Hrel|].
split; [unfold gdrained; cbv zeta; rewrite tc_o_eo; cbv beta iota; cbn [andb];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity | exact D7]|].
split; [exact tc_o_arelay|].
split; [exact (tc_aout_no _ _ _ _ _ _ _ _ _ _ D10)|].
split; [exact tc_o_done|].
split; [intros _; exact D8|].
split; [exact tc_o_later|].
split.
{ intros a Ha Hnj. apply (tl_kept_trans (gxW cx) W1 W2 (gxmem cx) m1 m2 a).
  - apply Hgs; [exact Ha|]. intros j Hj. apply Hnj. rewrite (tc_firstn_gps cx i tc_o_len Hi), tc_rig_slots_app.
    apply in_or_app. left. exact Hj.
  - apply D9; [exact Ha|]. unfold gslot. apply Hnj. rewrite (tc_firstn_gps cx i tc_o_len Hi), tc_rig_slots_app.
    apply in_or_app. right. rewrite tc_rig_slots_cons. cbn [fst snd]. rewrite tc_o_eo. left. reflexivity. }
eapply Permutation_trans; [exact D4|].
eapply Permutation_trans.
{ apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head. exact (Permutation_sym tc_o_PX). }
rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.
End tc_open.

Lemma top_rep_open : stmt_top_rep_open.
Proof.
unfold stmt_top_rep_open. cbv zeta.
intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 sp1 ly2 S2 Hp2 W2 m2 md2 k2 HB Hi Heof HG HAR1 HJ Hsp HD.
unfold DRK in HD. cbv zeta in HD.
destruct HD as (e' & h' & out' & ev' & LB & rest & D1 & _ & D3 & D4 & D5 & _ & D6 & D7 & D8 & D9 & D10).
exists e', h', ev', LB, out'.
eapply tc_o_gtopm; eassumption.
Qed.

(* ---- TOP's drain call: drain's memory premises and footprint ---- *)
Lemma tc_nodup_app_r : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. intros l1 l2 H. induction l1 as [|a l1 IH]; [exact H|]. inversion H; subst. apply IH. assumption. Qed.

Lemma top_drain_pre : stmt_top_drain_pre.
Proof.
unfold stmt_top_drain_pre. cbv zeta. intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 HB Hi Heof HG HAR1.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _).
destruct HG as (Hle & Hlq & _ & Hrly & _ & _ & Hdrs & _ & Hperm & _).
pose proof Hrly as (_ & _ & _ & _ & _ & _ & Hl16 & HGin & _).
rewrite length_app, length_map, length_skipn, Hlq in Hl16.
assert (HSA : gxG0 cx <= gSA cx i /\ gSA cx i + AENT <= gxG0 cx + ATABLE) by (unfold gSA, AENT, ATABLE; lia).
rewrite (tc_skipn_es cx i Hi) in Hrly.
destruct Hrly as (_ & _ & _ & _ & _ & _ & _ & _ & R9 & R10 & _).
rewrite Forall_forall in R10.
assert (L56 : forall x, aentry_ok B ly1 S1 W1 m1 x -> length (entry_bytes x) = 56%nat)
  by (intros x (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len x P1 P2)).
assert (Hok : aentry_ok B ly1 S1 W1 m1 (gnth cx i)) by (apply R10, in_or_app; right; left; reflexivity).
split; [exact HGin|]. split; [exact (proj1 HSA)|]. split; [exact (proj2 HSA)|].
split.
{ destruct R9 as (T & _ & _ & T3).
  assert (LP : length (concat (map entry_bytes (map fst qd))) = (56 * i)%nat).
  { rewrite relay_instance_gone_b_lem.rigl_concat_len; [rewrite length_map, Hlq; lia|].
    apply Forall_forall. intros x Hx. apply L56, R10, in_or_app. left. exact Hx. }
  rewrite map_app, concat_app in T3. cbn [map concat] in T3.
  unfold bzs in T3 |- *. rewrite !map_app in T3. rewrite <- !app_assoc in T3.
  apply garr8_app in T3 as (_ & T3b). apply garr8_app in T3b as (T3b & _).
  rewrite length_map, LP in T3b.
  replace (gSA cx i) with (gxG0 cx + Z.of_nat (56 * i)) by (unfold gSA, AENT; lia). exact T3b. }
split.
{ intros k Hk. apply apresent_writable.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 HGin) as (_ & _ & _ & _ & Hpo & _).
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)).
  exact (proj1 (Hpo (gSA cx i + k) ltac:(unfold AENT, ATABLE in *; lia))). }
split; [exact Hok|].
split.
{ rewrite (tc_skipn_gps cx i HLEN Hi) in Hdrs. pose proof (Forall_inv Hdrs) as Hd0. cbn [fst snd] in Hd0. exact (Hd0 Heof). }
exists (concat (map aentry_blks (map fst qd)) ++ concat (map aentry_blks (skipn (S i) (gxes cx))) ++
  gdone_srcs (firstn i (gps cx)) qd ++ rig_srcs (skipn (S i) (gps cx)) ++ gxrest cx).
rewrite (tc_skipn_es cx i Hi), (tc_skipn_gps cx i HLEN Hi), tc_rig_srcs_cons in Hperm. cbn [fst snd] in Hperm.
rewrite (proj2 (Z.eqb_eq _ _) Heof) in Hperm. cbv beta iota in Hperm.
eapply Permutation_trans; [exact Hperm|]. rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.

Lemma dr_fp_in : stmt_dr_fp_in.
Proof.
unfold stmt_dr_fp_in. cbv zeta. intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 HB Hi Heof HG HAR1 a Ha.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _ & _ & HPERM0 & _).
destruct HG as (Hle & Hlq & _ & Hrly & _ & _ & _ & _ & Hperm & _).
pose proof Hrly as (_ & _ & _ & _ & _ & _ & Hl16 & HGin & _).
rewrite length_app, length_map, length_skipn, Hlq in Hl16.
rewrite (tc_skipn_es cx i Hi), (tc_skipn_gps cx i HLEN Hi), tc_rig_srcs_cons in Hperm. cbn [fst snd] in Hperm.
rewrite (proj2 (Z.eqb_eq _ _) Heof) in Hperm. cbv beta iota in Hperm.
assert (HL1 : forall c, In c (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2) ->
  In c (ablocks B ly1 S1)).
{ intros c Hc. apply (Permutation_in _ (Permutation_sym Hperm)). right.
  rewrite map_app, concat_app. cbn [map concat].
  apply in_app_or in Hc. destruct Hc as [Hc | Hc].
  - apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hc.
  - apply in_or_app. right. apply in_or_app. right. apply in_app_or in Hc. destruct Hc as [Hc | Hc].
    + apply in_or_app. left. apply in_or_app. left. exact Hc.
    + apply in_or_app. right. apply in_or_app. left. exact Hc. }
assert (GF : forall b, In b ((gxG0 cx, ATABLE) :: concat (map aentry_blks (gxes cx)) ++ rig_srcs (gps cx) ++
    aout_blks (gxcap cx) (gxout cx)) -> In b (ablocks B ly1 S1) -> fst b <= a < fst b + req_size (snd b) ->
  (inFP (gFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (gxly cx) (gxS cx)) (ablocks B ly1 S1) a).
{ intros [p n] Hb H1 Hpa. cbn [fst snd] in Hpa. left. split; [|exists p, n; split; [exact H1 | exact Hpa]].
  exists (p, p + req_size n). split; [|exact Hpa]. unfold gFP, rig_fp, ablocks_fp.
  exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n) Hb). }
destruct Ha as (r & Hr & Hra). unfold dr_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Hra. apply (GF (gxG0 cx, ATABLE)); [left; reflexivity | exact HGin|].
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)). cbn [fst snd]. unfold gSA, AENT, ATABLE in *. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as (c & <- & Hc). cbn [fst snd] in Hra.
  pose proof (HL1 c Hc) as Hc1.
  apply in_app_or in Hc. destruct Hc as [Hc | Hc].
  + apply (GF c); [|exact Hc1 | exact Hra]. right. apply in_or_app. left. apply in_concat. exists (aentry_blks (gnth cx i)).
    split; [apply in_map; unfold gnth; apply nth_In; exact Hi | exact Hc].
  + apply in_app_or in Hc. destruct Hc as [Hc | Hc].
    * apply (GF c); [|exact Hc1 | exact Hra]. right. apply in_or_app. right. apply in_or_app. left.
      apply (tc_srcs_in (gnth cx i, ghj cx i)); [|exact Heof | exact Hc].
      rewrite <- (tc_gps_nth cx i HLEN). apply nth_In. rewrite tc_len_gps by exact HLEN. exact Hi.
    * unfold aout_blks in Hc. destruct (Z.eqb_spec cap2 0) as [Hc0 | Hc0]; [destruct Hc|].
      destruct Hc as [<- | []]. cbn [fst snd] in Hra.
      destruct (in_dec tc_dec (out2, cap2) (ablocks B (gxly cx) (gxS cx))) as [Hin0 | Hnin0].
      -- apply (Permutation_in _ HPERM0) in Hin0. destruct Hin0 as [Heq | Hin0].
         { apply (GF (out2, cap2)); [left; exact Heq | exact Hc1 | exact Hra]. }
         apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
         { apply (GF (out2, cap2)); [right; apply in_or_app; left; exact Hin0 | exact Hc1 | exact Hra]. }
         apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
         { apply (GF (out2, cap2)); [right; apply in_or_app; right; apply in_or_app; left; exact Hin0 | exact Hc1 | exact Hra]. }
         apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
         { apply (GF (out2, cap2)); [right; apply in_or_app; right; apply in_or_app; right; exact Hin0 | exact Hc1 | exact Hra]. }
         exfalso.
         pose proof (Permutation_NoDup Hperm (tj_nodup _ _ _ _ _ _ HAR1)) as HN.
         apply (tc_nodup_app_r [(gxG0 cx, ATABLE)]) in HN.
         apply tc_nodup_app_r, tc_nodup_app_r, tc_nodup_app_r in HN.
         apply (tc_nodup_disj _ _ (out2, cap2) HN); [|exact Hin0].
         unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
      -- right. exists out2, cap2. split; [exact Hc1|]. split; [exact Hnin0 | exact Hra].
Qed.

(* ---- W_rig_top_live ---- *)

(* ---- The geometry both statements use. ---- *)
(* image bytes lie below the low shadow (kLowMemEnd = SHADOW_OFF) *)
Lemma tl2_img_low : forall a, in_img SEGS a -> 0 <= a < SHADOW_OFF.
Proof.
intros a Hi. pose proof (pa_segs_low a Hi) as H. pose proof asan_consts as (_ & _ & _ & _ & C5).
rewrite C5 in H. unfold SHADOW_OFF. lia.
Qed.
(* the entry sp: GBASE's afn_pre window, RIG_STK_x = 17200 bytes above alloc_ceiling *)
Lemma tl2_sp : forall cx, GBASE B ARx MT RP MMAX RG cx -> alloc_ceiling + 17200 <= gsp0 cx <= 2 ^ 47.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : RIG_STK_x = 17200) by reflexivity. rewrite WS in Hslo. unfold gsp0. lia.
Qed.
(* the run's own frame (1, fpos): a frame of S1 (the journal's own), below alloc_ceiling, application memory and
   not image bytes *)
Lemma tl2_frm : forall cx fpos ly1 S1 Hp1 W1 m1 md1 k1,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
ARx ly1 S1 Hp1 W1 m1 md1 /\ In (1, fpos) (frames S1) /\
4096 <= frame_addr ly1 1 fpos /\ frame_addr ly1 1 fpos + 128 <= alloc_ceiling /\ in_app (frame_addr ly1 1 fpos) 128 /\
(forall a, frame_addr ly1 1 fpos <= a < frame_addr ly1 1 fpos + 128 -> ~ in_img SEGS a).
Proof.
intros cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ.
pose proof (tj_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR Hfin) as (H1 & H2 & H3).
change (fs_frame_bytes 1) with 128 in H2, H3.
split; [exact HAR|]. split; [exact Hfin|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
intros a Ha Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR _) Hi). right. left.
exists 1, fpos. split; [exact Hfin|]. change (fs_frame_bytes 1) with 128. exact Ha.
Qed.

(* ---- L1. ---- *)
Lemma live_kept : stmt_live_kept.
Proof.
unfold stmt_live_kept.
intros cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 Hp2 m2 md2 P HB HJ1 HROM1 HPK HFR HLK HLS HJ2 HPw HK HPR.
pose proof (tl2_sp cx HB) as SP.
pose proof HB as (_ & _ & _ & RGP & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HFR as (HFa & HFl & HFL120 & HS16 & HS24 & HS80 & HSV).
destruct (tl2_frm cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ1) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (SF : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. unfold SHADOW_OFF in SF.
assert (HF8 : F = 8 * (F / 8) + F mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
(* the bytes P names are none of: image bytes, F's flag cell F + 120 .., the frame slots and the saved registers *)
assert (NPI : forall a, in_img SEGS a -> ~ P a).
{ intros a Hi Hp. pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  destruct (HPw a Hp) as [H|[H|[H|[H|H]]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia | |].
  - exact (HFni a ltac:(lia) Hi).
  - rewrite SF in H. lia. }
assert (NPF : forall a, F + 120 <= a < F + 128 -> ~ P a).
{ intros a Ha Hp. destruct (HPw a Hp) as [H|[H|[H|[H|H]]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia | lia |].
  rewrite SF in H. exact (fshadow_not_app F 16 F 128 a HF4 ltac:(lia) HFapp H ltac:(lia)). }
assert (NPS : forall a, gsp1 cx + 16 <= a < gsp1 cx + 32 \/ gsp1 cx + 40 <= a < gsp1 cx + 88 \/
  gsp1 cx + 120 <= a < gsp1 cx + 224 -> ~ P a).
{ intros a Ha Hp. unfold gsp1, RIG_FRAME in Ha.
  destruct (HPw a Hp) as [H|[H|[H|[H|H]]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia | lia |].
  rewrite SF in H. lia. }
assert (VK : forall a n v, (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ P (a + k)) ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v Hn Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 m2 a n v); [|exact Hv].
  intros k Hk. destruct (Hn k Hk) as (Hr & Hnp). exact (HK (a + k) Hr Hnp). }
split.
- exists fpos, Hp2. split; [exact HJ2|].
  split.
  { intros a Ha.
    assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
    rewrite (HK a ltac:(lia) (NPI a Hi)). exact (HROM1 a Ha). }
  split.
  { intros a Hi Ho He Hp. exact (HPR a (HPK a Hi Ho He Hp)). }
  split.
  { split; [exact HFa|]. split; [exact HFl|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [lia | apply NPF; lia] | exact HFL120]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS16]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS24]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS80]|].
    intros i Hi. apply VK; [|exact (HSV i Hi)].
    intros k Hk. cbn in Hk. split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia]. }
  apply (alock_at_kept RG W1 m1 W1 m2 true HLK).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  assert (Hi : in_img SEGS a) by exact (proj1 (RGIMG a ltac:(unfold rg_rng; left; exact Ha))).
  pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  split; [exact (HK a ltac:(lia) (NPI a Hi))|].
  unfold arm. apply writable_kept. exact (HPR a).
- pose proof HLS as (L40 & L48 & L56 & L64 & L72).
  split; [|split; [|split; [|split]]]; (apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | assumption]).
Qed.

(* ---- L2. ---- *)
Lemma live_drain : stmt_live_drain.
Proof.
unfold stmt_live_drain.
intros cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 SA e h cap out ly2 S2 Hp2 W2 m2 md2 k2 Hp3 k3
  HB HJ1 HROM1 HPK HFR HLK HLS HJD HFPB HPK2 HJ2.
pose proof (tl2_sp cx HB) as SP.
pose proof HB as (_ & _ & _ & RGP & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & RGWR & _).
pose proof HFR as (HFa & HFl & HFL120 & HS16 & HS24 & HS80 & HSV).
destruct (tl2_frm cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ1) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HGD : gx_ok SEGS B (G_DR B RG)) by exact (gx_ok_sub SEGS B _ _ (rig_G_DR_RIG B RG) HGRIG).
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD) as (memS & HJDi & HagD).
pose proof HJDi as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRM & _).
(* drain's footprint holds only block bytes: no byte of F, and not 0 (the sink stays closed) *)
assert (NFP : forall a, F <= a < F + 128 -> ~ inFP (dr_fp SA e h cap out) a).
{ intros a Ha Hf. destruct (HFPB a Hf) as (b & n & Hin & Hr).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ b n 1 fpos HAR1 Hin Hfin) as Hd.
  rewrite HFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (SPR : forall a, fp_spares (dr_fp SA e h cap out) a).
{ intros a Ho. exfalso. destruct (HFPB 0 Ho) as (b & n & Hin & Hr).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ b n HAR1 Hin) as (_ & H4096 & _). lia. }
(* what drain keeps: the caller's frame slots (above its window), the bytes of F, g_lock *)
assert (KHI : forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. unfold gsp1, RIG_FRAME in Ha.
  apply (gse_keep_high_x B PST ARx (G_DR B RG) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGD HJD a); unfold gsp1, RIG_FRAME; lia. }
assert (KFR : forall a, F <= a < F + 128 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha.
  assert (Hrng : in_zr a (frame_rng ly1 (1, fpos)) \/
    in_zr a (shadow_addr (frame_addr ly1 1 fpos), fs_frame_bytes 1 / 8)).
  { left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes 1) with 128. lia. }
  rewrite (FRM 1 fpos a Hfin Hrng (NFP a Ha)).
  apply HagD. rewrite unsigned_lit_small by lia. intros HG. exact (HFni a Ha (proj1 (HGD a HG))). }
assert (KLK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hi & Ho & He).
  pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  split.
  - apply (gse_keep_img_x B PST ARx (G_DR B RG) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD a Hi Ho He
      (PSTG a ltac:(left; unfold inG, G_RIG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia)) (SPR a)).
    pose proof HRGP as (HL & _). cbn [zall_disjoint] in HL. unfold zdisj in HL. cbn [fst snd] in HL.
    destruct HL as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _).
    unfold inG, G_DR, G_SL. intros HG. rewrite !Exists_cons, Exists_nil in HG. unfold in_zr in HG. cbn [fst snd] in HG.
    (* G_DR: g_s, then G_SL's g_client_broken, g_send_eintr, g_nout, g_capout, g_out, errno *)
    destruct HG as [HG|[HG|[HG|[HG|[HG|[HG|[HG|[]]]]]]]];
    [ clear - D1 Ha HG | clear - D10 Ha HG | clear - D12 Ha HG | clear - D6 Ha HG | clear - D7 Ha HG
    | clear - D8 Ha HG | clear - D14 Ha HG ]; lia.
  - intros _. unfold arm. apply (RGWR (w_H W2) m2 a); [left; exact Ha|].
    apply (hidden_not_img SEGS W2 (Z_to_bv 64 a)). rewrite unsigned_lit_small by lia. exact Hi. }
assert (LF : ly_F ly2 = ly_F ly1) by (destruct Hly as (_ & _ & _ & _ & _ & LF & _); exact LF).
assert (VKH : forall a n v, gsp1 cx <= a -> a + Z.of_nat n <= gsp0 cx ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v).
{ intros a n v H1 H2 Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 a n v); [|exact Hv].
  intros k Hk. apply KHI. lia. }
split.
- exists fpos, Hp3. split; [exact HJ2|].
  split.
  { apply (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD);
      [| exact PSTR | exact HROM1].
    intros a Ha. destruct (HROMO a Ha) as (HnG & Hrest). split; [|exact Hrest].
    intros HG. exact (HnG (rig_G_DR_RIG B RG a HG)). }
  split; [exact (gse_apres_trans B _ _ _ _ _ _ HPK HPK2)|].
  split.
  { split; [unfold frame_addr in *; rewrite LF; exact HFa|].
    split; [unfold flag_addr in *; rewrite LF; exact HFl|].
    split.
    { unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 _ 8 _); [|exact HFL120].
      intros k Hk. apply KFR. lia. }
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS16]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS24]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS80]|].
    intros i Hi. apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact (HSV i Hi)]. }
  apply (alock_at_kept RG W1 m1 W2 m2 true HLK).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact (KLK a Ha).
- pose proof HLS as (L40 & L48 & L56 & L64 & L72).
  split; [|split; [|split; [|split]]];
  (apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | assumption]).
Qed.

(* ---- W_rig_top_gin ---- *)

(* ---- tg_: list and model facts for entry i's start (pure: no machine state). ---- *)

(* an entry with its own keys put back is itself *)
Lemma tg_entry_keys_self : forall e, entry_keys e (re_keys e) = e.
Proof. intros e. destruct e. reflexivity. Qed.

(* nheld is the number of held keys *)
Lemma tg_nheld_len : forall e, re_nheld e = Z.of_nat (length (re_keys e)).
Proof. intros e. reflexivity. Qed.

(* nothing ended sends nothing *)
Lemma tg_sends_nil : forall mx c O cap, sl_sends mx c O cap (ge_bytes []) = (c, O, cap).
Proof. intros. reflexivity. Qed.

Lemma tg_geik_nil : forall pre, geik pre [] = ([], []).
Proof. intros. reflexivity. Qed.

Lemma tg_gkrest_nil : forall cx no cap, gkrest cx no cap [] = [].
Proof. intros. reflexivity. Qed.

(* GBASE: one harness source per entry *)
Lemma tg_gbase_len : forall cx, GBASE B ARx MT RP MMAX RG cx -> length (gxhs cx) = length (gxes cx).
Proof. intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _). exact HL. Qed.

Lemma tg_firstn_snoc : forall {X : Type} (l : list X) i d, (i < length l)%nat ->
firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros X l i d. revert l. induction i as [|i IH]; intros [|x l] H; cbn [length] in H; try lia.
- reflexivity.
- change (x :: firstn (S i) l = (x :: firstn i l) ++ [nth i l d]).
  rewrite (IH l ltac:(lia)). reflexivity.
Qed.

Lemma tg_combine_app : forall {X Y : Type} (l1 : list X) (l2 : list Y) l1' l2', length l1 = length l2 ->
combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
Proof.
intros X Y l1. induction l1 as [|x l1 IH]; intros l2 l1' l2' H; destruct l2 as [|y l2]; cbn [length] in H.
- reflexivity.
- discriminate H.
- discriminate H.
- cbn [app combine]. rewrite (IH l2 l1' l2' ltac:(lia)). reflexivity.
Qed.

(* entry i's harness source joins the done sources when entry i was open *)
Lemma tg_gdone_snoc : forall ps qd e (hj : hsrc * nat) e' (h' : hsrc), length ps = length qd ->
gdone_srcs (ps ++ [(e, hj)]) (qd ++ [(e', h')]) = gdone_srcs ps qd ++ (if re_eof e =? 0 then asrc_blks h' else []).
Proof.
intros ps qd e hj e' h' H. unfold gdone_srcs.
rewrite (tg_combine_app ps qd [(e, hj)] [(e', h')] H), map_app, concat_app.
cbn [combine map concat fst snd]. rewrite app_nil_r. reflexivity.
Qed.

(* rig_rel over a list split in two *)
Lemma tg_rel_app : forall pre mx ps qs ps2 qs2 c O cap c' O' cap' c2 O2 cap2,
rig_rel pre mx c O cap ps qs c' O' cap' -> rig_rel pre mx c' O' cap' ps2 qs2 c2 O2 cap2 ->
rig_rel pre mx c O cap (ps ++ ps2) (qs ++ qs2) c2 O2 cap2.
Proof.
intros pre mx ps. induction ps as [|[e [h j]] r IH];
intros qs ps2 qs2 c O cap c' O' cap' c2 O2 cap2 H1 H2; destruct qs as [|[e' h'] q];
cbn [rig_rel app] in H1 |- *; try contradiction.
- destruct H1 as (Ec & EO & Ecap). subst c' O' cap'. exact H2.
- destruct H1 as (e1 & ev & LB & H1). exists e1, ev, LB. cbv zeta in H1 |- *.
  destruct H1 as (Ha & Hb & Hc). split; [exact Ha|]. split; [exact Hb|].
  revert Hc. destruct (sl_sends _ _ _ _ _) as [[c3 O3] cap3]. intros Hc.
  exact (IH q ps2 qs2 c3 O3 cap3 c' O' cap' c2 O2 cap2 Hc H2).
Qed.

(* rig_rel of one entry: its drain (gdrained's equations), its key run (geik) and the run's sends *)
Lemma tg_rel_one : forall pre mx cB OB capB e (hj : hsrc * nat) ev LB e1 h1 c1 O1 cap1 Ed ks c2 O2 cap2,
c1 = (if re_eof e =? 0 then dr_ctl cB (fst hj) ev else cB) ->
O1 = (if (re_eof e =? 0) && dr_live cB (fst hj) then OB ++ LB else OB) ->
cap1 = (if (re_eof e =? 0) && dr_live cB (fst hj)
        then drain_b_c.ds_ocap (dr_fin cB mx (Z.of_nat (length OB)) capB e (fst hj)) else capB) ->
(if re_eof e =? 0 then dr_rel cB mx (Z.of_nat (length OB)) capB e (fst hj) e1 h1 LB else e1 = e /\ h1 = fst hj) ->
geik pre (re_keys e1) = (Ed, ks) ->
sl_sends mx c1 O1 cap1 (ge_bytes Ed) = (c2, O2, cap2) ->
rig_rel pre mx cB OB capB [(e, hj)] [(entry_keys e1 ks, h1)] c2 O2 cap2.
Proof.
intros pre mx cB OB capB e hj ev LB e1 h1 c1 O1 cap1 Ed ks c2 O2 cap2 Ec EO Ecap Hd Hg Hs.
destruct hj as [h j]. cbn [fst] in Ec, EO, Ecap, Hd. subst c1 O1 cap1.
cbn [rig_rel]. exists e1, ev, LB. cbv zeta. split; [exact Hd|].
rewrite Hg. cbn [fst snd]. split; [reflexivity|].
rewrite Hs. cbn [rig_rel]. repeat split.
Qed.

(* ---- G1: entry i's key loop starts (nheld = S r): GIN at n = 0, ks = re_keys e1, Ed = [], fuel |ks|. ---- *)
Lemma gin_top : stmt_gin_top.
Proof.
unfold stmt_gin_top.
intros cx i r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 spent ly1 S1 W1 m1 HB HG Hbud Hn Hpre Hsh.
exists (re_keys e1), (length (re_keys e1)).
unfold GTOPM in HG. cbv zeta in HG.
destruct HG as (Hi & Hq & Hrel & Hdr & Har & Hout & Hsrc & Hsrc1 & Hdro & Hkept & Hperm).
unfold gtop_bud in Hbud. cbv zeta in Hbud.
rewrite tg_nheld_len in Hn.
unfold GIN. cbv zeta. rewrite tg_entry_keys_self.
refine (conj Hi (conj Hq (conj Hrel (conj Hdr (conj (tg_sends_nil _ _ _ _) (conj _ (conj _ (conj _
  (conj Har (conj Hout (conj Hsrc (conj Hsrc1 (conj Hdro (conj Hkept (conj Hperm (conj Hpre (conj Hsh _))))))))))))))))).
- lia.
- lia.
- unfold geik. rewrite app_nil_l. apply surjective_pairing.
- exact Hbud.
Qed.

(* ---- G2: entry i holds no key (nheld <= 0): GOUT (S i), entry i done as e1 with its source h1. ---- *)
Lemma gout_top : stmt_gout_top.
Proof.
unfold stmt_gout_top.
intros cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 spent ly1 S1 W1 m1 HB HG Hbud Hn.
assert (Hk : re_keys e1 = []).
{ rewrite tg_nheld_len in Hn. destruct (re_keys e1) as [|k ks]; [reflexivity|]. cbn [length] in Hn. lia. }
pose proof (tg_gbase_len cx HB) as HL.
unfold GTOPM in HG. cbv zeta in HG.
destruct HG as (Hi & Hq & Hrel & Hdr & Har & Hout & Hsrc & Hsrc1 & Hdro & Hkept & Hperm).
unfold gtop_bud in Hbud. cbv zeta in Hbud. rewrite Hk, tg_geik_nil in Hbud. cbn [fst] in Hbud.
rewrite tg_sends_nil in Hbud. cbv beta iota in Hbud. rewrite tg_gkrest_nil, app_nil_l in Hbud.
unfold gdrained in Hdr. cbv zeta in Hdr. destruct Hdr as (Ec1 & EO1 & Ecap1 & Hd).
assert (Hlt : (i < length (gps cx))%nat) by (unfold gps; rewrite length_combine, HL; lia).
assert (Hnth : nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i)).
{ unfold gps, gnth, ghj. apply combine_nth. symmetry. exact HL. }
assert (Hfs : firstn (S i) (gps cx) = firstn i (gps cx) ++ [(gnth cx i, ghj cx i)]).
{ rewrite (tg_firstn_snoc (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) Hlt), Hnth.
  reflexivity. }
assert (Hlf : length (firstn i (gps cx)) = length qd) by (rewrite length_firstn; lia).
assert (Hone : rig_rel (gpre cx) (gxmx cx) cB OB capB [(gnth cx i, ghj cx i)] [(e1, h1)] c1 O1 cap1).
{ pose proof (tg_rel_one (gpre cx) (gxmx cx) cB OB capB (gnth cx i) (ghj cx i) ev LB e1 h1 c1 O1 cap1 [] (re_keys e1)
    c1 O1 cap1 Ec1 EO1 Ecap1 Hd ltac:(rewrite Hk; apply tg_geik_nil) (tg_sends_nil _ _ _ _)) as H1.
  rewrite tg_entry_keys_self in H1. exact H1. }
exists (qd ++ [(e1, h1)]).
unfold GOUT.
refine (conj _ (conj _ (conj _ (conj _ (conj Hout (conj _ (conj Hdro (conj Hkept (conj _ Hbud))))))))).
- lia.
- rewrite length_app. cbn [length]. lia.
- rewrite Hfs. exact (tg_rel_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel Hone).
- rewrite (map_app fst qd [(e1, h1)]), <- app_assoc. exact Har.
- intros i' Hi' He'. destruct (Nat.lt_ge_cases i' i) as [Hlt' | Hge'].
  + rewrite app_nth1 by lia. exact (Hsrc i' Hlt' He').
  + assert (Ei : i' = i) by lia. subst i'. rewrite app_nth2 by lia. rewrite Hq, Nat.sub_diag. cbn [nth snd].
    apply Hsrc1. apply Z.eqb_eq. exact He'.
- rewrite (map_app fst qd [(e1, h1)]), <- app_assoc.
  rewrite Hfs, (tg_gdone_snoc _ _ _ _ _ _ Hlf), <- app_assoc. exact Hperm.
Qed.

(* ---- W_rig_top_calls ---- *)

(* ------------------------------------------------------------------ the text "param_gesture <id> " *)
Lemma ts_digits : forall f x acc, 0 <= x -> Forall (fun z => 0 <= z < 256) acc ->
  Forall (fun z => 0 <= z < 256) (printf_facts_c.pf_digits f x acc) /\
  (length (printf_facts_c.pf_digits f x acc) <= length acc + f)%nat.
Proof.
induction f as [|f IH]; intros x acc Hx Ha; cbn [printf_facts_c.pf_digits]; [split; [exact Ha | lia]|].
destruct (x <? 10) eqn:E.
- apply Z.ltb_lt in E. split; [constructor; [lia | exact Ha] | cbn [length]; lia].
- apply Z.ltb_ge in E. assert (H10 : 0 <= x mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  destruct (IH (x / 10) ((48 + x mod 10) :: acc)) as [H1 H2]; [apply Z.div_pos; lia | constructor; [lia | exact Ha] |].
  split; [exact H1 | cbn [length] in H2; lia].
Qed.

(* snprintf's text T: bytes, and at most 27 of them (so the 48-byte buffer holds it with its NUL) *)
Lemma ts_T : forall id,
  Forall (fun z => 0 <= z < 256) (relay_instance_gone_b_c.instance_prefix id) /\
  (length (relay_instance_gone_b_c.instance_prefix id) <= 27)%nat.
Proof.
intros id.
assert (HD : Forall (fun z => 0 <= z < 256) (printf_facts_c.pf_dec id) /\ (length (printf_facts_c.pf_dec id) <= 12)%nat).
{ unfold printf_facts_c.pf_dec. destruct (id <? 0) eqn:E.
  - apply Z.ltb_lt in E. destruct (ts_digits 11 (- id) [] ltac:(lia) (Forall_nil _)) as [H1 H2].
    split; [constructor; [lia | exact H1] | cbn [length] in H2 |- *; lia].
  - apply Z.ltb_ge in E. destruct (ts_digits 11 id [] E (Forall_nil _)) as [H1 H2].
    split; [exact H1 | cbn [length] in H2; lia]. }
destruct HD as [HD1 HD2]. unfold relay_instance_gone_b_c.instance_prefix.
rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length].
split; [|lia].
apply Forall_app; split; [repeat constructor; lia|].
apply Forall_app; split; [repeat constructor; lia|].
apply Forall_app; split; [exact HD1 | repeat constructor; lia].
Qed.

(* snprintf's post (abytes_at of pf_bytes) as the walk's garr8 *)
Lemma ts_garr8_of_abytes : forall (W : world SEGS) mem a l, Forall (fun z => 0 <= z < 256) l ->
  abytes_at W mem a (printf_facts_c.pf_bytes l) -> garr8 SEGS (arm W mem) a l.
Proof.
intros W mem a l Hr Hb j Hj.
assert (Hz : 0 <= nth j l 0 < 256) by (apply (proj1 (Forall_forall _ _) Hr); apply nth_In; exact Hj).
specialize (Hb j ltac:(unfold printf_facts_c.pf_bytes; rewrite length_map; exact Hj)).
unfold printf_facts_c.pf_bytes in Hb. rewrite map_nth in Hb.
rewrite Z_to_bv_unsigned in Hb. unfold bv_wrap in Hb. change (bv_modulus 8) with 256 in Hb. rewrite Z.mod_small in Hb by lia.
split; [|exact Hz].
destruct (aview_byte SEGS (w_H W) mem _ _ Hb) as (b & Hm & Hv & _).
intros k Hk. assert (k = 0)%nat by lia. subst k. rewrite Z.add_0_r. unfold arm. rewrite Hm. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (nth j l 0) 256) by lia. exact (eq_sym Hv).
Qed.

(* ------------------------------------------------------------------ the fake frame F and its shadow *)
(* the 6 zero shadow bytes F's shadow + 4 .. + 9 make any prefix of the buffer F + 32 .. F + 80 addressable (F is
   32-aligned: alx_frames) *)
Lemma ts_ra : forall (W : world SEGS) mem F n, F mod 32 = 0 -> 0 <= n <= 48 ->
  (forall o, 4 <= o < 10 -> aview SEGS (w_H W) mem (shadow_addr F + o) = Some 0) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (F + 32) n.
Proof.
intros W mem F n Hal Hn Hsh x Hx. exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF32. rewrite Hal in DF32.
replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr F + (x / 8 - F / 8)) by (unfold shadow_of_addr, shadow_addr; lia).
apply Hsh. lia.
Qed.

(* the shadow hull of a prefix of the buffer F + 32 .. F + 80 lies in F's 16 shadow bytes, which are present
   (alx_frames: F is 32-aligned, so its shadow address is 4-aligned and the hull's 8-byte granules stay inside them) *)
Lemma ts_hull : forall ly S Hp (W : world SEGS) mem md fpos F n,
  ARx ly S Hp W mem md -> In (1, fpos) (frames S) -> frame_addr ly 1 fpos = F -> 0 < n <= 48 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) (F + 32) n.
Proof.
intros ly S Hp W mem md fpos F n HAR Hin HF Hn s Hs.
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md 1 fpos HAR Hin) as (Hal & _ & _ & Hsh).
change (fs_frame_bytes 1 / 8) with 16 in Hsh. rewrite HF in Hal, Hsh.
unfold shadow_addr, SHADOW_OFF in Hs, Hsh.
pose proof (Z.div_mod F 32 ltac:(lia)) as D32. rewrite Hal in D32.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
pose proof (Z.div_mod (F + 32) 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (F + 32) 8 ltac:(lia)) as N1.
pose proof (Z.div_mod (F + 32 + n - 1) 8 ltac:(lia)) as E2.
pose proof (Z.mod_pos_bound (F + 32 + n - 1) 8 ltac:(lia)) as N2.
pose proof (Z.div_mod (2147450880 + (F + 32) / 8) 8 ltac:(lia)) as E3.
pose proof (Z.mod_pos_bound (2147450880 + (F + 32) / 8) 8 ltac:(lia)) as N3.
pose proof (Z.div_mod (2147450880 + (F + 32 + n - 1) / 8) 8 ltac:(lia)) as E4.
pose proof (Z.mod_pos_bound (2147450880 + (F + 32 + n - 1) / 8) 8 ltac:(lia)) as N4.
specialize (Hsh (s - (2147450880 + F / 8)) ltac:(lia)).
replace (2147450880 + F / 8 + (s - (2147450880 + F / 8))) with s in Hsh by lia.
apply (aview_some_of_apresent SEGS). exact (proj1 Hsh).
Qed.

(* the walk's journal: the call state's allocator state, the fake frame among its frames, the stack above the
   allocator's ceiling (astk_ok) *)
Lemma ts_jframe : forall W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k,
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W
    memT mdc k ->
  ARx lyc Sc Hpc W memT mdc /\ In (1, fpos) (frames Sc) /\ alloc_ceiling + RIG_STK_x <= sp0.
Proof.
intros W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ.
destruct HJ as (_ & _ & (memS & HJi & _) & _).
destruct HJi as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
split; [exact HAR|]. split; [rewrite Hfrs; apply in_or_app; left; apply in_eq | lia].
Qed.

(* the class-1 fake frame F (128 bytes): below the ceiling, 32-aligned, in application memory, present, not the
   runtime's *)
Lemma ts_frame : forall ly S Hp W mem md fpos F,
  ARx ly S Hp W mem md -> In (1, fpos) (frames S) -> frame_addr ly 1 fpos = F ->
  4096 <= F /\ F + 128 <= alloc_ceiling /\ F mod 32 = 0 /\
  (F + 128 <= 2147446784 \/ 17594333495296 <= F) /\
  (forall a, F <= a < F + 128 -> apresent (w_H W) mem a /\ ~ aowned B ly S a).
Proof.
intros ly S Hp W mem md fpos F HAR Hin HF.
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 1 fpos HAR Hin) as (H1 & H2 & H3).
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md 1 fpos HAR Hin) as (H4 & _ & H5 & _).
change (fs_frame_bytes 1) with 128 in H2, H3, H5. rewrite HF in H1, H2, H3, H4, H5.
unfold in_app, kLowShadowBeg, kHighMemBeg in H3.
split; [lia|]. split; [lia|]. split; [exact H4|]. split; [lia | exact H5].
Qed.

(* an image object (between 0x10000 and 0x5fb000, inside ly_img: IMGC) is not a byte of the fake frame
   (alx_client_img) *)
Lemma ts_lit_apart : forall ly S Hp W mem md fpos F x,
  ARx ly S Hp W mem md -> In (1, fpos) (frames S) -> frame_addr ly 1 fpos = F ->
  65536 <= x < 6270976 -> ~ (F <= x < F + 128).
Proof.
intros ly S Hp W mem md fpos F x HAR Hin HF Hx Hr.
destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md x HAR) as [Hn _].
{ right. left. exists 1, fpos. split; [exact Hin|]. rewrite HF. change (fs_frame_bytes 1) with 128. exact Hr. }
apply Hn. destruct (IMGC ly S Hp W mem md HAR) as [H1 H2]. unfold in_zr. lia.
Qed.

(* ------------------------------------------------------------------ what snprintf reads of the image *)
(* a word of 8 visible bytes reads *)
Lemma ts_rdword_some : forall (rd : Z -> option Z) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
destruct (rd a) as [b0|] eqn:E0; [|exfalso; apply (H 0 ltac:(lia)); rewrite Z.add_0_r; exact E0].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|exfalso; exact (H 1 ltac:(lia) E1)].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|exfalso; exact (H 2 ltac:(lia) E2)].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|exfalso; exact (H 3 ltac:(lia) E3)].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|exfalso; exact (H 4 ltac:(lia) E4)].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|exfalso; exact (H 5 ltac:(lia) E5)].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|exfalso; exact (H 6 ltac:(lia) E6)].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|exfalso; exact (H 7 ltac:(lia) E7)].
eexists. reflexivity.
Qed.

(* the guard cells: the GOT word (HGOTG) and the canary, readable in every state through seg_rom (HCANR) *)
Lemma ts_guard : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  aguard_ok W mem FR_GOT_GUARD FR_GUARD.
Proof.
intros ly S Hp W mem md HAR. split; [exact (HGOTG ly S Hp W mem md HAR)|].
apply ts_rdword_some. intros k Hk. pose proof (HCANR (FR_GUARD + k) ltac:(lia)) as Hr.
unfold aview, mbyte. destruct (mrestrict (w_H W) mem (Z_to_bv 64 (FR_GUARD + k))); cbn [option_map]; [discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 (FR_GUARD + k))) eqn:E; cbn [option_map]; [discriminate | intros _; exact (Hr eq_refl)].
Qed.

(* a .rodata literal s (glit_at_x) as snprintf's string facts: its bytes and NUL (rom_view), read-only image bytes
   below the scratch, its shadow (ashp_x: addressable and the hull visible), its granule tail visible *)
Lemma ts_lit : forall i s ly S Hp W regs mem md, (i < 33)%nat -> (length s <= 16)%nat ->
  glit_at_x ARx i (s ++ [0]) ->
  Forall (fun c => 0 < c < 256) s ->
  ARx ly S Hp W mem md -> rom_view SEGS W mem -> alloc_ceiling <= spZ regs - 3 * ESTACK ->
  astr_at W mem (VAL (A_OBJ i)) (printf_facts_c.pf_bytes s) /\
  aread_ok (3 * ESTACK) W regs mem (VAL (A_OBJ i)) (Z.of_nat (length s) + 1) /\
  atail_vis W mem (VAL (A_OBJ i) + Z.of_nat (length s)).
Proof.
intros i s ly S Hp W regs mem md Hi Hs (G1 & G2 & G3 & GT) Hnz HAR Hrom Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_obj_img i Hi) as Oi.
assert (EL : Z.of_nat (length (s ++ [0])) = Z.of_nat (length s) + 1) by (rewrite length_app; cbn [length]; lia).
rewrite EL in G2, G3, GT.
replace (VAL (A_OBJ i) + (Z.of_nat (length s) + 1) - 1) with (VAL (A_OBJ i) + Z.of_nat (length s)) in GT by lia.
destruct (G3 ly S Hp W mem md HAR) as [G3r G3h].
assert (HB : abytes_at W mem (VAL (A_OBJ i)) (printf_facts_c.pf_bytes s ++ [Z_to_bv 8 0])).
{ intros j Hj.
  replace (printf_facts_c.pf_bytes s ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (s ++ [0])) in Hj |- *
    by (unfold printf_facts_c.pf_bytes; rewrite map_app; reflexivity).
  rewrite length_map in Hj.
  rewrite (Hrom (VAL (A_OBJ i) + Z.of_nat j)); [|apply G2; rewrite length_app in Hj; cbn [length] in Hj; lia].
  rewrite (G1 j Hj), (nth_error_nth' (s ++ [0]) 0 Hj). cbn [option_map].
  rewrite (map_nth (Z_to_bv 8) (s ++ [0]) 0 j). reflexivity. }
assert (HV : forall a, VAL (A_OBJ i) <= a < VAL (A_OBJ i) + (Z.of_nat (length s) + 1) -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. pose proof (HB (Z.to_nat (a - VAL (A_OBJ i)))
    ltac:(unfold printf_facts_c.pf_bytes; rewrite length_app, length_map; cbn [length]; lia)) as Hv.
  rewrite Z2Nat.id in Hv by lia. replace (VAL (A_OBJ i) + (a - VAL (A_OBJ i))) with a in Hv by lia.
  rewrite Hv. discriminate. }
split; [|split].
- split; [exact HB|]. intros Hin. apply in_map_iff in Hin as (x & Hx & Hxs).
  pose proof (proj1 (Forall_forall _ _) Hnz x Hxs) as Hx0. cbv beta in Hx0.
  apply (f_equal (@bv_unsigned 8)) in Hx. rewrite !Z_to_bv_unsigned in Hx. unfold bv_wrap in Hx.
  change (bv_modulus 8) with 256 in Hx. rewrite !Z.mod_small in Hx by lia. lia.
- unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split; [exact (HV a Ha)|]. unfold ascratch_stk. lia. }
  split; [apply amem_range_high; lia|]. split; [exact G3r|]. exact G3h.
- intros a Ha. specialize (GT a ltac:(lia)). unfold aview, mbyte. cbv beta.
  destruct (mrestrict (w_H W) mem (Z_to_bv 64 a)) as [b|]; cbn [option_map]; [discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|]; cbn [option_map]; [discriminate | exfalso; exact (GT eq_refl)].
Qed.

(* ------------------------------------------------------------------ S1. snprintf at 0x82e04 *)
(* ASNPRINTF at d = F + 32, n = 48, the format "%s %d " (A_OBJ 20), the arguments "param_gesture" (A_OBJ 21) and
   id, lifted over the walk's journal by aj_gx_entry_at_x (its written bytes F + 32 .. F + 80 are bytes of the walk's
   own fake frame: awr_byte's in_frames clause).  The image facts snprintf reads come from HGOTG and HCANR
   (ts_guard) and from HLIT20 / HLIT21 (ts_lit); the narrowing's M1 / M3 from HLITGOT (SnpNarrowSites.v san_M1_pi /
   san_M3_pi), M2 from san_M2_x_pi with the Section's IMGC (commit 2f48fc47493's snp_call, at ARx). *)
Lemma snp_call : stmt_snp_call.
Proof.
unfold stmt_snp_call.
intros W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F id idv Post
  HJ Hsp Hsp16 Hgp Htp Hra Hraw R10 R11 R12 R13 R14 Hidv Hid HF Hsh Hrom K.
set (T := relay_instance_gone_b_c.instance_prefix id) in *.
destruct (ts_T id) as [TR TL27]. fold T in TR, TL27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ts_jframe W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ) as (HAR & Hin & Hceil).
destruct (ts_frame lyc Sc Hpc W memT mdc fpos F HAR Hin HF) as (HF0 & HFc & HF32 & HFr & HFb).
pose proof (pa_obj_img 20 ltac:(lia)) as O20. pose proof (pa_obj_img 21 ltac:(lia)) as O21.
pose proof (ts_lit_apart lyc Sc Hpc W memT mdc fpos F (VAL (A_OBJ 21)) HAR Hin HF ltac:(lia)) as A21.
assert (Hsp' : alloc_ceiling <= spZ regsT - 3 * ESTACK) by lia.
pose proof (ts_guard lyc Sc Hpc W memT mdc HAR) as EG.
destruct (ts_lit 20 RIG_FMT lyc Sc Hpc W regsT memT mdc ltac:(lia) ltac:(unfold RIG_FMT; cbn [length]; lia) HLIT20
  ltac:(unfold RIG_FMT; repeat constructor; lia) HAR Hrom Hsp') as (E20s & E20r & E20t).
destruct (ts_lit 21 RelayModel.K_GESTURE lyc Sc Hpc W regsT memT mdc ltac:(lia)
  ltac:(unfold RelayModel.K_GESTURE; cbn [length]; lia) HLIT21
  ltac:(unfold RelayModel.K_GESTURE; repeat constructor; lia) HAR Hrom Hsp') as (E21s & E21r & E21t).
(* the narrowing's premises (W_sites_x.v asnprintf_realizes_x; SnpNarrowSites.v at this placement): the format and
   "param_gesture" below the GOT word (HLITGOT), the buffer F + 32 above the image (san_M2_x_pi) *)
destruct (SnpNarrowSites.san_M1_pi (PI := PI) RIG_FMT eq_refl (proj1 HLITGOT)) as (N1a & N1b).
assert (E13 : bv_unsigned (getr regsT 13) = VAL (A_OBJ 21))
  by (rewrite R13; unfold w64; apply unsigned_lit_small; lia).
pose proof (SnpNarrowSites.san_M2_x_pi (PI := PI) B ARx hl LAWS IMGC lyc Sc Hpc W memT mdc fpos HAR Hin) as N2.
rewrite HF in N2.
eapply SRr_bind.
{ apply (aj_gx_entry_at_x B PST ARx LAWS (G_RIG B RG) 0 [] (3 * ESTACK) (SIGMA WS_snprintf)
    (fun a => F + 32 <= a < F + 32 + 48)
    (fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length T)) /\
       abytes_at W mem' (F + 32) (printf_facts_c.pf_bytes (firstn (Z.to_nat (48 - 1)) T ++ [0])))
    W regsT memT RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc mdc k (-224) raw HGRIG eq_refl HJ
    ltac:(lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw).
  - intros a. destruct (Z_lt_dec a (F + 32)) as [H|H]; [right; lia|].
    destruct (Z_lt_dec a (F + 32 + 48)) as [H'|H']; [left; lia | right; lia].
  - intros a Ha _. cbv beta in Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (HFb a ltac:(lia))).
  - intros a Ha _. cbv beta in Ha. split; [|lia]. unfold awr_byte. right. right. right.
    unfold in_frames. exists 1, fpos. split; [apply in_eq|].
    left. unfold in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 1) with 128. lia.
  - intros HPRE HSC. eapply SRr_mono.
    { apply (ASNPRINTF lyc Sc Hpc W regsT memT mdc (F + 32) 48 (VAL (A_OBJ 20)) RIG_FMT
        [printf_facts_c.Ps; printf_facts_c.PLit 32; printf_facts_c.Pd; printf_facts_c.PLit 32]
        [printf_facts_c.APtr RelayModel.K_GESTURE; printf_facts_c.AInt id] T EG
        (ecall_pre_stk_of_x B ARx (3 * ESTACK) lyc Sc Hpc W regsT memT mdc HPRE HSC) R10 R11 R12
        ltac:(lia) ltac:(lia) ltac:(lia) E20s eq_refl eq_refl N1a N1b
        (fun s Hs => SnpNarrowSites.san_M3_pi (PI := PI) (getr regsT 13) id s E13 (proj2 HLITGOT) Hs) N2
        eq_refl ltac:(lia) E20r E20t).
      + (* the arguments: "param_gesture" in the image, apart from the buffer; id in a4 *)
        cbn [apf_args_ok apf_arg_ok]. rewrite R13, R14. unfold w64.
        rewrite (unsigned_lit_small (VAL (A_OBJ 21))) by lia.
        split; [|split; [|exact I]].
        * split; [unfold RelayModel.K_GESTURE; repeat constructor; lia|].
          split; [lia|]. split; [exact E21s|]. split; [exact E21r|]. split; [exact E21t|].
          change (Z.of_nat (length RelayModel.K_GESTURE)) with 13. lia.
        * split; [exact Hid|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          rewrite Z.mod_mod_divide; [exact Hidv|]. exists (2 ^ 32). reflexivity.
      + (* the buffer F + 32 .. F + 80: frame bytes (present, not the runtime's), below the scratch, its shadow *)
        unfold awrite_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
        { intros a Ha. destruct (HFb a ltac:(lia)) as [Hpa Hno].
          split; [exact (apresent_writable SEGS _ _ _ Hpa)|]. split; [exact Hno|]. unfold ascratch_stk. lia. }
        split; [apply amem_range_high; lia|]. split; [exact (ts_ra W memT F 48 HF32 ltac:(lia) Hsh)|].
        intros _. exact (ts_hull lyc Sc Hpc W memT mdc fpos F 48 HAR Hin HF ltac:(lia)).
      + (* asnprintf_realizes' seven bytes past the buffer: F + 32 + 55 <= F + 128, the fake frame in high memory *)
        apply amem_range_high; lia.
      + exact (rt_rom_view_of_rom_view B W memT Hrom). }
    intros W' c' _ Hp'. apply aentry_post_of_art_post_x. exact Hp'. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (R10' & Hby) & Hfr & Hpres).
assert (EF : firstn (Z.to_nat (48 - 1)) T = T) by (apply firstn_all2; change (Z.to_nat (48 - 1)) with 47%nat; lia).
rewrite EF in Hby.
apply (K regs2 mem2 md2 HJ2 HP2 R10').
- apply ts_garr8_of_abytes; [apply Forall_app; split; [exact TR | repeat constructor; lia] | exact Hby].
- intros a Ha H1 H2. apply Hfr; [exact Ha | cbv beta; lia | lia].
- exact Hpres.
Qed.

(* ------------------------------------------------------------------ S2. strlen at 0x82e0c *)
(* ASTRLEN at x = F + 32, kk = |pre|, by aj_strlen_gx_at_x: the bytes and the NUL from the garr8 premise, the rest of
   the NUL's granule inside the fake frame (present), the shadow as for snprintf. *)
Lemma strlen_call : stmt_strlen_call.
Proof.
unfold stmt_strlen_call.
intros W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F pre Post
  HJ Hsp Hsp16 Hgp Htp Hra Hraw R10 HF Hg Hnz Hlen Hsh Hrom K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ts_jframe W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ) as (HAR & Hin & Hceil).
destruct (ts_frame lyc Sc Hpc W memT mdc fpos F HAR Hin HF) as (HF0 & HFc & HF32 & HFr & HFb).
eapply SRr_bind.
{ apply (aj_strlen_gx_at_x B PST ARx LAWS (SIGMA WS_strlen) ASTRLEN (G_RIG B RG) 0 [] W regsT memT RIG_STK_x sp0 FP ly S Hp
    W0 mem md [(1, fpos)] lyc Sc Hpc mdc k (F + 32) (Z.of_nat (length pre)) (-224) raw HGRIG eq_refl HJ R10
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw).
  - unfold first_byte. split; [lia|]. split.
    + intros i Hi. exists (nth (Z.to_nat i) pre 0). split.
      * pose proof (tp_garr8_aview (w_H W) memT (F + 32) (pre ++ [0]) (Z.to_nat i) Hg
          ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
        rewrite Z2Nat.id in Hv by lia. rewrite app_nth1 in Hv by lia. exact Hv.
      * intros E. apply Hnz. rewrite <- E. apply nth_In. lia.
    + intros _. pose proof (tp_garr8_aview (w_H W) memT (F + 32) (pre ++ [0]) (length pre) Hg
        ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
      rewrite nth_middle in Hv. exact Hv.
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HFb a ltac:(lia)))|]. lia.
  - intros a Ha. lia.
  - apply amem_range_high; lia.
  - apply amem_range_high; lia.
  - exact (ts_ra W memT F (Z.of_nat (length pre) + 1) HF32 ltac:(lia) Hsh).
  - exact (ts_hull lyc Sc Hpc W memT mdc fpos F (Z.of_nat (length pre) + 1) HAR Hin HF ltac:(lia)).
  - intros a Ha. pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length pre)) 8 ltac:(lia)) as M8.
    apply (aview_some_of_apresent SEGS). apply (proj1 (HFb a ltac:(lia))).
  - exact Hrom. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & R10' & Hfr & Hpres).
apply (K regs2 mem2 md2 HJ2 HP2 R10').
- intros a Ha Hn. apply Hfr; [exact Ha | lia].
- exact Hpres.
Qed.


Lemma tp_skipn_cons : forall {X : Type} (l : list X) (d : X) (k : nat), (k < length l)%nat ->
skipn k l = nth k l d :: skipn (S k) l.
Proof.
intros X l d. induction l as [|x l IH]; intros k Hk; cbn [length] in Hk; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
Lemma tp_table_entry : forall M G l tail k,
garr8 SEGS M G (bzs (concat (map entry_bytes l) ++ tail)) ->
Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l -> (k < length l)%nat ->
garr8 SEGS M (G + AENT * Z.of_nat k) (bzs (entry_bytes (nth k l relay_remove_b_c.no_entry))).
Proof.
intros M G l tail k Hg HF Hk.
rewrite (rrs_concat_split entry_bytes l relay_remove_b_c.no_entry k Hk) in Hg.
unfold bzs in Hg |- *. rewrite !map_app in Hg.
apply garr8_app in Hg as [Hg _]. apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
assert (HF1 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (firstn k l)).
{ rewrite <- (firstn_skipn k l) in HF. apply Forall_app in HF as [HF1 _]. exact HF1. }
rewrite length_map, (rrs_concat_len _ HF1), length_firstn in Hg.
replace (Nat.min k (length l)) with k in Hg by lia.
unfold AENT. replace (G + 56 * Z.of_nat k) with (G + Z.of_nat (56 * k)) by lia. exact Hg.
Qed.
Lemma tp_entry_eof : forall M SA e, garr8 SEGS M SA (bzs (entry_bytes e)) -> (re_eof e = 0 \/ re_eof e = 1) ->
val_mem SEGS M (SA + 4) 4 (re_eof e).
Proof.
intros M SA e Hg He. unfold entry_bytes, bzs in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4 in Hg.
apply rrs_garr8_le; [|cbn; lia].
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Hg.
rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.
Lemma tp_entry_nheld : forall M SA e, garr8 SEGS M SA (bzs (entry_bytes e)) -> length (re_pad1 e) = 4%nat ->
0 <= re_nheld e < 2 ^ 31 -> val_mem SEGS M (SA + 48) 4 (re_nheld e).
Proof.
intros M SA e Hg Hp He. unfold entry_bytes, bzs in Hg. rewrite !map_app in Hg.
do 8 (apply garr8_app in Hg as [_ Hg]). apply garr8_app in Hg as [Hg _].
lazymatch type of Hg with garr8 _ _ ?b _ => replace b with (SA + 48) in Hg by
  (rewrite ?length_map, ?OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
     ?OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, ?Hp; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) end.
apply rrs_garr8_le; [|cbn; lia].
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Hg.
rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.

Lemma tp_env_agree_ewset : forall R E n w, env_agree 32 R E -> (32 <= n)%nat -> env_agree 32 R (ewset E n w).
Proof. intros R E n w [HA HD] Hn. split; [|exact HD]. intros k Hk. rewrite ew_ewset_other by lia. apply HA. exact Hk. Qed.
Lemma tp_kept2 : forall E1 rs1 E2 rs2 H (m0 m1 m2 : word -> option byte) a,
frame_of E1 rs1 (mrestrict H m0) (mrestrict H m1) -> frame_of E2 rs2 (mrestrict H m1) (mrestrict H m2) ->
0 <= a < 2 ^ 64 -> ~ in_wrange E1 rs1 a -> ~ in_wrange E2 rs2 a -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E1 rs1 E2 rs2 H m0 m1 m2 a F1 F2 Ha N1 N2.
rewrite (aview_kept_out E2 rs2 H m1 m2 F2 a Ha N2). exact (aview_kept_out E1 rs1 H m0 m1 F1 a Ha N1).
Qed.

Lemma tp_pres : forall regs regs' r (b : bv 5), aregs_preserved regs regs' -> bv_unsigned b = r -> acallee_saved r ->
getr regs' b = getr regs b.
Proof. intros regs regs' r b H <- Hr. rewrite <- (Z_to_bv_bv_unsigned _ b). apply H. exact Hr. Qed.

(* W7's W_drain_sa.v dr_sa_align_slot over alx_blocks: a slot of the 16-aligned table is 8-aligned *)
Lemma tp_sa_align : forall ly S Hp W mem md (G : Z) (i : nat),
ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> (G + AENT * Z.of_nat i) mod 8 = 0.
Proof.
intros ly S Hp W mem md G i HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md G ATABLE HAR Hin) as (H16 & _).
apply Z.mod_divide in H16; [|lia]. destruct H16 as (k & ->).
unfold AENT. apply Z.mod_divide; [lia|]. exists (2 * k + 7 * Z.of_nat i). lia.
Qed.

(* the held array's clause of aentry_ok, in the form W_rr_m_dcnt.v's count lemma takes it *)
Lemma td_hk : forall ly S W mem e, aentry_ok B ly S W mem e -> re_hp e = 0 \/ re_kh e <> 0.
Proof.
intros ly S W mem e HE. unfold aentry_ok in HE.
destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHP & _).
destruct HHP as [(E0 & _)|(E0 & _ & _ & K8 & _)]; [left; lia | right; lia].
Qed.

Lemma tp_achain_call : forall cx ly1 W1 m1,
GBASE B ARx MT RP MMAX RG cx -> g_saved cx W1 m1 -> ly_top ly1 = ly_top (gxly cx) ->
(forall a, gsp0 cx <= a < 2 ^ 64 -> aview SEGS (w_H W1) m1 a = aview SEGS (w_H (gxW cx)) (gxmem cx) a) ->
exists ch1, achain ly1 (aview SEGS (w_H W1) m1) (gsp1 cx) (gsp0 cx) ch1.
Proof.
intros cx ly1 W1 m1 HB HSV Htop Hk.
pose proof HB as (HPRE & H32 & _).
pose proof HPRE as (_ & _ & Hra & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (_ & _ & Hs3 & Hs4 & _ & Hs6 & _ & Hs8 & Hs9).
assert (WS : RIG_STK_x = 17200) by reflexivity.
fold (gsp0 cx) in Hs4, Hs8, Hch.
destruct (Z_lt_le_dec (gsp0 cx) (ly_top (gxly cx) - 16)) as [Hlt | Hge].
- exists ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx).
  apply (achain_ly_top (gxly cx)); [exact Htop|].
  apply (achain_push (gxly cx) (aview SEGS (w_H (gxW cx)) (gxmem cx)) _ (gsp0 cx) (s0Z (gxregs cx)) (raZ (gxregs cx)) (gxch cx) (gsp1 cx) Hch).
  + lia.
  + exact Hk.
  + replace (gsp0 cx - 8) with (gsp1 cx + 120 + 8 * Z.of_nat 12) by (unfold gsp1, RIG_FRAME; lia).
    apply rdword_of_val_mem; [exact (HSV 12%nat ltac:(lia)) | unfold raZ; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 1)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R].
  + replace (gsp0 cx - 16) with (gsp1 cx + 120 + 8 * Z.of_nat 11) by (unfold gsp1, RIG_FRAME; lia).
    apply rdword_of_val_mem; [exact (HSV 11%nat ltac:(lia)) | unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 8)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R].
  + exact Hra.
  + rewrite WS in Hs4. lia.
  + pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
    replace (32 * (gsp0 cx / 32)) with ((4 * (gsp0 cx / 32)) * 8) by ring. apply Z_mod_mult.
  + exact Hlt.
  + unfold gsp1, RIG_FRAME. lia.
- exists []. left. split; [right; left; rewrite Htop; exact Hge | reflexivity].
Qed.

Definition TP_PHI : Z := 140737479966720.
Definition tp_sr1 : list sv := sr_set sr_atoms 22%bv (SOff (A_HI 45) 0).
Definition tp_regions1 : smem :=
[ YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 88 96 88 96 [];
  YP09.mkRegion (Some 33%nat) 4 8 8 8 [YP09.mkChunk 4 (CVal 4 (SOff 34 0))] ].
Definition tp_facts1 : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (18%nat, mkAF SB SB 0); (33%nat, mkAF 4096 TP_PHI 3); (34%nat, mkAF 0 1 0) ] []
  [ (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 56)) (SOff 32 0), SOff 33 0) ].
Definition tp_ss1 : sstate := mkSS A_rig_outer tp_sr1 tp_regions1 None tp_facts1.
Definition tp_SH1 : list shent := [ mkSHE 33 4 8 ].
Definition tp_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition tp_extra1 (G0 SA eof : Z) : list word := map (Z_to_bv 64) [G0; SA; eof].

Lemma tp_alias_sa : forall (E : env) G0 (i : Z) SA, ew E 14 = Z_to_bv 64 i -> ew E 32 = Z_to_bv 64 G0 -> ew E 33 = Z_to_bv 64 SA ->
SA = G0 + 56 * i -> 0 <= i <= 16 -> 0 <= G0 <= 2 ^ 50 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 56)) (SOff 32 0)) = sv_denot E (SOff 33 0).
Proof.
intros E G0 i SA H14 H32 H33 HSA Hi HG.
cbn [sv_denot]. rewrite H14, H32, H33, !Z.add_0_r, !Z_to_bv_bv_unsigned.
unfold alu64, mul_div, alu.
apply bv_eq. rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small i), (Z.mod_small 56), (Z.mod_small G0) by lia.
rewrite (Z.mod_small (i * 56)) by lia. f_equal. lia.
Qed.

Lemma tp_seat1 : forall (W : world SEGS) regs mem G0 SA eof sp (i : Z),
getr regs 22 = Z_to_bv 64 (VAL (A_HI 45)) -> bv_unsigned (getr regs 9) = sp -> getr regs 18 = w64 SHADOW_OFF ->
getr regs 14 = Z_to_bv 64 i -> 0 <= i <= 16 ->
SA = G0 + 56 * i -> 4096 <= G0 -> G0 + 896 <= alloc_ceiling -> alloc_ceiling <= sp -> G0 mod 8 = 0 -> eof = 0 \/ eof = 1 ->
0x10000 <= VAL (A_OBJ 8) -> VAL (A_OBJ 8) + 8 <= 0x5fb000 -> 2 ^ 46 <= sp -> sp + 96 <= 2 ^ 47 -> sp mod 32 = 0 ->
(SA + 8 <= VAL (A_OBJ 8) \/ VAL (A_OBJ 8) + 8 <= SA + 4) ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 8)) 8 G0 ->
val_mem SEGS (mrestrict (w_H W) mem) (SA + 4) 4 eof ->
(forall o, 88 <= o < 96 -> apresent (w_H W) mem (sp + o)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (tp_extra1 G0 SA eof))) tp_ss1
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_rig_outer)) mem (seg_rom SEGS))).
Proof.
intros W regs mem G0 SA eof sp i H22 H9 H18 H14 Hi HSA HG1 HG2 HGsp HG3 Heof Hs1 Hs2 Hsp1 Hsp2 Hsp3 Hdj VG VE HP.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_val_range (A_OBJ 8)) as HV8r.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (tp_extra1 G0 SA eof))).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 eof) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EH45 : ew E (A_HI 45) = Z_to_bv 64 (VAL (A_HI 45))) by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (U8 : base_val E (Some (A_OBJ 8)) = VAL (A_OBJ 8)) by (cbn [base_val]; rewrite EO8; apply unsigned_lit_small; lia).
assert (U9 : base_val E (Some 9%nat) = sp) by (cbn [base_val]; rewrite (EL 9%nat 9%bv eq_refl); exact H9).
assert (U33 : base_val E (Some 33%nat) = SA) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; unfold TP_PHI in *; lia).
assert (U18 : bv_unsigned (ew E 18) = SB) by (rewrite (EL 18%nat 18%bv eq_refl), H18; unfold w64, SHADOW_OFF, SB; apply unsigned_lit_small; lia).
unfold tp_ss1. apply pa_entry_st_ok_full.
- unfold tp_sr1. apply regs_ok_same; [apply regs_ok_Eimg_Ereg|].
  cbn [sv_denot]. rewrite EH45, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact H22.
- vm_compute. reflexivity.
- unfold tp_regions1. repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 8)) 0 8 _ G0);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold TP_PHI in *; zside | zside |].
    rewrite Z.add_0_r. exact VG.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (HP o Ho).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U33.
    split; [unfold TP_PHI in *; lia|]. split; [unfold TP_PHI in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ SA 4 4 _ eof);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VE].
- apply pairwise_disjoint_of_extents.
  unfold tp_regions1, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U8, U9, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold TP_PHI in *. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [tp_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EL 9%nat 9%bv eq_refl), H9, U18, E33, E34, !unsigned_lit_small by (unfold TP_PHI in *; lia).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (SA mod 8 = 0) by (rewrite HSA; replace (G0 + 56 * i) with (G0 + (7 * i) * 8) by ring; rewrite Z.mod_add by lia; exact HG3).
    unfold SB, TP_PHI in *. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
  + cbn [tp_facts1 f_alias alias_ok]. split; [|exact I].
    apply (tp_alias_sa E G0 i SA); [rewrite (EL 14%nat 14%bv eq_refl); exact H14 | exact E32 | exact E33 | exact HSA | exact Hi | unfold TP_PHI in *; lia].
Qed.

Ltac tp_nw HFr NW P Ubs :=
lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
assert (NW : forall a, ~ P a -> ~ in_wrange Ex rs a);
[ let a := fresh "a" in let Na := fresh "Na" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a Na (r & Hin & Hr); cbv beta in Na;
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    repeat (rewrite ew_ewset_other in Hr by lia); repeat (rewrite YN3v.ew_havoc_old in Hr by (cbv; lia)); rewrite ?Ubs in Hr; lia | ]);
  destruct Hin
| ] end.

Lemma tp_digits : forall f x acc, 0 <= x -> ~ In 0 acc ->
  ~ In 0 (printf_facts_c.pf_digits f x acc) /\ (length acc <= length (printf_facts_c.pf_digits f x acc))%nat.
Proof.
induction f as [|f IH]; intros x acc Hx Ha; cbn [printf_facts_c.pf_digits]; [split; [exact Ha | lia]|].
destruct (x <? 10) eqn:E.
- apply Z.ltb_lt in E. split; [|cbn [length]; lia].
  intros [H|H]; [lia | exact (Ha H)].
- apply Z.ltb_ge in E.
  assert (H10 : 0 <= x mod 10) by (apply Z.mod_pos_bound; lia).
  destruct (IH (x / 10) ((48 + x mod 10) :: acc)) as [H1 H2].
  + apply Z.div_pos; lia.
  + intros [H|H]; [lia | exact (Ha H)].
  + split; [exact H1|]. cbn [length] in H2. lia.
Qed.
Lemma tp_digits_le : forall f x acc, (length (printf_facts_c.pf_digits f x acc) <= length acc + f)%nat.
Proof.
induction f as [|f IH]; intros x acc; cbn [printf_facts_c.pf_digits]; [lia|].
destruct (x <? 10); [cbn [length]; lia|]. specialize (IH (x / 10) ((48 + x mod 10) :: acc)). cbn [length] in IH. lia.
Qed.
Lemma tp_digits11 : forall x, 0 <= x ->
  ~ In 0 (printf_facts_c.pf_digits 11 x []) /\ (1 <= length (printf_facts_c.pf_digits 11 x []) <= 11)%nat.
Proof.
intros x Hx. destruct (tp_digits 11 x [] Hx (fun H => H)) as [H1 _]. split; [exact H1|].
pose proof (tp_digits_le 11 x []) as H3. cbn [length] in H3. split; [|lia].
change (printf_facts_c.pf_digits 11 x []) with
  (if x <? 10 then [48 + x] else printf_facts_c.pf_digits 10 (x / 10) [48 + x mod 10]).
destruct (x <? 10) eqn:E; [cbn [length]; lia|].
apply Z.ltb_ge in E.
destruct (tp_digits 10 (x / 10) [48 + x mod 10]) as [_ H2].
- apply Z.div_pos; lia.
- assert (Hm : 0 <= x mod 10) by (apply Z.mod_pos_bound; lia). intros [Hd|[]]; lia.
- cbn [length] in H2. lia.
Qed.
Lemma tp_pre_nz : forall cx, ~ In 0 (gpre cx) /\ (16 <= length (gpre cx))%nat /\ (length (gpre cx) <= 27)%nat.
Proof.
intros cx. unfold gpre, relay_instance_gone_b_c.instance_prefix.
assert (HD : ~ In 0 (printf_facts_c.pf_dec (gxID cx)) /\
             (1 <= length (printf_facts_c.pf_dec (gxID cx)) <= 12)%nat).
{ unfold printf_facts_c.pf_dec. destruct (gxID cx <? 0) eqn:E.
  - apply Z.ltb_lt in E. destruct (tp_digits11 (- gxID cx) ltac:(lia)) as [H1 H2].
    split; [intros [H|H]; [lia | exact (H1 H)] | cbn [length]; lia].
  - apply Z.ltb_ge in E. destruct (tp_digits11 (gxID cx) E) as [H1 H2]. split; [exact H1 | lia]. }
destruct HD as [HD1 HD2]. split; [|split].
- rewrite !in_app_iff. intros [H|[H|[H|H]]].
  + unfold RelayModel.K_GESTURE in H. cbn in H. lia.
  + cbn in H. lia.
  + exact (HD1 H).
  + cbn in H. lia.
- rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length]. lia.
- rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length]. lia.
Qed.

Lemma rk_garr8_kv_tp : forall H H' (m m' : word -> option byte) a l, garr8 SEGS (mrestrict H m) a l ->
(forall b, a <= b < a + Z.of_nat (length l) -> aview SEGS H' m' b = aview SEGS H m b) -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hg Hk. apply (garr8_frame SEGS _ _ a l Hg). intros b Hb. apply (mbyte_of_aview SEGS). exact (Hk b Hb).
Qed.

Lemma tp_branch_ge : forall E a b va vb, sv_denot E a = Z_to_bv 64 va -> sv_denot E b = Z_to_bv 64 vb ->
0 <= va < 2 ^ 63 -> 0 <= vb < 2 ^ 63 -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (va <? vb).
Proof.
intros E a b va vb Ha Hb Hva Hvb. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite !bv_signed_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma tp_sh_den : forall E (n : nat) c x, bv_unsigned (ew E n) + c = x -> ew E 18 = w64 SHADOW_OFF -> 0 <= x < 2 ^ 60 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 18 0)) = w64 (SHADOW_OFF + x / 8).
Proof.
intros E n c x Hx E18 Hb. cbn [sv_denot]. rewrite Hx, E18, Z.add_0_r, Z_to_bv_bv_unsigned.
assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x / 8) (2 ^ 64)) by lia. rewrite Z.add_comm. apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.

Lemma tp_sh_den2 : forall x y, y = w64 SHADOW_OFF -> 0 <= x < 2 ^ 60 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) y = w64 (SHADOW_OFF + x / 8).
Proof.
intros x y -> Hb.
assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x / 8) (2 ^ 64)) by lia. rewrite Z.add_comm. apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.

Lemma tp_soff : forall E n c x, bv_unsigned (ew E n) = x -> sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof. intros E n c x H. cbn [sv_denot]. rewrite H. reflexivity. Qed.


Definition PD (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent,
c1 = cfg_at SEGS (BASE + A_rig_pd) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 20 = w64 (F + 32) /\ getr regs1 21 = w64 (shadow_addr F) /\
getr regs1 22 = w64 (rg_src RG + RIG_HI_SRC) /\ getr regs1 19 = w64 (AENT * Z.of_nat i) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 88) 8 (Z.of_nat i) /\
GLIVE B PST ARx RG cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots RG cx F W1 m1 /\
GTOPM cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 W1 m1 /\
gtop_bud cx e1 c1' O1 cap1 i ly1 S1 spent.

(* the runners over the generic journal (lib/A/W_relay_finish_h.v's Lets) *)
Let RUN := paj_run_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let BR := paj_branch (PI := PI).

Lemma top_p1 :
stmt_gout_kept -> stmt_top_rep_closed -> stmt_top_budget ->
stmt_live_kept ->
stmt_top_drain_pre -> stmt_dr_inv_of -> stmt_top_room -> stmt_dr_fp_in ->
stmt_top_rep_open -> stmt_dr_bytes -> stmt_dr_cnt -> stmt_live_drain ->
forall cx i W1 c1,
GBASE B ARx MT RP MMAX RG cx -> RGO B PST ARx MT RP MMAX RG cx i W1 c1 ->
(forall W2 c2, PD cx i W2 c2 -> SRr SEGS W2 c2 (gPOST B PST ARx MT RP RG cx)) ->
SRr SEGS W1 c1 (gPOST B PST ARx MT RP RG cx).
Proof.
intros LGK LRC LBU LLK LDP LDI LTR LFP LRO LDB LDC LLD cx i W1 c1 HB HO KPD.
destruct HO as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent & -> & HRB & R20 & R21 & R22 & R14 & Hi & HGL & HLS & HGO).
pose proof HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H18).
pose proof HGO as (Hle & Hlq & Hrel & Hrly & Hout & Hsrc & Hdrs & Hgs & Hperm & Hbud).
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 & HBT).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (SRCI : in_img SEGS (rg_src RG)) by (apply (proj1 (RGIMG (rg_src RG) ltac:(unfold rg_rng; right; right; left; lia)))).
assert (SRCI7 : in_img SEGS (rg_src RG + 7)) by (apply (proj1 (RGIMG (rg_src RG + 7) ltac:(unfold rg_rng; right; right; left; lia)))).
pose proof (pa_img_range (rg_src RG) SRCI) as SRCr. pose proof (pa_img_range (rg_src RG + 7) SRCI7) as SRCr7.
pose proof Hrly as (RS1 & _ & _ & _ & _ & _ & Rlen & RSG & (tail & _ & _ & Rtab) & Rok & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 RSG) as (HG16 & HG4096 & HGc & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in HGc, HGapp, HGpres.
(* entry i of the table *)
assert (HLES : length (gxes cx) = length (gxhs cx)) by (symmetry; exact HLEN).
assert (Hsk : skipn i (gxes cx) = gnth cx i :: skipn (S i) (gxes cx)) by (apply tp_skipn_cons; lia).
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (map fst qd ++ skipn i (gxes cx))).
{ eapply Forall_impl; [|exact Rok]. intros e (_ & _ & P1 & P2 & _). split; assumption. }
assert (HLmq : length (map fst qd) = i) by (rewrite length_map; exact Hlq).
assert (Hnth : nth i (map fst qd ++ skipn i (gxes cx)) relay_remove_b_c.no_entry = gnth cx i).
{ rewrite app_nth2 by lia. rewrite HLmq, Nat.sub_diag, Hsk. reflexivity. }
assert (HLtab : (i < length (map fst qd ++ skipn i (gxes cx)))%nat) by (rewrite length_app, HLmq, length_skipn; lia).
pose proof (tp_table_entry _ _ _ _ i Rtab Hok HLtab) as HTE. rewrite Hnth in HTE.
assert (HEok : aentry_ok B ly1 S1 W1 m1 (gnth cx i)).
{ rewrite Forall_forall in Rok. apply Rok. rewrite <- Hnth. apply nth_In. exact HLtab. }
pose proof HEok as (Heof01 & _).
pose proof (tp_entry_eof _ _ _ HTE Heof01) as HVE.

set (SA := gxG0 cx + AENT * Z.of_nat i) in *.
set (G0 := gxG0 cx) in *.
assert (Hes16 : (length (gxes cx) <= 16)%nat) by (rewrite length_app, HLmq, length_skipn in Rlen; lia).
assert (SP1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
assert (Hsp32 : gsp1 cx mod 32 = 0) by (rewrite SP1; rewrite Zminus_mod, H32; reflexivity).
assert (HDJ : SA + 8 <= VAL (A_OBJ 8) \/ VAL (A_OBJ 8) + 8 <= SA + 4).
{ rewrite <- RGSRC. destruct (Z_le_gt_dec (SA + 8) (rg_src RG)) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (rg_src RG + 8) (SA + 4)) as [D2|D2]; [right; exact D2|]. exfalso.
  set (a := Z.max (SA + 4) (rg_src RG)).
  assert (Hia : in_img SEGS a) by (apply (proj1 (RGIMG a ltac:(unfold rg_rng; right; right; left; unfold a; lia)))).
  refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR1 _) Hia). left. exists G0, ATABLE. split; [exact RSG|].
  rewrite RQT. unfold a, SA, AENT in *. lia. }
pose proof (tp_seat1 W1 regs1 m1 G0 SA (re_eof (gnth cx i)) (gsp1 cx) (Z.of_nat i)) as HS.
specialize (HS ltac:(rewrite R22, HH45; reflexivity)
  ltac:(rewrite H9; unfold w64; apply unsigned_lit_small; unfold gsp0 in *; lia)
  H18 R14 ltac:(lia) ltac:(unfold SA, AENT; lia) HG4096 HGc ltac:(rewrite SP1; unfold gsp0 in *; lia)
  ltac:(pose proof (Z.div_mod G0 16 ltac:(lia)) as D; rewrite HG16 in D; rewrite D;
        replace (16 * (G0 / 16) + 0) with ((2 * (G0 / 16)) * 8) by lia; apply Z_mod_mult)
  Heof01 ltac:(rewrite <- RGSRC; lia) ltac:(rewrite <- RGSRC; lia)
  ltac:(rewrite SP1; unfold gsp0 in *; lia) ltac:(rewrite SP1; unfold gsp0 in *; lia) Hsp32 HDJ
  ltac:(rewrite <- RGSRC; exact RS1) HVE
  ltac:(intros o Ho; apply Hpres1; rewrite SP1, WS; lia)).
remember (Eimg (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_eof (gnth cx i))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
clear HE.
assert (HBx : U E (SOff 18 0) = SHADOW_OFF) by (rewrite (U_atom E 18 SHADOW_OFF E18) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS (SOff 18 0) tp_SH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 _ W1 m1 md1 G0 ATABLE (SA + 4) 4 HAR1 RSG);
    [unfold SA, AENT; lia | rewrite RQT; unfold SA, AENT; lia].
  + exact HBx.
  + rewrite (U_atom E 33 _ E33) by (unfold SA, AENT; lia). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SA, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rig_outer)) with (Z_to_bv 64 (BASE + A_rig_outer)).
pose proof HJ as HJ0.
paj_run_tok_x RUN HS HJ SHOK tp_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]].
  intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite (EEo 9%nat 9%bv eq_refl), H9 in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (unfold gsp0 in *; lia).
  left. split; [left; rewrite SP1, WS in *; lia | lia]. }

rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
assert (E34' : ew (ewset (ewset E 512 w) 513 w0) 34 = Z_to_bv 64 (re_eof (gnth cx i))) by (rewrite !ew_ewset_other by lia; exact E34).
assert (HAE' : env_agree 32 (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i)))) (ewset (ewset E 512 w) 513 w0))
by (apply tp_env_agree_ewset; [apply tp_env_agree_ewset; [exact HAE | lia] | lia]).
assert (NW0 : forall a, ~ (gsp1 cx + 88 <= a < gsp1 cx + 96) -> ~ in_wrange E (ss_mem tp_ss1) a).
{ intros a Na (r & Hin & Hr). cbn [ss_mem tp_ss1 tp_regions1 In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; try lia.
  rewrite (EEo 9%nat 9%bv eq_refl), H9 in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by (unfold gsp0 in *; lia). lia. }
psrr_branch_tok RUN BR HS SHOK tp_Bspan.
- (* s->eof <> 0: no drain, to 0x82dd0 *)
  rewrite branch_ne_U, (U_atom _ 34 _ E34'), U_lit in Hc by lia.
  assert (Heof1 : re_eof (gnth cx i) <> 0) by (intros X; rewrite X in Hc; discriminate Hc).
  paj_run_to_tok_x RUNTO HS HJ SHOK tp_Bspan (AF_fr_relay_instance_gone + 0x1a4).
  { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]].
    intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ew_ewset_other, ew_ewset_other, (EEo 9%nat 9%bv eq_refl), H9 in Ha by lia.
    unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (unfold gsp0 in *; lia).
    left. split; [left; rewrite SP1, WS in *; lia | lia]. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => assert (HAE2 : env_agree 32 (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i)))) Ex)
    by (repeat first [exact HAE' | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 20; 21]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (22%bv : bv 5) N22. prreg HS (19%bv : bv 5) N19.
  assert (U9E : bv_unsigned (ew E 9) = gsp1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; unfold gsp0 in *; lia).
  tp_nw HFr0 NW0' (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) U9E.
  tp_nw HFr1 NW1 (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) U9E.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx + 88 <= a < gsp1 cx + 96) ->
    aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a)
  by (intros a Ha Na; exact (tp_kept2 _ _ _ _ _ _ _ _ a HFr0 HFr1 Ha (NW0' a Na) (NW1 a Na))).
  assert (PRES : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
  by (intros a Hp; eapply apresent_grows; [exact HG1 | eapply apresent_grows; [exact HG0 | exact Hp]]).
  assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
  assert (HGO1 : GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1)).
  { apply (LGK cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 (ms_mem ms1) fpos HB HAR1 Hfin); [|exact PRES|exact HGO].
    intros a Ha _. apply KEEP; [lia|]. rewrite SP1, WS in *. lia. }
  pose proof (LRC cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1) HB Hi Heof1 HGO1) as HTM.
  pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcl & Hbr & Hdd & _ & Hmx & _ & Hcapd).
  assert (Hcap0 : 0 <= cap2) by (destruct Hcapd as [(-> & _) | (Hc0 & _)]; lia).
  pose proof (LBU cx i qd c2 O2 cap2 spent ly1 S1 ly1 S1 (gnth cx i) (fst (ghj cx i)) 0 [] c2 O2 cap2 HB Hi Hlq Hrel Hcl Hbr
    Hdd Hcap0 Hmx Hbud) as HBU.
  specialize (HBU ltac:(unfold gdrained; rewrite (proj2 (Z.eqb_neq _ _) Heof1); cbn; repeat split; reflexivity)
    ltac:(intros X; apply Z.eqb_eq in X; contradiction)
    ltac:(intros _; destruct Hbud as (_ & _ & _ & _ & _ & HRM0 & _);
          split; [apply (mo_le_refl MT MLAW) | split; [lia | split; [exact HRM0 | reflexivity]]])).
  rewrite (proj2 (Z.eqb_neq _ _) Heof1), Z.add_0_r in HBU.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pmkst HS.
  apply KPD. unfold PD.
  exists (ms_regs ms1), ly1, S1, (ms_mem ms1), (with_vm_backing (m_vm_lazy md1) mat1 md1), k1, F, FL, qd, c2, O2, cap2,
    (gnth cx i), (fst (ghj cx i)), 0, [], c2, O2, cap2, out2, spent.
  split; [unfold cfg_at, A_rig_pd; reflexivity|].
  split; [unfold gregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRB|].
  split; [rewrite HK by (cbv; tauto); exact R20|].
  split; [rewrite HK by (cbv; tauto); exact R21|].
  split; [change 325%nat with (A_HI 45) in N22; rewrite N22, (img_env_atomP E (A_HI 45) HEI ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH45; reflexivity|].
  split; [rewrite N19, (EEo 14%nat 14%bv eq_refl), R14; apply bv_eq; unfold mul_div; rewrite bv_mul_unsigned, !Z_to_bv_unsigned;
          unfold bv_wrap, AENT; change (bv_modulus 64) with (2 ^ 64);
          rewrite (Z.mod_small (Z.of_nat i)), (Z.mod_small 56), (Z.mod_small (Z.of_nat i * 56)), (Z.mod_small (56 * Z.of_nat i)) by lia; lia|].
  split.
  { unfold arm. replace (gsp1 cx + 88) with (bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 9) + 88)
      by (rewrite !ew_ewset_other, U9E by lia; reflexivity).
    eapply (field_of_region _ _ 9 _ _ 88 96 88 96 88 8%N (SOff 14 0) (Z.of_nat i) RG1); [reflexivity | left; reflexivity | | cbn; lia | cbn; lia].
    cbn [sv_denot]. rewrite !ew_ewset_other, (EEo 14%nat 14%bv eq_refl), R14 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat1 md1)
    (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) HB HJ0 HROM1 HPK HFR HLK HLS HJ) as [HGL1 HLS1].
  { intros a Ha. right; right; left. exact Ha. }
  { exact KEEP. }
  { exact PRES. }
  split; [exact HGL1|]. split; [exact HLS1|]. split; [exact HTM | exact HBU].

- (* s->eof = 0: drain (s) at 0x82dcc *)
  rewrite branch_ne_U, (U_atom _ 34 _ E34'), U_lit in Hc by lia.
  assert (Heof0 : re_eof (gnth cx i) = 0) by (destruct Heof01 as [X|X]; [exact X | rewrite X in Hc; discriminate Hc]).
  paj_run_to_tok_x RUNTO HS HJ SHOK tp_Bspan AF_fr_drain.
  { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]].
    intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ew_ewset_other, ew_ewset_other, (EEo 9%nat 9%bv eq_refl), H9 in Ha by lia.
    unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (unfold gsp0 in *; lia).
    left. split; [left; rewrite SP1, WS in *; lia | lia]. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => assert (HAE2 : env_agree 32 (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i)))) Ex)
    by (repeat first [exact HAE' | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 20; 21]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (22%bv : bv 5) N22. prreg HS (19%bv : bv 5) N19. prreg HS (10%bv : bv 5) N10. prreg HS (1%bv : bv 5) N1.
  assert (U9E : bv_unsigned (ew E 9) = gsp1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; unfold gsp0 in *; lia).
  tp_nw HFr0 NW0' (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) U9E.
  tp_nw HFr1 NW1 (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) U9E.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx + 88 <= a < gsp1 cx + 96) ->
    aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a)
  by (intros a Ha Na; exact (tp_kept2 _ _ _ _ _ _ _ _ a HFr0 HFr1 Ha (NW0' a Na) (NW1 a Na))).
  assert (PRES : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
  by (intros a Hp; eapply apresent_grows; [exact HG1 | eapply apresent_grows; [exact HG0 | exact Hp]]).
  assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
  assert (HGO1 : GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1)).
  { apply (LGK cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 (ms_mem ms1) fpos HB HAR1 Hfin); [|exact PRES|exact HGO].
    intros a Ha _. apply KEEP; [lia|]. rewrite SP1, WS in *. lia. }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pmkst HS.
  set (mdc := with_vm_backing (m_vm_lazy md1) mat1 md1) in *.
  destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms1) mdc
    (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) HB HJ0 HROM1 HPK HFR HLK HLS HJ) as [HGL1 HLS1].
  { intros a Ha. right; right; left. exact Ha. }
  { exact KEEP. }
  { exact PRES. }
  pose proof HGL1 as (fpos1 & Hpg & HJg & HROMc & HPKc & HFRc & HLKc).
  pose proof (tj_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg) as HARc.
  assert (V88 : val_mem SEGS (arm W1 (ms_mem ms1)) (gsp1 cx + 88) 8 (Z.of_nat i)).
  { unfold arm. replace (gsp1 cx + 88) with (bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 9) + 88)
      by (rewrite !ew_ewset_other, U9E by lia; reflexivity).
    eapply (field_of_region _ _ 9 _ _ 88 96 88 96 88 8%N (SOff 14 0) (Z.of_nat i) RG1); [reflexivity | left; reflexivity | | cbn; lia | cbn; lia].
    cbn [sv_denot]. rewrite !ew_ewset_other, (EEo 14%nat 14%bv eq_refl), R14 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  pose proof HGO1 as (_ & _ & _ & _ & Hout1 & _).
  pose proof HPRE as (_ & _ & _ & HGP0 & HTP0 & _).
  pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcl & Hbr & Hdd & _ & Hmx & _ & Hcapd).
  assert (Hcap0 : 0 <= cap2) by (destruct Hcapd as [(-> & _) | (Hc0 & _)]; lia).
  destruct (LDP cx i qd c2 O2 cap2 out2 spent ly1 S1 Hpg W1 (ms_mem ms1) mdc HB Hi Heof0 HGO1 HARc)
    as (DTab & DG1 & DG2 & DGA & DAW & DEOK & DSRC & DPERM).
  pose proof DSRC as (Dj & Dasrc & Doth & Dfd & Dsk & DU & Db1 & Db2 & Db3).
  destruct (LDI ly1 S1 W1 (ms_mem ms1) (gnth cx i) (fst (ghj cx i)) (snd (ghj cx i)) (Z.of_nat (length O2)) cap2 DEOK DSRC) as [DINV DREST].
  destruct (LTR cx i qd c2 O2 cap2 spent ly1 S1 HB Hi Hlq Heof0 Hrel Hcl Hbr Hdd Hcap0 Hmx DINV DREST Hbud)
    as (RM1 & RM2 & RM3 & RM4 & RM5).
  pose proof HFRc as (_ & _ & _ & _ & _ & _ & HSV1).
  destruct (tp_achain_call cx ly1 W1 (ms_mem ms1) HB HSV1
    ltac:(eapply tp_ly_top; exact HJg)
    ltac:(intros a Ha; eapply gse_keep_high_x; [exact HGRIG | exact HJg | lia | rewrite WS; lia])) as (ch1 & Hch1).
  pose proof (LFP cx i qd c2 O2 cap2 out2 spent ly1 S1 Hpg W1 (ms_mem ms1) mdc HB Hi Heof0 HGO1 HARc) as HFP1.
  assert (Usp1 : spZ (ms_regs ms1) = gsp1 cx) by (unfold spZ; rewrite HK by (cbv; tauto); exact Hsp1).
  eapply SRr_bind.
  { eapply (gse_callS_x B PST ARx LAWS (G_RIG B RG) W1 (ms_regs ms1) (ms_mem ms1) _ RIG_STK_x (gsp0 cx) (gFP cx)
      (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos1)] ly1 S1 Hpg mdc k1 DRAIN_STK_x
      (dr_fp (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2) (-224) (Z_to_bv 64 (BASE + 2788)) ch1
      (fun ly2 S2 W2 regs2 mem2 md2 => exists Hpd kd,
         ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (gsp1 cx)
           (dr_fp (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2) ly1 S1 Hpg W1 (ms_mem ms1) mdc [] ly2 S2 Hpd W2 mem2 md2 kd /\
         DRK cx i c2 O2 cap2 out2 ly1 S1 W1 (ms_mem ms1) ly2 S2 W2 mem2 /\
         rp_RM RP S2 (dr_kr cx i c2 (Z.of_nat (length O2)) cap2))
      HGRIG HJg).
    - rewrite Usp1. unfold gsp1, RIG_FRAME. lia.
    - reflexivity.
    - lia.
    - unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia.
    - unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia.
    - rewrite HK by (cbv; tauto). rewrite Hgp1. exact HGP0.
    - rewrite HK by (cbv; tauto). rewrite Htp1. exact HTP0.
    - exact N1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - replace (gsp0 cx + -224) with (gsp1 cx) by (unfold gsp1, RIG_FRAME; lia).
      replace (s0Z (ms_regs ms1)) with (gsp0 cx) by (unfold s0Z; rewrite HK by (cbv; tauto); rewrite H8; unfold w64;
        rewrite unsigned_lit_small by (unfold gsp0 in *; lia); reflexivity).
      exact Hch1.
    - intros HPRE1. eapply SRr_mono.
      { eapply (DRAIN W1 ly1 S1 Hpg (ms_regs ms1) (ms_mem ms1) mdc ch1 G0 SA (gnth cx i) (snd (ghj cx i)) (fst (ghj cx i)) c2 O2
          (gxmx cx) (Z.of_nat (length O2)) cap2 out2 HPRE1).
        + rewrite N10, E33. reflexivity.
        + exact DTab.
        + exact DG1.
        + exact DG2.
        + (* dr_spec_x's entry alignment (W7's s7): a slot of the 16-aligned table (tp_sa_align, W7's W_drain_sa.v over
             alx_blocks) *)
          unfold SA. exact (tp_sa_align ly1 S1 Hpg W1 (ms_mem ms1) mdc G0 i HARc DTab).
        + exact DGA.
        + exact DAW.
        + exact DEOK.
        + exact Dj.
        + exact Dasrc.
        + exact Doth.
        + exact Dfd.
        + exact Dsk.
        + exact DU.
        + exact Hout1.
        + exact HROMc.
        + exact DPERM.
        + exact Db1.
        + exact Db2.
        + exact Db3.
        + exact RM1.
        + exact RM2.
        + exact RM3.
        + (* the room round: drain's room at dr_kr, its count premise (top_room) *)
          exact RM4.
        + exact RM5. }
      cbv beta. intros W3 c3 _ (ly' & S' & Hp' & regs' & mem' & md' & kd & e' & h' & out' & ev' & LB & rest & -> & HJd & HPr &
        HAK & HMO & HRMd & HP1 & HP2 & HGA & HAW & HEOK & Hrfd & Hreo & Hcp & Hcp2 & HU & Hsk' & Hkt & Hka & Hhk & HNDd & HSS &
        Has & Hslot & Hec & Hec2 & Hhfd & Hhcl & Hei & Hrec & Hoff & Hv & Hpc & Hpart & Hst & Hmap & Hfirst & Hheld & Hsk2 &
        HU2 & HLB & Hao).
      exists ly', S', Hp', regs', mem', md', kd. split; [rewrite N1; reflexivity|].
      split; [eapply rig_lift_DR; exact HJd|]. split; [exact HPr|].
      exists Hp', kd. split; [rewrite <- Usp1; exact HJd|].
      split; [|exact HRMd].
      unfold DRK. cbv zeta. exists e', h', out', ev', LB, rest.
      split; [exact HAK|]. split; [exact HMO|]. split; [exact HP1|]. split; [exact HP2|].
      split; [exact HGA|]. split; [exact HAW|]. split; [exact HEOK|].
      split; [unfold dr_rel; cbv zeta; repeat (split; [assumption|]); assumption|].
      split; [exact Has|]. split; [exact Hslot|]. exact Hao.
    - exact HFP1. }
  cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & -> & HJ3 & HJc3 & HP3 &
    (Hpd & kd & HJd & HDRK & HRMd)).
  pose proof HPRE as (_ & _ & _ & _ & _ & HAS0 & _). pose proof HAS0 as (_ & _ & As3 & As4 & _).
  assert (HCEIL : alloc_ceiling <= gsp1 cx - DRAIN_STK_x).
  { fold (gsp0 cx) in As4. rewrite WS in As4. unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia. }
  destruct (LRO cx i qd c2 O2 cap2 out2 spent ly1 S1 Hpg W1 (ms_mem ms1) mdc (gsp1 cx) ly3 S3 Hpd W3 mem3 md3 kd HB Hi Heof0
    HGO1 HARc HJd HCEIL HDRK) as (e1 & h1 & ev & LB & out1 & HTM).
  pose proof HTM as (_ & _ & _ & HGD & _).
  pose proof HDRK as (e' & h' & out' & ev' & LB' & rest & HAK' & HMO' & HP1' & HP2' & _ & _ & HEOK' & HREL' & _).
  pose proof (LDB ly1 S1 W1 (ms_mem ms1) ly3 S3 c2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 out' (gnth cx i) (fst (ghj cx i))
    e' h' LB' rest _ DEOK Dasrc Hcap0 Hmx ltac:(lia) DINV DREST HP1' HP2' HREL') as HBB.
  (* the room round's counts: over drain's blocks the counts move by drain's net count (stmt_dr_cnt); the blocks
     drain does not own (rest) are the same on both sides *)
  assert (HCNT3 : forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) =
    Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (dr_tr c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i)))).
  { intros P.
    pose proof (LDC c2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 out' (gnth cx i) (fst (ghj cx i)) e' h' LB' P
      DINV DREST (td_hk _ _ _ _ _ DEOK) (td_hk _ _ _ _ _ HEOK') Hcap0 HREL') as ECN. cbv zeta in ECN.
    rewrite (ReplyCnt.acnt_perm P _ _ HP2'), (ReplyCnt.acnt_perm P _ _ HP1'), !ReplyCnt.acnt_app.
    rewrite !ReplyCnt.acnt_app in ECN. lia. }
  pose proof (LBU cx i qd c2 O2 cap2 spent ly1 S1 ly3 S3 e1 h1 ev LB _ _ _ HB Hi Hlq Hrel Hcl Hbr Hdd Hcap0 Hmx Hbud HGD)
    as HBU.
  specialize (HBU ltac:(intros _; split; [exact DINV | split; [exact DREST | split; [exact HMO' |
      split; [exact HBB | split; [exact HRMd | exact HCNT3]]]]])
    ltac:(intros X; rewrite Heof0 in X; discriminate X)).
  destruct (LLD cx fpos1 F FL ly1 S1 Hpg W1 (ms_mem ms1) mdc k1 (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2 ly3 S3 Hpd
    W3 mem3 md3 kd Hp3
    (k1 + k3) HB HJg HROMc HPKc HFRc HLKc HLS1 HJd) as [HGL3 HLS3].
  { intros a Ha. destruct (HFP1 a Ha) as [(_ & Hb) | (b & n & Hin & _ & Hr)]; [exact Hb | exists b, n; split; [exact Hin | exact Hr]]. }
  { exact HAK'. }
  { exact HJ3. }
  assert (V88' : val_mem SEGS (arm W3 mem3) (gsp1 cx + 88) 8 (Z.of_nat i)).
  { unfold arm in *. eapply val_mem_kept; [|exact V88]. intros kk Hkk.
    eapply gse_keep_high_x; [exact HGRIG | exact HJc3 | unfold gsp1, RIG_FRAME, gsp0 in *; lia | unfold gsp1, RIG_FRAME in *; lia]. }
  apply KPD. unfold PD.
  exists regs3, ly3, S3, mem3, md3, (k1 + k3), F, FL, qd, c2, O2, cap2, e1, h1, ev, LB.
  do 3 eexists. exists out1. eexists.
  split; [unfold cfg_at, A_rig_pd; reflexivity|].
  split.
  { unfold gregs_base. unfold spZ.
    rewrite (tp_pres _ _ 2 2%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 3 3%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 4 4%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 8 8%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 9 9%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 18 18%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite !HK by (cbv; tauto). exact HRB. }
  split; [rewrite (tp_pres _ _ 20 20%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto); exact R20|].
  split; [rewrite (tp_pres _ _ 21 21%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto); exact R21|].
  split; [rewrite (tp_pres _ _ 22 22%bv HP3 eq_refl ltac:(unfold acallee_saved; lia));
          change 325%nat with (A_HI 45) in N22; rewrite N22, (img_env_atomP E (A_HI 45) HEI ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH45; reflexivity|].
  split; [rewrite (tp_pres _ _ 19 19%bv HP3 eq_refl ltac:(unfold acallee_saved; lia));
          rewrite N19, (EEo 14%nat 14%bv eq_refl), R14; apply bv_eq; unfold mul_div; rewrite bv_mul_unsigned, !Z_to_bv_unsigned;
          unfold bv_wrap, AENT; change (bv_modulus 64) with (2 ^ 64);
          rewrite (Z.mod_small (Z.of_nat i)), (Z.mod_small 56), (Z.mod_small (Z.of_nat i * 56)), (Z.mod_small (56 * Z.of_nat i)) by lia; lia|].
  split; [exact V88'|].
  split; [exact HGL3|]. split; [exact HLS3|]. split; [exact HTM | exact HBU].
Qed.

Definition tp_regions2 : smem :=
[ YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 56 88 56 56
    [YP09.mkChunk 56 (CVal 8 (SOff (A_OBJ 21) 0)); YP09.mkChunk 64 (CVal 8 (SOff (A_OBJ 20) 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0))];
  YP09.mkRegion (Some 21%nat) 4 10 4 10 [] ].
(* atom 21 = F's shadow address: 4-aligned (F is 32-aligned in any ARx state, alx_frames) *)
Definition tp_facts2 : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (18%nat, mkAF SB SB 0); (21%nat, mkAF SB (SB + 2^44) 2) ] [] [].
Definition tp_ss2 : sstate := mkSS A_rig_pd tp_sr1 tp_regions2 None tp_facts2.
Definition tp_Bspan0 : Z * Z := (0, 0).
Definition tp_extra2 (G0 idv : Z) : list word := map (Z_to_bv 64) [G0; idv].

Lemma tp_seat2 : forall (W : world SEGS) regs mem G0 idv sp sh,
getr regs 22 = Z_to_bv 64 (VAL (A_HI 45)) -> bv_unsigned (getr regs 9) = sp -> getr regs 18 = w64 SHADOW_OFF ->
bv_unsigned (getr regs 21) = sh -> SB <= sh <= SB + 2 ^ 44 -> sh mod 4 = 0 ->
0x10000 <= VAL (A_OBJ 8) -> VAL (A_OBJ 8) + 8 <= 0x5fb000 -> 2 ^ 46 <= sp -> sp + 96 <= 2 ^ 47 -> sp mod 32 = 0 ->
0 <= G0 < 2 ^ 64 -> 0 <= idv < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 8)) 8 G0 ->
val_mem SEGS (mrestrict (w_H W) mem) (sp + 56) 8 (VAL (A_OBJ 21)) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp + 64) 8 (VAL (A_OBJ 20)) ->
val_mem SEGS (mrestrict (w_H W) mem) (sp + 80) 8 idv ->
(forall o, 4 <= o < 10 -> apresent (w_H W) mem (sh + o)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (tp_extra2 G0 idv))) tp_ss2
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_rig_pd)) mem (seg_rom SEGS))).
Proof.
intros W regs mem G0 idv sp sh H22 H9 H18 H21 Hsh1 Hsh2 Hs1 Hs2 Hsp1 Hsp2 Hsp3 HG0 Hid VG V56 V64 V80 HP.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_val_range (A_OBJ 8)) as HV8r. pose proof (pa_val_range (A_OBJ 20)) as HV20r. pose proof (pa_val_range (A_OBJ 21)) as HV21r.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (tp_extra2 G0 idv))).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO20 : ew E (A_OBJ 20) = Z_to_bv 64 (VAL (A_OBJ 20))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO21 : ew E (A_OBJ 21) = Z_to_bv 64 (VAL (A_OBJ 21))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EH45 : ew E (A_HI 45) = Z_to_bv 64 (VAL (A_HI 45))) by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (U8 : base_val E (Some (A_OBJ 8)) = VAL (A_OBJ 8)) by (cbn [base_val]; rewrite EO8; apply unsigned_lit_small; lia).
assert (U9 : base_val E (Some 9%nat) = sp) by (cbn [base_val]; rewrite (EL 9%nat 9%bv eq_refl); exact H9).
assert (U21 : base_val E (Some 21%nat) = sh) by (cbn [base_val]; rewrite (EL 21%nat 21%bv eq_refl); exact H21).
assert (U18 : bv_unsigned (ew E 18) = SB) by (rewrite (EL 18%nat 18%bv eq_refl), H18; unfold w64, SHADOW_OFF, SB; apply unsigned_lit_small; lia).
unfold tp_ss2. apply pa_entry_st_ok_full.
- unfold tp_sr1. apply regs_ok_same; [apply regs_ok_Eimg_Ereg|].
  cbn [sv_denot]. rewrite EH45, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact H22.
- vm_compute. reflexivity.
- unfold tp_regions2. repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 8)) 0 8 _ G0);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact VG.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 56 8 _ (VAL (A_OBJ 21)));
      [cbn [sv_denot]; rewrite EO21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V56].
    * apply (chunk_ok_val SEGS E _ sp 64 8 _ (VAL (A_OBJ 20)));
      [cbn [sv_denot]; rewrite EO20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V64].
    * apply (chunk_ok_val SEGS E _ sp 80 8 _ idv);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V80].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U21.
    split; [unfold SB in *; lia|]. split; [unfold SB in *; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (HP o Ho).
- apply pairwise_disjoint_of_extents.
  unfold tp_regions2, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U8, U9, U21.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SB in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [tp_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (EL 9%nat 9%bv eq_refl), H9, U18, (EL 21%nat 21%bv eq_refl), H21.
  change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB in *. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

Definition tp_ss3 : sstate := mkSS 2844 sr_atoms [] None (mkFacts [] [] []).
Lemma tp_seat3 : forall (W : world SEGS) regs mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) tp_ss3
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 2844)) mem (seg_rom SEGS))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold tp_ss3. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [exact I | split; exact I].
Qed.

Definition tp_regions4 : smem :=
[ YP09.mkRegion (Some 19%nat) 48 52 48 48 [YP09.mkChunk 48 (CVal 4 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 32 40 32 40 [] ].
Definition tp_facts4 : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (18%nat, mkAF SB SB 0); (19%nat, mkAF 4096 TP_PHI 3); (32%nat, mkAF 0 (2^31 - 1) 0) ] [] [].
Definition tp_ss4 : sstate := mkSS 2852 sr_atoms tp_regions4 None tp_facts4.
Definition tp_SH4 : list shent := [ mkSHE 19 48 52 ].

Lemma tp_seat4 : forall (W : world SEGS) regs mem SA sp nh,
bv_unsigned (getr regs 19) = SA -> bv_unsigned (getr regs 9) = sp -> getr regs 18 = w64 SHADOW_OFF ->
4096 <= SA -> SA + 56 <= alloc_ceiling -> SA mod 8 = 0 -> alloc_ceiling <= sp -> sp + 96 <= 2 ^ 47 -> sp mod 32 = 0 ->
0 <= nh < 2 ^ 31 ->
val_mem SEGS (mrestrict (w_H W) mem) (SA + 48) 4 nh ->
(forall o, 32 <= o < 40 -> apresent (w_H W) mem (sp + o)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 nh])) tp_ss4
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 2852)) mem (seg_rom SEGS))).
Proof.
intros W regs mem SA sp nh H19 H9 H18 HS1 HS2 HS3 Hsp1 Hsp2 Hsp3 Hnh VN HP.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [Z_to_bv 64 nh])).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 nh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U19 : base_val E (Some 19%nat) = SA) by (cbn [base_val]; rewrite (EL 19%nat 19%bv eq_refl); exact H19).
assert (U9 : base_val E (Some 9%nat) = sp) by (cbn [base_val]; rewrite (EL 9%nat 9%bv eq_refl); exact H9).
assert (U18 : bv_unsigned (ew E 18) = SB) by (rewrite (EL 18%nat 18%bv eq_refl), H18; unfold w64, SHADOW_OFF, SB; apply unsigned_lit_small; lia).
unfold tp_ss4. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold tp_regions4. repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U19.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ SA 48 4 _ nh);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VN].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (HP o Ho).
- apply pairwise_disjoint_of_extents.
  unfold tp_regions4, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U19, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [tp_facts4 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (EL 9%nat 9%bv eq_refl), H9, U18, (EL 19%nat 19%bv eq_refl), H19, E32, unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, TP_PHI in *. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

Lemma top_p2 :
stmt_gtopm_kept -> stmt_live_kept -> stmt_gin_top -> stmt_gout_top ->
stmt_snp_call -> stmt_strlen_call ->
forall cx i W1 c1,
GBASE B ARx MT RP MMAX RG cx -> PD cx i W1 c1 ->
(forall r W2 c2, RGI B PST ARx MT RP MMAX RG cx i 0 r W2 c2 -> SRr SEGS W2 c2 (gPOST B PST ARx MT RP RG cx)) ->
(forall W2 c2, RGE B PST ARx MT RP MMAX RG cx i W2 c2 -> SRr SEGS W2 c2 (gPOST B PST ARx MT RP RG cx)) ->
SRr SEGS W1 c1 (gPOST B PST ARx MT RP RG cx).
Proof.
intros LTK LLK LGI LGO LSC LSL cx i W1 c1 HB HPD KI KE.
destruct HPD as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & e1 & h1 & ev & LB & c1' & O1 & cap1 & out1 & spent &
  -> & HRB & R20 & R21 & R22 & R19 & V88 & HGL & HLS & HTM & HBU).
pose proof HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H18).
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RID & _).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HLS as (L40 & L48 & L56 & L64 & L72).
pose proof HFR as (HFa & HFLa & HF120 & HF16 & HF24 & HF80 & HSV).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (SP1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
pose proof HPRE as (_ & _ & _ & HGP0 & HTP0 & HAS0 & _). pose proof HAS0 as (_ & _ & As3 & As4 & As5 & As6 & _).
fold (gsp0 cx) in As4, As5. rewrite WS in As4.
assert (SPB : alloc_ceiling + 17200 <= gsp0 cx <= 2 ^ 47) by lia.
assert (Hsp32 : gsp1 cx mod 32 = 0) by (rewrite SP1; rewrite Zminus_mod, H32; reflexivity).
destruct (tl2_frm cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof HFapp as HFA. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFA.
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *. rewrite HFa in HFal, HFpres, HFSpres.
pose proof HTM as (Hi & Hlq & Hrel & HGD & Hrly & Hout & Hdone & Hsrc1 & Hdrs & Hgs & Hperm).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HREL0 & _). pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen0 & _).
pose proof Hrly as (RS1 & _ & _ & _ & _ & _ & Rlen & RSG & (tail & _ & _ & Rtab) & Rok & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 RSG) as (HG16 & HG4096 & HGc & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in HGc, HGapp, HGpres.
assert (SRCI : in_img SEGS (rg_src RG)) by (apply (proj1 (RGIMG (rg_src RG) ltac:(unfold rg_rng; right; right; left; lia)))).
assert (SRCI7 : in_img SEGS (rg_src RG + 7)) by (apply (proj1 (RGIMG (rg_src RG + 7) ltac:(unfold rg_rng; right; right; left; lia)))).
pose proof (pa_img_range (rg_src RG) SRCI) as SRCr. pose proof (pa_img_range (rg_src RG + 7) SRCI7) as SRCr7.
set (G0 := gxG0 cx) in *.
set (idv := bv_unsigned (getr (gxregs cx) 10)) in *.
assert (Hshv : shadow_addr F = SB + F / 8) by (unfold shadow_addr, SB; reflexivity).
assert (HF8 : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8b.
(* F is 32-aligned (alx_frames), so its shadow address is 4-aligned *)
assert (Hsh4 : (SB + F / 8) mod 4 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HFal, Z.add_0_r in D.
  assert (F / 8 = 4 * (F / 32)) by (rewrite D at 1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring; apply Z.div_mul; lia).
  assert (SB mod 4 = 0) by reflexivity. pose proof (Z.div_mod SB 4 ltac:(lia)).
  replace (SB + F / 8) with ((SB / 4 + F / 32) * 4) by lia.
  apply Z_mod_mult. }
pose proof (tp_seat2 W1 regs1 m1 G0 idv (gsp1 cx) (shadow_addr F)) as HS.
specialize (HS ltac:(rewrite R22, HH45; reflexivity)
  ltac:(rewrite H9; unfold w64; apply unsigned_lit_small; lia) H18
  ltac:(rewrite R21; unfold w64; apply unsigned_lit_small; rewrite Hshv; unfold SB; lia)
  ltac:(rewrite Hshv; unfold SB; lia) ltac:(rewrite Hshv; exact Hsh4)
  ltac:(rewrite <- RGSRC; lia) ltac:(rewrite <- RGSRC; lia)
  ltac:(rewrite SP1; lia) ltac:(rewrite SP1; lia) Hsp32
  ltac:(unfold G0; lia) ltac:(unfold idv; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 10)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R)
  ltac:(rewrite <- RGSRC; exact RS1) L56 L64 HF80
  ltac:(intros o Ho; exact (proj1 (HFSpres o ltac:(lia))))).

remember (Eimg (Ereg regs1 (tp_extra2 G0 idv))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (tp_extra2 G0 idv)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
clear HE.
assert (U21 : bv_unsigned (ew E 21) = shadow_addr F)
by (rewrite (EEo 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; rewrite Hshv; unfold SB; lia).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W1) m1)) by constructor.
unfold cfg_at. change (w64 (BASE + A_rig_pd)) with (Z_to_bv 64 (BASE + A_rig_pd)).
pose proof HJ as HJ0.
paj_run_tok_x RUN HS HJ SHOK tp_Bspan0.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U21 in Ha.
  left. split; [|lia]. right; right; right. exists 1, fpos. split; [left; reflexivity|].
  right. rewrite HFa. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. lia. }

rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as RGS. cbn [ms_mem restrict] in RGS.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE2 : env_agree 32 (Ereg regs1 (tp_extra2 G0 idv)) Ex)
  by (repeat first [exact HAE | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 20; 21]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
pmkst HS.
prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13.
prreg HS (14%bv : bv 5) N14. prreg HS (1%bv : bv 5) N1. prreg HS (19%bv : bv 5) N19.
assert (ZSv : forall o, 4 <= o < 10 -> val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) (shadow_addr F + o) 1 0).
{ intros o Ho. rewrite <- U21.
  assert (Ho' : o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/ o = 9) by lia.
  destruct Ho' as [-> | [-> | [-> | [-> | [-> | ->]]]]];
  (eapply (field_of_region _ _ 21 _ _ 4 10 4 10 _ 1%N (SLit 0) 0 RGS); [reflexivity | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia]). }
assert (ZS : forall o, 4 <= o < 10 -> aview SEGS (w_H W1) (ms_mem ms1) (shadow_addr F + o) = Some 0)
by (intros o Ho; apply aview_of_val_mem1; [exact (ZSv o Ho) | lia]).
tp_nw HFr1 NW1 (fun a => shadow_addr F + 4 <= a < shadow_addr F + 10) U21.
assert (ROM1 : rom_view SEGS W1 (ms_mem ms1)).
{ intros a Hin.
  assert (HI : 0x10000 <= a < 0x5fb000)
    by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
  rewrite (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 a ltac:(lia) (NW1 a ltac:(rewrite Hshv; unfold SB; lia))).
  exact (HROM1 a Hin). }
eapply (LSC W1 (ms_regs ms1) (ms_mem ms1) (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) fpos
  ly1 S1 _ _ k1
  (Z_to_bv 64 (BASE + 2844)) F (gxID cx) idv (gPOST B PST ARx MT RP RG cx) HJ).
- unfold spZ. rewrite HK by (cbv; tauto). fold (spZ regs1). rewrite Hsp1, SP1. reflexivity.
- pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
  replace (32 * (gsp0 cx / 32)) with ((2 * (gsp0 cx / 32)) * 16) by ring. apply Z_mod_mult.
- rewrite HK by (cbv; tauto). rewrite Hgp1. exact HGP0.
- rewrite HK by (cbv; tauto). rewrite Htp1. exact HTP0.
- exact N1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite N10, (EEo 20%nat 20%bv eq_refl). exact R20.
- rewrite N11. reflexivity.
- change 261%nat with (A_OBJ 20) in N12. rewrite N12, (img_env_atomP E (A_OBJ 20) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). reflexivity.
- change 262%nat with (A_OBJ 21) in N13. rewrite N13, (img_env_atomP E (A_OBJ 21) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). reflexivity.
- rewrite N14, E33. reflexivity.
- unfold idv. rewrite H10. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
- exact RID.
- exact HFa.
- exact ZS.
- exact ROM1.
- intros regs2 mem2 md2 HJ2 HP2 HR2 HPRE2 HKP2 HPS2.
  assert (P2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms1) r)
  by (intros r Hr; exact (tp_pres _ _ _ r HP2 eq_refl Hr)).
  pose proof (tp_seat3 W1 regs2 mem2) as HS3.
  remember (Eimg (Ereg regs2 [])) as E3 eqn:HE3.
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
  assert (HAE3 : env_agree 32 (Ereg regs2 []) E3)
  by (rewrite HE3; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE3 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E3 m = getr regs2 rr)
  by (intros m rr Hm; subst E3; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
  rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  clear HE3.
  assert (SHOK3 : sh_ok SEGS (SOff 18 0) [] E3 (mrestrict (w_H W1) mem2)) by constructor.
  paj_run_tok_x RUN HS3 HJ2 SHOK3 tp_Bspan0. { apply awr_ok_x_nil. }
  rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 20; 21]%bv HS3 HAE3 ltac:(vm_compute; reflexivity)) as HK3.
  cbn [ms_regs restrict] in HK3.
  pmkst HS3.
  prreg HS3 (10%bv : bv 5) Q10. prreg HS3 (1%bv : bv 5) Q1.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem2 a)
  by (intros a Ha; apply (aview_kept_out E3 _ (w_H W1) mem2 (ms_mem ms2) HFr2 a Ha); intros (r & Hin & _); destruct Hin).
  assert (U2s : spZ (ms_regs ms1) = gsp1 cx) by (unfold spZ; rewrite HK by (cbv; tauto); exact Hsp1).
  assert (Hsc1 : forall a, 0 <= a < alloc_ceiling -> ~ (gsp0 cx - 224 - 3 * ESTACK <= a < gsp0 cx - 224)) by (intros a Ha Hs; lia).
  destruct (tp_pre_nz cx) as (PNZ & PL1 & PL2).
  eapply (LSL W1 (ms_regs ms2) (ms_mem ms2) (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) fpos
    ly1 S1 _ _ k1
    (Z_to_bv 64 (BASE + 2852)) F (gpre cx) (gPOST B PST ARx MT RP RG cx) HJ2).
  + unfold spZ. rewrite (HK3 2%bv ltac:(cbv; tauto)). rewrite (tp_pres _ _ 2 2%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)). fold (spZ (ms_regs ms1)). rewrite U2s, SP1. reflexivity.
  + pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
    replace (32 * (gsp0 cx / 32)) with ((2 * (gsp0 cx / 32)) * 16) by ring. apply Z_mod_mult.
  + rewrite (HK3 3%bv ltac:(cbv; tauto)). rewrite (tp_pres _ _ 3 3%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto). rewrite Hgp1. exact HGP0.
  + rewrite (HK3 4%bv ltac:(cbv; tauto)). rewrite (tp_pres _ _ 4 4%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto). rewrite Htp1. exact HTP0.
  + exact Q1.
  + apply ret_ok_codeptr_v; [lia | reflexivity].
  + rewrite Q10, (EE3 20%nat 20%bv eq_refl), (tp_pres _ _ 20 20%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto). exact R20.
  + exact HFa.
  + unfold arm in *. eapply rk_garr8_kv_tp; [exact HPRE2|]. intros b Hb. apply K3. rewrite length_app in Hb. cbn [length] in Hb. lia.
  + exact PNZ.
  + lia.
  + intros o Ho. rewrite K3 by (rewrite Hshv; unfold SB; lia).
    rewrite HKP2; [exact (ZS o Ho) | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; lia | rewrite Hshv; apply Hsc1; unfold SB; lia].
  + intros a Hin.
    assert (HI : 0x10000 <= a < 0x5fb000)
      by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
    rewrite K3 by lia. rewrite HKP2; [exact (ROM1 a Hin) | lia | | apply Hsc1; lia].
    intros Hb. apply (HFni a ltac:(lia)). destruct Hin as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
  + intros regs4 mem4 md4 HJ4 HP4 HR4 HKP4 HPS4.
    assert (G19 : getr regs4 19 = getr (ms_regs ms1) 19).
    { rewrite (tp_pres _ _ 19 19%bv HP4 eq_refl ltac:(unfold acallee_saved; lia)), (HK3 19%bv ltac:(cbv; tauto)).
      exact (tp_pres _ _ 19 19%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)). }
    assert (GR : forall (r : bv 5) n, bv_unsigned r = n -> acallee_saved n -> In r [2; 3; 4; 8; 9; 18; 19; 20; 21]%bv ->
      getr regs4 r = getr (ms_regs ms1) r).
    { intros r n Hn Hc Hin. rewrite (tp_pres _ _ n r HP4 Hn Hc), (HK3 r Hin). exact (tp_pres _ _ n r HP2 Hn Hc). }
    set (SA := G0 + AENT * Z.of_nat i) in *.
    assert (U19 : bv_unsigned (getr regs4 19) = SA).
    { rewrite G19, N19, (EEo 19%nat 19%bv eq_refl), E32, R19. unfold w64.
      rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      unfold SA, AENT. rewrite (Z.mod_small (56 * Z.of_nat i)), (Z.mod_small G0), Z.mod_small by lia. lia. }
    assert (KEEP14 : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
      aview SEGS (w_H W1) mem4 a = aview SEGS (w_H W1) m1 a).
    { intros a Ha Hnf.
      assert (Nsh : ~ (shadow_addr F + 4 <= a < shadow_addr F + 10)).
      { intros Hs. apply Hnf. exists 1, fpos. split; [left; reflexivity|]. right. rewrite HFa. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1 / 8) with 16. lia. }
      assert (Nbf : ~ (F + 32 <= a < F + 80)).
      { intros Hs. apply Hnf. exists 1, fpos. split; [left; reflexivity|]. left. rewrite HFa. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1) with 128. lia. }
      rewrite HKP4 by lia. rewrite K3 by lia. rewrite HKP2 by lia.
      exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 a ltac:(lia) (NW1 a Nsh)). }
    assert (PRES14 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mem4 a).
    { intros a Hp. apply HPS4. eapply apresent_grows; [exact HG2|]. apply HPS2. eapply apresent_grows; [exact HG1 | exact Hp]. }
    pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 mem4 fpos HB HAR1 Hfin KEEP14 PRES14 HTM) as HTM4.
    pose proof HTM4 as (_ & _ & _ & _ & Hrly4 & _).
    pose proof Hrly4 as (_ & _ & _ & _ & _ & _ & _ & _ & (tail4 & _ & _ & Rtab4) & Rok4 & _).
    assert (HLmq : length (map fst qd) = i) by (rewrite length_map; exact Hlq).
    assert (Hok4 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (map fst qd ++ e1 :: skipn (S i) (gxes cx))).
    { eapply Forall_impl; [|exact Rok4]. intros e (_ & _ & Q1' & Q2' & _). split; assumption. }
    assert (Hnth : nth i (map fst qd ++ e1 :: skipn (S i) (gxes cx)) relay_remove_b_c.no_entry = e1).
    { rewrite app_nth2 by lia. rewrite HLmq, Nat.sub_diag. reflexivity. }
    assert (HLtab : (i < length (map fst qd ++ e1 :: skipn (S i) (gxes cx)))%nat) by (rewrite length_app, HLmq; cbn [length]; lia).
    pose proof (tp_table_entry _ _ _ _ i Rtab4 Hok4 HLtab) as HTE4. rewrite Hnth in HTE4.
    assert (HEOK4 : aentry_ok B ly1 S1 W1 mem4 e1).
    { rewrite Forall_forall in Rok4. apply Rok4. apply in_or_app. right. left. reflexivity. }
    pose proof HEOK4 as (_ & _ & Hp14 & _ & _ & _ & _ & _ & _ & _ & Hnh26 & _).
    assert (Hnh0 : 0 <= re_nheld e1) by (unfold re_nheld; lia).
    pose proof (tp_entry_nheld _ _ _ HTE4 Hp14 ltac:(lia)) as VN4.
    fold SA in VN4.
    assert (HSAb : 4096 <= SA /\ SA + 56 <= alloc_ceiling) by (unfold SA, AENT; lia).
    pose proof (tj_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
    assert (U9r : bv_unsigned (getr regs4 9) = gsp1 cx).
    { rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto). rewrite H9.
      unfold w64. apply unsigned_lit_small. lia. }
    assert (R18r : getr regs4 18 = w64 SHADOW_OFF).
    { rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto). exact H18. }
    assert (HSAm : SA mod 8 = 0).
    { unfold SA, AENT. pose proof (Z.div_mod G0 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
      replace (G0 + 56 * Z.of_nat i) with ((2 * (G0 / 16) + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
    pose proof (tp_seat4 W1 regs4 mem4 SA (gsp1 cx) (re_nheld e1) U19 U9r R18r) as HS4.
    specialize (HS4 ltac:(unfold SA, AENT; lia) ltac:(unfold SA, AENT; lia) HSAm ltac:(lia) ltac:(lia) Hsp32 ltac:(lia)
      ltac:(unfold arm in VN4; exact VN4)
      ltac:(intros o Ho; eapply tj_pres; [exact HJ4 | rewrite WS; lia])).
    remember (Eimg (Ereg regs4 [Z_to_bv 64 (re_nheld e1)])) as E4 eqn:HE4.
    assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
    assert (HAE4 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) E4)
    by (rewrite HE4; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE4 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E4 m = getr regs4 rr)
    by (intros m rr Hm; subst E4; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
    rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
    assert (E4_32 : ew E4 32 = Z_to_bv 64 (re_nheld e1)) by (subst E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
    clear HE4.
    assert (HBx4 : U E4 (SOff 18 0) = SHADOW_OFF) by (rewrite (U_atom E4 18 SHADOW_OFF ltac:(rewrite (EE4 18%nat 18%bv eq_refl); exact R18r)) by (unfold SHADOW_OFF; lia); reflexivity).
    assert (SHOK4 : sh_ok SEGS (SOff 18 0) tp_SH4 E4 (mrestrict (w_H W1) mem4)).
    { constructor; [|constructor].
      eapply shent_ok_of_range.
      + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 _ W1 mem4 _ G0 ATABLE (SA + 48) 4 HAR4 RSG);
        [unfold SA, AENT; lia | rewrite RQT; unfold SA, AENT; lia].
      + exact HBx4.
      + rewrite (U_atom E4 19 SA) by (first [rewrite (EE4 19%nat 19%bv eq_refl); rewrite <- U19; symmetry; apply Z_to_bv_bv_unsigned | unfold SA, AENT; lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. pose proof HGapp as HGA. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. unfold SA, AENT in *. lia. }
    pose proof HJ4 as HJ40.
    paj_run_tok_x RUN HS4 HJ4 SHOK4 tp_Bspan.
    { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite (EE4 9%nat 9%bv eq_refl), U9r in Ha.
      left. split; [left; rewrite SP1, WS in *; lia | lia]. }
    rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
    rename w into w5a, w0 into w5b.
    assert (E5_32 : sv_denot (ewset (ewset E4 512 w5a) 513 w5b) (SOff 32 0) = Z_to_bv 64 (re_nheld e1))
    by (cbn [sv_denot]; rewrite !ew_ewset_other, E4_32, Z.add_0_r, Z_to_bv_bv_unsigned by lia; reflexivity).
    psrr_branch_tok RUN BR HS4 SHOK4 tp_Bspan.
    * rewrite (tp_branch_ge (ewset (ewset E4 512 w5a) 513 w5b) (SLit 0) (SOff 32 0) 0 (re_nheld e1) eq_refl E5_32 ltac:(lia) ltac:(lia)) in Hc.
      assert (Hnh00 : re_nheld e1 <= 0) by (destruct (Z.ltb_spec 0 (re_nheld e1)); [discriminate Hc | lia]).
      paj_run_to_tok_x RUNTO HS4 HJ4 SHOK4 tp_Bspan (AF_fr_relay_instance_gone + 0x318).
      { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
        apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite !ew_ewset_other, (EE4 9%nat 9%bv eq_refl), U9r in Ha by lia.
        left. split; [left; rewrite SP1, WS in *; lia | lia]. }
      rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
      assert (U9E4 : bv_unsigned (ew E4 9) = gsp1 cx) by (rewrite (EE4 9%nat 9%bv eq_refl); exact U9r).
      assert (U9E5 : bv_unsigned (ew (ewset (ewset E4 512 w5a) 513 w5b) 9) = gsp1 cx) by (rewrite !ew_ewset_other by lia; exact U9E4).
      tp_nw HFr5 NW5 (fun a => gsp1 cx + 32 <= a < gsp1 cx + 40) U9E4.
      tp_nw HFr6 NW6 (fun a => gsp1 cx + 32 <= a < gsp1 cx + 40) U9E5.
      assert (K56 : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx + 32 <= a < gsp1 cx + 40) ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) mem4 a)
      by (intros a Ha Na; exact (tp_kept2 _ _ _ _ _ _ _ _ a HFr5 HFr6 Ha (NW5 a Na) (NW6 a Na))).
      set (PF := fun a => (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (F + 32 <= a < F + 80) \/
        (shadow_addr F + 4 <= a < shadow_addr F + 10) \/ (gsp1 cx + 32 <= a < gsp1 cx + 40)).
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ PF a -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Na. unfold PF in Na.
        rewrite K56 by tauto. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
        exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha (NW1 a ltac:(tauto))). }
      assert (PRESF : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms6) a).
      { intros a Hp. eapply apresent_grows; [exact HG6|]. eapply apresent_grows; [exact HG5|]. apply PRES14. exact Hp. }
      assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Hnf. apply KEEPF; [lia|]. unfold PF. intros [X | [X | [X | X]]]; [lia | | | lia]; apply Hnf; exists 1, fpos;
        (split; [left; reflexivity|]); rewrite HFa; unfold in_zr; cbn [fst snd];
        [left; change (fs_frame_bytes 1) with 128; lia | right; change (fs_frame_bytes 1 / 8) with 16; lia]. }
      pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 (ms_mem ms6) fpos HB HAR1 Hfin KEEPL PRESF HTM) as HTM6.
      destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms6) (with_vm_backing (m_vm_lazy md4) mat6 md4) PF HB HJ0 HROM1 HPK HFR HLK HLS HJ4)
        as [HGL6 HLS6].
      { intros a Ha. unfold PF in Ha. rewrite SP1 in *. lia. }
      { exact KEEPF. }
      { exact PRESF. }
      assert (V88F : val_mem SEGS (arm W1 (ms_mem ms6)) (gsp1 cx + 88) 8 (Z.of_nat i)).
      { unfold arm in *. eapply val_mem_kept; [|exact V88]. intros kk Hkk. apply KEEPF; [lia|]. unfold PF.
        rewrite Hshv. unfold SB. lia. }
      lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => assert (HAE6 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) Ex)
        by (repeat first [exact HAE4 | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs4 _ [2; 3; 4; 8; 9; 18; 20]%bv HS4 HAE6 ltac:(vm_compute; reflexivity)) as HK6.
      cbn [ms_regs restrict] in HK6.
      pmkst HS4.
      destruct (LGO cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent ly1 S1 W1 (ms_mem ms6) HB HTM6 HBU Hnh00) as (qd' & HGO').
      apply KE. unfold RGE.
      exists (ms_regs ms6), ly1, S1, (ms_mem ms6), (with_vm_backing (m_vm_lazy md4) mat6 md4), k1, F, FL, qd', c1', O1, cap1, out1, spent.
      split; [unfold cfg_at, A_rig_step; reflexivity|].
      split.
      { unfold gregs_base, spZ. rewrite !HK6 by (cbv; tauto).
        rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite !HK by (cbv; tauto). exact HRB. }
      split; [rewrite HK6 by (cbv; tauto); rewrite (GR 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto); exact R20|].
      split; [exact V88F|]. split; [exact Hi|]. split; [exact HGL6|]. split; [exact HLS6 | exact HGO'].
    * rewrite (tp_branch_ge (ewset (ewset E4 512 w5a) 513 w5b) (SLit 0) (SOff 32 0) 0 (re_nheld e1) eq_refl E5_32 ltac:(lia) ltac:(lia)) in Hc.
      assert (Hnh01 : 0 < re_nheld e1) by (destruct (Z.ltb_spec 0 (re_nheld e1)); [lia | discriminate Hc]).
      paj_run_to_tok_x RUNTO HS4 HJ4 SHOK4 tp_Bspan (AF_fr_relay_instance_gone + 0x224).
      { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
        apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite !ew_ewset_other, (EE4 9%nat 9%bv eq_refl), U9r in Ha by lia.
        left. split; [left; rewrite SP1, WS in *; lia | lia]. }
      rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
      assert (U9E4 : bv_unsigned (ew E4 9) = gsp1 cx) by (rewrite (EE4 9%nat 9%bv eq_refl); exact U9r).
      assert (U9E5 : bv_unsigned (ew (ewset (ewset E4 512 w5a) 513 w5b) 9) = gsp1 cx) by (rewrite !ew_ewset_other by lia; exact U9E4).
      tp_nw HFr5 NW5 (fun a => gsp1 cx + 32 <= a < gsp1 cx + 40) U9E4.
      tp_nw HFr6 NW6 (fun a => gsp1 cx + 32 <= a < gsp1 cx + 40) U9E5.
      assert (K56 : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx + 32 <= a < gsp1 cx + 40) ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) mem4 a)
      by (intros a Ha Na; exact (tp_kept2 _ _ _ _ _ _ _ _ a HFr5 HFr6 Ha (NW5 a Na) (NW6 a Na))).
      set (PF := fun a => (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (F + 32 <= a < F + 80) \/
        (shadow_addr F + 4 <= a < shadow_addr F + 10) \/ (gsp1 cx + 32 <= a < gsp1 cx + 40)).
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ PF a -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Na. unfold PF in Na.
        rewrite K56 by tauto. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
        exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha (NW1 a ltac:(tauto))). }
      assert (PRESF : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms6) a).
      { intros a Hp. eapply apresent_grows; [exact HG6|]. eapply apresent_grows; [exact HG5|]. apply PRES14. exact Hp. }
      assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Hnf. apply KEEPF; [lia|]. unfold PF. intros [X | [X | [X | X]]]; [lia | | | lia]; apply Hnf; exists 1, fpos;
        (split; [left; reflexivity|]); rewrite HFa; unfold in_zr; cbn [fst snd];
        [left; change (fs_frame_bytes 1) with 128; lia | right; change (fs_frame_bytes 1 / 8) with 16; lia]. }
      pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 (ms_mem ms6) fpos HB HAR1 Hfin KEEPL PRESF HTM) as HTM6.
      destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms6) (with_vm_backing (m_vm_lazy md4) mat6 md4) PF HB HJ0 HROM1 HPK HFR HLK HLS HJ4)
        as [HGL6 HLS6].
      { intros a Ha. unfold PF in Ha. rewrite SP1 in *. lia. }
      { exact KEEPF. }
      { exact PRESF. }
      assert (V88F : val_mem SEGS (arm W1 (ms_mem ms6)) (gsp1 cx + 88) 8 (Z.of_nat i)).
      { unfold arm in *. eapply val_mem_kept; [|exact V88]. intros kk Hkk. apply KEEPF; [lia|]. unfold PF.
        rewrite Hshv. unfold SB. lia. }
      lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => assert (HAE6 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) Ex)
        by (repeat first [exact HAE4 | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs4 _ [2; 3; 4; 8; 9; 18; 20]%bv HS4 HAE6 ltac:(vm_compute; reflexivity)) as HK6.
      cbn [ms_regs restrict] in HK6.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS4 eq_refl) as RG6. cbn [ms_mem restrict] in RG6.
      prreg HS4 (19%bv : bv 5) F19. prreg HS4 (21%bv : bv 5) F21. prreg HS4 (23%bv : bv 5) F23. prreg HS4 (22%bv : bv 5) F22.
      prreg HS4 (24%bv : bv 5) F24. prreg HS4 (25%bv : bv 5) F25. prreg HS4 (27%bv : bv 5) F27.
      pmkst HS4.
      assert (E19' : bv_unsigned (ew (ewset (ewset E4 512 w5a) 513 w5b) 19) = SA)
        by (rewrite !ew_ewset_other, (EE4 19%nat 19%bv eq_refl) by lia; exact U19).
      assert (E18' : ew (ewset (ewset E4 512 w5a) 513 w5b) 18 = w64 SHADOW_OFF)
        by (rewrite !ew_ewset_other, (EE4 18%nat 18%bv eq_refl) by lia; exact R18r).
      assert (E10' : ew (ewset (ewset E4 512 w5a) 513 w5b) 10 = w64 (Z.of_nat (length (gpre cx))))
        by (rewrite !ew_ewset_other, (EE4 10%nat 10%bv eq_refl) by lia; exact HR4).
      set (r := (Z.to_nat (re_nheld e1) - 1)%nat).
      assert (HNHr : re_nheld e1 = Z.of_nat (S r)) by (unfold r; lia).
      assert (HPREF : garr8 SEGS (arm W1 (ms_mem ms6)) (F + 32) (gpre cx ++ [0])).
      { unfold arm in *. eapply rk_garr8_kv_tp; [exact HPRE2|]. intros b Hb. rewrite length_app in Hb. cbn [length] in Hb.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). apply K3. lia. }
      assert (HZSF : garr8 SEGS (arm W1 (ms_mem ms6)) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]).
      { intros j Hj. cbn [length] in Hj. split; [|destruct j as [|[|[|[|[|[|j]]]]]]; cbn; lia].
        replace (nth j [0; 0; 0; 0; 0; 0] 0) with 0 by (destruct j as [|[|[|[|[|[|j]]]]]]; cbn; lia).
        replace (shadow_addr F + 4 + Z.of_nat j) with (shadow_addr F + (4 + Z.of_nat j)) by lia.
        unfold arm. eapply val_mem_kept; [|exact (ZSv (4 + Z.of_nat j) ltac:(lia))].
        intros kk Hkk. cbn in Hkk. replace (shadow_addr F + (4 + Z.of_nat j) + kk) with (shadow_addr F + (4 + Z.of_nat j)) by lia.
        rewrite K56 by (rewrite Hshv; unfold SB; lia). rewrite HKP4 by (rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia).
        rewrite K3 by (rewrite Hshv; unfold SB; lia).
        rewrite HKP2; [reflexivity | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia]. }
      destruct (LGI cx i r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent ly1 S1 W1 (ms_mem ms6) HB HTM6 HBU HNHr HPREF HZSF)
        as (ks & f & HGIN).
      apply (KI r). unfold RGI.
      exists (ms_regs ms6), ly1, S1, (ms_mem ms6), (with_vm_backing (m_vm_lazy md4) mat6 md4), k1, F, FL, qd, cB, OB, capB, e1, h1, ev, LB,
        c1', O1, cap1, ks, [], f, c1', O1, cap1, out1, spent.
      split; [unfold cfg_at, A_rig_inner; reflexivity|].
      split.
      { unfold gregs_base, spZ. rewrite !HK6 by (cbv; tauto).
        rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite !HK by (cbv; tauto). exact HRB. }
      split; [rewrite F19; reflexivity|].
      split; [rewrite HK6 by (cbv; tauto); rewrite (GR 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto); exact R20|].
      split; [rewrite F21; reflexivity|].
      split; [rewrite F23, (EE4 19%nat 19%bv eq_refl), U19; reflexivity|].
      split; [rewrite F22, (EE4 19%nat 19%bv eq_refl), U19; apply (tp_sh_den2 (SA + 48)); [rewrite (EE4 18%nat 18%bv eq_refl); exact R18r | pose proof C1; lia]|].
      split; [rewrite F24, (EE4 10%nat 10%bv eq_refl); exact HR4|].
      split; [rewrite F25, (EE4 19%nat 19%bv eq_refl), U19; reflexivity|].
      split; [rewrite F27, (EE4 19%nat 19%bv eq_refl), U19; apply (tp_sh_den2 (SA + 40)); [rewrite (EE4 18%nat 18%bv eq_refl); exact R18r | pose proof C1; lia]|].
      split.
      { replace ((gSA cx i + 48) mod 8 + 3) with 3.
        2:{ change (gSA cx i) with SA. rewrite Zplus_mod, HSAm. reflexivity. }
        unfold arm. replace (gsp1 cx + 32) with (bv_unsigned (ew (ewset (ewset E4 512 w5a) 513 w5b) 9) + 32) by (rewrite U9E5; reflexivity).
        eapply (field_of_region _ _ 9 _ _ 32 40 32 40 32 8%N (SLit 3) 3 RG6); [reflexivity | left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
      split; [exact V88F|]. split; [exact HGL6|]. split; [exact HLS6 | exact HGIN].
Qed.

(* ---- TOP: rig_top_stmt from the two halves of the walk (top_p1: 0x82d98 -> drain -> 0x82dd0; top_p2: 0x82dd0 ->
   snprintf, strlen, the nheld test -> RGI / RGE) and the lemma tracks above, given drain's count lemma. ---- *)
Lemma rig_top_of_cnt : stmt_dr_cnt -> rig_top_stmt B PST ARx MT RP MMAX RG.
Proof.
intros LDC. unfold rig_top_stmt. intros cx i W1 c1 HB HO KI KE.
exact (top_p1 gout_kept top_rep_closed top_budget live_kept top_drain_pre dr_inv_of top_room dr_fp_in top_rep_open dr_bytes
  LDC live_drain cx i W1 c1 HB HO
  (fun W2 c2 HPD => top_p2 gtopm_kept live_kept gin_top gout_top snp_call strlen_call cx i W2 c2 HB HPD KI KE)).
Qed.

(* TOP, with drain's count growth from the RR family's model lemma (lib/A/W_rr_m_dcnt.v rmc_dr_cnt) *)
Theorem rig_top_proof : rig_top_stmt B PST ARx MT RP MMAX RG.
Proof. exact (rig_top_of_cnt W_rr_m_dcnt.rmc_dr_cnt). Qed.

(* ======================================================================================================
   ROUTE R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0; a Theorem Labs lane's G8 split, rig_top): segment TOP at a world relation R, concluding
   W_relay_instance_gone_cx.v's rig_top_stmt_xR.  Every name X_xR below is X above with the journal ajournal_gx_x ->
   ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, GLIVE / RGO / RGI / RGE / gPOST -> the cx file's _xR twins, the runs on
   the G chain (paj_run_x_xG / paj_run_to_x_xG, paj_run_tok_xR / paj_run_to_tok_xR, paj_branch_xR), the drain call by
   W_gestures_end.v gse_callS_xR at drain's R spec (W_contract_xR.v dr_spec_xR), snprintf / strlen by W_sites_x.v
   aj_gx_entry_at_xR / aj_strlen_gx_at_xR (their contracts stay strict); every other token is the strict text's.  The
   lemma tracks that name no journal and no step relation are used as they are.  One step differs: tc_o_KG_xR carries an
   image byte's writability by tc_wr_img_xR (no world hides an image byte), not by the journal's wle clause.  TOP calls
   no allocator rule, so the Section takes no RO / HA premise.
   ====================================================================================================== *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* drain's R spec (the cx file's Section wR DRAIN_R, its text) *)
Hypothesis DRAIN_R : W_contract_xR.dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
(* W_rig_top.v:1300 stmt_top_rep_open at R *)
Definition stmt_top_rep_open_xR : Prop :=
forall cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 sp1 ly2 S2 Hp2 W2 m2 md2 k2,
let e := gnth cx i in let h := fst (ghj cx i) in
GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof e = 0 ->
GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x sp1 (dr_fp (gSA cx i) e h cap2 out2)
  ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2 ->
alloc_ceiling <= sp1 - DRAIN_STK_x ->
DRK cx i c2 O2 cap2 out2 ly1 S1 W1 m1 ly2 S2 W2 m2 ->
exists e1 h1 ev LB out1,
let no2 := Z.of_nat (length O2) in
let live := dr_live c2 h in
let c1 := dr_ctl c2 h ev in
let O1 := if live then O2 ++ LB else O2 in
let cap1 := if live then drain_b_c.ds_ocap (dr_fin c2 (gxmx cx) no2 cap2 e h) else cap2 in
GTOPM cx i qd c2 O2 cap2 e1 h1 ev LB c1 O1 cap1 out1 ly2 S2 W2 m2.
(* W_rig_top.v:1373 stmt_live_kept at R *)
Definition stmt_live_kept_xR : Prop :=
forall cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 Hp2 m2 md2 (P : Z -> Prop),
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> g_lslots RG cx F W1 m1 ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp2 W1 m2 md2 k1 ->
(forall a, P a -> (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (gsp1 cx + 32 <= a < gsp1 cx + 40) \/
   (gsp1 cx + 88 <= a < gsp1 cx + 96) \/ (F + 32 <= a < F + 80) \/ (shadow_addr F <= a < shadow_addr F + 16)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
GLIVE_xR B PST ARx RG R cx F FL ly1 S1 W1 m2 md2 k1 /\ g_lslots RG cx F W1 m2.
(* W_rig_top.v:1391 stmt_live_drain at R *)
Definition stmt_live_drain_xR : Prop :=
forall cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 SA e h cap out ly2 S2 Hp2 W2 m2 md2 k2 Hp3 k3,
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> g_lslots RG cx F W1 m1 ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (gsp1 cx) (dr_fp SA e h cap out)
  ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2 ->
(forall a, inFP (dr_fp SA e h cap out) a -> exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) ->
apres_kept B W1 m1 W2 m2 ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly2 S2 Hp3 W2 m2 md2 k3 ->
GLIVE_xR B PST ARx RG R cx F FL ly2 S2 W2 m2 md2 k3 /\ g_lslots RG cx F W2 m2.
(* W_rig_top.v:1430 stmt_snp_call at R *)
Definition stmt_snp_call_xR : Prop :=
forall W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F id idv (Post : world SEGS -> config -> Prop),
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (F + 32) -> getr regsT 11 = w64 48 -> getr regsT 12 = w64 (VAL (A_OBJ 20)) ->
getr regsT 13 = w64 (VAL (A_OBJ 21)) -> getr regsT 14 = w64 idv -> idv mod 2 ^ 32 = id mod 2 ^ 32 -> - 2 ^ 31 <= id < 2 ^ 31 ->
frame_addr lyc 1 fpos = F ->
(forall o, 4 <= o < 10 -> aview SEGS (w_H W) memT (shadow_addr F + o) = Some 0) ->
rom_view SEGS W memT ->
(forall regs2 mem2 md2,
   ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W mem2 md2 k ->
   aregs_preserved regsT regs2 ->
   getr regs2 10 = w64 (Z.of_nat (length (relay_instance_gone_b_c.instance_prefix id))) ->
   garr8 SEGS (arm W mem2) (F + 32) (relay_instance_gone_b_c.instance_prefix id ++ [0]) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 80) -> ~ (sp0 - 224 - 3 * ESTACK <= a < sp0 - 224) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
   YA0nH.SRrG SEGS R W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Post) ->
YA0nH.SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_snprintf)) memT (seg_rom SEGS)) mdc) Post.
(* W_rig_top.v:1452 stmt_strlen_call at R *)
Definition stmt_strlen_call_xR : Prop :=
forall W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F (pre : list Z) (Post : world SEGS -> config -> Prop),
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (F + 32) -> frame_addr lyc 1 fpos = F ->
garr8 SEGS (arm W memT) (F + 32) (pre ++ [0]) -> ~ In 0 pre -> (length pre <= 47)%nat ->
(forall o, 4 <= o < 10 -> aview SEGS (w_H W) memT (shadow_addr F + o) = Some 0) ->
rom_view SEGS W memT ->
(forall regs2 mem2 md2,
   ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W mem2 md2 k ->
   aregs_preserved regsT regs2 -> getr regs2 10 = w64 (Z.of_nat (length pre)) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 224 - 2 * ESTACK <= a < sp0 - 224) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
   YA0nH.SRrG SEGS R W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Post) ->
YA0nH.SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_strlen)) memT (seg_rom SEGS)) mdc) Post.
(* W_rig_top.v:1475 tp_ly_top at R *)
Lemma tp_ly_top_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* W_rig_top.v:1483 tj_AR at R *)
Lemma tj_AR_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ARx ly' S' Hp' W' mem' md'.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
(* W_rig_top.v:1491 tj_pres at R *)
Lemma tj_pres_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & _) & _) a Ha.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.
(* W_rig_top.v:1845 tc_wr_kept for an image byte, with no hsub: no world hides an image byte (W_journal.v
   hidden_not_img), so a kept presence keeps writability across any world step *)
Lemma tc_wr_img_xR : forall (W W' : world SEGS) (m m' : word -> option byte) a,
  in_img SEGS a -> (apresent (w_H W) m a -> apresent (w_H W') m' a) ->
  writable_at SEGS (arm W m) a -> writable_at SEGS (arm W' m') a.
Proof.
intros W W' m m' a Hi Hp Hw. pose proof (pa_img_range a Hi) as HR.
assert (HX : in_img SEGS (bv_unsigned (Z_to_bv 64 a))) by (rewrite unsigned_lit_small by lia; exact Hi).
pose proof (hidden_not_img SEGS W (Z_to_bv 64 a) HX) as E.
pose proof (hidden_not_img SEGS W' (Z_to_bv 64 a) HX) as E'.
unfold arm, writable_at, wview, mrestrict in *. revert Hw. rewrite E, E'.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; intros Hw.
- destruct (Hp (conj E (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* W_rig_top.v:2236 Section tc_open at R *)
Section tc_open_xR.
Variables (cx : gcx) (i : nat) (qd : list (rentry * hsrc)) (c2 : ctl) (O2 : list byte) (cap2 out2 spent : Z)
  (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (sp1 : Z)
  (ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS) (m2 : word -> option byte) (md2 : Model) (k2 : Z)
  (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) (rest : list (Z * Z)).
Local Notation oE := (gnth cx i).
Local Notation oH := (fst (ghj cx i)).
Local Notation oJ := (snd (ghj cx i)).
Local Notation oSA := (gSA cx i).
Local Notation ocap := (if dr_live c2 (fst (ghj cx i))
  then drain_b_c.ds_ocap (dr_fin c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i))) else cap2).
Local Notation oA := (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2).
Local Notation oXt := (concat (map aentry_blks (map fst qd)) ++ concat (map aentry_blks (skipn (S i) (gxes cx))) ++
  gdone_srcs (firstn i (gps cx)) qd ++ rig_srcs (skipn (S i) (gps cx)) ++ gxrest cx).
Local Notation oX := ((gxG0 cx, ATABLE) :: oXt).
Hypothesis HB : GBASE B ARx MT RP MMAX RG cx.
Hypothesis Hi : (i < length (gxes cx))%nat.
Hypothesis Heof : re_eof (gnth cx i) = 0.
Hypothesis HG : GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
Hypothesis HAR1 : ARx ly1 S1 Hp1 W1 m1 md1.
Hypothesis HJ : ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x sp1
  (dr_fp (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2) ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2.
Hypothesis D1 : apres_kept B W1 m1 W2 m2.
Hypothesis D3 : Permutation (ablocks B ly1 S1) (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2 ++ rest).
Hypothesis D4 : Permutation (ablocks B ly2 S2) (aentry_blks e' ++ asrc_blks h' ++ aout_blks ocap out' ++ rest).
Hypothesis D5 : garr8 SEGS (arm W2 m2) (gSA cx i) (bzs (entry_bytes e')).
Hypothesis D6 : aentry_ok B ly2 S2 W2 m2 e'.
Hypothesis D7 : dr_rel c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i)) e' h' LB.
Hypothesis D8 : asrc_at B ly2 S2 W2 m2 (gslot RG cx i) h'.
Hypothesis D9 : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (gslot RG cx i <= a < gslot RG cx i + ASRC) ->
  abyte_kept W1 m1 W2 m2 a.
Hypothesis D10 : aout_at B RG ly2 S2 W2 m2 (dr_ctl c2 (fst (ghj cx i)) ev')
  (if dr_live c2 (fst (ghj cx i)) then O2 ++ LB else O2) (gxmx cx)
  (if dr_live c2 (fst (ghj cx i)) then Z.of_nat (length O2) + dr_tot (fst (ghj cx i)) else Z.of_nat (length O2)) ocap out'.
Lemma tc_o_eo_xR : (re_eof (gnth cx i) =? 0) = true.
Proof. apply Z.eqb_eq. exact Heof. Qed.
Lemma tc_o_len_xR : length (gxhs cx) = length (gxes cx).
Proof. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _). exact HLEN. Qed.
Lemma tc_o_fd_xR : re_fd e' = re_fd (gnth cx i) /\ hs_fd h' = hs_fd (fst (ghj cx i)).
Proof.
pose proof D7 as D. unfold dr_rel in D. cbv zeta in D.
destruct D as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F13 & _). exact (conj F1 F13).
Qed.
Lemma tc_o_AR2_xR : ARx ly2 S2 Hp2 W2 m2 md2.
Proof. exact (tj_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). Qed.
Lemma tc_o_P1_xR : Permutation (ablocks B ly1 S1) (oA ++ oX).
Proof.
destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & Hperm & _).
rewrite (tc_skipn_es cx i Hi), (tc_skipn_gps cx i tc_o_len_xR Hi), tc_rig_srcs_cons in Hperm.
cbn [fst snd] in Hperm. rewrite tc_o_eo_xR in Hperm. cbv beta iota in Hperm.
eapply Permutation_trans; [exact Hperm|].
rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.
Lemma tc_o_P2_xR : Permutation (ablocks B ly1 S1) (oA ++ rest).
Proof. rewrite <- !app_assoc. exact D3. Qed.
Lemma tc_o_PX_xR : Permutation oX rest.
Proof. apply (Permutation_app_inv_l oA). exact (Permutation_trans (Permutation_sym tc_o_P1_xR) tc_o_P2_xR). Qed.
Lemma tc_o_ND_xR : List.NoDup (oA ++ oX).
Proof. exact (Permutation_NoDup tc_o_P1_xR (tj_nodup _ _ _ _ _ _ HAR1)). Qed.
Lemma tc_o_inX_xR : forall b, In b oX -> In b (ablocks B ly1 S1) /\ In b (ablocks B ly2 S2) /\ ~ In b oA.
Proof.
intros b Hb. split; [apply (Permutation_in _ (Permutation_sym tc_o_P1_xR)); apply in_or_app; right; exact Hb|].
split.
- apply (Permutation_in _ (Permutation_sym D4)). apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
  exact (Permutation_in _ tc_o_PX_xR Hb).
- intros HA. exact (tc_nodup_disj _ _ b tc_o_ND_xR HA Hb).
Qed.
Lemma tc_o_inA_xR : forall c, In c oA -> In c (ablocks B ly1 S1).
Proof. intros c Hc. apply (Permutation_in _ (Permutation_sym tc_o_P1_xR)). apply in_or_app. left. exact Hc. Qed.
Lemma tc_o_table_xR : In (gxG0 cx, ATABLE) (ablocks B ly1 S1) /\ gxG0 cx <= oSA /\ oSA + AENT <= gxG0 cx + ATABLE.
Proof.
destruct HG as (_ & Hlq & _ & Hrly & _). pose proof Hrly as (_ & _ & _ & _ & _ & _ & Hl16 & HGin & _).
split; [exact HGin|].
rewrite length_app, length_map, length_skipn, Hlq in Hl16. unfold gSA, AENT, ATABLE. lia.
Qed.
Lemma tc_o_KB_xR : forall b a, In b oX -> fst b <= a < fst b + req_size (snd b) -> ~ (oSA <= a < oSA + AENT) ->
  abyte_kept W1 m1 W2 m2 a.
Proof.
intros [p n] a Hb Ha Hsa. destruct (tc_o_inX_xR _ Hb) as (H1 & H2 & HnA). cbn [fst snd] in Ha.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n tc_o_AR2_xR H2) as (_ & Hp4 & Hpc & _ & Hpo & _).
pose proof asan_consts as (C1 & _).
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
split.
- replace a with (p + (a - p)) by lia. rewrite (F2 p n (a - p) H1 H2 ltac:(lia)).
  + replace (p + (a - p)) with a by lia. apply Hag. rewrite unsigned_lit_small by lia. intros HGa.
    assert (Hgr : inG (G_RIG B RG) a) by (unfold G_RIG, inG; apply Exists_cons_tl; exact HGa).
    refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a tc_o_AR2_xR _) (proj1 (HGRIG a Hgr))).
    left. exists p, n. split; [exact H2 | lia].
  + replace (p + (a - p)) with a by lia. intros (r & Hr & Hra). unfold dr_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | Hr]; [cbn [fst snd] in Hra; lia|].
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hc). cbn [fst snd] in Hra.
    assert (Hne : (p, n) <> (q, m)) by (intros Heq; rewrite Heq in HnA; exact (HnA Hc)).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ p n q m HAR1 H1 (tc_o_inA_xR _ Hc) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- intros _. apply apresent_writable. exact (proj1 (Hpo a ltac:(lia))).
Qed.
Lemma tc_o_KBt_xR : forall b a, In b oXt -> fst b <= a < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros b a Hb Ha. apply (tc_o_KB_xR b a (or_intror Hb) Ha).
destruct tc_o_table_xR as (HT & HS1 & HS2).
assert (HbX : In b oX) by (right; exact Hb).
pose proof (proj1 (tc_o_inX_xR b HbX)) as Hb1.
assert (Hne : b <> (gxG0 cx, ATABLE)).
{ intros ->. pose proof (NoDup_app_remove_l _ _ tc_o_ND_xR) as HN. inversion HN as [|x l Hx _]; subst. exact (Hx Hb). }
destruct b as [p n].
pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ p n (gxG0 cx) ATABLE HAR1 Hb1 HT Hne) as Hd.
pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
unfold zdisjoint in Hd. cbn [fst snd] in Hd, Ha. lia.
Qed.
Lemma tc_o_fp_spares_xR : forall a, fp_spares (dr_fp oSA oE oH cap2 out2) a.
Proof.
intros a Ho. exfalso. destruct Ho as (r & Hr & H0). unfold dr_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in H0. destruct tc_o_table_xR as (HT & HS1 & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 HT) as (_ & Hp4 & _). lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hc). cbn [fst snd] in H0.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ q m HAR1 (tc_o_inA_xR _ Hc)) as (_ & Hp4 & _). lia.
Qed.
Lemma tc_o_KG_xR : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros a Hi' Ho He Hps Hg. split.
- exact (gse_keep_img_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Hi' Ho He Hps (tc_o_fp_spares_xR a) Hg).
-
  apply (tc_wr_img_xR W1 W2 m1 m2 a Hi'). exact (D1 a Hi' Ho He).
Qed.
Lemma tc_o_slots_xR : forall j, In j (rig_slots (firstn i (gps cx))) \/ In j (rig_slots (skipn (S i) (gps cx))) -> j <> oJ.
Proof.
intros j Hj ->. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HND & _).
rewrite <- (firstn_skipn i (gps cx)), tc_rig_slots_app, (tc_skipn_gps cx i tc_o_len_xR Hi), tc_rig_slots_cons in HND.
cbn [fst snd] in HND. rewrite tc_o_eo_xR in HND. cbv beta iota in HND. cbn [app] in HND.
apply NoDup_ListNoDup in HND. apply (NoDup_remove_2 _ _ _ HND). apply in_or_app. exact Hj.
Qed.
Lemma tc_o_slot_lt4_xR : (oJ < 4)%nat.
Proof. exact (tc_slot_lt4 cx i HB Hi Heof). Qed.
Lemma tc_o_arelay_xR : arelay_at B RG ly2 S2 W2 m2 (gxG0 cx) (map fst qd ++ e' :: skipn (S i) (gxes cx)).
Proof.
pose proof HB as (_ & _ & _ & RGP & _).
destruct HG as (Hle & Hlq & _ & Hrly & _).
rewrite (tc_skipn_es cx i Hi) in Hrly.
destruct Hrly as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
assert (KR : forall a, (rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4) -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. destruct (tc_rel_glob RGP a Ha) as (K1 & K2 & K3 & K4).
  exact (tc_o_KG_xR a K1 K2 K3 (PSTG a ltac:(tauto)) K4). }
assert (EL : length (map fst qd ++ e' :: skipn (S i) (gxes cx)) = length (map fst qd ++ gnth cx i :: skipn (S i) (gxes cx)))
  by (rewrite !length_app; reflexivity).
destruct tc_o_table_xR as (HT & HS1 & HS2).
split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; left; cbn in Hx; lia | exact R1]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; left; lia | exact R2]|].
split; [rewrite EL; apply (akept_vm W1 m1); [intros x Hx; apply KR; right; left; cbn in Hx; lia | exact R3]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; right; left; lia | exact R4]|].
split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; right; right; cbn in Hx; lia | exact R5]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; right; right; lia | exact R6]|].
split; [rewrite EL; exact R7|].
split; [exact (proj1 (proj2 (tc_o_inX_xR _ (or_introl eq_refl))))|].
assert (L56 : forall x, aentry_ok B ly1 S1 W1 m1 x -> length (entry_bytes x) = 56%nat)
  by (intros x (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len x P1 P2)).
assert (LE' : length (entry_bytes e') = 56%nat)
  by (destruct D6 as (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len e' P1 P2)).
rewrite Forall_forall in R10.
assert (LE : length (entry_bytes (gnth cx i)) = 56%nat) by (apply L56, R10, in_or_app; right; left; reflexivity).
assert (LP : length (concat (map entry_bytes (map fst qd))) = (56 * i)%nat).
{ rewrite relay_instance_gone_b_lem.rigl_concat_len; [rewrite length_map, Hlq; lia|].
  apply Forall_forall. intros x Hx. apply L56, R10, in_or_app. left. exact Hx. }
split.
{ destruct R9 as (T & T1 & T2 & T3). exists T.
  split; [rewrite EL; exact T1|].
  rewrite map_app, concat_app in T2, T3 |- *. cbn [map concat] in T2, T3 |- *.
  rewrite !length_app, LE, LP in T2.
  split; [rewrite !length_app, LE', LP; exact T2|].
  unfold bzs in T3 |- *. rewrite !map_app in T3 |- *. rewrite <- !app_assoc in T3 |- *.
  apply garr8_app in T3 as (T3a & T3b). apply garr8_app in T3b as (T3b & T3c).
  rewrite !length_map, LP in T3b. rewrite !length_map, LP, LE in T3c.
  apply garr8_app. rewrite !length_map, LP. split.
  - apply (akept_garr8 W1 m1); [|exact T3a]. intros x Hx. rewrite length_map, LP in Hx.
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
    apply (tc_o_KB_xR (gxG0 cx, ATABLE) x (or_introl eq_refl)); cbn [fst snd]; unfold gSA, AENT, ATABLE in *; lia.
  - apply garr8_app. rewrite !length_map, LE'. split.
    + replace (gxG0 cx + Z.of_nat (56 * i)) with (gSA cx i) by (unfold gSA, AENT; lia). exact D5.
    + apply (akept_garr8 W1 m1); [|exact T3c]. intros x Hx. rewrite length_app, !length_map in Hx.
      pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
      apply (tc_o_KB_xR (gxG0 cx, ATABLE) x (or_introl eq_refl)); cbn [fst snd]; unfold gSA, AENT, ATABLE in *; lia. }
split.
{ apply Forall_forall. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | [<- | Hx]].
  - assert (Hok : aentry_ok B ly1 S1 W1 m1 x) by (apply R10, in_or_app; left; exact Hx).
    assert (Hbl : forall b, In b (aentry_blks x) -> In b oXt).
    { intros b Hb. apply in_or_app. left. apply in_concat. exists (aentry_blks x). split; [apply in_map; exact Hx | exact Hb]. }
    apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 x Hok).
    + intros r Hr a Ha. destruct (tc_aentry_fp_blk _ _ _ _ x Hok r Hr a Ha) as (b & Hb & Hab).
      exact (tc_o_KBt_xR b a (Hbl b Hb) Hab).
    + intros b Hb. exact (proj1 (proj2 (tc_o_inX_xR b (or_intror (Hbl b Hb))))).
  - exact D6.
  - assert (Hok : aentry_ok B ly1 S1 W1 m1 x) by (apply R10, in_or_app; right; right; exact Hx).
    assert (Hbl : forall b, In b (aentry_blks x) -> In b oXt).
    { intros b Hb. apply in_or_app. right. apply in_or_app. left. apply in_concat. exists (aentry_blks x).
      split; [apply in_map; exact Hx | exact Hb]. }
    apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 x Hok).
    + intros r Hr a Ha. destruct (tc_aentry_fp_blk _ _ _ _ x Hok r Hr a Ha) as (b & Hb & Hab).
      exact (tc_o_KBt_xR b a (Hbl b Hb) Hab).
    + intros b Hb. exact (proj1 (proj2 (tc_o_inX_xR b (or_intror (Hbl b Hb))))). }
destruct R11 as [R11 R12]. split.
{ rewrite !map_app in R11 |- *. cbn [map] in R11 |- *. rewrite (proj1 tc_o_fd_xR). exact R11. }
apply Forall_app in R12 as [G1 G2]. apply Forall_cons_iff in G2 as [_ G4].
apply Forall_app. split; [exact G1|]. apply Forall_cons; [|exact G4].
intros b Hb Eb. subst b.
pose proof (Permutation_NoDup D4 (tj_nodup _ _ _ _ _ _ tc_o_AR2_xR)) as ND2.
apply (tc_nodup_disj _ _ (gxG0 cx, ATABLE) ND2 Hb).
apply in_or_app. right. apply in_or_app. right. exact (Permutation_in _ tc_o_PX_xR (in_eq _ _)).
Qed.
Lemma tc_o_done_xR : forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  asrc_at B ly2 S2 W2 m2 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
Proof.
intros i' Hi' He. destruct HG as (Hle & Hlq & _ & _ & _ & Hsrc & _).
pose proof (Hsrc i' Hi' He) as HS.
assert (Hj4 : (snd (ghj cx i') < 4)%nat) by (apply (tc_slot_lt4 cx i' HB); [lia | exact He]).
assert (Hji : snd (ghj cx i') <> oJ).
{ apply tc_o_slots_xR. left. apply (tc_slots_in (gnth cx i', ghj cx i')); [|exact He].
  apply tc_in_firstn_gps; [exact tc_o_len_xR | exact Hi' | lia]. }
assert (Hji' : Z.of_nat (snd (ghj cx i')) <> Z.of_nat oJ) by lia.
pose proof tc_o_slot_lt4_xR as HJ4.
unfold gslot in *.
apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HS).
- intros r Hr a Ha. destruct (tc_asrc_fp_blk _ _ _ _ _ _ HS r Hr a Ha) as [Hsl | (b & Hb & Hab)].
  + apply D9; unfold ASRC in *; lia.
  + apply (tc_o_KBt_xR b a); [|exact Hab]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact (tc_done_blks cx qd i i' b tc_o_len_xR Hlq ltac:(lia) Hi' He Hb).
- intros b Hb. assert (HbX : In b oX).
  { right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact (tc_done_blks cx qd i i' b tc_o_len_xR Hlq ltac:(lia) Hi' He Hb). }
  exact (proj1 (proj2 (tc_o_inX_xR b HbX))).
Qed.
Lemma tc_o_later_xR : Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly2 S2 W2 m2 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)).
Proof.
destruct HG as (_ & _ & _ & Hrly & _ & _ & Hdrs & _).
rewrite (tc_skipn_gps cx i tc_o_len_xR Hi) in Hdrs.
pose proof (Forall_inv Hdrs) as Hd0. cbn [fst snd] in Hd0. destruct (Hd0 Heof) as (_ & _ & _ & Hfd0 & _).
apply Forall_inv_tail in Hdrs.
rewrite (tc_skipn_es cx i Hi) in Hrly. pose proof Hrly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rok & (R11 & _)).
rewrite map_app in R11. cbn [map] in R11. apply NoDup_ListNoDup in R11. apply NoDup_remove_2 in R11.
pose proof tc_o_slot_lt4_xR as HJ4.
rewrite Forall_forall in Hdrs |- *. intros [ep [hp jp]] Hp He. cbn [fst snd] in He |- *.
destruct (Hdrs _ Hp He) as (Hj & HS & Hoth & HRr). cbn [fst snd] in Hj, HS, Hoth, HRr.
assert (Hji : jp <> oJ) by (apply tc_o_slots_xR; right; exact (tc_slots_in (ep, (hp, jp)) _ Hp He)).
assert (Hji' : Z.of_nat jp <> Z.of_nat oJ) by lia.
assert (Hfd : re_fd ep <> re_fd (gnth cx i)).
{ intros Heq. apply R11. apply in_or_app. right. rewrite <- Heq. apply in_map.
  unfold gps in Hp. rewrite tc_skipn_combine in Hp. exact (in_combine_l _ _ _ _ Hp). }
assert (HepIn : In ep (skipn (S i) (gxes cx))).
{ pose proof Hp as Hp'. unfold gps in Hp'. rewrite tc_skipn_combine in Hp'. exact (in_combine_l _ _ _ _ Hp'). }
assert (Hfdb : 0 <= re_fd ep < 2 ^ 31 /\ 0 <= re_fd (gnth cx i) < 2 ^ 31).
{ rewrite Forall_forall in Rok. split.
  - destruct (Rok ep ltac:(apply in_or_app; right; right; exact HepIn)) as (_ & _ & _ & _ & Hb & _). exact Hb.
  - destruct (Rok (gnth cx i) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & Hb & _). exact Hb. }
assert (Hbl : forall b, In b (asrc_blks hp) -> In b oXt).
{ intros b Hb. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  exact (tc_srcs_in (ep, (hp, jp)) _ b Hp He Hb). }
split; [exact Hj|]. split.
- apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HS).
  + intros r Hr a Ha. destruct (tc_asrc_fp_blk _ _ _ _ _ _ HS r Hr a Ha) as [Hsl | (b & Hb & Hab)].
    * apply D9; [unfold ASRC in Hsl |- *; lia | unfold gslot, ASRC in Hsl |- *; lia].
    * exact (tc_o_KBt_xR b a (Hbl b Hb) Hab).
  + intros b Hb. exact (proj1 (proj2 (tc_o_inX_xR b (or_intror (Hbl b Hb))))).
- split; [|exact HRr].
  apply (tc_aothers_kept W1 m1 W2 m2 jp (re_fd ep) oJ Hoth).
  + intros i'' Hi'' Hne a Ha. assert (Z.of_nat i'' <> Z.of_nat oJ) by lia.
    apply D9; [unfold ASRC in Ha |- *; lia | unfold gslot, ASRC in Ha |- *; lia].
  + intros _. exists (hs_fd h'), (hs_open h').
    pose proof D8 as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & _). unfold gslot in V1, V2.
    split; [exact V1|]. split; [exact V2|]. right. rewrite (proj2 tc_o_fd_xR), Hfd0, !(Z.mod_small _ (2 ^ 32)) by lia.
    intros Heq. exact (Hfd (eq_sym Heq)).
Qed.
Lemma tc_o_gtopm_xR : GTOPM cx i qd c2 O2 cap2 e' h' ev' LB (dr_ctl c2 (fst (ghj cx i)) ev')
  (if dr_live c2 (fst (ghj cx i)) then O2 ++ LB else O2) ocap out' ly2 S2 W2 m2.
Proof.
pose proof HG as (Hle & Hlq & Hrel & _ & _ & _ & _ & Hgs & _).
unfold GTOPM. cbv zeta. rewrite tc_o_eo_xR. cbv beta iota.
split; [exact Hi|]. split; [exact Hlq|]. split; [exact Hrel|].
split; [unfold gdrained; cbv zeta; rewrite tc_o_eo_xR; cbv beta iota; cbn [andb];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity | exact D7]|].
split; [exact tc_o_arelay_xR|].
split; [exact (tc_aout_no _ _ _ _ _ _ _ _ _ _ D10)|].
split; [exact tc_o_done_xR|].
split; [intros _; exact D8|].
split; [exact tc_o_later_xR|].
split.
{ intros a Ha Hnj. apply (tl_kept_trans (gxW cx) W1 W2 (gxmem cx) m1 m2 a).
  - apply Hgs; [exact Ha|]. intros j Hj. apply Hnj. rewrite (tc_firstn_gps cx i tc_o_len_xR Hi), tc_rig_slots_app.
    apply in_or_app. left. exact Hj.
  - apply D9; [exact Ha|]. unfold gslot. apply Hnj. rewrite (tc_firstn_gps cx i tc_o_len_xR Hi), tc_rig_slots_app.
    apply in_or_app. right. rewrite tc_rig_slots_cons. cbn [fst snd]. rewrite tc_o_eo_xR. left. reflexivity. }
eapply Permutation_trans; [exact D4|].
eapply Permutation_trans.
{ apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head. exact (Permutation_sym tc_o_PX_xR). }
rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.
End tc_open_xR.
(* W_rig_top.v:2553 top_rep_open at R *)
Lemma top_rep_open_xR : stmt_top_rep_open_xR.
Proof.
unfold stmt_top_rep_open_xR. cbv zeta.
intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 sp1 ly2 S2 Hp2 W2 m2 md2 k2 HB Hi Heof HG HAR1 HJ Hsp HD.
unfold DRK in HD. cbv zeta in HD.
destruct HD as (e' & h' & out' & ev' & LB & rest & D1 & _ & D3 & D4 & D5 & _ & D6 & D7 & D8 & D9 & D10).
exists e', h', ev', LB, out'.
eapply tc_o_gtopm_xR; eassumption.
Qed.
(* W_rig_top.v:2682 tl2_frm at R *)
Lemma tl2_frm_xR : forall cx fpos ly1 S1 Hp1 W1 m1 md1 k1,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
ARx ly1 S1 Hp1 W1 m1 md1 /\ In (1, fpos) (frames S1) /\
4096 <= frame_addr ly1 1 fpos /\ frame_addr ly1 1 fpos + 128 <= alloc_ceiling /\ in_app (frame_addr ly1 1 fpos) 128 /\
(forall a, frame_addr ly1 1 fpos <= a < frame_addr ly1 1 fpos + 128 -> ~ in_img SEGS a).
Proof.
intros cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ.
pose proof (tj_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR Hfin) as (H1 & H2 & H3).
change (fs_frame_bytes 1) with 128 in H2, H3.
split; [exact HAR|]. split; [exact Hfin|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
intros a Ha Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR _) Hi). right. left.
exists 1, fpos. split; [exact Hfin|]. change (fs_frame_bytes 1) with 128. exact Ha.
Qed.
(* W_rig_top.v:2702 live_kept at R *)
Lemma live_kept_xR : stmt_live_kept_xR.
Proof.
unfold stmt_live_kept_xR.
intros cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 Hp2 m2 md2 P HB HJ1 HROM1 HPK HFR HLK HLS HJ2 HPw HK HPR.
pose proof (tl2_sp cx HB) as SP.
pose proof HB as (_ & _ & _ & RGP & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HFR as (HFa & HFl & HFL120 & HS16 & HS24 & HS80 & HSV).
destruct (tl2_frm_xR cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ1) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (SF : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. unfold SHADOW_OFF in SF.
assert (HF8 : F = 8 * (F / 8) + F mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
assert (NPI : forall a, in_img SEGS a -> ~ P a).
{ intros a Hi Hp. pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  destruct (HPw a Hp) as [H|[H|[H|[H|H]]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia | |].
  - exact (HFni a ltac:(lia) Hi).
  - rewrite SF in H. lia. }
assert (NPF : forall a, F + 120 <= a < F + 128 -> ~ P a).
{ intros a Ha Hp. destruct (HPw a Hp) as [H|[H|[H|[H|H]]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia | lia |].
  rewrite SF in H. exact (fshadow_not_app F 16 F 128 a HF4 ltac:(lia) HFapp H ltac:(lia)). }
assert (NPS : forall a, gsp1 cx + 16 <= a < gsp1 cx + 32 \/ gsp1 cx + 40 <= a < gsp1 cx + 88 \/
  gsp1 cx + 120 <= a < gsp1 cx + 224 -> ~ P a).
{ intros a Ha Hp. unfold gsp1, RIG_FRAME in Ha.
  destruct (HPw a Hp) as [H|[H|[H|[H|H]]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia | lia |].
  rewrite SF in H. lia. }
assert (VK : forall a n v, (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ P (a + k)) ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v Hn Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 m2 a n v); [|exact Hv].
  intros k Hk. destruct (Hn k Hk) as (Hr & Hnp). exact (HK (a + k) Hr Hnp). }
split.
- exists fpos, Hp2. split; [exact HJ2|].
  split.
  { intros a Ha.
    assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
    rewrite (HK a ltac:(lia) (NPI a Hi)). exact (HROM1 a Ha). }
  split.
  { intros a Hi Ho He Hp. exact (HPR a (HPK a Hi Ho He Hp)). }
  split.
  { split; [exact HFa|]. split; [exact HFl|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [lia | apply NPF; lia] | exact HFL120]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS16]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS24]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS80]|].
    intros i Hi. apply VK; [|exact (HSV i Hi)].
    intros k Hk. cbn in Hk. split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia]. }
  apply (alock_at_kept RG W1 m1 W1 m2 true HLK).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  assert (Hi : in_img SEGS a) by exact (proj1 (RGIMG a ltac:(unfold rg_rng; left; exact Ha))).
  pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  split; [exact (HK a ltac:(lia) (NPI a Hi))|].
  unfold arm. apply writable_kept. exact (HPR a).
- pose proof HLS as (L40 & L48 & L56 & L64 & L72).
  split; [|split; [|split; [|split]]]; (apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | assumption]).
Qed.
(* W_rig_top.v:2762 live_drain at R *)
Lemma live_drain_xR : stmt_live_drain_xR.
Proof.
unfold stmt_live_drain_xR.
intros cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 SA e h cap out ly2 S2 Hp2 W2 m2 md2 k2 Hp3 k3
  HB HJ1 HROM1 HPK HFR HLK HLS HJD HFPB HPK2 HJ2.
pose proof (tl2_sp cx HB) as SP.
pose proof HB as (_ & _ & _ & RGP & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & RGWR & _).
pose proof HFR as (HFa & HFl & HFL120 & HS16 & HS24 & HS80 & HSV).
destruct (tl2_frm_xR cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ1) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HGD : gx_ok SEGS B (G_DR B RG)) by exact (gx_ok_sub SEGS B _ _ (rig_G_DR_RIG B RG) HGRIG).
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD) as (memS & HJDi & HagD).
pose proof HJDi as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRM & _).
assert (NFP : forall a, F <= a < F + 128 -> ~ inFP (dr_fp SA e h cap out) a).
{ intros a Ha Hf. destruct (HFPB a Hf) as (b & n & Hin & Hr).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ b n 1 fpos HAR1 Hin Hfin) as Hd.
  rewrite HFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (SPR : forall a, fp_spares (dr_fp SA e h cap out) a).
{ intros a Ho. exfalso. destruct (HFPB 0 Ho) as (b & n & Hin & Hr).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ b n HAR1 Hin) as (_ & H4096 & _). lia. }
assert (KHI : forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. unfold gsp1, RIG_FRAME in Ha.
  apply (gse_keep_high_xR B PST ARx R (G_DR B RG) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGD HJD a); unfold gsp1, RIG_FRAME; lia. }
assert (KFR : forall a, F <= a < F + 128 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha.
  assert (Hrng : in_zr a (frame_rng ly1 (1, fpos)) \/
    in_zr a (shadow_addr (frame_addr ly1 1 fpos), fs_frame_bytes 1 / 8)).
  { left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes 1) with 128. lia. }
  rewrite (FRM 1 fpos a Hfin Hrng (NFP a Ha)).
  apply HagD. rewrite unsigned_lit_small by lia. intros HG. exact (HFni a Ha (proj1 (HGD a HG))). }
assert (KLK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hi & Ho & He).
  pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  split.
  - apply (gse_keep_img_xR B PST ARx R (G_DR B RG) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD a Hi Ho He
      (PSTG a ltac:(left; unfold inG, G_RIG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia)) (SPR a)).
    pose proof HRGP as (HL & _). cbn [zall_disjoint] in HL. unfold zdisj in HL. cbn [fst snd] in HL.
    destruct HL as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _).
    unfold inG, G_DR, G_SL. intros HG. rewrite !Exists_cons, Exists_nil in HG. unfold in_zr in HG. cbn [fst snd] in HG.
    destruct HG as [HG|[HG|[HG|[HG|[HG|[HG|[HG|[]]]]]]]];
    [ clear - D1 Ha HG | clear - D10 Ha HG | clear - D12 Ha HG | clear - D6 Ha HG | clear - D7 Ha HG
    | clear - D8 Ha HG | clear - D14 Ha HG ]; lia.
  - intros _. unfold arm. apply (RGWR (w_H W2) m2 a); [left; exact Ha|].
    apply (hidden_not_img SEGS W2 (Z_to_bv 64 a)). rewrite unsigned_lit_small by lia. exact Hi. }
assert (LF : ly_F ly2 = ly_F ly1) by (destruct Hly as (_ & _ & _ & _ & _ & LF & _); exact LF).
assert (VKH : forall a n v, gsp1 cx <= a -> a + Z.of_nat n <= gsp0 cx ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v).
{ intros a n v H1 H2 Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 a n v); [|exact Hv].
  intros k Hk. apply KHI. lia. }
split.
- exists fpos, Hp3. split; [exact HJ2|].
  split.
  { apply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD);
      [| exact PSTR | exact HROM1].
    intros a Ha. destruct (HROMO a Ha) as (HnG & Hrest). split; [|exact Hrest].
    intros HG. exact (HnG (rig_G_DR_RIG B RG a HG)). }
  split; [exact (gse_apres_trans B _ _ _ _ _ _ HPK HPK2)|].
  split.
  { split; [unfold frame_addr in *; rewrite LF; exact HFa|].
    split; [unfold flag_addr in *; rewrite LF; exact HFl|].
    split.
    { unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 _ 8 _); [|exact HFL120].
      intros k Hk. apply KFR. lia. }
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS16]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS24]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS80]|].
    intros i Hi. apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact (HSV i Hi)]. }
  apply (alock_at_kept RG W1 m1 W2 m2 true HLK).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact (KLK a Ha).
- pose proof HLS as (L40 & L48 & L56 & L64 & L72).
  split; [|split; [|split; [|split]]];
  (apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | assumption]).
Qed.
(* W_rig_top.v:3079 ts_jframe at R *)
Lemma ts_jframe_xR : forall W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc W
    memT mdc k ->
  ARx lyc Sc Hpc W memT mdc /\ In (1, fpos) (frames Sc) /\ alloc_ceiling + RIG_STK_x <= sp0.
Proof.
intros W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ.
destruct HJ as (_ & _ & (memS & HJi & _) & _).
destruct HJi as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
split; [exact HAR|]. split; [rewrite Hfrs; apply in_or_app; left; apply in_eq | lia].
Qed.
(* W_rig_top.v:3195 snp_call at R; the snprintf contract stays strict (W_sites_x.v aj_gx_entry_at_xR), so its SRr_mono stays *)
Lemma snp_call_xR : stmt_snp_call_xR.
Proof.
unfold stmt_snp_call_xR.
intros W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F id idv Post
  HJ Hsp Hsp16 Hgp Htp Hra Hraw R10 R11 R12 R13 R14 Hidv Hid HF Hsh Hrom K.
set (T := relay_instance_gone_b_c.instance_prefix id) in *.
destruct (ts_T id) as [TR TL27]. fold T in TR, TL27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ts_jframe_xR W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ) as (HAR & Hin & Hceil).
destruct (ts_frame lyc Sc Hpc W memT mdc fpos F HAR Hin HF) as (HF0 & HFc & HF32 & HFr & HFb).
pose proof (pa_obj_img 20 ltac:(lia)) as O20. pose proof (pa_obj_img 21 ltac:(lia)) as O21.
pose proof (ts_lit_apart lyc Sc Hpc W memT mdc fpos F (VAL (A_OBJ 21)) HAR Hin HF ltac:(lia)) as A21.
assert (Hsp' : alloc_ceiling <= spZ regsT - 3 * ESTACK) by lia.
pose proof (ts_guard lyc Sc Hpc W memT mdc HAR) as EG.
destruct (ts_lit 20 RIG_FMT lyc Sc Hpc W regsT memT mdc ltac:(lia) ltac:(unfold RIG_FMT; cbn [length]; lia) HLIT20
  ltac:(unfold RIG_FMT; repeat constructor; lia) HAR Hrom Hsp') as (E20s & E20r & E20t).
destruct (ts_lit 21 RelayModel.K_GESTURE lyc Sc Hpc W regsT memT mdc ltac:(lia)
  ltac:(unfold RelayModel.K_GESTURE; cbn [length]; lia) HLIT21
  ltac:(unfold RelayModel.K_GESTURE; repeat constructor; lia) HAR Hrom Hsp') as (E21s & E21r & E21t).
destruct (SnpNarrowSites.san_M1_pi (PI := PI) RIG_FMT eq_refl (proj1 HLITGOT)) as (N1a & N1b).
assert (E13 : bv_unsigned (getr regsT 13) = VAL (A_OBJ 21))
  by (rewrite R13; unfold w64; apply unsigned_lit_small; lia).
pose proof (SnpNarrowSites.san_M2_x_pi (PI := PI) B ARx hl LAWS IMGC lyc Sc Hpc W memT mdc fpos HAR Hin) as N2.
rewrite HF in N2.
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ apply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_RIG B RG) 0 [] (3 * ESTACK) (SIGMA WS_snprintf)
    (fun a => F + 32 <= a < F + 32 + 48)
    (fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length T)) /\
       abytes_at W mem' (F + 32) (printf_facts_c.pf_bytes (firstn (Z.to_nat (48 - 1)) T ++ [0])))
    W regsT memT RIG_STK_x sp0 FP ly S Hp W0 mem md [(1, fpos)] lyc Sc Hpc mdc k (-224) raw HGRIG eq_refl HJ
    ltac:(lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw).
  - intros a. destruct (Z_lt_dec a (F + 32)) as [H|H]; [right; lia|].
    destruct (Z_lt_dec a (F + 32 + 48)) as [H'|H']; [left; lia | right; lia].
  - intros a Ha _. cbv beta in Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (HFb a ltac:(lia))).
  - intros a Ha _. cbv beta in Ha. split; [|lia]. unfold awr_byte. right. right. right.
    unfold in_frames. exists 1, fpos. split; [apply in_eq|].
    left. unfold in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 1) with 128. lia.
  - intros HPRE HSC. eapply SRr_mono.
    { apply (ASNPRINTF lyc Sc Hpc W regsT memT mdc (F + 32) 48 (VAL (A_OBJ 20)) RIG_FMT
        [printf_facts_c.Ps; printf_facts_c.PLit 32; printf_facts_c.Pd; printf_facts_c.PLit 32]
        [printf_facts_c.APtr RelayModel.K_GESTURE; printf_facts_c.AInt id] T EG
        (ecall_pre_stk_of_x B ARx (3 * ESTACK) lyc Sc Hpc W regsT memT mdc HPRE HSC) R10 R11 R12
        ltac:(lia) ltac:(lia) ltac:(lia) E20s eq_refl eq_refl N1a N1b
        (fun s Hs => SnpNarrowSites.san_M3_pi (PI := PI) (getr regsT 13) id s E13 (proj2 HLITGOT) Hs) N2
        eq_refl ltac:(lia) E20r E20t).
      +
        cbn [apf_args_ok apf_arg_ok]. rewrite R13, R14. unfold w64.
        rewrite (unsigned_lit_small (VAL (A_OBJ 21))) by lia.
        split; [|split; [|exact I]].
        * split; [unfold RelayModel.K_GESTURE; repeat constructor; lia|].
          split; [lia|]. split; [exact E21s|]. split; [exact E21r|]. split; [exact E21t|].
          change (Z.of_nat (length RelayModel.K_GESTURE)) with 13. lia.
        * split; [exact Hid|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          rewrite Z.mod_mod_divide; [exact Hidv|]. exists (2 ^ 32). reflexivity.
      +
        unfold awrite_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
        { intros a Ha. destruct (HFb a ltac:(lia)) as [Hpa Hno].
          split; [exact (apresent_writable SEGS _ _ _ Hpa)|]. split; [exact Hno|]. unfold ascratch_stk. lia. }
        split; [apply amem_range_high; lia|]. split; [exact (ts_ra W memT F 48 HF32 ltac:(lia) Hsh)|].
        intros _. exact (ts_hull lyc Sc Hpc W memT mdc fpos F 48 HAR Hin HF ltac:(lia)).
      +
        apply amem_range_high; lia.
      + exact (rt_rom_view_of_rom_view B W memT Hrom). }
    intros W' c' _ Hp'. apply aentry_post_of_art_post_x. exact Hp'. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (R10' & Hby) & Hfr & Hpres).
assert (EF : firstn (Z.to_nat (48 - 1)) T = T) by (apply firstn_all2; change (Z.to_nat (48 - 1)) with 47%nat; lia).
rewrite EF in Hby.
apply (K regs2 mem2 md2 HJ2 HP2 R10').
- apply ts_garr8_of_abytes; [apply Forall_app; split; [exact TR | repeat constructor; lia] | exact Hby].
- intros a Ha H1 H2. apply Hfr; [exact Ha | cbv beta; lia | lia].
- exact Hpres.
Qed.
(* W_rig_top.v:3274 strlen_call at R *)
Lemma strlen_call_xR : stmt_strlen_call_xR.
Proof.
unfold stmt_strlen_call_xR.
intros W regsT memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k raw F pre Post
  HJ Hsp Hsp16 Hgp Htp Hra Hraw R10 HF Hg Hnz Hlen Hsh Hrom K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (ts_jframe_xR W memT sp0 FP ly S Hp W0 mem md fpos lyc Sc Hpc mdc k HJ) as (HAR & Hin & Hceil).
destruct (ts_frame lyc Sc Hpc W memT mdc fpos F HAR Hin HF) as (HF0 & HFc & HF32 & HFr & HFb).
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ apply (aj_strlen_gx_at_xR B PST ARx LAWS R_trans WLE_R (SIGMA WS_strlen) ASTRLEN (G_RIG B RG) 0 [] W regsT memT RIG_STK_x sp0 FP ly S Hp
    W0 mem md [(1, fpos)] lyc Sc Hpc mdc k (F + 32) (Z.of_nat (length pre)) (-224) raw HGRIG eq_refl HJ R10
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw).
  - unfold first_byte. split; [lia|]. split.
    + intros i Hi. exists (nth (Z.to_nat i) pre 0). split.
      * pose proof (tp_garr8_aview (w_H W) memT (F + 32) (pre ++ [0]) (Z.to_nat i) Hg
          ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
        rewrite Z2Nat.id in Hv by lia. rewrite app_nth1 in Hv by lia. exact Hv.
      * intros E. apply Hnz. rewrite <- E. apply nth_In. lia.
    + intros _. pose proof (tp_garr8_aview (w_H W) memT (F + 32) (pre ++ [0]) (length pre) Hg
        ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
      rewrite nth_middle in Hv. exact Hv.
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HFb a ltac:(lia)))|]. lia.
  - intros a Ha. lia.
  - apply amem_range_high; lia.
  - apply amem_range_high; lia.
  - exact (ts_ra W memT F (Z.of_nat (length pre) + 1) HF32 ltac:(lia) Hsh).
  - exact (ts_hull lyc Sc Hpc W memT mdc fpos F (Z.of_nat (length pre) + 1) HAR Hin HF ltac:(lia)).
  - intros a Ha. pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length pre)) 8 ltac:(lia)) as M8.
    apply (aview_some_of_apresent SEGS). apply (proj1 (HFb a ltac:(lia))).
  - exact Hrom. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & R10' & Hfr & Hpres).
apply (K regs2 mem2 md2 HJ2 HP2 R10').
- intros a Ha Hn. apply Hfr; [exact Ha | lia].
- exact Hpres.
Qed.
(* W_rig_top.v:3611 PD at R *)
Definition PD_xR (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent,
c1 = cfg_at SEGS (BASE + A_rig_pd) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 20 = w64 (F + 32) /\ getr regs1 21 = w64 (shadow_addr F) /\
getr regs1 22 = w64 (rg_src RG + RIG_HI_SRC) /\ getr regs1 19 = w64 (AENT * Z.of_nat i) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 88) 8 (Z.of_nat i) /\
GLIVE_xR B PST ARx RG R cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots RG cx F W1 m1 /\
GTOPM cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 W1 m1 /\
gtop_bud cx e1 c1' O1 cap1 i ly1 S1 spent.
(* W_rig_top.v:3623 the runners, on the G chain at R (W_journal_x.v Section g; W_kit.v paj_branch_xR) *)
Let RUN_R := paj_run_x_xG B PST ARx LAWS R (G_RIG B RG) HGRIG 0 [].
Let RUNTO_R := paj_run_to_x_xG B PST ARx LAWS R (G_RIG B RG) HGRIG 0 [].
Let BR_R := paj_branch_xR (PI := PI) (R := R).
(* W_rig_top.v:3627 top_p1 at R *)
Lemma top_p1_xR :
stmt_gout_kept -> stmt_top_rep_closed -> stmt_top_budget ->
stmt_live_kept_xR ->
stmt_top_drain_pre -> stmt_dr_inv_of -> stmt_top_room -> stmt_dr_fp_in ->
stmt_top_rep_open_xR -> stmt_dr_bytes -> stmt_dr_cnt -> stmt_live_drain_xR ->
forall cx i W1 c1,
GBASE B ARx MT RP MMAX RG cx -> RGO_xR B PST ARx MT RP MMAX RG R cx i W1 c1 ->
(forall W2 c2, PD_xR cx i W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (gPOST_xR B PST ARx MT RP RG R cx)) ->
YA0nH.SRrG SEGS R W1 c1 (gPOST_xR B PST ARx MT RP RG R cx).
Proof.
intros LGK LRC LBU LLK LDP LDI LTR LFP LRO LDB LDC LLD cx i W1 c1 HB HO KPD.
destruct HO as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent & -> & HRB & R20 & R21 & R22 & R14 & Hi & HGL & HLS & HGO).
pose proof HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H18).
pose proof HGO as (Hle & Hlq & Hrel & Hrly & Hout & Hsrc & Hdrs & Hgs & Hperm & Hbud).
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 & HBT).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (SRCI : in_img SEGS (rg_src RG)) by (apply (proj1 (RGIMG (rg_src RG) ltac:(unfold rg_rng; right; right; left; lia)))).
assert (SRCI7 : in_img SEGS (rg_src RG + 7)) by (apply (proj1 (RGIMG (rg_src RG + 7) ltac:(unfold rg_rng; right; right; left; lia)))).
pose proof (pa_img_range (rg_src RG) SRCI) as SRCr. pose proof (pa_img_range (rg_src RG + 7) SRCI7) as SRCr7.
pose proof Hrly as (RS1 & _ & _ & _ & _ & _ & Rlen & RSG & (tail & _ & _ & Rtab) & Rok & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 RSG) as (HG16 & HG4096 & HGc & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in HGc, HGapp, HGpres.
assert (HLES : length (gxes cx) = length (gxhs cx)) by (symmetry; exact HLEN).
assert (Hsk : skipn i (gxes cx) = gnth cx i :: skipn (S i) (gxes cx)) by (apply tp_skipn_cons; lia).
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (map fst qd ++ skipn i (gxes cx))).
{ eapply Forall_impl; [|exact Rok]. intros e (_ & _ & P1 & P2 & _). split; assumption. }
assert (HLmq : length (map fst qd) = i) by (rewrite length_map; exact Hlq).
assert (Hnth : nth i (map fst qd ++ skipn i (gxes cx)) relay_remove_b_c.no_entry = gnth cx i).
{ rewrite app_nth2 by lia. rewrite HLmq, Nat.sub_diag, Hsk. reflexivity. }
assert (HLtab : (i < length (map fst qd ++ skipn i (gxes cx)))%nat) by (rewrite length_app, HLmq, length_skipn; lia).
pose proof (tp_table_entry _ _ _ _ i Rtab Hok HLtab) as HTE. rewrite Hnth in HTE.
assert (HEok : aentry_ok B ly1 S1 W1 m1 (gnth cx i)).
{ rewrite Forall_forall in Rok. apply Rok. rewrite <- Hnth. apply nth_In. exact HLtab. }
pose proof HEok as (Heof01 & _).
pose proof (tp_entry_eof _ _ _ HTE Heof01) as HVE.
set (SA := gxG0 cx + AENT * Z.of_nat i) in *.
set (G0 := gxG0 cx) in *.
assert (Hes16 : (length (gxes cx) <= 16)%nat) by (rewrite length_app, HLmq, length_skipn in Rlen; lia).
assert (SP1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
assert (Hsp32 : gsp1 cx mod 32 = 0) by (rewrite SP1; rewrite Zminus_mod, H32; reflexivity).
assert (HDJ : SA + 8 <= VAL (A_OBJ 8) \/ VAL (A_OBJ 8) + 8 <= SA + 4).
{ rewrite <- RGSRC. destruct (Z_le_gt_dec (SA + 8) (rg_src RG)) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (rg_src RG + 8) (SA + 4)) as [D2|D2]; [right; exact D2|]. exfalso.
  set (a := Z.max (SA + 4) (rg_src RG)).
  assert (Hia : in_img SEGS a) by (apply (proj1 (RGIMG a ltac:(unfold rg_rng; right; right; left; unfold a; lia)))).
  refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR1 _) Hia). left. exists G0, ATABLE. split; [exact RSG|].
  rewrite RQT. unfold a, SA, AENT in *. lia. }
pose proof (tp_seat1 W1 regs1 m1 G0 SA (re_eof (gnth cx i)) (gsp1 cx) (Z.of_nat i)) as HS.
specialize (HS ltac:(rewrite R22, HH45; reflexivity)
  ltac:(rewrite H9; unfold w64; apply unsigned_lit_small; unfold gsp0 in *; lia)
  H18 R14 ltac:(lia) ltac:(unfold SA, AENT; lia) HG4096 HGc ltac:(rewrite SP1; unfold gsp0 in *; lia)
  ltac:(pose proof (Z.div_mod G0 16 ltac:(lia)) as D; rewrite HG16 in D; rewrite D;
        replace (16 * (G0 / 16) + 0) with ((2 * (G0 / 16)) * 8) by lia; apply Z_mod_mult)
  Heof01 ltac:(rewrite <- RGSRC; lia) ltac:(rewrite <- RGSRC; lia)
  ltac:(rewrite SP1; unfold gsp0 in *; lia) ltac:(rewrite SP1; unfold gsp0 in *; lia) Hsp32 HDJ
  ltac:(rewrite <- RGSRC; exact RS1) HVE
  ltac:(intros o Ho; apply Hpres1; rewrite SP1, WS; lia)).
remember (Eimg (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_eof (gnth cx i))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
clear HE.
assert (HBx : U E (SOff 18 0) = SHADOW_OFF) by (rewrite (U_atom E 18 SHADOW_OFF E18) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS (SOff 18 0) tp_SH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 _ W1 m1 md1 G0 ATABLE (SA + 4) 4 HAR1 RSG);
    [unfold SA, AENT; lia | rewrite RQT; unfold SA, AENT; lia].
  + exact HBx.
  + rewrite (U_atom E 33 _ E33) by (unfold SA, AENT; lia). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SA, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rig_outer)) with (Z_to_bv 64 (BASE + A_rig_outer)).
pose proof HJ as HJ0.
paj_run_tok_xR RUN_R HS HJ SHOK tp_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]].
  intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite (EEo 9%nat 9%bv eq_refl), H9 in Ha.
  unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (unfold gsp0 in *; lia).
  left. split; [left; rewrite SP1, WS in *; lia | lia]. }
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
assert (E34' : ew (ewset (ewset E 512 w) 513 w0) 34 = Z_to_bv 64 (re_eof (gnth cx i))) by (rewrite !ew_ewset_other by lia; exact E34).
assert (HAE' : env_agree 32 (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i)))) (ewset (ewset E 512 w) 513 w0))
by (apply tp_env_agree_ewset; [apply tp_env_agree_ewset; [exact HAE | lia] | lia]).
assert (NW0 : forall a, ~ (gsp1 cx + 88 <= a < gsp1 cx + 96) -> ~ in_wrange E (ss_mem tp_ss1) a).
{ intros a Na (r & Hin & Hr). cbn [ss_mem tp_ss1 tp_regions1 In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; try lia.
  rewrite (EEo 9%nat 9%bv eq_refl), H9 in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by (unfold gsp0 in *; lia). lia. }
psrr_branch_tok RUN_R BR_R HS SHOK tp_Bspan.
-
  rewrite branch_ne_U, (U_atom _ 34 _ E34'), U_lit in Hc by lia.
  assert (Heof1 : re_eof (gnth cx i) <> 0) by (intros X; rewrite X in Hc; discriminate Hc).
  paj_run_to_tok_xR RUNTO_R HS HJ SHOK tp_Bspan (AF_fr_relay_instance_gone + 0x1a4).
  { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]].
    intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ew_ewset_other, ew_ewset_other, (EEo 9%nat 9%bv eq_refl), H9 in Ha by lia.
    unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (unfold gsp0 in *; lia).
    left. split; [left; rewrite SP1, WS in *; lia | lia]. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => assert (HAE2 : env_agree 32 (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i)))) Ex)
    by (repeat first [exact HAE' | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 20; 21]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (22%bv : bv 5) N22. prreg HS (19%bv : bv 5) N19.
  assert (U9E : bv_unsigned (ew E 9) = gsp1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; unfold gsp0 in *; lia).
  tp_nw HFr0 NW0' (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) U9E.
  tp_nw HFr1 NW1 (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) U9E.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx + 88 <= a < gsp1 cx + 96) ->
    aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a)
  by (intros a Ha Na; exact (tp_kept2 _ _ _ _ _ _ _ _ a HFr0 HFr1 Ha (NW0' a Na) (NW1 a Na))).
  assert (PRES : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
  by (intros a Hp; eapply apresent_grows; [exact HG1 | eapply apresent_grows; [exact HG0 | exact Hp]]).
  assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
  assert (HGO1 : GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1)).
  { apply (LGK cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 (ms_mem ms1) fpos HB HAR1 Hfin); [|exact PRES|exact HGO].
    intros a Ha _. apply KEEP; [lia|]. rewrite SP1, WS in *. lia. }
  pose proof (LRC cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1) HB Hi Heof1 HGO1) as HTM.
  pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcl & Hbr & Hdd & _ & Hmx & _ & Hcapd).
  assert (Hcap0 : 0 <= cap2) by (destruct Hcapd as [(-> & _) | (Hc0 & _)]; lia).
  pose proof (LBU cx i qd c2 O2 cap2 spent ly1 S1 ly1 S1 (gnth cx i) (fst (ghj cx i)) 0 [] c2 O2 cap2 HB Hi Hlq Hrel Hcl Hbr
    Hdd Hcap0 Hmx Hbud) as HBU.
  specialize (HBU ltac:(unfold gdrained; rewrite (proj2 (Z.eqb_neq _ _) Heof1); cbn; repeat split; reflexivity)
    ltac:(intros X; apply Z.eqb_eq in X; contradiction)
    ltac:(intros _; destruct Hbud as (_ & _ & _ & _ & _ & HRM0 & _);
          split; [apply (mo_le_refl MT MLAW) | split; [lia | split; [exact HRM0 | reflexivity]]])).
  rewrite (proj2 (Z.eqb_neq _ _) Heof1), Z.add_0_r in HBU.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pmkst HS.
  apply KPD. unfold PD_xR.
  exists (ms_regs ms1), ly1, S1, (ms_mem ms1), (with_vm_backing (m_vm_lazy md1) mat1 md1), k1, F, FL, qd, c2, O2, cap2,
    (gnth cx i), (fst (ghj cx i)), 0, [], c2, O2, cap2, out2, spent.
  split; [unfold cfg_at, A_rig_pd; reflexivity|].
  split; [unfold gregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRB|].
  split; [rewrite HK by (cbv; tauto); exact R20|].
  split; [rewrite HK by (cbv; tauto); exact R21|].
  split; [change 325%nat with (A_HI 45) in N22; rewrite N22, (img_env_atomP E (A_HI 45) HEI ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH45; reflexivity|].
  split; [rewrite N19, (EEo 14%nat 14%bv eq_refl), R14; apply bv_eq; unfold mul_div; rewrite bv_mul_unsigned, !Z_to_bv_unsigned;
          unfold bv_wrap, AENT; change (bv_modulus 64) with (2 ^ 64);
          rewrite (Z.mod_small (Z.of_nat i)), (Z.mod_small 56), (Z.mod_small (Z.of_nat i * 56)), (Z.mod_small (56 * Z.of_nat i)) by lia; lia|].
  split.
  { unfold arm. replace (gsp1 cx + 88) with (bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 9) + 88)
      by (rewrite !ew_ewset_other, U9E by lia; reflexivity).
    eapply (field_of_region _ _ 9 _ _ 88 96 88 96 88 8%N (SOff 14 0) (Z.of_nat i) RG1); [reflexivity | left; reflexivity | | cbn; lia | cbn; lia].
    cbn [sv_denot]. rewrite !ew_ewset_other, (EEo 14%nat 14%bv eq_refl), R14 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms1) (with_vm_backing (m_vm_lazy md1) mat1 md1)
    (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) HB HJ0 HROM1 HPK HFR HLK HLS HJ) as [HGL1 HLS1].
  { intros a Ha. right; right; left. exact Ha. }
  { exact KEEP. }
  { exact PRES. }
  split; [exact HGL1|]. split; [exact HLS1|]. split; [exact HTM | exact HBU].
-
  rewrite branch_ne_U, (U_atom _ 34 _ E34'), U_lit in Hc by lia.
  assert (Heof0 : re_eof (gnth cx i) = 0) by (destruct Heof01 as [X|X]; [exact X | rewrite X in Hc; discriminate Hc]).
  paj_run_to_tok_xR RUNTO_R HS HJ SHOK tp_Bspan AF_fr_drain.
  { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil]].
    intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ew_ewset_other, ew_ewset_other, (EEo 9%nat 9%bv eq_refl), H9 in Ha by lia.
    unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (unfold gsp0 in *; lia).
    left. split; [left; rewrite SP1, WS in *; lia | lia]. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => assert (HAE2 : env_agree 32 (Ereg regs1 (tp_extra1 G0 SA (re_eof (gnth cx i)))) Ex)
    by (repeat first [exact HAE' | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 20; 21]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (22%bv : bv 5) N22. prreg HS (19%bv : bv 5) N19. prreg HS (10%bv : bv 5) N10. prreg HS (1%bv : bv 5) N1.
  assert (U9E : bv_unsigned (ew E 9) = gsp1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; unfold gsp0 in *; lia).
  tp_nw HFr0 NW0' (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) U9E.
  tp_nw HFr1 NW1 (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) U9E.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx + 88 <= a < gsp1 cx + 96) ->
    aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a)
  by (intros a Ha Na; exact (tp_kept2 _ _ _ _ _ _ _ _ a HFr0 HFr1 Ha (NW0' a Na) (NW1 a Na))).
  assert (PRES : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
  by (intros a Hp; eapply apresent_grows; [exact HG1 | eapply apresent_grows; [exact HG0 | exact Hp]]).
  assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
  assert (HGO1 : GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1)).
  { apply (LGK cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 (ms_mem ms1) fpos HB HAR1 Hfin); [|exact PRES|exact HGO].
    intros a Ha _. apply KEEP; [lia|]. rewrite SP1, WS in *. lia. }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pmkst HS.
  set (mdc := with_vm_backing (m_vm_lazy md1) mat1 md1) in *.
  destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms1) mdc
    (fun a => gsp1 cx + 88 <= a < gsp1 cx + 96) HB HJ0 HROM1 HPK HFR HLK HLS HJ) as [HGL1 HLS1].
  { intros a Ha. right; right; left. exact Ha. }
  { exact KEEP. }
  { exact PRES. }
  pose proof HGL1 as (fpos1 & Hpg & HJg & HROMc & HPKc & HFRc & HLKc).
  pose proof (tj_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg) as HARc.
  assert (V88 : val_mem SEGS (arm W1 (ms_mem ms1)) (gsp1 cx + 88) 8 (Z.of_nat i)).
  { unfold arm. replace (gsp1 cx + 88) with (bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 9) + 88)
      by (rewrite !ew_ewset_other, U9E by lia; reflexivity).
    eapply (field_of_region _ _ 9 _ _ 88 96 88 96 88 8%N (SOff 14 0) (Z.of_nat i) RG1); [reflexivity | left; reflexivity | | cbn; lia | cbn; lia].
    cbn [sv_denot]. rewrite !ew_ewset_other, (EEo 14%nat 14%bv eq_refl), R14 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  pose proof HGO1 as (_ & _ & _ & _ & Hout1 & _).
  pose proof HPRE as (_ & _ & _ & HGP0 & HTP0 & _).
  pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcl & Hbr & Hdd & _ & Hmx & _ & Hcapd).
  assert (Hcap0 : 0 <= cap2) by (destruct Hcapd as [(-> & _) | (Hc0 & _)]; lia).
  destruct (LDP cx i qd c2 O2 cap2 out2 spent ly1 S1 Hpg W1 (ms_mem ms1) mdc HB Hi Heof0 HGO1 HARc)
    as (DTab & DG1 & DG2 & DGA & DAW & DEOK & DSRC & DPERM).
  pose proof DSRC as (Dj & Dasrc & Doth & Dfd & Dsk & DU & Db1 & Db2 & Db3).
  destruct (LDI ly1 S1 W1 (ms_mem ms1) (gnth cx i) (fst (ghj cx i)) (snd (ghj cx i)) (Z.of_nat (length O2)) cap2 DEOK DSRC) as [DINV DREST].
  destruct (LTR cx i qd c2 O2 cap2 spent ly1 S1 HB Hi Hlq Heof0 Hrel Hcl Hbr Hdd Hcap0 Hmx DINV DREST Hbud)
    as (RM1 & RM2 & RM3 & RM4 & RM5).
  pose proof HFRc as (_ & _ & _ & _ & _ & _ & HSV1).
  destruct (tp_achain_call cx ly1 W1 (ms_mem ms1) HB HSV1
    ltac:(eapply tp_ly_top_xR; exact HJg)
    ltac:(intros a Ha; eapply gse_keep_high_xR; [exact HGRIG | exact HJg | lia | rewrite WS; lia])) as (ch1 & Hch1).
  pose proof (LFP cx i qd c2 O2 cap2 out2 spent ly1 S1 Hpg W1 (ms_mem ms1) mdc HB Hi Heof0 HGO1 HARc) as HFP1.
  assert (Usp1 : spZ (ms_regs ms1) = gsp1 cx) by (unfold spZ; rewrite HK by (cbv; tauto); exact Hsp1).
  eapply (YA0nH.SRrG_bind SEGS R R_trans).
  { eapply (gse_callS_xR B PST ARx LAWS R R_trans (G_RIG B RG) W1 (ms_regs ms1) (ms_mem ms1) _ RIG_STK_x (gsp0 cx) (gFP cx)
      (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos1)] ly1 S1 Hpg mdc k1 DRAIN_STK_x
      (dr_fp (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2) (-224) (Z_to_bv 64 (BASE + 2788)) ch1
      (fun ly2 S2 W2 regs2 mem2 md2 => exists Hpd kd,
         ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (gsp1 cx)
           (dr_fp (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2) ly1 S1 Hpg W1 (ms_mem ms1) mdc [] ly2 S2 Hpd W2 mem2 md2 kd /\
         DRK cx i c2 O2 cap2 out2 ly1 S1 W1 (ms_mem ms1) ly2 S2 W2 mem2 /\
         rp_RM RP S2 (dr_kr cx i c2 (Z.of_nat (length O2)) cap2))
      HGRIG HJg).
    - rewrite Usp1. unfold gsp1, RIG_FRAME. lia.
    - reflexivity.
    - lia.
    - unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia.
    - unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia.
    - rewrite HK by (cbv; tauto). rewrite Hgp1. exact HGP0.
    - rewrite HK by (cbv; tauto). rewrite Htp1. exact HTP0.
    - exact N1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - replace (gsp0 cx + -224) with (gsp1 cx) by (unfold gsp1, RIG_FRAME; lia).
      replace (s0Z (ms_regs ms1)) with (gsp0 cx) by (unfold s0Z; rewrite HK by (cbv; tauto); rewrite H8; unfold w64;
        rewrite unsigned_lit_small by (unfold gsp0 in *; lia); reflexivity).
      exact Hch1.
    - intros HPRE1. eapply (YA0nH.SRrG_mono SEGS R).
      { eapply (DRAIN_R W1 ly1 S1 Hpg (ms_regs ms1) (ms_mem ms1) mdc ch1 G0 SA (gnth cx i) (snd (ghj cx i)) (fst (ghj cx i)) c2 O2
          (gxmx cx) (Z.of_nat (length O2)) cap2 out2 HPRE1).
        + rewrite N10, E33. reflexivity.
        + exact DTab.
        + exact DG1.
        + exact DG2.
        +
          unfold SA. exact (tp_sa_align ly1 S1 Hpg W1 (ms_mem ms1) mdc G0 i HARc DTab).
        + exact DGA.
        + exact DAW.
        + exact DEOK.
        + exact Dj.
        + exact Dasrc.
        + exact Doth.
        + exact Dfd.
        + exact Dsk.
        + exact DU.
        + exact Hout1.
        + exact HROMc.
        + exact DPERM.
        + exact Db1.
        + exact Db2.
        + exact Db3.
        + exact RM1.
        + exact RM2.
        + exact RM3.
        +
          exact RM4.
        + exact RM5. }
      cbv beta. intros W3 c3 _ (ly' & S' & Hp' & regs' & mem' & md' & kd & e' & h' & out' & ev' & LB & rest & -> & HJd & HPr &
        HAK & HMO & HRMd & HP1 & HP2 & HGA & HAW & HEOK & Hrfd & Hreo & Hcp & Hcp2 & HU & Hsk' & Hkt & Hka & Hhk & HNDd & HSS &
        Has & Hslot & Hec & Hec2 & Hhfd & Hhcl & Hei & Hrec & Hoff & Hv & Hpc & Hpart & Hst & Hmap & Hfirst & Hheld & Hsk2 &
        HU2 & HLB & Hao).
      exists ly', S', Hp', regs', mem', md', kd. split; [rewrite N1; reflexivity|].
      split; [eapply rig_lift_DR_xR; exact HJd|]. split; [exact HPr|].
      exists Hp', kd. split; [rewrite <- Usp1; exact HJd|].
      split; [|exact HRMd].
      unfold DRK. cbv zeta. exists e', h', out', ev', LB, rest.
      split; [exact HAK|]. split; [exact HMO|]. split; [exact HP1|]. split; [exact HP2|].
      split; [exact HGA|]. split; [exact HAW|]. split; [exact HEOK|].
      split; [unfold dr_rel; cbv zeta; repeat (split; [assumption|]); assumption|].
      split; [exact Has|]. split; [exact Hslot|]. exact Hao.
    - exact HFP1. }
  cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & -> & HJ3 & HJc3 & HP3 &
    (Hpd & kd & HJd & HDRK & HRMd)).
  pose proof HPRE as (_ & _ & _ & _ & _ & HAS0 & _). pose proof HAS0 as (_ & _ & As3 & As4 & _).
  assert (HCEIL : alloc_ceiling <= gsp1 cx - DRAIN_STK_x).
  { fold (gsp0 cx) in As4. rewrite WS in As4. unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia. }
  destruct (LRO cx i qd c2 O2 cap2 out2 spent ly1 S1 Hpg W1 (ms_mem ms1) mdc (gsp1 cx) ly3 S3 Hpd W3 mem3 md3 kd HB Hi Heof0
    HGO1 HARc HJd HCEIL HDRK) as (e1 & h1 & ev & LB & out1 & HTM).
  pose proof HTM as (_ & _ & _ & HGD & _).
  pose proof HDRK as (e' & h' & out' & ev' & LB' & rest & HAK' & HMO' & HP1' & HP2' & _ & _ & HEOK' & HREL' & _).
  pose proof (LDB ly1 S1 W1 (ms_mem ms1) ly3 S3 c2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 out' (gnth cx i) (fst (ghj cx i))
    e' h' LB' rest _ DEOK Dasrc Hcap0 Hmx ltac:(lia) DINV DREST HP1' HP2' HREL') as HBB.
  assert (HCNT3 : forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) =
    Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (dr_tr c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i)))).
  { intros P.
    pose proof (LDC c2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 out' (gnth cx i) (fst (ghj cx i)) e' h' LB' P
      DINV DREST (td_hk _ _ _ _ _ DEOK) (td_hk _ _ _ _ _ HEOK') Hcap0 HREL') as ECN. cbv zeta in ECN.
    rewrite (ReplyCnt.acnt_perm P _ _ HP2'), (ReplyCnt.acnt_perm P _ _ HP1'), !ReplyCnt.acnt_app.
    rewrite !ReplyCnt.acnt_app in ECN. lia. }
  pose proof (LBU cx i qd c2 O2 cap2 spent ly1 S1 ly3 S3 e1 h1 ev LB _ _ _ HB Hi Hlq Hrel Hcl Hbr Hdd Hcap0 Hmx Hbud HGD)
    as HBU.
  specialize (HBU ltac:(intros _; split; [exact DINV | split; [exact DREST | split; [exact HMO' |
      split; [exact HBB | split; [exact HRMd | exact HCNT3]]]]])
    ltac:(intros X; rewrite Heof0 in X; discriminate X)).
  destruct (LLD cx fpos1 F FL ly1 S1 Hpg W1 (ms_mem ms1) mdc k1 (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2 ly3 S3 Hpd
    W3 mem3 md3 kd Hp3
    (k1 + k3) HB HJg HROMc HPKc HFRc HLKc HLS1 HJd) as [HGL3 HLS3].
  { intros a Ha. destruct (HFP1 a Ha) as [(_ & Hb) | (b & n & Hin & _ & Hr)]; [exact Hb | exists b, n; split; [exact Hin | exact Hr]]. }
  { exact HAK'. }
  { exact HJ3. }
  assert (V88' : val_mem SEGS (arm W3 mem3) (gsp1 cx + 88) 8 (Z.of_nat i)).
  { unfold arm in *. eapply val_mem_kept; [|exact V88]. intros kk Hkk.
    eapply gse_keep_high_xR; [exact HGRIG | exact HJc3 | unfold gsp1, RIG_FRAME, gsp0 in *; lia | unfold gsp1, RIG_FRAME in *; lia]. }
  apply KPD. unfold PD_xR.
  exists regs3, ly3, S3, mem3, md3, (k1 + k3), F, FL, qd, c2, O2, cap2, e1, h1, ev, LB.
  do 3 eexists. exists out1. eexists.
  split; [unfold cfg_at, A_rig_pd; reflexivity|].
  split.
  { unfold gregs_base. unfold spZ.
    rewrite (tp_pres _ _ 2 2%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 3 3%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 4 4%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 8 8%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 9 9%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite (tp_pres _ _ 18 18%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)).
    rewrite !HK by (cbv; tauto). exact HRB. }
  split; [rewrite (tp_pres _ _ 20 20%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto); exact R20|].
  split; [rewrite (tp_pres _ _ 21 21%bv HP3 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto); exact R21|].
  split; [rewrite (tp_pres _ _ 22 22%bv HP3 eq_refl ltac:(unfold acallee_saved; lia));
          change 325%nat with (A_HI 45) in N22; rewrite N22, (img_env_atomP E (A_HI 45) HEI ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH45; reflexivity|].
  split; [rewrite (tp_pres _ _ 19 19%bv HP3 eq_refl ltac:(unfold acallee_saved; lia));
          rewrite N19, (EEo 14%nat 14%bv eq_refl), R14; apply bv_eq; unfold mul_div; rewrite bv_mul_unsigned, !Z_to_bv_unsigned;
          unfold bv_wrap, AENT; change (bv_modulus 64) with (2 ^ 64);
          rewrite (Z.mod_small (Z.of_nat i)), (Z.mod_small 56), (Z.mod_small (Z.of_nat i * 56)), (Z.mod_small (56 * Z.of_nat i)) by lia; lia|].
  split; [exact V88'|].
  split; [exact HGL3|]. split; [exact HLS3|]. split; [exact HTM | exact HBU].
Qed.
(* W_rig_top.v:4125 top_p2 at R *)
Lemma top_p2_xR :
stmt_gtopm_kept -> stmt_live_kept_xR -> stmt_gin_top -> stmt_gout_top ->
stmt_snp_call_xR -> stmt_strlen_call_xR ->
forall cx i W1 c1,
GBASE B ARx MT RP MMAX RG cx -> PD_xR cx i W1 c1 ->
(forall r W2 c2, RGI_xR B PST ARx MT RP MMAX RG R cx i 0 r W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (gPOST_xR B PST ARx MT RP RG R cx)) ->
(forall W2 c2, RGE_xR B PST ARx MT RP MMAX RG R cx i W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (gPOST_xR B PST ARx MT RP RG R cx)) ->
YA0nH.SRrG SEGS R W1 c1 (gPOST_xR B PST ARx MT RP RG R cx).
Proof.
intros LTK LLK LGI LGO LSC LSL cx i W1 c1 HB HPD KI KE.
destruct HPD as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & e1 & h1 & ev & LB & c1' & O1 & cap1 & out1 & spent &
  -> & HRB & R20 & R21 & R22 & R19 & V88 & HGL & HLS & HTM & HBU).
pose proof HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H18).
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RID & _).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HLS as (L40 & L48 & L56 & L64 & L72).
pose proof HFR as (HFa & HFLa & HF120 & HF16 & HF24 & HF80 & HSV).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (SP1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
pose proof HPRE as (_ & _ & _ & HGP0 & HTP0 & HAS0 & _). pose proof HAS0 as (_ & _ & As3 & As4 & As5 & As6 & _).
fold (gsp0 cx) in As4, As5. rewrite WS in As4.
assert (SPB : alloc_ceiling + 17200 <= gsp0 cx <= 2 ^ 47) by lia.
assert (Hsp32 : gsp1 cx mod 32 = 0) by (rewrite SP1; rewrite Zminus_mod, H32; reflexivity).
destruct (tl2_frm_xR cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof HFapp as HFA. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFA.
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *. rewrite HFa in HFal, HFpres, HFSpres.
pose proof HTM as (Hi & Hlq & Hrel & HGD & Hrly & Hout & Hdone & Hsrc1 & Hdrs & Hgs & Hperm).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HREL0 & _). pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen0 & _).
pose proof Hrly as (RS1 & _ & _ & _ & _ & _ & Rlen & RSG & (tail & _ & _ & Rtab) & Rok & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 RSG) as (HG16 & HG4096 & HGc & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in HGc, HGapp, HGpres.
assert (SRCI : in_img SEGS (rg_src RG)) by (apply (proj1 (RGIMG (rg_src RG) ltac:(unfold rg_rng; right; right; left; lia)))).
assert (SRCI7 : in_img SEGS (rg_src RG + 7)) by (apply (proj1 (RGIMG (rg_src RG + 7) ltac:(unfold rg_rng; right; right; left; lia)))).
pose proof (pa_img_range (rg_src RG) SRCI) as SRCr. pose proof (pa_img_range (rg_src RG + 7) SRCI7) as SRCr7.
set (G0 := gxG0 cx) in *.
set (idv := bv_unsigned (getr (gxregs cx) 10)) in *.
assert (Hshv : shadow_addr F = SB + F / 8) by (unfold shadow_addr, SB; reflexivity).
assert (HF8 : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8b.
assert (Hsh4 : (SB + F / 8) mod 4 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HFal, Z.add_0_r in D.
  assert (F / 8 = 4 * (F / 32)) by (rewrite D at 1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring; apply Z.div_mul; lia).
  assert (SB mod 4 = 0) by reflexivity. pose proof (Z.div_mod SB 4 ltac:(lia)).
  replace (SB + F / 8) with ((SB / 4 + F / 32) * 4) by lia.
  apply Z_mod_mult. }
pose proof (tp_seat2 W1 regs1 m1 G0 idv (gsp1 cx) (shadow_addr F)) as HS.
specialize (HS ltac:(rewrite R22, HH45; reflexivity)
  ltac:(rewrite H9; unfold w64; apply unsigned_lit_small; lia) H18
  ltac:(rewrite R21; unfold w64; apply unsigned_lit_small; rewrite Hshv; unfold SB; lia)
  ltac:(rewrite Hshv; unfold SB; lia) ltac:(rewrite Hshv; exact Hsh4)
  ltac:(rewrite <- RGSRC; lia) ltac:(rewrite <- RGSRC; lia)
  ltac:(rewrite SP1; lia) ltac:(rewrite SP1; lia) Hsp32
  ltac:(unfold G0; lia) ltac:(unfold idv; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 10)) as RR; change (bv_modulus 64) with (2 ^ 64) in RR; exact RR)
  ltac:(rewrite <- RGSRC; exact RS1) L56 L64 HF80
  ltac:(intros o Ho; exact (proj1 (HFSpres o ltac:(lia))))).
remember (Eimg (Ereg regs1 (tp_extra2 G0 idv))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (tp_extra2 G0 idv)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 G0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
clear HE.
assert (U21 : bv_unsigned (ew E 21) = shadow_addr F)
by (rewrite (EEo 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; rewrite Hshv; unfold SB; lia).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W1) m1)) by constructor.
unfold cfg_at. change (w64 (BASE + A_rig_pd)) with (Z_to_bv 64 (BASE + A_rig_pd)).
pose proof HJ as HJ0.
paj_run_tok_xR RUN_R HS HJ SHOK tp_Bspan0.
{ apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite U21 in Ha.
  left. split; [|lia]. right; right; right. exists 1, fpos. split; [left; reflexivity|].
  right. rewrite HFa. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. lia. }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as RGS. cbn [ms_mem restrict] in RGS.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE2 : env_agree 32 (Ereg regs1 (tp_extra2 G0 idv)) Ex)
  by (repeat first [exact HAE | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 20; 21]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
pmkst HS.
prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13.
prreg HS (14%bv : bv 5) N14. prreg HS (1%bv : bv 5) N1. prreg HS (19%bv : bv 5) N19.
assert (ZSv : forall o, 4 <= o < 10 -> val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) (shadow_addr F + o) 1 0).
{ intros o Ho. rewrite <- U21.
  assert (Ho' : o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/ o = 9) by lia.
  destruct Ho' as [-> | [-> | [-> | [-> | [-> | ->]]]]];
  (eapply (field_of_region _ _ 21 _ _ 4 10 4 10 _ 1%N (SLit 0) 0 RGS); [reflexivity | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia]). }
assert (ZS : forall o, 4 <= o < 10 -> aview SEGS (w_H W1) (ms_mem ms1) (shadow_addr F + o) = Some 0)
by (intros o Ho; apply aview_of_val_mem1; [exact (ZSv o Ho) | lia]).
tp_nw HFr1 NW1 (fun a => shadow_addr F + 4 <= a < shadow_addr F + 10) U21.
assert (ROM1 : rom_view SEGS W1 (ms_mem ms1)).
{ intros a Hin.
  assert (HI : 0x10000 <= a < 0x5fb000)
    by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
  rewrite (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 a ltac:(lia) (NW1 a ltac:(rewrite Hshv; unfold SB; lia))).
  exact (HROM1 a Hin). }
eapply (LSC W1 (ms_regs ms1) (ms_mem ms1) (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) fpos
  ly1 S1 _ _ k1
  (Z_to_bv 64 (BASE + 2844)) F (gxID cx) idv (gPOST_xR B PST ARx MT RP RG R cx) HJ).
- unfold spZ. rewrite HK by (cbv; tauto). fold (spZ regs1). rewrite Hsp1, SP1. reflexivity.
- pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
  replace (32 * (gsp0 cx / 32)) with ((2 * (gsp0 cx / 32)) * 16) by ring. apply Z_mod_mult.
- rewrite HK by (cbv; tauto). rewrite Hgp1. exact HGP0.
- rewrite HK by (cbv; tauto). rewrite Htp1. exact HTP0.
- exact N1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite N10, (EEo 20%nat 20%bv eq_refl). exact R20.
- rewrite N11. reflexivity.
- change 261%nat with (A_OBJ 20) in N12. rewrite N12, (img_env_atomP E (A_OBJ 20) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). reflexivity.
- change 262%nat with (A_OBJ 21) in N13. rewrite N13, (img_env_atomP E (A_OBJ 21) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). reflexivity.
- rewrite N14, E33. reflexivity.
- unfold idv. rewrite H10. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
- exact RID.
- exact HFa.
- exact ZS.
- exact ROM1.
- intros regs2 mem2 md2 HJ2 HP2 HR2 HPRE2 HKP2 HPS2.
  assert (P2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms1) r)
  by (intros r Hr; exact (tp_pres _ _ _ r HP2 eq_refl Hr)).
  pose proof (tp_seat3 W1 regs2 mem2) as HS3.
  remember (Eimg (Ereg regs2 [])) as E3 eqn:HE3.
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
  assert (HAE3 : env_agree 32 (Ereg regs2 []) E3)
  by (rewrite HE3; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE3 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E3 m = getr regs2 rr)
  by (intros m rr Hm; subst E3; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
  rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  clear HE3.
  assert (SHOK3 : sh_ok SEGS (SOff 18 0) [] E3 (mrestrict (w_H W1) mem2)) by constructor.
  paj_run_tok_xR RUN_R HS3 HJ2 SHOK3 tp_Bspan0. { apply awr_ok_x_nil. }
  rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 20; 21]%bv HS3 HAE3 ltac:(vm_compute; reflexivity)) as HK3.
  cbn [ms_regs restrict] in HK3.
  pmkst HS3.
  prreg HS3 (10%bv : bv 5) Q10. prreg HS3 (1%bv : bv 5) Q1.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem2 a)
  by (intros a Ha; apply (aview_kept_out E3 _ (w_H W1) mem2 (ms_mem ms2) HFr2 a Ha); intros (r & Hin & _); destruct Hin).
  assert (U2s : spZ (ms_regs ms1) = gsp1 cx) by (unfold spZ; rewrite HK by (cbv; tauto); exact Hsp1).
  assert (Hsc1 : forall a, 0 <= a < alloc_ceiling -> ~ (gsp0 cx - 224 - 3 * ESTACK <= a < gsp0 cx - 224)) by (intros a Ha Hs; lia).
  destruct (tp_pre_nz cx) as (PNZ & PL1 & PL2).
  eapply (LSL W1 (ms_regs ms2) (ms_mem ms2) (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) fpos
    ly1 S1 _ _ k1
    (Z_to_bv 64 (BASE + 2852)) F (gpre cx) (gPOST_xR B PST ARx MT RP RG R cx) HJ2).
  + unfold spZ. rewrite (HK3 2%bv ltac:(cbv; tauto)). rewrite (tp_pres _ _ 2 2%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)). fold (spZ (ms_regs ms1)). rewrite U2s, SP1. reflexivity.
  + pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
    replace (32 * (gsp0 cx / 32)) with ((2 * (gsp0 cx / 32)) * 16) by ring. apply Z_mod_mult.
  + rewrite (HK3 3%bv ltac:(cbv; tauto)). rewrite (tp_pres _ _ 3 3%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto). rewrite Hgp1. exact HGP0.
  + rewrite (HK3 4%bv ltac:(cbv; tauto)). rewrite (tp_pres _ _ 4 4%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto). rewrite Htp1. exact HTP0.
  + exact Q1.
  + apply ret_ok_codeptr_v; [lia | reflexivity].
  + rewrite Q10, (EE3 20%nat 20%bv eq_refl), (tp_pres _ _ 20 20%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)), HK by (cbv; tauto). exact R20.
  + exact HFa.
  + unfold arm in *. eapply rk_garr8_kv_tp; [exact HPRE2|]. intros b Hb. apply K3. rewrite length_app in Hb. cbn [length] in Hb. lia.
  + exact PNZ.
  + lia.
  + intros o Ho. rewrite K3 by (rewrite Hshv; unfold SB; lia).
    rewrite HKP2; [exact (ZS o Ho) | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; lia | rewrite Hshv; apply Hsc1; unfold SB; lia].
  + intros a Hin.
    assert (HI : 0x10000 <= a < 0x5fb000)
      by (destruct Hin as (sg & Hsg & _ & Hr); exact (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hr]))).
    rewrite K3 by lia. rewrite HKP2; [exact (ROM1 a Hin) | lia | | apply Hsc1; lia].
    intros Hb. apply (HFni a ltac:(lia)). destruct Hin as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
  + intros regs4 mem4 md4 HJ4 HP4 HR4 HKP4 HPS4.
    assert (G19 : getr regs4 19 = getr (ms_regs ms1) 19).
    { rewrite (tp_pres _ _ 19 19%bv HP4 eq_refl ltac:(unfold acallee_saved; lia)), (HK3 19%bv ltac:(cbv; tauto)).
      exact (tp_pres _ _ 19 19%bv HP2 eq_refl ltac:(unfold acallee_saved; lia)). }
    assert (GR : forall (r : bv 5) n, bv_unsigned r = n -> acallee_saved n -> In r [2; 3; 4; 8; 9; 18; 19; 20; 21]%bv ->
      getr regs4 r = getr (ms_regs ms1) r).
    { intros r n Hn Hc Hin. rewrite (tp_pres _ _ n r HP4 Hn Hc), (HK3 r Hin). exact (tp_pres _ _ n r HP2 Hn Hc). }
    set (SA := G0 + AENT * Z.of_nat i) in *.
    assert (U19 : bv_unsigned (getr regs4 19) = SA).
    { rewrite G19, N19, (EEo 19%nat 19%bv eq_refl), E32, R19. unfold w64.
      rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      unfold SA, AENT. rewrite (Z.mod_small (56 * Z.of_nat i)), (Z.mod_small G0), Z.mod_small by lia. lia. }
    assert (KEEP14 : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
      aview SEGS (w_H W1) mem4 a = aview SEGS (w_H W1) m1 a).
    { intros a Ha Hnf.
      assert (Nsh : ~ (shadow_addr F + 4 <= a < shadow_addr F + 10)).
      { intros Hs. apply Hnf. exists 1, fpos. split; [left; reflexivity|]. right. rewrite HFa. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1 / 8) with 16. lia. }
      assert (Nbf : ~ (F + 32 <= a < F + 80)).
      { intros Hs. apply Hnf. exists 1, fpos. split; [left; reflexivity|]. left. rewrite HFa. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1) with 128. lia. }
      rewrite HKP4 by lia. rewrite K3 by lia. rewrite HKP2 by lia.
      exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 a ltac:(lia) (NW1 a Nsh)). }
    assert (PRES14 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mem4 a).
    { intros a Hp. apply HPS4. eapply apresent_grows; [exact HG2|]. apply HPS2. eapply apresent_grows; [exact HG1 | exact Hp]. }
    pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 mem4 fpos HB HAR1 Hfin KEEP14 PRES14 HTM) as HTM4.
    pose proof HTM4 as (_ & _ & _ & _ & Hrly4 & _).
    pose proof Hrly4 as (_ & _ & _ & _ & _ & _ & _ & _ & (tail4 & _ & _ & Rtab4) & Rok4 & _).
    assert (HLmq : length (map fst qd) = i) by (rewrite length_map; exact Hlq).
    assert (Hok4 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (map fst qd ++ e1 :: skipn (S i) (gxes cx))).
    { eapply Forall_impl; [|exact Rok4]. intros e (_ & _ & Q1' & Q2' & _). split; assumption. }
    assert (Hnth : nth i (map fst qd ++ e1 :: skipn (S i) (gxes cx)) relay_remove_b_c.no_entry = e1).
    { rewrite app_nth2 by lia. rewrite HLmq, Nat.sub_diag. reflexivity. }
    assert (HLtab : (i < length (map fst qd ++ e1 :: skipn (S i) (gxes cx)))%nat) by (rewrite length_app, HLmq; cbn [length]; lia).
    pose proof (tp_table_entry _ _ _ _ i Rtab4 Hok4 HLtab) as HTE4. rewrite Hnth in HTE4.
    assert (HEOK4 : aentry_ok B ly1 S1 W1 mem4 e1).
    { rewrite Forall_forall in Rok4. apply Rok4. apply in_or_app. right. left. reflexivity. }
    pose proof HEOK4 as (_ & _ & Hp14 & _ & _ & _ & _ & _ & _ & _ & Hnh26 & _).
    assert (Hnh0 : 0 <= re_nheld e1) by (unfold re_nheld; lia).
    pose proof (tp_entry_nheld _ _ _ HTE4 Hp14 ltac:(lia)) as VN4.
    fold SA in VN4.
    assert (HSAb : 4096 <= SA /\ SA + 56 <= alloc_ceiling) by (unfold SA, AENT; lia).
    pose proof (tj_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
    assert (U9r : bv_unsigned (getr regs4 9) = gsp1 cx).
    { rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto). rewrite H9.
      unfold w64. apply unsigned_lit_small. lia. }
    assert (R18r : getr regs4 18 = w64 SHADOW_OFF).
    { rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto). exact H18. }
    assert (HSAm : SA mod 8 = 0).
    { unfold SA, AENT. pose proof (Z.div_mod G0 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
      replace (G0 + 56 * Z.of_nat i) with ((2 * (G0 / 16) + 7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
    pose proof (tp_seat4 W1 regs4 mem4 SA (gsp1 cx) (re_nheld e1) U19 U9r R18r) as HS4.
    specialize (HS4 ltac:(unfold SA, AENT; lia) ltac:(unfold SA, AENT; lia) HSAm ltac:(lia) ltac:(lia) Hsp32 ltac:(lia)
      ltac:(unfold arm in VN4; exact VN4)
      ltac:(intros o Ho; eapply tj_pres_xR; [exact HJ4 | rewrite WS; lia])).
    remember (Eimg (Ereg regs4 [Z_to_bv 64 (re_nheld e1)])) as E4 eqn:HE4.
    assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
    assert (HAE4 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) E4)
    by (rewrite HE4; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE4 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E4 m = getr regs4 rr)
    by (intros m rr Hm; subst E4; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
    rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
    assert (E4_32 : ew E4 32 = Z_to_bv 64 (re_nheld e1)) by (subst E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
    clear HE4.
    assert (HBx4 : U E4 (SOff 18 0) = SHADOW_OFF) by (rewrite (U_atom E4 18 SHADOW_OFF ltac:(rewrite (EE4 18%nat 18%bv eq_refl); exact R18r)) by (unfold SHADOW_OFF; lia); reflexivity).
    assert (SHOK4 : sh_ok SEGS (SOff 18 0) tp_SH4 E4 (mrestrict (w_H W1) mem4)).
    { constructor; [|constructor].
      eapply shent_ok_of_range.
      + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 _ W1 mem4 _ G0 ATABLE (SA + 48) 4 HAR4 RSG);
        [unfold SA, AENT; lia | rewrite RQT; unfold SA, AENT; lia].
      + exact HBx4.
      + rewrite (U_atom E4 19 SA) by (first [rewrite (EE4 19%nat 19%bv eq_refl); rewrite <- U19; symmetry; apply Z_to_bv_bv_unsigned | unfold SA, AENT; lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. pose proof HGapp as HGA. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. unfold SA, AENT in *. lia. }
    pose proof HJ4 as HJ40.
    paj_run_tok_xR RUN_R HS4 HJ4 SHOK4 tp_Bspan.
    { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
      apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite (EE4 9%nat 9%bv eq_refl), U9r in Ha.
      left. split; [left; rewrite SP1, WS in *; lia | lia]. }
    rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
    rename w into w5a, w0 into w5b.
    assert (E5_32 : sv_denot (ewset (ewset E4 512 w5a) 513 w5b) (SOff 32 0) = Z_to_bv 64 (re_nheld e1))
    by (cbn [sv_denot]; rewrite !ew_ewset_other, E4_32, Z.add_0_r, Z_to_bv_bv_unsigned by lia; reflexivity).
    psrr_branch_tok RUN_R BR_R HS4 SHOK4 tp_Bspan.
    * rewrite (tp_branch_ge (ewset (ewset E4 512 w5a) 513 w5b) (SLit 0) (SOff 32 0) 0 (re_nheld e1) eq_refl E5_32 ltac:(lia) ltac:(lia)) in Hc.
      assert (Hnh00 : re_nheld e1 <= 0) by (destruct (Z.ltb_spec 0 (re_nheld e1)); [discriminate Hc | lia]).
      paj_run_to_tok_xR RUNTO_R HS4 HJ4 SHOK4 tp_Bspan (AF_fr_relay_instance_gone + 0x318).
      { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
        apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite !ew_ewset_other, (EE4 9%nat 9%bv eq_refl), U9r in Ha by lia.
        left. split; [left; rewrite SP1, WS in *; lia | lia]. }
      rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
      assert (U9E4 : bv_unsigned (ew E4 9) = gsp1 cx) by (rewrite (EE4 9%nat 9%bv eq_refl); exact U9r).
      assert (U9E5 : bv_unsigned (ew (ewset (ewset E4 512 w5a) 513 w5b) 9) = gsp1 cx) by (rewrite !ew_ewset_other by lia; exact U9E4).
      tp_nw HFr5 NW5 (fun a => gsp1 cx + 32 <= a < gsp1 cx + 40) U9E4.
      tp_nw HFr6 NW6 (fun a => gsp1 cx + 32 <= a < gsp1 cx + 40) U9E5.
      assert (K56 : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx + 32 <= a < gsp1 cx + 40) ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) mem4 a)
      by (intros a Ha Na; exact (tp_kept2 _ _ _ _ _ _ _ _ a HFr5 HFr6 Ha (NW5 a Na) (NW6 a Na))).
      set (PF := fun a => (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (F + 32 <= a < F + 80) \/
        (shadow_addr F + 4 <= a < shadow_addr F + 10) \/ (gsp1 cx + 32 <= a < gsp1 cx + 40)).
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ PF a -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Na. unfold PF in Na.
        rewrite K56 by tauto. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
        exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha (NW1 a ltac:(tauto))). }
      assert (PRESF : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms6) a).
      { intros a Hp. eapply apresent_grows; [exact HG6|]. eapply apresent_grows; [exact HG5|]. apply PRES14. exact Hp. }
      assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Hnf. apply KEEPF; [lia|]. unfold PF. intros [X | [X | [X | X]]]; [lia | | | lia]; apply Hnf; exists 1, fpos;
        (split; [left; reflexivity|]); rewrite HFa; unfold in_zr; cbn [fst snd];
        [left; change (fs_frame_bytes 1) with 128; lia | right; change (fs_frame_bytes 1 / 8) with 16; lia]. }
      pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 (ms_mem ms6) fpos HB HAR1 Hfin KEEPL PRESF HTM) as HTM6.
      destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms6) (with_vm_backing (m_vm_lazy md4) mat6 md4) PF HB HJ0 HROM1 HPK HFR HLK HLS HJ4)
        as [HGL6 HLS6].
      { intros a Ha. unfold PF in Ha. rewrite SP1 in *. lia. }
      { exact KEEPF. }
      { exact PRESF. }
      assert (V88F : val_mem SEGS (arm W1 (ms_mem ms6)) (gsp1 cx + 88) 8 (Z.of_nat i)).
      { unfold arm in *. eapply val_mem_kept; [|exact V88]. intros kk Hkk. apply KEEPF; [lia|]. unfold PF.
        rewrite Hshv. unfold SB. lia. }
      lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => assert (HAE6 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) Ex)
        by (repeat first [exact HAE4 | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs4 _ [2; 3; 4; 8; 9; 18; 20]%bv HS4 HAE6 ltac:(vm_compute; reflexivity)) as HK6.
      cbn [ms_regs restrict] in HK6.
      pmkst HS4.
      destruct (LGO cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent ly1 S1 W1 (ms_mem ms6) HB HTM6 HBU Hnh00) as (qd' & HGO').
      apply KE. unfold RGE_xR.
      exists (ms_regs ms6), ly1, S1, (ms_mem ms6), (with_vm_backing (m_vm_lazy md4) mat6 md4), k1, F, FL, qd', c1', O1, cap1, out1, spent.
      split; [unfold cfg_at, A_rig_step; reflexivity|].
      split.
      { unfold gregs_base, spZ. rewrite !HK6 by (cbv; tauto).
        rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite !HK by (cbv; tauto). exact HRB. }
      split; [rewrite HK6 by (cbv; tauto); rewrite (GR 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto); exact R20|].
      split; [exact V88F|]. split; [exact Hi|]. split; [exact HGL6|]. split; [exact HLS6 | exact HGO'].
    * rewrite (tp_branch_ge (ewset (ewset E4 512 w5a) 513 w5b) (SLit 0) (SOff 32 0) 0 (re_nheld e1) eq_refl E5_32 ltac:(lia) ltac:(lia)) in Hc.
      assert (Hnh01 : 0 < re_nheld e1) by (destruct (Z.ltb_spec 0 (re_nheld e1)); [lia | discriminate Hc]).
      paj_run_to_tok_xR RUNTO_R HS4 HJ4 SHOK4 tp_Bspan (AF_fr_relay_instance_gone + 0x224).
      { apply awr_ok_x_cons; [intros a Ha; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|].
        apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        intros a Ha. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite !ew_ewset_other, (EE4 9%nat 9%bv eq_refl), U9r in Ha by lia.
        left. split; [left; rewrite SP1, WS in *; lia | lia]. }
      rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
      assert (U9E4 : bv_unsigned (ew E4 9) = gsp1 cx) by (rewrite (EE4 9%nat 9%bv eq_refl); exact U9r).
      assert (U9E5 : bv_unsigned (ew (ewset (ewset E4 512 w5a) 513 w5b) 9) = gsp1 cx) by (rewrite !ew_ewset_other by lia; exact U9E4).
      tp_nw HFr5 NW5 (fun a => gsp1 cx + 32 <= a < gsp1 cx + 40) U9E4.
      tp_nw HFr6 NW6 (fun a => gsp1 cx + 32 <= a < gsp1 cx + 40) U9E5.
      assert (K56 : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx + 32 <= a < gsp1 cx + 40) ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) mem4 a)
      by (intros a Ha Na; exact (tp_kept2 _ _ _ _ _ _ _ _ a HFr5 HFr6 Ha (NW5 a Na) (NW6 a Na))).
      set (PF := fun a => (gsp1 cx - 3 * ESTACK <= a < gsp1 cx) \/ (F + 32 <= a < F + 80) \/
        (shadow_addr F + 4 <= a < shadow_addr F + 10) \/ (gsp1 cx + 32 <= a < gsp1 cx + 40)).
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ PF a -> aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Na. unfold PF in Na.
        rewrite K56 by tauto. rewrite HKP4 by (rewrite ?SP1 in *; lia). rewrite K3 by lia. rewrite HKP2 by (rewrite ?SP1 in *; lia).
        exact (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha (NW1 a ltac:(tauto))). }
      assert (PRESF : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms6) a).
      { intros a Hp. eapply apresent_grows; [exact HG6|]. eapply apresent_grows; [exact HG5|]. apply PRES14. exact Hp. }
      assert (KEEPL : forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a ->
        aview SEGS (w_H W1) (ms_mem ms6) a = aview SEGS (w_H W1) m1 a).
      { intros a Ha Hnf. apply KEEPF; [lia|]. unfold PF. intros [X | [X | [X | X]]]; [lia | | | lia]; apply Hnf; exists 1, fpos;
        (split; [left; reflexivity|]); rewrite HFa; unfold in_zr; cbn [fst snd];
        [left; change (fs_frame_bytes 1) with 128; lia | right; change (fs_frame_bytes 1 / 8) with 16; lia]. }
      pose proof (LTK cx i qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 (ms_mem ms6) fpos HB HAR1 Hfin KEEPL PRESF HTM) as HTM6.
      destruct (LLK cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 _ (ms_mem ms6) (with_vm_backing (m_vm_lazy md4) mat6 md4) PF HB HJ0 HROM1 HPK HFR HLK HLS HJ4)
        as [HGL6 HLS6].
      { intros a Ha. unfold PF in Ha. rewrite SP1 in *. lia. }
      { exact KEEPF. }
      { exact PRESF. }
      assert (V88F : val_mem SEGS (arm W1 (ms_mem ms6)) (gsp1 cx + 88) 8 (Z.of_nat i)).
      { unfold arm in *. eapply val_mem_kept; [|exact V88]. intros kk Hkk. apply KEEPF; [lia|]. unfold PF.
        rewrite Hshv. unfold SB. lia. }
      lazymatch type of HS4 with st_ok_pi _ _ ?Ex _ _ => assert (HAE6 : env_agree 32 (Ereg regs4 [Z_to_bv 64 (re_nheld e1)]) Ex)
        by (repeat first [exact HAE4 | apply tp_env_agree_ewset; [|lia] | apply env_agree_havoc_ge; [cbv; lia|]]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs4 _ [2; 3; 4; 8; 9; 18; 20]%bv HS4 HAE6 ltac:(vm_compute; reflexivity)) as HK6.
      cbn [ms_regs restrict] in HK6.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS4 eq_refl) as RG6. cbn [ms_mem restrict] in RG6.
      prreg HS4 (19%bv : bv 5) F19. prreg HS4 (21%bv : bv 5) F21. prreg HS4 (23%bv : bv 5) F23. prreg HS4 (22%bv : bv 5) F22.
      prreg HS4 (24%bv : bv 5) F24. prreg HS4 (25%bv : bv 5) F25. prreg HS4 (27%bv : bv 5) F27.
      pmkst HS4.
      assert (E19' : bv_unsigned (ew (ewset (ewset E4 512 w5a) 513 w5b) 19) = SA)
        by (rewrite !ew_ewset_other, (EE4 19%nat 19%bv eq_refl) by lia; exact U19).
      assert (E18' : ew (ewset (ewset E4 512 w5a) 513 w5b) 18 = w64 SHADOW_OFF)
        by (rewrite !ew_ewset_other, (EE4 18%nat 18%bv eq_refl) by lia; exact R18r).
      assert (E10' : ew (ewset (ewset E4 512 w5a) 513 w5b) 10 = w64 (Z.of_nat (length (gpre cx))))
        by (rewrite !ew_ewset_other, (EE4 10%nat 10%bv eq_refl) by lia; exact HR4).
      set (r := (Z.to_nat (re_nheld e1) - 1)%nat).
      assert (HNHr : re_nheld e1 = Z.of_nat (S r)) by (unfold r; lia).
      assert (HPREF : garr8 SEGS (arm W1 (ms_mem ms6)) (F + 32) (gpre cx ++ [0])).
      { unfold arm in *. eapply rk_garr8_kv_tp; [exact HPRE2|]. intros b Hb. rewrite length_app in Hb. cbn [length] in Hb.
        rewrite K56 by lia. rewrite HKP4 by (rewrite ?SP1 in *; lia). apply K3. lia. }
      assert (HZSF : garr8 SEGS (arm W1 (ms_mem ms6)) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]).
      { intros j Hj. cbn [length] in Hj. split; [|destruct j as [|[|[|[|[|[|j]]]]]]; cbn; lia].
        replace (nth j [0; 0; 0; 0; 0; 0] 0) with 0 by (destruct j as [|[|[|[|[|[|j]]]]]]; cbn; lia).
        replace (shadow_addr F + 4 + Z.of_nat j) with (shadow_addr F + (4 + Z.of_nat j)) by lia.
        unfold arm. eapply val_mem_kept; [|exact (ZSv (4 + Z.of_nat j) ltac:(lia))].
        intros kk Hkk. cbn in Hkk. replace (shadow_addr F + (4 + Z.of_nat j) + kk) with (shadow_addr F + (4 + Z.of_nat j)) by lia.
        rewrite K56 by (rewrite Hshv; unfold SB; lia). rewrite HKP4 by (rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia).
        rewrite K3 by (rewrite Hshv; unfold SB; lia).
        rewrite HKP2; [reflexivity | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; lia | rewrite Hshv; unfold SB; rewrite ?SP1 in *; lia]. }
      destruct (LGI cx i r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 out1 spent ly1 S1 W1 (ms_mem ms6) HB HTM6 HBU HNHr HPREF HZSF)
        as (ks & f & HGIN).
      apply (KI r). unfold RGI_xR.
      exists (ms_regs ms6), ly1, S1, (ms_mem ms6), (with_vm_backing (m_vm_lazy md4) mat6 md4), k1, F, FL, qd, cB, OB, capB, e1, h1, ev, LB,
        c1', O1, cap1, ks, [], f, c1', O1, cap1, out1, spent.
      split; [unfold cfg_at, A_rig_inner; reflexivity|].
      split.
      { unfold gregs_base, spZ. rewrite !HK6 by (cbv; tauto).
        rewrite (GR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite (GR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)).
        rewrite !HK by (cbv; tauto). exact HRB. }
      split; [rewrite F19; reflexivity|].
      split; [rewrite HK6 by (cbv; tauto); rewrite (GR 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbv; tauto)), HK by (cbv; tauto); exact R20|].
      split; [rewrite F21; reflexivity|].
      split; [rewrite F23, (EE4 19%nat 19%bv eq_refl), U19; reflexivity|].
      split; [rewrite F22, (EE4 19%nat 19%bv eq_refl), U19; apply (tp_sh_den2 (SA + 48)); [rewrite (EE4 18%nat 18%bv eq_refl); exact R18r | pose proof C1; lia]|].
      split; [rewrite F24, (EE4 10%nat 10%bv eq_refl); exact HR4|].
      split; [rewrite F25, (EE4 19%nat 19%bv eq_refl), U19; reflexivity|].
      split; [rewrite F27, (EE4 19%nat 19%bv eq_refl), U19; apply (tp_sh_den2 (SA + 40)); [rewrite (EE4 18%nat 18%bv eq_refl); exact R18r | pose proof C1; lia]|].
      split.
      { replace ((gSA cx i + 48) mod 8 + 3) with 3.
        2:{ change (gSA cx i) with SA. rewrite Zplus_mod, HSAm. reflexivity. }
        unfold arm. replace (gsp1 cx + 32) with (bv_unsigned (ew (ewset (ewset E4 512 w5a) 513 w5b) 9) + 32) by (rewrite U9E5; reflexivity).
        eapply (field_of_region _ _ 9 _ _ 32 40 32 40 32 8%N (SLit 3) 3 RG6); [reflexivity | left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
      split; [exact V88F|]. split; [exact HGL6|]. split; [exact HLS6 | exact HGIN].
Qed.
(* W_rig_top.v:4541 rig_top_of_cnt at R *)
Lemma rig_top_of_cnt_xR : stmt_dr_cnt -> rig_top_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros LDC. unfold rig_top_stmt_xR. intros cx i W1 c1 HB HO KI KE.
exact (top_p1_xR gout_kept top_rep_closed top_budget live_kept_xR top_drain_pre dr_inv_of top_room dr_fp_in top_rep_open_xR dr_bytes
  LDC live_drain_xR cx i W1 c1 HB HO
  (fun W2 c2 HPD => top_p2_xR gtopm_kept live_kept_xR gin_top gout_top snp_call_xR strlen_call_xR cx i W2 c2 HB HPD KI KE)).
Qed.
(* W_rig_top.v:4550 rig_top_proof at R: TOP concludes W_relay_instance_gone_cx.v rig_top_stmt_xR *)
Theorem rig_top_proof_xR : rig_top_stmt_xR B PST ARx MT RP MMAX RG R.
Proof. exact (rig_top_of_cnt_xR W_rr_m_dcnt.rmc_dr_cnt). Qed.
End wR.
End c.
End b.
End a.

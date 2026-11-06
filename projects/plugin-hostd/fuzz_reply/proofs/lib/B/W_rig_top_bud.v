(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan), track "bud": the statements of lib/B/W_rig_top_defs.v stmt_dr_inv_of, stmt_top_room and
   stmt_top_budget.  Ported from k3's image-A track (a working branch 80fffa8e840,
   lib/A/W_rig_top_bud.v); the proofs read only the plain model (lib/Prog) and the kit's model definitions, which
   image B shares with image A.  The plain-model lemmas k3's file took from lib/Prog/RelayCap.v, gestures_end_b.v and
   relay_instance_gone_b.v are copied here unchanged (prefix tbc_), so this file does not depend on those proofs.

   The budget of the walk (W_relay_instance_gone_cx.v gbud) is the plain model's request trace restarted at entry i
   with the address names (fun _ => ga0), base 0 and g_out ga0 (grest).  Its head entry unfolds
   (relay_instance_gone_b_lem.rig_gone_run_cons, here tb_split) into the drain's trace, the key run's trace and the
   run over the entries after it.  The facts below make the three pieces the walk's own: a trace's measures
   (tr_cost, tr_max; tr_peak and tr_net through W_tr_peak.v tr_sz_measures) read only its sizes, which do not depend
   on the addresses (tb_sh); every size is nonnegative (tb_nn); the liveness of a one-byte send is the same along the
   whole run (tb_live_ctl, tb_rel_live); drain's trace at its own liveness is the model's (tb_drain_go); the key
   run's g_nout / g_capout are the stream's after its sends (tb_sends); and a dead run does not read g_nout
   (tb_gone_false).  tb_core turns these into the budget after the drain step (gtop_bud).
   C3 (the peak form; the image-A twin's re-fit of lib/A/W_rig_top.v, mirrored): drain's room is a prefix of the
   remaining trace's peak (top_room, W_tr_peak.v tr_peak_app), and tb_core carries gbud's peak room across the drain
   step with tr_peak_app and drain's NET change (tb_sh_pn; tb_alloc_app is gone).
   ROUTE (b), STEP 3 (the image-A twin: a Theorem Labs lane's RIG_x round of lib/A/W_rig_top.v, commit f4cd818e98d): at the
   generic Section of W_relay_instance_gone_cx.v.  THE ROOM at the drain call: gbud's room over the remaining trace
   grest i splits at the drain (tr_cost MT_rk is additive and nonnegative, tb_rk_nn), so drain gets
   rp_RM RP S (Z.to_nat (dr_cost MT_rk ..) + dr_kr ..) and its post's rp_RM RP S' dr_kr is gbud's room after the drain
   (top_room / top_budget).  THE COUNTS: drain's count premise dr_pk is within gbud's (tr_peakP of a prefix), and the
   live counts move by tr_netP of drain's trace, which tr_peakP_app (lib/B/W_rr_m_dcnt.v part I0) turns into gbud's
   count bound over the rest (tb_core; tb_er_cnt / tb_sh_cnt: the count measures read the sizes only).
   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rig_top_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_tr_peak.
(* tr_netP and its laws: part I0 of lib/B/W_rr_m_dcnt.v, A's lib/A/W_tr_cnt.v names *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rr_m_dcnt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- plain-model helpers, copied unchanged (names prefixed tbc_) from lib/Prog/RelayCap.v, gestures_end_b.v
   (p3b_ker_cap) and relay_instance_gone_b.v (the gsh lemmas): those files are not built for image B. ---- *)
Section tbm.
Import send_line_c gesture_end_c RelayRunT RelayRunF ListTr RelayModel RelayKeys send_line_b_c gesture_end_b_c
  gestures_end_b_c drain_b_c relay_remove_b_c relay_instance_gone_b_c relay_instance_gone_b_lem.

Lemma tbc_rc_step : forall c0 c1 c2 n1 m n2,
  c1 <= Z.max c0 (2 * n1) -> c2 <= Z.max c1 (2 * m) -> n1 <= n2 -> m <= n2 -> c2 <= Z.max c0 (2 * n2).
Proof.
  intros c0 c1 c2 n1 m n2 H1 H2 H3 H4.
  pose proof (Z.max_spec c0 (2 * n1)). pose proof (Z.max_spec c1 (2 * m)). pose proof (Z.max_spec c0 (2 * n2)).
  lia.
Qed.

Lemma tbc_rc_if_f : forall {X : Type} (z : Z) (a b : X), z <> 0 -> (if z =? 0 then a else b) = b.
Proof. intros X z a b H. destruct (Z.eqb_spec z 0) as [E|E]; [contradiction | reflexivity]. Qed.

Lemma tbc_with_nul_cons_len : forall l ls,
  Z.of_nat (length (with_nul (l :: ls))) = Z.of_nat (length l) + 1 + Z.of_nat (length (with_nul ls)).
Proof. intros l ls. unfold with_nul. cbn [map concat]. rewrite !length_app. cbn [length]. lia. Qed.

Lemma tbc_sl_run_cap_le : forall f mx no cap rem j o,
  fst (snd (sl_run f mx no cap rem j o)) <= Z.max cap (2 * (no + rem)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o; [cbn [sl_run fst snd]; apply Z.le_max_l|].
  cbn [sl_run]. cbv zeta.
  destruct (rem <=? 0); [cbn [fst snd]; apply Z.le_max_l|].
  assert (Hn : (if negb (mx =? 0) && (mx <? rem) then mx else rem) <= rem).
  { destruct (negb (mx =? 0) && (mx <? rem)) eqn:E; cbv iota; [|lia].
    apply andb_prop in E as [_ E]. apply Z.ltb_lt in E. lia. }
  revert Hn. generalize (if negb (mx =? 0) && (mx <? rem) then mx else rem). intros n Hn.
  destruct (cap <? no + n); cbn [fst snd].
  - specialize (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (Ret j)).
    pose proof (Z.max_spec ((no + n) * 2) (2 * (no + n + (rem - n)))).
    pose proof (Z.max_spec cap (2 * (no + rem))). lia.
  - specialize (IH mx (no + n) cap (rem - n) j o).
    pose proof (Z.max_spec cap (2 * (no + n + (rem - n)))).
    pose proof (Z.max_spec cap (2 * (no + rem))). lia.
Qed.

Lemma tbc_send_line_cap_le : forall live mx NO CAP LEN,
  send_line_cap live mx NO CAP LEN <= Z.max CAP (2 * (NO + LEN)).
Proof.
  intros [|] mx NO CAP LEN.
  - exact (tbc_sl_run_cap_le (Z.to_nat LEN) mx NO CAP LEN 0%nat adr0).
  - exact (Z.le_max_l CAP (2 * (NO + LEN))).
Qed.

Lemma tbc_lines_run_cap_le : forall live mx ls no cap H ka j o ha ks,
  fst (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))) <=
  Z.max cap (2 * (no + Z.of_nat (length (with_nul ls)))).
Proof.
  intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks.
  - cbn [lines_run snd fst]. apply Z.le_max_l.
  - cbn [lines_run]. cbv zeta. cbn [snd fst]. rewrite tbc_with_nul_cons_len.
    apply (tbc_rc_step cap (send_line_cap live mx no cap (Z.of_nat (length l) + 1)) _ (no + (Z.of_nat (length l) + 1))
             (no + (Z.of_nat (length l) + 1) + Z.of_nat (length (with_nul ls))));
      [apply tbc_send_line_cap_le | apply IH | lia | lia].
Qed.

Lemma tbc_lines_run_dead : forall mx ls no cap H ka j o ha ks,
  fst (fst (snd (fst (lines_run false mx no cap H ka ls j o ha ks)))) = cap.
Proof.
  intros mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks; [reflexivity|].
  cbn [lines_run]. cbv zeta. cbn [snd fst]. rewrite IH. reflexivity.
Qed.

Lemma tbc_drain_run_cap_le : forall f live mx s j a,
  ds_no s <= ds_no (fst (snd (drain_run f live mx s j a))) /\
  ds_ocap (fst (snd (drain_run f live mx s j a))) <=
    Z.max (ds_ocap s) (2 * ds_no (fst (snd (drain_run f live mx s j a)))).
Proof.
  intros f live mx. induction f as [|f IH]; intros s j a.
  - cbn [drain_run snd fst]. split; [lia | apply Z.le_max_l].
  - cbn [drain_run]. cbv zeta. destruct (ds_eintr s).
    + cbn [snd fst].
      match goal with |- context [drain_run f live mx ?s1 ?j1 ?a1] => destruct (IH s1 j1 a1) as [I1 I2] end.
      cbn [ds_no ds_ocap] in I1, I2. split; [exact I1 | exact I2].
    + destruct (ds_pend s) as [|r0 rs].
      { cbn [snd fst ds_no ds_ocap]. split; [lia | apply Z.le_max_l]. }
      match goal with |- context [Z.min ?a ?b <=? 0] => destruct (Z.min a b <=? 0) end.
      { cbn [snd fst ds_no ds_ocap]. split; [lia | apply Z.le_max_l]. }
      match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
      match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
        pose proof (tbc_lines_run_cap_le live mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o ha ks) as LC;
        destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
          as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
      cbn [snd fst] in LC |- *.
      match goal with |- context [drain_run f live mx ?s2 ?j4 ?a2] => destruct (IH s2 j4 a2) as [I1 I2] end.
      cbn [ds_no ds_ocap] in I1, I2.
      split; [lia|].
      exact (tbc_rc_step _ _ _ _ _ _ LC I2 I1 (Z.le_refl _)).
Qed.

Lemma tbc_drain_run_dead : forall f mx s j a, ds_ocap (fst (snd (drain_run f false mx s j a))) = ds_ocap s.
Proof.
  intros f mx. induction f as [|f IH]; intros s j a; [reflexivity|].
  cbn [drain_run]. cbv zeta. destruct (ds_eintr s).
  - cbn [snd fst]. rewrite IH. reflexivity.
  - destruct (ds_pend s) as [|r0 rs]; [reflexivity|].
    match goal with |- context [Z.min ?a ?b <=? 0] => destruct (Z.min a b <=? 0) end; [reflexivity|].
    match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
    match goal with |- context [lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
      pose proof (tbc_lines_run_dead mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o ha ks) as LC;
      destruct (lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
        as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [snd fst] in LC |- *. rewrite IH. cbn [ds_ocap]. exact LC.
Qed.

Lemma tbc_drain_ocap_le : forall live mx NO CAP e h,
  NO <= ds_no (drain_fin live mx NO CAP e h) /\
  ds_ocap (drain_fin live mx NO CAP e h) <= Z.max CAP (2 * ds_no (drain_fin live mx NO CAP e h)).
Proof.
  intros live mx NO CAP e h.
  exact (tbc_drain_run_cap_le (S (S (length (pending_stream h)))) live mx (drain_init NO CAP e h) 0%nat dadr0).
Qed.

Lemma tbc_drain_ocap_dead : forall mx NO CAP e h, ds_ocap (drain_fin false mx NO CAP e h) = CAP.
Proof. intros mx NO CAP e h. unfold drain_fin, drain_go. rewrite tbc_drain_run_dead. reflexivity. Qed.

Lemma tbc_after_drain_fin : forall lv mx NO CAP e h,
  re_eof e = 0 -> after_drain lv mx NO CAP e h = drain_fin lv mx NO CAP e h.
Proof. intros lv mx NO CAP e h E. unfold after_drain. rewrite E. reflexivity. Qed.

Lemma tbc_after_drain_init : forall lv mx NO CAP e h,
  re_eof e <> 0 -> after_drain lv mx NO CAP e h = drain_init NO CAP e h.
Proof. intros lv mx NO CAP e h E. unfold after_drain. rewrite (tbc_rc_if_f _ _ _ E). reflexivity. Qed.

Lemma tbc_after_drain_le : forall lv mx NO CAP e h,
  NO <= ds_no (after_drain lv mx NO CAP e h) /\
  ds_ocap (after_drain lv mx NO CAP e h) <= Z.max CAP (2 * ds_no (after_drain lv mx NO CAP e h)).
Proof.
  intros lv mx NO CAP e h. destruct (Z.eq_dec (re_eof e) 0) as [E|E].
  - rewrite (tbc_after_drain_fin lv mx NO CAP e h E). apply tbc_drain_ocap_le.
  - rewrite (tbc_after_drain_init lv mx NO CAP e h E). unfold drain_init. cbn [ds_no ds_ocap].
    split; [lia | apply Z.le_max_l].
Qed.

Lemma tbc_after_drain_dead : forall mx NO CAP e h, ds_ocap (after_drain false mx NO CAP e h) = CAP.
Proof.
  intros mx NO CAP e h. destruct (Z.eq_dec (re_eof e) 0) as [E|E].
  - rewrite (tbc_after_drain_fin false mx NO CAP e h E). apply tbc_drain_ocap_dead.
  - rewrite (tbc_after_drain_init false mx NO CAP e h E). reflexivity.
Qed.

Lemma tbc_p3b_ker_cap : forall live mx (xks xks' : list (Z * adrF)) no c j o j' o', map fst xks = map fst xks' ->
  fst (snd (keys_end_run live mx no c xks j o)) = fst (snd (keys_end_run live mx no c xks' j' o')).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros [|[xl' ka'] r'] no c j o j' o' E;
    cbn [map fst] in E; try discriminate; [reflexivity|].
  injection E as <- E. cbn [keys_end_run fst snd]. apply IH. exact E.
Qed.

Lemma tbc_gsh_seen : forall H ka l j ha ks j' ha' ks',
  snd (fst (seen_tr H ka l j ha ks)) = snd (fst (seen_tr H ka l j' ha' ks')) /\
  (length ks = length H -> length (snd (snd (seen_tr H ka l j ha ks))) = length (seen_arr H l)).
Proof.
  intros H ka l j ha ks j' ha' ks'. unfold seen_tr, seen_arr.
  destruct (gesture l) as [[g x]|]; [destruct g; destruct (index_of x H)|]; cbn [fst snd];
    (split; [reflexivity | intros E]); rewrite ?length_app, ?rigl_len_swap; cbn [length]; lia.
Qed.

Lemma tbc_gsh_lines : forall ls live mx no cap H ka j o ha ks j' o' ha' ks',
  snd (fst (lines_run live mx no cap H ka ls j o ha ks)) = snd (fst (lines_run live mx no cap H ka ls j' o' ha' ks')) /\
  (length ks = length H ->
   length (snd (snd (lines_run live mx no cap H ka ls j o ha ks))) =
   length (snd (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks j' o' ha' ks'; cbn [lines_run fst snd].
  - split; [reflexivity | intros E; exact E].
  - match goal with |- context [seen_tr H ka l ?j1 ha ks] => match goal with |- context [seen_tr H ka l ?j2 ha' ks'] =>
      destruct (tbc_gsh_seen H ka l j1 ha ks j2 ha' ks') as [S1 S2] end end.
    rewrite <- S1. split.
    + apply (proj1 (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    + intros E. apply (proj2 (IH _ _ _ _ _ _ _ _ _ _ 0%nat adr0 adr0 [])). apply S2. exact E.
Qed.

Lemma tbc_gsh_pushes : forall ls n cap j v rs j' v' rs',
  snd (fst (pushes_run n cap ls j v rs)) = snd (fst (pushes_run n cap ls j' v' rs')).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs j' v' rs'; cbn [pushes_run fst snd]; [reflexivity | apply IH].
Qed.

Lemma tbc_gsh_grow : forall c u j b j' b', fst (snd (grow_tr c u j b)) = fst (snd (grow_tr c u j' b')).
Proof. intros c u j b j' b'. unfold grow_tr. destruct (c - u <? 4096); reflexivity. Qed.

Lemma tbc_gsh_drain : forall f live mx s j a j' a',
  fst (snd (drain_run f live mx s j a)) = fst (snd (drain_run f live mx s j' a')) /\
  (length (da_keys a) = length (ds_H s) ->
   length (da_keys (snd (snd (drain_run f live mx s j a)))) = length (ds_H (fst (snd (drain_run f live mx s j a))))).
Proof.
  induction f as [|f IH]; intros live mx s j a j' a'; cbn [drain_run]; [split; [reflexivity | intros E; exact E]|].
  rewrite (tbc_gsh_grow (ds_cap s) (Z.of_nat (length (ds_u s))) j' (da_buf a') j (da_buf a)).
  destruct (ds_eintr s).
  - cbn [fst snd]. split; [apply (proj1 (IH _ _ _ _ _ _ _)) | intros E; apply (proj2 (IH _ _ _ _ _ 0%nat dadr0)); exact E].
  - destruct (ds_pend s) as [|r0 rs]; [cbn [fst snd]; split; [reflexivity | intros E; exact E]|].
    match goal with |- context [if (?x <=? 0) then _ else _] => destruct (x <=? 0) end;
      [cbn [fst snd]; split; [reflexivity | intros E; exact E]|].
    match goal with |- context [chunk ?u ?sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [snd (fst (pushes_run ?n ?c ?ls ?j1 (da_ev a) ?r1))] =>
      match goal with |- context [snd (fst (pushes_run n c ls ?j2 (da_ev a') ?r2))] =>
        rewrite (tbc_gsh_pushes ls n c j2 (da_ev a') r2 j1 (da_ev a) r1) end end.
    match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?J1 (da_out a) (da_hp a) (da_keys a)] =>
      match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?J2 (da_out a') (da_hp a') (da_keys a')] =>
        pose proof (tbc_gsh_lines rl live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) J1 (da_out a) (da_hp a) (da_keys a)
                      J2 (da_out a') (da_hp a') (da_keys a')) as [LS LL];
        rewrite <- LS; revert LL;
        destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl J1 (da_out a) (da_hp a) (da_keys a))
          as [[t1 [[oc' H'] ka']] [[o' ha'] ks']];
        destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl J2 (da_out a') (da_hp a') (da_keys a'))
          as [[t2 [[oc2 H2] ka2]] [[o2 ha2] ks2]]
      end end.
    cbn [fst snd]. intros LL. split.
    + apply (proj1 (IH _ _ _ _ _ _ _)).
    + intros E. apply (proj2 (IH _ _ _ _ _ 0%nat dadr0)). exact (LL E).
Qed.

Lemma tbc_gsh_after : forall lv mx no cap e h j a, length (da_keys a) = length (re_keys e) ->
  length (da_keys (after_drain_adr lv mx no cap e h j a)) = length (ds_H (after_drain lv mx no cap e h)).
Proof.
  intros lv mx no cap e h j a E. unfold after_drain_adr, after_drain.
  destruct (re_eof e =? 0); [|unfold drain_init; cbn [ds_H]; unfold keys_texts; rewrite length_map; exact E].
  unfold drain_adr, drain_fin, drain_go.
  rewrite (proj1 (tbc_gsh_drain _ lv mx (drain_init no cap e h) 0%nat dadr0 j a)).
  apply (proj2 (tbc_gsh_drain _ lv mx (drain_init no cap e h) j a 0%nat dadr0)).
  unfold drain_init. cbn [ds_H]. unfold keys_texts. rewrite length_map. exact E.
Qed.

Lemma tbc_gsh_geia : forall f pre n (Ha : list (list Z * adrF)),
  map fst (fst (geia_loop f pre n Ha)) = fst (gei_loop f pre n (map fst Ha)) /\
  map fst (snd (geia_loop f pre n Ha)) = snd (gei_loop f pre n (map fst Ha)).
Proof.
  induction f as [|f IH]; intros pre n Ha; cbn [geia_loop gei_loop]; [split; reflexivity|].
  rewrite length_map. destruct (Nat.ltb n (length Ha)) eqn:Hl; [|split; reflexivity].
  replace (nth n (map fst Ha) []) with (fst (nth n Ha ([], adr0)))
    by (rewrite <- (map_nth fst Ha ([], adr0) n); reflexivity).
  destruct (has_prefix pre (fst (nth n Ha ([], adr0)))).
  - replace (swap_remove [] n (map fst Ha)) with (map fst (swap_remove ([], adr0) n Ha))
      by (rewrite (rig_swap_map fst ([], adr0) n Ha) by (apply Nat.ltb_lt; exact Hl); reflexivity).
    pose proof (IH pre n (swap_remove ([], adr0) n Ha)) as [E1 E2]. revert E1 E2.
    destruct (geia_loop f pre n (swap_remove ([], adr0) n Ha)) as [Ea Ha'].
    destruct (gei_loop f pre n (map fst (swap_remove ([], adr0) n Ha))) as [Et Ht].
    cbn [fst snd map]. intros E1 E2. rewrite E1. split; [reflexivity | exact E2].
  - exact (IH pre (S n) Ha).
Qed.

Lemma tbc_gsh_combine_fst : forall {X Y} (l : list X) (l' : list Y), length l = length l' -> map fst (combine l l') = l.
Proof.
  intros X Y l. induction l as [|x l IH]; intros [|y l'] E; cbn [length] in E; try lia; [reflexivity|].
  cbn [combine map fst]. rewrite IH by lia. reflexivity.
Qed.

Lemma tbc_gsh_xks : forall pre (H : list (list Z)) (ka : list adrF), length ka = length H ->
  map fst (map (fun x => (Z.of_nat (length (fst x)), snd x)) (fst (geia pre (combine H ka)))) =
  map (fun x => Z.of_nat (length x)) (fst (gei pre H)).
Proof.
  intros pre H ka E. rewrite map_map. cbn [fst].
  rewrite <- (map_map fst (fun x => Z.of_nat (length x))). f_equal.
  unfold geia, gei. rewrite (proj1 (tbc_gsh_geia _ pre 0 _)), tbc_gsh_combine_fst by lia.
  rewrite length_combine, E, Nat.min_id. reflexivity.
Qed.

End tbm.

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

(* the room round's count measures (ReplyCnt.tr_peakP, W_rr_m_dcnt.v tr_netP) read the sizes only too *)
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
      rewrite <- (proj1 (tbc_gsh_seen H ka l j1 ha ks j2 ha' ks')) end end.
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
  rewrite (tbc_gsh_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j'
             (drain_b_c.da_buf a') j (drain_b_c.da_buf a)).
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst]. apply tb_sh_app; [exact TG | apply IH].
  - destruct (drain_b_c.ds_pend s) as [|r0 rs]; [exact TG|].
    match goal with |- context [if (?x <=? 0) then _ else _] => destruct (x <=? 0) end; [exact TG|].
    match goal with |- context [RelayModel.chunk ?u ?sk ?d] => destruct (RelayModel.chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [drain_b_c.pushes_run ?n ?c ?ls ?j1 (drain_b_c.da_ev a) ?r1] =>
      match goal with |- context [drain_b_c.pushes_run n c ls ?j2 (drain_b_c.da_ev a') ?r2] =>
        pose proof (tb_push_sh ls n c j1 (drain_b_c.da_ev a) r1 j2 (drain_b_c.da_ev a') r2) as TP;
        rewrite (tbc_gsh_pushes ls n c j2 (drain_b_c.da_ev a') r2 j1 (drain_b_c.da_ev a) r1) end end.
    match goal with
    |- context [drain_b_c.lines_run live mx ?n0 ?c0 ?H0 ?k0 rl ?J1 (drain_b_c.da_out a) (drain_b_c.da_hp a) (drain_b_c.da_keys a)] =>
      match goal with
      |- context [drain_b_c.lines_run live mx n0 c0 H0 k0 rl ?J2 (drain_b_c.da_out a') (drain_b_c.da_hp a') (drain_b_c.da_keys a')] =>
        pose proof (tb_lines_sh rl live mx n0 c0 H0 k0 J1 (drain_b_c.da_out a) (drain_b_c.da_hp a) (drain_b_c.da_keys a)
                      J2 (drain_b_c.da_out a') (drain_b_c.da_hp a') (drain_b_c.da_keys a')) as TL;
        rewrite <- (proj1 (tbc_gsh_lines rl live mx n0 c0 H0 k0 J1 (drain_b_c.da_out a)
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
  { intros nm0 j0 o0. apply tbc_gsh_after. unfold drain_b_c.drain_start.
    cbn [drain_b_c.da_keys]. rewrite length_map. reflexivity. }
  match goal with |- tb_sh ?L ?R =>
    match L with context [keys_end_run lv mx ?n0 ?c0 ?x1 ?j1 ?o1] =>
      match R with context [keys_end_run lv mx n0 c0 ?x2 ?j2 ?o2] =>
        assert (XE : map fst x1 = map fst x2)
          by (rewrite (tbc_gsh_xks _ _ _ (LD nm j o)),
                      (tbc_gsh_xks _ _ _ (LD nm' j' o')); reflexivity);
        pose proof (tb_ker_sh lv mx x1 x2 n0 c0 n0 c0 j1 o1 j2 o2 XE (fun _ => conj eq_refl eq_refl)) as TK;
        rewrite (tbc_p3b_ker_cap lv mx x1 x2 n0 c0 j1 o1 j2 o2 XE)
      end end end.
  rewrite (tbc_gsh_xks _ _ _ (LD nm j o)), (tbc_gsh_xks _ _ _ (LD nm' j' o')).
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
  pose proof (proj1 (tbc_after_drain_le lv mx no cap e (fst hj))) as HN.
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
  rewrite AH, AA, AT, !tbc_after_drain_dead.
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
        apply tbc_p3b_ker_cap. reflexivity.
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
  { apply tbc_gsh_after. unfold drain_b_c.drain_start. cbn [drain_b_c.da_keys].
    rewrite length_map. reflexivity. }
  pose proof (tbc_gsh_xks pre _ _ LD) as XE.
  set (xls := map (fun x => Z.of_nat (length x)) (fst (RelayKeys.gei pre (drain_b_c.ds_H s)))) in *.
  eexists _, _, _. split; [reflexivity|]. split; [|split].
  - destruct (re_eof e =? 0); [apply tb_dtr_sh | reflexivity].
  - intros xks j o E. apply tb_ker_sh; [rewrite XE, E; reflexivity | intros _; split; reflexivity].
  - intros j o. rewrite XE.
    match goal with |- tb_sh ?L _ => match L with context [keys_end_run lv mx ?n0 ?c0 ?x1 ?j1 ?o1] =>
      rewrite (tbc_p3b_ker_cap lv mx x1 (map (fun xl => (xl, ga0)) xls) n0 c0 j1 o1 0%nat ga0)
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
(* ---- The Section hypotheses every segment file copies (the names are the contracts').  Each is either the AR
   walk's (AR-free, verbatim) or its _x twin (image A's W_relay_instance_gone_cx.v, the same list). ---- *)
(* the instance's laws, over ARx *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling; W_journal_x.v range_addressable_of_block_hp0_x) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MLAW : ameter_laws MT.
(* the frame twins' hypotheses (W_frame_x.v), in place of ML / SMP: the image cover IMGC (frm_off_imgP_x; image B's
   bound 0x5fc000, W_kit_x.v's IMGC); a live block's size is non-negative (W_kit_x.v's BLKN); the owned-low law OWNLOW,
   the model invariant WFx with its law WFL, and the two facts the twins read off model_laws / stack_malloc_progressP
   (SFREE, SMALLOC) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
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
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HGRIG : gx_ok SEGS B (G_RIG B RG).
(* the register images of g_nsrc / g_src (PB_fr on AsanUbsan discharges both by vm_compute, as the image-A twin's
   HH44 / HH45) *)
Hypothesis HH41 : VAL (A_HI 41) = rg_nsrc RG + RIG_HI_NSRC.
Hypothesis HH42 : VAL (A_HI 42) = rg_src RG + RIG_HI_SRC.
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
(* the allocator instance's granule-tail fact (W7's ALLOC_TAIL over ARx, as W_drain_cx_x.v states it): a held key is
   represented over its |text| + 1 bytes (ruling (A)); a word read of a key to the end of its last granule is
   visible *)
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the runtime entries relay_instance_gone calls, at their SIGMA pcs, over ARx (W_sites_x.v / W_contract_x.v /
   W_journal_x.v Section hc; the free rule at the room record RP).  snprintf: a Theorem Labs lane's statement at fuzz_reply's
   addresses (W_sites.v asnprintf_realizes, its twin W_sites_x.v asnprintf_realizes_x), which the snprintf chain
   (RT_pf_vf.v snprintf_chain_ok, through a Theorem Labs lane's evt -> SRr bridge) discharges. *)
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
(* snprintf's stack-protector cells (see the header): the GOT word, a fact of every ARx state (at ARi0: the AR fact,
   am_const); the canary, image bytes *)
Hypothesis HGOTG : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  rdword (aview SEGS (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
(* the canary's bytes are image bytes (seg_rom SEGS at FR_GUARD .. + 8 is Some 0), so aview reads them in EVERY state
   through mbyte's seg_rom fallback: aguard_ok's second half needs nothing carried (a Theorem Labs lane's ruling; a Theorem Labs lane's
   pin measurement).  PB_fr decides it by vm_compute. *)
Hypothesis HCANR : forall a, FR_GUARD <= a < FR_GUARD + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None.
(* the two literals of the snprintf call and " end\0" (.str.4, A_lit_end5 = A_OBJ 28), in the cx's glit_at_x form
   over ARx (W_relay_instance_gone_cx.v: bytes, in_rom, ashp_x, the granule's tail) *)
Hypothesis HLIT17 : glit_at_x ARx 17 (RIG_FMT ++ [0]).
Hypothesis HLIT18 : glit_at_x ARx 18 (RelayModel.K_GESTURE ++ [0]).
Hypothesis HLIT28 : glit_at_x ARx 28 ([32; 101; 110; 100] ++ [0]).
(* The program statics PST hold no byte this walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x, the literals and " end\0"), and no byte of the
   relay's and the output's global cells (G_RIG, and the cells of HRGP that G_RIG does not name: g_src, g_nsrc,
   g_capsrc, g_send_max, g_client, g_send_dead).  At PST := [] both hold trivially (image A's PSTR / PSTG). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a,
(inG (G_RIG B RG) a \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
 rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ Exists (in_zr a) PST.

(* ---------------------------------------------------------------- B1: drain's model invariant *)

Lemma dr_inv_of : stmt_dr_inv_of B RG.
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
  gtop_bud B MT RP MMAX cx e1 c1 O1 cap1 i ly2 S2 (spent + tr_cost MT td).
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

Lemma top_room : stmt_top_room B ARx MT RP MMAX RG.
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
  pose proof (proj1 (tbc_after_drain_le (sl_live (gxc cx) 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i)
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

Lemma top_budget : stmt_top_budget B ARx MT RP MMAX RG.
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
    { rewrite (tbc_after_drain_fin _ _ _ _ _ _ EO). unfold dr_fin, drain_b_c.drain_fin. rewrite DG. reflexivity. }
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
      * rewrite <- FIN. unfold dr_fin. rewrite DL. apply tbc_drain_ocap_dead.
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
    rewrite (tbc_after_drain_init _ _ _ _ _ _ EO) in TK, TR.
    apply (tb_core cx i (gnth cx i) c2 O2 cap2 ly1 S1 ly2 S2 spent td K R _ HG TK TR); try reflexivity.
    + exact LV.
    + rewrite TC. exact HMO.
    + rewrite TN. lia.
    + lia.
    + exact HRM'.
    + exact HCNT'.
Qed.

End c.
End b.
End a.

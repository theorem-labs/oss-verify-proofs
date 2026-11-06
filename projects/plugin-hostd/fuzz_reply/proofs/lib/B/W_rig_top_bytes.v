(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan), track "bytes": drain's live bytes, lib/B/W_rig_top_defs.v stmt_dr_bytes.  Ported from
   k3's image-A track (a working branch 80fffa8e840, lib/A/W_rig_top_bytes.v); the proofs read only
   the plain drain model (lib/Prog) and the kit's W_rep.v block lists, which image B shares with image A.
   The blocks drain leaves of its entry, source and output weigh at most drain_run's request trace's net change
   (tr_net, C3's peak form; was the summed allocations tr_alloc) more than the blocks it found.  A potential over
   drain's state (td_pot: the buffer, the held array, the held keys, the expected list's vector, g_out and the pending
   texts) moves in each round by at most the round's net change less the expected list's new records (one per
   reference line pushed, |l| + 1 bytes); the pushed lines of all rounds are the reference lines of the pending stream
   (RelayModel.lines_app over relay_instance_gone_b_lem.dr_rest).
   C3 (the image-A twin's re-fit of lib/A/W_rig_top.v td_* / dr_bytes, mirrored): every request moves the live bytes by
   exactly its share of tr_net (W_tr_peak.v tr_net_app), td_pot weighs the pending texts too (drain frees each one as
   it reads it whole), and td_lw_pend is new.
   ROUTE (b), STEP 3 (the image-A twin: a Theorem Labs lane's RIG_x round of lib/A/W_rig_top.v, commit f4cd818e98d): only the
   Section header changes (W_relay_instance_gone_cx.v's generic list); dr_bytes reads no Section hypothesis.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayKeys send_line_b_c ListTr RelayRunT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_tr_peak.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
Lemma dr_bytes : stmt_dr_bytes B.
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
  (* the pending texts drain_init reads weigh what h's pending records do; drain's final pending texts weigh >= 0 *)
  pose proof (td_lw_pend (hl_recs (hs_pending h))) as LWP.
  pose proof (td_lw_nonneg (drain_b_c.ds_pend (drain_b_c.drain_fin (dr_live c h) mx no cap e h))) as NPF.
  pose proof (td_pot_eq (drain_b_c.drain_fin (dr_live c h) mx no cap e h)) as PF.
  pose proof (td_pot_init no cap e h) as PI0.
  unfold dr_fin, dr_tr, dr_lines.
  (* drain's final state, its trace's net change and the reference lines' records as opaque values, and only the
     facts the sum needs: no hypothesis is converted through drain_run (its kernel unfolding is costly) *)
  clear - D Z0 PF PI0 LWP NPF. revert D PF PI0 NPF.
  generalize (drain_b_c.drain_fin (dr_live c h) mx no cap e h) as F.
  generalize (tr_net (drain_b_c.drain_tr (dr_live c h) mx no cap e h 0 drain_b_c.dadr0)) as T.
  generalize (td_lw (RelayModel.lines (hs_state h) (bzs (pending_stream h)))) as L.
  intros L T F D PF PI0 NPF. unfold AREC in *. lia.
Qed.

End c.
End b.
End a.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the plain-model arithmetic the DRAIN hop of the IMAGE-B walk of relay_remove
   needs (lib/B/W_rr_m_drain.v): drain's live bytes and drain's model invariant.  Proves no function (kind:
   segment-lemma helpers); no walk, no image, no Section hypothesis.

   rm_dr_bytes: the blocks drain leaves of its entry, source and output weigh at most its request trace's net change
   (tr_net, C3's peak form; was the summed allocations tr_alloc) more than the blocks it found.  rm_dr_inv_of: drain's
   model invariant at the call, from the relay entry and the harness source.

   PORTED, verbatim but the import paths and the two statements inlined, from k3's A files
   a working branch 80fffa8e840: lib/A/W_rig_top_bytes.v (the td_* lemmas and dr_bytes, for
   W_rig_top_defs.v stmt_dr_bytes) and lib/A/W_rig_top_bud.v (dr_inv_of, for stmt_dr_inv_of).  Both are arithmetic
   over lib/Prog's plain model (drain_b_c, relay_instance_gone_b_lem, RelayModel, RelayKeys, ListTr) and lib/<I>'s
   W_rep / W_contract, which the B kit generates from the same lib/A text, so only `lib.A` -> `lib.B` changes.
   C3 (the image-A twin's re-fit of lib/A/W_rig_top.v td_* / dr_bytes, mirrored): every request moves the live bytes by
   exactly its share of tr_net (W_tr_peak.v tr_net_app), the potential td_pot weighs the pending texts too (drain frees
   each one as it reads it whole), and td_lw_pend is new. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel RelayKeys send_line_b_c ListTr RelayRunT.
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
Section c.
Variable B : asyms.
Variable RG : rep_globals.

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
Lemma rm_dr_bytes : forall ly S W mem ly' S' c mx no cap out out' e h e' h' LB rest HA,
  let fin := dr_fin c mx no cap e h in
  let cap' := if dr_live c h then drain_b_c.ds_ocap fin else cap in
  aentry_ok B ly S W mem e -> asrc_at B ly S W mem HA h -> 0 <= cap -> 0 <= mx <= 255 -> 0 <= no ->
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) ->
  Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) ->
  dr_rel c mx no cap e h e' h' LB ->
  blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr c mx no cap e h).
Proof using Type.
  intros ly S W mem ly' S' c mx no cap out out' e h e' h' LB rest HA. cbv zeta.
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


(* drain's model invariant at the call, from the relay entry and the harness source (k3's dr_inv_of,
   lib/A/W_rig_top_bud.v:715): the premises of lib/Prog/relay_instance_gone_b_lem.v rig_drain_model. *)
Lemma rm_dr_inv_of : forall ly S W mem e h j no cap,
  aentry_ok B ly S W mem e -> dr_src_ok B RG ly S W mem e h j ->
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) /\
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h).
Proof using Type.
  intros ly S W mem e h j no cap HE HS.
  destruct HE as (_ & HSK & _ & _ & _ & HCAP & HUL & HUM & HUZ & _).
  destruct HS as (_ & HA & _ & _ & HOV & HUW & _).
  destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _ & _ & _ & _ & HPD & _).
  destruct HPL as (_ & _ & _ & _ & _ & _ & _ & _ & HPF).
  apply relay_instance_gone_b_lem.rig_dinit; [exact HSK | exact HOV | exact HUW | unfold APARTIAL in HUM; lia |
    exact HUZ | lia | exact HPD |].
  eapply Forall_impl; [|exact HPF]. intros r (_ & _ & _ & Hr). exact (Hr eq_refl).
Qed.

End c.
End b.
End a.

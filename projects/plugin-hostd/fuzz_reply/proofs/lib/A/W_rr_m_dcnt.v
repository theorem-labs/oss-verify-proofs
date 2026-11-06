(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* drain's exact count growth, for every count predicate P: over the blocks W_rep.v represents the drained entry,
   the harness source and g_out over (aentry_blks / asrc_blks / aout_blks), the count of blocks whose size satisfies P
   (ReplyCnt.acnt P) after drain is the count before plus the net count change of drain's trace (W_tr_cnt.v tr_netP),
   rmc_dr_cnt; so it is within the trace's count peak (rmc_dr_cnt_peak, with rmc_net_peak: tr_netP <= tr_peakP).
   A pure model lemma: no astate, no walk file.
   - The method is the byte chain of commit 3d17f490d56, lib/A/W_rr_m_drain.v rmd_lw .. rmd_bsum_out and
     rmd_dr_bytes, with a COUNT potential in place of the bytes: s->buf and g_out count cphi P cap (W_tr_cnt.v: 0 for
     cap 0, no block), the held array cphi P ka, the keys, the pending texts and the expected texts
     sum zb (P (|x| + 1)) (rmc_cw), the expected vector rmc_ephi P ecap.  Every model step moves the potential by
     exactly its trace's tr_netP: rmc_grow, rmc_seen, rmc_sl_run / rmc_send (the g_out chain of W_tr_cnt.v tc_sl_run /
     tc_send as an equality), rmc_lines_run, rmc_push_tra, rmc_pushes, rmc_drop, rmc_run, rmc_drain.  rmc_run also
     proves that drain leaves no pending text (the byte chain only needed <=), so the equality is exact.
   - Premises beyond the byte lemma's: 0 <= cap (g_out's chain: a growth from cap >= 0 never makes a 0-size block;
     W_tr_cnt.v tc_sl_cex is the counterexample without it), and re_hp = 0 \/ re_kh <> 0 at both ends (the held array's
     block is counted at its size re_kh, the model's ent_ka is 0 when s->held is NULL).
   - The block counts (rmc_acnt_cons .. rmc_cnt_out) are proved here over ReplyCnt.acnt_app.
   - The closing arithmetic (rmc_close) is over a state F, a trace count T and lines L that are variables, and
     rmc_drain_dr / rmc_ocap state drain's facts at dr_fin / dr_tr / dr_lines, so no proof term asks the kernel to
     compare dr_fin with an unfolded drain run (rmc_dr_cnt in rmd_dr_bytes's one-proof form took 796 s at Qed). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF ListTr send_line_b_c gestures_end_b_c RelayModel RelayKeys drain_b_c relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract W_tr_cnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt ReplyTrPeakW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ I. the net count of a trace, event by event *)
Lemma rmc_netP_nil : forall (X : Type) (P : Z -> bool), tr_netP P (@nil (RelayRunT.rev X)) = 0.
Proof. reflexivity. Qed.
Lemma rmc_netP_m : forall (X : Type) (P : Z -> bool) n (r : list (RelayRunT.rev X)),
  tr_netP P (RelayRunT.RMalloc n :: r) = ReplyCnt.zb (P n) + tr_netP P r.
Proof. reflexivity. Qed.
Lemma rmc_netP_f : forall (X : Type) (P : Z -> bool) k (a : RelayRunT.addr X) (r : list (RelayRunT.rev X)),
  tr_netP P (RelayRunT.RFree k a :: r) = - ReplyCnt.zb (P k) + tr_netP P r.
Proof. reflexivity. Qed.
Lemma rmc_netP_r : forall (X : Type) (P : Z -> bool) k n (a : RelayRunT.addr X) (r : list (RelayRunT.rev X)),
  tr_netP P (RelayRunT.RRealloc k n a :: r) = ReplyCnt.zb (P n) - ReplyCnt.zb (P k) + tr_netP P r.
Proof. reflexivity. Qed.

(* the net count change of a trace is within its count peak *)
Lemma rmc_net_peak : forall (X : Type) (P : Z -> bool) (t : list (RelayRunT.rev X)),
  tr_netP P t <= ReplyCnt.tr_peakP P t.
Proof.
  intros X P t. induction t as [|[n|k a|k n a] r IH].
  - rewrite rmc_netP_nil. cbn [ReplyCnt.tr_peakP]. lia.
  - rewrite rmc_netP_m. cbn [ReplyCnt.tr_peakP]. lia.
  - rewrite rmc_netP_f. cbn [ReplyCnt.tr_peakP]. lia.
  - rewrite rmc_netP_r. cbn [ReplyCnt.tr_peakP]. lia.
Qed.

(* ------------------------------------------------------------------ II. drain's count potential, exactly *)
(* the count of the blocks of the texts ls, each of |l| + 1 bytes *)
Definition rmc_cw {A : Type} (P : Z -> bool) (ls : list (list A)) : Z :=
  fold_right (fun l acc => ReplyCnt.zb (P (Z.of_nat (length l) + 1)) + acc) 0 ls.

Lemma rmc_cw_nil : forall {A} (P : Z -> bool), rmc_cw P (@nil (list A)) = 0.
Proof. reflexivity. Qed.

Lemma rmc_cw_cons : forall {A} (P : Z -> bool) (x : list A) ls,
  rmc_cw P (x :: ls) = ReplyCnt.zb (P (Z.of_nat (length x) + 1)) + rmc_cw P ls.
Proof. reflexivity. Qed.

Lemma rmc_cw_app : forall {A} (P : Z -> bool) (l1 l2 : list (list A)), rmc_cw P (l1 ++ l2) = rmc_cw P l1 + rmc_cw P l2.
Proof.
  intros A P l1 l2. induction l1 as [|x l1 IH]; cbn [app]; [rewrite rmc_cw_nil; lia|].
  rewrite !rmc_cw_cons, IH. lia.
Qed.

Lemma rmc_cw_perm : forall {A} (P : Z -> bool) (l1 l2 : list (list A)), Permutation l1 l2 -> rmc_cw P l1 = rmc_cw P l2.
Proof. intros A P l1 l2 HP. induction HP; rewrite ?rmc_cw_cons in *; lia. Qed.

Lemma rmc_cw_map : forall {A A'} (P : Z -> bool) (f : A -> A') ls, rmc_cw P (map (map f) ls) = rmc_cw P ls.
Proof.
  intros A A' P f ls. induction ls as [|x ls IH]; [reflexivity|]. cbn [map].
  rewrite !rmc_cw_cons, IH, length_map. reflexivity.
Qed.

(* the pending texts of drain_init, as the harness list's records *)
Lemma rmc_cw_pend : forall (P : Z -> bool) (rs : list (Z * list byte)),
  rmc_cw P (map (fun r => bzs (snd r)) rs) = rmc_cw P (map snd rs).
Proof.
  intros P rs. induction rs as [|r rs IH]; [reflexivity|]. cbn [map]. rewrite !rmc_cw_cons, IH.
  unfold bzs. rewrite length_map. reflexivity.
Qed.

(* the count of an expected list's vector of ec texts (16 bytes each): none when ec = 0 *)
Definition rmc_ephi (P : Z -> bool) (ec : Z) : Z := if ec =? 0 then 0 else ReplyCnt.zb (P (AREC * ec)).

Lemma rmc_ephi_0 : forall P, rmc_ephi P 0 = 0.
Proof. reflexivity. Qed.

Lemma rmc_ephi_nz : forall P ec, ec <> 0 -> rmc_ephi P ec = ReplyCnt.zb (P (AREC * ec)).
Proof. intros P ec H. unfold rmc_ephi. rewrite (proj2 (Z.eqb_neq ec 0) H). reflexivity. Qed.

(* the buffer's growth replaces s->buf: malloc (8192) of nothing, or realloc cap -> 2 cap *)
Lemma rmc_grow : forall P c used j b,
  cphi P (fst (snd (drain_b_c.grow_tr c used j b))) = cphi P c + tr_netP P (fst (drain_b_c.grow_tr c used j b)).
Proof.
  intros P c used j b. unfold drain_b_c.grow_tr.
  destruct (c - used <? 4096); cbn [fst snd]; [|rewrite rmc_netP_nil; lia].
  destruct (Z.eqb_spec c 0) as [->|E]; cbv beta iota.
  - rewrite rmc_netP_m, rmc_netP_nil, cphi_0, (cphi_nz P 8192) by lia. lia.
  - rewrite rmc_netP_r, rmc_netP_nil, (cphi_nz P (c * 2)) by lia. rewrite (cphi_nz P c E). lia.
Qed.

(* gesture_seen: a begin grows the held array to c > 0 and adds the key's block; an end frees the key's block *)
Lemma rmc_seen : forall P H ka l j ha ks,
  cphi P (snd (fst (drain_b_c.seen_tr H ka l j ha ks))) + rmc_cw P (RelayKeys.seen_arr H l) =
    cphi P ka + rmc_cw P H + tr_netP P (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof.
  intros P H ka l j ha ks. unfold drain_b_c.seen_tr, RelayKeys.seen_arr.
  destruct (RelayModel.gesture l) as [[[|] x]|]; [| |cbn [fst snd]; rewrite rmc_netP_nil; lia].
  - destruct (RelayKeys.index_of x H) as [n|] eqn:E; [cbn [fst snd]; rewrite rmc_netP_nil; lia|].
    cbn [fst snd]. rewrite rmc_cw_app, rmc_cw_cons, rmc_cw_nil.
    rewrite (cphi_nz P ((Z.of_nat (length H) + 1) * 8)) by lia.
    destruct (Z.eqb_spec ka 0) as [->|Hk]; cbv beta iota.
    + rewrite !rmc_netP_m, rmc_netP_nil, cphi_0. lia.
    + rewrite rmc_netP_r, rmc_netP_m, rmc_netP_nil, (cphi_nz P ka Hk). lia.
  - destruct (RelayKeys.index_of x H) as [n|] eqn:E; [|cbn [fst snd]; rewrite rmc_netP_nil; lia].
    destruct (RelayKeys.index_of_some x H n E) as (a & b & HH & Ha). subst H n.
    rewrite (rmc_cw_perm P _ _ (RelayKeys.swap_remove_perm [] a x b)). cbn [fst snd].
    rewrite rmc_cw_cons, rmc_netP_f, rmc_netP_nil. lia.
Qed.

(* send_line's round chain from cap >= 0: every growth goes to (no + n) * 2 > 2 cap >= 0, and replaces g_out
   (W_tr_cnt.v tc_sl_run, as an equality) *)
Lemma rmc_sl_run : forall P f mx no cap rem j o, 0 <= cap ->
  tr_netP P (fst (send_line_b_c.sl_run f mx no cap rem j o)) =
    cphi P (fst (snd (send_line_b_c.sl_run f mx no cap rem j o))) - cphi P cap /\
  0 <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  intros P f. induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
  - cbn [fst snd]. rewrite rmc_netP_nil. split; lia.
  - destruct (rem <=? 0); [cbn [fst snd]; rewrite rmc_netP_nil; split; lia|].
    match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
    destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; cbv beta iota; [|apply IH; exact Hc].
    cbn [fst snd].
    destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia)) as [I1 I2].
    rewrite (cphi_nz P ((no + n) * 2)) in I1 by lia.
    destruct (Z.eqb_spec cap 0) as [E|E]; cbv beta iota.
    + subst cap. rewrite rmc_netP_m, cphi_0. split; lia.
    + rewrite rmc_netP_r, (cphi_nz P cap E). split; lia.
Qed.

Lemma rmc_send : forall P live mx no cap len j o, 0 <= cap ->
  tr_netP P (send_line_b_c.send_line_tr live mx no cap len j o) =
    cphi P (send_line_b_c.send_line_cap live mx no cap len) - cphi P cap /\
  0 <= send_line_b_c.send_line_cap live mx no cap len.
Proof.
  intros P live mx no cap len j o Hc. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
  destruct live; [|rewrite rmc_netP_nil; split; lia].
  destruct (rmc_sl_run P (Z.to_nat len) mx no cap len j o Hc) as [H1 H2].
  rewrite sl_run_fin in H1, H2. rewrite sl_run_fin. split; [exact H1 | exact H2].
Qed.

(* the relayed lines: g_out's growth, then gesture_seen, line by line *)
Lemma rmc_lines_run : forall P rl live mx no cap H ka j o ha ks, 0 <= cap ->
  let p := drain_b_c.lines_run live mx no cap H ka rl j o ha ks in
  cphi P (fst (fst (snd (fst p)))) + cphi P (snd (snd (fst p))) + rmc_cw P (snd (fst (snd (fst p)))) =
    cphi P cap + cphi P ka + rmc_cw P H + tr_netP P (fst (fst p)) /\
  0 <= fst (fst (snd (fst p))).
Proof.
  intros P rl. induction rl as [|l r IH]; intros live mx no cap H ka j o ha ks Hc; cbv zeta;
    cbn [drain_b_c.lines_run fst snd]; [rewrite rmc_netP_nil; split; lia|].
  pose proof (rmc_send P live mx no cap (Z.of_nat (length l) + 1) j o Hc) as [S2 S2n].
  match goal with |- context [drain_b_c.seen_tr H ka l ?jj ha ks] =>
    pose proof (rmc_seen P H ka l jj ha ks) as K2 end.
  match goal with |- context [drain_b_c.lines_run live mx ?no' ?cap' ?H' ?ka' r ?j' ?o' ?ha' ?ks'] =>
    pose proof (IH live mx no' cap' H' ka' j' o' ha' ks' S2n) as I3 end.
  cbv zeta in I3. destruct I3 as [I3 I3n]. rewrite !tr_netP_app. split; [lia | exact I3n].
Qed.

(* list_push: the vector's growth (malloc (128) or realloc 16 cap -> 32 cap), then the text's block *)
Lemma rmc_push_tra : forall P v N CAP m, tr_netP P (ListTr.list_push_tra v N CAP m) =
  rmc_ephi P (drain_b_c.push_cap N CAP) - rmc_ephi P CAP + ReplyCnt.zb (P (m + 1)).
Proof.
  intros P v N CAP m. unfold ListTr.list_push_tra, drain_b_c.push_cap. rewrite tr_netP_app.
  destruct (Z.eqb_spec N CAP) as [EN|EN]; cbv beta iota.
  - destruct (Z.eqb_spec CAP 0) as [E0|E0]; cbv beta iota.
    + rewrite E0, rmc_ephi_0, (rmc_ephi_nz P 8) by lia. rewrite !rmc_netP_m, !rmc_netP_nil.
      replace (AREC * 8) with 128 by reflexivity. lia.
    + rewrite (rmc_ephi_nz P (CAP * 2)), (rmc_ephi_nz P CAP) by lia.
      rewrite rmc_netP_r, rmc_netP_m, !rmc_netP_nil.
      replace (AREC * (CAP * 2)) with (32 * CAP) by (unfold AREC; lia).
      replace (AREC * CAP) with (16 * CAP) by reflexivity. lia.
  - rewrite rmc_netP_m, !rmc_netP_nil. lia.
Qed.

(* reference_feed's pushes: the expected list's vector grows to push_cap, each text adds its block *)
Lemma rmc_pushes : forall P ls n cap j v rs,
  rmc_ephi P (snd (fst (drain_b_c.pushes_run n cap ls j v rs))) + rmc_cw P ls =
    rmc_ephi P cap + tr_netP P (fst (fst (drain_b_c.pushes_run n cap ls j v rs))).
Proof.
  intros P ls. induction ls as [|l r IH]; intros n cap j v rs; cbn [drain_b_c.pushes_run fst snd];
    [rewrite rmc_cw_nil, rmc_netP_nil; lia|].
  match goal with |- context [drain_b_c.pushes_run (n + 1) ?pc r ?jj ?vv ?rr] =>
    pose proof (IH (n + 1) pc jj vv rr) as I2 end.
  rewrite tr_netP_app, rmc_push_tra, rmc_cw_cons. lia.
Qed.

(* the head pending text, dropped once it is all read: its block of |r0| + 1 bytes is freed *)
Lemma rmc_drop : forall P (b : bool) (r0 : list Z) (rs : list (list Z)) x,
  rmc_cw P (if b then rs else r0 :: rs) =
  rmc_cw P (r0 :: rs) + tr_netP P (if b then ListTr.list_drop_tra x (Z.of_nat (length r0)) else []).
Proof.
  intros P [|] r0 rs x; unfold ListTr.list_drop_tra; cbv beta iota;
    rewrite ?rmc_netP_f, ?rmc_netP_nil, !rmc_cw_cons; lia.
Qed.

(* the count weight of drain's state: s->buf, s->held and the held keys, the expected list's vector, g_out, and the
   pending texts' blocks *)
Definition rmc_pot (P : Z -> bool) (s : drain_b_c.dstate) : Z :=
  cphi P (drain_b_c.ds_cap s) + cphi P (drain_b_c.ds_ka s) + rmc_cw P (drain_b_c.ds_H s) +
  rmc_ephi P (drain_b_c.ds_ecap s) + cphi P (drain_b_c.ds_ocap s) + rmc_cw P (drain_b_c.ds_pend s).

Lemma rmc_run : forall P f live mx s j a,
  relay_instance_gone_b_lem.dr_inv s ->
  (length (relay_instance_gone_b_lem.dr_rest s) + (if drain_b_c.ds_eintr s then 2 else 1) <= f)%nat ->
  0 <= drain_b_c.ds_ocap s ->
  rmc_pot P (fst (snd (drain_b_c.drain_run f live mx s j a))) +
    rmc_cw P (RelayModel.lines (drain_b_c.ds_ref s) (relay_instance_gone_b_lem.dr_rest s)) =
  rmc_pot P s + tr_netP P (fst (drain_b_c.drain_run f live mx s j a)) /\
  drain_b_c.ds_pend (fst (snd (drain_b_c.drain_run f live mx s j a))) = [].
Proof.
  intros P f. induction f as [|f IH]; intros live mx [c u sk H ka ei pd off rf en ec no oc] j a INV FU OC;
    [destruct ei; cbn [drain_b_c.ds_eintr] in FU; lia|].
  unfold relay_instance_gone_b_lem.dr_inv in INV. unfold relay_instance_gone_b_lem.dr_rest in FU |- *.
  cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_eintr
       drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap drain_b_c.ds_no
       drain_b_c.ds_ocap] in INV, FU, OC |- *.
  destruct INV as (J & HC & HP).
  pose proof J as (Jk & Jw & Jl & Jz).
  pose proof (relay_instance_gone_b_lem.rig_ll_z _ Jl) as UL'.
  assert (UL'' : 0 <= Z.of_nat (length u) <= 6000) by (clear - UL'; lia).
  pose proof (relay_instance_gone_b_lem.rig_grow c (Z.of_nat (length u)) j (drain_b_c.da_buf a) HC UL'') as [G1 G2].
  pose proof (rmc_grow P c (Z.of_nat (length u)) j (drain_b_c.da_buf a)) as G4.
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
      destruct (IH live mx (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc) jj aa IV
                  ltac:(unfold relay_instance_gone_b_lem.dr_rest;
                        cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_eintr]; lia) OC) as [E EP] end.
    unfold relay_instance_gone_b_lem.dr_rest in E.
    cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref] in E. cbn [fst snd]. rewrite tr_netP_app.
    unfold rmc_pot in E |- *.
    cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend] in E |- *.
    split; [lia | exact EP].
  - destruct pd as [|r0 rs].
    + (* nothing pending: the growth only, no line left, nothing pending at the end *)
      cbn [relay_instance_gone_b_lem.dr_rest_of fst snd].
      assert (Z0 : rmc_cw P (RelayModel.lines rf []) = 0) by reflexivity.
      unfold rmc_pot.
      cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend].
      split; [lia | reflexivity].
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
        pose proof (rmc_pushes P (RelayModel.lines rf d) en ec jj vv rr) as P2 end.
      match goal with |- context [drain_b_c.lines_run live mx no oc H ka rl ?j3 ?o3 ?h3 ?k3] =>
        pose proof (rmc_lines_run P rl live mx no oc H ka j3 o3 h3 k3 OC) as LR;
        destruct (drain_b_c.lines_run live mx no oc H ka rl j3 o3 h3 k3) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] end.
      cbn [fst snd] in LR |- *. destruct LR as [LR LRn].
      match goal with |- context [drain_b_c.drain_run f live mx (drain_b_c.DS _ _ _ _ _ _ _ _ _ ?en' ?ec' ?no' _) ?jj ?aa] =>
        destruct (IH live mx _ jj aa (IVG H1 ka1 en' ec' no' oc1) (FUG H1 ka1 en' ec' no' oc1) LRn) as [E EP] end.
      unfold relay_instance_gone_b_lem.dr_rest in E.
      cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref] in E.
      rewrite RS1, RelayModel.lines_app, rmc_cw_app, !tr_netP_app.
      match goal with |- context [tr_netP P (if ?b then ListTr.list_drop_tra ?x _ else [])] =>
        pose proof (rmc_drop P b r0 rs x) as TD end.
      unfold rmc_pot in E |- *.
      cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend] in E |- *.
      unfold PEND in *.
      split; [lia | exact EP].
Qed.

(* drain_go from drain_init: the reference lines of the pending stream are all pushed, no pending text is left *)
Lemma rmc_drain : forall P live mx no cap e h, 0 <= cap ->
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  rmc_pot P (drain_b_c.drain_fin live mx no cap e h) +
    rmc_cw P (RelayModel.lines (hs_state h) (bzs (pending_stream h))) =
  rmc_pot P (drain_b_c.drain_init no cap e h) + tr_netP P (drain_b_c.drain_tr live mx no cap e h 0 drain_b_c.dadr0) /\
  drain_b_c.ds_pend (drain_b_c.drain_fin live mx no cap e h) = [].
Proof.
  intros P live mx no cap e h Hc IV ER.
  assert (FU : (length (relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h)) +
                (if drain_b_c.ds_eintr (drain_b_c.drain_init no cap e h) then 2 else 1)
                <= S (S (length (pending_stream h))))%nat).
  { rewrite ER. unfold bzs. rewrite length_map. destruct (drain_b_c.ds_eintr _); lia. }
  pose proof (rmc_run P (S (S (length (pending_stream h)))) live mx (drain_b_c.drain_init no cap e h) 0
                drain_b_c.dadr0 IV FU Hc) as E.
  rewrite ER in E. change (drain_b_c.ds_ref (drain_b_c.drain_init no cap e h)) with (hs_state h) in E.
  unfold drain_b_c.drain_fin, drain_b_c.drain_tr, drain_b_c.drain_go. exact E.
Qed.

(* ------------------------------------------------------------------ III. the counts of the represented blocks *)
Lemma rmc_acnt_nil : forall P, Z.of_nat (ReplyCnt.acnt P []) = 0.
Proof. reflexivity. Qed.

Lemma rmc_acnt_cons : forall P b l,
  Z.of_nat (ReplyCnt.acnt P (b :: l)) = ReplyCnt.zb (P (snd b)) + Z.of_nat (ReplyCnt.acnt P l).
Proof.
  intros P [a n] l. unfold ReplyCnt.acnt, ReplyCnt.zb. cbn [map List.filter snd].
  destruct (P n); cbn [length]; lia.
Qed.

Lemma rmc_acnt_app : forall P l1 l2,
  Z.of_nat (ReplyCnt.acnt P (l1 ++ l2)) = Z.of_nat (ReplyCnt.acnt P l1) + Z.of_nat (ReplyCnt.acnt P l2).
Proof. intros P l1 l2. rewrite ReplyCnt.acnt_app. lia. Qed.

Lemma rmc_cnt_opt : forall P (b : bool) a n,
  Z.of_nat (ReplyCnt.acnt P (if b then [] else [(a, n)])) = if b then 0 else ReplyCnt.zb (P n).
Proof. intros P [|] a n; [reflexivity|]. rewrite rmc_acnt_cons, rmc_acnt_nil. cbn [snd]. lia. Qed.

Lemma rmc_cnt_keys : forall P ks,
  Z.of_nat (ReplyCnt.acnt P (map (fun k => (gestures_end_b_c.key_addr k,
    Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) ks)) =
  rmc_cw P (drain_b_c.keys_texts ks).
Proof.
  intros P ks. unfold drain_b_c.keys_texts. induction ks as [|k ks IH]; [reflexivity|].
  cbn [map]. rewrite rmc_acnt_cons, rmc_cw_cons, IH. cbn [snd]. unfold bzs. rewrite length_map. reflexivity.
Qed.

Lemma rmc_cnt_recs : forall P (rs : list (Z * list byte)),
  Z.of_nat (ReplyCnt.acnt P (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) rs)) = rmc_cw P (map snd rs).
Proof.
  intros P rs. induction rs as [|r rs IH]; [reflexivity|]. cbn [map].
  rewrite rmc_acnt_cons, rmc_cw_cons, IH. reflexivity.
Qed.

(* the held array's block is counted at its size re_kh, which is ent_ka when s->held is not NULL *)
Lemma rmc_cnt_entry : forall P e, (re_hp e = 0 \/ re_kh e <> 0) ->
  Z.of_nat (ReplyCnt.acnt P (aentry_blks e)) =
    cphi P (re_cap e) + cphi P (drain_b_c.ent_ka e) + rmc_cw P (drain_b_c.keys_texts (re_keys e)).
Proof.
  intros P e HK. unfold aentry_blks, drain_b_c.ent_ka. rewrite !rmc_acnt_app, !rmc_cnt_opt, rmc_cnt_keys.
  change (if re_cap e =? 0 then 0 else ReplyCnt.zb (P (re_cap e))) with (cphi P (re_cap e)).
  destruct (Z.eqb_spec (re_hp e) 0) as [E|E]; cbv beta iota; [rewrite cphi_0; lia|].
  destruct HK as [HK|HK]; [contradiction|]. rewrite (cphi_nz P (re_kh e) HK). lia.
Qed.

Lemma rmc_cnt_list : forall P l,
  Z.of_nat (ReplyCnt.acnt P (alist_blks l)) = rmc_ephi P (hl_cap l) + rmc_cw P (map snd (hl_recs l)).
Proof. intros P l. unfold alist_blks. rewrite rmc_acnt_app, rmc_cnt_opt, rmc_cnt_recs. reflexivity. Qed.

Lemma rmc_cnt_src : forall P h, Z.of_nat (ReplyCnt.acnt P (asrc_blks h)) =
  ReplyCnt.zb (P APARTIAL) + Z.of_nat (ReplyCnt.acnt P (alist_blks (hs_pending h))) +
  Z.of_nat (ReplyCnt.acnt P (alist_blks (hs_expected h))) + Z.of_nat (ReplyCnt.acnt P (alist_blks (hs_held h))).
Proof. intros P h. unfold asrc_blks. rewrite rmc_acnt_cons, !rmc_acnt_app. cbn [snd]. lia. Qed.

Lemma rmc_cnt_out : forall P cap out, Z.of_nat (ReplyCnt.acnt P (aout_blks cap out)) = cphi P cap.
Proof. intros P cap out. unfold aout_blks. rewrite rmc_cnt_opt. reflexivity. Qed.

(* ------------------------------------------------------------------ IV. drain's count growth *)
(* the closing arithmetic, at any final state F, trace count T and drained lines L: what dr_rel says of the entry and
   the source drain leaves, and the potential equation of rmc_drain *)
Lemma rmc_close : forall (P : Z -> bool) (F : drain_b_c.dstate) (T : Z) (L : list (list Z)) (g : Z -> byte)
    no cap out cap' out' e h e' h',
  (re_hp e = 0 \/ re_kh e <> 0) -> (re_hp e' = 0 \/ re_kh e' <> 0) ->
  rmc_pot P F + rmc_cw P L = rmc_pot P (drain_b_c.drain_init no cap e h) + T ->
  drain_b_c.ds_pend F = [] ->
  cap' = drain_b_c.ds_ocap F ->
  re_cap e' = drain_b_c.ds_cap F ->
  drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H F ->
  drain_b_c.ent_ka e' = drain_b_c.ds_ka F ->
  hl_cap (hs_expected h') = drain_b_c.ds_ecap F ->
  hl_recs (hs_pending h') = [] ->
  hl_cap (hs_pending h') = hl_cap (hs_pending h) ->
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map g) L ->
  hs_held h' = hs_held h ->
  Z.of_nat (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out')) =
  Z.of_nat (ReplyCnt.acnt P (aentry_blks e ++ asrc_blks h ++ aout_blks cap out)) + T.
Proof.
  intros P F T L g no cap out cap' out' e h e' h' HE HE' D DP OC R4 R7 R8 R11 R16 R19 R22 R24.
  assert (Z0 : rmc_cw P (map snd (hl_recs (hs_pending h'))) = 0) by (rewrite R16; reflexivity).
  rewrite !rmc_acnt_app, !rmc_cnt_entry by assumption.
  rewrite !rmc_cnt_src, !rmc_cnt_list, !rmc_cnt_out, Z0.
  rewrite OC, R4, R7, R8, R11, R19, R22, R24, rmc_cw_app, rmc_cw_map.
  unfold rmc_pot, drain_b_c.drain_init in D.
  cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend] in D.
  rewrite rmc_cw_pend, DP, rmc_cw_nil in D.
  lia.
Qed.

(* rmc_drain at drain's names in W_contract.v *)
Lemma rmc_drain_dr : forall P c mx no cap e h, 0 <= cap ->
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  rmc_pot P (dr_fin c mx no cap e h) + rmc_cw P (dr_lines h) =
  rmc_pot P (drain_b_c.drain_init no cap e h) + tr_netP P (dr_tr c mx no cap e h) /\
  drain_b_c.ds_pend (dr_fin c mx no cap e h) = [].
Proof. intros P c mx no cap e h Hc IV ER. exact (rmc_drain P (dr_live c h) mx no cap e h Hc IV ER). Qed.

(* a dead drain keeps g_capout *)
Lemma rmc_ocap : forall c mx no cap e h,
  (if dr_live c h then drain_b_c.ds_ocap (dr_fin c mx no cap e h) else cap) = drain_b_c.ds_ocap (dr_fin c mx no cap e h).
Proof.
  intros c mx no cap e h. unfold dr_fin. destruct (dr_live c h); [reflexivity|].
  destruct (relay_instance_gone_b_lem.rig_drain_false mx no no cap e h 0 drain_b_c.dadr0) as (_ & _ & _ & X).
  symmetry. exact X.
Qed.

Lemma rmc_dr_cnt : forall c mx no cap out out' e h e' h' LB (P : Z -> bool),
  let fin := dr_fin c mx no cap e h in
  let cap' := if dr_live c h then drain_b_c.ds_ocap fin else cap in
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  (re_hp e = 0 \/ re_kh e <> 0) -> (re_hp e' = 0 \/ re_kh e' <> 0) -> 0 <= cap ->
  dr_rel c mx no cap e h e' h' LB ->
  Z.of_nat (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out')) =
  Z.of_nat (ReplyCnt.acnt P (aentry_blks e ++ asrc_blks h ++ aout_blks cap out)) + tr_netP P (dr_tr c mx no cap e h).
Proof.
  intros c mx no cap out out' e h e' h' LB P. cbv zeta.
  intros IV ER HE HE' Hc REL.
  destruct (rmc_drain_dr P c mx no cap e h Hc IV ER) as [D DP].
  destruct REL as (_ & _ & _ & R4 & _ & _ & R7 & R8 & _ & _ & R11 & _ & _ & _ & _ & R16 & _ & _ & R19 & _ & _ & R22 &
                   _ & R24 & _).
  exact (rmc_close P _ _ _ _ no cap out _ out' e h e' h' HE HE' D DP (rmc_ocap c mx no cap e h)
           R4 R7 R8 R11 R16 R19 R22 R24).
Qed.

(* the corollary at the trace's count peak *)
Lemma rmc_dr_cnt_peak : forall c mx no cap out out' e h e' h' LB (P : Z -> bool),
  let fin := dr_fin c mx no cap e h in
  let cap' := if dr_live c h then drain_b_c.ds_ocap fin else cap in
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  (re_hp e = 0 \/ re_kh e <> 0) -> (re_hp e' = 0 \/ re_kh e' <> 0) -> 0 <= cap ->
  dr_rel c mx no cap e h e' h' LB ->
  (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out') <=
   ReplyCnt.acnt P (aentry_blks e ++ asrc_blks h ++ aout_blks cap out) +
   Z.to_nat (ReplyCnt.tr_peakP P (dr_tr c mx no cap e h)))%nat.
Proof.
  intros c mx no cap out out' e h e' h' LB P. cbv zeta.
  intros IV ER HE HE' Hc REL.
  pose proof (rmc_dr_cnt c mx no cap out out' e h e' h' LB P IV ER HE HE' Hc REL) as E. cbv zeta in E.
  pose proof (rmc_net_peak _ P (dr_tr c mx no cap e h)) as N.
  pose proof (ReplyCnt.tr_peakP_nonneg _ P (dr_tr c mx no cap e h)) as N0.
  lia.
Qed.

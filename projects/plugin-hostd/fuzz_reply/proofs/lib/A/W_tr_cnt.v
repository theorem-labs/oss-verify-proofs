(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The ROOM round's count peaks: for each composite allocating spec, its constant count peak K_spec PROVED over the
   spec's own request trace, `ReplyCnt.tr_peakP P (<trace> ..) <= K_spec` for EVERY predicate P : Z -> bool (the allocator
   side's acceptance condition for the audit commit's constants).  Only lemmas; no spec text is stated here.
   - The helpers: tr_peakP_app (ReplyCnt.tr_peakP_w + ReplyTrPeakW.tr_peak_w_app), tr_peakP_frees (a trace of frees
     only has peak 0), and the chain potential of one g_out block (tc_chain): cphi P c = the count of the g_out block of
     capacity c (0 for c = 0, no block).  A segment that takes g_out from cap c to cap c' (growth events RMalloc c'
     from cap 0, RRealloc c c' otherwise, interleaved with frees of OTHER blocks) has peak <= 2 - cphi P c and net
     count <= cphi P c' - cphi P c; this composes over ++ when the next segment starts at the previous one's final cap
     (tc_chain_app), so every send-chain trace has peak <= 2 (a realloc's new block is counted before its old one is
     freed: the transient adds 1 to a running count <= 1).
   - The per-spec peaks at the audit commit's constants (decision (A)): tc_sl, tc_re (2), tc_ge (3),
     tc_gse (4), tc_rf (5), each a corollary of the bound 2 (tc_ge2, tc_gse2, tc_rf2); tc_lp, tc_gm / tc_gm_H,
     tc_ra / tc_ra_none, tc_oa; the frees-only zeros tc_lf, tc_hlf, tc_sr, tc_ldrop, tc_cshe; and the data-dependent
     tc_dr, tc_cnl (the trace's own peak plus 2).  No lemma for rr / rig (data-dependent peaks).
   Hypotheses beyond the traces' arguments (the counterexamples are proved below as *_cex lemmas):
   - 0 <= cap (tc_sl, tc_re, tc_ge, tc_gse, tc_rf; the chain potential needs it): with cap < 0 a round can grow to
     capacity 0, after which the next growth is an RMalloc that does not free the counted block (tc_sl_cex: send_line
     peak 3 > 2).
   - Forall (fun x => x <> []) xs (tc_gse): gse_tr runs ge_tr at sl_live c XL but threads ge_cap, whose second send
     is at sl_live (sl_ctl c XL) 5; for XL = 0 the trace has no request while ge_cap grows, so the next key reallocs
     from a cap the trace never made, and each such gap keeps one more block counted (tc_gse_cex: peak 5 > 4).
     gestures_end's keys are 1..6000 bytes
     (gestures_end_contract) and gse_spec's are 14..APARTIAL bytes (its premise W_contract.v aheld_ok).
   - 0 <= FD -> C = 0 \/ N <> C (tc_ra, tc_oa): a full table of C <> 0 entries reallocs to 2 C entries, of size 112 C,
     which is ATABLE only for C = 8 (tc_ra_cex: C = N = 16, peak 1 for P := (=? 1792) while zb (P ATABLE) = 0).
     ra_spec's callers hold it: for fd >= 0 the relay is empty (g_capsrc 0) or arelay_at (g_capsrc 16, g_nsrc = |es|
     < 4). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_kit W_journal W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr RelayRunF send_line_c send_line_b_c gesture_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  relay_event_b_c gestures_end_b_c relay_finish_b_c relay_add_b_c HarnessTr CheckRep RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt ReplyTrPeakW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the helpers *)
Lemma zb_bounds : forall b, 0 <= ReplyCnt.zb b <= 1.
Proof. intros []; cbn; lia. Qed.

(* the net count of a trace at the weight zb (P n): the count change it makes *)
Definition tr_netP {X : Type} (P : Z -> bool) (tr : list (RelayRunT.rev X)) : Z :=
  ReplyTrPeakW.tr_net_w (fun n => ReplyCnt.zb (P n)) tr.

Lemma tr_peakP_app : forall (X : Type) (P : Z -> bool) (a b : list (RelayRunT.rev X)),
  ReplyCnt.tr_peakP P (a ++ b) = Z.max (ReplyCnt.tr_peakP P a) (tr_netP P a + ReplyCnt.tr_peakP P b).
Proof. intros X P a b. unfold tr_netP. rewrite !ReplyCnt.tr_peakP_w. apply ReplyTrPeakW.tr_peak_w_app. Qed.
Lemma tr_netP_app : forall (X : Type) (P : Z -> bool) (a b : list (RelayRunT.rev X)),
  tr_netP P (a ++ b) = tr_netP P a + tr_netP P b.
Proof. intros X P a b. unfold tr_netP. apply ReplyTrPeakW.tr_net_w_app. Qed.
Lemma tr_netP_cons : forall (X : Type) (P : Z -> bool) (ev : RelayRunT.rev X) r,
  tr_netP P (ev :: r) =
  match ev with
  | RelayRunT.RMalloc n => ReplyCnt.zb (P n)
  | RelayRunT.RFree k _ => - ReplyCnt.zb (P k)
  | RelayRunT.RRealloc k n _ => ReplyCnt.zb (P n) - ReplyCnt.zb (P k)
  end + tr_netP P r.
Proof. intros. reflexivity. Qed.

(* a trace of frees only: its peak is 0, its net count <= 0 *)
Definition is_free {X : Type} (ev : RelayRunT.rev X) : bool :=
  match ev with RelayRunT.RFree _ _ => true | _ => false end.
Definition frees_only {X : Type} (tr : list (RelayRunT.rev X)) : Prop := forallb is_free tr = true.
Lemma frees_only_app : forall (X : Type) (a b : list (RelayRunT.rev X)),
  frees_only a -> frees_only b -> frees_only (a ++ b).
Proof. unfold frees_only. intros X a b Ha Hb. rewrite forallb_app, Ha, Hb. reflexivity. Qed.
Lemma tr_peakP_frees : forall (X : Type) (P : Z -> bool) (tr : list (RelayRunT.rev X)),
  frees_only tr -> ReplyCnt.tr_peakP P tr = 0.
Proof.
  intros X P tr. induction tr as [|[n|k a|k n a] r IH]; intros H; unfold frees_only in H;
    cbn [forallb is_free andb] in H; [reflexivity | discriminate | | discriminate].
  cbn [ReplyCnt.tr_peakP]. rewrite (IH H). pose proof (zb_bounds (P k)). lia.
Qed.
Lemma tr_netP_frees : forall (X : Type) (P : Z -> bool) (tr : list (RelayRunT.rev X)),
  frees_only tr -> tr_netP P tr <= 0.
Proof.
  intros X P tr. induction tr as [|[n|k a|k n a] r IH]; intros H; unfold frees_only in H;
    cbn [forallb is_free andb] in H; [reflexivity | discriminate | | discriminate].
  rewrite tr_netP_cons. pose proof (IH H). pose proof (zb_bounds (P k)). lia.
Qed.

(* ------------------------------------------------------------------ the chain potential of one g_out block *)
(* the count of the g_out block of capacity c: none when c = 0 *)
Definition cphi (P : Z -> bool) (c : Z) : Z := if c =? 0 then 0 else ReplyCnt.zb (P c).
Lemma cphi_bounds : forall P c, 0 <= cphi P c <= 1.
Proof. intros P c. unfold cphi. destruct (c =? 0); [lia | apply zb_bounds]. Qed.
Lemma cphi_0 : forall P, cphi P 0 = 0.
Proof. reflexivity. Qed.
Lemma cphi_nz : forall P c, c <> 0 -> cphi P c = ReplyCnt.zb (P c).
Proof. intros P c H. unfold cphi. rewrite (proj2 (Z.eqb_neq c 0) H). reflexivity. Qed.

(* t takes g_out from cap c to cap c' >= 0: its peak is within 2 less the start block's count, its net count is the
   end block's count less the start block's (or less) *)
Definition tc_chain {X : Type} (P : Z -> bool) (c : Z) (t : list (RelayRunT.rev X)) (c' : Z) : Prop :=
  ReplyCnt.tr_peakP P t <= 2 - cphi P c /\ tr_netP P t <= cphi P c' - cphi P c /\ 0 <= c'.

Lemma tc_chain_le2 : forall (X : Type) P c (t : list (RelayRunT.rev X)) c',
  tc_chain P c t c' -> ReplyCnt.tr_peakP P t <= 2.
Proof. intros X P c t c' (H & _). pose proof (cphi_bounds P c). lia. Qed.
Lemma tc_chain_nonneg : forall (X : Type) P c (t : list (RelayRunT.rev X)) c', tc_chain P c t c' -> 0 <= c'.
Proof. intros X P c t c' (_ & _ & H). exact H. Qed.
Lemma tc_chain_nil : forall (X : Type) P c, 0 <= c -> tc_chain P c (@nil (RelayRunT.rev X)) c.
Proof.
  intros X P c Hc. unfold tc_chain, tr_netP, ReplyTrPeakW.tr_net_w. cbn [ReplyCnt.tr_peakP fold_right].
  pose proof (cphi_bounds P c). lia.
Qed.
Lemma tc_chain_app : forall (X : Type) P c c1 c2 (a b : list (RelayRunT.rev X)),
  tc_chain P c a c1 -> tc_chain P c1 b c2 -> tc_chain P c (a ++ b) c2.
Proof.
  intros X P c c1 c2 a b (A1 & A2 & A3) (B1 & B2 & B3). unfold tc_chain.
  rewrite tr_peakP_app, tr_netP_app. pose proof (cphi_bounds P c1). lia.
Qed.
Lemma tc_chain_frees : forall (X : Type) P c (t : list (RelayRunT.rev X)), 0 <= c -> frees_only t -> tc_chain P c t c.
Proof.
  intros X P c t Hc Ht. unfold tc_chain. rewrite (tr_peakP_frees X P t Ht).
  pose proof (tr_netP_frees X P t Ht). pose proof (cphi_bounds P c). lia.
Qed.
Lemma tc_chain_free_cons : forall (X : Type) P c c' k a (r : list (RelayRunT.rev X)),
  0 <= c -> tc_chain P c r c' -> tc_chain P c (RelayRunT.RFree k a :: r) c'.
Proof.
  intros X P c c' k a r Hc H.
  exact (tc_chain_app X P c c c' [RelayRunT.RFree k a] r (tc_chain_frees X P c [RelayRunT.RFree k a] Hc eq_refl) H).
Qed.
(* a growth from no block (cap 0): malloc (c') *)
Lemma tc_chain_malloc : forall (X : Type) P c' c'' (r : list (RelayRunT.rev X)),
  c' <> 0 -> tc_chain P c' r c'' -> tc_chain P 0 (RelayRunT.RMalloc c' :: r) c''.
Proof.
  intros X P c' c'' r Hc (R1 & R2 & R3). unfold tc_chain. rewrite tr_netP_cons. cbn [ReplyCnt.tr_peakP].
  rewrite cphi_0. rewrite (cphi_nz P c' Hc) in R1, R2. pose proof (zb_bounds (P c')). pose proof (cphi_bounds P c'').
  lia.
Qed.
(* a growth of the block of cap c <> 0: realloc (c -> c'), the new block counted before the old one is freed *)
Lemma tc_chain_realloc : forall (X : Type) P c c' c'' a (r : list (RelayRunT.rev X)),
  c <> 0 -> c' <> 0 -> tc_chain P c' r c'' -> tc_chain P c (RelayRunT.RRealloc c c' a :: r) c''.
Proof.
  intros X P c c' c'' a r Hc Hc' (R1 & R2 & R3). unfold tc_chain. rewrite tr_netP_cons. cbn [ReplyCnt.tr_peakP].
  rewrite (cphi_nz P c Hc). rewrite (cphi_nz P c' Hc') in R1, R2.
  pose proof (zb_bounds (P c')). pose proof (zb_bounds (P c)). pose proof (cphi_bounds P c''). lia.
Qed.

(* ------------------------------------------------------------------ the send chain *)
(* one round chain of send_line, from cap >= 0: every growth goes to (no + n) * 2 > 2 cap >= 0 *)
Lemma tc_sl_run : forall P f mx no cap rem j o, 0 <= cap ->
  tc_chain P cap (fst (send_line_b_c.sl_run f mx no cap rem j o)) (fst (snd (send_line_b_c.sl_run f mx no cap rem j o))).
Proof.
  intros P f. induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
  - cbn [fst snd]. apply tc_chain_nil. exact Hc.
  - destruct (rem <=? 0); [cbn [fst snd]; apply tc_chain_nil; exact Hc|].
    match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
    destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; cbv beta iota; [|apply IH; exact Hc].
    cbn [fst snd].
    pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia)) as I.
    destruct (Z.eqb_spec cap 0) as [E|E]; cbv beta iota.
    + subst cap. apply tc_chain_malloc; [lia | exact I].
    + apply tc_chain_realloc; [exact E | lia | exact I].
Qed.
Lemma tc_send : forall P live mx no cap len j o, 0 <= cap ->
  tc_chain P cap (send_line_b_c.send_line_tr live mx no cap len j o) (send_line_b_c.send_line_cap live mx no cap len).
Proof.
  intros P live mx no cap len j o Hc. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
  destruct live; [|apply tc_chain_nil; exact Hc].
  pose proof (tc_sl_run P (Z.to_nat len) mx no cap len j o Hc) as H.
  rewrite sl_run_fin in H. rewrite sl_run_fin. exact H.
Qed.
Lemma tc_gend : forall P live mx no cap xl j o, 0 <= cap ->
  tc_chain P cap (gesture_end_b_c.gesture_end_tr live mx no cap xl j o)
    (gesture_end_b_c.gesture_end_cap live mx no cap xl).
Proof.
  intros P live mx no cap xl j o Hc. unfold gesture_end_b_c.gesture_end_tr, gesture_end_b_c.gesture_end_cap. cbv zeta.
  pose proof (tc_send P live mx no cap xl j o Hc) as H1.
  eapply tc_chain_app; [exact H1|]. apply tc_send. exact (tc_chain_nonneg _ _ _ _ _ H1).
Qed.

(* ================================================================== the per-spec count peaks *)
(* send_line: one round chain *)
Lemma tc_sl : forall P c mx no cap len, 0 <= cap -> ReplyCnt.tr_peakP P (sl_tr c mx no cap len) <= 2.
Proof. intros P c mx no cap len Hc. unfold sl_tr. eapply tc_chain_le2. apply tc_send. exact Hc. Qed.

(* relay_event: send_line (line, EL + 1) *)
Lemma tc_re : forall P live mx no cap el j o, 0 <= cap ->
  ReplyCnt.tr_peakP P (relay_event_b_c.relay_event_tr live mx no cap el j o) <= 2.
Proof. intros P live mx no cap el j o Hc. unfold relay_event_b_c.relay_event_tr. eapply tc_chain_le2. apply tc_send. exact Hc. Qed.

(* gesture_end: two sends on the same g_out, the second from the first's final cap *)
Lemma tc_ge_chain : forall P c mx no cap XL, 0 <= cap ->
  tc_chain P cap (ge_tr c mx no cap XL) (gesture_end_b_c.gesture_end_cap (sl_live c XL) mx no cap XL).
Proof. intros P c mx no cap XL Hc. unfold ge_tr. apply tc_gend. exact Hc. Qed.
Lemma tc_ge2 : forall P c mx no cap XL, 0 <= cap -> ReplyCnt.tr_peakP P (ge_tr c mx no cap XL) <= 2.
Proof. intros P c mx no cap XL Hc. eapply tc_chain_le2. apply tc_ge_chain. exact Hc. Qed.
(* the audit commit's constant (decision (A)): 3 *)
Lemma tc_ge : forall P c mx no cap XL, 0 <= cap -> ReplyCnt.tr_peakP P (ge_tr c mx no cap XL) <= 3.
Proof. intros P c mx no cap XL Hc. pose proof (tc_ge2 P c mx no cap XL Hc). lia. Qed.

(* gestures_end's key run: ge_cap is the final cap of the key's ge_tr when the key is not empty (ge_live5) *)
Lemma ge_cap_tr : forall c mx no cap XL, XL <> 0 ->
  ge_cap c mx no cap XL = gesture_end_b_c.gesture_end_cap (sl_live c XL) mx no cap XL.
Proof.
  intros c mx no cap XL HXL. unfold ge_cap, sl_cap, sl_no, gesture_end_b_c.gesture_end_cap.
  rewrite (ge_live5 c XL HXL). destruct (sl_live c XL); reflexivity.
Qed.
Lemma tc_gse_chain : forall P xs c mx no cap, 0 <= cap -> Forall (fun x => x <> []) xs ->
  exists c', tc_chain P cap (gse_tr c mx no cap xs) c'.
Proof.
  intros P xs. induction xs as [|x xs IH]; intros c mx no cap Hc HF.
  - exists cap. apply tc_chain_nil. exact Hc.
  - apply Forall_cons_iff in HF as [Hx HF].
    assert (HXL : Z.of_nat (length x) <> 0) by (destruct x as [|b x]; [congruence | cbn [length]; lia]).
    pose proof (tc_ge_chain P c mx no cap (Z.of_nat (length x)) Hc) as H1.
    rewrite <- (ge_cap_tr c mx no cap _ HXL) in H1.
    pose proof (tc_chain_nonneg _ _ _ _ _ H1) as H1n.
    destruct (IH (ge_ctl c (Z.of_nat (length x))) mx (ge_no c no (Z.of_nat (length x)))
      (ge_cap c mx no cap (Z.of_nat (length x))) H1n HF) as [c' H2].
    exists c'. cbn [gse_tr]. eapply tc_chain_app; [exact H1|]. apply tc_chain_free_cons; [exact H1n | exact H2].
Qed.
Lemma tc_gse2 : forall P c mx no cap xs, 0 <= cap -> Forall (fun x => x <> []) xs ->
  ReplyCnt.tr_peakP P (gse_tr c mx no cap xs) <= 2.
Proof.
  intros P c mx no cap xs Hc HF. destruct (tc_gse_chain P xs c mx no cap Hc HF) as [c' H].
  exact (tc_chain_le2 _ _ _ _ _ H).
Qed.
(* the audit commit's constant (decision (A)): 4; the non-empty keys are still needed (tc_gse_cex) *)
Lemma tc_gse : forall P c mx no cap xs, 0 <= cap -> Forall (fun x => x <> []) xs ->
  ReplyCnt.tr_peakP P (gse_tr c mx no cap xs) <= 4.
Proof. intros P c mx no cap xs Hc HF. pose proof (tc_gse2 P c mx no cap xs Hc HF). lia. Qed.

(* relay_finish: per entry the free of s->buf, then gestures_end on the one g_out chain *)
Lemma ker_cap_lens : forall live mx (xks1 xks2 : list (Z * RelayRunF.adrF)), map fst xks1 = map fst xks2 ->
  forall no cap j1 o1 j2 o2,
  fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks1 j1 o1)) =
  fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks2 j2 o2)).
Proof.
  intros live mx xks1. induction xks1 as [|[xl ka] r IH]; intros [|[xl' ka'] r'] E no cap j1 o1 j2 o2;
    cbn [map fst] in E; try discriminate; [reflexivity|].
  injection E as <- E. cbn [gestures_end_b_c.keys_end_run fst snd]. apply IH. exact E.
Qed.
Lemma ge_cap_of_keys : forall nm live mx no cap ks j o,
  gestures_end_b_c.gestures_end_cap live mx no cap (gestures_end_b_c.key_lens ks) =
  fst (snd (gestures_end_b_c.keys_end_run live mx no cap (gestures_end_b_c.key_runs nm ks) j o)).
Proof.
  intros nm live mx no cap ks j o. unfold gestures_end_b_c.gestures_end_cap. apply ker_cap_lens.
  unfold gestures_end_b_c.key_runs, gestures_end_b_c.key_lens. rewrite !map_map. reflexivity.
Qed.
Lemma tc_ker : forall P live mx xks no cap j o, 0 <= cap ->
  tc_chain P cap (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o))
    (fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o))).
Proof.
  intros P live mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o Hc;
    cbn [gestures_end_b_c.keys_end_run fst snd]; [apply tc_chain_nil; exact Hc|].
  pose proof (tc_gend P live mx no cap xl j o Hc) as H1. pose proof (tc_chain_nonneg _ _ _ _ _ H1) as H1n.
  eapply tc_chain_app; [exact H1|]. apply tc_chain_free_cons; [exact H1n|]. apply IH. exact H1n.
Qed.
Lemma tc_gsend : forall P live mx no cap xks HP KH j o ha, 0 <= cap ->
  tc_chain P cap (gestures_end_b_c.gestures_end_tr live mx no cap xks HP KH j o ha)
    (fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o))).
Proof.
  intros P live mx no cap xks HP KH j o ha Hc. unfold gestures_end_b_c.gestures_end_tr.
  pose proof (tc_ker P live mx xks no cap j o Hc) as H1.
  eapply tc_chain_app; [exact H1|]. apply tc_chain_frees; [exact (tc_chain_nonneg _ _ _ _ _ H1)|].
  destruct (HP =? 0); reflexivity.
Qed.
Lemma tc_eer : forall P nm live mx es no cap j o, 0 <= cap ->
  tc_chain P cap (fst (relay_finish_b_c.entries_end_run nm live mx no cap es j o))
    (fst (snd (relay_finish_b_c.entries_end_run nm live mx no cap es j o))).
Proof.
  intros P nm live mx es. induction es as [|e r IH]; intros no cap j o Hc;
    cbn [relay_finish_b_c.entries_end_run fst snd]; [apply tc_chain_nil; exact Hc|].
  apply (tc_chain_app _ _ _ cap); [apply tc_chain_frees; [exact Hc | destruct (re_cap e =? 0); reflexivity]|].
  match goal with |- tc_chain _ _ (gestures_end_b_c.gestures_end_tr _ _ _ _ _ _ _ ?J _ _ ++ _) _ =>
    rewrite (ge_cap_of_keys nm live mx no cap (re_keys e) J o);
    pose proof (tc_gsend P live mx no cap (gestures_end_b_c.key_runs nm (re_keys e)) (re_hp e) (re_kh e) J o
      (nm (re_hp e)) Hc) as H1
  end.
  eapply tc_chain_app; [exact H1|]. apply IH. exact (tc_chain_nonneg _ _ _ _ _ H1).
Qed.
(* Why the bound is 2 and not 1 (the round's entry premise does not cover the transient of a later round's realloc):
   "Pcls 1 := fun z => z =? K, K = gse_cap after round 0, entry cap 0, no live block of size K, LPRIM 1 = 1. The entry
   premise holds (0 + 1 <= 1), but round 1's GSE needs 1 + 1 <= 1." *)
Lemma tc_rf2 : forall P nm live mx no cap es j o, 0 <= cap ->
  ReplyCnt.tr_peakP P (relay_finish_b_c.relay_finish_tr nm live mx no cap es j o) <= 2.
Proof.
  intros P nm live mx no cap es j o Hc. unfold relay_finish_b_c.relay_finish_tr.
  eapply tc_chain_le2. apply tc_eer. exact Hc.
Qed.
(* the audit commit's constant (decision (A)): 5 *)
Lemma tc_rf : forall P nm live mx no cap es j o, 0 <= cap ->
  ReplyCnt.tr_peakP P (relay_finish_b_c.relay_finish_tr nm live mx no cap es j o) <= 5.
Proof. intros P nm live mx no cap es j o Hc. pose proof (tc_rf2 P nm live mx no cap es j o Hc). lia. Qed.

(* list_push: the vector's growth (malloc (128) or realloc 16 cap -> 32 cap), then strndup's malloc (n + 1) *)
Lemma tc_lp : forall P l n,
  ReplyCnt.tr_peakP P (lp_tr l n) <=
  Z.of_nat ((if P (lp_vbytes l) && lp_grow l then 1 else 0) + (if P (n + 1) then 1 else 0)).
Proof.
  intros P l n. unfold lp_tr, lp_grow, lp_vbytes, ListTr.list_push_tra.
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [E|E].
  - rewrite andb_true_r. unfold grow_cap. rewrite E, Z.eqb_refl.
    destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0]; cbn [app ReplyCnt.tr_peakP].
    + replace (AREC * 8) with 128 by reflexivity.
      destruct (P 128), (P (n + 1)); cbn; lia.
    + replace (AREC * (2 * hl_cap l)) with (32 * hl_cap l) by (unfold AREC; lia).
      destruct (P (32 * hl_cap l)), (P (16 * hl_cap l)), (P (n + 1)); cbn; lia.
  - rewrite andb_false_r. cbn [app ReplyCnt.tr_peakP]. destruct (P (n + 1)); cbn; lia.
Qed.

(* gesture_model: a "begin" of a key not held pushes it (growth + strndup), an "end" of a held key frees it *)
Lemma tc_gm : forall P s ln,
  ReplyCnt.tr_peakP P (HarnessTr.gesture_model_tr s ln) <=
  Z.of_nat ((if P (AREC * grow_cap (ListTr.sh_n s) (ListTr.sh_cap s)) && (ListTr.sh_n s =? ListTr.sh_cap s)
             then 1 else 0) + 1).
Proof.
  intros P s ln. unfold HarnessTr.gesture_model_tr.
  destruct (RelayModel.gesture ln) as [[[|] x]|].
  - destruct (existsb _ _); [cbn [ReplyCnt.tr_peakP]; lia|].
    unfold ListTr.list_push_tr, ListTr.list_grow_tr.
    destruct (Z.eqb_spec (ListTr.sh_n s) (ListTr.sh_cap s)) as [E|E].
    + rewrite andb_true_r. unfold grow_cap. rewrite E, Z.eqb_refl.
      destruct (Z.eqb_spec (ListTr.sh_cap s) 0) as [E0|E0]; cbn [app ReplyCnt.tr_peakP].
      * replace (AREC * 8) with 128 by reflexivity.
        destruct (P 128), (P (Z.of_nat (length x) + 1)); cbn; lia.
      * replace (AREC * (2 * ListTr.sh_cap s)) with (32 * ListTr.sh_cap s) by (unfold AREC; lia).
        destruct (P (32 * ListTr.sh_cap s)), (P (16 * ListTr.sh_cap s)), (P (Z.of_nat (length x) + 1)); cbn; lia.
    + rewrite andb_false_r. cbn [app ReplyCnt.tr_peakP]. destruct (P (Z.of_nat (length x) + 1)); cbn; lia.
  - destruct (HarnessTr.find_key _ _) as [i|]; [rewrite tr_peakP_frees by reflexivity; lia|].
    cbn [ReplyCnt.tr_peakP]. lia.
  - cbn [ReplyCnt.tr_peakP]. lia.
Qed.
(* the same at gm_spec's hlist H, its trace over sh_of nm H: lp_grow / lp_vbytes are sh_of's growth test and bytes *)
Lemma tc_gm_H : forall P nm H ln,
  ReplyCnt.tr_peakP P (HarnessTr.gesture_model_tr (ListTr.sh_of nm H) ln) <=
  Z.of_nat ((if P (lp_vbytes H) && lp_grow H then 1 else 0) + 1).
Proof.
  intros P nm H ln.
  assert (En : ListTr.sh_n (ListTr.sh_of nm H) = hl_n H).
  { unfold ListTr.sh_n, ListTr.sh_of, hl_n. cbn [ListTr.sh_recs]. rewrite length_map. reflexivity. }
  pose proof (tc_gm P (ListTr.sh_of nm H) ln) as G. rewrite En in G. exact G.
Qed.

(* relay_add: the table is made (malloc (16 * 56 = ATABLE)) from the empty table only *)
Lemma tc_ra_none : forall P FD N C g, (FD < 0 \/ N <> C) ->
  ReplyCnt.tr_peakP P (relay_add_b_c.relay_add_tr FD N C g) = 0.
Proof.
  intros P FD N C g H. unfold relay_add_b_c.relay_add_tr.
  replace ((FD <? 0) || negb (N =? C)) with true; [reflexivity|].
  destruct H as [H|H].
  - rewrite (proj2 (Z.ltb_lt FD 0) H). reflexivity.
  - rewrite (proj2 (Z.eqb_neq N C) H), orb_true_r. reflexivity.
Qed.
(* the hypothesis is ra_spec's: for fd >= 0 either the relay is empty (C = g_capsrc = 0) or it is arelay_at, whose
   g_capsrc is 16 and g_nsrc = |es| < 4 (ra_spec's `0 <= fd -> (length es < 4)%nat`) *)
Lemma tc_ra : forall P FD N C g, (0 <= FD -> C = 0 \/ N <> C) ->
  ReplyCnt.tr_peakP P (relay_add_b_c.relay_add_tr FD N C g) <= ReplyCnt.zb (P ATABLE).
Proof.
  intros P FD N C g H. pose proof (zb_bounds (P ATABLE)) as ZA.
  destruct (Z.ltb_spec FD 0) as [HF|HF]; [rewrite tc_ra_none by (left; exact HF); lia|].
  specialize (H HF).
  destruct (Z.eqb_spec N C) as [E|E]; [|rewrite tc_ra_none by (right; exact E); lia].
  destruct H as [->|H]; [|contradiction].
  unfold relay_add_b_c.relay_add_tr. rewrite E. cbn [Z.eqb negb].
  destruct (FD <? 0); cbn [orb]; cbv beta iota zeta; [cbn [ReplyCnt.tr_peakP]; lia|].
  change (16 * relay_add_b_c.SRC_ENTRY) with ATABLE. cbn [ReplyCnt.tr_peakP]. lia.
Qed.
(* without the hypothesis the bound fails: a full table of 16 entries reallocs to 32 entries (1792 bytes) *)
Lemma tc_ra_cex : forall g,
  ReplyCnt.tr_peakP (fun z => z =? 1792) (relay_add_b_c.relay_add_tr 0 16 16 g) = 1 /\
  ReplyCnt.zb ((fun z => z =? 1792) ATABLE) = 0.
Proof. intros g. split; vm_compute; reflexivity. Qed.

(* op_add: the 6000-byte buffer, then relay_add *)
Lemma tc_oa : forall P i FD N C g, (0 <= FD -> C = 0 \/ N <> C) ->
  ReplyCnt.tr_peakP P (HarnessTr.op_add_tr i FD N C g) <= ReplyCnt.zb (P 6000) + ReplyCnt.zb (P ATABLE).
Proof.
  intros P i FD N C g H. pose proof (zb_bounds (P 6000)). pose proof (zb_bounds (P ATABLE)).
  unfold HarnessTr.op_add_tr. destruct i as [i|]; cbn [ReplyCnt.tr_peakP]; [|lia].
  pose proof (tc_ra P FD N C g H). lia.
Qed.

(* ------------------------------------------------------------------ the frees-only traces *)
Lemma fo_recs_drop : forall rs, frees_only (ListTr.recs_drop_tr rs).
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. unfold frees_only, ListTr.recs_drop_tr in *.
  cbn [map concat ListTr.rec_drop_tr app forallb is_free andb]. exact IH.
Qed.
Lemma fo_list_free : forall s, frees_only (ListTr.list_free_tr s).
Proof.
  intros s. unfold ListTr.list_free_tr. apply frees_only_app; [apply fo_recs_drop|].
  destruct (ListTr.sh_cap s =? 0); reflexivity.
Qed.
Lemma tc_lf : forall P s, ReplyCnt.tr_peakP P (ListTr.list_free_tr s) = 0.
Proof. intros P s. apply tr_peakP_frees, fo_list_free. Qed.
Lemma tc_hlf : forall P nm l, ReplyCnt.tr_peakP P (HarnessTr.hlist_free_tr nm l) = 0.
Proof. intros P nm l. unfold HarnessTr.hlist_free_tr. apply tc_lf. Qed.
Lemma tc_sr : forall P nm h, ReplyCnt.tr_peakP P (HarnessTr.source_reset_tr nm h) = 0.
Proof.
  intros P nm h. apply tr_peakP_frees. unfold HarnessTr.source_reset_tr, HarnessTr.hlist_free_tr.
  apply frees_only_app; [apply fo_list_free|]. apply frees_only_app; [apply fo_list_free|].
  apply frees_only_app; [apply fo_list_free | reflexivity].
Qed.
Lemma tc_ldrop : forall P a n, ReplyCnt.tr_peakP P (ListTr.list_drop_tra a n) = 0.
Proof. intros P a n. apply tr_peakP_frees. reflexivity. Qed.
Lemma tc_cshe : forall P nm gone P0 rs d, ReplyCnt.tr_peakP P (HarnessTr.check_shape_ends_tr nm gone P0 rs d) = 0.
Proof.
  intros P nm gone P0 rs d. apply tr_peakP_frees. unfold HarnessTr.check_shape_ends_tr.
  destruct (gone =? 0); [|apply fo_recs_drop].
  match goal with |- context [match ?m with Some _ => _ | None => _ end] => destruct m as [[[a ds] z]|] end;
    [apply fo_recs_drop | reflexivity].
Qed.

(* ------------------------------------------------------------------ the data-dependent peaks, as the audit states them *)
(* drain and check_no_loss: the constant is the trace's own peak plus 2 *)
Lemma tc_dr : forall P c mx no cap e h,
  ReplyCnt.tr_peakP P (dr_tr c mx no cap e h) <= ReplyCnt.tr_peakP P (dr_tr c mx no cap e h) + 2.
Proof. intros. lia. Qed.
Lemma tc_cnl : forall P j s rs,
  ReplyCnt.tr_peakP P (HarnessTr.check_no_loss_tr j s rs) <= ReplyCnt.tr_peakP P (HarnessTr.check_no_loss_tr j s rs) + 2.
Proof. intros. lia. Qed.

(* ================================================================== the counterexamples of the added hypotheses *)
(* tc_gse (bound 4) without the non-empty keys: keys of 6, 0, 17, 20, 0, 69, 125, 0, 278, 551 bytes from cap 0 (send
   live, no limit).  Each empty key requests nothing while ge_cap grows (12 -> 32, 66 -> 136, 274 -> 554), and the next
   key reallocs from that cap, which the trace never made: the blocks of 12, 66, 274, 1110 stay counted, and key 551's
   realloc 1110 -> 2222 counts 2222 before freeing 1110: count 5 *)
Lemma tc_gse_cex : forall b,
  ReplyCnt.tr_peakP (fun z => (z =? 12) || (z =? 66) || (z =? 274) || (z =? 1110) || (z =? 2222))
    (gse_tr (CTL 3 0 0 0 0) 0 0 0
      [repeat b 6; []; repeat b 17; repeat b 20; []; repeat b 69; repeat b 125; []; repeat b 278; repeat b 551]) = 5.
Proof. intros b. vm_compute. reflexivity. Qed.
(* tc_sl without 0 <= cap: cap -3, no -2, one-byte rounds: realloc -3 -> -2, realloc -2 -> 0, malloc 2 (the 0-byte
   block still counted), realloc 2 -> 6: count 3 *)
Lemma tc_sl_cex :
  ReplyCnt.tr_peakP (fun z => (z =? 0) || (z =? 2) || (z =? 6))
    (sl_tr (CTL 3 0 0 0 0) 1 (-2) (-3) 6) = 3.
Proof. vm_compute. reflexivity. Qed.

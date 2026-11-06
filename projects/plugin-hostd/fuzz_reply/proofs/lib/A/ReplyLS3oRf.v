(* LS_rf_room over LS v3's out half (lib/A/ReplyLS3o.v).  proves no function (kind: invariant lemma).

   The arm's text (W_LLVMFuzzerTestOneInput_exit.v:329-330) is
     LS_rf_room : LS cx t m ly S -> lx_rf_room MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m),
   and lx_rf_room (lib/A/W_LLVMFuzzerTestOneInput_exit.v:201) threads gestures_end's room gse_room (W_contract.v:1586), which is in PEAK form
   (tr_peak, C3; lib/A/ReplyTrPeakC.v).  This file proves LS_rf_room_p, that text at MMAX := WR_MMAX, from fr_LS3c
   and fr_OUT.

   WHY IT CLOSES.  relay_finish sends only the END line of each held key, |key| + 5 bytes, so the whole run sends
   at most rf_sum (lm_es m) = sum of keys_total over the table, which fr_OUT's MASS bounds by 65,535 * t, and a
   send grows g_capout to at most twice what it has sent (ReplyLS3o.ou_rf_cap).  Each send's PEAK is at most twice
   the capacity it leaves less the capacity it started from (realloc holds the old block while the new one is
   live): ou_sl_peak_cap, ou_ge_peak.  The threading `bb + gse_cap r - cap` is therefore an upper bound on the
   live bytes at the next entry (every other block relay_finish touches is freed), and the invariant
     ou_inv M Mx bb cap := (M <= cap /\ bb <= LIVE_MAX) \/ (cap <= Mx /\ bb + 2 * Mx - cap <= LIVE_MAX)
   telescopes through it.  Its left disjunct is the case of a g_out buffer already larger than everything the run
   can send: there send_line never grows (ou_sl_nogrow), the traces are empty and the peak is 0.  At the top,
   M := 2 * 65,535 * OPS_MAX = 67,107,840 (< WR_MMAX) and Mx := Z.max (lm_cap m) M, and fr_LS3's room
   (fr_LS3_room_x: blocks_bytes S + 4,160,659,073 <= LIVE_MAX) covers 2 * M = 134,215,680. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv SlotDrain3Aux SlotPass2Aux
  relay_remove_b_aux send_line_b_c send_line_c RelayRunT RelayRunF ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak ReplyTrPeakC.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.

(* ================================================================== a send that does not grow the buffer *)
(* Prog/send_line_b_c.v:33: a round grows g_out only when g_capout < g_nout + n, and g_nout + rem is kept, so a
   buffer that already holds the whole send asks nothing. *)
Lemma ou_sl_nogrow : forall f mx no cap rem j o, 0 <= rem -> no + rem <= cap ->
  send_line_b_c.sl_run f mx no cap rem j o = ([], (cap, o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hr Hc; [reflexivity|].
  cbn [send_line_b_c.sl_run]. destruct (Z.leb_spec rem 0); [reflexivity|].
  pose proof (ev3_n_le mx rem) as Hn.
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
  destruct (Z.ltb_spec cap (no + n)); [lia|].
  apply IH; lia.
Qed.
Lemma ou_sl_tr_nogrow : forall live mx no cap len j o, 0 <= len -> no + len <= cap ->
  send_line_b_c.send_line_tr live mx no cap len j o = [] /\
  send_line_b_c.send_line_cap live mx no cap len = cap.
Proof.
  intros live mx no cap len j o Hl Hc.
  unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap. destruct live; [|split; reflexivity].
  rewrite (ou_sl_nogrow (Z.to_nat len) mx no cap len j o Hl Hc),
          (ou_sl_nogrow (Z.to_nat len) mx no cap len 0 RelayRunF.adr0 Hl Hc).
  split; reflexivity.
Qed.
Lemma ou_ge_nogrow : forall c mx no cap XL, 0 <= no -> 0 <= XL -> no + XL + 5 <= cap ->
  ge_tr c mx no cap XL = [] /\ ge_cap c mx no cap XL = cap.
Proof.
  intros c mx no cap XL Hno HX Hc.
  assert (E1 : send_line_b_c.send_line_cap (sl_live c XL) mx no cap XL = cap)
    by exact (proj2 (ou_sl_tr_nogrow (sl_live c XL) mx no cap XL 0 RelayRunF.adr0 HX ltac:(lia))).
  assert (Hsn : sl_no c no XL <= no + XL) by (unfold sl_no; destruct (sl_live c XL); lia).
  split.
  - unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv zeta.
    rewrite (proj1 (ou_sl_tr_nogrow (sl_live c XL) mx no cap XL 0 RelayRunF.adr0 HX ltac:(lia))).
    cbn [app RelayRunF.nretF]. rewrite E1.
    apply (proj1 (ou_sl_tr_nogrow (sl_live c XL) mx (no + XL) cap 5 _ _ ltac:(lia) ltac:(lia))).
  - unfold ge_cap, sl_cap. rewrite E1.
    exact (proj2 (ou_sl_tr_nogrow (sl_live (sl_ctl c XL) 5) mx (sl_no c no XL) cap 5 0 RelayRunF.adr0
             ltac:(lia) ltac:(lia))).
Qed.
Lemma ou_gse_nogrow : forall xs c O mx no cap, 0 <= no -> 2 * (no + kw5s xs) <= cap ->
  gse_cap (gse_run c O mx no cap xs) = cap.
Proof.
  induction xs as [|x xs IH]; intros c O mx no cap Hno Hc; [reflexivity|].
  rewrite kw5s_cons in Hc. cbn [gse_run].
  set (XL := Z.of_nat (length x)) in *.
  assert (HX : 0 <= XL) by (unfold XL; lia).
  pose proof (kw5s_nonneg xs) as Hk.
  pose proof (ou_ge_no c no XL HX) as G3.
  destruct (ou_ge_nogrow c mx no cap XL Hno HX ltac:(lia)) as (_ & EC).
  rewrite IH; [exact EC | lia | rewrite EC; lia].
Qed.

(* ================================================================== the peak of one send and of gesture_end *)
Lemma ou_tr_net_pos : forall {P : Type} (tr : list (RelayRunT.rev P)), tr_net tr <= tr_pos tr.
Proof.
  intros P tr. induction tr as [|ev tr IH]; [cbn; lia|].
  rewrite tr_net_cons, tr_pos_cons. destruct ev; lia.
Qed.
(* a send's peak, against the capacity it leaves: a realloc holds the old block while the new one is live *)
Lemma ou_sl_peak_cap : forall live mx no cap len j o, 0 <= cap ->
  tr_peak (send_line_b_c.send_line_tr live mx no cap len j o) + cap <=
  2 * send_line_b_c.send_line_cap live mx no cap len.
Proof.
  intros live mx no cap len j o Hc.
  unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap. destruct live.
  - pose proof (tp_sl_peak_cap_run (Z.to_nat len) mx no cap len j o Hc) as H.
    rewrite sl_run_fin in H. rewrite sl_run_fin. exact H.
  - rewrite tr_peak_nil. lia.
Qed.
(* gesture_end's two sends, as one statement over their trace *)
Lemma ou_two_sends_peak : forall live mx no cap len1 len2 j1 o1 j2 o2, 0 <= cap ->
  tr_peak (send_line_b_c.send_line_tr live mx no cap len1 j1 o1 ++
           send_line_b_c.send_line_tr live mx (no + len1)
             (send_line_b_c.send_line_cap live mx no cap len1) len2 j2 o2) + cap <=
  2 * send_line_b_c.send_line_cap live mx (no + len1)
        (send_line_b_c.send_line_cap live mx no cap len1) len2.
Proof.
  intros live mx no cap len1 len2 j1 o1 j2 o2 Hc.
  pose proof (ou_sl_peak_cap live mx no cap len1 j1 o1 Hc) as P1.
  pose proof (proj1 (tp_send_line live mx no cap len1 j1 o1 Hc)) as N1.
  pose proof (proj2 (tp_send_line live mx no cap len1 j1 o1 Hc)) as G1.
  pose proof (ou_tr_net_pos (send_line_b_c.send_line_tr live mx no cap len1 j1 o1)) as N2.
  pose proof (ou_sl_peak_cap live mx (no + len1) (send_line_b_c.send_line_cap live mx no cap len1) len2 j2 o2
                ltac:(lia)) as P2.
  pose proof (proj2 (tp_send_line live mx (no + len1) (send_line_b_c.send_line_cap live mx no cap len1) len2
                       j2 o2 ltac:(lia))) as G2.
  rewrite tr_peak_app. lia.
Qed.
Lemma ou_two_sends_net : forall live mx no cap len1 len2 j1 o1 j2 o2, 0 <= cap ->
  tr_net (send_line_b_c.send_line_tr live mx no cap len1 j1 o1 ++
          send_line_b_c.send_line_tr live mx (no + len1)
            (send_line_b_c.send_line_cap live mx no cap len1) len2 j2 o2) <=
  send_line_b_c.send_line_cap live mx (no + len1)
    (send_line_b_c.send_line_cap live mx no cap len1) len2 - cap.
Proof.
  intros live mx no cap len1 len2 j1 o1 j2 o2 Hc.
  pose proof (proj1 (tp_send_line live mx no cap len1 j1 o1 Hc)) as N1.
  pose proof (proj2 (tp_send_line live mx no cap len1 j1 o1 Hc)) as G1.
  pose proof (ou_tr_net_pos (send_line_b_c.send_line_tr live mx no cap len1 j1 o1)) as M1.
  pose proof (proj1 (tp_send_line live mx (no + len1) (send_line_b_c.send_line_cap live mx no cap len1) len2
                       j2 o2 ltac:(lia))) as N2.
  pose proof (ou_tr_net_pos (send_line_b_c.send_line_tr live mx (no + len1)
                 (send_line_b_c.send_line_cap live mx no cap len1) len2 j2 o2)) as M2.
  rewrite tr_net_app. lia.
Qed.
(* the second send of gesture_end leaves at most what ge_cap records: for XL > 0 the two agree, and for XL = 0 the
   first send is off, the second's trace is empty and ge_cap only grows *)
Lemma ou_sl_live_ge : forall c XL, sl_live c XL = true -> sl_live (sl_ctl c XL) 5 = true.
Proof.
  intros c XL H.
  unfold sl_live, send_line_c.send_live in H. apply andb_true_iff in H as (H1 & H2).
  apply negb_true_iff in H1. apply Z.eqb_eq in H2.
  unfold send_line_c.send_off in H1.
  apply orb_false_iff in H1 as (H12 & H3). apply orb_false_iff in H12 as (Hcl & Hbr).
  unfold sl_live, sl_ctl, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  rewrite Hcl, Hbr, H3, H2. reflexivity.
Qed.
Lemma ou_ge_tr_cap : forall c mx no cap XL, 0 <= cap ->
  send_line_b_c.send_line_cap (sl_live c XL) mx (no + XL)
    (send_line_b_c.send_line_cap (sl_live c XL) mx no cap XL) 5 <= ge_cap c mx no cap XL.
Proof.
  intros c mx no cap XL Hc.
  pose proof (proj2 (tp_send_line (sl_live c XL) mx no cap XL 0 RelayRunF.adr0 Hc)) as Hc1.
  unfold ge_cap, sl_cap.
  destruct (sl_live c XL) eqn:EL.
  - rewrite (ou_sl_live_ge c XL EL). unfold sl_no. rewrite EL. lia.
  - cbn [send_line_b_c.send_line_cap] in Hc1 |- *.
    exact (proj2 (tp_send_line (sl_live (sl_ctl c XL) 5) mx (sl_no c no XL) cap 5 0 RelayRunF.adr0 Hc)).
Qed.
Lemma ou_ge_peak : forall c mx no cap XL, 0 <= cap ->
  tr_peak (ge_tr c mx no cap XL) + cap <= 2 * ge_cap c mx no cap XL.
Proof.
  intros c mx no cap XL Hc.
  pose proof (ou_ge_tr_cap c mx no cap XL Hc) as HG.
  unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv zeta.
  pose proof (ou_two_sends_peak (sl_live c XL) mx no cap XL 5 0 RelayRunF.adr0
    (0 + RelayRunF.nretF (send_line_b_c.send_line_tr (sl_live c XL) mx no cap XL 0 RelayRunF.adr0))
    (send_line_b_c.send_line_out (sl_live c XL) mx no cap XL 0 RelayRunF.adr0) Hc) as H. lia.
Qed.
Lemma ou_ge_net : forall c mx no cap XL, 0 <= cap ->
  tr_net (ge_tr c mx no cap XL) <= ge_cap c mx no cap XL - cap.
Proof.
  intros c mx no cap XL Hc.
  pose proof (ou_ge_tr_cap c mx no cap XL Hc) as HG.
  unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv zeta.
  pose proof (ou_two_sends_net (sl_live c XL) mx no cap XL 5 0 RelayRunF.adr0
    (0 + RelayRunF.nretF (send_line_b_c.send_line_tr (sl_live c XL) mx no cap XL 0 RelayRunF.adr0))
    (send_line_b_c.send_line_out (sl_live c XL) mx no cap XL 0 RelayRunF.adr0) Hc) as H. lia.
Qed.
(* every request of gesture_end is at most twice what it has sent (ReplyLSDrainPre.v dpre_send_line) *)
Lemma ou_ge_max : forall c mx no cap XL M, 0 <= no -> 0 <= XL -> 2 * (no + XL + 5) <= M ->
  tr_max (ge_tr c mx no cap XL) <= M.
Proof.
  intros c mx no cap XL M Hno HX HM.
  assert (M0 : 0 <= M) by lia.
  unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv zeta. rewrite tr_max_app'.
  apply Z.max_lub.
  - apply (dpre_tr_max _ M M0). apply dpre_send_line. lia.
  - apply (dpre_tr_max _ M M0). apply dpre_send_line. lia.
Qed.

(* the induction's invariant: either the buffer already holds everything the run can send (no growth at all), or
   the live bytes plus twice the largest capacity the run can reach are within LIVE_MAX *)
Definition ou_inv (M Mx bb cap : Z) : Prop :=
  (M <= cap /\ bb <= LIVE_MAX) \/ (cap <= Mx /\ bb + 2 * Mx - cap <= LIVE_MAX).

Lemma ou_gse_room_p : forall xs MX M Mx c mx no cap bb,
  0 <= cap -> 0 <= no -> 0 <= M -> M <= Mx -> M < MX ->
  2 * (no + kw5s xs) <= M -> ou_inv M Mx bb cap ->
  gse_room MX bb c mx no cap xs.
Proof.
  induction xs as [|x xs IH]; intros MX M Mx c mx no cap bb Hc Hno HM0 HMx HMX HS HI; [exact I|].
  rewrite kw5s_cons in HS.
  set (XL := Z.of_nat (length x)) in *.
  assert (HX : 0 <= XL) by (unfold XL; lia).
  pose proof (kw5s_nonneg xs) as Hk.
  pose proof (ou_ge_cap_ge c mx no cap XL Hc) as G1.
  pose proof (ou_ge_cap_le c mx no cap XL Hc HX) as G2.
  pose proof (ou_ge_no c no XL HX) as G3.
  cbn [gse_room]. fold XL. split.
  - unfold ge_room. split.
    + pose proof (ou_ge_max c mx no cap XL M Hno HX ltac:(lia)). lia.
    + destruct HI as [(HA1 & HA2) | (HB1 & HB2)].
      * destruct (ou_ge_nogrow c mx no cap XL Hno HX ltac:(lia)) as (ET & _).
        rewrite ET, tr_peak_nil. lia.
      * pose proof (ou_ge_peak c mx no cap XL Hc). lia.
  - apply (IH MX M Mx (ge_ctl c XL) mx (ge_no c no XL) (ge_cap c mx no cap XL)); try lia.
    destruct HI as [(HA1 & HA2) | (HB1 & HB2)].
    + destruct (ou_ge_nogrow c mx no cap XL Hno HX ltac:(lia)) as (ET & EC).
      left. rewrite EC. split; [lia|]. rewrite ET. cbn [tr_net fold_right]. lia.
    + right. pose proof (ou_ge_net c mx no cap XL Hc). lia.
Qed.

Lemma ou_lx_rf_room_p : forall es MX M Mx c O mx no cap bb,
  0 <= cap -> 0 <= no -> 0 <= M -> M <= Mx -> M < MX ->
  2 * (no + rf_sum es) <= M -> ou_inv M Mx bb cap ->
  lx_rf_room MX bb c O mx no cap es.
Proof.
  induction es as [|e es IH]; intros MX M Mx c O mx no cap bb Hc Hno HM0 HMx HMX HS HI; [exact I|].
  rewrite rf_sum_cons in HS.
  pose proof (rf_sum_nonneg es) as Hr.
  pose proof (kw5s_nonneg (gse_keys e)) as Hk.
  destruct (ou_gse_cap (gse_keys e) c O mx no cap Hc) as (C1 & C2 & C3).
  cbn [lx_rf_room]. cbv zeta. split.
  - apply (ou_gse_room_p (gse_keys e) MX M Mx c mx no cap bb); try lia. exact HI.
  - apply (IH MX M Mx (gse_c (gse_run c O mx no cap (gse_keys e))) (gse_O (gse_run c O mx no cap (gse_keys e)))
             mx (gse_no (gse_run c O mx no cap (gse_keys e))) (gse_cap (gse_run c O mx no cap (gse_keys e))));
      try lia.
    destruct HI as [(HA1 & HA2) | (HB1 & HB2)].
    + left. rewrite (ou_gse_nogrow (gse_keys e) c O mx no cap Hno ltac:(lia)). lia.
    + right. lia.
Qed.

(* ================================================================== LS_rf_room at LS := fr_LS3c /\ fr_OUT *)
Section orf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable OM : Z.
(* the arm's LS_rf_room (W_LLVMFuzzerTestOneInput_exit.v:329-330) over relay_finish's run.  The premise
   `0 <= t <= OPS_MAX` is the loop's (lregs_H, _cut.v:549; SEG_LATCH passes t + 1), as in LS_exit_end3. *)
Lemma LS_rf_room_p : forall cx t m ly S,
  fr_LS3c B cx t m ly S -> fr_OUT OM cx t m ly S -> 0 <= t <= OPS_MAX ->
  lx_rf_room MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
Proof.
  intros cx t m ly S (HLS & _) (U1 & U2 & U3 & U4) Ht.
  pose proof (fr_LS3_room_x B cx t m ly S HLS) as Hroom.
  assert (HWM : WR_MMAX = 1072693248) by (vm_compute; reflexivity).
  assert (HLM : LIVE_MAX = 17179869184) by (vm_compute; reflexivity).
  pose proof (rf_sum_mass (lm_es m)) as Hrf.
  assert (Hmass : MASSe (lm_es m) <= MASS m).
  { unfold MASS. assert (0 <= pend_bytes m) by (apply zsum_map_nonneg; exact slot_pend_nonneg). lia. }
  apply (ou_lx_rf_room_p (lm_es m) MMAX (2 * (WMAX * OPS_MAX)) (Z.max (lm_cap m) (2 * (WMAX * OPS_MAX)))
          (lm_c m) [] (lm_mx m) 0 (lm_cap m) (blocks_bytes S));
    unfold WMAX, OPS_MAX in *; try lia.
  unfold ou_inv. destruct (Z_le_gt_dec (2 * (65535 * 512)) (lm_cap m)); [left | right]; lia.
Qed.
End orf.

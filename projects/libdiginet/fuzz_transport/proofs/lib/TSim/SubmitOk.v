(* fuzz_transport.c:1068-1122 op_submit (FT), TOps.v op_submit_m, case 4 of the loop (FT:1190-1192). From agree at
   the loop head the operation is Some (no abort, no UBSan trap) and agree holds again with one operation more:
   op_begin (FT:1074) writes OW, GOT and M.fail (R_ob); the rest of the operation writes the tail of g_s from
   s->queue on, g_cmd, g_q, g_nq and g_ncmd (R4q). submit_tagged_pre (SubmitTag.v, g_raw = 0) and submit_raw_pre
   (SubmitRaw.v) give agree_q after the operation and the operation up to settle(0) (FT:1083, :1121); agree's other
   clauses read nothing op 4 writes (SimLib.v agree_core_frame, R4_rs core_free), and settle(0) passes because
   op 4 neither predicts nor notices anything (OW and GOT as op_begin left them: SettleOk.v settle_ok). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import
  Agree Links SimLib QueueFacts SettleOk SubmitLib SubmitTag SubmitRaw.
Import ListNotations.
Open Scope Z_scope.

(* R4 as a range list of SimLib.v *)
Definition R4_rs : list (Z * Z) :=
  [(OFF_OW, SZ_OW); (OFF_GOT, SZ_GOT); (A_M_fail, 4); (OFF_g_s + 1760, SZ_g_s - 1760);
   (OFF_g_cmd, OFF_g_q + SZ_g_q - OFF_g_cmd); (OFF_g_nq, OFF_g_ncmd + 4 - OFF_g_nq)].

Lemma wsame_R4 : forall B B', wframe R4 B B' -> wsame B B' R4_rs.
Proof.
  intros B B' H. unfold wsame. apply (wframe_weaken R4 (in_ranges R4_rs) B B'); [|exact H].
  intros a Ha. unfold R4_rs. rewrite !in_ranges_cons, in_ranges_nil. revert Ha. woffs.
Qed.

(* R4 misses agree_core's footprint *)
Lemma R4_core_free : core_free R4_rs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem op_submit_ok : forall I ops B D c, links -> agree I ops B -> ops < OPS_MAX -> fuzz_in_ok D c ->
  exists B' c', op_submit_m B D c = Some (B', c') /\ agree I (ops + 1) B' /\ fuzz_in_ok D c'.
Proof.
  intros I ops B D c HL HA Hops Hc.
  assert (Hpre : exists B1 B7 c5, op_begin_m B = Some (B1, tt) /\ wframe R4q B1 B7 /\ agree_q (ops + 1) B7 /\
    fuzz_in_ok D c5 /\ op_submit_m B D c = match settle_m B7 0 with Some (B8, _) => Some (B8, c5) | None => None end).
  { destruct (Z.eq_dec (g_raw B) 0) as [Hr|Hr].
    - exact (submit_tagged_pre I ops B D c HL HA Hops Hr Hc).
    - exact (submit_raw_pre I ops B D c HL HA Hops Hr Hc). }
  destruct Hpre as (B1 & B7 & c5 & Hob & Hf & Hq & Hc5 & Eop).
  pose proof (ac_len _ _ _ (ag_core _ _ _ HA)) as HB.
  destruct (op_begin_stage B HB) as (B1' & Hob' & Hf1 & Hz1 & _).
  rewrite Hob in Hob'. injection Hob' as E1. subst B1'.
  pose proof (wsame_R4 B B7 (wframe_R4 B B1 B7 Hf1 Hf)) as HW.
  destruct HA as [Hcore Hka Hrx].
  assert (Ho : ops <= ops + 1 <= OPS_MAX) by lia.
  pose proof (foot_corem_core R4_rs (rdisj_spec R4_rs foot_core R4_core_free)) as Hd.
  pose proof (agree_core_frame I ops (ops + 1) B B7 R4_rs Hcore Ho HW R4_core_free Hq) as Hcore7.
  pose proof (c2_keepalive_frame B B7 R4_rs HW Hd Hka) as Hka7.
  pose proof (g_rx_frame B B7 R4_rs HW Hd Hrx) as Hrx7.
  destruct (ow_got_zero_frame B1 B7 Hf Hz1) as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 &
                                                 g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8).
  pose proof (settle_eq_zero B7 o1 g1 o2 g2 o3 g3 o4 g4 o5 g5 o6 g6 o7 g7 o8 g8) as Hse.
  assert (Hs : settle_m B7 0 = Some (B7, tt)).
  { apply (settle_ok I (ops + 1) B7 0 Hcore7 Hka7 Hse). intros H. cbn in H. discriminate H. }
  rewrite Hs in Eop. exists B7, c5. split; [exact Eop|]. split; [|exact Hc5].
  constructor; [exact Hcore7 | exact Hka7 | exact Hrx7].
Qed.

(* SrxBInv: the model piece of the image-B walk of diginet_session_rx (SrxBCut.v srxb_inv_stmt): the run invariants
   srxb_inv (the statement's (1), (2), (4), (5) and the bounds g_ncmd <= CMDS_MAX, S_queued <= QUEUE_MAX) hold at
   the world after the desk is learnt (srx_learn, :290-291), after the counters of :296-297 (srx_w1), and at the
   world the switch of :298-316 leaves (srx_sw at timg_B). No machine.
   srxb_inv is lib/TModel/TRunInv.v run_inv (the same seven conjuncts over the same names), and TRunInv's relation
   rk B0 B (B has B0's length, and run_inv B0 gives run_inv B; rk_out) is kept by every store that misses the bytes
   run_inv reads (rk_upd, by rk_go) and by each callee of the switch at any timg (on_announce_rk, on_ack_rk,
   on_data_rk, session_lost_rk: srx_sw states the disconnect arm through session_lost_m; the code inlines it, which
   SrxBCut.v srxb_sw_lost relates). The stores here: desk_mac (g_s + 120, at most 6 bytes) and desk_known
   (g_s + 116) for srx_learn; stats.rx_frames (g_s + 18152) and last_rx_us (g_s + 176) for srx_w1;
   stats.rx_ignored (g_s + 18184) for the ignored arm of the switch. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_session_rx_cg SrxBCut.
Import ListNotations.
Open Scope Z_scope.
Module RXB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_rx_cg.

(* the world after the desk is learnt (:290-291): two stores into g_s *)
Lemma srxbi_learn_rk : forall B b, length B = Z.to_nat W_LEN -> rk B (RXB.srx_learn B b).
Proof. intros B b HL. unfold RXB.srx_learn. ri_set. rk_go. Qed.

(* the world after the counters of :296-297: two stores into g_s *)
Lemma srxbi_w1_rk : forall B now, length B = Z.to_nat W_LEN -> rk B (RXB.srx_w1 B now).
Proof. intros B now HL. unfold RXB.srx_w1. ri_set. rk_go. Qed.

(* the switch of :298-316: a callee, or the store of stats.rx_ignored, or nothing *)
Lemma srxbi_sw_rk : forall I F B b now B2 u, length B = Z.to_nat W_LEN ->
  RXB.srx_sw I F B b now = Some (B2, u) -> rk B B2.
Proof.
  intros I F B b now B2 u HL H. unfold RXB.srx_sw, RXB.srx_ign in H.
  repeat match type of H with
  | (if ?c then _ else _) = _ => destruct c; cbv beta iota in H
  end.
  all: lazymatch type of H with
  | on_announce_m _ _ _ _ _ = _ => eapply (on_announce_rk B HL); [apply rk_refl | exact H]
  | on_ack_m _ _ _ _ = _ => eapply (on_ack_rk B HL); [apply rk_refl | exact H]
  | on_data_m _ _ _ _ _ = _ => eapply (on_data_rk B HL); [apply rk_refl | exact H]
  | session_lost_m _ _ _ _ = _ => eapply (session_lost_rk B HL); [apply rk_refl | exact H]
  | Some _ = Some _ => injection H as <- _; ri_set; rk_go
  end.
Qed.

Theorem srxb_inv_ok : SrxBCut.srxb_inv_stmt.
Proof.
  split; [|split].
  - intros Bx b HL HI. exact (proj2 (rk_out Bx (RXB.srx_learn Bx b) HL HI (srxbi_learn_rk Bx b HL))).
  - intros Bx now HL HI. exact (proj2 (rk_out Bx (RXB.srx_w1 Bx now) HL HI (srxbi_w1_rk Bx now HL))).
  - intros TF Bx b now B2 HL HI HS.
    exact (proj2 (rk_out Bx B2 HL HI (srxbi_sw_rk _ TF Bx b now B2 tt HL HS))).
Qed.

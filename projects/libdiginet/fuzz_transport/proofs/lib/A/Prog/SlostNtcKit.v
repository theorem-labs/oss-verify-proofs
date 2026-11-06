(* SlostNtcKit: the facts about session_lost that the notice piece of its walk (lib/A/Prog/SlostNtc.v) uses beyond the
   kits TransportGFrame.v and TransportGNotice.v (which holds this file's generic lemmas):
   - the model: sn_model (on the notice path, call_notify's test holds and notice_m gives Bw'), the worlds' lengths,
     g_s.notify and g_fail_next across the three g_s stores, slost_w2 at its numeral offset;
   - the written range: sn_wr_G, the bytes of slost_wr (g_s's three fields, and notice's stores: TransportGNotice.v
     notice_wr_G) are bytes of G. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg CanKit TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* On the notice path (the state the code loaded is not S_IDLE), call_notify's test holds and notice gives Bw'. *)
Lemma sn_model : forall (TF : option TI.tframe) Bw why Bw',
  TSS.session_lost_m timg_A TF Bw why = Some (Bw', tt) ->
  TW.S_state (slost_w1 Bw) <> TS0.DIGINET_S_IDLE ->
  TW.S_notify (slost_w2 Bw) = TI.ti_notice timg_A /\
  TC.notice_m timg_A TF (slost_w2 Bw) (slost_ntc Bw why) = Some (Bw', tt).
Proof.
  intros TF Bw why Bw' Hm Hne. rewrite slost_model in Hm.
  rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hm. unfold TSS.call_notify in Hm.
  destruct (Z.eqb_spec (TW.S_notify (slost_w2 Bw)) (TI.ti_notice timg_A)) as [E|E]; [|discriminate Hm].
  split; [exact E | exact Hm].
Qed.

Lemma sn_len1 : forall Bw, length Bw = Z.to_nat TW.W_LEN -> length (slost_w1 Bw) = Z.to_nat TW.W_LEN.
Proof. intros Bw L. unfold slost_w1, TW.set_S_desk_counter_valid, TW.set_S_inflight. wlen. Qed.

Lemma sn_len2 : forall Bw, length Bw = Z.to_nat TW.W_LEN -> length (slost_w2 Bw) = Z.to_nat TW.W_LEN.
Proof.
  intros Bw L. pose proof (sn_len1 Bw L) as L1. unfold slost_w2, TW.set_S_state. wlen.
Qed.

(* slost_w2 at the numeral offset of g_s.state (s + 112). *)
Lemma sn_w2_eq : forall Bw, slost_w2 Bw = TW.upd (slost_w1 Bw) (TW.OFF_g_s + 112) (TW.put 4 0).
Proof. intros Bw. reflexivity. Qed.

(* g_s.notify is not one of the three fields the call stores. *)
Lemma sn_notify : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  TW.S_notify (slost_w2 Bw) = TW.u_at (slost_w1 Bw) (TW.OFF_g_s + 96) 8.
Proof.
  intros Bw L. pose proof (sn_len1 Bw L) as L1. rewrite sn_w2_eq. unfold TW.S_notify, TW.A_S_notify.
  rewrite rd_upd_W by wside. reflexivity.
Qed.

(* g_fail_next is not one of them either, nor of notice's (an N_STATE notice writes GOT only). *)
Lemma sn_gfn : forall Bw, length Bw = Z.to_nat TW.W_LEN -> TW.g_fail_next (slost_w2 Bw) = TW.g_fail_next Bw.
Proof.
  intros Bw L. unfold TW.g_fail_next, slost_w2, slost_w1, TW.set_S_state, TW.set_S_desk_counter_valid,
    TW.set_S_inflight.
  rewrite !rd_upd_W by wside. reflexivity.
Qed.

Lemma sn_gfn' : forall (TF : option TI.tframe) Bw why Bw', length Bw = Z.to_nat TW.W_LEN ->
  TC.notice_m timg_A TF (slost_w2 Bw) (slost_ntc Bw why) = Some (Bw', tt) ->
  TW.g_fail_next Bw' = TW.g_fail_next Bw.
Proof.
  intros TF Bw why Bw' L H.
  rewrite (notice_state_acked_fail_next timg_A TF (slost_w2 Bw) (slost_ntc Bw why) Bw' (or_introl eq_refl)
    (sn_len2 Bw L) H).
  exact (sn_gfn Bw L).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The written range                                                *)
(* ------------------------------------------------------------------ *)

(* The bytes of slost_wr are bytes of G. *)
Lemma sn_wr_G : forall Bw why a, slost_wr Bw why a -> inG TG.G_HARNESS a.
Proof.
  intros Bw why a H.
  assert (HG : forall b n, In (b, n) TG.G_HARNESS -> b <= a < b + n -> inG TG.G_HARNESS a)
    by (intros b n Hin Hr; unfold inG; apply Exists_exists; exists (b, n);
        split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (TMAP_A_in_G _ _ _ TMAP_A_g_s) as Gs.
  unfold slost_wr in H.
  destruct H as [H | [H | (_ & [H | H])]].
  - apply (HG _ _ Gs). unfold twa_fld, TW.A_S_inflight, TW.OFF_g_s, TW.SZ_g_s in *. lia.
  - apply (HG _ _ Gs). unfold twa_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.SZ_g_s in *. lia.
  - apply (HG _ _ Gs). unfold twa_fld, TW.A_S_state, TW.OFF_g_s, TW.SZ_g_s in *. lia.
  - exact (notice_wr_G _ _ a H).
Qed.

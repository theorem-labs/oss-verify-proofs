(* diginet_session_close_seg_kit: the lemmas the pieces of diginet_session_close's walk share beyond the kit:
   - the model (lib/TModel/TSess.v diginet_session_close_m through diginet_session_close_cg.v close_model and
     close_setstate), each read off the model premise without an inversion of a world-carrying option: close_r_eq (the
     a0 the send gave is the result r), close_sent_nogo, close_send_some (when close_go Bw holds, send_control_m gives
     the send's world and r), close_rel_model (S_CLOSED: Bw' = close_w1 B1), close_ntc_model (else call_notify's test
     holds and notice_m gives Bw');
   - the worlds: close_w1 and close_w2 at their numeral offsets, their lengths, g_fail_next and g_s.notify across the
     stores of :155 and :84;
   - the written range: every byte of close_wr is a byte of G (close_wr_G; send_control's sendctl_wr 0 0 through
     io_send's iosend_wr field by field, notice's N_STATE stores in GOT), so it lies in G's hull, below the shadow. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* The constants the code holds as literals. *)
Lemma close_consts : TS0.DIGINET_CMD_DISCONNECT = 227 /\ TS0.DIGINET_S_CLOSED = 3 /\ TS0.DIGINET_R_CLOSED = 8 /\
  TS0.DIGINET_N_STATE = 2.
Proof. repeat split; reflexivity. Qed.

(* The result of the call is the r of the send. *)
Lemma close_r_eq : forall I F Bw now Bw' B1 r1 r,
  TSS.diginet_session_close_m I F Bw now = Some (Bw', r) -> close_sent I F Bw = Some (B1, r1) -> r1 = r.
Proof.
  intros I F Bw now Bw' B1 r1 r Hm Hs. rewrite close_model, Hs in Hm. cbv beta iota in Hm.
  destruct (TSS.set_state_m I F (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED) as [[B2 u]|];
    [|discriminate Hm].
  exact (f_equal (fun o : option (list byte * Z) => match o with Some (_, x) => x | None => r1 end) Hm).
Qed.

(* close_go Bw false: no send, the world Bw and r = 0. *)
Lemma close_sent_nogo : forall I F Bw, close_go Bw = false -> close_sent I F Bw = Some (Bw, 0).
Proof. intros I F Bw H. unfold close_sent. rewrite H. reflexivity. Qed.

(* close_go Bw true: send_control_m gives the send's world B1 and the result r. *)
Lemma close_send_some : forall I F Bw now Bw' r,
  TSS.diginet_session_close_m I F Bw now = Some (Bw', r) -> close_go Bw = true ->
  exists B1 f, TSS.send_control_m I F Bw TS0.DIGINET_CMD_DISCONNECT 0 = Some (B1, (r, f)) /\
    close_sent I F Bw = Some (B1, r).
Proof.
  intros I F Bw now Bw' r Hm Hgo.
  assert (ES : close_sent I F Bw =
    match TSS.send_control_m I F Bw TS0.DIGINET_CMD_DISCONNECT 0 with
    | None => None
    | Some (B1, (r, _)) => Some (B1, r)
    end) by (unfold close_sent; rewrite Hgo; reflexivity).
  destruct (TSS.send_control_m I F Bw TS0.DIGINET_CMD_DISCONNECT 0) as [[B1 [r1 f]]|] eqn:EC.
  - pose proof (close_r_eq I F Bw now Bw' B1 r1 r Hm ES) as Er. subst r1.
    exists B1, f. split; [reflexivity | exact ES].
  - rewrite close_model, ES in Hm. discriminate Hm.
Qed.

(* S_CLOSED after the store of :155: no notice, the model's world is close_w1 B1. *)
Lemma close_rel_model : forall I F Bw now Bw' B1 r1 r,
  TSS.diginet_session_close_m I F Bw now = Some (Bw', r) -> close_sent I F Bw = Some (B1, r1) ->
  TW.S_state (close_w1 B1) = TS0.DIGINET_S_CLOSED -> Bw' = close_w1 B1.
Proof.
  intros I F Bw now Bw' B1 r1 r Hm Hs Hc. rewrite close_model, Hs in Hm. cbv beta iota in Hm.
  rewrite close_setstate, (proj2 (Z.eqb_eq _ _) Hc) in Hm. cbv beta iota in Hm.
  symmetry. exact (f_equal (fun o : option (list byte * Z) => match o with Some (b, _) => b | None => Bw' end) Hm).
Qed.

(* Any other state: call_notify's test holds and notice_m gives Bw'. *)
Lemma close_ntc_model : forall I F Bw now Bw' B1 r1 r,
  TSS.diginet_session_close_m I F Bw now = Some (Bw', r) -> close_sent I F Bw = Some (B1, r1) ->
  TW.S_state (close_w1 B1) <> TS0.DIGINET_S_CLOSED ->
  TW.S_notify (close_w2 B1) = TI.ti_notice I /\ TC.notice_m I F (close_w2 B1) (close_ntc B1) = Some (Bw', tt).
Proof.
  intros I F Bw now Bw' B1 r1 r Hm Hs Hne. rewrite close_model, Hs in Hm. cbv beta iota in Hm.
  rewrite close_setstate, (proj2 (Z.eqb_neq _ _) Hne) in Hm. cbv beta iota in Hm. unfold TSS.call_notify in Hm.
  destruct (Z.eqb_spec (TW.S_notify (close_w2 B1)) (TI.ti_notice I)) as [E|E]; [|discriminate Hm].
  split; [exact E|].
  destruct (TC.notice_m I F (close_w2 B1) (close_ntc B1)) as [[B2 u]|]; [|discriminate Hm].
  destruct u. f_equal. f_equal.
  exact (f_equal (fun o : option (list byte * Z) => match o with Some (b, _) => b | None => B2 end) Hm).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The worlds                                                       *)
(* ------------------------------------------------------------------ *)

(* close_w1 and close_w2 at the numeral offsets of g_s.inflight (s + 212) and g_s.state (s + 112). *)
Lemma close_w1_eq : forall B1, close_w1 B1 = TW.upd B1 (TW.OFF_g_s + 212) (TW.put 4 0).
Proof. intros B1. reflexivity. Qed.
Lemma close_w2_eq : forall B1, close_w2 B1 = TW.upd (close_w1 B1) (TW.OFF_g_s + 112) (TW.put 4 3).
Proof. intros B1. reflexivity. Qed.

Lemma close_len1 : forall B1, length B1 = Z.to_nat TW.W_LEN -> length (close_w1 B1) = Z.to_nat TW.W_LEN.
Proof. intros B1 L. unfold close_w1, TW.set_S_inflight. wlen. Qed.

Lemma close_len2 : forall B1, length B1 = Z.to_nat TW.W_LEN -> length (close_w2 B1) = Z.to_nat TW.W_LEN.
Proof. intros B1 L. pose proof (close_len1 B1 L) as L1. unfold close_w2, TW.set_S_state. wlen. Qed.

(* g_fail_next is neither g_s.inflight nor g_s.state. *)
Lemma close_gfn1 : forall B1, length B1 = Z.to_nat TW.W_LEN -> TW.g_fail_next (close_w1 B1) = TW.g_fail_next B1.
Proof.
  intros B1 L. unfold TW.g_fail_next, close_w1, TW.set_S_inflight. rewrite !rd_upd_W by wside. reflexivity.
Qed.
Lemma close_gfn2 : forall B1, length B1 = Z.to_nat TW.W_LEN -> TW.g_fail_next (close_w2 B1) = TW.g_fail_next B1.
Proof.
  intros B1 L. unfold TW.g_fail_next, close_w2, close_w1, TW.set_S_state, TW.set_S_inflight.
  rewrite !rd_upd_W by wside. reflexivity.
Qed.

(* An N_STATE notice keeps g_fail_next (TNotifyFacts.v notice_state_acked_fail_next). *)
Lemma close_gfn' : forall (TF : option TI.tframe) B1 Bw', length B1 = Z.to_nat TW.W_LEN ->
  TC.notice_m timg_A TF (close_w2 B1) (close_ntc B1) = Some (Bw', tt) ->
  TW.g_fail_next Bw' = TW.g_fail_next B1.
Proof.
  intros TF B1 Bw' L H.
  rewrite (notice_state_acked_fail_next timg_A TF (close_w2 B1) (close_ntc B1) Bw' (or_introl eq_refl)
    (close_len2 B1 L) H).
  exact (close_gfn2 B1 L).
Qed.

(* g_s.notify (s + 96) is not one of the two fields the call stores. *)
Lemma close_notify : forall B1, length B1 = Z.to_nat TW.W_LEN ->
  TW.S_notify (close_w2 B1) = TW.u_at (close_w1 B1) (TW.OFF_g_s + 96) 8.
Proof.
  intros B1 L. pose proof (close_len1 B1 L) as L1. rewrite close_w2_eq. unfold TW.S_notify, TW.A_S_notify.
  rewrite rd_upd_W by wside. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The written range                                                *)
(* ------------------------------------------------------------------ *)

(* A byte inside a row of G is a byte of G. *)
Lemma close_inG_row : forall b n a, In (b, n) TG.G_HARNESS -> b <= a < b + n -> inG TG.G_HARNESS a.
Proof.
  intros b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn; lia].
Qed.

(* A byte of a field of the TMAP_A row (o, b, n), inside the row. *)
Lemma close_fld_G : forall o b n A w a, In (o, b, n) TMAP_A -> twa_fld o b A w a -> o <= A -> A + w <= o + n ->
  inG TG.G_HARNESS a.
Proof.
  intros o b n A w a Hin Ha H1 H2. apply (close_inG_row b n a (TMAP_A_in_G o b n Hin)).
  unfold twa_fld in Ha. lia.
Qed.

(* The side conditions of close_fld_G: closed ones by computation (close_cz), the ones with a variable index by lia
   over the unfolded offsets (close_czl). *)
Ltac close_cz := apply Z.leb_le; vm_compute; reflexivity.
Ltac close_czl :=
  unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd, TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT, TW.SZ_GOT,
    TC.CMDS_MAX, TC.TRANS_MAX in *; lia.

(* io_send's stores (iosend_wr n), field by field, for any n. *)
Lemma close_iosend_wr_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS a.
Proof.
  intros n a H. unfold iosend_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]].
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_g_fail_next H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_GOT H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_GOT H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_GOT H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_g_last_counter H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_M H); [close_cz|].
    pose proof (Z.le_min_r n TC.SPEC_MAX_FRAME) as Hm.
    assert (C : TW.A_M_fly_frame + TC.SPEC_MAX_FRAME <= TW.OFF_M + TW.SZ_M) by close_cz.
    lia.
  - destruct H as (s & Hs & H). apply (close_fld_G _ _ _ _ _ a TMAP_A_g_cmd H); close_czl.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_g_q H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_g_nq H); close_cz.
Qed.

(* send_control's stores with kp = klp = 0. *)
Lemma close_sendctl_wr_G : forall a, sendctl_wr 0 0 a -> inG TG.G_HARNESS a.
Proof.
  intros a H. unfold sendctl_wr in H. destruct H as [H | [H | (H & _)]].
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_g_s H); close_cz.
  - exact (close_iosend_wr_G _ a H).
  - exfalso. exact (H eq_refl).
Qed.

(* An N_STATE notice writes GOT.t[GOT.n] (0 <= GOT.n < 16) and GOT.n: bytes of GOT. *)
Lemma close_nwr_G : forall Bw (n : TI.ntc) a, TI.n_kind n = TC.N_STATE -> notice_wr Bw n a -> inG TG.G_HARNESS a.
Proof.
  intros Bw n a K H. unfold notice_wr in H. rewrite K in H.
  destruct H as [(_ & [(Hg & Hf) | Hf]) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (E & _)]]]]];
    try (unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in E; discriminate E).
  - set (g := TW.GOT_n Bw) in *. clearbody g. apply (close_fld_G _ _ _ _ _ a TMAP_A_GOT Hf); close_czl.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_GOT Hf); close_cz.
Qed.

(* Every byte the call stores is a byte of G. *)
Lemma close_wr_G : forall (F : option TI.tframe) Bw a, close_wr F Bw a -> inG TG.G_HARNESS a.
Proof.
  intros F Bw a H. unfold close_wr in H. destruct H as [(_ & H) | [H | (B1 & r & _ & _ & [H | H])]].
  - exact (close_sendctl_wr_G a H).
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_g_s H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_A_g_s H); close_cz.
  - exact (close_nwr_G (close_w2 B1) (close_ntc B1) a eq_refl H).
Qed.

(* So it lies in G's hull, below the shadow band. *)
Lemma close_wr_hull : forall (F : option TI.tframe) Bw a, close_wr F Bw a ->
  TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI.
Proof. intros F Bw a H. exact (inG_G_HARNESS_hull a (close_wr_G F Bw a H)). Qed.

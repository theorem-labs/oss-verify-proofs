(* Model facts of the patched io_recv (TCb.v io_recv_m, fuzz/fuzz_transport.c:906-929) for the io_recv walks
   (lib/Prog/T/io_recv.v, lib/U/Prog/T/io_recv.v), build-independent (no machine, no image):
   io_recv_m, and the m_rx_m / m_tick_m it runs, keep the length of the world and its g_fail_next byte. Every
   setter they reach writes M (OFF_M, 1648 bytes), OW (OFF_OW, 304 bytes; OW.t[i] with 0 <= i < TRANS_MAX and
   OW.dn[k] with 0 <= k < 2 by the model's bounds), g_rx_fail or g_rx_times; g_fail_next lies at OFF_g_fail_next,
   outside all of them. The worlds stay abstract: no proof here compares two reads by conversion. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.

(* B' has the length of B and B's g_fail_next byte *)
Definition gkeep (B B' : list byte) : Prop := length B' = length B /\ g_fail_next B' = g_fail_next B.

Lemma gkeep_refl : forall B, gkeep B B.
Proof. intros B. split; reflexivity. Qed.

Lemma gkeep_trans : forall B1 B2 B3, gkeep B1 B2 -> gkeep B2 B3 -> gkeep B1 B3.
Proof.
  intros B1 B2 B3 [L1 G1] [L2 G2]. split.
  - rewrite L2. exact L1.
  - rewrite G2. exact G1.
Qed.

(* a write that misses the g_fail_next byte, inside the world of the anchor B0 *)
Lemma gkeep_upd : forall B0 X k v, gkeep B0 X -> 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length B0) ->
  (k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  gkeep B0 (upd X k v).
Proof.
  intros B0 X k v [L G] Hk Hl Hd. split.
  - rewrite length_upd; [exact L | exact Hk | rewrite L; exact Hl].
  - unfold g_fail_next. rewrite u_at_upd_out.
    + exact G.
    + exact Hk.
    + unfold OFF_g_fail_next. lia.
    + change (Z.of_nat 1) with 1. lia.
    + rewrite L. exact Hl.
Qed.

Lemma some_pair_inv : forall (A C : Type) (a a' : A) (c c' : C), Some (a, c) = Some (a', c') -> a = a' /\ c = c'.
Proof. intros A C a a' c c' H. injection H as H1 H2. split; [exact H1 | exact H2]. Qed.

Lemma some_triple_inv : forall (A C D : Type) (a a' : A) (c c' : C) (d d' : D),
  Some (a, c, d) = Some (a', c', d') -> a = a' /\ c = c' /\ d = d'.
Proof. intros A C D a a' c c' d d' H. injection H as H1 H2 H3. split; [exact H1 | split; [exact H2 | exact H3]]. Qed.

Lemma len_w : forall B : list byte, length B = Z.to_nat W_LEN -> Z.of_nat (length B) = W_LEN.
Proof. intros B H. rewrite H. apply Z2Nat.id. unfold W_LEN. lia. Qed.

Ltac gk_setters :=
  unfold set_OW_t_reason, set_OW_t_old, set_OW_t_state, set_M_state, set_OW_n, set_M_desk_counter_valid,
    set_M_fly_on, set_M_e1_us, set_M_e2_acked, set_M_wake_sent, set_OW_e2, set_M_fail, set_M_next_ka,
    set_OW_desk_off, set_OW_desk, set_OW_desk_body, set_OW_desk_p, set_M_foreign, set_OW_foreign, set_OW_acked,
    set_OW_acked_counter, set_OW_acked_retry, set_M_backoff_until, set_OW_acks, set_M_desk_counter,
    set_OW_dn_body, set_OW_dn_len, set_OW_dn_counter, set_OW_dn_retry, set_OW_ndata, set_M_last_rx,
    set_M_desk_known, set_M_desk, set_g_rx_fail, set_g_rx_times in *.

(* the boolean branch facts as propositions, for lia *)
Ltac gk_bools :=
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  end.

(* a side goal of gkeep_upd: offsets and lengths by lia *)
Ltac gk_side :=
  gk_bools;
  repeat match goal with |- context [length (put ?n ?w)] => rewrite (length_put n w) end;
  repeat match goal with
  | |- context [length (sub ?bs ?k ?n)] =>
      generalize (length_sub_le bs k n); generalize (length (sub bs k n)); intros
  end;
  unfold A_M_desk_known, A_M_desk, A_M_state, A_M_e2_acked, A_M_e1_us, A_M_foreign, A_M_last_rx, A_M_wake_sent,
    A_M_next_ka, A_M_backoff_until, A_M_desk_counter_valid, A_M_desk_counter, A_M_fail, A_M_fly_on,
    A_OW_n, A_OW_t_state, A_OW_t_old, A_OW_t_reason, A_OW_e2, A_OW_acks, A_OW_desk, A_OW_foreign, A_OW_acked,
    A_OW_ndata, A_OW_acked_counter, A_OW_acked_retry, A_OW_desk_off, A_OW_desk_p, A_OW_desk_body,
    A_OW_dn_body, A_OW_dn_len, A_OW_dn_counter, A_OW_dn_retry, OFF_M, OFF_OW, OFF_g_rx_fail, OFF_g_rx_times,
    OFF_g_fail_next, W_LEN, TRANS_MAX in *;
  lia.

(* gkeep B0 X for X a nest of upd over a world Y with gkeep B0 Y in the context *)
Ltac gk_go :=
  lazymatch goal with
  | |- gkeep ?B0 (upd ?X ?k ?v) => apply (gkeep_upd B0 X k v); [gk_go | gk_side | gk_side | gk_side]
  | |- gkeep ?B0 ?X =>
      first [ match goal with H : gkeep B0 X |- _ => exact H end
            | lazymatch X with B0 => apply gkeep_refl end ]
  end.

Ltac gk := gk_setters; gk_go.

(* split H : <model term> = Some _ at a branch whose scrutinee holds no branch itself (innermost first, so a test
   inside an argument is split before the call that takes it), until H is Some _ = Some _ (or a call left whole,
   or None = Some _, closed) *)
Ltac gk_split H :=
  repeat (cbv beta iota zeta in H;
    lazymatch type of H with
    | None = Some _ => discriminate H
    | Some _ = Some _ => fail
    | _ =>
        match type of H with
        | context [match ?c with _ => _ end] =>
            lazymatch c with
            | context [match _ with _ => _ end] => fail
            | _ => tryif is_var c then destruct c else (let E := fresh "E" in destruct c eqn:E)
            end
        end
    end).

(* ---- the model functions m_rx runs: m_set, m_lost, m_wake, m_maybe_online, m_tick ---- *)

Lemma m_set_gk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' st why u, gkeep B0 B -> m_set_m B st why = Some (B', u) -> gkeep B0 B'.
Proof.
  intros B0 HL0 B B' st why u HK H. pose proof (len_w B0 HL0) as HL.
  unfold m_set_m in H. gk_split H; apply some_pair_inv in H as [<- _]; gk.
Qed.

Lemma m_lost_gk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' why u, gkeep B0 B -> m_lost_m B why = Some (B', u) -> gkeep B0 B'.
Proof.
  intros B0 HL0 B B' why u HK H. pose proof (len_w B0 HL0) as HL. unfold m_lost_m in H.
  refine (m_set_gk B0 HL0 _ B' S_IDLE why u _ H). gk.
Qed.

Lemma m_maybe_online_gk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' u, gkeep B0 B -> m_maybe_online_m B = Some (B', u) -> gkeep B0 B'.
Proof.
  intros B0 HL0 B B' u HK H. pose proof (len_w B0 HL0) as HL. unfold m_maybe_online_m in H. gk_split H.
  - refine (m_set_gk B0 HL0 _ B' S_ONLINE R_ONLINE u _ H). gk.
  - apply some_pair_inv in H as [<- _]. exact HK.
Qed.

Lemma m_tick_gk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' u, gkeep B0 B -> m_tick_m B = Some (B', u) -> gkeep B0 B'.
Proof.
  intros B0 HL0 B B' u HK H. unfold m_tick_m in H. gk_split H.
  all: first [ exact (m_lost_gk B0 HL0 B B' _ u HK H)
             | (apply some_pair_inv in H as [<- _]; exact HK) ].
Qed.

(* every call of m_set / m_lost / m_wake / m_maybe_online / m_tick in the context, turned into gkeep B0 of its
   world, in the order the dependencies allow (a call whose argument world is not yet known waits) *)
Ltac gk_calls B0 HL0 :=
  repeat match goal with
  | E : m_set_m ?Y _ _ = Some (?Z, _) |- _ =>
      let K := fresh "K" in assert (K : gkeep B0 Z) by (refine (m_set_gk B0 HL0 Y Z _ _ _ _ E); gk); clear E
  | E : m_lost_m ?Y _ = Some (?Z, _) |- _ =>
      let K := fresh "K" in assert (K : gkeep B0 Z) by (refine (m_lost_gk B0 HL0 Y Z _ _ _ E); gk); clear E
  | E : m_maybe_online_m ?Y = Some (?Z, _) |- _ =>
      let K := fresh "K" in
      assert (K : gkeep B0 Z) by (refine (m_maybe_online_gk B0 HL0 Y Z _ _ E); gk); clear E
  | E : m_tick_m ?Y = Some (?Z, _) |- _ =>
      let K := fresh "K" in assert (K : gkeep B0 Z) by (refine (m_tick_gk B0 HL0 Y Z _ _ E); gk); clear E
  end.

Lemma m_wake_gk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall B B' r, gkeep B0 B -> m_wake_m B = Some (B', r) -> gkeep B0 B'.
Proof.
  intros B0 HL0 B B' r HK H. pose proof (len_w B0 HL0) as HL. unfold m_wake_m in H. gk_split H.
  all: apply some_pair_inv in H as [<- _]; gk_calls B0 HL0; gk.
Qed.

Ltac gk_calls_w B0 HL0 :=
  repeat match goal with
  | E : m_wake_m ?Y = Some (?Z, _) |- _ =>
      let K := fresh "K" in assert (K : gkeep B0 Z) by (refine (m_wake_gk B0 HL0 Y Z _ _ E); gk); clear E
  | _ => progress gk_calls B0 HL0
  end.

Lemma m_rx_gk : forall B0, length B0 = Z.to_nat W_LEN ->
  forall I F B B' n r, gkeep B0 B -> m_rx_m I F B n = Some (B', r) -> gkeep B0 B'.
Proof.
  intros B0 HL0 I F B B' n r HK H. pose proof (len_w B0 HL0) as HL. unfold m_rx_m in H.
  destruct F as [fr|]; [|discriminate H].
  gk_split H.
  all: apply some_pair_inv in H as [<- _]; gk_calls_w B0 HL0; gk.
Qed.

(* ---- io_recv_m ---- *)

Lemma io_recv_gk : forall I F B cap B' r got, length B = Z.to_nat W_LEN ->
  io_recv_m I F B cap = Some (B', r, got) -> gkeep B B'.
Proof.
  intros I F B cap B' r got HL0 H. pose proof (len_w B HL0) as HL. pose proof (gkeep_refl B) as HK.
  unfold io_recv_m in H. gk_split H.
  all: apply some_triple_inv in H as [HB _]; subst B'; gk_calls B HL0.
  all: try gk.
  all: lazymatch goal with
       | E : m_rx_m _ _ ?Y _ = Some (?Z, _) |- gkeep ?B0 ?Z => refine (m_rx_gk B0 HL0 _ _ Y Z _ _ _ E); gk
       end.
Qed.

(* what the walks use: io_recv_m keeps g_fail_next *)
Lemma io_recv_m_g_fail_next : forall I F B cap B' r got, length B = Z.to_nat W_LEN ->
  io_recv_m I F B cap = Some (B', r, got) -> g_fail_next B' = g_fail_next B.
Proof. intros I F B cap B' r got HL H. exact (proj2 (io_recv_gk I F B cap B' r got HL H)). Qed.

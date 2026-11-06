(* Facts about the model of diginet_session_poll (TSess.v diginet_session_poll_m, poll_drain_m) and of the io_recv it
   calls through g_s.io.recv (TCb.v io_recv_m), cut where the binary's code branches. Build-independent: the walks
   Prog/T/diginet_session_poll.v (plain) and U/Prog/T/diginet_session_poll.v (ubsan) use them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldLemmas TSess0 TCb TSess.
Import ListNotations.
Open Scope Z_scope.

(* the pair inside a Some, by name (no injection on a world-carrying option in the walks) *)
Lemma some_pair_inv : forall (X Y : Type) (a a' : X) (b b' : Y), Some (a, b) = Some (a', b') -> a = a' /\ b = b'.
Proof. intros X Y a a' b b' H. injection H as -> ->. split; reflexivity. Qed.

Lemma call_now_inv : forall I B now, call_now I B = Some now -> S_io_now_us B = ti_io_now I /\ now = io_now_m B.
Proof.
  intros I B now H. unfold call_now in H. revert H.
  destruct (Z.eqb_spec (S_io_now_us B) (ti_io_now I)) as [E|E]; intros H; cbv beta iota in H; [|discriminate H].
  injection H as <-. split; [exact E | reflexivity].
Qed.

Lemma call_recv_inv : forall I F B cap B' r got, call_recv I F B cap = Some (B', r, got) ->
  S_io_recv B = ti_io_recv I /\ io_recv_m I F B cap = Some (B', r, got).
Proof.
  intros I F B cap B' r got H. unfold call_recv in H. revert H.
  destruct (Z.eqb_spec (S_io_recv B) (ti_io_recv I)) as [E|E]; intros H; cbv beta iota in H; [|discriminate H].
  split; [exact E | exact H].
Qed.

(* io_recv's result is an int, and when it is > 0 it is the number of bytes handed over (:917, :927-928) *)
Lemma io_recv_m_ret : forall I F B cap B' r got, 0 <= cap < 2 ^ 31 ->
  io_recv_m I F B cap = Some (B', r, got) -> - 2 ^ 31 <= r < 2 ^ 31 /\ (0 < r -> Z.of_nat (length got) = r).
Proof.
  intros I F B cap B' r got Hcap H. unfold io_recv_m in H. revert H.
  destruct (truth (g_rx_fail B)); intros H; cbv beta iota in H.
  { injection H as _ <- <-. unfold EIO. split; [lia | intros; lia]. }
  revert H. destruct ((g_rx B =? 0) || (g_rx_times B =? 0)); intros H; cbv beta iota in H.
  { injection H as _ <- <-. split; [lia | intros; lia]. }
  revert H. destruct (int_dec (g_rx_times B)) as [t|]; intros H; cbv beta iota zeta in H; [|discriminate H].
  set (B1 := set_g_rx_times B t) in H.
  assert (Hn : 0 <= (if g_rx_len B1 <? cap then g_rx_len B1 else cap) <= cap).
  { pose proof (u_at_range B1 OFF_g_rx_len 8) as R. change (u_at B1 OFF_g_rx_len 8) with (g_rx_len B1) in R.
    destruct (Z.ltb_spec (g_rx_len B1) cap); lia. }
  revert H Hn. generalize (if g_rx_len B1 <? cap then g_rx_len B1 else cap). intros n H Hn.
  revert H. lazymatch goal with |- (match ?e with Some _ => _ | None => _ end = _) -> _ => destruct e as [B2|] end;
    intros H; cbv beta iota in H; [|discriminate H].
  revert H. destruct (frame_read F (g_rx B2) n) as [bytes|] eqn:FR; intros H; cbv beta iota in H;
    [|discriminate H].
  assert (Sw : bv_swrap 32 n = n).
  { unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
    rewrite Z.mod_small by lia. lia. }
  rewrite Sw in H. injection H as _ <- <-.
  split; [lia |]. intros Hr.
  replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; exact Hr).
  unfold frame_read in FR. revert FR.
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct F as [f|]; intros FR; cbv beta iota zeta in FR; [|discriminate FR]. revert FR.
  destruct ((g_rx B2 - tf_addr f <? 0) || (n <? 0) || (Z.of_nat (length (tf_bytes f)) <? g_rx B2 - tf_addr f + n))
    eqn:C; intros FR; cbv beta iota in FR; [discriminate FR |].
  injection FR as <-.
  apply orb_false_iff in C as [C C3]. apply orb_false_iff in C as [C1 C2].
  apply Z.ltb_ge in C1. apply Z.ltb_ge in C3.
  rewrite length_sub by lia. lia.
Qed.

(* diginet_session_poll_m (:505-527) cut at the binary's branches: the argument test of :508-509, now and the
   deadline (:510-515), the first recv (:516) and its error exit (:517-518), now, rx when it handed over a frame,
   tick (:519-522), and the drain loop with the fuel g_rx_times (:523-526) *)
Lemma poll_cases : forall I F B w B' r, diginet_session_poll_m I F B w = Some (B', r) ->
  ((S_io_recv B = 0 \/ S_io_now_us B = 0) /\ B' = B /\ r = DIGINET_E_ARG) \/
  (S_io_recv B <> 0 /\ S_io_now_us B <> 0 /\
   exists now due B1 r1 got,
     call_now I B = Some now /\ diginet_session_deadline_m B now = Some due /\
     call_recv I F B DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) /\
     ((r1 < 0 /\ B' = B1 /\ r = r1) \/
      (0 <= r1 /\ exists now2 B2 B3 r3,
         call_now I B1 = Some now2 /\
         ((r1 = 0 /\ B2 = B1) \/ (0 < r1 /\ exists r2, diginet_session_rx_m I F B1 got now2 = Some (B2, r2))) /\
         diginet_session_tick_m I F B2 now2 = Some (B3, r3) /\
         poll_drain_m I F B3 (Z.to_nat (g_rx_times B3)) = Some (B', r)))).
Proof.
  intros I F B w B' r H. unfold diginet_session_poll_m in H. revert H.
  destruct (Z.eqb_spec (S_io_recv B) 0) as [E1|E1]; intros H; cbv beta iota delta [orb] in H.
  { left. apply some_pair_inv in H as [<- <-]. split; [left; exact E1 | split; reflexivity]. }
  revert H. destruct (Z.eqb_spec (S_io_now_us B) 0) as [E2|E2]; intros H; cbv beta iota in H.
  { left. apply some_pair_inv in H as [<- <-]. split; [right; exact E2 | split; reflexivity]. }
  right. split; [exact E1 |]. split; [exact E2 |].
  revert H. destruct (call_now I B) as [now|] eqn:CN; intros H; cbv beta iota in H; [|discriminate H].
  revert H. destruct (diginet_session_deadline_m B now) as [due|] eqn:DD; intros H; cbv beta iota zeta in H;
    [|discriminate H].
  revert H. destruct (call_recv I F B DIGINET_MAX_FRAME_LEN) as [[[B1 r1] got]|] eqn:CR; intros H;
    cbv beta iota in H; [|discriminate H].
  exists now, due, B1, r1, got.
  split; [first [exact CN | reflexivity] |]. split; [first [exact DD | reflexivity] |].
  split; [first [exact CR | reflexivity] |].
  revert H. destruct (Z.ltb_spec r1 0) as [L|L]; intros H; cbv beta iota in H.
  { left. apply some_pair_inv in H as [<- <-]. split; [exact L | split; reflexivity]. }
  right. split; [exact L |].
  revert H. destruct (call_now I B1) as [now2|] eqn:CN2; intros H; cbv beta iota in H; [|discriminate H].
  revert H. destruct (if 0 <? r1 then diginet_session_rx_m I F B1 got now2 else Some (B1, DIGINET_OK))
    as [[B2 r2]|] eqn:RX; intros H; cbv beta iota in H; [|discriminate H].
  revert H. destruct (diginet_session_tick_m I F B2 now2) as [[B3 r3]|] eqn:TK; intros H; cbv beta iota in H;
    [|discriminate H].
  exists now2, B2, B3, r3. split; [first [exact CN2 | reflexivity] |]. split.
  { revert RX. destruct (Z.ltb_spec 0 r1) as [P|P]; intros RX; cbv beta iota in RX.
    - right. split; [exact P |]. exists r2. exact RX.
    - left. split; [lia |]. apply some_pair_inv in RX as [<- _]. reflexivity. }
  split; [first [exact TK | reflexivity] | exact H].
Qed.

(* one turn of the drain loop (:524-525) or its exit (:526) *)
Lemma poll_drain_cases : forall I F B fuel B' r, poll_drain_m I F B fuel = Some (B', r) ->
  exists B1 r1 got, call_recv I F B DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) /\
    ((r1 <= 0 /\ B' = B1 /\ r = r1) \/
     (0 < r1 /\ exists f now B2 r2, fuel = S f /\ call_now I B1 = Some now /\
        diginet_session_rx_m I F B1 got now = Some (B2, r2) /\ poll_drain_m I F B2 f = Some (B', r))).
Proof.
  intros I F B fuel B' r H.
  assert (U : poll_drain_m I F B fuel =
    match call_recv I F B DIGINET_MAX_FRAME_LEN with
    | None => None
    | Some (B1, r1, got) =>
        if 0 <? r1 then
          match fuel with
          | O => None
          | S f =>
              match call_now I B1 with
              | None => None
              | Some now =>
                  match diginet_session_rx_m I F B1 got now with
                  | None => None
                  | Some (B2, _) => poll_drain_m I F B2 f
                  end
              end
          end
        else Some (B1, if r1 <? 0 then r1 else 0)
    end) by (destruct fuel; reflexivity).
  rewrite U in H. clear U. revert H.
  destruct (call_recv I F B DIGINET_MAX_FRAME_LEN) as [[[B1 r1] got]|] eqn:CR; intros H; cbv beta iota in H;
    [|discriminate H].
  exists B1, r1, got. split; [first [exact CR | reflexivity] |].
  revert H. destruct (Z.ltb_spec 0 r1) as [P|P]; intros H; cbv beta iota in H.
  - right. split; [exact P |].
    destruct fuel as [|f]; cbv beta iota in H; [discriminate H |].
    revert H. destruct (call_now I B1) as [now|] eqn:CN; intros H; cbv beta iota in H; [|discriminate H].
    revert H. destruct (diginet_session_rx_m I F B1 got now) as [[B2 r2]|] eqn:RX; intros H; cbv beta iota in H;
      [|discriminate H].
    exists f, now, B2, r2. split; [reflexivity |].
    split; [first [exact CN | reflexivity] |]. split; [first [exact RX | reflexivity] | exact H].
  - left. apply some_pair_inv in H as [<- <-]. split; [exact P | split; [reflexivity |]].
    destruct (Z.ltb_spec r1 0); lia.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 1162 of its 1219 lines of code are new or changed and 392 lines of the source are left out. *)
(* diginet_session_tick (transport/src/diginet_session.c:414-472) in the plain build, 0x16cdc .. 0x16fb4, against
   diginet_session_tick_c.v. The walk keeps the 48 bytes of saved registers at the top of the 1568-byte frame as one
   cell (tick_inv) and cuts the rest of the frame into cells only where a callee or a store needs them: the notice
   struct at sp + 32 (memset, then notice), take's body / body_len / has_display at sp + 32 / + 24 / + 20, the
   keepalive byte at sp + 32. Pieces: ret_ok (the epilogue), ka_ok and take_ok (:449-471), tail_ok (:445-471),
   ackl_ok (:436-441), rexmit_ok (:432-434, retransmit and send_raw inlined), inflight_ok (:430-443), and the theorem
   (:418-427, session_lost and set_state inlined, lost_path). The world algebra of each path is a lemma about the
   model (ka_world, rex_world); the model facts on take and notice are TModel/TSessFacts.v, on io_send
   TModel/TIoSendFail.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0
  TCb TSess TSessFacts TIoSendFail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import diginet_session_tick_c take_c send_data_c
  notice_c io_send_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c.
Import ListNotations.
Open Scope Z_scope.

Lemma mod64_inj : forall a b, -2^63 <= a < 2^64 -> -2^63 <= b < 2^64 -> (a < 0 <-> b < 0) \/ (0 <= a /\ 0 <= b) ->
  (a mod 2^64 =? b mod 2^64) = (a =? b).
Proof.
  intros a b Ha Hb Hs. destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. lia.
Qed.

Lemma br_eqb : forall a b, bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a mod 2^64 =? b mod 2^64).
Proof. intros. unfold bv_eqb. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma br_ltu : forall a b, bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a mod 2^64 <? b mod 2^64).
Proof. intros. unfold bv_ltu. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma br_lts : forall a b, bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (bv_swrap 64 a <? bv_swrap 64 b).
Proof. intros. unfold bv_lts. rewrite !Z_to_bv_signed. reflexivity. Qed.

(* the branch conditions in the model's terms *)
Lemma br_eqb_s : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. rewrite br_eqb. destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. lia.
Qed.
Lemma br_eqb_u : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. rewrite br_eqb, !Z.mod_small by lia. reflexivity. Qed.
Lemma br_ltu_u : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. rewrite br_ltu, !Z.mod_small by lia. reflexivity. Qed.
Lemma swrap64_id : forall a, -2^63 <= a < 2^63 -> bv_swrap 64 a = a.
Proof.
  intros a Ha. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma br_lts_s : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. rewrite br_lts, !swrap64_id by lia. reflexivity. Qed.

(* a piece [a, a + n) of a stack region, as its own cell *)
Lemma stk_cut : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  stk rsegs m lo a /\ (exists junk, rw_cells rsegs m a [CB n junk]) /\ stk rsegs m (a + Z.of_nat n) hi.
Proof.
  intros m lo hi a n H Ha Hn.
  destruct (stk_split rsegs m lo a hi H) as [S1 S2]; [pose proof H as (H1 & _ & _); lia|].
  destruct (stk_split rsegs m a (a + Z.of_nat n) hi S2) as [S3 S4]; [lia|].
  destruct (stk_carve rsegs m a (a + Z.of_nat n) n S3) as [_ [junk FR]]; [lia|].
  replace (a + Z.of_nat n - Z.of_nat n) with a in FR by lia.
  split; [exact S1|]. split; [exists junk; exact FR | exact S4].
Qed.

Lemma stk_join : forall m lo hi a b cs, stk rsegs m lo a -> rw_cells rsegs m a cs ->
  b = a + Z.of_nat (cells_size cs) -> stk rsegs m b hi -> b <= hi -> lo <= a ->
  stk rsegs m lo hi.
Proof.
  intros m lo hi a b cs S1 C -> S2 H1 H2.
  eapply stk_merge; [eapply stk_release; [exact S1 | exact C | lia] | exact S2 | lia].
Qed.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(* g_fail_next across a write of the world that misses it *)
Lemma gf_put : forall B k n x, length B = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  (k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  length (upd B k (put n x)) = Z.to_nat W_LEN /\ g_fail_next (upd B k (put n x)) = g_fail_next B.
Proof.
  intros B k n x L Hk Hn Hd. pose proof (tsf_gf_put (g_fail_next B) B k n x (conj L eq_refl) Hk Hn Hd) as [H1 H2].
  split; assumption.
Qed.

Lemma swrap32_range : forall x, -2^31 <= bv_swrap 32 x < 2^31.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia.
Qed.

Lemma swrap32_id : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_eq0 : forall n, 0 <= n < 2^32 -> (bv_swrap 32 n =? 0) = (n =? 0).
Proof.
  intros n Hn. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.eqb_spec n 0) as [->|N]; [reflexivity|]. apply Z.eqb_neq. intros E. apply N.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cb_c4 : forall m a x, rw_cells rsegs m a [CB 4 (put 4 x)] -> rw_cells rsegs m a [C4 (Z_to_bv 64 x)].
Proof.
  intros m a x [[Hwf Hb] Hw]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite le4_put. exact Hb.
  - exact Hw.
Qed.

Lemma cb_c8 : forall m a x, rw_cells rsegs m a [CB 8 (put 8 x)] -> rw_cells rsegs m a [C8 (Z_to_bv 64 x)].
Proof.
  intros m a x [[Hwf Hb] Hw]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite le8_put. exact Hb.
  - exact Hw.
Qed.

Lemma bytes_at_firstn : forall m a l k, bytes_at rsegs m a l -> bytes_at rsegs m a (firstn k l).
Proof.
  intros m a l k (H1 & H2 & H). split; [lia|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite ne_firstn.
  destruct (Nat.ltb_spec i k); [apply H; lia | lia].
Qed.

Lemma rw_cells_CB_bytes : forall m a n l, rw_cells rsegs m a [CB n l] -> bytes_at rsegs m a l /\ length l = n.
Proof. intros m a n l [[Hwf Hb] _]. cbn in Hwf, Hb. rewrite app_nil_r in Hb. split; [exact Hb | tauto]. Qed.

Lemma stk_empty : forall m a, 0 <= a <= 2^64 -> stk rsegs m a a.
Proof. intros m a Ha. split; [lia|]. split; [lia|]. intros x Hx. lia. Qed.

Lemma s32_eq0 : forall B k, (s32_at B k =? 0) = (u_at B k 4 =? 0).
Proof. intros B k. unfold s32_at. apply swrap32_eq0. apply (u_at_range B k 4). Qed.

Lemma allow_bin : forall now x g, 0 <= now < 2^64 -> 0 <= x < 2^64 -> 0 <= g < 2^64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 now) - bv_unsigned (Z_to_bv 64 x)))
                                           (Z_to_bv 64 g))) 1)
  = Z_to_bv 64 (int_of_bool (g <=? u64 (now - x))).
Proof.
  intros now x g Hn Hx Hg. rewrite v_sltu_b2z. f_equal.
  rewrite (unsigned_lit now), (unsigned_lit x), (unsigned_lit g) by lia.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  unfold u64, int_of_bool.
  destruct (Z.ltb_spec ((now - x) mod 2^64) g) as [Lt|Ge].
  - replace (g <=? (now - x) mod 2^64) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - replace (g <=? (now - x) mod 2^64) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma put8_eq : forall x y, x mod 2^64 = y mod 2^64 -> put 8 x = put 8 y.
Proof. intros x y E. rewrite <- (put_mod64 8 x), <- (put_mod64 8 y) by lia. rewrite E. reflexivity. Qed.

(* the contract's post, by name *)
Definition tick_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) (B' : list byte) (r : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 2160, bv_unsigned sp);
           (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    wmem rsegs m' B' /\ g_fail_next B' <= 1.

Definition tick_inv (sp : word) (lo : Z) (m0 m : word -> option byte) (B : list byte)
    (ra0 v0 v1 v2 v3 v4 : word) : Prop :=
  bv_unsigned sp mod 16 = 0 /\ lo + 2160 <= bv_unsigned sp /\ W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 2160 /\
  stk rsegs m lo (bv_unsigned sp + -48) /\
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 ra0] /\
  wmem rsegs m B /\ g_fail_next B <= 1 /\ mem_inv rsegs m /\
  munch [(bv_unsigned sp - 2160, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m0 m /\
  wmono rsegs m0 m.

(* a branch whose condition is CLOSED (no local variable in it): decided by computation. It refuses an open
   condition, so vm_compute never meets a Z_to_bv 64 of an open term. *)
Ltac br_closed := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  (match c with context [?x] => is_var x; fail 1 "br_closed: open condition" | _ => idtac end);
  let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota end.

Ltac nb := try change (negb true) with false; try change (negb false) with true.

Ltac inv_intro I := destruct I as (SP16 & LO & WO & ST & FRs & WM & GF & MI & MU & WMO).
Ltac inv_split := split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
  split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; assumption.

(* the callee's sp: the frame below the saved registers *)
Ltac sp_facts sp :=
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
  let Hsp := fresh "Hsp" in
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -1568)) = bv_unsigned sp + -1568) by (apply unsigned_lit; lia).

(* 0x16edc: the epilogue *)
Lemma ret_ok : forall (ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo : Z) (B : list byte) (r : Z),
  tick_inv sp lo m0 m B ra0 v0 v1 v2 v3 v4 ->
  evt rsegs (tick_post ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B r)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16edc) fc None m (seg_rom rsegs)).
Proof.
  intros until r. intros I. inv_intro I.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -1568)) = bv_unsigned sp + -1568) by (apply unsigned_lit; lia).
  do 7 step.
  release_frame FRs ST (bv_unsigned sp).
  step.
  apply evt_done. unfold tick_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WMO|]. split; [exact MI|]. split; [exact ST|]. split; [exact WM | exact GF].
Qed.

(* ---- the model of tick from :445 on, by pieces ---- *)
Definition tick_ka_w (B : list byte) (now : Z) : list byte :=
  let B := set_S_next_keepalive_us B (u64 (S_next_keepalive_us B + ms_m (S_cfg_keepalive_ms B))) in
  let B := if S_next_keepalive_us B <=? now
           then set_S_next_keepalive_us B (u64 (now + ms_m (S_cfg_keepalive_ms B))) else B in
  set_S_stats_tx_keepalives B (u64 (S_stats_tx_keepalives B + 1)).

Definition tick_ka_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  send_data_m I F (tick_ka_w B now) [b8 0] 1 now.

Definition tick_take_m (I : timg) (F : option tframe) (B : list byte) (allow now : Z) : option (list byte * Z) :=
  match take_m B allow with
  | None => None
  | Some (B, (body, body_len, has_display, n)) =>
      if n =? 0 then Some (B, DIGINET_OK)
      else
        let B := if has_display =? 0 then B else set_S_last_display_us (set_S_display_sent B 1) now in
        send_data_m I F B (firstn (Z.to_nat body_len) body) n now
  end.

Definition tick_tail_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  if negb (S_state B =? DIGINET_S_ONLINE) || negb (S_inflight B =? 0) || (now <? S_backoff_until_us B) then
    Some (B, DIGINET_OK)
  else if S_next_keepalive_us B <=? now then tick_ka_m I F B now
  else if S_queued B =? 0 then Some (B, DIGINET_OK)
  else tick_take_m I F B (int_of_bool ((S_display_sent B =? 0) ||
                                       (S_cfg_display_gap_us B <=? u64 (now - S_last_display_us B)))) now.

Lemma lenW : forall B k v, length B = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  length (upd B k v) = Z.to_nat W_LEN.
Proof. intros B k v L Hk H. rewrite length_upd; [exact L | exact Hk | rewrite L; unfold W_LEN in *; lia]. Qed.

Ltac uoff := unfold A_S_state, A_S_inflight, A_S_backoff_until_us, A_S_next_keepalive_us,
  A_S_queued, A_S_display_sent, A_S_last_display_us, A_S_cfg_display_gap_us, A_S_cfg_keepalive_ms,
  A_S_stats_tx_keepalives, A_S_inflight_frame, A_S_inflight_len, A_S_inflight_counter, A_S_inflight_retries,
  A_S_inflight_sent_us, A_S_stats_tx_retransmits, A_S_stats_tx_frames, A_S_stats_ack_lost, A_S_cfg_ack_timeout_ms,
  A_S_cfg_max_retries, A_S_desk_counter_valid, A_S_io_send, A_S_notify, A_S_notify_ctx, A_S_io_ctx,
  A_S_wake_sent_us, A_S_cfg_wake_timeout_ms, A_S_last_rx_us, A_S_cfg_offline_ms, DIGINET_ETH_HDR_LEN, W_LEN, OFF_g_s, OFF_g_fail_next in *.

(* length X = Z.to_nat W_LEN for a nest of upd over a world *)
Ltac wlen L := first [ exact L | apply lenW; [wlen L | uoff; lia | rewrite ?length_put; uoff; lia] ].
(* a side goal k + n <= Z.of_nat (length X) or alike *)
Ltac wside L :=
  repeat match goal with |- context [length (upd ?X ?k ?v)] =>
    let E := fresh "E" in assert (E : length (upd X k v) = Z.to_nat W_LEN) by wlen L; rewrite E; clear E end;
  rewrite ?L, ?length_put; uoff; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Lemma ka_world : forall B now, length B = Z.to_nat W_LEN -> 0 <= now < 2^64 ->
  tick_ka_w B now =
  upd (upd B A_S_next_keepalive_us
         (put 8 (if now <? (S_cfg_keepalive_ms B * 1000 + S_next_keepalive_us B) mod 2^64
                 then S_cfg_keepalive_ms B * 1000 + S_next_keepalive_us B
                 else S_cfg_keepalive_ms B * 1000 + now)))
      A_S_stats_tx_keepalives (put 8 (S_stats_tx_keepalives B + 1)).
Proof.
  intros B now L Hn. unfold tick_ka_w.
  pose proof (u_at_range B A_S_cfg_keepalive_ms 4) as Rk.
  change (2 ^ (8 * Z.of_nat 4)) with (2^32) in Rk.
  unfold set_S_next_keepalive_us, S_next_keepalive_us, S_cfg_keepalive_ms,
    set_S_stats_tx_keepalives, S_stats_tx_keepalives, ms_m, u64.
  rewrite (u_at_upd_put B A_S_next_keepalive_us 8) by wside L.
  rewrite (u_at_upd_out B _ A_S_next_keepalive_us A_S_cfg_keepalive_ms 4) by wside L.
  change (2 ^ (8 * Z.of_nat 8)) with (2^64).
  rewrite (Z.mod_small (u_at B A_S_cfg_keepalive_ms 4 * 1000)) by lia.
  rewrite Zmod_mod.
  set (kv := u_at B A_S_cfg_keepalive_ms 4 * 1000). set (nx := u_at B A_S_next_keepalive_us 8).
  destruct (Z.leb_spec ((nx + kv) mod 2^64) now) as [Le|Gt].
  - rewrite (upd_upd_same B) by wside L.
    replace (now <? (kv + nx) mod 2 ^ 64) with false by (symmetry; apply Z.ltb_ge; rewrite Z.add_comm; exact Le).
    rewrite (u_at_upd_out B _ A_S_next_keepalive_us A_S_stats_tx_keepalives 8) by wside L.
    f_equal; [f_equal; apply put8_eq; rewrite Zmod_mod; f_equal; lia | apply put8_eq; apply Zmod_mod].
  - replace (now <? (kv + nx) mod 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; rewrite Z.add_comm; exact Gt).
    rewrite (u_at_upd_out B _ A_S_next_keepalive_us A_S_stats_tx_keepalives 8) by wside L.
    f_equal; [f_equal; apply put8_eq; rewrite Zmod_mod; f_equal; lia | apply put8_eq; apply Zmod_mod].
Qed.

(* ---- reading a field of a byte list built by app ---- *)
Lemma u_at_app_l : forall (l1 l2 : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length l1) ->
  u_at (l1 ++ l2) k n = u_at l1 k n.
Proof.
  intros l1 l2 k n Hk Hn. unfold u_at, sub. f_equal.
  rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length l1 - Z.to_nat k))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma u_at_app_r : forall (l1 l2 : list byte) k n, Z.of_nat (length l1) <= k ->
  u_at (l1 ++ l2) k n = u_at l2 (k - Z.of_nat (length l1)) n.
Proof.
  intros l1 l2 k n Hk. unfold u_at, sub. f_equal.
  rewrite skipn_app, (skipn_all2 l1) by lia. cbn [app]. f_equal. f_equal. lia.
Qed.

Lemma ble_zeros : forall l, (forall b, In b l -> b = Z_to_bv 8 0) -> bytes_le_to_Z l = 0.
Proof.
  induction l as [|b l IH]; intros H; [reflexivity|]. cbn [bytes_le_to_Z].
  rewrite IH by (intros c Hc; apply H; right; exact Hc). rewrite (H b) by (left; reflexivity). reflexivity.
Qed.

Lemma in_firstn' : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.
Lemma in_skipn' : forall {A} n (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H. Qed.

Lemma u_at_zeros : forall k j n, u_at (repeat (Z_to_bv 8 0) k) j n = 0.
Proof.
  intros k j n. unfold u_at, sub. apply ble_zeros. intros b Hb.
  apply in_firstn', in_skipn', repeat_spec in Hb. exact Hb.
Qed.

(* the 72 bytes of a struct diginet_notice with no announce, personality, MAC offset or body *)
Definition ntc_bytes (kind st old why cnt rt : Z) : list byte :=
  put 4 kind ++ put 4 st ++ put 4 old ++ put 4 why ++ repeat (Z_to_bv 8 0) 48 ++ put 4 cnt ++ put 2 rt ++
  repeat (Z_to_bv 8 0) 2.

Ltac ua := unfold ntc_bytes;
  repeat (rewrite u_at_app_r by (rewrite ?length_put, ?repeat_length; cbn; lia));
  first [ rewrite u_at_app_l by (rewrite ?length_put, ?repeat_length; cbn; lia) | idtac ];
  first [ rewrite u_at_zeros | rewrite u_at_put ]; try reflexivity.

Lemma ntc_bytes_at : forall m p sp K kind st old why cnt rt,
  bytes_at rsegs m p (ntc_bytes kind st old why cnt rt) ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window sp K p 72 -> K <= bv_unsigned sp ->
  ntc_at m p (Ntc (bv_swrap 32 (kind mod 2^32)) (bv_swrap 32 (st mod 2^32)) (bv_swrap 32 (old mod 2^32))
                  (bv_swrap 32 (why mod 2^32)) (cnt mod 2^32) (rt mod 2^16) 0 0 None [] 0) sp K.
Proof.
  intros m p sp K kind st old why cnt rt BA Hp Hp8 Ow Ok HK.
  unfold ntc_at. split; [exact Hp|]. split; [exact Hp8|]. split; [exact Ow|]. split; [exact Ok|].
  exists (ntc_bytes kind st old why cnt rt). split; [exact BA|].
  split; [unfold ntc_bytes; rewrite !length_app, !length_put, !repeat_length; reflexivity|].
  cbn [n_kind n_state n_old n_reason n_pers n_mac_offset n_body_len n_counter n_retry n_body n_ann].
  unfold s32_at.
  split; [f_equal; ua|]. split; [f_equal; ua|]. split; [f_equal; ua|]. split; [f_equal; ua|].
  split; [ua|]. split; [f_equal; ua|]. split; [ua|]. split; [ua|]. split; [ua|].
  assert (U48 : u_at (ntc_bytes kind st old why cnt rt) 48 8 = 0) by ua.
  rewrite U48. split; [apply bytes_at_nil; lia|]. split; [unfold off_world; cbn; unfold W_BASE_PLAIN; lia|].
  split; [unfold off_window; cbn; lia|]. ua.
Qed.

(* the RELRO tables and the current heap frame, from the entry memory to the memory of a callee in tick's frame *)
Lemma relro_move : forall m0 m (sp : word), relro_img m0 ->
  munch [(bv_unsigned sp - 2160, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m0 m ->
  W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 2160 -> relro_img m.
Proof.
  intros m0 m sp RL MU WO i Hi. pose proof (RL i Hi) as E. unfold mrd in *. rewrite MU; [exact E|].
  unfold RELRO_LEN, RELRO_BASE, W_BASE_PLAIN, W_LEN in *. rewrite wa_unsigned by lia. cbn [outside]. lia.
Qed.

Lemma tf_move : forall m0 m (sp : word) K TF, tframe_at m0 sp 2160 TF ->
  munch [(bv_unsigned sp - 2160, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m0 m ->
  W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 2160 -> 0 <= K <= 592 ->
  tframe_at m (Z_to_bv 64 (bv_unsigned sp + -1568)) K TF.
Proof.
  intros m0 m sp K [fr|] TFm MU WO HK; [|exact I].
  destruct TFm as (Hp & Hb & Hw & Hwin). pose proof (bytes_at_bound _ _ _ _ Hb) as Bb.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold W_BASE_PLAIN, W_LEN in WO.
  split; [exact Hp|]. split; [|split; [exact Hw|]].
  - eapply bytes_at_transport; [exact Hb | exact MU |]. cbn [disjoint_from].
    unfold off_world, off_window in *. lia.
  - unfold off_window in *. rewrite unsigned_lit by lia. lia.
Qed.

Lemma swrap32_mod : forall x, bv_swrap 32 (x mod 2^32) = bv_swrap 32 x.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  f_equal. rewrite Zplus_mod, Zmod_mod, <- Zplus_mod. reflexivity.
Qed.
Lemma s32_mod32 : forall x, bv_swrap 32 x mod 2^32 = x mod 2^32.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.
Lemma s32_mod16 : forall x, bv_swrap 32 x mod 2^16 = x mod 2^16.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

(* two byte lists with the same values are equal (a closed computation compares them by their values) *)
Lemma bytes_eq_vals : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] E; cbn in E; try discriminate; [reflexivity|].
  injection E as Ea El. f_equal; [apply bv_eq; exact Ea | apply IH; exact El].
Qed.

Lemma rwc_join : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m B cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (Ha & Hn & Hw1)] -> [[W2 B2] (Hb & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma rwc_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ Hb] _]. exact Hb. Qed.

(* ---- the ACK_LOST arm (:436-441) ---- *)
Definition ackl_w (B : list byte) : list byte :=
  let B := set_S_inflight B 0 in set_S_stats_ack_lost B (u64 (S_stats_ack_lost B + 1)).
Definition ackl_n (B : list byte) : ntc :=
  let B := ackl_w B in
  Ntc DIGINET_N_ACK_LOST (S_state B) 0 0 (S_inflight_counter B) (u16 (S_inflight_retries B)) 0 0 None [] 0.

(* 0x16f48 .. 0x16fb0 of the keepalive branch, then the return *)
Ltac ka_rest SEND B now sp lo Hc HM KA S1 S2 Hsp L GF MI :=
  do 4 step;
  lazymatch goal with W : wmem_at _ _ _ ?X |- _ =>
    let EW := fresh "EW" in
    assert (EW : X = tick_ka_w B now)
      by (rewrite ka_world by assumption; change (S_cfg_keepalive_ms B) with (u_at B 1672 4);
          change (S_next_keepalive_us B) with (u_at B 1832 8); rewrite Hc; reflexivity);
    rewrite EW in W; clear EW
  end;
  let S1a := fresh "S1a" in let S1b := fresh "S1b" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  destruct (stk_split rsegs m1 lo (bv_unsigned sp + -1568) (bv_unsigned sp + -1536) S1) as [S1a S1b]; [lia|]; clear S1;
  do 7 step;
  eapply evt_cut;
  [ eapply SEND with (body := [b8 0]) (ncmds := 1) (now := now) (bodyp := bv_unsigned sp + -1536) (lo := lo)
        (TF := _) (B := tick_ka_w B now);
    [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia
    | let KB := fresh "KB" in pose proof KA as [[_ KB] _]; exact KB
    | unfold arg_blk, off_world, off_window; rewrite Hsp; cbn [length Z.of_nat Pos.of_succ_nat]; lia
    | assumption
    | rewrite ka_world by assumption;
      let L1 := fresh "L1" in let G1 := fresh "G1" in let L2 := fresh "L2" in let G2 := fresh "G2" in
      destruct (gf_put B 1832 8 (if now <? (S_cfg_keepalive_ms B * 1000 + S_next_keepalive_us B) mod 2 ^ 64
                 then S_cfg_keepalive_ms B * 1000 + S_next_keepalive_us B else S_cfg_keepalive_ms B * 1000 + now))
        as [L1 G1]; [exact L | uoff; lia | uoff; lia | uoff; lia |];
      destruct (gf_put _ 19864 8 (S_stats_tx_keepalives B + 1) L1) as [L2 G2]; [uoff; lia | uoff; lia | uoff; lia |];
      change A_S_next_keepalive_us with 1832; change A_S_stats_tx_keepalives with 19864; rewrite G2, G1; exact GF
    | exact HM
    | rewrite Hsp; Z.div_mod_to_equations; lia
    | rewrite Hsp; exact S1a
    | rewrite Hsp; lia
    | unfold w_off_stack; rewrite Hsp; lia
    | exact MI ]
  | let ms' := fresh "ms'" in let m2 := fresh "m" in
    let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MI2 := fresh "MI" in let ST2 := fresh "ST" in
    let WM2 := fresh "WM" in let GF2 := fresh "GF" in let Eq := fresh "Eq" in
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2 & WM2 & GF2);
    subst ms'; rewrite Hsp in MUc, ST2; clear S1a;
    lazymatch goal with W : wmem_at _ _ m1 _ |- _ => clear W end;
    transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc MI; try clear m1;
    rewrite (ret_pc_even 94128) by (first [lia | reflexivity]);
    step;
    let S3 := fresh "S3" in let ST4 := fresh "ST" in
    pose proof (stk_merge rsegs m2 lo (bv_unsigned sp + -1568) (bv_unsigned sp + -1536) ST2 S1b ltac:(lia)) as S3;
    pose proof (stk_join m2 lo (bv_unsigned sp + -48) (bv_unsigned sp + -1536) (bv_unsigned sp + -1535) _ S3 KA
      ltac:(cbn; lia) S2 ltac:(lia) ltac:(lia)) as ST4;
    eapply ret_ok; unfold tick_inv; inv_split ] end.

Lemma ka_ok : send_data_contract ->
  forall (ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo : Z) (B B' : list byte) (now r : Z)
    (TF : option tframe),
  tick_inv sp lo m0 m B ra0 v0 v1 v2 v3 v4 -> 0 <= now < 2^64 ->
  tick_ka_m timg_plain TF B now = Some (B', r) ->
  evt rsegs (tick_post ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' r)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp t0 t1 t2 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) (Z_to_bv 64 (u_at B 1832 8)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f2c) fc None m (seg_rom rsegs)).
Proof.
  intros SEND. intros until TF. intros I Hnow HM. inv_intro I.
  unfold send_data_contract, send_data_ENTRY, send_data_FRAME in SEND.
  wk_facts. sp_facts sp. pose proof ST as (Hlo & _ & _).
  assert (Eo : OFF_g_s = 1648) by reflexivity.
  pose proof (wm_len _ _ _ _ WM) as L.
  pose proof (u_at_range B 1672 4) as Rk. change (2 ^ (8 * Z.of_nat 4)) with (2^32) in Rk.
  destruct (stk_cut m lo (bv_unsigned sp + -48) (bv_unsigned sp + -1536) 1 ST) as (S1 & (jk & KA) & S2); [lia|lia|].
  replace (bv_unsigned sp + -1536 + Z.of_nat 1) with (bv_unsigned sp + -1535) in S2 by lia. clear ST.
  do 5 step.
  rewrite (unsigned_lit (u_at B 1672 4)) by lia.
  step.
  rewrite br_ltu, (Z.mod_small now) by lia.
  destruct (now <? (u_at B 1672 4 * 1000 + u_at B 1832 8) mod 2^64) eqn:Hc; cbv iota.
  - ka_rest SEND B now sp lo Hc HM KA S1 S2 Hsp L GF MI.
  - step. ka_rest SEND B now sp lo Hc HM KA S1 S2 Hsp L GF MI.
Qed.

(* the take path's stack pieces back into one stack region below the saved registers *)
Ltac take_join sp lo Sv Sw Sy S0b JB2 JL2 JH2 ST2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let T1 := fresh "T1" in let T2 := fresh "T2" in let T3 := fresh "T3" in let T4 := fresh "ST" in
    pose proof (stk_join mm (bv_unsigned sp + -1536) (bv_unsigned sp + -48) (bv_unsigned sp + -1536)
                  (bv_unsigned sp + -52) _ Sv JB2 ltac:(cbn; lia) Sw ltac:(lia) ltac:(lia)) as T1;
    pose proof (stk_join mm (bv_unsigned sp + -1544) (bv_unsigned sp + -48) (bv_unsigned sp + -1544)
                  (bv_unsigned sp + -1536) _ Sy JL2 ltac:(cbn; lia) T1 ltac:(lia) ltac:(lia)) as T2;
    pose proof (stk_merge rsegs mm lo (bv_unsigned sp + -1568) (bv_unsigned sp + -1548) ST2 S0b ltac:(lia)) as T3;
    pose proof (stk_join mm lo (bv_unsigned sp + -48) (bv_unsigned sp + -1548)
                  (bv_unsigned sp + -1544) _ T3 JH2 ltac:(cbn; lia) T2 ltac:(lia) ltac:(lia)) as T4;
    clear T1 T2 T3
  end.

(* 0x16f9c .. 0x16fb0: send_data of the taken body, then the return *)
Ltac take_send SEND sp lo len n now X B2 HM HX Hsp S0b Sv Sw Sy JB2 JL2 JH2 ST2 GF2 :=
  do 5 step;
  let LX := fresh "LX" in let BX := fresh "BX" in
  pose proof (rw_cells_CB_bytes _ _ _ _ JB2) as [BX LX];
  rewrite <- HX in HM;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
  let S0c := fresh "S0c" in let S0d := fresh "S0d" in
  destruct (stk_split rsegs m2 lo (bv_unsigned sp + -1568) (bv_unsigned sp + -1568) ST2) as [S0c S0d]; [lia|];
  eapply evt_cut;
  [ eapply SEND with (body := firstn (Z.to_nat len) X) (ncmds := n) (now := now) (bodyp := bv_unsigned sp + -1536)
        (lo := lo) (B := B2);
    [ reflexivity | reflexivity
    | rewrite length_firstn, LX; f_equal; lia
    | reflexivity | reflexivity | lia | lia
    | apply bytes_at_firstn; exact BX
    | unfold arg_blk, off_world, off_window; rewrite length_firstn, LX; rewrite Hsp; lia
    | assumption
    | assumption
    | exact HM
    | rewrite Hsp; Z.div_mod_to_equations; lia
    | rewrite Hsp; exact ST2
    | rewrite Hsp; lia
    | unfold w_off_stack; rewrite Hsp; lia
    | assumption ]
  | let ms' := fresh "ms'" in let m3 := fresh "m" in
    let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MI3 := fresh "MI" in let ST3 := fresh "ST" in
    let WM3 := fresh "WM" in let GF3 := fresh "GF" in let Eq := fresh "Eq" in
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3 & WM3 & GF3);
    subst ms'; rewrite Hsp in MUc, ST3; clear S0c S0d ST2;
    lazymatch goal with W : wmem_at _ _ m2 _ |- _ => clear W end;
    lazymatch goal with W : mem_inv _ m2 |- _ => clear W end;
    transport_after_call rsegs m2 m3 MUc WMc; clear MUc WMc; try clear m2;
    rewrite (ret_pc_even 94128) by (first [lia | reflexivity]);
    step;
    take_join sp lo Sv Sw Sy S0b JB2 JL2 JH2 ST3;
    eapply ret_ok; unfold tick_inv; inv_split ]
  end.

Lemma take_ok : take_contract -> send_data_contract ->
  forall (ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo : Z) (B B' : list byte) (allow now r : Z)
    (TF : option tframe),
  tick_inv sp lo m0 m B ra0 v0 v1 v2 v3 v4 -> 0 <= now < 2^64 -> 0 <= allow <= 1 ->
  tick_take_m timg_plain TF B allow now = Some (B', r) ->
  evt rsegs (tick_post ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' r)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp t0 t1 t2 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) a0 a1 a2 (Z_to_bv 64 allow) a4 a5 a6 a7
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f6c) fc None m (seg_rom rsegs)).
Proof.
  intros TAKE SEND. intros until TF. intros I Hnow Hal HM. inv_intro I.
  unfold take_contract, take_ENTRY, take_FRAME in TAKE.
  unfold send_data_contract, send_data_ENTRY, send_data_FRAME in SEND.
  wk_facts. sp_facts sp. pose proof ST as (Hlo & _ & _).
  assert (Eo : OFF_g_s = 1648) by reflexivity.
  unfold tick_take_m in HM.
  destruct (take_m B allow) as [[B1 [[[body len] hd] n]]|] eqn:HT; [|discriminate HM].
  pose proof (take_m_out _ _ _ _ _ _ _ HT) as (Rn & Rl & Rh).
  destruct (stk_cut m lo (bv_unsigned sp + -48) (bv_unsigned sp + -1548) 4 ST) as (S0 & (jh & JH) & Sx); [lia|lia|].
  replace (bv_unsigned sp + -1548 + Z.of_nat 4) with (bv_unsigned sp + -1544) in Sx by lia. clear ST.
  destruct (stk_cut m (bv_unsigned sp + -1544) (bv_unsigned sp + -48) (bv_unsigned sp + -1544) 8 Sx)
    as (Sy & (jl & JL) & Sz); [lia|lia|].
  replace (bv_unsigned sp + -1544 + Z.of_nat 8) with (bv_unsigned sp + -1536) in Sz by lia. clear Sx.
  destruct (stk_cut m (bv_unsigned sp + -1536) (bv_unsigned sp + -48) (bv_unsigned sp + -1536) 1484 Sz)
    as (Sv & (jb & JB) & Sw); [lia|lia|].
  replace (bv_unsigned sp + -1536 + Z.of_nat 1484) with (bv_unsigned sp + -52) in Sw by lia. clear Sz.
  destruct (stk_split rsegs m lo (bv_unsigned sp + -1568) (bv_unsigned sp + -1548) S0) as [S0a S0b]; [lia|]. clear S0.
  do 5 step.
  eapply evt_cut.
  { eapply TAKE with (bp := bv_unsigned sp + -1536) (blp := bv_unsigned sp + -1544) (hdp := bv_unsigned sp + -1548)
      (allow := allow) (lo := lo) (B := B) (B' := B1) (body := body) (len := len) (hd := hd) (taken := n).
    1-5: reflexivity.
    - lia.
    - exact JB.
    - unfold arg_blk, off_world, off_window; rewrite Hsp; lia.
    - exact JL.
    - unfold arg_blk, off_world, off_window; rewrite Hsp; lia.
    - Z.div_mod_to_equations; lia.
    - exact JH.
    - unfold arg_blk, off_world, off_window; rewrite Hsp; lia.
    - Z.div_mod_to_equations; lia.
    - unfold blk_sep; lia.
    - unfold blk_sep; lia.
    - unfold blk_sep; lia.
    - exact WM.
    - exact GF.
    - exact HT.
    - rewrite Hsp; Z.div_mod_to_equations; lia.
    - rewrite Hsp; exact S0a.
    - rewrite Hsp; lia.
    - unfold w_off_stack; rewrite Hsp; lia.
    - exact MI. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & X & m2 & Eq & MUc & WMc & MI2 & ST2 & WM2 & GF2
              & JB2 & HX & JL2 & JH2).
  subst ms'. rewrite Hsp in MUc, ST2. clear WM S0a.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI. try clear m.
  pose proof (wm_len _ _ _ _ WM2) as L1.
  rewrite (ret_pc_even 94080) by (first [lia | reflexivity]).
  apply cb_c4 in JH2. apply cb_c8 in JL2.
  step.
  rewrite br_eqb_s by (pose proof (swrap32_range n); lia).
  rewrite swrap32_eq0 by lia.
  destruct (n =? 0) eqn:Hn0; cbv iota.
  - (* nothing taken: return 0 *)
    injection HM as <- <-. apply Z.eqb_eq in Hn0. subst n.
    take_join sp lo Sv Sw Sy S0b JB2 JL2 JH2 ST2.
    eapply ret_ok. unfold tick_inv. inv_split.
  - apply Z.eqb_neq in Hn0.
    do 2 step.
    unfold sx32. rewrite (unsigned_lit hd), (swrap32_id hd) by lia.
    step.
    rewrite br_eqb_s by lia.
    destruct (hd =? 0) eqn:Hh; cbv iota.
    + take_send SEND sp lo len n now X B1 HM HX Hsp S0b Sv Sw Sy JB2 JL2 JH2 ST2 GF2.
    + do 3 step.
      lazymatch goal with W : wmem_at _ _ _ (upd (upd B1 1848 (put 8 now)) 1856 (put 4 1)) |- _ =>
        replace (upd (upd B1 1848 (put 8 now)) 1856 (put 4 1))
          with (set_S_last_display_us (set_S_display_sent B1 1) now) in W
          by (unfold set_S_last_display_us, set_S_display_sent; apply upd_upd_comm; rewrite ?length_put; uoff; lia)
      end.
      assert (GF3 : g_fail_next (set_S_last_display_us (set_S_display_sent B1 1) now) <= 1).
      { unfold set_S_last_display_us, set_S_display_sent.
        destruct (gf_put B1 A_S_display_sent 4 1 L1) as [La Ga]; [uoff; lia | uoff; lia | uoff; lia |].
        destruct (gf_put _ A_S_last_display_us 8 now La) as [Lb Gb]; [uoff; lia | uoff; lia | uoff; lia |].
        rewrite Gb, Ga. exact GF2. }
      take_send SEND sp lo len n now X (set_S_last_display_us (set_S_display_sent B1 1) now) HM HX Hsp S0b Sv Sw Sy
        JB2 JL2 JH2 ST2 GF3.
Qed.

Lemma tail_ok : take_contract -> send_data_contract ->
  forall (ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo : Z) (B B' : list byte) (now r : Z)
    (TF : option tframe),
  tick_inv sp lo m0 m B ra0 v0 v1 v2 v3 v4 -> 0 <= now < 2^64 ->
  tick_tail_m timg_plain TF B now = Some (B', r) ->
  evt rsegs (tick_post ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' r)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp t0 t1 t2 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16ebc) fc None m (seg_rom rsegs)).
Proof.
  intros TAKE SEND. intros until TF. intros I Hnow HM. pose proof I as I0. inv_intro I.
  wk_facts. sp_facts sp.
  assert (Eo : OFF_g_s = 1648) by reflexivity.
  unfold tick_tail_m in HM.
  do 3 step.
  rewrite (br_eqb_s (s32_at B 1760) 2) by (pose proof (s32_range B 1760); lia).
  change (s32_at B 1760 =? 2) with (S_state B =? DIGINET_S_ONLINE).
  destruct (S_state B =? DIGINET_S_ONLINE) eqn:Hst; nb; cbv iota; cbn [negb orb] in HM.
  2: { step. injection HM as <- <-. eapply ret_ok. exact I0. }
  do 2 step.
  rewrite (br_eqb_s (s32_at B 1860) 0) by (pose proof (s32_range B 1860); lia).
  change (s32_at B 1860 =? 0) with (S_inflight B =? 0).
  destruct (S_inflight B =? 0) eqn:Hin; nb; cbv iota; cbn [negb orb] in HM.
  2: { step. injection HM as <- <-. eapply ret_ok. exact I0. }
  do 2 step.
  rewrite (br_ltu_u now (u_at B 1840 8)) by (pose proof (u_at_range B 1840 8); cbn in *; lia).
  change (now <? u_at B 1840 8) with (now <? S_backoff_until_us B).
  destruct (now <? S_backoff_until_us B) eqn:Hbo; nb; cbv iota; cbn [negb orb] in HM.
  { step. injection HM as <- <-. eapply ret_ok. exact I0. }
  do 2 step.
  rewrite (br_ltu_u now (u_at B 1832 8)) by (pose proof (u_at_range B 1832 8); cbn in *; lia).
  change (now <? u_at B 1832 8) with (now <? S_next_keepalive_us B).
  rewrite <- Z.leb_antisym.
  destruct (S_next_keepalive_us B <=? now) eqn:Hka; cbv iota; cbn iota in HM.
  { eapply ka_ok; [exact SEND | exact I0 | exact Hnow | exact HM]. }
  do 2 step.
  rewrite (br_eqb_s (s32_at B 19792) 0) by (pose proof (s32_range B 19792); lia).
  rewrite s32_eq0. change (u_at B 19792 4 =? 0) with (S_queued B =? 0).
  destruct (S_queued B =? 0) eqn:Hq; cbv iota; cbn iota in HM.
  { injection HM as <- <-.
    replace (s32_at B 19792) with 0 by (unfold s32_at; apply Z.eqb_eq in Hq; change (u_at B 19792 4) with (S_queued B);
                                        rewrite Hq; reflexivity).
    eapply ret_ok. exact I0. }
  do 2 step.
  rewrite (br_eqb_s (s32_at B 1856) 0) by (pose proof (s32_range B 1856); lia).
  change (s32_at B 1856 =? 0) with (S_display_sent B =? 0).
  destruct (S_display_sent B =? 0) eqn:Hds; cbv iota; cbn [orb] in HM.
  { step. eapply take_ok; [exact TAKE | exact SEND | exact I0 | exact Hnow | lia | exact HM]. }
  do 6 step.
  rewrite allow_bin by (first [lia | apply (u_at_range B 1848 8) | (pose proof (u_at_range B 1696 4); cbn in *; lia)]).
  eapply take_ok; [exact TAKE | exact SEND | exact I0 | exact Hnow | unfold int_of_bool; match goal with |- context [if ?c then _ else _] => destruct c end; lia | exact HM].
Qed.

Lemma ackl_ok : memset_contract -> notice_contract -> take_contract -> send_data_contract ->
  forall (ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo : Z) (B B3 B' : list byte) (now r : Z)
    (TF : option tframe),
  tick_inv sp lo m0 m B ra0 v0 v1 v2 v3 v4 -> 0 <= now < 2^64 ->
  tframe_at m0 sp 2160 TF -> relro_img m0 ->
  call_notify timg_plain TF (ackl_w B) (ackl_n B) = Some (B3, tt) ->
  tick_tail_m timg_plain TF B3 now = Some (B', r) ->
  evt rsegs (tick_post ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' r)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp t0 t1 t2 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) (Z_to_bv 64 (s32_at B 1680)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) (Z_to_bv 64 (s32_at B 1760)) (Z_to_bv 64 (s32_at B 3396))
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16e64) fc None m (seg_rom rsegs)).
Proof.
  intros MSET NOTICE TAKE SEND. intros until TF. intros I Hnow TFm RL HN HT. inv_intro I.
  unfold memset_contract, MEMSET in MSET. unfold notice_contract, notice_ENTRY, notice_FRAME in NOTICE.
  wk_facts. sp_facts sp. pose proof ST as (Hlo & _ & _).
  assert (Eo : OFF_g_s = 1648) by reflexivity.
  pose proof (wm_len _ _ _ _ WM) as L.
  unfold call_notify in HN.
  destruct (S_notify (ackl_w B) =? ti_notice timg_plain) eqn:Hnf; [|discriminate HN].
  apply Z.eqb_eq in Hnf. change (ti_notice timg_plain) with 0x149e4 in Hnf.
  assert (LW : length (ackl_w B) = Z.to_nat W_LEN).
  { unfold ackl_w, set_S_stats_ack_lost, set_S_inflight. apply lenW; [apply lenW|..]; rewrite ?length_put; uoff; lia. }
  pose proof (notice_m_fail_next _ _ _ _ _ LW HN) as GF3.
  assert (GFW : g_fail_next (ackl_w B) = g_fail_next B).
  { unfold ackl_w, set_S_stats_ack_lost, set_S_inflight.
    destruct (gf_put B A_S_inflight 4 0 L) as [La Ga]; [uoff; lia | uoff; lia | uoff; lia |].
    destruct (gf_put _ A_S_stats_ack_lost 8 (u64 (S_stats_ack_lost (upd B A_S_inflight (put 4 0)) + 1)) La)
      as [Lb Gb]; [uoff; lia | uoff; lia | uoff; lia |].
    rewrite Gb, Ga. reflexivity. }
  destruct (stk_cut m lo (bv_unsigned sp + -48) (bv_unsigned sp + -1536) 8 ST) as (S0 & (j1 & K1) & Sx); [lia|lia|].
  replace (bv_unsigned sp + -1536 + Z.of_nat 8) with (bv_unsigned sp + -1528) in Sx by lia. clear ST.
  destruct (stk_cut m (bv_unsigned sp + -1528) (bv_unsigned sp + -48) (bv_unsigned sp + -1528) 64 Sx)
    as (Sy & (j2 & K2) & Sz); [lia|lia|].
  replace (bv_unsigned sp + -1528 + Z.of_nat 64) with (bv_unsigned sp + -1464) in Sz by lia. clear Sx.
  do 4 step.
  lazymatch goal with W : wmem_at _ _ _ (upd (upd B 1860 (put 4 0)) 19888 (put 8 (u_at B 19888 8 + 1))) |- _ =>
    replace (upd (upd B 1860 (put 4 0)) 19888 (put 8 (u_at B 19888 8 + 1))) with (ackl_w B) in W
  end.
  2: { unfold ackl_w, set_S_stats_ack_lost, set_S_inflight, S_stats_ack_lost, u64.
       rewrite (u_at_upd_out B _ A_S_inflight A_S_stats_ack_lost 8) by (rewrite ?length_put, ?L; uoff; lia).
       f_equal. apply put8_eq. apply Zmod_mod. }
  do 4 step.
  eapply evt_cut.
  { eapply MSET. rewrite !unsigned_lit by lia. exact K2. exact MI. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & K2').
  subst ms'. rewrite !unsigned_lit in MUc, K2' by lia.
  change (Z.to_nat 64) with 64%nat in K2'. change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in K2'.
  clear K2.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI. try clear m.
  rewrite (ret_pc_even 93828) by (first [lia | reflexivity]).
  do 9 step.
  change (u_at (ackl_w B) 1744 8) with (S_notify (ackl_w B)). rewrite Hnf.
  step.
  destruct (stk_split rsegs m1 lo (bv_unsigned sp + -1568) (bv_unsigned sp + -1536) S0) as [S0a S0b]; [lia|].
  clear S0.
  pose proof (rwc_bytes _ _ _ (rwc_join m1 (bv_unsigned sp + -1536) (bv_unsigned sp + -1528) _ _ K1 ltac:(cbn; lia) K2')) as NBb.
  lazymatch type of NBb with bytes_at _ _ _ ?NB =>
    replace NB with (ntc_bytes 5 (s32_at B 1760) 0 0 (s32_at (ackl_w B) 3392) (s32_at B 3396)) in NBb
  end.
  2: { cbn [cells_bytes cbytes app]. rewrite !le4_put, le2_put. unfold ntc_bytes.
       change (firstn 56 (repeat (Z_to_bv 8 0) 64)) with (put 4 0 ++ put 4 0 ++ repeat (Z_to_bv 8 0) 48).
       change (skipn 2 (skipn 60 (repeat (Z_to_bv 8 0) 64))) with (repeat (Z_to_bv 8 0) 2).
       rewrite !app_nil_r, <- !app_assoc. reflexivity. }
  pose proof (ntc_bytes_at m1 (bv_unsigned sp + -1536) (Z_to_bv 64 (bv_unsigned sp + -1568)) 48 _ _ _ _ _ _ NBb)
    as NT.
  lazymatch type of NT with _ -> _ -> _ -> _ -> _ -> ntc_at _ _ ?n _ _ =>
    replace n with (ackl_n B) in NT
  end.
  2: { unfold ackl_n. f_equal.
       - rewrite swrap32_mod, swrap32_id by (pose proof (s32_range B 1760); lia).
         unfold ackl_w, S_state, set_S_stats_ack_lost, set_S_inflight, s32_at.
         rewrite !(u_at_upd_out) by wside L. reflexivity.
       - unfold s32_at. rewrite s32_mod32, Z.mod_small by (apply (u_at_range _ _ 4)). reflexivity.
       - unfold s32_at. rewrite s32_mod16. unfold u16, ackl_w, S_inflight_retries, set_S_stats_ack_lost, set_S_inflight.
         rewrite !(u_at_upd_out) by wside L. reflexivity. }
  eapply evt_cut.
  { eapply NOTICE with (p := bv_unsigned sp + -1536) (n := ackl_n B) (Fr := TF) (B := ackl_w B) (B' := B3) (lo := lo).
    - reflexivity.
    - apply NT; unfold off_world, off_window; rewrite ?Hsp; first [lia | Z.div_mod_to_equations; lia].
    - apply (tf_move m0 m1 sp 48 TF TFm MU WO). lia.
    - apply (relro_move m0 m1 sp RL MU WO).
    - exact WMw0.
    - exact HN.
    - rewrite Hsp; Z.div_mod_to_equations; lia.
    - rewrite Hsp; exact S0a.
    - rewrite Hsp; lia.
    - unfold w_off_stack; rewrite Hsp; lia.
    - exact MI2. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3 & WM3).
  subst ms'. rewrite Hsp in MUc, ST3. clear WMw0 S0a NT NBb.
  transport_after_call rsegs m1 m3 MUc WMc. clear MUc WMc MI2. try clear m1.
  rewrite (ret_pc_even 93868) by (first [lia | reflexivity]).
  step.
  assert (GFB3 : g_fail_next B3 <= 1) by (rewrite GF3, GFW; exact GF).
  pose proof (stk_join m3 (bv_unsigned sp + -1528) (bv_unsigned sp + -48) (bv_unsigned sp + -1528)
                (bv_unsigned sp + -1464) _ Sy K2' ltac:(cbn; lia) Sz ltac:(lia) ltac:(lia)) as T1.
  pose proof (stk_merge rsegs m3 lo (bv_unsigned sp + -1568) (bv_unsigned sp + -1536) ST3 S0b ltac:(lia)) as T2.
  pose proof (stk_join m3 lo (bv_unsigned sp + -48) (bv_unsigned sp + -1536)
                (bv_unsigned sp + -1528) _ T2 K1 ltac:(cbn; lia) T1 ltac:(lia) ltac:(lia)) as T3.
  eapply tail_ok; [exact TAKE | exact SEND | | exact Hnow | exact HT].
  unfold tick_inv. inv_split.
Qed.

(* ---- retransmit (:403-412) ---- *)
Definition rex_w (B : list byte) (now : Z) : list byte :=
  let B := set_S_inflight_retries B (u32 (S_inflight_retries B + 1)) in
  let retry := u16 (S_inflight_retries B) in
  let B := upd B (A_S_inflight_frame + DIGINET_ETH_HDR_LEN + 12) (put 1 (u8 (Z.shiftr retry 8))) in
  let B := upd B (A_S_inflight_frame + DIGINET_ETH_HDR_LEN + 13) (put 1 (u8 retry)) in
  let B := set_S_inflight_sent_us B now in
  set_S_stats_tx_retransmits B (u64 (S_stats_tx_retransmits B + 1)).

Lemma put_eq : forall n x y, (n <= 8)%nat -> x mod 2^(8 * Z.of_nat n) = y mod 2^(8 * Z.of_nat n) -> put n x = put n y.
Proof.
  intros n x y Hn E. unfold put.
  rewrite <- (Z_to_le_bytes_mod n x (8 * Z.of_nat n)), <- (Z_to_le_bytes_mod n y (8 * Z.of_nat n)) by lia.
  rewrite E. reflexivity.
Qed.

Lemma rex_world : forall B now, length B = Z.to_nat W_LEN -> 0 <= now < 2^64 ->
  rex_w B now =
  upd (upd (upd (upd (upd B 19880 (put 8 (u_at B 19880 8 + 1))) 1890
                   (put 1 (Z.shiftr (bv_unsigned (Z_to_bv 64 (s32_at B 3396 + 1))) 8)))
              1891 (put 1 (s32_at B 3396 + 1)))
         3396 (put 4 (s32_at B 3396 + 1)))
    3400 (put 8 now).
Proof.
  intros B now L Hn. unfold rex_w.
  unfold set_S_inflight_retries, S_inflight_retries, set_S_inflight_sent_us, set_S_stats_tx_retransmits,
    S_stats_tx_retransmits.
  rewrite (u_at_upd_put B A_S_inflight_retries 4) by wside L.
  rewrite !(u_at_upd_out) by wside L.
  change A_S_inflight_retries with 3396. change A_S_inflight_sent_us with 3400.
  change A_S_stats_tx_retransmits with 19880. change (A_S_inflight_frame + DIGINET_ETH_HDR_LEN + 12) with 1890.
  change (A_S_inflight_frame + DIGINET_ETH_HDR_LEN + 13) with 1891.
  set (r := u_at B 3396 4). pose proof (u_at_range B 3396 4) as Rr. fold r in Rr.
  change (2 ^ (8 * Z.of_nat 4)) with (2^32) in *.
  assert (Hs : (bv_swrap 32 r + 1) mod 2^32 = (r + 1) mod 2^32).
  { rewrite Zplus_mod, s32_mod32, <- Zplus_mod. reflexivity. }
  (* the values *)
  assert (E4 : put 4 (s32_at B 3396 + 1) = put 4 (u32 (r + 1))).
  { apply put_eq; [lia|]. change (2 ^ (8 * Z.of_nat 4)) with (2^32). unfold u32, s32_at. fold r.
    rewrite Hs, Zmod_mod. reflexivity. }
  assert (E1b : put 1 (s32_at B 3396 + 1) = put 1 (u8 (u16 (u32 (r + 1) mod 2 ^ 32)))).
  { apply put_eq; [lia|]. change (2 ^ (8 * Z.of_nat 1)) with (2^8). unfold u8, u16, u32, s32_at. fold r.
    rewrite !Zmod_mod. change 256 with (2^8). change 65536 with (2^16).
    rewrite (mod_mod8_of_modw ((r + 1) mod 2^32) 16), (mod_mod8_of_modw (r + 1) 32) by lia.
    rewrite <- (mod_mod8_of_modw (bv_swrap 32 r + 1) 32), Hs, (mod_mod8_of_modw (r + 1) 32) by lia. reflexivity. }
  assert (E1a : put 1 (Z.shiftr (bv_unsigned (Z_to_bv 64 (s32_at B 3396 + 1))) 8)
                = put 1 (u8 (Z.shiftr (u16 (u32 (r + 1) mod 2 ^ 32)) 8))).
  { apply put_eq; [lia|]. change (2 ^ (8 * Z.of_nat 1)) with (2^8). unfold u8, u16, u32, s32_at. fold r.
    rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?z) with (z mod 2^64).
    rewrite !Zmod_mod. change 256 with (2^8). change 65536 with (2^16).
    rewrite (shiftr_mod_mod8 (bv_swrap 32 r + 1) 8 64) by lia.
    rewrite <- (shiftr_mod_mod8 (bv_swrap 32 r + 1) 8 32) by lia. rewrite Hs.
    rewrite (shiftr_mod_mod8 ((r + 1) mod 2^32) 8 16) by lia. reflexivity. }
  assert (Es : put 8 (u_at B 19880 8 + 1) = put 8 (u64 (u_at B 19880 8 + 1))).
  { apply put8_eq. unfold u64. rewrite Zmod_mod. reflexivity. }
  rewrite E4, E1b, E1a, Es.
  lazymatch goal with |- upd (upd (upd (upd (upd ?B0 ?k1 ?v1) ?k2 ?v2) ?k3 ?v3) ?k4 ?v4) ?k5 ?v5 = _ =>
    rewrite (upd_upd_comm (upd (upd (upd B0 k1 v1) k2 v2) k3 v3) v4 v5 k4 k5) by wside L;
    rewrite (upd_upd_comm (upd (upd B0 k1 v1) k2 v2) v3 v5 k3 k5) by wside L;
    rewrite (upd_upd_comm (upd B0 k1 v1) v2 v5 k2 k5) by wside L;
    rewrite (upd_upd_comm B0 v1 v5 k1 k5) by wside L;
    rewrite (upd_upd_comm (upd B0 k5 v5) v1 v2 k1 k2) by wside L;
    rewrite (upd_upd_comm (upd (upd B0 k5 v5) k2 v2) v1 v3 k1 k3) by wside L
  end.
  reflexivity.
Qed.


Lemma rexmit_ok : io_send_contract -> take_contract -> send_data_contract ->
  forall (ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo : Z) (B B6 B' : list byte) (now r r' : Z)
    (TF : option tframe),
  tick_inv sp lo m0 m B ra0 v0 v1 v2 v3 v4 -> 0 <= now < 2^64 ->
  retransmit_m timg_plain TF B now = Some (B6, r) ->
  (if r <? 0 then Some (B6, r) else tick_tail_m timg_plain TF B6 now) = Some (B', r') ->
  evt rsegs (tick_post ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' r')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp t0 t1 t2 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) (Z_to_bv 64 (s32_at B 1680)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) s3 (Z_to_bv 64 (s32_at B 3396))
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16dd8) fc None m (seg_rom rsegs)).
Proof.
  intros IOS TAKE SEND. intros until TF. intros I Hnow HR HK. pose proof I as I0. inv_intro I.
  unfold io_send_contract, io_send_ENTRY, io_send_FRAME in IOS.
  wk_facts. sp_facts sp. pose proof ST as (Hlo & _ & _).
  assert (Eo : OFF_g_s = 1648) by reflexivity.
  pose proof (wm_len _ _ _ _ WM) as L.
  pose proof (u_at_range B 3384 8) as Rl. change (2 ^ (8 * Z.of_nat 8)) with (2^64) in Rl.
  assert (LW : length (rex_w B now) = Z.to_nat W_LEN) by (rewrite rex_world by assumption; wlen L).
  change (match inflight_bytes (rex_w B now) with
          | None => None | Some fr => send_raw_m timg_plain TF (rex_w B now) fr end = Some (B6, r)) in HR.
  unfold inflight_bytes in HR.
  assert (Lr : S_inflight_len (rex_w B now) = u_at B 3384 8).
  { rewrite rex_world by assumption. unfold S_inflight_len. rewrite !u_at_upd_out by wside L. reflexivity. }
  rewrite Lr in HR.
  destruct (1514 <? u_at B 3384 8) eqn:Hlen; [discriminate HR|]. apply Z.ltb_ge in Hlen.
  unfold send_raw_m, call_send in HR.
  destruct (S_io_send (rex_w B now) =? ti_io_send timg_plain) eqn:His; [|discriminate HR].
  apply Z.eqb_eq in His. change (ti_io_send timg_plain) with 0x144ec in His.
  assert (His' : u_at B 1720 8 = 0x144ec).
  { rewrite <- His. rewrite rex_world by assumption. unfold S_io_send. rewrite !u_at_upd_out by wside L. reflexivity. }
  destruct (io_send_m timg_plain (rex_w B now) (sub (rex_w B now) A_S_inflight_frame (Z.to_nat (u_at B 3384 8))))
    as [[B5 r5]|] eqn:HIO; [|discriminate HR].
  pose proof (io_send_m_fail_next _ _ _ _ _ HIO LW) as G5.
  pose proof (io_send_m_ret _ _ _ _ _ HIO) as R5. replace (- EIO) with (-5) in R5 by reflexivity.
  assert (GW : g_fail_next (rex_w B now) <= 1).
  { rewrite rex_world by assumption.
    destruct (gf_put B 19880 8 (u_at B 19880 8 + 1) L) as [L1 G1]; [uoff; lia | uoff; lia | uoff; lia |].
    destruct (gf_put _ 1890 1 (Z.shiftr (bv_unsigned (Z_to_bv 64 (s32_at B 3396 + 1))) 8) L1) as [L2 G2];
      [uoff; lia | uoff; lia | uoff; lia |].
    destruct (gf_put _ 1891 1 (s32_at B 3396 + 1) L2) as [L3 G3]; [uoff; lia | uoff; lia | uoff; lia |].
    destruct (gf_put _ 3396 4 (s32_at B 3396 + 1) L3) as [L4 G4]; [uoff; lia | uoff; lia | uoff; lia |].
    destruct (gf_put _ 3400 8 now L4) as [L5 G5']; [uoff; lia | uoff; lia | uoff; lia |].
    rewrite G5', G4, G3, G2, G1. exact GF. }
  destruct (stk_split rsegs m lo (bv_unsigned sp + -1568) (bv_unsigned sp + -48) ST) as [S0a S0b]; [lia|]. clear ST.
  do 13 step.
  lazymatch goal with W : wmem_at _ _ _ ?X |- _ =>
    replace X with (rex_w B now) in W by (rewrite rex_world by assumption; reflexivity) end.
  rewrite His'.
  step.
  eapply evt_cut.
  { eapply IOS with (p := W_BASE_PLAIN + OFF_g_s + 216)
      (frame := sub (rex_w B now) A_S_inflight_frame (Z.to_nat (u_at B 3384 8))) (B := rex_w B now) (B' := B5)
      (r := r5) (lo := lo).
    - reflexivity.
    - rewrite length_sub by (rewrite ?LW; uoff; lia). rewrite Z2Nat.id by lia. reflexivity.
    - uoff; lia.
    - apply (wm_src rsegs W_BASE_PLAIN _ (rex_w B now) A_S_inflight_frame); [assumption | uoff; lia | uoff; lia | uoff; lia].
    - right. rewrite length_sub by (rewrite ?LW; uoff; lia). uoff; unfold SZ_g_s. lia.
    - left. rewrite length_sub by (rewrite ?LW; uoff; lia). rewrite Hsp. uoff; lia.
    - exact GW.
    - rewrite Hsp; Z.div_mod_to_equations; lia.
    - rewrite Hsp; exact S0a.
    - rewrite Hsp; lia.
    - unfold w_off_stack; rewrite Hsp; lia.
    - assumption.
    - assumption.
    - exact HIO. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2 & WM2).
  subst ms'. rewrite Hsp in MUc, ST2. clear S0a.
  lazymatch goal with W : wmem_at _ _ _ (rex_w B now) |- _ => clear W end.
  lazymatch type of MUc with munch _ ?m1 _ =>
    lazymatch goal with W : mem_inv _ m1 |- _ => clear W end;
    transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc; try clear m1 end.
  rewrite (ret_pc_even 93712) by (first [lia | reflexivity]).
  pose proof (wm_len _ _ _ _ WM2) as L5.
  step.
  rewrite br_eqb_s by (destruct R5 as [-> | ->]; lia).
  destruct R5 as [-> | ->]; br_closed.
  - (* io_send returned 0: tx_frames++, on to :445 *)
    cbn [Z.eqb] in HR. injection HR as <- <-. cbn [Z.ltb Z.compare] in HK.
    do 3 step.
    lazymatch goal with W : wmem_at _ _ _ (upd B5 19840 (put 8 ?v)) |- _ =>
      replace (upd B5 19840 (put 8 v)) with (set_S_stats_tx_frames B5 (u64 (S_stats_tx_frames B5 + 1))) in W
        by (unfold set_S_stats_tx_frames, S_stats_tx_frames; change A_S_stats_tx_frames with 19840;
            f_equal; apply put8_eq; unfold u64; rewrite Zmod_mod; reflexivity)
    end.
    assert (GF6 : g_fail_next (set_S_stats_tx_frames B5 (u64 (S_stats_tx_frames B5 + 1))) <= 1).
    { unfold set_S_stats_tx_frames.
      destruct (gf_put B5 A_S_stats_tx_frames 8 (u64 (S_stats_tx_frames B5 + 1)) L5) as [La Ga];
        [uoff; lia | uoff; lia | uoff; lia |].
      rewrite Ga, G5. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_merge rsegs mm lo (bv_unsigned sp + -1568) (bv_unsigned sp + -48) ST2 S0b ltac:(lia)) as ST3 end.
    eapply tail_ok; [exact TAKE | exact SEND | | exact Hnow | exact HK].
    unfold tick_inv. inv_split.
  - (* io_send returned -EIO: return it *)
    cbn [Z.eqb] in HR. injection HR as <- <-. cbn [Z.ltb Z.compare] in HK. injection HK as <- <-.
    step. br_closed.
    step.
    pose proof (stk_merge rsegs m2 lo (bv_unsigned sp + -1568) (bv_unsigned sp + -48) ST2 S0b ltac:(lia)) as ST3.
    assert (GF6 : g_fail_next B5 <= 1) by lia.
    eapply ret_ok. unfold tick_inv. inv_split.
Qed.

(* ---- :430-443 and on (after the two timeouts of :421-427) ---- *)
Definition tick_rest_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * Z) :=
  let step :=
    if negb (S_inflight B =? 0) && (ms_m (S_cfg_ack_timeout_ms B) <=? u64 (now - S_inflight_sent_us B)) then
      if S_inflight_retries B <? S_cfg_max_retries B then
        match retransmit_m I F B now with
        | None => None
        | Some (B, r) => if r <? 0 then Some (inl (B, r)) else Some (inr B)
        end
      else
        match call_notify I F (ackl_w B) (ackl_n B) with
        | None => None
        | Some (B, _) => Some (inr B)
        end
    else Some (inr B) in
  match step with
  | None => None
  | Some (inl (B, r)) => Some (B, r)
  | Some (inr B) => tick_tail_m I F B now
  end.

(* a timeout test now - since >= v * 1000 (all uint64_t, v a uint32_t), as bltu computes it *)
Lemma tmo_bin : forall now x t, 0 <= now < 2^64 -> 0 <= x < 2^64 -> 0 <= t < 2^32 ->
  bv_ltu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 now) - bv_unsigned (Z_to_bv 64 x)))
         (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 t) * 1000))
  = negb (ms_m t <=? u64 (now - x)).
Proof.
  intros now x t Hn Hx Ht. rewrite (unsigned_lit now), (unsigned_lit x), (unsigned_lit t) by lia.
  rewrite br_ltu. unfold ms_m, u64. rewrite Z.leb_antisym, negb_involutive. reflexivity.
Qed.

(* bgeu / bltu of two sign-extended uint32_t loads compares the uint32_t values *)
Lemma ltu_s32 : forall B k k', bv_ltu (Z_to_bv 64 (s32_at B k)) (Z_to_bv 64 (s32_at B k')) = (u_at B k 4 <? u_at B k' 4).
Proof.
  intros B k k'. rewrite br_ltu. unfold s32_at.
  pose proof (u_at_range B k 4) as Ra. pose proof (u_at_range B k' 4) as Rb.
  change (2 ^ (8 * Z.of_nat 4)) with (2^32) in Ra, Rb.
  set (a := u_at B k 4) in *. set (b := u_at B k' 4) in *.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.ltb_spec a b) as [Lt|Ge]; [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

Lemma inflight_ok : io_send_contract -> memset_contract -> notice_contract -> take_contract -> send_data_contract ->
  forall (ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo : Z) (B B' : list byte) (now r : Z)
    (TF : option tframe),
  tick_inv sp lo m0 m B ra0 v0 v1 v2 v3 v4 -> 0 <= now < 2^64 ->
  tframe_at m0 sp 2160 TF -> relro_img m0 ->
  tick_rest_m timg_plain TF B now = Some (B', r) ->
  evt rsegs (tick_post ra0 sp gp tp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' r)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -1568)) gp tp t0 t1 t2 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (s32_at B 1760)) s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16da0) fc None m (seg_rom rsegs)).
Proof.
  intros IOS MSET NOTICE TAKE SEND. intros until TF. intros I Hnow TFm RL HM. pose proof I as I0. inv_intro I.
  wk_facts. sp_facts sp.
  assert (Eo : OFF_g_s = 1648) by reflexivity.
  pose proof (u_at_range B 1676 4) as R1. pose proof (u_at_range B 3400 8) as R2.
  change (2 ^ (8 * Z.of_nat 4)) with (2^32) in R1. change (2 ^ (8 * Z.of_nat 8)) with (2^64) in R2.
  unfold tick_rest_m in HM.
  do 5 step.
  rewrite (br_eqb_s (s32_at B 1860) 0) by (pose proof (s32_range B 1860); lia).
  change (s32_at B 1860 =? 0) with (S_inflight B =? 0).
  destruct (S_inflight B =? 0) eqn:Hin; cbv iota; cbn [negb andb] in HM.
  { eapply tail_ok; [exact TAKE | exact SEND | exact I0 | exact Hnow | exact HM]. }
  do 6 step.
  rewrite tmo_bin by lia.
  change (u_at B 1676 4) with (S_cfg_ack_timeout_ms B). change (u_at B 3400 8) with (S_inflight_sent_us B).
  destruct (ms_m (S_cfg_ack_timeout_ms B) <=? u64 (now - S_inflight_sent_us B)) eqn:Hto; nb; cbv iota.
  2: { eapply tail_ok; [exact TAKE | exact SEND | exact I0 | exact Hnow | exact HM]. }
  do 3 step.
  rewrite ltu_s32.
  change (u_at B 3396 4) with (S_inflight_retries B). change (u_at B 1680 4) with (S_cfg_max_retries B).
  destruct (S_inflight_retries B <? S_cfg_max_retries B) eqn:Hr; nb; cbv iota.
  - destruct (retransmit_m timg_plain TF B now) as [[B6 r6]|] eqn:HR; [|discriminate HM].
    eapply rexmit_ok; [exact IOS | exact TAKE | exact SEND | exact I0 | exact Hnow | exact HR |].
    destruct (r6 <? 0); exact HM.
  - destruct (call_notify timg_plain TF (ackl_w B) (ackl_n B)) as [[B3 []]|] eqn:HN; [|discriminate HM].
    eapply ackl_ok; [exact MSET | exact NOTICE | exact TAKE | exact SEND | exact I0 | exact Hnow | exact TFm
                      | exact RL | exact HN | exact HM].
Qed.

(* ---- session_lost (:160-165) from tick, with set_state (:79-86) inlined ---- *)
Definition lost_w1 (B : list byte) : list byte := set_S_desk_counter_valid (set_S_inflight B 0) 0.
Definition lost_w (B : list byte) : list byte := set_S_state (lost_w1 B) DIGINET_S_IDLE.
Definition lost_n (B : list byte) (why : Z) : ntc :=
  Ntc DIGINET_N_STATE DIGINET_S_IDLE (S_state B) why 0 0 0 0 None [] 0.

Lemma lost_m : forall I F B why, length B = Z.to_nat W_LEN -> S_state B <> DIGINET_S_IDLE ->
  session_lost_m I F B why = call_notify I F (lost_w B) (lost_n B why).
Proof.
  intros I F B why L Hs. unfold session_lost_m, set_state_m.
  assert (E : S_state (set_S_desk_counter_valid (set_S_inflight B 0) 0) = S_state B).
  { unfold S_state, set_S_desk_counter_valid, set_S_inflight, s32_at. rewrite !u_at_upd_out by wside L. reflexivity. }
  rewrite E. destruct (Z.eqb_spec (S_state B) DIGINET_S_IDLE) as [X|_]; [contradiction|]. reflexivity.
Qed.

(* ---- the dispatch of :418-427 ---- *)
Lemma tick_m_done : forall I F B now, S_state B = DIGINET_S_CLOSED \/ S_state B = DIGINET_S_IDLE ->
  diginet_session_tick_m I F B now = Some (B, DIGINET_OK).
Proof.
  intros I F B now [E|E]; unfold diginet_session_tick_m; rewrite E; reflexivity.
Qed.

Lemma tick_m_wake : forall I F B now, S_state B = DIGINET_S_WAKING ->
  (ms_m (S_cfg_wake_timeout_ms B) <=? u64 (now - S_wake_sent_us B)) = true ->
  diginet_session_tick_m I F B now =
  match session_lost_m I F B DIGINET_R_WAKE_TIMEOUT with None => None | Some (B, _) => Some (B, DIGINET_OK) end.
Proof. intros I F B now E C. unfold diginet_session_tick_m. rewrite E, C. reflexivity. Qed.

Lemma tick_m_silence : forall I F B now, S_state B = DIGINET_S_ONLINE ->
  (ms_m (S_cfg_offline_ms B) <=? u64 (now - S_last_rx_us B)) = true ->
  diginet_session_tick_m I F B now =
  match session_lost_m I F B DIGINET_R_SILENCE with None => None | Some (B, _) => Some (B, DIGINET_OK) end.
Proof. intros I F B now E C. unfold diginet_session_tick_m. rewrite E, C. reflexivity. Qed.

Lemma tick_m_rest : forall I F B now, S_state B <> DIGINET_S_CLOSED -> S_state B <> DIGINET_S_IDLE ->
  (S_state B = DIGINET_S_WAKING -> (ms_m (S_cfg_wake_timeout_ms B) <=? u64 (now - S_wake_sent_us B)) = false) ->
  (S_state B = DIGINET_S_ONLINE -> (ms_m (S_cfg_offline_ms B) <=? u64 (now - S_last_rx_us B)) = false) ->
  diginet_session_tick_m I F B now = tick_rest_m I F B now.
Proof.
  intros I F B now H3 H0 HW HO. unfold diginet_session_tick_m, tick_rest_m. cbv zeta.
  destruct (Z.eqb_spec (S_state B) DIGINET_S_CLOSED) as [X1|_]; [contradiction|].
  destruct (Z.eqb_spec (S_state B) DIGINET_S_IDLE) as [X2|_]; [contradiction|]. cbn [orb].
  destruct (Z.eqb_spec (S_state B) DIGINET_S_WAKING) as [X3|_]; [rewrite (HW X3)|]; cbn [andb].
  all: destruct (Z.eqb_spec (S_state B) DIGINET_S_ONLINE) as [X4|_]; [rewrite (HO X4)|]; cbn [andb].
  all: reflexivity.
Qed.

(* :421-423 / :425-427 from the first store of session_lost to the return: the two inlined set_state paths differ
   only in where their memset returns (MRET), how many instructions build the notice's old state / reason word
   before 0x16e4c (NB), and the reason (OLD, WHY) *)
Ltac lost_path MSET NOTICE HL TFm RL MRET NBN OLD WHY HM TF Hsp WO :=
  lazymatch goal with
  | WM : wmem_at _ _ _ ?B, L : length ?B = _, GF : g_fail_next ?B <= 1, ST : stk _ _ ?lo (bv_unsigned ?sp + -48),
    MU : munch _ ?m0 _ |- _ =>
  do 2 step;
  lazymatch goal with W : wmem_at _ _ _ (upd (upd B 1816 (put 4 0)) 1860 (put 4 0)) |- _ =>
    replace (upd (upd B 1816 (put 4 0)) 1860 (put 4 0)) with (lost_w1 B) in W
      by (unfold lost_w1, set_S_desk_counter_valid, set_S_inflight; apply upd_upd_comm; wside L) end;
  let S0 := fresh "S0" in let Sx := fresh "Sx" in let K1 := fresh "K1" in let j1 := fresh "j" in
  destruct (stk_cut _ lo (bv_unsigned sp + -48) (bv_unsigned sp + -1536) 16 ST) as (S0 & (j1 & K1) & Sx); [lia|lia|];
  replace (bv_unsigned sp + -1536 + Z.of_nat 16) with (bv_unsigned sp + -1520) in Sx by lia; clear ST;
  let Sy := fresh "Sy" in let Sz := fresh "Sz" in let K2 := fresh "K2" in let j2 := fresh "j" in
  destruct (stk_cut _ (bv_unsigned sp + -1520) (bv_unsigned sp + -48) (bv_unsigned sp + -1520) 56 Sx)
    as (Sy & (j2 & K2) & Sz); [lia|lia|];
  replace (bv_unsigned sp + -1520 + Z.of_nat 56) with (bv_unsigned sp + -1464) in Sz by lia; clear Sx;
  do 4 step;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  eapply evt_cut;
  [ eapply MSET; [ rewrite !unsigned_lit by lia; exact K2 | assumption ]
  | let ms' := fresh "ms'" in let PO := fresh "PO" in let m2 := fresh "m" in let Eq := fresh "Eq" in
    let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MI2 := fresh "MI" in let K2' := fresh "K2" in
    intros ms' PO; unfold memset_post in PO;
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & K2');
    subst ms'; rewrite !unsigned_lit in MUc, K2' by lia;
    change (Z.to_nat 56) with 56%nat in K2';
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in K2';
    clear K2;
    lazymatch goal with W : mem_inv _ m1 |- _ => clear W end;
    transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc; try clear m1;
    rewrite (ret_pc_even MRET) by (first [lia | reflexivity]);
    NBN;
    do 4 step;
    lazymatch goal with W : wmem_at _ _ _ (upd (lost_w1 B) 1760 (put 4 0)) |- _ =>
      change (upd (lost_w1 B) 1760 (put 4 0)) with (lost_w B) in W end;
    (* the model: the notice call *)
    rewrite (lost_m _ _ _ _ L) in HM by (rewrite HL; unfold DIGINET_S_IDLE; lia);
    unfold call_notify in HM;
    let Hnf := fresh "Hnf" in
    destruct (S_notify (lost_w B) =? ti_notice timg_plain) eqn:Hnf; [|cbn iota in HM; discriminate HM];
    apply Z.eqb_eq in Hnf; change (ti_notice timg_plain) with 0x149e4 in Hnf;
    let HN := fresh "HN" in let B3 := fresh "B" in
    destruct (notice_m timg_plain TF (lost_w B) (lost_n B WHY)) as [[B3 []]|] eqn:HN; cbn iota in HM;
      [|discriminate HM];
    injection HM as <- <-;
    replace (u_at (lost_w1 B) 1744 8) with 0x149e4
      by (rewrite <- Hnf; unfold lost_w, lost_w1, set_S_state, set_S_desk_counter_valid, set_S_inflight, S_notify;
          rewrite (u_at_upd_out _ _ A_S_state) by wside L; reflexivity);
    step;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
    let S0a := fresh "S0a" in let S0b := fresh "S0b" in
    destruct (stk_split rsegs m3 lo (bv_unsigned sp + -1568) (bv_unsigned sp + -1536) S0) as [S0a S0b]; [lia|];
    clear S0;
    let NBb := fresh "NBb" in
    lazymatch goal with K1' : rw_cells _ m3 (bv_unsigned sp + -1536) _, K2'' : rw_cells _ m3 (bv_unsigned sp + -1520) _ |- _ =>
      pose proof (rwc_bytes _ _ _ (rwc_join m3 (bv_unsigned sp + -1536) (bv_unsigned sp + -1520) _ _ K1'
                    ltac:(cbn; lia) K2'')) as NBb end;
    lazymatch type of NBb with bytes_at _ _ _ ?NB =>
      replace NB with (ntc_bytes 2 0 OLD WHY 0 0) in NBb by (apply bytes_eq_vals; vm_compute; reflexivity) end;
    let NT := fresh "NT" in
    pose proof (ntc_bytes_at m3 (bv_unsigned sp + -1536) (Z_to_bv 64 (bv_unsigned sp + -1568)) 48 _ _ _ _ _ _ NBb)
      as NT;
    lazymatch type of NT with _ -> _ -> _ -> _ -> _ -> ntc_at _ _ ?n _ _ =>
      replace n with (lost_n B WHY) in NT by (unfold lost_n; rewrite HL; vm_compute; reflexivity) end;
    eapply evt_cut;
    [ eapply NOTICE with (p := bv_unsigned sp + -1536) (n := lost_n B WHY) (Fr := TF) (B := lost_w B) (lo := lo);
      [ reflexivity
      | apply NT; unfold off_world, off_window; rewrite ?Hsp; first [lia | Z.div_mod_to_equations; lia]
      | apply (tf_move m0 m3 sp 48 TF TFm MU WO); lia
      | apply (relro_move m0 m3 sp RL MU WO)
      | assumption
      | exact HN
      | rewrite Hsp; Z.div_mod_to_equations; lia
      | rewrite Hsp; exact S0a
      | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia
      | assumption ]
    | let ms' := fresh "ms'" in let m4 := fresh "m" in let Eq := fresh "Eq" in
      let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MI4 := fresh "MI" in let ST4 := fresh "ST" in
      let WM4 := fresh "WM" in
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & Eq & MUc & WMc & MI4 & ST4 & WM4);
      subst ms'; rewrite Hsp in MUc, ST4; clear S0a NT NBb;
      lazymatch goal with W : wmem_at _ _ m3 _ |- _ => clear W end;
      lazymatch goal with W : mem_inv _ m3 |- _ => clear W end;
      transport_after_call rsegs m3 m4 MUc WMc; clear MUc WMc; try clear m3;
      rewrite (ret_pc_even 93792) by (first [lia | reflexivity]);
      do 2 step;
      let LW := fresh "LW" in
      assert (LW : length (lost_w B) = Z.to_nat W_LEN)
        by (unfold lost_w, lost_w1, set_S_state, set_S_desk_counter_valid, set_S_inflight; wlen L);
      let GF4 := fresh "GF" in
      assert (GF4 : g_fail_next B3 <= 1);
      [ rewrite (notice_m_fail_next _ _ _ _ _ LW HN);
        unfold lost_w, lost_w1, set_S_state, set_S_desk_counter_valid, set_S_inflight;
        let L1 := fresh "L" in let G1 := fresh "G" in let L2 := fresh "L" in let G2 := fresh "G" in
        let L3 := fresh "L" in let G3 := fresh "G" in
        destruct (gf_put B A_S_inflight 4 0 L) as [L1 G1]; [uoff; lia | uoff; lia | uoff; lia |];
        destruct (gf_put _ A_S_desk_counter_valid 4 0 L1) as [L2 G2]; [uoff; lia | uoff; lia | uoff; lia |];
        destruct (gf_put _ A_S_state 4 DIGINET_S_IDLE L2) as [L3 G3]; [uoff; lia | uoff; lia | uoff; lia |];
        rewrite G3, G2, G1; exact GF
      | ];
      let T1 := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in
      lazymatch goal with K1' : rw_cells _ _ (bv_unsigned sp + -1536) _, K2'' : rw_cells _ _ (bv_unsigned sp + -1520) _,
                          ST4 : stk _ _ lo (bv_unsigned sp + -1568) |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m5 _) =>
        pose proof (stk_join m5 (bv_unsigned sp + -1520) (bv_unsigned sp + -48) (bv_unsigned sp + -1520)
                      (bv_unsigned sp + -1464) _ Sy K2'' ltac:(cbn; lia) Sz ltac:(lia) ltac:(lia)) as T1;
        pose proof (stk_merge rsegs m5 lo (bv_unsigned sp + -1568) (bv_unsigned sp + -1536) ST4 S0b ltac:(lia)) as T2;
        pose proof (stk_join m5 lo (bv_unsigned sp + -48) (bv_unsigned sp + -1536)
                      (bv_unsigned sp + -1520) _ T2 K1' ltac:(cbn; lia) T1 ltac:(lia) ltac:(lia)) as T3
        end
      end;
      eapply ret_ok; unfold tick_inv; inv_split ] end ] end
  end.

Theorem diginet_session_tick_holds :
  take_contract -> send_data_contract -> notice_contract -> io_send_contract -> memset_contract ->
  diginet_session_tick_contract.
Proof.
  intros TAKE SEND NOTICE IOS MSET.
  unfold diginet_session_tick_contract, diginet_session_tick_ENTRY, diginet_session_tick_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    now r B B' TF A0 A1 Hnow WM GF HM TFm RL SP16 ST LO WO MI.
  subst a0 a1. unfold w_off_stack in WO.
  pose proof MSET as MSET0. pose proof NOTICE as NOTICE0.
  unfold memset_contract, MEMSET in MSET. unfold notice_contract, notice_ENTRY, notice_FRAME in NOTICE.
  wk_facts. sp_facts sp. pose proof ST as (Hlo & _ & _).
  assert (Eo : OFF_g_s = 1648) by reflexivity.
  pose proof (wm_len _ _ _ _ WM) as L.
  pose proof (munch_refl [(bv_unsigned sp - 2160, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  lazymatch goal with |- evt _ ?Q ?st =>
    change (evt rsegs (tick_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo B' r) st) end.
  step. br_closed.
  carve_frame 48%nat ST.
  do 7 step.
  do 6 step.
  rewrite (br_lts_s 1 (s32_at B 1760)) by (pose proof (s32_range B 1760); lia).
  change (s32_at B 1760) with (S_state B).
  pose proof (s32_range B 1760) as Rst. change (s32_at B 1760) with (S_state B) in Rst.
  pose proof (u_at_range B 1688 4) as R1. pose proof (u_at_range B 1824 8) as R2.
  pose proof (u_at_range B 1692 4) as R3. pose proof (u_at_range B 1800 8) as R4.
  change (2 ^ (8 * Z.of_nat 4)) with (2^32) in R1, R3. change (2 ^ (8 * Z.of_nat 8)) with (2^64) in R2, R4.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (I0 : tick_inv sp lo m m1 B ra s0 s1 s2 s3 s4) by (unfold tick_inv; inv_split) end.
  destruct (1 <? S_state B) eqn:H1; cbv iota.
  - (* state > IDLE, WAKING *)
    do 2 step.
    rewrite (br_eqb_s (S_state B) 2) by lia.
    destruct (S_state B =? 2) eqn:H2; cbv iota.
    + (* ONLINE: :425 *)
      apply Z.eqb_eq in H2.
      do 6 step.
      rewrite tmo_bin, negb_involutive by lia.
      change (u_at B 1688 4) with (S_cfg_offline_ms B). change (u_at B 1824 8) with (S_last_rx_us B).
      destruct (ms_m (S_cfg_offline_ms B) <=? u64 (now - S_last_rx_us B)) eqn:Hto; cbv iota.
      * rewrite (tick_m_silence _ _ _ _ H2 Hto) in HM.
        lost_path MSET NOTICE H2 TFm RL 93748 ltac:(do 6 step) 2 DIGINET_R_SILENCE HM TF Hsp WO.
      * rewrite (tick_m_rest _ _ _ _) in HM by (first [ intros; assumption | intros X; unfold DIGINET_S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE in *; lia | unfold DIGINET_S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE in *; lia ]).
        eapply inflight_ok; [exact IOS | exact MSET0 | exact NOTICE0 | exact TAKE | exact SEND | exact I0 | exact Hnow
                              | exact TFm | exact RL | exact HM].
    + apply Z.eqb_neq in H2.
      do 2 step.
      rewrite (br_eqb_s (S_state B) 3) by lia.
      destruct (S_state B =? 3) eqn:H3; nb; cbv iota.
      * apply Z.eqb_eq in H3. step.
        rewrite (tick_m_done _ _ _ _ (or_introl H3)) in HM. injection HM as <- <-.
        eapply ret_ok. exact I0.
      * apply Z.eqb_neq in H3. apply Z.ltb_lt in H1.
        rewrite (tick_m_rest _ _ _ _) in HM by (first [ intros; assumption | intros X; unfold DIGINET_S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE in *; lia | unfold DIGINET_S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE in *; lia ]).
        eapply inflight_ok; [exact IOS | exact MSET0 | exact NOTICE0 | exact TAKE | exact SEND | exact I0 | exact Hnow
                              | exact TFm | exact RL | exact HM].
  - (* state <= WAKING *)
    apply Z.ltb_ge in H1.
    step.
    rewrite (br_eqb_s (S_state B) 0) by lia.
    destruct (S_state B =? 0) eqn:H0; cbv iota.
    + apply Z.eqb_eq in H0.
      rewrite (tick_m_done _ _ _ _ (or_intror H0)) in HM. injection HM as <- <-.
      eapply ret_ok. exact I0.
    + apply Z.eqb_neq in H0.
      do 2 step.
      rewrite (br_eqb_s (S_state B) 1) by lia.
      destruct (S_state B =? 1) eqn:Hw; nb; cbv iota.
      * apply Z.eqb_eq in Hw.
        do 6 step.
        rewrite tmo_bin by lia.
        change (u_at B 1692 4) with (S_cfg_wake_timeout_ms B). change (u_at B 1800 8) with (S_wake_sent_us B).
        destruct (ms_m (S_cfg_wake_timeout_ms B) <=? u64 (now - S_wake_sent_us B)) eqn:Hto; nb; cbv iota.
        -- rewrite (tick_m_wake _ _ _ _ Hw Hto) in HM.
           lost_path MSET NOTICE Hw TFm RL 93520 ltac:(do 7 step) 1 DIGINET_R_WAKE_TIMEOUT HM TF Hsp WO.
        -- rewrite (tick_m_rest _ _ _ _) in HM by (first [ intros; assumption | intros X; unfold DIGINET_S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE in *; lia | unfold DIGINET_S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE in *; lia ]).
           eapply inflight_ok; [exact IOS | exact MSET0 | exact NOTICE0 | exact TAKE | exact SEND | exact I0
                                 | exact Hnow | exact TFm | exact RL | exact HM].
      * apply Z.eqb_neq in Hw.
        rewrite (tick_m_rest _ _ _ _) in HM by (first [ intros; assumption | intros X; unfold DIGINET_S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE in *; lia | unfold DIGINET_S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE in *; lia ]).
        eapply inflight_ok; [exact IOS | exact MSET0 | exact NOTICE0 | exact TAKE | exact SEND | exact I0 | exact Hnow
                              | exact TFm | exact RL | exact HM].
Qed.

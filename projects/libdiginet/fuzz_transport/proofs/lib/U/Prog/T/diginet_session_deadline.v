(* diginet_session_deadline (transport/src/diginet_session.c:476-503) at 0x17c5c, 356 bytes; a leaf (ms and min64
   inlined), no stack frame, no world write. The walk follows diginet_session_deadline_m (TModel/TSess0.v): the state
   branches of :479-489 up to the join at 0x17d08, the inflight arm of :491-492, and the queue scan of :495-497 (the
   loop 0x17d68-0x17d84, by induction on its fuel against deadline_display_only_m) up to the clamp of :502. The three
   UBSan traps (unimp at 0x17dbc) are never reached: s = &g_s is 8-aligned (0x17c74), the scan's index stays below
   512 because the model is Some (0x17d68), and &s->queue[i] does not wrap (0x17d6c). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldLemmas TWorldMem TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import diginet_session_deadline_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- branch conditions over literal words ---- *)
Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec 0 (z + 1)).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
  - replace (z mod 2^64) with (z + 2^64).
    + destruct (Z.ltb_spec (z + 2^64) (2^63)); lia.
    + symmetry. rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma lts_lit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit by assumption. reflexivity. Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma eqb_sl : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|N]; [apply bv_eqb_refl|].
  unfold bv_eqb. apply Z.eqb_neq. intros E. apply N.
  rewrite <- (signed_lit a Ha), <- (signed_lit b Hb). f_equal. apply bv_eq. exact E.
Qed.

(* ---- register values in the model's uint64_t form ---- *)
Lemma to_u64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (u64 z).
Proof. intros z. apply bv_eq. rewrite !unsigned_lit_wrap. unfold u64. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* (uint64_t)v * 1000u + w, the inlined ms (:77) added to a uint64_t field *)
Lemma wrap_ms : forall u v, 0 <= u < 2^64 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 u) * 1000 + v) = Z_to_bv 64 (u64 (v + ms_m u)).
Proof.
  intros u v Hu. rewrite unsigned_lit by exact Hu. apply bv_eq. rewrite !unsigned_lit_wrap.
  unfold u64, ms_m, u64. rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_r. rewrite Z.add_comm. reflexivity.
Qed.

Lemma u64_range : forall z, 0 <= u64 z < 2^64.
Proof. intros z. unfold u64. apply Z.mod_pos_bound. lia. Qed.
Lemma min_range : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= min64_m a b < 2^64.
Proof. intros a b Ha Hb. unfold min64_m. destruct (a <? b); lia. Qed.
Lemma if_range : forall (c : bool) a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= (if c then a else b) < 2^64.
Proof. intros c a b Ha Hb. destruct c; assumption. Qed.
Lemma ua8_range : forall B k, 0 <= u_at B k 8 < 2^64.
Proof. intros B k. exact (u_at_range B k 8). Qed.
Lemma ua4_range : forall B k, 0 <= u_at B k 4 < 2^64.
Proof. intros B k. pose proof (u_at_range B k 4) as H. change (2 ^ (8 * Z.of_nat 4)) with (2^32) in H. lia. Qed.
Lemma ua1_range : forall B k, 0 <= u_at B k 1 < 2^64.
Proof. intros B k. pose proof (u_at_range B k 1) as H. change (2 ^ (8 * Z.of_nat 1)) with (2^8) in H. lia. Qed.

Ltac rng := solve [ repeat first [ apply u64_range | apply min_range | apply ua8_range | apply ua4_range
                                 | apply ua1_range | apply if_range | lia ] ].

Lemma min_l_eq : forall a b, a < b -> min64_m a b = a.
Proof. intros a b H. unfold min64_m. rewrite (proj2 (Z.ltb_lt a b) H). reflexivity. Qed.
Lemma min_r_eq : forall a b, b <= a -> min64_m a b = b.
Proof. intros a b H. unfold min64_m. rewrite (proj2 (Z.ltb_ge a b) H). reflexivity. Qed.
Lemma mx_t : forall p q, p < q -> (if p <? q then q else p) = q.
Proof. intros p q H. rewrite (proj2 (Z.ltb_lt p q) H). reflexivity. Qed.
Lemma mx_f : forall p q, q <= p -> (if p <? q then q else p) = p.
Proof. intros p q H. rewrite (proj2 (Z.ltb_ge p q) H). reflexivity. Qed.

Lemma evt_done_eq : forall ms, evt rsegs (eq ms) ms.
Proof. intros ms. apply evt_done. reflexivity. Qed.

(* ---- the model, cut at the binary's join points ---- *)
Definition dl_clamp (now d : Z) : Z := if d <? now then now else d.                       (* :502 *)

(* :498-499, the display gap, from t *)
Definition dl_tdisp (B : list byte) (dsp t : Z) : Z :=
  if negb (dsp =? 0) && negb (S_display_sent B =? 0) then
    let g := u64 (S_last_display_us B + S_cfg_display_gap_us B) in if g <? t then t else g
  else t.

(* :494 then :498-499 *)
Definition dl_t (B : list byte) (now dsp : Z) : Z :=
  dl_tdisp B dsp (if now <? S_backoff_until_us B then S_backoff_until_us B else now).

(* :491-502 from the d of :489 (the binary's join 0x17430); online = (state == ONLINE) *)
Definition dl_tail (B : list byte) (now d : Z) (online : bool) : option Z :=
  if negb (S_inflight B =? 0) then
    Some (min64_m d (u64 (S_inflight_sent_us B + ms_m (S_cfg_ack_timeout_ms B))))
  else
  let dq := if online && negb (S_queued B =? 0) then
      match deadline_display_only_m B 0 1 (Z.to_nat (S_queued B)) with
      | None => None
      | Some dsp => Some (min64_m d (dl_t B now dsp))
      end
    else Some d in
  match dq with
  | None => None
  | Some d => Some (dl_clamp now d)
  end.

(* the d of :478-489 *)
Definition dl_dO (B : list byte) (now : Z) : Z :=
  let d := if S_state B =? 1
           then min64_m (u64 (now + 1000000)) (u64 (S_wake_sent_us B + ms_m (S_cfg_wake_timeout_ms B)))
           else u64 (now + 1000000) in
  if S_state B =? 2 then
    let d := min64_m d (u64 (S_last_rx_us B + ms_m (S_cfg_offline_ms B))) in
    if S_inflight B =? 0 then
      min64_m d (if S_backoff_until_us B <? S_next_keepalive_us B then S_next_keepalive_us B
                 else S_backoff_until_us B)
    else d
  else d.

Lemma dl_split : forall B now, diginet_session_deadline_m B now =
  if (S_state B =? 3) || (S_state B =? 0) then Some (u64 (now + 1000000))
  else dl_tail B now (dl_dO B now) (S_state B =? 2).
Proof. intros B now. reflexivity. Qed.

(* the first turn of the scan (display_only = 1 at i = 0) when s->queued >= 1 *)
Lemma dd_first : forall B q, 1 <= q ->
  deadline_display_only_m B 0 1 (Z.to_nat q) =
  deadline_display_only_m B (0 + 1) (S_queue_display B 0) (Z.to_nat (q - (0 + 1))).
Proof. intros B q Hq. replace (Z.to_nat q) with (S (Z.to_nat (q - (0 + 1)))) by lia. reflexivity. Qed.

(* ---- walk tactics ---- *)
Ltac getters :=
  repeat match goal with
  | |- context [s32_at ?B 1760] => change (s32_at B 1760) with (S_state B)
  | |- context [u_at ?B 1692 4] => change (u_at B 1692 4) with (S_cfg_wake_timeout_ms B)
  | |- context [u_at ?B 1800 8] => change (u_at B 1800 8) with (S_wake_sent_us B)
  | |- context [u_at ?B 1688 4] => change (u_at B 1688 4) with (S_cfg_offline_ms B)
  | |- context [u_at ?B 1824 8] => change (u_at B 1824 8) with (S_last_rx_us B)
  | |- context [s32_at ?B 1860] => change (s32_at B 1860) with (S_inflight B)
  | |- context [u_at ?B 1832 8] => change (u_at B 1832 8) with (S_next_keepalive_us B)
  | |- context [u_at ?B 1840 8] => change (u_at B 1840 8) with (S_backoff_until_us B)
  | |- context [u_at ?B 1676 4] => change (u_at B 1676 4) with (S_cfg_ack_timeout_ms B)
  | |- context [u_at ?B 3400 8] => change (u_at B 3400 8) with (S_inflight_sent_us B)
  | |- context [u_at ?B 19792 4] => change (u_at B 19792 4) with (S_queued B)
  | |- context [s32_at ?B 1856] => change (s32_at B 1856) with (S_display_sent B)
  | |- context [u_at ?B 1848 8] => change (u_at B 1848 8) with (S_last_display_us B)
  | |- context [u_at ?B 1696 4] => change (u_at B 1696 4) with (S_cfg_display_gap_us B)
  end.

Ltac br := cbn [negb].

(* a diamond [bltu a, b, J; mv a, b; J:] whose join holds min64_m x y in a *)
Ltac dmin x y :=
  eapply evt_cut;
  [ step; rewrite ltu_lit by rng; destruct (Z.ltb_spec x y) as [Ld|Ld]; cbv iota;
    [ rewrite <- (min_l_eq x y Ld); apply evt_done_eq
    | step; rewrite (min_r_eq x y Ld); apply evt_done; reflexivity ]
  | intros ? <- ].

(* a diamond [bltu p, q, J; mv q, p; J:] whose join holds (if p <? q then q else p) in q *)
Ltac dmax p q :=
  eapply evt_cut;
  [ step; rewrite ltu_lit by rng; destruct (Z.ltb_spec p q) as [Ld|Ld]; cbv iota;
    [ rewrite <- (mx_t p q Ld); apply evt_done_eq
    | step; rewrite (mx_f p q Ld); apply evt_done; reflexivity ]
  | intros ? <- ].

Ltac zf H e := replace e with false in H by (symmetry; apply Z.eqb_neq; lia).
Ltac simpb H := cbn [negb orb andb Z.eqb Pos.eqb] in H.
Ltac zt H e := replace e with true in H by (symmetry; apply Z.eqb_eq; lia).

Theorem diginet_session_deadline_holds : diginet_session_deadline_contract.
Proof.
  unfold diginet_session_deadline_contract, diginet_session_deadline_ENTRY, diginet_session_deadline_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo now r B HA0 HA1 Hnow WM HM Hsp ST LO WOS MI.
  subst a0 a1.
  assert (EO : OFF_g_s = 1648) by reflexivity.
  pose proof (s32_range B (OFF_g_s + 112)) as RS. change (s32_at B (OFF_g_s + 112)) with (S_state B) in RS.
  pose proof (s32_range B (OFF_g_s + 212)) as RI. change (s32_at B (OFF_g_s + 212)) with (S_inflight B) in RI.
  pose proof (s32_range B (OFF_g_s + 208)) as RD. change (s32_at B (OFF_g_s + 208)) with (S_display_sent B) in RD.
  pose proof (ua4_range B (OFF_g_s + 18144)) as RQ. change (u_at B (OFF_g_s + 18144) 4) with (S_queued B) in RQ.
  rewrite dl_split in HM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* the clamp of :502 and the return (0x17db0-0x17db8) *)
  assert (JE : forall (dv : Z) (w0 w1 w2 x2 x3 x4 x5 x6 x7 : word), 0 <= dv < 2^64 -> r = dl_clamp now dv ->
    evt rsegs QQ (MS (mkR ra sp gp tp w0 w1 w2 s0 s1 (Z_to_bv 64 dv) (Z_to_bv 64 now) x2 x3 x4 x5 x6 x7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17db0) fc None m (seg_rom rsegs))).
  { intros dv w0 w1 w2 x2 x3 x4 x5 x6 x7 Rd Hr.
    step. rewrite ltu_lit by lia. destruct (Z.ltb_spec now dv) as [L|L]; cbv iota.
    - assert (Er : r = dv) by (rewrite Hr; unfold dl_clamp; destruct (Z.ltb_spec dv now); lia).
      step. apply evt_done. unfold QQ. rewrite Er. do 15 eexists. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|exact WM].
    - assert (Er : r = now) by (rewrite Hr; unfold dl_clamp; destruct (Z.ltb_spec dv now); lia).
      step. step. apply evt_done. unfold QQ. rewrite Er. do 15 eexists. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  (* :500 min64 (0x17da8) *)
  assert (JD : forall (d t : Z) (w0 w1 w2 x2 x4 x5 x6 x7 : word), 0 <= d < 2^64 -> 0 <= t < 2^64 ->
    r = dl_clamp now (min64_m d t) ->
    evt rsegs QQ (MS (mkR ra sp gp tp w0 w1 w2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 now) x2 (Z_to_bv 64 t) x4 x5 x6 x7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17da8) fc None m (seg_rom rsegs))).
  { intros d t w0 w1 w2 x2 x4 x5 x6 x7 Rd Rt Hr.
    step. rewrite ltu_lit by lia. destruct (Z.ltb_spec d t) as [L|L]; cbv iota.
    - apply (JE d); [lia|]. rewrite Hr, (min_l_eq d t L). reflexivity.
    - step. apply (JE t); [lia|]. rewrite Hr, (min_r_eq d t L). reflexivity. }
  (* the loop's exit (0x17d88), t2 = display_only: :498-499 the display gap *)
  assert (JB : forall (d t dsp : Z) (w0 w1 x4 x5 x6 x7 : word), 0 <= d < 2^64 -> 0 <= t < 2^64 -> 0 <= dsp < 2^64 ->
    r = dl_clamp now (min64_m d (dl_tdisp B dsp t)) ->
    evt rsegs QQ (MS (mkR ra sp gp tp w0 w1 (Z_to_bv 64 dsp) s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 now)
                          (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 t) x4 x5 x6 x7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17d88) fc None m (seg_rom rsegs))).
  { intros d t dsp w0 w1 x4 x5 x6 x7 Rd Rt Rdsp Hr.
    step. rewrite eqb_lit by lia. destruct (Z.eqb_spec dsp 0) as [E|E]; cbv iota.
    - eapply (JD d t); [lia|lia|]. rewrite Hr, E. reflexivity.
    - step. getters. step. rewrite eqb_sl by lia. destruct (Z.eqb_spec (S_display_sent B) 0) as [E2|E2]; cbv iota.
      + eapply (JD d t); [lia|lia|]. rewrite Hr. unfold dl_tdisp. rewrite E2.
        replace (dsp =? 0) with false by (symmetry; apply Z.eqb_neq; exact E). reflexivity.
      + do 3 step. getters. rewrite (to_u64 (S_last_display_us B + S_cfg_display_gap_us B)).
        step. rewrite ltu_lit by rng.
        destruct (Z.ltb_spec (u64 (S_last_display_us B + S_cfg_display_gap_us B)) t) as [L|L]; cbv iota.
        * eapply (JD d t); [lia|lia|]. rewrite Hr. unfold dl_tdisp.
          replace (dsp =? 0) with false by (symmetry; apply Z.eqb_neq; exact E).
          replace (S_display_sent B =? 0) with false by (symmetry; apply Z.eqb_neq; exact E2). cbn [negb andb].
          rewrite (proj2 (Z.ltb_lt _ _) L). reflexivity.
        * step. eapply (JD d (u64 (S_last_display_us B + S_cfg_display_gap_us B))); [lia|rng|]. rewrite Hr. unfold dl_tdisp.
          replace (dsp =? 0) with false by (symmetry; apply Z.eqb_neq; exact E).
          replace (S_display_sent B =? 0) with false by (symmetry; apply Z.eqb_neq; exact E2). cbn [negb andb].
          rewrite (proj2 (Z.ltb_ge _ _) L). reflexivity. }
  (* the loop of :495-497 (0x17d68-0x17d84): a7 = i + 1, a5 = 32 i, a6 = &s->queue[i].display,
     t0 = ~(s + 1760) (the pointer-overflow bound), t1 = 513 (the bound of the index check), a3 = t of :494 *)
  assert (LOOP : forall (k : nat) (d t i : Z) (w2 : word), 0 <= d < 2^64 -> 0 <= t < 2^64 ->
    Z.of_nat k = S_queued B - (i + 1) -> 0 <= i < 512 ->
    match deadline_display_only_m B (i + 1) (S_queue_display B i) k with
    | Some dsp => r = dl_clamp now (min64_m d (dl_tdisp B dsp t))
    | None => False
    end ->
    evt rsegs QQ (MS (mkR ra sp gp tp (Z_to_bv 64 18446744073709338543) (Z_to_bv 64 513) w2 s0 s1
                          (Z_to_bv 64 d) (Z_to_bv 64 now) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 t)
                          (Z_to_bv 64 (S_queued B)) (Z_to_bv 64 (32 * i))
                          (Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 1785 + 32 * i))) (Z_to_bv 64 (i + 1))
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17d68) fc None m (seg_rom rsegs))).
  { induction k as [|k IH]; intros d t i w2 Rd Rt Hk Hi LM.
    - (* the index trap (i = 512) and the pointer-overflow trap are not taken: i < 512, 32 i < ~(s + 1760) *)
      step. rewrite eqb_lit by lia. replace (i + 1 =? 513) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step. rewrite ltu_lit by lia. replace (18446744073709338543 <? 32 * i) with false by (symmetry; apply Z.ltb_ge; lia).
      cbv iota.
      step.
      replace (u_at B (OFF_g_s + 1785 + 32 * i) 1) with (S_queue_display B i)
        by (unfold S_queue_display, A_S_queue_display; f_equal; lia).
      step. rewrite ltu_lit by lia. replace (i + 1 <? S_queued B) with false by (symmetry; apply Z.ltb_ge; lia). br.
      cbn [deadline_display_only_m] in LM.
      eapply (JB d t (S_queue_display B i)); [lia|lia|rng|exact LM].
    - step. rewrite eqb_lit by lia. replace (i + 1 =? 513) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step. rewrite ltu_lit by lia. replace (18446744073709338543 <? 32 * i) with false by (symmetry; apply Z.ltb_ge; lia).
      cbv iota.
      step.
      replace (u_at B (OFF_g_s + 1785 + 32 * i) 1) with (S_queue_display B i)
        by (unfold S_queue_display, A_S_queue_display; f_equal; lia).
      step. rewrite ltu_lit by lia. replace (i + 1 <? S_queued B) with true by (symmetry; apply Z.ltb_lt; lia). br.
      do 4 step. rewrite eqb_lit by rng.
      cbn [deadline_display_only_m] in LM.
      destruct (Z.eqb_spec (S_queue_display B i) 0) as [E|E]; br.
      + eapply (JB d t (S_queue_display B i)); [lia|lia|rng|]. rewrite E in LM |- *. exact LM.
      + replace (S_queue_display B i =? 0) with false in LM by (symmetry; apply Z.eqb_neq; exact E).
        unfold S_queue_N in LM. destruct (Z.leb_spec 512 (i + 1)) as [Hb|Hb].
        { replace (512 <=? i + 1) with true in LM by (symmetry; apply Z.leb_le; exact Hb).
          cbv iota in LM. contradiction. }
        replace (512 <=? i + 1) with false in LM by (symmetry; apply Z.leb_gt; exact Hb). cbv iota in LM.
        replace (W_BASE_UBSAN + (OFF_g_s + 1785 + 32 * i) + 32) with (W_BASE_UBSAN + (OFF_g_s + 1785 + 32 * (i + 1)))
          by lia.
        replace (32 * i + 32) with (32 * (i + 1)) by lia.
        replace (i + 2) with (i + 1 + 1) by lia.
        apply (IH d t (i + 1)); [lia|lia|lia|lia|exact LM]. }
  (* the join 0x17d08: :491-502 from d; a3 = (state == ONLINE) *)
  assert (J1 : forall (d : Z) (online : bool) (x4 x5 x6 x7 : word), 0 <= d < 2^64 ->
    dl_tail B now d online = Some r ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 now) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s))
                          (Z_to_bv 64 (Z.b2z online)) x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17d08) fc None m (seg_rom rsegs))).
  { intros d online x4 x5 x6 x7 Rd HT.
    unfold dl_tail in HT.
    step. getters. step. rewrite eqb_sl by lia. destruct (Z.eqb_spec (S_inflight B) 0) as [EI|EI]; cbv iota.
    - try rewrite EI in HT. simpb HT.
      destruct online.
      + change (Z.b2z true) with 1. step. if_false.
        do 3 step. getters. step. rewrite eqb_lit by lia.
        destruct (Z.eqb_spec (S_queued B) 0) as [EQ|EQ]; cbv iota.
        * try rewrite EQ in HT. simpb HT. injection HT as HT.
          apply (JE d); [lia|]. symmetry. exact HT.
        * replace (S_queued B =? 0) with false in HT by (symmetry; apply Z.eqb_neq; exact EQ).
          simpb HT. rewrite (dd_first B (S_queued B)) in HT by lia.
          step. getters.
          dmax now (S_backoff_until_us B).
          do 6 step.
          replace (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 1760))) 18446744073709551615))
            with (Z_to_bv 64 18446744073709338543) by (apply bv_eq; reflexivity).
          replace (W_BASE_UBSAN + OFF_g_s + 1785) with (W_BASE_UBSAN + (OFF_g_s + 1785 + 32 * 0)) by lia.
          change (Z_to_bv 64 0) with (Z_to_bv 64 (32 * 0)).
          change (Z_to_bv 64 1) with (Z_to_bv 64 (0 + 1)).
          apply (LOOP (Z.to_nat (S_queued B - (0 + 1))) d
                   (if now <? S_backoff_until_us B then S_backoff_until_us B else now) 0); [lia|rng|lia|lia|].
          destruct (deadline_display_only_m B (0 + 1) (S_queue_display B 0) (Z.to_nat (S_queued B - (0 + 1))))
            as [dsp|]; cbv iota in HT |- *; [|discriminate HT].
          injection HT as HT. symmetry. exact HT.
      + change (Z.b2z false) with 0. step. if_true.
        simpb HT. injection HT as HT. apply (JE d); [lia|]. symmetry. exact HT.
    - replace (S_inflight B =? 0) with false in HT by (symmetry; apply Z.eqb_neq; exact EI). simpb HT.
      injection HT as HT.
      do 5 step. getters. rewrite wrap_ms by rng.
      step. rewrite ltu_lit by rng.
      destruct (Z.ltb_spec d (u64 (S_inflight_sent_us B + ms_m (S_cfg_ack_timeout_ms B)))) as [L|L]; cbv iota.
      + assert (Er : r = d) by (rewrite <- HT; apply min_l_eq; exact L).
        step. apply evt_done. unfold QQ. rewrite Er. do 15 eexists. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|exact WM].
      + assert (Er : r = u64 (S_inflight_sent_us B + ms_m (S_cfg_ack_timeout_ms B)))
          by (rewrite <- HT; apply min_r_eq; exact L).
        step. step. apply evt_done. unfold QQ. rewrite Er. do 15 eexists. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  (* entry 0x17c5c: d = now + 1 s (:478); the state branches of :479-489 *)
  do 4 step. rewrite (to_u64 (now + 1000000)).
  step. rewrite eqb_lit by (unfold W_BASE_UBSAN, OFF_g_s; lia).
  replace (W_BASE_UBSAN + OFF_g_s =? 0) with false by reflexivity. cbv iota.           (* :479 !s is false *)
  (* the alignment trap (0x17c70-0x17c74): s = &g_s = 0x33970 is 8-aligned *)
  step. replace (Z.land (bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s))) 7) with 0 by reflexivity.
  step. rewrite bv_eqb_refl. br.
  step. getters.
  do 2 step. rewrite lts_lit by lia.
  destruct (Z.ltb_spec 1 (S_state B)) as [L1|L1]; cbv iota.
  - step. step. rewrite eqb_sl by lia. destruct (Z.eqb_spec (S_state B) 2) as [E2|E2]; cbv iota.
    + (* ONLINE (0x17cc8): :484 the offline timeout, :487-489 keepalive / backoff *)
      try rewrite E2 in HM. simpb HM.
      do 5 step. getters. rewrite wrap_ms by rng.
      dmin (u64 (now + 1000000)) (u64 (S_last_rx_us B + ms_m (S_cfg_offline_ms B))).
      step. getters. step. step. rewrite eqb_sl by lia.
      destruct (Z.eqb_spec (S_inflight B) 0) as [EI|EI]; br.
      * step. step. getters.
        dmax (S_backoff_until_us B) (S_next_keepalive_us B).
        dmin (min64_m (u64 (now + 1000000)) (u64 (S_last_rx_us B + ms_m (S_cfg_offline_ms B))))
             (if S_backoff_until_us B <? S_next_keepalive_us B then S_next_keepalive_us B else S_backoff_until_us B).
        apply (J1 _ true); [rng|]. rewrite <- HM. f_equal.
        unfold dl_dO. rewrite E2, EI. reflexivity.
      * apply (J1 _ true); [rng|]. rewrite <- HM. f_equal.
        unfold dl_dO. rewrite E2. replace (S_inflight B =? 0) with false by (symmetry; apply Z.eqb_neq; exact EI).
        reflexivity.
    + step. step. rewrite eqb_sl by lia. destruct (Z.eqb_spec (S_state B) 3) as [E3|E3]; br.
      * (* CLOSED: return d *)
        try rewrite E3 in HM. simpb HM. injection HM as HM.
        step. apply evt_done. unfold QQ. rewrite <- HM. do 15 eexists. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|exact WM].
      * (* a state above CLOSED: d unchanged *)
        zf HM (S_state B =? 3). zf HM (S_state B =? 0). zf HM (S_state B =? 2). simpb HM.
        apply (J1 _ false); [rng|]. rewrite <- HM. f_equal.
        unfold dl_dO. replace (S_state B =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (S_state B =? 2) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - step. rewrite eqb_sl by lia. destruct (Z.eqb_spec (S_state B) 0) as [E0|E0]; cbv iota.
    + (* IDLE: return d *)
      try rewrite E0 in HM. simpb HM. injection HM as HM.
      step. apply evt_done. unfold QQ. rewrite <- HM. do 15 eexists. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|exact WM].
    + step. step. rewrite eqb_sl by lia. destruct (Z.eqb_spec (S_state B) 1) as [E1|E1]; br.
      * (* WAKING (0x17c90): :481-482 the wake timeout *)
        try rewrite E1 in HM. simpb HM.
        do 5 step. getters. rewrite wrap_ms by rng.
        dmin (u64 (now + 1000000)) (u64 (S_wake_sent_us B + ms_m (S_cfg_wake_timeout_ms B))).
        step. step.
        apply (J1 _ false); [rng|]. rewrite <- HM. f_equal.
        unfold dl_dO. rewrite E1. reflexivity.
      * (* a negative state: d unchanged *)
        zf HM (S_state B =? 3). zf HM (S_state B =? 0). zf HM (S_state B =? 2). simpb HM.
        apply (J1 _ false); [rng|]. rewrite <- HM. f_equal.
        unfold dl_dO. replace (S_state B =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (S_state B =? 2) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

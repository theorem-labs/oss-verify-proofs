(* on_data (plain build): its machine contract from the contracts of send_control, diginet_frame_is_keepalive and notice. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_is_keepalive_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import send_control_c notice_c on_data_c.
Import ListNotations.
Open Scope Z_scope.

Ltac od_nod := let H := fresh in intro H; discriminate H.

(* ---- the model, cut at the binary's join points ---- *)

Definition od_acks (B : list byte) (r : Z) : list byte :=
  if r =? 0 then set_S_stats_tx_acks B (u64 (S_stats_tx_acks B + 1)) else B.
Definition od_data (B : list byte) : list byte := set_S_stats_rx_data B (u64 (S_stats_rx_data B + 1)).
Definition od_retry (B buf : list byte) (now : Z) : list byte :=
  if fr_retry buf =? 0 then B
  else let B := set_S_stats_rx_desk_retries B (u64 (S_stats_rx_desk_retries B + 1)) in
       set_S_backoff_until_us B (u64 (now + ms_m (S_cfg_backoff_ms B))).
Definition od_tail4 (I : timg) (F : option tframe) (B buf : list byte) : option (list byte * unit) :=
  let B := set_S_desk_counter B (fr_send buf) in
  let B := set_S_desk_counter_valid B 1 in
  if fr_keepalive buf then Some (B, tt)
  else call_notify I F B (Ntc DIGINET_N_DATA (S_state B) 0 0 (fr_send buf) (fr_retry buf) 0 0 None
                              (fr_body buf) (fr_body_len buf)).
Definition od_tail3 (I : timg) (F : option tframe) (B buf : list byte) : option (list byte * unit) :=
  if negb (S_desk_counter_valid B =? 0) && (fr_send buf =? S_desk_counter B) && negb (fr_retry buf =? 0) then
    Some (set_S_stats_rx_duplicates B (u64 (S_stats_rx_duplicates B + 1)), tt)
  else od_tail4 I F B buf.

Lemma on_data_m_eq : forall I F B buf now,
  on_data_m I F B buf now =
  match send_control_m I F B DIGINET_CMD_ACK (fr_send buf) with
  | None => None
  | Some (B1, (r, _)) => od_tail3 I F (od_retry (od_data (od_acks B1 r)) buf now) buf
  end.
Proof. reflexivity. Qed.

(* ---- model facts the walk needs beyond the callee contracts ---- *)

Lemma od_io_send_r : forall I B frame B' r, io_send_m I B frame = Some (B', r) -> r = 0 \/ r = - EIO.
Proof.
  intros I B frame B' r. unfold io_send_m. cbv zeta.
  destruct (check_sent_frame_m _ _) as [[B1 u1]|]; cbv beta iota; [|od_nod].
  match goal with |- (match ?X with Some _ => _ | None => _ end) = _ -> _ => destruct X as [[B2 u2]|] end;
    cbv beta iota; [|od_nod].
  intros H. injection H as _ <-. destruct (truth _); [right | left]; reflexivity.
Qed.

Lemma od_send_control_r : forall I F B cmd ack B1 r f,
  send_control_m I F B cmd ack = Some (B1, (r, f)) -> -2^63 <= r < 2^63.
Proof.
  intros I F B cmd ack B1 r f. unfold send_control_m. cbv zeta.
  destruct (diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN (S_cfg_sum_mode B) <? 0).
  - intros H. injection H as _ <- _. unfold diginet_frame_build_code.
    destruct (negb _); [lia|].
    remember (lib_build_code [] DIGINET_MIN_FRAME_LEN) as c eqn:Ec. vm_compute in Ec. subst c. lia.
  - unfold send_raw_m.
    destruct (call_send _ _ _) as [[B3 r3]|] eqn:CS; cbv beta iota; [|od_nod].
    assert (R3 : r3 = 0 \/ r3 = - EIO).
    { unfold call_send in CS. destruct (_ =? _); [|discriminate CS]. eapply od_io_send_r. exact CS. }
    unfold EIO in R3. destruct (r3 =? 0); intros H; injection H as _ <- _; lia.
Qed.

Lemma od_csd_same : forall F B n B1 u, check_state_data_m F B n = Some (B1, u) -> B1 = B.
Proof.
  intros F B n B1 u. unfold check_state_data_m. cbv zeta.
  destruct (_ || _); [od_nod|].
  destruct (_ <? 0); [od_nod|].
  destruct (negb _); [od_nod|].
  destruct (frame_read _ _ _); [|od_nod].
  destruct (_ <? _); [od_nod|].
  destruct (_ || _); [od_nod|].
  intros H. injection H as <- _. reflexivity.
Qed.

Lemma od_notice_gf : forall I F B n B', n_kind n = DIGINET_N_DATA -> length B = Z.to_nat W_LEN ->
  notice_m I F B n = Some (B', tt) -> g_fail_next B' = g_fail_next B.
Proof.
  intros I F B n B' K L. unfold notice_m. rewrite K.
  replace (DIGINET_N_DATA =? N_STATE) with false by reflexivity.
  replace (DIGINET_N_DATA =? N_ACKED) with false by reflexivity.
  replace (DIGINET_N_DATA =? N_ACK_LOST) with false by reflexivity.
  replace (DIGINET_N_DATA =? N_DESK) with false by reflexivity.
  replace (DIGINET_N_DATA =? N_DATA) with true by reflexivity.
  cbv beta iota.
  destruct (check_state_data_m F B n) as [[B1 u1]|] eqn:CSD; cbv beta iota; [|od_nod].
  apply od_csd_same in CSD. subst B1.
  destruct (int_inc (GOT_ndata B)) as [d|]; cbv beta iota; [|od_nod].
  intros H. injection H as <-.
  unfold g_fail_next, set_GOT_ndata. apply u_at_upd_out; rewrite ?length_put, ?L;
    unfold W_LEN, A_GOT_ndata, OFF_GOT, OFF_g_fail_next; lia.
Qed.

(* ---- machine-value lemmas ---- *)

Lemma od_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* the machine compares the sign extensions of two 32-bit words; the model compares the unsigned words *)
Lemma od_eqb_s32 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. lia.
Qed.

Lemma od_zx16 : forall v, 0 <= v < 2^16 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma od_sx32 : forall v, 0 <= v < 2^64 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 (bv_swrap 32 v).
Proof. intros v Hv. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma od_sx16 : forall v, 0 <= v < 2^64 -> sx16 (Z_to_bv 64 v) = Z_to_bv 64 (bv_swrap 16 v).
Proof. intros v Hv. unfold sx16. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma od_put8_eq : forall v w, v mod 2^64 = w mod 2^64 -> put 8 v = put 8 w.
Proof. intros v w E. rewrite <- (put_mod64 8 v), <- (put_mod64 8 w) by lia. rewrite E. reflexivity. Qed.

Lemma od_put4_swrap : forall v, put 4 (bv_swrap 32 v) = put 4 v.
Proof.
  intros v. unfold put.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 v) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 v 32) by lia.
  f_equal. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma od_put2_swrap : forall v, put 2 (bv_swrap 16 v) = put 2 v.
Proof.
  intros v. unfold put.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_swrap 16 v) 16) by lia.
  rewrite <- (Z_to_le_bytes_mod 2 v 16) by lia.
  f_equal. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 16) with 32768 by reflexivity.
  replace (bv_modulus 16) with 65536 by reflexivity.
  change (2^16) with 65536.
  Z.div_mod_to_equations. lia.
Qed.

Lemma od_swrap_s32 : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 (x mod 2 ^ (8 * Z.of_nat 4)) = x.
Proof.
  intros x Hx. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* reading a field of a byte list built of put pieces *)
Lemma od_ua_skip : forall n v C k w, Z.of_nat n <= k ->
  u_at (put n v ++ C) k w = u_at C (k - Z.of_nat n) w.
Proof.
  intros n v C k w Hk. unfold u_at, sub.
  replace (Z.to_nat k) with (Z.to_nat (k - Z.of_nat n) + n)%nat by lia.
  rewrite <- skipn_skipn.
  pose proof (skipn_app_exact (put n v) C) as E. rewrite length_put in E. rewrite E. reflexivity.
Qed.

Lemma od_ua_here : forall n v C, u_at (put n v ++ C) 0 n = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n v C. unfold u_at, sub. change (skipn (Z.to_nat 0) (put n v ++ C)) with (put n v ++ C).
  rewrite firstn_app, length_put, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite length_put; lia). apply bytes_le_to_Z_put.
Qed.

Lemma od_ua_zero8 : forall C k, k = 0 \/ k = 4 -> u_at (put 8 0 ++ C) k 4 = 0.
Proof. intros C k [-> | ->]; reflexivity. Qed.

Ltac od_skip :=
  repeat (rewrite od_ua_skip by lia;
          match goal with |- context [?k - Z.of_nat ?n] =>
            is_Zlit k; let v := eval vm_compute in (k - Z.of_nat n) in change (k - Z.of_nat n) with v end).

(* the bytes of a run of cells inside a cell list *)
Lemma od_rw_mid : forall m A cs1 cs2 cs3, rw_cells rsegs m A (cs1 ++ cs2 ++ cs3) ->
  bytes_at rsegs m (A + Z.of_nat (cells_size cs1)) (cells_bytes cs2).
Proof.
  intros m A cs1 cs2 cs3 [[WF H] _].
  apply cells_wf_app in WF. destruct WF as [WF1 _].
  rewrite !cells_bytes_app in H. apply bytes_at_app in H. destruct H as [_ H].
  apply bytes_at_app in H. destruct H as [H _].
  rewrite cells_bytes_length in H by exact WF1. exact H.
Qed.

Lemma od_rw_cut : forall m A cs i j, rw_cells rsegs m A cs ->
  bytes_at rsegs m (A + Z.of_nat (cells_size (firstn i cs))) (cells_bytes (firstn j (skipn i cs))).
Proof.
  intros m A cs i j H. apply (od_rw_mid m A (firstn i cs) (firstn j (skipn i cs)) (skipn j (skipn i cs))).
  rewrite !firstn_skipn. exact H.
Qed.

(* the body bytes of the frame (DgnSpec fr_body), at buf + 30 *)
Lemma od_body_at : forall m buf b, fr_code b = 0 -> bytes_at rsegs m buf b ->
  bytes_at rsegs m (buf + 30) (fr_body b).
Proof.
  intros m buf b FC BB.
  destruct (fr_code_ok b FC) as (L30 & _ & _ & _).
  rewrite <- (firstn_skipn 30 b) in BB. apply bytes_at_app in BB. destruct BB as [_ BB].
  rewrite firstn_length_le in BB by lia. change (Z.of_nat 30) with 30 in BB.
  unfold fr_body. rewrite <- (firstn_skipn (Z.to_nat (fr_body_len b)) (skipn 30 b)) in BB.
  apply bytes_at_app in BB. destruct BB as [BB _]. exact BB.
Qed.

(* the heap frame and the RELRO tables lie outside on_data's footprint *)
Lemma od_tframe : forall m m' (sp spc : word) TF, tframe_at m sp 768 TF ->
  munch [(bv_unsigned sp - 768, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  bv_unsigned spc = bv_unsigned sp + -112 -> tframe_at m' spc 48 TF.
Proof.
  intros m m' sp spc TF T MU Hs. destruct TF as [fr|]; [|exact I]. cbn [tframe_at] in T |- *.
  destruct T as (T0 & TB & TW & TO). unfold off_world in TW |- *. unfold off_window in TO |- *.
  split; [exact T0|]. split; [|split; [exact TW | rewrite Hs; lia]].
  eapply bytes_at_transport; [exact TB | exact MU |]. cbn [disjoint_from]. split; [lia | split; [lia | exact I]].
Qed.

Lemma od_relro : forall m m' (sp : word), relro_img m ->
  munch [(bv_unsigned sp - 768, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 768 -> relro_img m'.
Proof.
  intros m m' sp R MU WO i Hi. specialize (R i Hi). unfold mrd in *.
  rewrite (MU (wa (RELRO_BASE + i))); [exact R|].
  unfold wa. rewrite unsigned_lit by (unfold RELRO_BASE, RELRO_LEN in *; lia).
  cbn [outside]. unfold RELRO_BASE, RELRO_LEN, W_BASE_PLAIN, W_LEN in *.
  split; [lia | split; [lia | exact I]].
Qed.

(* the session's setters keep g_fail_next (outside g_s) and the length of the world *)
Lemma od_set_ok : forall B k n v, length B = Z.to_nat W_LEN -> OFF_g_s <= k -> k + Z.of_nat n <= OFF_g_s + SZ_g_s ->
  g_fail_next (upd B k (put n v)) = g_fail_next B /\ length (upd B k (put n v)) = Z.to_nat W_LEN.
Proof.
  intros B k n v L H1 H2. split.
  - unfold g_fail_next. apply u_at_upd_out; rewrite ?length_put, ?L;
      unfold W_LEN, OFF_g_s, SZ_g_s, OFF_g_fail_next in *; lia.
  - rewrite length_upd_put; [exact L | unfold OFF_g_s in *; lia | rewrite L; unfold W_LEN, OFF_g_s, SZ_g_s in *; lia].
Qed.

Ltac od_set := apply od_set_ok; [assumption | ..]; cbv -[Z.add Z.le Z.of_nat]; lia.

Lemma od_ok_acks : forall B r, length B = Z.to_nat W_LEN ->
  g_fail_next (od_acks B r) = g_fail_next B /\ length (od_acks B r) = Z.to_nat W_LEN.
Proof.
  intros B r L. unfold od_acks. destruct (r =? 0); [|split; [reflexivity | exact L]].
  unfold set_S_stats_tx_acks. od_set.
Qed.

Lemma od_ok_data : forall B, length B = Z.to_nat W_LEN ->
  g_fail_next (od_data B) = g_fail_next B /\ length (od_data B) = Z.to_nat W_LEN.
Proof. intros B L. unfold od_data, set_S_stats_rx_data. od_set. Qed.

Lemma od_ok_retry : forall B buf now, length B = Z.to_nat W_LEN ->
  g_fail_next (od_retry B buf now) = g_fail_next B /\ length (od_retry B buf now) = Z.to_nat W_LEN.
Proof.
  intros B buf now L. unfold od_retry. destruct (fr_retry buf =? 0); [split; [reflexivity | exact L]|].
  cbv zeta. unfold set_S_backoff_until_us, set_S_stats_rx_desk_retries.
  assert (H1 : g_fail_next (upd B A_S_stats_rx_desk_retries (put 8 (u64 (S_stats_rx_desk_retries B + 1))))
               = g_fail_next B /\
               length (upd B A_S_stats_rx_desk_retries (put 8 (u64 (S_stats_rx_desk_retries B + 1))))
               = Z.to_nat W_LEN) by od_set.
  destruct H1 as [G1 L1].
  match goal with |- context [upd ?X A_S_backoff_until_us (put 8 ?V)] =>
    assert (H2 : g_fail_next (upd X A_S_backoff_until_us (put 8 V)) = g_fail_next X /\
                 length (upd X A_S_backoff_until_us (put 8 V)) = Z.to_nat W_LEN) by od_set end.
  destruct H2 as [G2 L2]. split; [rewrite G2; exact G1 | exact L2].
Qed.

Lemma od_ok_dup : forall B, length B = Z.to_nat W_LEN ->
  g_fail_next (set_S_stats_rx_duplicates B (u64 (S_stats_rx_duplicates B + 1))) = g_fail_next B.
Proof.
  intros B L. unfold set_S_stats_rx_duplicates.
  assert (H : g_fail_next (upd B A_S_stats_rx_duplicates (put 8 (u64 (S_stats_rx_duplicates B + 1)))) = g_fail_next B /\
              length (upd B A_S_stats_rx_duplicates (put 8 (u64 (S_stats_rx_duplicates B + 1)))) = Z.to_nat W_LEN)
    by od_set.
  exact (proj1 H).
Qed.

Lemma od_ok_dc : forall B x, length B = Z.to_nat W_LEN ->
  g_fail_next (set_S_desk_counter_valid (set_S_desk_counter B x) 1) = g_fail_next B /\
  length (set_S_desk_counter_valid (set_S_desk_counter B x) 1) = Z.to_nat W_LEN.
Proof.
  intros B x L. unfold set_S_desk_counter_valid, set_S_desk_counter.
  assert (H1 : g_fail_next (upd B A_S_desk_counter (put 4 x)) = g_fail_next B /\
               length (upd B A_S_desk_counter (put 4 x)) = Z.to_nat W_LEN) by od_set.
  destruct H1 as [G1 L1].
  assert (H2 : g_fail_next (upd (upd B A_S_desk_counter (put 4 x)) A_S_desk_counter_valid (put 4 1)) =
               g_fail_next (upd B A_S_desk_counter (put 4 x)) /\
               length (upd (upd B A_S_desk_counter (put 4 x)) A_S_desk_counter_valid (put 4 1)) = Z.to_nat W_LEN)
    by od_set.
  destruct H2 as [G2 L2]. split; [rewrite G2; exact G1 | exact L2].
Qed.

Ltac od_world E := match goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) _] |- _ => rewrite E in H end.

Theorem on_data_holds :
  send_control_contract -> diginet_frame_is_keepalive_contract -> notice_contract -> on_data_contract.
Proof.
  intros SC KA NT.
  unfold send_control_contract, send_control_ENTRY, send_control_FRAME in SC.
  unfold diginet_frame_is_keepalive_contract, DIGINET_FRAME_IS_KEEPALIVE in KA.
  unfold notice_contract, notice_ENTRY, notice_FRAME in NT.
  unfold on_data_contract, on_data_ENTRY, on_data_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    fp buf now b fj B B' TF A0 A1 A2 NOW DF WM GF HM TFA REL SP16 ST LO WO MI.
  subst a0 a1 a2.
  unfold w_off_stack in WO.
  wk_facts.
  assert (Eo : OFF_g_s = 1648) by reflexivity.
  destruct DF as (FC & BB & ABb & DC & ABf & FP8).
  destruct ABb as (Hb0 & Hb1 & Hb2 & Hb3). destruct ABf as (Hf0 & Hf1 & Hf2 & Hf3).
  unfold off_world in Hb2, Hf2. unfold off_window in Hb3, Hf3. unfold dframe_cells in DC.
  pose proof (fr_body_len_ok b FC) as (BL0 & PL0 & BLS).
  assert (LBL : Z.of_nat (length (fr_body b)) = fr_body_len b) by (rewrite (length_fr_body b FC); lia).
  pose proof (be32_range b 18) as RSEND. change (be32 b 18) with (fr_send b) in RSEND.
  pose proof (be16_range b 26) as RRETRY. change (be16 b 26) with (fr_retry b) in RRETRY.
  pose proof (at8_range b 28) as RCMD. change (at8 b 28) with (fr_cmd b) in RCMD.
  rewrite on_data_m_eq in HM.
  destruct (send_control_m timg_plain TF B DIGINET_CMD_ACK (fr_send b)) as [[B1 [r f0]]|] eqn:HSC;
    [|discriminate HM].
  pose proof (od_send_control_r _ _ _ _ _ _ _ _ HSC) as RR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 768, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 112%nat ST.
  (* prologue: addi sp,sp,-112; sd ra,s0,s1,s2,s3; mv s2,a2; mv s0,a1; mv s1,a0 *)
  do 9 step.
  (* lw a2,20(a1): f->h.send_counter *)
  step. rewrite od_sx32 by lia.
  (* lui a0,0x4; addiw s3,a0,1776; add s3,s1,s3; li a1,160; mv a0,s1; li a3,0; li a4,0; jal send_control *)
  do 8 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  eapply evt_cut.
  { eapply SC with (cmd := 160) (ack := fr_send b) (kp := 0) (klp := 0) (lo := lo) (K := []) (KL := []).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - left; reflexivity.
    - exact WM.
    - exact GF.
    - exact HSC.
    - rewrite Hsp; Z.div_mod_to_equations; lia.
    - rewrite Hsp; exact ST.
    - rewrite Hsp; lia.
    - unfold w_off_stack; rewrite Hsp; lia.
    - exact MI. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 &
              Eq & MUc & WMc & MI2 & ST2 & WM2 & GF2 & _).
  subst ms'. rewrite Hsp in MUc, ST2.
  cbn [app Z.eqb] in MUc.
  clear WM.
  transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI. try clear m1.
  rewrite (ret_pc_even 93036) by (first [lia | reflexivity]).
  pose proof (wm_len _ _ _ _ WM2) as LB1.
  lazymatch type of FR with rw_cells _ _ _ (CB 72 ?j :: _) => set (J72 := j) in FR; clearbody J72 end.
  clear SC.
  (* ---- 0x16b7c, after the tx_acks update ---- *)
  assert (J1 : forall (mX : word -> option byte) (Bx : list byte) (a0v : word),
    rw_cells rsegs mX (bv_unsigned sp + -112) [CB 72 J72; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mX fp (dframe_cells buf b fj) ->
    bytes_at rsegs mX buf b ->
    wmem rsegs mX Bx -> g_fail_next Bx <= 1 ->
    stk rsegs mX lo (bv_unsigned sp + -112) -> mem_inv rsegs mX ->
    munch [(bv_unsigned sp - 768, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mX ->
    wmono rsegs m mX ->
    od_tail3 timg_plain TF (od_retry (od_data Bx) b now) b = Some (B', tt) ->
    evt rsegs QQ (MS (mkR (Z_to_bv 64 93036) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7
                          (Z_to_bv 64 fp) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) a0v x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 now) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18160))
                          s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 93052) fc None mX (seg_rom rsegs))).
  { intros mX Bx a0v FRx DCx BBx WMx GFx STx MIx MUx WMOx HMx.
    clear FR DC BB WM2 GF2 ST2 MI2 MU0 WM0 HM LB1 HSC.
    unfold dframe_cells in DCx.
    pose proof (wm_len _ _ _ _ WMx) as LBx.
    destruct (od_ok_data Bx LBx) as [GD LD].
    destruct (od_ok_retry (od_data Bx) b now LD) as [GR LR].
    (* ld a1,0(s3); lhu a0,28(s0); addi a1,a1,1; sd a1,0(s3) *)
    step. step. rewrite od_zx16 by lia. step. step.
    assert (ED : upd Bx 19808 (put 8 (u_at Bx 19808 8 + 1)) = od_data Bx)
      by (unfold od_data, set_S_stats_rx_data, S_stats_rx_data, u64; rewrite put_mod64 by lia; reflexivity).
    od_world ED.
    (* ---- 0x16bb0, after the retry update ---- *)
    assert (J2 : forall (mY : word -> option byte) (By : list byte) (a1v a2v a3v : word),
      rw_cells rsegs mY (bv_unsigned sp + -112) [CB 72 J72; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs mY fp (dframe_cells buf b fj) ->
      bytes_at rsegs mY buf b ->
      wmem rsegs mY By -> g_fail_next By <= 1 ->
      stk rsegs mY lo (bv_unsigned sp + -112) -> mem_inv rsegs mY ->
      munch [(bv_unsigned sp - 768, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mY ->
      wmono rsegs m mY ->
      od_tail3 timg_plain TF By b = Some (B', tt) ->
      evt rsegs QQ (MS (mkR (Z_to_bv 64 93036) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7
                            (Z_to_bv 64 fp) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fr_retry b))
                            a1v a2v a3v x14 x15 x16 x17
                            (Z_to_bv 64 now) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18160))
                            s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 93104) fc None mY (seg_rom rsegs))).
    { intros mY By a1v a2v a3v FRy DCy BBy WMy GFy STy MIy MUy WMOy HMy.
      clear FRx DCx BBx GFx STx MIx MUx WMOx HMx LBx GD LD GR LR ED.
      match goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) (od_data Bx)] |- _ => clear H end.
      unfold dframe_cells in DCy.
      pose proof (wm_len _ _ _ _ WMy) as LBy.
      unfold od_tail3 in HMy.
      (* lw a2,168(s1); lw a1,20(s0) *)
      step. change (s32_at By 1816) with (S_desk_counter_valid By).
      step. rewrite od_sx32 by lia.
      (* ---- 0x16bd8, not a duplicate ---- *)
      assert (J3 : forall (mZ : word -> option byte) (Bz : list byte) (a0v a2v : word),
        rw_cells rsegs mZ (bv_unsigned sp + -112) [CB 72 J72; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs mZ fp (dframe_cells buf b fj) ->
        bytes_at rsegs mZ buf b ->
        wmem rsegs mZ Bz -> g_fail_next Bz <= 1 ->
        stk rsegs mZ lo (bv_unsigned sp + -112) -> mem_inv rsegs mZ ->
        munch [(bv_unsigned sp - 768, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mZ ->
        wmono rsegs m mZ ->
        od_tail4 timg_plain TF Bz b = Some (B', tt) ->
        evt rsegs QQ (MS (mkR (Z_to_bv 64 93036) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7
                              (Z_to_bv 64 fp) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) a0v
                              (Z_to_bv 64 (bv_swrap 32 (fr_send b))) a2v a3v x14 x15 x16 x17
                              (Z_to_bv 64 now) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18160))
                              s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 93144) fc None mZ (seg_rom rsegs))).
      { intros mZ Bz a0z a2z FRz DCz BBz WMz GFz STz MIz MUz WMOz HMz.
        clear FRy DCy BBy WMy GFy STy MIy MUy WMOy HMy LBy.
        unfold dframe_cells in DCz.
        pose proof (wm_len _ _ _ _ WMz) as LBz.
        destruct (od_ok_dc Bz (fr_send b) LBz) as [GC LC].
        unfold od_tail4 in HMz. cbv zeta in HMz.
        (* li a0,1; sw a1,164(s1); sw a0,168(s1) *)
        step. step.
        assert (E1 : upd Bz 1812 (put 4 (bv_swrap 32 (fr_send b))) = set_S_desk_counter Bz (fr_send b))
          by (unfold set_S_desk_counter; rewrite od_put4_swrap; reflexivity).
        od_world E1.
        step.
        assert (E2 : upd (set_S_desk_counter Bz (fr_send b)) 1816 (put 4 1) =
                     set_S_desk_counter_valid (set_S_desk_counter Bz (fr_send b)) 1) by reflexivity.
        od_world E2.
        set (B6 := set_S_desk_counter_valid (set_S_desk_counter Bz (fr_send b)) 1) in *.
        (* mv a0,s0; jal diginet_frame_is_keepalive *)
        step. step.
        pose proof (od_rw_cut _ _ _ 9 1 DCz) as K30.
        pose proof (od_rw_cut _ _ _ 11 2 DCz) as K32.
        cbn [firstn skipn cells_size csize cells_bytes cbytes Nat.add app] in K30, K32.
        change (Z.of_nat 30) with 30 in K30. change (Z.of_nat 32) with 32 in K32. rewrite app_nil_r in K32.
        pose proof (od_body_at _ buf b FC BBz) as BODY.
        eapply evt_cut.
        { eapply KA with (cmd := fr_cmd b) (body := buf + 30) (bb := fr_body b).
          - lia.
          - exact RCMD.
          - lia.
          - exact K30.
          - rewrite LBL. exact K32.
          - exact BODY. }
        intros ms' (y11 & y12 & ->).
        rewrite (ret_pc_even 93164) by (first [lia | reflexivity]).
        rewrite LBL. change (keepalive_of (fr_cmd b) (fr_body_len b) (fr_body b)) with (fr_keepalive b).
        (* bnez a0,0x16c48 *)
        step.
        rewrite od_eqb0 by (destruct (fr_keepalive b); lia).
        revert HMz. destruct (fr_keepalive b); cbn [Z.eqb negb]; intros HMz.
        - (* a keepalive: return *)
          injection HMz as HB.
          do 5 step. release_frame FRz STz (bv_unsigned sp). do 2 step.
          apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
          split; [exact MUz|]. split; [exact WMOz|]. split; [exact MIz|]. split; [exact STz|].
          rewrite <- HB. split; [eassumption | rewrite GC; exact GFz].
        - (* the DATA notice: lw a1,112(s1); ld a2,96(s1); ld a0,104(s1); li a3,3 *)
          step. step. step. step.
          (* sw a3,0(sp); sw a1,4(sp); sd zero,8(sp); sd s0,16(sp) *)
          step. step. step. step.
          (* lw a1,20(s0); lh a3,28(s0); ld a4,32(s0); ld a5,40(s0) *)
          step. rewrite od_sx32 by lia. step. rewrite od_sx16 by lia. step. step.
          (* sd zero,24; sd zero,32; sd zero,40; sd a4,48; sd a5,56; sw a1,64; sh a3,68; sh zero,70 *)
          do 8 step.
          (* mv a1,sp; jalr a2 *)
          step. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
          (* the call through g_s.notify: the model's Some gives the cell's value, notice's entry *)
          unfold call_notify in HMz.
          destruct (S_notify B6 =? ti_notice timg_plain) eqn:NOTI; rewrite ?NOTI in HMz; cbv beta iota in HMz;
            [|discriminate HMz].
          apply Z.eqb_eq in NOTI.
          change (u_at B6 1744 8) with (S_notify B6). rewrite NOTI. change (ti_notice timg_plain) with 84452.
          rewrite (ret_pc_even 84452) by (first [lia | reflexivity]).
          (* the struct diginet_notice the binary built at sp - 112 *)
          pose proof (od_rw_cut _ _ _ 0 12 FRz) as NB0.
          cbn [firstn skipn cells_size csize cells_bytes cbytes Nat.add app] in NB0.
          change (Z.of_nat 0) with 0 in NB0. rewrite Z.add_0_r in NB0.
          set (NBv := put 4 3 ++ put 4 (S_state B6) ++ put 8 0 ++ put 8 fp ++ put 8 0 ++ put 8 0 ++ put 8 0
                      ++ put 8 (buf + 30) ++ put 8 (fr_body_len b) ++ put 4 (fr_send b) ++ put 2 (fr_retry b)
                      ++ put 2 0).
          assert (NBA : bytes_at rsegs mC (bv_unsigned sp + -112) NBv).
          { eapply bytes_at_ext; [exact NB0|]. unfold NBv.
            rewrite ?le8_put, ?le4_put, ?le2_put, app_nil_r.
            rewrite (od_put4_swrap (fr_send b)), (od_put2_swrap (fr_retry b)). reflexivity. }
          assert (UB : u_at NBv 48 8 = buf + 30).
          { unfold NBv. od_skip. rewrite od_ua_here. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
            apply Z.mod_small. lia. }
          assert (NTA : ntc_at mC (bv_unsigned sp + -112)
                          (Ntc DIGINET_N_DATA (S_state B6) 0 0 (fr_send b) (fr_retry b) 0 0 None (fr_body b)
                               (fr_body_len b))
                          (Z_to_bv 64 (bv_unsigned sp + -112)) 48).
          { unfold ntc_at. cbn [n_kind n_state n_old n_reason n_counter n_retry n_mac_offset n_pers n_ann n_body
                                n_body_len].
            unfold off_world, off_window. rewrite Hsp.
            split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
            exists NBv. split; [exact NBA|].
            split; [unfold NBv; rewrite !length_app, !length_put; reflexivity|].
            rewrite UB.
            split; [unfold NBv, s32_at; rewrite od_ua_here; reflexivity|].
            split; [unfold NBv, s32_at at 1; od_skip; rewrite od_ua_here; apply od_swrap_s32;
                    unfold S_state; apply s32_range|].
            split; [unfold NBv, s32_at; od_skip; rewrite od_ua_zero8 by lia; reflexivity|].
            split; [unfold NBv, s32_at; od_skip; rewrite od_ua_zero8 by lia; reflexivity|].
            split; [unfold NBv; od_skip; rewrite od_ua_here; reflexivity|].
            split; [unfold NBv, s32_at; od_skip; rewrite od_ua_zero8 by lia; reflexivity|].
            split; [unfold NBv; od_skip; rewrite od_ua_here; change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64);
                    apply Z.mod_small; lia|].
            split; [unfold NBv; od_skip; rewrite od_ua_here; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32);
                    apply Z.mod_small; lia|].
            split; [unfold NBv; od_skip; rewrite od_ua_here; change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16);
                    apply Z.mod_small; lia|].
            split; [exact BODY|].
            split; [lia|]. split; [lia|].
            unfold NBv; od_skip; rewrite od_ua_here; reflexivity. }
          eapply evt_cut.
          { eapply NT with (p := bv_unsigned sp + -112) (Fr := TF) (B := B6) (lo := lo)
              (n := Ntc DIGINET_N_DATA (S_state B6) 0 0 (fr_send b) (fr_retry b) 0 0 None (fr_body b)
                        (fr_body_len b)).
            - reflexivity.
            - exact NTA.
            - exact (od_tframe m mC sp _ TF TFA MUz Hsp).
            - exact (od_relro m mC sp REL MUz WO).
            - eassumption.
            - exact HMz.
            - rewrite Hsp; Z.div_mod_to_equations; lia.
            - rewrite Hsp; exact STz.
            - rewrite Hsp; lia.
            - unfold w_off_stack; rewrite Hsp; lia.
            - exact MIz. }
          intros ms' (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & mN &
                      Eq & MUc & WMc & MIN & STN & WMN).
          subst ms'. rewrite Hsp in MUc, STN.
          match goal with H : rw_cells rsegs mC W_BASE_PLAIN [CB (Z.to_nat W_LEN) _] |- _ => clear H end.
          clear NTA NBA NB0 UB K30 K32 BODY.
          transport_after_call rsegs mC mN MUc WMc. clear MUc WMc MIz. try clear mC.
          rewrite (ret_pc_even 93256) by (first [lia | reflexivity]).
          (* the epilogue: ld ra,104(sp); ld s0..s3; addi sp,sp,112; ret *)
          do 5 step. release_frame FRz STN (bv_unsigned sp). do 2 step.
          apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
          split; [exact MUz|]. split; [exact WMOz|]. split; [exact MIN|]. split; [exact STN|].
          split; [exact WMN|].
          pose proof (od_notice_gf timg_plain TF B6
                        (Ntc DIGINET_N_DATA (S_state B6) 0 0 (fr_send b) (fr_retry b) 0 0 None (fr_body b)
                             (fr_body_len b))
                        B' eq_refl LC HMz) as GN.
          rewrite GN, GC. exact GFz. }
      (* beqz a2,0x16bd8 *)
      step.
      rewrite od_eqb0 by (pose proof (s32_range By A_S_desk_counter_valid); unfold S_desk_counter_valid; lia).
      revert HMy. destruct (Z.eqb_spec (S_desk_counter_valid By) 0) as [V0|V1]; cbn [negb andb]; intros HMy.
      + eapply (J3 _ By); [exact FRy | exact DCy | exact BBy | exact WMy | exact GFy | exact STy | exact MIy
          | exact MUy | exact WMOy | exact HMy].
      + (* beqz a0,0x16bd8 *)
        step. rewrite od_eqb0 by lia.
        revert HMy. destruct (Z.eqb_spec (fr_retry b) 0) as [T0|T1]; cbn [negb andb]; intros HMy.
        * rewrite Bool.andb_false_r in HMy. cbv iota in HMy.
          eapply (J3 _ By); [exact FRy | exact DCy | exact BBy | exact WMy | exact GFy | exact STy | exact MIy
            | exact MUy | exact WMOy | exact HMy].
        * (* lw a0,164(s1); bne a1,a0,0x16bd8 *)
          step. change (s32_at By 1812) with (bv_swrap 32 (S_desk_counter By)).
          step.
          rewrite od_eqb_s32 by (pose proof (u_at_range By A_S_desk_counter 4) as UR;
            change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in UR; unfold S_desk_counter; lia).
          rewrite Bool.andb_true_r in HMy.
          revert HMy. destruct (Z.eqb_spec (fr_send b) (S_desk_counter By)) as [D0|D1]; cbn [negb]; intros HMy.
          -- (* a duplicate: ld a0,8(s3); addi a0,a0,1; sd a0,8(s3); j 0x16c48 *)
             step. step. step.
             assert (EU : upd By 19816 (put 8 (u_at By 19816 8 + 1)) =
                          set_S_stats_rx_duplicates By (u64 (S_stats_rx_duplicates By + 1)))
               by (unfold set_S_stats_rx_duplicates, S_stats_rx_duplicates, u64; rewrite put_mod64 by lia; reflexivity).
             od_world EU.
             injection HMy as HB.
             step.
             do 5 step. release_frame FRy STy (bv_unsigned sp). do 2 step.
             apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
             split; [exact MUy|]. split; [exact WMOy|]. split; [exact MIy|]. split; [exact STy|].
             rewrite <- HB. split; [eassumption | rewrite od_ok_dup by exact LBy; exact GFy].
          -- eapply (J3 _ By); [exact FRy | exact DCy | exact BBy | exact WMy | exact GFy | exact STy | exact MIy
               | exact MUy | exact WMOy | exact HMy]. }
    (* beqz a0,0x16bb0 *)
    step.
    rewrite od_eqb0 by lia.
    destruct (Z.eqb_spec (fr_retry b) 0) as [T0|T1]; cbv iota.
    - (* retry = 0 *)
      assert (ER : od_retry (od_data Bx) b now = od_data Bx)
        by (unfold od_retry; replace (fr_retry b =? 0) with true by (symmetry; apply Z.eqb_eq; exact T0); reflexivity).
      eapply (J2 _ (od_retry (od_data Bx) b now)); [exact FRx | exact DCx | exact BBx | rewrite ER; eassumption
        | rewrite GR, GD; exact GFx | exact STx | exact MIx | exact MUx | exact WMOx | exact HMx].
    - (* lwu a1,36(s1); ld a2,16(s3); li a3,1000; mul a1,a1,a3; addi a2,a2,1; sd a2,16(s3) *)
      step. step. step. step. step. step.
      (* add a1,a1,s2; sd a1,192(s1) *)
      step. step.
      assert (CB : S_cfg_backoff_ms (set_S_stats_rx_desk_retries (od_data Bx)
                                       (u64 (S_stats_rx_desk_retries (od_data Bx) + 1)))
                   = u_at (od_data Bx) 1684 4).
      { unfold S_cfg_backoff_ms, set_S_stats_rx_desk_retries.
        apply u_at_upd_out; rewrite ?length_put, ?LD; unfold A_S_stats_rx_desk_retries, A_S_cfg_backoff_ms; lia. }
      assert (ER : upd (upd (od_data Bx) 19824 (put 8 (u_at (od_data Bx) 19824 8 + 1))) 1840
                     (put 8 (bv_unsigned (Z_to_bv 64 (u_at (od_data Bx) 1684 4)) * 1000 + now))
                   = od_retry (od_data Bx) b now).
      { unfold od_retry. replace (fr_retry b =? 0) with false by (symmetry; apply Z.eqb_neq; exact T1).
        cbv zeta. rewrite CB. unfold set_S_backoff_until_us, set_S_stats_rx_desk_retries, S_stats_rx_desk_retries.
        f_equal.
        - unfold u64. rewrite put_mod64 by lia. reflexivity.
        - apply od_put8_eq. unfold ms_m, u64.
          pose proof (u_at_range (od_data Bx) 1684 4) as UR. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in UR.
          rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia. }
      od_world ER.
      eapply (J2 _ (od_retry (od_data Bx) b now)); [exact FRx | exact DCx | exact BBx | eassumption
        | rewrite GR, GD; exact GFx | exact STx | exact MIx | exact MUx | exact WMOx | exact HMx]. }
  (* bnez a0,0x16b7c *)
  step.
  rewrite od_eqb0 by exact RR.
  destruct (Z.eqb_spec r 0) as [R0|R1]; cbn [negb]; cbv iota.
  - (* r = 0: ld a0,48(s3); addi a0,a0,1; sd a0,48(s3) *)
    step. step. step.
    assert (EA : upd B1 19856 (put 8 (u_at B1 19856 8 + 1)) = od_acks B1 r).
    { unfold od_acks. replace (r =? 0) with true by (symmetry; apply Z.eqb_eq; exact R0).
      unfold set_S_stats_tx_acks, S_stats_tx_acks, u64. rewrite put_mod64 by lia. reflexivity. }
    od_world EA.
    destruct (od_ok_acks B1 r LB1) as [GA _].
    eapply (J1 _ (od_acks B1 r)); [exact FR | exact DC | exact BB | eassumption | rewrite GA; exact GF2
      | exact ST2 | exact MI2 | exact MU0 | exact WM0 | exact HM].
  - (* r <> 0 *)
    assert (EA : od_acks B1 r = B1) by (unfold od_acks; destruct (Z.eqb_spec r 0); [contradiction | reflexivity]).
    eapply (J1 _ (od_acks B1 r)); [exact FR | exact DC | exact BB | rewrite EA; exact WM2 | rewrite EA; exact GF2
      | exact ST2 | exact MI2 | exact MU0 | exact WM0 | exact HM].
Qed.

Print Assumptions on_data_holds.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 533 of its 587 lines of code are new or changed and 395 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_frame/lib/Prog/diginet_frame_build.v, with its module paths, module names and numbers changed; 359 of its 417 lines of code are new or changed and 529 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Prog/T/diginet_session_close.v, with its module names, addresses and numbers changed; 398 of its 540 lines of code are new or changed and 275 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg
  TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memcpy_c memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import send_control_c notice_c
  diginet_session_wake_c.
Import ListNotations.
Open Scope Z_scope.

Lemma wake_eqb : forall v c, -2^63 <= v < 2^63 -> -2^63 <= c < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 c) = (v =? c).
Proof.
  intros v c Hv Hc. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v c) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E.
  assert (E2 : (v - c) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in E2; [|lia]. destruct E2 as [k Ek]. nia.
Qed.

Lemma wake_lts0 : forall v, -2^63 <= v < 2^63 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv. rewrite bv_lts_zero_r, unsigned_lit_wrap.
  destruct (Z.ltb_spec v 0) as [N|N].
  - apply Z.leb_le. assert (E : v mod 2^64 = v + 2^64) by (symmetry; apply Z.mod_unique with (-1); lia). lia.
  - apply Z.leb_gt. rewrite Z.mod_small by lia. lia.
Qed.

(* io_send answers 0 or -EIO (fuzz_transport.c:898) *)
Lemma wake_io_send_r : forall I B fr B' r, io_send_m I B fr = Some (B', r) -> r = 0 \/ r = - EIO.
Proof.
  intros I B fr B' r H. unfold io_send_m in H. cbv zeta in H.
  destruct (check_sent_frame_m _ _) as [[B1 u]|]; [|discriminate H]. cbv beta iota in H.
  lazymatch type of H with (match ?X with _ => _ end) = _ => destruct X as [[B2 u2]|] end; [|discriminate H].
  cbv beta iota in H. injection H as _ <-. destruct (truth _); [right|left]; reflexivity.
Qed.

(* send_control's result is -1, 0 or -EIO, and its frame is [] only when the build failed (r < 0) *)
Lemma wake_sc : forall I F B cmd ack B' r f, send_control_m I F B cmd ack = Some (B', (r, f)) ->
  -2^63 <= r < 2^63 /\ (f = [] -> r < 0).
Proof.
  intros I F B cmd ack B' r f H. unfold send_control_m in H. cbv zeta in H.
  assert (E : diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN (S_cfg_sum_mode B) = -1 \/
              diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN (S_cfg_sum_mode B) = 60).
  { unfold diginet_frame_build_code. destruct (negb _); [left; reflexivity | right; vm_compute; reflexivity]. }
  destruct E as [E|E]; rewrite E in H.
  - change (-1 <? 0) with true in H. cbv iota in H. injection H as _ <- <-. split; [lia | intros _; lia].
  - change (60 <? 0) with false in H. cbv iota in H.
    destruct (send_raw_m _ _ _ _) as [[B1 r1]|] eqn:SR; [|discriminate H].
    injection H as _ <- <-. split.
    + unfold send_raw_m, call_send in SR.
      destruct (S_io_send _ =? ti_io_send _); [|discriminate SR].
      destruct (io_send_m _ _ _) as [[B2 r2]|] eqn:IO; [|discriminate SR].
      apply wake_io_send_r in IO.
      destruct (r2 =? 0); injection SR as _ <-; unfold EIO in IO; lia.
    + unfold lib_frame. intros N. apply app_eq_nil in N as [_ N]. apply app_eq_nil in N as [_ N]. discriminate N.
Qed.

(* lengths of a world after writes inside it; HB : length B0 = Z.to_nat W_LEN for its base *)
Lemma wake_len_upd : forall (bs v : list byte) k L, length bs = L -> 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat L ->
  length (upd bs k v) = L.
Proof. intros bs v k L <- Hk Hl. apply length_upd; lia. Qed.

Ltac wlen HB := first [ exact HB | (apply wake_len_upd; [wlen HB | lia | rewrite ?length_put; lia]) ].

Ltac wside HB :=
  rewrite ?length_put;
  repeat match goal with
  | |- context [length (upd ?bs ?k ?v)] =>
      let L := fresh "L" in assert (L : length (upd bs k v) = Z.to_nat W_LEN) by (wlen HB); rewrite L; clear L
  end;
  try rewrite HB;
  lia.

(* a read of the world outside every write of an upd chain *)
Ltac wout HB := repeat first [ rewrite u_at_upd_out by wside HB | rewrite s32_at_upd_out by wside HB ].

(* A store of the model's u_at as the binary's sign-extended lw value writes the same 4 bytes. *)
Lemma wake_put4_s32 : forall bs k, put 4 (u_at bs k 4) = put 4 (s32_at bs k).
Proof.
  intros bs k. unfold put, s32_at.
  rewrite <- (Z_to_le_bytes_mod 4 (u_at bs k 4) 32), <- (Z_to_le_bytes_mod 4 (bv_swrap 32 (u_at bs k 4)) 32) by lia.
  f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite (Z.mod_eq (u_at bs k 4 + 2^31) (2^32)) by lia.
  replace (u_at bs k 4 + 2 ^ 31 - 2 ^ 32 * ((u_at bs k 4 + 2 ^ 31) / 2 ^ 32) - 2 ^ 31)
    with (u_at bs k 4 + (- ((u_at bs k 4 + 2 ^ 31) / 2 ^ 32)) * 2 ^ 32) by ring.
  symmetry. apply Z.mod_add. lia.
Qed.

(* The world after the binary's stores of :139-143 (memcpy of e2, then stats_tx_wakes++, inflight_len,
   inflight_counter, inflight_retries, inflight_sent_us, inflight) is the model's (frame, len, tx_wakes, then
   inflight_start's inflight, counter, retries, sent_us): the spans are disjoint, so the order does not matter. *)
Lemma wake_world : forall X (e2 : list byte) now, length X = Z.to_nat W_LEN -> length e2 = 60%nat ->
  upd (upd (upd (upd (upd (upd (upd X 1864 e2) 3384 (put 8 (Z.of_nat (length e2)))) 19872
      (put 8 (u64 (u_at (upd (upd X 1864 e2) 3384 (put 8 (Z.of_nat (length e2)))) 19872 8 + 1)))) 1860 (put 4 1))
      3392 (put 4 (u_at (upd (upd (upd X 1864 e2) 3384 (put 8 (Z.of_nat (length e2)))) 19872
          (put 8 (u64 (u_at (upd (upd X 1864 e2) 3384 (put 8 (Z.of_nat (length e2)))) 19872 8 + 1)))) 1808 4)))
      3396 (put 4 0)) 3400 (put 8 now)
  =
  upd (upd (upd (upd (upd (upd (upd X 1864 e2) 19872 (put 8 (u_at (upd X 1864 e2) 19872 8 + 1))) 3384 (put 8 60))
      3392 (put 4 (s32_at (upd X 1864 e2) 1808))) 3396 (put 4 0)) 3400 (put 8 now)) 1860 (put 4 1).
Proof.
  intros X e2 now HX HL.
  assert (Ew : W_LEN = 65616) by reflexivity.
  rewrite HL. change (Z.of_nat 60) with 60.
  assert (HY : length (upd X 1864 e2) = Z.to_nat W_LEN) by (wlen HX).
  set (Y := upd X 1864 e2) in *. clearbody Y.
  assert (V1 : u_at (upd Y 3384 (put 8 60)) 19872 8 = u_at Y 19872 8) by (wout HY; reflexivity).
  rewrite V1.
  assert (V2 : u_at (upd (upd Y 3384 (put 8 60)) 19872 (put 8 (u64 (u_at Y 19872 8 + 1)))) 1808 4 = u_at Y 1808 4)
    by (wout HY; reflexivity).
  rewrite V2, wake_put4_s32. unfold u64. rewrite put_mod64 by lia.
  rewrite (upd_upd_comm _ _ _ 3400 1860) by wside HY.
  rewrite (upd_upd_comm _ _ _ 3396 1860) by wside HY.
  rewrite (upd_upd_comm _ _ _ 3392 1860) by wside HY.
  rewrite (upd_upd_comm _ _ _ 19872 3384) by wside HY.
  reflexivity.
Qed.

(* A stack window stays a stack across a call that writes one cell and gives it back filled. *)
Lemma wake_stk_fill : forall m m' lo hi X c src,
  stk rsegs m lo hi -> munch [(X, X + Z.of_nat c)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' X [CB c src] -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi X c src (H1 & H2 & H) MU WM [[Hwf (HX & HXl & HB)] _].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in HXl, HB. rewrite app_nil_r in HXl, HB.
  split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (Z.leb_spec X a) as [L1|L1]; [destruct (Z.ltb_spec a (X + Z.of_nat c)) as [L2|L2]|].
  - rewrite <- Hl in L2.
    replace a with (X + Z.of_nat (Z.to_nat (a - X))) by lia.
    rewrite HB by lia.
    destruct (nth_error src (Z.to_nat (a - X))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

(* ---- from the plain diginet_session_close walk (close_relro .. close_notice_fail), renamed ---- *)

Lemma wake_relro : forall W m m', relro_img m -> munch W m m' ->
  (forall i, 0 <= i < RELRO_LEN -> outside W (RELRO_BASE + i)) -> relro_img m'.
Proof.
  intros W m m' RR MU HO i Hi. rewrite <- (RR i Hi). unfold mrd.
  rewrite (MU (wa (RELRO_BASE + i))); [reflexivity|].
  unfold wa. rewrite unsigned_lit by (unfold RELRO_BASE, RELRO_LEN in *; lia). apply HO. exact Hi.
Qed.

Lemma wake_tframe : forall m m' (sp sp' : word) K K' TF,
  tframe_at m sp K TF ->
  munch [(bv_unsigned sp - K, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  bv_unsigned sp - K <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp ->
  tframe_at m' sp' K' TF.
Proof.
  intros m m' sp sp' K K' [fr|] TFA MU H1 H2; [|exact I].
  destruct TFA as (P0 & BA & OW & OWin). unfold off_world, off_window in *.
  split; [exact P0|]. split; [|split; [exact OW | unfold off_window; lia]].
  apply (bytes_at_transport rsegs _ m m' _ _ BA MU). cbn [disjoint_from]. lia.
Qed.

Lemma wake_sub_app_l : forall (A R : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length A) ->
  sub (A ++ R) k n = sub A k n.
Proof.
  intros A R k n Hk Hn. unfold sub. rewrite skipn_app.
  replace (Z.to_nat k - length A)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app, length_skipn. replace (n - (length A - Z.to_nat k))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma wake_sub_app_r : forall (A R : list byte) k n, Z.of_nat (length A) <= k ->
  sub (A ++ R) k n = sub R (k - Z.of_nat (length A)) n.
Proof.
  intros A R k n Hk. unfold sub. rewrite skipn_app.
  replace (skipn (Z.to_nat k) A) with (@nil byte) by (symmetry; apply skipn_all2; lia).
  cbn [app]. f_equal. f_equal. lia.
Qed.

Lemma wake_s32_put : forall v, -2^31 <= v < 2^31 -> bv_swrap 32 (bytes_le_to_Z (put 4 v)) = v.
Proof.
  intros v Hv. rewrite bytes_le_to_Z_put. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2 ^ (8 * Z.of_nat 4)). change (bv_half_modulus 32) with (2 ^ 31).
  rewrite Zplus_mod_idemp_l. replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

(* A struct diginet_notice on the stack: one doubleword w holding kind and state, then the old state and the
   reason as words, the other 56 bytes 0. *)
Lemma wake_ntc : forall m p (sp' : word) K (w : word) kind st old why,
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window sp' K p 72 -> 0 <= bv_unsigned sp' - K ->
  bv_swrap 32 (bytes_le_to_Z (sub (le8 w) 0 4)) = kind -> bv_swrap 32 (bytes_le_to_Z (sub (le8 w) 4 4)) = st ->
  -2^31 <= old < 2^31 -> -2^31 <= why < 2^31 ->
  bytes_at rsegs m p ((le8 w ++ put 4 old ++ put 4 why) ++ repeat (Z_to_bv 8 0) 56) ->
  ntc_at m p (Ntc kind st old why 0 0 0 0 None [] 0) sp' K.
Proof.
  intros m p sp' K w kind st old why P0 P8 OW OWin SK KW SW Ho Hw BA.
  unfold ntc_at. cbn [n_kind n_state n_old n_reason n_pers n_mac_offset n_body_len n_counter n_retry n_body n_ann].
  split; [exact P0|]. split; [exact P8|]. split; [exact OW|]. split; [exact OWin|].
  set (P := le8 w ++ put 4 old ++ put 4 why).
  set (Z0 := repeat (Z_to_bv 8 0) 56).
  assert (L8 : Z.of_nat (length (le8 w)) = 8) by (rewrite length_le8; reflexivity).
  assert (L4 : forall v, Z.of_nat (length (put 4 v)) = 4) by (intros; rewrite length_put; reflexivity).
  assert (LP : Z.of_nat (length P) = 16) by (unfold P; rewrite !length_app, length_le8, !length_put; reflexivity).
  assert (HL : forall k n, 0 <= k -> k + Z.of_nat n <= 16 -> sub (P ++ Z0) k n = sub P k n)
    by (intros k n Hk' Hn'; apply wake_sub_app_l; lia).
  assert (V24 : bytes_le_to_Z (sub (P ++ Z0) 24 8) = 0)
    by (rewrite wake_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V32 : bytes_le_to_Z (sub (P ++ Z0) 32 8) = 0)
    by (rewrite wake_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V40 : bytes_le_to_Z (sub (P ++ Z0) 40 4) = 0)
    by (rewrite wake_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V48 : bytes_le_to_Z (sub (P ++ Z0) 48 8) = 0)
    by (rewrite wake_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V56 : bytes_le_to_Z (sub (P ++ Z0) 56 8) = 0)
    by (rewrite wake_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V64 : bytes_le_to_Z (sub (P ++ Z0) 64 4) = 0)
    by (rewrite wake_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V68 : bytes_le_to_Z (sub (P ++ Z0) 68 2) = 0)
    by (rewrite wake_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  exists (P ++ Z0).
  split; [exact BA|].
  split; [rewrite length_app; unfold P, Z0; rewrite !length_app, length_le8, !length_put, repeat_length; reflexivity|].
  unfold s32_at, u_at.
  rewrite (HL 0 4%nat), (HL 4 4%nat), (HL 8 4%nat), (HL 12 4%nat) by lia.
  assert (S0 : sub P 0 4 = sub (le8 w) 0 4) by (unfold P; apply wake_sub_app_l; lia).
  assert (S4 : sub P 4 4 = sub (le8 w) 4 4) by (unfold P; apply wake_sub_app_l; lia).
  assert (S8 : sub P 8 4 = put 4 old)
    by (unfold P; rewrite wake_sub_app_r by lia; rewrite L8;
        rewrite wake_sub_app_l by (rewrite ?L4; lia); apply sub_all, length_put).
  assert (S12 : sub P 12 4 = put 4 why)
    by (unfold P; rewrite wake_sub_app_r by lia; rewrite L8;
        rewrite wake_sub_app_r by (rewrite ?L4; lia); rewrite L4; apply sub_all, length_put).
  rewrite S0, S4, S8, S12, KW, SW, !wake_s32_put by lia.
  rewrite V24, V32, V40, V48, V56, V64, V68.
  cbn [length]. unfold off_world, off_window.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [apply bytes_at_nil; lia|].
  split; [left; unfold W_BASE_PLAIN; lia|].
  split; [left; lia|].
  reflexivity.
Qed.

Lemma wake_fail_upd : forall B k n v, length B = Z.to_nat W_LEN -> 0 <= k ->
  (k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) -> k + Z.of_nat n <= W_LEN ->
  length (upd B k (put n v)) = Z.to_nat W_LEN /\ g_fail_next (upd B k (put n v)) = g_fail_next B.
Proof.
  intros B k n v LB H0 Hk Hn. unfold OFF_g_fail_next, W_LEN in *. split.
  - rewrite length_upd_put; [exact LB | lia | rewrite LB; lia].
  - unfold g_fail_next. apply u_at_upd_out;
      [lia | unfold OFF_g_fail_next; lia | rewrite length_put; unfold OFF_g_fail_next; cbn; lia | rewrite length_put, LB; lia].
Qed.

Ltac wake_cf_side := unfold OFF_GOT, OFF_g_fail_next, W_LEN, A_S_state, OFF_g_s in *; cbn; lia.

(* notice of a state change that is not to ONLINE writes GOT only: g_fail_next is kept *)
Lemma wake_notice_fail : forall I Fr B B2 st old why,
  length B = Z.to_nat W_LEN -> st <> S_ONLINE ->
  notice_m I Fr B (Ntc DIGINET_N_STATE st old why 0 0 0 0 None [] 0) = Some (B2, tt) ->
  g_fail_next B2 = g_fail_next B.
Proof.
  intros I Fr B B2 st old why LB Hst HN.
  unfold notice_m in HN. cbn [n_kind n_state n_old n_reason] in HN.
  replace (DIGINET_N_STATE =? N_STATE) with true in HN by reflexivity.
  cbv beta iota zeta in HN.
  replace (st =? S_ONLINE) with false in HN by (symmetry; apply Z.eqb_neq; exact Hst).
  destruct (GOT_n B <? TRANS_MAX) eqn:G1.
  - destruct (GOT_n B <? 0) eqn:G2; cbv beta iota in HN; [discriminate HN|].
    destruct (int_inc (GOT_n B)) as [g1|]; cbv beta iota in HN; [|discriminate HN].
    injection HN as <-.
    apply Z.ltb_lt in G1. apply Z.ltb_ge in G2. unfold TRANS_MAX in G1.
    unfold set_GOT_n, set_GOT_t_reason, set_GOT_t_old, set_GOT_t_state, A_GOT_n, A_GOT_t_reason, A_GOT_t_old,
      A_GOT_t_state.
    destruct (wake_fail_upd B (OFF_GOT + 4 + 12 * GOT_n B + 0) 4 st LB) as [L1 F1];
      [wake_cf_side | wake_cf_side | wake_cf_side |].
    destruct (wake_fail_upd _ (OFF_GOT + 4 + 12 * GOT_n B + 4) 4 old L1) as [L2 F2];
      [wake_cf_side | wake_cf_side | wake_cf_side |].
    destruct (wake_fail_upd _ (OFF_GOT + 4 + 12 * GOT_n B + 8) 4 why L2) as [L3 F3];
      [wake_cf_side | wake_cf_side | wake_cf_side |].
    destruct (wake_fail_upd _ (OFF_GOT + 0) 4 g1 L3) as [L4 F4];
      [wake_cf_side | wake_cf_side | wake_cf_side |].
    rewrite F4, F3, F2, F1. reflexivity.
  - cbv beta iota in HN.
    destruct (int_inc (GOT_n B)) as [g1|]; cbv beta iota in HN; [|discriminate HN].
    injection HN as <-.
    unfold set_GOT_n, A_GOT_n.
    destruct (wake_fail_upd B (OFF_GOT + 0) 4 g1 LB) as [_ F1];
      [wake_cf_side | wake_cf_side | wake_cf_side |].
    exact F1.
Qed.

Theorem diginet_session_wake_holds :
  send_control_contract -> memcpy_contract -> memset_contract -> notice_contract ->
  diginet_session_wake_contract.
Proof.
  intros SC MCP MST NTC.
  unfold send_control_contract, send_control_ENTRY, send_control_FRAME in SC.
  unfold notice_contract, notice_ENTRY, notice_FRAME in NTC.
  unfold diginet_session_wake_contract, diginet_session_wake_ENTRY, diginet_session_wake_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo now r B B' TF A0 A1 Hnow WM GF HM TFa RO SP16 ST LO WO MI.
  subst a0 a1.
  unfold w_off_stack in WO.
  wk_facts.
  pose proof (wm_len _ _ _ _ WM) as HB0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -192)) = bv_unsigned sp + -192) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 848, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 48%nat ST.
  carve_frame 56%nat ST.
  carve_frame 16%nat ST.
  carve_frame 60%nat ST.
  carve_frame 4%nat ST.
  carve_frame 8%nat ST.
  (* prologue *)
  do 10 step.
  replace (bv_eqb (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
  cbv iota.
  step. step.
  change (s32_at B 1764) with (S_desk_known B).
  pose proof (s32_range B A_S_desk_known) as RK. change (s32_at B A_S_desk_known) with (S_desk_known B) in RK.
  step.
  rewrite wake_eqb by lia.
  unfold diginet_session_wake_m in HM.
  assert (EOg : OFF_g_s = 1648) by reflexivity.
  destruct (Z.eqb_spec (S_desk_known B) 0) as [K0|K0]; cbv iota.
  - (* desk not known: return DIGINET_E_ARG *)
    injection HM as <- <-.
    do 8 step.
    release_frame FR4 ST (bv_unsigned sp + -184).
    release_frame FR3 ST (bv_unsigned sp + -180).
    release_frame FR2 ST (bv_unsigned sp + -120).
    release_frame FR1 ST (bv_unsigned sp + -104).
    release_frame FR0 ST (bv_unsigned sp + -48).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WMO|]. split; [exact MI|]. split; [exact ST|]. split; [exact WM | exact GF].
  - cbv iota in HM.
    do 4 step.
    change (s32_at B 1784) with (S_foreign B).
    pose proof (s32_range B A_S_foreign) as RF. change (s32_at B A_S_foreign) with (S_foreign B) in RF.
    step.
    rewrite wake_eqb by lia.
    destruct (Z.eqb_spec (S_foreign B) 0) as [F0|F0]; cbv iota.
    + (* the wake *)
      cbv beta iota delta [negb] in HM.
      do 3 step.
      pose proof (wm_len _ _ _ _ WMw) as HB3.
      do 5 step.
      (* jal send_control *)
      step.
      change (set_S_wake_sent_us (set_S_wake_acked (set_S_e1_named_us B 0) 0) now)
        with (upd (upd (upd B 1788 (put 4 0)) 1792 (put 4 0)) 1800 (put 8 now)) in HM.
      destruct (send_control_m timg_plain TF (upd (upd (upd B 1788 (put 4 0)) 1792 (put 4 0)) 1800 (put 8 now))
                 DIGINET_CMD_WAKE 0) as [[B4 [r4 e2]]|] eqn:HSC; [|discriminate HM].
      eapply evt_cut.
      { eapply SC with (cmd := 226) (ack := 0) (kp := bv_unsigned sp + -180) (klp := bv_unsigned sp + -192)
                       (K := junk2) (KL := junk4) (lo := lo) (TF := TF).
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - lia.
        - lia.
        - right. split; [exact FR2|]. split.
          { unfold arg_blk, off_world, off_window. rewrite Hsp. lia. }
          split; [exact FR4|]. split.
          { unfold arg_blk, off_world, off_window. rewrite Hsp. lia. }
          split; [Z.div_mod_to_equations; lia|]. unfold blk_sep. lia.
        - exact WMw.
        - unfold g_fail_next. assert (EOf : OFF_g_fail_next = 64968) by reflexivity. wout HB0. exact GF.
        - exact HSC.
        - rewrite Hsp. Z.div_mod_to_equations. lia.
        - rewrite Hsp. exact ST.
        - rewrite Hsp. lia.
        - unfold w_off_stack. rewrite Hsp. lia.
        - exact MI. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 &
                  Eq & MUc & WMc & MI2 & ST2 & WM2 & GF2 & CELLS).
      subst ms'. rewrite Hsp in MUc, ST2.
      rewrite (proj2 (Z.eqb_neq (bv_unsigned sp + -180) 0)) in MUc by lia. cbn [app] in MUc.
      destruct CELLS as [Kz|[KC KLC]]; [lia|].
      clear WMw.
      transport_after_call rsegs m0 m2 MUc WMc. clear MUc WMc MI. try clear m0.
      rewrite (ret_pc_even 0x163f4) by (first [lia | reflexivity]).
      rename ST2 into ST.
      step.
      pose proof (wake_sc _ _ _ _ _ _ _ _ HSC) as [Rr Rf].
      rewrite wake_lts0 by exact Rr.
      destruct (Z.ltb_spec r4 0) as [Rn|Rn]; cbv iota; cbv iota in HM.
      * (* send_control failed: return its r *)
        injection HM as <- <-.
        do 8 step.
        release_frame KLC ST (bv_unsigned sp + -184).
        release_frame FR3 ST (bv_unsigned sp + -180).
        release_frame KC ST (bv_unsigned sp + -120).
        release_frame FR1 ST (bv_unsigned sp + -104).
        release_frame FR0 ST (bv_unsigned sp + -48).
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WMO|]. split; [exact MI2|]. split; [exact ST|]. split; [exact WM2 | exact GF2].
      * (* the frame was sent: keep it *)
        assert (Ne : e2 <> []) by (intros E; specialize (Rf E); lia).
        assert (Ke : (match e2 with [] => junk2 | _ :: _ => e2 end) = e2) by (destruct e2; [contradiction | reflexivity]).
        assert (Kl : (match e2 with [] => junk4 | _ :: _ => put 8 (Z.of_nat (length e2)) end) =
                     put 8 (Z.of_nat (length e2))) by (destruct e2; [contradiction | reflexivity]).
        rewrite Ke in KC. rewrite Kl in KLC. clear Ke Kl.
        assert (HL : length e2 = 60%nat) by (pose proof KC as [[[Hw _] _] _]; exact Hw).
        rewrite HL in KLC. change (Z.of_nat 60) with 60 in KLC.
        (* ld s2,0(sp): e2_len = 60 *)
        step.
        replace (bv_extract 0 64 (le_bytes_to_word (put 8 60))) with (Z_to_bv 64 60)
          by (apply bv_eq; vm_compute; reflexivity).
        (* memcpy (s->inflight_frame, e2, e2_len) *)
        do 3 step.
        step.
        pose proof KC as [[_ KB] _]. cbn [cells_bytes cbytes] in KB. rewrite app_nil_r in KB.
        pose proof (wm_len _ _ _ _ WM2) as HB4.
        eapply evt_cut.
        { eapply MCP with (src := e2).
          - rewrite unsigned_lit by lia. exact KB.
          - rewrite unsigned_lit by lia. exact HL.
          - apply (wm_piece rsegs W_BASE_PLAIN m2 B4 1864); [exact WM2 | vm_compute; reflexivity | lia | wk_side | wk_side].
          - rewrite !unsigned_lit by lia. lia.
          - exact MI2. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WOc & MI3 & DST3 & SRC3).
        subst ms'.
        rewrite (unsigned_lit (W_BASE_PLAIN + OFF_g_s + 216)) in MUc, DST3 by lia.
        change (bv_unsigned (Z_to_bv 64 60)) with 60 in MUc, DST3. change (Z.to_nat 60) with 60%nat in DST3.
        pose proof (wake_stk_fill _ _ _ _ _ 60%nat _ ST MUc WOc DST3) as ST3.
        wk_world_after_call rsegs m2 m3.
        transport_after_call rsegs m2 m3 MUc WOc. clear MUc WOc MI2. try clear m2.
        rename ST3 into ST.
        rewrite (ret_pc_even 0x1640c) by (first [lia | reflexivity]).
        (* li a0,0; the inlined inflight_start and stats_tx_wakes++; sw s1,212(s0) *)
        do 12 step.
        lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) _] |- _ => rename H into WM4 end.
        unfold inflight_start_m in HM. cbv beta iota zeta in HM.
        lazymatch type of HM with context [set_state_m _ _ ?P7 _ _] =>
        lazymatch type of WM4 with rw_cells _ _ _ [CB _ ?Mw] =>
          assert (EP : P7 = Mw) by exact (wake_world B4 e2 now HB4 HL)
        end end.
        rewrite EP in HM. clear EP.
        lazymatch type of WM4 with rw_cells _ _ _ [CB _ ?X] => set (W4 := X) in * end.
        assert (ES : S_state W4 = s32_at (upd B4 1864 e2) 1760).
        { unfold W4, S_state. change A_S_state with 1760. wout HB4. reflexivity. }
        assert (GW : g_fail_next W4 = g_fail_next B4).
        { unfold W4, g_fail_next. change OFF_g_fail_next with 64968. wout HB4. reflexivity. }
        pose proof (s32_range (upd B4 1864 e2) 1760) as RS.
        (* inlined set_state (WAKING, R_WAKE): beq s4,s1 *)
        step.
        rewrite wake_eqb by lia.
        unfold set_state_m in HM. rewrite ES in HM. cbv zeta in HM.
        change DIGINET_S_WAKING with 1 in HM. change DIGINET_R_WAKE with 1 in HM.
        revert HM. destruct (Z.eqb_spec (s32_at (upd B4 1864 e2) 1760) 1) as [S1|S1]; intro HM; cbv iota;
          cbv beta iota in HM.
        -- (* already WAKING: return 0 *)
          injection HM as <- <-.
          do 8 step.
          release_frame KLC ST (bv_unsigned sp + -184).
          release_frame FR3 ST (bv_unsigned sp + -180).
          release_frame KC ST (bv_unsigned sp + -120).
          release_frame FR1 ST (bv_unsigned sp + -104).
          release_frame FR0 ST (bv_unsigned sp + -48).
          release_frame FR ST (bv_unsigned sp).
          apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
          split; [exact MU|]. split; [exact WMO|]. split; [exact MI3|]. split; [exact ST|].
          split; [exact WM4 | rewrite GW; exact GF2].
        -- (* the state changes: the notice through s->notify *)
          unfold call_notify in HM.
          pose proof (wm_len _ _ _ _ WM4) as LW.
          assert (NS : S_notify (set_S_state W4 1) = S_notify W4).
          { unfold S_notify, set_S_state. change A_S_notify with 1744. change A_S_state with 1760.
            rewrite u_at_upd_out by wside LW. reflexivity. }
          assert (LS : length (set_S_state W4 1) = Z.to_nat W_LEN).
          { unfold set_S_state. change A_S_state with 1760. wlen LW. }
          assert (GS : g_fail_next (set_S_state W4 1) = g_fail_next W4).
          { unfold g_fail_next, set_S_state. change A_S_state with 1760. change OFF_g_fail_next with 64968.
            rewrite u_at_upd_out by wside LW. reflexivity. }
          rewrite NS in HM.
          revert HM. destruct (Z.eqb_spec (S_notify W4) (ti_notice timg_plain)) as [NT|NT];
            intro HM; cbv beta iota in HM; [|discriminate HM].
          revert HM.
          lazymatch goal with |- context [notice_m ?I ?Fr ?Bx ?n] =>
            set (NN := n); destruct (notice_m I Fr Bx NN) as [[B5 []]|] eqn:HN end;
            intro HM; cbv beta iota in HM; [|discriminate HM].
          injection HM as <- <-.
          (* addi a0,sp,88; li a2,56; li a1,0; jal memset *)
          do 3 step. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
          eapply evt_cut.
          { eapply MST; [ | exact MI3 ].
            rewrite (unsigned_lit (bv_unsigned sp + -104)) by lia.
            change (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) with 56%nat. exact FR0. }
          intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & Eq & MUc & WMc & MI5 & FRm).
          subst ms'.
          rewrite (unsigned_lit (bv_unsigned sp + -104)) in MUc, FRm by lia.
          change (bv_unsigned (Z_to_bv 64 56)) with 56 in MUc, FRm.
          change (Z.to_nat 56) with 56%nat in FRm.
          change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in FRm.
          transport_after_call rsegs m4 m5 MUc WMc. clear MUc WMc MI3. try clear m4.
          rename FRm into FR0.
          rewrite (ret_pc_even 0x16450) by (first [lia | reflexivity]).
          (* slli a1,s1,32; ld a2,96(s0) = S_notify *)
          step. step.
          change (u_at W4 1744 8) with (S_notify W4).
          rewrite NT. change (ti_notice timg_plain) with 84452.
          (* ld a0,104(s0); addi a1,a1,2; sd a1,72(sp); sw s4,80(sp); sw s1,84(sp) *)
          do 5 step.
          (* sw s1,112(s0): the state becomes WAKING *)
          step.
          lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) _] |- _ => rename H into WM5 end.
          change (upd W4 1760 (put 4 1)) with (set_S_state W4 1) in WM5.
          (* addi a1,sp,72; jalr a2: notice *)
          step. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m6 end.
          lazymatch goal with H : mem_inv rsegs m6 |- _ => rename H into MI6 end.
          assert (NTCa : ntc_at m6 (bv_unsigned sp + -120) NN (Z_to_bv 64 (bv_unsigned sp + -192)) 48).
          { unfold NN. change DIGINET_N_STATE with 2.
            apply (wake_ntc _ _ _ _ (Z_to_bv 64 4294967298));
              [ lia | Z.div_mod_to_equations; lia | unfold off_world; lia
              | unfold off_window; rewrite Hsp; lia | rewrite Hsp; lia | vm_compute; reflexivity
              | vm_compute; reflexivity | exact RS | lia | ].
            pose proof FR1 as [[_ BA] _]. pose proof FR0 as [[_ BM] _].
            cbn [cells_bytes cbytes] in BA, BM. rewrite !le4_put in BA. rewrite app_nil_r in BA, BM.
            apply bytes_at_app. split; [exact BA|].
            rewrite !length_app, length_le8, !length_put.
            replace (bv_unsigned sp + -120 + Z.of_nat (8 + (4 + 4))) with (bv_unsigned sp + -104) by lia.
            exact BM. }
          eapply evt_cut.
          { eapply NTC with (p := bv_unsigned sp + -120) (n := NN) (Fr := TF) (B := set_S_state W4 1) (B' := B5)
              (lo := lo);
            [ reflexivity | exact NTCa
            | apply (wake_tframe m m6 sp _ 848 48 TF TFa MU); rewrite Hsp; lia
            | apply (wake_relro _ m m6 RO MU); intros i Hi; cbn [outside]; repeat split;
              unfold RELRO_BASE, RELRO_LEN in *; lia
            | exact WM5 | exact HN | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST
            | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI6 ]. }
          intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & Eq & MUc & WMc & MI7 & ST7 & WM7).
          subst ms'. rewrite Hsp in MUc, ST7.
          clear WM5 NTCa.
          transport_after_call rsegs m6 m7 MUc WMc. clear MUc WMc MI6. try clear m6.
          rename ST7 into ST.
          rewrite (ret_pc_even 0x16478) by (first [lia | reflexivity]).
          (* li a0,0; j 163b0; the epilogue *)
          step. step.
          do 8 step.
          release_frame KLC ST (bv_unsigned sp + -184).
          release_frame FR3 ST (bv_unsigned sp + -180).
          release_frame KC ST (bv_unsigned sp + -120).
          release_frame FR1 ST (bv_unsigned sp + -104).
          release_frame FR0 ST (bv_unsigned sp + -48).
          release_frame FR ST (bv_unsigned sp).
          unfold NN in HN.
          pose proof (wake_notice_fail timg_plain TF _ B5 1 (s32_at (upd B4 1864 e2) 1760) 1 LS
            ltac:(unfold S_ONLINE; lia) HN) as GN.
          apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
          split; [exact MU|]. split; [exact WMO|]. split; [exact MI7|]. split; [exact ST|].
          split; [exact WM7 | rewrite GN, GS, GW; exact GF2].
    + (* foreign: refused *)
      cbv beta iota delta [negb] in HM.
      injection HM as <- <-.
      do 4 step.
      do 8 step.
      release_frame FR4 ST (bv_unsigned sp + -184).
      release_frame FR3 ST (bv_unsigned sp + -180).
      release_frame FR2 ST (bv_unsigned sp + -120).
      release_frame FR1 ST (bv_unsigned sp + -104).
      release_frame FR0 ST (bv_unsigned sp + -48).
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WMO|]. split; [exact MI|]. split; [exact ST|].
      assert (EB : set_S_stats_refused B (u64 (S_stats_refused B + 1)) = upd B 19904 (put 8 (u_at B 19904 8 + 1))).
      { unfold set_S_stats_refused, S_stats_refused, u64. rewrite put_mod64 by lia. reflexivity. }
      rewrite EB. split; [exact WMw|].
      unfold g_fail_next. assert (EOf : OFF_g_fail_next = 64968) by reflexivity. wout HB0. exact GF.
Qed.

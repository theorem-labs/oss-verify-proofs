(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 533 of its 587 lines of code are new or changed and 395 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_frame/lib/Prog/diginet_frame_build.v, with its module paths, module names and numbers changed; 359 of its 417 lines of code are new or changed and 529 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import send_control_c notice_c
  diginet_session_close_c.
Import ListNotations.
Open Scope Z_scope.

Lemma close_eqb : forall v w, -2^63 <= v < 2^63 -> -2^63 <= w < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
  intros v w Hv Hw. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v w) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  assert (Q : (v - w) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in Q; [|lia]. destruct Q as [c Ec]. nia.
Qed.

Lemma close_split2 : forall m A B cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [assumption|]|].
    + rewrite cells_bytes_length in B2 by assumption. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply Hw. lia.
Qed.

Lemma close_join2 : forall m A B cs1 cs2,
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

Lemma close_relro : forall W m m', relro_img m -> munch W m m' ->
  (forall i, 0 <= i < RELRO_LEN -> outside W (RELRO_BASE + i)) -> relro_img m'.
Proof.
  intros W m m' RR MU HO i Hi. rewrite <- (RR i Hi). unfold mrd.
  rewrite (MU (wa (RELRO_BASE + i))); [reflexivity|].
  unfold wa. rewrite unsigned_lit by (unfold RELRO_BASE, RELRO_LEN in *; lia). apply HO. exact Hi.
Qed.

Lemma close_tframe : forall m m' (sp sp' : word) K K' TF,
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

Lemma close_sub_app_l : forall (A R : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length A) ->
  sub (A ++ R) k n = sub A k n.
Proof.
  intros A R k n Hk Hn. unfold sub. rewrite skipn_app.
  replace (Z.to_nat k - length A)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app, length_skipn. replace (n - (length A - Z.to_nat k))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma close_sub_app_r : forall (A R : list byte) k n, Z.of_nat (length A) <= k ->
  sub (A ++ R) k n = sub R (k - Z.of_nat (length A)) n.
Proof.
  intros A R k n Hk. unfold sub. rewrite skipn_app.
  replace (skipn (Z.to_nat k) A) with (@nil byte) by (symmetry; apply skipn_all2; lia).
  cbn [app]. f_equal. f_equal. lia.
Qed.

Lemma close_s32_put : forall v, -2^31 <= v < 2^31 -> bv_swrap 32 (bytes_le_to_Z (put 4 v)) = v.
Proof.
  intros v Hv. rewrite bytes_le_to_Z_put. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2 ^ (8 * Z.of_nat 4)). change (bv_half_modulus 32) with (2 ^ 31).
  rewrite Zplus_mod_idemp_l. replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

(* A struct diginet_notice on the stack: one doubleword w holding kind and state, then the old state and the
   reason as words, the other 56 bytes 0. *)
Lemma close_ntc : forall m p (sp' : word) K (w : word) kind st old why,
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
    by (intros k n Hk' Hn'; apply close_sub_app_l; lia).
  assert (V24 : bytes_le_to_Z (sub (P ++ Z0) 24 8) = 0)
    by (rewrite close_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V32 : bytes_le_to_Z (sub (P ++ Z0) 32 8) = 0)
    by (rewrite close_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V40 : bytes_le_to_Z (sub (P ++ Z0) 40 4) = 0)
    by (rewrite close_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V48 : bytes_le_to_Z (sub (P ++ Z0) 48 8) = 0)
    by (rewrite close_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V56 : bytes_le_to_Z (sub (P ++ Z0) 56 8) = 0)
    by (rewrite close_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V64 : bytes_le_to_Z (sub (P ++ Z0) 64 4) = 0)
    by (rewrite close_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  assert (V68 : bytes_le_to_Z (sub (P ++ Z0) 68 2) = 0)
    by (rewrite close_sub_app_r by lia; rewrite LP; vm_compute; reflexivity).
  exists (P ++ Z0).
  split; [exact BA|].
  split; [rewrite length_app; unfold P, Z0; rewrite !length_app, length_le8, !length_put, repeat_length; reflexivity|].
  unfold s32_at, u_at.
  rewrite (HL 0 4%nat), (HL 4 4%nat), (HL 8 4%nat), (HL 12 4%nat) by lia.
  assert (S0 : sub P 0 4 = sub (le8 w) 0 4) by (unfold P; apply close_sub_app_l; lia).
  assert (S4 : sub P 4 4 = sub (le8 w) 4 4) by (unfold P; apply close_sub_app_l; lia).
  assert (S8 : sub P 8 4 = put 4 old)
    by (unfold P; rewrite close_sub_app_r by lia; rewrite L8;
        rewrite close_sub_app_l by (rewrite ?L4; lia); apply sub_all, length_put).
  assert (S12 : sub P 12 4 = put 4 why)
    by (unfold P; rewrite close_sub_app_r by lia; rewrite L8;
        rewrite close_sub_app_r by (rewrite ?L4; lia); rewrite L4; apply sub_all, length_put).
  rewrite S0, S4, S8, S12, KW, SW, !close_s32_put by lia.
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

Lemma close_fail_upd : forall B k n v, length B = Z.to_nat W_LEN -> 0 <= k ->
  (k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) -> k + Z.of_nat n <= W_LEN ->
  length (upd B k (put n v)) = Z.to_nat W_LEN /\ g_fail_next (upd B k (put n v)) = g_fail_next B.
Proof.
  intros B k n v LB H0 Hk Hn. unfold OFF_g_fail_next, W_LEN in *. split.
  - rewrite length_upd_put; [exact LB | lia | rewrite LB; lia].
  - unfold g_fail_next. apply u_at_upd_out;
      [lia | unfold OFF_g_fail_next; lia | rewrite length_put; unfold OFF_g_fail_next; cbn; lia | rewrite length_put, LB; lia].
Qed.

Ltac cf_side := unfold OFF_GOT, OFF_g_fail_next, W_LEN, A_S_state, OFF_g_s in *; cbn; lia.

(* notice of a state change that is not to ONLINE writes GOT only: g_fail_next is kept *)
Lemma close_notice_fail : forall I Fr B B2 st old why,
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
    destruct (close_fail_upd B (OFF_GOT + 4 + 12 * GOT_n B + 0) 4 st LB) as [L1 F1];
      [cf_side | cf_side | cf_side |].
    destruct (close_fail_upd _ (OFF_GOT + 4 + 12 * GOT_n B + 4) 4 old L1) as [L2 F2];
      [cf_side | cf_side | cf_side |].
    destruct (close_fail_upd _ (OFF_GOT + 4 + 12 * GOT_n B + 8) 4 why L2) as [L3 F3];
      [cf_side | cf_side | cf_side |].
    destruct (close_fail_upd _ (OFF_GOT + 0) 4 g1 L3) as [L4 F4];
      [cf_side | cf_side | cf_side |].
    rewrite F4, F3, F2, F1. reflexivity.
  - cbv beta iota in HN.
    destruct (int_inc (GOT_n B)) as [g1|]; cbv beta iota in HN; [|discriminate HN].
    injection HN as <-.
    unfold set_GOT_n, A_GOT_n.
    destruct (close_fail_upd B (OFF_GOT + 0) 4 g1 LB) as [_ F1];
      [cf_side | cf_side | cf_side |].
    exact F1.
Qed.

Theorem diginet_session_close_holds :
  send_control_contract -> memset_contract -> notice_contract -> diginet_session_close_contract.
Proof.
  intros SC MSET NOT.
  unfold send_control_contract, send_control_ENTRY, send_control_FRAME in SC.
  unfold memset_contract, MEMSET in MSET.
  unfold notice_contract, notice_ENTRY, notice_FRAME in NOT.
  unfold diginet_session_close_contract, diginet_session_close_ENTRY, diginet_session_close_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    now r B B' TF A0 A1 Hnow WM GF HM TFA RR SP16 ST LO WO MI.
  subst a0 a1.
  unfold w_off_stack in WO.
  wk_facts.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 768, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  unfold diginet_session_close_m in HM. cbv zeta in HM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 112%nat ST.
  do 6 step.
  rename m into mI. rename MU into MU0. rename WMO into WM0.
  lazymatch goal with HF : rw_cells _ ?mm (bv_unsigned sp + -112) ?cs |- _ =>
    rename mm into m1; set (FRC := cs) in HF; rename HF into FR end.
  assert (Us : bv_unsigned (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) = W_BASE_PLAIN + OFF_g_s)
    by (apply unsigned_lit; unfold W_BASE_PLAIN, OFF_g_s; lia).
  assert (Eg : OFF_g_s = 1648) by reflexivity.
  assert (TAIL : forall (m2 : word -> option byte) (B1 : list byte) (r1 : Z)
                 (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -112) FRC ->
    stk rsegs m2 lo (bv_unsigned sp + -112) ->
    munch [(bv_unsigned sp - 768, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m2 ->
    wmono rsegs mI m2 -> mem_inv rsegs m2 ->
    wmem rsegs m2 B1 -> g_fail_next B1 <= 1 ->
    match set_state_m timg_plain TF (set_S_inflight B1 0) DIGINET_S_CLOSED DIGINET_R_CLOSED with
    | Some (B2, _) => Some (B2, r1)
    | None => None
    end = Some (B', r) ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 r1) x10 x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x16598) fc None m2 (seg_rom rsegs))).
  { intros m2 B1 r1 ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR2 ST2 MU2 WM2 MI2 WW2 GF2 HM2.
    pose proof (wm_len _ _ _ _ WW2) as LB1.
    (* lw s3,112(s0) *)
    step. change (s32_at B1 1760) with (S_state B1).
    pose proof (s32_range B1 A_S_state) as RS1. change (s32_at B1 A_S_state) with (S_state B1) in RS1.
    (* li s2,3; sw zero,212(s0) *)
    step. step.
    change (upd B1 1860 (put 4 0)) with (set_S_inflight B1 0) in *.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) _] |- _ => rename H into WW3 end.
    lazymatch goal with H : munch _ mI _ |- _ => rename H into MU3 end.
    lazymatch goal with H : wmono rsegs mI _ |- _ => rename H into WM3 end.
    lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI3 end.
    (* beq s3,s2 *)
    step.
    rewrite close_eqb by lia.
    assert (SI : S_state (set_S_inflight B1 0) = S_state B1).
    { unfold S_state, set_S_inflight. apply s32_at_upd_out;
        [ unfold A_S_inflight, OFF_g_s; lia | unfold A_S_state, OFF_g_s; lia
        | rewrite length_put; unfold A_S_state, A_S_inflight, OFF_g_s; cbn; lia
        | rewrite length_put, LB1; unfold A_S_inflight, OFF_g_s, W_LEN; cbn; lia ]. }
    assert (GI : g_fail_next (set_S_inflight B1 0) = g_fail_next B1).
    { unfold g_fail_next, set_S_inflight. apply u_at_upd_out;
        [ unfold A_S_inflight, OFF_g_s; lia | unfold OFF_g_fail_next; lia
        | rewrite length_put; unfold OFF_g_fail_next, A_S_inflight, OFF_g_s; cbn; lia
        | rewrite length_put, LB1; unfold A_S_inflight, OFF_g_s, W_LEN; cbn; lia ]. }
    unfold set_state_m in HM2. rewrite SI in HM2. cbv zeta in HM2.
    change (S_state B1 =? DIGINET_S_CLOSED) with (S_state B1 =? 3) in HM2.
    revert HM2. destruct (Z.eqb_spec (S_state B1) 3) as [C3|C3]; intro HM2; cbv beta iota delta [negb];
      cbv beta iota in HM2.
    - (* already closed: return r1 *)
      injection HM2 as EB ER.
      rewrite ER. unfold FRC in FR2.
      step. do 5 step.
      release_frame FR2 ST2 (bv_unsigned sp).
      do 2 step.
      apply evt_done. unfold QQ. do 14 eexists. eexists. split; [reflexivity|].
      split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST2|].
      split; [rewrite <- EB; exact WW3 | rewrite <- EB, GI; exact GF2].
    - (* the state changes: the notice of set_state *)
      unfold call_notify in HM2.
      assert (LI : length (set_S_inflight B1 0) = Z.to_nat W_LEN).
      { unfold set_S_inflight. rewrite length_upd_put; [exact LB1 | unfold A_S_inflight, OFF_g_s; lia
          | rewrite LB1; unfold A_S_inflight, OFF_g_s, W_LEN; cbn; lia]. }
      assert (NS : S_notify (set_S_state (set_S_inflight B1 0) DIGINET_S_CLOSED) = S_notify (set_S_inflight B1 0)).
      { unfold S_notify, set_S_state. apply u_at_upd_out;
          [ unfold A_S_state, OFF_g_s; lia | unfold A_S_notify, OFF_g_s; lia
          | rewrite length_put; unfold A_S_state, A_S_notify, OFF_g_s; cbn; lia
          | rewrite length_put, LI; unfold A_S_state, OFF_g_s, W_LEN; cbn; lia ]. }
      rewrite NS in HM2.
      revert HM2. destruct (Z.eqb_spec (S_notify (set_S_inflight B1 0)) (ti_notice timg_plain)) as [NT|NT];
        intro HM2; cbv beta iota in HM2; [|discriminate HM2].
      revert HM2.
      lazymatch goal with |- context [notice_m ?I ?Fr ?Bx ?n] =>
        set (NN := n); destruct (notice_m I Fr Bx NN) as [[B2 []]|] eqn:HN end;
        intro HM2; cbv beta iota in HM2; [|discriminate HM2].
      injection HM2 as EB ER.
      unfold FRC in FR2.
      pose proof (rw_cells_split_CB rsegs _ (bv_unsigned sp + -112) [] 72 _ _ [16%nat; 56%nat] FR2 eq_refl) as FRx.
      clear FR2. cbn [app mk_CB_cells] in FRx.
      destruct (close_split2 _ _ (bv_unsigned sp + -96) [CB 16 _] _ FRx ltac:(cbn [cells_size csize]; lia))
        as [FRa FRx2].
      destruct (close_split2 _ _ (bv_unsigned sp + -40) [CB 56 _] _ FRx2 ltac:(cbn [cells_size csize]; lia))
        as [FRm FRs].
      clear FRx FRx2.
      do 3 step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      assert (U96 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
      eapply evt_cut.
      { eapply MSET; [ | exact MI3 ].
        rewrite U96. change (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) with 56%nat. exact FRm. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & Eq & MUc & WMc & MI4 & FRm4).
      subst ms'.
      rewrite U96 in MUc, FRm4. change (bv_unsigned (Z_to_bv 64 56)) with 56 in MUc, FRm4.
      change (Z.to_nat 56) with 56%nat in FRm4.
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in FRm4.
      clear FRm.
      transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3. try clear m3.
      rewrite (ret_pc_even 0x165b8) by (first [lia | reflexivity]).
      (* slli a1,s2,32; li a2,8; ld a3,96(s0) = S_notify *)
      step. step. step.
      change (u_at (set_S_inflight B1 0) 1744 8) with (S_notify (set_S_inflight B1 0)).
      rewrite NT. change (ti_notice timg_plain) with 84452.
      (* ld a0,104(s0); addi a1,a1,2; sd a1,0(sp); sw s3,8(sp); sw a2,12(sp) *)
      step. step. step. step. step.
      (* sw s2,112(s0): the state becomes CLOSED *)
      step.
      lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) _] |- _ => rename H into WMw end.
      change (upd (set_S_inflight B1 0) 1760 (put 4 3)) with (set_S_state (set_S_inflight B1 0) DIGINET_S_CLOSED) in WMw.
      (* mv a1,sp; jalr a3: notice *)
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
      lazymatch goal with H : munch _ mI m5 |- _ => rename H into MU5 end.
      lazymatch goal with H : wmono rsegs mI m5 |- _ => rename H into WM5 end.
      lazymatch goal with H : mem_inv rsegs m5 |- _ => rename H into MI5 end.
      lazymatch goal with H : stk rsegs m5 lo _ |- _ => rename H into ST5 end.
      assert (NTC : ntc_at m5 (bv_unsigned sp + -112) NN (Z_to_bv 64 (bv_unsigned sp + -112)) 48).
      { unfold NN. change DIGINET_N_STATE with 2. change DIGINET_S_CLOSED with 3. change DIGINET_R_CLOSED with 8.
        apply (close_ntc _ _ _ _ (Z_to_bv 64 12884901890));
          [ lia | Z.div_mod_to_equations; lia | unfold off_world; lia
          | unfold off_window; rewrite Hsp; lia | rewrite Hsp; lia | vm_compute; reflexivity | vm_compute; reflexivity
          | exact RS1 | lia | ].
        pose proof FRa as [[_ BA] _]. pose proof FRm4 as [[_ BM] _].
        cbn [cells_bytes cbytes] in BA, BM. rewrite !le4_put in BA. rewrite app_nil_r in BA, BM.
        apply bytes_at_app. split; [exact BA|].
        rewrite !length_app, length_le8, !length_put.
        replace (bv_unsigned sp + -112 + Z.of_nat (8 + (4 + 4))) with (bv_unsigned sp + -96) by lia.
        exact BM. }
      eapply evt_cut.
      { eapply NOT with (p := bv_unsigned sp + -112) (n := NN) (Fr := TF)
          (B := set_S_state (set_S_inflight B1 0) DIGINET_S_CLOSED) (B' := B2) (lo := lo);
        [ reflexivity | exact NTC
        | apply (close_tframe mI m5 sp _ 768 48 TF TFA MU5); rewrite Hsp; lia
        | apply (close_relro _ mI m5 RR MU5); intros i Hi; cbn [outside]; repeat split;
          unfold RELRO_BASE, RELRO_LEN in *; lia
        | exact WMw | exact HN | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST5
        | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI5 ]. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & Eq & MUc & WMc & MI6 & ST6 & WM6).
      subst ms'. rewrite Hsp in MUc, ST6.
      clear WMw NTC.
      transport_after_call rsegs m5 m6 MUc WMc. clear MUc WMc MI5. try clear m5.
      rewrite (ret_pc_even 0x165e4) by (first [lia | reflexivity]).
      (* j 165ec; mv a0,s1 *)
      step. step.
      pose proof (close_join2 _ _ (bv_unsigned sp + -96) _ _ FRa ltac:(cbn [cells_size csize]; lia) FRm4) as FRam.
      pose proof (close_join2 _ _ (bv_unsigned sp + -40) _ _ FRam ltac:(cbn [cells_size csize app]; lia) FRs) as FR6.
      clear FRa FRm4 FRs FRam. cbn [app] in FR6.
      do 5 step.
      release_frame FR6 ST6 (bv_unsigned sp).
      do 2 step.
      rewrite ER.
      lazymatch goal with H : munch _ mI _ |- _ => rename H into MU7 end.
      lazymatch goal with H : wmono rsegs mI _ |- _ => rename H into WM7 end.
      assert (LS : length (set_S_inflight B1 0) = Z.to_nat W_LEN) by exact LI.
      assert (GS : g_fail_next (set_S_state (set_S_inflight B1 0) DIGINET_S_CLOSED) = g_fail_next (set_S_inflight B1 0))
        by exact (proj2 (close_fail_upd _ A_S_state 4 DIGINET_S_CLOSED LI ltac:(cf_side) ltac:(cf_side) ltac:(cf_side))).
      assert (LS2 : length (set_S_state (set_S_inflight B1 0) DIGINET_S_CLOSED) = Z.to_nat W_LEN)
        by exact (proj1 (close_fail_upd _ A_S_state 4 DIGINET_S_CLOSED LI ltac:(cf_side) ltac:(cf_side) ltac:(cf_side))).
      unfold NN in HN.
      pose proof (close_notice_fail timg_plain TF _ B2 DIGINET_S_CLOSED (S_state B1) DIGINET_R_CLOSED LS2
        ltac:(unfold DIGINET_S_CLOSED, S_ONLINE; lia) HN) as GN.
      apply evt_done. unfold QQ. do 14 eexists. eexists. split; [reflexivity|].
      split; [exact MU7|]. split; [exact WM7|]. split; [exact MI6|]. split; [exact ST6|].
      split; [rewrite <- EB; exact WM6 | rewrite <- EB, GN, GS, GI; exact GF2]. }

  (* beqz a0: s = &g_s is not NULL *)
  step.
  change (bv_eqb (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 0)) with false. cbv iota.
  (* mv s0,a0; lw a0,116(a0): desk_known *)
  step. step.
  change (s32_at B 1764) with (S_desk_known B).
  pose proof (s32_range B A_S_desk_known) as RDK. change (s32_at B A_S_desk_known) with (S_desk_known B) in RDK.
  step.
  rewrite close_eqb by lia.
  revert HM. destruct (Z.eqb_spec (S_desk_known B) 0) as [DK|DK]; intro HM; cbv beta iota delta [negb]; cbn [negb andb] in HM.
  { (* desk_known = 0: li s1,0 *)
    step.
    eapply TAIL; [exact FR | exact ST | exact MU0 | exact WM0 | exact MI | exact WM | exact GF | exact HM]. }
  step.
  change (s32_at B 1784) with (S_foreign B).
  pose proof (s32_range B A_S_foreign) as RFO. change (s32_at B A_S_foreign) with (S_foreign B) in RFO.
  step.
  rewrite close_eqb by lia.
  revert HM. destruct (Z.eqb_spec (S_foreign B) 0) as [FO|FO]; intro HM; cbv beta iota delta [negb]; cbn [negb andb] in HM.
  2: { (* foreign: li s1,0 *)
    step.
    eapply TAIL; [exact FR | exact ST | exact MU0 | exact WM0 | exact MI | exact WM | exact GF | exact HM]. }
  step.
  change (s32_at B 1760) with (S_state B).
  pose proof (s32_range B A_S_state) as RST. change (s32_at B A_S_state) with (S_state B) in RST.
  step. step.
  rewrite close_eqb by lia.
  change (S_state B =? DIGINET_S_CLOSED) with (S_state B =? 3) in HM.
  revert HM. destruct (Z.eqb_spec (S_state B) 3) as [S3|S3]; intro HM; cbv beta iota delta [negb]; cbn [negb andb] in HM.
  { (* closed already: li s1,0 *)
    step.
    eapply TAIL; [exact FR | exact ST | exact MU0 | exact WM0 | exact MI | exact WM | exact GF | exact HM]. }
  (* send_control (s, DIGINET_CMD_DISCONNECT, 0, NULL, NULL) *)
  revert HM. destruct (send_control_m timg_plain TF B DIGINET_CMD_DISCONNECT 0) as [[B1 [r1 f1]]|] eqn:HS;
    intro HM; cbv beta iota in HM; [|discriminate HM].
  do 5 step. step.
  eapply evt_cut.
  { eapply SC with (K := []) (KL := []) (TF := TF) (B := B) (B' := B1) (r := r1) (f := f1) (cmd := 227) (ack := 0)
      (kp := 0) (klp := 0) (lo := lo);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | left; reflexivity
      | exact WM | exact GF | exact HS | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST
      | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2 & WM2 & GF2 & _).
  subst ms'. rewrite Hsp in MUc, ST2. clear WM.
  change (0 =? 0) with true in MUc. cbv beta iota in MUc. rewrite app_nil_r in MUc.
  transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI. try clear m1.
  rewrite (ret_pc_even 0x16624) by (first [lia | reflexivity]).
  step. step.
  eapply TAIL; [exact FR | exact ST2 | exact MU0 | exact WM0 | exact MI2 | exact WM2 | exact GF2 | exact HM].
Qed.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TNeed
  TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
  send_control_c set_state_c diginet_session_wake_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- machine helpers ---- *)

Lemma wake_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* a branch on a closed condition *)
Ltac wake_closed_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* rw_cells of a list split at a cell boundary, and joined back *)
Lemma wake_rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2.
  rewrite cells_size_app in Hw. destruct Hw as (Ha & Hn & Hw).
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma wake_rw_cells_cat : forall segs m A A2 cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m A2 cs2 -> A2 = A + Z.of_nat (cells_size cs1) ->
  rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A A2 cs1 cs2 [[W1 B1] (Ha1 & Hn1 & Hw1)] [[W2 B2] (Ha2 & Hn2 & Hw2)] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply (proj2 (bytes_at_app segs m A _ _)). split; [exact B1|].
    rewrite (cells_bytes_length cs1 W1). exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [L|L].
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

(* wake's 112-byte frame after the prologue: e2_len at sp (8), 4 bytes, e2[60] at sp + 12, the five saved
   registers at sp + 72; split into the cells send_control's keep premise asks for, and joined back *)
Lemma wake_frame_split : forall segs m A j cs,
  rw_cells segs m A (CB 72 j :: cs) ->
  exists j0 j1 j2, rw_cells segs m A [CB 8 j0] /\ rw_cells segs m (A + 8) [CB 4 j1] /\
    rw_cells segs m (A + 12) [CB 60 j2] /\ rw_cells segs m (A + 72) cs.
Proof.
  intros segs m A j cs H.
  apply (rw_cells_split_CB segs m A [] 72 j cs [8; 4; 60]%nat) in H; [|reflexivity].
  cbn [app mk_CB_cells] in H.
  apply (wake_rw_cells_app segs m A [_]) in H. destruct H as [H0 H].
  apply (wake_rw_cells_app segs m _ [_]) in H. destruct H as [H1 H].
  apply (wake_rw_cells_app segs m _ [_]) in H. destruct H as [H2 H3].
  cbn [cells_size csize Nat.add] in H1, H2, H3.
  do 3 eexists. split; [exact H0|]. split; [|split].
  - replace (A + 8) with (A + Z.of_nat 8) by lia. exact H1.
  - replace (A + 12) with (A + Z.of_nat 8 + Z.of_nat 4) by lia. exact H2.
  - replace (A + 72) with (A + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 60) by lia. exact H3.
Qed.

Lemma wake_frame_merge : forall segs m A c0 c1 c2 cs,
  rw_cells segs m A [c0] -> rw_cells segs m (A + 8) [c1] -> rw_cells segs m (A + 12) [c2] ->
  rw_cells segs m (A + 72) cs -> csize c0 = 8%nat -> csize c1 = 4%nat -> csize c2 = 60%nat ->
  rw_cells segs m A (c0 :: c1 :: c2 :: cs).
Proof.
  intros segs m A c0 c1 c2 cs H0 H1 H2 H3 E0 E1 E2.
  change (c0 :: c1 :: c2 :: cs) with ([c0] ++ [c1] ++ [c2] ++ cs).
  apply (wake_rw_cells_cat segs m A (A + 8)); [exact H0 | | cbn [cells_size]; rewrite E0; lia].
  apply (wake_rw_cells_cat segs m (A + 8) (A + 12)); [exact H1 | | cbn [cells_size]; rewrite E1; lia].
  apply (wake_rw_cells_cat segs m (A + 12) (A + 72)); [exact H2 | exact H3 | cbn [cells_size]; rewrite E2; lia].
Qed.

Lemma wake_cb_len : forall segs m A n bs, rw_cells segs m A [CB n bs] -> length bs = n.
Proof. intros segs m A n bs [[Hwf _] _]. exact (proj1 Hwf). Qed.

Lemma wake_cb_bytes : forall segs m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs.
Proof. intros segs m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma wake_c8_head : forall segs m A (w : word) cs,
  rw_cells segs m A (CB 8 (le8 w) :: cs) -> rw_cells segs m A (C8 w :: cs).
Proof.
  intros segs m A w cs [[Hwf Hb] Hw]. split; [split|].
  - split; [exact I | exact (proj2 Hwf)].
  - exact Hb.
  - exact Hw.
Qed.

Lemma wake_nz_match : forall {X Y : Type} (l : list X) (a b : Y), l <> [] -> match l with [] => a | _ => b end = b.
Proof. intros X Y l a b H. destruct l; [contradiction | reflexivity]. Qed.

(* The stack below the frame across a callee (memcpy) that writes only inside the world: memcpy's post states no
   stk, and the stack's lower end may lie below the world. *)
Lemma wake_stk_world : forall segs m m' lo hi W A B,
  stk segs m lo hi -> munch W m m' -> wmono segs m m' -> wmem_at segs A m' B ->
  (forall x, lo <= x < hi -> outside W x \/ A <= x < A + W_LEN) -> stk segs m' lo hi.
Proof.
  intros segs m m' lo hi W A B (H1 & H2 & H) MU WMo WM HC.
  pose proof (wm_bytes segs A m' B WM) as (Ba & Bl & Bb). pose proof (wm_len segs A m' B WM) as L.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WMo; exact Hw|].
  destruct (HC a Ha) as [Ho | Hin].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - specialize (Bb (Z.to_nat (a - A))).
    replace (A + Z.of_nat (Z.to_nat (a - A))) with a in Bb by lia.
    destruct (nth_error B (Z.to_nat (a - A))) as [b'|] eqn:E.
    + exists b'. apply Bb. rewrite L. unfold W_LEN in *. lia.
    + apply nth_error_None in E. rewrite L in E. unfold W_LEN in *. lia.
Qed.

(* the facts the contract keeps about the entry memory, carried to a callee's window *)
Lemma wake_tframe_move : forall m m' (sp sp2 : word) K K2 TF,
  tframe_at m sp K TF ->
  munch [(bv_unsigned sp - K, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  bv_unsigned sp - K <= bv_unsigned sp2 - K2 -> bv_unsigned sp2 <= bv_unsigned sp ->
  tframe_at m' sp2 K2 TF.
Proof.
  intros m m' sp sp2 K K2 [fr|] H MU H1 H2; [|exact I].
  destruct H as (Ha & Hb & Hw & Ho). unfold off_world, off_window in *.
  split; [exact Ha|]. split.
  - eapply bytes_at_transport; [exact Hb | exact MU |]. cbn [disjoint_from].
    split; [lia | split; [lia | exact I]].
  - split; [exact Hw | unfold off_window; lia].
Qed.

Lemma wake_relro_move : forall m m' W, relro_img m -> munch W m m' ->
  (forall x, RELRO_BASE <= x < RELRO_BASE + RELRO_LEN -> outside W x) -> relro_img m'.
Proof.
  intros m m' W H MU HO i Hi. unfold mrd.
  rewrite (MU (wa (RELRO_BASE + i))).
  - exact (H i Hi).
  - rewrite wa_unsigned by (unfold RELRO_BASE, RELRO_LEN in *; lia). apply HO. lia.
Qed.

(* ---- model helpers ---- *)

Lemma wake_io_send_r : forall I B fr B' r, io_send_m I B fr = Some (B', r) -> r = 0 \/ r = - EIO.
Proof.
  intros I B fr B' r H. unfold io_send_m in H. cbv zeta in H.
  lazymatch type of H with (match ?X with _ => _ end) = _ => destruct X as [[B1 u1]|]; [|discriminate H] end.
  cbv beta iota in H.
  lazymatch type of H with (match ?X with _ => _ end) = _ => destruct X as [[B2 u2]|]; [|discriminate H] end.
  cbv beta iota in H.
  injection H as _ Hr. rewrite <- Hr. destruct (truth (g_fail_next B)); [right | left]; reflexivity.
Qed.

Lemma wake_lib_frame_ne : forall dst src send ack retry cmd ncmds body mode,
  lib_frame dst src send ack retry cmd ncmds body mode <> [].
Proof.
  intros. unfold lib_frame, put16. intros E. apply (f_equal (@length byte)) in E.
  rewrite !length_app in E. cbn [length] in E. lia.
Qed.

Lemma wake_sc_r : forall I F B cmd ack B' r f, send_control_m I F B cmd ack = Some (B', (r, f)) ->
  r = -1 \/ r = - EIO \/ (r = 0 /\ f <> []).
Proof.
  intros I F B cmd ack B' r f H. unfold send_control_m, diginet_frame_build_code in H. cbv zeta in H.
  assert (E60 : lib_build_code [] DIGINET_MIN_FRAME_LEN = 60) by (vm_compute; reflexivity).
  rewrite E60 in H.
  destruct (negb ((S_cfg_sum_mode B =? 0) || (S_cfg_sum_mode B =? 1))); cbv beta iota in H.
  - change (-1 <? 0) with true in H. cbv beta iota in H. injection H as _ Hr _. left. congruence.
  - change (60 <? 0) with false in H. cbv beta iota in H.
    lazymatch type of H with (match ?X with _ => _ end) = _ => destruct X as [[B1 r1]|] eqn:SR; [|discriminate H] end.
    cbv beta iota in H. injection H as _ Hr Hf. subst r f.
    unfold send_raw_m, call_send in SR.
    destruct (S_io_send B =? ti_io_send I); cbv beta iota in SR; [|discriminate SR].
    lazymatch type of SR with (match ?X with _ => _ end) = _ => destruct X as [[B2 r2]|] eqn:IO; [|discriminate SR] end.
    cbv beta iota in SR. apply wake_io_send_r in IO.
    destruct (r2 =? 0); injection SR as _ Hr; subst r1;
      (destruct IO as [-> | ->]; [right; right; split; [reflexivity | apply wake_lib_frame_ne] | right; left; reflexivity]).
Qed.

(* ---- world algebra ---- *)

Lemma wake_len_upd : forall X k v n, length X = n -> 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat n ->
  length (upd X k v) = n.
Proof. intros X k v n HX Hk Hv. subst n. apply length_upd; lia. Qed.

(* length X = Z.to_nat W_LEN for a chain of stores at literal offsets over a world whose length is in the context *)
Ltac wake_len :=
  lazymatch goal with
  | |- length (upd _ _ _) = _ =>
      apply wake_len_upd; [wake_len | lia | rewrite ?length_put; unfold W_LEN; lia]
  | |- _ => assumption
  end.

Lemma wake_gfn_upd : forall X k v, length X = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= OFF_g_fail_next -> g_fail_next (upd X k v) = g_fail_next X.
Proof.
  intros X k v HX Hk Hv. unfold g_fail_next. apply u_at_upd_out; rewrite ?HX; unfold OFF_g_fail_next, W_LEN in *; lia.
Qed.

(* g_fail_next of a chain of stores at literal offsets inside g_s *)
Ltac wake_gfn :=
  repeat (rewrite wake_gfn_upd; [ | wake_len | lia | rewrite ?length_put; unfold OFF_g_fail_next; lia ]).

(* :125-128 the refused path: s->stats.refused++ *)
Lemma wake_refused_world : forall B v, upd B 19904 (put 8 (v + 1)) = set_S_stats_refused B (u64 (v + 1)).
Proof. intros. unfold set_S_stats_refused, u64. rewrite put_mod64 by lia. reflexivity. Qed.

(* sw of the sign-extended lw value stores the 4 bytes that were read *)
Lemma wake_put4_s32 : forall X k, put 4 (s32_at X k) = put 4 (u_at X k 4).
Proof.
  intros X k. unfold s32_at, put.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 (u_at X k 4)) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (u_at X k 4) 32) by lia.
  f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Zminus_mod_idemp_l. f_equal. ring.
Qed.

(* :139-142 the world after memcpy, stats.tx_wakes++ and the inlined inflight_start, in the machine's store order
   (inflight_frame, tx_wakes, inflight, inflight_len, inflight_counter, inflight_retries, inflight_sent_us), is the
   model's (inflight_frame, inflight_len, tx_wakes, then inflight_start_m) *)
Lemma wake_main_world : forall B4 e2 now,
  length B4 = Z.to_nat W_LEN -> length e2 = 60%nat ->
  upd (upd (upd (upd (upd
    (upd (upd B4 1864 e2) 19872 (put 8 (u_at (upd B4 1864 e2) 19872 8 + 1)))
    1860 (put 4 1)) 3384 (put 8 60))
    3392 (put 4 (s32_at (upd (upd B4 1864 e2) 19872 (put 8 (u_at (upd B4 1864 e2) 19872 8 + 1))) 1808)))
    3396 (put 4 0)) 3400 (put 8 now)
  = set_S_inflight_sent_us (set_S_inflight_retries (set_S_inflight_counter (set_S_inflight
      (set_S_stats_tx_wakes (set_S_inflight_len (set_S_inflight_frame B4 e2) (Z.of_nat (length e2)))
        (u64 (S_stats_tx_wakes (set_S_inflight_len (set_S_inflight_frame B4 e2) (Z.of_nat (length e2))) + 1))) 1)
      (S_host_counter (set_S_stats_tx_wakes (set_S_inflight_len (set_S_inflight_frame B4 e2) (Z.of_nat (length e2)))
        (u64 (S_stats_tx_wakes (set_S_inflight_len (set_S_inflight_frame B4 e2) (Z.of_nat (length e2))) + 1)))))
      0) now.
Proof.
  intros B4 e2 now L4 LE.
  rewrite LE. change (Z.of_nat 60) with 60.
  unfold set_S_inflight_sent_us, set_S_inflight_retries, set_S_inflight_counter, set_S_inflight,
    set_S_stats_tx_wakes, set_S_inflight_len, set_S_inflight_frame, S_stats_tx_wakes, S_host_counter, u64.
  change A_S_inflight_sent_us with 3400. change A_S_inflight_retries with 3396.
  change A_S_inflight_counter with 3392. change A_S_inflight with 1860. change A_S_stats_tx_wakes with 19872.
  change A_S_inflight_len with 3384. change A_S_inflight_frame with 1864. change A_S_host_counter with 1808.
  rewrite put_mod64 by lia.
  assert (L5 : length (upd B4 1864 e2) = Z.to_nat W_LEN) by wake_len.
  rewrite (u_at_upd_out (upd B4 1864 e2) (put 8 60) 3384 19872 8)
    by (rewrite ?length_put, ?L5; unfold W_LEN; lia).
  rewrite (upd_upd_comm (upd B4 1864 e2) (put 8 60) (put 8 (u_at (upd B4 1864 e2) 19872 8 + 1)) 3384 19872)
    by (rewrite ?length_put, ?L5; unfold W_LEN; lia).
  set (W6 := upd (upd B4 1864 e2) 19872 (put 8 (u_at (upd B4 1864 e2) 19872 8 + 1))).
  assert (L6 : length W6 = Z.to_nat W_LEN) by (unfold W6; wake_len).
  rewrite (upd_upd_comm W6 (put 8 60) (put 4 1) 3384 1860) by (rewrite ?length_put, ?L6; unfold W_LEN; lia).
  rewrite (u_at_upd_out W6 (put 8 60) 3384 1808 4) by (rewrite ?length_put, ?L6; unfold W_LEN; lia).
  rewrite wake_put4_s32. reflexivity.
Qed.

(* diginet_session_wake at 0x16af8 (transport/src/diginet_session.c:119-145), frame 112: e2_len at sp, e2[60] at
   sp + 12, ra and s0-s3 at sp + 72. The model's branches in the machine's order: S_desk_known = 0 returns
   DIGINET_E_ARG; S_foreign <> 0 bumps stats.refused (s3 = s + 0x4730) and returns DIGINET_E_REFUSED; else the three
   wake stores, send_control (s, WAKE, 0, e2, &e2_len) with e2 and e2_len carved from the frame, return on r < 0,
   memcpy (s->inflight_frame, e2, 60) folded into the world, stats.tx_wakes++, the inlined inflight_start, and
   set_state (s, WAKING, R_WAKE). The machine stores inflight_len after tx_wakes and inflight; wake_main_world
   reorders them to the model's world. The tframe and RELRO facts stay about the entry memory and are carried to
   set_state's window by the footprint MU. *)
Theorem diginet_session_wake_holds :
  send_control_contract -> memcpy_contract -> set_state_contract -> diginet_session_wake_contract.
Proof.
  intros SC MC SS.
  unfold send_control_contract, send_control_ENTRY, send_control_FRAME in SC.
  unfold set_state_contract, set_state_ENTRY, set_state_FRAME in SS.
  unfold diginet_session_wake_contract, diginet_session_wake_ENTRY, diginet_session_wake_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo now r B B' TF A0 A1 NOW WM GF HM TFm RR SP16 ST LO WO MI.
  subst a0 a1.
  unfold w_off_stack in WO.
  wk_facts.
  assert (Eg : OFF_g_s = 1648) by reflexivity.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112)
    by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 752, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  pose proof (wm_len _ _ _ _ WM) as LB.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 112%nat ST.
  (* addi sp,sp,-112; sd ra,104(sp); sd s0,96(sp); sd s1,88(sp); sd s2,80(sp); sd s3,72(sp) *)
  do 6 step.
  (* mv s0,a0; li a0,-1; beqz s0 (s = &g_s is not NULL) *)
  do 3 step. wake_closed_if.
  (* mv s1,a1; andi a1,s0,7; bnez a1 (&g_s is 8-aligned) *)
  do 3 step. wake_closed_if.
  (* lw a1,116(s0); beqz a1 *)
  step.
  change (s32_at B 1764) with (S_desk_known B).
  step.
  pose proof (s32_range B A_S_desk_known) as RDK. change (s32_at B A_S_desk_known) with (S_desk_known B) in RDK.
  rewrite wake_eqb0 by lia.
  unfold diginet_session_wake_m in HM.
  destruct (S_desk_known B =? 0) eqn:DK; cbv iota; cbv iota in HM.
  - (* S_desk_known = 0: return DIGINET_E_ARG *)
    injection HM as <- <-.
    do 5 step.
    release_frame FR ST (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
    exact (conj MU (conj WMO (conj MI (conj ST (conj WM GF))))).
  - (* lw a0,136(s0); lui a1,0x4; addiw s3,a1,1840; add s3,s0,s3; beqz a0 *)
    step.
    change (s32_at B 1784) with (S_foreign B).
    pose proof (s32_range B A_S_foreign) as RFO. change (s32_at B A_S_foreign) with (S_foreign B) in RFO.
    do 4 step.
    rewrite wake_eqb0 by lia.
    destruct (S_foreign B =? 0) eqn:FO; cbv iota; cbv [negb] in HM; cbv iota in HM.
    + (* S_foreign = 0: the wake (:129-144) *)
      (* sw zero,140(s0); sw zero,144(s0); sd s1,152(s0) *)
      do 3 step.
      assert (GF3 : g_fail_next (upd (upd (upd B 1788 (put 4 0)) 1792 (put 4 0)) 1800 (put 8 now)) <= 1)
        by (wake_gfn; exact GF).
      change (upd (upd (upd B 1788 (put 4 0)) 1792 (put 4 0)) 1800 (put 8 now))
        with (set_S_wake_sent_us (set_S_wake_acked (set_S_e1_named_us B 0) 0) now) in WMw, GF3.
      destruct (send_control_m timg_ubsan TF (set_S_wake_sent_us (set_S_wake_acked (set_S_e1_named_us B 0) 0) now)
                  DIGINET_CMD_WAKE 0) as [[B4 [r4 e2]]|] eqn:HSC; cbv beta iota in HM; [|discriminate HM].
      pose proof (wake_sc_r _ _ _ _ _ _ _ _ HSC) as R4.
      (* li a1,226; addi a3,sp,12; mv a4,sp; mv a0,s0; li a2,0; jal send_control *)
      do 6 step.
      destruct (wake_frame_split _ _ _ _ _ FR) as (j0 & j1 & j2 & KL0 & GAP & K0 & SAV). clear FR.
      replace (bv_unsigned sp + -112 + 12) with (bv_unsigned sp + -100) in K0 by lia.
      eapply evt_cut.
      { eapply SC with (ack := 0) (K := j2) (KL := j0);
          [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | | exact WMw
          | exact GF3 | exact HSC | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST
          | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI ].
        right. unfold arg_blk, blk_sep, off_world, off_window. rewrite !Hsp.
        split; [exact K0|]. split; [lia|]. split; [exact KL0|]. split; [lia|].
        split; [Z.div_mod_to_equations; lia | lia]. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2 & WM4 & GF4 & KP).
      subst ms'. rewrite Hsp in MUc, ST2.
      destruct KP as [KP|[KC KLC]]; [lia|].
      replace (bv_unsigned sp + -100 =? 0) with false in MUc by (symmetry; apply Z.eqb_neq; lia).
      cbn [app] in MUc.
      clear WMw.
      lazymatch type of MUc with munch _ ?ma ?mb =>
        apply (munch_trans _ _ ma mb) in MU;
        [| eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros ? (? & ? & _); repeat split; lia];
        transport_after_call rsegs ma mb MUc WMc; clear MUc WMc MI; try clear ma
      end.
      rewrite (ret_pc_even 0x16b7c) by (first [lia | reflexivity]).
      pose proof (wake_cb_bytes _ _ _ _ _ KC) as SRC.
      pose proof (wake_cb_len _ _ _ _ _ KC) as LKC.
      replace (bv_unsigned sp + -100) with (bv_unsigned sp + -112 + 12) in KC by lia.
      pose proof (wake_frame_merge _ _ _ _ _ _ _ KLC GAP KC SAV eq_refl eq_refl eq_refl) as FR.
      clear KLC GAP KC SAV.
      rename ST2 into ST, MI2 into MI.
      destruct R4 as [-> | [-> | [-> NE]]].
      * (* r = -1 (the build failed): bltz a0 taken, return r *)
        step. wake_closed_if.
        change (-1 <? 0) with true in HM. cbv iota in HM. injection HM as <- <-.
        do 5 step. release_frame FR ST (bv_unsigned sp). do 2 step.
        apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
        exact (conj MU (conj WMO (conj MI (conj ST (conj WM4 GF4))))).
      * (* r = -EIO (io.send failed): bltz a0 taken, return r *)
        step. wake_closed_if.
        change (- EIO <? 0) with true in HM. cbv iota in HM. injection HM as <- <-.
        do 5 step. release_frame FR ST (bv_unsigned sp). do 2 step.
        apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
        exact (conj MU (conj WMO (conj MI (conj ST (conj WM4 GF4))))).
      * (* r = 0: e2 holds the 60 built bytes and e2_len = 60 *)
        step. wake_closed_if.
        change (0 <? 0) with false in HM. cbv iota in HM.
        unfold inflight_start_m in HM. cbv beta iota zeta in HM.
        lazymatch type of HM with context [set_state_m ?I ?T ?X ?s ?w] =>
          destruct (set_state_m I T X s w) as [[B12 []]|] eqn:HSS; cbv beta iota in HM; [|discriminate HM] end.
        injection HM as <- <-.
        rewrite (wake_nz_match e2) in SRC, LKC by exact NE.
        rewrite !(wake_nz_match e2) in FR by exact NE.
        rewrite LKC in FR. change (Z.of_nat 60) with 60 in FR. rewrite <- (le8_put 60) in FR.
        apply wake_c8_head in FR.
        (* ld s2,0(sp); addi a0,s0,216; addi a1,sp,12; mv a2,s2; jal memcpy *)
        do 5 step.
        pose proof (wm_len _ _ _ _ WM4) as L4.
        assert (U0 : bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 216)) = W_BASE_UBSAN + OFF_g_s + 216)
          by (apply unsigned_lit; lia).
        assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -100)) = bv_unsigned sp + -100)
          by (apply unsigned_lit; lia).
        assert (U2 : bv_unsigned (Z_to_bv 64 60) = 60) by reflexivity.
        assert (DST : rw_cells rsegs m2 (bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 216)))
                        [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 60)))
                            (sub B4 1864 (Z.to_nat (bv_unsigned (Z_to_bv 64 60))))]).
        { apply (wm_piece rsegs W_BASE_UBSAN m2 B4 1864);
            [exact WM4 | rewrite U0; lia | lia | rewrite U2; lia | rewrite U2; unfold W_LEN; lia]. }
        eapply evt_cut.
        { eapply MC with (src := e2);
            [ rewrite U1; exact SRC | rewrite U2, LKC; reflexivity | exact DST
            | rewrite U0, U1, U2; right; lia | exact MI ]. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & DC & SB).
        subst ms'. clear DST SB.
        (* the copied bytes are the world's inflight_frame; the stack below the frame is still a stack *)
        assert (WM5 : wmem rsegs m3 (upd B4 1864 e2)).
        { apply (wm_fill rsegs W_BASE_UBSAN m2 m3 B4 _ 1864 _ e2 WM4 MUc WMc DC);
            [rewrite U0; lia | lia | rewrite U2; lia | rewrite U2; unfold W_LEN; lia]. }
        assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -112)).
        { apply (wake_stk_world _ _ _ _ _ _ _ _ ST MUc WMc WM5). intros z Hz. cbn [outside].
          destruct (Z_lt_le_dec z W_BASE_UBSAN) as [Hl|Hl]; [left; split; [lia | exact I]|].
          destruct (Z_lt_le_dec z (W_BASE_UBSAN + W_LEN)) as [Hh|Hh]; [right; lia | left; split; [lia | exact I]]. }
        clear WM4 ST DC.
        transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI. try clear m2.
        rewrite (ret_pc_even 0x16b94) by (first [lia | reflexivity]).
        rename ST3 into ST, MI3 into MI.
        (* ld a0,0(s3); addi a0,a0,1; sd a0,0(s3); lw a0,160(s0); li a1,1; sw a1,212(s0); sd s2,1736(s0);
           sw a0,1744(s0); sw zero,1748(s0); sd s1,1752(s0); li a1,1; li a2,1; mv a0,s0; jal set_state *)
        do 14 step.
        (* the world the stores left is the model's, the one set_state_m starts from *)
        lazymatch goal with H : wmem rsegs _ ?W |- _ =>
          assert (GF11 : g_fail_next W <= 1) by (wake_gfn; exact GF4);
          rewrite (wake_main_world B4 e2 now L4 LKC) in H, GF11; rename H into WM11
        end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (TF3 : tframe_at mm (Z_to_bv 64 (bv_unsigned sp + -112)) 384 TF)
            by (apply (wake_tframe_move m mm sp _ 752 384 TF TFm MU); rewrite Hsp; lia);
          assert (RR3 : relro_img mm)
            by (apply (wake_relro_move m mm _ RR MU); intros z Hz; cbn [outside];
                unfold RELRO_BASE, RELRO_LEN in Hz; repeat split; lia)
        end.
        eapply evt_cut.
        { eapply SS; [ reflexivity | reflexivity | reflexivity | lia | lia | exact WM11 | exact GF11 | exact HSS
                     | exact TF3 | exact RR3 | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST
                     | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI ]. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 &
                    Eq & MUc & WMc & MI6 & ST6 & WM6 & GF6).
        subst ms'. rewrite Hsp in MUc, ST6.
        clear WM11 TF3 RR3.
        lazymatch type of MUc with munch _ ?ma ?mb =>
          apply (munch_trans _ _ ma mb) in MU;
          [| eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros ? (? & ? & _); repeat split; lia];
          transport_after_call rsegs ma mb MUc WMc; clear MUc WMc MI; try clear ma
        end.
        rewrite (ret_pc_even 0x16bcc) by (first [lia | reflexivity]).
        rename ST6 into ST, MI6 into MI.
        (* li a0,0; ld ra,104(sp); ld s0,96(sp); ld s1,88(sp); ld s2,80(sp); ld s3,72(sp); addi sp,sp,112; ret *)
        do 6 step. release_frame FR ST (bv_unsigned sp). do 2 step.
        apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
        exact (conj MU (conj WMO (conj MI (conj ST (conj WM6 GF6))))).
    + (* S_foreign <> 0: ld a0,32(s3); addi a0,a0,1; sd a0,32(s3); li a0,-10; j; return DIGINET_E_REFUSED *)
      injection HM as <- <-.
      step.
      change (u_at B 19904 8) with (S_stats_refused B).
      do 2 step.
      do 7 step.
      release_frame FR ST (bv_unsigned sp).
      do 2 step.
      apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
      rewrite wake_refused_world in WMw.
      refine (conj MU (conj WMO (conj MI (conj ST (conj WMw _))))).
      unfold set_S_stats_refused, A_S_stats_refused. wake_gfn. exact GF.
Qed.

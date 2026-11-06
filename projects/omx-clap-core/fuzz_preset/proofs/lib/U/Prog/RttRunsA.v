From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import MallocRuns.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require round_trip_text_c pj_write_c tx_put_c tx_value_c
  fuzz_free_c pj_free_c.
Import ListNotations.
Open Scope Z_scope.

(* round_trip_text of the #102 ubsan twin 27566683 (lib/U/Prog/round_trip_text_c.v, ROUND_TRIP_TEXT 0x15334, 388 B): the
   straight-line runs between its calls, the twins of lib/Prog/RttRunsA.v (plain, 0x14d88).  The ubsan body is the plain
   one instruction for instruction at + 0x5ac.  pj_write, tx_put, tx_value, fuzz_free and pj_free by their contracts'
   names; free 0x18250 (no named constant in lib/U/Prog). *)

Lemma rttA_stk_wr_at : forall m lo hi n, stk rsegs m lo hi -> n = hi - lo -> wr_at rsegs m lo n.
Proof.
  intros m lo hi n (H1 & H2 & H) ->. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

Lemma rttA_roc8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v HB. split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]. Qed.

(* 0x15334: the prologue (7 saved registers), s0 := copy, s3 := pretty, s1 := doc; jal pj_write *)
Definition rtt_seg0_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
  112 <= S <= 2 ^ 63 -> stk rsegs m (S - 56) S ->
  evt rsegs (fun ms' => exists m', munch [(S - 56, S)] m m' /\ wmono rsegs m m' /\
      bytes_at rsegs m' (S - 8) (le8 ra) /\ bytes_at rsegs m' (S - 16) (le8 s0) /\
      bytes_at rsegs m' (S - 24) (le8 s1) /\ bytes_at rsegs m' (S - 32) (le8 s2) /\
      bytes_at rsegs m' (S - 40) (le8 s3) /\ bytes_at rsegs m' (S - 48) (le8 s4) /\
      bytes_at rsegs m' (S - 56) (le8 s5) /\ wr_at rsegs m' (S - 56) 56 /\
      ms' = MS (mkR (Z_to_bv 64 0x15364) (Z_to_bv 64 (S - 112)) gp tp t0 t1 t2 a2 a0 a0 a1 a2 a3 a4 a5 a6 a7 s2 a1
                    s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pj_write_c.PJ_WRITE_PC) fc None m' (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 round_trip_text_c.ROUND_TRIP_TEXT) fc None m (seg_rom rsegs)).

Lemma rtt_seg0 : rtt_seg0_stmt.
Proof.
  unfold rtt_seg0_stmt, pj_write_c.PJ_WRITE_PC, round_trip_text_c.ROUND_TRIP_TEXT.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S HS HK.
  pose proof HK as HK0. replace (S - 56) with (S + -56) in HK by lia.
  destruct (carve8 m (S + -56) S (S + -8) HK ltac:(lia) ltac:(lia)) as (HK1 & j1 & K1).
  destruct (carve8 m (S + -56) (S + -8) (S + -16) HK1 ltac:(lia) ltac:(lia)) as (HK2 & j2 & K2).
  destruct (carve8 m (S + -56) (S + -16) (S + -24) HK2 ltac:(lia) ltac:(lia)) as (HK3 & j3 & K3).
  destruct (carve8 m (S + -56) (S + -24) (S + -32) HK3 ltac:(lia) ltac:(lia)) as (HK4 & j4 & K4).
  destruct (carve8 m (S + -56) (S + -32) (S + -40) HK4 ltac:(lia) ltac:(lia)) as (HK5 & j5 & K5).
  destruct (carve8 m (S + -56) (S + -40) (S + -48) HK5 ltac:(lia) ltac:(lia)) as (HK6 & j6 & K6).
  destruct (carve8 m (S + -56) (S + -48) (S + -56) HK6 ltac:(lia) ltac:(lia)) as (HK7 & j7 & K7).
  clear HK HK1 HK2 HK3 HK4 HK5 HK6 HK7.
  assert (HM : munch [(S - 56, S)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  do 12 step.
  apply evt_done. eexists.
  split; [exact HM|]. split; [exact HW|].
  replace (S - 8) with (S + -8) by lia. replace (S - 16) with (S + -16) by lia.
  replace (S - 24) with (S + -24) by lia. replace (S - 32) with (S + -32) by lia.
  replace (S - 40) with (S + -40) by lia. replace (S - 48) with (S + -48) by lia.
  split; [eapply rwc8_bytes; [exact K1 | reflexivity]|].
  split; [eapply rwc8_bytes; [exact K2 | reflexivity]|].
  split; [eapply rwc8_bytes; [exact K3 | reflexivity]|].
  split; [eapply rwc8_bytes; [exact K4 | reflexivity]|].
  split; [eapply rwc8_bytes; [exact K5 | reflexivity]|].
  split; [eapply rwc8_bytes; [exact K6 | reflexivity]|].
  split; [replace (S - 56) with (S + -56) by lia; eapply rwc8_bytes; [exact K7 | reflexivity]|].
  split; [eapply rttA_stk_wr_at; [exact HK0 | lia]|].
  replace (S - 112) with (S + -112) by lia. reflexivity.
Qed.

(* 0x15364: s2 := text; the 32-byte struct text at P zeroed (b, n, cap, failed); jal tx_put(P, "", 0) *)
Definition rtt_seg1_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
  0 <= P -> P + 32 <= 2 ^ 64 -> stk rsegs m P (P + 32) ->
  evt rsegs (fun ms' => exists m', munch [(P, P + 32)] m m' /\ wmono rsegs m m' /\
      bytes_at rsegs m' P (le8 (Z_to_bv 64 0)) /\ bytes_at rsegs m' (P + 8) (le8 (Z_to_bv 64 0)) /\
      bytes_at rsegs m' (P + 16) (le8 (Z_to_bv 64 0)) /\ bytes_at rsegs m' (P + 24) (le8 (Z_to_bv 64 0)) /\
      wr_at rsegs m' P 32 /\
      ms' = MS (mkR (Z_to_bv 64 0x1538c) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 0x102e8)
                    (Z_to_bv 64 0) a3 a4 a5 a6 a7 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 tx_put_c.TX_PUT) fc None m' (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15364) fc None m (seg_rom rsegs)).

Lemma rtt_seg1 : rtt_seg1_stmt.
Proof.
  unfold rtt_seg1_stmt, tx_put_c.TX_PUT.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P HP1 HP2 HK.
  pose proof HK as HK0.
  destruct (carve8 m P (P + 32) (P + 24) HK ltac:(lia) ltac:(lia)) as (HK1 & j1 & K1).
  destruct (carve8 m P (P + 24) (P + 16) HK1 ltac:(lia) ltac:(lia)) as (HK2 & j2 & K2).
  destruct (carve8 m P (P + 16) (P + 8) HK2 ltac:(lia) ltac:(lia)) as (HK3 & j3 & K3).
  destruct (carve8 m P (P + 8) P HK3 ltac:(lia) ltac:(lia)) as (HK4 & j4 & K4).
  clear HK HK1 HK2 HK3 HK4.
  assert (HM : munch [(P, P + 32)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  do 10 step.
  apply evt_done. eexists.
  split; [exact HM|]. split; [exact HW|].
  split; [eapply rwc8_bytes; [exact K4 | reflexivity]|].
  split; [eapply rwc8_bytes; [exact K3 | reflexivity]|].
  split; [eapply rwc8_bytes; [exact K2 | reflexivity]|].
  split; [eapply rwc8_bytes; [exact K1 | reflexivity]|].
  split; [eapply rttA_stk_wr_at; [exact HK0 | lia]|].
  reflexivity.
Qed.

(* 0x1538c: jal tx_value(P, doc = s1, pretty = s3, 0) *)
Definition rtt_seg2_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
  0 <= P < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x153a0) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) s1 s3
                    (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 tx_value_c.TX_VALUE) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1538c) fc None m (seg_rom rsegs)).

Lemma rtt_seg2 : rtt_seg2_stmt.
Proof.
  unfold rtt_seg2_stmt, tx_value_c.TX_VALUE.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P HP.
  do 5 step. apply evt_done. reflexivity.
Qed.

(* 0x153a0: beqz s3 (compact: on to 0x153b8); pretty: jal tx_put(P, "\n", 1) *)
Definition rtt_seg3_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
  evt rsegs (fun ms' =>
      (s3 = Z_to_bv 64 0 /\
       ms' = MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6) F (Z_to_bv 64 0x153b8) fc None m (seg_rom rsegs)) \/
      (s3 <> Z_to_bv 64 0 /\
       ms' = MS (mkR (Z_to_bv 64 0x153b8) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 0x10392)
                     (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 tx_put_c.TX_PUT) fc None m (seg_rom rsegs)))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x153a0) fc None m (seg_rom rsegs)).

Lemma rtt_seg3 : rtt_seg3_stmt.
Proof.
  unfold rtt_seg3_stmt, tx_put_c.TX_PUT.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P.
  step. if_cases HB; zify_cond HB.
  - apply evt_done. left. split; [apply bv_eq; exact HB | reflexivity].
  - do 5 step. apply evt_done. right. split; [intros E; subst s3; apply HB; reflexivity | reflexivity].
Qed.

(* 0x153e4 (ran out): jal free(want = s3) *)
Definition rtt_segO1_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x153ec) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                    s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18250) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x153e4) fc None m (seg_rom rsegs)).

Lemma rtt_segO1 : rtt_segO1_stmt.
Proof.
  unfold rtt_segO1_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step. apply evt_done. reflexivity.
Qed.

(* 0x153ec (ran out): jal fuzz_free(text = s2) *)
Definition rtt_segO2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x153f4) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                    s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 fuzz_free_c.FUZZ_FREE) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x153ec) fc None m (seg_rom rsegs)).

Lemma rtt_segO2 : rtt_segO2_stmt.
Proof.
  unfold rtt_segO2_stmt, fuzz_free_c.FUZZ_FREE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step. apply evt_done. reflexivity.
Qed.

(* 0x1544c (read back): s4 := rc; jal free(want = s3) *)
Definition rtt_segF1_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x15458) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7 s2 s3 a0 s5 s6
                    s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18250) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1544c) fc None m (seg_rom rsegs)).

Lemma rtt_segF1 : rtt_segF1_stmt.
Proof.
  unfold rtt_segF1_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step. apply evt_done. reflexivity.
Qed.

(* 0x15458 (read back): jal fuzz_free(text = s2) *)
Definition rtt_segF2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x15460) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                    s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 fuzz_free_c.FUZZ_FREE) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15458) fc None m (seg_rom rsegs)).

Lemma rtt_segF2 : rtt_segF2_stmt.
Proof.
  unfold rtt_segF2_stmt, fuzz_free_c.FUZZ_FREE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step. apply evt_done. reflexivity.
Qed.

(* 0x15488 with copy = 0 (s0 = 0): jal pj_free(&back = P) *)
Definition rtt_seg7b_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x154a8) (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 0) s1 (Z_to_bv 64 P)
                    a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 pj_free_c.PJ_FREE) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 0) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15488) fc None m (seg_rom rsegs)).

Lemma rtt_seg7b : rtt_seg7b_stmt.
Proof.
  unfold rtt_seg7b_stmt, pj_free_c.PJ_FREE.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P.
  step. if_true. do 2 step. apply evt_done. reflexivity.
Qed.

(* 0x154a8 (normal end): s2 := 0; j 0x153f8; a0 := s2; restore ra s0 .. s5; sp += 112; ret *)
Definition rtt_seg8z_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z) (rav s0v s1v s2v s3v s4v s5v : word),
  0 <= P -> P + 112 <= 2 ^ 64 ->
  bytes_at rsegs m (P + 104) (le8 rav) -> bytes_at rsegs m (P + 96) (le8 s0v) -> bytes_at rsegs m (P + 88) (le8 s1v) ->
  bytes_at rsegs m (P + 80) (le8 s2v) -> bytes_at rsegs m (P + 72) (le8 s3v) -> bytes_at rsegs m (P + 64) (le8 s4v) ->
  bytes_at rsegs m (P + 56) (le8 s5v) ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (P + 112)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                    s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x154a8) fc None m (seg_rom rsegs)).

Lemma rtt_seg8z : rtt_seg8z_stmt.
Proof.
  unfold rtt_seg8z_stmt.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P
    rav s0v s1v s2v s3v s4v s5v HP1 HP2 B1 B2 B3 B4 B5 B6 B7.
  apply rttA_roc8 in B1, B2, B3, B4, B5, B6, B7.
  do 12 step. apply evt_done. reflexivity.
Qed.

(* 0x153f4 (ran out): s2 := 1; a0 := s2; restore ra s0 .. s5; sp += 112; ret *)
Definition rtt_seg8o_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z) (rav s0v s1v s2v s3v s4v s5v : word),
  0 <= P -> P + 112 <= 2 ^ 64 ->
  bytes_at rsegs m (P + 104) (le8 rav) -> bytes_at rsegs m (P + 96) (le8 s0v) -> bytes_at rsegs m (P + 88) (le8 s1v) ->
  bytes_at rsegs m (P + 80) (le8 s2v) -> bytes_at rsegs m (P + 72) (le8 s3v) -> bytes_at rsegs m (P + 64) (le8 s4v) ->
  bytes_at rsegs m (P + 56) (le8 s5v) ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (P + 112)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                    s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x153f4) fc None m (seg_rom rsegs)).

Lemma rtt_seg8o : rtt_seg8o_stmt.
Proof.
  unfold rtt_seg8o_stmt.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P
    rav s0v s1v s2v s3v s4v s5v HP1 HP2 B1 B2 B3 B4 B5 B6 B7.
  apply rttA_roc8 in B1, B2, B3, B4, B5, B6, B7.
  do 11 step. apply evt_done. reflexivity.
Qed.

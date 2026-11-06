From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import LedgerCells fuzz_alloc_peak_reset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_live_c fuzz_alloc_count_c
  fuzz_alloc_peak_c check_bounded_alloc_c check_reject_clean_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require fuzz_alloc_ran_out_c fuzz_alloc_ran_out_reset_c
  fuzz_alloc_most_c.
Import ListNotations.
Open Scope Z_scope.

(* the ledger cells' numerals, computed from LedgerCells' names (never typed): the form the step tactic reads *)
Local Abbreviation OWNv := ltac:(let v := eval cbv in GL_OWN_RAN_OUT in exact v) (only parsing).
Local Abbreviation RANv := ltac:(let v := eval cbv in GL_RAN_OUT in exact v) (only parsing).
Local Abbreviation MOSTv := ltac:(let v := eval cbv in GL_MOST in exact v) (only parsing).

(* The segment walks of LLVMFuzzerTestOneInput on the #102 ubsan pin 45b0357d (fuzz_preset.c:800-836 of the #102
   source; unstripped twin 27566683952ebd54..., FUNC 0x13718 size 336): the plain walks of lib/Prog/EntSegA.v
   (cold/h-rw-pre-4-rw102-ent f3c1596d9c63) at the ubsan addresses. The ubsan entry is the plain one instruction for
   instruction, 0xf0 higher; only the jal targets (callees by symbol: check_no_overread 0x13868, parse_noting 0x13a38,
   check_as_written 0x13ad4, check_reject_clean_starved 0x13c3c, pj_free 0x16340, read_members 0x13e94,
   check_round_trip 0x1408c) and s5's offset differ (auipc s5, 0x22 at 0x13748: s5 = GL_OWN_RAN_OUT + 0x4f8;
   sb / lbu at -0x4f8(s5)). Frame: addi sp, sp, -0x70; ra, s0-s5 at sp+0x68 .. sp+0x38; doc at sp+0.
   Registers: s0 = size, s1 = data, s2 = live, s3 = count (then took), s4 = rc, s5 = &g_own_ran_out + 0x4f8 (then the
   count after the reading). The ran-out exits (0x137b4, 0x137c0, 0x137d8 not taken, 0x1384c taken) are not walked: the
   callers give a0 = 0 and the two flag bytes 0 at those points. *)

Lemma ent_roc8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v HB. split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]. Qed.

Lemma ent_carve8 : forall m lo hi a, stk rsegs m lo hi -> lo <= hi - 8 -> a = hi - 8 ->
  stk rsegs m lo a /\ exists j, rw_cells rsegs m a [CB 8 j].
Proof.
  intros m lo hi a H Hl ->. destruct (stk_carve rsegs m lo hi 8 H ltac:(lia)) as (H1 & j & H2).
  split; [exact H1 | exists j; exact H2].
Qed.

Lemma ent_rwc8 : forall m A v v', rw_cells rsegs m A [C8 v] -> v = v' -> bytes_at rsegs m A (le8 v').
Proof.
  intros m A v v' ((_ & HB) & _) <-. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.

Lemma ent_stk_wr_at : forall m lo hi n, stk rsegs m lo hi -> n = hi - lo -> wr_at rsegs m lo n.
Proof.
  intros m lo hi n (H1 & H2 & H) ->. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

Lemma ent_wrap : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 64) with (2 ^ 64) by reflexivity. rewrite Zmod_mod. reflexivity.
Qed.

Lemma ent_zx8_0 : zx8 (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* 0x137e4: li a0, 0; the epilogue; ret *)
Lemma ent_epi : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z)
  (rav s0v s1v s2v s3v s4v s5v : word),
  0 <= P -> P + 112 <= 2 ^ 64 ->
  bytes_at rsegs m (P + 104) (le8 rav) -> bytes_at rsegs m (P + 96) (le8 s0v) ->
  bytes_at rsegs m (P + 88) (le8 s1v) -> bytes_at rsegs m (P + 80) (le8 s2v) ->
  bytes_at rsegs m (P + 72) (le8 s3v) -> bytes_at rsegs m (P + 64) (le8 s4v) ->
  bytes_at rsegs m (P + 56) (le8 s5v) ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (P + 112)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5
                    a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x137e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P
    rav s0v s1v s2v s3v s4v s5v HP1 HP2 B1 B2 B3 B4 B5 B6 B7.
  apply ent_roc8 in B1, B2, B3, B4, B5, B6, B7.
  do 10 step. apply evt_done. reflexivity.
Qed.

(* 0x13718 .. 0x13744: the prologue and the size test; a file over PRESET_FILE_MAX_BYTES returns 0 (0x13740 -> 0x137e4) *)
Lemma ent_segA : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
  112 <= S < 2 ^ 64 -> stk rsegs m (S - 56) S ->
  evt rsegs (fun ms' => exists m', munch [(S - 56, S)] m m' /\ wmono rsegs m m' /\
      ((0x300000 < bv_unsigned a1 /\
        ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0x300000) a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)) \/
       (bv_unsigned a1 <= 0x300000 /\
        bytes_at rsegs m' (S - 8) (le8 ra) /\ bytes_at rsegs m' (S - 16) (le8 s0) /\
        bytes_at rsegs m' (S - 24) (le8 s1) /\ bytes_at rsegs m' (S - 32) (le8 s2) /\
        bytes_at rsegs m' (S - 40) (le8 s3) /\ bytes_at rsegs m' (S - 48) (le8 s4) /\
        bytes_at rsegs m' (S - 56) (le8 s5) /\ wr_at rsegs m' (S - 56) 56 /\
        ms' = MS (mkR ra (Z_to_bv 64 (S - 112)) gp tp t0 t1 t2 a1 a0 a0 (Z_to_bv 64 0x300000) a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13748) fc None m' (seg_rom rsegs))))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13718) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S HS HK.
  pose proof HK as HK0. replace (S - 56) with (S + -56) in HK by lia.
  destruct (ent_carve8 m (S + -56) S (S + -8) HK ltac:(lia) ltac:(lia)) as (HK1 & j1 & K1).
  destruct (ent_carve8 m (S + -56) (S + -8) (S + -16) HK1 ltac:(lia) ltac:(lia)) as (HK2 & j2 & K2).
  destruct (ent_carve8 m (S + -56) (S + -16) (S + -24) HK2 ltac:(lia) ltac:(lia)) as (HK3 & j3 & K3).
  destruct (ent_carve8 m (S + -56) (S + -24) (S + -32) HK3 ltac:(lia) ltac:(lia)) as (HK4 & j4 & K4).
  destruct (ent_carve8 m (S + -56) (S + -32) (S + -40) HK4 ltac:(lia) ltac:(lia)) as (HK5 & j5 & K5).
  destruct (ent_carve8 m (S + -56) (S + -40) (S + -48) HK5 ltac:(lia) ltac:(lia)) as (HK6 & j6 & K6).
  destruct (ent_carve8 m (S + -56) (S + -48) (S + -56) HK6 ltac:(lia) ltac:(lia)) as (HK7 & j7 & K7).
  clear HK HK1 HK2 HK3 HK4 HK5 HK6 HK7.
  assert (HM : munch [(S - 56, S)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  do 11 step.
  if_cases HB; zify_cond HB.
  - do 10 step.
    apply evt_done. eexists.
    split; [exact HM|]. split; [exact HW|].
    left. split; [lia | reflexivity].
  - do 1 step.
    apply evt_done. eexists.
    split; [exact HM|]. split; [exact HW|].
    right. split; [lia|].
    replace (S - 8) with (S + -8) by lia. replace (S - 16) with (S + -16) by lia.
    replace (S - 24) with (S + -24) by lia. replace (S - 32) with (S + -32) by lia.
    replace (S - 40) with (S + -40) by lia. replace (S - 48) with (S + -48) by lia.
    split; [eapply ent_rwc8; [exact K1 | reflexivity]|].
    split; [eapply ent_rwc8; [exact K2 | reflexivity]|].
    split; [eapply ent_rwc8; [exact K3 | reflexivity]|].
    split; [eapply ent_rwc8; [exact K4 | reflexivity]|].
    split; [eapply ent_rwc8; [exact K5 | reflexivity]|].
    split; [eapply ent_rwc8; [exact K6 | reflexivity]|].
    split; [replace (S - 56) with (S + -56) by lia; eapply ent_rwc8; [exact K7 | reflexivity]|].
    split; [eapply ent_stk_wr_at; [exact HK0 | lia]|].
    replace (S - 112) with (S + -112) by lia. reflexivity.
Qed.

(* 0x13838 (check_reject_clean_starved returned on the refused arm): j 0x137e4; the epilogue *)
Lemma ent_segC2 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z)
  (rav s0v s1v s2v s3v s4v s5v : word),
  0 <= P -> P + 112 <= 2 ^ 64 ->
  bytes_at rsegs m (P + 104) (le8 rav) -> bytes_at rsegs m (P + 96) (le8 s0v) ->
  bytes_at rsegs m (P + 88) (le8 s1v) -> bytes_at rsegs m (P + 80) (le8 s2v) ->
  bytes_at rsegs m (P + 72) (le8 s3v) -> bytes_at rsegs m (P + 64) (le8 s4v) ->
  bytes_at rsegs m (P + 56) (le8 s5v) ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (P + 112)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5
                    a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13838) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P
    rav s0v s1v s2v s3v s4v s5v HP1 HP2 B1 B2 B3 B4 B5 B6 B7.
  step.
  exact (ent_epi ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P
    rav s0v s1v s2v s3v s4v s5v HP1 HP2 B1 B2 B3 B4 B5 B6 B7).
Qed.

(* 0x1384c (check_round_trip returned 0): the arguments of check_reject_clean_starved(data, size, took, &doc) *)
Lemma ent_segE2 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13864) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 s1 s0 s3
                    (Z_to_bv 64 P) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13c3c) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1384c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P.
  step. if_false. do 5 step. apply evt_done. reflexivity.
Qed.

(* 0x13864 (check_reject_clean_starved returned): j 0x137dc; pj_free(&doc) *)
Lemma ent_segE3 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x137e4) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P)
                    a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16340) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13864) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P.
  do 3 step. apply evt_done. reflexivity.
Qed.

Section KA.
Hypothesis HLIVE : fuzz_alloc_live_contract.
Hypothesis HCOUNT : fuzz_alloc_count_contract.
Hypothesis HPEAK : fuzz_alloc_peak_contract.
Hypothesis HRESET : fuzz_alloc_peak_reset_contract.
Hypothesis HCBA : check_bounded_alloc_contract.
Hypothesis HCRC : check_reject_clean_contract.
Hypothesis HRO : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract.

(* 0x13770 (check_no_overread returned 0): live = fuzz_alloc_live(); count = fuzz_alloc_count(); fuzz_alloc_peak_reset();
   the arguments of parse_noting(data, size, &doc) *)
Lemma ent_segB1 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z) (live count : word),
  bytes_at rsegs m G_LIVE (le8 live) -> bytes_at rsegs m G_COUNT (le8 count) -> wr_at rsegs m G_PEAK 8 ->
  evt rsegs (fun ms' => exists m', munch [(G_PEAK, G_PEAK + 8)] m m' /\ wmono rsegs m m' /\
      bytes_at rsegs m' G_PEAK (le8 live) /\ bytes_at rsegs m' G_LIVE (le8 live) /\
      bytes_at rsegs m' G_COUNT (le8 count) /\
      ms' = MS (mkR (Z_to_bv 64 0x13798) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 s1 s0 (Z_to_bv 64 P)
                    a3 a4 a5 a6 a7 live count s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13a38) fc None m' (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13770) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P live count
    BL BC WP.
  step. if_false.
  step.
  eapply evt_cut; [eapply HLIVE; exact BL|].
  intros ms' E. cbv beta in E. subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  do 2 step.
  eapply evt_cut; [eapply HCOUNT; exact BC|].
  intros ms' E. cbv beta in E. subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  do 2 step.
  eapply evt_cut; [eapply HRESET; [exact BL | exact WP]|].
  intros ms' (a0' & a1' & m' & E & BP & MU & WM). subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  do 4 step.
  apply evt_done. exists m'.
  split; [exact MU|]. split; [exact WM|]. split; [exact BP|].
  split; [eapply bytes_at_transport; [exact BL | exact MU |];
          cbn [disjoint_from]; rewrite length_le8; unfold fuzz_alloc_peak_reset_c.G_PEAK, G_LIVE; lia|].
  split; [eapply bytes_at_transport; [exact BC | exact MU |];
          cbn [disjoint_from]; rewrite length_le8; unfold fuzz_alloc_peak_reset_c.G_PEAK, G_COUNT; lia|].
  reflexivity.
Qed.

(* 0x13798 (parse_noting returned rc): check_bounded_alloc(fuzz_alloc_peak() - live, size); count2 = fuzz_alloc_count();
   out_of_memory() is 0 (the g_own_ran_out byte 0, fuzz_alloc_ran_out() = 0); the arguments of
   check_as_written(data, size, rc, &doc) *)
Lemma ent_segB2 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z) (peak count : word),
  bytes_at rsegs m G_PEAK (le8 peak) -> bytes_at rsegs m G_COUNT (le8 count) ->
  bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  bv_unsigned s0 <= 2 ^ 40 ->
  (bv_unsigned peak - bv_unsigned s2) mod 2 ^ 64 <= 256 * bv_unsigned s0 + 20480 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR (Z_to_bv 64 0x137d8) (Z_to_bv 64 P) gp tp t0' t1' t2' s0 s1 s1 s0 a0 (Z_to_bv 64 P)
                    a4' a5' a6' a7' s2 s3 a0 count s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13ad4) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (GL_OWN_RAN_OUT + 0x4f8)) s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13798) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P peak count
    BP BC BO BR HS0 HH.
  pose proof (zr_word s0) as R0. unfold inr64 in R0.
  assert (RDO : ov_read_bytes rsegs m (wa OWNv) 1 = Some (le1 (Z_to_bv 64 0))).
  { replace (wa OWNv) with (wa (GL_OWN_RAN_OUT + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) 0 1 BO ltac:(lia)) by (rewrite length_le1; lia).
    reflexivity. }
  do 2 step.
  eapply evt_cut; [eapply HPEAK; exact BP|].
  intros ms' E. cbv beta in E. subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  do 3 step.
  eapply evt_cut.
  { eapply HCBA with (held := (bv_unsigned peak - bv_unsigned s2) mod 2 ^ 64) (size := bv_unsigned s0);
      [ apply ent_wrap | symmetry; apply Z_to_bv_bv_unsigned | apply Z.mod_pos_bound; lia | lia | exact HH ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E). subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  step.
  eapply evt_cut; [eapply HCOUNT; exact BC|].
  intros ms' E. cbv beta in E. subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  step. rewrite ?ent_zx8_0. step. if_false.
  do 2 step.
  eapply evt_cut; [eapply (HRO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0));
                   [vm_compute; reflexivity | exact BR]|].
  intros ms' E. cbv beta in E. subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  step. if_false.
  do 5 step.
  apply evt_done. do 11 eexists. reflexivity.
Qed.

(* 0x137d8 (check_as_written returned 0): took = count2 - count; rc = 0 goes on at 0x1383c; rc != 0:
   check_reject_clean(rc, &doc, live), then the arguments of check_reject_clean_starved(data, size, took, NULL) *)
Lemma ent_segC : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P lo rc : Z),
  s4 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 ->
  0 <= P -> P + 112 <= 2 ^ 64 ->
  (rc <> 0 -> bytes_at rsegs m P (repeat (Z_to_bv 8 0) 56)) ->
  (rc <> 0 -> bytes_at rsegs m G_LIVE (le8 s2)) ->
  mem_inv rsegs m -> stk rsegs m lo P -> lo + 16 <= P ->
  (G_LIVE + 8 <= P - 16 \/ P <= G_LIVE) ->
  evt rsegs (fun ms' =>
      (rc = 0 /\
       ms' = MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                     s2 (Z_to_bv 64 (bv_unsigned s5 - bv_unsigned s3)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1383c) fc None m (seg_rom rsegs)) \/
      (rc <> 0 /\
       exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         munch [(P - 16, P)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo P /\
         ms' = MS (mkR (Z_to_bv 64 0x13838) (Z_to_bv 64 P) gp tp t0' t1' t2' s0 s1 s1 s0
                       (Z_to_bv 64 (bv_unsigned s5 - bv_unsigned s3)) (Z_to_bv 64 0)
                       a4' a5' a6' a7' s2 (Z_to_bv 64 (bv_unsigned s5 - bv_unsigned s3)) s4 s5 s6 s7 s8 s9 s10 s11
                       t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13c3c) fc None m' (seg_rom rsegs)))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x137d8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P lo rc
    E4 Hrc HP1 HP2 HZ HL HI HK HLo HG.
  subst s4.
  step. if_true. step.
  destruct (Z.eq_dec rc 0) as [E0 | E0].
  - subst rc. step. if_true. apply evt_done. left. split; reflexivity.
  - assert (C0 : bv_eqb (Z_to_bv 64 rc) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
      replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
      apply Z.eqb_neq. Z.div_mod_to_equations. lia. }
    step. rewrite C0; cbv iota.
    do 4 step.
    eapply evt_cut.
    { eapply HCRC with (rc := rc) (lo := lo);
        [ reflexivity | lia | exact E0
        | rewrite unsigned_lit by lia; exact (HZ E0)
        | exact (HL E0) | exact HI
        | rewrite unsigned_lit by lia; exact HK
        | rewrite unsigned_lit by lia; unfold CHECK_REJECT_CLEAN_FRAME; lia
        | rewrite !unsigned_lit by lia; right; lia
        | rewrite unsigned_lit by lia; unfold CHECK_REJECT_CLEAN_FRAME; exact HG ]. }
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E & MU & WM & MI & ST).
    subst ms'. rewrite unsigned_lit in MU, ST by lia.
    rewrite ret_pc_even by first [lia | reflexivity].
    do 5 step.
    apply evt_done. right. split; [exact E0|].
    exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    reflexivity.
Qed.

End KA.

Section KA2.
Hypothesis HRST : fuzz_alloc_ran_out_reset_c.fuzz_alloc_ran_out_reset_contract.
Hypothesis HMOST : fuzz_alloc_most_c.fuzz_alloc_most_contract.

(* 0x13748: g_own_ran_out = 0; fuzz_alloc_ran_out_reset(); fuzz_alloc_most(PJ_ALLOC_BOUND(size)) (= 256 * size + 0x5000);
   the arguments of check_no_overread(data, size) *)
Lemma ent_segA2 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
  wr_at rsegs m GL_OWN_RAN_OUT 1 -> wr_at rsegs m fuzz_alloc_ran_out_reset_c.G_RAN_OUT 1 ->
  wr_at rsegs m fuzz_alloc_most_c.G_MOST 8 ->
  evt rsegs (fun ms' => exists m',
      munch [(GL_OWN_RAN_OUT, GL_OWN_RAN_OUT + 1); (fuzz_alloc_ran_out_reset_c.G_RAN_OUT,
              fuzz_alloc_ran_out_reset_c.G_RAN_OUT + 1); (fuzz_alloc_most_c.G_MOST, fuzz_alloc_most_c.G_MOST + 8)] m m' /\
      wmono rsegs m m' /\
      bytes_at rsegs m' GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) /\
      bytes_at rsegs m' fuzz_alloc_ran_out_reset_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) /\
      ms' = MS (mkR (Z_to_bv 64 0x13770) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 s1 s0 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 (Z_to_bv 64 (GL_OWN_RAN_OUT + 0x4f8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13868) fc None m' (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13748) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P WO WR WM0.
  unfold GL_OWN_RAN_OUT in *. unfold fuzz_alloc_ran_out_reset_c.G_RAN_OUT in *.
  unfold fuzz_alloc_most_c.G_MOST, GL_MOST in *.
  pose proof WO as (Wo & Wn & _).
  assert (HS : store_ok rsegs m (wa (OWNv + 0)) 1 = true) by (eapply wr_at_store_ok; [exact WO | lia | lia]).
  step. step.
  set (mw := write_to_mem m (wa (OWNv + 0)) (le1 (Z_to_bv 64 0))).
  assert (BW : bytes_at rsegs mw OWNv (le1 (Z_to_bv 64 0))).
  { unfold mw. rewrite Z.add_0_r. apply bytes_at_write_same; rewrite ?length_le1; lia. }
  assert (MW : munch [(OWNv, OWNv + 1)] m mw).
  { unfold mw. rewrite Z.add_0_r. apply munch_write; [apply munch_refl | lia | rewrite length_le1; lia | cbn; left; lia]. }
  assert (WMW : wmono rsegs m mw) by (unfold mw; apply wmono_write, wmono_refl).
  step.
  eapply evt_cut; [eapply HRST; exact (wr_at_transport rsegs m mw _ _ WR WMW)|].
  intros ms' (a0' & m1 & E & B1 & MU1 & WM1). subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  do 4 step.
  eapply evt_cut; [eapply HMOST; exact (wr_at_transport rsegs m m1 _ _ WM0 (wmono_trans rsegs m mw m1 WMW WM1))|].
  intros ms' (a1' & m2 & E & _ & MU2 & WM2). subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  do 3 step.
  apply evt_done. exists m2.
  split.
  { intros x Ho. cbn [outside] in Ho. rewrite (MU2 x ltac:(cbn [outside]; tauto)), (MU1 x ltac:(cbn [outside]; tauto)).
    apply MW. cbn [outside]. tauto. }
  split; [exact (wmono_trans rsegs m m1 m2 (wmono_trans rsegs m mw m1 WMW WM1) WM2)|].
  assert (BW1 : bytes_at rsegs m1 OWNv (le1 (Z_to_bv 64 0))).
  { apply (bytes_at_transport rsegs [(RANv, RANv + 1)] mw m1 OWNv _ BW MU1).
    cbn [disjoint_from]. rewrite length_le1. split; [lia | exact I]. }
  split.
  { apply (bytes_at_transport rsegs [(MOSTv, MOSTv + 8)] m1 m2 OWNv _ BW1 MU2).
    cbn [disjoint_from]. rewrite length_le1. split; [lia | exact I]. }
  split.
  { apply (bytes_at_transport rsegs [(MOSTv, MOSTv + 8)] m1 m2 RANv _ B1 MU2).
    cbn [disjoint_from]. rewrite length_le1. split; [lia | exact I]. }
  reflexivity.
Qed.

End KA2.

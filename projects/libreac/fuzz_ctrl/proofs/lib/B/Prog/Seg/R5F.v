(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 127 of its 157 lines of code are new or changed and 981 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R5.v r5_evt (:248) at a working branch 3803efccea0
     (blob 89e3315b7e73cf0f4e13b33131d4089b918be111);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r5_evt_of_F (evtF_evt + rng_all) re-derives the source statement of r5_evt in the lib.Lib
     vocabulary (the source states it on the lib.B.Tk.UL engine; the two engines step the same
     RiscvSemantics machine, so the re-run is the same 20 instructions).
   The run has no call, so it is one `_F`. Bridge input only: no top, no W_cutfree_ok, no cut-free twin.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R5.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The source file's cell helpers, restated over the lib.Lib cells (R5.v states them over the UL cells). *)
Lemma r5F_cell_bytes : forall m A cs k c bs,
  rw_cells rsegs m A cs -> cell_at cs k = Some c -> cbytes c = bs ->
  bytes_at rsegs m (A + Z.of_nat k) bs.
Proof.
  intros m A cs k c bs [[Hwf Hb] _] Hat <-.
  destruct (cell_at_split cs k c c Hat) as (pre & post & -> & Hsz & _).
  apply cells_wf_app in Hwf. destruct Hwf as [Hwfp Hwfc]. cbn in Hwfc. destruct Hwfc as [Hwfc Hwfs].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite (cells_bytes_length pre Hwfp), Hsz in Hb.
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma r5F_cell0 : forall m A cs v w,
  rw_cells rsegs m A cs -> cell_at cs 0 = Some (C8 v) -> v = w -> bytes_at rsegs m A (le8 w).
Proof.
  intros m A cs v w H Hc <-.
  pose proof (r5F_cell_bytes m A cs 0 (C8 v) (le8 v) H Hc eq_refl) as Hb.
  change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb.
Qed.

Lemma r5F_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Local Ltac r5F_val :=
  cbn [cbytes];
  first [ reflexivity
        | f_equal; first [ reflexivity
                         | apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn; lia ] ].

(* The footprint twin of R5.r5_evt: the whole R5 segment [0x8169c, 0x816e8], 20 instructions, no call, no
   instrumented check. The accesses are the five spill blocks it writes, one rng premise each. *)
Lemma r5_evt_F : forall (RNG : footprint)
  (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j1 j2 j3 j4 j5 : list byte),
    bv_unsigned s2 mod 8 = 0 ->
    rw_cells rsegs m (bv_unsigned s1 + 16) [CB 24 j1] ->
    rw_cells rsegs m (bv_unsigned s1 + 128) [CB 8 j2] ->
    rw_cells rsegs m (bv_unsigned s1 + 248) [CB 8 j3] ->
    rw_cells rsegs m (bv_unsigned s1 + 256) [CB 8 j4] ->
    rw_cells rsegs m (bv_unsigned s1 + 272) [CB 8 j5] ->
    rng RNG (bv_unsigned s1 + 16) 24 ->
    rng RNG (bv_unsigned s1 + 128) 8 ->
    rng RNG (bv_unsigned s1 + 248) 8 ->
    rng RNG (bv_unsigned s1 + 256) 8 ->
    rng RNG (bv_unsigned s1 + 272) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' s2' s5' s6' s8' s11' : word) (m' : word -> option byte),
         ms' = MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2' s3 s4 s5' s6' s7 s8' s9 s10 s11'
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x816ec) fc None m' (seg_rom rsegs) /\
         s5' = Z_to_bv 64 36 /\ s6' = Z_to_bv 64 0 /\ s11' = Z_to_bv 64 32 /\
         munch (R5.r5_W (bv_unsigned s1)) m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (bv_unsigned s1 + 16) (le8 (Z_to_bv 64 (bv_unsigned s2 + 20))) /\
         bytes_at rsegs m' (bv_unsigned s1 + 24) (le8 (Z_to_bv 64 (bv_unsigned s2 + 16))) /\
         bytes_at rsegs m' (bv_unsigned s1 + 32) (le8 (Z_to_bv 64 0)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 128) (le8 (Z_to_bv 64 0xe38f0000)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 248) (le8 (Z_to_bv 64 0x1234)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 256) (le8 (Z_to_bv 64 0x21140)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 272) (le8 (Z_to_bv 64 (bv_unsigned s2))))
      (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8169c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m j1 j2 j3 j4 j5 H8 C1 C2 C3 C4 C5 G1 G2 G3 G4 G5.
  assert (Hl7 : forall X, X = 7 -> Z.land (bv_unsigned s2) X = 0) by (intros X ->; exact (r5F_land7 _ H8)).
  pose proof (munch_refl [(bv_unsigned s1 + 16, bv_unsigned s1 + 40); (bv_unsigned s1 + 128, bv_unsigned s1 + 136);
                          (bv_unsigned s1 + 248, bv_unsigned s1 + 256); (bv_unsigned s1 + 256, bv_unsigned s1 + 264);
                          (bv_unsigned s1 + 272, bv_unsigned s1 + 280)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s1) as R1. change (bv_modulus 64) with (2^64) in R1.
  pose proof (rw_cells_bound _ _ _ _ C1) as HB1. cbn [cells_size csize Nat.add] in HB1.
  pose proof (rw_cells_bound _ _ _ _ C2) as HB2. cbn [cells_size csize Nat.add] in HB2.
  pose proof (rw_cells_bound _ _ _ _ C3) as HB3. cbn [cells_size csize Nat.add] in HB3.
  pose proof (rw_cells_bound _ _ _ _ C4) as HB4. cbn [cells_size csize Nat.add] in HB4.
  pose proof (rw_cells_bound _ _ _ _ C5) as HB5. cbn [cells_size csize Nat.add] in HB5.
  do 20 step.
  apply evtF_done. cbn beta.
  unfold R5.r5_W.
  eexists _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [exact MU|]. split; [exact WM|].
  split.
  { replace (bv_unsigned s1 + 16) with (bv_unsigned s1 + 16 + Z.of_nat 0) by (change (Z.of_nat 0) with 0%Z; lia).
    apply (r5F_cell_bytes _ _ _ 0 _ _ C1 ltac:(cells_cbv; reflexivity)). r5F_val. }
  split.
  { replace (bv_unsigned s1 + 24) with (bv_unsigned s1 + 16 + Z.of_nat 8) by (change (Z.of_nat 8) with 8%Z; lia).
    apply (r5F_cell_bytes _ _ _ 8 _ _ C1 ltac:(cells_cbv; reflexivity)). r5F_val. }
  split.
  { replace (bv_unsigned s1 + 32) with (bv_unsigned s1 + 16 + Z.of_nat 16) by (change (Z.of_nat 16) with 16%Z; lia).
    apply (r5F_cell_bytes _ _ _ 16 _ _ C1 ltac:(cells_cbv; reflexivity)).
    cbn [cbytes]. f_equal. f_equal. apply Hl7. vm_compute. reflexivity. }
  split; [eapply r5F_cell0; [exact C2 | cells_cbv; reflexivity |
            first [reflexivity | apply bv_eq; vm_compute; reflexivity]]|].
  split; [eapply r5F_cell0; [exact C3 | cells_cbv; reflexivity |
            first [reflexivity | apply bv_eq; vm_compute; reflexivity]]|].
  split; [eapply r5F_cell0; [exact C4 | cells_cbv; reflexivity |
            first [reflexivity | apply bv_eq; vm_compute; reflexivity]]|].
  eapply r5F_cell0; [exact C5 | cells_cbv; reflexivity |].
  first [reflexivity | symmetry; apply MState.Z_to_bv_bv_unsigned].
Qed.

(* ---- the compare lemma (the auditor's check): the source statement back from r5_evt_F ----
   R5.r5_evt states the run on the lib.B.Tk.UL engine. Its [mstep] is the lib.Lib [mstep] (both are
   `ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'`), so a lib.Lib run of the same
   Q is a UL run of it; the memory words (bytes_at, munch, wmono, rw_cells) are the same definitions in the
   two copies. *)
Module ULE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.

Lemma ul_msteps_of_msteps : forall ms ms', msteps rsegs ms ms' -> ULE.msteps rsegs ms ms'.
Proof.
  intros ms ms' H.
  induction H as [ms0|ms0 ms1 ms2 Hst Hs IH]; [apply ULE.msteps_refl|].
  eapply ULE.msteps_cons; [|exact IH]. destruct Hst as [HA HB]. split; [exact HA | exact HB].
Qed.

Lemma ul_evt_of_evt : forall (Q : machine_state -> Prop) ms, evt rsegs Q ms -> ULE.evt rsegs Q ms.
Proof.
  intros Q ms (ms1 & H & HQ). exists ms1. split; [exact (ul_msteps_of_msteps _ _ H) | exact HQ].
Qed.

Lemma r5_evt_of_F : forall
  (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j1 j2 j3 j4 j5 : list byte),
    bv_unsigned s2 mod 8 = 0 ->
    rw_cells rsegs m (bv_unsigned s1 + 16) [CB 24 j1] ->
    rw_cells rsegs m (bv_unsigned s1 + 128) [CB 8 j2] ->
    rw_cells rsegs m (bv_unsigned s1 + 248) [CB 8 j3] ->
    rw_cells rsegs m (bv_unsigned s1 + 256) [CB 8 j4] ->
    rw_cells rsegs m (bv_unsigned s1 + 272) [CB 8 j5] ->
    ULE.evt rsegs
      (fun ms' => exists (a0' a1' a2' s2' s5' s6' s8' s11' : word) (m' : word -> option byte),
         ms' = MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2' s3 s4 s5' s6' s7 s8' s9 s10 s11'
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x816ec) fc None m' (seg_rom rsegs) /\
         s5' = Z_to_bv 64 36 /\ s6' = Z_to_bv 64 0 /\ s11' = Z_to_bv 64 32 /\
         munch (R5.r5_W (bv_unsigned s1)) m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (bv_unsigned s1 + 16) (le8 (Z_to_bv 64 (bv_unsigned s2 + 20))) /\
         bytes_at rsegs m' (bv_unsigned s1 + 24) (le8 (Z_to_bv 64 (bv_unsigned s2 + 16))) /\
         bytes_at rsegs m' (bv_unsigned s1 + 32) (le8 (Z_to_bv 64 0)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 128) (le8 (Z_to_bv 64 0xe38f0000)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 248) (le8 (Z_to_bv 64 0x1234)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 256) (le8 (Z_to_bv 64 0x21140)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 272) (le8 (Z_to_bv 64 (bv_unsigned s2))))
      (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8169c) fc None m (seg_rom rsegs)).
Proof.
  intros rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m j1 j2 j3 j4 j5 H8 C1 C2 C3 C4 C5.
  pose proof (rw_cells_bound _ _ _ _ C1) as HB1. cbn [cells_size csize Nat.add] in HB1.
  pose proof (rw_cells_bound _ _ _ _ C2) as HB2. cbn [cells_size csize Nat.add] in HB2.
  pose proof (rw_cells_bound _ _ _ _ C3) as HB3. cbn [cells_size csize Nat.add] in HB3.
  pose proof (rw_cells_bound _ _ _ _ C4) as HB4. cbn [cells_size csize Nat.add] in HB4.
  pose proof (rw_cells_bound _ _ _ _ C5) as HB5. cbn [cells_size csize Nat.add] in HB5.
  apply ul_evt_of_evt.
  apply (evtF_evt rsegs RNG_all).
  apply (r5_evt_F RNG_all rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m j1 j2 j3 j4 j5 H8 C1 C2 C3 C4 C5);
    apply rng_all; lia.
Qed.

(* The source statement itself: this type-checks only if r5_evt_of_F has R5.r5_evt's type. *)
Definition r5_evt_of_F_is_source : ltac:(let T := type of R5.r5_evt in exact T) := r5_evt_of_F.

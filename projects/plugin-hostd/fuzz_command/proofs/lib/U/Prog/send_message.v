(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 1213 of its 1275 lines of code are new or changed and 486 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import memcpy_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition sm_mid1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (src n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j0 j1 j2 j3,
    ms' = MS (mkR (Z_to_bv 64 0x14474) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 n)
                  (Z_to_bv 64 src) a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18c10) fc None m' (seg_rom rsegs)
    /\ a0 = Z_to_bv 64 (Z.max n 1)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 64)%Z
         [CB 8 j0; C4 (Z_to_bv 64 7); CB 4 j1; CB 8 j2; CB 8 j3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma sm_max1 : forall n : Z, (0 <= n < 2 ^ 64)%Z ->
  Z_to_bv 64 (n + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (Z.max n 1).
Proof.
  intros n Hn. unfold v_sltiu. rewrite unsigned_lit by lia.
  change (bv_wrap 64 1) with 1%Z.
  destruct (Z.ltb_spec n 1); rewrite unsigned_lit by lia; f_equal; lia.
Qed.

Lemma sm_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo src n : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 64 <= bv_unsigned sp)%Z -> (0 <= n < 2 ^ 64)%Z -> (0 <= src < 2 ^ 64)%Z ->
  evt rsegs (sm_mid1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc src n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 src) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14444) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo src n ST LO NR SR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 64%nat junk [] [8; 4; 4; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 12 step.
  apply evt_done. unfold sm_mid1.
  replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp + -64)%Z by lia.
  do 19 eexists. split; [reflexivity|].
  split; [apply sm_max1; exact NR|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma sm_ro8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof.
  intros m A v H. split.
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Definition sm_mid2 (rao s0o s1o s2 sp1 gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (src n d : Z) (D : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j0 j1,
    ms' = MS (mkR (Z_to_bv 64 0x144a8) sp1 gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 src) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 d) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15ab4) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp1, bv_unsigned sp1 + 64); (d, d + n); (0x343e8, 0x343e8 + 4)]%Z m m'
    /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp1)
         [CB 8 j0; C4 (Z_to_bv 64 7); CB 4 j1; C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n); C8 s2; C8 s1o; C8 s0o; C8 rao]
    /\ bytes_at rsegs m' d D /\ bytes_at rsegs m' src D
    /\ rw_cells rsegs m' 0x343e8 [C4 (Z_to_bv 64 0)].

Lemma sm_run2 : memcpy_contract ->
  forall ra sp1 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (rao s0o s1o : word) (src n d q0 : Z)
    (D junk2 j0 j1 j2 j3 : list byte),
  rw_cells rsegs m (bv_unsigned sp1)
    [CB 8 j0; C4 (Z_to_bv 64 7); CB 4 j1; CB 8 j2; CB 8 j3; C8 s2; C8 s1o; C8 s0o; C8 rao] ->
  bytes_at rsegs m src D -> Z.of_nat (length D) = n ->
  rw_cells rsegs m d [CB (length D) junk2] ->
  (n <> 0 -> (src + n <= d \/ d + n <= src) /\ (src + n <= 0x10000 \/ 0x55000 <= src) /\
     src + n <= bv_unsigned sp1)%Z ->
  (d + n <= 0x10000 \/ 0x55000 <= d)%Z -> (0 < d)%Z -> (d + n <= bv_unsigned sp1)%Z ->
  (0 <= src < 2 ^ 64)%Z ->
  bytes_at rsegs m 0x22d10 (le8 (Z_to_bv 64 0x343e8)) ->
  rw_cells rsegs m 0x343e8 [C4 (Z_to_bv 64 q0)] ->
  (2 ^ 21 <= bv_unsigned sp1 < 2 ^ 63)%Z ->
  mem_inv rsegs m ->
  evt rsegs (sm_mid2 rao s0o s1o s2 sp1 gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc src n d D m)
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 src) (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14474) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra sp1 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rao s0o s1o src n d q0 D junk2 j0 j1 j2 j3 FR SRC LEN DST SEPS SEPD DPOS DLO SR GOT GQ SPR MI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  apply sm_ro8 in GOT.
  pose proof (munch_refl [(bv_unsigned sp1, bv_unsigned sp1 + 64); (d, d + n); (0x343e8, 0x343e8 + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UD : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
  step. if_false. step. step. if_cases HZ.
  - zify_cond HZ.
    destruct D as [|b0 D']; [|cbn [length] in LEN; lia].
    cbn [length] in LEN. subst n.
    do 6 step.
    apply evt_done. unfold sm_mid2.
    do 18 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia|].
    split; [split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia|].
    eassumption.
  - zify_cond HZ.
    destruct (SEPS HZ) as (SEP1 & SEP2 & SEP3).
    do 4 step.
    call (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D junk2).
    + rewrite US. exact SRC.
    + rewrite UN. lia.
    + rewrite UD, UN. replace (Z.to_nat n) with (length D) by lia. exact DST.
    + rewrite US, UD, UN. lia.
    + exact MI.
    + rewrite US in POST.
      match goal with H : rw_cells rsegs _ (bv_unsigned (Z_to_bv 64 d)) _ |- _ => rewrite UD, UN in H end.
      do 6 step.
      apply evt_done. unfold sm_mid2.
      do 18 eexists. split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split.
      { match goal with H : rw_cells rsegs ?mm d [CB _ D] |- bytes_at rsegs ?mm d D =>
          destruct H as [[_ Hb] _]; cbn [cells_bytes cbytes] in Hb; rewrite app_nil_r in Hb; exact Hb end. }
      split; [eassumption|]. eassumption.
Qed.

Lemma sm_run3 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  (bv_unsigned sp + 8 < 2 ^ 64)%Z ->
  evt rsegs (fun ms' => exists a0',
      ms' = MS (mkR (Z_to_bv 64 0x144b0) sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17400) fc None m (seg_rom rsegs) /\
      a0' = Z_to_bv 64 (bv_unsigned sp + 8))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x144a8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPR.
  do 2 step.
  apply evt_done. eexists. split; [reflexivity|].
  first [reflexivity | apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity].
Qed.

Lemma sm_run4 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (d : word),
  bytes_at rsegs m (bv_unsigned sp + 16) (le8 d) ->
  evt rsegs (fun ms' => exists a0',
      ms' = MS (mkR (Z_to_bv 64 0x144b8) sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs) /\
      a0' = d)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x144b0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d LD.
  apply sm_ro8 in LD.
  do 2 step.
  apply evt_done. eexists. split; [reflexivity|].
  first [reflexivity | apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity].
Qed.

Lemma sm_run5 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (rao s0o s1o s2o : word),
  bytes_at rsegs m (bv_unsigned sp + 32) (le8 s2o) -> bytes_at rsegs m (bv_unsigned sp + 40) (le8 s1o) ->
  bytes_at rsegs m (bv_unsigned sp + 48) (le8 s0o) -> bytes_at rsegs m (bv_unsigned sp + 56) (le8 rao) ->
  (bv_unsigned sp + 64 < 2 ^ 64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR rao (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 s0o s1o a0 a1 a2 a3 a4 a5 a6 a7
                    s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rao) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x144b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    rao s0o s1o s2o L2 L1 L0 LR SPR.
  apply sm_ro8 in L2, L1, L0, LR.
  do 6 step.
  apply evt_done.
  reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YN03 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU
  VerbsB CommandB verbs_receive_c rec_clear_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require RecKindB rec_shape_of rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_calls_free_c.
From Stdlib Require Import Permutation.
Local Open Scope Z_scope.

Lemma sm_cells_bytes_app : forall l1 l2, cells_bytes (l1 ++ l2) = cells_bytes l1 ++ cells_bytes l2.
Proof.
  induction l1 as [|c l1 IH]; intros l2; cbn [app cells_bytes]; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma sm_cells_wf_app : forall l1 l2, cells_wf (l1 ++ l2) -> cells_wf l1.
Proof.
  induction l1 as [|c l1 IH]; intros l2 H; [exact I|].
  destruct H as [H1 H2]. split; [exact H1 | exact (IH l2 H2)].
Qed.

Lemma sm_cell_get : forall segs m A pre c post, rw_cells segs m A (pre ++ c :: post) ->
  bytes_at segs m (A + Z.of_nat (cells_size pre)) (cbytes c).
Proof.
  intros segs m A pre c post [[Hwf Hb] _].
  rewrite sm_cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb].
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb as [Hb _].
  rewrite (cells_bytes_length pre (sm_cells_wf_app _ _ Hwf)) in Hb. exact Hb.
Qed.

Lemma sm_cell_get2 : forall segs m A pre c post k, rw_cells segs m A (pre ++ c :: post) -> cells_size pre = k ->
  bytes_at segs m (A + Z.of_nat k) (cbytes c).
Proof. intros segs m A pre c post k H <-. exact (sm_cell_get segs m A pre c post H). Qed.

Lemma sm_mod8 : forall z, z mod 16 = 0 -> (z - 56) mod 8 = 0.
Proof. intros z H. Z.div_mod_to_equations. lia. Qed.

Lemma sm_le_of_bytes : forall (B : malloc_syms) m a bs, ms_segs B = rsegs -> bytes_at rsegs m a bs -> le_at B m a bs.
Proof.
  intros B0 m a bs HS (H0 & H1 & H2). unfold le_at, blk_data. cbv zeta. rewrite HS. intros i Hi.
  rewrite mbyte_mrd. replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  apply H2. lia.
Qed.

Lemma sm_bytes_of_le : forall (B : malloc_syms) m a bs, ms_segs B = rsegs -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> le_at B m a bs -> bytes_at rsegs m a bs.
Proof.
  intros B0 m a bs HS H0 H1 H. apply bytes_at_of_mbyte; [exact H0 | exact H1 |].
  intros i Hi. unfold le_at, blk_data in H. cbv zeta in H. rewrite HS in H.
  rewrite (H (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma sm_le_keep : forall (B : malloc_syms) m m' a bs, le_at B m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  le_at B m' a bs.
Proof.
  intros B0 m m' a bs H K. unfold le_at, blk_data in *. cbv zeta in *. intros i Hi.
  rewrite K by exact Hi. exact (H i Hi).
Qed.

Lemma sm_bytes_of_image : forall segs m n A bs, image_bytes segs A n = Some bs ->
  (forall i, 0 <= i < Z.of_nat n -> mbyte segs m (A + i) = seg_rom segs (Z_to_bv 64 (A + i))) ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 -> bytes_at segs m A bs.
Proof.
  intros segs m n. induction n as [|n IH]; intros A bs HI HM H0 H1; cbn [image_bytes] in HI.
  - injection HI as <-. split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (PropExec.seg_rom segs (wa A)) as [b0|] eqn:E0; [|discriminate].
    destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E1; [|discriminate].
    injection HI as <-.
    change (b0 :: bs') with ([b0] ++ bs'). apply bytes_at_app. split.
    + split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth_error].
      replace (A + Z.of_nat 0) with A by lia. rewrite <- mbyte_mrd.
      pose proof (HM 0 ltac:(lia)) as H. rewrite Z.add_0_r in H. rewrite H. exact E0.
    + replace (A + Z.of_nat (length [b0])) with (A + 1) by (cbn; lia).
      apply IH; [exact E1 | | lia | lia]. intros i Hi.
      replace (A + 1 + i) with (A + (1 + i)) by lia. apply HM. lia.
Qed.

Lemma sm_img_res : forall (B : malloc_syms) k lo sz a, ms_segs B = rsegs ->
  nth_error (map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)) k = Some (lo, sz) ->
  lo <= a < lo + sz -> in_img B a.
Proof.
  intros B0 k lo sz a HS E Ha. unfold in_img. rewrite HS. split.
  - assert (L : length rsegs = 4%nat) by (vm_compute; reflexivity).
    intros H. rewrite H in L. discriminate.
  - rewrite nth_error_map in E. destruct (nth_error (segments_reserved rsegs) k) as [s|] eqn:E2; [|discriminate].
    cbv beta iota delta [option_map] in E. injection E as E3 E4.
    exists s. split; [exact (nth_error_In _ _ E2) | lia].
Qed.

Lemma sm_img_iv : forall (B : malloc_syms) a, ms_segs B = rsegs -> 0x10000 <= a < 0x55000 -> in_img B a.
Proof.
  intros B0 a HS Ha.
  destruct (Z_lt_ge_dec a 0x13000).
  { apply (sm_img_res B0 0 0x10000 0x3000); [exact HS | vm_compute; reflexivity | lia]. }
  destruct (Z_lt_ge_dec a 0x22000).
  { apply (sm_img_res B0 1 0x13000 0xF000); [exact HS | vm_compute; reflexivity | lia]. }
  destruct (Z_lt_ge_dec a 0x23000).
  { apply (sm_img_res B0 2 0x22000 0x1000); [exact HS | vm_compute; reflexivity | lia]. }
  apply (sm_img_res B0 3 0x23000 0x32000); [exact HS | vm_compute; reflexivity | lia].
Qed.

Lemma sm_out_sep : forall (B : malloc_syms) a k, ms_segs B = rsegs -> 1 <= k ->
  (forall i, 0 <= i < k -> ~ in_img B (a + i)) -> a + k <= 0x10000 \/ 0x55000 <= a.
Proof.
  intros B0 a k HS Hk H.
  destruct (Z_le_gt_dec (a + k) 0x10000) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec 0x55000 a) as [E'|E']; [right; exact E'|].
  exfalso. apply (H (Z.max 0 (0x10000 - a))); [lia|]. apply (sm_img_iv B0); [exact HS | lia].
Qed.

Lemma sm_relro_iv : forall a, in_globals frame_RELRO a -> 0x226b0 <= a < 0x23000.
Proof. intros a (lo & len & Hin & Hb). unfold frame_RELRO in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. Qed.

Lemma sm_relro_of : forall a, 0x226b0 <= a < 0x22d40 -> in_globals frame_RELRO a.
Proof. intros a Ha. exists 140976, 1680. split; [left; reflexivity | lia]. Qed.

Lemma sm_g_iv : forall a, in_globals frame_G a -> 0x33ff0 <= a < 0x343ec.
Proof. intros a (lo & len & Hin & Hb). unfold frame_G in Hin. destruct Hin as [E|[]]. injection E as <- <-. lia. Qed.

Lemma sm_g_of : forall a, 0x33ff0 <= a < 0x343ec -> in_globals frame_G a.
Proof. intros a Ha. exists 212976, 1020. split; [left; reflexivity | lia]. Qed.

Lemma sm_ro_low : forall x, ro_addr rsegs x = true -> bv_unsigned x < 2 ^ 20.
Proof.
  intros x Hx. destruct (Z_lt_ge_dec (bv_unsigned x) (2 ^ 20)) as [H|H]; [exact H|].
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
  rewrite <- (Z_to_bv_bv_unsigned x) in Hx. rewrite ro_addr_hi in Hx by lia. discriminate.
Qed.

Lemma sm_ro_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 20 -> Frame.outside W x) -> ro_agree rsegs m'.
Proof.
  intros W m m' H HM HW x Hx. unfold mrd. rewrite (HM x); [exact (H x Hx)|].
  pose proof (sm_ro_low x Hx). pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
  apply HW. lia.
Qed.

Lemma sm_got_img : image_bytes rsegs 0x22d10 8 = Some (le8 (Z_to_bv 64 0x343e8)).
Proof. vm_compute. repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ]. Qed.

Lemma sm_image_nth : forall segs n A bs i, image_bytes segs A n = Some bs -> (i < n)%nat ->
  PropExec.seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  intros segs n. induction n as [|n IH]; intros A bs i HI Hi; [lia|].
  cbn [image_bytes] in HI.
  destruct (PropExec.seg_rom segs (wa A)) as [b0|] eqn:E0; [|discriminate].
  destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E1; [|discriminate].
  injection HI as <-.
  destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E0.
  - replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IH; [exact E1 | lia].
Qed.

Lemma sm_got_rom_img : image_bytes rsegs 0x22d40 8 = Some (le8 (Z_to_bv 64 0x54730)).
Proof. vm_compute. repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ]. Qed.

Lemma sm_got_rom : forall m a, word_mem rsegs m SSP_GOT_B SSP_GUARD_B -> SSP_GOT_B <= a < SSP_GOT_B + 8 ->
  mbyte rsegs m a = seg_rom rsegs (Z_to_bv 64 a).
Proof.
  intros m a W Ha.
  pose proof (KindBGlue.word_mem_le8 rsegs m SSP_GOT_B SSP_GUARD_B W ltac:(unfold SSP_GUARD_B; lia)
    ltac:(unfold SSP_GOT_B; lia) ltac:(unfold SSP_GOT_B; lia)) as (_ & _ & H).
  rewrite Mem.length_le8 in H.
  assert (Ei : a = SSP_GOT_B + Z.of_nat (Z.to_nat (a - SSP_GOT_B))) by lia.
  rewrite Ei, mbyte_mrd. rewrite (H (Z.to_nat (a - SSP_GOT_B)) ltac:(unfold SSP_GOT_B in *; lia)).
  symmetry. exact (sm_image_nth rsegs 8 _ _ (Z.to_nat (a - SSP_GOT_B)) sm_got_rom_img ltac:(unfold SSP_GOT_B in *; lia)).
Qed.

Lemma sm_guard_wr : forall m i, 0 <= i < 8 -> writable_at rsegs m (SSP_GUARD_B + i).
Proof.
  intros m i Hi. unfold SSP_GUARD_B.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  repeat (destruct C as [C|C];
    [subst i; unfold writable_at, wview; destruct (m _); [discriminate | vm_compute; discriminate]|]).
  subst i; unfold writable_at, wview; destruct (m _); [discriminate | vm_compute; discriminate].
Qed.

Lemma sm_quit_ro : forall i, 0 <= i < Z.of_nat (cells_size [C4 (Z_to_bv 64 0)]) -> ro_addr rsegs (Z_to_bv 64 (0x343e8 + i)) = false.
Proof.
  intros i Hi. cbn in Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i; vm_compute; reflexivity.
Qed.

Lemma sm_rfree_le : forall F b, (forall pn, In pn F -> 0 <= snd pn) -> RecKindB.sb_le (RecKindB.rfree_b b F) b.
Proof.
  unfold RecKindB.rfree_b. induction F as [|pn F IH]; intros b HF; cbn [fold_left]; [apply RecKindB.sb_le_refl|].
  eapply RecKindB.sb_le_trans; [apply IH | apply RecKindB.sb_free_le].
  - intros x Hx. apply HF. right. exact Hx.
  - apply HF. left. reflexivity.
Qed.

Lemma sm_rfree_cap : forall F b, sb_cap (RecKindB.rfree_b b F) = sb_cap b.
Proof.
  unfold RecKindB.rfree_b. induction F as [|pn F IH]; intros b; cbn [fold_left]; [reflexivity|].
  rewrite IH. cbn. reflexivity.
Qed.

Lemma sm_up_le : forall b k n, 0 <= k -> 0 <= n -> RecKindB.sb_le b (sb_up b k n).
Proof. intros b k n Hk Hn. unfold RecKindB.sb_le, sb_up. cbn. lia. Qed.

Lemma sm_blocks_nonneg : forall L A pn, WF A -> In pn (blocks L A) -> 0 <= snd pn.
Proof.
  intros L A pn HW Hin. unfold blocks in Hin. apply in_map_iff in Hin as (x & <- & Hx). cbn.
  exact (AllocBound.ub_nonneg A HW x Hx).
Qed.

Lemma sm_pw_perm : forall {X} (R : X -> X -> Prop) l l', (forall x y, R x y -> R y x) ->
  Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros X R l l' Hs HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact I.
  - destruct H as [H1 H2]. split; [|exact (IH H2)]. intros y Hy. apply H1.
    exact (Permutation_in _ (Permutation_sym HP) Hy).
  - destruct H as [H1 [H2 H3]]. split; [|split; [|exact H3]].
    + intros z [<-|Hz]; [apply Hs; apply H1; left; reflexivity | exact (H2 z Hz)].
    + intros z Hz. apply H1. right. exact Hz.
  - exact (IH2 (IH1 H)).
Qed.

Lemma sm_pw_cross : forall {X} (R : X -> X -> Prop) u v x y, pairwise R (u ++ v) -> In x u -> In y v -> R x y.
Proof.
  intros X R u. induction u as [|z u IH]; intros v x y H Hx Hy; [destruct Hx|].
  destruct H as [H1 H2]. destruct Hx as [<-|Hx].
  - apply H1. apply in_or_app. right. exact Hy.
  - exact (IH v x y H2 Hx Hy).
Qed.

Lemma sm_pw_dup : forall l l2 D pn, pairwise ranges_disjoint l -> Permutation l (l2 ++ D) ->
  In pn l2 -> In pn D -> 1 <= snd pn -> False.
Proof.
  intros l l2 D pn HP HPm H2 HD Hs.
  assert (HS : forall x y, ranges_disjoint x y -> ranges_disjoint y x) by (unfold ranges_disjoint; intros; lia).
  pose proof (sm_pw_cross _ _ _ _ _ (sm_pw_perm _ _ _ HS HPm HP) H2 HD) as R. unfold ranges_disjoint in R. lia.
Qed.

Lemma sm_pw_same : forall l a k k', pairwise ranges_disjoint l -> In (a, k) l -> In (a, k') l ->
  1 <= k -> 1 <= k' -> k = k'.
Proof.
  intros l a k k' HP H1 H2 Hk Hk'. destruct (Z.eq_dec k k') as [E|E]; [exact E|].
  destruct (YI06.pairwise_in2 _ _ _ _ HP H1 H2 ltac:(intro F; injection F; lia)) as [R|R];
    unfold ranges_disjoint in R; cbn in R; lia.
Qed.

Lemma sm_pw_mid : forall l1 x l2, pairwise ranges_disjoint (l1 ++ x :: l2) -> 1 <= snd x -> ~ In x (l1 ++ l2).
Proof.
  intros l1 x l2 HP Hs Hin. destruct (pairwise_app_mid' _ _ _ _ _ HP Hin) as [R|R]; unfold ranges_disjoint in R; lia.
Qed.

Lemma sm_call_pn : forall segs bl mem a c P pn, call_at segs bl mem a c P -> In pn P -> In pn bl /\ 1 <= snd pn.
Proof.
  intros segs bl mem a c P pn (_ & _ & HL & _ & _ & _ & HK) Hin.
  apply In_nth_error in Hin as (k & Ek).
  assert (Hk : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (HK k s pn Es Ek) as (_ & _ & Hb & Hsz & _). split; [exact Hb | lia].
Qed.

Lemma sm_rec_O : forall segs L A mem R O pn, g_rec_rep segs L A mem R O -> In pn O -> In pn (blocks L A) /\ 1 <= snd pn.
Proof.
  intros segs L A mem R O pn (Q & (HS & HC & HA & HP & HX & HW) & HO) Hin.
  apply HO in Hin. unfold lay_blocks in Hin.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP' & Hpn).
    apply In_nth_error in HP' as (i & Ei).
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (sm_call_pn _ _ _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (sm_call_pn _ _ _ _ _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + unfold answer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [q|];
        cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & _ & Hb & Hsz & _). split; [exact Hb | lia].
    + unfold reply_at in HP. destruct (r_reply R) as [t|]; destruct (l_reply Q) as [q|];
        cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & _ & Hne & Hb & Hsz & _).
      split; [exact Hb|]. destruct t as [|b0 t]; [contradiction|]. cbn [length] in Hsz. lia.
Qed.

Lemma sm_rec_calls : forall segs L A mem R O, g_rec_rep segs L A mem R O -> (length (r_calls R) <= 16)%nat.
Proof. intros segs L A mem R O (Q & (_ & (C1 & _) & _) & _). exact C1. Qed.

Lemma sm_rcw_vr : forall k a, (k <= 16)%nat -> rec_clear_writes k a -> vr_writes a.
Proof.
  intros k a Hk H. unfold rec_clear_writes, vr_writes, nargs_field in *.
  unfold G_REC, REC_SIZE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE in *.
  left. destruct H as [H|[(i & Hi & H)|[H|H]]]; lia.
Qed.

Lemma sm_wv : forall h h' md, with_vmmaps h (with_vmmaps h' md) = with_vmmaps h md.
Proof. intros h h' md. unfold with_vmmaps. reflexivity. Qed.

Lemma sm_ptr_stable : forall A L L' p n, WF A -> In (p, n) (user_blocks A) -> layout_le A L L' ->
  ptr_addr L' p = ptr_addr L p.
Proof.
  intros A L L' p n HW Hin (_ & _ & _ & HR).
  destruct (YN03.block_region A p n HW Hin) as (k & o & rg & -> & Hr & _).
  destruct (region_of_lt A k rg Hr) as [Hk _].
  unfold ptr_addr, loc_addr. rewrite (HR k Hk). reflexivity.
Qed.

Lemma sm_lle_trans : forall A A' L1 L2 L3, layout_le A L1 L2 -> layout_le A' L2 L3 ->
  (length (st_regions A) <= length (st_regions A'))%nat -> layout_le A L1 L3.
Proof.
  intros A A' L1 L2 L3 (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (G4 r ltac:(lia)). exact (H4 r Hr).
Qed.

Ltac sm_keep X :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hx := fresh "Hx" in let C := fresh "C" in
  intros r Hr Hx; unfold callee_saved in Hr;
  assert (C : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/
              r = 27) by lia;
  repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X) by reflexivity; reflexivity|]);
  subst r; rewrite (getr_of_eqv _ _ _ X) by reflexivity; reflexivity.

Section Send.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALLOC_PC : ms_malloc B = 0x18c10.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GUARD_AT : ms_guard B = SSP_GUARD_B.
Hypothesis GOT_AT : ms_got_guard B = SSP_GOT_B.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTXO : ctx_owned B API.
Hypothesis G_STAT : forall a, in_globals frame_G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RELRO_FREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a ->
  ~ (ms_got_guard B <= a < ms_got_guard B + 8) -> ~ owned B L A a /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis RCLEAR : rec_clear_contract B API.
Hypothesis VRECV : verbs_receive_contract B API.
Hypothesis ERRNO_IMG : in_img B (errno_addr B).
Hypothesis ERRNO_GUARD : errno_addr B + 4 <= SSP_GUARD_B \/ SSP_GUARD_B + 8 <= errno_addr B.

Lemma sm_nown : forall L A mem md a, aa_MR API L A mem md -> (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
  ~ owned B L A a -> forall L' A' mem' md', aa_MR API L' A' mem' md' -> ~ owned B L' A' a.
Proof using AX CTXO.
  intros L A mem md a HM Ha Ho L' A' mem' md' HM' Ho'.
  destruct Ha as [Ha|Ha].
  - pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM' Ho'). lia.
  - destruct Ho' as [Hal|Hst]; apply Ho; [|right; exact Hst].
    apply (CTXO L A mem md a HM). exact (ax_img AX L' A' mem' md' a HM' Ha Hal).
Qed.

Lemma sm_gnown : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof using AX G_STAT.
  intros L A mem md a HM Hg Ho. destruct (G_STAT a Hg) as (Hi & Hs & Hc & _).
  destruct Ho as [Hal|Hst]; [exact (Hc (ax_img AX L A mem md a HM Hi Hal)) | exact (Hs Hst)].
Qed.

Lemma sm_blk_img : forall L A mem md a k i, aa_MR API L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (a + i).
Proof using AX.
  intros L A mem md a k i HM Hin Hi. apply YI06.blocks_In in Hin as (p & <- & Hp).
  exact (ax_blocks_img AX L A mem md p k i HM Hp Hi).
Qed.

Theorem send_message_holds : send_message_contract B API.
Proof using SEGS MALLOC_PC FREE_PC ERRNO_LOW GUARD_AT GOT_AT AX CTXO G_STAT RELRO_FREE MALLOC FREE MEMCPY RCLEAR VRECV
  ERRNO_IMG ERRNO_GUARD.
  unfold send_message_contract.
  intros L A regs mem md b R O src n q0 D can _ PRE CMD FRM A10 A11 SRCD LEN NMAX SRCP REP REFUSE QUIT0 QW QOUT VT
    RES ROOM.
  destruct PRE as [PRE SPT].
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC. pose proof alloc_ceiling_lt as AC2.
  assert (SMK : SM_K = 15008) by reflexivity.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite SMK in HCEIL, HWS.
  destruct CMD as (RO & GIMG & _ & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  rewrite SEGS in HWS, HERR, RO, QW, REP.
  assert (GIM : forall a, in_globals frame_RELRO a -> mbyte rsegs mem a = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. rewrite <- SEGS. exact (GIMG a Ha). }
  clear GIMG.
  assert (Hn0 : 0 <= n) by lia.
  assert (MN1 : 1 <= Z.max n 1) by lia.
  set (KP := fun a => (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) /\ ~ owned B L A a).
  assert (KPN : forall a L' A' m' md', KP a -> aa_MR API L' A' m' md' -> ~ owned B L' A' a).
  { intros a L' A' m' md' [Ha Ho] HM'. exact (sm_nown L A mem md a HMR Ha Ho L' A' m' md' HM'). }
  assert (KPR : forall a, KP a -> 0 <= a < 2 ^ 64).
  { intros a [[Ha|Ha] _]; [lia | pose proof (in_img_low B SEGS a Ha); lia]. }
  assert (KPH : forall a, alloc_ceiling <= a < 2 ^ 64 -> KP a).
  { intros a Ha. split; [left; exact Ha|]. intros Ho. pose proof (owned_low B _ LAWS _ _ _ _ _ HMR Ho). lia. }
  assert (GX : forall a, in_globals frame_G a ->
             KP a /\ ~ scratch_k B SM_K regs a /\ ~ (errno_addr B <= a < errno_addr B + 4)).
  { intros a Ha. pose proof (sm_g_iv a Ha) as Hr. destruct (G_STAT a Ha) as (Hi & _ & _ & He).
    split; [split; [right; exact Hi | exact (sm_gnown L A mem md a HMR Ha)]|]. split; [|exact He].
    unfold scratch_k. rewrite SMK. change (spZ regs) with (bv_unsigned sp). intros [H|H]; [lia | exact (He H)]. }
  assert (RLX : forall a, in_globals frame_RELRO a -> ~ (ms_got_guard B <= a < ms_got_guard B + 8) ->
             KP a /\ ~ scratch_k B SM_K regs a /\ ~ vr_writes a).
  { intros a Ha Hg. pose proof (sm_relro_iv a Ha) as Hr. destruct (RELRO_FREE L A mem md a HMR Ha Hg) as [Ho He].
    split; [|split].
    - split; [right; apply (sm_img_iv B a SEGS); lia | exact Ho].
    - unfold scratch_k. rewrite SMK. change (spZ regs) with (bv_unsigned sp). intros [H|H]; [lia | exact (He H)].
    - unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT. lia. }
  assert (ST : stk rsegs mem (bv_unsigned sp - 15008) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 src)) as RSW. unfold bv_modulus in RSW. cbn in RSW.
  set (sw := bv_unsigned (Z_to_bv 64 src)) in *.
  assert (EW : Z_to_bv 64 sw = Z_to_bv 64 src) by apply Z_to_bv_bv_unsigned.
  assert (SWE : n <> 0 -> sw = src).
  { intros Hn. destruct (SRCP Hn) as (H1 & H2 & _). unfold sw. apply unsigned_lit. lia. }
    rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 sw) by (rewrite EW; exact A10).
    assert (R11 : reg_get regs 11 = Z_to_bv 64 n) by exact A11.
    rewrite R10, R11. unfold SEND_MESSAGE.
    eapply sm_run1; [exact ST | lia | lia | lia]. }
  intros ms1 (can1 & Q1 & EQ1). unfold sm_mid1 in Q1.
  destruct Q1 as (u0 & u1 & u2 & v0 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & j0 & j1 & j2 & j3
    & -> & V0 & MU1 & WM1 & FR1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x14474) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 n) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 sw) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (Z.max n 1)) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; exact V0).
  assert (E1_18 : getr R1 18 = reg_get regs 18) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
  assert (K1 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by sm_keep X1.
  assert (USP1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 64)) = bv_unsigned sp - 64) by (apply unsigned_lit; lia).
  assert (SP1 : spZ R1 = bv_unsigned sp - 64) by (unfold spZ; rewrite E1_2; exact USP1).
  assert (CK1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 64 <= a < bv_unsigned sp) ->
             mbyte rsegs m1 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m1 a)).
  { intros a Ha Hx. assert (Ho : Frame.outside [(bv_unsigned sp - 64, bv_unsigned sp)] a) by (cbn; split; [exact Hx | exact I]).
    split; [exact (munch_mbyte _ _ _ _ _ MU1 Ha Ho) | exact (munch_writable _ _ _ _ _ MU1 Ha Ho)]. }
  assert (RO1 : ro_agree rsegs m1).
  { apply (sm_ro_munch _ mem m1 RO MU1). intros x Hx. cbn. split; [lia | exact I]. }
  assert (PRE1 : call_pre_k B (aa_MR API) ALLOC_STACK L A R1 m1 md).
  { pose proof (KindBGlue.kb_pre_A B API SM_K 64 ALLOC_STACK L A regs mem md R1 m1
      [(bv_unsigned sp - 64, bv_unsigned sp)] PRE0) as KPA.
    rewrite SEGS in KPA. change ALLOC_STACK with 8192 in *.
    apply KPA; clear KPA.
    - lia. - lia. - rewrite SMK. lia.
    - rewrite SP1. reflexivity.
    - rewrite SP1. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - exact E1_4.
    - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    - exact MU1.
    - exact WM1.
    - intros x Hx Hs. change (spZ regs) with (bv_unsigned sp) in Hs. cbn. split; [lia | exact I].
    - intros x Hx _. cbn. split; [lia | exact I]. }
    pose proof MALLOC as MAL. unfold malloc_contract in MAL. rewrite SEGS, MALLOC_PC in MAL.
  eapply SR_bind.
  { eapply (MAL L A R1 m1 md (Z.max n 1) b); [exact PRE1 | exact RO1 | exact E1_10 | exact RES |].
    apply (RecKindB.room_slots_mono _ (sb_up b SM_PEAK SM_PEAKB) _ VR_REQ);
      [apply (sm_up_le b SM_PEAK SM_PEAKB); unfold SM_PEAK, SM_PEAKB; lia
      | unfold VR_REQ; lia | exact ROOM]. }
  intros c2 RET.
  destruct RET as (L1 & A1 & R2 & m2 & md1 & d & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RO2 & GK & UBK
    & INIT & RLEN & RES').
  destruct POST as (HMR1 & HWF1 & HBD1 & HLE1 & HSTAB1 & HPRES1 & HVM1 & HFRAME1 & HBLKS1 & HSCR1).
  rewrite SEGS in HFRAME1, HBLKS1, HSCR1, RO2. unfold blocks_kept in KEPT. rewrite SEGS in KEPT.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR1) as (Hh1 & Hl1 & Hmat1).
  destruct BLK as (b1 & b2 & BLK1 & BLK2).
  destruct FRESH as (FR_lo & FR_hi & FR_img).
  assert (INB1 : In (d, Z.max n 1) (blocks L1 A1)) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  assert (PW1 : pairwise ranges_disjoint (blocks L1 A1)) by exact (mr_blocks_disjoint B _ LAWS _ _ _ _ HMR1).
  assert (DNEW : ~ In (d, Z.max n 1) (blocks L A)).
  { rewrite BLK2. apply (sm_pw_mid b1 _ b2); [rewrite <- BLK1; exact PW1 | cbn; lia]. }
  assert (OB : forall pn, In pn O -> In pn (blocks L A) /\ 1 <= snd pn) by (intros pn H; exact (sm_rec_O _ _ _ _ _ _ _ REP H)).
  assert (DOA : ~ In d (map fst O)).
  { intros H. apply in_map_iff in H as ([a k] & Ea & Hin). cbn in Ea. subst a.
    destruct (OB _ Hin) as [Hb Hk]. rewrite BLK2 in Hb. cbn in Hk.
    pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR1 BLK1 Hb). lia. }
  assert (DSEP : d + Z.max n 1 <= 0x10000 \/ 0x55000 <= d) by (apply (sm_out_sep B d _ SEGS MN1); exact FR_img).
  assert (BLD : forall a k, In (a, k) (blocks L A) -> a + k <= d \/ d + Z.max n 1 <= a).
  { intros a k Hin. rewrite BLK2 in Hin. exact (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR1 BLK1 Hin). }
  assert (CK2 : forall a, KP a -> ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp - 64) ->
             ~ (errno_addr B <= a < errno_addr B + 4) ->
             mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
  { intros a Ha Hs He. apply HFRAME1; [exact (proj1 Ha) | exact (proj2 Ha) | exact (KPN a _ _ _ _ Ha HMR1) | |
      intros F; exact F].
    unfold scratch_k. rewrite SP1. change ALLOC_STACK with 8192. intros [H|H]; [apply Hs; lia | exact (He H)]. }
  assert (F2 : forall a, KP a -> ~ scratch_k B SM_K regs a ->
             mbyte rsegs m2 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m2 a)).
  { intros a Ha Hs. unfold scratch_k in Hs. rewrite SMK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
    assert (Hs1 : ~ (bv_unsigned sp - 15008 <= a < bv_unsigned sp)) by tauto.
    assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
    destruct (CK1 a (KPR a Ha) ltac:(lia)) as [E1 W1]. destruct (CK2 a Ha ltac:(lia) Hs2) as [E2 W2].
    split; [congruence | tauto]. }
  assert (BK2 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m2 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hi. destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
    rewrite (KEPT a k i Hin (fun F => F) Hi). exact (proj1 (CK1 (a + i) ltac:(lia) ltac:(lia))). }
  assert (BM2 : forall pn, In pn (blocks L A) -> In pn (blocks L1 A1)).
  { intros pn Hin. rewrite BLK1. rewrite BLK2 in Hin.
    apply in_app_or in Hin as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; right; exact Hb]. }
  assert (FR2 := FR1).
  apply (rw_cells_transfer rsegs m1 m2) in FR2;
    [| intros i Hi; cbn in Hi; destruct (CK2 (bv_unsigned sp - 64 + i) (KPH (bv_unsigned sp - 64 + i) ltac:(lia)) ltac:(lia) ltac:(lia)) as [E W];
       split; [exact E | apply W]].
  assert (SRC2 : bytes_at rsegs m2 sw D).
  { destruct (Z.eq_dec n 0) as [Z0|Z0].
    - destruct D as [|x D']; [|cbn [length] in LEN; lia].
      split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
    - rewrite (SWE Z0). destruct (SRCP Z0) as (S1 & S2 & (p & k & Hpk & Hpo & Hp1 & Hp2) & _).
      apply (sm_bytes_of_le B m2 src D SEGS); [lia | lia |].
      apply (sm_le_keep B mem); [exact SRCD|]. rewrite SEGS. intros i Hi.
      replace (src + i) with (p + (src + i - p)) by ring. apply (BK2 p k); [exact Hpk | lia]. }
  destruct (present_rw_cells rsegs m2 d (length D)) as [junk2 DST2]; [lia | lia | |].
  { intros i Hi. exact (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i HMR1 INB1 ltac:(lia))). }
  assert (GOT2 : bytes_at rsegs m2 0x22d10 (le8 (Z_to_bv 64 0x343e8))).
  { apply (sm_bytes_of_image rsegs m2 8 _ _ sm_got_img); [| lia | lia].
    intros i Hi. cbn in Hi.
    assert (Hr : in_globals frame_RELRO (0x22d10 + i)) by (apply sm_relro_of; lia).
    destruct (RLX _ Hr ltac:(rewrite GOT_AT; unfold SSP_GOT_B; lia)) as (G1 & G2 & _).
    rewrite <- (GIM _ Hr). exact (proj1 (F2 _ G1 G2)). }
  assert (LE4 : forall v, length (le4 v) = 4%nat) by reflexivity.
  assert (GQ2 : rw_cells rsegs m2 0x343e8 [C4 (Z_to_bv 64 q0)]).
  { split; [split; [cbn; tauto|]|].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (sm_bytes_of_le B m2 _ _ SEGS); [lia | rewrite LE4; lia |].
      apply (sm_le_keep B mem); [exact QUIT0|]. rewrite SEGS. intros i Hi. rewrite LE4 in Hi.
      destruct (GX (G_QUIT + i) (sm_g_of (G_QUIT + i) ltac:(unfold G_QUIT; lia))) as (G1 & G2 & _).
      exact (proj1 (F2 _ G1 G2)).
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      destruct (GX (G_QUIT + i) (sm_g_of (G_QUIT + i) ltac:(unfold G_QUIT; lia))) as (G1 & G2 & _).
      change (writable_at rsegs m2 (G_QUIT + i)). apply (proj2 (F2 _ G1 G2)). exact (QW i Hi). }
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by exact (eq_trans (HPRES1 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_4 : getr R2 4 = getr regs 4) by exact (eq_trans (HPRES1 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 n) by exact (eq_trans (HPRES1 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 sw) by exact (eq_trans (HPRES1 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_18 : reg_get R2 18 = reg_get regs 18)
    by exact (eq_trans (HPRES1 18 ltac:(unfold callee_saved; lia)) E1_18).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 d) by exact A0'.
  assert (K2 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr Hx. rewrite (HPRES1 r Hr). exact (K1 r Hr Hx). }
    rewrite E1_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_8, E2_9, E2_10, E2_18.
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO2 |].
    eapply (sm_run2 MEMCPY) with (D := D) (junk2 := junk2) (q0 := q0).
    - rewrite USP1. apply rw_cells_normalize; [exact RO2 | exact FR2 |]. intros i Hi. cbn in Hi. apply ro_addr_hi. lia.
    - apply bytes_at_normalize; [exact RO2 | exact SRC2].
    - exact LEN.
    - apply rw_cells_normalize; [exact RO2 | exact DST2 |]. intros i Hi. cbn [cells_size csize] in Hi.
      rewrite Nat.add_0_r in Hi. apply (ro_addr_out B SEGS); [lia | apply FR_img; lia].
    - intros Hn. rewrite (SWE Hn). rewrite USP1. destruct (SRCP Hn) as (S1 & S2 & (p & k & Hpk & Hpo & Hp1 & Hp2) & _).
      pose proof (BLD p k Hpk) as Dj.
      assert (Hk : 1 <= k) by lia.
      pose proof (sm_out_sep B p k SEGS Hk (fun i Hi => sm_blk_img L A mem md p k i HMR Hpk Hi)) as Sp.
      destruct (block_facts B _ LAWS _ _ _ _ _ _ 0 HMR Hpk ltac:(lia)) as (_ & Hq1 & Hq2 & _).
      lia.
    - lia.
    - lia.
    - rewrite USP1. lia.
    - lia.
    - apply bytes_at_normalize; [exact RO2 | exact GOT2].
    - apply rw_cells_normalize; [exact RO2 | exact GQ2 | exact sm_quit_ro].
    - rewrite USP1. lia.
    - apply mem_inv_normalize. }
  intros ms3 (can3 & (s3 & Q3 & REL3 & ROS3) & EQ3). unfold sm_mid2 in Q3.
  destruct Q3 as (w0 & w1 & w2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & w3 & w4 & w5 & w6 & m3' & k0 & k1
    & -> & MU3' & WM3' & FR3' & BD3' & BS3' & GQ3').
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [CAN3 HR3].
  remember (ms_mem can3) as m3 eqn:Em3. subst can3. clear Em3.
  assert (RN2 : mem_rel rsegs m2 (normalize rsegs m2)) by (apply mem_rel_normalize; exact RO2).
  pose proof (munch_rel rsegs _ _ _ _ _ RN2 HR3 ROS3 MU3') as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ RN2 HR3 ROS3 WM3') as WM3.
  pose proof (ro_agree_same rsegs _ _ RO2 ROS3) as RO3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR3 FR3') as FR3.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR3) BD3') as BD3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR3 GQ3') as GQ3.
  clear MU3' WM3' FR3' BD3' BS3' GQ3' HR3 REL3 ROS3 RN2.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  rewrite USP1 in MU3, FR3.
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x144a8) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_4 : getr R3 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; exact E2_4).
  assert (K3' : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R3 (Z_to_bv 5 r) = getr R2 (Z_to_bv 5 r)) by sm_keep X3.
  assert (K3 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr Hx. rewrite (K3' r Hr Hx). exact (K2 r Hr Hx). }
  clear K3'.
  assert (SP3 : spZ R3 = bv_unsigned sp - 64) by (unfold spZ; rewrite E3_2; exact USP1).
  assert (OW3 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 64 <= a < bv_unsigned sp) -> ~ (d <= a < d + n) ->
             ~ (G_QUIT <= a < G_QUIT + 4) ->
             Frame.outside [(bv_unsigned sp - 64, bv_unsigned sp - 64 + 64); (d, d + n); (0x343e8, 0x343e8 + 4)] a).
  { intros a Ha H1 H2 H3. unfold G_QUIT in H3. cbn. repeat split; lia. }
  assert (CK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 64 <= a < bv_unsigned sp) -> ~ (d <= a < d + n) ->
             ~ (G_QUIT <= a < G_QUIT + 4) ->
             mbyte rsegs m3 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a <-> writable_at rsegs m3 a)).
  { intros a Ha H1 H2 H3. pose proof (OW3 a Ha H1 H2 H3) as Ho.
    split; [exact (munch_mbyte _ _ _ _ _ MU3 Ha Ho) | exact (munch_writable _ _ _ _ _ MU3 Ha Ho)]. }
  assert (MR3 : aa_MR API L1 A1 m3 md1).
  { apply (mr_frame B _ LAWS L1 A1 m2 m3 md1 md1 HMR1).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HMR1 Ho) as [Ha1 Ha2]. rewrite SEGS.
      assert (Hd : ~ (d <= a < d + n)).
      { intros Hd. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - d) HMR1 INB1 ltac:(lia))))).
        replace (d + (a - d)) with a by ring. exact Ho. }
      assert (Hq : ~ (G_QUIT <= a < G_QUIT + 4)).
      { intros Hq. exact (sm_gnown L1 A1 m2 md1 a HMR1 (sm_g_of a ltac:(unfold G_QUIT in Hq; lia)) Ho). }
      exact (proj1 (CK3 a ltac:(lia) ltac:(lia) Hd Hq)).
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ _ HMR1 Ho) as [Ha1 Ha2].
      assert (Hd : ~ (d <= a < d + n)).
      { intros Hd. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - d) HMR1 INB1 ltac:(lia))))).
        replace (d + (a - d)) with a by ring. exact Ho. }
      assert (Hq : ~ (G_QUIT <= a < G_QUIT + 4)).
      { intros Hq. exact (sm_gnown L1 A1 m2 md1 a HMR1 (sm_g_of a ltac:(unfold G_QUIT in Hq; lia)) Ho). }
      exact (munch_present _ _ _ a MU3 ltac:(lia) (OW3 a ltac:(lia) ltac:(lia) Hd Hq) Hp).
    - intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L1 A1 m2 md1 p k i HMR1 Hin Hi) as (Hp & H4 & Hc & _).
      apply (present_of_writable_out B SEGS m3 (ptr_addr L1 p + i) ltac:(lia) (ax_blocks_img AX L1 A1 m2 md1 p k i HMR1 Hin Hi)).
      unfold writable_at. apply WM3. exact (RecKindB.present_writable rsegs m2 _ Hp).
    - reflexivity.
    - exact Hh1.
    - exact Hl1.
    - exact Hmat1. }
  assert (SW3 : forall a, bv_unsigned sp - 15008 <= a < bv_unsigned sp - 64 -> writable_at rsegs m3 a).
  { intros a Ha. unfold writable_at. apply WM3. change (writable_at rsegs m2 a).
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 8256)) as [Hlo|Hhi].
    - apply (proj2 (CK2 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia))). apply (proj2 (CK1 a ltac:(lia) ltac:(lia))).
      apply HWS. lia.
    - apply HSCR1. unfold scratch_k. rewrite SP1. change ALLOC_STACK with 8192. left. lia. }
  assert (ERR3 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m3 a).
  { intros a Ha. unfold writable_at. apply WM3. change (writable_at rsegs m2 a). apply HSCR1. right. exact Ha. }
  assert (BK3 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m3 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hi. destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
    rewrite <- (BK2 a k i Hin Hi).
    assert (Hd : ~ (d <= a + i < d + n)) by (pose proof (BLD a k Hin); lia).
    assert (Hq : ~ (G_QUIT <= a + i < G_QUIT + 4)).
    { intros Hq. apply (sm_blk_img L A mem md a k i HMR Hin Hi). apply (sm_img_iv B _ SEGS). unfold G_QUIT in Hq. lia. }
    exact (proj1 (CK3 (a + i) ltac:(lia) ltac:(lia) Hd Hq)). }
  assert (F3 : forall a, KP a -> ~ scratch_k B SM_K regs a -> ~ (G_QUIT <= a < G_QUIT + 4) ->
             mbyte rsegs m3 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m3 a)).
  { intros a Ha Hs Hq. destruct (F2 a Ha Hs) as [E2 W2].
    unfold scratch_k in Hs. rewrite SMK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
    assert (Hs1 : ~ (bv_unsigned sp - 15008 <= a < bv_unsigned sp)) by tauto.
    assert (Hd : ~ (d <= a < d + n)).
    { intros Hd. destruct (proj1 Ha) as [Hh'|Hi]; [lia|]. apply (FR_img (a - d)); [lia|].
      replace (d + (a - d)) with a by ring. exact Hi. }
    destruct (CK3 a (KPR a Ha) ltac:(lia) Hd Hq) as [E3 W3]. split; [congruence | tauto]. }
  assert (REP3 : g_rec_rep rsegs L1 A1 m3 R O).
  { apply (rec_rep_frame rsegs G_REC REC_SC L A mem R O L1 A1 m3 REP).
    - intros a Ha.
      assert (Hg : in_globals frame_G a) by (apply sm_g_of; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
      destruct (GX a Hg) as (G1 & G2 & _).
      destruct (F3 a G1 G2 ltac:(unfold G_QUIT, G_REC, REC_SIZE, REC_SC, SC_SIZE in *; lia)) as [E W].
      split; [exact E | apply W].
    - intros p k i Hin Hi. exact (BK3 p k i (proj1 (OB _ Hin)) Hi).
    - intros pn Hin. exact (BM2 pn (proj1 (OB _ Hin))). }
  assert (PRE3 : call_pre_k B (aa_MR API) RCL_K L1 A1 R3 m3 md1).
  { unfold RCL_K, RCF_K. change ALLOC_STACK with 8192.
    split; [exact MR3|]. split; [exact HWF1|]. split; [exact HBD1|].
    split; [rewrite E3_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP3; replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP3; lia|]. split; [rewrite SP3; lia|].
    split; [intros a Ha; rewrite SP3 in Ha; rewrite SEGS; apply SW3; lia|].
    split; [rewrite E3_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; exact (ERR3 a Ha)|].
    intros HI. rewrite INIT in HI. discriminate. }
  assert (RES3 : res_ok_slots A1 (sb_malloc b (Z.max n 1))) by exact RES'.
    pose proof (RCLEAR L1 A1 R3 m3 md1 R O (sb_malloc b (Z.max n 1))) as RC. unfold REC_CLEAR in RC. rewrite SEGS in RC.
  eapply SR_bind; [exact (RC PRE3 RO3 REP3 RES3) |]. clear RC.
  intros c4 RET4.
  destruct RET4 as (L2 & A2 & R4 & m4 & md2 & O2 & Dr & -> & POST4 & REP4 & O2O & DrO & PERM & BLK4 & KEPT4 & UB4a & UB4b
    & GCL & RO4 & GK4 & INIT4 & RLEN4 & RES4).
  destruct POST4 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HPRES2 & HVM2 & HFRAME2 & HBLKS2 & HSCR2).
  try rewrite SEGS in HFRAME2. try rewrite SEGS in HBLKS2. try rewrite SEGS in HSCR2. try rewrite SEGS in RO4.
  try rewrite SEGS in GCL. try rewrite SEGS in REP4.
  unfold blocks_kept in KEPT4. try rewrite SEGS in KEPT4.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
  assert (NC : (length (r_calls R) <= 16)%nat) by exact (sm_rec_calls _ _ _ _ _ _ REP).
  assert (CK4 : forall a, KP a -> ~ (bv_unsigned sp - 8384 <= a < bv_unsigned sp - 64) ->
             ~ (errno_addr B <= a < errno_addr B + 4) -> ~ vr_writes a ->
             mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a)).
  { intros a Ha Hs He Hv.
    apply HFRAME2; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha MR3) | exact (KPN a _ _ _ _ Ha HMR2) | |].
    - unfold scratch_k. rewrite SP3. unfold RCL_K, RCF_K. change ALLOC_STACK with 8192.
      intros [H|H]; [apply Hs; lia | exact (He H)].
    - intros H. exact (Hv (sm_rcw_vr _ _ NC H)). }
  assert (F4 : forall a, KP a -> ~ scratch_k B SM_K regs a -> ~ vr_writes a ->
             mbyte rsegs m4 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m4 a)).
  { intros a Ha Hs Hv. assert (Hq : ~ (G_QUIT <= a < G_QUIT + 4)) by (intros Hq; apply Hv; right; right; exact Hq).
    destruct (F3 a Ha Hs Hq) as [E3 W3].
    unfold scratch_k in Hs. rewrite SMK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
    assert (Hs1 : ~ (bv_unsigned sp - 15008 <= a < bv_unsigned sp)) by tauto.
    assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
    destruct (CK4 a Ha ltac:(lia) Hs2 Hv) as [E4 W4]. split; [congruence | tauto]. }
  assert (BM4 : forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> In pn (blocks L2 A2)).
  { intros pn Hin Hno. pose proof (Permutation_in _ PERM (BM2 pn Hin)) as H. apply in_app_or in H as [H|H]; [exact H|].
    exfalso. apply Hno. apply in_map. exact (proj1 (proj1 (DrO pn) H)). }
  assert (BK4 : forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
             mbyte rsegs m4 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hno Hi. rewrite <- (BK3 a k i Hin Hi).
    apply (KEPT4 a k i (BM2 _ Hin)); [|exact Hi]. intros H. apply Hno.
    apply in_map_iff in H as ([a' k'] & Ea & H). cbn in Ea. subst a'.
    exact (in_map fst _ _ (proj1 (proj1 (DrO _) H))). }
  assert (FR4 := FR3).
  apply (rw_cells_transfer rsegs m3 m4) in FR4;
    [| intros i Hi; cbn in Hi; destruct (CK4 (bv_unsigned sp - 64 + i) (KPH (bv_unsigned sp - 64 + i) ltac:(lia)) ltac:(lia) ltac:(lia)
         ltac:(unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT; lia)) as [E W]; split; [exact E | apply W]].
  assert (SW4 : forall a, bv_unsigned sp - 15008 <= a < bv_unsigned sp - 64 -> writable_at rsegs m4 a).
  { intros a Ha. destruct (Z_lt_ge_dec a (bv_unsigned sp - 8384)) as [Hlo|Hhi].
    - apply (proj2 (CK4 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia)
        ltac:(unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT; lia))).
      apply SW3. lia.
    - apply HSCR2. unfold scratch_k. rewrite SP3. unfold RCL_K, RCF_K. change ALLOC_STACK with 8192. left. lia. }
  assert (ERR4 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m4 a)
    by (intros a Ha; apply HSCR2; right; exact Ha).
  assert (Q4 : rw_cells rsegs m4 0x343e8 [C4 (Z_to_bv 64 0)]).
  { apply (rw_cells_transfer rsegs m3); [exact GQ3|]. intros i Hi. cbn in Hi.
    assert (Hg : in_globals frame_G (0x343e8 + i)) by (apply sm_g_of; lia).
    assert (Hn : ~ rec_clear_writes (length (r_calls R)) (0x343e8 + i)).
    { unfold rec_clear_writes, nargs_field, G_REC, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY,
        OFF_REPLY_SIZE.
      intros [H|[(j & Hj & H)|[H|H]]]; lia. }
    destruct (GCL _ Hg Hn) as [E W]. split; [exact E | apply W]. }
  assert (INB2 : In (d, Z.max n 1) (blocks L2 A2)).
  { pose proof (Permutation_in _ PERM INB1) as H. apply in_app_or in H as [H|H]; [exact H|].
    exfalso. apply DOA. exact (in_map fst _ _ (proj1 (proj1 (DrO _) H))). }
  assert (NO2 : ~ In (d, Z.max n 1) O2) by (intros H; apply DOA; exact (in_map fst _ _ (O2O _ H))).
  assert (DAT4 : le_at B m4 d D).
  { apply (sm_le_of_bytes B m4 _ _ SEGS). apply (bytes_at_transfer rsegs m3); [exact BD3|]. intros i Hi.
    apply (KEPT4 d (Z.max n 1) i INB1); [|lia].
    intros H. apply DOA. apply in_map_iff in H as ([a' k'] & Ea & H). cbn in Ea. subst a'.
    exact (in_map fst _ _ (proj1 (proj1 (DrO _) H))). }
  assert (E4_2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by exact (eq_trans (HPRES2 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (E4_4 : getr R4 4 = getr regs 4) by exact (eq_trans (HPRES2 4 ltac:(unfold callee_saved; lia)) E3_4).
  assert (K4 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr Hx. rewrite (HPRES2 r Hr). exact (K3 r Hr Hx). }
    rewrite E3_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E4_2. apply sm_run3. rewrite USP1. lia. }
  intros ms5 (can5 & (a0r & -> & A0R) & EQ5).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  assert (E5_1 : getr R5 1 = Z_to_bv 64 0x144b0) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by (rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_4 : getr R5 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X5 eq_refl); simp_regs; exact E4_4).
  assert (E5_10 : getr R5 10 = Z_to_bv 64 (bv_unsigned sp - 56)).
  { rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs. rewrite A0R, USP1. f_equal. lia. }
  assert (K5' : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R5 (Z_to_bv 5 r) = getr R4 (Z_to_bv 5 r)) by sm_keep X5.
  assert (K5 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R5 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr Hx. rewrite (K5' r Hr Hx). exact (K4 r Hr Hx). }
  clear K5'.
  assert (SP5 : spZ R5 = bv_unsigned sp - 64) by (unfold spZ; rewrite E5_2; exact USP1).
  destruct (ax_statics AX L2 A2 m4 md2 HMR2) as (WG4 & (g4 & Hg4 & WGG4) & _).
  rewrite SEGS, GOT_AT, GUARD_AT in WG4. rewrite SEGS, GUARD_AT in WGG4.
  assert (LIV : length (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) iv_ptrs_b)) = 144%nat) by (vm_compute; reflexivity).
  assert (LIN : length info_bytes = 160%nat) by (vm_compute; reflexivity).
  assert (VT4 : vr_tables B m4 (Z_to_bv 64 g4)).
  { destruct VT as (V1 & V2 & V3 & V4). split; [|split; [|split]].
    - apply (sm_le_keep B mem); [exact V1|]. rewrite SEGS. intros i Hi. rewrite LIV in Hi.
      assert (Hr : in_globals frame_RELRO (IV_TABLE_B + i)) by (apply sm_relro_of; unfold IV_TABLE_B; lia).
      destruct (RLX _ Hr ltac:(rewrite GOT_AT; unfold IV_TABLE_B, SSP_GOT_B; lia)) as (G1 & G2 & G3).
      exact (proj1 (F4 _ G1 G2 G3)).
    - apply (sm_le_keep B mem); [exact V2|]. rewrite SEGS. intros i Hi. rewrite LIN in Hi.
      assert (Hr : in_globals frame_RELRO (INFO_TABLE + i)) by (apply sm_relro_of; unfold INFO_TABLE; lia).
      destruct (RLX _ Hr ltac:(rewrite GOT_AT; unfold INFO_TABLE, SSP_GOT_B; lia)) as (G1 & G2 & G3).
      exact (proj1 (F4 _ G1 G2 G3)).
    - apply (sm_le_of_bytes B m4 _ _ SEGS).
      apply (KindBGlue.word_mem_le8 rsegs m4 SSP_GOT_B SSP_GUARD_B WG4); unfold SSP_GUARD_B, SSP_GOT_B; lia.
    - apply (sm_le_of_bytes B m4 _ _ SEGS).
      apply (KindBGlue.word_mem_le8 rsegs m4 SSP_GUARD_B g4 WGG4); unfold SSP_GUARD_B; lia. }
  assert (SH4 : Mem.bytes_at rsegs m4 rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes).
  { apply (sm_bytes_of_image rsegs m4 448 _ _ rec_shape_of.g_shapes_image);
      [| unfold rec_shape_of_c.G_SHAPES; lia | unfold rec_shape_of_c.G_SHAPES; lia].
    intros i Hi. change (Z.of_nat 448) with 448 in Hi.
    assert (Hr : in_globals frame_RELRO (rec_shape_of_c.G_SHAPES + i))
      by (apply sm_relro_of; unfold rec_shape_of_c.G_SHAPES; lia).
    destruct (RLX _ Hr ltac:(rewrite GOT_AT; unfold rec_shape_of_c.G_SHAPES, SSP_GOT_B; lia)) as (G1 & G2 & G3).
    rewrite <- (GIM _ Hr). exact (proj1 (F4 _ G1 G2 G3)). }
  assert (MF0 : le_at B m4 (bv_unsigned sp - 56) (Mem.le4 (Z_to_bv 64 7))).
  { pose proof (sm_cell_get2 rsegs m4 _ [CB 8 k0] (C4 (Z_to_bv 64 7)) _ 8%nat FR4 eq_refl) as H.
    change (Z.of_nat 8) with 8 in H. replace (bv_unsigned sp - 64 + 8) with (bv_unsigned sp - 56) in H by lia.
    apply (sm_le_of_bytes B m4 _ _ SEGS). exact H. }
  assert (MF8 : le_at B m4 (bv_unsigned sp - 56 + 8) (Mem.le8 (Z_to_bv 64 d))).
  { pose proof (sm_cell_get2 rsegs m4 _ [CB 8 k0; C4 (Z_to_bv 64 7); CB 4 k1] (C8 (Z_to_bv 64 d)) _ 16%nat FR4 eq_refl)
      as H.
    change (Z.of_nat 16) with 16 in H. replace (bv_unsigned sp - 64 + 16) with (bv_unsigned sp - 56 + 8) in H by lia.
    apply (sm_le_of_bytes B m4 _ _ SEGS). exact H. }
  assert (MF16 : le_at B m4 (bv_unsigned sp - 56 + 16) (Mem.le8 (Z_to_bv 64 n))).
  { pose proof (sm_cell_get2 rsegs m4 _ [CB 8 k0; C4 (Z_to_bv 64 7); CB 4 k1; C8 (Z_to_bv 64 d)] (C8 (Z_to_bv 64 n)) _
      24%nat FR4 eq_refl) as H.
    change (Z.of_nat 24) with 24 in H. replace (bv_unsigned sp - 64 + 24) with (bv_unsigned sp - 56 + 16) in H by lia.
    apply (sm_le_of_bytes B m4 _ _ SEGS). exact H. }
  assert (PRE5 : call_pre_k B (aa_MR API) VR_K L2 A2 R5 m4 md2).
  { unfold VR_K.
    split; [exact HMR2|]. split; [exact HWF2|]. split; [exact HBD2|].
    split; [rewrite E5_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP5; replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP5; lia|]. split; [rewrite SP5; lia|].
    split; [intros a Ha; rewrite SP5 in Ha; rewrite SEGS; apply SW4; lia|].
    split; [rewrite E5_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; exact (ERR4 a Ha)|].
    intros HI. rewrite (INIT4 INIT) in HI. discriminate. }
    pose proof (VRECV L2 A2 R5 m4 md2 (RecKindB.rfree_b (sb_malloc b (Z.max n 1)) Dr) (rec_clear R) O2 (bv_unsigned sp - 56) 7 d n 0 D
      (Z_to_bv 64 g4)) as VR.
  unfold VERBS_RECEIVE in VR. rewrite SEGS in VR.
  eapply SR_bind.
  { apply VR; clear VR.
    - unfold call_pre_t. split; [exact PRE5 | rewrite SP5; lia].
    - exact RO4.
    - exact FRM.
    - exact E5_10.
    - apply sm_mod8. exact HAL.
    - lia.
    - lia.
    - change (bv_unsigned (getr R5 2)) with (spZ R5). rewrite SP5. lia.
    - exact ERRNO_IMG.
    - exact ERRNO_GUARD.
    - exact MF0.
    - exact MF8.
    - exact MF16.
    - intros i Hi. split.
      + intros Ho. pose proof (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho). lia.
      + unfold scratch_k. rewrite SP5. intros [H|H]; lia.
    - intros i Hi. unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT. lia.
    - exact INB2.
    - exact NO2.
    - exact DAT4.
    - exact LEN.
    - exact NMAX.
    - exact REP4.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact REFUSE.
    - apply (sm_le_of_bytes B m4 _ _ SEGS). destruct Q4 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb.
      rewrite app_nil_r in Hb. exact Hb.
    - intros i Hi. destruct Q4 as [_ (_ & _ & W)]. exact (W i ltac:(cbn; lia)).
    - intros i Hi. assert (Hg : in_globals frame_G (G_QUIT + i)) by (apply sm_g_of; unfold G_QUIT; lia).
      split; [exact (sm_gnown _ _ _ _ _ HMR2 Hg)|].
      unfold scratch_k. rewrite SP5. destruct (G_STAT _ Hg) as (_ & _ & _ & He).
      intros [H|H]; [unfold G_QUIT, VR_K in H; lia | exact (He H)].
    - exact VT4.
    - exact SH4.
    - exact RES4.
    - apply (RecKindB.room_slots_mono _ (sb_up b SM_PEAK SM_PEAKB) _ VR_REQ); [| unfold VR_REQ; lia | exact ROOM].
      assert (HD : forall pn, In pn Dr -> 0 <= snd pn).
      { intros pn Hp. apply (sm_blocks_nonneg L1 A1 pn HWF1).
        apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact Hp. }
      destruct (sm_rfree_le Dr (sb_malloc b (Z.max n 1)) HD) as (Q1 & Q2 & Q3).
      cbn [sb_live sb_bytes sb_cap sb_malloc] in Q1, Q2, Q3.
      unfold RecKindB.sb_le, sb_up, SM_PEAK, SM_PEAKB. cbn [sb_live sb_bytes sb_cap].
      change (2 ^ 19) with 524288. lia. }
  intros c6 RET6.
  destruct RET6 as (fx' & L3 & A3 & R6 & m5 & md3 & O3 & kv & -> & FPK & POST6 & RO5 & RUN6 & INB6 & DAT6 & DO3 & STAY6
    & NO6 & INIT6 & RLEN6 & MSG0 & MSG8 & MSG16 & BL6 & KEPT6 & VT6 & SH6 & RES6 & CAP6).
  destruct POST6 as (HMR3 & HWF3 & HBD3 & HLE3 & HSTAB3 & HPRES3 & HVM3 & HFRAME3 & HBLKS3 & HSCR3).
  try rewrite SEGS in HFRAME3. try rewrite SEGS in HBLKS3. try rewrite SEGS in HSCR3. try rewrite SEGS in RO5.
  unfold blocks_kept in KEPT6. try rewrite SEGS in KEPT6.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR3) as (Hh3 & Hl3 & Hmat3).
  destruct FPK as [FZ _].
  assert (CK5 : forall a, KP a -> ~ (bv_unsigned sp - 15008 <= a < bv_unsigned sp - 64) ->
             ~ (errno_addr B <= a < errno_addr B + 4) -> ~ vr_writes a ->
             mbyte rsegs m5 a = mbyte rsegs m4 a /\ (writable_at rsegs m4 a <-> writable_at rsegs m5 a)).
  { intros a Ha Hs He Hv.
    apply HFRAME3; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha HMR2) | exact (KPN a _ _ _ _ Ha HMR3) | | exact Hv].
    unfold scratch_k. rewrite SP5. unfold VR_K. intros [H|H]; [apply Hs; lia | exact (He H)]. }
  assert (F5 : forall a, KP a -> ~ scratch_k B SM_K regs a -> ~ vr_writes a ->
             mbyte rsegs m5 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m5 a)).
  { intros a Ha Hs Hv. destruct (F4 a Ha Hs Hv) as [E4 W4].
    unfold scratch_k in Hs. rewrite SMK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
    assert (Hs1 : ~ (bv_unsigned sp - 15008 <= a < bv_unsigned sp)) by tauto.
    assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
    destruct (CK5 a Ha ltac:(lia) Hs2 Hv) as [E5 W5]. split; [congruence | tauto]. }
  assert (BM5 : forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> In pn (blocks L3 A3)).
  { intros pn Hin Hno. apply STAY6; [exact (BM4 pn Hin Hno)|]. intros H. apply Hno. exact (in_map fst _ _ (O2O _ H)). }
  assert (BK5 : forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
             mbyte rsegs m5 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hno Hi. rewrite <- (BK4 a k i Hin Hno Hi).
    apply (KEPT6 a k i (BM4 _ Hin Hno)); [|exact Hi]. intros (k' & H). apply Hno.
    exact (in_map fst _ _ (O2O _ H)). }
  assert (FR5 := FR4).
  apply (rw_cells_transfer rsegs m4 m5) in FR5;
    [| intros i Hi; cbn in Hi; destruct (CK5 (bv_unsigned sp - 64 + i) (KPH (bv_unsigned sp - 64 + i) ltac:(lia))
         ltac:(lia) ltac:(lia) ltac:(unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT; lia)) as [E W];
       split; [exact E | apply W]].
  assert (E6_2 : reg_get R6 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by exact (eq_trans (HPRES3 2 ltac:(unfold callee_saved; lia)) E5_2).
  assert (E6_4 : getr R6 4 = getr regs 4) by exact (eq_trans (HPRES3 4 ltac:(unfold callee_saved; lia)) E5_4).
  assert (K6 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R6 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr Hx. rewrite (HPRES3 r Hr). exact (K5 r Hr Hx). }
    rewrite E5_1.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E6_2. eapply sm_run4 with (d := Z_to_bv 64 d).
    rewrite USP1. apply (sm_bytes_of_le B m5 _ _ SEGS); [lia | rewrite Mem.length_le8; lia |].
    replace (bv_unsigned sp - 64 + 16) with (bv_unsigned sp - 56 + 8) by lia. exact MSG8. }
  intros ms7 (can7 & (a0f & -> & A0F) & EQ7).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ7 eq_refl eq_refl) as (R7 & -> & X7).
  assert (E7_1 : getr R7 1 = Z_to_bv 64 0x144b8) by (rewrite (getr_of_eqv _ _ 1 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_2 : getr R7 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by (rewrite (getr_of_eqv _ _ 2 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_4 : getr R7 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X7 eq_refl); simp_regs; exact E6_4).
  assert (E7_10 : getr R7 10 = Z_to_bv 64 d) by (rewrite (getr_of_eqv _ _ 10 X7 eq_refl); simp_regs; exact A0F).
  assert (K7' : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R7 (Z_to_bv 5 r) = getr R6 (Z_to_bv 5 r)) by sm_keep X7.
  assert (K7 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R7 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr Hx. rewrite (K7' r Hr Hx). exact (K6 r Hr Hx). }
  clear K7'.
  assert (SP7 : spZ R7 = bv_unsigned sp - 64) by (unfold spZ; rewrite E7_2; exact USP1).
  destruct (proj1 (YI06.blocks_In L3 A3 d (Z.max n 1)) INB6) as (pd & PD & UPD).
  assert (PRE7 : call_pre B (aa_MR API) L3 A3 R7 m5 md3).
  { split; [exact HMR3|]. split; [exact HWF3|]. split; [exact HBD3|].
    split; [rewrite E7_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP7; replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP7; change ALLOC_STACK with 8192; lia|]. split; [rewrite SP7; lia|].
    split; [intros a Ha; rewrite SP7 in Ha; change ALLOC_STACK with 8192 in Ha; rewrite SEGS; apply HSCR3;
            unfold scratch_k; rewrite SP5; unfold VR_K; left; lia|].
    split; [rewrite E7_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; apply HSCR3; right; exact Ha|].
    intros HI. rewrite (YI04.init_done_of_block A3 (pd, Z.max n 1) HWF3 UPD) in HI. discriminate. }
    pose proof (FREE fx' L3 A3 R7 m5 md3 pd (Z.max n 1) kv) as FRE.
  rewrite SEGS, FREE_PC in FRE.
  eapply SR_bind; [exact (FRE PRE7 RO5 UPD ltac:(rewrite E7_10, PD; reflexivity) RES6) |]. clear FRE.
  intros c8 RET8.
  destruct RET8 as (L4 & A4 & R8 & m6 & md4 & -> & POST8 & BLK8 & KEPT8 & RO6 & GK8 & UB8 & INIT8 & RLEN8 & RES8).
  destruct POST8 as (HMR4 & HWF4 & HBD4 & HLE4 & HSTAB4 & HPRES4 & HVM4 & HFRAME4 & HBLKS4 & HSCR4).
  try rewrite SEGS in HFRAME4. try rewrite SEGS in HBLKS4. try rewrite SEGS in HSCR4. try rewrite SEGS in RO6.
  unfold blocks_kept in KEPT8. try rewrite SEGS in KEPT8.
  rewrite PD in BLK8, KEPT8, HFRAME4.
  destruct BLK8 as (c1 & c2 & BLK8a & BLK8b).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR4) as (Hh4 & Hl4 & Hmat4).
  assert (CK6 : forall a, KP a -> ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp - 64) ->
             ~ (errno_addr B <= a < errno_addr B + 4) -> ~ (d <= a < d + Z.max n 1) ->
             mbyte rsegs m6 a = mbyte rsegs m5 a /\ (writable_at rsegs m5 a <-> writable_at rsegs m6 a)).
  { intros a Ha Hs He Hd.
    apply HFRAME4; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha HMR3) | exact (KPN a _ _ _ _ Ha HMR4) | | exact Hd].
    unfold scratch. rewrite SP7. change ALLOC_STACK with 8192. intros [H|H]; [apply Hs; lia | exact (He H)]. }
  assert (F6 : forall a, KP a -> ~ scratch_k B SM_K regs a -> ~ vr_writes a ->
             mbyte rsegs m6 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m6 a)).
  { intros a Ha Hs Hv. destruct (F5 a Ha Hs Hv) as [E5 W5].
    unfold scratch_k in Hs. rewrite SMK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
    assert (Hs1 : ~ (bv_unsigned sp - 15008 <= a < bv_unsigned sp)) by tauto.
    assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
    assert (Hd : ~ (d <= a < d + Z.max n 1)).
    { intros Hd. destruct (proj1 Ha) as [Hh'|Hi]; [lia|]. apply (FR_img (a - d)); [lia|].
      replace (d + (a - d)) with a by ring. exact Hi. }
    destruct (CK6 a Ha ltac:(lia) Hs2 Hd) as [E6 W6]. split; [congruence | tauto]. }
  assert (PW3 : pairwise ranges_disjoint (blocks L3 A3)) by exact (mr_blocks_disjoint B _ LAWS _ _ _ _ HMR3).
  assert (DM3 : ~ In (d, Z.max n 1) (c1 ++ c2)) by (apply (sm_pw_mid c1 _ c2); [rewrite <- BLK8a; exact PW3 | cbn; lia]).
  assert (BM6 : forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> In pn (blocks L4 A4)).
  { intros pn Hin Hno. rewrite BLK8b. pose proof (BM5 pn Hin Hno) as H. rewrite BLK8a in H.
    apply in_app_or in H as [H|[H|H]]; [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
    subst pn. exfalso. exact (DNEW Hin). }
  assert (BK6 : forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
             mbyte rsegs m6 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hno Hi. rewrite <- (BK5 a k i Hin Hno Hi).
    apply (KEPT8 a k i (BM5 _ Hin Hno)); [|exact Hi]. intros ->.
    pose proof (BLD d k Hin). lia. }
  assert (FR6 := FR5).
  apply (rw_cells_transfer rsegs m5 m6) in FR6;
    [| intros i Hi; cbn in Hi; destruct (CK6 (bv_unsigned sp - 64 + i) (KPH (bv_unsigned sp - 64 + i) ltac:(lia))
         ltac:(lia) ltac:(lia) ltac:(lia)) as [E W]; split; [exact E | apply W]].
  assert (E8_2 : reg_get R8 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by exact (eq_trans (HPRES4 2 ltac:(unfold callee_saved; lia)) E7_2).
  assert (K8 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ r = 18) ->
             getr R8 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr Hx. rewrite (HPRES4 r Hr). exact (K7 r Hr Hx). }
    rewrite E7_1.
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E8_2.
    eapply sm_run5 with (rao := reg_get regs 1) (s0o := reg_get regs 8) (s1o := reg_get regs 9)
      (s2o := reg_get regs 18); rewrite USP1.
    - pose proof (sm_cell_get2 rsegs m6 _ [CB 8 k0; C4 (Z_to_bv 64 7); CB 4 k1; C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n)]
        (C8 (reg_get regs 18)) _ 32%nat FR6 eq_refl) as H. change (Z.of_nat 32) with 32 in H. exact H.
    - pose proof (sm_cell_get2 rsegs m6 _ [CB 8 k0; C4 (Z_to_bv 64 7); CB 4 k1; C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n);
        C8 (reg_get regs 18)] (C8 (reg_get regs 9)) _ 40%nat FR6 eq_refl) as H. change (Z.of_nat 40) with 40 in H.
      exact H.
    - pose proof (sm_cell_get2 rsegs m6 _ [CB 8 k0; C4 (Z_to_bv 64 7); CB 4 k1; C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n);
        C8 (reg_get regs 18); C8 (reg_get regs 9)] (C8 (reg_get regs 8)) _ 48%nat FR6 eq_refl) as H.
      change (Z.of_nat 48) with 48 in H. exact H.
    - pose proof (sm_cell_get2 rsegs m6 _ [CB 8 k0; C4 (Z_to_bv 64 7); CB 4 k1; C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n);
        C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8)] (C8 (reg_get regs 1)) _ 56%nat FR6 eq_refl)
        as H. change (Z.of_nat 56) with 56 in H. exact H.
    - lia. }
  intros ms9 (can9 & -> & EQ9).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ9 eq_refl eq_refl) as (R9 & -> & X9).
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  assert (FG6 : forall a, in_globals frame_G a ->
             mbyte rsegs m6 a = mbyte rsegs m5 a /\ (writable_at rsegs m5 a <-> writable_at rsegs m6 a)).
  { intros a Hg. pose proof (sm_g_iv a Hg) as Hr. destruct (GX a Hg) as (G1 & _ & G3).
    apply (CK6 a G1); [lia | exact G3 | lia]. }
  destruct (ax_statics AX L4 A4 m6 md4 HMR4) as (WG6 & (g6 & Hg6 & WGG6) & _).
  rewrite SEGS, GOT_AT, GUARD_AT in WG6. rewrite SEGS, GUARD_AT in WGG6.
  apply SR_ret.
  exists fx', L4, A4, R9, m6, md4, O3, (sb_free kv (Z.max n 1)).
  split; [rewrite RP; reflexivity|].
  split; [exact FZ|].
  split; [lia|].
  split.
  { unfold call_post_ko. rewrite ?SEGS.
    split; [exact HMR4|]. split; [exact HWF4|]. split; [exact HBD4|].
    assert (LLE : layout_le A L L4).
    { apply (sm_lle_trans A A3 L L3 L4); [| exact HLE4 | lia].
      apply (sm_lle_trans A A2 L L2 L3); [| exact HLE3 | lia].
      apply (sm_lle_trans A A1 L L1 L2); [exact HLE1 | exact HLE2 | lia]. }
    split; [exact LLE|].
    split; [intros p k Hp _; exact (sm_ptr_stable A L L4 p k HWF Hp LLE)|].
    split.
    { intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [C|C].
      { subst r. rewrite (getr_of_eqv _ _ _ X9) by reflexivity. simp_regs. rewrite USP1.
        replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity. }
      repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X9) by reflexivity;
        first [reflexivity | exact (K8 _ Hr ltac:(lia))]|]).
      subst r; rewrite (getr_of_eqv _ _ _ X9) by reflexivity; first [reflexivity | exact (K8 _ Hr ltac:(lia))]. }
    split.
    { destruct HVM1 as [vm1 ->]. destruct HVM2 as [vm2 ->]. destruct HVM3 as [vm3 ->]. destruct HVM4 as [vm4 ->].
      exists vm4. rewrite !sm_wv. reflexivity. }
    split.
    { intros a Ha Ho Ho' Hs Hv. exact (F6 a (conj Ha Ho) Hs Hv). }
    split.
    { intros p k i Hp _ Hno Hi. apply (BK6 (ptr_addr L p) k i); [| exact Hno | exact Hi].
      unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hp). }
    intros a Hs. unfold scratch_k in Hs. rewrite SMK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
    destruct Hs as [Hs|He]; [|apply HSCR4; right; exact He].
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 64)) as [Hlo|Hhi].
    - destruct (Z_lt_ge_dec a (bv_unsigned sp - 8256)) as [Hl8|Hh8].
      + apply (proj2 (CK6 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia))).
        apply HSCR3. unfold scratch_k. rewrite SP5. unfold VR_K. left. lia.
      + apply HSCR4. unfold scratch. rewrite SP7. change ALLOC_STACK with 8192. left. lia.
    - destruct FR6 as [_ (_ & _ & W)]. pose proof (W (a - (bv_unsigned sp - 64)) ltac:(cbn; lia)) as Wa.
      unfold writable_at. replace a with (bv_unsigned sp - 64 + (a - (bv_unsigned sp - 64))) by ring. exact Wa. }
  split.
  { unfold cmd_mem. rewrite ?SEGS.
    split; [exact RO6|].
    split.
    { unfold G_img_c. cbv zeta. intros a Ha. rewrite ?SEGS.
      destruct (Z_lt_ge_dec a SSP_GOT_B) as [H1|H1]; [|destruct (Z_lt_ge_dec a (SSP_GOT_B + 8)) as [H2|H2]].
      - destruct (RLX a Ha ltac:(rewrite GOT_AT; lia)) as (G1 & G2 & G3). rewrite <- (GIM a Ha).
        exact (proj1 (F6 a G1 G2 G3)).
      - exact (sm_got_rom m6 a WG6 ltac:(lia)).
      - destruct (RLX a Ha ltac:(rewrite GOT_AT; lia)) as (G1 & G2 & G3). rewrite <- (GIM a Ha).
        exact (proj1 (F6 a G1 G2 G3)). }
    split; [exists (Z_to_bv 64 g6); apply (sm_le_of_bytes B m6 _ _ SEGS);
            apply (KindBGlue.word_mem_le8 rsegs m6 SSP_GUARD_B g6 WGG6); unfold SSP_GUARD_B; lia|].
    intros i Hi. exact (sm_guard_wr m6 i Hi). }
  split.
  { revert RUN6. destruct (vr_run (rec_clear R) D) as [[R' x] quit]. intros [REPV QV].
    split.
    - apply (rec_rep_frame rsegs G_REC REC_SC L3 A3 m5 R' O3 L4 A4 m6 REPV).
      + intros a Ha.
        assert (Hg : in_globals frame_G a) by (apply sm_g_of; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
        destruct (FG6 a Hg) as [E W]. split; [exact E | apply W].
      + intros p k i Hin Hi. destruct (sm_rec_O _ _ _ _ _ _ _ REPV Hin) as [Hb Hk]. cbn [snd] in Hk.
        apply (KEPT8 p k i Hb); [|exact Hi].
        intros Hp. cbv beta in Hp. subst p. apply DO3.
        rewrite <- (sm_pw_same _ d k (Z.max n 1) PW3 Hb INB6 Hk MN1). exact Hin.
      + intros pn Hin. destruct (sm_rec_O _ _ _ _ _ _ _ REPV Hin) as [Hb _]. rewrite BLK8b. rewrite BLK8a in Hb.
        apply in_app_or in Hb as [Hb|[Hb|Hb]]; [apply in_or_app; left; exact Hb | | apply in_or_app; right; exact Hb].
        subst pn. exfalso. exact (DO3 Hin).
    - apply (sm_le_keep B m5); [exact QV|]. rewrite SEGS. intros i Hi. rewrite LE4 in Hi.
      exact (proj1 (FG6 (G_QUIT + i) (sm_g_of (G_QUIT + i) ltac:(unfold G_QUIT; lia)))). }
  split.
  { destruct (Z.eq_dec n 0) as [Z0|Z0].
    - destruct D as [|x D']; [|cbn [length] in LEN; lia].
      unfold le_at, blk_data. cbv zeta. intros i Hi. cbn in Hi. lia.
    - destruct (SRCP Z0) as (S1 & S2 & (p & k & Hpk & Hpo & Hp1 & Hp2) & _).
      apply (sm_le_keep B mem); [exact SRCD|]. rewrite SEGS. intros i Hi.
      replace (src + i) with (p + (src + i - p)) by ring. apply (BK6 p k); [exact Hpk | exact Hpo | lia]. }
  split.
  { intros pn Hin. rewrite BLK8b in Hin.
    assert (H3 : In pn (blocks L3 A3)).
    { rewrite BLK8a. apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
    destruct (BL6 pn H3) as [[H2 HnO2]|HO3]; [|right; exact HO3].
    left.
    assert (H1 : In pn (blocks L1 A1)).
    { apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. left. exact H2. }
    rewrite BLK1 in H1. split.
    - rewrite BLK2. apply in_app_or in H1 as [H|[H|H]]; [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
      subst pn. exfalso. exact (DM3 Hin).
    - intros HO. assert (HD : In pn Dr) by (apply DrO; split; [exact HO | exact HnO2]).
      exact (sm_pw_dup _ _ _ pn PW1 PERM H2 HD (proj2 (OB pn HO))). }
  split; [exact BM6|].
  split.
  { intros pn Hin Hno HO3. apply (NO6 pn (BM4 pn Hin Hno)); [|exact HO3].
    intros H. apply Hno. exact (in_map fst _ _ (O2O _ H)). }
  split.
  { unfold blocks_kept. rewrite SEGS. intros a k i Hin Hno Hi. apply (BK6 a k i Hin); [|exact Hi].
    intros H. apply Hno. apply in_map_iff in H as ([a' k'] & Ea & H). cbn in Ea. subst a'. unfold owned_by.
    exists k'. exact H. }
  split; [intros _; exact (INIT8 (YI04.init_done_of_block A3 (pd, Z.max n 1) HWF3 UPD))|].
  split.
  { exists (Z_to_bv 64 g6). destruct VT as (V1 & V2 & V3 & V4). split; [|split; [|split]].
    - apply (sm_le_keep B mem); [exact V1|]. rewrite SEGS. intros i Hi. rewrite LIV in Hi.
      assert (Hr : in_globals frame_RELRO (IV_TABLE_B + i)) by (apply sm_relro_of; unfold IV_TABLE_B; lia).
      destruct (RLX _ Hr ltac:(rewrite GOT_AT; unfold IV_TABLE_B, SSP_GOT_B; lia)) as (G1 & G2 & G3).
      exact (proj1 (F6 _ G1 G2 G3)).
    - apply (sm_le_keep B mem); [exact V2|]. rewrite SEGS. intros i Hi. rewrite LIN in Hi.
      assert (Hr : in_globals frame_RELRO (INFO_TABLE + i)) by (apply sm_relro_of; unfold INFO_TABLE; lia).
      destruct (RLX _ Hr ltac:(rewrite GOT_AT; unfold INFO_TABLE, SSP_GOT_B; lia)) as (G1 & G2 & G3).
      exact (proj1 (F6 _ G1 G2 G3)).
    - apply (sm_le_of_bytes B m6 _ _ SEGS).
      apply (KindBGlue.word_mem_le8 rsegs m6 SSP_GOT_B SSP_GUARD_B WG6); unfold SSP_GUARD_B, SSP_GOT_B; lia.
    - apply (sm_le_of_bytes B m6 _ _ SEGS).
      apply (KindBGlue.word_mem_le8 rsegs m6 SSP_GUARD_B g6 WGG6); unfold SSP_GUARD_B; lia. }
  split; [exact RES8|].
  cbn [sb_free sb_cap]. rewrite CAP6, sm_rfree_cap. cbn [sb_malloc sb_cap]. reflexivity.
Qed.

End Send.

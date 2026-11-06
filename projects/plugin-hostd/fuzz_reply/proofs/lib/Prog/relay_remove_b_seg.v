(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its addresses and numbers changed; 295 of its 362 lines of code are new or changed and 1162 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c
  memcpy_c memcpy_same_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rm_cells_cut : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma rm_cells_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Lemma rm_lts0 : forall x : word, bv_lts x (Z_to_bv 64 0) = (bv_signed x <? 0).
Proof. intros x. unfold bv_lts. change (bv_signed (Z_to_bv 64 0)) with 0. reflexivity. Qed.

Lemma rm_bytes_pre : forall m A (s t : list byte), bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A s.
Proof. intros m A s t H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma rm_neg : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_signed a0 < 0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a58) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HN.
  step.
  rewrite rm_lts0, (proj2 (Z.ltb_lt _ _) HN). cbv iota.
  step. apply evt_done. reflexivity.
Qed.

Lemma rm_seg1 : pthread_mutex_lock_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 200740 <= lo ->
  0 <= bv_signed a0 ->
  rw_cells rsegs m 200728 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j,
      ms' = MS (mkR (Z_to_bv 64 0x13a8c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 200728) a0
                    (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 200640) s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3' t4' t5' t6')
               F (Z_to_bv 64 0x13a8c) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp + -48, bv_unsigned sp); (200732, 200736)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp + -48) /\
      rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      rw_cells rsegs m' 200728 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a58) fc None m (seg_rom rsegs)).
Proof.
  intros SPL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LOL HP GL MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct (rm_cells_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (rm_cells_cut _ _ [_] [_] GL12) as [GL1 GL2]. clear GL12.
  assert (TB : bytes_at rsegs m 200728 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 GL0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B. exact (rm_bytes_pre _ _ _ _ B). }
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (200732, 200736)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  step.
  rewrite rm_lts0, (proj2 (Z.ltb_ge _ _) HP). cbv iota.
  do 12 step.
  call (SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            200728 (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0)))).
  1: reflexivity.
  1: exact TB.
  1: reflexivity.
  1: exact GL1.
  1: assumption.
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact ST|]. split; [exact FR|].
  apply (rm_cells_join _ _ (200728 + 4) [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] GL0);
    [apply (rm_cells_join _ _ _ [C4 (Z_to_bv 64 16)] [C4 (Z_to_bv 64 0)] POST GL2) |]; cbn; lia.
Qed.

Lemma rm_lts0l : forall z, 0 <= z < 2 ^ 63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 z) = (0 <? z).
Proof.
  intros z Hz. unfold bv_lts. change (bv_signed (Z_to_bv 64 0)) with 0.
  rewrite YK11.bv_signed_small by (rewrite unsigned_lit; lia). rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma rm_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rm_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Definition rm_disp (sp gp tp s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FD G N : Z) (fdk eofk : nat -> Z) (m : word -> option byte) (ms' : machine_state) : Prop :=
  exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6,
    ((forall k, (k < Z.to_nat N)%nat -> fdk k <> FD) /\
     ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FD) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                   t3 t4 t5 t6) F (Z_to_bv 64 0x13b14) fc None m (seg_rom rsegs)) \/
    (exists i, (i < Z.to_nat N)%nat /\ fdk i = FD /\ (forall k, (k < i)%nat -> fdk k <> FD) /\
      ((eofk i = 0 /\
        ms' = MS (mkR (Z_to_bv 64 0x13acc) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FD) (Z_to_bv 64 (G + 56 * Z.of_nat i))
                      a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (56 * Z.of_nat i)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x135d0) fc None m (seg_rom rsegs)) \/
       (eofk i <> 0 /\
        ms' = MS (mkR (Z_to_bv 64 0x13ad8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FD) (Z_to_bv 64 (G + 56 * Z.of_nat i))
                      a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (56 * Z.of_nat i)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x130ec) fc None m (seg_rom rsegs)))).

Definition rm_reads (m : word -> option byte) (G N : Z) (fdk eofk : nat -> Z) : Prop :=
  forall k, (k < Z.to_nat N)%nat ->
    0 <= fdk k < 2 ^ 31 /\ 0 <= eofk k < 2 ^ 31 /\
    ov_read_bytes rsegs m (Z_to_bv 64 (G + 56 * Z.of_nat k)) 4 = Some (le4 (Z_to_bv 64 (fdk k))) /\
    ov_read_bytes rsegs m (Z_to_bv 64 (G + 56 * Z.of_nat k + 4)) 4 = Some (le4 (Z_to_bv 64 (eofk k))).

Lemma rm_loop : forall x1 sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (FD G N : Z) (fdk eofk : nat -> Z),
  0 <= G -> G + 1000 < 2 ^ 64 -> 0 <= FD < 2 ^ 31 -> 0 < N <= 4 -> rm_reads m G N fdk eofk ->
  forall d k a0 a3, (Z.to_nat N - k = d)%nat -> (k < Z.to_nat N)%nat -> (forall k', (k' < k)%nat -> fdk k' <> FD) ->
  evt rsegs (rm_disp sp gp tp s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc FD G N fdk eofk m)
    (MS (mkR x1 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FD) a0 (Z_to_bv 64 G) (Z_to_bv 64 (56 * N)) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (56 * Z.of_nat k)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13aa8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m FD G N fdk eofk
    G0 GB HFD HN RD d.
  induction d as [|d IH]; intros k a0 a3 Hd Hk Hbefore; [lia|].
  destruct (RD k Hk) as (Hf & He & R0 & R1).
  step. step.
  rewrite (rm_sx32 (fdk k)) by lia.
  step.
  rewrite (rm_eqb (fdk k) FD) by lia.
  destruct (Z.eqb_spec (fdk k) FD) as [EQ|NE]; cbv iota.
  - step. rewrite (rm_sx32 (eofk k)) by lia.
    step.
    rewrite (rm_eqb (eofk k) 0) by lia.
    destruct (Z.eqb_spec (eofk k) 0) as [E0|E1]; cbv [negb]; cbv iota.
    + step. apply evt_done. unfold rm_disp. do 17 eexists. right. exists k.
      split; [exact Hk|]. split; [exact EQ|]. split; [exact Hbefore|]. left. split; [exact E0 | reflexivity].
    + step. step. apply evt_done. unfold rm_disp. do 17 eexists. right. exists k.
      split; [exact Hk|]. split; [exact EQ|]. split; [exact Hbefore|]. right. split; [exact E1 | reflexivity].
  - step. step.
    rewrite (rm_eqb (56 * N) (56 * Z.of_nat k + 56)) by lia.
    destruct (Z.eqb_spec (56 * N) (56 * Z.of_nat k + 56)) as [EN|NN]; cbv iota.
    + apply evt_done. unfold rm_disp. do 17 eexists. left. split; [|reflexivity].
      intros k' Hk'. destruct (Nat.lt_ge_cases k' k) as [L|L]; [exact (Hbefore k' L)|].
      assert (k' = k) by lia. subst k'. exact NE.
    + step.
      replace (56 * Z.of_nat k + 56) with (56 * Z.of_nat (S k)) by lia.
      apply IH; [lia | lia |].
      intros k' Hk'. destruct (Nat.lt_ge_cases k' k) as [L|L]; [exact (Hbefore k' L)|].
      assert (k' = k) by lia. subst k'. exact NE.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma rm_seg2 : forall x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (FD G N : Z) (fdk eofk : nat -> Z),
  0 <= G -> G + 1000 < 2 ^ 64 -> 0 <= FD < 2 ^ 31 -> 0 <= N <= 4 -> rm_reads m G N fdk eofk ->
  ov_read_bytes rsegs m (Z_to_bv 64 200664) 4 = Some (le4 (Z_to_bv 64 N)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 200688) 8 = Some (le8 (Z_to_bv 64 G)) ->
  evt rsegs (rm_disp sp gp tp (Z_to_bv 64 200728) (Z_to_bv 64 200640) s4 s5 s6 s7 s8 s9 s10 s11 F fc FD G N fdk eofk m)
    (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 200728) (Z_to_bv 64 FD) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 200640) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a8c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m FD G N fdk eofk
    G0 GB HFD HN RD RN RG.
  step.
  rewrite (rm_sx32 N) by lia.
  step.
  rewrite (rm_lts0l N) by lia.
  destruct (Z.ltb_spec 0 N) as [NP|NZ]; cbv [negb]; cbv iota.
  - do 5 step.
    lazymatch goal with |- context [Z_to_bv 64 (?a - ?b)] =>
      replace (Z_to_bv 64 (a - b)) with (Z_to_bv 64 (56 * N))
        by (f_equal; rewrite (unsigned_lit N) by lia; rewrite !Z.shiftl_mul_pow2 by lia;
            rewrite !unsigned_lit by lia; lia)
    end.
    eapply (rm_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m FD G N fdk eofk G0 GB HFD
              ltac:(lia) RD (Z.to_nat N - 0) 0); [lia | lia | intros; lia].
  - apply evt_done. unfold rm_disp. do 17 eexists. left. split; [|reflexivity].
    intros k Hk. lia.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma rm_end : pthread_mutex_unlock_contract ->
  forall x1 sp1 gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (j : list byte) (w1 w8 w9 w18 w19 : word),
  rw_cells rsegs m (bv_unsigned sp1) [CB 8 j; C8 w19; C8 w18; C8 w9; C8 w8; C8 w1] ->
  rw_cells rsegs m 200728 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m 134468 (le4 (Z_to_bv 64 (-1))) ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 96 <= bv_unsigned sp1 -> 200740 <= lo -> bv_unsigned sp1 + 48 < 2 ^ 64 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp1 + 48)) gp tp t0' t1' t2' w8 w9 a0' a1' a2' a3' a4' a5' a6' a7'
                    w18 w19 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc w1) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp1 - 96, bv_unsigned sp1 + 48); (200732, 200736)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp1 + 48) /\
      rw_cells rsegs m' 200728 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR x1 sp1 gp tp t0 t1 t2 (Z_to_bv 64 200728) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b14) fc None m (seg_rom rsegs)).
Proof.
  intros SPU x1 sp1 gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo j w1 w8 w9 w18 w19 FR GL WK ST LO LOL SPB MI.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp1 - 96, bv_unsigned sp1 + 48); (200732, 200736)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  call (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 200728 lo).
  1: reflexivity.
  1: exact GL.
  1: exact ST.
  1: lia.
  1: lia.
  1: exact MI.
  cbv delta [mkR].
  match goal with H : bytes_at rsegs ?mm 134468 _ |- _ =>
    assert (HR : ov_read_bytes rsegs mm (wa (134468 + 0)) 4 = Some (le4 (Z_to_bv 64 (-1))))
      by (rewrite (bytes_at_read rsegs mm 134468 _ 0 4 H ltac:(lia)) by (rewrite length_le4; lia); reflexivity)
  end.
  step. step. step.
  change (le1 (Z_to_bv 64 0)) with (le1 (zxb (Z_to_bv 8 0))).
  mem_after_store.
  step. if_true.
  do 7 step.
  match goal with S : stk _ _ lo (bv_unsigned sp1) |- _ => release_frame FR S (bv_unsigned sp1 + 48) end.
  apply evt_done. do 16 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma rm_segd : forall x1 sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (G : Z) (i : nat),
  0 <= G -> G + 1000 < 2 ^ 64 -> (i < 4)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 200688) 8 = Some (le8 (Z_to_bv 64 G)) ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13ad8) sp1 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (G + 56 * Z.of_nat i))
                                      (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 200640) (Z_to_bv 64 (56 * Z.of_nat i))
                                      s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x130ec) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 200640) (Z_to_bv 64 (56 * Z.of_nat i))
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13acc) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m G i
    G0 GB HI RG.
  step. step. step. apply evt_done. reflexivity.
Qed.

Lemma rm_segg : forall x1 sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (G B : Z) (i : nat),
  0 <= G -> G + 1000 < 2 ^ 64 -> (i < 4)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 200688) 8 = Some (le8 (Z_to_bv 64 G)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (G + 56 * Z.of_nat i + 16)) 8 = Some (le8 (Z_to_bv 64 B)) ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13ae8) sp1 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B)
                                      a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 200640) (Z_to_bv 64 (56 * Z.of_nat i))
                                      s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x15664) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 200640) (Z_to_bv 64 (56 * Z.of_nat i))
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ad8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m G B i
    G0 GB HI RG RB.
  step. step. step. step. apply evt_done. reflexivity.
Qed.

Lemma rm_segf : memcpy_contract -> memcpy_same_contract ->
  forall x1 sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (G N : Z) (i : nat) (src dj : list byte),
  0 <= G -> G + 1000 < 2 ^ 64 -> (G + 896 <= 200640 \/ 200768 <= G) -> 1 <= N <= 4 -> Z.of_nat i < N ->
  rw_cells rsegs m 200664 [C4 (Z_to_bv 64 N)] ->
  ov_read_bytes rsegs m (Z_to_bv 64 200688) 8 = Some (le8 (Z_to_bv 64 G)) ->
  length src = 56%nat ->
  ((Z.of_nat i < N - 1 /\ bytes_at rsegs m (G + 56 * (N - 1)) src /\
    rw_cells rsegs m (G + 56 * Z.of_nat i) [CB 56 dj]) \/
   (Z.of_nat i = N - 1 /\ rw_cells rsegs m (G + 56 * Z.of_nat i) [CB 56 src])) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR (Z_to_bv 64 0x13b14) sp1 gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (G + 56 * Z.of_nat i))
                    a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 200640) (Z_to_bv 64 (56 * Z.of_nat i))
                    s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13b14) fc None m' (seg_rom rsegs) /\
      munch [(G + 56 * Z.of_nat i, G + 56 * Z.of_nat i + 56); (200664, 200668)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\
      rw_cells rsegs m' 200664 [C4 (Z_to_bv 64 (N - 1))] /\
      rw_cells rsegs m' (G + 56 * Z.of_nat i) [CB 56 src] /\ bytes_at rsegs m' (G + 56 * (N - 1)) src)
    (MS (mkR x1 sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 200640) (Z_to_bv 64 (56 * Z.of_nat i))
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ae8) fc None m (seg_rom rsegs)).
Proof.
  intros MCP MCS x1 sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    G N i src dj G0 GB GD HN HI CN RG LS HC MI.
  assert (US : bv_unsigned (Z_to_bv 64 (G + 56 * (N - 1))) = G + 56 * (N - 1)) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 (G + 56 * Z.of_nat i)) = G + 56 * Z.of_nat i) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 56) = 56) by reflexivity.
  pose proof (munch_refl [(G + 56 * Z.of_nat i, G + 56 * Z.of_nat i + 56); (200664, 200668)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HC as [(HLT & SRC & DST) | (HEQ & DST)].
  - step. step.
    rewrite (rm_sx32 N) by lia.
    step. step.
    replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 N) + -1)) with (N - 1)
      by (rewrite unsigned_lit by lia; unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31);
          change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small by lia; lia).
    step. step. step. step.
    lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?a - bv_unsigned ?b)] =>
      replace (Z_to_bv 64 (bv_unsigned a - bv_unsigned b)) with (Z_to_bv 64 (56 * (N - 1)))
        by (f_equal; rewrite (unsigned_lit (N - 1)) by lia; rewrite !Z.shiftl_mul_pow2 by lia;
            rewrite !unsigned_lit by lia; lia)
    end.
    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (MCP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src dj);
        [ rewrite US; exact SRC | rewrite UN; exact LS | rewrite UD, UN; exact DST | rewrite US, UD, UN; lia
        | assumption ]
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; unfold memcpy_post in PO; rewrite ?US, ?UD, ?UN in PO; revert ms' PO;
        post_call rsegs mm ]
    end.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption.
  - step. step.
    rewrite (rm_sx32 N) by lia.
    step. step.
    replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 N) + -1)) with (N - 1)
      by (rewrite unsigned_lit by lia; unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31);
          change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small by lia; lia).
    step. step. step. step.
    lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?a - bv_unsigned ?b)] =>
      replace (Z_to_bv 64 (bv_unsigned a - bv_unsigned b)) with (Z_to_bv 64 (56 * (N - 1)))
        by (f_equal; rewrite (unsigned_lit (N - 1)) by lia; rewrite !Z.shiftl_mul_pow2 by lia;
            rewrite !unsigned_lit by lia; lia)
    end.
    step. step. step.
    replace (Z_to_bv 64 (G + 56 * (N - 1))) with (Z_to_bv 64 (G + 56 * Z.of_nat i)) by (f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (MCS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src);
        [ reflexivity | rewrite UN; exact LS | rewrite UD, UN; exact DST | assumption ]
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; unfold memcpy_post in PO; rewrite ?UD, ?UN in PO; revert ms' PO;
        post_call rsegs mm ]
    end.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    replace (G + 56 * (N - 1)) with (G + 56 * Z.of_nat i) by lia.
    repeat (split; [eassumption|]). eassumption.
Qed.

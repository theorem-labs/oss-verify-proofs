From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes
  ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandTac.
Import ListNotations.
Open Scope Z_scope.

Definition crt_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : list cell :=
  [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition crt_ret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom rsegs).

Lemma crt_s9 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vra : word),
  bv_unsigned sp = S - 992 -> 992 <= S < 2 ^ 64 ->
  rw_cells rsegs m (S - 88) (crt_saved vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) ->
  evt rsegs (crt_ret vra (Z_to_bv 64 S) gp tp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15078) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 vra ESP RS FR.
  unfold crt_saved in FR.
  replace (S - 88) with (bv_unsigned sp + 904) in FR by lia.
  do 13 zstep.
  replace (bv_unsigned sp + 992) with S by lia.
  apply evt_done. unfold crt_ret. do 15 eexists. reflexivity.
Qed.

Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sx32_zero : forall z, 0 <= z < 2 ^ 32 -> (bv_unsigned (sx32 (Z_to_bv 64 z)) = 0 <-> z = 0).
Proof.
  intros z Hz. unfold sx32. rewrite (unsigned_lit z) by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z_lt_ge_dec z (2 ^ 31)).
  - rewrite (Z.mod_small (z + 2 ^ 31)) by lia. replace (z + 2 ^ 31 - 2 ^ 31) with z by lia.
    rewrite Z.mod_small by lia. lia.
  - assert (E1 : (z + 2 ^ 31) mod 2 ^ 32 = z + 2 ^ 31 - 2 ^ 32) by (symmetry; apply Z.mod_unique with 1; lia).
    rewrite E1.
    assert (E2 : (z + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) mod 2 ^ 64 = z - 2 ^ 32 + 2 ^ 64)
      by (symmetry; apply Z.mod_unique with (-1); lia).
    rewrite E2. lia.
Qed.

Definition crt_at_copy (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ms' : machine_state) : Prop :=
  exists a1', ms' = MS (mkR (Z_to_bv 64 0x14fd4) (Z_to_bv 64 (bv_unsigned sp - 992)) gp tp t0 t1 t2 s0 s1
                            (Z_to_bv 64 (bv_unsigned sp - 984)) a1' a2 a3 a4 a5 a6 a7 a0 a2 a1
                            (Z_to_bv 64 0x34028) (Z_to_bv 64 0x343e8) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x15c24) fc None m (seg_rom rsegs).

Lemma crt_al8 : forall s k, s mod 16 = 0 -> (s + 8 * k) mod 8 = 0.
Proof. intros s k H. Z.div_mod_to_equations. lia. Qed.

Lemma crt_s0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo W nw q nc : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 992 <= bv_unsigned sp -> 0x40000 <= lo ->
  a0 = Z_to_bv 64 W -> W mod 8 = 0 -> bv_unsigned sp <= W + 24 -> W + 28 <= 2 ^ 64 ->
  bytes_at rsegs m (W + 24) (le4 (Z_to_bv 64 nw)) -> 0 <= nw < 2 ^ 31 ->
  bytes_at rsegs m 0x22d10 (le8 (Z_to_bv 64 0x343e8)) -> bytes_at rsegs m 0x22cf8 (le8 (Z_to_bv 64 0x34028)) ->
  bytes_at rsegs m 0x343e8 (le4 (Z_to_bv 64 q)) -> 0 <= q < 2 ^ 32 ->
  bytes_at rsegs m 213040 (le4 (Z_to_bv 64 nc)) -> 0 <= nc <= 16 ->
  evt rsegs (fun ms' =>
      ((nw = 0 \/ (q = 0 /\ nc = 0)) /\ exists m',
         crt_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' ms' /\
         munch [(bv_unsigned sp - 992, bv_unsigned sp)] m m' /\ wmono rsegs m m') \/
      (nw <> 0 /\ (q <> 0 \/ nc <> 0) /\ exists m' junk,
         crt_at_copy sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m' ms' /\
         munch [(bv_unsigned sp - 992, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned sp - 992) (CB 904 junk :: crt_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f60) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo W nw q nc ST LO LOI -> WAL HW1 HW2 HN RN HG1 HG2 HQ RQ HC RC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 992, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UW : bv_unsigned (Z_to_bv 64 W) = W) by (apply unsigned_lit; lia).
  apply bytes_ro4 in HN, HQ, HC. apply bytes_ro8 in HG1, HG2.
  carve_frame 992%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 992%nat junk [] [904; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  do 14 zstep.
  zb_masks. rewrite ?UW, ?WAL.
  zstep. if_cases HAL.
  { exfalso. zify_cond HAL. rewrite ?UW, ?WAL in HAL. lia. }
  zstep.
  zstep. if_cases HZ.
  - zify_cond HZ. rewrite sx32_small in HZ by lia. rewrite unsigned_lit in HZ by lia.
    do 13 zstep.
    apply evt_done. left. split; [left; lia|]. exists m0. split; [unfold crt_ret; do 15 eexists; reflexivity|].
    split; [exact MU | exact WM].
  - zify_cond HZ. rewrite sx32_small in HZ by lia. rewrite unsigned_lit in HZ by lia.
    do 8 zstep. if_cases HQZ.
    + zify_cond HQZ. rewrite sx32_zero in HQZ by lia.
      do 2 zstep.
      apply evt_done. right. split; [lia|]. split; [left; lia|]. exists m0, (firstn 904 junk).
      split; [unfold crt_at_copy; eexists; reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact FR.
    + zify_cond HQZ. rewrite sx32_zero in HQZ by lia. do 2 zstep. if_cases HCZ.
      * zify_cond HCZ. rewrite sx32_small, unsigned_lit in HCZ by lia.
        assert (NC0 : nc = 0) by (apply andb_false_iff in HCZ; destruct HCZ as [HCZ|HCZ]; apply Z.ltb_ge in HCZ; lia).
        do 13 zstep.
        apply evt_done. left. split; [right; split; [exact HQZ | exact NC0]|]. exists m0.
        split; [unfold crt_ret; do 15 eexists; reflexivity|]. split; [exact MU | exact WM].
      * rewrite sx32_small in HCZ by lia. zify_cond HCZ. rewrite ?unsigned_lit in * by lia.
        assert (NC0 : nc <> 0) by lia.
        do 2 zstep.
        apply evt_done. right. split; [lia|]. split; [right; exact NC0|]. exists m0, (firstn 904 junk).
        split; [unfold crt_at_copy; eexists; reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact FR.
Qed.

Lemma crt_s1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (rp st ho : word),
  s5 = Z_to_bv 64 0x34028 -> s6 = Z_to_bv 64 0x343e8 ->
  bytes_at rsegs m 0x343e8 (le4 (Z_to_bv 64 q)) ->
  bytes_at rsegs m 213960 (le8 rp) -> bytes_at rsegs m 213976 (le8 st) -> bytes_at rsegs m 213984 (le8 ho) ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x14ff0) sp gp tp t0 t1 t2 a0 s1 rp rp a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 ho (sx32 (Z_to_bv 64 q)) st s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x20f68) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14fd4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q rp st ho
    -> -> HQ HR HS HH.
  apply bytes_ro4 in HQ. apply bytes_ro8 in HR, HS, HH.
  do 7 zstep.
  apply evt_done. reflexivity.
Qed.

Lemma crt_s2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st ho : word),
  bv_unsigned a0 <> 0 -> s5 = Z_to_bv 64 0x34028 ->
  rw_cells rsegs m 213976 [C8 st; C8 ho] ->
  evt rsegs (fun ms' => exists m', ms' = MS (mkR (Z_to_bv 64 0x1500c) sp gp tp t0 t1 t2 s0 a0 s2 sp a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x15324) fc None m' (seg_rom rsegs) /\
                        munch [(213976, 213992)] m m' /\ wmono rsegs m m' /\ rw_cells rsegs m' 213976 [C8 s4; C8 s3])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ff0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st ho
    NZ -> FR.
  pose proof (munch_refl [(213976, 213992)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. if_false_by (proj2 (Z.eqb_neq _ _) NZ).
  do 6 zstep.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact FR].
Qed.

Lemma crt_s3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lw : word),
  bytes_at rsegs m (bv_unsigned sp) (le8 lw) ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x15018) sp gp tp t0 t1 t2 s0 s1 a0 lw a2 a3 a4 a5 a6 a7
                                   a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x14444) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1500c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lw HL.
  apply bytes_ro8 in HL. replace (bv_unsigned sp) with (bv_unsigned sp + 0) in HL by lia.
  do 3 zstep.
  apply evt_done. reflexivity.
Qed.

Lemma crt_s4 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x15020) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15018) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 zstep.
  apply evt_done. reflexivity.
Qed.

Lemma crt_s8 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x15078) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15070) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 zstep.
  apply evt_done. reflexivity.
Qed.

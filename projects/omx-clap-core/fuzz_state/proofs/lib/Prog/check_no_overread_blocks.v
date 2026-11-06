From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import memcpy_c memset_c bcmp_c past_nul_c past_nul.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma cno_rw_app : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (H1 & H2 & Hw)].
  apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ B2].
  rewrite cells_size_app in H2, Hw.
  rewrite (cells_bytes_length _ W1) in B2.
  split; [split; [exact W2 | exact B2]|].
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
  apply Hw. lia.
Qed.

Lemma cno_memcmp_refl : forall xs, memcmp_model xs xs (length xs) = Some 0.
Proof. induction xs as [|x xs IH]; cbn; [reflexivity|]. rewrite Z.eqb_refl. exact IH. Qed.

Lemma cno_pro : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x13474) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1
                    (Z_to_bv 64 65) a3 a4 a5 a6 a7 s2 a1 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13e38) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      munch [(bv_unsigned sp + -96, bv_unsigned sp)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13440) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO.
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 96%nat ST.
  do 13 zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [|split; [exact MU | exact WM]].
  lazymatch goal with H : rw_cells _ _ _ (?c :: ?cs) |- _ =>
    pose proof (cno_rw_app _ _ [c] cs H) as FR' end.
  cbn [cells_size csize Nat.add] in FR'.
  replace (bv_unsigned sp + -64) with (bv_unsigned sp + -96 + Z.of_nat 32) by lia.
  exact FR'.
Qed.

Lemma cno_s1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x13488) sp gp tp t0 t1 t2 a0 s1 s4 s3 (Z_to_bv 64 66) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13e38) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13474) fc None m (seg_rom rsegs)).
Proof. intros. do 5 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_s2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x13498) sp gp tp t0 t1 t2 s0 a0 (Z_to_bv 64 (bv_unsigned s3 + 18)) a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 (Z_to_bv 64 (bv_unsigned s3 + 18)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16594) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13488) fc None m (seg_rom rsegs)).
Proof. intros. do 4 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_s4 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x134f4) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 (bv_unsigned sp + 16)) a2 a3 a4 a5
                    a6 a7 s2 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14e90) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134e4) fc None m (seg_rom rsegs)).
Proof. intros. do 4 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_s5 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x13504) sp gp tp t0 t1 t2 s0 s1 s2 (Z_to_bv 64 (bv_unsigned sp + 8)) a2 a3 a4 a5
                    a6 a7 s2 s3 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14e90) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134f4) fc None m (seg_rom rsegs)).
Proof. intros. do 4 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_s7 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x13574) sp gp tp t0 t1 t2 s0 s1 s4 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x141c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1356c) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_s8 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x1357c) sp gp tp t0 t1 t2 s0 s1 s5 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x141c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13574) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_s9 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x13584) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16454) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1357c) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_s10 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x1358c) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16454) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13584) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_s11 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x13594) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x16454) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1358c) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_epi : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 : word),
  rw_cells rsegs m (bv_unsigned sp + 32) [C8 xs6; C8 xs5; C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 96)) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5
                    a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc xra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13594) fc None m (seg_rom rsegs)).
Proof. intros. do 10 zstep. apply evt_done. reflexivity. Qed.

Lemma cno_cz2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res n : Z) (db j0 j1 j2 : list byte),
  memset_contract ->
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 j0] ->
  bytes_at rsegs m res db ->
  rw_cells rsegs m (res + n) [CB 17 j1] ->
  rw_cells rsegs m (res + (n + 18) + -1) [CB 1 j2] ->
  s2 = Z_to_bv 64 res -> s3 = Z_to_bv 64 n -> s5 = Z_to_bv 64 (n + 18) ->
  0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n -> 4096 <= res ->
  res + n + 18 <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2 ^ 64 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x134e4) sp gp tp t0' t1' t2' s0 s1 s0 (Z_to_bv 64 (bv_unsigned sp + 24))
                    a2' a3' a4' a5' a6' a7' s2 s3 s4 s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14e90) fc None m' (seg_rom rsegs) /\
      munch [(res + n, res + n + 18); (bv_unsigned sp + 8, bv_unsigned sp + 32)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\ bytes_at rsegs m' res (db ++ repeat (Z_to_bv 8 0) 18))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res n db j0 j1 j2 MEMSET SL DB R1 R2 E2 E3 E5 Hn Hl Hr Hsp Hsp2 MI.
  subst s2 s3 s5.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(res + n, res + n + 18); (bv_unsigned sp + 8, bv_unsigned sp + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 5 zstep.
  eapply evt_cut.
  { eapply MEMSET with (junk := j1).
    - rewrite (unsigned_lit (res + n)) by lia. exact R1.
    - exact MI. }
  intros ms' POST. unfold memset_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
    E & MUc & WMc & MIc & RVc).
  subst ms'.
  rewrite (unsigned_lit (res + n)) in MUc, RVc by lia.
  change (bv_unsigned (Z_to_bv 64 17)) with 17 in MUc.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 17))) with 17%nat in RVc.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RVc.
  replace (ret_pc (Z_to_bv 64 0x134c8)) with (Z_to_bv 64 0x134c8) by (apply bv_eq; vm_compute; reflexivity).
  assert (MU2 : munch [(res + n, res + n + 18); (bv_unsigned sp + 8, bv_unsigned sp + 32)] m m2).
  { eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
  pose proof (wmono_trans rsegs m m m2 WM WMc) as WM2.
  apply (rw_cells_transport rsegs [(res + n, res + n + 17)] m m2) in SL;
    [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
  apply (rw_cells_transport rsegs [(res + n, res + n + 17)] m m2) in R2;
    [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
  apply (bytes_at_transport rsegs [(res + n, res + n + 17)] m m2) in DB;
    [| exact MUc | cbn [disjoint_from]; lia].
  clear MU WM MI R1 MUc WMc.
  rename MU2 into MU, WM2 into WM, MIc into MI, RVc into R1.
  zstep.
  rewrite (pn_le1 0) by lia. mem_after_store.
  do 6 zstep.
  apply evt_done. do 14 eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  destruct R1 as [[_ B1] _]. destruct R2 as [[_ B2] _].
  cbn [cells_bytes cbytes app] in B1, B2.
  match goal with |- bytes_at _ ?mm _ _ =>
    assert (B12 : bytes_at rsegs mm (res + n) (repeat (Z_to_bv 8 0) 18)) end.
  { replace (repeat (Z_to_bv 8 0) 18) with ((repeat (Z_to_bv 8 0) 17 ++ []) ++ [Z_to_bv 8 (0 mod 256)]) by reflexivity.
    apply bytes_at_app. split; [exact B1|].
    match goal with |- bytes_at _ _ ?a _ => replace a with (res + (n + 18) + -1) by (cbn; lia) end.
    exact B2. }
  apply bytes_at_app. split; [exact DB|]. rewrite Hl. exact B12.
Qed.

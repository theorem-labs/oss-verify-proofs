From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition VR_ENTRY : Z := 0x1742c.
Definition VR_STRNDUP : Z := 0x20eac.
Definition VR_FRAME : Z := 608.

Definition vr_frame_cells (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) (junk : list byte) : list cell :=
  [CB 528 junk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition pro_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (msg data n : word) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
                    (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x17468) (Z_to_bv 64 (bv_unsigned sp - VR_FRAME)) gp tp t0' t1' t2' s0 s1 data n
                  a2' a3' a4' a5' a6' a7' msg s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 VR_STRNDUP) fc None m' (seg_rom rsegs) /\
    rw_cells rsegs m' (bv_unsigned sp - VR_FRAME) (vr_frame_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 junk) /\
    munch [(bv_unsigned sp - VR_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp - VR_FRAME).

Lemma read_all_pro : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [skipn Z.of_nat] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Lemma vr_pro :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (data n : word),
    stk rsegs m lo (bv_unsigned sp) -> lo + VR_FRAME <= bv_unsigned sp ->
    bytes_at rsegs m (bv_unsigned a0 + 8) (le8 data) -> bytes_at rsegs m (bv_unsigned a0 + 16) (le8 n) ->
    bv_unsigned a0 + 24 <= bv_unsigned sp - VR_FRAME \/ bv_unsigned sp <= bv_unsigned a0 ->
    mem_inv rsegs m ->
    evt rsegs (pro_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m a0 data n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VR_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo data n ST LO HD HN DJ MI.
  unfold VR_FRAME in *.
  pose proof (munch_refl [(bv_unsigned sp - 608, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. change (bv_modulus 64) with (2^64) in Ra0.
  pose proof (proj1 ST) as LO0.
  pose proof (bytes_at_bound rsegs _ _ _ HN) as BN. rewrite length_le8 in BN.
  carve_frame 608%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 608%nat junk [] [528; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  unfold VR_ENTRY.
  do 11 zstep.
  pose proof (read_all_pro _ _ _ HD) as RD. rewrite length_le8 in RD.
  pose proof (read_all_pro _ _ _ HN) as RN. rewrite length_le8 in RN.
  do 4 zstep.
  replace (bv_unsigned sp + -608) with (bv_unsigned sp - 608) in * by lia.
  apply evt_done. unfold pro_post, vr_frame_cells, VR_FRAME, VR_STRNDUP.
  do 15 eexists. split; [reflexivity|].
  split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

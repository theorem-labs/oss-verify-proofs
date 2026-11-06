From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import check_braid FloatExact crt_convert.
Import ListNotations.
Open Scope Z_scope.

Definition CRT_MALLOC : Z := 0x147c4.

Ltac crt_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

Ltac crt_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.

Ltac crt_w := crt_usub; rewrite ?Z.shiftl_mul_pow2 by lia;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].

Ltac crt_fin := apply evt_done; f_equal; crt_regs; crt_w.

Definition crt_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (audio pcm nch ns : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 junk,
    ms' = MS (mkR (Z_to_bv 64 0x13344) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 s0 (Z_to_bv 64 audio)
               (Z_to_bv 64 (4 * (nch * ns))) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (3 * (nch * ns))) s3 (Z_to_bv 64 ns)
               (Z_to_bv 64 nch) (Z_to_bv 64 (nch * ns)) (Z_to_bv 64 pcm) s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CRT_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma crt_seg1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (audio pcm nch ns lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp ->
    2 <= nch <= 127 -> 1 <= ns <= 12 -> 0 <= audio < 2^63 -> 0 <= pcm < 2^63 ->
    evt rsegs (crt_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc audio pcm nch ns m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 audio) (Z_to_bv 64 pcm) (Z_to_bv 64 nch) (Z_to_bv 64 ns)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x132f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m audio pcm nch ns lo
    ST LO HN HS HA HP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (NN : 0 < nch * ns <= 1524) by nia.
  carve_frame 80%nat ST.
  do 19 step.
  apply evt_done. unfold crt_s1_post.
  do 16 eexists. split.
  2: { split; [eassumption|]. split; [eassumption|]. replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia.
       eassumption. }
  f_equal. crt_regs.
  all: crt_w.
Qed.

Definition CRT_CALLOC : Z := 0x1454c.
Definition CRT_FREE : Z := 0x14684.

Lemma crt_seg2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (nch : Z),
    0 <= nch <= 127 ->
    evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13350) sp gp tp t0 t1 t2 a0 s1 (Z_to_bv 64 (8 * nch)) a1 a2 a3 a4
                                       a5 a6 a7 s2 s3 s4 (Z_to_bv 64 nch) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CRT_MALLOC) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 nch) s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x13344) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nch HN.
  do 3 step.
  crt_fin.
Qed.

Lemma crt_seg3 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k : Z),
    0 < k <= 1524 ->
    evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13368) sp gp tp t0 t1 t2 s0 s1 s2 (Z_to_bv 64 1) a2 a3 a4
                                       a5 a6 a7 s2 a0 s4 s5 (Z_to_bv 64 k) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CRT_CALLOC) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 k) s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x13350) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m k HK.
  do 3 step. take true.
  do 2 step.
  crt_fin.
Qed.

Lemma crt_seg5 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13464) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4
                                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1345c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step.
  crt_fin.
Qed.

Lemma crt_seg6 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte)
         (v0 v1 v2 v3 v4 v5 v6 v7 vra : word),
    rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 80)) gp tp t0 t1 t2 v0 v1 s0 a1 a2 a3 a4
                                       a5 a6 a7 v2 v3 v4 v5 v6 v7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13464) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk
    v0 v1 v2 v3 v4 v5 v6 v7 vra FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 12 step.
  crt_fin.
Qed.

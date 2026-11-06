(* check_state_desk_seg_tail: the three pieces of check_state_desk in image B (fuzz_transport.asan-ubsan) around
   the two bcmp calls: csd_call1_F (0x8569c, the UBSan alignment test of the announce, .. the call at 0x856ac),
   csd_mid_F (the return 0x856b0, bcmp answered 0, the UBSan bound and wrap tests of vn, .. the call at 0x856f0) and
   csd_ret_F (the return 0x856f4, the UBSan bound and wrap tests of nn, .. the `ret` at 0x85740, through the
   epilogue). Image B's twin of lib/A/Prog/check_state_desk_seg_tail.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_desk_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Section Pieces.
Variables (RNG : ExecF.footprint)
  (sp gp tp t0 t1 t2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Local Notation ST pc x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 mm :=
  (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
           s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
Local Notation AN NB := (TW.u_at NB 24 8).
Local Notation DB Bw := (TW.u_at Bw TW.A_OW_desk_body 8).

(* ---- 0x8569c .. the call of bcmp at 0x856ac: announce & 7 = 0; a0 = announce, a1 = OW.desk_body + 15,
   a2 = vn ---- *)

Lemma csd_call1_F : forall (m : word -> option byte) (NB Bw : list byte) (vn nn : nat)
    (ra x10 x12 x13 x14 x15 x16 x17 : word),
  0 <= AN NB < 2 ^ 63 -> AN NB mod 8 = 0 ->
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = ST CSD_BCMP (Z_to_bv 64 CSD_RET1) (Z_to_bv 64 (AN NB)) (Z_to_bv 64 (DB Bw + 24))
                        (Z_to_bv 64 (AN NB)) (Z_to_bv 64 (DB Bw + 15)) (Z_to_bv 64 (Z.of_nat vn)) x13 x14 x15
                        x16 x17 (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 ASAN_K) m)
    (ST 0x8569c ra (Z_to_bv 64 (AN NB)) (Z_to_bv 64 (DB Bw + 24)) x10
        (Z_to_bv 64 (DB Bw + 15)) x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 ASAN_K) m).
Proof.
  intros m NB Bw vn nn ra x10 x12 x13 x14 x15 x16 x17 HA HA8.
  unfold ASAN_K, CSD_BCMP, CSD_RET1.
  (* 0x8569c andi a0,s0,7; 0x856a0 bnez a0: announce mod 8 = 0 (the UBSan alignment test) *)
  step.
  step. br_false ltac:(rewrite (unsigned_lit (AN NB)) by lia; rewrite land7, HA8, bv_eqb_refl; reflexivity).
  step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* ---- the return of the first call (0x856b0), its answer 0, .. the call at 0x856f0 ---- *)

Lemma csd_mid_F : forall (m : word -> option byte) (p : Z) (NB Bw : list byte) (fr : TI.tframe) (vn nn : nat)
    (ra2 x11 x12 x13 x14 x15 x16 x17 : word),
  csd_mem m p NB Bw fr vn nn -> csd_rng RNG (bv_unsigned sp) p NB fr vn nn -> csd_bnd p NB Bw fr ->
  (vn <= 9)%nat -> (nn <= 9)%nat ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists y13 y14 y15 : word,
       ms' = ST CSD_BCMP (Z_to_bv 64 CSD_RET2) (Z_to_bv 64 (AN NB + 10)) (Z_to_bv 64 (DB Bw + 24))
               (Z_to_bv 64 (AN NB + 10)) (Z_to_bv 64 (DB Bw + 24)) (Z_to_bv 64 (Z.of_nat nn)) y13 y14 y15
               x16 x17 (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 ASAN_K) m)
    (ST CSD_RET1 ra2 (Z_to_bv 64 (AN NB)) (Z_to_bv 64 (DB Bw + 24))
        (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 ASAN_K) m).
Proof.
  intros m p NB Bw fr vn nn ra2 x11 x12 x13 x14 x15 x16 x17 MEM RNGH BND LV LN.
  csd_prep MEM RNGH BND.
  destruct (M17 (AN NB + Z.of_nat vn) ltac:(left; reflexivity)) as (MBY & kx & MKX & SKX).
  assert (RBY : ExecF.rng RNG (AN NB + Z.of_nat vn) 1)
    by (apply RA; do 9 right; exists (AN NB + Z.of_nat vn); split; [left; reflexivity | left; reflexivity]).
  assert (RSY : ExecF.rng RNG ((AN NB + Z.of_nat vn) / 8 + ASAN_K) 1)
    by (apply RA; do 9 right; exists (AN NB + Z.of_nat vn); split; [left; reflexivity | right; reflexivity]).
  pose proof (Z.mod_pos_bound (AN NB + Z.of_nat vn) 8 ltac:(lia)) as MBX.
  unfold ASAN_K, CSD_RET1, CSD_RET2 in *.
  assert (BODY : forall y13 y14 y15 : word,
    ExecF.evtF rsegs RNG
      (fun ms' => exists z13 z14 z15 : word,
         ms' = ST CSD_BCMP (Z_to_bv 64 546548) (Z_to_bv 64 (AN NB + 10)) (Z_to_bv 64 (DB Bw + 24))
                 (Z_to_bv 64 (AN NB + 10)) (Z_to_bv 64 (DB Bw + 24)) (Z_to_bv 64 (Z.of_nat nn)) z13 z14 z15
                 x16 x17 (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 2147450880) m)
      (ST 0x856d8 ra2 (Z_to_bv 64 (AN NB)) (Z_to_bv 64 (DB Bw + 24))
          (Z_to_bv 64 (AN NB + Z.of_nat vn)) y13 y14 y15 x14 x15 x16 x17
          (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 2147450880) m)).
  { intros y13 y14 y15.
    pose proof (rd1 _ _ _ MBY) as RB.
    step. clear RB.
    step. brF false.
    step. try rewrite (unsigned_lit (AN NB)) by lia.
    step. step. step. step.
    apply evtF_done. do 3 eexists. reflexivity. }
  (* 0x856b0 bne a0,zero: the answer is 0 *)
  step. brF false.
  (* 0x856b4 li a0,10; 0x856b8 bgeu s2,a0: vn < 10 (the UBSan bound test) *)
  step. step. br_false ltac:(unfold bv_ltu; rewrite (unsigned_lit (Z.of_nat vn)) by lia;
    change (bv_unsigned (Z_to_bv 64 10)) with 10; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
  (* 0x856bc xori a0,s0,-1; 0x856c0 bltu a0,s2: announce + vn does not wrap (the UBSan wrap test) *)
  step. try rewrite (unsigned_lit (AN NB)) by lia.
  step. br_false ltac:(exact (csd_ltu_xor (AN NB) (Z.of_nat vn) ltac:(lia) ltac:(lia) ltac:(lia))).
  (* 0x856c4 add a0,s0,s2 and the check of the 1-byte load at announce + vn *)
  csd_chk1 ltac:(try rewrite (unsigned_lit (AN NB)) by lia; try rewrite (unsigned_lit (Z.of_nat vn)) by lia)
    (AN NB + Z.of_nat vn) MKX SKX RSY BODY.
Qed.

(* ---- the return of the second call (0x856f4), its answer 0, .. the `ret` at 0x85740 ---- *)

Lemma csd_ret_F : forall (m : word -> option byte) (p : Z) (NB Bw : list byte) (fr : TI.tframe) (vn nn : nat)
    (ra c0 c1 c2 c3 c4 : word) (lo : Z) (ra2 x11 x12 x13 x14 x15 x16 x17 : word),
  csd_mem m p NB Bw fr vn nn -> csd_rng RNG (bv_unsigned sp) p NB fr vn nn -> csd_bnd p NB Bw fr ->
  (vn <= 9)%nat -> (nn <= 9)%nat ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp + -48 ->
  rw_cells rsegs m (bv_unsigned sp + -48) (csd_fr c4 c3 c2 c1 c0 ra) ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (r10 r11 r12 r13 r14 r15 r16 r17 spx : word),
       ms' = MS (mkR ra spx gp tp t0 t1 t2 c0 c1 r10 r11 r12 r13 r14 r15 r16 r17 c2 c3 c4
                     s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m (seg_rom rsegs) /\
       bv_unsigned spx = bv_unsigned sp /\ stk rsegs m lo (bv_unsigned sp))
    (ST CSD_RET2 ra2 (Z_to_bv 64 (AN NB + 10)) (Z_to_bv 64 (DB Bw + 24))
        (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 ASAN_K) m).
Proof.
  intros m p NB Bw fr vn nn ra c0 c1 c2 c3 c4 lo ra2 x11 x12 x13 x14 x15 x16 x17 MEM RNGH BND LV LN ST48 HLO FR.
  csd_prep MEM RNGH BND.
  destruct (M17 (AN NB + 10 + Z.of_nat nn) ltac:(right; reflexivity)) as (MBY & kx & MKX & SKX).
  assert (RBY : ExecF.rng RNG (AN NB + 10 + Z.of_nat nn) 1)
    by (apply RA; do 9 right; exists (AN NB + 10 + Z.of_nat nn); split; [right; reflexivity | left; reflexivity]).
  assert (RSY : ExecF.rng RNG ((AN NB + 10 + Z.of_nat nn) / 8 + ASAN_K) 1)
    by (apply RA; do 9 right; exists (AN NB + 10 + Z.of_nat nn); split; [right; reflexivity | right; reflexivity]).
  pose proof (Z.mod_pos_bound (AN NB + 10 + Z.of_nat nn) 8 ltac:(lia)) as MBX.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST48) as L0.
  unfold ASAN_K, CSD_RET2, csd_fr in *.
  assert (BODY : forall y13 y14 y15 : word,
    ExecF.evtF rsegs RNG
      (fun ms' => exists (r10 r11 r12 r13 r14 r15 r16 r17 spx : word),
         ms' = MS (mkR ra spx gp tp t0 t1 t2 c0 c1 r10 r11 r12 r13 r14 r15 r16 r17 c2 c3 c4
                       s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs) /\
         bv_unsigned spx = bv_unsigned sp /\ stk rsegs m lo (bv_unsigned sp))
      (ST 0x8571c ra2 (Z_to_bv 64 (AN NB + 10)) (Z_to_bv 64 (DB Bw + 24))
          (Z_to_bv 64 (AN NB + 10 + Z.of_nat nn)) y13 y14 y15 x14 x15 x16 x17
          (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 2147450880) m)).
  { intros y13 y14 y15.
    pose proof (rd1 _ _ _ MBY) as RB.
    step. clear RB.
    step. brF false.
    do 8 step.
    apply evtF_done. do 9 eexists. split; [reflexivity|].
    split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia|].
    release_frame FR ST48 (bv_unsigned sp). exact ST48. }
  (* 0x856f4 bne a0,zero: the answer is 0 *)
  step. brF false.
  (* 0x856f8 li a0,9; 0x856fc bltu a0,s3: nn <= 9 (the UBSan bound test) *)
  step. step. br_false ltac:(unfold bv_ltu; rewrite (unsigned_lit (Z.of_nat nn)) by lia;
    change (bv_unsigned (Z_to_bv 64 9)) with 9; apply Z.ltb_ge; lia).
  (* 0x85700 xori a0,s0,-1; 0x85704 bltu a0,s3: announce + 10 + nn does not wrap (the UBSan wrap test) *)
  step. try rewrite (unsigned_lit (AN NB + 10)) by lia.
  step. br_false ltac:(exact (csd_ltu_xor (AN NB + 10) (Z.of_nat nn) ltac:(lia) ltac:(lia) ltac:(lia))).
  (* 0x85708 add a0,s0,s3 and the check of the 1-byte load at announce + 10 + nn *)
  csd_chk1 ltac:(try rewrite (unsigned_lit (AN NB + 10)) by lia; try rewrite (unsigned_lit (Z.of_nat nn)) by lia)
    (AN NB + 10 + Z.of_nat nn) MKX SKX RSY BODY.
Qed.

End Pieces.

(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
     image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
       sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
     source run: lib/B/Prog/Seg/F38.v (not in this delivery) seg_F38 (its three sl_run runs).
       F38.v (an earlier version, blob fea2ecee7e4ebf8726114535df6769d708c588b4, not in this delivery) is from a working branch 3803efccea0.  The frame-loop
       latch 0x82d1c-0x82d28 calls nothing, stores nothing and reads no memory at all (registers a0, a3 only), so
       there is no _pre_F / _post_F split and the twin takes no rng premise;
     tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
           lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
     compare: seg_F38_run re-derives the run the segment proof feeds to Tac_slot.sl_run_lib, from seg_F38_F at
       RNG := RNG_all (evtF_evt; there is no rng premise to discharge).  The segment proof states its three arms
       in the UL engine and lifts them with SmLib.ul_entry; the lib.Lib form below is the one
       Tac_slot.sl_run_lib takes (F7.v's path), with the three arms joined in one post. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* F38.v's two bit-vector helpers (f38_eqb_lit, f38_swrap), copied so that this file does not depend on F38. *)
Lemma f38f_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma f38f_swrap : forall x, 0 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.

Ltac bvlit := first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].

(* ===== S_F38: the frame-loop latch.  s5 = j (0 <= j <= 255), s9 = left_(j+1).
     0x82d1c addiw a3,s5,1 ; 0x82d20 li a0,256 ; 0x82d24 bne a3,a0,81ec4 ; 0x82d28 j 82eac,
   and on the back edge 0x81ec4 bnez s9,81ecc ; 0x81ec8 j 82eac.  Three arms:
     j = 255                  -> 0x82eac;
     j <> 255, left = 0       -> 0x81ec4 -> 0x81ec8 -> 0x82eac;
     j <> 255, left <> 0      -> 0x81ec4, with a3 = j + 1.
   No call, no store, no load, no instrumented check: the footprint is empty. ===== *)

Lemma seg_F38_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (jz L : Z),
    s5v = Z_to_bv 64 jz -> s9v = Z_to_bv 64 L ->
    0 <= jz <= 255 -> 0 <= L < 2 ^ 64 ->
    evtF rsegs RNG
      (fun ms' => exists (a0' a3' pc' : word),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' a1 a2 a3' a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v
                       s10 s11v t3 t4 t5 t6)
                  Fr pc' fc None m (seg_rom rsegs) /\
         ((pc' = Z_to_bv 64 0x82eac /\ (jz = 255 \/ L = 0)) \/
          (pc' = Z_to_bv 64 0x81ec4 /\ jz <> 255 /\ L <> 0 /\ a3' = Z_to_bv 64 (jz + 1))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82d1c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6
    Fr fc m jz L -> -> Hj HL.
  (* 0x82d1c addiw a3,s5,1 = j + 1 ; 0x82d20 li a0,256 *)
  step. rewrite ?(MState.unsigned_lit jz) by lia. rewrite ?(f38f_swrap (jz + 1)) by lia.
  step.
  (* 0x82d24 bne a3,a0 *)
  step. rewrite ?f38f_eqb_lit by lia.
  destruct (Z.eq_dec jz 255) as [Ej|Hjne].
  - (* j = 255: not taken, 0x82d28 j 82eac *)
    rewrite Ej. cbn [Z.eqb Z.add Pos.add].
    first [if_false | if_true].
    step.
    apply evtF_done. cbv beta. do 3 eexists.
    split; [first [reflexivity | (cbv delta [mkR]; reflexivity)]|].
    left. split; [bvlit | left; first [exact Ej | reflexivity]].
  - replace (jz + 1 =? 256) with false by (symmetry; apply Z.eqb_neq; lia).
    first [if_true | if_false].
    destruct (Z.eq_dec L 0) as [E0|Hne0].
    + (* left_(j+1) = 0: 0x81ec4 bnez s9 not taken ; 0x81ec8 j 82eac *)
      rewrite E0.
      step. first [if_false | if_true].
      step.
      apply evtF_done. cbv beta. do 3 eexists.
      split; [first [reflexivity | (cbv delta [mkR]; reflexivity)]|].
      left. split; [bvlit | right; first [exact E0 | reflexivity]].
    + (* left_(j+1) >= 1: the back edge lands at the loop head 0x81ec4 *)
      apply evtF_done. cbv beta. do 3 eexists.
      split; [first [reflexivity | (cbv delta [mkR]; reflexivity)]|].
      right. split; [bvlit|]. split; [exact Hjne|]. split; [exact Hne0|].
      first [reflexivity | bvlit].
Qed.

(* ===== The run itself, in the lib.Lib Exec form Tac_slot.sl_run_lib takes (the auditor's compare). ===== *)

Lemma seg_F38_run :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (jz L : Z),
    s5v = Z_to_bv 64 jz -> s9v = Z_to_bv 64 L ->
    0 <= jz <= 255 -> 0 <= L < 2 ^ 64 ->
    Exec.evt rsegs
      (fun ms' => exists (a0' a3' pc' : word),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' a1 a2 a3' a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v
                       s10 s11v t3 t4 t5 t6)
                  Fr pc' fc None m (seg_rom rsegs) /\
         ((pc' = Z_to_bv 64 0x82eac /\ (jz = 255 \/ L = 0)) \/
          (pc' = Z_to_bv 64 0x81ec4 /\ jz <> 255 /\ L <> 0 /\ a3' = Z_to_bv 64 (jz + 1))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82d1c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6
    Fr fc m jz L E5 E9 Hj HL.
  apply (evtF_evt rsegs RNG_all). apply (seg_F38_F RNG_all); assumption.
Qed.

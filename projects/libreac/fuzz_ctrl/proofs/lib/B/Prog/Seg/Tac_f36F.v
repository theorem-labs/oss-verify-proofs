(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 1754 of its 1873 lines of code are new or changed and 892 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_f36.v, with its addresses changed; 323 of its 425 lines of code are new or changed and 1771 lines of the source are left out. *)
(* Footprint (ExecF.evtF) twins of the machine runs of lib/B/Prog/Seg/Tac_f36.v (segment F36 of fuzz_ctrl
   LLVMFuzzerTestOneInput, asan-ubsan image B). Bridge input for the cgif-form walk only.
   rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/Tac_f36.v f36_evt_c20, f36_evt_c2c, f36_evt_hit, f36_evt_c24, f36_evt_last,
     f36_evt_next, f36_evt_pre, f36_evt_call, f36_evt_call_ro at a working branch 3803efccea0
     (blob 6c08f44bcc36243b384c97652381360492cd712c);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f36_evt_c20_of_F, f36_evt_c2c_of_F, f36_evt_hit_of_F, f36_evt_c24_of_F, f36_evt_pre_of_F
     (evtF_evt + rng_all) re-derive the source statements verbatim; f36_evt_next_of_F_bounded and
     f36_evt_last_of_F_bounded re-derive them under four added address bounds (the source statement bounds
     neither A + 160 nor the loaded row pointer c), with the shape checks f36_evt_next_of_F_bounded_shape /
     f36_evt_last_of_F_bounded_shape (each hypothesis is the exact type of the matching source lemma);
     f36_evt_call splits into f36_evt_call_pre_F (Tac_f36.v:1689-1691, up to the callee entry) and
     f36_evt_call_post_F (Tac_f36.v:1704-1711, from the return pc 0x82ca0, no step), no _of_F. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag RcMatch RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  asan_stack_malloc_c reac_box_catalogue_match_c reac_ctrl_parse_c reac_ctrl_classify_box_frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_f36.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The StepF twin of Tac_f36.v's f36_sb (one `sb` inside a stack range): same script, StepF `step`, and the goal
   pattern of the footprint form (evtF has four explicit arguments). *)
Ltac f36F_sb lo hi a :=
  match goal with
  | P : f36_SP ?m0 ?mm lo hi |- _ =>
      pose proof (f36_SP_store_ok m0 mm lo hi a P ltac:(lia)) as _ST;
      step;
      match goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mm ?aa ?bs) _) =>
          let P' := fresh "P" in
          pose proof (f36_SP_st m0 mm a bs lo hi ltac:(reflexivity) P ltac:(lia)) as P';
          change (write_to_mem mm aa bs) with (write_to_mem mm (wa a) bs);
          clear P _ST;
          set (write_to_mem mm (wa a) bs) in *
      end
  end.

(* ===================== the runs with no memory access ===================== *)

(* 0x82c84 li s7,0 -> 0x82c88 (Tac_f36.v:2121-2129). No memory access: no rng premise. *)
Lemma f36_evt_c20_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (RNG : footprint),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0)
                             s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c84) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evtF_done. reflexivity. Qed.

Lemma f36_evt_c20_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    LF.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0)
                             s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c84) fc None m (seg_rom rsegs)).
Proof. intros. apply (evtF_evt rsegs RNG_all). apply f36_evt_c20_F. Qed.
Definition f36_evt_c20_src_check : ltac:(let T := type of Tac_f36.f36_evt_c20 in exact T) := f36_evt_c20_of_F.

(* 0x82c90 li s7,0 -> 0x82c94 (Tac_f36.v:2110-2118). No memory access: no rng premise. *)
Lemma f36_evt_c2c_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (RNG : footprint),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0)
                             s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c94) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c90) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evtF_done. reflexivity. Qed.

Lemma f36_evt_c2c_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    LF.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0)
                             s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c94) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c90) fc None m (seg_rom rsegs)).
Proof. intros. apply (evtF_evt rsegs RNG_all). apply f36_evt_c2c_F. Qed.
Definition f36_evt_c2c_src_check : ltac:(let T := type of Tac_f36.f36_evt_c2c in exact T) := f36_evt_c2c_of_F.

(* 0x82c54 beqz a0,82c88 with a0 = 0 (Tac_f36.v:2015-2028): taken. No memory access: no rng premise. *)
Lemma f36_evt_hit_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (RNG : footprint),
    a0 = Z_to_bv 64 0 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                             t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m RNG ->.
  step. try first [if_true | if_false].
  apply evtF_done. reflexivity.
Qed.

Lemma f36_evt_hit_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    LF.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                             t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs)).
Proof. intros. apply (evtF_evt rsegs RNG_all). apply f36_evt_hit_F. assumption. Qed.
Definition f36_evt_hit_src_check : ltac:(let T := type of Tac_f36.f36_evt_hit in exact T) := f36_evt_hit_of_F.

(* ===================== the shadow stores ===================== *)

(* 0x82c88 sb s11,4(s3) ; j 82c94 (Tac_f36.v:2089-2107). Writes the one shadow byte [S3 + 4, S3 + 5). *)
Lemma f36_evt_c24_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 : Z) (RNG : footprint),
    s3 = Z_to_bv 64 S3 -> stk rsegs m (S3 + 4) (S3 + 5) ->
    rng RNG (S3 + 4) 1 ->
    evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
                                         s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    Fr (Z_to_bv 64 0x82c94) fc None m' (seg_rom rsegs) /\
         f36_SP m m' (S3 + 4) (S3 + 5))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m S3 RNG -> HST R4.
  pose proof (f36_SP_refl m (S3 + 4) (S3 + 5) HST) as P0.
  f36F_sb (S3 + 4) (S3 + 5) (S3 + 4).
  step.
  match goal with P : f36_SP m ?mm _ _ |- _ => apply evtF_done; exists mm; split; [reflexivity | exact P] end.
Qed.

Lemma f36_evt_c24_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 : Z),
    s3 = Z_to_bv 64 S3 -> stk rsegs m (S3 + 4) (S3 + 5) ->
    LF.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
                                         s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    Fr (Z_to_bv 64 0x82c94) fc None m' (seg_rom rsegs) /\
         f36_SP m m' (S3 + 4) (S3 + 5))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m S3 E HST.
  pose proof HST as (Hlo & Hhi & _).
  eapply evtF_evt. eapply f36_evt_c24_F; [exact E | exact HST | apply rng_all; lia].
Qed.
Definition f36_evt_c24_src_check : ltac:(let T := type of Tac_f36.f36_evt_c24 in exact T) := f36_evt_c24_of_F.

(* 0x82c38 bnez s8,82c40 (taken) ; 0x82c40-0x82c4c sb s11,8..11(s3) ; 0x82c50 li s6,1 -> 0x82c54
   (Tac_f36.v:1974-2005). Writes the four shadow bytes [S3 + 8, S3 + 12). *)
Lemma f36_evt_pre_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 rw : Z) (RNG : footprint),
    s3 = Z_to_bv 64 S3 -> s8 = Z_to_bv 64 rw -> s11 = Z_to_bv 64 (-8) -> 0 < rw < 2 ^ 64 ->
    stk rsegs m (S3 + 8) (S3 + 12) ->
    rng RNG (S3 + 8) 4 ->
    evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                                         (Z_to_bv 64 1) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    Fr (Z_to_bv 64 0x82c54) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S3 + 8) (S3 + 12) /\
         (forall c cs, bytes_at rsegs m c cs -> (c + Z.of_nat (length cs) <= S3 + 8 \/ S3 + 12 <= c) ->
            bytes_at rsegs m' c cs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c38) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m S3 rw RNG -> -> -> Hrw HST R8.
  (* 0x82c38 bnez s8,82c40: taken *)
  step. rewrite (f36_eqb_lit rw 0) by lia. first [if_true | if_false].
  pose proof (f36_SP_refl m (S3 + 8) (S3 + 12) HST) as P0.
  (* 0x82c40 .. 0x82c4c sb s11,8..11(s3) *)
  f36F_sb (S3 + 8) (S3 + 12) (S3 + 8).
  f36F_sb (S3 + 8) (S3 + 12) (S3 + 9).
  f36F_sb (S3 + 8) (S3 + 12) (S3 + 10).
  f36F_sb (S3 + 8) (S3 + 12) (S3 + 11).
  (* 0x82c50 li s6,1 *)
  match goal with P : f36_SP m ?mm _ _ |- _ =>
    step;
    apply evtF_done; exists mm; split; [reflexivity|];
    destruct P as (MU & WM & HST' & K); split; [exact MU|]; split; [exact WM|]; split; [exact HST' | exact K]
  end.
Qed.

Lemma f36_evt_pre_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 rw : Z),
    s3 = Z_to_bv 64 S3 -> s8 = Z_to_bv 64 rw -> s11 = Z_to_bv 64 (-8) -> 0 < rw < 2 ^ 64 ->
    stk rsegs m (S3 + 8) (S3 + 12) ->
    LF.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                                         (Z_to_bv 64 1) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    Fr (Z_to_bv 64 0x82c54) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S3 + 8) (S3 + 12) /\
         (forall c cs, bytes_at rsegs m c cs -> (c + Z.of_nat (length cs) <= S3 + 8 \/ S3 + 12 <= c) ->
            bytes_at rsegs m' c cs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c38) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m S3 rw E3 E8 E11 Hrw HST.
  pose proof HST as (Hlo & Hhi & _).
  eapply evtF_evt. eapply f36_evt_pre_F; try eassumption. apply rng_all; lia.
Qed.
Definition f36_evt_pre_src_check : ltac:(let T := type of Tac_f36.f36_evt_pre in exact T) := f36_evt_pre_of_F.

(* ===================== the row latch ===================== *)

(* The latch with a0 <> 0: 0x82c54 beqz falls through, 0x82c58 j 82c70, 0x82c70 ld a0,160(s1), 0x82c74 ld a0,0(a0),
   0x82c78 addi s9,s9,1, 0x82c7c addi s7,s7,296, 0x82c80 bltu s9,a0,82be4 taken, then the row head 0x82be4 li a0,296,
   mulh, mul, srai -> 0x82bf4 (Tac_f36.v:2038-2062). Reads [A + 160, A + 168) and [c, c + 8). *)
Lemma f36_evt_next_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z) (i : nat) (RNG : footprint),
    s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 (Z.of_nat i) ->
    s7 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i) -> (i < 10)%nat ->
    ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
    ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
    rng RNG (A + 160) 8 -> rng RNG c 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (CAT_ROW * Z.of_nat (S i)))
                             (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                             (Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat (S i))) s8 (Z_to_bv 64 (Z.of_nat (S i)))
                             s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c i RNG -> H0 -> -> Hi RD160 RDc R160 Rc.
  step. rewrite H0. cbv iota.
  step. step. step. step. step. step.
  rewrite (f36_ltu_lit (Z.of_nat i + 1) 11) by lia. first [if_true | if_false].
  step. step. step. step.
  apply evtF_done.
  do 10 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

(* The source statement of Tac_f36.v:2038-2062 under the two address-range side conditions that rng_all needs
   (the source does not bound A + 160, read by `ld a0,160(s1)` at pc 0x82c70, nor the loaded row pointer c,
   read by `ld a0,0(a0)` at pc 0x82c74). NOT the source statement verbatim: hence the `_bounded` name. *)
Lemma f36_evt_next_of_F_bounded :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z) (i : nat),
    0 <= A + 160 -> A + 168 <= 2 ^ 64 -> 0 <= c -> c + 8 <= 2 ^ 64 ->
    s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 (Z.of_nat i) ->
    s7 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i) -> (i < 10)%nat ->
    ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
    ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
    LF.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (CAT_ROW * Z.of_nat (S i)))
                             (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                             (Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat (S i))) s8 (Z_to_bv 64 (Z.of_nat (S i)))
                             s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c i B1 B2 B3 B4 E1 H0 E9 E7 Hi RD160 RDc.
  eapply evtF_evt. eapply f36_evt_next_F; try eassumption; apply rng_all; lia.
Qed.

(* The auditor's shape check: the hypothesis is the exact statement of Tac_f36.f36_evt_next (feed the source
   lemma to it to discharge the hypothesis), so the added bounds are the only difference. *)
Lemma f36_evt_next_of_F_bounded_shape :
  (forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z) (i : nat),
     s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 (Z.of_nat i) ->
     s7 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i) -> (i < 10)%nat ->
     ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
     ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
     LF.evt rsegs
       (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (CAT_ROW * Z.of_nat (S i)))
                              (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                              (Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat (S i))) s8 (Z_to_bv 64 (Z.of_nat (S i)))
                              s10 s11 t3 t4 t5 t6)
                            Fr (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs))
       (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs))) ->
  (forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z) (i : nat),
     0 <= A + 160 -> A + 168 <= 2 ^ 64 -> 0 <= c -> c + 8 <= 2 ^ 64 ->
     s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 (Z.of_nat i) ->
     s7 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i) -> (i < 10)%nat ->
     ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
     ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
     LF.evt rsegs
       (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (CAT_ROW * Z.of_nat (S i)))
                              (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                              (Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat (S i))) s8 (Z_to_bv 64 (Z.of_nat (S i)))
                              s10 s11 t3 t4 t5 t6)
                            Fr (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs))
       (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs))).
Proof.
  intros H ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c i B1 B2 B3 B4 E1 H0 E9 E7 Hi RD160 RDc.
  eapply H; eassumption.
Qed.


(* i + 1 = 11: 0x82c80 bltu falls through; 0x82c84 li s7,0 -> 0x82c88 (Tac_f36.v:2065-2085).
   Reads [A + 160, A + 168) and [c, c + 8). *)
Lemma f36_evt_last_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z) (RNG : footprint),
    s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 10 ->
    ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
    ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
    rng RNG (A + 160) 8 -> rng RNG c 8 ->
    evtF rsegs RNG
      (fun ms' => exists s7', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                                        s5 s6 (Z_to_bv 64 0) s8 s7' s10 s11 t3 t4 t5 t6)
                                   Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c RNG -> H0 -> RD160 RDc R160 Rc.
  step. rewrite H0. cbv iota.
  step. step. step. step. step. step.
  try first [if_true | if_false].
  step.
  apply evtF_done. eexists. reflexivity.
Qed.

(* The source statement of Tac_f36.v:2065-2085 under the two address-range side conditions that rng_all needs
   (A + 160, read by `ld a0,160(s1)` at pc 0x82c70, and the loaded row pointer c, read by `ld a0,0(a0)` at pc
   0x82c74). NOT the source statement verbatim: hence the `_bounded` name. *)
Lemma f36_evt_last_of_F_bounded :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z),
    0 <= A + 160 -> A + 168 <= 2 ^ 64 -> 0 <= c -> c + 8 <= 2 ^ 64 ->
    s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 10 ->
    ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
    ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
    LF.evt rsegs
      (fun ms' => exists s7', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                                        s5 s6 (Z_to_bv 64 0) s8 s7' s10 s11 t3 t4 t5 t6)
                                   Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c B1 B2 B3 B4 E1 H0 E9 RD160 RDc.
  eapply evtF_evt. eapply f36_evt_last_F; try eassumption; apply rng_all; lia.
Qed.

(* The auditor's shape check for f36_evt_last_of_F_bounded (hypothesis = Tac_f36.f36_evt_last). *)
Lemma f36_evt_last_of_F_bounded_shape :
  (forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z),
     s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 10 ->
     ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
     ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
     LF.evt rsegs
       (fun ms' => exists s7', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                                         s5 s6 (Z_to_bv 64 0) s8 s7' s10 s11 t3 t4 t5 t6)
                                    Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
       (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs))) ->
  (forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z),
     0 <= A + 160 -> A + 168 <= 2 ^ 64 -> 0 <= c -> c + 8 <= 2 ^ 64 ->
     s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 10 ->
     ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
     ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
     LF.evt rsegs
       (fun ms' => exists s7', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                                         s5 s6 (Z_to_bv 64 0) s8 s7' s10 s11 t3 t4 t5 t6)
                                    Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
       (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs))).
Proof.
  intros H ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c B1 B2 B3 B4 E1 H0 E9 RD160 RDc.
  eapply H; eassumption.
Qed.


(* ===================== the catalogue-match call, split at the jal ===================== *)

(* 0x82c94 mv a0,s2 ; 0x82c98 mv a1,s4 ; 0x82c9c jal 0x84e40 <reac_box_catalogue_match>: stops AT the callee
   entry with ra = 0x82ca0 (Tac_f36.v:1689-1691). No memory access, so no rng premise. *)
Lemma f36_evt_call_pre_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (RNG : footprint),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82ca0) sp gp tp t0 t1 t2 s0 s1 s2 s4 a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x84e40) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c94) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m RNG.
  step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* From the return pc 0x82ca0 to the run's exit cut 0x82ca0 (Tac_f36.v:1704-1711): no step.
   The premises are the callee post facts the proved run uses at that point. *)
Lemma f36_evt_call_post_F :
  forall (sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (phi len S FS : Z) (fb : list byte)
         (RNG : footprint),
    munch (f36_W S FS) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - CM_K) S ->
    asan_cells m' -> shadow_rw m' -> addressable m' (S - CM_K) CM_K ->
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
       (reac_box_catalogue_match_D phi len) ->
    evtF rsegs RNG
      (fun ms' => exists (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word)
                         (m'' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82ca0) sp gp tp t0'' t1'' t2'' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82ca0) fc None m'' (seg_rom rsegs) /\
         munch (f36_W S FS) m m'' /\ wmono rsegs m m'' /\ mem_inv rsegs m'' /\ stk rsegs m'' (S - CM_K) S /\
         asan_cells m'' /\ shadow_rw m'' /\ addressable m'' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m'' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR (Z_to_bv 64 0x82ca0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
               a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82ca0) fc None m' (seg_rom rsegs)).
Proof.
  intros sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
    Fr fc m m' phi len S FS fb RNG MU WM MI ST AC SW AD FP.
  apply evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact AC|]. split; [exact SW|]. split; [exact AD | exact FP].
Qed.

(* The ro twin of the call split (Tac_f36.v:1800-1876). The three instructions before the jal touch no memory, so
   the pre stretch is f36_evt_call_pre_F itself; only the post differs (ro_agree in place of mem_inv, and the
   post drops asan_cells). *)
Lemma f36_evt_call_ro_pre_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (RNG : footprint),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82ca0) sp gp tp t0 t1 t2 s0 s1 s2 s4 a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x84e40) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c94) fc None m (seg_rom rsegs)).
Proof. intros. apply f36_evt_call_pre_F. Qed.

Lemma f36_evt_call_ro_post_F :
  forall (sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (phi len S FS : Z) (fb : list byte)
         (RNG : footprint),
    munch (f36_W S FS) m m' -> wmono rsegs m m' -> ro_agree rsegs m' -> stk rsegs m' (S - CM_K) S ->
    shadow_rw m' -> addressable m' (S - CM_K) CM_K ->
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
       (reac_box_catalogue_match_D phi len) ->
    evtF rsegs RNG
      (fun ms' => exists (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word)
                         (m'' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82ca0) sp gp tp t0'' t1'' t2'' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82ca0) fc None m'' (seg_rom rsegs) /\
         munch (f36_W S FS) m m'' /\ wmono rsegs m m'' /\ ro_agree rsegs m'' /\ stk rsegs m'' (S - CM_K) S /\
         shadow_rw m'' /\ addressable m'' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m'' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR (Z_to_bv 64 0x82ca0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
               a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82ca0) fc None m' (seg_rom rsegs)).
Proof.
  intros sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
    Fr fc m m' phi len S FS fb RNG MU WM RO ST SW AD FP.
  apply evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact ST|].
  split; [exact SW|]. split; [exact AD | exact FP].
Qed.

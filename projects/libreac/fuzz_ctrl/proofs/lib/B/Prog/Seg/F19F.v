(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 756 of its 937 lines of code are new or changed and 2376 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F18.v; 70 of its 133 lines of code are new or changed and 874 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F18F.v, with its module names, addresses and numbers changed; 31 of its 85 lines of code are new or changed and 79 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/F19.v f19_evt (:108) at a working branch 3803efccea0
     (blob 6370824fb2234f56af3f03cc74b96e0642b32f20);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f19_evt calls wrapper_bcmp (jal at 0x82664), so it is split: f19_pre_F re-runs F19.v:146-162
     (0x8264c -> the wrapper entry 0x42aac, ra = 0x82668) and f19_post_F re-runs F19.v:194-203 (the return pc
     0x82668 -> the run's end, no step), with the wrapper post facts as premises. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F19.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Local Notation BCMP_WRAP_K := BW.BCMP_WRAP_K.

(* The pre half of f19_evt: 0x8264c bnez a0 (a0 = 0, not taken) ; addi a1,s2,6 ; li a0,7 ;
   bltu a1,a0 (T43, not taken) ; li a2,6 ; ld a0,96(s1) ; jal wrapper_bcmp, stopping at the wrapper entry
   0x42aac with ra = 0x82668.  The only access is the spill word [A + 96, A + 104). *)
Lemma f19_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A L R : Z),
    s1v = Z_to_bv 64 A -> s2v = Z_to_bv 64 R -> a0 = Z_to_bv 64 0 ->
    0 <= L < 2 ^ 64 -> 0 < R -> R + 50 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 L)) ->
    rng RNG (A + 96) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82668) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 L) (Z_to_bv 64 (R + 6)) (Z_to_bv 64 6) a3 a4 a5 a6 a7 (Z_to_bv 64 R)
                               s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x42aac) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8264c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R -> -> -> HLb HR0 HR50 H96 R96.
  assert (HL96 : ov_read_bytes rsegs m (wa (A + 96)) 8 = Some (le8 (Z_to_bv 64 L))).
  { pose proof (bytes_at_ov_read rsegs m (A + 96) (le8 (Z_to_bv 64 L)) 0 8 H96 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in replace cnd with v by (vm_compute; reflexivity); cbv iota
  | _ => idtac
  end.
  step. step. step.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with false;
      [cbv iota | symmetry; apply F19.f19_ltu_false; [lia | rewrite Z.mod_small by lia; lia]]
  end.
  step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* The post half of f19_evt (F19.v:194-203): from the return pc 0x82668 there is no further instruction before
   the run's exit cut, so the post is the wrapper post facts themselves. *)
Lemma f19_post_F :
  forall (RNG : footprint)
         (ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (A R vcmp lo : Z),
    munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
    asan_cells m' -> shadow_rw m' ->
    evtF rsegs RNG
      (fun ms' => exists (ra'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word)
                         (m'' : word -> option byte),
         ms' = MS (mkR ra'' sp gp tp t0'' t1'' t2'' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1'' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 R) s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82668) fc None m'' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m''
         /\ wmono rsegs m m'' /\ mem_inv rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp)
         /\ asan_cells m'' /\ shadow_rw m'')
      (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
               (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 R) s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82668) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra' sp gp tp t0' t1' t2' s0 a1' a2' a3' a4' a5' a6' a7' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
    Fr fc m m' A R vcmp lo MU WM MI ST AC SW.
  apply evtF_done.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact ST|]. split; [exact AC | exact SW].
Qed.

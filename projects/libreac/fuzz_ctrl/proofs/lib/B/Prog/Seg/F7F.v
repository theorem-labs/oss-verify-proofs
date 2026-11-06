(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 554 of its 593 lines of code are new or changed and 357 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F7.v; 14 of its 49 lines of code are new or changed and 558 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17; measured against this image only;
   source runs: lib/B/Prog/Seg/F7.v f7_evt (:353) at a working branch 3803efccea0
     (blob a2221dc0471df2aa6811536e6bde16cca9888dad);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   text start: f7_pre_F taken by path from dba073859bd lib/B/Prog/Seg/F7F.v and re-checked on this source;
   split: f7_evt calls reac_ctrl_kind_name at 0x82170 (parent 23:50Z: split at EVERY call, never state a callee
     contract locally).  f7_pre_F re-runs F7.v lines 386-393 (0x8215c -> the callee entry 0x83d98, ra = 0x82174);
     the callee's return pc 0x82174 IS the run's exit cut (Inv_B82174_at), so the post stretch is empty and no
     f7_post_F exists: the walk composes reac_ctrl_kind_name itself and lands on f7_evt's own Q.
   compare: no <run>_of_F (the source statement f7_evt runs through the callee; the split stretch is cited above). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot F7.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

(* The footprint twin of F7's run 0x8215c -> 0x82170 (up to the reac_ctrl_kind_name entry 0x83d98): the two compares
   not taken, the record pointer reload from the spill [A+280] and the word load through it.
   Regions: [A+280, A+288) read (the record pointer spill), [kp, kp+4) read (the record's kind word). The stretch
   has no instrumented check, so no shadow byte is read. *)
Lemma f7_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A kp v : Z),
    s1 = Z_to_bv 64 A -> bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 kp)) ->
    a0 = Z_to_bv 64 v -> s8v = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
    bytes_at rsegs m kp (le4 (Z_to_bv 64 v)) ->
    rng RNG (A + 280) 8 -> rng RNG kp 4 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82174) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v)
                              a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 0x83d98) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8215c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m A kp v -> H280 -> -> Hv Hkp R280 Rkp.
  assert (HL280 : ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 kp))).
  { pose proof (bytes_at_ov_read rsegs m (A + 280) (le8 (Z_to_bv 64 kp)) 0 8 H280 ltac:(rewrite length_le8; lia))
      as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HLkp : ov_read_bytes rsegs m (wa kp) 4 = Some (le4 (Z_to_bv 64 v))).
  { pose proof (bytes_at_ov_read rsegs m kp (le4 (Z_to_bv 64 v)) 0 4 Hkp ltac:(rewrite length_le4; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le4; lia). exact HH. }
  (* 0x8215c bne a0,s8 : not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x82160 ld a0,280(s1) ; 0x82164 lw a0,0(a0) *)
  step. step. rewrite (f7_sx32_small v Hv).
  (* 0x82168 bne s8,a0 : not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x8216c mv a0,s8 ; 0x82170 jal reac_ctrl_kind_name *)
  step. step.
  apply evtF_done. reflexivity.
Qed.

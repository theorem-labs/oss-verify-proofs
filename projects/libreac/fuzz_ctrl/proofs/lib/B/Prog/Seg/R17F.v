(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 355 of its 391 lines of code are new or changed and 975 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R17.v; 20 of its 62 lines of code are new or changed and 349 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R17.v r17_evt at a working branch 3803efccea0
     (blob e7c3fc62c1847da93e307e57de184c18ae9fcf72);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r17_evt calls reac_ports_parse, so it is split at the call (parent a Theorem Labs lane, binding): the stretch
     r17_pre_F re-runs R17.v:96-111 (0x819a8 up to the reac_ports_parse entry 0x883d0, ra = 0x819d0) and there is
     no post stretch, because the run's exit cut Inv_B819d0_at IS the return pc (R17.v:112-136 is the contract
     application alone). No `_F` steps through a callee and this file states no callee contract. *)
(* rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcDecl RcLeaf RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp RtmB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R17.
(* Last: StepF's step / if_true (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF ExecF_all StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

(* ---- the footprint form of [0x819a8, the reac_ports_parse entry) ---- *)

Lemma r17_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi q mr : Z),
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 mr -> s4v = Z_to_bv 64 phi ->
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= q -> q + 12 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 mr)) ->
    bytes_at rsegs m (A + 120) (le8 (Z_to_bv 64 q)) ->
    rng RNG (A + 272) 8 -> rng RNG (A + 120) 8 ->
    evtF rsegs RNG
      (fun ms' => exists R : bvmap 5 word,
         ms' = MS R Fr (Z_to_bv 64 REAC_PORTS_PARSE) fc None m (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x819d0 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\
         getr R 11 = Z_to_bv 64 q /\ getr R 18 = Z_to_bv 64 (phi + 18) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1v /\
         getr R 19 = s3 /\ getr R 20 = s4v /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x819a8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A phi q mr -> -> -> HA0 HAb Hphi0 Hphi50 Hq0 Hqb R272 R120 Rg272 Rg120.
  pose proof (rh_rdn m (A + 272) (le8 (Z_to_bv 64 mr)) 8 R272 ltac:(apply length_le8)) as RD272.
  pose proof (rh_rdn m (A + 120) (le8 (Z_to_bv 64 q)) 8 R120 ltac:(apply length_le8)) as RD120.
  step.                                         (* 819a8 ld a1,272(s1) : a1 := mr *)
  step. if_true_by (R17.r17_eqb_refl (Z_to_bv 64 mr)).   (* 819ac beq a0,a1 : taken *)
  step.                                         (* 819b4 li a0,-18 *)
  step.                                         (* 819b8 bltu s4,a0 : taken, the trap 819bc not reached *)
  first [ if_true_by (R17.r17_ltu phi Hphi0 Hphi50)
        | lazymatch goal with
          | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
              replace c with true;
                [ cbv iota
                | symmetry; unfold bv_ltu; rewrite !MState.unsigned_lit_wrap; apply Z.ltb_lt;
                  Z.div_mod_to_equations; lia ]
          end ].
  step.                                         (* 819c0 addi s2,s4,18 *)
  step.                                         (* 819c4 mv a0,s2 *)
  step.                                         (* 819c8 ld a1,120(s1) : a1 := q *)
  step.                                         (* 819cc jal reac_ports_parse *)
  apply evtF_done. eexists. split; [reflexivity|].
  do 17 (split; [first [ reflexivity | f_equal; lia ]|]). first [ reflexivity | f_equal; lia ].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its module names, addresses and numbers changed; 141 of its 255 lines of code are new or changed and 816 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P2.v; 42 of its 78 lines of code are new or changed and 219 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P2.v p2_evt at a working branch 3803efccea0
     (blob d84d761a5b901110c6bbcfc966fb5eb9fae0b030);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p2_evt_of_F (evtF_evt + rng_all) re-derives the source statement; p2_evt_same checks that its
     statement is the one of P2.p2_evt. *)
(* rule 24: no function proved. *)
(* The footprint twin of P2's run [0x81ca8, 0x81cb0): sb s2,332(s3) (one byte to the frame-shadow byte Sh + 332)
   and ld s8,56(s1) (the code-byte pointer at Ab + 56).  Two accesses, no instrumented check, no call. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Tac_bp.bp_fix matches [evt] (3 arguments); the [evtF] goal has 4.  Same hook over evtF. *)
Ltac bp_fixF :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      first [rewrite (bp_le1_lit z) by lia | rewrite (bp_le1 (Z_to_bv 64 z))]; mem_after_store
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (bp_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac bp_sbF := step; bp_fixF.

(* ---- the run: sb s2,332(s3); ld s8,56(s1) ---- *)
Lemma p2_evt_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab v : Z) (xb : byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    0 <= Sh -> Sh + 392 <= Ab -> Ab + 64 <= 2 ^ 64 ->
    rw_cells rsegs m (Sh + 332) [C1 xb] -> ro_cells rsegs m (Ab + 56) [C8 (Z_to_bv 64 v)] ->
    rng RNG (Sh + 332) 1 -> rng RNG (Ab + 56) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81cb0) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 24 = Z_to_bv 64 v /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 332, Sh + 333)] m m' /\ wmono rsegs m m' /\
         exists b, mrd rsegs m' (wa (Sh + 332)) = Some b)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ca8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab v xb -> -> HS0 HSA HA64 CH RO GS GA.
  pose proof (rw_cells_bound rsegs m (Sh + 332) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(Sh + 332, Sh + 333)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  bp_sbF.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  apply (bp_ba_rd m1 (Sh + 332) _ (Sh + 332) HbC). cbn [length Z.of_nat Pos.of_succ_nat]. lia.
Qed.

(* The compare lemma: the source statement of P2.p2_evt, re-derived from p2_evt_F at RNG_all. *)
Lemma p2_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab v : Z) (xb : byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    0 <= Sh -> Sh + 392 <= Ab -> Ab + 64 <= 2 ^ 64 ->
    rw_cells rsegs m (Sh + 332) [C1 xb] -> ro_cells rsegs m (Ab + 56) [C8 (Z_to_bv 64 v)] ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81cb0) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 24 = Z_to_bv 64 v /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 332, Sh + 333)] m m' /\ wmono rsegs m m' /\
         exists b, mrd rsegs m' (wa (Sh + 332)) = Some b)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ca8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab v xb E3 E1 HS0 HSA HA64 CH RO.
  apply (evtF_evt rsegs RNG_all).
  apply p2_evt_F with (Sh := Sh) (Ab := Ab) (v := v) (xb := xb); try assumption;
    apply rng_all; lia.
Qed.

(* p2_evt_of_F has exactly the statement of the source lemma P2.p2_evt. *)
Definition p2_evt_same : ltac:(let T := type of P2.p2_evt in exact T) := p2_evt_of_F.

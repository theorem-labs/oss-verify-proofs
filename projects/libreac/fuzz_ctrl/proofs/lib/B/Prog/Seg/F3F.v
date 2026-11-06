(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names and numbers changed; 184 of its 206 lines of code are new or changed and 374 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F3.v; 25 of its 74 lines of code are new or changed and 157 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F3.v f3_head at a working branch 3803efccea0
     (blob cf3727f5291d15f41f47c59024825202a3688221);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f3_head_of_F (evtF_evt + rng_all) re-derives the source statement. *)
(* rule 24: no function proved. *)
(* The run 0x81f78 -> 0x81f94 / 0x82020 touches no memory (li a0,50 / bltu s4,a0 / bnez s2 / li a0,-18 /
   bltu s2,a0): instruction fetch is not an access, so f3_head_F carries no rng premise. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F3.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- the footprint twin of F3.f3_head (F3.v:26-75) ---- *)
Lemma f3_head_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (N phi : Z),
    0 <= N < 2 ^ 64 -> 0 < phi -> phi + 50 <= 2 ^ 64 ->
    evtF rsegs RNG
      (fun ms' => exists a0' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 phi) s3 (Z_to_bv 64 N) s5 s6
                       s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if N <? 50 then 0x82020 else 0x81f94)) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 phi) s3 (Z_to_bv 64 N) s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f78) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m N phi
    HN Hphi0 Hphi1.
  (* 0x81f78 li a0,50 ; 0x81f7c bltu s4,a0 *)
  step. step.
  lazymatch goal with
  | |- context [bv_ltu (Z_to_bv 64 N) ?c] =>
      let u := eval vm_compute in (bv_unsigned c) in
      assert (Ec : bv_ltu (Z_to_bv 64 N) c = (N <? u))
        by (unfold bv_ltu; rewrite (MState.unsigned_lit N) by lia; change (bv_unsigned c) with u; reflexivity)
  end.
  rewrite Ec. destruct (Z.ltb_spec N 50) as [Hlt|Hge]; cbv iota.
  - apply evtF_done. eexists. reflexivity.
  - (* 0x81f80 bnez s2 (taken) *)
    step.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        let E := fresh "E" in
        assert (E : c = true)
          by (rewrite (bv_eqb_lit phi 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; lia);
        rewrite E; cbv iota; clear E
    end.
    (* 0x81f88 li a0,-18 ; 0x81f8c bltu s2,a0 (taken) *)
    step. step.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        lazymatch c with
        | bv_ltu (Z_to_bv 64 phi) ?d =>
            let u := eval vm_compute in (bv_unsigned d) in
            let E := fresh "E" in
            assert (E : c = true)
              by (unfold bv_ltu; rewrite (MState.unsigned_lit phi) by lia; change (bv_unsigned d) with u;
                  apply Z.ltb_lt; lia);
            rewrite E; cbv iota; clear E
        end
    end.
    apply evtF_done. eexists. reflexivity.
Qed.

(* ---- the compare lemma: the source statement of F3.f3_head, re-derived from f3_head_F ---- *)
Lemma f3_head_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (N phi : Z),
    0 <= N < 2 ^ 64 -> 0 < phi -> phi + 50 <= 2 ^ 64 ->
    evt rsegs
      (fun ms' => exists a0' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 phi) s3 (Z_to_bv 64 N) s5 s6
                       s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if N <? 50 then 0x82020 else 0x81f94)) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 phi) s3 (Z_to_bv 64 N) s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f78) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all). apply f3_head_F; assumption.
Qed.
Definition f3_head_src_check : ltac:(let T := type of F3.f3_head in exact T) := f3_head_of_F.

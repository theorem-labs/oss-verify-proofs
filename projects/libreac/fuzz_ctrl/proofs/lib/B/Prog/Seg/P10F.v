(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names and numbers changed; 147 of its 169 lines of code are new or changed and 374 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P10.v; 57 of its 107 lines of code are new or changed and 119 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P10.v p10_evt at a working branch 3803efccea0
     (blob f615c6bb3a285fcf1fb97cc494a9ed3c0c8103dc);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p10_evt_of_F composes p10_pre_F, the caller's reac_ports_unknown_contract premise and p10_post_F
     and re-derives the source statement of P10.p10_evt verbatim; p10_evt_same checks that type against
     P10.p10_evt.  p10_pre_F re-runs P10.v lines 56-60 (0x81dd4 .. 0x81de4, up to the callee entry),
     p10_post_F lines 71-79 (the return pc 0x81de8, no instruction left in the stretch). *)
(* rule 24: no function proved. *)
(* The footprint twin of P10's run [0x81dd4, 0x81de8), split at the call (parent ruling: every call splits):
     beq a0,s2 (taken); li a0,0; mv a1,s8; jal reac_ports_unknown -> p10_pre_F, stops AT the callee entry
     0x88628 with ra = 0x81de8; those four instructions touch no memory, so p10_pre_F needs no rng premise.
     p10_post_F is the return pc 0x81de8, no step left. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P10.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- 0x81dd4 .. 0x81de4: beq (taken); li a0,0; mv a1,s8; jal reac_ports_unknown ---- *)
Lemma p10_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Cc : Z),
    a0 = Z_to_bv 64 (-1) -> s2 = Z_to_bv 64 (-1) -> s8 = Z_to_bv 64 Cc ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81de8) sp gp tp t0 t1 t2 s0 s1
                                (Z_to_bv 64 0) (Z_to_bv 64 Cc) a2 a3 a4 a5 a6 a7
                                (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 (Z_to_bv 64 Cc) s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x88628) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81dd4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Cc -> -> ->.
  step. (* 0x81dd4 beq a0,s2,0x81ddc *)
  if_true.
  step. (* 0x81ddc li a0,0 *)
  step. (* 0x81de0 mv a1,s8 *)
  step. (* 0x81de4 jal reac_ports_unknown *)
  apply evtF_done. reflexivity.
Qed.

(* ---- the return pc 0x81de8: the premises are the callee post facts P10's proof uses ---- *)
Lemma p10_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s8 s9 s10 : word) (S Cc : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 ->
    getr R 10 = Z_to_bv 64 (-1) ->
    munch [(S - 16, S); (Cc, Cc + 1)] m m' -> wmono rsegs m m' -> stk rsegs m' (S - 16) S ->
    bytes_at rsegs m' Cc [Z_to_bv 8 0] ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81de8) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\ getr R' 26 = s10 /\
         getr R' 10 = Z_to_bv 64 (-1) /\
         munch [(S - 16, S); (Cc, Cc + 1)] m m'' /\ wmono rsegs m m'' /\ stk rsegs m'' (S - 16) S /\
         bytes_at rsegs m'' Cc [Z_to_bv 8 0])
      (MS R F (Z_to_bv 64 0x81de8) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m' sp gp tp s0 s1 s3 s7 s8 s9 s10 S Cc
    K2 K3 K4 K8 K9 K19 K23 K24 K25 K26 K10 MU WM ST HB.
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K23|]. split; [exact K24|]. split; [exact K25|]. split; [exact K26|].
  split; [exact K10|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST | exact HB].
Qed.

(* ---- the compare lemma: the source statement of P10.p10_evt ---- *)
Lemma p10_evt_of_F : reac_ports_unknown_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Cc : Z),
    sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (-1) -> s2 = Z_to_bv 64 (-1) -> s8 = Z_to_bv 64 Cc ->
    16 <= S < 2 ^ 64 -> 0 < Cc < 2 ^ 64 ->
    stk rsegs m (S - 16) S -> wr_at rsegs m Cc 1 -> (Cc + 1 <= S - 16 \/ S <= Cc) ->
    asan_cells m -> shadow_rw m -> addressable m Cc 1 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(S - 16, S); (Cc, Cc + 1)] x) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81de8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (-1) /\
         munch [(S - 16, S); (Cc, Cc + 1)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S - 16) S /\
         bytes_at rsegs m' Cc [Z_to_bv 8 0])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81dd4) fc None m (seg_rom rsegs)).
Proof.
  intros PU ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S Cc -> -> -> -> HS HC0 HST HWR HSEP HAC HSW HAD HOUT.
  pose proof PU as HC. unfold reac_ports_unknown_contract, REAC_PORTS_UNKNOWN in HC.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 Cc) = Cc) by (apply MState.unsigned_lit; lia).
  assert (ECz : (Cc =? 0) = false) by (apply Z.eqb_neq; lia).
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all). apply p10_pre_F with (Cc := Cc); reflexivity. }
  intros ms' ->.
  eapply evt_cut.
  { eapply HC with (p := 0) (c := Cc) (lo := S - 16) (bs := @nil byte).
    all: unfold reac_ports_unknown_W, REAC_PORTS_UNKNOWN_FRAME.
    all: rewrite ?EU, ?EC, ?ECz.
    all: try reflexivity.
    all: try assumption.
    all: try (intros HH; exfalso; apply HH; reflexivity).
    all: try (intros _; split; [assumption | split; [intros HH; exfalso; apply HH; reflexivity | lia]]).
    all: try (intros _; assumption).
    all: lia. }
  intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & m' & E & MU & WM & ST' & _ & HB).
  subst ms'.
  unfold reac_ports_unknown_W, REAC_PORTS_UNKNOWN_FRAME in MU. rewrite EU, ECz in MU. rewrite EU in ST'.
  pose proof (HB ltac:(lia)) as HB0. rewrite P10.p10_nok in HB0.
  replace (ret_pc (Z_to_bv 64 0x81de8)) with (Z_to_bv 64 0x81de8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p10_post_F with (m := m) (S := S) (Cc := Cc); try reflexivity; assumption.
Qed.

(* p10_evt_of_F has exactly the statement of the source lemma P10.p10_evt. *)
Definition p10_evt_same : ltac:(let T := type of P10.p10_evt in exact T) := p10_evt_of_F.

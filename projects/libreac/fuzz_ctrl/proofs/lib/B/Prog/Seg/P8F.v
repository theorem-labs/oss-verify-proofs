(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 123 of its 143 lines of code are new or changed and 376 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P8.v; 60 of its 103 lines of code are new or changed and 100 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P8.v p8_evt at a working branch 3803efccea0
     (blob 32bfb16a8ea1aa6b5054822a65fad561cdf0e5d1);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p8_evt_of_F composes p8_pre_F, the caller's reac_ports_parse_contract premise and p8_post_F and
     re-derives the source statement of P8.p8_evt verbatim; p8_evt_same checks that type against P8.p8_evt.
     p8_pre_F re-runs P8.v lines 51-55 (0x81da8 .. 0x81db8, up to the callee entry), p8_post_F lines 64-72
     (the return pc 0x81dbc, no instruction left in the stretch). *)
(* rule 24: no function proved. *)
(* The footprint twin of P8's run [0x81da8, 0x81dbc), split at the call (parent ruling: every call splits):
     beq a0,s2 (taken); ld a0,64(s1); li a1,0; jal reac_ports_parse  -> p8_pre_F, stops AT the callee entry
     0x883d0 with ra = 0x81dbc;
     the return pc 0x81dbc                                           -> p8_post_F, no step left.
   No _F lemma steps through the callee and this file states no callee contract. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P8.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- 0x81da8 .. 0x81db8: beq (taken); ld a0,64(s1); li a1,0; jal reac_ports_parse ---- *)
Lemma p8_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab p : Z),
    s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 (-1) -> s2 = Z_to_bv 64 (-1) ->
    0 <= p < 2 ^ 64 -> 0 <= Ab -> Ab + 80 <= 2 ^ 64 ->
    ro_cells rsegs m (Ab + 64) [C8 (Z_to_bv 64 p)] ->
    rng RNG (Ab + 64) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81dbc) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab)
                                (Z_to_bv 64 p) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x883d0) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab p -> -> -> Hp HA0 HA64 RO64 GA.
  step. (* 0x81da8 beq a0,s2,0x81db0 *)
  if_true.
  step. (* 0x81db0 ld a0,64(s1) *)
  step. (* 0x81db4 li a1,0 *)
  step. (* 0x81db8 jal reac_ports_parse *)
  apply evtF_done. reflexivity.
Qed.

(* ---- the return pc 0x81dbc: the run ends there; the premises are the callee post facts P8's proof uses ---- *)
Lemma p8_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s8 s9 s10 : word) (S : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 ->
    getr R 10 = Z_to_bv 64 (-1) ->
    munch [(S - 16, S)] m m' -> wmono rsegs m m' -> stk rsegs m' (S - 16) S ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81dbc) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\ getr R' 26 = s10 /\
         getr R' 10 = Z_to_bv 64 (-1) /\
         munch [(S - 16, S)] m m'' /\ wmono rsegs m m'' /\ stk rsegs m'' (S - 16) S)
      (MS R F (Z_to_bv 64 0x81dbc) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m' sp gp tp s0 s1 s3 s7 s8 s9 s10 S
    K2 K3 K4 K8 K9 K19 K23 K24 K25 K26 K10 MU WM ST.
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K23|]. split; [exact K24|]. split; [exact K25|]. split; [exact K26|].
  split; [exact K10|]. split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* ---- the compare lemma: the source statement of P8.p8_evt, out of the two stretches and the caller's own
       reac_ports_parse_contract premise (the proved run's callee step, unchanged) ---- *)
Lemma p8_evt_of_F : reac_ports_parse_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Ab p : Z),
    sp = Z_to_bv 64 S -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 (-1) -> s2 = Z_to_bv 64 (-1) ->
    0 <= p < 2 ^ 64 -> 0 <= Ab -> Ab + 80 <= 2 ^ 64 -> 16 <= S < 2 ^ 64 ->
    ro_cells rsegs m (Ab + 64) [C8 (Z_to_bv 64 p)] ->
    stk rsegs m (S - 16) S ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81dbc) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (-1) /\
         munch [(S - 16, S)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S - 16) S)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da8) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S Ab p -> -> -> -> Hp HA0 HA64 HS RO64 HST.
  pose proof PP as HC. unfold reac_ports_parse_contract, REAC_PORTS_PARSE in HC.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply p8_pre_F with (Ab := Ab) (p := p); try assumption; try reflexivity.
    apply rng_all; lia. }
  intros ms' ->.
  eapply evt_cut.
  { eapply HC with (p := p) (q := 0) (lo := S - 16) (bs := @nil byte).
    all: rewrite ?EU.
    all: try reflexivity.
    all: try assumption.
    all: try (intros _ HH; exfalso; apply HH; reflexivity).
    all: try (unfold REAC_PORTS_PARSE_FRAME; lia).
    all: lia. }
  intros ms' PO. unfold reac_ports_parse_post in PO.
  destruct PO as (t0' & t1' & t2' & t3' & t4' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' &
                  E & WM & _ & ST' & HP).
  subst ms'. rewrite P8.p8_nok in HP |- *. rewrite EU in HP, ST'. unfold REAC_PORTS_PARSE_FRAME in HP.
  replace (ret_pc (Z_to_bv 64 0x81dbc)) with (Z_to_bv 64 0x81dbc)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p8_post_F with (m := m) (S := S); try reflexivity; assumption.
Qed.

(* p8_evt_of_F has exactly the statement of the source lemma P8.p8_evt. *)
Definition p8_evt_same : ltac:(let T := type of P8.p8_evt in exact T) := p8_evt_of_F.

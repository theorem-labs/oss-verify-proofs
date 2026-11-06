(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 114 of its 134 lines of code are new or changed and 376 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P9.v; 55 of its 96 lines of code are new or changed and 93 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P9.v p9_evt at a working branch 3803efccea0
     (blob 1722ad5cfbb3dd226b4d5abc5dacbd03bb3d2695);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p9_evt_of_F composes p9_pre_F, the caller's reac_ports_parse_contract premise and p9_post_F and
     re-derives the source statement of P9.p9_evt verbatim; p9_evt_same checks that type against P9.p9_evt.
     p9_pre_F re-runs P9.v lines 48-52 (0x81dbc .. 0x81dd0, up to the callee entry), p9_post_F lines 61-69
     (the return pc 0x81dd4, no instruction left in the stretch). *)
(* rule 24: no function proved. *)
(* The footprint twin of P9's run [0x81dbc, 0x81dd4), split at the call (parent ruling: every call splits):
     li s2,-1; beq a0,s2 (taken); li a0,0; li a1,0; jal reac_ports_parse -> p9_pre_F, stops AT the callee
     entry 0x883d0 with ra = 0x81dd4; those five instructions touch no memory, so p9_pre_F needs no rng
     premise.  p9_post_F is the return pc 0x81dd4, no step left. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P9.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- 0x81dbc .. 0x81dd0: li s2,-1; beq (taken); li a0,0; li a1,0; jal reac_ports_parse ---- *)
Lemma p9_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 (-1) ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81dd4) sp gp tp t0 t1 t2 s0 s1
                                (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x883d0) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81dbc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step. (* 0x81dbc li s2,-1 *)
  step. (* 0x81dc0 beq a0,s2,0x81dc8 *)
  if_true.
  step. step. (* 0x81dc8 li a0,0; 0x81dcc li a1,0 *)
  step. (* 0x81dd0 jal reac_ports_parse *)
  apply evtF_done. reflexivity.
Qed.

(* ---- the return pc 0x81dd4: the premises are the callee post facts P9's proof uses ---- *)
Lemma p9_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s8 s9 s10 : word) (S : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 ->
    getr R 10 = Z_to_bv 64 (-1) -> getr R 18 = Z_to_bv 64 (-1) ->
    munch [(S - 16, S)] m m' -> wmono rsegs m m' -> stk rsegs m' (S - 16) S ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81dd4) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\ getr R' 26 = s10 /\
         getr R' 10 = Z_to_bv 64 (-1) /\ getr R' 18 = Z_to_bv 64 (-1) /\
         munch [(S - 16, S)] m m'' /\ wmono rsegs m m'' /\ stk rsegs m'' (S - 16) S)
      (MS R F (Z_to_bv 64 0x81dd4) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m' sp gp tp s0 s1 s3 s7 s8 s9 s10 S
    K2 K3 K4 K8 K9 K19 K23 K24 K25 K26 K10 K18 MU WM ST.
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K23|]. split; [exact K24|]. split; [exact K25|]. split; [exact K26|].
  split; [exact K10|]. split; [exact K18|]. split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* ---- the compare lemma: the source statement of P9.p9_evt ---- *)
Lemma p9_evt_of_F : reac_ports_parse_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
    sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (-1) -> 16 <= S < 2 ^ 64 ->
    stk rsegs m (S - 16) S ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81dd4) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (-1) /\ getr R 18 = Z_to_bv 64 (-1) /\
         munch [(S - 16, S)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S - 16) S)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81dbc) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S -> -> HS HST.
  pose proof PP as HC. unfold reac_ports_parse_contract, REAC_PORTS_PARSE in HC.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all). apply p9_pre_F. reflexivity. }
  intros ms' ->.
  eapply evt_cut.
  { eapply HC with (p := 0) (q := 0) (lo := S - 16) (bs := @nil byte).
    all: rewrite ?EU.
    all: try reflexivity.
    all: try assumption.
    all: try (intros HH; exfalso; apply HH; reflexivity).
    all: try (unfold REAC_PORTS_PARSE_FRAME; lia).
    all: lia. }
  intros ms' PO. unfold reac_ports_parse_post in PO.
  destruct PO as (t0' & t1' & t2' & t3' & t4' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' &
                  E & WM & _ & ST' & HP).
  subst ms'. rewrite P9.p9_nok in HP |- *. rewrite EU in HP, ST'. unfold REAC_PORTS_PARSE_FRAME in HP.
  replace (ret_pc (Z_to_bv 64 0x81dd4)) with (Z_to_bv 64 0x81dd4)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p9_post_F with (m := m) (S := S); try reflexivity; assumption.
Qed.

(* p9_evt_of_F has exactly the statement of the source lemma P9.p9_evt. *)
Definition p9_evt_same : ltac:(let T := type of P9.p9_evt in exact T) := p9_evt_of_F.

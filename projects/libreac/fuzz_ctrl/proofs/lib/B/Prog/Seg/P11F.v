(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 190 of its 216 lines of code are new or changed and 370 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P11.v; 66 of its 111 lines of code are new or changed and 171 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P11.v p11_evt at a working branch 3803efccea0
     (blob b8f0598ab1abbd4c65343d4c1517daf3084c90c9);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p11_evt_of_F composes p11_pre_F, the caller's reac_ctrl_kind_name_contract premise and
     p11_post_F and re-derives the source statement of P11.p11_evt verbatim; p11_evt_same checks that type
     against P11.p11_evt.  p11_pre_F re-runs P11.v lines 63-70 (0x81de8 .. 0x81e04, up to the callee entry),
     p11_post_F lines 77-86 (the return pc 0x81e08, no instruction left in the stretch). *)
(* rule 24: no function proved. *)
(* The footprint twin of P11's run [0x81de8, 0x81e08), split at the call (parent ruling: every call splits):
     li a1,-1; beq a0,a1 (taken); lbu a0,0(s8); beqz (taken); li a0,14; jal reac_ctrl_kind_name
       -> p11_pre_F, stops AT the callee entry 0x83d98 with ra = 0x81e08.
     The one access of the stretch is the code byte at Cc read by the lbu, so the one rng premise is
     rng RNG Cc 1; the byte is in application memory and carries no instrumented check here.
     p11_post_F is the return pc 0x81e08, no step left. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- 0x81de8 .. 0x81e04: li a1,-1; beq (taken); lbu a0,0(s8); beqz (taken); li a0,14; jal ---- *)
Lemma p11_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Cc : Z),
    a0 = Z_to_bv 64 (-1) -> s8 = Z_to_bv 64 Cc ->
    0 <= Cc -> Cc + 1 <= 2 ^ 64 ->
    bytes_at rsegs m Cc [Z_to_bv 8 0] ->
    rng RNG Cc 1 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81e08) sp gp tp t0 t1 t2 s0 s1
                                (Z_to_bv 64 14) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 (Z_to_bv 64 Cc) s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x83d98) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81de8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Cc -> -> HC0 HC1 Hcb GC.
  pose proof (bytes_at_ov_read rsegs m Cc [Z_to_bv 8 0] 0 1 Hcb ltac:(cbn; lia)) as HR.
  cbn [Z.of_nat firstn skipn] in HR. rewrite Z.add_0_r in HR.
  step. (* 0x81de8 li a1,-1 *)
  step. (* 0x81dec beq a0,a1,0x81df4 *)
  if_true.
  step. (* 0x81df4 lbu a0,0(s8) *)
  step. (* 0x81df8 beqz a0,0x81e00 *)
  if_true.
  step. (* 0x81e00 li a0,14 *)
  step. (* 0x81e04 jal reac_ctrl_kind_name *)
  apply evtF_done. reflexivity.
Qed.

(* ---- the return pc 0x81e08: the premises are the callee post facts P11's proof uses ---- *)
Lemma p11_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s8 s9 s10 : word) (S : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 ->
    getr R 10 = Z_to_bv 64 QMARK ->
    munch [(S - 16, S)] m m' -> wmono rsegs m m' -> stk rsegs m' (S - 16) S ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81e08) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\ getr R' 26 = s10 /\
         getr R' 10 = Z_to_bv 64 QMARK /\
         munch [(S - 16, S)] m m'' /\ wmono rsegs m m'' /\ stk rsegs m'' (S - 16) S)
      (MS R F (Z_to_bv 64 0x81e08) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m' sp gp tp s0 s1 s3 s7 s8 s9 s10 S
    K2 K3 K4 K8 K9 K19 K23 K24 K25 K26 K10 MU WM ST.
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K23|]. split; [exact K24|]. split; [exact K25|]. split; [exact K26|].
  split; [exact K10|]. split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* ---- the compare lemma: the source statement of P11.p11_evt ---- *)
Lemma p11_evt_of_F : reac_ctrl_kind_name_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Cc : Z),
    sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (-1) -> s8 = Z_to_bv 64 Cc ->
    16 <= S < 2 ^ 64 -> 0 <= Cc -> Cc + 1 <= 2 ^ 64 ->
    bytes_at rsegs m Cc [Z_to_bv 8 0] ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m (S - 16) S -> KIND_NAME + 112 <= S - 16 ->
    asan_cells m -> shadow_rw m -> addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(S - 16, S)] x) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81e08) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 QMARK /\
         munch [(S - 16, S)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S - 16) S)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81de8) fc None m (seg_rom rsegs)).
Proof.
  intros KN ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S Cc -> -> -> HS HC0 HC1 Hcb HT HSTR HST Hlo HAC HSW HAD HOUT.
  pose proof KN as HC. unfold reac_ctrl_kind_name_contract, REAC_CTRL_KIND_NAME in HC.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply p11_pre_F with (Cc := Cc); try assumption; try reflexivity.
    apply rng_all; lia. }
  intros ms' ->.
  eapply evt_cut.
  { eapply HC with (lo := S - 16).
    all: unfold REAC_CTRL_KIND_NAME_FRAME.
    all: rewrite ?EU.
    all: try assumption.
    all: lia. }
  intros ms' (a1' & a2' & a3' & m' & E & MU & WM & _ & ST' & _).
  subst ms'. unfold REAC_CTRL_KIND_NAME_FRAME in MU, ST'. rewrite EU in MU, ST'.
  replace (ret_pc (Z_to_bv 64 0x81e08)) with (Z_to_bv 64 0x81e08)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p11_post_F with (m := m) (S := S); try reflexivity; try assumption.
  all: first [ reflexivity
             | rewrite (MState.unsigned_lit 14) by lia; rewrite (P11.p11_addr_big 14) by lia; reflexivity ].
Qed.

(* p11_evt_of_F has exactly the statement of the source lemma P11.p11_evt. *)
Definition p11_evt_same : ltac:(let T := type of P11.p11_evt in exact T) := p11_evt_of_F.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 193 of its 213 lines of code are new or changed and 376 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P7.v; 67 of its 122 lines of code are new or changed and 158 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P7.v p7_evt at a working branch 3803efccea0
     (blob d62a9469a6e1fc3b750cafa2cc39a743825452f7);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p7_evt_of_F composes p7_pre_F, the caller's reac_ctrl_identity_fragment_contract premise and
     p7_post_F and re-derives the source statement of P7.p7_evt verbatim; p7_evt_same checks that type
     against P7.p7_evt.  p7_pre_F re-runs P7.v lines 64-70 (0x81d80 .. 0x81da4, up to the callee entry),
     p7_post_F lines 79-88 (the return pc 0x81da8, no instruction left in the stretch). *)
(* rule 24: no function proved. *)
(* The footprint twin of P7's run [0x81d80, 0x81da8), split at the call (parent ruling: every call splits):
     li s2,-1; beq a0,s2 (taken); ld a0,208(s1); li a1,0; li a2,0; ld a3,88(s1); ld a4,80(s1); ld a5,72(s1);
     jal reac_ctrl_identity_fragment -> p7_pre_F, stops AT the callee entry 0x859e4 with ra = 0x81da8.
   The accesses of the stretch are the four spilled record pointers [Ab + 208], [Ab + 88], [Ab + 80],
   [Ab + 72], 8 bytes each, with no instrumented check.  p7_post_F is the return pc 0x81da8, no step left. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P7.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- 0x81d80 .. 0x81da4: li s2,-1; beq (taken); the four loads and two li; jal ---- *)
Lemma p7_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab f pa pp pn : Z),
    s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 (-1) ->
    0 <= f < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    0 <= Ab -> Ab + 248 <= 2 ^ 64 ->
    ro_cells rsegs m (Ab + 208) [C8 (Z_to_bv 64 f)] ->
    ro_cells rsegs m (Ab + 88) [C8 (Z_to_bv 64 pa)] ->
    ro_cells rsegs m (Ab + 80) [C8 (Z_to_bv 64 pp)] ->
    ro_cells rsegs m (Ab + 72) [C8 (Z_to_bv 64 pn)] ->
    rng RNG (Ab + 208) 8 -> rng RNG (Ab + 88) 8 -> rng RNG (Ab + 80) 8 -> rng RNG (Ab + 72) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81da8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab)
                                (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a6 a7
                                (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x859e4) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d80) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab f pa pp pn -> -> Hf Hpa Hpp Hpn HA0 HA64 RO208 RO88 RO80 RO72 G208 G88 G80 G72.
  step. (* 0x81d80 li s2,-1 *)
  step. (* 0x81d84 beq a0,s2,0x81d8c *)
  if_true.
  step. (* 0x81d8c ld a0,208(s1) *)
  step. step. (* li a1,0; li a2,0 *)
  step. step. step. (* ld a3,88(s1); ld a4,80(s1); ld a5,72(s1) *)
  step. (* 0x81da4 jal reac_ctrl_identity_fragment *)
  apply evtF_done. reflexivity.
Qed.

(* ---- the return pc 0x81da8: the premises are the callee post facts P7's proof uses ---- *)
Lemma p7_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s8 s9 s10 : word) (S : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 ->
    getr R 10 = Z_to_bv 64 (-1) -> getr R 18 = Z_to_bv 64 (-1) ->
    munch [(S - 4672, S)] m m' -> wmono rsegs m m' -> stk rsegs m' (S - 4672) S ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81da8) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\ getr R' 26 = s10 /\
         getr R' 10 = Z_to_bv 64 (-1) /\ getr R' 18 = Z_to_bv 64 (-1) /\
         munch [(S - 4672, S)] m m'' /\ wmono rsegs m m'' /\ stk rsegs m'' (S - 4672) S)
      (MS R F (Z_to_bv 64 0x81da8) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m' sp gp tp s0 s1 s3 s7 s8 s9 s10 S
    K2 K3 K4 K8 K9 K19 K23 K24 K25 K26 K10 K18 MU WM ST.
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K23|]. split; [exact K24|]. split; [exact K25|]. split; [exact K26|].
  split; [exact K10|]. split; [exact K18|]. split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* ---- the compare lemma: the source statement of P7.p7_evt ---- *)
Lemma p7_evt_of_F : reac_ctrl_identity_fragment_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Ab f pa pp pn : Z),
    sp = Z_to_bv 64 S -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 (-1) ->
    0 <= f < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    0 <= Ab -> Ab + 248 <= 2 ^ 64 -> 0 <= S < 2 ^ 64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_FRAGMENT_K -> S <= APPMEM_END ->
    ro_cells rsegs m (Ab + 208) [C8 (Z_to_bv 64 f)] ->
    ro_cells rsegs m (Ab + 88) [C8 (Z_to_bv 64 pa)] ->
    ro_cells rsegs m (Ab + 80) [C8 (Z_to_bv 64 pp)] ->
    ro_cells rsegs m (Ab + 72) [C8 (Z_to_bv 64 pn)] ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_FRAGMENT_K) S ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81da8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (-1) /\ getr R 18 = Z_to_bv 64 (-1) /\
         munch [(S - 4672, S)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S - 4672) S)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d80) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S Ab f pa pp pn -> -> -> Hf Hpa Hpp Hpn HA0 HA64 HS HSal Hlo Hhi RO208 RO88 RO80 RO72 HST HMI HAC HSW
    HRB HRM HGC HC254 HC255.
  pose proof FRAG as HC. unfold reac_ctrl_identity_fragment_contract, REAC_CTRL_IDENTITY_FRAGMENT in HC.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; exact HS).
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply p7_pre_F with (Ab := Ab) (f := f) (pa := pa) (pp := pp) (pn := pn);
      try assumption; try reflexivity; apply rng_all; lia. }
  intros ms' ->.
  eapply evt_cut.
  { eapply HC with (f := f) (fr := 0) (len := 0) (pa := pa) (pp := pp) (pn := pn)
      (st := repeat (Z_to_bv 8 0) 72) (g := repeat (Z_to_bv 8 0) 50).
    all: rewrite ?EU.
    all: try reflexivity.
    all: try assumption.
    all: try (intros _ HH; exfalso; apply HH; reflexivity).
    all: try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI' & ST' & _ & _ & _).
  subst ms'.
  rewrite P7.p7_refuse0 in MU |- *. cbn [fg_fp] in MU. change (fg_ret FgRefuse) with (-1).
  rewrite EU in MU, ST'. unfold REAC_CTRL_IDENTITY_FRAGMENT_K in MU, ST'.
  replace (ret_pc (Z_to_bv 64 0x81da8)) with (Z_to_bv 64 0x81da8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p7_post_F with (m := m) (S := S); try reflexivity; assumption.
Qed.

(* p7_evt_of_F has exactly the statement of the source lemma P7.p7_evt. *)
Definition p7_evt_same : ltac:(let T := type of P7.p7_evt in exact T) := p7_evt_of_F.

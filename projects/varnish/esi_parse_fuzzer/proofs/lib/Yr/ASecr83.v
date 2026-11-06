(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts AMTac ANodeA7 ANodeA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section A7post.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo res : Z) (scr : list byte)
            (s2v s1v s0v ra0 : word).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (usp + -48).
  Hypothesis LOLE : lo <= usp - 48.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis USP : usp <= 2^47.
  Hypothesis FR : rw_cells rsegs m (usp + -48) [CB 12 scr; C4 (wz 34); C8 s2v; C8 s1v; C8 s0v; C8 ra0].
  Hypothesis RA : bv_unsigned ra0 mod 2 = 0.
  Hypothesis GCF : ro_cells rsegs m 0xa9180 [C8 (wz CF)].
  Hypothesis CML : ro_cells rsegs m (CF + 144) [C8 (wz 0)].
  Hypothesis RC : (bv_unsigned a0 = 2^64 - 12 /\ res = 0) \/ (1 <= bv_unsigned a0 <= 2^64 - 4097 /\ res = bv_unsigned a0).

  Definition a7post_post : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    st = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz res) a1' a2' a3' a4' a5' a6' a7'
                 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(usp - 48, usp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp.

  Lemma a7post_spec : evt rsegs a7post_post
    (MS (mkR (wz mmapordie_resume) (wz (usp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz mmap_after_pc) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. eapply mmapordie_post_ok; try eassumption.
    intros. unfold a7post_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
End A7post.

Section A6post.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo size tol res : Z) (scr : list byte)
            (s4v s3v s2v s1v s0v ra0 : word).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (usp + -96).
  Hypothesis LOLE : lo <= usp - 96.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis USP : usp <= 2^47.
  Hypothesis SZ : 0 <= size < 2^64.
  Hypothesis TOL : 0 <= tol <= 1.
  Hypothesis FR : rw_cells rsegs m (usp + -96) (mapfixed_frame scr s4v s3v s2v s1v s0v ra0).
  Hypothesis RA : bv_unsigned ra0 mod 2 = 0.
  Hypothesis GCF : ro_cells rsegs m 0xa9180 [C8 (wz CF)].
  Hypothesis CML : ro_cells rsegs m (CF + 144) [C8 (wz 0)].
  Hypothesis RC : (tol = 1 /\ bv_unsigned a0 = 2^64 - 12 /\ res = 0) \/ (1 <= bv_unsigned a0 <= 2^64 - 4097 /\ res = bv_unsigned a0).

  Definition a6post_post : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    st = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz res) a1' a2' a3' a4' a5' a6' a7'
                 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(usp - 96, usp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp.

  Lemma a6post_spec : evt rsegs a6post_post
    (MS (mkR (wz mapfixed_resume) (wz (usp + -96)) gp tp t0 t1 t2 (wz size) (wz tol) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz mmap_after_pc) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. eapply mapfixed_post_ok; try eassumption.
    intros. unfold a6post_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.
End A6post.

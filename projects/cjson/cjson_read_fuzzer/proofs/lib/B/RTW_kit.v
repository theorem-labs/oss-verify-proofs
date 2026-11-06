(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Lemma amo_aligned_wz : forall wd p, 0 <= p < 2^64 -> p mod amo_bytes wd = 0 -> amo_aligned wd (wz p) = true.
Proof.
  intros wd p Hp Hm. unfold amo_aligned. unfold wz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  replace (p mod bv_modulus 64) with p by (symmetry; apply Z.mod_small; exact Hp). rewrite Hm. reflexivity.
Qed.
Ltac amo_sym :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      replace (amo_aligned wd a) with true by (symmetry; apply amo_aligned_wz; [lia| cbn [amo_bytes]; first [assumption| lia]]);
      cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?x)] => rewrite (Z.eqb_refl (bv_unsigned x)); cbv iota
  end.
Ltac refold_mkR :=
  match goal with
  | |- context [MS (TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
       (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) ?F ?pc ?fc ?rv ?m ?ro] =>
    change (TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
       (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
       (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
    with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  | _ => idtac
  end.


Ltac amo_step_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; amo_sym; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i; refold_mkR ]
      end
  end.
Ltac amo_zstep :=
  cbv beta delta [wz];
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => amo_step_core segs R F pc fc rv m ro
  end; zsimp.


(* [comment removed for export] *)
Goal forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m p v d (Q : machine_state -> Prop),
  rw_cells bsegs m p [C8 (wz v)] -> p mod 8 = 0 -> 0 <= p < 2^64 -> a2 = wz d -> mem_inv bsegs m ->
  (forall m', rw_cells bsegs m' p [C8 (amo_val AMO_ADD (wz v) (wz d))] ->
     evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz p) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x3679c) fc None m' (seg_rom bsegs))) ->
  evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz p) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x36798) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HC AL HP -> MI K. cbv beta delta [wz] in K.
  amo_zstep. apply K. exact HC.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac amo_sym :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      replace (amo_aligned wd a) with true by (symmetry; apply amo_aligned_wz; [lia| cbn [amo_bytes]; first [assumption| lia]]);
      cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?x)] => rewrite (Z.eqb_refl (bv_unsigned x)); cbv iota
  end.
Ltac refold_mkR :=
  match goal with
  | |- context [MS (TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
       (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) ?F ?pc ?fc ?rv ?m ?ro] =>
    change (TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
       (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
       (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
    with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  | _ => idtac
  end.
Ltac amo_step_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; amo_sym; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i; refold_mkR ]
      end
  end.
Ltac amo_zstep :=
  cbv beta delta [wz];
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => amo_step_core segs R F pc fc rv m ro
  end; zsimp.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u F_malloc_fast_u F_malloc_entry_u F_malloc_enframe_u MallocTree_u MallocKit_A_u F_mm_syscalls_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocKit_AB_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import Malloc_fp_u MallocKit_A2_u F_malloc_bigw_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocKit_A3_u ASlot_W10_u.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mm_frame (nd gm cnt size sc : Z) (j8 : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (wz nd); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); CB 8 j8; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma round_up_pg_idem x : round_up_pg (round_up_pg x) = round_up_pg x.
Proof.
  pose proof (MallocKit_A2_u.round_up_pg_mod x) as M.
  unfold round_up_pg at 1. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
  change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia.
Qed.

Lemma signed_lit_small z : -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.

Lemma divu_word a b : 0 <= a < 2^64 -> 0 < b < 2^64 -> mul_div M_DIVU (Z_to_bv 64 a) (wz b) = Z_to_bv 64 (a / b).
Proof.
  intros Ha Hb. unfold mul_div. rewrite (wz_unsigned b) by lia. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned, (wz_unsigned b), unsigned_lit, Z_to_bv_unsigned by lia.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr) (rid : N) (r0 : region).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

Definition mm_ai : Z :=
  let ai := (4096 - UNIT) / size - 1 in
  let ai := if cnt - 1 <? ai then cnt - 1 else ai in
  if ai <? 0 then 0 else ai.

Definition mm_st4 : mstate :=
  upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2).

Lemma mm_ai_range : 0 <= mm_ai <= cnt - 1.
Proof.
  unfold mm_ai, UNIT. change (4096 - 16) with 4080.
  pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)).
  destruct (Z.ltb_spec (cnt - 1) (4080 / size - 1)); [destruct (Z.ltb_spec (cnt - 1) 0)| destruct (Z.ltb_spec (4080 / size - 1) 0)]; lia.
Qed.
(* [comment removed for export] *)
End MMOK.
End CEIL_WRAP_1.


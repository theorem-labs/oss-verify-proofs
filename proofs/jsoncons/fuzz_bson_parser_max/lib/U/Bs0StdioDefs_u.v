(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
  ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes SumWalkTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Export Bs0ExitBase_u Bs0Exit_run1_u.      (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
  swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
  swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

(* [comment removed for export] *)
Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0xb71e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea230))
  /\ rdn RSEGS mem (Z_to_bv 64 0xea230) 8%nat = Some (word_to_le_bytes 8 can).

(* [comment removed for export] *)
Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
       (mem' : word -> option byte) : Prop := {
  swp_agree : forall x : word,
      ~ (su - 112 <= bv_unsigned x < su)%Z ->
      ~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
      ~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
      mem' x = mem x;
  swp_grows : mem_grows mem mem';
  swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
  swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.

(* [comment removed for export] *)
Lemma sw_post_rdn : forall mem su f bufp bufsz mem' (a : word) n bs,
  sw_post mem su f bufp bufsz mem' ->
  rdn RSEGS mem a n = Some bs ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= su - 112 \/ su <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 32 \/ f + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 56 \/ f + 64 <= bv_unsigned a)%Z ->
  rdn RSEGS mem' a n = Some bs.
Proof.
  intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
  rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
  intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.

Lemma sw_post_store_ok : forall mem su f bufp bufsz mem' (a : word) n,
  sw_post mem su f bufp bufsz mem' ->
  store_ok RSEGS mem a n = true -> store_ok RSEGS mem' a n = true.
Proof. intros mem su f bufp bufsz mem' a n P H. eapply store_ok_mono; [apply (swp_grows _ _ _ _ _ _ P) | exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
       (sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
  ec_sp   : getr regs 2 = sp;
  ec_tp   : getr regs 4 = tp;
  ec_a0   : getr regs 10 = code;
  ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  ec_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  ec_tplo : (168 <= bv_unsigned tp)%Z;
  ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
  ec_tid  : (0 < tid < 2147483648)%Z;
  (* [comment removed for export] *)
  ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  (* [comment removed for export] *)
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0xea228) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0xb71f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb14f8));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0xb71f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb14f0));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0xb14f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x341ec));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0xb8548) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0xb7080) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ac0c));      (* [comment removed for export] *)
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0xb8218) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb8218));      (* [comment removed for export] *)
  ec_ax   : exists ax : axv, atexit_cells mem ax;      (* [comment removed for export] *)
  ec_cb   : rdn RSEGS mem (Z_to_bv 64 0xc8554) 1%nat = Some [Z_to_bv 8 0];      (* [comment removed for export] *)
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0xb7088) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0xb8300 wp2 rp2
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0xb83f0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0xb83f0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0xb83f0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0xb83f0 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ff58));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0xb83f0 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0xb83f0 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0xb83f0 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0xb83f0 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0xb83f0 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0xea238 <= wb < wp /\ wp <= 0xeb000)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

(* [comment removed for export] *)
Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
           (code : word) (pending : list byte) : Prop :=
  exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
    exit_common regs mem sp tp code tid wp2 rp2
    /\ m_halted model = None /\ m_vm_lazy model = []
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0xb83f0 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatExec StoreOk Frame ShapeAlg Spec RefMemcpyLib.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record Pf0Img := {
  pf_segs   : list Segment;
  pf_entry  : Z;   (* [comment removed for export] *)
  pf_ret    : Z;   (* [comment removed for export] *)
  pf_file   : Z;   (* [comment removed for export] *)
  pf_buf    : Z;   (* [comment removed for export] *)
  pf_swrite : Z;   (* [comment removed for export] *)
  pf_canary : Z;   (* [comment removed for export] *)
  pf_ro_hi  : Z    (* [comment removed for export] *)
}.

Definition PF0_S0 : Pf0Img :=
  {| pf_segs := Ubsan.M.loaded_segments; pf_entry := 0x139d8; pf_ret := 0x1392c; pf_file := 0x33f90;
     pf_buf := 0x64cb8; pf_swrite := 0x2b114; pf_canary := 0x64450; pf_ro_hi := 0x33000 |}.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PF0_FR : Z := 1200.
Definition FILE_SIZE : Z := 232.
Definition BUF_SIZE : Z := 1024.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithImg.
  Variable I : Pf0Img.
  Let SEGS := pf_segs I.
  Let f := pf_file I.

  Definition cellZ (mem : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
    rdn SEGS mem (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

  (* [comment removed for export] *)
  Record stdout_wmode (mem : word -> option byte) (w : Z) : Prop := {
    sw_flags : cellZ mem f 4 5;                       (* [comment removed for export] *)
    sw_rpos  : cellZ mem (f + 8) 8 0;
    sw_rend  : cellZ mem (f + 16) 8 0;
    sw_wend  : cellZ mem (f + 32) 8 (pf_buf I + BUF_SIZE);
    sw_wpos  : cellZ mem (f + 40) 8 w;
    sw_wbase : cellZ mem (f + 56) 8 (pf_buf I);
    sw_write : cellZ mem (f + 72) 8 (pf_swrite I);
    sw_buf   : cellZ mem (f + 88) 8 (pf_buf I);
    sw_bsz   : cellZ mem (f + 96) 8 BUF_SIZE;
    sw_fd    : cellZ mem (f + 120) 4 1;
    sw_mode  : cellZ mem (f + 136) 4 4294967295;
    sw_lock  : cellZ mem (f + 140) 4 4294967295;
    sw_lbf   : cellZ mem (f + 144) 4 4294967295
  }.

  (* [comment removed for export] *)
  Definition pf0_fp (sp : Z) : list (word * Z) :=
    [(Z_to_bv 64 (sp - PF0_FR), PF0_FR); (Z_to_bv 64 f, FILE_SIZE); (Z_to_bv 64 (pf_buf I), BUF_SIZE)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  Definition printf0_first_stmt : Prop :=
    forall (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) (sp : word) (can : Z) (K : TSet),
      getr regs 1 = Z_to_bv 64 (pf_ret I) -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
      bv_unsigned sp mod 16 = 0 ->
      4294967296 + PF0_FR <= bv_unsigned sp -> bv_unsigned sp <= 0x7fffffffffff ->
      store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - PF0_FR)) (Z.to_nat PF0_FR) = true ->
      (* [comment removed for export] *)
      (forall i, 0x10000 <= i < pf_ro_hi I -> mem (Z_to_bv 64 i) = None) ->
      (* [comment removed for export] *)
      (forall i, f <= i < f + FILE_SIZE -> mem (Z_to_bv 64 i) = None) ->
      cellZ mem (pf_canary I) 8 can -> 0 <= can < 2 ^ 64 ->
      fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
      m_halted model = None -> m_vm_lazy model = [] ->
      K [] ->
      (forall regs' mem',
         keeps_cs regs regs' ->
         frame_mod mem mem' (pf0_fp (bv_unsigned sp)) ->
         stdout_wmode mem' (pf_buf I) ->
         realizes SEGS (mkCfg (mkst regs' (Z_to_bv 64 (pf_ret I)) mem' (seg_rom SEGS)) model) K) ->
      realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 (pf_entry I)) mem (seg_rom SEGS)) model)
               (t_emit (W 1 [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]) K).
End WithImg.

Definition printf0_first_stmt_s0 : Prop := printf0_first_stmt PF0_S0.
(* [comment removed for export] *)

(* [comment removed for export] *)

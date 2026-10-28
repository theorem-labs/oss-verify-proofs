(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStepTac BHoare BWalkTac BStoreOk BStreamSim BMmapSim BExitSim BShapeAlg BNodes BSumWalkTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export BRefExitBase.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
  swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
  swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x185ed0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e5898))
  /\ rdn RSEGS mem (Z_to_bv 64 0x6e5898) 8%nat = Some (word_to_le_bytes 8 can).

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

  ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));

  ec_lock : rdn RSEGS mem (Z_to_bv 64 0x6e5ac8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));

  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0x185f00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17e680));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0x185f08) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17e668));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0x17e668) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x91314));

  ec_comp : rdn RSEGS mem (Z_to_bv 64 0x18d9d0) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x185070) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x165294));
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0x186f40) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x186f40));
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x185078) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));

  ec_axl  : rdn RSEGS mem (Z_to_bv 64 0x6e58ac) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  ec_axh  : rdn RSEGS mem (Z_to_bv 64 0x6e58b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));

  ec_glob : stdio_globals mem;

  ec_err  : file_clean mem 0x189920 wp2 rp2
}.

Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x189b00 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x189b00 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x189b00 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x189b00 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16cdd0));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x189b00 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x189b00 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x189b00 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x189b00 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x189b00 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x6e5ad0 <= wb < wp /\ wp <= 0x6e8000)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
           (code : word) (pending : list byte) : Prop :=
  exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
    exit_common regs mem sp tp code tid wp2 rp2
    /\ m_halted model = None /\ m_vm_lazy model = []
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0x189b00 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
  ExitSim ShapeAlg Nodes SumWalkTac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Export U9ExitBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Record sw_file {RCa1 : RunCtx}  (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
  swf_wpos  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  swf_wbase : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  swf_fd    : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
  swf_buf   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swf_bsz   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.
Arguments Build_sw_file {RCa1}.

Definition ssp_cells {RCa1 : RunCtx}  (mem : word -> option byte) (can : word) : Prop :=
  rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22ec0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x944a8))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x944a8) 8%nat = Some (word_to_le_bytes 8 can).

Record sw_post {RCa1 : RunCtx}  (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
       (mem' : word -> option byte) : Prop := {
  swp_agree : forall x : word,
      ~ (su - 112 <= bv_unsigned x < su)%Z ->
      ~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
      ~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
      mem' x = mem x;
  swp_grows : mem_grows mem mem';
  swp_wend  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
  swp_wpos  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swp_wbase : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.
Arguments Build_sw_post {RCa1}.

Lemma sw_post_rdn {RCa1 : RunCtx}  : forall mem su f bufp bufsz mem' (a : word) n bs,
  sw_post mem su f bufp bufsz mem' ->
  rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem a n = Some bs ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= su - 112 \/ su <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 32 \/ f + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 56 \/ f + 64 <= bv_unsigned a)%Z ->
  rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' a n = Some bs.
Proof.
  intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
  rewrite (rdn_ext (run_segments RSEGS rc_inp rc_sp rc_mb) n mem' mem a Hnw); [exact H|].
  intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.



Definition PATX : Z := 0x94280.
Definition PATX_CALL : Z := 0x1a328.
Definition PAEF_GUARD : Z := 0x14d20.
Definition PAEF_INCB : Z := 0x34144.
Definition atx_U {RCa1 : RunCtx}  (mem : word -> option byte) : Prop :=
     rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x94290) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x94284) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
Definition atx_R {RCa1 : RunCtx}  (mem : word -> option byte) : Prop :=
     rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x94290) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x94298))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x94288) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x94284) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x94298) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x942a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1a328))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x943a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14d20))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x34144) 1%nat = Some [Z_to_bv 8 0].
Definition atx_state {RCa1 : RunCtx}  (mem : word -> option byte) : Prop := atx_U mem \/ atx_R mem.

Record exit_common {RCa1 : RunCtx}  (regs : bvmap 5 word) (mem : word -> option byte)
       (sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
  ec_sp   : getr regs 2 = sp;
  ec_tp   : getr regs 4 = tp;
  ec_a0   : getr regs 10 = code;
  ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  ec_sok  : store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  ec_tplo : (168 <= bv_unsigned tp)%Z;
  ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
  ec_tid  : (0 < tid < 2147483648)%Z;
  ec_mtid : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  ec_lock : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x944a0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  ec_fe   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22ec8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22e30));
  ec_fs   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22ed0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22e28));
  ec_fa   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22e28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14868));
  ec_comp : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x24138) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22e70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1a260));
  ec_g2   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22e78) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  ec_dso  : exists dso : word, rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x23ed8) 8%nat = Some (word_to_le_bytes 8 dso);
  ec_atx  : atx_state mem;
  ec_glob : stdio_globals mem;
  ec_err  : file_clean mem 0x23f00 wp2 rp2
}.
Arguments Build_exit_common {RCa1}.

Record stdout_pending {RCa1 : RunCtx}  (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x23ff0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x23ff0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x23ff0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x23ff0 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1c84c));
  sp_buf   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x23ff0 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x23ff0 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x23ff0 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x23ff0 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x23ff0 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x944b0 <= wb < wp /\ wp <= 0x95000)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
  sp_bytes : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.
Arguments Build_stdout_pending {RCa1}.

Definition exit_pre {RCa1 : RunCtx}  (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
           (code : word) (pending : list byte) : Prop :=
  exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
    exit_common regs mem sp tp code tid wp2 rp2
    /\ m_halted model = None /\ m_vm_lazy model = []
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0x23ff0 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
              /\ m_channel_reader model = true) ).   (* LibWritev's premise *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

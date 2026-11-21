(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (exit_preA written out in plain text from its encoded (CDefT) form, its pending branch now also requiring a reader on the output channel, which the revision's writev reads; the CDefT name table, then unused, removed). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Asan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape Tac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim SumWalkTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Export A_stdio_defs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT A_exit_lib A_exit_front1 A_unreg_globals.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Record exit_commonA (regs : bvmap 5 word) (mem : word -> option byte)
       (su : Z) (code : word) (tid : Z) (wp0 rp0 wp2 rp2 : word) : Prop := {
  ec_sp   : getr regs 2 = Z_to_bv 64 su;
  ec_tp   : getr regs 4 = Z_to_bv 64 0x639690;
  ec_a0   : getr regs 10 = code;
  ec_spal : (su mod 16 = 0)%Z;
  ec_stk  : stk RSEGS mem (su - 320) su;                  (* [comment removed for export] *)
  ec_mi   : mem_inv RSEGS mem;
  ec_tid  : (0 < tid < 2^31)%Z;
  (* [comment removed for export] *)
  ec_lock : rw_cells RSEGS mem 0x659900 [C4 (Z_to_bv 64 0)];                  (* [comment removed for export] *)
  ec_mtid : rw_cells RSEGS mem 0x6395e8 [C4 (Z_to_bv 64 tid)];                (* [comment removed for export] *)
  ec_atexit : exists (b : bool) fin jp jq jf, atexit_cells b mem fin jp jq jf /\ (b = true -> incb_cell mem);   (* [comment removed for export] *)
  ec_nl   : ro_cells RSEGS mem 0x659923 [C1 (Z_to_bv 8 0)];                   (* [comment removed for export] *)
  ec_comp : rw_cells RSEGS mem 0x102f90 [C1 (Z_to_bv 8 0)];                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  ec_rtc  : asan_rtc mem;
  ec_mapped : mapped mem 0x7fffa000 0x800d3000;                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  ec_in   : file_clean mem 0x0f72a8 wp0 rp0;                                   (* [comment removed for export] *)
  ec_err  : file_clean mem 0x0f70c8 wp2 rp2                                    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record stdout_pendingA (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x0f71b8 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x0f71b8 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x0f71b8 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x0f71b8 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0e32ec));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x0f71b8 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x0f71b8 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x0f71b8 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x0f71b8 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x0f71b8 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x659da0 <= wb < wp /\ wp <= 0x65a1a0)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

(* [comment removed for export] *)
Definition exit_preA (su : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mo : Model)
           (code : word) (pending : list byte) : Prop :=
  (* plain text: the pending branch also carries the channel reader the revision's writev reads *)
  (@Corelib.Init.Logic.ex (@Corelib.Numbers.BinNums.Z) (fun tid : (@Corelib.Numbers.BinNums.Z) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun wp0 : (@stdpp.bitvector.definitions.bv 64%N) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun rp0 : (@stdpp.bitvector.definitions.bv 64%N) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun wp2 : (@stdpp.bitvector.definitions.bv 64%N) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun rp2 : (@stdpp.bitvector.definitions.bv 64%N) => (@Corelib.Init.Logic.and (@exit_commonA regs mem su code tid wp0 rp0 wp2 rp2) (@Corelib.Init.Logic.or (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) pending (@Corelib.Init.Datatypes.nil (@stdpp.bitvector.definitions.bv 8%N))) (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun wp1 : (@stdpp.bitvector.definitions.bv 64%N) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun rp1 : (@stdpp.bitvector.definitions.bv 64%N) => (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A.A_exit_base.file_clean mem 1012152%Z wp1 rp1)))))) (@Corelib.Init.Logic.ex (@Corelib.Numbers.BinNums.Z) (fun wb : (@Corelib.Numbers.BinNums.Z) => (@Corelib.Init.Logic.ex (@Corelib.Numbers.BinNums.Z) (fun wp : (@Corelib.Numbers.BinNums.Z) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun bufp : (@stdpp.bitvector.definitions.bv 64%N) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun bufsz : (@stdpp.bitvector.definitions.bv 64%N) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun rp1 : (@stdpp.bitvector.definitions.bv 64%N) => (@Corelib.Init.Logic.ex (@stdpp.bitvector.definitions.bv 64%N) (fun can : (@stdpp.bitvector.definitions.bv 64%N) => (@Corelib.Init.Logic.and (@stdout_pendingA mem wb wp bufp bufsz rp1 can pending) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds mo) (@stdpp.bitvector.definitions.Z_to_bv 64%N 1%Z)) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv 64%N 1%Z)))) (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.State.m_channel_reader mo) (@Corelib.Init.Datatypes.true))))))))))))))))))))))))))))
(* [comment removed for export] *).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

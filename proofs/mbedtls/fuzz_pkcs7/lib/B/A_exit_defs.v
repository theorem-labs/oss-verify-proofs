(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape Tac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim SumWalkTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Export A_stdio_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_exit_lib A_exit_front1 A_unreg_globals.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_exit_defs () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "exit_commonA"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.B.A_exit_base.file_clean"; "stdout_pendingA"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"].


(* [comment removed for export] *)
Record exit_commonA (regs : bvmap 5 word) (mem : word -> option byte)
       (su : Z) (code : word) (tid : Z) (wp0 rp0 wp2 rp2 : word) : Prop := {
  ec_sp   : getr regs 2 = Z_to_bv 64 su;
  ec_tp   : getr regs 4 = Z_to_bv 64 0x63ca90;
  ec_a0   : getr regs 10 = code;
  ec_spal : (su mod 16 = 0)%Z;
  ec_stk  : stk RSEGS mem (su - 320) su;                  (* [comment removed for export] *)
  ec_mi   : mem_inv RSEGS mem;
  ec_tid  : (0 < tid < 2^31)%Z;
  (* [comment removed for export] *)
  ec_lock : rw_cells RSEGS mem 0x65cd00 [C4 (Z_to_bv 64 0)];                  (* [comment removed for export] *)
  ec_mtid : rw_cells RSEGS mem 0x63c9e8 [C4 (Z_to_bv 64 tid)];                (* [comment removed for export] *)
  ec_atexit : exists (b : bool) fin jp jq jf, atexit_cells b mem fin jp jq jf /\ (b = true -> incb_cell mem);   (* [comment removed for export] *)
  ec_nl   : ro_cells RSEGS mem 0x65cd23 [C1 (Z_to_bv 8 0)];                   (* [comment removed for export] *)
  ec_comp : rw_cells RSEGS mem 0x106390 [C1 (Z_to_bv 8 0)];                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  ec_rtc  : asan_rtc mem;
  ec_mapped : mapped mem 0x7fffa000 0x800d3000;                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  ec_in   : file_clean mem 0x0fa668 wp0 rp0;                                   (* [comment removed for export] *)
  ec_err  : file_clean mem 0x0fa488 wp2 rp2                                    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record stdout_pendingA (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x0fa578 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x0fa578 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x0fa578 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x0fa578 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0e66b8));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x0fa578 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x0fa578 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x0fa578 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x0fa578 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x0fa578 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x65d1a0 <= wb < wp /\ wp <= 0x65d5a0)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

(* [comment removed for export] *)
Definition exit_preA (su : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mo : Model)
           (code : word) (pending : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_exit_defs ()) "(0.$1.Ltid,$1.(0.(2.&40.)Lwp0,(2.&40.)(0.(2.&40.)Lrp0,(2.&40.)(0.(2.&40.)Lwp2,(2.&40.)(0.(2.&40.)Lrp2,(2.&40.)(3.(4.O5.O4.O6.O2.R5.R4.R3.R2.R1.)(5.(3.(6.(7.(2.&8.))O1.(8.(2.&8.)))(0.(2.&40.)Lwp1,(2.&40.)(0.(2.&40.)Lrp1,(2.&40.)(9.O4.+?:578.R2.R1.))))(0.$1.Lwb,$1.(0.$1.Lwp,$1.(0.(2.&40.)Lbufp,(2.&40.)(0.(2.&40.)Lbufsz,(2.&40.)(0.(2.&40.)Lrp1,(2.&40.)(0.(2.&40.)Lcan,(2.&40.)(3.(:.O4.R6.R5.R4.R3.R2.R1.O1.)(6.(;.$<.)(=.(>.O3.)(?.&40.+1.))(10.$<.(11.(?.&40.+1.))))))))))))))))))")
(* [comment removed for export] *).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

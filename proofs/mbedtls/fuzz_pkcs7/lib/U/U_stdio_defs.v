(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ShapeX SumWalkTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Export U_exit_base.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_stdio_defs () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "sw_post"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.ex"; "exit_common"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.file_clean"; "stdout_pending"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"].


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
Definition ssp_cells (mem : word -> option byte) (can : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_stdio_defs ()) "(0.(1.(2.(3.(4.&8.)))(5.$6.O2.(7.&40.+4;<=8.)#8.)(8.(3.(4.&8.))(9.#8.(7.&40.+7=330.))))(1.(2.(3.(4.&8.)))(5.$6.O2.(7.&40.+7=330.)#8.)(8.(3.(4.&8.))(9.#8.O1.))))")
(* [comment removed for export] *).

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
Lemma sw_post_rdn : ltac2:(CDefT.buildp (gd_tbl_P_stdio_defs ()) "Pmem,P,(4.&40.)(2.(4.&8.))Psu,$:.Pf,$:.Pbufp,(4.&40.)Pbufsz,(4.&40.)Pmem',P,(4.&40.)(2.(4.&8.))Pa,(4.&40.)Pn,$;.Pbs,(3.(4.&8.))P,(<.R9.R8.R7.R6.R5.R4.)P,(1.(2.(3.(4.&8.)))(5.$6.R:.R4.R3.)(8.(3.(4.&8.))R2.))P,(=.(>.(?.&40.R5.)(10.R4.))(11.+2.+40.))P,(12.(=.(>.(?.&40.R6.)(10.R5.))(13.R;.+70.))(=.R;.(?.&40.R6.)))P,(12.(=.(>.(?.&40.R7.)(10.R6.))(>.R;.+20.))(=.(>.R;.+30.)(?.&40.R7.)))P,(12.(=.(>.(?.&40.R8.)(10.R7.))(>.R<.+38.))(=.(>.R<.+40.)(?.&40.R8.)))(1.(2.(3.(4.&8.)))(5.$6.R:.R9.R8.)(8.(3.(4.&8.))R7.))")
(* [comment removed for export] *).
Proof.
  intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
  rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
  intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.


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
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0x7d328) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0x4bce0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x48360));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0x4bce8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x48358));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0x48358) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1d1bc));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0x4cf68) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x4bc80) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3f630));
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x4bc88) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0x4cd30 wp2 rp2;
  (* [comment removed for export] *)
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0x4ccf0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4ccf0));
  (* [comment removed for export] *)
  ec_atexit : exists b : bool, atexit_st b mem
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x4ce20 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x4ce20 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x4ce20 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x4ce20 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x41a34));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x4ce20 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x4ce20 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x4ce20 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x4ce20 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x4ce20 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x7d338 <= wb < wp /\ wp <= 0x7e000)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

(* [comment removed for export] *)
Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
           (code : word) (pending : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_stdio_defs ()) "(14.(4.&40.)Lsp,(4.&40.)(14.(4.&40.)Ltp,(4.&40.)(14.$:.Ltid,$:.(14.(4.&40.)Lwp2,(4.&40.)(14.(4.&40.)Lrp2,(4.&40.)(0.(15.O5.O4.R5.R4.O2.R3.R2.R1.)(0.(1.(2.(4.&40.))(16.O3.)(17.(4.&40.)))(0.(1.(3.(18.(4.&40.)(4.&40.)))(19.O3.)(1:.(18.(4.&40.)(4.&40.))))(12.(0.(1.(3.(4.&8.))O1.(1:.(4.&8.)))(14.(4.&40.)Lwp1,(4.&40.)(14.(4.&40.)Lrp1,(4.&40.)(1;.O4.+4<>20.R2.R1.))))(14.$:.Lwb,$:.(14.$:.Lwp,$:.(14.(4.&40.)Lbufp,(4.&40.)(14.(4.&40.)Lbufsz,(4.&40.)(14.(4.&40.)Lrp1,(4.&40.)(14.(4.&40.)Lcan,(4.&40.)(0.(1<.O4.R6.R5.R4.R3.R2.R1.O1.)(1.(2.$1=.)(1>.(1?.O3.)(7.&40.+1.))(8.$1=.(20.(7.&40.+1.))))))))))))))))))))")
(* [comment removed for export] *).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

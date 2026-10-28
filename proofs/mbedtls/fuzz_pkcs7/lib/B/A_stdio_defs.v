(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ShapeX SumWalkTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Export A_exit_base.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_stdio_defs () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "sw_post"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.sub"].


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
Definition ssp_cells (mem : word -> option byte) (can : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_stdio_defs ()) "(0.(1.(2.(3.(4.&8.)))(5.$6.O2.(7.&40.+?6:>0.)#8.)(8.(3.(4.&8.))(9.#8.(7.&40.+65<:=0.))))(1.(2.(3.(4.&8.)))(5.$6.O2.(7.&40.+65<:=0.)#8.)(8.(3.(4.&8.))(9.#8.O1.))))")
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
Lemma sw_post_rdn : ltac2:(CDefT.buildp (gd_tbl_A_stdio_defs ()) "Pmem,P,(4.&40.)(2.(4.&8.))Psu,$:.Pf,$:.Pbufp,(4.&40.)Pbufsz,(4.&40.)Pmem',P,(4.&40.)(2.(4.&8.))Pa,(4.&40.)Pn,$;.Pbs,(3.(4.&8.))P,(<.R9.R8.R7.R6.R5.R4.)P,(1.(2.(3.(4.&8.)))(5.$6.R:.R4.R3.)(8.(3.(4.&8.))R2.))P,(=.(>.(?.&40.R5.)(10.R4.))(11.+2.+40.))P,(12.(=.(>.(?.&40.R6.)(10.R5.))(13.R;.+70.))(=.R;.(?.&40.R6.)))P,(12.(=.(>.(?.&40.R7.)(10.R6.))(>.R;.+20.))(=.(>.R;.+30.)(?.&40.R7.)))P,(12.(=.(>.(?.&40.R8.)(10.R7.))(>.R<.+38.))(=.(>.R<.+40.)(?.&40.R8.)))(1.(2.(3.(4.&8.)))(5.$6.R:.R9.R8.)(8.(3.(4.&8.))R7.))")
(* [comment removed for export] *).
Proof.
  intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
  rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
  intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_B3 F_ntf_D F_ntf_E.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_ntf_F () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_ntf_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.Z."], [["1bool"; "1false"; "1list"; "2and"; "2eq"; "2iff"; "3Z"; "4fm_facts"; "5unmap_seqs"; "5zeros"; "6aptr"; "6c_free_meta_head"; "6mctx"; "6mstate"; "6optr"; "6s_ctx"]; ["6sc_in_seq_range"; "6set_unmap_seq_map"; "6upd_ctx"; "7add"; "7land"; "7le"; "7lt"; "0c"; "0f"; "0g"; "0sc"; "0st"; "8empty"; "9bv"; ":Z_countable"; ";gmap"]; [";gmap_empty"; "<eq_dec"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition seq_st (ns sc : Z) (st : mstate) : mstate := record_seq sc (upd_ctx (set_seq ns) st).
Lemma fm_facts_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_ntf_F "K'='<pR611&:'4&>&;r2&?r3%211%411%611%713%:3921&7r4%221:&Br5%2241%621<p051p091pQDE1pQBG1pQHJ1").
Proof. intros st f g E H hd Hh. unfold ctx in *. cbn [upd_ctx s_ctx] in Hh. rewrite E in Hh. exact (H hd Hh). Qed.
Lemma seq_range_test : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_ntf_F "M'6'3&Ezr1%3221+QO%5231%7231&5&F+O&D&Cr2-7%3221+_oooooooooooO%6221%9281'4'0&@%119(1%53421%A271p0C1pQFL1").
Proof. intros sc.
intros Hsc. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
unfold sc_in_seq_range.
destruct (Z.lt_ge_cases sc 7) as [L|GE].
- replace ((sc + -7) mod 2 ^ 64) with (sc + -7 + 2^64).
2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try lia.
- rewrite Z.mod_small by lia.
destruct (Z.leb_spec 7 sc); destruct (Z.ltb_spec sc 39); cbn; split; intros; try reflexivity; try discriminate; lia.
Qed.
Lemma unmap_seqs_empty : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_ntf_F "N'='4'2'My8%211%411&8&B'<&A&L'O'6&Q1&N%443213&Q0%145435%8231r1%;221qQ@=1%?213%A11&9uQ0%211%K3F41pQHM1").
Proof. intros st. reflexivity. Qed.
End CEIL_WRAP_1.

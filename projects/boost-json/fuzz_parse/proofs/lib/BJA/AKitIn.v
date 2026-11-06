(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14consk14listk13nil37Corelib4Init5Logicmd2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~o63le1hf7Z_to_bvhfbbv_unsigned" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma le1_byte : ltac2:(zQ "90!h9!jc!l9!m0!m7!o1!s0!s6!t0>1w@1$1@1$0#k0@3$5@1$3@1$1@1$0#8@1$6^1@3$2@1$1@1$0#8@2$7@1$0#8@2$8@1$0#k0^1@1$4@1$1@1$0#8").
Proof.
  intros w. pose proof (le1_mod (bv_unsigned w)) as E. rewrite Z_to_bv_bv_unsigned in E. rewrite E. unfold b8. f_equal.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

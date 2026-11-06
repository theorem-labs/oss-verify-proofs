(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Zhfbbv_unsigned46Stdlib6ZArith6BinInt1Zl23addl23mul" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Local Notation M64 := 18446744073709551616%Z.

(* [comment removed for export] *)
Definition v4 : ltac2:(zQ "30!h9!jc!k1>2b0@1$1@1$0#8>2b1@1$1@1$0#8>2b2@1$1@1$0#8>2b3@1$1@1$0#8$2") := ltac2:(zQ "50!h9!jc!k4!ma!n0\2b0@1$1@1$0#8\2b1@1$1@1$0#8\2b2@1$1@1$0#8\2b3@1$1@1$0#8@2$3@2$3@2$3@2$2@1$0#8^4@2$4+hg0@2$2@1$0#8^3@2$4+hggg0@2$2@1$0#8^2@2$4+hggggg0@2$2@1$0#8^1").


(* [comment removed for export] *)

Section merge.
  Variables b0 b1 b2 b3 c0 c1 c2 c3 : byte.

  (* [comment removed for export] *)


  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End merge.
(* [comment removed for export] *)

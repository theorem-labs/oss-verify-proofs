(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A3 ASlot_W1.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~m34cellk14consm32C8k13nilm32CB46Stdlib6ZArith6BinInt1Zrd3mulhf7Z_to_bv" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition ag_frame : ltac2:(zQ "50!h9!jc!l9!m0!pf>2sc$3>1j@1$2@1$1@1$0#8>3s4v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s0v@1$1@1$0#k0>3rav@1$1@1$0#k0@1$2$4") := ltac2:(zQ "b0!pf!q6!h9!qd!jc!l9!r2!m0!r8!t5!tb\2sc$7\1j@1$5@1$4@1$2#8\3s4v@1$4@1$2#k0\3s3v@1$4@1$2#k0\3s2v@1$4@1$2#k0\3s1v@1$4@1$2#k0\3s0v@1$4@1$2#k0\3rav@1$4@1$2#k0@3$1$0@1$3@2$a@1$2#k0@2$9^8+2@3$1$0@2$8Ni8^7@3$1$0@1$3^6@3$1$0@1$3^5@3$1$0@1$3^4@3$1$0@1$3^3@3$1$0@1$3^2@3$1$0@1$3^1@1$6$0").

Section AG1.
Variables (sc lo : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
End AG1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section EPI.
Variables (lo : Z).
Hypothesis CLO : alloc_ceiling <= lo.
End EPI.

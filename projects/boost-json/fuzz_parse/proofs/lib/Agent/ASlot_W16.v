(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc6mstate37Corelib4Init9Datatypesm34bool46Stdlib6ZArith6BinInt1Zo23addm34andbhc5usageo24eveno23ltbo23mulhc4PGSZo23eqbo24landm34negbm34prodm34pairhc4UNITm33orbhc2IBhcbround_up_pgo23leb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_W16~~~~~~hh18mm_small04Npos37Corelib4Init5Logichm52eq35stdpp9bitvectorbdefinitionshnf7Z_to_bvhnfbbv_unsignedo22lehm53ando22lto23opp" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mm_usage1 : ltac2:(zQ "20!h9!la>3st1$1>2sc$0>6usage0$0$0") := ltac2:(zQ "80!h9!nb!pa!q0!la!q7!qf!r6\3st1$4\2sc$0\6usage0$0M1\0$1$0@2$3@1$6^2@2$7^2+i0@2$2^1@2$5^3@2$2^2+1^1").

Definition mm_cnt_red : ltac2:(zQ "20!h9!nb>2sc$0>4size$0>3cnt$0>6usage1$0>7nosmall$1$0") := ltac2:(zQ "90!nb!h9!rc!q0!r6!s2!s9!sf!t6\2sc$1\4size$1\3cnt$1\6usage1$1\7nosmall$0M0\0$0$1@2$3@2$4^2@2$2+4^3@1$8^1M0\0$0$1@2$3@2$6@2$7^5+3+1@2$4@2$2+8$5@2$2^4^3+2M0\0$0$1@2$3@2$6@2$7^5+3+2@2$4@2$2+4$5@2$2^4^3+3M0\0$0$1@2$3@2$6@2$7^5+3Z@2$4@2$2+8$5@2$2^4^3+3M0\0$0$1@2$3@2$6@2$7^5+3Z@2$4@2$2+2$5@2$2^4^3+5^3^3").

Definition mm_small : ltac2:(zQ "20!h9!td>4size$0>3req$0>6usage1$0>3cnt$0>6needed$0@2$1$0$0") := ltac2:(zQ "e0!h9!pa!nb!u4!ub!r6!rc!q0!v2!td!v8!s2!vd!hgb\4size$0\3req$0\6usage1$0\3cnt$0\6needed$0=3req$0@1$c@2$1@2$1^4$a$4M2\0$2@2$9$0$0@2$8@2$5^1@2$1^6$4@2$7@2$d@2$6+4$b^1@2$5^4@2$6+2^3@4$3$0$0+1^1@4$3$0$0^3^2").

Definition mm_final : ltac2:(zQ "30!h9!nb!td>4size$0>3req$0>6usage1$0>3cnt$0>7nosmall$1@2$2$0$0") := ltac2:(zQ "c0!h9!nb!q0!t6!u4!td!hl3!ub!vd!pa!hgb!rc\4size$0\3req$0\6usage1$0\3cnt$0\7nosmall$1=6needed$0@1$8@2$9@2$b^5^2$7M1\0$1@2$5$0$0@2$2@1$3^2@2$a^3+7@5$6^6^5^4^3^1@4$4$0$0^3^1").

Lemma land_4095_word : ltac2:(zQ "60!hlf!h9!sf!hn9!hpc!hq7>1z$1@3$3$1@2$2@2$5@1$0#k0@2$4@1$0#k0^1+vvf@2$2^1+vvf").
Proof. intros z.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^52 * 2^12).
  change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
  apply Z.mod_mod_divide. exists (2^52). reflexivity.
Qed.

Lemma land3_range : ltac2:(zQ "40!sf!hr6!hrb!h9>1x$3@2$2@2$1Z@2$0^1+3@2$1@2$0^1+3+3").
Proof. intros x. change (Z.land x 3) with (Z.land x (Z.ones 2)). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2^2) ltac:(lia)). lia. Qed.

Lemma land_4095_range : ltac2:(zQ "50!sf!hrb!h9!hr6!hs2>1y$2@2$1@2$3Z@2$0^1+vvf@2$4@2$0^1+vvf+hgg0").
Proof. intros y. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma round_up_pg_alt : ltac2:(zQ "60!h9!hn9!vd!pa!sf!hs7>1x$0@3$1$0@2$3@2$4@1$5^1+vvf^1@1$2^1").
Proof. intros x. unfold round_up_pg. change (PGSZ - 1) with 4095. lia. Qed.

Lemma round_up_pg_range : ltac2:(zQ "60!vd!hr6!hrb!h9!pa!hs2>1x$3>0@2$1Z^1@2$2@2$1^2@1$0^2@2$5@1$0^2@2$4^2+hgg0").
Proof. intros x. intros. unfold round_up_pg. change (PGSZ - 1) with 4095. pose proof (land_4095_range (- x)). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

End MMC.
(* [comment removed for export] *)

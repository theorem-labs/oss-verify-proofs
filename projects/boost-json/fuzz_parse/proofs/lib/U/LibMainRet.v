(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import Ub_code_46e98_47484.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWfk12eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ma4getrk13notk13and3h5LinuxProcessSemantics5Riscv7Preluder85bvmaphf7Z_to_bv37Corelib4Init9Datatypesv06optionma4mkstk12ex69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~hhd6msteps69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hm0floaded_segments" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Theorem main_ret_0 : ltac2:(zQ "h03!h9!jc!l5!l9!le!m5!q5!qc!r2!te!u6!hg8!hh1!hh8!hl6!hp6&>0@1$1@1$0#k0@1$b@1$1@1$0#8&@3$3@1$0#5+aKv$2@2$4@1$0#5+a&@3$3@1$0#5+8Kv$2@2$4@1$0#5+8>4regs@2$9@1$0#5@1$1@1$0#k0>3mem~0>3rom~0>0@3$5@1$1@1$0#k0@2$6^3~1@2$a@1$0#k0Z@2$d@2$9@1$0#5@1$1@1$0#k0\5regs'@2$9@1$0#5@1$1@1$0#k0@2$8@3$e$f@5$c?2fx^5Kd@3$3@1$0#k0+knhl8Kv$2@2$4@1$0#k0+knhl8@1$1@1$0#k0^4^3@5$c?2fx^1Kd@3$3@1$0#k0+knht8Kv$2@2$4@1$0#k0+knht8@1$1@1$0#k0^4^3@2$8@3$5@1$1@1$0#k0@2$6^1~2@2$a@1$0#k0Z@2$8@3$5@1$1@1$0#k0@2$6^1~1@2$a@1$0#k0Z>1r@1$1@1$0#5>0@1$7@3$5@1$1@1$0#5^1@3$3@1$0#5+1Kv$2@2$4@1$0#5+1>0@1$7@3$5@1$1@1$0#5^2~2>0@1$7@3$5@1$1@1$0#5^3~1>0@1$7@3$5@1$1@1$0#5^4@3$3@1$0#5+bKv$2@2$4@1$0#5+b@3$5@1$1@1$0#k0@2$6^6^5@2$6^a^5").
Proof.
  intros regs mem rom Ha0.
  destruct (c_lts (getr regs 21) (getr regs 0)) eqn:Hc.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_tk F_47158 D_47158 ltac:(exact Hc).
      stepn F_47164 D_47164.
      stepn F_472ac D_472ac.
      stepret F_472b0 D_472b0 (Z_to_bv 64 0x47168) ltac:(reflexivity).
      stepn F_47168 D_47168.
      stepn F_4716c D_4716c.
      stepb_tk F_47170 D_47170 ltac:(cond_compute).
      apply mst_refl.
    + repeat split; gres; try reflexivity.
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_ft F_47158 D_47158 ltac:(exact Hc).
      stepn F_4715c D_4715c.
      stepn F_47160 D_47160.
      apply mst_refl.
    + repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity).
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.
End FPX1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

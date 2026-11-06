(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import As_code_be914_bedc0 .
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWfk12eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ma4getrk13notk13and3h5LinuxProcessSemantics5Riscv7Preluder85bvmaphf7Z_to_bv37Corelib4Init9Datatypesv06optionma4mkstk12ex69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~hhd6msteps69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~hm0floaded_segments" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Theorem amain_ret_0 : ltac2:(zQ "h03!h9!jc!l5!l9!le!m5!q5!qc!r2!te!u6!hg8!hh1!hh8!hl6!hp5&>0@1$1@1$0#k0@1$b@1$1@1$0#8&@3$3@1$0#5+aKv$2@2$4@1$0#5+a&@3$3@1$0#5+8Kv$2@2$4@1$0#5+8>4regs@2$9@1$0#5@1$1@1$0#k0>3mem~0>3rom~0>0@3$5@1$1@1$0#k0@2$6^3~1@2$a@1$0#k0Z@2$d@2$9@1$0#5@1$1@1$0#k0\5regs'@2$9@1$0#5@1$1@1$0#k0@2$8@3$e$f@5$c?2fx^5Kd@3$3@1$0#k0+ruqp4Kv$2@2$4@1$0#k0+ruqp4@1$1@1$0#k0^4^3@5$c?2fx^1Kd@3$3@1$0#k0+rurh4Kv$2@2$4@1$0#k0+rurh4@1$1@1$0#k0^4^3@2$8@3$5@1$1@1$0#k0@2$6^1~2@2$a@1$0#k0Z@2$8@3$5@1$1@1$0#k0@2$6^1~1@2$a@1$0#k0Z>1r@1$1@1$0#5>0@1$7@3$5@1$1@1$0#5^1@3$3@1$0#5+1Kv$2@2$4@1$0#5+1>0@1$7@3$5@1$1@1$0#5^2~2>0@1$7@3$5@1$1@1$0#5^3~1>0@1$7@3$5@1$1@1$0#5^4@3$3@1$0#5+bKv$2@2$4@1$0#5+b@3$5@1$1@1$0#k0@2$6^6^5@2$6^a^5").
Proof.
  intros regs mem rom Ha0.
  destruct (c_lts (getr regs 21) (getr regs 0)) eqn:Hc.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_tk F_bea94 D_bea94 ltac:(exact Hc).
      stepn F_beaa0 D_beaa0.
      stepn F_bebe8 D_bebe8.
      stepret F_bebec D_bebec (Z_to_bv 64 0xbeaa4) ltac:(reflexivity).
      stepn F_beaa4 D_beaa4.
      stepn F_beaa8 D_beaa8.
      stepb_tk F_beaac D_beaac ltac:(cond_compute).
      apply mst_refl.
    + repeat split; gres; try reflexivity.
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_ft F_bea94 D_bea94 ltac:(exact Hc).
      stepn F_bea98 D_bea98.
      stepn F_bea9c D_bea9c.
      apply mst_refl.
    + repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity).
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.
End FPX1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

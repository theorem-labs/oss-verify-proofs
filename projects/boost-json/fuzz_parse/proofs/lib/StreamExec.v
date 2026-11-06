(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import ExitSim PropExec CatSim CatExec SeqExec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk13nilk14prodk14listk16optionk14Nonek14consk13natk14pair37Corelib4Init5Logicp11Ip12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsqeh3Build_machine_stateqedmachine_stateqecwrite_to_mem3h5LinuxProcessSemanticsfLinuxProcessSem3Runhhbh0advance_past_svchhbcapply_effect3h5LinuxProcessSemanticsfLinuxProcessSem5Statehmc7MemCopyhmc9mkEffectU3h5LinuxProcessSemantics5Riscv7Preludehr25bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hu16fp_csrhu17fp_regshu14mksthu16regupdhu16v_addihf2BVhf4BvWf" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_apply_write : ltac2:(zQ "hb4!h9!jc!l9!lf!m6!md!n6!nd!o4!oa!q5!q9!u5!vc!hgc!hk7!hlc!hpa!hq5!ht8!ihc!ii6!ij1!ij9!ik3!ikd!il2&>0@1$1@1$0#k0@1$5@1$1@1$0#8&@2$3@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2>4regs@2$h3@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2sv@1$5@1$1@1$0#k0>3mem~0>3rom~0>3ret@1$1@1$0#k0>3buf@1$1@1$0#k0>4data@1$4@1$1@1$0#8@3$b$d@1$f@2$h0@8$c^8@1$h5?2fx^7^6@1$6@1$1@1$0#k0@1$h4?2fx^5^4@6$h2^3@3$7~1@4$9@1$1@1$0#k0@1$4@1$1@1$0#8^2^1@1$2~1~3~3@1$2$h1@1$2@2$3@1$1@1$0#k0$8@5$h6?2fx@3$h7^8@3$h9@1$0#5+aKv$a@2$ha@1$0#5+a^3@2$h8^7+4@3$e^5^2^1^4").
Proof.
  intros regs pc sv mem rom ret buf data.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
End FPX1.
(* [comment removed for export] *)

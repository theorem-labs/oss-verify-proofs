(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from SymDrive.v for the budget-premise witness: the same statements and proof scripts over BudgetWit.Rzb.realizes; only the name tables change. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SymExec Frame RefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg SymExec2 SymExec2Sound SymRun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos35stdpp9bitvectorbdefinitionsje2bv03nat03nil37Corelib5Lists7ListDefma3nth79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~o78sidecond04prod06option37Corelib4Init5Logictf2eqo76kentry04bool04pairo77scriptso79sym_statehe1Z3h5LinuxProcessSemanticsfLinuxProcessSem3Runhi75mkCfg3h5LinuxProcessSemantics5Riscv7Preludehlc5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hob4mkst69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~hse8realizeso75s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ihd7know_okihd7regs_okihd9scs_denotje7Z_to_bv04None04true3h5LinuxProcessSemanticsfLinuxProcessSem5Stateipb5Modelipb8m_haltedipb9m_vm_lazyhse4TSeto72SSo75carryo73envo74expro74s_pco76s_regso76sentryo78sym_execihd9mem_denoto74lres04Some05falseo7bknow_lookuptf3and37Corelib4Init5Peanojm62leo72SA06lengthtf2ex3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejp2dbytes_le_to_Zhob3rdn79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive5Drive~~~~~~jt95kreado76adenoto76edenotihd4flat46Stdlib6ZArith6BinInt1Zkjd6of_nat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsklfh0word_to_le_byteskjd3addhob6v_addikjd2lekjd2ltkjd3powtf1Ije2BVje4BvWfhob6regupdo74ridxo76sr_updma3mapma3seqhob4getr37Corelib4Init3Natlgd3addo74ELito74EVar46Stdlib5Arith8PeanoNat3Natlj43eqb36Stdlib5Lists4Listll67existsb69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~ln4cexpr_vars_ltln4asr_vars_lto73Envln47vals_evll62In03apptf3notjm62ltjt99junk_valsjt9fsr_after_call_j3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypemh37Segment79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BudgetWit3Rzbml38realizes" s.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SymDrive.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.Rzb.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Drive.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!h8!mk8@1$0$1").
Context {SC : StepCfg}.

Theorem rz_run : ltac2:(zQ "i72!j7!h8!lb!s6!t1!t7!v3!v8!hg1!m5!hg7!hgd!hh7!m0!hi3!hl3!ho2!hs6!mod!ih5!im2!imd!in8!io5!iof!ip5!is9!it2!ite!iub!iv3!iv8!jg0!jg6!jgd!jh4!jhd!ji6!jj1&>0@1$2@1$0#k0@1$5@1$2@1$0#8&@2$4@1$2@1$0#k0@1$2@1$0#k0>4fuel$d>5stops@1$1$e>3scr$b>2pc$e>2sr@1$1$i1>2kn@1$1$7>2nx$d>3ss'$c>3scs@1$1$3>4scr'$b>3kn'@1$1$7>4scs2@1$1$3>3hs2@1$1$8>1E$i0>1M~0>3rom~0>1R@2$h0@1$0#5@1$2@1$0#k0>5model$ha>1T$hd>0@3$6@2$4@2$4$c@1$1$3$b@7$i5?4segs^h3$h9^h2^h1@5$he^h0^f@1$9$i4^e^d@1$9$3@4$a@2$4$c@1$1$3$b@4$a$c@1$1$3^c^b^a>0@3$6@2$4@2$4@1$1$7@1$1$3@1$1$8@3$hf@1$h3^d^f@1$9$8@4$a@2$4@1$1$7@1$1$3@1$1$8@4$a@1$1$7@1$1$3^a^9^8>0@3$h5^8^h1^5>0@4$h4?4segs^9^8^h1>0@4$h6?4segs^9^a^f>0@4$h6?4segs^a^b^d>0@3$6@1$5@1$2@1$0#k0@1$hb^8@1$h8@1$2@1$0#k0>0@3$6@1$1~1@1$hc^9@1$9~1>0>2R'@2$h0@1$0#5@1$2@1$0#k0>2M'~0>0@3$h5^h0@1$i3^h6^2>0@4$h4?4segs^h1^2^h4>0@3$6~0^3@3$i6^h2^h1@1$h3^h8@4$h2?4segs?2SC@2$f@5$h1?2fx^5@2$h7@1$0#k0@1$i2^h9^4^h1^f^e@4$h2?4segs?2SC@2$f@5$h1?2fx^c@2$h7@1$0#k0^h9^e^d^b^a").
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  ndestruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [|reflexivity].
  eapply carry_after; eassumption.
Qed.

End Drive.

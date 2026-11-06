(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsIface AsDriverLaws AsMainPre.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12ex01Zk13and37Corelib4Init9Datatypesm36option3h5LinuxProcessSemanticsfLinuxProcessSem3Runo49cfg_model3h5LinuxProcessSemantics5Riscv7Preluderc5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~ua5as_Stua3asr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~hj58HeapCeil46Stdlib6ZArith6BinInt1Zhnc2lek12eq3h5LinuxProcessSemanticsfLinuxProcessSem2Fshpf2Fso46cfg_mso46config3h5LinuxProcessSemanticsfLinuxProcessSembStackLayouthu29EntryDraw3h5LinuxProcessSemanticsfLinuxProcessSem5Stateii39ProcInputii37in_argvii35in_fsii34m_fs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAsDriverLaws~~~~~~ina8ADRV_CNTina9ADRV_LIVEinah0asan_driver_lawsuafas_LIVE_CNT_MAXuabas_LIVE_MAXuacasan_rt_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsMainPre~~~~~~jh95AMpre" s.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Instance.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  (* [comment removed for export] *)
  Variable P_main : ltac2:(zQ "50!h9!jc!ht9!ih6!il1>0@1$1@1$0#k0>0@1$1@1$0#k0>0@1$1@1$0#k0>0$3>0$4>0$2P").

  (* [comment removed for export] *)
  Definition as_instance_stmt : ltac2:(zQ "00P") := ltac2:(zQ "hc1!h9!jc!l5!la!ld!nb!r0!u2!hi7!hif!hn0!hp4!hpa!hsa!ht0!ht9!ih6!il1!ile!im9!in2!irc!is8!it5!iua!ivc!jga!jl8&>0@1$1@1$0#k0@1$5@1$1@1$0#8>3sp0@1$1@1$0#k0>4brk0@1$1@1$0#k0>5mbase@1$1@1$0#k0>5rdraw$h0>3inp$h1>1c$f>0@6?6P_main^6^5^4^3^2^1@2$2$a\5HCEIL$a@2$2$9\1H$9@2$2@1$8^1\2s0@1$8^1@2$2@2$7@1$0#5@1$1@1$0#k0\4regs@2$7@1$0#5@1$1@1$0#k0@2$2~0\3mem~0@2$2$3\1B$3@2$2$3\3tid$3@2$2$3\3can$3@2$4@2$ha^8^7@2$4@1$h7^7@2$4@2$4@2$b$h6@1$h9^7@2$b$h5@1$h8^7@2$4@d$hb?2fx^8^7^f@1$h2^b^6@1$e^a@1$6^a^5^4^3^2^1@3$c$d@1$h4@1$6^a@1$h3^b").
End Instance.

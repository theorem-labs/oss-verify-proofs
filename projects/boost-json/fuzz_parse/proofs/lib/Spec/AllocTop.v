(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Decode.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk44listk44prod37Corelib4Init5Logicma2eq3h5LinuxProcessSemanticsfLinuxProcessSem5Stateo39ProcInputo39alloc_topo3ainit_modelo38m_vmmapso3estack_max_size46Stdlib6ZArith6BinInt1Zv23subhfbbv_unsignedo3csp_window_lo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~hid8CEIL_MINo3csp_window_hihid8CEIL_MAXv22lema3and3h5LinuxProcessSemanticsfLinuxProcessSem3Runhpc8valid_spo37FdEntryo35Modelo38with_fds3h5LinuxProcessSemanticsfLinuxProcessSem2Fshv12Fso37with_fso3bInputStreamo3awith_stdino3bwith_haltedo38with_tido37PipeBufo3awith_pipeso3bwith_killedo35Credso3awith_credso3awith_clocko3cwith_sigmasko3h4with_sigabrt_pendingk44boolo3h3with_abort_terminalhv14patho3cwith_statpino36VmMapso3fvm_forget_range5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapjheh0forget_vm_rangesjheh1with_mmap_backingo3bwith_vmmapso3fwith_vm_backingo3bvm_add_lazyjheebrk_model_nextjhedwith_brk_nextjheh5with_mmap_replacementjheh3with_mmap_destroyedjheh9mmap_fixed_destroyed_nextjheh2mmap_fixed_rw_nextjheh7mmap_fixed_rw_span_nextjhehdmmap_fixed_noaccess_span_next5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm8Mprotectkn3h3mprotect_model_nexto3cmkVmMapsFullo3avm_init_sp" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma alloc_top_init : ltac2:(zQ "d0!h9!jc!k1!lc!m3!ne!r1!rd!s9!t6!u1!hga!hh0>8reserved@1$3@2$4@1$1@1$0#k0@1$1@1$0#k0>4brk0@1$1@1$0#k0>5mbase@1$1@1$0#k0>2sp@1$1@1$0#k0>3lim$2>3inp$6@3$5$2@1$7@1$9@6$8^6^5^4^3^2^1@2$b@2$c@1$0#k0^3$a").
Proof. intros. rewrite m_vmmaps_init_model. reflexivity. Qed.

Lemma stack_max_size_val : ltac2:(zQ "30!ne!k1!u1@3$0$1$2+ogggg0").
Proof. reflexivity. Qed.

Lemma CEIL_MIN_val : ltac2:(zQ "60!ne!k1!hhe!u1!hma!hga@3$0$1$4@2$5$2$3").
Proof. reflexivity. Qed.

Lemma CEIL_MAX_val : ltac2:(zQ "60!ne!k1!hn6!u1!ho5!hga@3$0$1$4@2$5$2$3").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_top_range : ltac2:(zQ "a0!h9!u1!hp1!hga!hh0!hp6!hs8!ho5!hma!jc>2sp@1$9@1$0#k0>0@1$6^1@2$5@2$2$8@2$3@2$4@1$0#k0^2$1@2$2@2$3@2$4@1$0#k0^2$1$7").
Proof.
  intros sp (Hlo & Hhi & _). rewrite CEIL_MIN_val, CEIL_MAX_val. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma alloc_top_with_fds : ltac2:(zQ "b0!rd!t6!lc!m3!ne!h9!k1!ht4!hte!hu6!jc>1v@1$2@2$3@1$a@1$5#k0$7>1m$8@3$4$6@1$0@1$1@2$9^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_fds. reflexivity. Qed.
Lemma alloc_top_with_fs : ltac2:(zQ "70!rd!t6!ne!k1!ihc!hte!ii2>1v$4>1m$5@3$2$3@1$0@1$1@2$6^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_fs. reflexivity. Qed.
Lemma alloc_top_with_stdin : ltac2:(zQ "70!rd!t6!ne!k1!iic!hte!ija>1v$4>1m$5@3$2$3@1$0@1$1@2$6^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_stdin. reflexivity. Qed.
Lemma alloc_top_with_halted : ltac2:(zQ "80!rd!t6!ne!h9!k1!hte!ik7!jc>1v@1$7@1$3#k0>1m$5@3$2$4@1$0@1$1@2$6^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_halted. reflexivity. Qed.
Lemma alloc_top_with_tid : ltac2:(zQ "80!rd!t6!ne!h9!k1!hte!il5!jc>1v@1$7@1$3#k0>1m$5@3$2$4@1$0@1$1@2$6^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_tid. reflexivity. Qed.
Lemma alloc_top_with_pipes : ltac2:(zQ "b0!rd!t6!lc!m3!ne!h9!k1!hte!im0!ima!jc>1v@1$2@2$3@1$a@1$5#k0$8>1m$7@3$4$6@1$0@1$1@2$9^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_pipes. reflexivity. Qed.
Lemma alloc_top_with_killed : ltac2:(zQ "80!rd!t6!ne!h9!k1!hte!in7!jc>1v@1$7@1$3#k0>1m$5@3$2$4@1$0@1$1@2$6^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_killed. reflexivity. Qed.
Lemma alloc_top_with_creds : ltac2:(zQ "70!rd!t6!ne!k1!io5!hte!iod>1v$4>1m$5@3$2$3@1$0@1$1@2$6^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_creds. reflexivity. Qed.
Lemma alloc_top_with_clock : ltac2:(zQ "80!rd!t6!ne!h9!k1!hte!ipa!jc>1v@1$7@1$3#k0>1m$5@3$2$4@1$0@1$1@2$6^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_clock. reflexivity. Qed.
Lemma alloc_top_with_sigmask : ltac2:(zQ "80!rd!t6!ne!h9!k1!hte!iq7!jc>1v@1$7@1$3#k0>1m$5@3$2$4@1$0@1$1@2$6^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_sigmask. reflexivity. Qed.
Lemma alloc_top_with_sigabrt_pending : ltac2:(zQ "60!rd!t6!ne!k1!hte!ir6>1m$4@3$2$3@1$0@1$1@1$5^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_sigabrt_pending. reflexivity. Qed.
Lemma alloc_top_with_abort_terminal : ltac2:(zQ "70!rd!t6!ise!ne!k1!hte!it5>1v$2>1m$5@3$3$4@1$0@1$1@2$6^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_abort_terminal. reflexivity. Qed.
Lemma alloc_top_with_statpin : ltac2:(zQ "a0!rd!t6!lc!ne!h9!k1!iuc!hte!iv4!jc>1p$6>2bs@1$2@1$9@1$4#8>1m$7@3$3$5@1$0@1$1@3$8^3^2^1@1$0@1$1^1").
Proof. intros. rewrite m_vmmaps_with_statpin. reflexivity. Qed.

(* [comment removed for export] *)
Lemma m_vmmaps_vm_forget_range : ltac2:(zQ "60!k1!t6!ne!hte!jg3!jgc>2lo$0>2hi$0>1m$3@3$2$4@1$1@3$5^3^2^1@1$1^1").
Proof. reflexivity. Qed.
Lemma m_vmmaps_forget_vm_ranges : ltac2:(zQ "90!h9!t6!jc!lc!m3!ne!hte!jg3!jl2>2rs@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0>1m$6@3$5$7@1$1@2$8^2^1@1$1^1").
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. apply m_vmmaps_vm_forget_range.
Qed.
Lemma m_vmmaps_with_mmap_backing : ltac2:(zQ "70!h9!jc!t6!ne!hte!jg3!jm7>5flags@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m$4@3$3$5@1$2@4$6^4^3^2^1@1$2^1").
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma alloc_top_with_vmmaps : ltac2:(zQ "70!rd!ne!k1!hte!jg3!t6!jnd>1h$4>1m$3@3$1$2@1$0@1$5@2$6^2^1@1$0^2").
Proof. intros. rewrite m_vmmaps_with_vmmaps. reflexivity. Qed.
Lemma alloc_top_with_vm_backing : ltac2:(zQ "a0!h9!jc!lc!rd!t6!m3!ne!k1!hte!job>2lz@1$2@2$5@1$1@1$0#k0@1$1@1$0#k0>2mt@1$2@1$1@1$0#k0>1m$8@3$6$7@1$3@1$4@3$9^3^2^1@1$3@1$4^1").
Proof. reflexivity. Qed.
Lemma alloc_top_vm_add_lazy : ltac2:(zQ "80!h9!rd!t6!jc!ne!k1!hte!jpd>1a@1$3@1$0#k0>1n@1$3@1$0#k0>1m$6@3$4$5@1$1@1$2@3$7^3^2^1@1$1@1$2^1").
Proof. reflexivity. Qed.
Lemma alloc_top_vm_forget_range : ltac2:(zQ "60!k1!rd!t6!ne!hte!jgc>2lo$0>2hi$0>1m$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1").
Proof. reflexivity. Qed.
Lemma alloc_top_forget_vm_ranges : ltac2:(zQ "a0!h9!rd!t6!jc!lc!m3!ne!k1!hte!jl2>2rs@1$4@2$5@1$3@1$0#k0@1$3@1$0#k0>1m$8@3$6$7@1$1@1$2@2$9^2^1@1$1@1$2^1").
Proof. intros. rewrite m_vmmaps_forget_vm_ranges. reflexivity. Qed.
Lemma alloc_top_with_mmap_backing : ltac2:(zQ "80!h9!jc!rd!t6!ne!k1!hte!jm7>5flags@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m$6@3$4$5@1$2@1$3@4$7^4^3^2^1@1$2@1$3^1").
Proof. intros. rewrite m_vmmaps_with_mmap_backing. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_top_brk_model_next : ltac2:(zQ "70!h9!rd!jc!ne!k1!jg3!jqb>1h$5>3req@1$2@1$0#k0>1r@1$2@1$0#k0@3$3$4@1$1@3$6^3^2^1@1$1^3").
Proof. reflexivity. Qed.
Lemma alloc_top_with_brk_next : ltac2:(zQ "80!h9!rd!t6!jc!ne!k1!hte!jrd>1m$6>3req@1$3@1$0#k0>1r@1$3@1$0#k0@3$4$5@1$1@1$2@3$7^3^2^1@1$1@1$2^3").
Proof.
  intros. unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges, m_vmmaps_with_vmmaps.
  apply alloc_top_brk_model_next.
Qed.
Lemma alloc_top_with_mmap_replacement : ltac2:(zQ "80!h9!jc!rd!t6!ne!k1!hte!jse>5flags@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m$6@3$4$5@1$2@1$3@4$7^4^3^2^1@1$2@1$3^1").
Proof. intros. unfold with_mmap_replacement. rewrite m_vmmaps_with_mmap_backing. reflexivity. Qed.
Lemma alloc_top_with_mmap_destroyed : ltac2:(zQ "90!h9!rd!jc!ne!k1!hte!jg3!t6!ju8>1a@1$2@1$0#k0>1n@1$2@1$0#k0>2h'$6>1m$5@3$3$4@1$1@1$7@4$8^4^3^2^1@1$1^2").
Proof. intros. unfold with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity. Qed.
Lemma alloc_top_mmap_fixed_destroyed_next : ltac2:(zQ "70!h9!rd!jc!ne!k1!jg3!kg0>1h$5>4addr@1$2@1$0#k0>1n@1$2@1$0#k0@3$3$4@1$1@3$6^3^2^1@1$1^3").
Proof. reflexivity. Qed.
Lemma alloc_top_mmap_fixed_rw_next : ltac2:(zQ "70!h9!rd!jc!ne!k1!jg3!khe>1h$5>4addr@1$2@1$0#k0>1n@1$2@1$0#k0@3$3$4@1$1@3$6^3^2^1@1$1^3").
Proof. reflexivity. Qed.
Lemma alloc_top_mmap_fixed_rw_span_next : ltac2:(zQ "70!h9!rd!jc!ne!k1!jg3!kj5>1h$5>4addr@1$2@1$0#k0>1n@1$2@1$0#k0@3$3$4@1$1@3$6^3^2^1@1$1^3").
Proof. reflexivity. Qed.
Lemma alloc_top_mmap_fixed_noaccess_span_next : ltac2:(zQ "70!h9!rd!jc!ne!k1!jg3!kl1>1h$5>4addr@1$2@1$0#k0>1n@1$2@1$0#k0@3$3$4@1$1@3$6^3^2^1@1$1^3").
Proof. reflexivity. Qed.
Lemma alloc_top_mprotect_model_next : ltac2:(zQ "80!h9!rd!t6!jc!ne!k1!hte!kqb>1m$6>4addr@1$3@1$0#k0>1n@1$3@1$0#k0@3$4$5@1$1@1$2@3$7^3^2^1@1$1@1$2^3").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_top_same_sp : ltac2:(zQ "a2!h9!jc!lc!m3!k1!rd!ne!jg3!ks3!kt2&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1h$7>2rs~1>4maps~1>2na~1>2sb@1$1@1$0#k0>1b@1$1@1$0#k0>3lim$4>2mb@1$1@1$0#k0@3$6$4@1$5@8$8^7^6^5^4^3^2^1@1$9^8@1$5^8").
Proof. reflexivity. Qed.

#[export] Hint Rewrite alloc_top_with_fds alloc_top_with_fs alloc_top_with_stdin alloc_top_with_halted
  alloc_top_with_tid alloc_top_with_pipes alloc_top_with_killed alloc_top_with_creds alloc_top_with_clock
  alloc_top_with_sigmask alloc_top_with_sigabrt_pending alloc_top_with_abort_terminal alloc_top_with_statpin
  alloc_top_with_vmmaps alloc_top_with_vm_backing alloc_top_vm_add_lazy alloc_top_vm_forget_range
  alloc_top_forget_vm_ranges alloc_top_with_mmap_backing alloc_top_with_brk_next alloc_top_with_mmap_replacement
  alloc_top_with_mmap_destroyed alloc_top_mmap_fixed_destroyed_next alloc_top_mmap_fixed_rw_next
  alloc_top_mmap_fixed_rw_span_next alloc_top_mmap_fixed_noaccess_span_next alloc_top_mprotect_model_next
  alloc_top_brk_model_next alloc_top_same_sp : alloc_top.
(* [comment removed for export] *)

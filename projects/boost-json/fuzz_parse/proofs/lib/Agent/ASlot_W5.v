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
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04meta37Corelib4Init9Datatypesk44None04aptr0am_set_next0am_set_prev37Corelib4Init5Logico12eq0cget_meta_rec06mstatek44Some37Corelib7Numbers7BinNumsr71Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W5~~~~~~t43clr07LActive07dequeue06m_next04optr08put_meta0aset_activeo13not06active06m_prev" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition clr : ltac2:(zQ "10!je>1r$0$0") := ltac2:(zQ "50!lc!m3!m9!n5!je\1r$4@2$3@1$0$1@2$2@1$0$1^1").

Lemma dequeue_self_eq : ltac2:(zQ "e0!m3!p5!pa!q8!lc!r0!t0!hh5!hhb!hi4!hid!hj5!hjb!hk5>2sc$6>1g$0>2st$3>0@3$1$b@1$a@2$2^1^2@2$5$0^2@3$1$3@3$9@1$8^4^3^2@3$c^3@1$7@2$2^2^3@3$d^4@1$4$0^2").
Proof. intros sc g st.
  intros GN. unfold dequeue. rewrite GN. cbn [optr_eqb negb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbn [negb set_head].
  rewrite upd_meta_put. reflexivity.
Qed.

Lemma dequeue_other_eq : ltac2:(zQ "h20!m3!r0!p5!pa!q8!hj5!hjb!hl1!t0!hh5!hhb!hl7!hi4!hid!hlf!m9!n5!hk5>2sc$8>1g$0>2nx$0>2pv$0>2st$4>0@3$2$5@1$d@2$3^1^4@2$1$0^3>0@3$2$5@1$e@2$3^2^5@2$1$0^3>0@1$7@3$2$0^5^6>0@1$7@3$2$0^5^7>0@3$2$5@2$b^5^9@2$1$0^8@3$2$4@3$c@1$a^a^9^6=3st1$4@3$6^7@2$f@2$1$0^8@2$3^6^7^6=3st2$4@3$6^9@2$h0@2$1$0^8@2$3^1^9^1=3st3$4@3$h1^c@2$1$0^a^1@3$6^c@1$9@2$3^9^c^1").
Proof. intros sc g nx pv st.
  intros GN GP NEn NEp HA. unfold dequeue. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head set_head].
  rewrite !upd_meta_put.
  match goal with |- context [optr_eqb (active ?s sc) (Some g)] => change (active s sc) with (active st sc) end.
  rewrite HA. cbn [optr_eqb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbv zeta.
  f_equal. f_equal. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
  rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity.
Qed.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

End DEQ.
(* [comment removed for export] *)

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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_bigw.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A3 ASlot_W10.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos46Stdlib6ZArith6BinInt1Zhf2lt37Corelib4Init5Logicjc3and01Zhf3pow35stdpp9bitvectorbdefinitionslf7Z_to_bvjc2eq3h5LinuxProcessSemantics5Riscv5Instrob6M_DIVU3h5LinuxProcessSemantics5Riscv3Semr87mul_div79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~u42wzhf3divhf2lelf2bv37Corelib4Init9Datatypeshjb4boolhf3subhf3ltb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hm74UNIThm76mstatehm7ec_mmap_counterhm7cm_set_maplenhm74mctxhm7h0set_mmap_counterhm73u32hm77upd_ctxhm78upd_metahf3addhf6shiftr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_W174MMOK~~~~~~ii35mm_ai" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma divu_word : ltac2:(zQ "d0!h9!j7!l0!l6!l9!nc!o6!qf!ta!hi6!hib!hj1!hj6>1a$3>1b$3>0@2$2@2$bZ^2@2$1^2@2$4+2+k0>0@2$2@2$1Z^2@2$1^2@2$4+2+k0@3$6@1$c@1$0#k0@4$8@1$0#k0$7@2$5@1$0#k0^4@1$9^3@2$5@1$0#k0@2$a^4^3").
Proof. intros a b.
  intros Ha Hb. unfold mul_div. rewrite (wz_unsigned b) by lia. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned, (wz_unsigned b), unsigned_lit, Z_to_bv_unsigned by lia.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr) (rid : N) (r0 : region).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : ltac2:(zQ "20!hj1!l0@2$1@2$0+1?3cnt@2$0?3cnt+i0").
Hypothesis SZ : ltac2:(zQ "40!l0!hj1!j7!l9@2$0@2$1+h0?4size@2$2?4size@2$3+2+h2").
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

Definition mm_ai : ltac2:(zQ "10!l6$0") := ltac2:(zQ "60!hl3!l6!hlb!hm1!hq5!hib=2ai$1@2$2@2$5@2$2+hgg0$4?4size+1=2ai$1M0\0$0$1@2$3@2$2?3cnt+1^1@2$2?3cnt+1^1M0\0$0$1@2$3^1ZZ^1").

Definition mm_st4 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "90!hr7!hs9!ht9!hu1!hv6!hvd!ig8!ih4!iha@2$5\1c$2@2$3@1$4@2$7@1$0^1+1^1@3$6?2mt@1$1@2$8?2nd+c?3st2").

Lemma mm_ai_range : ltac2:(zQ "40!ima!hj1!l0!hlb@2$2@2$1Z$0@2$1$0@2$3?3cnt+1").
Proof.
  unfold mm_ai, UNIT. change (4096 - 16) with 4080.
  pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)).
  destruct (Z.ltb_spec (cnt - 1) (4080 / size - 1)); [destruct (Z.ltb_spec (cnt - 1) 0)| destruct (Z.ltb_spec (4080 / size - 1) 0)]; lia.
Qed.
End MMOK.
(* [comment removed for export] *)

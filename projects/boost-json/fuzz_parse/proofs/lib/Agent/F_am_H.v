(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require KStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_am_A F_am_K F_am_C F_am_F F_am_G.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~hc7brk_ans04Npos35stdpp9bitvectorbdefinitionsm92bv37Corelib4Init9Datatypesob6optionob4prodob4consob3nilob4pair3h5LinuxProcessSemanticsfLinuxProcessSem3Runs7bapply_zeroshcdbrk_new_pages79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hh12wam97Z_to_bv37Corelib4Init5Logichlb2eq46Stdlib6ZArith6BinInt1Zhn52lthlb3andhn53addhn54landhn56modulohn53opphn53powm9bbv_unsignedob4Somehn52leob4bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hu39fixed_ansob4truehc8errno_ofob5falsehlb2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~ikc4resp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_H~~~~~~ip06fx_rel79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdF_mm_syscalls~~~~~~it9bfixed_shapehu3edec_mmap_fixed" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

(* [comment removed for export] *)
Definition brk_res : ltac2:(zQ "20!h9!l9>3cur$0>3req$0>1a$1$0") := ltac2:(zQ "20!h9!l9\3cur$0\3req$0\1a$1M1\1a$1$0^1^2^3").
Definition brk_mem : ltac2:(zQ "50!m3!h9!o6!q3!l9>3cur$1>3req$1>1a$4>0@1$2@1$0#k0@1$3@1$2@1$0#8") := ltac2:(zQ "d2!m3!o6!h9!qc!q3!l9!r3!ra!s0!v3!hg1!hkb!hl1&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0\3cur$2\3req$2\1a$5M5\1a$5~0^1M4\1x@1$4@2$3$2$2~0@2$a^3^2\1p@2$3$2$2M3\1p@2$3$2$2~0^1\2lo$2\1n$2@2$9?1m@3$6~1@4$8@1$1@1$0#k0@1$1@1$0#k0@1$b^2@2$c@1$0#k0^1@1$7~1?1m?1m").
End BRKNODES.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_neg_aligned : ltac2:(zQ "c0!h9!hmf!m3!hod!hp3!hpa!hq1!hq9!hr3!hra!hl1!hs1>3cur$0>0@2$4@2$3Z^1@2$3^1@2$9+2+k0>0@3$1$0@2$7^2+hgg0Z@3$1$0@2$6@2$b@1$2#k0@2$a@1$2#k0@2$5Z@1$8^3+vvfZ").
Proof. intros cur.
  intros H AL. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  replace ((0 + - cur) mod 2^64) with ((2^52 - cur / 4096) * 4096) by (Z.div_mod_to_equations; lia).
  change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. apply Z.mod_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma brk_new_pages_aligned : ltac2:(zQ "b0!h9!hmf!qc!hq9!hsf!q3!s0!hg1!hpa!ht6!hod>3cur$0>1n$0>0@2$9Z^2>0@2$aZ^2>0@3$1$0@2$3^4+hgg0Z>0@3$1$0@2$3^4+hgg0Z@3$1@1$5@2$2$0$0@2$7^6@2$8^6^5@2$4@2$2$0$0@4$6$0$0^6^5").
Proof. intros cur n.
  intros C0 N0 CA NA. unfold brk_new_pages. rewrite <- !KStep.round_up_pg_eq.
  rewrite !KStep.round_up_pg_aligned by (auto; rewrite Z.add_mod, CA, NA by lia; reflexivity).
  replace (cur <? cur + n) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition fx_rel : ltac2:(zQ "50!htc!m3!h9!ihf!o6>1A$2>1a$3>1r@1$4@1$1#k0>1u$0P") := ltac2:(zQ "d1!h9!hmf!htc!hp3!m3!ihf!hsf!q3!iic!ij3!o6!ije!hl1&@3$1@1$7$0@1$9^3@2$6$0^1\1A$0\1a$5\1r@1$a@1$4#k0\1u$2M5\1a$5P^3\1e$0@2$3~0@3$1$2^2$b@2$3@3$1@1$a@1$4#k0^2@2$c@1$4#k0^4@3$1$2^1$8\1e$0@2$3~0@3$1$2^2$8").
(* [comment removed for export] *)
Lemma dec_mmap_fixed_shape : ltac2:(zQ "e0!ihf!htc!hmf!ik6!m3!h9!io8!o6!hsf!q3!hp3!isf!jhf!jie>1A$5>1L$5>3rsp$6>1a$0>0@3$2@1$9$0@3$d^4^3^2@2$8$0^1@2$3@1$7@1$4#k0\1r@1$7@1$4#k0@2$3$1\1u$1@2$a@4$b^7^4^2^1@3$2$6^5@4$c^7^6^2^1").
Proof. intros A L rsp a.
  unfold dec_mmap_fixed, fixed_shape. destruct rsp as [r ws zs us cs ci]. intros H. Decode.dec_cc cs ci H.
  destruct ws; [| discriminate]. destruct zs; [| discriminate]. destruct us as [|[ua un] us].
  - destruct (errno_of r) eqn:E; [| discriminate]. inversion H; subst. exists r, false. cbn. rewrite E. auto.
  - destruct us; [| discriminate]. destruct (bv_eqb ua (Z_to_bv 64 A) && bv_eqb un (Z_to_bv 64 (mmap_len L))) eqn:E; [| discriminate].
    apply andb_prop in E. destruct E as [E1 E2]. apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. subst ua un.
    destruct (errno_of r) eqn:E.
    + inversion H; subst. exists r, true. cbn. rewrite E. auto.
    + destruct (bv_eqb r (Z_to_bv 64 A)) eqn:E3; [| discriminate]. apply Fs.bv_eqb_eq in E3. inversion H; subst. exists (Z_to_bv 64 A), true. cbn. auto.
Qed.

(* [comment removed for export] *)

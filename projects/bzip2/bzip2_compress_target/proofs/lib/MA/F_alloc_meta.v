(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode SFMisc.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require MallocKit_A2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require MallocModel_B.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocKit_B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocModel_B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocKit_B2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocKit_B3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.MallocModel_B.F_ntf_B.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require F_am_A F_am_K F_am_K2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require F_am_G.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require F_am_D F_am_E.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require F_am_G.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA Require F_am_G F_am_H F_am_P.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_A OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_K OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_K2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_G.F_am_C OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_D OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_E OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_G.F_am_F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_G OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_H OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MA.F_am_P.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).

(* [comment removed for export] *)
Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
  magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof. intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof.
  intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
  revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
  destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : AMpre st.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis KH : forall st1 mo s' ms',
     am_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     implT o (k st1 mo) s' Q ms'.

Definition FP (stX : mstate) (a : Z) : Prop := alloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

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
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End ASM.

(* [comment removed for export] *)

End ACeilS1.

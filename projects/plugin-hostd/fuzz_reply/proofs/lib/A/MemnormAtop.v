(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormAtop.v (a working branch 30a1993588f, c5 + memnorm; file sha256 ad8520183d38) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Theorem Labs, 2026-10 (task MEMNORM): the memnorm-kept twin of AGtopE's primary-size Allocate composition.
   rule 24: no function proved (kind: top-level composition over arm hypotheses).

   AGtopE.aalloc_prim_realizes_e_of_arms splits one Allocate call into the four arms (hit / miss on the g and k paths)
   and concludes ErrnoG.aalloc_prim_realizes_e.  [aalloc_prim_realizes_em_of_arms] is the same case split over the
   arms' memnorm-kept forms, concluding MemnormT.aalloc_prim_realizes_em: ErrnoG.alloc_leaf_e plus
   `memnorm mem -> memnorm mem'` (MemnormT.alloc_leaf_em).  The arms are Section hypotheses, as in AGtopE; the script
   is AGtopE.v:85-103 (copied, marked).  The closed cgif corollary is MemnormAtopcgif.v.  AGtopE is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AllocG AGtop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoG MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
(* `Require ErrnoG` reaches YA09, whose last non-local `Ltac Zify...flag ::=` leaves the euclidean-division
   conversion OFF (YA09.v:3351); AGtop's lia calls were written with it ON.  #[local], so nothing escapes
   (BUILD.md (sha256 a15bb0f1b85d; internal record), 'Tactic hygiene'). *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable oomb : Z.
Variable cf : Z.
Hypothesis HCF : cf = 0 \/ cf = 1.
(* field round 3 part 3b: the Allocate contract's memory precondition (MemnormT's MP); each arm may read it *)
Variable MP : (word -> option byte) -> Prop.

(* The goal of one call, with errno kept on the grant branch and memnorm kept. *)
Let GOALem (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (n : Z) (tr : list Z) : Prop :=
  amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x31bd8 regs mem md)
    (MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr).
Let PRE (inst so bp : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (n : Z) (tr : list Z) : Prop :=
  alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr.

(* The uninited-cache refutation, as in AGtop. *)
Hypothesis UNINIT : forall inst ly S W mem md c, ARX inst ly S W mem md -> 1 <= c <= 31 ->
  st_cache_inited S = false -> pc_chunks (cache S c) = [].

(* The four arms, at their memnorm-kept forms. *)
Hypothesis ARM_HITG_em : forall inst so bp ly S W regs mem md n tr l off, cf = 0 \/ cf = 1 ->
  PRE inst so bp ly S W regs mem md n tr -> MP mem -> 49 <= n <= 64512 ->
  st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  GOALem inst ly S W regs mem md n tr.
Hypothesis ARM_HITK_em : forall inst so bp ly S W regs mem md n tr l off, cf = 0 \/ cf = 1 ->
  PRE inst so bp ly S W regs mem md n tr -> MP mem -> 0 <= n <= 48 ->
  st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  GOALem inst ly S W regs mem md n tr.
Hypothesis ARM_MISSG_em : forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  PRE inst so bp ly S W regs mem md n tr -> MP mem -> 49 <= n <= 64512 ->
  pc_chunks (cache S (chunk_class n)) = [] ->
  GOALem inst ly S W regs mem md n tr.
Hypothesis ARM_MISSK_em : forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  PRE inst so bp ly S W regs mem md n tr -> MP mem -> 0 <= n <= 48 ->
  pc_chunks (cache S (chunk_class n)) = [] ->
  GOALem inst ly S W regs mem md n tr.

Theorem aalloc_prim_realizes_em_of_arms :
  MemnormT.aalloc_prim_realizes_em tfibsegs B U mt ARX AOX rpre nmax lmax lpost 0x31bd8 oomb 8 1 cf MP.
Proof.
(* copy of AGtopE.v:85-102, with the arms' _em names; part 3b passes the call's MP to the arm *)
intros inst so bp ly S W regs mem md n tr HPRE HMP Hn64.
pose proof (proj1 HPRE) as HAR.
assert (Hn0 : 0 <= n) by (clear - HPRE; unfold alloc_pre in HPRE; decompose [and] HPRE; lia).
assert (Nrange : 0 <= n <= 64512) by lia.
pose proof (primary_geometry n ltac:(lia) (AGtop.prim_fp_g n Nrange)) as (Hcl & _).
destruct (pc_chunks (cache S (chunk_class n))) as [|x t] eqn:El.
- destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
  + exact (ARM_MISSG_em inst so bp ly S W regs mem md n tr HCF HPRE HMP ltac:(lia) El).
  + exact (ARM_MISSK_em inst so bp ly S W regs mem md n tr HCF HPRE HMP ltac:(lia) El).
- assert (LX : exists l off, x :: t = l ++ [off])
    by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
  destruct LX as (l & off & LX). rewrite LX in El.
  destruct (st_cache_inited S) eqn:CI.
  + destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
    * exact (ARM_HITG_em inst so bp ly S W regs mem md n tr l off HCF HPRE HMP ltac:(lia) CI El).
    * exact (ARM_HITK_em inst so bp ly S W regs mem md n tr l off HCF HPRE HMP ltac:(lia) CI El).
  + exfalso. rewrite (UNINIT inst ly S W mem md (chunk_class n) HAR ltac:(lia) CI) in El.
    destruct l; discriminate El.
Qed.
End b.
End a.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormAtop.v (a working branch 29b7505aa27, file sha256 ad8520183d38) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at 3d44582d342f) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc ced0368250cb6538 (a working branch b85bfdee67c4), --assume-source, --resolve the internal file resolve-102.txt (0 lines name this file); 2 numerals changed. *)
(* Modified by Theorem Labs, 2026-10-31: the cf layer's field-round-3 part-3b MP hunks (proofs/cgif/cgif_file_fuzzer/lib/MemnormAtop.v at a working branch 3cae605a900a, file blob 8bdbbebb5e, unchanged by part 3c) applied by hand: `Variable MP`, the four arms' `MP mem ->`, MP in the conclusion and HMP passed to each arm, because this unit's MemnormT.aalloc_prim_realizes_em takes MP. No numeral changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/MemnormAtop.v, with its module paths, module names and addresses changed; 36 of its 90 lines of code are new or changed and 28 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGtop.v (a working branch 95e6f1d72b6, file sha256 2db975f84ec7; written for cgif_file_fuzzer.asan-ubsan 1c29845fe605) onto libreac/fuzz_decode's asan image (pin 5973b76807d8, unstripped twin 4cb0a852e826); module paths changed, names TfibSyms -> GrantSyms; its 2 image addresses moved by code-verified function pairs (2 port_addr_check 0767e70e074a MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* The top of the frame-generic primary-size Allocate walk: the dispatch of YFij.v (hit / miss, k path n <= 48 /
   g path 49 <= n) ending in YGAlloc.aalloc_prim_realizes.  The cgif_file corollary is AGtopcgif.v.

   Ported from proofs/cgif/cgif_file_fuzzer/lib/YFij.v (prim_fp, malloc_hit, malloc_miss, malloc_prim; cgif_file's
   released malloc walk, same image) with the caller's frame made abstract: the entry is Allocate's first instruction
   0x324b0 (YGAlloc.alloc_pre), not the malloc wrapper, and the allocator relation ARX is opaque.

   [aalloc_prim_realizes_of_arms] takes the four arms and the uninited-cache fact as premises in the exact shape the
   dispatch applies them (each arm covers cf in {0, 1}).  This file imports no cgif instance (AllocGcgif, AGif2cgif,
   AGif0cgif) and no walk file, so another image takes it by path; the dispatch over the c5 interface
   ([aalloc_prim_realizes_if], AIface / AIfaceK with the hit arms AGik / AGil) is in AGtopcgif.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AB1q AF0l AF0m AFl0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YGAlloc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* YFij.v:37 prim_fp, generic in n. *)
Lemma prim_fp_g : forall n, 0 <= n <= 64512 -> from_primary n = true.
Proof.
intros n Nrange. unfold from_primary, needed_primary, rounded_size, round_up, rz_size, rz_log, kMaxSize. apply Z.leb_le.
pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as M.
destruct (Z.leb_spec n 48); [change (Z.shiftl 16 0) with 16; lia|].
destruct (Z.leb_spec n 96); [change (Z.shiftl 16 1) with 32; lia|].
destruct (Z.leb_spec n 448); [change (Z.shiftl 16 2) with 64; lia|].
destruct (Z.leb_spec n 3968); [change (Z.shiftl 16 3) with 128; lia|].
destruct (Z.leb_spec n 16128); [change (Z.shiftl 16 4) with 256; lia|].
destruct (Z.leb_spec n 32256); [change (Z.shiftl 16 5) with 512; lia|].
destruct (Z.leb_spec n 64512); [change (Z.shiftl 16 6) with 1024; lia|]. lia.
Qed.

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

(* The goal of one call at cgif_file's image: Allocate at 0x324b0, al = 8, atp = 1 (FROM_MALLOC). *)
Let GOAL (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (n : Z) (tr : list Z) : Prop :=
  amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x324b0 regs mem md)
    (alloc_leaf tfibsegs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr).
Let PRE (inst so bp : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (n : Z) (tr : list Z) : Prop :=
  alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr.

(* The uninited-cache refutation (YFij.v:75-77): a class whose cache is not inited has no cached chunk. *)
Hypothesis UNINIT : forall inst ly S W mem md c, ARX inst ly S W mem md -> 1 <= c <= 31 ->
  st_cache_inited S = false -> pc_chunks (cache S c) = [].

(* The four arms (YFij.v:57-58, 65-66: YFik.malloc_hitg, YFil.malloc_hitk, YFim.malloc_missg, YFin.malloc_missk). *)
Hypothesis ARM_HITG : forall inst so bp ly S W regs mem md n tr l off, cf = 0 \/ cf = 1 ->
  PRE inst so bp ly S W regs mem md n tr -> 49 <= n <= 64512 ->
  st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  GOAL inst ly S W regs mem md n tr.
Hypothesis ARM_HITK : forall inst so bp ly S W regs mem md n tr l off, cf = 0 \/ cf = 1 ->
  PRE inst so bp ly S W regs mem md n tr -> 0 <= n <= 48 ->
  st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  GOAL inst ly S W regs mem md n tr.
Hypothesis ARM_MISSG : forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  PRE inst so bp ly S W regs mem md n tr -> 49 <= n <= 64512 ->
  pc_chunks (cache S (chunk_class n)) = [] ->
  GOAL inst ly S W regs mem md n tr.
Hypothesis ARM_MISSK : forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  PRE inst so bp ly S W regs mem md n tr -> 0 <= n <= 48 ->
  pc_chunks (cache S (chunk_class n)) = [] ->
  GOAL inst ly S W regs mem md n tr.

(* YFij.v:68 malloc_prim, generic. *)
Theorem aalloc_prim_realizes_of_arms :
  aalloc_prim_realizes tfibsegs B U mt ARX AOX rpre nmax lmax lpost 0x324b0 oomb 8 1 cf.
Proof.
intros inst so bp ly S W regs mem md n tr HPRE Hn64.
pose proof (proj1 HPRE) as HAR.
assert (Hn0 : 0 <= n) by (clear - HPRE; unfold alloc_pre in HPRE; decompose [and] HPRE; lia).
assert (Nrange : 0 <= n <= 64512) by lia.
pose proof (primary_geometry n ltac:(lia) (prim_fp_g n Nrange)) as (Hcl & _).
destruct (pc_chunks (cache S (chunk_class n))) as [|x t] eqn:El.
- destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
  + exact (ARM_MISSG inst so bp ly S W regs mem md n tr HCF HPRE ltac:(lia) El).
  + exact (ARM_MISSK inst so bp ly S W regs mem md n tr HCF HPRE ltac:(lia) El).
- assert (LX : exists l off, x :: t = l ++ [off])
    by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
  destruct LX as (l & off & LX). rewrite LX in El.
  destruct (st_cache_inited S) eqn:CI.
  + destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
    * exact (ARM_HITG inst so bp ly S W regs mem md n tr l off HCF HPRE ltac:(lia) CI El).
    * exact (ARM_HITK inst so bp ly S W regs mem md n tr l off HCF HPRE ltac:(lia) CI El).
  + exfalso. rewrite (UNINIT inst ly S W mem md (chunk_class n) HAR ltac:(lia) CI) in El.
    destruct l; discriminate El.
Qed.
End b.
End a.

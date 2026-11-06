(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF40 YF4i YF4j YF4k YF4l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b. Context {imgk : img}.
Variable B : asyms.
Hypothesis TS : TfxSyms B.
Hypothesis U1 : tfx_unwind_spec.
Hypothesis D1 : tfx_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly (0x533a4 + D_2c4) regs0 ch.
Hypothesis PRE : acall_pre tfxsegs B ly S W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange : 0 <= n <= 64512.
Hypothesis Htr : In tr (as_universe B).
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Lemma prim_fp : from_primary n = true.
Proof.
clear - Nrange. unfold from_primary, needed_primary, rounded_size, round_up, rz_size, rz_log, kMaxSize. img_apply Z.leb_le.
pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(img_lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(img_lia)) as M.
destruct (Z.leb_spec n 48); [img_try (img_change (Z.shiftl 16 0) with 16; img_lia)|].
destruct (Z.leb_spec n 96); [img_try (img_change (Z.shiftl 16 1) with 32; img_lia)|].
destruct (Z.leb_spec n 448); [img_try (img_change (Z.shiftl 16 2) with 64; img_lia)|].
destruct (Z.leb_spec n 3968); [img_try (img_change (Z.shiftl 16 3) with 128; img_lia)|].
destruct (Z.leb_spec n 16128); [img_try (img_change (Z.shiftl 16 4) with 256; img_lia)|].
destruct (Z.leb_spec n 32256); [img_try (img_change (Z.shiftl 16 5) with 512; img_lia)|].
destruct (Z.leb_spec n 64512); [img_try (img_change (Z.shiftl 16 6) with 1024; img_lia)|]. img_lia.
Qed.
Section c.
Variables (l : list Z) (off : Z).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S (chunk_class n)) = l ++ [off].
Theorem malloc_hit :
amreal tfxsegs (malloc n tr S) W (cfg_at tfxsegs (0x53104 + D_2c4) regs0 mem0 md0) (malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n).
Proof.
destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
- img_exact (malloc_hitg B TS U1 D1 ly S W regs0 mem0 md0 n ch PRE Hn ltac:(img_lia) Htr Hlive l off Hinited Hcache).
- img_exact (malloc_hitk B TS U1 D1 ly S W regs0 mem0 md0 n ch PRE Hn ltac:(img_lia) Htr Hlive l off Hinited Hcache).
Qed.
End c.
Theorem malloc_miss : pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfxsegs (malloc n tr S) W (cfg_at tfxsegs (0x53104 + D_2c4) regs0 mem0 md0) (malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n).
Proof.
intros Hmiss. destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
- img_exact (malloc_missg B TS U1 D1 ly S W regs0 mem0 md0 n ch PRE Hn ltac:(img_lia) Htr Hlive Hmiss).
- img_exact (malloc_missk B TS U1 D1 ly S W regs0 mem0 md0 n ch PRE Hn ltac:(img_lia) Htr Hlive Hmiss).
Qed.
Theorem malloc_prim :
amreal tfxsegs (malloc n tr S) W (cfg_at tfxsegs (0x53104 + D_2c4) regs0 mem0 md0) (malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n).
Proof.
destruct (pc_chunks (cache S (chunk_class n))) as [|x t] eqn:El; [img_try (img_exact (malloc_miss El))|].
assert (LX : exists l off, x :: t = l ++ [off]) by (img_try (exists (List.removelast (x :: t)), (List.last (x :: t) 0); img_apply List.app_removelast_last; discriminate)).
destruct LX as (l & off & LX). rewrite LX in El.
pose proof (proj1 (proj1 PRE)) as HARm. pose proof (primary_geometry n ltac:(img_lia) prim_fp) as (Hcl & _).
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm) (chunk_class n) ltac:(img_lia))) as WC.
destruct (st_cache_inited S) eqn:CI; [img_try (img_exact (malloc_hit l off CI El))|].
exfalso. rewrite WC in El. cbn in El. destruct l; discriminate El.
Qed.
End b.
End a.

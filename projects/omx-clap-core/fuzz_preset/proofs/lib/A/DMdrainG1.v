(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainG1.v (commit 67deba317dfb, blob f153f740c3d2) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable ly : alayout.
Hypothesis LY : layout_ok ly.

Lemma LYB2 :
kHighMemBeg <= ly_prim ly /\ ly_prim ly <= ly_space ly /\
ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\
kHighMemBeg <= ly_stk_lo ly.
Proof.
pose proof (lo_high ly LY) as HI. unfold owned_extents in HI.
repeat match type of HI with Forall _ (_ :: _) => apply Forall_cons_iff in HI as [? HI] end.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold in_high in *. cbn [fst snd] in *.
repeat split; try lia.
Qed.

Hypothesis IMG : img_cover ly.
Hypothesis TAPP : in_app (ly_T ly) kThreadObjSize.
Hypothesis TIMG : zdisjoint (ly_T ly, kThreadObjSize) (ly_img ly).
Lemma TOBJ :
ly_T ly mod 4096 = 0 /\ zone3 (ly_T ly) kThreadObjSize /\
4096 <= ly_T ly /\ ly_T ly + kThreadObjSize <= ASAN_CEIL /\
(ly_T ly + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_T ly).
Proof.
assert (Z : zone3 (ly_T ly) kThreadObjSize) by (apply (zone3_intro ly); [exact IMG | unfold kThreadObjSize; lia | exact TAPP | exact TIMG]).
pose proof (lo_T_al ly LY) as AL. unfold page_aligned in AL.
pose proof (lo_stk_ceil ly LY) as SC.
destruct Z as (Z0 & Z1 & Z2).
split; [exact AL|]. split; [split; [exact Z0 | split; [exact Z1 | exact Z2]]|].
split; [exact Z0|]. split; [exact Z1|]. left. lia.
Qed.

Lemma SPACE : kHighMemBeg <= ly_space ly /\ ly_space ly + kSpaceSize <= ASAN_CEIL /\ ly_space ly mod 65536 = 0.
Proof.
pose proof LYB2 as (P1 & P2 & P3 & P4 & _).
pose proof (lo_space_al ly LY) as AL.
unfold kSpaceSize, kPrimResvSize, ASAN_CEIL, kHighMemBeg in *. splits; first [exact AL | lia].
Qed.

Lemma STKR : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. pose proof LYB2 as (_ & _ & _ & _ & _ & _ & _ & K8 & K9). split; [exact K9 | exact K8]. Qed.
End e.
End c.

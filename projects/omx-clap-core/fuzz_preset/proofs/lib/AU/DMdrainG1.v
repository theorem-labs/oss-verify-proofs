(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainG1.v (commit ce1a656b52b7, file sha256 38dce5d556dd) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainG1.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 842fe27b0f71) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainG1.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the LAYOUT facts Drain's entry shell asks of the process layout,
   from layout_ok alone - where the thread object, the primary space and the stack sit, and that they are apart.
   DMdrainE takes them as hypotheses (HT / HTz / HTstk / Hstklo / HSB); this file is where they come from, so the
   drain's composition needs nothing of the layout beyond DMiface.qview's qv_ly.  The derivation is DMdeq.LYB's
   (DMdeq.v:97-112), for the thread object and the space instead of the batch list.
   rule 24: no function proved (kind: layout arithmetic; the lane's reuse search is the internal file LOOKUP-B1-drain.txt,
   `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24
   check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey.
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

(* the released shape, as DMdeq.LYB reads it off layout_ok *)
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

(* the thread object: page aligned, in an application zone off the image window (YF0x.zone3), and below the
   stack (layout_ok's lo_stk_ceil puts the stack above ASAN_CEIL) *)
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

(* the primary space: in high memory, below the ceiling, 64 KiB aligned *)
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

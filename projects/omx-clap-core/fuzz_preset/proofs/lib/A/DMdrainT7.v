(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT7.v (commit 67deba317dfb, blob f358ce3d4644) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMdrainG1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma prim_apart : forall ly, layout_ok ly ->
(ly_prim ly + kPrimResvSize <= ly_T ly \/ ly_T ly + kThreadObjSize <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly).
Proof.
intros ly LY. pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP].
do 5 (apply Forall_cons_iff in DP as [_ DP]). apply Forall_cons_iff in DP as [PSTK _].
unfold zdisjoint in PT, PSTK. cbn [fst snd] in PT, PSTK. split; lia.
Qed.

Section g.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (X : astate).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation G := (qc_list (st_qglobal X)).
Hypothesis LY : layout_ok ly.
Hypothesis HSP : ly_stk_lo ly + DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis BADDR : forall b, In b (all_batches X) ->
  ly_prim ly <= SB + b_self b /\ SB + b_self b + kBatchBytes <= SB + kSpaceSize /\ (SB + b_self b) mod 8192 = 0 /\
  0 <= SB + b_self b < ASAN_CEIL.

Theorem batch_off_win : forall b, In b (all_batches X) -> forall a, SB + b_self b <= a < SB + b_self b + kBatchBytes ->
(forall lastb initr, rev G = lastb :: initr -> In lastb (all_batches X) -> b_self b <> b_self lastb \/ AFgj.GLv ly gq + 8 <= a) ->
~ AFgj.WIN ly regs0 gq a.
Proof.
intros b Hb a Ha HL. destruct (BADDR b Hb) as (A1 & A2 & A3 & A4).
pose proof (DMdrainG1.LYB2 ly LY) as (P1 & P2 & P3 & P4 & _).
pose proof (prim_apart ly LY) as [PT PS].
unfold AFgj.WIN, AFgj.WINF, AFgj.WINA. fold sp0.
ceil. unfold A_QUAR, A_ALLOCATOR, o_quar, ASAN_CEIL, kHighMemBeg, kSpaceSize, kPrimResvSize, kBatchBytes, kThreadObjSize, t_qc, DSTACK in *.
intros [H | [[H | [H | H]] | [Hne H]]].
- lia.
- lia.
- lia.
- lia.
- destruct (rev G) as [|lastb initr] eqn:ER.
  + apply Hne. rewrite <- (rev_involutive G), ER. reflexivity.
  + assert (Hin : In lastb (all_batches X)).
    { unfold all_batches. apply in_app_iff. right. rewrite <- (rev_involutive G), ER. cbn [rev]. apply in_app_iff. right. left. reflexivity. }
    assert (EG : AFgj.GLv ly gq = SB + b_self lastb) by (unfold AFgj.GLv; rewrite ER; reflexivity).
    destruct (BADDR lastb Hin) as (L1 & L2 & L3 & L4).
    destruct (HL lastb initr eq_refl Hin) as [NE | GE].
    * rewrite EG in H. lia.
    * lia.
Qed.
End g.
End f.

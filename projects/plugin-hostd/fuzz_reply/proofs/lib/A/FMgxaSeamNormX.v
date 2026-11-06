(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx form of FMgxaSeamNorm.v's one AR lemma (layout_of_preU, Section KP), over the
   engine's allocator relation ARx. FMgxaSeamNorm.v is not edited: every other lemma of it is AR-free and is used
   from it.

   The conversion is fuzz_preset's (PSnpSeamNorm.v at a working branch dad42dbecbc4, :1344-1352) of
   a Theorem Labs lane's FMgxaSeamNorm.v (3242941dc964, :1332-1338): FMupoison.ecall_preU (AR over `unpoison U mem`) ->
   FCiface.ecall_pre_x (ARx over mem, with the ghost head list Hp), and AR's am_layout -> the layout law. Reply's
   AR_laws_x (Reusable/YCbqG.v) has no layout field (preset's alx_layout_ok, field 18), so the law is the Section
   hypothesis LAY in preset's field text (ARx_layout_ok_law); FMgxaSeamARX.v proves it at reply's ARX from ARmcf's
   amc_layout.

   stk_bounds_x is preset's engine lemma of the same name (its YCbqG.v, derived there from alx_layout_ok by lo_top),
   here from LAY: the real stack lies in [kHighMemBeg, kHighMemEnd]. FMgxaSeamReadyX.v and the seam's assembly read it
   in place of a Theorem Labs lane's FMupoison.stk_kHighMemBeg (ARm's am_layout). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
Import ListNotations.
Local Open Scope Z_scope.

Section KPX. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAY : forall ly S Hp W mem md, ARx ly S Hp W mem md -> layout_ok ly.

(* the contract's ecall_pre_x carries layout_ok (Step 3's first premise) *)
Lemma layout_of_pre_x : forall ly S Hp (W : world tfibsegs) regs mem md,
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> layout_ok ly.
Proof. intros ly S Hp W regs mem md (HAR & _). exact (LAY ly S Hp W mem md HAR). Qed.

(* the real stack's bounds (layout_ok's lo_top) *)
Lemma stk_bounds_x : forall ly S Hp (W : world tfibsegs) mem md,
  ARx ly S Hp W mem md -> kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof.
intros ly S Hp W mem md HAR.
pose proof (lo_top _ (LAY ly S Hp W mem md HAR)) as (_ & _ & _ & Hhi & _ & _ & Hbeg).
exact (conj Hbeg Hhi).
Qed.

End KPX.

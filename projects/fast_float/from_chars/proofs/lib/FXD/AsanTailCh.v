(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FT3000 : nat := 3000.
Section TailCh.
Context {N : Type}.
Notation MC := (@mchain N).
Definition PT_RETRY : plan := PRun FT3000 [0xca418; 0xca39c] [].
Definition PT_RETRY2 : plan := PRun FT3000 [0xca418; 0xca39c; 0xca458] [].
(* [comment removed for export] *)
Definition T_F0W : wsrc := WBuf (lconst 0x638690) BPre 0.
Definition T_F1W : wsrc := WLit 0x14c9f.
(* [comment removed for export] *)
Definition T_WBL1 : MC := MWritevL 1 T_F0W T_F1W (MAlt MVoid (MSegK 20 PT_RETRY2 (KCons 0xca39c 0 (MPop MEnd) KNil))).
Definition T_KWL (k : MC) : MC :=
  MJoin (MWritevL 1 T_F0W T_F1W (MAlt MVoid (MSegK 20 PT_RETRY2 (KCons 0xca418 66 T_WBL1 (KCons 0xca39c 0 (MPop MEnd) KNil))))) 0xca39c k.
(* [comment removed for export] *)
Definition T_WBF : MC := MWritev2 (lconst 0x638690) (MSegK 20 PT_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))).
Definition T_WBF1 : MC := MWritev2 (lconst 0x638690) (MAlt MVoid (MSegK 20 PT_RETRY (KCons 0xca39c 0 (MPop MEnd) KNil))).
Definition T_KWF (n : nat) (k : MC) : MC :=
  match n with
  | Datatypes.S (Datatypes.S O) => MJoin (MWritev2 (lconst 0x638690) (MAlt MVoid (MSegK 20 PT_RETRY (KCons 0xca418 66 T_WBF1 (KCons 0xca39c 0 (MPop MEnd) KNil))))) 0xca39c k
  | _ => MJoin (MWritev2 (lconst 0x638690) (MSegK 20 PT_RETRY (KCons 0xca418 66 (MLoopW 22 T_WBF (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c k
  end.
End TailCh.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxPlan FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcSteps AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HxSurg HarnFam HarnLoop HarnSite HarnFk AcFam3 HarnChain HarnJoin HarnJoinN HarnJoinM HarnDev HarnLong HarnLongL HarnCR HarnCR2 HarnSP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sh_ab (r : Z) (S : sst) : option (nat * nat) :=
  let sh := oshadow (tb_heap r S) in
  match find_base (s_rgs S) sh 0, find_base (s_rgs S) (laddc sh 3) 0 with
  | Some iA, Some iB =>
      match nth_error (s_rgs S) iA, nth_error (s_rgs S) iB with
      | Some A, Some B => if (lin_eqb (rg_size A) (lconst 3) && lin_eqb (rg_size B) (lconst 1))%bool then Some (iA, iB) else None
      | _, _ => None
      end
  | _, _ => None
  end.
Definition sh_drop (r : Z) (S : sst) : option (list rstep) := match sh_ab r S with Some (iA, iB) => Some [RDrop iA; RDrop iB] | None => None end.
Definition sh_mrg (r : Z) (S : sst) : option (nat * nat) :=
  match sh_ab r S with Some (iA, iB) => if Nat.eqb iB (Datatypes.S iA) then Some (iA, 2%nat) else None | None => None end.
Definition SHMERGE (r : Z) (k : MCH) : MCH := TRY (HSURG (SSteps (sh_drop r))) (TRY (HSURG (SMerge (sh_mrg r))) k).
Definition STASH_HK (k : nat) (r : Z) (c : MCH) : MCH := SHMERGE r (STASH_H k r c).


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the CONFIG_RSEQ flag of the start-up layer). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanTbl AsanEntry AsanPlan AsanStart.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* the six start-up certificates: three [OFS] bands, each at both CONFIG_RSEQ values; every one is
   computed at a closed flag *)
Definition RESC (r : bool) : option (list (sst * smodel)) := startup_res r (S0c r 176 4080 5) TBLd IMGd.
Definition RESA (r : bool) : option (list (sst * smodel)) := startup_res r (S0c r 4096 4176 67) TBLd IMGd.
Definition RESB (r : bool) : option (list (sst * smodel)) := startup_res r (S0c r 4192 4256 68) TBLd IMGd.
Definition FINC : list (sst * smodel) := Eval vm_compute in list_of (RESC false) ++ list_of (RESC true).
Definition FINA : list (sst * smodel) := Eval vm_compute in list_of (RESA false) ++ list_of (RESA true).
Definition FINB : list (sst * smodel) := Eval vm_compute in list_of (RESB false) ++ list_of (RESB true).
(* [comment removed for export] *)
Lemma startup_ok_res : (some_nonempty (RESC false) && some_nonempty (RESC true) && some_nonempty (RESA false) &&
  some_nonempty (RESA true) && some_nonempty (RESB false) && some_nonempty (RESB true))%bool = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
(* [comment removed for export] *)
Lemma finals_res_eq : (list_of (RESC false) ++ list_of (RESC true)) ++ (list_of (RESA false) ++ list_of (RESA true)) ++
  (list_of (RESB false) ++ list_of (RESB true)) = FINC ++ FINA ++ FINB.
Proof. vm_cast_no_check (eq_refl (FINC ++ FINA ++ FINB)). Qed.
(* [comment removed for export] *)

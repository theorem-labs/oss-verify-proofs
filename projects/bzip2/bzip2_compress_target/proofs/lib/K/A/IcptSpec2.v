(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint memcmp_res (b1 b2 : list byte) : Z :=
  match b1, b2 with
  | x :: r1, y :: r2 => if Z.eqb (bv_unsigned x) (bv_unsigned y) then memcmp_res r1 r2 else bv_unsigned x - bv_unsigned y
  | _, _ => 0
  end.

Lemma memcmp_res_refl : forall b, memcmp_res b b = 0.
Proof. induction b as [|x r IH]; cbn [memcmp_res]; [reflexivity|]. rewrite Z.eqb_refl. exact IH. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

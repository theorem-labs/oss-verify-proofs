(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Record rrow : Type := RR { rr_b : AX2.expr; rr_n : AX2.expr; rr_k : Z; rr_par : option AX2.expr }.

Definition resp_a (RT : list rrow) (a : AX2.saddr) : AX2.saddr :=
  match List.find (fun r => AX2.expr_eqb (AX2.a_base a) (rr_b r)) RT with
  | Some r => AX2.SA (rr_n r) (AX2.a_off a - rr_k r)
  | None => a
  end.

Definition resp_k (RT : list rrow) (K : AX2.kentry) : AX2.kentry :=
  match K with
  | AX2.KWord a w v => AX2.KWord (resp_a RT a) w v
  | AX2.KZero a n => AX2.KZero (resp_a RT a) n
  | AX2.KBlob a n k => AX2.KBlob (resp_a RT a) n k
  | AX2.KWr a n => AX2.KWr (resp_a RT a) n
  | AX2.KFill a n c => AX2.KFill (resp_a RT a) n c
  | AX2.KUnk a n => AX2.KUnk (resp_a RT a) n
  | _ => K
  end.

Definition resp_cs (RT : list rrow) (CS : CAP.acs) : CAP.acs := CAP.set_kn CS (map (resp_k RT) (CAP.kn CS)).


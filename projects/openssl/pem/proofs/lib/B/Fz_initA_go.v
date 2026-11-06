(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import RT_gshacc Fz_gochk Fz_initA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem initA_go : Forall (fun p => A_GOBJ (fst p) (snd p)) INITA_GOBJS
  /\ Forall (fun p => exists b sz, A_GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz) INITA_GCOVER.
Proof. apply go_both_sound. vm_compute. reflexivity. Qed.

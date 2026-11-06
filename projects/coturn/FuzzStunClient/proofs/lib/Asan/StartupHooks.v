(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanNodesDepot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
Definition XNdA (id : nat) (args : list expr) (cs : acs) : option acs :=
  if (113 <=? id)%nat then DPN.xn Asan.M.loaded_segments NX0 0x1954d8 0x1854c8 0x608000 id args cs else None.
Definition XNdB (id : nat) (args : list expr) (cs : acs) : option acs :=
  if (113 <=? id)%nat then DPN.xn AsanUbsan.M.loaded_segments NX0 0x193a98 0x183a88 0x607000 id args cs else None.

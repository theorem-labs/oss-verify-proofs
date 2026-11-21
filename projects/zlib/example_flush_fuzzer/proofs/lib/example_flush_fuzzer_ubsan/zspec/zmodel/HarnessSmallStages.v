(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool String.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface
  DeflateState Deflate InflateState Inflate HarnessKit HarnessSmall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.


Definition ocanon (fails : list Z) : horacle :=
  mkHO (fun k => existsb (Z.eqb k) fails) (fun _ _ => 0) (fun _ => zstrm0).

Definition crun {A} (fails : list Z) (k : Z) (m : SM hst A) : option (A * hst) :=
  hrun m (mkHS (ocanon fails) k [] false).

Definition cb (n : Z) : Z := compressBound_m n.


Inductive cpat : Type := CZ | CD.

Inductive ia_out : Type := IX_W | IX_E (rc : Z) | IX_N.
Inductive ib_out : Type := BX_F | BX_E (rc : Z).
Inductive upat : Type := UN (c : cpat) | UF (c : cpat).


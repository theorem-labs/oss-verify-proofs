(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition FLAGS_NOREPLACE : Z := 0x104022.

Section WithA.
Variable segs : list Segment.
Variable A : atable.
Variable LIMIT : Z.

(* [comment removed for export] *)
Definition node_mmap_noreplace (cs : acs) : option (acs * acs) :=
  if negb (is_ecall_at segs cs) then None else
  match mmap_gate cs with
  | Some (prot, flags, false) =>
      let g := if Z.eqb flags FLAGS_NOREPLACE then
                 match prot with
                 | 3 => mmap_fixed_free A LIMIT cs KRWLAZY false false    (* [comment removed for export] *)
                 | 0 => mmap_fixed_free A LIMIT cs KNONELAZY false false  (* [comment removed for export] *)
                 | _ => None
                 end
               else None in
      match g with Some csG => Some (refuse cs, csG) | None => None end
  | _ => None
  end.

(* [comment removed for export] *)
Definition XB_nr (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  match id, args with
  | O, [] => node_mmap_noreplace cs
  | _, _ => None
  end.
End WithA.

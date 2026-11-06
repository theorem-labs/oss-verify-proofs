(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/StrStr.v, unchanged. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/StrStr.v for reac-pw/fuzz_segconf.asan-ubsan (image B), with its module paths changed. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Fixpoint prefix_eqb (nd h : list Z) : bool :=
  match nd, h with
  | [], _ => true
  | _ :: _, [] => false
  | a :: nd', b :: h' => (a =? b) && prefix_eqb nd' h'
  end.

Fixpoint find_first (h nd : list Z) : option nat :=
  if prefix_eqb nd h then Some 0%nat
  else match h with
       | [] => None
       | _ :: h' => option_map S (find_first h' nd)
       end.

Definition strstr_val (A : Z) (hb nb : list byte) : Z :=
  match find_first (map bv_unsigned hb) (map bv_unsigned nb) with
  | Some i => A + Z.of_nat i
  | None => 0
  end.

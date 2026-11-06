(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac sf_fold1 v c :=
  let b := eval vm_compute in c in
  let rec go v :=
    lazymatch v with
    | context C [b] => let v' := context C [c] in go v'
    | _ => v
    end in
  go v.
Ltac sf_fold v cands :=
  lazymatch cands with
  | (?c, ?rest) => let v' := sf_fold1 v c in sf_fold v' rest
  | tt => v
  end.
(* [comment removed for export] *)
Ltac sf_def t cands := let v := eval vm_compute in t in let v' := sf_fold v cands in exact v'.

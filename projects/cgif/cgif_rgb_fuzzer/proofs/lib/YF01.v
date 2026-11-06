(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00.
Unset Lia Cache. Unset Nia Cache.
Ltac img_eq_vmcast :=
try img_inst; img_case; lazymatch goal with |- @eq ?T _ ?b => vm_cast_no_check (@eq_refl T b) end.
Ltac img_norm_st HS R :=
lazymatch type of R with
| ?f ?s2 = _ =>
lazymatch type of HS with
| ?P ?s1 ?m =>
first [ constr_eq s1 s2
| (let E_ := fresh "IMGE" in
assert (E_ : s1 = s2) by img_eq_vmcast;
rewrite E_ in HS; clear E_)
| idtac ]
| _ => idtac
end
| _ => idtac
end.
Ltac img_eqrefl_m := first [ exact eq_refl | (try img_inst; img_case; reflexivity) | (try img_inst; img_case; vm_compute; reflexivity) ].

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Export QRBl.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbIns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac ub_closed c := assert_fails (idtac; match c with context [?x] => is_var x end).

Ltac ub_if_lit_c :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => ub_closed c; ub_if_lit
end.

Ltac ub_pre_norm :=
repeat first
[ match goal with |- context [bv_unsigned (Z_to_bv 64 (Z.of_nat ?n))] => rewrite (unsigned_lit (Z.of_nat n)) by lia end
| match goal with |- context [Z.shiftl ?e ?k] => rewrite (Z.shiftl_mul_pow2 e k) by lia end ].

Ltac ub_cmp_auto_c :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
first [ replace c with false; [cbv iota | symmetry; ub_pre_norm; ub_cmp_norm; lazymatch goal with |- ?d = _ => ub_closed d end; vm_compute; reflexivity]
| replace c with true; [cbv iota | symmetry; ub_pre_norm; ub_cmp_norm; lazymatch goal with |- ?d = _ => ub_closed d end; vm_compute; reflexivity] ]
end.

Ltac ub_resolve :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
first [ ub_if_lit_c
| match goal with H : ?p mod 16 = 0 |- context [Z.land (bv_unsigned (Z_to_bv 64 ?p)) _] => ubsan_align H end
| match goal with H : ?p mod 16 = 0 |- context [Z.land ?p _] => ubsan_align H end
| ub_align_auto
| if_falsex
| ub_cmp_auto_c
| idtac ]
| |- _ => idtac
end.

Ltac ub_skip :=
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
tryif ub_closed pc then
(let b := eval vm_compute in (TopUbIns.ub_ins pc) in
lazymatch b with
| true => step; ub_resolve; ub_skip
| _ => idtac
end)
else idtac
| |- _ => idtac
end.
Ltac bstep := ub_skip; step.
Ltac bstepz := ub_skip; stepz.

Ltac ub_skip_g E stp :=
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 (?b + ?k)) _ _ _ _) =>
tryif ub_closed k then
(let c := eval vm_compute in (TopUbIns.ub_ins (E + k)) in
lazymatch c with
| true => stp; ub_resolve; ub_skip_g E stp
| _ => idtac
end)
else idtac
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?b) _ _ _ _) =>
tryif is_var b then
(let c := eval vm_compute in (TopUbIns.ub_ins E) in
lazymatch c with
| true => stp; ub_resolve; ub_skip_g E stp
| _ => idtac
end)
else idtac
| |- _ => idtac
end.
Ltac bstep_g E stp := ub_skip_g E stp; stp.

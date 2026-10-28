From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QHnV Qsw7 QRUw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QHnV Qsw7 QRUw.
Import TopUbTac.
Import ListNotations.
Open Scope Z_scope.

Ltac shl_norm := repeat first
[ match goal with |- context [bv_unsigned (Z_to_bv 64 (Z.of_nat ?n))] => rewrite (unsigned_lit (Z.of_nat n)) by lia end
| match goal with |- context [Z.shiftl ?x ?k] => rewrite (Z.shiftl_mul_pow2 x k) by lia end
| match goal with |- context [?x * 2 ^ ?k] => let v := eval vm_compute in (2 ^ k) in change (x * 2 ^ k) with (x * v) end
| match goal with |- context [Z.of_nat ?n * ?k + ?x] => rewrite (Z.add_comm (Z.of_nat n * k) x) end ].

Ltac ub_more := lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shl_norm; ub_cmp_auto | idtac ]
| |- _ => idtac
end.

Ltac tk1_walk lo hi n E := lazymatch n with
| O => idtac
| S ?n' =>
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let b := eval vm_compute in (andb (Z.leb lo pc) (Z.ltb pc hi)) in
lazymatch b with
| true => try (shl_norm; rewrite ?E); first [stepz | step]; tk1_walk lo hi n' E
| false => idtac
end
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
ub_resolve; ub_more;
lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail 1 "tk1_walk: branch left open"
| |- _ => tk1_walk lo hi n' E
end
| |- _ => idtac
end
end.

Ltac tk1_pc := lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ub_closed pc then (let v := eval vm_compute in pc in idtac "PROBE pc" v) else idtac "PROBE pc open"
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac "PROBE branch"
| |- _ => idtac "PROBE other"
end.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QHnV Qsw7 QRUw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac.

Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QHnV Qsw7 QRUw.
Import TopUbTac Tk1Tac.
Import ListNotations.
Open Scope Z_scope.

Ltac align_true :=
match goal with
| H : ?p mod 16 = 0 |- context [Z.land (bv_unsigned (Z_to_bv 64 ?p)) _] =>
rewrite ?(unsigned_lit p) by lia; first [rewrite (land7_of_mod16 p H) | rewrite (land3_of_mod16 p H)]; first [ub_if_lit | if_truex]
| H : ?p mod 16 = 0 |- context [Z.land ?p _] =>
first [rewrite (land7_of_mod16 p H) | rewrite (land3_of_mod16 p H)]; first [ub_if_lit | if_truex]
end.

Ltac tk3_walk pc E := repeat (lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => try E; first [ub_if_lit_c | if_falsex | if_truex | align_true | ub_cmp_auto_c]
| |- _ => try shl_norm; try E; first [bstepz | stepz]
end).

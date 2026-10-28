From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QHnV Qsw7 QRUw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QHnV Qsw7 QRUw.
Import TopUbTac Tk1Tac.
Import ListNotations.
Open Scope Z_scope.

(* Alignment check branch on an address p with p mod 16 = 0 in context, either polarity (beqz or bnez on
   andi p 7 / andi p 3): the land closes to 0 and the branch condition to a literal. *)
Ltac tk1_align :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
match goal with
| H : ?p mod 16 = 0 |- context [Z.land (bv_unsigned (Z_to_bv 64 ?p)) _] =>
rewrite (unsigned_lit p) by lia; first [rewrite (land7_of_mod16 p H) | rewrite (land3_of_mod16 p H)]; ub_if_lit
| H : ?p mod 16 = 0 |- context [Z.land ?p _] =>
first [rewrite (land7_of_mod16 p H) | rewrite (land3_of_mod16 p H)]; ub_if_lit
end
end.

(* tk1_walk that also closes alignment check branches of either polarity (tk1_align before ub_resolve). *)
Ltac tk1_walk_a lo hi n E := lazymatch n with
| O => idtac
| S ?n' =>
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let b := eval vm_compute in (andb (Z.leb lo pc) (Z.ltb pc hi)) in
lazymatch b with
| true => try (shl_norm; rewrite ?E); first [stepz | step]; tk1_walk_a lo hi n' E
| false => idtac
end
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
first [ tk1_align | ub_resolve; ub_more ];
lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail 1 "tk1_walk_a: branch left open"
| |- _ => tk1_walk_a lo hi n' E
end
| |- _ => idtac
end
end.

(* One check branch at the goal head: tk1_align, else ub_resolve + ub_more; fails if the branch stays open. *)
Ltac tk1_chk :=
first [ tk1_align | ub_resolve; ub_more ];
lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail 1 "tk1_chk: check branch left open"
| |- _ => idtac
end.

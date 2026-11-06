(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Zify.
From Stdlib Require Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaTuning.
From Ltac2 Require Ltac2.
Module HeapLia.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaTuning.
Import Ltac2.Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Ltac2 rec hp_plain2 (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b c => if Constr.equal c 'False then hp_plain2 (Constr.Binder.type b) else false   (* [comment removed for export] *)
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@or then (if hp_plain2 (Array.get args 0) then hp_plain2 (Array.get args 1) else false)
          else if Constr.equal h '@and then (if hp_plain2 (Array.get args 0) then hp_plain2 (Array.get args 1) else false)
          else zt_plain_arith t
      | Constr.Unsafe.Constant _ _ => if Constr.equal h '@not then hp_plain2 (Array.get args 0) else zt_plain_arith t
      | _ => zt_plain_arith t
      end
  | _ => zt_plain_arith t
  end.

(* [comment removed for export] *)
Ltac2 hp_prune2 () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if hp_plain2 ty then None
                          else if Bool.and (zt_is_local id) (zt_is_prop ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac hp_prune2 := ltac2:(Control.enter hp_prune2).

(* [comment removed for export] *)
Ltac hp_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac hp_closed_cmp A :=
  lazymatch A with
  | @eq Z ?x ?y => hp_zlit x; hp_zlit y
  | not (@eq Z ?x ?y) => hp_zlit x; hp_zlit y
  | Z.lt ?x ?y => hp_zlit x; hp_zlit y
  | Z.le ?x ?y => hp_zlit x; hp_zlit y
  | Z.gt ?x ?y => hp_zlit x; hp_zlit y
  | Z.ge ?x ?y => hp_zlit x; hp_zlit y
  end.
Ltac hp_spec_closed :=
  repeat match goal with
  | H : ?A -> _ |- _ => hp_closed_cmp A;
      first [ specialize (H ltac:(vm_compute; first [ reflexivity | discriminate | intros ?; discriminate ])) | clear H ]
  end.

Ltac heap_lia :=
  first [ hp_spec_closed; LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | hp_spec_closed; hp_prune2; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac heap_lia_pruned :=
  first [ hp_spec_closed; LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | hp_spec_closed; hp_prune2; Zify.zify; xlia zchecker ].
End HeapLia.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaTuning.
Import HeapLia.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Ltac2 rec hp_plain3 (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b c => if hp_plain3 (Constr.Binder.type b) then hp_plain3 c else false
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@or then (if hp_plain3 (Array.get args 0) then hp_plain3 (Array.get args 1) else false)
          else if Constr.equal h '@and then (if hp_plain3 (Array.get args 0) then hp_plain3 (Array.get args 1) else false)
          else zt_plain_arith t
      | Constr.Unsafe.Constant _ _ => if Constr.equal h '@not then hp_plain3 (Array.get args 0) else zt_plain_arith t
      | _ => zt_plain_arith t
      end
  | _ => zt_plain_arith t
  end.
Ltac2 hp_prune3 () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if hp_plain3 ty then None
                          else if Bool.and (zt_is_local id) (zt_is_prop ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac hp_prune3 := ltac2:(Control.enter hp_prune3).
Ltac heap_lia_imp := hp_spec_closed; hp_prune3; Zify.zify; xlia zchecker.

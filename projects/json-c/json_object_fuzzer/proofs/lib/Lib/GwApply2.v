(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool.
From stdpp Require Import base decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen GwApply.
From Ltac2 Require Import Ltac2 Constr Control Message.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Set Default Proof Mode "Classic".

Ltac gw_side_extra := fail.

Ltac2 gw2_is_fact_name (id : ident) : bool :=
let s := Ident.to_string id in
List.exist (gw_has_prefix s) ["D_"; "E_"; "ANCH_"; "LINK_"; "RNG_"; "AL_"; "LAY_"; "JTL_"; "ROM_"].

Ltac2 gw2_is_code_fact_name (id : ident) : bool := gw_has_prefix (Ident.to_string id) "CODE_".

Ltac2 gw2_is_extra_fact_name (id : ident) : bool :=
let s := Ident.to_string id in
List.exist (gw_has_prefix s) ["CS_"; "VOL_"; "FACT_"].

Ltac2 rec gw2_head (c : constr) : constr :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f _ => gw2_head f
| Constr.Unsafe.Cast c _ _ => gw2_head c
| _ => c
end.

Ltac2 gw2_header_names (t : constr) : ident list :=
let m := gw_mod_of (gw2_head t) in
let extra := [@segs; @base] in
match gw_mod_lookup m @gw_all with
| Some w => List.append (gw_binder_names (Constr.type w)) extra
| None => Control.throw (Tactic_failure (Some (Message.of_string "gw_by_name2: the generic module has no witness lemma gw_all")))
end.

Ltac2 gw2_fits (ty : constr) (want : constr) : bool :=
match Control.case (fun () => Std.unify ty want) with
| Val _ => true
| Err _ => false
end.
Ltac2 rec gw2_ctx_args_until (want : constr) (c : constr) (ty : constr) : constr :=
if gw2_fits ty want then c else
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in gw2_ctx_args_until want constr:($c $h) (Constr.Unsafe.substnl [h] 0 rest)
| Err _ => c
end
| None => c
end
| _ => c
end.
Ltac2 rec gw2_ctx_args (c : constr) (ty : constr) : constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in gw2_ctx_args constr:($c $h) (Constr.Unsafe.substnl [h] 0 rest)
| Err _ => c
end
| None => c
end
| _ => c
end.

Ltac2 gw2_value (c : constr) : constr :=
if gw_is_prop c then c else
match Constr.Unsafe.kind (gw2_head c) with
| Constr.Unsafe.Constant k _ =>
let u := Std.eval_unfold [(Std.ConstRef k, Std.AllOccurrences)] c in
Std.eval_cbv { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
Std.rZeta := false; Std.rDelta := false; Std.rConst := [] } u
| _ => c
end.

Ltac2 gw2_goal_binder_is (id : ident) : bool :=
match Constr.Unsafe.kind (Control.goal ()) with
| Constr.Unsafe.Prod b _ => match Constr.Binder.name b with Some n => Ident.equal n id | None => false end
| _ => false
end.

Ltac2 rec gw2_prefix (m : ident list) (names : ident list) (t : constr) (ty : constr) : constr * constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
if List.exist (Ident.equal id) names then
let arg :=
match gw_mod_lookup m id with
| Some c => gw2_value (gw2_ctx_args_until (Constr.Binder.type b) c (Constr.type c))
| None =>
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in h
| Err _ =>
if gw2_goal_binder_is id then (Std.intros false [Std.IntroNaming (Std.IntroIdentifier id)]; Control.hyp id)
else if gw2_is_fact_name id then
let bty := Constr.Binder.type b in '(ltac:(gw_side) : $bty)
else if gw2_is_code_fact_name id then
let bty := Constr.Binder.type b in '(ltac:(code_at_vm) : $bty)
else if gw2_is_extra_fact_name id then
let bty := Constr.Binder.type b in '(ltac:(gw_side_extra) : $bty)
else Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "gw_by_name2: no GwI constant, context hypothesis or computable fact for header name ") (Message.of_ident id))))
end
end in
gw2_prefix m names constr:($t $arg) (Constr.Unsafe.substnl [arg] 0 rest)
else (t, ty)
| None => (t, ty)
end
| _ => (t, ty)
end.

Ltac2 gw_by_name2_0 (rep : constr) (t : constr) : unit :=
let m := gw_mod_of rep in
let names := gw2_header_names t in
let (t', ty') := gw2_prefix m names t (Constr.type t) in
gw_go t' ty'.
Ltac gw_by_name2 rep t :=
let f := ltac2:(rep t |- gw_by_name2_0 (Option.get (Ltac1.to_constr rep)) (Option.get (Ltac1.to_constr t))) in f rep t.

Ltac2 rec gw2_ctx_prefix (names : ident list) (t : constr) (ty : constr) : constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
if List.exist (Ident.equal id) names then
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in gw2_ctx_prefix names constr:($t $h) (Constr.Unsafe.substnl [h] 0 rest)
| Err _ => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "gw_ctx2: the context lacks the sibling's header name ") (Message.of_ident id))))
end
else t
| None => t
end
| _ => t
end.
Ltac2 gw_ctx2_0 (t : constr) : unit :=
let names := gw2_header_names t in
let r := gw2_ctx_prefix names t (Constr.type t) in gw_try_exact r.
Ltac gw_ctx2 t := let f := ltac2:(t |- gw_ctx2_0 (Option.get (Ltac1.to_constr t))) in f t.

Ltac2 gw_inst_term0 (rep : constr) (t : constr) : unit :=
let m := gw_mod_of rep in
let names := gw2_header_names t in
let (t', _) := gw2_prefix m names t (Constr.type t) in
gw_try_exact t'.
Ltac gw_inst_term rep t :=
let f := ltac2:(rep t |- gw_inst_term0 (Option.get (Ltac1.to_constr rep)) (Option.get (Ltac1.to_constr t))) in f rep t.

Ltac2 rec gw2_leading_names (names : ident list) (ty : constr) : ident list :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id => if List.exist (Ident.equal id) names then id :: gw2_leading_names names rest else []
| None => []
end
| _ => []
end.
Ltac2 gw_probe0 (label : string) (t : constr) : unit :=
let names := gw2_header_names t in
let l := gw2_leading_names names (Constr.type t) in
Message.print (List.fold_left (fun acc id => Message.concat acc (Message.concat (Message.of_string " ") (Message.of_ident id)))
(Message.of_string (String.app "DEFARGS " (String.app label " BYNAME:"))) l).
Ltac2 Notation "gw_probe" label(tactic(0)) t(constr) := gw_probe0 label t.

Ltac2 rec gw2_callee_strip (names : ident list) (cb : constr) (ty : constr) : constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
if List.exist (Ident.equal id) names then
let bty := Constr.Binder.type b in
let isprop := Constr.equal (Constr.type bty) 'Prop in
let mine := match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in Some h
| Err _ => None
end in
let arg :=
if isprop then
match mine with
| Some h => if Constr.equal (Constr.type h) bty then Some h else None
| None => None
end
else if Ident.equal id @base then Some cb
else match mine with
| Some h => Some h
| None => Some '(ltac:(gw_dummy) : $bty)
end in
match arg with
| Some a => gw2_callee_strip names cb (Constr.Unsafe.substnl [a] 0 rest)
| None =>
if Constr.Unsafe.noccur_between 1 1 rest then gw2_callee_strip names cb (Constr.Unsafe.substnl ['I] 0 rest)
else Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "gw_callee_ty2: the statement depends on a header hypothesis the caller does not share: ") (Message.of_ident id))))
end
else ty
| None => ty
end
| _ => ty
end.
Ltac2 gw_callee_ty2_0 (hdr : constr) (t : constr) (cb : constr) : unit :=
let names := List.append (gw_binder_names (Constr.type hdr)) [@segs; @base] in
let r := gw2_callee_strip names cb (Constr.type t) in
gw_try_exact r.
Ltac gw_callee_ty2 hdr t cb :=
let f := ltac2:(hdr t cb |- gw_callee_ty2_0 (Option.get (Ltac1.to_constr hdr)) (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr cb))) in
f hdr t cb.

Ltac2 rec gw2_callee_app (names : ident list) (cb : constr) (t : constr) (ty : constr) : constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
if List.exist (Ident.equal id) names then
let bty := Constr.Binder.type b in
let isprop := Constr.equal (Constr.type bty) 'Prop in
let mine := match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in Some h
| Err _ => None
end in
let arg :=
if isprop then
match mine with
| Some h => if Constr.equal (Constr.type h) bty then h
else Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "gw_callee_stmt: header hypothesis with another statement in the caller: ") (Message.of_ident id))))
| None => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "gw_callee_stmt: the statement depends on a header hypothesis the caller lacks: ") (Message.of_ident id))))
end
else if Ident.equal id @base then cb
else match mine with
| Some h => h
| None => '(ltac:(gw_dummy) : $bty)
end in
gw2_callee_app names cb constr:($t $arg) (Constr.Unsafe.substnl [arg] 0 rest)
else t
| None => t
end
| _ => t
end.
Ltac2 gw_callee_stmt0 (hdr : constr) (t : constr) (cb : constr) : unit :=
let names := List.append (gw_binder_names (Constr.type hdr)) [@segs; @base] in
let r := gw2_callee_app names cb t (Constr.type t) in
gw_try_exact r.
Ltac gw_callee_stmt hdr t cb :=
let f := ltac2:(hdr t cb |- gw_callee_stmt0 (Option.get (Ltac1.to_constr hdr)) (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr cb))) in
f hdr t cb.

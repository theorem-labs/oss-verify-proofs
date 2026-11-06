(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition gw_rom_RSIZE_CLASSES : list (stdpp.bitvector.definitions.bv 8) :=
[stdpp.bitvector.definitions.Z_to_bv 8 1; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 2; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 3; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 4; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 5; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 6; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 7; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 8; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 9; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 10; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 12; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 15; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 18; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 20; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 25; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 31; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 36; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 42; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 50; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 63; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 72; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 84; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 102; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 127; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 146; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 170; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 204; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 255; stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 36; stdpp.bitvector.definitions.Z_to_bv 8 1; stdpp.bitvector.definitions.Z_to_bv 8 84; stdpp.bitvector.definitions.Z_to_bv 8 1; stdpp.bitvector.definitions.Z_to_bv 8 153; stdpp.bitvector.definitions.Z_to_bv 8 1; stdpp.bitvector.definitions.Z_to_bv 8 255; stdpp.bitvector.definitions.Z_to_bv 8 1; stdpp.bitvector.definitions.Z_to_bv 8 72; stdpp.bitvector.definitions.Z_to_bv 8 2; stdpp.bitvector.definitions.Z_to_bv 8 170; stdpp.bitvector.definitions.Z_to_bv 8 2; stdpp.bitvector.definitions.Z_to_bv 8 50; stdpp.bitvector.definitions.Z_to_bv 8 3; stdpp.bitvector.definitions.Z_to_bv 8 255; stdpp.bitvector.definitions.Z_to_bv 8 3; stdpp.bitvector.definitions.Z_to_bv 8 145; stdpp.bitvector.definitions.Z_to_bv 8 4; stdpp.bitvector.definitions.Z_to_bv 8 84; stdpp.bitvector.definitions.Z_to_bv 8 5; stdpp.bitvector.definitions.Z_to_bv 8 101; stdpp.bitvector.definitions.Z_to_bv 8 6; stdpp.bitvector.definitions.Z_to_bv 8 255; stdpp.bitvector.definitions.Z_to_bv 8 7; stdpp.bitvector.definitions.Z_to_bv 8 36; stdpp.bitvector.definitions.Z_to_bv 8 9; stdpp.bitvector.definitions.Z_to_bv 8 170; stdpp.bitvector.definitions.Z_to_bv 8 10; stdpp.bitvector.definitions.Z_to_bv 8 204; stdpp.bitvector.definitions.Z_to_bv 8 12; stdpp.bitvector.definitions.Z_to_bv 8 255; stdpp.bitvector.definitions.Z_to_bv 8 15; stdpp.bitvector.definitions.Z_to_bv 8 72; stdpp.bitvector.definitions.Z_to_bv 8 18; stdpp.bitvector.definitions.Z_to_bv 8 84; stdpp.bitvector.definitions.Z_to_bv 8 21; stdpp.bitvector.definitions.Z_to_bv 8 152; stdpp.bitvector.definitions.Z_to_bv 8 25; stdpp.bitvector.definitions.Z_to_bv 8 255; stdpp.bitvector.definitions.Z_to_bv 8 31].
Definition gw_rom_RDEBRUIJN : list (stdpp.bitvector.definitions.bv 8) :=
[stdpp.bitvector.definitions.Z_to_bv 8 0; stdpp.bitvector.definitions.Z_to_bv 8 1; stdpp.bitvector.definitions.Z_to_bv 8 28; stdpp.bitvector.definitions.Z_to_bv 8 2; stdpp.bitvector.definitions.Z_to_bv 8 29; stdpp.bitvector.definitions.Z_to_bv 8 14; stdpp.bitvector.definitions.Z_to_bv 8 24; stdpp.bitvector.definitions.Z_to_bv 8 3; stdpp.bitvector.definitions.Z_to_bv 8 30; stdpp.bitvector.definitions.Z_to_bv 8 22; stdpp.bitvector.definitions.Z_to_bv 8 20; stdpp.bitvector.definitions.Z_to_bv 8 15; stdpp.bitvector.definitions.Z_to_bv 8 25; stdpp.bitvector.definitions.Z_to_bv 8 17; stdpp.bitvector.definitions.Z_to_bv 8 4; stdpp.bitvector.definitions.Z_to_bv 8 8; stdpp.bitvector.definitions.Z_to_bv 8 31; stdpp.bitvector.definitions.Z_to_bv 8 27; stdpp.bitvector.definitions.Z_to_bv 8 13; stdpp.bitvector.definitions.Z_to_bv 8 23; stdpp.bitvector.definitions.Z_to_bv 8 21; stdpp.bitvector.definitions.Z_to_bv 8 19; stdpp.bitvector.definitions.Z_to_bv 8 16; stdpp.bitvector.definitions.Z_to_bv 8 7; stdpp.bitvector.definitions.Z_to_bv 8 26; stdpp.bitvector.definitions.Z_to_bv 8 12; stdpp.bitvector.definitions.Z_to_bv 8 18; stdpp.bitvector.definitions.Z_to_bv 8 6; stdpp.bitvector.definitions.Z_to_bv 8 11; stdpp.bitvector.definitions.Z_to_bv 8 5; stdpp.bitvector.definitions.Z_to_bv 8 10; stdpp.bitvector.definitions.Z_to_bv 8 9].
Definition gw_rom_RSMALL_CNT : list (stdpp.bitvector.definitions.bv 8) :=
[stdpp.bitvector.definitions.Z_to_bv 8 30; stdpp.bitvector.definitions.Z_to_bv 8 30; stdpp.bitvector.definitions.Z_to_bv 8 30; stdpp.bitvector.definitions.Z_to_bv 8 31; stdpp.bitvector.definitions.Z_to_bv 8 15; stdpp.bitvector.definitions.Z_to_bv 8 15; stdpp.bitvector.definitions.Z_to_bv 8 20; stdpp.bitvector.definitions.Z_to_bv 8 10; stdpp.bitvector.definitions.Z_to_bv 8 10; stdpp.bitvector.definitions.Z_to_bv 8 31; stdpp.bitvector.definitions.Z_to_bv 8 15; stdpp.bitvector.definitions.Z_to_bv 8 7; stdpp.bitvector.definitions.Z_to_bv 8 25; stdpp.bitvector.definitions.Z_to_bv 8 12; stdpp.bitvector.definitions.Z_to_bv 8 6; stdpp.bitvector.definitions.Z_to_bv 8 21; stdpp.bitvector.definitions.Z_to_bv 8 10; stdpp.bitvector.definitions.Z_to_bv 8 5; stdpp.bitvector.definitions.Z_to_bv 8 18; stdpp.bitvector.definitions.Z_to_bv 8 8; stdpp.bitvector.definitions.Z_to_bv 8 4; stdpp.bitvector.definitions.Z_to_bv 8 31; stdpp.bitvector.definitions.Z_to_bv 8 15; stdpp.bitvector.definitions.Z_to_bv 8 7; stdpp.bitvector.definitions.Z_to_bv 8 28; stdpp.bitvector.definitions.Z_to_bv 8 14; stdpp.bitvector.definitions.Z_to_bv 8 6].
Definition gw_rom_RMED_CNT : list (stdpp.bitvector.definitions.bv 8) :=
[stdpp.bitvector.definitions.Z_to_bv 8 28; stdpp.bitvector.definitions.Z_to_bv 8 24; stdpp.bitvector.definitions.Z_to_bv 8 20; stdpp.bitvector.definitions.Z_to_bv 8 32].

Definition gw_rd1 (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (a : Z) : bool :=
match LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs (QZDE.wa a) 1 with Some [_] => true | _ => false end.

Definition gw_win (a b : Z) : Prop := (a <= b)%Z.
Definition gw_winal (a k : Z) : Prop := (a mod k = 0)%Z.

Ltac gw_expose_win := repeat match goal with H : gw_win _ _ |- _ => unfold gw_win in H end.
Ltac gw_expose_winal := repeat match goal with H : gw_winal _ _ |- _ => unfold gw_winal in H end.
Ltac gw_expose_al a := repeat match goal with H : gw_al a _ |- _ => unfold gw_al in H end.
Ltac gw_expose_fam a :=
repeat match goal with
| H : gw_br a _ |- _ => unfold gw_br in H
| H : gw_le a _ |- _ => unfold gw_le in H
| H : gw_le _ a |- _ => unfold gw_le in H
| H : gw_le (a + _) _ |- _ => unfold gw_le in H
| H : gw_le _ (a + _) |- _ => unfold gw_le in H
end; gw_expose_win.

From Stdlib Require Import Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac gwm_is_zlit c := lazymatch c with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac gw_addr_norm_in H :=
repeat match type of H with context [(?b + ?c1 + ?c2)%Z] =>
gwm_is_zlit c1; let v := eval vm_compute in (c1 + c2)%Z in gwm_is_zlit v; replace (b + c1 + c2)%Z with (b + v)%Z in H by lia end.
Ltac gw_addr_norm :=
repeat match goal with |- context [(?b + ?c1 + ?c2)%Z] =>
gwm_is_zlit c1; let v := eval vm_compute in (c1 + c2)%Z in gwm_is_zlit v; replace (b + c1 + c2)%Z with (b + v)%Z by lia end.
Ltac gw_exact H :=
first [ exact H
| let H' := fresh "GWX" in pose proof H as H'; gw_addr_norm_in H'; gw_addr_norm; exact H' ].

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import GwCallee GwFold.
From Ltac2 Require Import Ltac2 Constr Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Ltac2 rec gwm_ctx_args (ty : constr) (acc : constr list) : constr list * constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in gwm_ctx_args rest (h :: acc)
| Err _ =>
match Constr.Unsafe.kind (Constr.Binder.type b) with
| Constr.Unsafe.App f _ =>
if Constr.equal f '@gw_hyp then
match Env.expand [id] with
| r :: _ => gwm_ctx_args rest (Env.instantiate r :: acc)
| [] => (acc, ty)
end
else (acc, ty)
| _ => (acc, ty)
end
end
| None => (acc, ty)
end
| _ => (acc, ty)
end.
Ltac2 gwm_ctx_app (t : constr) : constr * constr :=
let (acc, rest) := gwm_ctx_args (Constr.type t) [] in
let r := match acc with
| [] => t
| _ :: _ => Constr.Unsafe.make (Constr.Unsafe.App t (Array.of_list (List.rev acc)))
end in
(r, Constr.Unsafe.substnl acc 0 rest).
Ltac2 gw_ctx_fold_ty2_0 (t : constr) (tb : constr) : unit := let (_, ty) := gwm_ctx_app t in gwf_exact (gwf_fold (gwf_table tb) ty).
Ltac gw_ctx_fold_ty2 t tb := let f := ltac2:(t tb |- gw_ctx_fold_ty2_0 (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr tb))) in f t tb.
Ltac2 gw_ctx_fold_tm2_0 (t : constr) : unit := let (r, _) := gwm_ctx_app t in Std.exact_no_check r.
Ltac gw_ctx_fold_tm2 t := let f := ltac2:(t |- gw_ctx_fold_tm2_0 (Option.get (Ltac1.to_constr t))) in f t.

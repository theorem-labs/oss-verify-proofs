(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Ltac is_closed_arith e :=
  lazymatch e with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac | true => idtac | false => idtac
  | Z.add ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.sub ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.mul ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.div ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.modulo ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.land ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.lor ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.lxor ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.shiftr ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.shiftl ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.opp ?a => is_closed_arith a
  | Z.b2z ?a => is_closed_arith a
  | Z.ltb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.leb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.eqb ?a ?b => is_closed_arith a; is_closed_arith b
  | negb ?a => is_closed_arith a
  | andb ?a ?b => is_closed_arith a; is_closed_arith b
  | orb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.pow ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.to_nat ?a => is_closed_arith a
  | Z.of_nat ?a => is_closed_arith a
  | O => idtac | S ?a => is_closed_arith a
  | @bv_unsigned _ ?a => is_closed_arith a
  | @bv_signed _ ?a => is_closed_arith a
  | Z_to_bv _ ?a => is_closed_arith a
  | sxb ?a => is_closed_arith a
  | zxb ?a => is_closed_arith a
  end.
Ltac fold_lits :=
  cbn beta;
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
        lazymatch e with
        | Z0 => fail | Zpos _ => fail | Zneg _ => fail
        | _ => is_closed_arith e;
               let v := eval vm_compute in e in
               progress change (Z_to_bv 64 e) with (Z_to_bv 64 v)
        end
  | |- context [sxb (Z_to_bv 8 ?z)] =>
        is_closed_arith z;
        let v := eval vm_compute in (bv_signed (Z_to_bv 8 z)) in
        progress change (sxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word)
  | |- context [zxb (Z_to_bv 8 ?z)] =>
        is_closed_arith z;
        let v := eval vm_compute in (bv_unsigned (Z_to_bv 8 z)) in
        progress change (zxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word)
  end.

(* [comment removed for export] *)
Ltac fold_ext :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_closed_arith z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        progress change (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v : word)
  | |- context [zx32 (Z_to_bv 64 ?z)] => is_closed_arith z; let v := eval vm_compute in (bv_unsigned (zx32 (Z_to_bv 64 z))) in
        progress change (zx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v : word)
  end.
Ltac fl := fold_ext; fold_lits.

(* [comment removed for export] *)
Ltac callx tac :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ] end.
Ltac callxp tac prep :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | prep; post_call segs m ] end.

(* [comment removed for export] *)
Ltac restk lo ST :=
  repeat match goal with H : stk _ ?mm lo ?x, H' : stk _ ?mm' lo ?x' |- _ => constr_eq mm mm'; clear H' end;
  match goal with H : stk _ _ lo _ |- _ => rename H into ST end.


End CeilWrap.
(* [comment removed for export] *)
Ltac is_closed_arith e :=
  lazymatch e with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac | true => idtac | false => idtac
  | Z.add ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.sub ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.mul ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.div ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.modulo ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.land ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.lor ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.lxor ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.shiftr ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.shiftl ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.opp ?a => is_closed_arith a
  | Z.b2z ?a => is_closed_arith a
  | Z.ltb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.leb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.eqb ?a ?b => is_closed_arith a; is_closed_arith b
  | negb ?a => is_closed_arith a
  | andb ?a ?b => is_closed_arith a; is_closed_arith b
  | orb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.pow ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.to_nat ?a => is_closed_arith a
  | Z.of_nat ?a => is_closed_arith a
  | O => idtac | S ?a => is_closed_arith a
  | @bv_unsigned _ ?a => is_closed_arith a
  | @bv_signed _ ?a => is_closed_arith a
  | Z_to_bv _ ?a => is_closed_arith a
  | sxb ?a => is_closed_arith a
  | zxb ?a => is_closed_arith a
  end.
Ltac fold_lits :=
  cbn beta;
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
        lazymatch e with
        | Z0 => fail | Zpos _ => fail | Zneg _ => fail
        | _ => is_closed_arith e;
               let v := eval vm_compute in e in
               progress change (Z_to_bv 64 e) with (Z_to_bv 64 v)
        end
  | |- context [sxb (Z_to_bv 8 ?z)] =>
        is_closed_arith z;
        let v := eval vm_compute in (bv_signed (Z_to_bv 8 z)) in
        progress change (sxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word)
  | |- context [zxb (Z_to_bv 8 ?z)] =>
        is_closed_arith z;
        let v := eval vm_compute in (bv_unsigned (Z_to_bv 8 z)) in
        progress change (zxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word)
  end.
Ltac fold_ext :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_closed_arith z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        progress change (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v : word)
  | |- context [zx32 (Z_to_bv 64 ?z)] => is_closed_arith z; let v := eval vm_compute in (bv_unsigned (zx32 (Z_to_bv 64 z))) in
        progress change (zx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v : word)
  end.
Ltac fl := fold_ext; fold_lits.
Ltac callx tac :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ] end.
Ltac callxp tac prep :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | prep; post_call segs m ] end.
Ltac restk lo ST :=
  repeat match goal with H : stk _ ?mm lo ?x, H' : stk _ ?mm' lo ?x' |- _ => constr_eq mm mm'; clear H' end;
  match goal with H : stk _ _ lo _ |- _ => rename H into ST end.

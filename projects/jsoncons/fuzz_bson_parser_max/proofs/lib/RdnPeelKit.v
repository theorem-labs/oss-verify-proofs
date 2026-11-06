(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec StepTac.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Ltac1 Array.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Fixpoint wchainZ (m : word -> option byte) (ws : list (Z * list byte)) : word -> option byte :=
  match ws with
  | [] => m
  | (x, bs) :: r => wbytes (wchainZ m r) (Z_to_bv 64 x) bs
  end.

Fixpoint wch_ok (y : Z) (n : nat) (ws : list (Z * list byte)) : Prop :=
  match ws with
  | [] => True
  | (x, bs) :: r =>
      (0 <= x < 2 ^ 64 /\ x + Z.of_nat (length bs) <= 2 ^ 64 /\ (y + Z.of_nat n <= x \/ x + Z.of_nat (length bs) <= y))
      /\ wch_ok y n r
  end.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Lemma rdn_wchainZ_out : forall segs m ws y n,
  0 <= y < 2 ^ 64 -> y + Z.of_nat n <= 2 ^ 64 -> wch_ok y n ws ->
  rdn segs (wchainZ m ws) (Z_to_bv 64 y) n = rdn segs m (Z_to_bv 64 y) n.
Proof.
  intros segs m ws y n Hy Hyn. induction ws as [|[x bs] r IH]; cbn [wchainZ wch_ok]; [reflexivity|].
  intros [(Hx & Hxl & Hd) Hr]. rewrite rdn_wbytes_out.
  - exact (IH Hr).
  - rewrite !u_Z2bv by lia. exact Hd.
  - rewrite u_Z2bv by lia. exact Hyn.
  - rewrite u_Z2bv by lia. exact Hxl.
Qed.
End FPX_1.

(* [comment removed for export] *)
Ltac2 rec chain_split (m : constr) (b : constr) : constr * constr :=
  match Constr.Unsafe.kind m with
  | Constr.Unsafe.App h args =>
      if Bool.and (Constr.equal h '@wbytes) (Int.equal (Array.length args) 3) then
        let a := Array.get args 1 in
        if Constr.equal a b then ('(@nil (Z * list byte)), m)
        else
          match Constr.Unsafe.kind a with
          | Constr.Unsafe.App ha aargs =>
              if Bool.and (Constr.equal ha '@Z_to_bv) (Int.equal (Array.length aargs) 2) then
                if Constr.equal (Array.get aargs 0) '64%N then
                  let x := Array.get aargs 1 in
                  let bs := Array.get args 2 in
                  let (r, base) := chain_split (Array.get args 0) b in
                  ('(@cons (Z * list byte) ($x, $bs) $r), base)
                else ('(@nil (Z * list byte)), m)
              else ('(@nil (Z * list byte)), m)
          | _ => ('(@nil (Z * list byte)), m)
          end
      else ('(@nil (Z * list byte)), m)
  | _ => ('(@nil (Z * list byte)), m)
  end.

Ltac wch_solve side :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; [ side | wch_solve side ]
  end.

(* [comment removed for export] *)
Ltac2 rdn_peel_many (side : Ltac1.t) : unit :=
  lazy_match! Control.goal () with
  | @eq _ (rdn ?segs ?m (Z_to_bv 64 ?y) ?n) _ =>
      let b := '(Z_to_bv 64 $y) in
      let (ws, base) := chain_split m b in
      lazy_match! ws with
      | nil => Control.zero (Tactic_failure None)
      | _ =>
          ltac1:(segs m base ws y n side |-
                 change_no_check m with (wchainZ base ws);
                 rewrite (rdn_wchainZ_out segs base ws y n); [ | side | side | cbn [wch_ok]; wch_solve side ])
            (Ltac1.of_constr segs) (Ltac1.of_constr m) (Ltac1.of_constr base) (Ltac1.of_constr ws) (Ltac1.of_constr y) (Ltac1.of_constr n) side
      end
  end.
Ltac rdn_peel_many side := let f := ltac2:(side |- Control.enter (fun () => rdn_peel_many side)) in f side.

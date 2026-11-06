(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec SeqExec StepTac WalkTac WalkFastV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac gr_fast1 :=
  match goal with
  | |- context [getr ?ch0 ?r] =>
      let ch := wf_chain_of ch0 in
      lazymatch ch with regupd _ _ _ => idtac end;
      let zr := reg_lit_z r in
      let res := rch_walk ch zr in
      lazymatch res with
      | (?l, Some ?v) =>
          let base := rch_base ch l in
          let E := constr:(getr_rch_hit base l r v (@eq_refl bool false) (@eq_refl word v) : getr ch0 r = v) in
          rewrite E
      | (?l, None) =>
          lazymatch l with RNil => fail | _ => idtac end;
          let base := rch_base ch l in
          let E := constr:(getr_rch_miss base l r (@eq_refl bool true) : getr ch0 r = getr base r) in
          rewrite E
      end
  end.

(* [comment removed for export] *)
Ltac gr_slow :=
  lazymatch goal with
  | |- context [getr (regupd _ _ _) _] =>
      repeat (first [ rewrite getr_same by (intros E; discriminate E)
                    | rewrite getr_other by (intros E; discriminate E) ])
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac add0_fast :=
  tryif (match goal with
         | |- context [Z.add _ Z0] => idtac
         | |- context [Z.add Z0 _] => idtac
         end)
  then rewrite ?Z.add_0_r, ?Z.add_0_l else idtac.

Ltac gr_fast := repeat gr_fast1; gr_slow; add0_fast.

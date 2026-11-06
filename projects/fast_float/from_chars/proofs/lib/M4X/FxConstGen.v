(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition gdata : Type := (list (sst * list xfact) * list nat * list plan)%type.

Section Trace.
Variable t : tree xi.
Variable img : tree Z.
Variable ins : list positive.
Variable depth : nat.
Variable s0 : sst.

(* [comment removed for export] *)
Fixpoint xtrace (nodes : list (Z * xaction)) (pend : list xst) : list (option gdata) :=
  match nodes with
  | [] => []
  | (pc, a) :: rest =>
      let here := List.filter (fun X => Z.eqb (s_pc (xs_st X)) pc) pend in
      let others := List.filter (fun X => negb (Z.eqb (s_pc (xs_st X)) pc)) pend in
      match here with
      | [] => None :: xtrace rest others
      | _ :: _ =>
          let go := fun (o : option (list xst)) => match o with Some ks => None :: xtrace rest (others ++ ks) | None => [] end in
          match a with
          | XGenTs mk g =>
              let '(Ps, ix) := mk here in
              let d := Some (Ps, ix, List.map (fun Q => g (fst Q)) Ps) in
              match xchecks t img depth s0 g Ps with Some f => d :: xtrace rest (others ++ f) | None => [d] end
          | XCall c => go (xcalls c here)
          | XCallK c => go (xcalls c here)
          | XCallKs cs => go (xcallsm cs here)
          | XFragK c pcQ => go (xfrags c pcQ here)
          | XFragKs cs pcQ => go (xfragsm cs pcQ here)
          | XHand f => go (xhands f here)
          end
      end
  end.
Definition xtrace_start (p0 : plan) (nodes : list (Z * xaction)) : list (option gdata) :=
  match check t img ins depth p0 s0 with Some f => xtrace nodes (List.map (fun K => XST K []) f) | None => [] end.
End Trace.

(* [comment removed for export] *)
Fixpoint treg_eqb (a b : tree lin) : bool :=
  match a, b with
  | TEmpty, TEmpty => true
  | TNode l v r, TNode l' v' r' =>
      if match v, v' with Some x, Some y => lin_eqb x y | None, None => true | _, _ => false end
      then if treg_eqb l l' then treg_eqb r r' else false else false
  | _, _ => false
  end.
Definition tkey_eqb (P Q : sst) : bool :=
  if Pos.eqb (s_next P) (s_next Q) then
    if Nat.eqb (List.length (s_facts P)) (List.length (s_facts Q)) then
      if Z.eqb (s_pc P) (s_pc Q) then treg_eqb (s_regs P) (s_regs Q) else false
    else false
  else false.
Fixpoint pick_plan (Ps : list (sst * list xfact)) (pls : list plan) (P : sst) : plan :=
  match Ps, pls with
  | (Q, _) :: Ps', pl :: pls' => match Ps' with [] => pl | _ => if tkey_eqb Q P then pl else pick_plan Ps' pls' P end
  | _, _ => PFin
  end.
Definition xgen_c (d : gdata) : xaction :=
  let '(Ps, ix, pls) := d in XGenTs (fun _ => (Ps, ix)) (pick_plan Ps pls).
Fixpoint xconst (nodes : list (Z * xaction)) (ds : list (option gdata)) : list (Z * xaction) :=
  match nodes with
  | [] => []
  | (pc, a) :: rest =>
      match ds with
      | Some d :: ds' => (pc, match a with XGenTs _ _ => xgen_c d | _ => a end) :: xconst rest ds'
      | None :: ds' => (pc, a) :: xconst rest ds'
      | [] => (pc, a) :: xconst rest []
      end
  end.

Lemma xgen_c_gen : forall d, exists mk g, xgen_c d = XGenTs mk g.
Proof. intros [[Ps ix] pls]. cbn. eauto. Qed.
Lemma xconst_xsites : forall nodes ds, xsites (xconst nodes ds) = xsites nodes.
Proof.
  induction nodes as [|[pc a] rest IH]; intros ds; [reflexivity|]. destruct ds as [|[d|] ds']; cbn [xconst].
  - destruct a; cbn [xsites]; rewrite ?IH; reflexivity.
  - destruct a; cbn [xsites]; rewrite ?IH; try reflexivity. destruct (xgen_c_gen d) as (mk' & g' & ->). cbn [xsites]. rewrite ?IH. reflexivity.
  - destruct a; cbn [xsites]; rewrite ?IH; reflexivity.
Qed.
Lemma xconst_xksites : forall nodes ds, xksites (xconst nodes ds) = xksites nodes.
Proof.
  induction nodes as [|[pc a] rest IH]; intros ds; [reflexivity|]. destruct ds as [|[d|] ds']; cbn [xconst].
  - destruct a; cbn [xksites]; rewrite ?IH; reflexivity.
  - destruct a; cbn [xksites]; rewrite ?IH; try reflexivity. destruct (xgen_c_gen d) as (mk' & g' & ->). cbn [xksites]. rewrite ?IH. reflexivity.
  - destruct a; cbn [xksites]; rewrite ?IH; reflexivity.
Qed.
Lemma xconst_xfsites : forall nodes ds, xfsites (xconst nodes ds) = xfsites nodes.
Proof.
  induction nodes as [|[pc a] rest IH]; intros ds; [reflexivity|]. destruct ds as [|[d|] ds']; cbn [xconst].
  - destruct a; cbn [xfsites]; rewrite ?IH; reflexivity.
  - destruct a; cbn [xfsites]; rewrite ?IH; try reflexivity. destruct (xgen_c_gen d) as (mk' & g' & ->). cbn [xfsites]. rewrite ?IH. reflexivity.
  - destruct a; cbn [xfsites]; rewrite ?IH; reflexivity.
Qed.
Lemma xconst_xhandl : forall nodes ds, xhandl (xconst nodes ds) = xhandl nodes.
Proof.
  induction nodes as [|[pc a] rest IH]; intros ds; [reflexivity|]. destruct ds as [|[d|] ds']; cbn [xconst].
  - destruct a; cbn [xhandl]; rewrite ?IH; reflexivity.
  - destruct a; cbn [xhandl]; rewrite ?IH; try reflexivity. destruct (xgen_c_gen d) as (mk' & g' & ->). cbn [xhandl]. rewrite ?IH. reflexivity.
  - destruct a; cbn [xhandl]; rewrite ?IH; reflexivity.
Qed.

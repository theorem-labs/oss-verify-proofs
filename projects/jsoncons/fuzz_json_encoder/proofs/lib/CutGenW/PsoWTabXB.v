(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore LibSym SegRun SegPlan Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmEncSpecs PmLibSpecsW PmRef.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX Pm5CutKit CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsoInstXB ParseSomeChkXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import RelObsXB.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 250. Set Printing Depth 100000.

Module PSOWT.
Import PML PMR OBSXA.
(* [comment removed for export] *)
Fixpoint nodup_acts (l : list act) : list act :=
  match l with [] => [] | a :: r => if existsb (act_eqb a) r then nodup_acts r else a :: nodup_acts r end.
Fixpoint bytes (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: bytes (lo + 1) n' end.
(* [comment removed for export] *)
Definition tmpl_bytev (tmpl : list kentry) : option nat := match min_var (named_bytes 0 tmpl) None with Some (_, v) => Some v | None => None end.
Definition leaf_acts (i k : nat) : option (Z * list act * bool) :=      (* [comment removed for export] *)
  match nth_error CPS i, nth_error TAGS i with
  | Some c, Some tg =>
      let ps := nth k (CC.cp_PSS c) (SR.PS 0 [] [] []) in let t := nth k tg (CC.TOther 0) in
      match leaf_state (CC.cp_know c) (SR.ps_cells ps) with
      | Some (slo, shi) =>
          if negb (slo =? shi) then None else
          match match ob_bytev (observe (CC.cp_nx c) ps t) with Some bv => Some bv | None => tmpl_bytev (CC.cp_know c) end with      (* [comment removed for export] *)
          | Some bv => let adm := List.filter (byte_adm bv (SR.ps_cells ps)) (bytes 0 256) in
                       Some (slo, nodup_acts (List.map (fun b => dispatch slo ST_ROOT b) adm), forallb (fun b => pindep slo b) adm)
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition RSRC (j : nat) : option (nat * nat * Z) := PSO.src_of j.
Definition SRCST (j : nat) : option Z := match RSRC j with Some (i, k, _) => match leaf_acts i k with Some (s, _, _) => Some s | None => None end | None => None end.
Definition RACT (j : nat) : option act := match RSRC j with Some (i, k, _) => match leaf_acts i k with Some (_, [a], _) => Some a | _ => None end | None => None end.
Definition RPIND (j : nat) : bool := match RSRC j with Some (i, k, _) => match leaf_acts i k with Some (_, _, p) => p | None => false end | None => false end.
Definition RACTS : list (option act) := Eval vm_compute in List.map RACT (seq 0 PSO.NCUT).
(* [comment removed for export] *)
Fixpoint racti (fuel : nat) (j : nat) : option act :=
  match nth j RACTS None with
  | Some a => Some a
  | None => match fuel, RSRC j with S f, Some (i, _, _) => if Nat.ltb i PSOC.NDECL then None else racti f i | _, _ => None end
  end.
Definition RACTI : list (option act) := Eval vm_compute in List.map (racti 6) (seq 0 PSO.NCUT).
Definition ract (j : nat) : option act := nth j RACTI None.
(* [comment removed for export] *)
Definition consumes (a : act) : bool :=
  match a with
  | AErr _ k => k | AAccept => false | ASkip => false | ASlash => true | ABegin _ => true | AEnd _ => true | AString _ => true | ANumber => true
  | ALit _ => false | AComma => true | AGoto _ k => k | APop k => k | APushCr => true | ALitDone => true | AParseString => false | AParseNumber => false | AStuck => false
  end.
Definition dadv (i k : nat) : Z :=
  match nth_error CPS i with
  | Some c => let cells := SR.ps_cells (nth k (CC.cp_PSS c) (SR.PS 0 [] [] [])) in
      match PSO.pview (CC.cp_know c), PSO.pview cells with Some t, Some l => PSO.d_adv (PSO.mkdelta cells t l) | _, _ => 0 end
  | None => 0 end.
Fixpoint roffi (fuel : nat) (j : nat) : Z :=
  match fuel, RSRC j with S f, Some (i, k, _) => (if Nat.ltb i PSOC.NDECL then 0 else roffi f i) + dadv i k | _, _ => 0 end.
Definition ROFFS : list Z := Eval vm_compute in List.map (roffi 6) (seq 0 PSO.NCUT).
Definition roff (j : nat) : Z := nth j ROFFS 0.
Definition woffi (j : nat) : Z :=
  match PSO.kind_of j with
  | PSO.KPop => match ract j with Some a => (if consumes a then 1 else 0) | None => 0 end - roff j
  | _ => - roff j
  end.
Definition WOFFS : list Z := Eval vm_compute in List.map woffi (seq 0 PSO.NCUT).
Definition woff (j : nat) : Z := nth j WOFFS 0.
Fixpoint ppvi (fuel : nat) (j : nat) : list nat :=      (* [comment removed for export] *)
  (match PSO.kind_of j with PSO.KParent => [(CC.cp_nx (PSO.cutn j) - APC.NCS - 1)%nat] | _ => [] end) ++
  match fuel, RSRC j with S f, Some (i, _, _) => if Nat.ltb i PSOC.NDECL then [] else ppvi f i | _, _ => [] end.
Definition PPVS : list (list nat) := Eval vm_compute in List.map (ppvi 6) (seq 0 PSO.NCUT).
Definition ppv (j : nat) : list nat := nth j PPVS [].
Definition SEV : nat := 90.
Lemma SEV_ok : nth 11 (CC.cp_regs (PSO.cutn 10)) (ELit 0) = EVar SEV /\ PSO.kind_of 10 = PSO.KSe /\ forall j, PSO.kind_of j = PSO.KSe -> j = 10%nat.
Proof.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  assert (X : forallb (fun j => negb (PSO.kind_eqb (PSO.kind_of j) PSO.KSe) || Nat.eqb j 10) (seq 0 PSO.NCUT) = true) by (vm_compute; reflexivity).
  intros j Hj. destruct (Nat.lt_ge_cases j PSO.NCUT) as [L|G].
  - rewrite forallb_forall in X. specialize (X j ltac:(apply in_seq; lia)). rewrite Hj in X. cbn in X. apply Nat.eqb_eq in X. exact X.
  - exfalso. unfold PSO.kind_of in Hj. rewrite nth_overflow in Hj; [discriminate Hj|].
    assert (LEN : length PSO.INFO = PSO.NCUT) by (vm_compute; reflexivity). rewrite LEN. exact G.
Qed.
(* [comment removed for export] *)
Definition eofk (j : nat) : bool := (PSO.kind_eqb (PSO.kind_of j) PSO.KErrh && PSO.u0 j)%bool.
(* [comment removed for export] *)
Definition census := List.map (fun j => (j, PSO.kind_of j, ract j, RPIND j, roff j, woff j, ppv j)) (seq (PSOC.NDECL) (PSO.NCUT - PSOC.NDECL)).
End PSOWT.
Eval vm_compute in PSOWT.census.

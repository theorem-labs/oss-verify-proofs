(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PropExec AzSymExec3 AzSymExec3B AzPlanCore AzPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.






(* [comment removed for export] *)
Inductive dstep : Type :=
| DRun (stops : list Z) | DLo (e : expr) (mid : Z) | DHi (e : expr) (mid : Z) | DRLo (r : nat) (mid : Z) | DRHi (r : nat) (mid : Z)
| DExt (id : nat) (args : list expr) | DFact (K : kentry) | DVia (e via : expr) (lo hi : Z) | DLe (e big : expr) (hi : Z)
| DScale (e : expr) (c hi : Z)
| DBrF | DBrT   (* [comment removed for export] *)
| DX2a (id : nat) (args : list expr) | DX2b (id : nat) (args : list expr)   (* [comment removed for export] *)
(* [comment removed for export] *)
| DExtA (id : nat) (pre : list expr) (b : expr) (off : Z) (w : nat) (post : list expr).

Section Stepper.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable bfuel : nat.

Definition dgo (gcb : nat) (cs : acs) (st : dstep) : option acs :=
  match st with
  | DRun stops => run_block_gc segs IT gcb false 0%nat bfuel (stops ++ STOPS A) cs   (* [comment removed for export] *)
  | DLo e mid => match erange (kn cs) e with Some (lo, hi) => Some (set_kn cs (KRange e lo mid :: kn cs)) | None => None end
  | DHi e mid => match erange (kn cs) e with Some (lo, hi) => Some (set_kn cs (KRange e (mid + 1) hi :: kn cs)) | None => None end
  | DRLo r mid => let e := reg cs r in match erange (kn cs) e with Some (lo, hi) => Some (set_kn cs (KRange e lo mid :: kn cs)) | None => None end
  | DRHi r mid => let e := reg cs r in match erange (kn cs) e with Some (lo, hi) => Some (set_kn cs (KRange e (mid + 1) hi :: kn cs)) | None => None end
  | DExt id args => XN id args cs
  | DExtA id pre b off w post =>
      match know_lookup segs (kn cs) b off w false [] [] with
      | LHit v [] _ =>
          (* [comment removed for export] *)
          let raw := match v with EExt false 0 w' x => if Nat.eqb w' w then x else v | _ => v end in
          XN id (pre ++ raw :: post) cs
      | _ => None
      end
  | DFact K => if fact_ok (kn cs) K then Some (add_kn cs [K]) else None
  | DVia e via lo hi => if factvia_ok (kn cs) e via lo hi then Some (add_kn cs [KRange e lo hi]) else None
  | DLe e big hi => if factle_ok (kn cs) e big hi then Some (add_kn cs [KRange e 0 hi]) else None
  | DScale e c hi => if factscale_ok (kn cs) e c hi then Some (add_kn cs [KRange e 0 hi]) else None
  | DX2a id args => match XB id args cs with Some (a, _) => Some a | None => None end
  | DX2b id args => match XB id args cs with Some (_, b) => Some b | None => None end
  | DBrF | DBrT =>
      match branch_probe2 IT cs with
      | Some (e, pos) =>
          match erange (kn cs) e with
          | Some (lo, hi) =>
              let cs0 := set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs) in
              let cs1 := set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs) in
              let taken := match st with DBrT => true | _ => false end in
              Some (if Bool.eqb taken pos then cs1 else cs0)
          | None => None
          end
      | None => None
      end
  end.
(* [comment removed for export] *)
Fixpoint dpath (gcb : nat) (cs : acs) (sts : list dstep) (n : nat) : nat * acs :=
  match sts with
  | [] => (n, cs)
  | st :: r => match dgo gcb cs st with Some cs' => dpath gcb cs' r (Datatypes.S n) | None => (n, cs) end
  end.
End Stepper.


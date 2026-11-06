(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Set Primitive Projections.
Class RunCeiling : Type := mkRC {
  rc_sp : Z ;
  rc_guard : word ;
  rc_secret : Z ;
  rc_secret_range : (0 <= rc_secret < 2^64)%Z
}.
Unset Primitive Projections.

Definition alloc_ceiling {RC : RunCeiling} : Z :=
  (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608)%Z.
Arguments alloc_ceiling : simpl never.

Section RC__.
Context {RC__ : RunCeiling}.

Lemma alloc_ceiling_range : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z.
Proof. unfold alloc_ceiling. lia. Qed.

Lemma alloc_ceiling_lt : (alloc_ceiling < two_pow_64)%Z.
Proof. unfold alloc_ceiling, two_pow_64. lia. Qed.

(* [comment removed for export] *)
Lemma alloc_ceiling_ge_min : (sp_window_lo - stack_max_size <= alloc_ceiling)%Z.
Proof. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. Qed.

Lemma alloc_ceiling_le_max : (alloc_ceiling <= sp_window_hi - stack_max_size)%Z.
Proof. unfold alloc_ceiling, sp_window_hi, stack_max_size. lia. Qed.

(* [comment removed for export] *)
Lemma alloc_ceiling_of_sp : forall h : VmMaps,
  bv_unsigned (vm_init_sp h) = rc_sp ->
  (sp_window_lo <= rc_sp <= sp_window_hi)%Z ->
  alloc_top h = alloc_ceiling.
Proof.
  intros h Hsp Hv. unfold alloc_top, alloc_ceiling, sp_window_lo, sp_window_hi, stack_max_size in *.
  rewrite Hsp. lia.
Qed.

End RC__.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 lc_isc (h : constr) (r : Std.reference) : bool :=
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant c _ => (match r with Std.ConstRef c' => Constant.equal c c' | _ => false end)
  | Constr.Unsafe.Ind i _ => (match r with Std.IndRef i' => Ind.equal i i' | _ => false end)
  | _ => false
  end.
Ltac2 lc_ceil_rc (t : constr) : constr option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      if Bool.and (Int.equal (Array.length args) 2) (lc_isc f reference:(Z.sub)) then
        (match Constr.Unsafe.kind (Array.get args 0) with
         | Constr.Unsafe.App f1 a1 =>
             if Bool.and (Int.equal (Array.length a1) 2) (lc_isc f1 reference:(Z.max)) then
               (match Constr.Unsafe.kind (Array.get a1 1) with
                | Constr.Unsafe.App f2 a2 =>
                    if Bool.and (Int.equal (Array.length a2) 2) (lc_isc f2 reference:(Z.min)) then
                      (match Constr.Unsafe.kind (Array.get a2 1) with
                       | Constr.Unsafe.Proj _ _ c => Some c
                       | Constr.Unsafe.App _ a3 => if Int.equal (Array.length a3) 1 then Some (Array.get a3 0) else None
                       | _ => None
                       end)
                    else None
                | _ => None
                end)
             else None
         | _ => None
         end)
      else None
  | _ => None
  end.
(* [comment removed for export] *)
Ltac2 lc_add (acc : (constr * constr) list) (t : constr) : (constr * constr) list :=
  match lc_ceil_rc t with
  | Some rc => if List.exist (fun p => let (t', _) := p in Constr.equal t' t) acc then acc else (t, rc) :: acc
  | None => acc
  end.
Ltac2 rec lc_occ_prop (acc : (constr * constr) list) (t : constr) : (constr * constr) list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      let n := Array.length args in
      if Int.equal n 2 then
        (if Bool.or (Bool.or (lc_isc h reference:(Z.le)) (lc_isc h reference:(Z.lt))) (Bool.or (lc_isc h reference:(Z.ge)) (lc_isc h reference:(Z.gt)))
         then lc_add (lc_add acc (Array.get args 0)) (Array.get args 1)
         else if Bool.or (Bool.or (lc_isc h reference:(and)) (lc_isc h reference:(or))) (lc_isc h reference:(iff))
         then Array.fold_left lc_occ_prop acc args
         else acc)
      else if Int.equal n 3 then
        (if lc_isc h reference:(eq) then
           (if lc_isc (Array.get args 0) reference:(Z) then lc_add (lc_add acc (Array.get args 1)) (Array.get args 2) else acc)
         else acc)
      else if Int.equal n 1 then
        (if lc_isc h reference:(not) then lc_occ_prop acc (Array.get args 0) else acc)
      else acc
  | Constr.Unsafe.Prod b body =>
      (* [comment removed for export] *)
      if Constr.Unsafe.noccur_between 1 1 body then lc_occ_prop (lc_occ_prop acc (Constr.Binder.type b)) body else acc
  | Constr.Unsafe.Cast c _ _ => lc_occ_prop acc c
  | _ => acc
  end.
(* [comment removed for export] *)
Ltac2 lf_fold_ceiling () : unit :=
  let gocc := lc_occ_prop [] (Control.goal ()) in
  let hocc := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => match lc_occ_prop [] ty with [] => None | l => Some (id, l) end
                 end) (Control.hyps ()) in
  let rc0 := match gocc with
             | p :: _ => let (_, rc) := p in Some rc
             | [] => match hocc with
                     | q :: _ => let (_, l) := q in (match l with p :: _ => let (_, rc) := p in Some rc | [] => None end)
                     | [] => None
                     end
             end in
  match rc0 with
  | None => Control.zero (Tactic_failure None)
  | Some rc =>
      List.iter (fun q => let (id, l) := q in
                   List.iter (fun p => let (t, rc) := p in
                                let hc := Control.hyp id in
                                ltac1:(t rc h |- change t with (@alloc_ceiling rc) in h) (Ltac1.of_constr t) (Ltac1.of_constr rc) (Ltac1.of_constr hc)) l) hocc;
      List.iter (fun p => let (t, rc) := p in
                   ltac1:(t rc |- change t with (@alloc_ceiling rc)) (Ltac1.of_constr t) (Ltac1.of_constr rc)) gocc;
      let id := Fresh.in_goal @zceil in
      Std.assert (Std.AssertValue id constr:(@alloc_ceiling_range $rc))
  end.
Ltac lf_fold_ceiling := ltac2:(Control.enter lf_fold_ceiling).

Ltac lf_ceil_hook := try lf_fold_ceiling.

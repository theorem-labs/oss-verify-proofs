(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HxSurg HarnFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HL Require Import HarnLoop HarnSite HarnFk HarnChain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PKEY : positive := 49.
Definition DBAND : Z := 1048576.
(* [comment removed for export] *)
Definition PM_FRAME : Z := 160.
Definition PM_LOW : Z := 64.
Definition PM_R3 : Z := 32.
(* [comment removed for export] *)
Definition pm_geo (S : sst) : option (nat * Z * Z * Z) :=
  match find_idx (s_rgs S) (rgk S 2) 0, find_idx (s_rgs S) (rgk S 8) 0 with
  | Some (i, o), Some (i8, o8) =>
      if Nat.eqb i i8 then match nth_error (s_rgs S) i with
                           | Some R => match is_const (rg_size R) with Some z => Some (i, z, o, o8 - 96 - (o + PM_LOW)) | None => None end
                           | None => None end
      else None
  | _, _ => None
  end.
Definition pm_ok (g : nat * Z * Z * Z) : bool := let '(_, z, o, sm) := g in ((Z.eqb sm 0 || Z.eqb sm 16) && Z.ltb (DBAND + 64) o && Z.ltb (o + PM_LOW + sm) z)%bool.
Definition pm_front (S : sst) : option nat := match pm_geo S with Some (i, _, _, _) => Some i | None => None end.
(* [comment removed for export] *)
Definition pm_cut (S : sst) : option (list rstep) :=
  match pm_geo S with
  | Some (O, z, o, sm) =>
      if pm_ok (O, z, o, sm) then
        match nth_error (s_rgs S) O with
        | Some R => let ps := if Z.eqb sm 0 then [(16, RW); (o - DBAND - 16, RW); (DBAND + PM_LOW - PM_R3, RW); (PM_R3, RW); (z - o - PM_LOW, RW)]
                              else [(o - DBAND, RW); (DBAND + PM_LOW - PM_R3, RW); (PM_R3, RW); (16, RW); (z - o - PM_LOW - 16, RW)] in
                    if rkind_eqb (rg_kind R) RW then Some (cut_k O (rg_base R) (rg_cont R) RW z ps) else None
        | None => None end
      else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition csz_at (S : sst) (i : nat) : Z := match nth_error (s_rgs S) i with Some R => match is_const (rg_size R) with Some z => z | None => 0 end | None => 0 end.
Definition pm_gidx (S : sst) : option nat := if Z.eqb (csz_at S 0) 16 then Some O else if Z.eqb (csz_at S 3) 16 then Some 3%nat else None.
(* [comment removed for export] *)
Definition pm_r0 (S : sst) : option lin := match pm_geo S with Some g => if pm_ok g then let '(_, _, _, sm) := g in Some (lconst (sm / 16)) else None | None => None end.
Definition PMCUT (k : MCH) : MCH :=
  NODE (HPSRK PKEY pm_r0) (SURG (SFront pm_front) (SURG (SSteps pm_cut) (SURG (SFront pm_gidx) k))).

(* [comment removed for export] *)
Definition SP0T : list (positive * Z) := [(1%positive, 32768); (2%positive, 4096); (3%positive, 64); (4%positive, 16)].
Definition stk_c (R : region) : option Z :=
  if terms_eqb (l_t (rg_base R)) SP0T then (let c := sgn64 (l_c (rg_base R)) in if Z.ltb c 0 then Some c else None) else None.
(* [comment removed for export] *)
Definition stk_pieces (S : sst) : list (nat * Z) :=
  List.flat_map (fun '(i, R) => match stk_c R with Some c => [(i, c)] | None => [] end) (List.combine (List.seq 0 (List.length (s_rgs S))) (s_rgs S)).
Fixpoint ins_desc (x : nat * Z) (l : list (nat * Z)) : list (nat * Z) :=
  match l with [] => [x] | y :: r => if Z.leb (snd y) (snd x) then x :: l else y :: ins_desc x r end.
Definition stk_desc (S : sst) : list (nat * Z) := List.fold_left (fun acc x => ins_desc x acc) (stk_pieces S) [].
(* [comment removed for export] *)
Definition pm_nth_hi (j : nat) (S : sst) : option nat := match nth_error (stk_desc S) j with Some (i, _) => Some i | None => None end.
Definition pm_merge (S : sst) : option (list rstep) :=
  match List.length (stk_pieces S) with 5%nat => Some [RMergeCC O; RMergeCC O; RMergeCC O; RMergeCC O] | _ => None end.
(* [comment removed for export] *)
Definition PMJOIN (k : MCH) : MCH :=
  SURG (SFront (pm_nth_hi 0)) (SURG (SFront (pm_nth_hi 1)) (SURG (SFront (pm_nth_hi 2)) (SURG (SFront (pm_nth_hi 3)) (SURG (SFront (pm_nth_hi 4))
  (SURG (SSteps pm_merge) k))))).
(* [comment removed for export] *)
Definition pm_stk1 (S : sst) : option nat := match stk_pieces S with [(i, _)] => Some i | _ => None end.
Fixpoint SINK (n m : nat) (k : MCH) : MCH := match m with O => k | Datatypes.S m' => SURG (SFront (fun _ => Some n)) (SINK n m' k) end.
Definition PMFIX (n : nat) (k : MCH) : MCH := SURG (SFront pm_stk1) (SINK n n k).

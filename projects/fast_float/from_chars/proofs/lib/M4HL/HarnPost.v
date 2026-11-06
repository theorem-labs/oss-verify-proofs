(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require HarnFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.HxDerive OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HL Require Import HarnLoop HarnChain HarnBudget.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition M1 : Z := 18446744073709551615.
(* [comment removed for export] *)
Definition rel_of (f : fact) : option (lin * Z * Z * positive * positive) :=
  match f with
  | FRange g lo hi =>
      match l_t g with
      | [(a, ka); (b, kb)] =>
          if (Pos.ltb a b && Z.eqb kb 1 && Z.eqb ka M1)%bool then Some (g, lo, hi, b, a)
          else if (Pos.ltb b a && Z.eqb ka 1 && Z.eqb kb M1)%bool then Some (g, lo, hi, a, b)
          else None
      | _ => None
      end
  | _ => None
  end.
Definition rels (fs : list fact) : list (lin * Z * Z * positive * positive) := List.flat_map (fun f => match rel_of f with Some r => [r] | None => [] end) fs.
Definition has_terms (fs : list fact) (l : lin) : bool := existsb (fun f => match f with FRange g _ _ => terms_eqb (l_t g) (l_t l) | _ => false end) fs.
(* [comment removed for export] *)
Definition sel_direct (fs : list fact) (rs : list (lin * Z * Z * positive * positive)) : list (lin * lin) :=
  List.flat_map (fun '(g, lo, hi, z, x) =>
     if negb (Z.eqb (l_c g) 0) then [] else       (* [comment removed for export] *)
     let dz := var_range fs z in let dx := var_range fs x in
     if (if Z.ltb (hi + snd dx) (snd dz) then true else Z.ltb (fst dz) (lo + fst dx)) then [(g, lvar x)] else []) rs.
(* [comment removed for export] *)
Definition sel_chain (fs : list fact) (rs : list (lin * Z * Z * positive * positive)) : list (lin * lin) :=
  List.flat_map (fun '(g1, _, _, z, x) =>
     List.flat_map (fun '(g2, _, _, z2, w) => if Pos.eqb z2 x then (if has_terms fs (ladd g1 g2) then [] else [(g1, g2)]) else []) rs) rs.
(* [comment removed for export] *)
Definition budget_of (fs : list fact) (x r : positive) : list lin :=
  List.flat_map (fun f => match f with
                          | FRange g _ _ =>
                              match l_t g with
                              | [(a, ka); (b, kb)] =>
                                  if (Pos.eqb a x && Z.eqb ka 1 && Pos.eqb b r && Z.ltb 0 kb && Z.ltb kb 4294967296)%bool then [g]
                                  else if (Pos.eqb b x && Z.eqb kb 1 && Pos.eqb a r && Z.ltb 0 ka && Z.ltb ka 4294967296)%bool then [g]
                                  else []
                              | _ => [] end
                          | _ => [] end) fs.
Definition sel_budget (S : sst) (rs : list (lin * Z * Z * positive * positive)) : list (lin * lin) :=
  let fs := s_facts S in
  match l_t (rC S) with
  | [(r, _)] => List.flat_map (fun '(g1, _, _, z, x) => match budget_of fs x r with
                                                        | g2 :: _ => if has_terms fs (ladd g1 g2) then [] else [(g1, g2)]
                                                        | [] => [] end) rs
  | _ => []
  end.
(* [comment removed for export] *)
Definition cvars (S : sst) : list positive := List.map fst (l_t (rU S)) ++ List.map fst (l_t (rC S)).
Definition bform_of (S : sst) (x : positive) : list lin :=
  let cv := cvars S in
  List.flat_map (fun f => match f with
                          | FRange g _ _ =>
                              if (existsb (fun '(y, k) => (Pos.eqb y x && Z.eqb k 1)%bool) (l_t g) &&
                                  forallb (fun '(y, _) => (Pos.eqb y x || existsb (Pos.eqb y) cv)%bool) (l_t g) && Nat.leb 2 (List.length (l_t g)))%bool then [g] else []
                          | _ => [] end) (s_facts S).
Definition sel_bform (S : sst) : list (lin * lin) :=
  let fs := s_facts S in
  List.flat_map (fun '(g1, _, _, z, x) => List.flat_map (fun g2 => if has_terms fs (ladd g1 g2) then [] else [(g1, g2)]) (bform_of S x)) (rels fs).
(* [comment removed for export] *)
Definition sel_all (S : sst) : list (lin * lin) :=
  let fs := s_facts S in let rs := rels fs in sel_direct fs rs ++ sel_chain fs rs ++ sel_budget S rs.
Definition POSTUSE (n : nat) (k : MCH) : MCH := NODE (HFSUML sel_all) k.
(* [comment removed for export] *)
Definition POSTCHAIN (n : nat) (k : MCH) : MCH := k.
Definition POSTBUDGET (n : nat) (k : MCH) : MCH := k.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module FGC.
Definition FACTGC_ID : nat := 117.   (* [comment removed for export] *)

Section Node.
  Context {fx : FPState}.

  Definition is_lit (e : expr) : bool := match e with ELit _ => true | _ => false end.

  (* [comment removed for export] *)
  Definition content_base (K : kentry) : option expr :=
    match K with
    | KWord (SA b _) _ _ | KZero (SA b _) _ | KBlob (SA b _) _ _ | KFill (SA b _) _ _ | KUnk (SA b _) _ | KWr (SA b _) _ => Some b
    | _ => None
    end.

  Definition has_cells (k : list kentry) (b : expr) : bool :=
    existsb (fun K => match content_base K with Some b' => expr_eqb b' b | None => false end) k.

  Definition hot_bases (H : list expr) : list expr := map (fun e => fst (split_lit e)) H.

  Definition is_hot (hs : list expr) (b : expr) : bool := is_lit b || existsb (expr_eqb b) hs.

  Definition keep_entry (hs : list expr) (k : list kentry) (K : kentry) : bool :=
    match K with
    | KDisj (SA b1 _) _ (SA b2 _) _ =>
        let c1 := has_cells k b1 in let c2 := has_cells k b2 in
        match hs with
        | [] => c1 && c2
        | _ => let h1 := is_hot hs b1 in let h2 := is_hot hs b2 in (h1 || h2) && (h1 || c1) && (h2 || c2)
        end
    | _ => true
    end%bool.

  Definition gc_kn (H : list expr) (k : list kentry) : list kentry :=
    List.filter (keep_entry (hot_bases H) k) k.

  (* [comment removed for export] *)
  Definition xn (args : list expr) (cs : acs) : option acs := Some (set_kn cs (gc_kn args (kn cs))).
End Node.
End FGC.

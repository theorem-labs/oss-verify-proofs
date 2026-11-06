(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA AcFam AcPri AcConvA AcNPop AcNEnq AcNPopG.

Module AcExt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALp AcMALlib AcNPop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition givex_hdr_ok (M : smodel) (a : ast) : bool :=
  (a_on a && Nat.eqb (List.length (a_pri a)) PRI_LEN && list_eqb pair_eqb (sm_own M) (a_own a))%bool.
Definition apost_givex (ix : list nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (givex_hdr_ok M a && incr_b ix &&
         forallb (fun i => match nth_error (s_rgs S) i with Some R => ext_in (s_facts S) a R | None => false end) ix)%bool
    (Some (with_rgs S (remove_ixs ix (s_rgs S)), M, a)).
Definition apost_shrinkx (i : nat) (s : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obind (nth_error (s_rgs S) i) (fun R =>
  obool (givex_hdr_ok M a && Z.leb 1 s && Z.leb s (fst (irange (s_facts S) (rg_size R))) && ext_in (s_facts S) a R)%bool
    (Some (with_rgs S (firstn i (s_rgs S) ++ RG (rg_base R) (lconst s) (rg_kind R) (sub_cont (rg_cont R) 0 s) :: skipn (Datatypes.S i) (s_rgs S)), M, a))).
(* [comment removed for export] *)
Fixpoint set_nth_rg (i : nat) (R : region) (l : list region) : list region :=
  match l, i with [], _ => [] | _ :: r, O => R :: r | x :: r, Datatypes.S i' => x :: set_nth_rg i' R r end.
Definition apost_extsub (i : nat) (b z : lin) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obind (nth_error (a_rgs a) i) (fun Re =>
  obool (a_on a && lwf (s_next S) b && lwf (s_next S) z && inside_lin (s_facts S) b z (rg_base Re) (rg_size Re) &&
         fact_implied (s_facts S) (FMod b 3 0))%bool
    (Some (S, M, AST (a_on a) (set_nth_rg i (ext_rg b z) (a_rgs a)) (a_fcts a) (a_own a) (a_dep a) (a_nl a) (a_live a) (a_pri a)))).
(* [comment removed for export] *)
Definition apost_exthull (i j1 j2 : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obind (nth_error (s_rgs S) j1) (fun R1 => obind (nth_error (s_rgs S) j2) (fun R2 =>
  apost_extsub i (rg_base R1) (lsub (ladd (rg_base R2) (rg_size R2)) (rg_base R1)) S M a)).
Definition apost_extdrop (i : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  if (a_on a && Nat.ltb i (List.length (a_rgs a)))%bool then Some (S, M, ext_drop a i) else None.
(* [comment removed for export] *)
End AcExt.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnq OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive anode2 : Type :=
| A1 (nk : anode)          (* [comment removed for export] *)
| NConvA                   (* [comment removed for export] *)
| NPop (c : Z)             (* [comment removed for export] *)
| NShB (c : Z)             (* [comment removed for export] *)
| NShG (c : Z)             (* [comment removed for export] *)
| NGive (c : Z) (ix : list nat)      (* [comment removed for export] *)
| NShrink (c : Z) (i : nat) (s : Z)  (* [comment removed for export] *)
| NPopG                    (* [comment removed for export] *)
| NGiveX (ix : list nat)            (* [comment removed for export] *)
| NShrinkX (i : nat) (s : Z)        (* [comment removed for export] *)
| NExtDrop (i : nat)                (* [comment removed for export] *)
| NExtSub (i : nat) (b z : lin)     (* [comment removed for export] *)
| NExtHull (i j1 j2 : nat)          (* [comment removed for export] *)
| NEnq.                    (* [comment removed for export] *)

Definition apost_alloc2 (LIMIT : Z) (nk : anode2) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  match nk with
  | A1 k => apost_alloc LIMIT k S M a
  | NConvA => apost_conva LIMIT S M a
  | NPop c => apost_npop LIMIT c S M a
  | NShB c => None                  (* [comment removed for export] *)
  | NShG c => None
  | NGive c ix => None
  | NShrink c i s => None
  | NPopG => apost_npopg LIMIT S M a
  | NGiveX ix => apost_givex ix S M a
  | NShrinkX i s => None            (* [comment removed for export] *)
  | NExtDrop i => apost_extdrop i S M a
  | NExtSub i b z => apost_extsub i b z S M a
  | NExtHull i j1 j2 => apost_exthull i j1 j2 S M a
  | NEnq => apost_nenq LIMIT S M a
  end.
(* [comment removed for export] *)

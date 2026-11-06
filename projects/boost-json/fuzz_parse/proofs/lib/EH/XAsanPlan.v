(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Export XAsanPlanCore.
Import ListNotations.
Open Scope Z_scope.

Module AP.
Include APC.
Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : XPropExec.FPState}.


Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.     (* [comment removed for export] *)
Variable LIMIT : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive snode : Type :=
| YMunmap      (* [comment removed for export] *)
| YBrk         (* [comment removed for export] *)
| YSetTid.     (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive xnode : Type :=
| XIMemset     (* [comment removed for export] *)
| XIMemcpy     (* [comment removed for export] *)
| XMemset      (* [comment removed for export] *)
| XMemcpy      (* [comment removed for export] *)
| XMemIsZero   (* [comment removed for export] *)
| XEnvScan     (* [comment removed for export] *)
| XPnScan      (* [comment removed for export] *)
| XLayout      (* [comment removed for export] *)
| XIStrncpy    (* [comment removed for export] *)
| XPopFree     (* [comment removed for export] *)
| XSniff.      (* [comment removed for export] *)

Inductive plan : Type :=
| PRun (stops : list Z) (k : plan)           (* [comment removed for export] *)
| PSplit (e : expr) (mid : Z) (k1 k2 : plan) (* [comment removed for export] *)
| PCase2 (e : expr) (mid : Z) (k1 k2 : plan) (* [comment removed for export] *)
| PCaseDisj (b1 b2 : expr) (k1 k2 : plan)  (* [comment removed for export] *)
| PShDisj (b1 n1 b2 n2 : expr) (k : plan)  (* [comment removed for export] *)
| PContra                                    (* [comment removed for export] *)
| PFact (K : kentry) (k : plan)              (* [comment removed for export] *)
| PJoin (b : expr) (off : Z) (n : nat) (k : plan)  (* [comment removed for export] *)
| PForget (ixs : list nat) (k : plan)        (* [comment removed for export] *)
| PDropRange (b : expr) (n : expr) (k : plan) (* [comment removed for export] *)
| PGcKeep (ws : list (expr * expr)) (k : plan) (* [comment removed for export] *)
| PBump (m : nat) (k : plan)                 (* [comment removed for export] *)
| PHavoc (rs : list nat) (k : plan)          (* [comment removed for export] *)
| PHavocBig (K : nat) (k : plan)             (* [comment removed for export] *)
| PFresh (r : nat) (logc : Z) (base : option expr) (k : plan)  (* [comment removed for export] *)
| PSys (y : snode) (k : plan)                (* [comment removed for export] *)
| PMmap (krefused kgranted : plan)           (* [comment removed for export] *)
| PMmapIn (kkept kok kdestroyed : plan)      (* [comment removed for export] *)
| PMprotect (krefused kgranted : plan)       (* [comment removed for export] *)
| PBrk2 (kblocked kgranted : plan)           (* [comment removed for export] *)
| PX (x : xnode) (args : list expr) (k : plan)   (* [comment removed for export] *)
| PExt (id : nat) (args : list expr) (k : plan)  (* [comment removed for export] *)
| PEmit (id : nat) (args : list expr) (k : plan) (* [comment removed for export] *)
| PExt2 (id : nat) (args : list expr) (k1 k2 : plan) (* [comment removed for export] *)
| PLoop (J : nat) (N : expr) (inv : acs) (body k : plan)  (* [comment removed for export] *)
| PNext                                      (* [comment removed for export] *)
| PHandoff (h : nat)                         (* [comment removed for export] *)
| PExit                                      (* [comment removed for export] *)
| PSpin                                      (* [comment removed for export] *)
| PFog (i : nat) (sz : Z) (k : plan)          (* [comment removed for export] *)
| PFogNew (i : nat) (sz : Z) (k : plan)       (* [comment removed for export] *)
| PGhost (b n : expr) (k : plan)              (* [comment removed for export] *)
| PUnvis (b n : expr) (k : plan)              (* [comment removed for export] *)
| PHavocBrk (lo hi : Z) (k : plan)            (* [comment removed for export] *)
| PIntro (lo hi : Z) (k : plan)               (* [comment removed for export] *)
| PDiamond (joinpc : Z) (rs : list nat) (k : plan)  (* [comment removed for export] *)
| PRename (m : list (nat * nat)) (k : plan)   (* [comment removed for export] *)
| PCompact (k : plan)                         (* [comment removed for export] *)
| PVia (j : nat) (js : acs) (lo : nat) (karms k : plan)  (* [comment removed for export] *)
| PMerge (j : nat)                            (* [comment removed for export] *)
| PAbstractCell (b : expr) (n : Z) (k : plan) (* [comment removed for export] *)
| PHavocWords (bs : list expr) (k : plan)    (* [comment removed for export] *)
| PRespell (r : nat) (e : expr) (k : plan)    (* [comment removed for export] *)
| PMmapInH (kkept kok kdestroyed : plan).     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : acs).

Section Check.
Variable XN : nat -> list expr -> acs -> option acs.                      (* [comment removed for export] *)
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).  (* [comment removed for export] *)
Variable XB : nat -> list expr -> acs -> option (acs * acs).              (* [comment removed for export] *)
Variable XON : xnode -> bool.                                               (* [comment removed for export] *)
Variable HS : nat -> option acs.   (* [comment removed for export] *)
Variable KC : nat.                 (* [comment removed for export] *)
Variable bfuel : nat.              (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End Check.

End WithSegs.
End FPX_1.

End AP.
(* [comment removed for export] *)

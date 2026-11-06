(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope uint63_scope.

Record fval : Set := FV { vtag : int; vw : w64 }.
Definition fv0 : fval := FV 0 w_zero.
Definition fv_of_w (w : w64) : fval := FV 0 w.

(* [comment removed for export] *)
Definition kind_lim : int := 1152921504606846976.          (* [comment removed for export] *)
Definition K_P : int := 0.
Definition K_N : int := 1.
Definition K_LO : int := 2.
Definition K_HI : int := 3.
Definition K_NLO : int := 4.
Definition K_B5 : int := 5.
Definition K_PG : int := 6.          (* [comment removed for export] *)
Definition K_SL3 : int := 7.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition vkind (t : int) : int :=
  if t <? 1152921504606846976 then 0 else if t <? 2305843009213693952 then 1
  else if t <? 3458764513820540928 then 2 else if t <? 4611686018427387904 then 3
  else if t <? 5764607523034234880 then 4 else if t <? 6917529027641081856 then 5
  else if t <? 8070450532247928832 then 6 else 7.
Definition vbase (t : int) : int := t - vkind t * kind_lim.
Definition ktag (k b : int) : int := k * kind_lim + b.
Definition is_plain (t : int) : bool := t <? kind_lim.
(* [comment removed for export] *)
Definition is_linear (t : int) : bool := t <? 2305843009213693952.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition neg_tag (t : int) : int := if t <? kind_lim then t + kind_lim else t - kind_lim.

(* [comment removed for export] *)
Inductive slot : Set :=
| SK (b : int)              (* [comment removed for export] *)
| SV (v : fval) (j : int)   (* [comment removed for export] *)
| SU.                       (* [comment removed for export] *)
Record slots : Set := SL { sl0 : slot; sl1 : slot; sl2 : slot; sl3 : slot;
                           sl4 : slot; sl5 : slot; sl6 : slot; sl7 : slot }.
Definition sget (j : int) (s : slots) : slot :=
  if j =? 0 then sl0 s else if j =? 1 then sl1 s else if j =? 2 then sl2 s else if j =? 3 then sl3 s
  else if j =? 4 then sl4 s else if j =? 5 then sl5 s else if j =? 6 then sl6 s else sl7 s.

(* [comment removed for export] *)
Inductive cell : Set := CV (v : fval) | CU | CB (s : slots).

(* [comment removed for export] *)
Inductive pkind : Set := PKZero | PKImage | PKUnk.

Record page : Type := PG { pg_wr : bool; pg_kind : pkind; pg_cells : itrie cell }.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive rkind : Set := RK_plain | RK_shadow (parent : int).

Record region : Type := RGK { rg_lo : int; rg_len : int; rg_align : int;
                              rg_dflt : option pkind;   (* [comment removed for export] *)
                              rg_pages : itrie page;
                              rg_clo : int; rg_chi : int;  (* [comment removed for export] *)
                              rg_kind : rkind }.
Notation RG lo len al dflt pages clo chi := (RGK lo len al dflt pages clo chi RK_plain).
(* [comment removed for export] *)
Definition shadow_K : int := 2147450880.
(* [comment removed for export] *)
Definition clo_dflt : int := 0.
Definition chi_dflt : int := 9223372036854775807.          (* [comment removed for export] *)

(* [comment removed for export] *)
Record fseg : Type := SG { sg_base : int; sg_size : int; sg_wr : bool; sg_hex : string }.
Definition fimage := list fseg.

Record fstate : Type := FS {
  f_pc   : int;
  f_regs : itrie fval;          (* [comment removed for export] *)
  f_mem  : itrie region;
  f_resv : option fval          (* [comment removed for export] *)
}.

Definition rget (s : fstate) (r : int) : fval :=
  if r =? 0 then fv0 else match iget r (f_regs s) with Some v => v | None => fv0 end.
Definition rset (s : fstate) (r : int) (v : fval) (npc : int) : fstate :=
  FS npc (if r =? 0 then f_regs s else iset r v (f_regs s)) (f_mem s) (f_resv s).
Definition set_pc (s : fstate) (npc : int) : fstate := FS npc (f_regs s) (f_mem s) (f_resv s).

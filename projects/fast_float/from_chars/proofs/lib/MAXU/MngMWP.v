(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition rgeo (HTOP : Z) (L : layout) (s : astate) : Prop :=
  forall r rg, region_of s r = Some rg -> rg_live rg = true ->
    PGSZ <= ly_reg L r /\ ly_reg L r + rg_len rg <= HTOP /\ ranges_disjoint (ly_reg L r, rg_len rg) (0x10000, 0x89000).

(* [comment removed for export] *)
Definition lext (L L' : layout) (s : astate) : Prop :=
  ly_ctx L' = ly_ctx L /\ ly_brk0 L' = ly_brk0 L /\ ly_sec L' = ly_sec L /\
  forall r, (r < length (st_regions s))%nat -> ly_reg L' r = ly_reg L r.

(* [comment removed for export] *)
Definition in_regs (L : layout) (s : astate) (x : Z) : Prop :=
  exists r rg, region_of s r = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\ ly_reg L r <= x < ly_reg L r + rg_len rg.

(* [comment removed for export] *)
Definition mframe (sp0 K : Z) (L : layout) (s : astate) (L' : layout) (s' : astate) (m m' : word -> option byte) : Prop :=
  forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) ->
    (sp0 - K <= x < sp0) \/ (in_footprint L' s' x /\ ~ in_user_block L s x) \/ in_regs L' s' x.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface R_sizeclass R_cache_defs R_prim_defs R_glue_defs R_thread R_depot_defs R_quar_defs R_qdorec R_qcbrec RT_state RT_rep RT_freestate RT_geo0 RT_drain_defs RT_drain_ldefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition dl_ok (p : dlp) : Prop :=
  fdfs_only (dl_PMc p) /\ mat_stable (dl_PMc p) /\ l_ACEIL (lay (dl_Σ0 p)) <= dl_lo p /\ dl_lo p + 0x4000 <= dl_usp p + -2208
  /\ dl_usp p <= 2 ^ 47 /\ geo_ok (dl_Σ0 p).

(* [comment removed for export] *)
Definition item_post (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) : config -> Prop :=
  fun cf => exists Σk' : rtsA, ASTA RTA Σk' (dl_PMc p) (dl_N p j b ents i rest Σk') cf
    /\ (rt_wfP Σk' ((b, skipn (S i) ents) :: rest) /\ dl_sig p Σk' /\ nth_error (r_st (pr Σk' 24)) ib = Some CkBatch).

Definition item_stmt (p : dlp) : Prop :=
  forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch),
  (i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
  cps bsegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition item_prim_stmt (p : dlp) : Prop :=
  forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (c : Z) (ic : nat) (n : Z),
  (i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
  1 <= c <= 31 -> nth_error (r_st (pr Σk c)) ic = Some (CkQuar n) ->
  nth i ents (0, 0) = (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16, n) ->
  cps bsegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition item_sec_stmt (p : dlp) : Prop :=
  forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (k : nat) (s : secst),
  (i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
  nth_error (sec Σk) k = Some s -> s_quar s = true -> nth i ents (0, 0) = (s_mb s + 6128, s_n s) ->
  cps bsegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition batch_stmt (p : dlp) : Prop :=
  forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (rest : list batch),
  rt_wfP Σk ((b, []) :: rest) -> dl_sig p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
  cps bsegs (ASTA RTA Σk (dl_PMc p) (dl_D p j b ents rest Σk))
    (fun cf => exists Σk' : rtsA, ASTA RTA Σk' (dl_PMc p) (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).

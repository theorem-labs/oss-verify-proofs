(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0hb X0j3
X0gp X0id X0hx X0hv X0fy X0fg X0e5 X0e8 X0ci X0co.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X17w X19m X17a X18y X18i X18g X16j X161 X14q X14t X133 X139.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X133 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X139.
Import ListNotations.
Open Scope Z_scope.

Definition dl_ok (p : dlp) : Prop :=
fdfs_only (dl_PMc p) /\ mat_stable (dl_PMc p) /\ l_ACEIL (lay (dl_Σ0 p)) <= dl_lo p /\ dl_lo p + 0x4000 <= dl_usp p + -2208
/\ dl_usp p <= 2 ^ 47 /\ geo_ok (dl_Σ0 p).

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
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Definition dl_ok (p : dlp) : Prop :=
fdfs_only (dl_PMc p) /\ mat_stable (dl_PMc p) /\ l_ACEIL (lay (dl_Σ0 p)) <= dl_lo p /\ dl_lo p + 0x4000 <= dl_usp p + -2208
/\ dl_usp p <= 2 ^ 47 /\ geo_ok (dl_Σ0 p).

Definition item_post (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) : config -> Prop :=
fun cf => exists Σk' : rtsA, ASTA RTA Σk' (dl_PMc p) (dl_N p j b ents i rest Σk') cf
/\ (rt_wfP Σk' ((b, skipn (S i) ents) :: rest) /\ dl_sig p Σk' /\ nth_error (r_st (pr Σk' 24)) ib = Some CkBatch).

Definition item_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps asegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition item_prim_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (c : Z) (ic : nat) (n : Z),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
1 <= c <= 31 -> nth_error (r_st (pr Σk c)) ic = Some (CkQuar n) ->
nth i ents (0, 0) = (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16, n) ->
cps asegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition item_sec_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (k : nat) (s : secst),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
nth_error (sec Σk) k = Some s -> s_quar s = true -> nth i ents (0, 0) = (s_mb s + 6128, s_n s) ->
cps asegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition batch_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (rest : list batch),
rt_wfP Σk ((b, []) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps asegs (ASTA RTA Σk (dl_PMc p) (dl_D p j b ents rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' (dl_PMc p) (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).

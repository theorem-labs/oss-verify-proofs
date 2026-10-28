(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_state RT_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Definition fixed_commit_node : Prop :=
  forall (Σ Σ' : rtsA) (PMc : Model -> Prop) (Pm K : machine_state -> Prop) (addr len : Z),
  fdfs_only PMc -> mat_stable PMc -> lay Σ' = lay Σ -> sec Σ' = sec Σ -> sec_nres Σ' = sec_nres Σ -> aw Σ' = aw Σ ->
  rt_eager Σ + len <= rt_eager Σ' -> rt_eager Σ' <= 2 ^ 38 -> layout_ok (lay Σ) -> A_bytes (aw Σ) <= CREDIT0 ->
  0 < len -> len mod 4096 = 0 -> addr mod 4096 = 0 -> l_SB (lay Σ) <= addr -> addr + len <= l_SB (lay Σ) + 2 ^ 37 ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 222) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
      /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 50 /\ areg ms 15 = Z_to_bv 64 0
      /\ K (nretA ms (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 len)]))) ->
  cps bsegs (ASTA RTA Σ PMc Pm) (ASTA RTA Σ' PMc K).

Definition munmap_node : Prop :=
  forall (Σ Σ' : rtsA) (PMc : Model -> Prop) (Pm K : machine_state -> Prop) (mb len : Z),
  fdfs_only PMc -> mat_stable PMc -> lay Σ' = lay Σ -> aw Σ' = aw Σ ->
  In (Z_to_bv 64 mb, Z_to_bv 64 len) (map secmap (rev (sec Σ))) ->
  Permutation (rt_maps Σ') (map_remove (rt_maps Σ) (Z_to_bv 64 mb)) ->
  rt_eager Σ <= rt_eager Σ' + len -> layout_ok (lay Σ) -> A_bytes (aw Σ) <= CREDIT0 -> rt_eager Σ <= 2 ^ 38 ->
  0 < len -> len mod 4096 = 0 -> 0 <= mb -> mb mod 4096 = 0 -> mb + len <= l_ACEIL (lay Σ) ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 215) /\ areg ms 10 = Z_to_bv 64 mb /\ areg ms 11 = Z_to_bv 64 len
      /\ K (nretA ms (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 mb, Z_to_bv 64 len)] [] []))) ->
  cps bsegs (ASTA RTA Σ PMc Pm) (ASTA RTA Σ' PMc K).

Definition madvise_node : Prop :=
  forall (Σ : rtsA) (PMc : Model -> Prop) (Pm K : machine_state -> Prop) (PB PE : Z),
  fdfs_only PMc -> mat_stable PMc -> layout_ok (lay Σ) ->
  PB mod 4096 = 0 -> PE mod 4096 = 0 -> PB < PE ->
  (K_LOW_SHADOW_lo <= PB /\ PE <= K_LOW_SHADOW_hi \/ K_HIGH_SHADOW_lo <= PB /\ PE <= K_HIGH_SHADOW_hi) ->
  (forall p : word, PB <= bv_unsigned p -> bv_unsigned p + 4096 <= PE -> page_allowedb (rtA_allow Σ) p = true) ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 233) /\ areg ms 10 = Z_to_bv 64 PB /\ areg ms 11 = Z_to_bv 64 (PE - PB)
      /\ areg ms 12 = Z_to_bv 64 4
      /\ K (nretA ms (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 PB, Z_to_bv 64 (PE - PB))]))) ->
  cps bsegs (ASTA RTA Σ PMc Pm) (ASTA RTA Σ PMc K).

Definition fixed_commit_pab_node : Prop :=
  forall (Σ Σ' : rtsA) (PMc : Model -> Prop) (Pm K : machine_state -> Prop) (addr len : Z),
  fdfs_only PMc -> mat_stable PMc -> lay Σ' = lay Σ -> sec Σ' = sec Σ -> aw Σ' = aw Σ ->
  rt_eager Σ + len <= rt_eager Σ' -> rt_eager Σ' <= 2 ^ 38 -> layout_ok (lay Σ) -> A_bytes (aw Σ) <= CREDIT0 ->
  0 < len -> len mod 4096 = 0 -> addr mod 4096 = 0 -> l_PAB (lay Σ) <= addr -> addr + len <= l_PAB (lay Σ) + 0x800000 ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 222) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
      /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 50 /\ areg ms 15 = Z_to_bv 64 0
      /\ K (nretA ms (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 len)]))) ->
  cps bsegs (ASTA RTA Σ PMc Pm) (ASTA RTA Σ' PMc K).

Definition sgrant_ok (Σ : rtsA) (P len : Z) : Prop :=
  grant_ok (lay Σ) P len /\ Forall (fun e => apart P len (bv_unsigned (fst e)) (bv_unsigned (snd e))) (rt_maps Σ).

Definition grant_node : Prop :=
  forall (Σ : rtsA) (Σ' : Z -> rtsA) (PMc : Model -> Prop) (Pm : machine_state -> Prop) (K : Z -> machine_state -> Prop) (len : Z),
  fdfs_only PMc -> mat_stable PMc -> rt_wf Σ ->
  0 < len -> len mod 4096 = 0 -> len <= 2 ^ 32 -> rt_eager Σ + len <= 2 ^ 38 ->
  (forall P, lay (Σ' P) = lay Σ /\ aw (Σ' P) = aw Σ /\ Permutation (rt_maps (Σ' P)) ((Z_to_bv 64 P, Z_to_bv 64 len) :: rt_maps Σ)
     /\ rt_eager Σ + len <= rt_eager (Σ' P) /\ rt_eager (Σ' P) <= 2 ^ 38) ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 222) /\ areg ms 11 = Z_to_bv 64 len
      /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 34 /\ areg ms 15 = Z_to_bv 64 0
      /\ forall P, sgrant_ok Σ P len -> K P (nretA ms (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 len)]))) ->
  cps bsegs (ASTA RTA Σ PMc Pm) (fun c => exists P, sgrant_ok Σ P len /\ ASTA RTA (Σ' P) PMc (K P) c).

End GWIN.

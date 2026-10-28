(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Pj_rtkA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Snc.
Variable RT : rt_sig.

Definition sncW_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p q n : Z) (bp bq : list Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 n ->
  0 < p <= 2^47 -> 0 < q <= 2^47 -> 0 < n < 2^26 ->
  bytes_at asegs m p (map (Z_to_bv 8) bp) -> bytes_at asegs m q (map (Z_to_bv 8) bq) ->
  Forall (fun c => 0 <= c < 256) bp -> Forall (fun c => 0 <= c < 256) bq ->
  n <= Z.of_nat (length bp) -> n <= Z.of_nat (length bq) ->
  checked_src RT Σ m sp lo p n -> checked_src RT Σ m sp lo q n ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strncasecmp m)))
    (fun c => exists r : word, icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r lo 0 0 m (fun _ => True) c).

Definition snc0_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a2 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strncasecmp m)))
    (fun c => exists r : word, icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r lo 0 0 m (fun _ => True) c).

Lemma checked_src_shrink : forall Σ m sp lo s n k, checked_src RT Σ m sp lo s n -> 0 < k <= n -> checked_src RT Σ m sp lo s k.
Proof.
  intros Σ m sp lo s n k [H SEP] HK. split; [| lia]. intros _. destruct (H ltac:(lia)) as [AC RC].
  split; [apply (acc_sub asegs m s n); [exact AC| lia| lia]|].
  destruct RC as [(p & c & Hin & H1 & H2)|[(f & c & Hin & H1 & H2)|[(H1 & H2)|(H1 & H2)]]].
  - left. exists p, c. split; [exact Hin| lia].
  - right; left. exists f, c. split; [exact Hin| lia].
  - right; right; left. lia.
  - right; right; right. lia.
Qed.

Lemma sncW_of_icontract_20 : strncasecmp_icontract RT ->
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p q n : Z) (bp bq : list Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 n ->
  0 < p <= 2^47 -> 0 < q <= 2^47 -> 0 < n < 2^20 ->
  bytes_at asegs m p (map (Z_to_bv 8) bp) -> bytes_at asegs m q (map (Z_to_bv 8) bq) ->
  Forall (fun c => 0 <= c < 256) bp -> Forall (fun c => 0 <= c < 256) bq ->
  n <= Z.of_nat (length bp) -> n <= Z.of_nat (length bq) ->
  checked_src RT Σ m sp lo p n -> checked_src RT Σ m sp lo q n ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strncasecmp m)))
    (fun c => exists r : word, icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r lo 0 0 m (fun _ => True) c).
Proof.
  intros SC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q n bp bq lo
    FDO MST E0 E1 E2 HP HQ HN BP BQ FP FQ LP LQ CP CQ HA MI COK.
  set (k := Z.min n (Z.of_nat (scase_idx bp bq (Z.to_nat n)) + 1)).
  assert (K : 0 < k <= n) by (subst k; lia).
  eapply cps_conseq; [eapply (SC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q n bp bq lo
      FDO MST E0 E1 E2 HP HQ ltac:(lia) BP BQ FP FQ); [subst k; lia| subst k; lia| exact (checked_src_shrink _ _ _ _ _ _ _ CP K)| exact (checked_src_shrink _ _ _ _ _ _ _ CQ K)
      | exact HA| exact MI| exact COK]| intros c Hc; exact Hc|].
  intros c Hc. first [destruct Hc as (r & _ & H); exists r; exact H | eexists; exact Hc].
Qed.

End Snc.

Section SncKit.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Lemma aevt_sncW : sncW_stmt RT -> forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p q n : Z) (bp bq : list Z) (lo : Z),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 n ->
  0 < p <= 2^47 -> 0 < q <= 2^47 -> 0 < n < 2^26 ->
  bytes_at asegs m p (map (Z_to_bv 8) bp) -> bytes_at asegs m q (map (Z_to_bv 8) bq) ->
  Forall (fun c => 0 <= c < 256) bp -> Forall (fun c => 0 <= c < 256) bq ->
  n <= Z.of_nat (length bp) -> n <= Z.of_nat (length bq) ->
  checked_src RT Σ m sp lo p n -> checked_src RT Σ m sp lo q n ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  (forall (r : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_strncasecmp) fc None m (seg_rom asegs)).
Proof using FDO MST.
  intros SC. intros until lo. intros E0 E1 E2 HP HQ HN BP BQ FP FQ LP LQ CP CQ ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (SC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m p q n bp bq lo FDO MST E0 E1 E2 HP HQ HN BP BQ FP FQ LP LQ CP CQ ART0 MI0 COK).
  - intros c (r & HQ'). unfold icpt_postF in HQ'. eexists Σ, _. split; [exact HQ'|].
    intros ms' (m' & RS & RA & PR & _).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK r q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR).
Qed.

Lemma aevt_snc0 : snc0_stmt RT -> forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  a2 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  (forall (r : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_strncasecmp) fc None m (seg_rom asegs)).
Proof using FDO MST.
  intros SC. intros until lo. intros E2 ART0 MI0 COK HK.
  eapply aevt_icall.
  - exact (SC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST E2 ART0 MI0 COK).
  - intros c (r & HQ'). unfold icpt_postF in HQ'. eexists Σ, _. split; [exact HQ'|].
    intros ms' (m' & RS & RA & PR & _).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK r q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR).
Qed.

Lemma Forall_firstn_skipn : forall (P : Z -> Prop) (l : list Z) (i n : nat), Forall P l -> Forall P (firstn n (skipn i l)).
Proof.
  intros P l i n H. rewrite <- (firstn_skipn i l) in H. apply Forall_app in H. destruct H as [_ H].
  rewrite <- (firstn_skipn n (skipn i l)) in H. apply Forall_app in H. destruct H as [H _]. exact H.
Qed.
End SncKit.

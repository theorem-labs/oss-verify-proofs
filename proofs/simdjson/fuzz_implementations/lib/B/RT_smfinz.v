(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts RT_release R_fs_ok R_fs4 RT_stackmalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.

Lemma sm_finish_x : forall (X : Z -> mem -> Prop) (Σ : rtsA) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (k : nat) (j lo : Z) (fc : bv 32)
    (Pm : machine_state -> Prop) c1,
  ART_A Σ m -> (k = 5 \/ k = 0 \/ k = 4 \/ k = 1 \/ k = 3 \/ k = 2)%nat -> 0 <= j < NF (Z.of_nat k) ->
  nth (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) (fss_flags (fs_of Σ k)) 1 = 0 ->
  1 <= credit Σ -> fs_room k (frames Σ) ->
  rtA_sp0 Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  AST SEGTOP_A (rtA_allow Σ) Pm (fun mo => ARTM RTA Σ mo /\ PMc mo) c1 ->
  (forall ms, Pm ms -> exists m',
     ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       (Z_to_bv 64 (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)))) m' ms
     /\ munch (sm_W (Z.of_nat k) (l_FSB (lay Σ)) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) (bv_unsigned sp)) m m'
     /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
     /\ fs_hint (l_FSB (lay Σ)) (Z.of_nat k) m' (fss_hint (fs_of Σ k) + j + 1) /\ fs_const (l_FSB (lay Σ)) m'
     /\ fs_flags (l_FSB (lay Σ)) (Z.of_nat k) m'
          (upd (fss_flags (fs_of Σ k)) (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) 1)
     /\ wr_at bsegs m' (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) (fsz (Z.of_nat k))
     /\ rw_cells bsegs m' (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) + fsz (Z.of_nat k) - 8)
          [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + (fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)))]
     /\ wr_at bsegs m' (shad (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))))
          (fsz (Z.of_nat k) / 8)
     /\ fs_free_frames (l_FSB (lay Σ)) (Z.of_nat k) m'
          (upd (fss_flags (fs_of Σ k)) (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) 1)
     /\ X (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) m') ->
  exists (Σ' : rts RTA) (f : Z),
       ASTA RTA Σ' PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) (bv_unsigned sp) m m'
         /\ wr_at bsegs m' f (fs_size k - 8) /\ wr_at bsegs m' (shad f) (fs_size k / 8) /\ X f m') c1
       /\ rt_frames RTA Σ' = (f, k) :: rt_frames RTA Σ /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
       /\ rt_credit RTA Σ' = rt_credit RTA Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP.
Proof.
  intros X Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m k j lo fc Pm c1 HA Hk Hj Hfree Hcr Hlen LOW LOR SPT HAST HPm.
  set (FSB := l_FSB (lay Σ)) in *. set (pos := (fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) in *.
  set (f := frame_addr FSB (Z.of_nat k) pos) in *.
  set (g' := mkFs (fss_hint (fs_of Σ k) + j + 1) (upd (fss_flags (fs_of Σ k)) (Z.to_nat pos) 1)).
  set (usp := bv_unsigned sp) in *.
  assert (Hlo : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; unfold rtA_sp0 in LOW; lia).
  assert (Husp : lo + 208 <= usp) by (unfold RT_STACK in LOR; lia).
  assert (Husp2 : usp <= USTACK_TOP) by lia.
  exists (fs_push Σ k g' f), f.
  pose proof (push_f Σ m k j HA Hk) as (F1 & F2 & F3).
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity | exact (conj F1 (conj F2 F3))]]]]].
  unfold ASTA. change (rt_allow RTA (fs_push Σ k g' f)) with (rtA_allow Σ).
  eapply AST_conseq; [exact HAST| |intros mo Hmo; exact Hmo].
  intros ms HP. destruct (HPm ms HP) as (m' & RS & MU & WM & MI & ST' & P1 & P2 & P3 & P4 & P5 & P6 & P7 & PX).
  destruct (push_post Σ m m' k j usp lo HA Hk Hj Hfree Hcr Hlen Hlo Husp Husp2 MU WM P1 P2 P3 P4 P5 P6 P7 eq_refl) as (ART' & PRES & WR1 & WR2).
  exists m'. split; [exact RS|]. split; [split; [exact ART' | split; [exact MI | split; [exact WM | exact ST']]]|].
  split; [exact (rt_pres_vis _ _ _ _ _ _ PRES)|]. split; [exact WR1 |]. split; [exact WR2 | exact PX].
Qed.

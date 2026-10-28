(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_freeI RT_freeJ RT_freeK RT_freeL RT_freeM RT_freeN RT_freeS RT_freeT RT_freeU RT_freeV RT_freeW RT_freeX RT_freeY RT_refill RT_sys_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Lemma artm_maps : forall Σ Σ' mo, lay Σ' = lay Σ -> rt_maps Σ' = rt_maps Σ -> rt_eager Σ' = rt_eager Σ -> ARTM_A Σ mo -> ARTM_A Σ' mo.
Proof.
  intros Σ Σ' mo E1 E2 E3 (A1 & A2 & A3 & A4 & AS).
  unfold ARTM_A, artm_sys, confined0 in *. rewrite E1, E2, E3. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  exact AS.
Qed.

Theorem rta_free_prim : drain_stmt -> fixed_commit_node ->
  forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n,
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n) -> tp = Z_to_bv 64 0x6be3e8 ->
  ART_A Σ m -> mem_inv bsegs m -> call_ok RTA Σ m sp lo -> unwind_ok ra s0 sp ->
  1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  cps bsegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_postF RTA fc Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
  intros DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n
    FDO MST -> -> ART0 MI0 CALL UWOK Hc Hn.
  intros TT cf Hc0 Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
  assert (HLO2 : lo + 0x10000 <= bv_unsigned sp) by (clear - LOR; unfold RT_STACK in *; lia).
  assert (Husp : bv_unsigned sp + 16 <= USTACK_TOP) by exact SPT.
  assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m) ms ->
                       evt bsegs (segA_post Σ c i n ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
    by (intros ms <-; exact (segA_evt Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                               ART0 MI0 CALL UWOK Hc Hn)).
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
  intros c1 Hc1.
  apply AST_exI in Hc1 as [tr Hc1]. apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1].
  apply AST_exI in Hc1 as [y3 Hc1]. apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1].
  apply AST_exI in Hc1 as [y7 Hc1]. apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [m4 Hc1].
  pose proof Hc1 as (_ & (_ & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4) & _ & _).
  destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
  pose proof (free_p_wf Σ m c i n _ ART0 Hc Hn Dok Dinv) as HW1.
  pose proof (pend_e_p _ c i n (pend_free_p Σ m c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)) ART0 Hc Hn)) as HP.
  assert (Hc1' : AST SEGTOP_A (rtA_allow (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))))
                   (eq (enq_entry_st (bv_unsigned sp) (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n gp y0 y1 y2 y3 y4 y5
                          s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4))
                   (fun mo => ARTM_A (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) mo /\ PMc mo) c1).
  { eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E |].
    intros mo (HM & HP'). split; [|exact HP']. apply (artm_eq Σ); [reflexivity | reflexivity | apply rt_eager_fp | exact HM]. }
  exact (enq_stage Σ (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) PMc
           ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m m4 lo
           (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n (p_ubeg (l_SB (lay Σ)) c i n) TT
           DRAIN FC FDO MST HW1 HP eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk c1 Hc1').
Qed.

Lemma map_upd_same : forall {X Y} (f : X -> Y) (l : list X) k x, (forall y, nth_error l k = Some y -> f x = f y) -> map f (upd l k x) = map f l.
Proof.
  intros X Y f l. induction l as [|y l IH]; intros k x H; [destruct k; reflexivity|].
  destruct k as [|k]; cbn [upd map].
  - rewrite (H y eq_refl). reflexivity.
  - rewrite (IH k x H). reflexivity.
Qed.

Lemma rt_maps_fs : forall Σ k s D', nth_error (sec Σ) k = Some s -> rt_maps (free_s Σ k s D') = rt_maps Σ.
Proof.
  intros Σ k s D' Hk. unfold rt_maps, free_s. cbn [sec lay]. rewrite !map_rev.
  rewrite (map_upd_same secmap (sec Σ) k (mkSec (s_mb s) (s_n s) true)); [reflexivity|].
  intros y Hy. rewrite Hk in Hy. injection Hy as <-. reflexivity.
Qed.

Lemma rt_eager_fs : forall Σ k s D', nth_error (sec Σ) k = Some s -> rt_eager (free_s Σ k s D') = rt_eager Σ.
Proof.
  intros Σ k s D' Hk. unfold rt_eager, free_s. cbn [pr sec sec_nres]. rewrite secsum_upd; [reflexivity|].
  intros y Hy. rewrite Hk in Hy. injection Hy as <-. reflexivity.
Qed.

End GWIN.

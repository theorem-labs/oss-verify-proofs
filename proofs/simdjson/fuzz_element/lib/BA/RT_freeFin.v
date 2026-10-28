(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_freeI RT_freeJ RT_freeK RT_freeL RT_freeM RT_freeN RT_freeS RT_freeT RT_freeU RT_freeV RT_freeW RT_freeX RT_freeY RT_freeZ RT_freeSA RT_freeSA2 RT_freeSA3 RT_refill RT_sys_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Theorem rta_free_sec : drain_stmt -> fixed_commit_node -> free_pass_stmt ->
  forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (k : nat) (s : secst),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (s_ubeg s) -> tp = Z_to_bv 64 0x6a7e68 ->
  ART_A Σ m -> mem_inv asegs m -> call_ok RTA Σ m sp lo -> unwind_ok ra s0 sp ->
  nth_error (sec Σ) k = Some s -> s_quar s = false ->
  cps asegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_postF RTA fc Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (s_ubeg s) lo m).
Proof.
  intros DRAIN FC FPASS Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k s
    FDO MST -> -> ART0 MI0 CALL UWOK Hk Hq.
  destruct (Z_lt_le_dec 0x10000000 (s_n s)) as [Hbig|Hsn];
    [exact (FPASS Σ PMc ra sp gp _ t0 t1 t2 s0 s1 _ a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k s
              FDO MST eq_refl eq_refl ART0 MI0 CALL UWOK Hk Hq Hbig)|].
  intros TT cf Hc0 Hk'.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
  assert (HLO2 : lo + 0x10000 <= bv_unsigned sp) by (clear - LOR; unfold RT_STACK in *; lia).
  assert (Husp : bv_unsigned sp + 16 <= USTACK_TOP) by exact SPT.
  assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 (Z_to_bv 64 (s_ubeg s)) a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m) ms ->
                       evt asegs (segA_post_s Σ k s ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
    by (intros ms <-; exact (segA_evt_s Σ k s ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                               ART0 MI0 CALL UWOK Hk Hq Hsn)).
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
  intros c1 Hc1.
  apply AST_exI in Hc1 as [tr Hc1]. apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1].
  apply AST_exI in Hc1 as [y3 Hc1]. apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1].
  apply AST_exI in Hc1 as [y7 Hc1]. apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [m4 Hc1].
  pose proof Hc1 as (_ & (_ & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4) & _ & _).
  destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
  pose proof (free_s_wf Σ m k s _ ART0 Hk Hq Hsn Dok Dinv) as HW1.
  pose proof (pend_e_s Σ m k s (fst (depot_put (dep Σ) tr)) ART0 Hk Hq) as HP.
  assert (Hc1' : AST SEGTOP_A (rtA_allow (free_s Σ k s (fst (depot_put (dep Σ) tr))))
                   (eq (enq_entry_st (bv_unsigned sp) (l_T (lay Σ)) (s_mb s + 6128) (s_n s) gp y0 y1 y2 y3 y4 y5
                          s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4))
                   (fun mo => ARTM_A (free_s Σ k s (fst (depot_put (dep Σ) tr))) mo /\ PMc mo) c1).
  { eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E |].
    intros mo (HM & HP'). split; [|exact HP']. apply (artm_maps Σ); [reflexivity | apply (rt_maps_fs Σ k s _ Hk) | apply (rt_eager_fs Σ k s _ Hk) | exact HM]. }
  exact (enq_stage Σ (free_s Σ k s (fst (depot_put (dep Σ) tr))) PMc
           ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m m4 lo
           (s_mb s + 6128) (s_n s) (s_ubeg s) TT
           DRAIN FC FDO MST HW1 HP eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk' c1 Hc1').
Qed.

Theorem rta_free : drain_stmt -> fixed_commit_node -> free_pass_stmt -> free_contract RTA.
Proof.
  intros DRAIN FC FPASS Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
    FDO MST Hin Ea0 Etp HA MI CALL UWOK.
  cbn [rt_live RTA] in Hin. unfold rtA_live in Hin.
  destruct (In_vis_live (ann Σ) (live Σ) p n Hin) as (n' & Hin' & _). clear Hin. rename n into n_client. rename n' into n. rename Hin' into Hin.
  pose proof (ART_wf Σ m HA) as (_ & _ & (_ & _ & V3 & _) & _).
  destruct (V3 p n Hin) as [(c & i & Hc & Hn & ->)|(s & Hs & Hq & Hsn & ->)].
  - exact (rta_free_prim DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             c i n FDO MST Ea0 Etp HA MI CALL UWOK Hc Hn).
  - destruct (In_nth_error _ _ Hs) as (k & Hk).
    exact (rta_free_sec DRAIN FC FPASS Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             k s FDO MST Ea0 Etp HA MI CALL UWOK Hk Hq).
Qed.

End GWIN.

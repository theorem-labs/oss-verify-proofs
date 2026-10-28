(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_freeI RT_freeJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Lemma rt_eager_ext : forall Σ Σ', (forall k, r_muser (pr Σ' k) = r_muser (pr Σ k) /\ r_mfa (pr Σ' k) = r_mfa (pr Σ k)) ->
  sec Σ' = sec Σ -> sec_nres Σ' = sec_nres Σ -> rt_eager Σ' = rt_eager Σ.
Proof.
  intros Σ Σ' H E1 E2. unfold rt_eager. rewrite E1, E2. f_equal. f_equal. apply sum_cls_ext. intros k _.
  destruct (H (Z.of_nat k)) as (X1 & X2). rewrite X1, X2. reflexivity.
Qed.

Lemma rt_eager_new : forall Σ c i n p D' cal jB M k, rt_eager (enq_new (free_p Σ c i n p D') cal jB M k) = rt_eager Σ.
Proof.
  intros Σ c i n p D' cal jB M k. apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
  cbn [enq_new set_ql pop24 free_p pr].
  destruct (Z.eqb_spec k' 24) as [->|_]; [destruct (Z.eqb_spec 24 c) as [<-|_] | destruct (Z.eqb_spec k' c) as [->|_]];
    unfold upd_reg; cbn [r_muser r_mfa]; split; reflexivity.
Qed.

Theorem rta_free_new2 : drain_stmt -> forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (cal : list Z) (jB j0 : nat) (st0 : ckst),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n) -> tp = Z_to_bv 64 0x6be3e8 ->
  ART_A Σ m -> mem_inv bsegs m -> call_ok RTA Σ m sp lo -> unwind_ok ra s0 sp ->
  1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  ca Σ 24 = cal ++ [Z.of_nat jB] -> nth_error (r_st (pr Σ 24)) j0 = Some st0 ->
  (j0 = jB /\ st0 = CkIdle /\ ql Σ = [])
  \/ (st0 = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)] /\ length ents0 = 1021%nat) ->
  cps bsegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_postF RTA fc Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
  intros DRAIN Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n cal jB j0 st0
    FDO MST -> -> ART0 MI0 CALL UWOK Hc Hn HCA Hj0 Hvar.
  intros TT cf Hc0 Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
  assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
  assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
  assert (Husp : usp + 16 <= USTACK_TOP) by exact SPT.
  assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m) ms ->
    evt bsegs (fun ms => exists tr : list Z,
      enq_post (enq_new (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) cal jB
                        (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n)
               (live_remove (p_abeg (l_SB (lay Σ)) c i + rz_size n) (live Σ)) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms) ms).
  { intros ms <-.
    eapply evt_cut; [exact (segA_evt Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                             ART0 MI0 CALL UWOK Hc Hn)|].
    intros ms P. destruct P as (tr & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m4 & -> & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4).
    destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
    eapply evt_mono; [apply (new_enq Σ m c i n tr cal jB j0 st0 usp ART0 Hc Hn HCA Hj0 Hvar Hsp Dok Dinv
                               ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
                               eq_refl ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4)|].
    intros ms P. exists tr. exact P. }
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
  intros c1 Hc1. apply AST_exI in Hc1 as [tr Hc1].
  apply (fin_from_enq DRAIN Σ (enq_new (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) cal jB
                                       (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n)
           PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo (p_ubeg (l_SB (lay Σ)) c i n) TT c1 FDO MST
           eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp); [|exact Hk].
  eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP). split; [|exact HP].
  apply (artm_eq Σ); [reflexivity | reflexivity | apply rt_eager_new | exact HM].
Qed.

End GWIN.

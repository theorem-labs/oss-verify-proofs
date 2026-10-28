(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_quar_defs R_deallocate R_qput R_qenqueue R_asan_free R_prim_kit R_depot_unwind RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malpre RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freeC RT_freeD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma artm_eq : forall Σ Σ' mo, lay Σ' = lay Σ -> sec Σ' = sec Σ -> rt_eager Σ' = rt_eager Σ -> ARTM_A Σ mo -> ARTM_A Σ' mo.
Proof.
  intros Σ Σ' mo E1 E2 E3 (A1 & A2 & A3 & A4 & AS).
  unfold ARTM_A, artm_sys, confined0, rt_maps in *. rewrite E1, E2, E3. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  exact AS.
Qed.

Lemma rt_eager_fp : forall Σ c i n p D' l, 1 <= c <= 31 -> rt_eager (set_ql (free_p Σ c i n p D') l) = rt_eager Σ.
Proof.
  intros Σ c i n p D' l Hc. unfold rt_eager, set_ql, free_p. cbn [pr sec sec_nres]. f_equal. f_equal. apply sum_cls_ext. intros k _.
  destruct (Z.eqb_spec (Z.of_nat k) c) as [Ek|Ek]; [rewrite Ek; unfold upd_reg; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma fe_dep : forall Σ m tr, ART_A Σ m -> (In tr T_MAIN /\ (1 <= length tr <= TR_MAX)%nat) ->
  depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)) /\ dep_inv (fst (depot_put (dep Σ) tr)).
Proof.
  intros Σ m tr HA Htr. pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
  assert (TRM : In tr T_MAIN /\ (length tr <= TR_MAX)%nat) by (destruct Htr as (H1 & H2); split; [exact H1 | lia]).
  destruct TRM as (TRM & TRL).
  split; [apply (qc_depot_ok_put_ok _ _ _ _ _ DOK DN); lia | exact (dep_inv_put _ _ DINV TRM ltac:(lia))].
Qed.

(* [comment removed for export] *)
Theorem rta_free_app : forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (pre : list (Z * list (Z * Z))) j0 (ents : list (Z * Z)),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n) -> tp = Z_to_bv 64 0xba93f0 ->
  ART_A Σ m -> mem_inv ctasegs m -> call_ok RTA Σ m sp lo -> unwind_ch m ra s0 sp ->
  1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents)] -> nth_error (r_st (pr Σ 24)) j0 = Some CkBatch ->
  (length ents < 1021)%nat -> RT_state.qbytes (ql Σ) + n <= 0x100000 ->
  cps ctasegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post RTA Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n pre j0 ents
    FDO MST -> -> ART0 MI0 CALL UWOK Hc Hn HQL Hj0 HL HBY.
  intros TT cf Hc0 Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
  assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
  assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
  assert (Husp : usp + 16 <= USTACK_TOP) by exact SPT.
  assert (W1 : evt ctasegs
    (fun ms => exists (tr : list Z) (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       ms = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom ctasegs)
       /\ ART_A (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
                        (pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])])) m'
       /\ mem_inv ctasegs m' /\ wmono ctasegs m m' /\ stk ctasegs m' lo usp
       /\ rt_pres (live_remove (p_ubeg (l_SB (lay Σ)) c i n) (live Σ)) (frames Σ) usp m m')
    (entry_st ra sp gp (Z_to_bv 64 0xba93f0) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)).
  { eapply evt_cut; [exact (segA_evt Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                             ART0 MI0 CALL UWOK Hc Hn)|].
    intros ms P. destruct P as (tr & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m4 & -> & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4).
    destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
    eapply evt_mono; [apply (app_run Σ c i n (fst (depot_put (dep Σ) tr)) pre j0 ents usp (ART_wf Σ m ART0) Hc Hn HQL Hj0 Hsp
                               ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
                               eq_refl ART4 Dok MI4 ST4 HLO HLO2 Husp ICF FR4 HL HBY)|].
    intros ms P. destruct P as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m' & -> & ART' & MI' & WM' & ST' & MWa).
    exists tr, z3, z0, z1, z2, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m'. split; [reflexivity|].
    split; [exact (c_ART _ _ (app_wf Σ m c i n _ pre j0 ents ART0 Hc Hn Dok Dinv HQL HL HBY) ART')|].
    split; [exact MI'|]. split; [exact (wmono_trans ctasegs _ _ _ WM4 WM')|]. split; [exact ST'|].
    intros a Ha. rewrite (MWa a).
    - exact (RP4 a Ha).
    - pose proof (geo_of_ART Σ m ART0) as HG.
      assert (HO : outside (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 j0) usp) (bv_unsigned a)).
      { apply (kv_client Σ _ [(24, j0); (24, j0)] [] [] usp HG
                 (se_img Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_grant Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
                 (se_slot Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_shad_app Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
                 (se_secmap Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_stack Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
                 ltac:(apply Forall_forall; intros; exact I) (live_remove (p_ubeg (l_SB (lay Σ)) c i n) (live Σ))); [|exact Ha].
        intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
        pose proof (ART_wf Σ m ART0) as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
        destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
        + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
          intros [E|[E|[]]]; injection E as <- <-; rewrite Hj0 in Hn'; discriminate.
        + right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
          split; [reflexivity | intros []]. }
      revert HO. apply sub_fp_covered. unfold W_E. cbn [all_covered covered]. clear - Hsp.
      split; [left; split; lia|]. split; [right; right; right; left; split; lia|]. split; [right; right; right; right; right; left; split; lia | exact I]. }
  lazymatch type of W1 with evt ctasegs _ ?X => assert (W1' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes ctasegs _ _ _ cf (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc0).
  intros c1 Hc1. apply Hk. apply AST_exI in Hc1 as [tr Hc1]. apply AST_exI in Hc1 as [v Hc1].
  exists (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
                 (pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])])), v.
  split; [|split; [reflexivity | split; [reflexivity | split; reflexivity]]].
  unfold ASTA. eapply AST_conseq; [exact Hc1| |].
  - intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & ART' & MI' & WM' & ST' & RP').
    exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
    split; [split; [exact ART' | split; [exact MI' | exact ST']]|]. exact RP'.
  - intros mo (HM & HP). split; [|exact HP].
    cbn [ARTM RTA]. apply (artm_eq Σ); [reflexivity | reflexivity | apply rt_eager_fp; exact Hc | exact HM].
Qed.

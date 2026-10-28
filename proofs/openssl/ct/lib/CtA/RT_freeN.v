(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F R_qenqueue_M R_qenqueue_MF R_asan_free R_prim_kit R_refill RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_freeI RT_freeJ RT_freeK RT_freeL RT_freeM RT_refillstmt RT_refillst RT_refillwf RT_rfkit RT_refillrun RT_count RT_refill RT_sys_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mf_post (Σ : rtsA) (c : Z) (i : nat) (n : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (tr : list Z) (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (jf : list byte),
    ms = refill_entry_st (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (bv_unsigned sp + -2208 + -64)) gp t0' t1' t2'
           (Z_to_bv 64 (pc_addr (l_T (lay Σ)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ)))) a4' a5' a6' a7'
           (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 (qcacheT (l_T (lay Σ)))) (Z_to_bv 64 (bv_unsigned sp + -2128))
           (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc (l_T (lay Σ)) 24 m5
    /\ ARTc (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) m5
    /\ (In tr T_MAIN /\ (1 <= length tr <= TR_MAX)%nat)
    /\ mem_inv ctasegs m5 /\ wmono ctasegs m m5 /\ stk ctasegs m5 lo (bv_unsigned sp + -2208 + -64)
    /\ rt_pres (live_remove (p_abeg (l_SB (lay Σ)) c i + rz_size n) (live Σ)) (frames Σ) (bv_unsigned sp) m m5
    /\ icpt_frame m5 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
    /\ qput_frame m5 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x1c424c)
         (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16)) (Z_to_bv 64 0x1c41dc) (Z_to_bv 64 1)
         (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6
    /\ rw_cells ctasegs m5 (bv_unsigned sp + -2208 + -64)
         [CB 8 jf; C8 (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)); C8 (Z_to_bv 64 (l_T (lay Σ) + 208));
          C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (l_T (lay Σ) + 80)); C8 (Z_to_bv 64 QUAR);
          C8 (Z_to_bv 64 0x1a038c)].

(* [comment removed for export] *)
Lemma mf_front : forall (Σ : rtsA) (c : Z) (i : nat) (n : Z)
    (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) (j0 : nat),
  ART_A Σ m -> mem_inv ctasegs m -> call_ok RTA Σ m sp lo -> unwind_ch m ra s0 sp ->
  1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) -> ca Σ 24 = [] ->
  (ql Σ = [] \/ exists pre ents0, nth_error (r_st (pr Σ 24)) j0 = Some CkBatch /\ ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)]
                                  /\ length ents0 = 1021%nat) ->
  evt ctasegs (mf_post Σ c i n ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (entry_st ra sp gp (Z_to_bv 64 0xba93f0) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m).
Proof.
  intros Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo j0
    ART0 MI0 CALL UWOK Hc Hn HCA0 Hvar0.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
  assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
  assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
  assert (Husp : usp + 16 <= USTACK_TOP) by exact SPT.
  pose proof (ART_wf Σ m ART0) as HW. pose proof (geo_of_wf Σ HW) as HG.
  pose proof (g_grant Σ HG (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
  pose proof (se_disj Σ HG) as (T5 & T4 & ATP). pose proof (g_prb Σ HG) as (P1 & P2 & P3).
  pose proof (fk_prb Σ HG) as (FP1 & FP2 & FP3 & FP4 & FP5).
  pose proof (fk_aceil Σ HG) as (AC1 & AC2).
  assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp AC1; unfold USTACK_TOP, SHB in *; lia).
  eapply evt_cut; [exact (segA_evt Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                           ART0 MI0 CALL UWOK Hc Hn)|].
  intros ms P. destruct P as (tr & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m4 & -> & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4).
  destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
  pose proof (free_p_wf Σ m c i n _ ART0 Hc Hn Dok Dinv) as HW1. pose proof (geo_of_wf0 _ HW1) as HG1.
  pose proof ART4 as (CR4 & PR4 & CA4 & CH4 & SR4 & QR4 & DR4 & FS4 & IR4 & SH4 & VIS4).
  pose proof (CA4 24 ltac:(lia)) as (PC24 & _). cbn [ca ca_init free_p lay] in PC24. rewrite HCA0 in PC24. cbn [length Z.of_nat] in PC24.
  pose proof QR4 as (QT4 & _). cbn [ql free_p lay] in QT4.
  (* [comment removed for export] *)
  eapply evt_cut.
  { destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
    - rewrite HQL in QT4.
      apply (qenq_miss_A_empty_spec (Z_to_bv 64 0x1a038c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 QUAR)
               (Z_to_bv 64 (l_T (lay Σ) + 80)) y3 y4 y5 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (l_T (lay Σ) + 208))
               (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4
               (l_T (lay Σ)) (usp + -2128) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n lo _ _ QT4 PC24);
        rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
      + clear - GT1. lia.
      + clear - T5. unfold SEGTOP_A in *. lia.
      + clear - GT3 HLO. lia.
      + exact ST4.
      + clear - HLO2. lia.
      + clear - Hsp Husp. unfold USTACK_TOP in *. lia.
      + exact MI4.
    - rewrite HQL in QT4. pose proof (qwf_ql _ HW1) as QWF. cbn [ql free_p lay] in QWF. rewrite HQL in QWF.
      pose proof HW as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq, HQL in Q1.
      eapply (qenq_miss_A_full_spec (Z_to_bv 64 0x1a038c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 QUAR)
               (Z_to_bv 64 (l_T (lay Σ) + 80)) y3 y4 y5 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (l_T (lay Σ) + 208))
               (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4
               (l_T (lay Σ)) (usp + -2128) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n lo _ _ (l_SB (lay Σ)) pre
               (p_abeg (l_SB (lay Σ)) 24 j0) ents0 HL0 QT4 QWF);
        rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
      + clear - Q1. unfold QMAX_L in *. lia.
      + exact PC24.
      + clear - GT1. lia.
      + clear - T5. unfold SEGTOP_A in *. lia.
      + clear - GT3 HLO. lia.
      + clear - FP2 FP4 FP5 HLO. unfold r24. lia.
      + clear - FP4 FP5 ATP. unfold r24 in *. lia.
      + clear - FP1 FP4. lia.
      + exact ST4.
      + clear - HLO2. lia.
      + clear - Hsp Husp. unfold USTACK_TOP in *. lia.
      + exact MI4. }
  intros ms P. destruct P as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & m5 & -> & MU5 & WM5 & MI5 & (jf & EF5) & ST5).
  rewrite (unsigned_lit (usp + -2208)) in MU5, EF5, ST5 |- * by exact RSP.
  apply evt_done.
  assert (HBt : Forall (fun bt => exists j, nth_error (r_st (pr (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24)) j = Some CkBatch
                                         /\ fst bt = p_abeg (l_SB (lay (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))))) 24 j)
                       (ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
                        ++ qg (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))))).
  { pose proof HW1 as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB. }
  pose proof HW1 as (_ & _ & _ & _ & _ & _ & _ & Dok1 & _).
  assert (Ha : l_ACEIL (lay (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))) <= usp + -2208 - 64)
    by (cbn [lay free_p]; clear - Hsp; lia).
  exists tr, z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, m5, jf.
  split; [reflexivity|].
  split; [exact (ARTc_stack _ (usp + -2208 - 64) (usp + -2208) HG1 Ha m4 m5 ART4 MU5 WM5 HBt Dok1)|].
  split; [exact Htr|]. split; [exact MI5|]. split; [exact (wmono_trans ctasegs _ _ _ WM4 WM5)|].
  split; [replace (usp + -2208 + -64) with (usp + -2208 - 64) by ring; exact ST5|].
  split.
  { intros a Ha'. rewrite (MU5 a); [exact (RP4 a Ha')|].
    refine (kv_client (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) [(usp + -2208 - 64, usp + -2208)] [] [] [] usp HG1
             (sk_img _ _ _ HG1 Ha) (sk_grant _ _ _ HG1 Ha) (sk_slot _ _ _ HG1 Ha) (sk_shad_app _ _ _ HG1 Ha) (sk_secmap _ _ _ HG1 Ha) _
             ltac:(apply Forall_forall; intros; exact I) (live_remove (p_abeg (l_SB (lay Σ)) c i + rz_size n) (live Σ)) _ _ Ha').
    - intros a' k' H1 H2. cbn [disjoint_from]. split; [clear - H1; lia | exact I].
    - intros p' n' Hin. pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
      destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
      + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity | intros []].
      + right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
        split; [reflexivity | intros []]. }
  split.
  { apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). cbn [disjoint_from]. split; [clear; lia | exact I]. }
  split.
  { unfold qput_frame in FR4 |- *. apply (rw_cells_transport ctasegs _ m4 m5 _ _ FR4 MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
    split; [clear; lia | exact I]. }
  replace (usp + -2208 + -64) with (usp + -2208 - 64) by ring. exact EF5.
Qed.

Lemma rt_eager_fp : forall Σ c i n p D', rt_eager (free_p Σ c i n p D') = rt_eager Σ.
Proof.
  intros Σ c i n p D'. apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
  cbn [free_p pr]. destruct (Z.eqb_spec k' c) as [->|_]; [unfold upd_reg; cbn [r_muser r_mfa]|]; split; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem rta_free_miss2 : drain_stmt -> fixed_commit_node ->
  forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (j0 : nat),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n) -> tp = Z_to_bv 64 0xba93f0 ->
  ART_A Σ m -> mem_inv ctasegs m -> call_ok RTA Σ m sp lo -> unwind_ch m ra s0 sp ->
  1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) -> ca Σ 24 = [] ->
  (ql Σ = [] \/ exists pre ents0, nth_error (r_st (pr Σ 24)) j0 = Some CkBatch /\ ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)]
                                  /\ length ents0 = 1021%nat) ->
  cps ctasegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post RTA Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
  intros DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n j0
    FDO MST -> -> ART0 MI0 CALL UWOK Hc Hn HCA0 Hvar0.
  intros TT cf Hc0 Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
  assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
  assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
  assert (Husp : usp + 16 <= USTACK_TOP) by exact SPT.
  pose proof (ART_wf Σ m ART0) as HW. pose proof (geo_of_wf Σ HW) as HG. pose proof (fk_aceil Σ HG) as (AC1 & AC2).
  assert (RSP : 0 <= usp + -2208 + -64 < 2 ^ 64) by (clear - Hsp Husp AC1; unfold USTACK_TOP, SHB in *; lia).
  (* [comment removed for export] *)
  assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0xba93f0) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m) ms ->
                       evt ctasegs (mf_post Σ c i n ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
    by (intros ms <-; exact (mf_front Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo j0
                               ART0 MI0 CALL UWOK Hc Hn HCA0 Hvar0)).
  apply (cps_realizes ctasegs _ _ _ cf (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
  intros c1 Hc1.
  apply AST_exI in Hc1 as [tr Hc1]. apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1].
  apply AST_exI in Hc1 as [y3 Hc1]. apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1].
  apply AST_exI in Hc1 as [y7 Hc1]. apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [y10 Hc1].
  apply AST_exI in Hc1 as [m5 Hc1]. apply AST_exI in Hc1 as [jf Hc1].
  pose proof Hc1 as (_ & (_ & ART5 & Htr & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5 & EF5) & _ & _).
  destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
  pose proof (mi_wf1 Σ m c i n tr ART0 Hc Hn Dok Dinv) as HW1.
  pose proof (mi_room Σ m c i n tr ART0 Hc Hn HCA0 Dok Dinv) as HROOM.
  (* [comment removed for export] *)
  pose proof HW1 as (_ & (HR1 & _) & _).
  pose proof (refill_ca_len (pr (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24) 24 ltac:(clear; lia)
                (HR1 24 ltac:(clear; lia))) as LCA.
  change (MaxCount 24 / 2) with 1 in LCA.
  pose proof (refill_wf0 _ 24 ltac:(clear; lia) HW1 HCA0 HROOM) as HWb.
  pose proof HWb as (_ & (_ & _ & HR3 & _) & _). destruct (HR3 24 ltac:(clear; lia)) as (_ & _ & CAF).
  cbn [refillΣ ca] in CAF. rewrite Z.eqb_refl in CAF.
  destruct (refill_ca (pr (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24) 24) as [|x [|y l]] eqn:ECA;
    [cbn in LCA; lia | | cbn in LCA; lia].
  pose proof (proj1 (Forall_forall _ _) CAF x (in_eq x [])) as (Hx & _).
  set (jB := Z.to_nat x).
  assert (HjB : refill_ca (pr (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24) 24 = [Z.of_nat jB])
    by (rewrite ECA; unfold jB; rewrite Z2Nat.id by (clear - Hx; lia); reflexivity).
  (* [comment removed for export] *)
  assert (Hc1' : AST SEGTOP_A (rtA_allow (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))))
                   (eq (refill_entry_st (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp y0 y1 y2
                          (Z_to_bv 64 (pc_addr (l_T (lay Σ)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ)))) y3 y4 y5 y6
                          (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 (qcacheT (l_T (lay Σ)))) (Z_to_bv 64 (usp + -2128))
                          (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y7 y8 y9 y10 F fc (l_T (lay Σ)) 24 m5))
                   (fun mo => ARTM_A (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) mo /\ PMc mo) c1).
  { eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E |].
    intros mo (HM & HP). split; [|exact HP]. apply (artm_eq Σ); [reflexivity | reflexivity | apply rt_eager_fp | exact HM]. }
  apply (refill_core _ PMc m5 24 lo (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp
           (Z_to_bv 64 (pc_addr (l_T (lay Σ)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ)))) (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16))
           (Z_to_bv 64 (qcacheT (l_T (lay Σ)))) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 F fc
           y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 FDO MST HW1 ART5 ltac:(clear; lia) HCA0 HROOM MI5
           ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; exact ST5) ltac:(cbn [lay free_p]; exact HLO)
           ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; clear - HLO2; lia)
           ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; clear - Husp; unfold USTACK_TOP in *; lia) FC TT c1 Hc1').
  intros c2 Hc2.
  (* [comment removed for export] *)
  assert (VAR : exists (jX : nat) (stX : ckst),
            nth_error (r_st (pr (refillΣ (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24) 24)) jX = Some stX
            /\ ((jX = jB /\ stX = CkIdle /\ ql Σ = [])
                \/ (stX = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 jX, ents0)] /\ length ents0 = 1021%nat))).
  { destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
    - exists jB, CkIdle. split; [|left; split; [reflexivity|]; split; [reflexivity | exact HQL]].
      exact (ng_jB _ [] jB HWb ltac:(cbn [refillΣ ca]; rewrite Z.eqb_refl; exact HjB)).
    - exists j0, CkBatch. split; [|right; split; [reflexivity|]; exists pre, ents0; split; [exact HQL | exact HL0]].
      apply (rfs_keep _ 24 ltac:(clear; lia) HW1). rewrite (fp_other Σ c i n _ _ 24 j0); [exact Hj0|].
      destruct (Z.eq_dec 24 c) as [<-|X]; [right; intros ->; rewrite Hn in Hj0; discriminate Hj0 | left; exact X]. }
  destruct VAR as (jX & stX & HjX & HvarX).
  assert (W2 : forall ms, rf_post (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24 lo
                          (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp
                          (Z_to_bv 64 (pc_addr (l_T (lay Σ)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ)))) (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16))
                          (Z_to_bv 64 (qcacheT (l_T (lay Σ)))) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 m5 ms ->
                 evt ctasegs (fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32),
                              enq_post (enq_new (refillΣ (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24) [] jB
                                                (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n)
                                       (live (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))) (frames Σ)
                                       ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' lo m ms') ms).
  { intros ms (m6 & RET & ART6 & MI6 & WM6 & ST6 & MU6).
    destruct RET as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & F' & fc' & ->).
    rewrite (ret_pc_even qenq_refill_ret) by (unfold qenq_refill_ret; first [reflexivity | lia]).
    rewrite (unsigned_lit (usp + -2208 + -64)) in ST6, MU6 by exact RSP.
    eapply evt_mono; [apply (miss_enq Σ m c i n tr jB jX stX usp ART0 Hc Hn HCA0 Hsp Dok Dinv HjB HjX HvarX
                               ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' m5 m6 lo jf (Z_to_bv 64 qenq_refill_ret)
                               z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 eq_refl HLO HLO2 Husp WM5 RP5 ICF5 FR5 EF5 ART6 MI6 WM6 ST6 MU6)|].
    intros ms' P. exists F', fc'. exact P. }
  apply (cps_realizes ctasegs _ _ _ c2 (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below _ _ _ _ (fl_ASTA_mat_stable _ PMc MST) W2) Hc2).
  intros c3 Hc3. apply AST_exI in Hc3 as [F' Hc3]. apply AST_exI in Hc3 as [fc' Hc3].
  apply (fin_from_enq DRAIN Σ (enq_new (refillΣ (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24) [] jB
                                       (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n)
           PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' m lo (p_ubeg (l_SB (lay Σ)) c i n) TT c3 FDO MST
           eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp); [|exact Hk].
  eapply AST_conseq; [exact Hc3 | intros ms H; exact H|]. intros mo (HM & HP). split; [|exact HP].
  apply (artm_eq (refillΣ (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24));
    [reflexivity | reflexivity | exact (mi_rt_eager Σ c i n tr jB) | exact HM].
Qed.

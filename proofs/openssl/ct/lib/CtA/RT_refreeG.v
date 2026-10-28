(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ricpt_frame (m : mem) (usp : Z) (ra s0 s1 s2 s3 s4 s5 : word) : Prop :=
  (exists s4r s3r s2r s1r s0r, rw_cells ctasegs m (usp + -2128) [C8 s4r; C8 s3r; C8 s2r; C8 s1r; C8 s0r; C8 (Z_to_bv 64 0x19c820)])
  /\ (exists jr, rw_cells ctasegs m (usp + -2080) [CB 8 jr])
  /\ rw_cells ctasegs m (usp + -2072) [C8 (Z_to_bv 64 0x1c4880)]
  /\ (exists jq, rw_cells ctasegs m (usp + -2064) [CB 8 jq])
  /\ (exists w, rw_cells ctasegs m (usp + -2056) [C8 (Z_to_bv 64 (usp + -2040)); C8 w])
  /\ (exists ws, u64arr ctasegs m (usp + -2040) ws /\ length ws = 255%nat).

Lemma ricpt_frame_transport : forall W (m m' : mem) usp ra s0 s1 s2 s3 s4 s5, ricpt_frame m usp ra s0 s1 s2 s3 s4 s5 ->
  munch W m m' -> wmono ctasegs m m' -> disjoint_from W (usp - 2128) 2128 -> ricpt_frame m' usp ra s0 s1 s2 s3 s4 s5.
Proof.
  intros W m m' usp ra s0 s1 s2 s3 s4 s5 ((s4r & s3r & s2r & s1r & s0r & F1) & (jr & F2) & F3 & (jq & F4) & (w & F5) & (ws & F6 & F6l)) MU WM HD.
  split; [|split; [|split; [|split; [|split]]]].
  - exists s4r, s3r, s2r, s1r, s0r. apply (rw_cells_transport ctasegs W m m' _ _ F1 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
  - exists jr. apply (rw_cells_transport ctasegs W m m' _ _ F2 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
  - apply (rw_cells_transport ctasegs W m m' _ _ F3 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
  - exists jq. apply (rw_cells_transport ctasegs W m m' _ _ F4 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
  - exists w. apply (rw_cells_transport ctasegs W m m' _ _ F5 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
  - exists ws. split; [|exact F6l]. apply (u64arr_transport ctasegs W m m' _ _ F6 MU WM). rewrite F6l.
    apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma ricpt_frame_agree : forall (m m' : mem) usp ra s0 s1 s2 s3 s4 s5, ricpt_frame m usp ra s0 s1 s2 s3 s4 s5 ->
  (forall a : word, usp - 2128 <= bv_unsigned a < usp -> m' a = m a) -> ricpt_frame m' usp ra s0 s1 s2 s3 s4 s5.
Proof.
  intros m m' usp ra s0 s1 s2 s3 s4 s5 ((s4r & s3r & s2r & s1r & s0r & F1) & (jr & F2) & F3 & (jq & F4) & (w & F5) & (ws & F6 & F6l)) AG.
  split; [|split; [|split; [|split; [|split]]]].
  - exists s4r, s3r, s2r, s1r, s0r. apply (rw_cells_agree_nw ctasegs m m' _ _ F1). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
  - exists jr. apply (rw_cells_agree_nw ctasegs m m' _ _ F2). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
  - apply (rw_cells_agree_nw ctasegs m m' _ _ F3). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
  - exists jq. apply (rw_cells_agree_nw ctasegs m m' _ _ F4). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
  - exists w. apply (rw_cells_agree_nw ctasegs m m' _ _ F5). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
  - exists ws. split; [|exact F6l]. apply (u64arr_agree_nw ctasegs m m' _ _ F6). intros a Ha. apply AG. rewrite F6l in Ha. cbn in Ha. lia.
Qed.

(* [comment removed for export] *)
Definition renq_post (Σ2 : rtsA) (live0 : list (Z * Z)) (frames0 : list (Z * nat)) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 : word) (m' : mem),
    (ms = enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m' /\ w4 = s4)
    /\ ARTc Σ2 m' /\ rt_wfx Σ2 /\ rt_count Σ2 /\ mem_inv ctasegs m' /\ wmono ctasegs m m' /\ stk ctasegs m' lo (bv_unsigned sp + -2208)
    /\ rt_pres live0 frames0 (bv_unsigned sp) m m'
    /\ ricpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
    /\ qput_frame m' (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ2) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x19c930)
         w0 w1 w2 w3 w4 w5 s6.

(* [comment removed for export] *)
Definition drain_stmt_r : Prop :=
  forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
  fdfs_only PMc -> mat_stable PMc ->
  ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < qbytes (ql Σ) ->
  qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x19c930) w0 w1 w2 w3 w4 w5 s6 ->
  stk ctasegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
  mem_inv ctasegs m ->
  cps ctasegs
    (ASTA RTA Σ PMc (eq (MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
                                 (Z_to_bv 64 (l_T (lay Σ) + 80)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x100000)
                                 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a038c) fc None m (seg_rom ctasegs))))
    (fun cf => exists Σ' : rtsA,
       ASTA RTA Σ' PMc (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                                         (fc' : bv 32) (m' : mem),
           ms = MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
                        a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0x19c930) fc' None m' (seg_rom ctasegs)
           /\ ART_A Σ' m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (usp + -2128)
           /\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m') cf
       /\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ).

(* [comment removed for export] *)
Definition rfin_post (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1 w2 w3 w5 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m5 : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5' a6' a7'
                 w2 w3 s4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x19c930) fc None m' (seg_rom ctasegs)
    /\ ART_A Σ2 m' /\ mem_inv ctasegs m' /\ wmono ctasegs m5 m' /\ stk ctasegs m' lo (bv_unsigned sp + -2128)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp - 2128)] m5 m'
    /\ ricpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5.

(* [comment removed for export] *)
Lemma ret_tail_r : forall (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
    t3 t4 t5 t6 w0 w1 w2 w3 w5 wc ws : word) (F : bvmap 5 word) (fc : bv 32) (m5 : mem) (lo : Z),
  geo_ok Σ2 -> ARTc Σ2 m5 -> rt_wfx Σ2 -> rt_count Σ2 -> RT_state.qbytes (ql Σ2) <= 0x100000 ->
  mem_inv ctasegs m5 -> stk ctasegs m5 lo (bv_unsigned sp + -2208) -> l_ACEIL (lay Σ2) <= lo -> lo + 0xFFB0 <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP ->
  ricpt_frame m5 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5 ->
  qput_frame m5 (bv_unsigned sp + -2208) wc ws (Z_to_bv 64 0x19c930) w0 w1 w2 w3 s4 w5 s6 ->
  evt ctasegs (rfin_post Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1 w2 w3 w5 F fc lo m5)
    (enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5).
Proof.
  intros Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w0 w1 w2 w3 w5 wc ws F fc m5 lo
    HG ART5 HWX HC HBY MI5 ST5 HLO HLO2 Husp ICF FR5.
  set (usp := bv_unsigned sp) in *.
  pose proof (fk_aceil Σ2 HG) as (X1 & X2).
  assert (RSP2 : 0 <= usp + -2128 < 2 ^ 64) by (clear - HLO HLO2 Husp X1; unfold USTACK_TOP, SHB in *; lia).
  pose proof ART5 as (_ & _ & _ & _ & _ & QR & _). destruct QR as (QT & _).
  pose proof QT as QT'. apply (proj1 (qcache_rep_iff _ _ _)) in QT'. destruct QT' as (QH & _).
  unfold enq_ret_st.
  replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80))
    by (rewrite (unsigned_lit (usp + -2128)) by exact RSP2; f_equal; lia).
  replace (usp + -2208) with (usp + -2128 - 80) in ST5, FR5 by lia.
  pose proof (qbytes_nonneg _ _ (qwf_ql_x Σ2 HWX)) as QB0.
  eapply evt_mono.
  { apply (qput_B_ret_spec (Z_to_bv 64 0x19c930) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s2' s3' s4' s5' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11
             t3 t4 t5 t6 ra0 w0 w1 w2 w3 s4 w5 s6 wc ws F fc m5 (l_T (lay Σ2) + 80) (R_quar_defs.qbytes (ql Σ2)) lo
             (Z_to_bv 64 (Z.of_nat (length (ql Σ2)))) (Z_to_bv 64 (qfirst (ql Σ2))) (Z_to_bv 64 (qlast (ql Σ2))));
      try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP2.
    all: try exact ST5. all: try exact FR5. all: try (clear - HLO2; lia). all: try (clear - X1 HLO; unfold SHB in *; lia).
    rewrite qbytes_eq. clear - QB0 HBY. rewrite qbytes_eq in QB0. lia. }
  intros ms6 P6. destruct P6 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6).
  rewrite (unsigned_lit (usp + -2128)) in MU6, ST6 by exact RSP2. rewrite (ret_pc_even 0x19c930) by (first [reflexivity | lia]).
  lazymatch type of MU6 with munch ?W6 _ _ =>
    pose proof (munch_weaken W6 [(usp - 2208, usp - 2128)] m5 m6 ltac:(clear - HLO2; solve_sub_fp) MU6) as MU56;
    pose proof (munch_weaken W6 [(usp - 2208, usp)] m5 m6 ltac:(clear - HLO2; solve_sub_fp) MU6) as MU56' end.
  unfold rfin_post. exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m6. split; [reflexivity|].
  split; [|split; [exact MI6 | split; [exact WM6 | split; [exact ST6 | split; [exact MU56|]]]]].
  - apply c_ART; [exact (rt_wf_of_x Σ2 HWX HC ltac:(clear - HBY; unfold QMAX_L; lia))|].
    apply (ARTc_stack Σ2 (usp - 2208) usp HG ltac:(clear - HLO HLO2; lia) m5 m6 ART5 MU56' WM6).
    + destruct HWX as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB.
    + destruct HWX as (_ & _ & _ & _ & _ & _ & _ & DOK & _). exact DOK.
  - apply (ricpt_frame_transport _ m5 m6 usp ra s0 s1 s2 s3 s4 s5 ICF MU6 WM6). cbn [disjoint_from]. split; [clear; lia | exact I].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F R_qenqueue_M R_qenqueue_MF R_asan_free R_prim_kit R_refill RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_freeI RT_freeJ RT_freeK RT_freeL RT_refillstmt RT_refillst RT_refillwf RT_rfkit RT_count.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma pend_refill : forall Σ1 c i n, rt_wf0 Σ1 -> pend_ok Σ1 c i n -> pend_ok (refillΣ Σ1 24) c i n.
Proof.
  intros Σ1 c i n HW (Hc & Hn & FR & RC1 & RC2).
  split; [exact Hc|]. split; [exact (rfs_keep Σ1 24 ltac:(lia) HW c i _ Hn)|].
  split; [exact FR|]. split.
  - intros c' i' n' Hc' Hi' Hne. destruct (rfs_st Σ1 24 ltac:(lia) HW c' i' _ Hi') as [Hi0|(_ & E & _)]; [exact (RC1 c' i' n' Hc' Hi0 Hne) | discriminate E].
  - exact RC2.
Qed.

(* [comment removed for export] *)
Lemma pend_room : forall Σ1 c i n, rt_wf0 Σ1 -> pend_ok Σ1 c i n -> ca Σ1 24 = [] -> refill_room Σ1 24.
Proof.
  intros Σ1 c i n HW (Hc & Hn & FR & RC1 & RC2) HCA. apply (carved_room_gen Σ1 24 i HW ltac:(lia) HCA).
  intros i' n' Hi' Hne. apply (RC1 24 i' n' ltac:(lia) Hi'). destruct (Z.eq_dec 24 c) as [<-|X]; [right; exact Hne | left; exact X].
Qed.

Section Miss.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n : Z) (tr : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HCA0 : ca Σ 24 = [].
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis Dok : depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis Dinv : dep_inv (fst (depot_put (dep Σ) tr)).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))).
#[local] Notation Σb := (refillΣ (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24).
#[local] Notation Σ2 := (enq_new (refillΣ (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) 24) [] jB
                          (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).
Hypothesis HjB : refill_ca (pr Σ1 24) 24 = [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σb 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle /\ ql Σ = [])
  \/ (st0 = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)] /\ length ents0 = 1021%nat).

(* [comment removed for export] *)
Lemma mi_wf1 : rt_wf0 Σ1.
Proof using HA Hc Hn Dok Dinv. exact (free_p_wf Σ m c i n _ HA Hc Hn Dok Dinv). Qed.

Lemma mi_pend1 : pend_ok Σ1 c i n.
Proof using HA Hc Hn. exact (pend_free_p Σ m c i n _ _ HA Hc Hn). Qed.

Lemma mi_room : refill_room Σ1 24.
Proof using HA Hc Hn HCA0 Dok Dinv. exact (pend_room Σ1 c i n mi_wf1 mi_pend1 HCA0). Qed.

Lemma mi_wfb : rt_wf0 Σb.
Proof using HA Hc Hn HCA0 Dok Dinv. exact (refill_wf0 Σ1 24 ltac:(clear; lia) mi_wf1 HCA0 mi_room). Qed.

Lemma mi_pendb : pend_ok Σb c i n.
Proof using HA Hc Hn Dok Dinv. exact (pend_refill Σ1 c i n mi_wf1 mi_pend1). Qed.

Lemma mi_cab : ca Σb 24 = [] ++ [Z.of_nat jB].
Proof using HjB. cbn [refillΣ ca]. rewrite Z.eqb_refl. exact HjB. Qed.

Lemma mi_var : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σb)) 24 j0) (map fst (ql Σb))).
Proof using Hvar.
  destruct Hvar as [(E1 & E2 & _)|(E1 & pre & ents0 & HQL & _)]; [left; split; assumption|]. right. split; [exact E1|].
  cbn [refillΣ ql free_p lay]. rewrite HQL, map_app. apply in_or_app. right. left. reflexivity.
Qed.

Lemma mi_rt_eager : rt_eager Σ2 = rt_eager Σb.
Proof.
  apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
  cbn [enq_new set_ql pop24 pr]. destruct (Z.eqb_spec k' 24) as [->|_]; [|split; reflexivity]. unfold upd_reg. cbn [r_muser r_mfa]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma miss_enq : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m5 m6 : mem) (lo : Z) (jf : list byte) (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bv_unsigned sp = usp -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
  wmono ctasegs m m5 -> rt_pres (live Σ1) (frames Σ) usp m m5 ->
  icpt_frame m5 usp ra s0 s1 s2 s3 s4 s5 ->
  qput_frame m5 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x1c424c) (Z_to_bv 64 usp)
    (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0x1c41dc) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 ->
  rw_cells ctasegs m5 (usp + -2208 + -64) [CB 8 jf; C8 (Z_to_bv 64 M); C8 (Z_to_bv 64 (T + 208)); C8 (Z_to_bv 64 (usp + -2128));
                                          C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (T + 80)); C8 (Z_to_bv 64 QUAR); C8 (Z_to_bv 64 0x1a038c)] ->
  ARTc Σb m6 -> mem_inv ctasegs m6 -> wmono ctasegs m5 m6 -> stk ctasegs m6 lo (usp + -2208 + -64) ->
  munch (W_R T SB 24 (ClassSize 24 * Z.of_nat (length (r_st (pr Σ1 24)))) (usp + -2208 + -64)) m5 m6 ->
  evt ctasegs (enq_post Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (Z_to_bv 64 (usp + -2208 + -64)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (pc_addr T 24)) (Z_to_bv 64 (cacheT T))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 M) (Z_to_bv 64 (qcacheT T)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 n)
             (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 qenq_refill_ret) fc None m6 (seg_rom ctasegs)).
Proof using HA Hc Hn HCA0 Hsp Dok Dinv HjB Hj0 Hvar.
  intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m5 m6 lo jf ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    Esp HLO HLO2 Husp WM5 RP5 ICF FR5 EF5 ART6 MI6 WM6 ST6 MU6.
  pose proof mi_wf1 as HW1. pose proof mi_wfb as HWb. pose proof mi_pendb as HPb. pose proof mi_cab as HCA. pose proof mi_var as Hvar'.
  pose proof HPb as (_ & Hnq & _).
  pose proof (geo_of_wf0 Σb HWb) as HG. pose proof (geo_of_wf0 Σ1 HW1) as HG1.
  pose proof (ng_jB Σb [] jB HWb HCA) as HjB'.
  change (lay Σb) with (lay Σ) in *. change (lay Σ1) with (lay Σ) in *.
  pose proof (se_geo Σb j0 jB st0 CkIdle HG Hj0 HjB') as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj Σb HG) as (T5 & T4 & ATP).
  pose proof (g_prb Σb HG) as (P1 & P2 & P3).
  change (lay Σb) with (lay Σ) in *.
  assert (Hn1 : 1 <= n <= 2 ^ 16).
  { pose proof HG as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hnq)) as (X & X1 & _). cbv beta iota in X, X1. pose proof (ClassSize_range c Hc) as (X2 & _).
    pose proof (rz_facts n) as (_ & X3). clear - X X1 X2 X3; lia. }
  assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
  (* [comment removed for export] *)
  assert (HWR : forall a k, usp + -2208 + -64 <= a -> a + k <= usp -> disjoint_from (W_R T SB 24 (ClassSize 24 * Z.of_nat (length (r_st (pr Σ1 24)))) (usp + -2208 + -64)) a k).
  { intros a k H1 H2. pose proof (rz_geo Σ1 24 HG1 ltac:(lia)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
    pose proof (rz_shad Σ1 24 HG1 ltac:(lia)) as (S1 & S2). pose proof (se_disj Σ1 HG1) as (Z5 & Z4 & ZTP).
    cbn [lay free_p] in *. unfold W_R. cbn [disjoint_from]. clear - H1 H2 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11 Y12 S1 S2 Hsp K14 K15 K4 K6.
    unfold rb, kUserCap, rinfo, RIS_of, SHB in *. repeat split; try exact I; lia. }
  assert (EF6 : rw_cells ctasegs m6 (usp + -2208 + -64) [CB 8 jf; C8 (Z_to_bv 64 M); C8 (Z_to_bv 64 (T + 208)); C8 (Z_to_bv 64 (usp + -2128));
                                          C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (T + 80)); C8 (Z_to_bv 64 QUAR); C8 (Z_to_bv 64 0x1a038c)]).
  { apply (rw_cells_transport ctasegs _ m5 m6 _ _ EF5 MU6 WM6). apply HWR; cbn [cells_size csize Nat.add]; clear - Hsp; lia. }
  pose proof (g_grant Σb HG (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
  pose proof ART6 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
  (* [comment removed for export] *)
  destruct (new_wfx Σb [] jB c i n HWb HPb HCA) as (WX & WC).
  pose proof (qwf_ql_x _ WX) as QWF. cbn [enq_new set_ql ql pop24 lay refillΣ free_p] in QWF.
  pose proof HWb as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq in Q1. cbn [refillΣ ql free_p] in Q1.
  (* [comment removed for export] *)
  assert (Hinit : ca_init Σb = true) by reflexivity.
  pose proof (CA 24 ltac:(lia)) as PC. cbn [ca ca_init lay] in PC. rewrite Hinit in PC. rewrite HCA in PC.
  destruct PC as (PCC & chs & ARR & Hlen & Hpre).
  change (ClassSize 24) with 8192 in PCC.
  assert (Hw : nth_error chs (Z.to_nat (Z.of_nat (length ([] ++ [Z.of_nat jB])) - 1)) = Some (cpw 24 (Z.of_nat jB))).
  { pose proof (fl_hit_w (cpw 24) ([] ++ [Z.of_nat jB]) chs ltac:(discriminate) Hpre) as X. rewrite last_last in X.
    replace (Z.to_nat (Z.of_nat (length ([] ++ [Z.of_nat jB])) - 1)) with (length ([] ++ [Z.of_nat jB]) - 1)%nat by (clear; cbn [length app]; lia).
    exact X. }
  assert (HAB : chunk_addr SB 24 (cpw 24 (Z.of_nat jB)) = bB).
  { rewrite fl_hit_addr; [rewrite Nat2Z.id; reflexivity | lia | | reflexivity]. change (ClassSize 24) with 8192. clear - K9 K10. unfold p_abeg, rb, kUserCap in *.
    change (ClassSize 24) with 8192 in *. lia. }
  pose proof (MaxCount_range 24 ltac:(lia)) as (MC1 & _).
  (* [comment removed for export] *)
  assert (NC : exists stj jb, qnew_cells m6 T SB (Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb).
  { destruct CR as (CI & _ & _ & _ & _ & _ & _ & ICR). pose proof ICR as STS. do 31 (apply proj2 in STS). apply proj1 in STS.
    cbn [lay] in STS. destruct (stk_split ctasegs m6 (T + 2768) (T + 2784) (T + 3168) STS ltac:(lia)) as [_ STS1].
    destruct (stk_split ctasegs m6 (T + 2784) (T + 2784 + 8) (T + 3168) STS1 ltac:(lia)) as [STS2 _].
    destruct (fl_c8_of_stk m6 (T + 2784) STS2) as (stj & HST).
    destruct CH as (P & _). pose proof (P 24 jB CkIdle ltac:(lia) HjB') as PB.
    cbn [pchunk lay] in PB. destruct PB as (PB & _). change (ClassSize 24) with 8192 in PB.
    destruct (fl_CB_of_stk m6 bB 8192 PB) as (jb & HJB).
    exists stj, jb. unfold qnew_cells. split; [exact PCC|]. split; [exact ARR|]. split; [exact HST|].
    split; [cbn [lay] in CI; destruct CI as (CI & _); exact (proj1 (proj1 (rwc_app ctasegs m6 i_spacebeg [C8 (Z_to_bv 64 SB)] _) CI))|].
    rewrite HAB. exact HJB. }
  destruct NC as (stj & jb & NC).
  (* [comment removed for export] *)
  replace (usp + -2208 + -64) with (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -64) by (rewrite (unsigned_lit (usp + -2208)) by exact RSP; reflexivity).
  eapply (evt_mono ctasegs (qenq_post (Z_to_bv 64 0x1a038c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
                            (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) (Z_to_bv 64 0x100000)
                            s7 s8 s9 s10 s11 F fc
                            [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
                             (b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] (qcacheT T) (ql Σ ++ [(bB, [(M, n)])]) lo m6
                            (fun m' => qnew_after m' T SB (Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs))).
  { destruct Hvar as [(E1 & E2 & HQL)|(E1 & pre & ents0 & HQL & HL0)].
    - pose proof QR as (QT & _). cbn [ql lay refillΣ free_p] in QT. rewrite HQL in QT.
      eapply evt_mono.
      { apply (qenq_miss_B_empty_spec ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0x1a038c) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
                 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) F fc m6 T (usp + -2128) M n SB lo
                 (Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb jf);
          try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
        all: try (clear - Hn1; lia). all: try (clear - MC1; lia). all: try (clear; cbn; lia).
        all: try (clear - P3; unfold p_abeg; apply Z.mod_divide in P3; [|lia]; destruct P3 as [q Hq]; rewrite Hq;
                  replace (q * 2 ^ 16 + 24 * 2 ^ 32 + Z.of_nat jB * ClassSize 24) with ((q * 8 + 24 * 2 ^ 19 + Z.of_nat jB) * 8192)
                    by (change (ClassSize 24) with 8192; ring); apply Z.mod_mul; lia).
        all: try (clear - K9 K10; unfold r24, rb, kUserCap in *; lia).
        all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
        all: try (clear - T5; unfold SEGTOP_A in *; lia).
        all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
        all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
        all: try exact ST6. all: try exact EF6.
        all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
      intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL.
      eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp.
    - pose proof QR as (QT & _). cbn [ql lay refillΣ free_p] in QT. rewrite HQL in QT. rewrite HQL in QWF, Q1.
      rewrite <- app_assoc in QWF. cbn [app] in QWF.
      eapply evt_mono.
      { apply (qenq_miss_B_full_spec ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0x1a038c) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
                 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) F fc m6 T (usp + -2128) M n SB lo
                 (Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb jf pre b0 ents0);
          try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
        all: try (clear - Hn1; lia). all: try (clear - MC1; lia). all: try (clear; cbn; lia).
        all: try (clear - Q1 Hn1; unfold QMAX_L in *; lia).
        all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
        all: try (clear - T5; unfold SEGTOP_A in *; lia).
        all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
        all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
        all: try exact ST6. all: try exact QWF. all: try exact EF6.
        all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
      intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL, <- app_assoc. cbn [app].
      eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp. }
  intros ms7 P7. destruct P7 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m7 & -> & MU7 & WM7 & MI7 & QR7 & NA7 & ST7).
  rewrite (ret_pc_even 0x1a038c) by (first [reflexivity | lia]).
  destruct NA7 as (NA1 & NA2 & _).
  assert (HSUB : sub_fp [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
                         (b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] W).
  { clear - Hsp. unfold W_E, qcacheT, pc_addr, cstat_alloc. solve_sub_fp. }
  assert (PC7 : pclass_rep T 24 (ca_init Σb) [] m7).
  { rewrite Hinit. split.
    - replace (Z.of_nat (length ([] ++ [Z.of_nat jB])) - 1) with (Z.of_nat (length (@nil Z))) in NA1 by (clear; cbn [length app]; lia).
      change (ClassSize 24) with 8192. exact NA1.
    - exists chs. split; [exact NA2|]. split; [exact Hlen|]. exact (firstn_snoc_map (cpw 24) [] (Z.of_nat jB) chs Hpre). }
  (* [comment removed for export] *)
  assert (RP7 : rt_pres (live Σ2) (frames Σ) usp m m7).
  { intros a Ha. rewrite (MU7 a).
    - rewrite (MU6 a); [exact (RP5 a Ha)|].
      assert (Hsp1 : l_ACEIL (lay Σ1) + 0x400 <= usp + -2208 + -64) by (cbn [lay free_p]; clear - Hsp; lia).
      refine (kv_client Σ1 (W_R T SB 24 (ClassSize 24 * Z.of_nat (length (r_st (pr Σ1 24)))) (usp + -2208 + -64)) [] [] []
               (usp + -2208 + -64) HG1 (rz_img Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_grant Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_slot Σ1 24 _ HG1 ltac:(lia) Hsp1)
               (rz_shad_app Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_secmap Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_stack Σ1 24 _ HG1 ltac:(lia) Hsp1)
               ltac:(apply Forall_forall; intros; exact I) (live Σ1) _ _ _).
      + intros p' n' Hin. pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
        destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
        * left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity | intros []].
        * right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
          split; [reflexivity | intros []].
      + destruct Ha as [X|X]; [left; clear - X Hsp; lia | right; exact X].
    - apply HSUB.
      apply (kv_client Σb _ [(24, j0); (24, jB)] [] [] usp HG
               (se_img Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp) (se_grant Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp)
               (se_slot Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp) (se_shad_app Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp)
               (se_secmap Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp) (se_stack Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp)
               ltac:(apply Forall_forall; intros; exact I) (live Σb)); [|exact Ha].
      intros p' n' Hin. pose proof HWb as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
      destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
      + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
        intros [E|[E|[]]]; injection E as <- <-; [rewrite Hj0 in Hn'; injection Hn' as Est; destruct Hvar' as [(_ & X)|(X & _)]; rewrite X in Est; discriminate Est
                                                 | rewrite HjB' in Hn'; discriminate Hn'].
      + right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
        split; [reflexivity | intros []]. }
  unfold enq_post. exists (Z_to_bv 64 0x1a038c), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2128)),
    (Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 usp), (Z_to_bv 64 (M + 16)), (Z_to_bv 64 0x1c41dc), (Z_to_bv 64 1),
    (Z_to_bv 64 (usp + -2128)), (Z_to_bv 64 (usp + -81)), m7.
  split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
  split; [exact (new_ART_gen Σb c i n [] jB j0 st0 usp HWb Hc Hnq HCA Hj0 Hvar' Hsp m6 m7 ART6 (munch_weaken _ _ _ _ HSUB MU7) WM7 QR7 PC7)|].
  split; [exact WX|]. split; [exact WC|]. split; [exact MI7|]. split; [exact (wmono_trans ctasegs _ _ _ (wmono_trans ctasegs _ _ _ WM5 WM6) WM7)|].
  split; [rewrite Esp; rewrite (unsigned_lit (usp + -2208)) in ST7 by exact RSP; exact ST7|].
  split; [rewrite Esp; exact RP7|].
  split.
  { rewrite Esp. apply (icpt_frame_transport _ m6 m7 usp ra s0 s1 s2 s3 s4 s5 (icpt_frame_transport _ m5 m6 usp ra s0 s1 s2 s3 s4 s5 ICF MU6 WM6
      ltac:(apply HWR; clear - Hsp; lia)) MU7 WM7). unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from].
    clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
  rewrite Esp. unfold qput_frame in FR5 |- *. apply (rw_cells_transport ctasegs _ m6 m7 _ _ (rw_cells_transport ctasegs _ m5 m6 _ _ FR5 MU6 WM6
    ltac:(apply HWR; cbn [cells_size csize Nat.add]; clear - Hsp; lia)) MU7 WM7).
  unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End Miss.

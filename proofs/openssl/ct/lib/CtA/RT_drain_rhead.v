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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_prim_kit R_quar_defs R_qrec_defs R_qput R_qdrain R_qrecycle R_qrecycle_C RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freestmt RT_freeE RT_drain_defs RT_drain_pure RT_drain_led RT_drain_start RT_drain_kit RT_drain_art RT_drain_xfer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition bidx (SB b : Z) : nat := Z.to_nat ((b - SB - 24 * 2 ^ 32) / 8192).
Definition bslots (SB : Z) (bs : list batch) : list (Z * nat) := map (fun b => (24, bidx SB (fst b))) bs.

Lemma bidx_abeg : forall SB i, bidx SB (p_abeg SB 24 i) = i.
Proof.
  intros SB i. unfold bidx, p_abeg. change (ClassSize 24) with 8192.
  replace (SB + 24 * 2 ^ 32 + Z.of_nat i * 8192 - SB - 24 * 2 ^ 32) with (Z.of_nat i * 8192) by lia.
  rewrite Z.div_mul by lia. apply Nat2Z.id.
Qed.

(* [comment removed for export] *)
Lemma bslots_ok : forall Σ bs, Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) bs ->
  forall c i, In (c, i) (bslots (l_SB (lay Σ)) bs) -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch.
Proof.
  intros Σ bs HB c i Hin. unfold bslots in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
  destruct (proj1 (Forall_forall _ _) HB b Hb) as (j & Hj & Eb). rewrite Eb, bidx_abeg. split; [reflexivity | exact Hj].
Qed.

Lemma bslots_cover : forall Σ bs, Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) bs ->
  Forall (fun iv => exists c i, In (c, i) (bslots (l_SB (lay Σ)) bs) /\ p_abeg (l_SB (lay Σ)) c i <= fst iv /\ snd iv <= p_abeg (l_SB (lay Σ)) c i + ClassSize c)
    (bivs bs).
Proof.
  intros Σ bs HB. apply Forall_forall. intros iv Hiv. unfold bivs in Hiv. apply in_map_iff in Hiv as (b & <- & Hb).
  destruct (proj1 (Forall_forall _ _) HB b Hb) as (j & Hj & Eb). exists 24, j. split.
  - unfold bslots. apply in_map_iff. exists b. split; [rewrite Eb, bidx_abeg; reflexivity | exact Hb].
  - cbn [fst snd]. rewrite Eb. change (ClassSize 24) with 8192. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RRun.
Variables (Σ : rtsA) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word).
Hypothesis HA : ARTc Σ m.
Hypothesis HW : rt_wfx Σ.
Hypothesis HC : rt_count Σ.
Hypothesis HBY : 0x100000 < RT_state.qbytes (ql Σ).
Hypothesis FR : qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x1c424c)
                  w0 w1 w2 w3 w4 w5 s6.
Hypothesis ST : stk ctasegs m lo (usp + -2208).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x4000 <= usp + -2208.
Hypothesis HSP : usp <= 2 ^ 47.
Hypothesis MI : mem_inv ctasegs m.
Hypothesis HBYr : 0x10000000 < R_quar_defs.qbytes (qg Σ ++ ql Σ).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation G := (qg Σ ++ ql Σ).

(* [comment removed for export] *)
Definition rh_entry (t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x19de04) (Z_to_bv 64 (usp + -2288)) gp (Z_to_bv 64 tpA) t0' t1' t2' s0' s1' (Z_to_bv 64 QUAR)
          (Z_to_bv 64 (usp + -2288)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) a4' a5' a6' a7' s2' s3' s4' s5
          (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 qdorec_entry) fc None m3 (seg_rom ctasegs).

Definition rh_post : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word) (m3 : mem),
    ms = rh_entry t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' m3
    /\ ARTc (set_q Σ [] (rec_r G QMIN)) m3 /\ qcache_rep m3 (usp + -2288) (rec_x G QMIN)
    /\ qrec_frame m3 (usp + -2288) (Z_to_bv 64 0x1a02c4) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4
    /\ qput_frame m3 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x1c424c) w0 w1 w2 w3 w4 w5 s6
    /\ stk ctasegs m3 lo (usp + -2288) /\ mem_inv ctasegs m3 /\ wmono ctasegs m m3 /\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m3.

Lemma rr_qg : exists pre bl el, qg Σ = pre ++ [(bl, el)].
Proof using HW HBYr.
  destruct (qg Σ) as [|b0 rest] eqn:E.
  - exfalso. pose proof HW as (_ & _ & _ & _ & (Q1 & _) & _). cbn [app] in HBYr. rewrite <- qbytes_eq in HBYr.
    unfold QMAX_L in Q1. lia.
  - destruct (exists_last (l := b0 :: rest) ltac:(discriminate)) as (pre & (bl & el) & E2). exists pre, bl, el. exact E2.
Qed.

(* [comment removed for export] *)
Definition W_RH (T usp bl : Z) (bs : list batch) : list ivl :=
  [(i_q_cmutex, i_q_cmutex + 4); (i_q_global, i_q_global + 32); (T + 80, T + 112); (bl, bl + 8); (usp - 2304, usp - 2208)] ++ bivs bs.

Lemma rr_cert : forall bl, In bl (map fst G) ->
  Forall (dzone Σ (bslots SB G) [] [] (TZ_X T) IZ_Q [] lo (usp + -2128)) (W_RH T usp bl G).
Proof using HW HLO2.
  intros bl Hbl. pose proof HW as (_ & _ & _ & _ & (_ & _ & Q4 & _) & _).
  assert (Q4' : Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg SB 24 i) G)
    by (apply (Permutation_Forall (Permutation_app_comm (ql Σ) (qg Σ))); exact Q4).
  unfold W_RH. apply Forall_app. split.
  - constructor; [left; exists (i_q_cmutex, i_q_cmutex + 4); split; [left; reflexivity | cbn; lia]|].
    constructor; [left; exists (i_q_global, i_q_global + 32); split; [right; left; reflexivity | cbn; lia]|].
    constructor; [right; left; exists (T + 80, T + 112); split; [left; reflexivity | cbn; lia]|].
    constructor.
    { right; right; left. apply in_map_iff in Hbl as (b & E & Hb). destruct (proj1 (Forall_forall _ _) Q4' b Hb) as (j & Hj & Eb).
      exists 24, j. split; [unfold bslots; apply in_map_iff; exists b; split; [rewrite Eb, bidx_abeg; reflexivity | exact Hb]|].
      cbn [fst snd]. rewrite <- E, Eb. change (ClassSize 24) with 8192. lia. }
    constructor; [do 9 right; cbn; lia | constructor].
  - apply Forall_forall. intros iv Hiv. right; right; left. exact (proj1 (Forall_forall _ _) (bslots_cover Σ G Q4') iv Hiv).
Qed.

Theorem rr_evt : evt ctasegs rh_post (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp).
Proof using HA HW HC HBY FR ST HLO HLO2 HSP MI HBYr.
  pose proof (xr_geo Σ HW) as (HG & X1 & X2 & X3 & X4 & X6 & X7 & X8 & X9). unfold SHB in X8.
  pose proof (xq_cells Σ m HA) as (QT & QGr & LK & QM).
  apply (proj1 (rwc_app ctasegs m q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661)] [C8 (Z_to_bv 64 0x100000)])) in QM.
  destruct QM as (QM & _).
  pose proof (qwf_of_wfx Σ HW) as WF.
  assert (Hne : ql Σ <> []) by (intros E; pose proof HBY as X; rewrite E in X; change (RT_state.qbytes []) with 0 in X; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2208)) = usp + -2208) by (apply unsigned_lit; lia).
  assert (STd : stk ctasegs m lo (bv_unsigned (Z_to_bv 64 (usp + -2208)))) by (rewrite Esp; exact ST).
  destruct rr_qg as (pre & bl & el & EQG).
  assert (Hbl : In bl (map fst G)) by (rewrite EQG; apply in_map_iff; exists (bl, el); split; [reflexivity | apply in_or_app; left; apply in_or_app; right; left; reflexivity]).
  eapply evt_cut; [exact (xr_head Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
                            w0 w1 w2 w3 w4 w5 s6 HA HW HBY FR ST HLO HLO2 HSP MI)|].
  intros ms0 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). unfold xr_dentry.
  pose proof QGr as QGr'. pose proof WF as WF'. pose proof HBYr as HBYr'. rewrite EQG in QGr', WF', HBYr'.
  assert (HBY2 : 0x10000000 < R_quar_defs.qbytes (pre ++ [(bl, el)]) + R_quar_defs.qbytes (ql Σ) < 2 ^ 56).
  { rewrite <- qbytes_app. split; [exact HBYr'|]. pose proof HW as (_ & _ & _ & _ & (Q1 & Q2 & _) & _).
    rewrite <- EQG, qbytes_app, <- !qbytes_eq. unfold QMAX_L, QMAX_G in *. lia. }
  eapply evt_cut; [apply (qdrain_rec_app_spec (Z_to_bv 64 0x1a02c4) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                             (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
                             t3' t4' t5' t6' F fc m (T + 80) SB (T + 208) (usp + -2128) lo pre (ql Σ) bl el Hne QGr' QT WF' HBY2 LK QM);
                    try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia);
                    [exact STd | exact MI]|].
  intros ms (u0 & u1 & u2 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & QG2 & QT2 & LK2 & ST2).
  rewrite Esp in MU2, ST2. rewrite <- EQG in QG2.
  assert (HBYG : R_quar_defs.qbytes G < 2 ^ 56) by (rewrite EQG, qbytes_app; lia).
  assert (ST2' : stk ctasegs m2 lo (bv_unsigned (Z_to_bv 64 (usp + -2208)))) by (rewrite Esp; exact ST2).
  eapply evt_mono; [apply (qrec_A_spec_closed (Z_to_bv 64 0x1a02c4) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) u0 u1 u2
                             (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) v4 v5 v6 v7 s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
                             u3 u4 u5 u6 F fc m2 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) QMIN SB lo G QG2 WF HBYG);
                    try (unfold QMIN; lia); try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia);
                    [exact LK2 | exact ST2' | exact MI2]|].
  intros ms (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & y3 & y4 & y5 & y6 & m3 & -> & MU3 & WM3 & MI3 & QG3 & TQ3 & LK3 & FR3 & ST3).
  rewrite Esp in MU3, ST3, TQ3, FR3. replace (usp + -2208 + -80) with (usp + -2288) in ST3, TQ3, FR3 by lia.
  rewrite Esp. replace (usp + -2208 + -80) with (usp + -2288) by lia.
  exists y0, y1, y2, z0, z1, z5, z6, z7, z8, z2, z3, z4, y3, y4, y5, y6, m3. split; [reflexivity|].
  (* [comment removed for export] *)
  assert (MU : munch (W_RH T usp bl G) m m3).
  { apply (munch_trans _ m m2 m3).
    - eapply munch_weaken; [|exact MU2]. intros x Hx. unfold W_RH in Hx. apply (proj1 (R_qrec_defs.outside_app _ _ _)) in Hx. destruct Hx as (Hx & _).
      cbn [outside] in Hx |- *. unfold i_q_cmutex, i_q_global, INST, g_instance in *. lia.
    - eapply munch_weaken; [|exact MU3]. intros x Hx. unfold W_RH in Hx. apply (proj1 (R_qrec_defs.outside_app _ _ _)) in Hx. destruct Hx as (Hx & Hb).
      apply (proj2 (R_qrec_defs.outside_app _ _ _)). split; [|exact Hb].
      cbn [outside] in Hx |- *. unfold i_q_cmutex, i_q_global, INST, g_instance in *. lia. }
  assert (WM : wmono ctasegs m m3) by exact (wmono_trans ctasegs _ _ _ WM2 WM3).
  pose proof (rr_cert bl Hbl) as CERT. pose proof (xr_TZ Σ) as (TZ1 & TZ2).
  pose proof HW as (_ & _ & HV & _ & (_ & _ & Q4 & _) & _ & _ & Hdep & _).
  assert (Q4' : Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg SB 24 i) G)
    by (apply (Permutation_Forall (Permutation_app_comm (ql Σ) (qg Σ))); exact Q4).
  pose proof (bslots_ok Σ G Q4') as HD.
  assert (HQ : quar_rep (set_q Σ [] (rec_r G QMIN)) m3).
  { unfold quar_rep. cbn [lay ql qg set_q]. split; [|split; [exact QG3 | exact LK3]].
    apply (qcache_rep_frame _ m2 m3 _ _ QT2 MU3 WM3); [|constructor].
    apply disjoint_from_app; [cbn [disjoint_from]; unfold qcacheT; unfold SEGTOP_A in *; repeat split; lia|].
    apply disjoint_bivs. apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) Q4' e He) as (j & Hj & Ej).
    pose proof (dk_slot_in Σ HG 24 j CkBatch ltac:(lia) Hj) as (S1 & S2 & _). pose proof (dk_T Σ HG) as (_ & _ & _ & _ & T5).
    pose proof (dk_geo Σ HG) as (_ & _ & _ & _ & _ & G6 & G7 & _). rewrite Ej. unfold qcacheT. change (ClassSize 24) with 8192 in *. lia. }
  split; [exact (artc_q Σ m m3 (W_RH T usp bl G) (bslots SB G) (TZ_X T) lo (usp + -2128) [] (rec_r G QMIN) HG HD TZ1 TZ2 HLO CERT HA Hdep MU WM HQ)|].
  split; [exact TQ3|]. split; [exact FR3|].
  split.
  { unfold qput_frame in *. apply (rw_cells_transport ctasegs _ m m3 _ _ FR MU WM). cbn [cells_size csize Nat.add Z.of_nat].
    pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    unfold W_RH. apply disjoint_from_app.
    - apply in_map_iff in Hbl as (b & Eb & Hb). destruct (proj1 (Forall_forall _ _) Q4' b Hb) as (j & Hj & Ej).
      pose proof (dk_slot_in Σ HG 24 j CkBatch ltac:(lia) Hj) as (S1 & S2 & _). rewrite <- Eb, Ej.
      cbn [disjoint_from]. unfold i_q_cmutex, i_q_global, INST, g_instance. change (ClassSize 24) with 8192 in *. unfold SHB in G1.
      repeat split; lia.
    - apply disjoint_bivs. apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) Q4' e He) as (j & Hj & Ej).
      pose proof (dk_slot_in Σ HG 24 j CkBatch ltac:(lia) Hj) as (S1 & S2 & _). rewrite Ej. change (ClassSize 24) with 8192 in *. lia. }
  split; [exact ST3|]. split; [exact MI3|]. split; [exact WM|].
  exact (client_q Σ m m3 (W_RH T usp bl G) (bslots SB G) (TZ_X T) lo (usp + -2128) HG HD TZ1 HLO ltac:(clear - HLO2; lia) CERT HV MU).
Qed.

End RRun.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_prim_kit R_quar_defs R_qput R_qdrain R_qrecycle RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freestmt RT_freeE RT_drain_defs RT_drain_pure RT_drain_led RT_drain_start RT_drain_kit RT_drain_art.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Definition W_D (T usp : Z) (bw : list ivl) : list ivl :=
  [(i_q_cmutex, i_q_cmutex + 4); (i_q_global, i_q_global + 32); (T + 80, T + 112)] ++ bw ++ [(usp - 2256, usp - 2208)].
Definition W_X (T usp : Z) (bw : list ivl) : list ivl := W_D T usp bw ++ [(usp - 2208, usp - 2128)].
Definition TZ_X (T : Z) : list ivl := [(T + 80, T + 112)].

Lemma xq_cells : forall Σ m, ARTc Σ m ->
  qcache_rep m (l_T (lay Σ) + 80) (ql Σ) /\ qcache_rep m QG (qg Σ) /\ q_lock m 0 0
  /\ rw_cells bsegs m q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)].
Proof.
  intros Σ m (A1 & _ & _ & _ & _ & (Q1 & Q2 & Q3) & _). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
  destruct A1 as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
  repeat match type of IC with _ /\ ?R => destruct IC as [?X IC] end.
  match goal with H : rw_cells bsegs m i_q_max _ |- _ => exact H end.
Qed.

Lemma qwf_of_wfx : forall Σ, rt_wfx Σ -> qwf (l_SB (lay Σ)) (qg Σ ++ ql Σ).
Proof.
  intros Σ (H1 & HR & HV & HS & (Q1 & Q2 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9) & _).
  assert (GQ : Permutation (ql Σ ++ qg Σ) (qg Σ ++ ql Σ)) by apply Permutation_app_comm.
  split; [apply (Permutation_NoDup (Permutation_map fst GQ)); apply NoDup_ListNoDup; exact Q5|].
  apply (Permutation_Forall GQ). apply Forall_forall. intros b Hb.
  destruct (proj1 (Forall_forall _ _) Q4 b Hb) as (i & Hi & Eb). pose proof (proj1 (Forall_forall _ _) Q6 b Hb) as Hl.
  pose proof HR as (HR1 & _). pose proof (HR1 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W11).
  pose proof H1 as (_ & _ & _ & _ & _ & HSB & _). change (ClassSize 24) with 8192 in W11.
  assert (Hlt : (i < length (r_st (pr Σ 24)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  unfold p_abeg in Eb. change (ClassSize 24) with 8192 in Eb. unfold r24.
  split; [rewrite Eb; apply Z.mod_divide; [lia|]; apply Z.mod_divide in HSB; [|lia]; destruct HSB as (q & Hq);
          exists (q * 8 + 24 * 2 ^ 19 + Z.of_nat i); lia|].
  split; [lia|]. split; [lia|]. split; [exact Hl|].
  apply Forall_forall. intros e He.
  assert (Hq : In e (qents Σ)) by (unfold qents; apply in_flat_map; exists b; split; [exact Hb | exact He]).
  pose proof (qent_n_pos Σ e HR HS (proj1 (Forall_forall _ _) Q7 e Hq)). lia.
Qed.

Definition dpost (fc : bv 32) (Σ' : rtsA) (gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 : word) (lo usp : Z) (live0 : list (Z * Z))
    (frames0 : list (Z * nat)) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 0x86460) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
                 a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0x86460) fc None m' (seg_rom bsegs)
    /\ ART_A Σ' m' /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo (usp + -2128) /\ rt_pres live0 frames0 (usp + -2128) m m'.

Section XRun.
Variables (Σ : rtsA) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word).
Hypothesis HA : ARTc Σ m.
Hypothesis HW : rt_wfx Σ.
Hypothesis HC : rt_count Σ.
Hypothesis HBY : 0x100000 < RT_state.qbytes (ql Σ).
Hypothesis FR : qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x86460)
                  w0 w1 w2 w3 w4 w5 s6.
Hypothesis ST : stk bsegs m lo (usp + -2208).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x4000 <= usp + -2208.
Hypothesis HSP : usp <= 2 ^ 47.
Hypothesis MI : mem_inv bsegs m.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma xr_geo : geo_ok Σ /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ (T + 4096 <= 0x10000 \/ SEGTOP_A <= T)
  /\ (T + 4096 <= r24 SB \/ r24 SB + 2 ^ 32 <= T) /\ 0 < SB /\ r24 SB + 2 ^ 32 <= l_ACEIL L /\ 2 ^ 44 + SHB <= l_ACEIL L
  /\ l_ACEIL L <= 2 ^ 47.
Proof using HW.
  clear - HW.
  assert (HG : geo_ok Σ) by (destruct HW as (H1 & H2 & _ & H4 & _ & H6 & _); exact (conj H1 (conj H2 (conj H4 H6)))).
  pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof (dk_T Σ HG) as (T1 & T2 & T3 & T4 & T5).
  unfold r24. split; [exact HG|]. repeat split; try lia.
Qed.

Definition xms0 : machine_state :=
  MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR) (Z_to_bv 64 (l_T (lay Σ) + 80))
          a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 0x633ec) fc None m (seg_rom bsegs).

Lemma xr_bytes : 0x100000 < R_quar_defs.qbytes (ql Σ) < 2 ^ 63.
Proof using HW HBY.
  clear - HW HBY. rewrite <- qbytes_eq. destruct HW as (_ & _ & _ & _ & (Q1 & _) & _). unfold QMAX_L in Q1. lia.
Qed.

Definition xr_dentry (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) : machine_state :=
  MS (mkR (Z_to_bv 64 0x63324) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
          (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) a4' a5' a6' a7'
          s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 qdrain_entry) fc None m (seg_rom bsegs).

Lemma xr_head : evt bsegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                                        ms = xr_dentry t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6') xms0.
Proof using HA HW HBY FR ST HLO HLO2 HSP MI.
  pose proof (xq_cells Σ m HA) as (QT & _). apply (proj1 (qcache_rep_iff _ _ _)) in QT. destruct QT as (QH & _).
  pose proof xr_bytes as HB. pose proof xr_geo as (_ & X1 & X2 & _ & _ & _ & _ & X8 & X9).
  assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
  unfold xms0. replace (usp + -2208) with (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80) by (rewrite Esp; lia).
  eapply evt_mono; [apply (qput_B_drain_spec (Z_to_bv 64 0x86460) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s2 s3 s4 s5
                             a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 s6 ra0 F fc m (T + 80) (T + 208)
                             (usp + -2128) (R_quar_defs.qbytes (ql Σ)) lo _ _ _ QH HB); [| exact MI]|].
  - rewrite Esp. replace (usp + -2128 - 80) with (usp + -2208) by lia. exact FR.
  - intros ms (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). rewrite Esp. replace (usp + -2128 + -80) with (usp + -2208) by lia.
    exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6'. reflexivity.
Qed.

Lemma xr_quar : forall (m2 m3 : mem) G, qcache_rep m2 QG G -> qcache_rep m2 (T + 80) [] -> q_lock m2 0 0 ->
  Forall (fun e => r24 SB <= fst e /\ fst e + 8192 <= r24 SB + 2 ^ 32) G ->
  munch [(usp + -2208, usp + -2128)] m2 m3 -> wmono bsegs m2 m3 -> quar_rep (set_q Σ [] G) m3.
Proof using HW HLO HLO2.
  intros m2 m3 G QG2 QT2 LK2 RG MU WM. pose proof xr_geo as (_ & X1 & X2 & _ & _ & X6 & X7 & X8 & X9). unfold SHB in X8.
  unfold quar_rep. cbn [lay ql qg set_q].
  split; [apply (qcache_rep_frame _ m2 m3 _ _ QT2 MU WM); [cbn [disjoint_from]; unfold qcacheT; lia | constructor]|].
  split; [apply (qcache_rep_frame _ m2 m3 _ _ QG2 MU WM); [cbn [disjoint_from]; lia|];
          apply Forall_forall; intros e He; pose proof (proj1 (Forall_forall _ _) RG e He) as (E1 & E2); cbn [disjoint_from]; lia|].
  unfold q_lock in LK2. apply (rw_cells_transport bsegs _ m2 m3 _ _ LK2 MU WM). cbn [disjoint_from cells_size csize Nat.add Z.of_nat].
  unfold i_q_cmutex, INST, g_instance. lia.
Qed.

Lemma xr_cert : forall bw D, Forall (fun iv => exists c i, In (c, i) D /\ p_abeg SB c i <= fst iv /\ snd iv <= p_abeg SB c i + ClassSize c) bw ->
  Forall (dzone Σ D [] [] (TZ_X T) IZ_Q [] lo (usp + -2128)) (W_X T usp bw).
Proof using HLO2.
  intros bw D HB. unfold W_X, W_D. rewrite <- !app_assoc. apply Forall_app. split; [|apply Forall_app; split].
  - constructor; [left; exists (i_q_cmutex, i_q_cmutex + 4); split; [left; reflexivity | cbn; lia]|].
    constructor; [left; exists (i_q_global, i_q_global + 32); split; [right; left; reflexivity | cbn; lia]|].
    constructor; [right; left; exists (T + 80, T + 112); split; [left; reflexivity | cbn; lia] | constructor].
  - apply Forall_forall. intros iv Hiv. right; right; left. exact (proj1 (Forall_forall _ _) HB iv Hiv).
  - constructor; [do 9 right; cbn; lia | constructor; [do 9 right; cbn; lia | constructor]].
Qed.

Lemma xr_TZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_X T)
  /\ disjoint_from (TZ_X T) T 0x50 /\ disjoint_from (TZ_X T) (T + 48) 16 /\ disjoint_from (TZ_X T) (T + 0xc60) 1
  /\ (forall c, 1 <= c <= 31 -> disjoint_from (TZ_X T) (pc_addr T c) 80).
Proof.
  unfold TZ_X. split; [repeat constructor; cbn; lia|]. cbn [disjoint_from]. split; [split; [lia | exact I]|].
  split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|]. intros c Hc. unfold pc_addr. split; [lia | exact I].
Qed.

Lemma xr_tail : forall bw D (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem),
  (forall c i, In (c, i) D -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch) ->
  Forall (fun iv => exists c i, In (c, i) D /\ p_abeg SB c i <= fst iv /\ snd iv <= p_abeg SB c i + ClassSize c) bw ->
  munch (W_D T usp bw) m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
  qcache_rep m2 QG (qg Σ ++ ql Σ) -> qcache_rep m2 (T + 80) [] -> q_lock m2 0 0 -> stk bsegs m2 lo (usp + -2208) ->
  R_quar_defs.qbytes (qg Σ ++ ql Σ) <= 0x10000000 ->
  evt bsegs (dpost fc (set_q Σ [] (qg Σ ++ ql Σ)) gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp (live Σ) (frames Σ) m)
    (MS (mkR (Z_to_bv 64 0x63324) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
             a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (ret_pc (Z_to_bv 64 0x63324)) fc None m2 (seg_rom bsegs)).
Proof using HA HW HC FR ST HLO HLO2 HSP MI.
  intros bw D t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 HD HB MU2 WM2 MI2 QG2 QT2 LK2 ST2 HBYg.
  pose proof xr_geo as (HG & X1 & X2 & X3 & X4 & X6 & X7 & X8 & X9). unfold SHB in X8.
  assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
  rewrite (ret_pc_even 0x63324) by (first [reflexivity | lia]).
  replace (usp + -2208) with (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80) by (rewrite Esp; lia).

  assert (FR2 : qput_frame m2 (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128))
                  (Z_to_bv 64 0x86460) w0 w1 w2 w3 w4 w5 s6).
  { rewrite Esp. replace (usp + -2128 - 80) with (usp + -2208) by lia. unfold qput_frame in *.
    apply (rw_cells_transport bsegs _ m m2 _ _ FR MU2 WM2). cbn [cells_size csize Nat.add Z.of_nat].
    unfold W_D. apply dsj_app; [cbn [disjoint_from]; unfold i_q_cmutex, i_q_global, INST, g_instance; repeat split; lia|].
    apply dsj_app; [|cbn [disjoint_from]; repeat split; lia].
    apply dsj_forall. apply Forall_forall. intros iv Hiv. destruct (proj1 (Forall_forall _ _) HB iv Hiv) as (c & i & HDi & E1 & E2).
    destruct (HD c i HDi) as (-> & Hb). pose proof (dk_slot_in Σ HG 24 i CkBatch ltac:(lia) Hb) as (S1 & S2 & _).
    pose proof (dk_geo Σ HG) as (_ & _ & _ & G4 & _ & _ & G7 & _). lia. }
  assert (ST2' : stk bsegs m2 lo (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80)) by (rewrite Esp; replace (usp + -2128 - 80) with (usp + -2208) by lia; exact ST2).
  eapply evt_mono; [apply (qput_C_spec (Z_to_bv 64 0x86460) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                             (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000)
                             s7 s8 s9 s10 s11 t3' t4' t5' t6' (Z_to_bv 64 0x63324) w0 w1 w2 w3 w4 w5 s6
                             (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) F fc m2 lo FR2 ST2'); [rewrite Esp; lia | unfold SEGTOP_A in *; lia | exact MI2]|].
  intros ms (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
  rewrite Esp in MU3, ST3. replace (usp + -2128 - 80) with (usp + -2208) in MU3 by lia.
  rewrite (ret_pc_even 0x86460) by (first [reflexivity | lia]).

  assert (MU : munch (W_X T usp bw) m m3).
  { apply (munch_trans _ m m2 m3); [apply (munch_weaken (W_D T usp bw)); [|exact MU2] | apply (munch_weaken [(usp + -2208, usp + -2128)]); [|exact MU3]].
    - intros x Hx. unfold W_X in Hx. apply (proj1 (R_qrec_defs.outside_app _ _ _)) in Hx. exact (proj1 Hx).
    - intros x Hx. unfold W_X in Hx. apply (proj1 (R_qrec_defs.outside_app _ _ _)) in Hx. destruct Hx as (_ & Hx). cbn [outside] in Hx |- *. lia. }
  assert (WM : wmono bsegs m m3) by exact (wmono_trans bsegs _ _ _ WM2 WM3).
  pose proof (xr_cert bw D HB) as CERT. pose proof xr_TZ as (TZ1 & TZ2).
  assert (HD' : forall c i, In (c, i) D -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch) by exact HD.
  pose proof HW as (_ & _ & HV & _ & _ & _ & _ & Hdep & _).
  assert (HQ : quar_rep (set_q Σ [] (qg Σ ++ ql Σ)) m3).
  { apply (xr_quar m2 m3 _ QG2 QT2 LK2); [|exact MU3 | exact WM3].
    pose proof (qwf_region _ _ (qwf_of_wfx Σ HW)) as RG. exact RG. }
  unfold dpost. exists u0, u1, u2, v0, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, F, m3. split; [reflexivity|].
  split; [apply c_ART; [exact (rt_wf_transfer Σ HW HC ltac:(rewrite qbytes_eq; unfold QMAX_G; lia)) |]
         | split; [exact MI3 | split; [exact WM | split; [exact ST3|]]]].
  - exact (artc_q Σ m m3 (W_X T usp bw) D (TZ_X T) lo (usp + -2128) [] (qg Σ ++ ql Σ) HG HD' TZ1 TZ2 HLO CERT HA Hdep MU WM HQ).
  - exact (client_q Σ m m3 (W_X T usp bw) D (TZ_X T) lo (usp + -2128) HG HD' TZ1 HLO ltac:(clear - HLO2; lia) CERT HV MU).
Qed.

Theorem xfer_evt : R_quar_defs.qbytes (qg Σ ++ ql Σ) <= 0x10000000 ->
  evt bsegs (dpost fc (set_q Σ [] (qg Σ ++ ql Σ)) gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp (live Σ) (frames Σ) m) xms0.
Proof using HA HW HC HBY FR ST HLO HLO2 HSP MI.
  intros HBYg. pose proof xr_geo as (HG & X1 & X2 & X3 & X4 & X6 & X7 & X8 & X9). unfold SHB in X8.
  pose proof (xq_cells Σ m HA) as (QT & QGr & LK & QM).
  apply (proj1 (rwc_app bsegs m q_max [C8 (Z_to_bv 64 0x10000000)] [C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)])) in QM.
  destruct QM as (QM & _).
  pose proof (qwf_of_wfx Σ HW) as WF.
  assert (Hne : ql Σ <> []) by (intros E; pose proof HBY as X; rewrite E in X; change (RT_state.qbytes []) with 0 in X; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2208)) = usp + -2208) by (apply unsigned_lit; lia).
  assert (STd : stk bsegs m lo (bv_unsigned (Z_to_bv 64 (usp + -2208)))) by (rewrite Esp; exact ST).
  eapply evt_cut; [exact xr_head|]. intros ms0 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). unfold xr_dentry.
  assert (CASE : qg Σ = [] \/ exists pre bl el, qg Σ = pre ++ [(bl, el)]).
  { destruct (qg Σ) as [|b0 rest] eqn:E; [left; reflexivity | right].
    destruct (exists_last (l := b0 :: rest) ltac:(discriminate)) as (pre & (bl & el) & E2). exists pre, bl, el. exact E2. }
  destruct CASE as [EQG|(pre & bl & el & EQG)].
  -
    pose proof QGr as QGr'. pose proof WF as WF'. pose proof HBYg as HBYg'. rewrite EQG in QGr', WF', HBYg'. cbn [app] in WF', HBYg'.
    eapply evt_cut; [apply (qdrain_ret_empty_spec (Z_to_bv 64 0x63324) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                               (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
                               t3' t4' t5' t6' F fc m (T + 80) SB (T + 208) (usp + -2128) lo (ql Σ) Hne QGr' QT WF' HBYg' LK QM);
                      try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia); [exact STd | exact MI]|].
    intros ms (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & QG2 & QT2 & LK2 & ST2).
    rewrite Esp in MU2, ST2.
    apply (xr_tail [] [] u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 (fun c i X => False_ind _ X) (Forall_nil _)); try assumption.
    + eapply munch_weaken; [|exact MU2]. unfold W_D, i_q_cmutex, i_q_global, INST, g_instance. cbn [app]. solve_sub_fp.
    + rewrite EQG. exact QG2.
  -
    pose proof QGr as QGr'. pose proof WF as WF'. pose proof HBYg as HBYg'. rewrite EQG in QGr', WF', HBYg'.
    assert (Hbl : exists ib, nth_error (r_st (pr Σ 24)) ib = Some CkBatch /\ bl = p_abeg SB 24 ib).
    { destruct HW as (_ & _ & _ & _ & (_ & _ & Q4 & _) & _). rewrite EQG in Q4.
      exact (proj1 (Forall_forall _ _) Q4 (bl, el) ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)). }
    destruct Hbl as (ib & Hib & Ebl).
    eapply evt_cut; [apply (qdrain_ret_app_spec (Z_to_bv 64 0x63324) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                               (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
                               t3' t4' t5' t6' F fc m (T + 80) SB (T + 208) (usp + -2128) lo pre (ql Σ) bl el Hne QGr' QT WF');
                      try (rewrite qbytes_app in HBYg'; exact HBYg');
                      try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia);
                      [exact LK | exact QM | exact STd | exact MI]|].
    intros ms (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & QG2 & QT2 & LK2 & ST2).
    rewrite Esp in MU2, ST2.
    apply (xr_tail [(bl, bl + 8)] [(24, ib)] u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2); try assumption.
    + intros c i [E|[]]. injection E as <- <-. split; [reflexivity | exact Hib].
    + constructor; [|constructor]. exists 24, ib. split; [left; reflexivity|]. cbn [fst snd]. rewrite Ebl. change (ClassSize 24) with 8192. lia.
    + eapply munch_weaken; [|exact MU2]. unfold W_D, i_q_cmutex, i_q_global, INST, g_instance. cbn [app]. solve_sub_fp.
    + rewrite EQG. exact QG2.
Qed.

End XRun.

Definition dfinal (fc : bv 32) (Σ : rtsA) (PMc : Model -> Prop) (gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 : word) (lo usp : Z) (m : mem) :
  config -> Prop :=
  fun cf => exists Σ' : rtsA,
    ASTA RTA Σ' PMc (dpost fc Σ' gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp (live Σ) (frames Σ) m) cf
    /\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ /\ ann Σ' = ann Σ.

Theorem drain_xfer : forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11
         t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
  fdfs_only PMc -> mat_stable PMc ->
  ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < RT_state.qbytes (ql Σ) ->
  qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x86460) w0 w1 w2 w3 w4 w5 s6 ->
  stk bsegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
  mem_inv bsegs m ->
  R_quar_defs.qbytes (qg Σ ++ ql Σ) <= 0x10000000 ->
  cps bsegs (ASTA RTA Σ PMc (eq (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp)))
    (dfinal fc Σ PMc gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp m).
Proof.
  intros Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
    FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI HBYg.
  intros TT cf Hc0 Hk.
  pose proof (xfer_evt Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
                w0 w1 w2 w3 w4 w5 s6 HA HW HC HBY FR ST HLO HLO2 HSP MI HBYg) as W1.
  lazymatch type of W1 with evt bsegs _ ?X => assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc0).
  intros c1 Hc1. apply Hk. exists (set_q Σ [] (qg Σ ++ ql Σ)).
  split; [|split; [reflexivity | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
  unfold ASTA. eapply AST_conseq; [exact Hc1| |].
  - intros ms P. exact P.
  - intros mo (HM & HP). split; [|exact HP]. cbn [ARTM RTA]. apply (artm_eq Σ); [reflexivity | reflexivity | reflexivity | exact HM].
Qed.

End GWIN.

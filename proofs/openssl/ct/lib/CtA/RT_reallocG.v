(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_leaves R_setshadow R_sec_defs R_depot_defs R_fs_defs R_unwind_defs R_asan_defs R_allocate1 R_tlsgetaddr R_quar_defs R_qput R_qenqueue R_asan_malloc R_asan_free R_asan_realloc R_prim_kit R_intalloc I_lkit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_artfacts RT_malpre RT_malstate RT_maltail RT_freelift RT_malloc RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_freeI RT_freeJ RT_freeK RT_freeL RT_freeM RT_freeN RT_freeS RT_freeT RT_freeU RT_freeV RT_freeW RT_freeX RT_freeY RT_freeZ RT_refillstmt RT_sys_stmt RT_reatail RT_reacore_stmt RT_reacore_m RT_reafront R_unwind_chain RT_sites RT_refreekA RT_refreekC RT_refreekD RT_refreekL RT_refreekH RT_refreeG RT_refreeA2 RT_refreeV RT_refreeW RT_refreeX RT_refreeH RT_refreeY RT_drain_kit RT_freeSA RT_freeSA2 RT_freeSA3 RT_refreeSA RT_refreeSA2 RT_refreeSA3 RT_reacore_case RT_realloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmt.
Variable RT : rt_sig.
(* [comment removed for export] *)
Definition realloc_contract_any : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n0 n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n0) (rt_live RT Σ) -> 1 <= n <= 0x8000000 ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba93f0 ->
  live_room (rt_live RT Σ) n -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_realloc m)))
            (realloc_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p n0 n lo m).
End Stmt.

(* [comment removed for export] *)
Definition rcore_stmt_all : Prop := rcore_case (fun _ => True).

Lemma rcore_all_of : rcore_case (fun n => n <= 64512) -> rcore_stmt_sec -> rcore_stmt_all.
Proof.
  intros HP HS. unfold rcore_stmt_all, rcore_stmt_sec, rcore_case in *.
  intros Σ PMc mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo tr tb j0 FDO MST _ Hn.
  destruct (Z.le_gt_cases n 64512) as [H|H].
  - exact (HP Σ PMc mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo tr tb j0 FDO MST H Hn).
  - exact (HS Σ PMc mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo tr tb j0 FDO MST H Hn).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_any_geo : forall (Σ : rtsA) (m : mem) p n lo, ART_A Σ m -> In (p, n) (live Σ) -> l_ACEIL (lay Σ) <= lo ->
  exists A S, wr_at ctasegs m A S /\ ahdr m (p - 16) n /\ A + 16 <= p /\ p + n <= A + S /\ A + S <= lo /\ 0 <= A
    /\ 1 <= n < 2 ^ 32 /\ (p + n <= 0x10000 \/ SEGTOP_A <= p).
Proof.
  intros Σ m p n lo HA Hin HLO.
  pose proof (af_live_range RTA rta_art_facts Σ m p n HA Hin) as (Hp0 & _ & HpR).
  destruct (ART_chunk Σ m HA) as [CP CS].
  destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hni & Ep & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & Hq & Hsn & Ep & Y1 & Y2)].
  - (* [comment removed for export] *)
    pose proof (CP c i (CkAlloc n) Hc Hni) as (WrA & HD & _).
    pose proof (ART_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hni)) as X. cbv beta iota in X.
    assert (Hn1 : 1 <= n) by (clear - X; lia).
    pose proof (sa_geo Σ m c i n HA Hc Hni Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
    & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
    pose proof (ClassSize_range c Hc) as (CR & _).
    exists (p_abeg (l_SB (lay Σ)) c i), (ClassSize c).
    split; [exact WrA|].
    split; [replace (p - 16) with (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) by (rewrite Ep; unfold p_ubeg; clear; lia); exact HD|].
    split; [exact Y1|]. split; [exact Y2|]. split; [clear - K4 K39 HLO; lia|]. split; [clear - K7 K29; lia|].
    split; [clear - Hn1 K11 K12 K14 CR; lia | exact HpR].
  - (* [comment removed for export] *)
    destruct (In_nth_error _ _ Hs) as (k & Hk).
    pose proof (CS k s Hk) as X. unfold schunk in X. rewrite Hq in X. destruct X as (_ & WrS & _ & HD & _).
    pose proof (ss_geo Σ m k s HA Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
    & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
    pose proof (geo_of_ART Σ m HA) as HG. pose proof HG as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
    pose proof (proj1 (Forall_forall _ _) HSF s Hs) as ((Hn1 & Hn2) & _).
    exists (s_mb s), (smsz (s_n s)).
    split; [exact WrS|].
    split; [rewrite Ep, <- Hsn; replace (s_ubeg s - 16) with (s_mb s + 4096 + 2032) by (unfold s_ubeg; clear; lia); exact HD|].
    rewrite Ep, <- Hsn. unfold s_ubeg. rewrite <- Hsn in HpR. rewrite Ep in HpR. unfold s_ubeg in HpR.
    split; [clear; lia|]. split; [clear - K16 K17; lia|]. split; [clear - K8 HLO; lia|]. split; [clear - K7; lia|].
    split; [clear - Hn1 Hn2; lia | exact HpR].
Qed.

Lemma rb_midG : forall (Σ' : rtsA) (LV : list (Z * Z)) (m2 : mem) (p q n n0 B lo usp : Z)
    (ra0 sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  ART_A Σ' m2 -> mem_inv ctasegs m2 -> live Σ' = (q, n) :: LV -> In (p, n0) LV -> 1 <= n <= 0x8000000 ->
  l_ACEIL (lay Σ') <= lo -> lo <= usp -> usp <= 2 ^ 47 -> rtA_sp0 Σ' - STACK_WIN <= usp ->
  evt ctasegs (fun ms => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (src : list byte) (m3 : mem),
               ms = MS (mkR (Z_to_bv 64 0x19c930) sp gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 B) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 p)
                            (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 B) (Z_to_bv 64 1) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
                            s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 deallocate_entry) fc None m3 (seg_rom ctasegs)
               /\ munch [(q, q + Z.min n n0)] m2 m3 /\ wmono ctasegs m2 m3 /\ mem_inv ctasegs m3 /\ ART_A Σ' m3
               /\ bytes_at ctasegs m2 p src /\ length src = Z.to_nat (Z.min n n0) /\ bytes_at ctasegs m3 q src)
    (MS (mkR ra0 sp gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 B) (Z_to_bv 64 p) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 INST) (Z_to_bv 64 n) s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19c89c) fc None m2 (seg_rom ctasegs)).
Proof.
  intros Σ' LV m2 p q n n0 B lo usp ra0 sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    ART2 MI2 HL Hin Hn HLO HLU HU47 Hsp'.
  assert (Hinq : In (q, n) (live Σ')) by (rewrite HL; left; reflexivity).
  assert (Hinp : In (p, n0) (live Σ')) by (rewrite HL; right; exact Hin).
  destruct (live_any_geo Σ' m2 p n0 lo ART2 Hinp HLO) as (Ap & Sp & WrA & (b1 & ctx & Hb1 & HD) & Hpa & Hpb & Hplo & HAp & Hn0 & HpR).
  destruct (live_any_geo Σ' m2 q n lo ART2 Hinq HLO) as (Aq & Sq & WrQ & _ & Hqa & Hqb & Hqlo & HAq & _ & HqR).
  pose proof (af_live_disj RTA rta_art_facts Σ' m2 q n p n0 [] LV ART2 HL Hin) as DJ.
  (* [comment removed for export] *)
  pose proof (ART_consts Σ' m2 ART2) as (_ & _ & _ & _ & _ & _ & _ & ICR). destruct (ic_memcpy_got _ _ ICR) as (G1 & G2).
  set (k := Z.min n n0) in *.
  assert (Hk : 1 <= k <= n /\ k <= n0) by (unfold k; clear - Hn Hn0; lia).
  destruct (fl_CB_of_wr m2 _ _ p (Z.to_nat k) WrA ltac:(clear - Hpa; lia) ltac:(clear - Hpb Hk; lia)) as (src & SRC).
  destruct (fl_CB_of_wr m2 _ _ q (Z.to_nat k) WrQ ltac:(clear - Hqa; lia) ltac:(clear - Hqb Hk; lia)) as (junk & DST).
  pose proof SRC as ((WF & SB0) & _). cbn [cells_wf cell_wf] in WF. destruct WF as (LS & _).
  cbn [cells_bytes cbytes] in SB0. rewrite app_nil_r in SB0.
  eapply evt_mono.
  { apply (realloc_M_spec ra0 sp gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 p q n n0 B b1 ctx src junk);
      try assumption; fold k.
    all: lazymatch goal with
         | |- rw_cells _ _ (?x + -16) _ => replace (x + -16) with (p - 16) by (clear; lia); exact HD
         | |- rw_cells _ _ _ [CB _ _] => exact DST
         | |- _ \/ _ => clear - DJ Hk; lia
         | |- _ => clear - Hpa Hpb Hplo HAp Hn0 Hqa Hqb Hqlo HAq Hn Hk HLU HU47; lia
         end. }
  intros ms (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3). fold k in MU3, DST3 |- *.
  exists t0', t1', t2', a6', a7', t3', t4', t5', t6', src, m3. split; [reflexivity|].
  split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|].
  split.
  { (* [comment removed for export] *)
    assert (MUC : munch (W_client Σ' usp) m2 m3).
    { eapply (munch_weaken _ _ m2 m3); [|exact MU3]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (X1 & X2). split; [|exact I].
      intros Hqx. destruct (outside_app_inv _ _ _ X2) as (_ & X3). destruct (outside_app_inv _ _ _ X3) as (X4 & _).
      refine (not_outside _ q (q + n) x _ ltac:(lia) X4). rewrite HL. left. reflexivity. }
    exact (ART_transport _ Σ' m2 m3 ART2 MUC WM3 (art_avoid_client Σ' m2 usp ART2 Hsp')). }
  split; [exact SB0|]. split; [exact LS|].
  destruct DST3 as ((_ & DB) & _). cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rsegS_post (Σ : rtsA) (k : nat) (s : secst) (tr : list Z) (ra vsp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms = enq_entry_st_r (bv_unsigned vsp) (l_T (lay Σ)) (s_mb s + 6128) (s_n s) gp t0' t1' t2' a5' a6' a7'
           s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m'
    /\ ARTc (free_s Σ k s (fst (depot_put (dep Σ) tr))) m'
    /\ mem_inv ctasegs m' /\ wmono ctasegs m m' /\ stk ctasegs m' lo (bv_unsigned vsp + -2208)
    /\ rt_pres (live_remove (s_ubeg s) (live Σ)) (frames Σ) (bv_unsigned vsp) m m'
    /\ ricpt_frame m' (bv_unsigned vsp) ra s0 s1 s2 s3 s4 s5
    /\ qput_frame m' (bv_unsigned vsp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 0x19c930)
         s0 (Z_to_bv 64 (s_mb s + 6128 + 16)) s2 s3 s4 s5 s6.

Lemma rb_segS : forall (Σ : rtsA) (m : mem) (k : nat) (s : secst) (lo : Z) (tr : list Z) (tb : list word)
    (ra vsp gp t0 t1 t2 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  ART_A Σ m -> nth_error (sec Σ) k = Some s -> s_quar s = false ->
  l_ACEIL (lay Σ) + 0xFFB0 <= bv_unsigned vsp -> bv_unsigned vsp + 16 <= USTACK_TOP -> l_ACEIL (lay Σ) <= lo -> lo + 0xFFB0 <= bv_unsigned vsp ->
  stk ctasegs m lo (bv_unsigned vsp + -2128) -> mem_inv ctasegs m ->
  rw_cells ctasegs m (bv_unsigned vsp + -2056) [C8 (Z_to_bv 64 (bv_unsigned vsp + -2040)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))] ->
  u64arr ctasegs m (bv_unsigned vsp + -2040) (wr_trace tr tb) -> length tb = 255%nat ->
  In tr T_MAIN /\ (1 <= length tr <= TR_MAX)%nat ->
  ricpt_frame m (bv_unsigned vsp) ra s0 s1 s2 s3 s4 s5 ->
  evt ctasegs (rsegS_post Σ k s tr ra vsp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (bv_unsigned vsp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0 (Z_to_bv 64 (s_ubeg s))
             (Z_to_bv 64 INST) (Z_to_bv 64 (s_ubeg s)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 1) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros Σ m k s lo tr tb ra vsp gp t0 t1 t2 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    ART0 Hk Hq Hsp Husp HLO HLO2 ST MI BC TB HTB Htr ICF.
  set (usp := bv_unsigned vsp) in *.
  pose proof (ss_geo Σ m k s ART0 Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
  replace (s_ubeg s) with (s_mb s + 6128 + 16) by (unfold s_ubeg; clear; lia).
  eapply evt_mono.
  { destruct K10 as [HL|HH].
    - exact (segA_run_sL_r Σ m k s usp lo tr tb ART0 Hk Hq HL Hsp Husp HLO HLO2 ST MI BC TB HTB Htr
               gp t0 t1 t2 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc).
    - exact (segA_run_s_r Σ m k s usp lo tr tb ART0 Hk Hq HH Hsp Husp HLO HLO2 ST MI BC TB HTB Htr
               gp t0 t1 t2 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc). }
  intros ms P. destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m' & -> & ART' & MI' & WM' & MW' & ST' & FR').
  unfold rsegS_post. exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, m'. split; [reflexivity|].
  split; [exact ART'|]. split; [exact MI'|]. split; [exact WM'|]. split; [exact ST'|]. split.
  { intros a Ha. exact (MW' a (ss_client_r Σ m k s usp ART0 Hk Hsp _ Ha)). }
  split; [|exact FR'].
  apply (ricpt_frame_transport (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (s_mb s + 6128) (s_n s) usp)
           m m' usp ra s0 s1 s2 s3 s4 s5 ICF MW' WM').
  unfold W_A1. cbn [disjoint_from].
  clear - K8 K15 K16 K17 K18 K21 K22 K23 K25 K28 K31 K32 Hsp. unfold SHB in *. repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BackG.
Variables (Σ : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m1 : mem) (p n0 n lo : Z)
          (tr : list Z) (tb : list word) (jp jq jr : list byte).
Hypothesis DRAIN : drain_stmt_r.
Hypothesis FC : fixed_commit_node.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis Hin : In (p, n0) (live Σ).
Hypothesis Hn : 1 <= n <= 0x8000000.
Hypothesis HA : ART_A Σ m.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x10000 <= bv_unsigned sp.
Hypothesis SPT : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis Htr : In tr T_MAIN /\ (1 <= length tr <= TR_MAX)%nat.
Hypothesis MU1 : munch (W_fr (l_T (lay Σ)) (bv_unsigned sp)) m m1.
Hypothesis WM1 : wmono ctasegs m m1.
Hypothesis IC1 : rw_cells ctasegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis IC2 : rw_cells ctasegs m1 (bv_unsigned sp + -72) [CB 8 jp].
Hypothesis IC3 : rw_cells ctasegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))].
Hypothesis TB1 : u64arr ctasegs m1 (bv_unsigned sp + -2120) (wr_trace tr tb).
Hypothesis HTB : length tb = 255%nat.
Hypothesis IC4 : rw_cells ctasegs m1 (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))].
Hypothesis IC5 : rw_cells ctasegs m1 (bv_unsigned sp + -2144) [CB 8 jq].
Hypothesis IC6 : rw_cells ctasegs m1 (bv_unsigned sp + -2152) [C8 (Z_to_bv 64 0x1c4880)].
Hypothesis IC7 : rw_cells ctasegs m1 (bv_unsigned sp + -2160) [CB 8 jr].
Hypothesis IC8 : rw_cells ctasegs m1 (bv_unsigned sp + -2208)
                   [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 realloc_pc); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x19c820)].
#[local] Notation usp := (bv_unsigned sp).

Theorem rback_cpsG : cps ctasegs (rcore_post Σ PMc (usp + -2136) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
                                          (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 n lo m1)
                              (realloc_post RTA Σ PMc ra sp gp (Z_to_bv 64 0xba93f0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p n0 n lo m).
Proof using DRAIN FC FDO MST Hin Hn HA LOW LOR SPT Htr MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 IC5 IC6 IC7 IC8.
  intros TT c2 Hc2 Hk. destruct Hc2 as (Σ' & q & HAST & HL & HF & HS & HCR & Hq0 & Hq16 & HqU).
  (* [comment removed for export] *)
  unfold ASTA in HAST. apply AST_exI in HAST as (m2 & HAST).
  pose proof HAST as (_ & (RET & ART2 & MI2 & WM2 & ST2 & PR2 & WR2 & AC2) & _ & _).
  destruct RET as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & Ems).
  rewrite (ret_pc_even 0x19c89c) in Ems by (lia || reflexivity).
  replace (usp + -2136 + -72) with (usp + -2208) in * by lia.
  assert (HACE : l_ACEIL (lay Σ') = l_ACEIL (lay Σ)) by (unfold l_ACEIL; unfold rtA_sp0 in HS; rewrite HS; reflexivity).
  assert (HLO' : l_ACEIL (lay Σ') <= lo) by (rewrite HACE; exact LOW).
  assert (Hinp : In (p, n0) (live Σ')) by (rewrite HL; right; exact Hin).
  assert (Hinq : In (q, n) (live Σ')) by (rewrite HL; left; reflexivity).
  pose proof (af_live_disj RTA rta_art_facts Σ' m2 q n p n0 [] (live Σ) ART2 HL Hin) as DJ.
  destruct (live_any_geo Σ' m2 p n0 lo ART2 Hinp HLO') as (Ap & Sp & _ & _ & _ & Hpb & HpA & _ & Hn0 & HpR).
  assert (Hplo : p + n0 <= lo) by (clear - Hpb HpA; lia). clear Ap Sp Hpb HpA.
  destruct (live_any_geo Σ' m2 q n lo ART2 Hinq HLO') as (Aq & Sq & _ & _ & _ & Hqb & HqA & _ & _ & HqR).
  assert (Hqlo : q + n <= lo) by (clear - Hqb HqA; lia). clear Aq Sq Hqb HqA.
  assert (Hqp : q <> p) by (clear - DJ Hn Hn0; lia).
  assert (Hc2' : AST SEGTOP_A (rtA_allow Σ')
                   (eq (MS (mkR (Z_to_bv 64 0x19c89c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p)
                                (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136))
                                (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x19c89c) fc' None m2 (seg_rom ctasegs)))
                   (fun mo => ARTM_A Σ' mo /\ PMc mo) c2).
  { destruct HAST as (H1 & _ & H3 & H4). split; [exact H1|]. split; [exact (eq_sym Ems)|]. split; [exact H3 | exact H4]. }
  (* [comment removed for export] *)
  assert (WMd : forall ms, eq (MS (mkR (Z_to_bv 64 0x19c89c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p)
                                (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136))
                                (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x19c89c) fc' None m2 (seg_rom ctasegs)) ms -> evt ctasegs _ ms)
    by (intros ms <-; exact (rb_midG Σ' (live Σ) m2 p q n n0 (usp + -2136) lo (usp + -2208) (Z_to_bv 64 0x19c89c) (Z_to_bv 64 (usp + -2208)) gp t0 t1 t2
                               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F' fc'
                               ART2 MI2 HL Hin Hn HLO' ltac:(clear - LOR; lia) ltac:(clear - SPT; unfold USTACK_TOP in *; lia)
                               ltac:(change (rtA_sp0 Σ' - STACK_WIN) with (l_ACEIL (lay Σ')); clear - HLO' LOR; lia))).
  apply (cps_realizes ctasegs _ _ _ c2 (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) WMd) Hc2').
  intros c3 Hc3.
  apply AST_exI in Hc3 as (t0' & Hc3). apply AST_exI in Hc3 as (t1' & Hc3). apply AST_exI in Hc3 as (t2' & Hc3). apply AST_exI in Hc3 as (a6' & Hc3).
  apply AST_exI in Hc3 as (a7' & Hc3). apply AST_exI in Hc3 as (t3' & Hc3). apply AST_exI in Hc3 as (t4' & Hc3). apply AST_exI in Hc3 as (t5' & Hc3).
  apply AST_exI in Hc3 as (t6' & Hc3). apply AST_exI in Hc3 as (src & Hc3). apply AST_exI in Hc3 as (m3 & Hc3).
  pose proof Hc3 as (_ & (Ems3 & MU3 & WM3 & MI3 & ART3 & SRC2 & LSRC & DST3) & _ & _).
  (* [comment removed for export] *)
  assert (AG13 : forall a : word, usp + -2208 <= bv_unsigned a < USTACK_TOP -> m3 a = m1 a).
  { intros a Ha. rewrite (MU3 a) by (cbn [outside]; split; [clear - Ha Hqlo LOR Hn Hn0; lia | exact I]). apply PR2. left. exact Ha. }
  assert (AGc : forall A (cs : list cell), usp + -2208 <= A -> A + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs m1 A cs -> rw_cells ctasegs m3 A cs).
  { intros A cs H1 H2 H. apply (rw_cells_agree_nw ctasegs m1 m3 _ _ H). intros a Ha. apply AG13. lia. }
  pose proof IC1 as IC1'. apply AGc in IC1'; [| clear; lia | cbn [cells_size csize Nat.add]; clear - SPT; lia].
  pose proof IC2 as IC2'. apply AGc in IC2'; [| clear; lia | cbn [cells_size csize Nat.add]; clear - SPT; lia].
  pose proof IC3 as IC3'. apply AGc in IC3'; [| clear; lia | cbn [cells_size csize Nat.add]; clear - SPT; lia].
  pose proof IC4 as IC4'. apply AGc in IC4'; [| clear; lia | cbn [cells_size csize Nat.add]; clear - SPT; lia].
  pose proof IC5 as IC5'. apply AGc in IC5'; [| clear; lia | cbn [cells_size csize Nat.add]; clear - SPT; lia].
  pose proof IC6 as IC6'. apply AGc in IC6'; [| clear; lia | cbn [cells_size csize Nat.add]; clear - SPT; lia].
  pose proof IC7 as IC7'. apply AGc in IC7'; [| clear; lia | cbn [cells_size csize Nat.add]; clear - SPT; lia].
  pose proof IC8 as IC8'. apply AGc in IC8'; [| clear; lia | cbn [cells_size csize Nat.add]; clear - SPT; lia].
  assert (TB1' : u64arr ctasegs m3 (usp + -2120) (wr_trace tr tb)).
  { apply (u64arr_agree_nw ctasegs m1 m3 _ _ TB1). intros a Ha. apply AG13. rewrite wr_trace_length in Ha by (rewrite HTB; clear - Htr; destruct Htr as (_ & X); lia).
    rewrite HTB in Ha. clear - Ha SPT. lia. }
  assert (ST3 : stk ctasegs m3 lo (usp + -2208)).
  { apply (stk_transport_disjoint ctasegs _ m2 m3 lo (usp + -2208) ST2 MU3 WM3). cbn [disjoint_from]. split; [clear - Hqlo Hn Hn0; lia | exact I]. }
  (* [comment removed for export] *)
  set (vsp := Z_to_bv 64 (usp - 80)).
  assert (Evsp : bv_unsigned vsp = usp - 80) by (apply unsigned_lit; clear - LOR LOW SPT HA; pose proof (rta_sp0_win Σ m HA); unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia).
  assert (ICF3 : ricpt_frame m3 (bv_unsigned vsp) ra s0 s1 s2 s3 s4 s5).
  { rewrite Evsp. unfold ricpt_frame.
    replace (usp - 80 + -2128) with (usp + -2208) by lia. replace (usp - 80 + -2080) with (usp + -2160) by lia.
    replace (usp - 80 + -2072) with (usp + -2152) by lia. replace (usp - 80 + -2064) with (usp + -2144) by lia.
    replace (usp - 80 + -2056) with (usp + -2136) by lia. replace (usp - 80 + -2040) with (usp + -2120) by lia.
    split; [do 5 eexists; exact IC8'|]. split; [eexists; exact IC7'|]. split; [exact IC6'|]. split; [eexists; exact IC5'|].
    split; [eexists; exact IC4'|]. exists (wr_trace tr tb). split; [exact TB1'|].
    rewrite wr_trace_length; [exact HTB|]. rewrite HTB. destruct Htr as (_ & X). lia. }
  (* [comment removed for export] *)
  destruct (fe_dep Σ' m3 tr ART3 Htr) as (Dok & Dinv).
  assert (STAGE : forall (Σ1 : rtsA) (M : Z) c4 (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : word) (m4 : mem),
            rt_wf0 Σ1 -> pend_e Σ1 M n0 -> live Σ1 = live_remove p (live Σ') -> frames Σ1 = frames Σ' -> lay Σ1 = lay Σ' -> credit Σ1 = credit Σ' ->
            ARTc Σ1 m4 -> mem_inv ctasegs m4 -> wmono ctasegs m3 m4 -> stk ctasegs m4 lo (bv_unsigned vsp + -2208) ->
            rt_pres (live Σ1) (frames Σ1) (bv_unsigned vsp) m3 m4 ->
            ricpt_frame m4 (bv_unsigned vsp) ra (Z_to_bv 64 (bv_unsigned vsp + -2056)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
              (Z_to_bv 64 (bv_unsigned vsp + -2056)) ->
            qput_frame m4 (bv_unsigned vsp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 0x19c930)
              (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
              (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (usp + -89)) ->
            AST SEGTOP_A (rtA_allow Σ1) (eq (enq_entry_st_r (bv_unsigned vsp) (l_T (lay Σ1)) M n0 gp y0 y1 y2 y3 y4 y5 s7 s8 s9 s10 s11 y6 y7 y8 y9 F' fc' m4))
                (fun mo => ARTM_A Σ1 mo /\ PMc mo) c4 ->
            realizes ctasegs c4 TT).
  { intros Σ1 M c4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 m4 HW1 HP EL1 EF1 ELY1 EC1 ART4 MI4 WM4 ST4 RP4 ICF4 FR4 Hc4'.
    refine (enq_stage_r Σ' Σ1 PMc
              ra vsp gp (Z_to_bv 64 (bv_unsigned vsp + -2056)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q) (Z_to_bv 64 (bv_unsigned vsp + -2056))
              (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F' fc' m3 m4 lo M n0 p TT
              DRAIN FC FDO MST HW1 HP EL1 EF1 ELY1 EC1 HLO' ltac:(rewrite Evsp; clear - LOR; lia)
              ltac:(rewrite Evsp; clear - SPT; lia) ART4 MI4 WM4 ST4 RP4 ICF4 FR4 _ c4 Hc4').
    intros c5 (Σ2 & HAST5 & EL5 & EF5 & ES5 & EC5).
    assert (EL2 : live Σ2 = (q, n) :: live_remove p (live Σ)) by (rewrite EL5, HL; exact (live_remove_cons_ne p q n (live Σ) Hqp)).
    assert (EF2 : frames Σ2 = frames Σ) by (rewrite EF5; exact HF).
    assert (HACE2 : l_ACEIL (lay Σ2) = l_ACEIL (lay Σ)) by (unfold l_ACEIL; unfold rtA_sp0 in ES5, HS; rewrite ES5, HS; reflexivity).
    assert (W5 : forall ms,
              (exists (w0 w1 w2 w3 w5 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word) (F'' : bvmap 5 word) (fc'' : bv 32) (m5 : mem),
                 ms = MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (bv_unsigned vsp + -2128)) gp (Z_to_bv 64 tpA) t0'' t1'' t2'' w0 w1 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                              w2 w3 (Z_to_bv 64 q) w5 (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'') F'' (Z_to_bv 64 0x19c930) fc'' None m5 (seg_rom ctasegs)
                 /\ ART_A Σ2 m5 /\ mem_inv ctasegs m5 /\ stk ctasegs m5 lo (bv_unsigned vsp + -2128)
                 /\ rt_pres (live Σ2) (frames Σ') (bv_unsigned vsp) m3 m5
                 /\ ricpt_frame m5 (bv_unsigned vsp) ra (Z_to_bv 64 (bv_unsigned vsp + -2056)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
                      (Z_to_bv 64 (bv_unsigned vsp + -2056))) ->
              evt ctasegs (fun ms' => exists m6, ret_st ra sp gp (Z_to_bv 64 0xba93f0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m6 ms'
                   /\ rt_after_f RTA Σ2 usp lo m m6 /\ rt_pres (live_remove p (rt_live RTA Σ)) (rt_frames RTA Σ) usp m m6
                   /\ wr_at ctasegs m6 q n /\ acc ctasegs m6 q n
                   /\ (forall old, bytes_at ctasegs m p old -> Z.of_nat (length old) = Z.min n0 n -> bytes_at ctasegs m6 q old)) ms).
    { intros ms (w0 & w1 & w2 & w3 & w5 & t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & F'' & fc'' & m5
                 & -> & ART5 & MI5 & ST5 & RP5 & ICF5).
      assert (Hsp' : l_ACEIL (lay Σ) + 0xF000 <= usp) by (clear - LOW LOR; lia).
      (* [comment removed for export] *)
      assert (AC_old : forall a : word, aclient (live Σ) (frames Σ) usp (bv_unsigned a) -> m2 a = m a).
      { intros a Ha. rewrite (PR2 a (aclient_mono _ _ _ usp (usp + -2208) _ (fun e H => H) ltac:(clear; lia) Ha)).
        exact (MU1 a (fr_client Σ m usp HA Hsp' _ Ha)). }
      assert (NQ : forall a, aclient (live Σ) (frames Σ) usp a -> ~ (q <= a < q + n)).
      { intros a Ha Hxq. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
        - clear - Ha Hxq Hqlo LOR. lia.
        - destruct Ha as ((lo0 & hi0 & Hin0 & Hlh0) & _). unfold CLIENT_STATIC in Hin0.
          repeat (destruct Hin0 as [E|Hin0]; [injection E as <- <-; clear - Hlh0 Hxq HqR Hn; unfold SEGTOP_A in *; lia|]). destruct Hin0.
        - destruct Ha as (p2 & n2 & Hin2 & Hp2).
          pose proof (af_live_disj RTA rta_art_facts Σ' m3 q n p2 n2 [] (live Σ) ART3 HL Hin2) as D. clear - D Hp2 Hxq. lia.
        - destruct Ha as (f & kf & Hinf & Hf). rewrite <- HF in Hinf.
          pose proof (af_frames_range RTA rta_art_facts Σ' m3 f kf ART3 Hinf) as (_ & _ & _ & D). specialize (D q n Hinq). clear - D Hf Hxq. lia.
        - destruct Ha as (f & kf & Hinf & Hf). rewrite <- HF in Hinf.
          pose proof (af_fshadow_apart RTA rta_art_facts Σ' m3 f kf ART3 Hinf) as (D & _). specialize (D q n Hinq). clear - D Hf Hxq. lia. }
      assert (A23 : forall a : word, aclient (live Σ) (frames Σ) usp (bv_unsigned a) -> m3 a = m2 a).
      { intros a Ha. apply MU3. cbn [outside]. split; [|exact I]. pose proof (NQ _ Ha) as X. clear - X Hn Hn0. lia. }
      assert (Hin2q : In (q, n) (live Σ2)) by (rewrite EL2; left; reflexivity).
      (* [comment removed for export] *)
      assert (AG35 : forall a : word, usp - 80 <= bv_unsigned a < USTACK_TOP -> m5 a = m3 a) by (intros a Ha; apply RP5; left; rewrite Evsp; exact Ha).
      pose proof (rw_cells_agree_nw ctasegs m3 m5 _ _ IC1' ltac:(intros a Ha; apply AG35; cbn [cells_size csize Nat.add] in Ha; clear - Ha SPT; lia)) as IC1''.
      pose proof (rw_cells_agree_nw ctasegs m3 m5 _ _ IC2' ltac:(intros a Ha; apply AG35; cbn [cells_size csize Nat.add] in Ha; clear - Ha SPT; lia)) as IC2''.
      pose proof (rw_cells_agree_nw ctasegs m3 m5 _ _ IC3' ltac:(intros a Ha; apply AG35; cbn [cells_size csize Nat.add] in Ha; clear - Ha SPT; lia)) as IC3''.
      eapply evt_mono.
      { apply (rb_back Σ2 m5 q lo ra sp vsp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra (Z_to_bv 64 (bv_unsigned vsp + -2056)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
                 (Z_to_bv 64 (bv_unsigned vsp + -2056)) jp w0 w1 w2 w3 w5 (Z_to_bv 64 (usp + -89)) t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' fc'');
          try assumption.
        - clear - Hq0 HqU Hn. unfold USTACK_TOP in *. lia.
        - rewrite HACE2. exact LOW. }
      intros ms' (m6 & RET6 & ART6 & MI6 & ST6 & MU6 & WM6).
      exists m6. split; [exact RET6|]. split; [split; [exact ART6 | split; [exact MI6 | exact ST6]]|].
      pose proof (ART_wf Σ2 m6 ART6) as HW2. pose proof (geo_of_wf Σ2 HW2) as HG2.
      assert (A56 : forall a : word, aclient (live Σ2) (frames Σ2) usp (bv_unsigned a) -> m6 a = m5 a).
      { intros a Ha. apply MU6. pose proof HW2 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
        pose proof (aclient_split Σ2 (live Σ2) usp (bv_unsigned a) HG2 ltac:(rewrite HACE2; clear - LOW LOR; lia)
                      ltac:(intros p0 n1 Hin0; destruct (V3 p0 n1 Hin0) as [X|(s & Hs & Hq & Hsn & ->)]; [left; exact X|];
                            right; destruct (In_nth_error _ _ Hs) as (k & Hk'); exists k, s; split; [exact Hk' | split; [exact Hq | split; [exact Hsn | reflexivity]]])
                      Ha) as HO.
        cbn [outside] in HO |- *. rewrite HACE2 in HO. clear - HO LOW LOR. split; [lia | exact I]. }
      split.
      { (* [comment removed for export] *)
        intros a Ha. cbn [rt_live rt_frames RTA] in Ha. unfold rtA_live, rtA_frames in Ha.
        pose proof (aclient_live_remove _ _ _ _ _ Ha) as Ha0.
        assert (Ha2 : aclient (live Σ2) (frames Σ2) usp (bv_unsigned a)).
        { rewrite EF2. apply (aclient_mono (live_remove p (live Σ)) (live Σ2) (frames Σ) usp usp (bv_unsigned a)); [intros e He; rewrite EL2; right; exact He | clear; lia | exact Ha]. }
        rewrite (A56 a Ha2).
        assert (Ha5 : aclient (live Σ2) (frames Σ') (bv_unsigned vsp) (bv_unsigned a)).
        { rewrite <- EF5. apply (aclient_mono (live Σ2) (live Σ2) (frames Σ2) usp (bv_unsigned vsp) (bv_unsigned a)); [intros e He; exact He | rewrite Evsp; clear; lia | exact Ha2]. }
        rewrite (RP5 a Ha5).
        rewrite (A23 a Ha0). exact (AC_old a Ha0). }
      destruct (af_acc_live RTA rta_art_facts Σ2 m6 q n ART6 Hin2q) as (WR6 & AC6).
      split; [exact WR6|]. split; [exact AC6|].
      (* [comment removed for export] *)
      intros old Hold Lold.
      assert (Hold2 : bytes_at ctasegs m2 p old).
      { apply (bytes_at_agree ctasegs m m2 p old Hold). intros a Ha. apply AC_old. right; right; left. exists p, n0. split; [exact Hin|]. clear - Ha Lold. lia. }
      assert (Eold : old = src) by (apply (bytes_at_det m2 p old src Hold2 SRC2); rewrite LSRC; clear - Lold; lia).
      subst old.
      apply (bytes_at_agree ctasegs m3 m6 q src DST3). intros a Ha.
      assert (Haq : q <= bv_unsigned a < q + n) by (clear - Ha Lold; lia).
      rewrite (MU6 a ltac:(cbn [outside]; split; [clear - Haq Hqlo LOR; lia | exact I])).
      apply RP5. right; right; left. exists q, n. split; [exact Hin2q | exact Haq]. }
    apply (cps_realizes ctasegs _ _ _ c5 (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ2) _ _ _ (fl_ASTA_mat_stable Σ2 PMc MST) W5) HAST5).
    intros c6 Hc6. apply Hk. exists Σ2, q. split; [exact Hc6|].
    cbn [rt_live rt_frames rt_sp0 rt_credit RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit.
    split; [exact EL2|]. split; [exact EF2|]. split; [unfold rtA_sp0 in ES5, HS; rewrite ES5; exact HS|]. split; [rewrite EC5; exact HCR|].
    split; [exact Hq0|]. split; [exact Hq16 | exact HqU]. }
  (* [comment removed for export] *)
  pose proof (ART_wf Σ' m3 ART3) as (_ & _ & HV3 & _). destruct HV3 as (_ & _ & V3 & _).
  destruct (V3 p n0 Hinp) as [(c & i & Hc & Hni & Ep)|(s & Hs & Hq & Hsn & Ep)].
  { (* [comment removed for export] *)
    assert (Hc3' : AST SEGTOP_A (rtA_allow Σ')
                     (eq (MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (bv_unsigned vsp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 (bv_unsigned vsp + -2056))
                                  (Z_to_bv 64 (p_ubeg (l_SB (lay Σ')) c i n0)) (Z_to_bv 64 INST) (Z_to_bv 64 (p_ubeg (l_SB (lay Σ')) c i n0)) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                  (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 1) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
                                  (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 deallocate_entry) fc' None m3
                             (seg_rom ctasegs)))
                     (fun mo => ARTM_A Σ' mo /\ PMc mo) c3).
    { destruct Hc3 as (H1 & _ & H3 & H4). split; [exact H1|]. split; [|split; [exact H3 | exact H4]].
      rewrite Ems3, Evsp, <- Ep. replace (usp - 80 + -2128) with (usp + -2208) by lia. replace (usp - 80 + -2056) with (usp + -2136) by lia. reflexivity. }
    assert (WA : forall ms, eq (MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (bv_unsigned vsp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 (bv_unsigned vsp + -2056))
                                  (Z_to_bv 64 (p_ubeg (l_SB (lay Σ')) c i n0)) (Z_to_bv 64 INST) (Z_to_bv 64 (p_ubeg (l_SB (lay Σ')) c i n0)) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                  (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 1) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
                                  (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 deallocate_entry) fc' None m3
                             (seg_rom ctasegs)) ms ->
                 evt ctasegs (rsegA_post Σ' c i n0 tr ra vsp gp (Z_to_bv 64 (bv_unsigned vsp + -2056)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
                              (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 F' fc' lo m3) ms).
    { intros ms <-.
      apply (rb_segA Σ' m3 c i n0 lo tr tb ra vsp gp t0' t1' t2' a6' a7' (Z_to_bv 64 (bv_unsigned vsp + -2056)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
               (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' ART3 Hc Hni).
      - rewrite Evsp. clear - HLO' LOR. lia.
      - rewrite Evsp. clear - SPT. lia.
      - exact HLO'.
      - rewrite Evsp. clear - LOR. lia.
      - rewrite Evsp. replace (usp - 80 + -2128) with (usp + -2208) by lia. exact ST3.
      - exact MI3.
      - rewrite Evsp. replace (usp - 80 + -2056) with (usp + -2136) by lia. replace (usp - 80 + -2040) with (usp + -2120) by lia. exact IC4'.
      - rewrite Evsp. replace (usp - 80 + -2040) with (usp + -2120) by lia. exact TB1'.
      - exact HTB.
      - exact Htr.
      - exact ICF3. }
    apply (cps_realizes ctasegs _ _ _ c3 (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) WA) Hc3').
    intros c4 Hc4. unfold rsegA_post in Hc4.
    apply AST_exI in Hc4 as (y0 & Hc4). apply AST_exI in Hc4 as (y1 & Hc4). apply AST_exI in Hc4 as (y2 & Hc4). apply AST_exI in Hc4 as (y3 & Hc4).
    apply AST_exI in Hc4 as (y4 & Hc4). apply AST_exI in Hc4 as (y5 & Hc4). apply AST_exI in Hc4 as (y6 & Hc4). apply AST_exI in Hc4 as (y7 & Hc4).
    apply AST_exI in Hc4 as (y8 & Hc4). apply AST_exI in Hc4 as (y9 & Hc4). apply AST_exI in Hc4 as (m4 & Hc4).
    pose proof Hc4 as (_ & (_ & ART4 & MI4 & WM4 & ST4 & RP4 & ICF4 & FR4) & _ & _).
    pose proof (free_p_wf Σ' m3 c i n0 _ ART3 Hc Hni Dok Dinv) as HW1.
    pose proof (pend_e_p _ c i n0 (pend_free_p Σ' m3 c i n0 (p_abeg (l_SB (lay Σ')) c i + rz_size n0) (fst (depot_put (dep Σ') tr)) ART3 Hc Hni)) as HP.
    assert (Hc4' : AST SEGTOP_A (rtA_allow (free_p Σ' c i n0 (p_abeg (l_SB (lay Σ')) c i + rz_size n0) (fst (depot_put (dep Σ') tr))))
                     (eq (enq_entry_st_r (bv_unsigned vsp) (l_T (lay Σ')) (p_abeg (l_SB (lay Σ')) c i + rz_size n0 - 16) n0 gp y0 y1 y2 y3 y4 y5
                            s7 s8 s9 s10 s11 y6 y7 y8 y9 F' fc' m4))
                     (fun mo => ARTM_A (free_p Σ' c i n0 (p_abeg (l_SB (lay Σ')) c i + rz_size n0) (fst (depot_put (dep Σ') tr))) mo /\ PMc mo) c4).
    { eapply AST_conseq; [exact Hc4 | intros ms (E & _); symmetry; exact E |].
      intros mo (HM & HP'). split; [|exact HP']. apply (artm_eq Σ'); [reflexivity | reflexivity | apply rt_eager_fp | exact HM]. }
    exact (STAGE (free_p Σ' c i n0 (p_abeg (l_SB (lay Σ')) c i + rz_size n0) (fst (depot_put (dep Σ') tr))) (p_abeg (l_SB (lay Σ')) c i + rz_size n0 - 16)
             c4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 m4 HW1 HP ltac:(rewrite Ep; reflexivity) eq_refl eq_refl eq_refl ART4 MI4 WM4 ST4 RP4 ICF4 FR4 Hc4'). }
  { (* [comment removed for export] *)
    destruct (In_nth_error _ _ Hs) as (k & Hks).
    assert (Hc3' : AST SEGTOP_A (rtA_allow Σ')
                     (eq (MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (bv_unsigned vsp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 (bv_unsigned vsp + -2056))
                                  (Z_to_bv 64 (s_ubeg s)) (Z_to_bv 64 INST) (Z_to_bv 64 (s_ubeg s)) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                  (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 1) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
                                  (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 deallocate_entry) fc' None m3
                             (seg_rom ctasegs)))
                     (fun mo => ARTM_A Σ' mo /\ PMc mo) c3).
    { destruct Hc3 as (H1 & _ & H3 & H4). split; [exact H1|]. split; [|split; [exact H3 | exact H4]].
      rewrite Ems3, Evsp, <- Ep. replace (usp - 80 + -2128) with (usp + -2208) by lia. replace (usp - 80 + -2056) with (usp + -2136) by lia. reflexivity. }
    assert (WA : forall ms, eq (MS (mkR (Z_to_bv 64 0x19c930) (Z_to_bv 64 (bv_unsigned vsp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 (bv_unsigned vsp + -2056))
                                  (Z_to_bv 64 (s_ubeg s)) (Z_to_bv 64 INST) (Z_to_bv 64 (s_ubeg s)) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                  (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 1) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
                                  (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 deallocate_entry) fc' None m3
                             (seg_rom ctasegs)) ms ->
                 evt ctasegs (rsegS_post Σ' k s tr ra vsp gp (Z_to_bv 64 (bv_unsigned vsp + -2056)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
                              (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 F' fc' lo m3) ms).
    { intros ms <-.
      apply (rb_segS Σ' m3 k s lo tr tb ra vsp gp t0' t1' t2' a6' a7' (Z_to_bv 64 (bv_unsigned vsp + -2056)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
               (Z_to_bv 64 (bv_unsigned vsp + -2056)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' ART3 Hks Hq).
      - rewrite Evsp. clear - HLO' LOR. lia.
      - rewrite Evsp. clear - SPT. lia.
      - exact HLO'.
      - rewrite Evsp. clear - LOR. lia.
      - rewrite Evsp. replace (usp - 80 + -2128) with (usp + -2208) by lia. exact ST3.
      - exact MI3.
      - rewrite Evsp. replace (usp - 80 + -2056) with (usp + -2136) by lia. replace (usp - 80 + -2040) with (usp + -2120) by lia. exact IC4'.
      - rewrite Evsp. replace (usp - 80 + -2040) with (usp + -2120) by lia. exact TB1'.
      - exact HTB.
      - exact Htr.
      - exact ICF3. }
    apply (cps_realizes ctasegs _ _ _ c3 (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) WA) Hc3').
    intros c4 Hc4. unfold rsegS_post in Hc4.
    apply AST_exI in Hc4 as (y0 & Hc4). apply AST_exI in Hc4 as (y1 & Hc4). apply AST_exI in Hc4 as (y2 & Hc4). apply AST_exI in Hc4 as (y3 & Hc4).
    apply AST_exI in Hc4 as (y4 & Hc4). apply AST_exI in Hc4 as (y5 & Hc4). apply AST_exI in Hc4 as (y6 & Hc4). apply AST_exI in Hc4 as (y7 & Hc4).
    apply AST_exI in Hc4 as (y8 & Hc4). apply AST_exI in Hc4 as (y9 & Hc4). apply AST_exI in Hc4 as (m4 & Hc4).
    pose proof Hc4 as (_ & (_ & ART4 & MI4 & WM4 & ST4 & RP4 & ICF4 & FR4) & _ & _).
    pose proof (free_s_wf Σ' m3 k s _ ART3 Hks Hq Dok Dinv) as HW1.
    pose proof (pend_e_s Σ' m3 k s (fst (depot_put (dep Σ') tr)) ART3 Hks Hq) as HP. rewrite Hsn in HP. rewrite Hsn in Hc4.
    assert (Hc4' : AST SEGTOP_A (rtA_allow (free_s Σ' k s (fst (depot_put (dep Σ') tr))))
                     (eq (enq_entry_st_r (bv_unsigned vsp) (l_T (lay Σ')) (s_mb s + 6128) n0 gp y0 y1 y2 y3 y4 y5
                            s7 s8 s9 s10 s11 y6 y7 y8 y9 F' fc' m4))
                     (fun mo => ARTM_A (free_s Σ' k s (fst (depot_put (dep Σ') tr))) mo /\ PMc mo) c4).
    { eapply AST_conseq; [exact Hc4 | intros ms (E & _); symmetry; exact E |].
      intros mo (HM & HP'). split; [|exact HP']. apply (artm_maps Σ'); [reflexivity | apply (rt_maps_fs Σ' k s _ Hks) | apply (rt_eager_fs Σ' k s _ Hks) | exact HM]. }
    exact (STAGE (free_s Σ' k s (fst (depot_put (dep Σ') tr))) (s_mb s + 6128)
             c4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 m4 HW1 HP ltac:(rewrite Ep; reflexivity) eq_refl eq_refl eq_refl ART4 MI4 WM4 ST4 RP4 ICF4 FR4 Hc4'). }
Qed.

End BackG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rta_realloc_gen_of : rcore_stmt_all -> drain_stmt_r -> fixed_commit_node -> realloc_contract_any RTA.
Proof.
  intros CP DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 n lo
    FDO MST Hin Hn Ha0 Ha1 Htp Hlen Hcr ART0 MI0 CALL UWOK. subst a0 a1 tp.
  intros TT cf Hc Hkk. cbn [ART rt_live rt_frames rt_sp0 rt_credit RTA] in Hin, Hlen, Hcr, ART0.
  unfold rtA_live, rtA_credit in Hin, Hlen, Hcr.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _).
  assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
  destruct (live_any_geo Σ m p n0 lo ART0 Hin LOW') as (Ap & Sp & _ & _ & _ & _ & _ & _ & Hn0 & _). clear Ap Sp.
  destruct (ART_ia Σ m ART0) as (b & IS).
  pose proof (ART_consts Σ m ART0) as (_ & _ & _ & _ & _ & _ & _ & ICR). destruct (ic_stats _ _ ICR) as (fr & fd & STS).
  pose proof (af_live_range RTA rta_art_facts Σ m p n0 ART0 Hin) as (Hp0 & Hp1 & _). cbn [rt_sp0 RTA] in Hp1.
  pose proof (rta_sp0_range Σ m ART0) as Hsr.
  destruct (site_trace_main m realloc_pc (l_top (lay Σ) - 0x800000) (l_top (lay Σ)) ra s0 sp ltac:(right; right; right; left; reflexivity) UWOK ltac:(lia))
    as (ch & tr & CHC & HTR & Htr & Htrl).
  assert (W1 : evt ctasegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n (l_T (lay Σ)) lo tr m)
                 (entry_st ra sp gp (Z_to_bv 64 0xba93f0) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6 F fc e_realloc m)).
  { unfold entry_st, e_realloc.
    apply (realloc_A_spec ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n
             (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo b ch tr fr fd); try assumption.
    all: try (clear - Hp0 Hp1 Hsr Hn0; unfold STACK_WIN, USTACK_TOP in *; lia).
    all: try (clear - Hn; lia).
    all: try (clear - LOR; unfold RT_STACK in *; lia).
    all: try (clear - SPT; unfold USTACK_TOP in *; lia).
    all: try (clear - Hbt; lia). all: try (clear - Htop; lia).
    all: try (pose proof (sr_tcx Σ m ART0) as (_ & _ & _ & _ & X5 & _); clear - X5; unfold SEGTOP_A in *; lia).
    all: try (clear - HT; unfold img_hull_lo, img_hull_hi, SEGTOP_A in *; lia). }
  assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0xba93f0) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                   s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_realloc m) ms ->
                  evt ctasegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n (l_T (lay Σ)) lo tr m) ms)
    by (intros ms <-; exact W1).
  clear W1.
  apply (cps_realizes ctasegs _ _ _ cf (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. unfold realloc_A_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
  apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
  apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
  apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (jq & Hc1). apply AST_exI in Hc1 as (jr & Hc1).
  apply AST_exI in Hc1 as (j0 & Hc1). apply AST_exI in Hc1 as (m1 & Hc1).
  destruct Hc1 as (HM & HPm & HPM & HZ).
  destruct HPm as (Hms & MU1 & WM1 & MI1 & IS1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & IC5 & IC6 & IC7 & IC8 & AFr & J0 & UB1 & ST1).
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= bv_unsigned sp) by (unfold RT_STACK in LOR; lia).
  pose proof (fr_ART Σ m (bv_unsigned sp) ART0 Hsp0 m1 MU1 WM1 IS1 UB1) as ART1.
  set (usp := bv_unsigned sp) in *.
  assert (Hc2 : ASTA RTA Σ PMc (eq (rcore_entry Σ (usp + -2136) gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n m1)) c1).
  { split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold rcore_entry.
    replace (usp + -2136 + -200) with (usp + -2336) by lia. reflexivity. }
  assert (ST1' : stk ctasegs m1 lo (usp + -2136 + -200)) by (replace (usp + -2136 + -200) with (usp + -2336) by lia; exact ST1).
  assert (TRC : trc_cells (usp + -2136) tr m1 tb).
  { split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact IC4|]. split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact TB1 | exact HTB]. }
  assert (AFC : raf_cells (usp + -2136) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
                  (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 m1 j0).
  { split; replace (usp + -2136 + -200) with (usp + -2336) by lia; [exact AFr | exact J0]. }
  assert (LOR' : lo + 0x1000 <= usp + -2136 + -200) by (unfold RT_STACK in LOR; lia).
  assert (SPT' : usp + -2136 + 2144 <= USTACK_TOP) by lia.
  assert (SPA' : (usp + -2136) mod 16 = 8).
  { pose proof SPA as SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [k Hk].
    replace (usp + -2136) with (8 + (k - 134) * 16) by lia. rewrite Z_mod_plus_full. reflexivity. }
  assert (K : forall c2, rcore_post Σ PMc (usp + -2136) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
                           (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 n lo m1 c2 -> realizes ctasegs c2 TT).
  { intros c2 Hc2'. exact (rback_cpsG Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m1 p n0 n lo tr tb jp jq jr
                             DRAIN FC FDO MST Hin Hn ART0 LOW' ltac:(unfold RT_STACK in LOR; exact LOR) SPT (conj Htr Htrl) MU1 WM1 IC1 IC2 IC3 TB1 HTB
                             IC4 IC5 IC6 IC7 IC8 TT c2 Hc2' Hkk). }
  exact (CP Σ PMc m1 (usp + -2136) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
           (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n lo tr tb j0
           FDO MST I Hn Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' Htr Htrl TRC AFC TT c1 Hc2 K).
Qed.

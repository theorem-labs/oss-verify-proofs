(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs R_sizeclass R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qput R_qrecycle R_qdorec R_qcbrec R_cdealloc RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeE RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_start RT_drain_kit RT_drain_geo RT_drain_ldefs RT_drain_istmt RT_drain_art4 RT_drain_loop RT_drain_itemp RT_drain_batch RT_drain_rec RT_drain_xfer RT_drain_rhead RT_freestmt RT_drain_fin RT_refreeG RT_redrain_ldefs RT_redrain_istmt RT_redrain_loop RT_redrain_itemp RT_redrain_batch RT_redsec_defs RT_redsec_ret RT_redsec_runA RT_redsec RT_redrain_xfer RT_redrain_rhead RT_redrain_rec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition dr_post_r (Σ : rtsA) (PMc : Model -> Prop) (gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 : word) (lo usp : Z) (m : mem) :
  config -> Prop :=
  fun cf => exists Σ' : rtsA,
    ASTA RTA Σ' PMc (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                                      (fc' : bv 32) (m' : mem),
        ms = MS (mkR (Z_to_bv 64 0x19683c) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
                     a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0x19683c) fc' None m' (seg_rom bsegs)
        /\ ART_A Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -2128)
        /\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m') cf
    /\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ.

Section DFin.
Variable p : dlp.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

(* [comment removed for export] *)
Theorem rec_from_R_r : forall (Σ' : rtsA) (m0 : mem) (s2 s3 s4 w0 w1 w2 w3 w4 w5 s6 : word),
  qrec_frame (dl_m0 p) C (Z_to_bv 64 0x19a1d0) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4 ->
  qput_frame (dl_m0 p) (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x19683c) w0 w1 w2 w3 w4 w5 s6 ->
  rt_pres (live Σ0) (frames Σ0) (usp + -2128) m0 (dl_m0 p) -> rt_wfP Σ' [] -> dl_sig_r p Σ' ->
  cps bsegs (ASTA RTA Σ' PMc (dl_R_r p Σ'))
    (dr_post_r Σ0 PMc (dl_gp p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) w0 w1 w2 w3 w4 w5 s6 lo usp m0).
Proof using HOK.
  intros Σ' m0 s2 s3 s4 w0 w1 w2 w3 w4 w5 s6 QF PF RP0 HWP HS.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof (dl_nums_r p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit).
  pose proof (geo_of_wfP _ _ HWP) as HG. pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
  pose proof (hqb_of_wfP _ _ HWP) as HQB.
  assert (HL : l_ACEIL (lay Σ') <= lo) by (rewrite El; exact N9).
  assert (Esp1 : bv_unsigned (Z_to_bv 64 (usp + -2208)) = usp + -2208) by (apply unsigned_lit; lia).
  assert (Esp2 : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
  apply cps_pointwise.
  intros ms (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & MI & ST & (G & WG & HGo) & RP & QR).
  (* [comment removed for export] *)
  assert (QF1 : qrec_frame m (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -80) (Z_to_bv 64 0x19a1d0) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4).
  { rewrite Esp1. replace (usp + -2208 + -80) with (usp - 2288) by lia. unfold qrec_frame in *.
    apply (rw_cells_agree_nw (dl_m0 p) m _ _ QF). intros a Ha. apply RP. left. cbn [cells_size csize Nat.add Z.of_nat] in Ha. unfold USTACK_TOP. lia. }
  assert (PF1 : qput_frame m (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x19683c) w0 w1 w2 w3 w4 w5 s6).
  { unfold qput_frame in *. apply (rw_cells_agree_nw (dl_m0 p) m _ _ PF). intros a Ha. apply RP. left.
    cbn [cells_size csize Nat.add Z.of_nat] in Ha. unfold USTACK_TOP. lia. }
  destruct QR as (QH & _).
  replace (usp - 2288) with (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -80) in QH, ST by (rewrite Esp1; lia).
  eapply (cps_seq bsegs).
  { eapply (dl_evt Σ' PMc _ _ MST). intros ms0 <-.
    rewrite (ret_pc_even 0x197d10); [|lia|reflexivity].
    replace (Z_to_bv 64 (usp - 2288)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -80)) by (rewrite Esp1; f_equal; lia).
    eapply evt_mono; [eapply (qrec_ret_spec (Z_to_bv 64 0x19a1d0) (Z_to_bv 64 (usp + -2208)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p)
                               a0 a1 a2 a3 a4 a5 a6 a7 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
                               (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (Z_to_bv 64 0x197d10) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4
                               _ _ _ _ (dl_F p) (dl_fc p) m lo)|].
    1: exact QH. 1: exact QF1. 1: exact ST. 1: rewrite Esp1; lia. 1: exact N4. 1: exact MI.
    intros ms' P. exact (conj P (conj A (conj MI (conj RP PF1)))). }
  apply cps_pointwise.
  intros ms ((t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1) & A0 & MI0 & RP0' & PF0).
  rewrite Esp1 in MU1, ST1.
  assert (HW1 : Forall (fun iv => lo <= fst iv /\ snd iv <= usp + -2128) [(usp + -2208 - 80, usp + -2208)]) by (repeat constructor; cbn [fst snd]; lia).
  pose proof (artc_stk Σ' m m1 _ lo (usp + -2128) HG HL HW1 A Hdep HQB MU1 WM1) as A1.
  pose proof (client_stk Σ' m m1 _ lo (usp + -2128) HG HL ltac:(lia) HW1 Hlive MU1) as RP1. rewrite Elv, Efr in RP1.
  assert (PF2 : qput_frame m1 (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
                  (Z_to_bv 64 0x19683c) w0 w1 w2 w3 w4 w5 s6).
  { rewrite Esp2. replace (usp + -2128 - 80) with (usp + -2208) by lia. unfold qput_frame in *.
    apply (rw_cells_transport bsegs _ m m1 _ _ PF0 MU1 WM1). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. lia. }
  assert (ST1' : stk bsegs m1 lo (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80)) by (rewrite Esp2; replace (usp + -2128 - 80) with (usp + -2208) by lia; exact ST1).
  eapply (cps_seq bsegs).
  { eapply (dl_evt Σ' PMc _ _ MST). intros ms0 <-.
    rewrite (ret_pc_even 0x19a1d0); [|lia|reflexivity].
    replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80)) by (rewrite Esp2; f_equal; lia).
    eapply evt_mono; [apply (qput_C_spec (Z_to_bv 64 0x19683c) (Z_to_bv 64 (usp + -2128)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2'
                               (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 (dl_r5 p) (dl_r6 p)
                               (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (Z_to_bv 64 0x19a1d0)
                               w0 w1 w2 w3 w4 w5 s6 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (dl_F p) (dl_fc p) m1 lo)|].
    1: exact PF2. 1: exact ST1'. 1: rewrite Esp2; lia. 1: exact N4. 1: exact MI1.
    intros ms' P. exact (conj P (conj A1 (conj RP0' RP1))). }
  intros T0 cf Hcf Hk. apply Hk. exists Σ'.
  split; [| split; [exact Elv | split; [exact Efr | split; [exact El | exact Ecr]]]].
  unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
  intros ms ((t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2)
             & A1' & RP0'' & RP1').
  rewrite Esp2 in MU2, ST2.
  rewrite (ret_pc_even 0x19683c); [|lia|reflexivity].
  exists t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', (dl_F p), (dl_fc p), m2. split; [reflexivity|].
  assert (HW2 : Forall (fun iv => lo <= fst iv /\ snd iv <= usp + -2128) [(usp + -2128 - 80, usp + -2128)]) by (repeat constructor; cbn [fst snd]; lia).
  pose proof (artc_stk Σ' m1 m2 _ lo (usp + -2128) HG HL HW2 A1' Hdep HQB MU2 WM2) as A2.
  pose proof (client_stk Σ' m1 m2 _ lo (usp + -2128) HG HL ltac:(lia) HW2 Hlive MU2) as RP2. rewrite Elv, Efr in RP2.
  split; [exact (c_ART Σ' m2 (rt_wfP_nil Σ' HWP) A2)|]. split; [exact MI2|]. split; [exact ST2|].
  refine (rt_pres_trans _ _ _ _ m1 m2 _ RP2). refine (rt_pres_trans _ _ _ _ m m1 _ RP1').
  refine (rt_pres_trans _ _ _ _ (dl_m0 p) m RP0 _). exact (rt_pres_mono _ _ (C + 32) (usp + -2128) _ _ RP ltac:(lia)).
Qed.

End DFin.

(* [comment removed for export] *)
Theorem item_ok_r : fixed_commit_node -> (forall p, dl_ok p -> item_sec_stmt_r p) -> forall p, dl_ok p -> item_stmt_r p.
Proof.
  intros FC ISEC p HOK j Σk b ib ents i rest Hi HWP HS Hib Eb.
  assert (Hq : qent_ok Σk (nth i ents (0, 0))).
  { pose proof HWP as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & Q7 & _) & _). unfold qentsP, qallP in Q7.
    apply (proj1 (Forall_forall _ _) Q7). apply in_flat_map. exists (b, skipn i ents).
    split; [apply in_app_iff; right; apply in_app_iff; right; left; reflexivity|].
    cbn [snd]. rewrite (skipn_nth_cons ents i (0, 0) Hi). left. reflexivity. }
  destruct Hq as [(c & ic & Hc & Hic & Eh)|(s & Hs & Hsq & Hn & Eh)].
  - apply (item_prim_ok_r p FC HOK j Σk b ib ents i rest c ic (snd (nth i ents (0, 0))) Hi HWP HS Hib Eb Hc Hic).
    rewrite <- Eh. destruct (nth i ents (0, 0)); reflexivity.
  - destruct (In_nth_error _ _ Hs) as (k & Hk).
    apply (ISEC p HOK j Σk b ib ents i rest k s Hi HWP HS Hib Eb Hk Hsq). rewrite <- Eh, Hn. destruct (nth i ents (0, 0)); reflexivity.
Qed.

(* [comment removed for export] *)
Theorem drain_rec_r : fixed_commit_node -> (forall p, dl_ok p -> item_sec_stmt_r p) ->
  forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
  fdfs_only PMc -> mat_stable PMc ->
  ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < RT_state.qbytes (ql Σ) ->
  qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x19683c) w0 w1 w2 w3 w4 w5 s6 ->
  stk bsegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
  mem_inv bsegs m ->
  0x10000000 < R_quar_defs.qbytes (qg Σ ++ ql Σ) ->
  cps bsegs (ASTA RTA Σ PMc (eq (xms0_r Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp)))
    (dr_post_r Σ PMc gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp m).
Proof.
  intros FC ISEC Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
    FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI HBYr.
  pose proof (xr_geo_r Σ HW) as (HG & _).
  pose proof (rt_wfP_start Σ HW HC) as HWP1.
  eapply (cps_seq bsegs).
  { eapply (dl_evt Σ PMc _ _ MST). intros ms <-.
    exact (rr_evt_r Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
             HA HW HC HBY FR ST HLO HLO2 HSP MI HBYr). }
  eapply (cps_seq bsegs); [exact (dd_switch Σ (set_q Σ [] (rec_r (qg Σ ++ ql Σ) QMIN)) PMc _ eq_refl eq_refl eq_refl eq_refl)|].
  apply cps_pointwise.
  intros ms (t0' & t1' & t2' & s0' & s1' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & t3' & t4' & t5' & t6' & m3 & -> & A3 & QR3 & QF3 & PF3
             & ST3 & MI3 & WM3 & RP3).
  pose (p := mkDLP Σ m3 usp lo PMc gp s10 s11 F fc s0' s1' s2' s3' s4' s5 (Z_to_bv 64 0x100000) s7 s8 s9).
  assert (HOK : dl_ok p) by (split; [exact FDO|]; split; [exact MST|]; split; [exact HLO|]; split; [exact HLO2|]; split; [exact HSP | exact HG]).
  assert (Einit : ca_init Σ = true).
  { destruct (ca_init Σ) eqn:E; [reflexivity|]. exfalso.
    pose proof HW as (_ & HR & _ & _ & (_ & _ & Q4 & _) & _). pose proof (proj2 (proj2 (proj2 (proj2 (proj2 HR)))) E 24) as E24.
    destruct (qg Σ ++ ql Σ) as [|b0 bs] eqn:EG.
    - cbn in HBYr. lia.
    - assert (Hb0 : In b0 (ql Σ ++ qg Σ)) by (apply (Permutation_in _ (Permutation_app_comm (qg Σ) (ql Σ))); rewrite EG; left; reflexivity).
      destruct (proj1 (Forall_forall _ _) Q4 b0 Hb0) as (ib & Hib & _). rewrite E24 in Hib. destruct ib; discriminate. }
  assert (HS1 : dl_sig_r p (set_q Σ [] (rec_r (qg Σ ++ ql Σ) QMIN))) by (repeat split; [exact Einit]).
  pose proof (item_ok_r FC ISEC p HOK) as ITEM. pose proof (batch_ok_r p FC HOK) as BATCH.
  eapply (cps_seq bsegs).
  { eapply (cps_conseq bsegs); [exact (dl_from_E_r p HOK ITEM BATCH _ (rec_x (qg Σ ++ ql Σ) QMIN) HWP1 HS1) | | intros cf Hcf; exact Hcf].
    intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
    intros ms E. rewrite <- E. exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6', m3. split; [reflexivity|].
    split; [exact A3|]. split; [exact QR3|]. split; [exact ST3|]. split; [exact MI3|].
    split; [exists []; split; [exact (wmono_out_nil m3 m3 (wmono_refl bsegs m3)) | constructor]|].
    intros a _. reflexivity. }
  apply dl_cps_ex. intros Σ' (HWP' & HS').
  exact (rec_from_R_r p HOK Σ' m s2 s3 s4 w0 w1 w2 w3 w4 w5 s6 QF3 PF3 RP3 HWP' HS').
Qed.

(* [comment removed for export] *)
Theorem drain_ok_r : fixed_commit_node -> (forall p, dl_ok p -> item_sec_stmt_r p) ->
  forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
  fdfs_only PMc -> mat_stable PMc ->
  ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < RT_state.qbytes (ql Σ) ->
  qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x19683c) w0 w1 w2 w3 w4 w5 s6 ->
  stk bsegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
  mem_inv bsegs m ->
  cps bsegs (ASTA RTA Σ PMc (eq (xms0_r Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp)))
    (dr_post_r Σ PMc gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp m).
Proof.
  intros FC ISEC Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
    FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI.
  destruct (Z_le_gt_dec (R_quar_defs.qbytes (qg Σ ++ ql Σ)) 0x10000000) as [Hx|Hr].
  - eapply (cps_conseq bsegs);
      [exact (drain_xfer_r Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
                w0 w1 w2 w3 w4 w5 s6 FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI Hx) | intros cf X; exact X |].
    intros cf (Σ' & Hcf & E1 & E2 & E3 & E4). exists Σ'. split; [|exact (conj E1 (conj E2 (conj E3 E4)))].
    unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & -> & X1 & X2 & _ & X4 & X5).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m'.
    split; [reflexivity | exact (conj X1 (conj X2 (conj X4 X5)))].
  - exact (drain_rec_r FC ISEC Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
             w0 w1 w2 w3 w4 w5 s6 FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI ltac:(lia)).
Qed.

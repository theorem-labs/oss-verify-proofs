(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeC RT_refillstmt RT_refillst RT_refillwf RT_rfkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Section RfArt.
Variables (Σ : rtsA) (c usp : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x400 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation W := (W_R (l_T (lay Σ)) (l_SB (lay Σ)) c (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) usp).

Let HG : geo_ok Σ := geo_of_wf0 Σ HW0.

Theorem refill_ART : forall (m m' : mem), ARTc Σ m -> munch W m m' -> wmono asegs m m' ->
  reg_rep SB c (refill_reg (pr Σ c) c) m' ->
  pclass_rep T c true (refill_ca (pr Σ c) c) m' ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> pclass_rep T c' true (ca Σ c') m') ->
  (forall i, (length (r_st (pr Σ c)) <= i)%nat -> nth_error (r_st (refill_reg (pr Σ c) c)) i = Some CkIdle -> pchunk (ann Σ) SB c i CkIdle m') ->
  ARTc (refillΣ Σ c) m'.
Proof.
  intros m m' ART MW WM REG PCc PCo NEW.
  pose proof (rz_img Σ c usp HG Hc Hsp) as HWi. pose proof (rz_T Σ c usp HG Hc Hsp) as HWt.
  pose proof (rz_grant Σ c usp HG Hc Hsp) as HWg. pose proof (rz_grant67 Σ c usp HG Hc Hsp) as HWg67.
  pose proof (rz_ris Σ c usp HG Hc Hsp) as HWr. pose proof (rz_fa Σ c usp HG Hc Hsp) as HWf.
  pose proof (rz_slot Σ c usp HG Hc Hsp) as HWs. pose proof (rz_shad_slot Σ c usp HG Hc Hsp) as HWss.
  pose proof (rz_shad_reg Σ c usp HG Hc Hsp) as HWsr. pose proof (rz_shad_app Σ c usp HG Hc Hsp) as HWsa.
  pose proof (rz_secmap Σ c usp HG Hc Hsp) as HWm.
  pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
  destruct ART as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
  apply ARTc_intro; cbn [refillΣ lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fsc0 fs4 fs1 ia_init credit live frames ann].
  -
    apply (consts_rep_frame L m m' CR); [|exact WM]. intros a Ha. apply MW.
    destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
    + rewrite E. unfold W_R. cbn [outside]. pose proof (rz_geo Σ c HG Hc) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      pose proof (se_disj Σ HG) as (_ & T4 & ATP). pose proof (rz_shad Σ c HG Hc) as (Q1 & Q2).
      clear - K4 K5 K6 K8 K11 ATP T4 Q1 Q2 K3 Hsp Hc. unfold rb, kUserCap, rinfo, RIS_of, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, SHB in *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    + apply (kv_consts Σ W (TZ_R T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_R; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
  -
    intros c' Hc'. cbn [refillΣ pr lay]. destruct (Z.eqb_spec c' c) as [->|Hcc]; [exact REG|].
    exact (reg_rep_transport W _ c' _ m m' (PR c' Hc') MW WM (kv_reg Σ W [c] HG HWr HWf HWsr c' Hc' ltac:(intros [E|[]]; exact (Hcc (eq_sym E))))).
  -
    intros c' Hc'. cbn [refillΣ ca ca_init lay]. destruct (Z.eqb_spec c' c) as [->|Hcc]; [exact PCc | exact (PCo c' Hc' Hcc)].
  -
    destruct CH as [P Sc]. split.
    + intros c' i' st Hc' Hn'. destruct (rfs_st Σ c Hc HW0 c' i' st Hn') as [Hn0|(-> & -> & Hi)].
      * apply (pchunk_transport W _ c' i' _ m m' (P c' i' st Hc' Hn0) MW WM). exact (kv_pchunk Σ W [] HG HWs HWss c' i' st Hc' Hn0 ltac:(intros [])).
      * apply NEW; [exact Hi|]. cbn [refillΣ pr] in Hn'. rewrite Z.eqb_refl in Hn'. exact Hn'.
    + intros k s Hk. apply (schunk_transport W k s m m' (Sc k s Hk) MW WM). exact (kv_schunk Σ W [] HG HWsa HWm k s Hk ltac:(intros [])).
  -
    exact (sec_rep_transport W _ m m' SR MW WM (kv_sec Σ W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
  -
    apply (quar_rep_transport W _ m m' QR MW WM). pose proof HW0 as (_ & _ & _ & _ & (_ & _ & QB & _) & _).
    eapply kv_quar; try eassumption.
    + unfold TZ_R, qcacheT. cbn [disjoint_from]. split; [lia | exact I].
    + apply Forall_forall. intros; exact I.
    + intros i _ [].
  -
    pose proof HW0 as (_ & _ & _ & _ & _ & _ & _ & DOK & _).
    exact (dep_rep_transport W L (dep Σ) m m' DR DOK MW WM (kv_dep Σ W [] HWi ltac:(apply Forall_forall; intros; exact I) HWg67)).
  -
    exact (fs_rep_transport W _ m m' FR MW WM (kv_fs Σ W [] (TZ_R T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
             ltac:(unfold TZ_R; cbn; repeat split; try exact I; lia))).
  - exact (ia_rep_transport W _ m m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
  - exact (shadow_rep_transport W _ m m' SHR MW WM (kv_shadow Σ W [] HG HWsa)).
  - exact (vis_rep_wmono _ m m' VIS WM).
Qed.

End RfArt.

End GWIN.

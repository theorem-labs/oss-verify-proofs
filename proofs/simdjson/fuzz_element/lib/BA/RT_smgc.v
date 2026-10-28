(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_lkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_facts RT_release R_fs_ok R_fs0 R_fs1 R_fs4 R_fs5 R_gc R_fs0gc R_fs1gc R_fs4gc R_fs5gc R_prim_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_stackmalloc RT_stackmalloc1 RT_noret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Ltac pick X := first [ exact X | exact (proj1 X) | let Y := fresh "PK" in pose proof (proj2 X) as Y; clear X; pick Y ].

Lemma zero_flags_repeat : forall fl, nbusy fl = 0%nat -> map b8 fl = repeat (b8 0) (length fl).
Proof.
  induction fl as [|z fl IH]; intros H; [reflexivity|]. cbn [nbusy] in H. cbn [map length repeat].
  destruct (Z.eqb_spec z 0) as [E|E]; [| lia]. rewrite E, IH by lia. reflexivity.
Qed.

Lemma gc_facts : forall (Σ : rtsA) (m : mem) (sp : word) lo,
  ART_A Σ m -> call_ok RTA Σ m sp lo -> frames Σ = [] -> bv_unsigned sp + 0xa0 <= rtA_sp0 Σ ->
  stack_cells (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) m
  /\ 0 <= l_top (lay Σ) - 0x800000 < l_top (lay Σ) /\ l_top (lay Σ) - 0x800000 <= bv_unsigned sp <= l_top (lay Σ) /\ l_top (lay Σ) < 2 ^ 63
  /\ (forall c, 0 <= c <= 10 -> u8arr asegs m (fl_base (l_FSB (lay Σ)) c) (repeat (b8 0) (Z.to_nat (NF c))))
  /\ ro_cells asegs m 0x16a228 [C8 (Z_to_bv 64 0x171438)].
Proof.
  intros Σ m sp lo HA CALL HFR TOPR.
  destruct CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0, RT_STACK, STACK_WIN, USTACK_TOP in *.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & SC & _ & ICR).
  pose proof (geo_layout Σ m HA) as ((W1 & W2) & M16 & (TL1 & TL2) & TL4 & _). unfold sp_window_lo, sp_window_hi in *.
  split; [exact SC|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
  - intros c Hc.
    pose proof (ART_fs Σ m HA) as ((_ & OFL) & F05 & F00 & F04 & F01 & _).
    pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & HFw & _). destruct HFw as (W0 & W02 & W4 & Wc1 & _ & _ & _ & FCNT & _).
    assert (CLS : forall k, (k = 5 \/ k = 0 \/ k = 4 \/ k = 1)%nat -> c = Z.of_nat k ->
                 u8arr asegs m (fl_base (l_FSB (lay Σ)) c) (repeat (b8 0) (Z.to_nat (NF c)))).
    { intros k Hk ->. pose proof (FCNT k Hk) as CNT. rewrite HFR in CNT. cbn [List.filter length Z.of_nat] in CNT.
      assert (Hwf : fs_cls_wf (Z.of_nat k) (fs_of Σ k)) by (destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; assumption).
      destruct Hwf as ((LEN & _) & _ & _).
      assert (HF : fs_flags (l_FSB (lay Σ)) (Z.of_nat k) m (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; [exact (proj1 (proj2 F05)) | exact (proj1 (proj2 F00)) | exact (proj1 (proj2 F04)) | exact (proj1 (proj2 F01))]).
      assert (NB0 : nbusy (fss_flags (fs_of Σ k)) = 0%nat) by lia.
      unfold fs_flags in HF. rewrite (zero_flags_repeat _ NB0) in HF. rewrite <- LEN, Nat2Z.id. exact HF. }
    assert (Hc' : c = 0 \/ c = 1 \/ c = 4 \/ c = 5 \/ In c OCLS) by (unfold OCLS; cbn; lia).
    destruct Hc' as [E|[E|[E|[E|HIN]]]];
      [exact (CLS 0%nat ltac:(lia) E) | exact (CLS 1%nat ltac:(lia) E) | exact (CLS 4%nat ltac:(lia) E) | exact (CLS 5%nat ltac:(lia) E) | exact (OFL c HIN)].
  - pose proof ICR as X. pick X.
Qed.

Lemma gc_munch_noret : forall (FSB lo usp : Z) (m mg : mem),
  munch [(usp - 208, usp); (FSB + 0x60, FSB + 0x61)] m mg -> lo <= usp - 208 -> munch [(FSB + 0x60, FSB + 0x61); (lo, usp)] m mg.
Proof.
  intros FSB lo usp m mg MU Hlo. eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside fst snd] in Hx |- *.
  destruct Hx as (X1 & X2 & _). split; [lia|]. split; [lia | exact I].
Qed.

Lemma art_after_gc : forall (Σ : rtsA) (m mg : mem) (sp : word) lo,
  ART_A Σ m -> call_ok RTA Σ m sp lo ->
  munch [(bv_unsigned sp - 208, bv_unsigned sp); (l_FSB (lay Σ) + 0x60, l_FSB (lay Σ) + 0x61)] m mg -> wmono asegs m mg -> fs_const (l_FSB (lay Σ)) mg ->
  ART_A Σ mg /\ rt_pres (rtA_live Σ) (frames Σ) (bv_unsigned sp) m mg.
Proof.
  intros Σ m mg sp lo HA CALL MU WM FC.
  destruct CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0, RT_STACK in *.
  assert (Hlo : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
  pose proof (gc_munch_noret (l_FSB (lay Σ)) lo (bv_unsigned sp) m mg MU ltac:(lia)) as MUn.
  assert (GB : u8arr asegs mg (l_FSB (lay Σ) + 0x60) [Z_to_bv 8 (if false then 1 else 0)]).
  { unfold fs_const in FC. apply (proj1 (rwc_app asegs mg _ [C8 (Z_to_bv 64 20)] [C1 (Z_to_bv 8 0)])) in FC. destruct FC as (_ & FC1).
    cbn [cells_size csize Nat.add] in FC1. replace (l_FSB (lay Σ) + 88 + Z.of_nat 8) with (l_FSB (lay Σ) + 0x60) in FC1 by lia. exact (u8arr_of_rw_C1 mg _ _ FC1). }
  split.
  - exact (art_after_gen Σ m mg lo (bv_unsigned sp) HA MUn WM false GB Hlo ltac:(lia) _ ltac:(intros _ X; discriminate X) ltac:(intros X; discriminate X)).
  - exact (nr_pres Σ m mg lo (bv_unsigned sp) HA MUn Hlo (bv_unsigned sp) ltac:(lia) ltac:(lia)).
Qed.

Lemma rt_pres_trans : forall L Fr sp (m1 m2 m3 : mem), rt_pres L Fr sp m1 m2 -> rt_pres L Fr sp m2 m3 -> rt_pres L Fr sp m1 m3.
Proof. intros L Fr sp m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma sm_finish_gc : forall (Σ : rtsA) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m mg : mem) (k : nat) (j lo : Z) (fc : bv 32)
    (Pm : machine_state -> Prop) c1,
  ART_A Σ mg -> (k = 5 \/ k = 0 \/ k = 4 \/ k = 1)%nat -> 0 <= j < NF (Z.of_nat k) ->
  nth (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) (fss_flags (fs_of Σ k)) 1 = 0 ->
  1 <= credit Σ -> fs_room k (frames Σ) ->
  rtA_sp0 Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  wmono asegs m mg -> rt_pres (rtA_live Σ) (frames Σ) (bv_unsigned sp) m mg ->
  AST SEGTOP_A (rtA_allow Σ) Pm (fun mo => ARTM RTA Σ mo /\ PMc mo) c1 ->
  (forall ms, Pm ms -> exists m',
     ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       (Z_to_bv 64 (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)))) m' ms
     /\ munch (sm_W (Z.of_nat k) (l_FSB (lay Σ)) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) (bv_unsigned sp)) mg m'
     /\ wmono asegs mg m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     /\ fs_hint (l_FSB (lay Σ)) (Z.of_nat k) m' (fss_hint (fs_of Σ k) + j + 1) /\ fs_const (l_FSB (lay Σ)) m'
     /\ fs_flags (l_FSB (lay Σ)) (Z.of_nat k) m'
          (upd (fss_flags (fs_of Σ k)) (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) 1)
     /\ wr_at asegs m' (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) (fsz (Z.of_nat k))
     /\ rw_cells asegs m' (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) + fsz (Z.of_nat k) - 8)
          [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + (fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)))]
     /\ wr_at asegs m' (shad (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))))
          (fsz (Z.of_nat k) / 8)
     /\ fs_free_frames (l_FSB (lay Σ)) (Z.of_nat k) m'
          (upd (fss_flags (fs_of Σ k)) (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) 1)) ->
  exists (Σ' : rts RTA) (f : Z),
       ASTA RTA Σ' PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c1
       /\ rt_frames RTA Σ' = (f, k) :: rt_frames RTA Σ /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
       /\ rt_credit RTA Σ' = rt_credit RTA Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP.
Proof.
  intros Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mg k j lo fc Pm c1 HA Hk Hj Hfree Hcr Hlen LOW LOR SPT WMg PRg HAST HPm.
  destruct (sm_finish Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mg k j lo fc Pm c1 HA Hk Hj Hfree Hcr Hlen LOW LOR SPT HAST HPm)
    as (Σ' & f & HQ & E1 & E2 & E3 & E4 & E5).
  exists Σ', f. split; [| exact (conj E1 (conj E2 (conj E3 (conj E4 E5))))].
  unfold ASTA in *. eapply AST_conseq; [exact HQ | | intros mo X; exact X].
  intros ms (m' & RS & (A1 & A2 & A3 & A4) & PR & W1 & W2). exists m'. split; [exact RS|].
  split; [exact (conj A1 (conj A2 (conj (wmono_trans asegs m mg m' WMg A3) A4)))|].
  split; [exact (rt_pres_trans _ _ _ m mg m' PRg PR) | exact (conj W1 W2)].
Qed.

Theorem smgc_proof_4 : smgc_case 4.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST Hk -> Hlen Hcr ART0 MI0 CALL FCG GNIL TOPR.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 4%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  clear FC. destruct (gc_facts Σ m sp lo ART0 CALL GNIL TOPR) as (SC & B0 & RS & TOP & FLZ & GF).
  assert (W1 : evt asegs (sm4_gc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 4))
                            (fss_flags (fs_of Σ 4)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 4) m)).
  { unfold entry_st.
    exact (stack_malloc_4_gc_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 4)) (fss_flags (fs_of Σ 4)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) (Z_to_bv 64 0x171438) FCG FH FL OK ltac:(change (fs_cap (Z.of_nat 4)) with 16 in NB; lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) SC B0 RS TOP FLZ GF MI0). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm4_gc_post in Hc1.

  apply AST_exI in Hc1 as (mg & Hc0).
  assert (PRE : munch [(bv_unsigned sp - 208, bv_unsigned sp); (l_FSB (lay Σ) + 0x60, l_FSB (lay Σ) + 0x61)] m mg /\ wmono asegs m mg /\ fs_const (l_FSB (lay Σ)) mg)
    by (destruct Hc0 as (_ & HP & _); destruct HP as (A1 & A2 & A3 & _); exact (conj A1 (conj A2 A3))).
  destruct PRE as (MUg & WMg & FCg).
  destruct (art_after_gc Σ m mg sp lo ART0 CALL MUg WMg FCg) as (ARTg & PRg).
  assert (Hc1 : AST SEGTOP_A (rtA_allow Σ) (sm4_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 4))
                  (fss_flags (fs_of Σ 4)) lo mg) (fun mo => ARTM RTA Σ mo /\ PMc mo) c1).
  { eapply AST_conseq; [exact Hc0 | intros ms (_ & _ & _ & X); exact X | intros mo X; exact X]. }
  clear Hc0. unfold sm4_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 1024)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 4) + Z.of_nat jn) mod 1024)) (fss_flags (fs_of Σ 4)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish_gc Σ PMc ra sp gp (Z_to_bv 64 0x6a7e68) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mg 4%nat (Z.of_nat jn) lo fc _ c1 ARTg ltac:(lia)
           ltac:(change (NF (Z.of_nat 4)) with 1024; lia) Hfree Hcr (cap_std 4%nat _ ltac:(lia) Hlen) LOW LOR SPT WMg PRg Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 984 junk2 _ (fsz (Z.of_nat 4)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.

Theorem smgc_proof_0 : smgc_case 0.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST Hk -> Hlen Hcr ART0 MI0 CALL FCG GNIL TOPR.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 0%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  clear FC. destruct (gc_facts Σ m sp lo ART0 CALL GNIL TOPR) as (SC & B0 & RS & TOP & FLZ & GF).
  assert (W1 : evt asegs (sm0_gc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 0))
                            (fss_flags (fs_of Σ 0)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 0) m)).
  { unfold entry_st.
    exact (stack_malloc_0_gc_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 0)) (fss_flags (fs_of Σ 0)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) (Z_to_bv 64 0x171438) FCG FH FL OK ltac:(change (fs_cap (Z.of_nat 0)) with 2040 in NB; lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) SC B0 RS TOP FLZ GF MI0). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm0_gc_post in Hc1.

  apply AST_exI in Hc1 as (mg & Hc0).
  assert (PRE : munch [(bv_unsigned sp - 208, bv_unsigned sp); (l_FSB (lay Σ) + 0x60, l_FSB (lay Σ) + 0x61)] m mg /\ wmono asegs m mg /\ fs_const (l_FSB (lay Σ)) mg)
    by (destruct Hc0 as (_ & HP & _); destruct HP as (A1 & A2 & A3 & _); exact (conj A1 (conj A2 A3))).
  destruct PRE as (MUg & WMg & FCg).
  destruct (art_after_gc Σ m mg sp lo ART0 CALL MUg WMg FCg) as (ARTg & PRg).
  assert (Hc1 : AST SEGTOP_A (rtA_allow Σ) (sm0_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 0))
                  (fss_flags (fs_of Σ 0)) lo mg) (fun mo => ARTM RTA Σ mo /\ PMc mo) c1).
  { eapply AST_conseq; [exact Hc0 | intros ms (_ & _ & _ & X); exact X | intros mo X; exact X]. }
  clear Hc0. unfold sm0_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : Z.of_nat jn < 16384 /\ nth (Z.to_nat ((fss_hint (fs_of Σ 0) + Z.of_nat jn) mod 16384)) (fss_flags (fs_of Σ 0)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish_gc Σ PMc ra sp gp (Z_to_bv 64 0x6a7e68) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mg 0%nat (Z.of_nat jn) lo fc _ c1 ARTg ltac:(lia)
           ltac:(change (NF (Z.of_nat 0)) with 16384; lia) Hfree Hcr (cap_std 0%nat _ ltac:(lia) Hlen) LOW LOR SPT WMg PRg Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 24 junk2 _ (fsz (Z.of_nat 0)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.

Theorem smgc_proof_5 : smgc_case 5.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST Hk -> Hlen Hcr ART0 MI0 CALL FCG GNIL TOPR.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 5%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  clear FC. destruct (gc_facts Σ m sp lo ART0 CALL GNIL TOPR) as (SC & B0 & RS & TOP & FLZ & GF).
  assert (W1 : evt asegs (sm5_gc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 5))
                            (fss_flags (fs_of Σ 5)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 5) m)).
  { unfold entry_st.
    exact (stack_malloc_5_gc_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 5)) (fss_flags (fs_of Σ 5)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) (Z_to_bv 64 0x171438) FCG FH FL OK ltac:(change (fs_cap (Z.of_nat 5)) with 16 in NB; lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) SC B0 RS TOP FLZ GF MI0). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm5_gc_post in Hc1.

  apply AST_exI in Hc1 as (mg & Hc0).
  assert (PRE : munch [(bv_unsigned sp - 208, bv_unsigned sp); (l_FSB (lay Σ) + 0x60, l_FSB (lay Σ) + 0x61)] m mg /\ wmono asegs m mg /\ fs_const (l_FSB (lay Σ)) mg)
    by (destruct Hc0 as (_ & HP & _); destruct HP as (A1 & A2 & A3 & _); exact (conj A1 (conj A2 A3))).
  destruct PRE as (MUg & WMg & FCg).
  destruct (art_after_gc Σ m mg sp lo ART0 CALL MUg WMg FCg) as (ARTg & PRg).
  assert (Hc1 : AST SEGTOP_A (rtA_allow Σ) (sm5_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 5))
                  (fss_flags (fs_of Σ 5)) lo mg) (fun mo => ARTM RTA Σ mo /\ PMc mo) c1).
  { eapply AST_conseq; [exact Hc0 | intros ms (_ & _ & _ & X); exact X | intros mo X; exact X]. }
  clear Hc0. unfold sm5_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 512)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 5) + Z.of_nat jn) mod 512)) (fss_flags (fs_of Σ 5)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish_gc Σ PMc ra sp gp (Z_to_bv 64 0x6a7e68) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mg 5%nat (Z.of_nat jn) lo fc _ c1 ARTg ltac:(lia)
           ltac:(change (NF (Z.of_nat 5)) with 512; lia) Hfree Hcr (cap_std 5%nat _ ltac:(lia) Hlen) LOW LOR SPT WMg PRg Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 2008 junk2 _ (fsz (Z.of_nat 5)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.

Theorem smgc1_proof : smgc1_case.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> Hlen Hcr ART0 MI0 CALL FCG GNIL TOPR.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 1%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  clear FC. destruct (gc_facts Σ m sp lo ART0 CALL GNIL TOPR) as (SC & B0 & RS & TOP & FLZ & GF).
  assert (W1 : evt asegs (sm1_gc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 1))
                            (fss_flags (fs_of Σ 1)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc e_stack_malloc_1 m)).
  { unfold entry_st.
    exact (stack_malloc_1_gc_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 1)) (fss_flags (fs_of Σ 1)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) (Z_to_bv 64 0x171438) FCG FH FL OK ltac:(change (fs_cap (Z.of_nat 1)) with 4096 in NB; lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) SC B0 RS TOP FLZ GF MI0). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm1_gc_post in Hc1.

  apply AST_exI in Hc1 as (mg & Hc0).
  assert (PRE : munch [(bv_unsigned sp - 208, bv_unsigned sp); (l_FSB (lay Σ) + 0x60, l_FSB (lay Σ) + 0x61)] m mg /\ wmono asegs m mg /\ fs_const (l_FSB (lay Σ)) mg)
    by (destruct Hc0 as (_ & HP & _); destruct HP as (A1 & A2 & A3 & _); exact (conj A1 (conj A2 A3))).
  destruct PRE as (MUg & WMg & FCg).
  destruct (art_after_gc Σ m mg sp lo ART0 CALL MUg WMg FCg) as (ARTg & PRg).
  assert (Hc1 : AST SEGTOP_A (rtA_allow Σ) (sm1_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 1))
                  (fss_flags (fs_of Σ 1)) lo mg) (fun mo => ARTM RTA Σ mo /\ PMc mo) c1).
  { eapply AST_conseq; [exact Hc0 | intros ms (_ & _ & _ & X); exact X | intros mo X; exact X]. }
  clear Hc0. unfold sm1_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < Z.to_nat 8192)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 1) + Z.of_nat jn) mod 8192)) (fss_flags (fs_of Σ 1)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish_gc Σ PMc ra sp gp (Z_to_bv 64 0x6a7e68) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mg 1%nat (Z.of_nat jn) lo fc _ c1 ARTg ltac:(lia)
           ltac:(change (NF (Z.of_nat 1)) with 8192; lia) Hfree Hcr (cap_1 _ Hlen) LOW LOR SPT WMg PRg Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 88 junk2 _ (fsz (Z.of_nat 1)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.

Theorem smgc_proof : smgc_stmt.
Proof.
  intros k Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST Hk.
  destruct Hk as [-> | [-> | ->]];
    [ exact (smgc_proof_0 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST ltac:(lia))
    | exact (smgc_proof_4 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST ltac:(lia))
    | exact (smgc_proof_5 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST ltac:(lia)) ].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Exec RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface D_defs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts RT_release R_fs_ok R_fs_defs16 R_fs0 R_fs1 R_fs6.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import R_fs_gen.   (* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import R_fs4.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_stackmalloc Ed_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma sm_finishF : forall (Σ : rtsA) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word) (fc0 : bv 32) (m : mem) (k : nat) (j lo : Z)
    (Pm : machine_state -> Prop) c1,
  ART_A Σ m -> (k <= 10)%nat -> 0 <= j < NF (Z.of_nat k) ->
  nth (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) (fss_flags (fs_of Σ k)) 1 = 0 ->
  1 <= credit Σ -> (length (frames Σ) < FRAMES_MAX)%nat ->
  rtA_sp0 Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  AST SEGTOP_A (rtA_allow Σ) Pm (fun mo => ARTM RTA Σ mo /\ PMc mo) c1 ->
  (forall ms, Pm ms -> exists m',
     ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0
       (Z_to_bv 64 (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)))) m' ms
     /\ munch (sm_W (Z.of_nat k) (l_FSB (lay Σ)) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) (bv_unsigned sp)) m m'
     /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
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
       ASTA RTA Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 (Z_to_bv 64 f) m' ms
         /\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c1
       /\ rt_frames RTA Σ' = (f, k) :: rt_frames RTA Σ /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
       /\ rt_credit RTA Σ' = rt_credit RTA Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP.
Proof.
  intros Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 m k j lo Pm c1 HA Hk Hj Hfree Hcr Hlen LOW LOR SPT HAST HPm.
  set (FSB := l_FSB (lay Σ)) in *. set (pos := (fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) in *.
  set (f := frame_addr FSB (Z.of_nat k) pos) in *.
  set (g' := mkFs (fss_hint (fs_of Σ k) + j + 1) (upd (fss_flags (fs_of Σ k)) (Z.to_nat pos) 1)).
  set (usp := bv_unsigned sp) in *.
  assert (Hlo : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; unfold rtA_sp0 in LOW; lia).
  assert (Husp : lo + 208 <= usp) by (unfold RT_STACK in LOR; lia).
  assert (Husp2 : usp <= USTACK_TOP) by lia.
  exists (fs_push Σ k g' f), f.
  pose proof (push_f Σ m k j HA Hk) as (F1 & F2 & F3).
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity | exact (conj F1 (conj F2 F3))]]]]].
  unfold ASTA. change (rt_allow RTA (fs_push Σ k g' f)) with (rtA_allow Σ).
  eapply AST_conseq; [exact HAST| |intros mo Hmo; exact Hmo].
  intros ms HP. destruct (HPm ms HP) as (m' & RS & MU & WM & MI & ST' & P1 & P2 & P3 & P4 & P5 & P6 & P7).
  destruct (push_post Σ m m' k j usp lo HA Hk Hj Hfree Hcr Hlen Hlo Husp Husp2 MU WM P1 P2 P3 P4 P5 P6 P7) as (ART' & PRES & WR1 & WR2).
  exists m'. split; [exact RS|]. split; [split; [exact ART' | split; [exact MI | split; [exact WM | exact ST']]]|].
  split; [exact PRES|]. split; [exact WR1 | exact WR2].
Qed.

Theorem rta_stack_malloc_0F : stack_malloc_contractF RTA 0.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST Hk -> Hlen Hcr ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 0%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  assert (W1 : evt asegs (sm0_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (frm_clear fc) (l_FSB (lay Σ)) (fss_hint (fs_of Σ 0))
                            (fss_flags (fs_of Σ 0)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x70c438) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 0) m)).
  { unfold entry_st.
    exact (stack_malloc_0_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F (frm_clear fc) m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 0)) (fss_flags (fs_of Σ 0)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      FC FH FL OK ltac:(lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm0_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : Z.of_nat jn < 16384 /\ nth (Z.to_nat ((fss_hint (fs_of Σ 0) + Z.of_nat jn) mod 16384)) (fss_flags (fs_of Σ 0)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finishF Σ PMc ra sp gp (Z_to_bv 64 0x70c438) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (frm_clear fc) m 0%nat (Z.of_nat jn) lo _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 0)) with 16384; lia) Hfree Hcr Hlen LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 24 junk2 _ (fsz (Z.of_nat 0)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState ITree Nodes. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_cdealloc RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeE RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_art3 RT_drain_geo RT_drain_cdk RT_drain_cdeal RT_drain_ldefs RT_drain_istmt RT_drain_loop RT_drain_itemp RT_drain_batch RT_refreeG RT_redrain_ldefs RT_redrain_istmt RT_redrain_loop RT_redrain_itemp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section Batch.
Variable p : dlp.
Hypothesis FC : fixed_commit_node.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).

Theorem batch_ok_r : batch_stmt_r p.
Proof using FC HOK.
  intros j Σk b ib ents rest HWP HS Hib Eb.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit).
  pose proof (geo_of_wfP _ _ HWP) as HG.
  pose proof HWP as (HL & HR & Hlive & HSW & HQW & HFW & HB & Hdep & _).
  pose proof (hqb_of_wfP _ _ HWP) as HQB.
  pose proof (dl_nums_r p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  assert (HLk : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
  pose proof (proj1 (proj2 (proj2 HR)) 24 ltac:(lia)) as (Hcnt & _ & Hcl0).
  assert (Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σk 24)))) (ca Σk 24)) by (eapply Forall_impl; [|exact Hcl0]; intros x (X & _); exact X).
  pose proof (proj1 HR 24 ltac:(lia)) as HRW.
  assert (HAw : A_bytes (aw Σk) <= CREDIT0) by (destruct HB as (X1 & _ & X3 & _); lia).
  assert (HEg : rt_eager (recp Σk 24 ib) <= 2 ^ 38)
    by (exact (proj1 (proj2 (proj2 (proj2 (budget_wf_recp Σk 24 ib CkBatch HB HR HSW ltac:(lia) Hib ltac:(discriminate) Einit)))))).
  pose proof (rt_wfP_batch Σk b rest ib HWP Hib Eb Einit) as HWP'.
  apply cps_pointwise.
  intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
  pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
  pose proof FR as (FR1 & FR2 & FR3).
  assert (HA' : ARTc (set_st Σk 24 ib CkIdle) m).
  { apply (artc_unbatch Σk m ib HA Hib). rewrite <- Eb. exact (qbatch_stk m b _ ents QB). }
  assert (Esp : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
  eapply (cps_conseq ctasegs).
  - exact (cd_lift Σk PMc m 24 ib CkBatch lo (Z_to_bv 64 0x19e0f8) (Z_to_bv 64 (C - 112)) (dl_gp p) t0 t1 t2 (Z_to_bv 64 C)
             (Z_to_bv 64 INST) a4 a5 a6 a7 (Z_to_bv 64 6744600) (Z_to_bv 64 6745224) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37))
             s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p)
             FDO MST FC HG HA' ltac:(lia) Hib Einit HRW Hcl Hcnt ltac:(rewrite Esp; exact ST) HLk ltac:(rewrite Esp; lia) ltac:(rewrite Esp; lia)
             MI Hlive Hdep HQB HL HAw HEg).
  - intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
    intros ms E. rewrite <- E. unfold cd_msD. rewrite <- Eb, El. reflexivity.
  - intros cf Hcf. exists (recp Σk 24 ib). split.
    + unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
      intros ms2 (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & HA2 & MU2 & WM2 & MI2 & ST2 & RP2).
      rewrite Esp in MU2, ST2, RP2.
      rewrite (ret_pc_even 0x19e0f8); [| lia | reflexivity].
      exists (Z_to_bv 64 0x19e0f8), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', (Z_to_bv 64 b), s6, s7, s8, s9,
        t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
      assert (RPa : rt_pres (live Σ0) (frames Σ0) (C - 112) m m2) by (rewrite <- Elv, <- Efr; exact RP2).
      pose proof (pres_munch _ _ _ m m2 RPa) as MUa.
      split; [exact HA2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m2 WG WM2) | exact HGo]|].
      split; [exact (rt_pres_trans _ _ _ _ m m2 RP (rt_pres_mono _ _ (C - 112) (C + 32) m m2 RPa ltac:(lia)))|].
      split.
      * split; [|split].
        -- apply (rw_cells_transport ctasegs _ m m2 _ _ FR1 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
        -- apply (rw_cells_transport ctasegs _ m m2 _ _ FR2 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
        -- apply (rw_cells_transport ctasegs _ m m2 _ _ FR3 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
      * apply (qcache_rep_frame _ m m2 C rest QR MU2 WM2).
        -- exact (bt_stack_av Σk C lo C 32 HG HLk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        -- apply Forall_forall. intros (b', ents') Hin.
           destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'.
           exact (bt_batch_av Σk j' C lo HG Hj' HLk ltac:(lia) ltac:(lia)).
    + split; [exact HWP'|].
      pose proof (recp_fields Σk 24 ib) as (X1 & X2 & _ & _ & _ & X6 & _ & _ & _ & _ & _ & X12 & X13 & X14).
      split; [rewrite X1; exact El|]. split; [rewrite X13; exact Elv|]. split; [rewrite X14; exact Efr|].
      split; [rewrite X12; exact Ecr|]. split; [rewrite X6; exact Eql | rewrite X2; exact Einit].
Qed.

End Batch.

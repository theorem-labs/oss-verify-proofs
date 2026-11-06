(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf LeptL_kit Pm_iface Pm_iface2 PmL_getindex_loop.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section GETINDEX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixcmapGetIndex_ok : pixcmapGetIndex_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cmap pi cv x
    FDO MST -> -> -> COBJ OPI PIC ENV.
  unfold lpost, lenv, keeps, keepsL, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OPI as (OWI & PI0 & PI8 & PIH & PIS).
  destruct COBJ as ((cpad & CMC) & (CIN & CM0 & CM16 & _) & (AIN & AR0 & AR16 & ARN) & (CD & CNA & CNR) & CNE).
  destruct cv as [arr depth nalloc n]. cbn [c_arr c_depth c_nalloc c_n] in *. unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC.
  assert (NAB : nalloc <= 256) by (rewrite CNA; cbn [In] in CD; destruct CD as [E|[E|[E|[E|[]]]]]; rewrite <- E; cbn; lia).
  assert (AKI : accok (rt_live RT Σ) (rt_frames RT Σ) m pi 4) by (right; exact OWI).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  (* [comment removed for export] *)
  assert (LOC : pi + 4 <= lo /\ (pi + 4 <= cmap \/ cmap + 24 <= pi) /\ (pi + 4 <= arr \/ arr + 4 * nalloc <= pi)).
  { destruct OWI as (f & k & Hin & Q1 & Q2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R1 & _ & R2).
    pose proof (R2 cmap 24 CIN). pose proof (R2 arr (4 * nalloc) AIN). unfold STACK_WIN in *. lia. }
  destruct LOC as (PILO & PICM & PIAR).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  unfold entry_st, e_pixcmapGetIndex, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pi, pi + 4)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  pose proof ST as (STa & STb & _).
  chunk_facts RT AF GP cmap 24.
  chunk_facts RT AF GP arr (4 * nalloc).
  (* [comment removed for export] *)
  pose proof (af_acc_live RT AF Σ m arr (4 * nalloc) ART0 AIN) as (WRA & _).
  apply wr_at_rw_CB in WRA; [| lia]. destruct WRA as (abs & ABC).
  pose proof ABC as [[[ABL _] _] _]. cbn in ABL.
  refresh RT AF.
  cps_walk AF MST.
  pose proof (munch_refl [(usp - 16, usp); (pi, pi + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  awalk [0x921f0].
  sx32_fix. brfork HN0.
  - (* [comment removed for export] *)
    awalk (@nil Z).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; exact (accok_aclient _ _ _ _ pi 4 zz AKI Hzz)| exact I]]).
    agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [clear - HxS LOW LOR; lia| clear - HxO; tauto]).
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    exists Σ, 1, 0. split; [| repeat split; reflexivity].
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
    split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
    split; [assumption | right; split; reflexivity].
  - (* [comment removed for export] *)
    awalk [0x921f0].
    lazymatch goal with H : rw_cells asegs ?mm arr [CB _ abs] |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (u8arr_of_rw_cells asegs _ _ _ _ H) as [AB _] end.
    eapply evt_cut.
    { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        epose proof (gidx_loop (Z.to_nat n) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm arr (4 * nalloc) n abs) as GL end.
      replace (n - 0) with n in GL by lia. replace (arr + 4 * 0) with arr in GL by lia.
      eapply GL; unfold parked in *.
      all: lazymatch goal with
           | |- bytes_at _ _ _ _ => exact AB
           | |- acc _ _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- Z.of_nat (length _) = _ => rewrite ABL; lia
           | |- Z.of_nat (Z.to_nat _) = _ => rewrite Z2Nat.id by lia; lia
           | |- _ => first [ lia | (Z.div_mod_to_equations; lia) ]
           end. }
   
    clear AB.
    intros ms' (i' & t2' & a5' & a6' & t3' & t4' & t5' & [[Hi ->] | ->]); unfold gidx_st, GIDX_FOUND, GIDX_NOTFOUND.
    + (* [comment removed for export] *)
      awalk (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; exact (accok_aclient _ _ _ _ pi 4 zz AKI Hzz)| exact I]]).
      agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [clear - HxS LOW LOR; lia| clear - HxO; tauto]).
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      exists Σ, 0, i'. split; [| repeat split; reflexivity].
      eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      split; [assumption | left; split; [reflexivity| lia]].
    + (* [comment removed for export] *)
      awalk (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; exact (accok_aclient _ _ _ _ pi 4 zz AKI Hzz)| exact I]]).
      agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [clear - HxS LOW LOR; lia| clear - HxO; tauto]).
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      exists Σ, 1, 0. split; [| repeat split; reflexivity].
      eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      split; [assumption | right; split; reflexivity].
Qed.
End GETINDEX.

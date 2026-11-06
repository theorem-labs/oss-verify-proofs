(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit LeptL_kit LeptL_zero_loop.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma sdiv32_small : forall wd, 0 <= wd < 2^31 ->
  bv_swrap 32 (bv_swrap 32 ((wd + bv_swrap 32 (bv_wrap 32 ((wd / 2147483648) mod 18446744073709551616) / 134217728)) mod 18446744073709551616) / 32) = wd / 32.
Proof.
  intros wd H. rewrite (Z.div_small wd 2147483648) by lia. change (0 mod 18446744073709551616) with 0. change (bv_wrap 32 0) with 0.
  change (0 / 134217728) with 0. rewrite (bv_swrap_small 32 0) by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite Z.add_0_r. rewrite Z.mod_small by lia. rewrite (bv_swrap_small 32 wd) by (change (bv_half_modulus 32) with (2^31); lia).
  assert (R : 0 <= wd / 32 < 2^31) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

Section ZERO.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixZero_ok : pixZero_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix pe v cv x
    FDO MST -> -> -> POBJ VDATA OPE PEC ENV RES.
  unfold lpost, lenv, keeps, keepsL, lres, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct OPE as (OWNF & PE0 & PE8 & PESH & PESEG).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixZero, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pe, pe + 4)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof ST as (STa & STb & _).
  assert (OWN : accok (rt_live RT Σ) (rt_frames RT Σ) m pe 4) by (right; exact OWNF).
  assert (PELO : pe + 4 <= lo).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _).
    pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN in R. lia. }
  (* [comment removed for export] *)
  assert (PEP : pe + 4 <= pix \/ pix + 64 <= pe).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). specialize (R pix 64 PIN). lia. }
  assert (PED : pe + 4 <= p_data v \/ p_data v + rsize v <= pe).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). specialize (R (p_data v) (rsize v) DIN). lia. }
  park OWNF.
  chunk_facts RT AF GP pix 64.
  chunk_facts RT AF GP (p_data v) (rsize v).
  unfold pix_cells in PXC.
  (* [comment removed for export] *)
  pose proof (af_acc_live RT AF Σ m (p_data v) (rsize v) ART0 DIN) as (WRD & _).
  unfold rsize in *. apply wr_at_rw_CB in WRD; [| lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL.
  refresh RT AF. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 128, usp); (pe, pe + 4)] [0x926fc].
  sx32_fix.
  Time awalk [0x926fc].
  assert (DBND : 1 <= p_d v <= 32) by (cbn [In] in HD1; lia).
  set (wd := p_w v * p_d v).
  assert (WDB : 0 < wd <= 640000) by (unfold wd; nia).
  rewrite (sx32_small (p_d v)) by lia. rewrite !(unsigned_lit (p_d v)) by lia.
  replace (p_d v * p_w v) with wd by (unfold wd; ring).
  swrap32_fix. rewrite !(Z.mod_small wd 18446744073709551616) by lia.
  change 31 with (Z.ones 5). rewrite !(Z.land_ones wd 5) by lia. change (2 ^ 5) with 32.
  rewrite (sdiv32_small wd) by lia.
  apply u8arr_of_rw_cells in DBC. destruct DBC as [RB _].
  assert (WPLE : p_wpl v = (wd + 31) / 32) by (unfold wd; exact HWPL).
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (zero_rows (Z.to_nat (p_h v)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (p_data v) (p_wpl v) (p_h v) pe wd (wd / 32) (wd mod 32) dbs _) as ZR end.
    replace (p_data v + 4 * (0 * p_wpl v)) with (p_data v) in ZR by lia.
    eapply ZR.
    all: lazymatch goal with
         | |- bytes_at _ _ _ _ => exact RB
         | |- rw_cells _ _ _ _ => eassumption
         | |- acc _ _ _ _ => idtac
         | |- mem_inv _ _ => assumption
         | |- Z.of_nat (length _) = _ => rewrite DBL; lia
         | |- _ => idtac
         end.
    all: unfold parked in *.
    all: lazymatch goal with
         | |- acc _ _ _ _ => assumption
         | |- Z.of_nat (Z.to_nat _) = _ => rewrite Z2Nat.id by lia; lia
         | |- _ => first [ lia | (Z.div_mod_to_equations; lia) ]
         end. }
  intros ms' PO. unfold zero_exit in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & y & m' & -> & MU' & WM' & MI' & PEC').
  loop_art RT AF Σ m' (usp + -128) MU'
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; exact (accok_aclient _ _ _ _ pe 4 zz OWN Hzz)| exact I]]).
  clear PEC RB.
  lazymatch type of MU' with munch _ ?mm m' =>
    loop_transport mm m' MU' ltac:(fun Hx => clear - Hx PESEG PELO PEP PED LOW LOR SPT SPB STa CKR CKR0; unfold parked in *; lia) end.
  cwalk (@nil Z).
  cps_stop.
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                   split; [lia| split; [tauto| exact I]]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  exists Σ. do 2 eexists.
  split; [| repeat split; first [reflexivity | lia]].
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [exact ARTl| split; [exact MI'| split; [| assumption]]]| split; assumption]|].
  - repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
  - split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))| exact PEC'].
Qed.
End ZERO.

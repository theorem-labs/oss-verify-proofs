(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf Lept_objkit LeptL_kit
  Gm_iface Gq_iface Gm_kit Gm_leaf Gm_livekit Gm_livekit2 Gq_clone Gq_rmc_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section RMC_N0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.

Theorem pixRemoveColormap_n0 : pixRemoveColormap_case RT 0 false.
Proof using AF GP RC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> -> POBJ D8 VDATA NZV UC TRS ENV RES AL CM.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixRemoveColormap, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  clearbody usp.
  unfold LSTK, STDERR_STACK, REMOVE_COST, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (LVF := rt_live RT Σ) in *.
  set (PF0 := fun a => aclient LVF (rt_frames RT Σ) usp a).
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pix + 20, pix + 24)] a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ)) by (intros e He; exact He).
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  destruct POBJ as (PXC & (PIN & PX0 & PX16 & _) & HDROK & PDAT & PCM).
  cbv iota in CM.
  clear PCM.
  pose proof (af_live_range RT AF Σ m pix 64 ART0 PIN) as (_ & PXR & PXS). unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in PXR, PXS.
  pose proof (gp_live_hi RT GP Σ m pix 64 ART0 PIN) as PXH.
  unfold pix_cells in PXC.
  clear NZV TRS.
  park_disj. carve_frame 320%nat ST.
  idtac "MARK carved".
  Time walk_to AF MST [(usp - 320, usp)] [e_stack_malloc 3%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_3 RT GP) as SM3; unfold stack_malloc_contract' in SM3; eapply SM3 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 3%nat 512 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 3%nat 512 pix 64.
  pose proof (proj2 FSH) as WRSH. cbn [cells_size csize Nat.add] in WRSH. change (Z.of_nat 64) with 64 in WRSH.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "MARK frame open".
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [0x9a59c].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  park_disj.
  idtac "MARK header done".
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [0x95318; 0x9a5ac; 0x9a5c8].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  park_disj.
  assert (AGF1 : agree_on PF m _) by (eapply agree_sub; [exact AGF| intros zz [Hz _]; exact Hz]). clear AGF. rename AGF1 into AGF.
  assert (PFS1 : forall a, PF a -> usp <= a \/ a < lo) by (intros a [Ha _]; exact (PFS a Ha)).
  assert (PFO : forall a, PF a -> (a < pix + 20 \/ pix + 24 <= a)).
  { intros a [_ Ho]. cbn [outside] in Ho. lia. }
  idtac "MARK at clone".
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64); (pix + 20, pix + 24)] [0x9a78c].
  assert (AMO : amo_aligned AW (Z_to_bv 64 (pix + 20)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. clear - PX16. Z.div_mod_to_equations; lia. }
  amo_step AMO.
  rewrite (amo_inc_bytes 1 ltac:(lia)).
  mem_after_store.
  idtac "MARK stored".
  Time awalk [0x9a78c].
  Time awalk [e_set_shadow 245].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                        split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); pose proof (PFO _ Hx); destruct Hx as [Hx Ho]; destruct (NFA _ Hx) as [N1 N2];
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "MARK at set_shadow".
  eapply cps_seq.
  { pose proof (rc_set_shadow RT RC 245) as SS; unfold set_shadow_contract in SS; eapply SS with (lo := lo) (d := fr / 8 + 2147450880) (n := 64); rt_side idtac.
    all: first [ exact WRSH | unfold set_shadow_vals; cbn; tauto | idtac ]. }
  idtac "MARK set_shadow applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                                 | pose proof (NFA _ (proj1 Hx)) as [N1 N2]; unfold shad, SHB in *; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "MARK after set_shadow".
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [0x9a7e0].
  frame_release_g RT AF GP MST Σ fr 3%nat 512 PF AGF PFS1 usp lo 0x9a7e8
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
    ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct Hx as [Hx Ho]; destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
    ltac:(fun Hx => exact (proj1 Hx))
    ltac:(fun fl FLN => idtac).
  idtac "MARK released".
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 448, usp)] (@nil Z).
  
  cps_stop.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  assert (LVE : rt_live RT S2 = LVF) by (unfold LVF; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity).
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pix, v end.
  split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [split; [exact ART2| split; assumption]| split; assumption]|].
    split.
    + intros a Ha Ho. apply AGF. split; [| exact Ho]. exact Ha.
    + left. split; [exact CM|]. split; [reflexivity|].
      unfold pix_obj_rc, pix_cells_rc, chunk. rewrite LVE.
      split; [exact PXC|]. split; [repeat split; try assumption; lia|]. split; [exact HDROK|].
      split; [exact PDAT| left; exact CM].
  - rewrite LVE.
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
    split; [intros _; reflexivity|]. split; [intros HH; exfalso; exact (HH CM)|].
    repeat split; auto; lia.
Qed.
End RMC_N0.

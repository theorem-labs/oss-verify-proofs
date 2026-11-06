(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_selkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section SELSET.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem selSetElement_ok : selSetElement_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo sel v row col ty
    FDO MST -> -> -> -> -> SB HROW HCOL HTY ENV.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  pose proof SB as (SC & (SIN & S0 & S16 & _) & HSY & HSX & HLEN & DC & (DIN & D0 & D16 & _) & ROWS & NDUP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_selSetElement, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  unfold sel_cells in SC.
  set (rp := nth (Z.to_nat row) (s_rows v) 0) in *.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(rp, rp + 4 * s_sx v)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (RIN0 : In rp (s_rows v)) by (apply nth_In; lia).
  pose proof (proj1 (Forall_forall _ _) ROWS rp RIN0) as (RIN & R0 & R16 & _).
  chunk_facts RT AF GP sel 32.
  chunk_facts RT AF GP (s_data v) (8 * s_sy v).
  chunk_facts RT AF GP rp (4 * s_sx v).
  assert (NES : rp <> sel /\ rp <> s_data v).
  { apply NoDup_cons_iff in NDUP as (N1 & N2). apply NoDup_cons_iff in N2 as (N3 & _).
    split; [intros E; apply N1; right; rewrite <- E; exact RIN0| intros E; apply N3; rewrite <- E; exact RIN0]. }
  pose proof (live_addr_disj RT AF Σ m rp (4 * s_sx v) sel 32 ART0 RIN SIN (proj1 NES)) as QRS.
  pose proof (live_addr_disj RT AF Σ m rp (4 * s_sx v) (s_data v) (8 * s_sy v) ART0 RIN DIN (proj2 NES)) as QRD.
  rewrite <- (map_map (Z_to_bv 64) C8) in DC. apply rw_cells_C8s_u64arr in DC.
  remember (map (Z_to_bv 64) (s_rows v)) as ws eqn:EWS.
  assert (ULEN : Z.of_nat (length ws) = s_sy v) by (rewrite EWS, map_length; exact HLEN).
  assert (NTH : nth_error ws (Z.to_nat row) = Some (Z_to_bv 64 rp)) by (rewrite EWS; apply map_nth_error; unfold rp; apply nth_error_nth'; lia).
  pose proof (proj1 (af_acc_live RT AF Σ m rp (4 * s_sx v) ART0 RIN)) as WRR.
  apply wr_at_rw_CB in WRR; [| lia]. destruct WRR as (rbs & RBC).
  pose proof RBC as [[[RBL _] _] _]. cbn in RBL. apply u8arr_of_rw_cells in RBC.
  destruct (u8arr_u32arr m rp rbs (s_sx v) RBC ltac:(rewrite RBL; lia)) as (rws & UAR & UARL).
  clear RBC RBL.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 16, usp); (rp, rp + 4 * s_sx v)] (@nil Z).
  sx32_fix. awalk (@nil Z).
  sx32_fix. awalk (@nil Z).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_read asegs mm (s_data v) ws row (Z_to_bv 64 rp) (Z_to_bv 64 (s_data v + row * 8)) DC NTH ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD end.
  lstep. clear RD.
  awalk (@nil Z).
  arr_sw rp col (rp + col * 4).
  awalk (@nil Z).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                      intros zz Hzz; right; right; left; exists rp, (4 * s_sx v); split; [exact RIN| lia]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; lia)
  end.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  eexists.
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
  split; [intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
  destruct SB as (_ & CS & _ & _ & _ & _ & CD & _ & _).
  unfold sel_body. split; [unfold sel_cells; assumption|]. split; [exact CS|]. split; [exact HSY|]. split; [exact HSX|]. split; [exact HLEN|].
  split; [rewrite <- (map_map (Z_to_bv 64) C8), <- EWS; apply u64arr_rw_cells_C8s; assumption|].
  split; [exact CD|]. split; [exact ROWS| exact NDUP].
Qed.
End SELSET.

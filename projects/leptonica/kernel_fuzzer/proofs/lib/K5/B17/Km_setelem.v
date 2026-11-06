(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit D_iface D_defs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import LeptB_guard LeptB_guard2 LeptB_guard3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_kernelSetElement : Z := 0x91f14.

Section SETELEM.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

(* [comment removed for export] *)
Definition kel_cells (sy sx cy cx data : Z) : list cell :=
  [C4 (Z_to_bv 64 sy); C4 (Z_to_bv 64 sx); C4 (Z_to_bv 64 cy); C4 (Z_to_bv 64 cx); C8 (Z_to_bv 64 data)].

Definition kernelSetElement_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (kel sy sx cy cx data i j rp : Z) (x0 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 kel -> a1 = Z_to_bv 64 i -> a2 = Z_to_bv 64 j ->
  0 <= i < sy -> 0 <= j < sx -> sy < 2^31 -> sx < 2^31 ->
  rw_cells asegs m kel (kel_cells sy sx cy cx data) -> chunk (rt_live RT Σ) kel 24 ->
  rw_cells asegs m (data + 8 * i) [C8 (Z_to_bv 64 rp)] -> chunk (rt_live RT Σ) data (8 * sy) ->
  rw_cells asegs m (rp + 4 * j) [C4 x0] -> chunk (rt_live RT Σ) rp (4 * sx) ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelSetElement m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(rp + 4 * j, rp + 4 * j + 4)] m m'
          /\ (exists x, rw_cells asegs m' (rp + 4 * j) [C4 x])) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

Theorem kernelSetElement_ok : kernelSetElement_cps.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo kel sy sx cy cx data i j rp x0
    FDO MST -> -> -> -> IB JB SYB SXB KC (KIN & K0 & K16 & KN) DC (DIN & D0 & D16 & DN) RC (RIN & R0 & R16 & RN) ENV.
  unfold kel_cells in KC.
  unfold lpost, lenv, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_kernelSetElement in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(rp + 4 * j, rp + 4 * j + 4)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]. }
  pose proof ST as (STa & STb & _).
  chunk_facts RT AF GP kel 24. chunk_facts RT AF GP data (8 * sy). chunk_facts RT AF GP rp (4 * sx).
  refresh RT AF.
  idtac "SE-PREFIX".
  (* [comment removed for export] *)
  cps_walk AF MST.
  pose proof (munch_refl [(usp - 16, usp); (rp + 4 * j, rp + 4 * j + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  awalk0.
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
  idtac "SE-WALK".
  (* [comment removed for export] *)
  rewrite ?(sx32_small sy) by (clear - IB SYB; lia).
  awalk0.
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
  idtac "SE-WALK2".
  (* [comment removed for export] *)
  rewrite ?(sx32_small sx) by (clear - JB SXB; lia).
  awalk0.
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
  idtac "SE-WALK3".
  (* [comment removed for export] *)
  replace (data + 8 * i) with (data + i * 8) in * by (clear; lia).
  replace (rp + 4 * j) with (rp + j * 4) in * by (clear; lia).
  awalk0.
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
  idtac "SE-WALK4".
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_read_at asegs mm (data + i * 8) [C8 (Z_to_bv 64 rp)] 0 (C8 (Z_to_bv 64 rp)) 8 (Z_to_bv 64 (data + i * 8)) DC eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as RD end.
  lstep. clear RD.
  idtac "SE-LD".
  awalk0.
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
  idtac "SE-WALK5".
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_store_ok_at asegs mm (rp + j * 4) [C4 x0] 0 (C4 x0) 4 (Z_to_bv 64 (rp + j * 4)) RC eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK end.
  zstep.
  idtac "SE-ST".
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?E') ?bs) _) => idtac "STORED-AT" E' "BYTES" bs end.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?E') (le4 ?v)) _) =>
    assert (RC2 : rw_cells asegs (write_to_mem mm (wa E') (le4 v)) (rp + j * 4) [C4 v])
      by (pose proof (rw_cells_write asegs mm (rp + j * 4) [C4 x0] 0 (C4 x0) (C4 v) RC eq_refl eq_refl) as W;
          replace (rp + j * 4 + Z.of_nat 0) with E' in W by (cbn; lia); cbn in W; apply W; cbn; auto)
  end.
  idtac "SE-RC2".
  clear RC. store_done. rename RC2 into RC.
  idtac "SE-STDONE".
  awalk0.
  lazymatch goal with |- _ => idtac "GOAL-SHAPE" end.
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ ?pc _ _ ?mf _))) _ => idtac "CPS-PC:" pc | |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "EVT-PC:" pc | |- ?g => idtac "OTHER" end.
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists rp, (4 * sx); split; [exact RIN| lia]| exact I]]).
  idtac "SE-ART".
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as HxS; cbn [outside] in Hx2;
                                   repeat split; try exact I; clear - HxS Hx2 LOW LOR; lia).
  idtac "SE-AGF".
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  exists Σ. split; [| repeat split; reflexivity].
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
  idtac "SE-LPOST".
  split.
  - intros a Ha Ho. apply AGF. split; [exact Ha|]. cbn [outside] in Ho |- *. clear - Ho. lia.
  - exists (reg_get F 10). first [exact RC | (replace (rp + 4 * j) with (rp + j * 4) by (clear; lia); exact RC)].
Qed.
End SETELEM.

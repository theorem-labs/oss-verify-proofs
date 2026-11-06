(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Gm_iface Gm_ropkit Gm_rasterop_epi Fh_rop_iface Fh_rasterop1_defs LeptB_guard LeptB_guard2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tlia ::= sf_clear_big;   (* [comment removed for export] *)
              first [ xlia zchecker
                    | zn_lits; xlia zchecker
                    | zn_lits; zdiv_lits; xlia zchecker
                    | sf_unhide; unpark_all; zify_prune_sub;
                      first [ zn_lits; xlia zchecker
                            | zn_lits; zdiv_lits; xlia zchecker
                            | zn_lits; Z.div_mod_to_equations; xlia zchecker
                            | Zify.zify; xlia zchecker ]
                    | Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
Ltac local_acc FSH fr idx off FR64 NAME :=
  let T := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in let B := fresh "B" in
  pose proof FSH as T; split_at T idx T2; split_at T2 1%nat T3; clear T T3;
  lazymatch type of T2 with rw_cells _ ?mm _ _ =>
    assert (NAME : acc asegs mm (fr + off) 4)
      by (destruct T2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + off) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
          let c := eval vm_compute in (2147450880 + Z.of_nat idx) in
          replace (shad (fr + off)) with (fr / 8 + c) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
          exact B) end; clear T2.
(* [comment removed for export] *)
Ltac dedup_ro := repeat match goal with H1 : ro_cells asegs ?m ?a ?c, H2 : ro_cells asegs ?m ?a ?c |- _ => clear H2 end.
Ltac drop_ro a := repeat match goal with H : ro_cells asegs _ a _ |- _ => clear H end.
Ltac drop_acc a := repeat match goal with H : acc asegs _ a _ |- _ => clear H end.
Ltac drop_cells a := repeat match goal with H : rw_cells asegs _ a _ |- _ => clear H end.
Section ROPS1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis LOW : rasteropLow_src1_cps RT.
Lemma rop_src1_c0 : rop_src1_case RT 0.
Proof using AF GP LOW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixd pixs vd vs cvd cvs dx dy dw dh sx sy FDO MST -> -> -> -> -> -> -> -> -> SYC POD PD8 PDN POS PS8 PSN NEQ DNEQ RIND RINS DX4 SX4 ENV RES AL.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOWB & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct POD as (PXD & (INPD & PXD0 & PXD16 & _) & HOKD & DATD & _).
  destruct DATD as [E|((INDD & DD0 & DD16 & DDN) & DDNE)]; [contradiction|].
  destruct POS as (PXS & (INPS & PXS0 & PXS16 & _) & HOKS & DATS & _).
  destruct DATS as [E|((INDS & DS0 & DS16 & DSN) & DSNE)]; [contradiction|].
  destruct vd as [w h d spp wpl xres yres inf spec pcm data].
  destruct vs as [ws hs ds spps wpls xress yress infs specs pcms datas].
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in *.
  unfold pix_cells in PXD, PXS. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD, PXS.
  unfold rsize in *. cbn [p_wpl p_h] in *. subst d ds.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixRasterop, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof LOW as RL. unfold rasteropLow_src1_cps in RL.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(data, data + 4 * (wpl * h))] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (WPR : 0 < w <= 20000) by (destruct HOKD as (_ & HW & _); cbn [p_w] in HW; exact HW).
  assert (HPR : 0 < h <= 20000) by (destruct HOKD as (_ & _ & HH & _); cbn [p_h] in HH; exact HH).
  assert (WSR : 0 < ws <= 20000) by (destruct HOKS as (_ & HW & _); cbn [p_w] in HW; exact HW).
  assert (HSR : 0 < hs <= 20000) by (destruct HOKS as (_ & _ & HH & _); cbn [p_h] in HH; exact HH).
  assert (WPLE : wpl = (w + 31) / 32) by (destruct HOKD as (_ & _ & _ & HWPL & _); cbn [p_w p_d p_wpl] in HWPL; rewrite Z.mul_1_r in HWPL; exact HWPL).
  assert (WPLB : 0 < wpl <= 5001) by (clear - WPLE WPR; subst wpl; Z.div_mod_to_equations; lia).
  assert (RSZ : 0 < 4 * (wpl * h) <= 67108864) by (destruct HOKD as (_ & _ & _ & _ & HRS); cbn [p_wpl p_h] in HRS; exact HRS).
  assert (WPLSE : wpls = (ws + 31) / 32) by (destruct HOKS as (_ & _ & _ & HWPL & _); cbn [p_w p_d p_wpl] in HWPL; rewrite Z.mul_1_r in HWPL; exact HWPL).
  assert (WPLSB : 0 < wpls <= 5001) by (clear - WPLSE WSR; subst wpls; Z.div_mod_to_equations; lia).
  assert (RSZS : 0 < 4 * (wpls * hs) <= 67108864) by (destruct HOKS as (_ & _ & _ & _ & HRS); cbn [p_wpl p_h] in HRS; exact HRS).
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP data (4 * (wpl * h)).
  chunk_facts RT AF GP pixs 64. chunk_facts RT AF GP datas (4 * (wpls * hs)).
  park_disj.
  carve_frame 224%nat ST.
  clear_acc.
  walk_to AF MST [(usp - 224, usp)] [0x4c1bc].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  eapply cps_seq.
  { eapply (gp_stack_malloc_1 RT GP) with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [auto| auto| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
  fframe_chunk RT AF fr 1%nat 128 pixd 64.
  fframe_chunk RT AF fr 1%nat 128 data (4 * (wpl * h)).
  fframe_chunk RT AF fr 1%nat 128 pixs 64.
  fframe_chunk RT AF fr 1%nat 128 datas (4 * (wpls * hs)).
  refresh RT AF. unfold shad, SHB in *. clear_acc. dedup_ro. park_disj.
  walk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa23c4].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. unfold shad, SHB in *.
  dedup_ro. drop_acc data. drop_acc datas. drop_ro 933792. drop_ro 980768.
  local_acc FSH fr 4%nat 32 FR64 ACCW. local_acc FSH fr 6%nat 48 FR64 ACCH. local_acc FSH fr 8%nat 64 FR64 ACCD.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa240c; 0xa3328; 0xa2618].
  lstep. lstep. lstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => change c with true; cbv iota end.
  awalk [0xa3328; 0xa2618; 0xa24d8].
  clear ACCW ACCH ACCD.
  local_acc FSH fr 10%nat 80 FR64 ACCSW. local_acc FSH fr 12%nat 96 FR64 ACCSH. local_acc FSH fr 14%nat 112 FR64 ACCSD.
  awalk [0xa3328; 0xa2618; 0xa24e8].
  clear ACCSW ACCSH ACCSD.
  rewrite !(sx32_small 1) by lia.
  awalk [0xa3328; 0xa2618; 0xa2548].
  rewrite ?(sx32_small w), ?(sx32_small h), ?(sx32_small 1), ?(sx32_small wpl), ?(sx32_small ws), ?(sx32_small hs), ?(sx32_small wpls) by lia.
  awalk [0xa3328; 0xa2618].
  rewrite ?(sx32_small w), ?(sx32_small h), ?(sx32_small 1) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { eapply RL with (lo := lo) (datad := data) (dpw := w) (dph := h) (dwpl := wpl) (dx := dx) (dy := dy) (dw := dw) (dh := dh)
                   (datas := datas) (spw := ws) (sph := hs) (swpl := wpls) (sx := sx) (sy := sy); rt_side idtac.
    - unfold raster1, chunk. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      repeat split; first [assumption | lia].
    - unfold raster1, chunk. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      repeat split; first [assumption | lia].
    - lenv_tac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [HxA HxO]; split; [apply (aclient_mono _ _ usp _ _ _ _ HxA); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact HxO]).
  unfold shad, SHB in *. park_disj.
  (* [comment removed for export] *)
  repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
  repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa2470].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                       destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  pose proof (proj2 FRM) as WFR. pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add] in WFR, WFS.
  change (Z.of_nat 120) with 120 in WFR. change (Z.of_nat 16) with 16 in WFS.
  lazymatch goal with FRx : rw_cells asegs _ (usp + -224) _ |- _ => split_before FRx (C8 s11) FRe end.
  subst QF.
  eapply (rop_epi RT AF GP Σ) with (sp := sp) (lo := lo) (fr := fr) (fb := usp + -224); try eassumption.
  (* [comment removed for export] *)
  all: lazymatch goal with
       | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
       | |- _ - 1 <= rt_credit _ _ =>
           repeat match goal with H : context [rt_credit] |- _ => revert H end; repeat match goal with H : _ |- _ => clear H end; intros; lia
       | |- _ \/ _ => unfold parked in * |-; assumption
       | |- _ => first [ assumption | (clear - AL; unfold usp in *; cbn [cells_size csize Nat.add]; lia) ]
       end.
Qed.
End ROPS1.

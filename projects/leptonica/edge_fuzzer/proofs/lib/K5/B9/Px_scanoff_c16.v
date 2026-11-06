(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_gmax_defs Ed_iface Px_defs Px_kit Px_scanoff_loop LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac guard_fix ::= try sx32_fix; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end; swrap_fix; po_fix; al_fix; try mulh_fix.

(* [comment removed for export] *)
Definition scanoff_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix ploc x y : Z) (v : pixv) (cv : cmapv) (old : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> s32 a1 x -> s32 a2 y -> a3 = Z_to_bv 64 1 -> a4 = Z_to_bv 64 ploc ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_d v = 1 -> p_data v <> 0 -> -1 <= x <= p_w v - 1 -> 0 <= y < p_h v ->
  optrS sp ploc 4 -> rw_cells asegs m ploc [C4 old] ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 2 0 (SCANOFF_COST x) -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                                         e_pixGetLastOffPixelInRun m)))
    (fun c => exists (Σ' : rts RT) (r : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(ploc, ploc + 4)] m m'
          /\ rw_cells asegs m' ploc [C4 (Z_to_bv 64 r)] /\ 0 <= r <= x + 1) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - SCANOFF_COST x <= rt_credit RT Σ').

Section SCANOFF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Hypothesis GETPIX : pixGetPixel1_cps RT.

Lemma scanoff_c16 : scanoff_case RT 16.
Proof using AF GP GETPIX.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix pval x y v cv old
    FDO MST -> -> [XR ->] [YR ->] -> -> POBJ D1 VDATA XB YB OPM PMC ENV RES AL.
  unfold lpost, lenv, keeps, keepsL, lres, optrS in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). destruct OPM as (PMLO & PMT & PM4).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixGetLastOffPixelInRun, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SCANOFF_COST in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF0 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pval, pval + 4)] a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  (* [comment removed for export] *)
  assert (PMCL : forall zz, pval <= zz < pval + 4 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp zz)
    by (intros zz Hzz; left; unfold USTACK_TOP; lia).
  assert (PMP : pval + 4 <= pix \/ pix + 64 <= pval).
  { pose proof (af_live_range RT AF Σ m pix 64 ART0 PIN) as (_ & R & _). unfold STACK_WIN in R. lia. }
  assert (PMD : pval + 4 <= p_data v \/ p_data v + rsize v <= pval).
  { pose proof (af_live_range RT AF Σ m (p_data v) (rsize v) ART0 DIN) as (_ & R & _). unfold STACK_WIN in R. lia. }
  chunk_facts RT AF GP pix 64.
  chunk_facts RT AF GP (p_data v) (rsize v).
  unfold pix_cells in PXC.
  pose proof (af_acc_live RT AF Σ m (p_data v) (rsize v) ART0 DIN) as (WRD & _).
  unfold rsize in *. apply wr_at_rw_CB in WRD; [| lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL.
  pose proof DBC as DBC0. hide DBC0.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a).
  { intros q k a Hq Ha. split; [right; right; left; exists q, k; split; [exact Hq| lia]|]. cbn [outside]. split; [| exact I].
    pose proof (af_live_range RT AF Σ m q k ART0 Hq) as (_ & R & _). unfold STACK_WIN in R. lia. }
  hide POBJ.
  carve_frame 176%nat ST.
  walk_to AF MST [(usp - 176, usp)] [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 1%nat 128 pix 64.
  fframe_chunk RT AF fr 1%nat 128 (p_data v) (4 * (p_wpl v * p_h v)).
  lazymatch goal with A : ART RT ?S ?mm, FRSx : rt_frames RT ?S = (fr, 1%nat) :: ?frs0 |- _ =>
    assert (FOD : forall xx, pval <= xx < pval + 4 -> (xx < fr \/ fr + 128 <= xx) /\ (xx < shad fr \/ shad (fr + 128) <= xx))
      by (intros xx Hxx; apply (new_frame_apart RT AF S mm fr 1%nat frs0 (rt_live RT Σ) usp xx A FRSx);
          [ intros e He; repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | left; unfold USTACK_TOP; lia ]) end.
  pose proof (FOD pval ltac:(lia)) as FOE; specialize (FOD (pval + 4 - 1) ltac:(lia)); unfold shad, SHB in FOD, FOE.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 176, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x12d214].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>   (* [comment removed for export] *)
    assert (ACCP : acc asegs mm pval 4)
      by (apply (af_acc_stack RT AF S mm pval 4 A); [repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia | unfold USTACK_TOP; lia]) end.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCDP.
  assert (AGF1 : agree_on PF m _) by (eapply agree_sub; [exact AGF| intros zz [Hz _]; exact Hz]). clear AGF. rename AGF1 into AGF.
  park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 240, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pval, pval + 4)]
               [e_stack_malloc 1%nat; 0x12d4dc; 0x12d550; 0x12d390].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with FRMx : rw_cells asegs ?mm fr _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof FRMx as FRT; split_at FRT 7%nat FRV; destruct FRV as [_ FRW]; cbn [cells_size csize Nat.add] in FRW;
    destruct (wr_at_rw_CB mm (fr + 64) 4 (wr_at_sub mm (fr + 52) 68 (fr + 64) 4 FRW ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (vjunk & VALB);
    destruct (cb4_c4 mm (fr + 64) _ VALB) as (vold & VALC); clear FRW VALB end.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; apply (aclient_mono _ _ usp _ _ _ _ (PMCL zz Hzz)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]]]]).
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx;
    agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; destruct Hx as [_ HxO];
                             cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]) end.
  eapply cps_seq.
  { eapply (scanoff_scan RT AF GP GETPIX x) with (lo := lo) (v := v) (cv := cv) (live := rt_live RT Σ) (frames := rt_frames RT Σ).
    all: try eassumption; try lia; try reflexivity.
    1: unfold hid in POBJ; lazymatch goal with PXCx : rw_cells asegs ?mm pix _ |- pix_obj _ ?mm _ _ _ => exact (pix_obj_agree (rt_live RT Σ) PF m mm pix v cv POBJ AGF PML PXCx) end.
    all: unfold STACK_WIN, LSTK, RT_STACK, USTACK_TOP; repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => pose proof (NFA _ (proj1 Hx)) as NF1; destruct Hx as [Hx HxO]; split;
                [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                | revert HxO NF1; clear; cbn [outside]; intros HxO NF1; repeat split; try exact I; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>   (* [comment removed for export] *)
    assert (ACCP : acc asegs mm pval 4)
      by (apply (af_acc_stack RT AF S mm pval 4 A); [repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia | unfold USTACK_TOP; lia]) end.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 176, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pval, pval + 4)] [e_stack_malloc 1%nat; 0x12d3fc].   (* [comment removed for export] *)
    (* [comment removed for export] *)
  lazymatch goal with |- context [bv_swrap 32 (?l mod 18446744073709551616 + 1)] =>
    replace (bv_swrap 32 (l mod 18446744073709551616 + 1)) with (l + 1)
      by (destruct (Z.eq_dec l (-1)) as [->|NE]; [vm_compute; reflexivity| rewrite Z.mod_small by lia; symmetry; apply bv_swrap_small; change (bv_half_modulus 32) with (2^31); lia]) end.
  brF.
  awalk [e_stack_malloc 1%nat; 0x12d3fc].   (* [comment removed for export] *)
  frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x12d3fc
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; apply (aclient_mono _ _ usp _ _ _ _ (PMCL zz Hzz)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; destruct Hx as [_ HxO];
                      cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact (proj1 Hx))
      ltac:(fun fl FLN =>
              assert (FLPM : fl < pval \/ pval + 4 <= fl)
                by (left; lia)).   (* [comment removed for export] *)
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 176, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -176) |- _ => release_frame FR ST' usp end.
  cps_stop.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch goal with PMCx : rw_cells asegs _ pval [C4 _] |- _ =>
    rewrite ?sx32_small in PMCx by lia; rewrite ?unsigned_lit in PMCx by lia; rewrite ?swrap32_small in PMCx by lia end.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => lazymatch goal with PMCx : rw_cells asegs _ pval [C4 (Z_to_bv 64 ?r)] |- _ => exists S, r end end.
  split; [| unfold GETPIXEL_COST in *; alg_tac].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
  split.
  { repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. intros a Ha Ho; exact (AGF a (conj Ha Ho)). }
  split; [lazymatch goal with PMCx : rw_cells asegs _ pval _ |- _ => exact PMCx end|].
  lia.
Qed.

End SCANOFF.

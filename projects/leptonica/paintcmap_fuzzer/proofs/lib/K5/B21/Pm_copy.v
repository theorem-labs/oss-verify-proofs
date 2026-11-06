(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_iface Pm_iface2 Pm_iface4 Pm_ckit Pm_okit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Ltac shbr_inv8m :=
  match goal with
  | K : shk ?m ?b ?X, ACC : acc asegs ?m ?a ?n |- evt _ _ (MS _ _ (if _ then _ else _) _ _ ?m _) =>
      let OK := fresh "SHOK" in
      assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok m a n X 8 b ACC K); lia);
      apply sh_ok_8 in OK; [ | lia ]; rewrite ?OK; brT; clear K OK
  end.

(* [comment removed for export] *)
Lemma mul4_guard0 : forall x, 0 <= x < 2^29 ->
  bv_swrap 32 (bv_wrap 32 ((x + 536870912) mod 18446744073709551616) / 1073741824) = 0.
Proof.
  intros x Hx. rewrite Z.mod_small by lia. unfold bv_wrap. rewrite Z.mod_small by (unfold bv_modulus; change (2 ^ Z.of_N 32) with (2^32); lia).
  rewrite Z.div_small by lia. reflexivity.
Qed.

Section PIXCOPY.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis TMPL : pixCreateTemplateNoInit_nn_cps RT.

Theorem pixCopy_ok : pixCopy_nn_cps RT.
Proof using AF RC GP TMPL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pixs v cv
    FDO MST -> -> -> POBJ VDAT ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixCopy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof TMPL as TM. unfold pixCreateTemplateNoInit_nn_cps in TM. unfold RASTER_COST in TM.
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & DATs & _).
  destruct DATs as [DZ|((DSIN & DS0 & DS16 & DSN) & DSNE)]; [contradiction|].
  unfold pix_cells in PXC. unfold rsize in *.
  set (dsrc := p_data v) in *.
  pose proof (af_live_range RT AF Σ m dsrc _ ART0 DSIN) as (_ & DSR & _). unfold STACK_WIN in DSR.
  assert (WPLB : 0 < p_wpl v <= 20001) by (rewrite HWPL; clear - HD1 HW1; cbn in HD1; Z.div_mod_to_equations; nia).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pixs 64.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 64, usp)] [0x8f4a0; 0x5daa0; 0x5d604; 0x8db6c].
  (* [comment removed for export] *)
  rewrite ?(sx32_small (p_wpl v)) by lia. rewrite ?(unsigned_lit (p_wpl v)) by lia.
  rewrite (mul4_guard0 (p_wpl v)) by lia. br.
  Time awalk [0x8f4a0; 0x5daa0; 0x5d604; 0x8db6c].
  rewrite ?(sx32_small (p_h v)) by lia. rewrite ?(unsigned_lit (p_h v)) by lia.
  rewrite ?(swrap32_small (p_wpl v * 4)) by lia.
  rewrite ?(Z.mod_small (p_wpl v * 4)) by lia.
  rewrite ?(swrap32_small (p_wpl v * 4 * p_h v)) by lia. try br.
  Time awalk [0x8f4a0; 0x5daa0; 0x5d604; 0x8db6c].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply TM with (lo := lo) (pixs := pixs) (v := v) (cv := cv); rt_side idtac.
    all: lazymatch goal with
         | |- pix_obj _ ?mc _ _ _ => exact (pix_obj_keep _ m mc pixs v cv (keeps_live_of_agf _ _ _ _ _ AGF) POBJ)
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with HC : pm_hdr_copy _ ?vv _ ?cc |- _ =>
    lazymatch goal with H : pix_obj _ _ ?p vv cc |- _ => rename H into POBJ1; rename HC into HCOPY; set (pixd := p) in * end end.
  lazymatch goal with H : pixd <> 0 |- _ => rename H into PNZ end.
  lazymatch goal with H : rt_live RT _ = pm_copy_live pixd _ _ _ |- _ => rename H into LVH end.
  - (* [comment removed for export] *)
    lazymatch type of POBJ1 with pix_obj _ _ _ ?vv ?cc => set (vd := vv) in *; set (cvd := cc) in * end.
    destruct HCOPY as (VW & VH & VD & VWPL & VDATA & VCM0 & VCM).
    pose proof POBJ1 as (PXD & (PDIN & PD0 & PD16 & _) & (HDd & HWd & HHd & HWPLd & HRSd) & DATd & _).
    destruct DATd as [DZ|((DIN & DA0 & DA16 & DAN) & DNE)]; [contradiction|].
    unfold pix_cells in PXD. unfold rsize in *.
    set (dat := p_data vd) in *. set (rs := 4 * (p_wpl vd * p_h vd)) in *.
    assert (RSEQ : rs = 4 * (p_wpl v * p_h v)) by (unfold rs; rewrite VWPL, VH; reflexivity).
    unfold pm_copy_live, rsize in LVH. fold dat in LVH. fold rs in LVH.
    lazymatch goal with A : ART RT ?S1 ?mm |- cps _ (ASTA RT ?S1 _ _) _ =>
      assert (SUB01 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S1)) by (intros e He; rewrite LVH; apply in_or_app; right; right; right; exact He);
      assert (NCD : forall a, PF a -> a < dat \/ dat + rs <= a)
        by (intros a Ha; apply (fresh_chunk_apart RT AF S1 mm _ dat rs ((pixd, 64) :: rt_live RT Σ) (rt_frames RT S1) usp a A LVH eq_refl);
            [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul| apply (aclient_mono _ _ usp _ _ usp _ Ha); [intros e He; right; exact He| solve [frames_sub_tac]| lia]]);
      assert (NEQDP : dat + rs <= pixd \/ pixd + 64 <= dat) by (apply (live_apart2 RT AF S1 mm dat rs pixd 64 A DIN PDIN DNE))
    end.
    assert (PFDS : forall a, dsrc <= a < dsrc + rs -> PF a) by (intros a Ha; right; right; left; exists dsrc, (4 * (p_wpl v * p_h v)); split; [exact DSIN| lia]).
    assert (APSD : dat + rs <= dsrc \/ dsrc + rs <= dat)
      by (pose proof (NCD dsrc (PFDS dsrc ltac:(lia))); pose proof (NCD (dsrc + rs - 1) (PFDS (dsrc + rs - 1) ltac:(lia))); lia).
    assert (PFPS : forall a, pixs <= a < pixs + 64 -> PF a) by (intros a Ha; right; right; left; exists pixs, 64; split; [exact PIN| exact Ha]).
    assert (APSP : dat + rs <= pixs \/ pixs + 64 <= dat)
      by (destruct (Z_lt_le_dec dat (pixs + 64)) as [LLx|GGx]; [| right; lia]; destruct (Z_le_gt_dec pixs dat) as [LLy|GGy];
          [pose proof (NCD dat (PFPS dat ltac:(lia))); lia| left; pose proof (NCD pixs (PFPS pixs ltac:(lia))); lia]).
    lazymatch type of LVH with rt_live RT ?S1 = _ =>
      assert (INPS1 : In (pixs, 64) (rt_live RT S1)) by (apply SUB01; exact PIN);
      assert (INDS1 : In (dsrc, rs) (rt_live RT S1)) by (apply SUB01; rewrite RSEQ; exact DSIN)
    end.
    park LVH.
    chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
    lazymatch goal with A : ART RT ?S1 ?mm |- cps _ (ASTA RT ?S1 _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      assert (PCS : forall a, aclient (rt_live RT S1) (rt_frames RT Σ) usp a -> usp <= a \/ a < lo)
        by (intros a Ha; pose proof (aclient_split RT AF S1 mm usp a A) as SPL;
            repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H in SPL end;
            repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in SPL end;
            destruct (SPL Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]);
      pose proof (agree_refl (fun a => aclient (rt_live RT S1) (rt_frames RT Σ) usp a /\ outside [(dat, dat + rs)] a) mm) as AGC
    end.
    hide AGC.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 64, usp)] [0x8f4a0; 0x5daa0; 0x5d604; 0x8db6c].
    assert (WPLBd : 0 < p_wpl vd <= 20001) by (rewrite VWPL; lia).
    rewrite ?(zx32_small (p_wpl vd)), ?(zx32_small (p_h vd)) by lia.
    rewrite ?(unsigned_lit (p_wpl vd)), ?(unsigned_lit (p_h vd)) by lia.
    rewrite (Z.mod_small (p_wpl vd * 4)) by lia.
    replace (p_wpl vd * 4 * p_h vd) with rs by (unfold rs; lia).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm))) _ =>
      pose proof (af_acc_live RT AF S mm dat rs A DIN) as (WRD & ACCD) end.
    eapply cps_seq.
    { pose proof (rc_asan_memset RT RC) as MS0; unfold memset_icontract in MS0; eapply MS0 with (lo := lo) (d := dat) (n := rs) (c := Z_to_bv 8 0); rt_side idtac.
      all: lazymatch goal with
           | |- (0 <= _ <= _) => change (2^47) with 140737488355328; lia
           | |- checked_dst _ _ _ _ _ _ =>
               unfold checked_dst; rewrite ?unsigned_lit by lia; split; [intros _; split; [exact ACCD| left; exists dat, rs; split; [exact DIN| lia]]|];
               split; [intros i Hi; right; right; left; exists dat, rs; split; [exact DIN| lia]| exact WRD]
           | |- ?g => idtac "LEFTOVER:" g
           end. }
    after_call RT AF.
    unfold hid in AGC.
    agf_call AGC AG ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                           destruct Hx as [_ Hx2]; cbn [outside] in Hx2; exact (proj1 Hx2)]).
    hide AGC.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                     [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (SUB01 e He)| solve [frames_sub_tac]| lia]|
                                   pose proof (NCD _ Hx); lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 64, usp)] [0x8f4a0; 0x5daa0; 0x5d604; 0x8db6c].
    try shbr_inv8m.
    Time awalk [0x8f4a0; 0x5daa0; 0x5d604; 0x8db6c].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm))) _ =>
      assert (INS2 : In (dsrc, rs) (rt_live RT S)) by (solve [in_live_tac]); assert (IND2 : In (dat, rs) (rt_live RT S)) by (solve [in_live_tac]);
      pose proof (af_acc_live RT AF S mm dsrc rs A INS2) as (WRS & ACCS); pose proof (af_acc_live RT AF S mm dat rs A IND2) as (WRD2 & ACCD2) end.
    apply wr_at_rw_CB in WRS; [| lia]. destruct WRS as (sbs & SBC).
    pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
    assert (SBL' : Z.of_nat (length sbs) = rs) by (rewrite SBL; lia).
    eapply cps_seq.
    { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0; eapply MC0 with (lo := lo) (d := dat) (s := dsrc) (bs := sbs); rewrite ?SBL'.
      all: lazymatch goal with
           | |- fdfs_only _ => exact FDO
           | |- mat_stable _ => exact MST
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; rewrite RSEQ; lia | f_equal; rewrite RSEQ; rewrite swrap32_small by lia; lia]
           | |- bytes_at _ _ _ _ => exact SB
           | |- ART _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- checked_src _ _ _ _ _ _ _ =>
               unfold checked_src; rewrite ?unsigned_lit by lia; split; [intros _; split; [exact ACCS| left; exists dsrc, rs; split; [exact INS2| lia]]| left; lia]
           | |- checked_dst _ _ _ _ _ _ =>
               unfold checked_dst; rewrite ?unsigned_lit by lia; split; [intros _; split; [exact ACCD2| left; exists dat, rs; split; [exact IND2| lia]]|];
               split; [intros i Hi; right; right; left; exists dat, rs; split; [exact IND2| lia]| exact WRD2]
           | |- call_ok _ _ _ _ _ =>
               unfold call_ok; rewrite ?unsigned_lit by lia; split; [assumption|];
               repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN, RT_STACK, USTACK_TOP;
               split; [lia| split; [lia| split; [lia| clear - SPA; Z.div_mod_to_equations; lia]]]
           | |- _ \/ _ => unfold parked in APSD; exact APSD
           | |- (_ <= _ <= _) => change (2^47) with 140737488355328; lia
           | |- (_ < _) => change (2^40) with 1099511627776; lia
           | |- ?g => idtac "LEFTOVER:" g
           end. }
    rewrite ?SBL'. clear SB.
    after_call RT AF.
    unfold hid in AGC.
    agf_call AGC AG ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                           destruct Hx as [_ Hx2]; cbn [outside] in Hx2; exact (proj1 Hx2)]).
    hide AGC.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                     [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (SUB01 e He)| solve [frames_sub_tac]| lia]|
                                   pose proof (NCD _ Hx); lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 64, usp)] (@nil Z).
    cps_stop.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?SF _ _ _ => exists SF, pixd, vd, cvd end.
    split.
    2:{ unpark LVH. split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; unfold pm_copy_live, rsize; reflexivity|]. clear LVH. alg_tac. }
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
    split; [intros a Ha _; apply AGF; exact Ha|]. split; [exact PNZ|].
    split; [| unfold pm_hdr_copy; split; [exact VW|]; split; [exact VH|]; split; [exact VD|]; split; [exact VWPL|]; split; [exact VDATA|]; split; [exact VCM0| exact VCM]].
    lazymatch type of POBJ1 with pix_obj ?lv1 ?ma _ _ _ => lazymatch type of PXD with rw_cells _ ?mb _ _ =>
      apply (pix_obj_retarget lv1 lv1 ma mb pixd vd vd cvd POBJ1 PXD); try reflexivity; [auto|] end end.
    intros CNZ. destruct POBJ1 as (_ & _ & _ & _ & [CZ|(CO & N1 & N2 & N3 & N4)]); [contradiction|]. destruct CO as (_ & (CIN & _) & _).
    lazymatch goal with A : ART RT ?S1 ?ma |- keeps_live _ ?ma _ => pose proof (live_apart2 RT AF S1 ma (p_cmap vd) 24 dat rs A CIN DIN N3) as APC end.
    unfold hid in AGC. eapply keeps_live_of_agree; [exact AGC| intros e [<-|[]]; exact CIN| intros b k xx [E|[]] Hx; injection E as <- <-; cbn [outside]; split; [lia| exact I]].
Qed.
End PIXCOPY.

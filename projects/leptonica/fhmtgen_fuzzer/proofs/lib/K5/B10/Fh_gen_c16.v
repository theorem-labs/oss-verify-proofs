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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface I_strcmp_spec I_strcmp_lift LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_deserkit Lept_gmax_defs D_iface D_defs D_libiface Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit Gm_leaf Fh_iface Fh_statics Fh_gen_defs Fh_drvkit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac gfix := repeat match goal with |- context [bv_wrap 32 ?z] => rewrite (bv_wrap_small 32 z) by (change (bv_modulus 32) with (2^32); lia) end;
  repeat match goal with |- context [?a / 134217728] => rewrite (Z.div_small a 134217728) by lia end;
  rewrite ?unsigned_lit by lia;
  repeat match goal with |- context [bv_swrap 32 ?z] => rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); lia) end;
  repeat match goal with |- context [?E mod 18446744073709551616] => rewrite (Z.mod_small E 18446744073709551616) by lia end;
  repeat match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    match c with context [?a <? ?b] =>
      first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end end;
  cbn [Z.b2z].
Ltac gstep := first [ cwalk1 | progress gfix; try br | progress guard_fix; try br ].
Ltac gwalk stops := repeat (tryif at_stop stops then fail else gstep).

Section GEN.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FH : fh_gaps RT.
Hypothesis TPL : pixCreateTemplate_cps RT.
Hypothesis LOW : fhmtgen_low_1_cps RT.

Lemma fh_gen_c16 : fh_gen_case RT 16.
Proof using AF RC GP FH TPL LOW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixs name vs cvs i FDO MST -> -> -> -> POS D1 SDNZ WS HS (I10 & NIN & NB) LSEL ENV RES AL.
  unfold lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW0 & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POS as (PXS & (PSIN & PS0 & PS16 & _) & HOKS & _ & PSCM).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixFHMTGen_1, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, FHMTGEN_COST, TEMPLATE_COST, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pixs 64.
  chunk_facts RT AF GP name 8.
  unfold pix_cells in PXS. rewrite D1 in PXS.
  hide POS. hide PSCM. hide HOKS. hide LSEL. hide NB.
  carve_frame 208%nat ST.
  walk_to AF MST [(usp - 208, usp)] [e_stack_malloc 0%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; clear - P LOR; split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S0 end.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 0%nat 64 pixs 64.
  fframe_chunk RT AF fr 0%nat 64 name 8.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0xb0d1c].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                       destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; e_returnErrorPtr].
  assert (FRS0 : rt_frames RT S0 = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (LV0 : rt_live RT S0 = rt_live RT Σ) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (SP00 : rt_sp0 RT S0 = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (CR0 : rt_credit RT S0 = rt_credit RT Σ - 1) by (repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia).
  (* [comment removed for export] *)
  lazymatch goal with
  | FRx : rw_cells asegs ?mc (usp + -208) ?csFR, FRMx : rw_cells asegs ?mc fr ?csFRM, FSHx : rw_cells asegs ?mc (fr / 8 + 2147450880) ?csFSH,
    PXx : rw_cells asegs ?mc pixs ?csPX |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (JOIN : forall (mJ : mem) (r1 r5 r6 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 r21 r28 r29 r30 r31 : word) F' fc',
       r8 = Z_to_bv 64 usp -> r21 = Z_to_bv 64 (Z.of_nat i) ->
       ART RT S0 mJ -> mem_inv asegs mJ -> stk asegs mJ lo (usp + -208) ->
       rw_cells asegs mJ (usp + -208) csFR -> rw_cells asegs mJ fr csFRM -> rw_cells asegs mJ (fr / 8 + 2147450880) csFSH -> rw_cells asegs mJ pixs csPX ->
       LIBH mJ -> io_ssp mJ -> agree_on PF m mJ -> wmono asegs m mJ ->
       cps asegs (ASTA RT S0 PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP_A) r5 r6 r7 r8 (Z_to_bv 64 (usp + -208))
            r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) z64 (Z_to_bv 64 pixs) r21 (Z_to_bv 64 0xf0f40) s7
            (Z_to_bv 64 2147450880) s9 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + 2147450880)) r28 r29 r30 r31 F' fc' 0xb0ed8 mJ))) QF)
  end.
  { intros mJ r1 r5 r6 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 r21 r28 r29 r30 r31 F' fc' -> -> ARTJ MIJ STJ FRJ FRMJ FSHJ PXJ LHJ SSPJ AGJ WMJ.
    clear AGF. rename AGJ into AGF.
    repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRJ => fail | FRMJ => fail | FSHJ => fail | PXJ => fail | _ => clear H end end.
    repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTJ => fail | ART0 => fail | _ => clear H end end.
    repeat match goal with H : LIBH _ |- _ => lazymatch H with LHJ => fail | _ => clear H end end.
    repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPJ => fail | _ => clear H end end.
    repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STJ => fail | _ => clear H end end.
    repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIJ => fail | _ => clear H end end.
    repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WMJ => fail | _ => clear H end end.
    repeat match goal with H : munch _ _ _ |- _ => clear H end.
    clear_acc.
    rename FRJ into FR. rename FRMJ into FRM. rename FSHJ into FSH. rename PXJ into PXS.
    unfold entry_st.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_pixCreateTemplate; e_returnErrorPtr].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                  destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a)
      by (intros q k a Hq Ha; right; right; left; exists q, k; split; [exact Hq| lia]).
    unfold hid in POS.
    lazymatch goal with PX : rw_cells asegs ?mc pixs _, A : ART RT ?S ?mc |- cps _ (ASTA RT ?S _ _) _ =>
      assert (POS1 : pix_obj (rt_live RT S) mc pixs vs cvs)
        by (apply (pix_obj_mono (rt_live RT Σ) (rt_live RT S) mc pixs vs cvs); [solve [live_sub_tac]|];
            apply (pix_obj_agree (rt_live RT Σ) PF m mc pixs vs cvs POS AGF PML); unfold pix_cells; rewrite D1; exact PX) end.
    hide POS.
    pose proof TPL as TP. unfold pixCreateTemplate_cps in TP.
    eapply cps_seq.
    { eapply TP with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POS1
           | |- p_data _ <> 0 => exact SDNZ
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => unfold TEMPLATE_COST, RASTER_COST; lres_tac
           | |- ?g => idtac "LEFT:" g
           end. }
    clear POS1.
    after_call RT AF.
    lazymatch goal with H : live_destroy ?pd ?vd0 ?cvd0 (rt_live RT ?S1) = _ |- _ =>
      rename pd into pixd; rename vd0 into vd; rename cvd0 into cvd; rename S1 into Σ1; rename H into LDES end.
    lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
    lazymatch goal with H : pix_obj (rt_live RT Σ1) _ pixd vd cvd |- _ => rename H into POBJD end.
    lazymatch goal with H : forall p n, In (p, n) (rt_live RT Σ1) -> 0 < n |- _ => rename H into LVP1 end.
    lazymatch goal with H : Z.of_nat (length (rt_live RT Σ1)) <= _ |- _ => rename H into LLEN1 end.
    lazymatch goal with H : p_w vd = p_w vs |- _ => rename H into VDW end.
    lazymatch goal with H : p_h vd = p_h vs |- _ => rename H into VDH end.
    lazymatch goal with H : p_d vd = p_d vs |- _ => rename H into VDD end.
    lazymatch goal with H : p_data vd <> 0 |- _ => rename H into VDDATA end.
    assert (SUB1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1))
      by (intros e He; apply (live_destroy_In (rt_live RT Σ1) pixd vd cvd); rewrite LDES, LV0; exact He).
    pose proof (SUB1 _ PSIN) as INS1.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    pose proof POBJD as (PDC & (PDIN & PD0 & PD16 & _) & (HD1d & HW1d & HH1d & HWPLd & HRSd) & PDATAD & _).
    destruct PDATAD as [DZd|((DDIN & DD0 & DD16 & DDSZ) & DDNE)]; [contradiction|].
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    assert (FRS1 : rt_frames RT Σ1 = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    chunk_facts RT AF GP pixd 64.
    chunk_facts RT AF GP (p_data vd) (rsize vd).
    fframe_chunk RT AF fr 0%nat 64 pixd 64.
    fframe_chunk RT AF fr 0%nat 64 pixs 64.
    fframe_chunk RT AF fr 0%nat 64 (p_data vd) (rsize vd).
    hide POBJD. hide LDES. hide LVP1. hide LLEN1.
    park_disj.
    unfold pix_cells in PDC.
    assert (NEPS : pixd <> pixs).
    { unfold hid in LDES. pose proof PSIN as PSIN'. rewrite <- LV0, <- LDES in PSIN'.
      destruct (live_destroy_In _ _ _ _ _ PSIN') as (_ & NE & _). cbn [fst] in NE. hide LDES. congruence. }
    unfold hid in HOKS. pose proof HOKS as (_ & HSW & HSH & HSWPL & HSRS). hide HOKS. rewrite D1 in HSWPL.
    assert (WPLE : p_wpl vd = p_wpl vs) by (rewrite HWPLd, HSWPL, VDW, VDD, D1; reflexivity).
    assert (WPLB : 0 < p_wpl vs <= 626) by (rewrite HSWPL; clear - HSW; Z.div_mod_to_equations; lia).
    assert (SRCIN : In (p_data vs, rsize vs) (rt_live RT Σ1)).
    { unfold hid in POS. destruct POS as (_ & _ & _ & PD & _). destruct PD as [Z0|((CIN & _) & _)]; [contradiction|]. exact (SUB1 _ CIN). }
    lazymatch goal with A1 : ART RT Σ1 ?m1 |- _ =>
      pose proof (af_live_range RT AF Σ1 m1 (p_data vs) (rsize vs) A1 SRCIN) as (SR0 & SR1 & _);
      pose proof (af_live_range RT AF Σ1 m1 (p_data vd) (rsize vd) A1 DDIN) as (DR0 & DR1 & _) end.
    assert (SP0B : rt_sp0 RT Σ1 <= 2^47) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    assert (RSB : 0 < rsize vs /\ 0 < rsize vd /\ p_wpl vs * 32 * 4 + 4 < rsize vs /\ p_wpl vs * 32 * 4 + 4 < rsize vd).
    { unfold rsize. rewrite WPLE, VDH. clear - WPLB HS HSH. nia. }
    unfold STACK_WIN in *.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_fhmtgen_low_1; e_returnErrorPtr; e_pixCopy].
    gwalk [e_fhmtgen_low_1; e_returnErrorPtr; e_pixCopy].
    (* [comment removed for export] *)
    rewrite WPLE.
    sx32_fix. rewrite ?unsigned_lit by lia.
    repeat match goal with |- context [bv_swrap 32 ?z] =>
      rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - HSW HSH WPLB WS HS; lia) end.
    repeat match goal with |- context [?E mod 18446744073709551616] =>
      rewrite (Z.mod_small E 18446744073709551616) by (clear - HSW HSH WPLB; lia) end.
    assert (RSE : 4 * (p_wpl vs * (p_h vs - 64 + 64)) = rsize vd) by (unfold rsize; rewrite WPLE, VDH; f_equal; f_equal; lia).
    assert (SRCH : chunk (rt_live RT Σ1) (p_data vs) (rsize vs)).
    { unfold hid in POS. destruct POS as (_ & _ & _ & PD & _). destruct PD as [Z0|(CH & _)]; [contradiction|].
      exact (chunk_mono (rt_live RT Σ) _ _ _ SUB1 CH). }
    assert (NERD : p_data vd <> p_data vs).
    { unfold hid in POS, LDES. destruct POS as (_ & _ & _ & PD & _). destruct PD as [Z0|((CIN & _) & _)]; [contradiction|].
      rewrite <- LV0, <- LDES in CIN. destruct (live_destroy_In _ _ _ _ _ CIN) as (_ & _ & NE & _). specialize (NE VDDATA). cbn [fst] in NE. congruence. }
    assert (SPL1 : rt_sp0 RT Σ1 - 8388608 <= usp - 368) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    lazymatch goal with A1 : ART RT Σ1 ?m1 |- _ =>
      assert (QPD : pixd + 64 <= p_data vd \/ p_data vd + rsize vd <= pixd)
        by (pose proof (live_apart RT AF Σ1 m1 pixd 64 (p_data vd) (rsize vd) A1 PDIN DDIN ltac:(congruence)) as X; clear - X; lia) end.
    park_disj.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                  destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POBJD.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame0 RT AF S mm fr usp (usp - 368) bb kk xx A ltac:(rewrite FRS1; left; reflexivity) SPL1 Hb Hx)) end end.
    pose proof (pix_obj_keep _ _ _ pixd vd _ KL POBJD) as POBJK. clear POBJD KL.
    pose proof LOW as LW. unfold fhmtgen_low_1_cps in LW.
    eapply cps_seq.
    { eapply LW with (lo := lo) (rd := p_data vd) (rs := p_data vs) (w := p_w vs - 64) (h := p_h vs - 64) (wpl := p_wpl vs) (index := Z.of_nat i); rt_side idtac.
      all: lazymatch goal with
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; lia
           | |- chunk _ _ _ =>
               first [ rewrite RSE; exact (conj DDIN (conj DD0 (conj DD16 DDSZ)))
                     | replace (4 * (p_wpl vs * (p_h vs - 64 + 64))) with (rsize vs) by (unfold rsize; f_equal; f_equal; lia); exact SRCH ]
           | |- _ <> _ => exact NERD
           | |- _ = (_ + 64 + 31) / 32 => rewrite HSWPL; f_equal; lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- ?g => first [ lia | idtac "LEFT:" g ]
           end. }
    after_call RT AF.
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into Σ2 end.
    lazymatch goal with A1 : ART RT Σ1 ?m1 |- _ =>
      assert (NCD : forall a, PF a -> a < p_data vd \/ p_data vd + rsize vd <= a)
        by (intros a Ha; apply (new_chunk_apart_sub RT AF Σ1 m1 (p_data vd) (rsize vd) (rt_live RT Σ) (rt_frames RT Σ) usp a A1 DDIN);
            [ intros e He; split; [exact (SUB1 e He)|]; unfold hid in LDES; rewrite <- LV0, <- LDES in He;
              destruct (live_destroy_In _ _ _ _ _ He) as (_ & _ & NE & _); exact (NE VDDATA)
            | intros e He; rewrite FRS1; right; exact He
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | exact Ha ]) end.
    lazymatch goal with H : rt_live RT Σ2 = rt_live RT Σ1 |- _ => rename H into LVK end.
    (* [comment removed for export] *)
    lazymatch goal with AG : agree_on (fun a => aclient ?lv ?frs ?spc a /\ outside ?W a) ?ma ?mb, PD : rw_cells asegs ?mb pixd _, A1 : ART RT Σ1 ?m1 |- _ =>
      assert (POBJ2 : pix_obj (rt_live RT Σ2) mb pixd vd cvd)
        by (rewrite LVK; apply (pix_obj_agree_cm (rt_live RT Σ1) _ ma mb pixd vd cvd POBJK AG);
            [ intros NZ a Ha; destruct POBJK as (_ & _ & _ & _ & PCM); destruct PCM as [Z0|((_ & (CIN & _) & _) & _ & _ & CND & _)]; [contradiction|];
              pose proof (live_apart RT AF Σ1 m1 (p_cmap vd) 24 (p_data vd) (rsize vd) A1 CIN DDIN CND) as X;
              split; [right; right; left; exists (p_cmap vd), 24; split; [rewrite LVK; exact CIN| exact Ha]| cbn [outside]; rewrite RSE; unfold rsize in X; clear - X Ha; split; [lia| exact I]]
            | unfold pix_cells; exact PD ]) end.
    clear POBJK.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LVK; exact (SUB1 e He)| solve [frames_sub_tac]| lia]
                                   | cbn [outside]; let N0 := fresh "N0" in pose proof (NCD _ Hx) as N0; unfold rsize in N0; rewrite RSE; clear - N0; split; [lia| exact I]]).
    hide POBJ2.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0xb113c].
    (* [comment removed for export] *)
    assert (FRSK : rt_frames RT Σ2 = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPLK : rt_sp0 RT Σ2 - 8388608 <= usp - 368) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    lazymatch goal with MUx : munch ?W ?mb ?mc, A : ART RT Σ2 ?mb |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (KEEP1 : keeps_live (rt_live RT Σ2) mb mc)
        by (apply (keeps_live_of_munch _ W mb mc MUx); intros bb kk xx Hb Hx;
            exact (live_outside_frame0 RT AF Σ2 mb fr usp (usp - 368) bb kk xx A ltac:(rewrite FRSK; left; reflexivity) SPLK Hb Hx)) end.
    frame_release_k RT AF GP MST Σ fr 0%nat 64 PF AGF PFS usp lo 0xb1144
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                      destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact Hx)
      ltac:(fun fl FLN => idtac).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 208, usp)] (@nil Z).
    fold usp. cwalk (@nil Z).
  lazymatch goal with ST' : stk asegs _ lo (usp + -208), FR' : rw_cells asegs _ (usp + -208) _ |- _ => release_frame FR' ST' usp end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (KEEP3 : keeps_live (rt_live RT Σ2) mm mc)
        by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
            intros bb kk Hb a Ha; apply MUx; cbn [outside]; split; [| exact I];
            lazymatch goal with A : ART RT Σ2 ?mb |- _ => pose proof (af_live_range RT AF Σ2 mb bb kk A Hb) as (_ & R1 & _) end;
            repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in R1 end; unfold STACK_WIN in R1; lia);
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    unfold hid in POBJ2.
    lazymatch type of POBJ2 with pix_obj _ ?mb _ _ _ => lazymatch goal with K3 : keeps_live _ ?mr ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (KEEPF : keeps_live (rt_live RT Σ2) mb mc)
        by (eapply keeps_live_trans; [exact KEEP1|]; eapply keeps_live_trans; [exact KEEPR| exact K3]) end end.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', pixd, vd, cvd end.
    unfold hid in LDES, LVP1, LLEN1.
    split.
    { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [intros a Ha _; apply AGF; exact Ha|].
      rewrite LV2. split; [exact (pix_obj_keep _ _ _ pixd vd _ KEEPF POBJ2)|].
      split; [exact VDW|]. split; [exact VDH|]. split; [rewrite VDD; exact D1| exact VDDATA]. }
    rewrite LV2, FRS2, SP2, CR2, LVK.
    split; [rewrite LDES; exact LV0|]. split; [exact LVP1|]. split; [rewrite LV0 in LLEN1; exact LLEN1|].
    split; [reflexivity|]. split; [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
    unfold FHMTGEN_COST, TEMPLATE_COST, RASTER_COST in *.
    repeat match goal with H : context [rt_credit] |- _ => revert H end; clear; intros; lia. }
  (* [comment removed for export] *)
  destruct (hm_cmp i 0 I10 ltac:(lia)) as (_ & _ & LN8 & _).
  assert (IB : (i < 10)%nat) by exact I10.
(* [comment removed for export] *)
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 0 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 0) (b1 := hm_name i) (b2 := hm_name 0); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 0 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 0)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 0 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 0) as [EI|NI0].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 0))) z64 = false)
    by (pose proof (RNE NI0) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 0) = -1 \/ strcmp_res (hm_name i) (hm_name 0) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  cwalk [e_strcmp].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 1 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 1) (b1 := hm_name i) (b2 := hm_name 1); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 1 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 1)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 1 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 1) as [EI|NI1].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 1))) z64 = false)
    by (pose proof (RNE NI1) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 1) = -1 \/ strcmp_res (hm_name i) (hm_name 1) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  cwalk [e_strcmp].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 2 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 2) (b1 := hm_name i) (b2 := hm_name 2); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 2 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 2)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 2 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 2) as [EI|NI2].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 2))) z64 = false)
    by (pose proof (RNE NI2) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 2) = -1 \/ strcmp_res (hm_name i) (hm_name 2) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  cwalk [e_strcmp].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 3 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 3) (b1 := hm_name i) (b2 := hm_name 3); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 3 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 3)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 3 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 3) as [EI|NI3].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 3))) z64 = false)
    by (pose proof (RNE NI3) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 3) = -1 \/ strcmp_res (hm_name i) (hm_name 3) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  cwalk [e_strcmp].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 4 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 4) (b1 := hm_name i) (b2 := hm_name 4); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 4 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 4)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 4 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 4) as [EI|NI4].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 4))) z64 = false)
    by (pose proof (RNE NI4) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 4) = -1 \/ strcmp_res (hm_name i) (hm_name 4) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  cwalk [e_strcmp].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 5 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 5) (b1 := hm_name i) (b2 := hm_name 5); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 5 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 5)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 5 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 5) as [EI|NI5].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 5))) z64 = false)
    by (pose proof (RNE NI5) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 5) = -1 \/ strcmp_res (hm_name i) (hm_name 5) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  cwalk [e_strcmp].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 6 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 6) (b1 := hm_name i) (b2 := hm_name 6); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 6 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 6)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 6 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 6) as [EI|NI6].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 6))) z64 = false)
    by (pose proof (RNE NI6) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 6) = -1 \/ strcmp_res (hm_name i) (hm_name 6) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  cwalk [e_strcmp].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 7 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 7) (b1 := hm_name i) (b2 := hm_name 7); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 7 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 7)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 7 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 7) as [EI|NI7].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 7))) z64 = false)
    by (pose proof (RNE NI7) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 7) = -1 \/ strcmp_res (hm_name i) (hm_name 7) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  cwalk [e_strcmp].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 8 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 8) (b1 := hm_name i) (b2 := hm_name 8); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 8 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 8)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 8 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 8) as [EI|NI8].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 8))) z64 = false)
    by (pose proof (RNE NI8) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 8) = -1 \/ strcmp_res (hm_name i) (hm_name 8) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  cwalk [e_strcmp].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in NB, LSEL.
  lazymatch goal with A : ART RT S0 ?mc |- cps _ (ASTA RT S0 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; rewrite LN8 in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia);
    pose proof (acc_live RT AF S0 mc name 8 A ltac:(rewrite LV0; exact NIN)) as ACCN;
    pose proof (fh_acc_selnames RT AF S0 mc A) as ACCSEL
  end.
  hide NB. hide LSEL.
  destruct (hm_cmp i 9 IB ltac:(lia)) as (SZB & SOK & _).
  eapply cps_seq.
  { pose proof (fh_strcmp RT FH) as SC; unfold strcmp_icontract in SC;
    eapply SC with (lo := lo) (p1 := name) (p2 := SEL_NAMES_AT + 80 * Z.of_nat 9) (b1 := hm_name i) (b2 := hm_name 9); rt_side idtac.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- Z.of_nat (length _) < _ => first [ rewrite LN8; vm_compute; reflexivity | vm_compute; reflexivity ]
         | |- _ => idtac
         end.
    all: first [ reflexivity | exact SOK | exact NBc | exact (lib_sel_row _ 9 LSELc ltac:(lia))
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ name 8); [exact ACCN| lia| clear - SZB; lia]
                                                              | left; exists name, 8; split; [rewrite LV0; exact NIN| clear - SZB; lia]]
                                            | left; lia])
               | (unfold checked_src; split; [intros _; split; [eapply (acc_sub asegs _ SEL_NAMES_AT 800); [exact ACCSEL| lia| unfold SEL_NAMES_AT, LIB_SEL_AT; clear - SZB; lia]
                                                              | apply (fh_class_selnames RT S0 (Z.of_nat 9)); [lia| clear - SZB; lia]]
                                            | left; unfold SEL_NAMES_AT, LIB_SEL_AT; lia]) ]. }
  clear NBc LSELc ACCN ACCSEL SZB SOK.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 368, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [e_strcmp; 0xb0ed8].
  (* [comment removed for export] *)
  destruct (hm_cmp i 9 IB ltac:(lia)) as (_ & _ & _ & REQ & RNE & RR).
  destruct (Nat.eq_dec i 9) as [EI|NI9].
  { (* [comment removed for export] *)
    rewrite (REQ EI). change (bv_eqb (Z_to_bv 64 0) z64) with true. cbv iota.
    cwalk [0xb0ed8].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply JOIN; try eassumption.
    all: first [ reflexivity | (symmetry; exact ESP) | (rewrite EI; reflexivity)
               | (repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans) ]. }
  assert (BF : bv_eqb (Z_to_bv 64 (strcmp_res (hm_name i) (hm_name 9))) z64 = false)
    by (pose proof (RNE NI9) as RN0; clear - RN0 RR;
        assert (RCS : strcmp_res (hm_name i) (hm_name 9) = -1 \/ strcmp_res (hm_name i) (hm_name 9) = 1) by lia;
        destruct RCS as [RCS|RCS]; rewrite RCS; vm_compute; reflexivity).
  rewrite BF. cbv iota. clear BF REQ RNE RR.
  exfalso. clear - IB NI0 NI1 NI2 NI3 NI4 NI5 NI6 NI7 NI8 NI9. lia.
(* [comment removed for export] *)
Qed.
End GEN.

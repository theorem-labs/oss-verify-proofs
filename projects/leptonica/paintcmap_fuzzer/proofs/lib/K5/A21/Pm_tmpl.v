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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_iface Pm_iface2 Pm_iface4 Pm_ckit Pm_okit D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma tr_tmpl_noinit : In [PM_NOINIT_MALLOC; RA_TMPL_NOINIT] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.
Lemma tr_tmpl_copycmap : In [PMCOPY_CALLOC1; RA_TMPL_COPYCMAP] CLIENT_TRACES.  Proof. vm_compute. tauto. Qed.

Section TMPL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis NOINIT : pixCreateNoInit_nn_cps RT e_pixCreateNoInit PM_NOINIT_MALLOC.
Hypothesis CCM : pixCopyColormap_cps RT.
Hypothesis SREP : stringReplace_null_cps RT.
Hypothesis PAD : pixSetPadBits_cps RT.
Hypothesis RERRI : returnError_cps RT e_returnErrorInt.

Theorem pixCreateTemplateNoInit_ok : pixCreateTemplateNoInit_nn_cps RT.
Proof using AF GP NOINIT CCM SREP PAD RERRI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pixs v cv
    FDO MST -> -> POBJ ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixCreateTemplateNoInit, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof RERRI as REI. unfold returnError_cps in REI.
  pose proof NOINIT as NI. unfold pixCreateNoInit_nn_cps in NI. pose proof CCM as CC. unfold pixCopyColormap_cps in CC.
  pose proof SREP as SR. unfold stringReplace_null_cps in SR. pose proof PAD as PD. unfold pixSetPadBits_cps in PD.
  unfold RASTER_COST in NI, CC, PD.
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & _ & _).
  pose proof POBJ as (_ & _ & HOKV & _).
  unfold pix_cells in PXC.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pixs 64.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 32, usp)] [0x8e648; 0x8f8fc; 0x8dd94; 0x91080; 0x8dad0; 0x8d86c].
  assert (DB : 1 <= p_d v <= 32) by (clear - HD1; cbn [In] in HD1; lia).
  rewrite (sx32_small (p_w v)), (sx32_small (p_h v)), (sx32_small (p_d v)) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]) ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply NI with (lo := lo) (w := p_w v) (h := p_h v) (d := p_d v) (ras := @nil Z); rt_side idtac.
    all: lazymatch goal with
         | |- s32 _ _ => split; [lia| reflexivity]
         | |- hdr_args_ok _ _ _ => exact (hdr_args_of_pix v HOKV)
         | |- uctx _ _ _ _ => unfold uctx; cbn [chain_ok]; unfold link_invalid; rewrite ?unsigned_lit by lia; left; lia
         | |- In _ CLIENT_TRACES => exact tr_tmpl_noinit
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold RASTER_COST; lres_tac
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with H : pix_obj _ _ ?p _ (mkCmapv 0 0 0 0) |- _ => rename H into POBJD; set (pixd := p) in * end.
  lazymatch goal with H : pixd <> 0 |- _ => rename H into PNZ end.
  lazymatch goal with H : rt_live RT _ = _ :: (pixd, 64) :: _ |- _ => rename H into LVH end.
  lazymatch goal with H : p_w _ = p_w v |- _ => rename H into VW end. lazymatch goal with H : p_h _ = p_h v |- _ => rename H into VH end.
  lazymatch goal with H : p_d _ = p_d v |- _ => rename H into VD end. lazymatch goal with H : p_data _ <> 0 |- _ => rename H into VDATA end.
  lazymatch goal with H : p_cmap _ = 0 |- _ => rename H into VCMAP end.
  - (* [comment removed for export] *)
    lazymatch type of POBJD with pix_obj _ _ _ ?vv _ => set (vd := vv) in * end.
    pose proof POBJD as (PXD & (PDIN & PD0 & PD16 & _) & (HDd & HWd & HHd & HWPLd & HRSd) & DATd & _).
    destruct DATd as [DZ|((DIN & DA0 & DA16 & DAN) & DNE)]; [contradiction|].
    unfold pix_cells in PXD.
    unfold rsize in *. set (dat := p_data vd) in *. set (rs := 4 * (p_wpl vd * p_h vd)) in *.
    chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
    assert (PDH : pixd + 64 <= 2147446784 \/ 17594333495296 <= pixd) by (lazymatch goal with D : pixd + 64 <= 2147446784 \/ _ |- _ => exact D end).
    assert (PDS : pixd + 64 <= 65536 \/ 6471680 <= pixd) by (lazymatch goal with D : pixd + 64 <= 65536 \/ _ |- _ => exact D end).
    lazymatch goal with A : ART RT ?S1 ?mm |- cps _ (ASTA RT ?S1 _ _) _ =>
      assert (NCP : forall a, PF a -> a < pixd \/ pixd + 64 <= a)
        by (intros a Ha; apply (fresh_chunk_apart RT AF S1 mm [(dat, rs)] pixd 64 (rt_live RT Σ) (rt_frames RT S1) usp a A LVH eq_refl);
            [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul| apply (aclient_mono _ _ usp _ _ usp _ Ha); [auto| solve [frames_sub_tac]| lia]]);
      assert (NCD : forall a, PF a -> a < dat \/ dat + rs <= a)
        by (intros a Ha; apply (fresh_chunk_apart RT AF S1 mm [] dat rs ((pixd, 64) :: rt_live RT Σ) (rt_frames RT S1) usp a A LVH eq_refl);
            [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul| apply (aclient_mono _ _ usp _ _ usp _ Ha); [intros e He; right; exact He| solve [frames_sub_tac]| lia]]);
      assert (NEQDP : dat + rs <= pixd \/ pixd + 64 <= dat)
        by (apply (live_apart2 RT AF S1 mm dat rs pixd 64 A); [solve [in_live_tac]| solve [in_live_tac]| exact DNE])
    end.
    assert (PFPS : forall a, pixs <= a < pixs + 64 -> PF a) by (intros a Ha; right; right; left; exists pixs, 64; split; [exact PIN| exact Ha]).
    assert (NEQPD : pixs + 64 <= pixd \/ pixd + 64 <= pixs)
      by (pose proof (NCP pixs (PFPS pixs ltac:(lia))); pose proof (NCP (pixs + 63) (PFPS (pixs + 63) ltac:(lia))); lia).
    (* [comment removed for export] *)
    assert (TAIL : forall (S : rts RT) (mE : mem) (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc' (sppw : word),
       ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -32) -> rw_cells asegs mE (usp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
       LIBH mE -> io_ssp mE ->
       rw_cells asegs mE pixd [C4 (Z_to_bv 64 (p_w vd)); C4 (Z_to_bv 64 (p_h vd)); C4 (Z_to_bv 64 (p_d vd)); C4 sppw;
                               C4 (Z_to_bv 64 (p_wpl vd)); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 (p_xres vd)); C4 (Z_to_bv 64 (p_yres vd));
                               C4 (Z_to_bv 64 (p_inf vd)); C4 (Z_to_bv 64 (p_spec vd)); C8 z64; C8 (Z_to_bv 64 (p_cmap vd)); C8 (Z_to_bv 64 dat)] ->
       agree_on PF m mE -> wmono asegs m mE ->
       rt_frames RT S = rt_frames RT Σ -> rt_live RT S = (dat, rs) :: (pixd, 64) :: rt_live RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
       rt_credit RT Σ - (2 * 67108864 + 16384 + 8 + 1) <= rt_credit RT S ->
       cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 pixs) (Z_to_bv 64 pixd)
                                       r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 r28 r29 r30 r31
                                       F' fc' 0x8f4fc mE))) QF).
    { intros S mE r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc' sppw ARTE MIE STE FRE LHE SSPE PXDE AGE WME EFR ELV ESP0 ECR.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | PXDE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | ART0 => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      clear_acc.
      pose proof (pix_obj_keep (rt_live RT Σ) m mE pixs v cv (keeps_live_of_agf _ _ _ _ _ AGF) POBJ) as POBJE.
      pose proof POBJE as (PXCE & _). unfold pix_cells in PXCE.
      unfold entry_st.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
      (* [comment removed for export] *)
      Time walk_to AF MST [(usp - 32, usp); (pixd, pixd + 64)] [0x8e648; 0x8f8fc; 0x8dd94; 0x91080; 0x8dad0; 0x8d86c].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]).
      set (vd1 := mkPixv (p_w vd) (p_h vd) (p_d vd) (bv_unsigned sppw) (p_wpl vd) (bv_unsigned (sx32 (Z_to_bv 64 (p_xres v))))
                         (bv_unsigned (sx32 (Z_to_bv 64 (p_yres v)))) (p_inf vd) (p_spec vd) 0 dat).
      eapply cps_seq.
      { eapply CC with (lo := lo) (pixd := pixd) (pixs := pixs) (vd := vd1) (v := v) (cv := cv) (ras := @nil Z); rt_side idtac.
        all: lazymatch goal with
             | |- pix_obj _ _ _ _ (mkCmapv 0 0 0 0) =>
                 unfold pix_obj, pix_cells, chunk, pix_hdr_ok, rsize, vd1; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
                 rewrite !Z_to_bv_bv_unsigned; rewrite VCMAP in PXDE; split; [exact PXDE|];
                 split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]|];
                 split; [split; [exact HDd| split; [exact HWd| split; [exact HHd| split; [exact HWPLd| exact HRSd]]]]|];
                 split; [right; split; [split; [solve [in_live_tac]| split; [lia| split; [assumption| lia]]]| exact DNE]| left; reflexivity]
             | |- pix_obj _ _ _ _ _ =>
                 apply (pix_obj_mono (rt_live RT Σ)); [rewrite ELV; intros e He; right; right; exact He|
                   lazymatch goal with |- pix_obj _ ?mc _ _ _ => exact (pix_obj_keep _ m mc pixs v cv (keeps_live_of_agf _ _ _ _ _ AGF) POBJ) end]
             | |- p_d _ = p_d _ => unfold vd1; cbn [p_d]; exact VD
             | |- _ <> _ => unfold parked in NEQPD; lia
             | |- uctx _ _ _ _ => unfold uctx; cbn [chain_ok]; unfold link_invalid; rewrite ?unsigned_lit by lia; left; lia
             | |- In _ CLIENT_TRACES => exact tr_tmpl_copycmap
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFTOVER:" g
             end. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]|
                                     cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
      lazymatch goal with H : pix_obj _ _ _ (pixv_cmap vd1 ?c) ?cvx |- _ => rename H into POBJ2; set (cmapd := c) in *; rename cvx into cvd end.
      lazymatch goal with H : rt_live RT ?S2 = (if cmapd =? 0 then _ else _) |- _ => rename H into LV2 end.
      lazymatch goal with H : cmapd <> 0 -> _ |- _ => rename H into CMI end.
      (* [comment removed for export] *)
      lazymatch type of LV2 with rt_live RT ?S2 = _ =>
        assert (SUB2 : forall e, In e (rt_live RT S) -> In e (rt_live RT S2)) by (rewrite LV2; destruct (cmapd =? 0); [auto| intros e He; right; right; exact He]);
        assert (LEN2 : Z.of_nat (length (rt_live RT S2)) <= Z.of_nat (length (rt_live RT Σ)) + 4) by (rewrite LV2, ELV; destruct (cmapd =? 0); cbn [length]; lia);
        assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n)
          by (rewrite LV2; destruct (Z.eqb_spec cmapd 0) as [CE|CNE];
              [ rewrite ELV; intros p n Hin; cbn [In] in Hin; destruct Hin as [Hin|[Hin|Hin]]; [injection Hin as <- <-; lia| injection Hin as <- <-; lia| exact (LVP _ _ Hin)]
              | destruct POBJ2 as (_ & _ & _ & _ & [CZ|((_ & _ & (_ & _ & _ & AN) & _) & _)]); [cbn [pixv_cmap p_cmap] in CZ; contradiction|];
                rewrite ELV; intros p n Hin; cbn [In] in Hin; destruct Hin as [Hin|[Hin|[Hin|[Hin|Hin]]]];
                [injection Hin as <- <-; exact AN| injection Hin as <- <-; lia| injection Hin as <- <-; lia| injection Hin as <- <-; lia| exact (LVP _ _ Hin)] ]);
        assert (INPD2 : In (pixd, 64) (rt_live RT S2)) by (apply SUB2; rewrite ELV; right; left; reflexivity);
        assert (INDAT2 : In (dat, rs) (rt_live RT S2)) by (apply SUB2; rewrite ELV; left; reflexivity);
        assert (INPS2 : In (pixs, 64) (rt_live RT S2)) by (apply SUB2; rewrite ELV; right; right; exact PIN);
        assert (SUB02 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S2)) by (intros e He; apply SUB2; rewrite ELV; right; right; exact He)
      end.
      (* [comment removed for export] *)
      lazymatch goal with A : ART RT ?S2 ?mm |- cps _ (ASTA RT ?S2 _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
        assert (CMAP_AP : cmapd <> 0 -> In (cmapd, 24) (rt_live RT S2) /\ (cmapd + 24 <= pixd \/ pixd + 64 <= cmapd) /\ (cmapd + 24 <= dat \/ dat + rs <= cmapd))
          by (intros CNZ; destruct POBJ2 as (_ & _ & _ & _ & [CZ|(CO & N1 & N2 & N3 & N4)]); [cbn [pixv_cmap p_cmap] in CZ; contradiction|];
              destruct CO as (_ & (CIN & _) & _); cbn [pixv_cmap p_cmap p_data vd1] in CIN, N1, N3;
              split; [exact CIN|]; split; [apply (live_apart2 RT AF S2 mm cmapd 24 pixd 64 A CIN INPD2 N1)| apply (live_apart2 RT AF S2 mm cmapd 24 dat rs A CIN INDAT2 N3)]);
        assert (PCS : forall a, aclient (rt_live RT S2) (rt_frames RT Σ) usp a -> usp <= a \/ a < lo)
          by (intros a Ha; pose proof (aclient_split RT AF S2 mm usp a A) as SPL;
              repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H in SPL end;
              repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in SPL end;
              destruct (SPL Ha) as [HH|HH]; [left; exact HH| right; unfold STACK_WIN in HH; lia]);
        (* [comment removed for export] *)
        pose proof (agree_refl (fun a => aclient (rt_live RT S2) (rt_frames RT Σ) usp a /\ outside [(pixd, pixd + 64); (dat, dat + rs)] a) mm) as AGC
      end.
      hide AGC. park LV2.
      pose proof POBJ2 as (PXD2 & _). unfold pix_cells, pixv_cmap, vd1 in PXD2.
      cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD2. rewrite !Z_to_bv_bv_unsigned in PXD2.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
      (* [comment removed for export] *)
      Time walk_to AF MST [(usp - 32, usp); (pixd, pixd + 64)] [0x8e648; 0x8f8fc; 0x8dd94; 0x91080; 0x8dad0; 0x8d86c].
      split_at PXD2 10%nat PXT. split_at PXT 1%nat PXR.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]).
      eapply cps_seq.
      { eapply SR with (lo := lo) (pd := pixd + 40); rt_side idtac.
        all: lazymatch goal with
             | |- optr _ _ _ _ _ =>
                 unfold optr, optrL; split; [left; exists pixd, 64; split; [solve [in_live_tac]| lia]|]; split; [lia|];
                 split; [clear - PD16; Z.div_mod_to_equations; lia|];
                 split; [unfold parked in PDH; lia| unfold parked in PDS; unfold SEGTOP_A; lia]
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- ?g => idtac "LEFTOVER:" g
             end. }
      after_call RT AF.
      unfold hid in AGC.
      agf_call AGC AG ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                             destruct Hx as [_ Hx2]; cbn [outside] in Hx2 |- *; split; [lia| exact I]]).
      hide AGC.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                       [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (SUB02 e He)| solve [frames_sub_tac]| lia]|
                                     cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
      lazymatch goal with T : rw_cells asegs ?mm (pixd + 40) [C8 ?t] |- _ =>
        lazymatch type of PXD2 with rw_cells _ _ _ ?cs1 => lazymatch type of PXR with rw_cells _ _ _ ?cs3 =>
          assert (PXD3 : rw_cells asegs mm pixd (cs1 ++ ([C8 t] ++ cs3)));
          [ apply rw_cells_app; split; [exact PXD2|]; cbn [cells_size csize Nat.add];
            apply rw_cells_app; split; [replace (pixd + Z.of_nat 40) with (pixd + 40) by lia; exact T|];
            cbn [cells_size csize Nat.add]; replace (pixd + Z.of_nat 40 + Z.of_nat 8) with (pixd + 48) by lia; exact PXR
          | cbn [app] in PXD3; clear PXD2 T PXR ] end end end.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
      (* [comment removed for export] *)
      Time walk_to AF MST [(usp - 32, usp); (pixd, pixd + 64)] [0x8e648; 0x8f8fc; 0x8dd94; 0x91080; 0x8dad0; 0x8d86c].
      unfold hid in AGC.
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGC MUx ltac:(fun Hx => destruct Hx as [HxA HxO]; pose proof (PCS _ HxA); cbn [outside] in HxO |- *; split; [lia| split; [exact (proj1 HxO)| exact I]]) end.
      hide AGC.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]).
      set (v3 := mkPixv (p_w vd) (p_h vd) (p_d vd) (bv_unsigned sppw) (p_wpl vd) (bv_unsigned (sx32 (Z_to_bv 64 (p_xres v))))
                        (bv_unsigned (sx32 (Z_to_bv 64 (p_yres v)))) (bv_unsigned (sx32 (Z_to_bv 64 (p_inf v)))) (p_spec vd) cmapd dat).
      lazymatch type of PXD3 with rw_cells _ ?mb _ _ => lazymatch type of POBJ2 with pix_obj (rt_live RT ?S2) ?ma _ _ _ =>
        lazymatch goal with A : ART RT ?S3 mb |- _ =>
          assert (POBJ3 : pix_obj (rt_live RT S3) mb pixd v3 cvd)
            by (assert (PXD3' : rw_cells asegs mb pixd (pix_cells v3))
                  by (unfold pix_cells, v3; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite !Z_to_bv_bv_unsigned; exact PXD3);
                apply (pix_obj_retarget (rt_live RT S2) (rt_live RT S3) ma mb pixd (pixv_cmap vd1 cmapd) v3 cvd POBJ2 PXD3'); try reflexivity;
                [ intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
                | cbn [pixv_cmap p_cmap]; intros CNZ; destruct (CMAP_AP CNZ) as (CIN & AP1 & AP2); unfold hid in AGC;
                  eapply keeps_live_of_agree; [exact AGC| intros e [<-|[]]; exact CIN|
                    intros b k xx [E|[]] Hx; injection E as <- <-; cbn [outside]; split; [lia| split; [lia| exact I]]] ])
        end end end.
      unfold v3 in POBJ3.
      eapply cps_seq.
      { eapply PD with (lo := lo) (pix := pixd) (cv := cvd)
          (v := mkPixv (p_w vd) (p_h vd) (p_d vd) (bv_unsigned sppw) (p_wpl vd) (bv_unsigned (sx32 (Z_to_bv 64 (p_xres v))))
                       (bv_unsigned (sx32 (Z_to_bv 64 (p_yres v)))) (bv_unsigned (sx32 (Z_to_bv 64 (p_inf v)))) (p_spec vd) cmapd dat); rt_side idtac.
        all: lazymatch goal with
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ => lres_tac
             | |- ?g => idtac "LEFTOVER:" g
             end. }
      after_call RT AF.
      unfold hid in AGC.
      agf_call AGC AG ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                             destruct Hx as [_ Hx2]; cbn [outside] in Hx2 |- *; split; [exact (proj1 (proj2 Hx2))| exact I]]).
      hide AGC.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                       [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (SUB02 e He)| solve [frames_sub_tac]| lia]|
                                     cbn [outside]; pose proof (NCD _ Hx); split; [lia| exact I]]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
      Time walk_to AF MST [(usp - 32, usp)] (@nil Z).
      cps_stop.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?SF _ _ _ => exists SF, pixd, v3, cvd end.
      split.
      2:{ unfold pm_copy_live, rsize, v3. cbn [p_cmap p_data p_wpl p_h]. unpark LV2.
          split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; fold rs; destruct (cmapd =? 0); reflexivity|].
          clear LV2. alg_tac. }
      eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
      split; [intros a Ha _; apply AGF; exact Ha|]. split; [exact PNZ|].
      split.
      { lazymatch type of PXD3 with rw_cells _ ?mb _ _ => lazymatch type of POBJ2 with pix_obj (rt_live RT ?S2) ?ma _ _ _ =>
          assert (PXF : rw_cells asegs mb pixd (pix_cells v3))
            by (unfold pix_cells, v3; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite !Z_to_bv_bv_unsigned; exact PXD3);
          lazymatch goal with |- pix_obj ?lvF _ _ _ _ =>
            apply (pix_obj_retarget (rt_live RT S2) lvF ma mb pixd (pixv_cmap vd1 cmapd) v3 cvd POBJ2 PXF); try reflexivity end end end.
        - intros e He. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. exact He.
        - cbn [pixv_cmap p_cmap]. intros CNZ. destruct (CMAP_AP CNZ) as (CIN & AP1 & AP2). unfold hid in AGC.
          eapply keeps_live_of_agree; [exact AGC| intros e [<-|[]]; exact CIN| intros b k xx [E|[]] Hx; injection E as <- <-; cbn [outside]; split; [lia| split; [lia| exact I]]]. }
      unfold pm_hdr_copy, v3. cbn [p_w p_h p_d p_wpl p_data p_cmap].
      split; [exact VW|]. split; [exact VH|]. split; [exact VD|].
      split; [rewrite HWPLd, HWPL, VW, VD; reflexivity|].
      split; [exact VDATA|].
      split; [intros CZ; destruct (Z.eq_dec cmapd 0) as [E|NE]; [exact E| destruct (CMI NE) as (NZ & _); contradiction]|].
      intros NE. destruct (CMI NE) as (_ & R). exact R. }
    (* [comment removed for export] *)
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 32, usp); (pixd, pixd + 64)] [0x8f4fc; 0x8e648; 0x8f8fc; 0x8dd94; 0x91080; 0x8dad0; 0x8d86c].
    assert (NEPD : pixs <> pixd) by (unfold parked in NEQPD; lia).
    br.
    Time awalk [0x8f4fc; 0x8e648; 0x8f8fc; 0x8dd94; 0x91080; 0x8dad0; 0x8d86c].
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:HSPP end.
    + (* [comment removed for export] *)
      clear HSPP.
      Time awalk [0x8f4fc; 0x8e648; 0x8f8fc; 0x8dd94; 0x91080; 0x8dad0; 0x8d86c].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]).
      (eapply cps_seq; [eapply REI with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |]).
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
      to_entry.
      eapply TAIL with (sppw := Z_to_bv 64 (p_spp vd)).
      all: lazymatch goal with
           | |- ART _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- stk _ _ _ _ => assumption
           | |- LIBH _ => assumption
           | |- io_ssp _ => assumption
           | |- rw_cells asegs _ _ [_; _; _; _] => exact FR
           | |- rw_cells asegs _ _ _ => exact PXD
           | |- agree_on _ _ _ => exact AGF
           | |- wmono _ ?m0 ?mf => lazymatch goal with WMx : wmono asegs m0 mf |- _ => exact WMx end
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
           | |- ?g => idtac "LEFTOVER:" g
           end.
    + (* [comment removed for export] *)
      clear HSPP.
      Time awalk [0x8f4fc; 0x8e648; 0x8f8fc; 0x8dd94; 0x91080; 0x8dad0; 0x8d86c].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [solve [in_live_tac]| lia]| exact I]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]).
      eapply TAIL with (sppw := sx32 (Z_to_bv 64 (p_spp v))).
      all: lazymatch goal with
           | |- ART _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- stk _ _ _ _ => assumption
           | |- LIBH _ => assumption
           | |- io_ssp _ => assumption
           | |- rw_cells asegs _ _ [_; _; _; _] => exact FR
           | |- rw_cells asegs _ _ _ => exact PXD
           | |- agree_on _ _ _ => exact AGF
           | |- wmono _ ?m0 ?mf => lazymatch goal with WMx : wmono asegs m0 mf |- _ => exact WMx end
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
           | |- ?g => idtac "LEFTOVER:" g
           end.
Qed.
End TMPL.

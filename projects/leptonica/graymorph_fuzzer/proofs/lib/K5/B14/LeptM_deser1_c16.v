(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_deserkit LeptC_deser2_defs Lept_deser_defs LeptM_deser1_kit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section DESER1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis CRE : pixCreate_cps RT.
Hypothesis DES : pixDestroy_cps RT.
Hypothesis CMD : pixcmapDeserialize_cps RT.
Hypothesis SETC : pixSetColormap_cps RT.

Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (QF : config -> Prop) (fr : Z) (dp n : Z) (ras : list Z).

Theorem deser_cut1_ok_16 :
  (forall rdes, In rdes [0xae030; 0xae1c4] -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut2_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ->
  deser_cut1_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP RERR CRE DES CMD SETC.
  (* [comment removed for export] *)
  intros CTXA LVP EPI CUT2.
  intros S mc nc w h d psz j0 j1 jp f0 f1 f2 c16 vx pd r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r20 r25 r28 r29 r30 r31 F' fc'
    ARTc MIc STc FR FRM FSH LHc SSPc AGF FRS ESP0 ECR ELV NCR WR HR DR PSZD PSZR PSZ.
  pose proof (CTXA 0xae030 ltac:(cbn; tauto)) as CTX1. pose proof (CTXA 0xae1c4 ltac:(cbn; tauto)) as CTX2. clear CTXA.
  destruct CTX1 as (FDO & MST & ART0 & LOW & LOR & LO0 & SPT & SPA & SPB & FRB & LVB & CRB & NR & DP0 & DPA & OWN & CHN & RA4 & TRS1).
  destruct CTX2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TRS2).
  unfold deser_epi_stmt_16 in EPI. unfold deser_cut2_stmt_16 in CUT2.
  set (PF := deser_PF RT Σ usp) in *.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  unfold entry_st.
  (* [comment removed for export] *)
  assert (LSUB0 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) by (intros e He; rewrite ELV; exact He).
  pose proof (af_frames_range RT AF S mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF S mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG).
  pose proof (af_frames_hi RT AF S mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 1) with 128 in FRHI, FRSH. rewrite ESP0 in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  assert (NFA : forall a, PF a -> (a < fr \/ fr + 128 <= a) /\ (a < shad fr \/ shad (fr + 128) <= a)).
  { intros a Ha. apply (new_frame_apart RT AF S mc fr 1%nat (rt_frames RT Σ) (rt_live RT Σ) usp a ARTc FRS LSUB0);
      [rewrite ESP0; lia| rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  assert (FRTOP : fr + 128 <= 140737488355328) by (clear - FRHI SP0R; lia).
  pose proof (proj2 FRM) as WFR. pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add deser_fshadow] in WFR, WFS.
  change (Z.of_nat 120) with 120 in WFR. change (Z.of_nat 16) with 16 in WFS.
  unfold deser_fshadow in FSH.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 224, usp)] [0x90d6c].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  eapply cps_seq.
  { pose proof CRE as CR; unfold pixCreate_cps in CR.
    eapply CR with (lo := lo) (w := w) (h := h) (d := d); rt_side idtac.
    all: lazymatch goal with
         | |- s32 _ _ => unfold s32; split; [lia| reflexivity]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold RASTER_COST; lres_tac
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  Time after_call RT AF. unfold RASTER_COST in *.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact LSUB0| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with H : ?p = 0 \/ _ |- _ => rename H into POBJ; set (pixd := p) in * end.
  lazymatch goal with H : rt_live RT _ = (if pixd =? 0 then _ else _) |- _ => rename H into LVH end.
  destruct (Z.eq_dec pixd 0) as [PZ|PNZ].
  { (* [comment removed for export] *)
    clear POBJ. rewrite PZ in *. change (0 =? 0) with true in LVH. cbv iota in LVH.
    ds_refresh RT AF GP.
    Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    lazymatch goal with |- ?g => idtac "LEAF1-AT-RERR" end.
    ds_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH LVP usp lo (usp + -176)
      [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    all: lazymatch goal with |- ?g => idtac "LEAF1-LEFTOVER:" g end. }
  (* [comment removed for export] *)
  destruct POBJ as [PZ'|(POBJ & VW & VH & VD & PDNZ & PCM0)]; [contradiction|].
  replace (pixd =? 0) with false in LVH by (symmetry; apply Z.eqb_neq; exact PNZ).
  lazymatch type of POBJ with pix_obj _ _ _ ?vv _ => set (v := vv) in * end.
  destruct POBJ as (PXC & (INP & PX0 & PX16 & _) & HOK & DAT & PCM).
  destruct DAT as [E|((IND & DA0 & DA16 & DAN) & DNE)]; [contradiction|].
  clearbody v. destruct v as [w' h' d' spp wpl xres yres inf spec pcm data].
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in *. subst w' h' d' pcm.
  unfold pix_cells in PXC. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXC.
  unfold rsize in *. cbn [p_wpl p_h] in *.
  set (rs := 4 * (wpl * h)) in *.
  assert (EPS : psz = rs) by (destruct HOK as (_ & _ & _ & HWPL & _); cbn [p_w p_d p_wpl] in HWPL; unfold rs; rewrite HWPL; exact PSZD).
  rewrite EPS in *. clear EPS PSZD.
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?X ?mm |- cps _ (ASTA RT ?X _ _) _ =>
    assert (FRESH : forall e, In e (rt_live RT Σ) -> fst e <> pixd /\ fst e <> data)
      by (intros [q j] He; cbn [fst]; pose proof (LVP q j He) as J; split;
          [ apply (live_pos_ne RT AF X mm [(data, rs)] pixd 64 (rt_live RT Σ) q j A ltac:(rewrite LVH, ELV; reflexivity)); [right; exact He| lia| exact J]
          | apply (live_pos_ne RT AF X mm [] data rs ((pixd, 64) :: rt_live RT Σ) q j A ltac:(rewrite LVH, ELV; reflexivity)); [right; exact He| exact DAN| exact J] ]) end.
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP data rs.
  lazymatch goal with A : ART RT ?X ?mm |- cps _ (ASTA RT ?X _ _) _ =>
    assert (FRSx : rt_frames RT X = (fr, 1%nat) :: rt_frames RT Σ)
      by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
  fframe_chunk RT AF fr 1%nat 128 pixd 64. fframe_chunk RT AF fr 1%nat 128 data rs.
  ds_refresh RT AF GP.
  Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  rewrite ?Z.add_0_r. swrap_fix.      (* [comment removed for export] *)
  brfork HNC.
  1:{ (* [comment removed for export] *)
    awalk [0xae158].
    cps_stop. art_now RT AF ltac:(ds_ivt).
    lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
    to_entry.
    eapply CUT2 with (pixd := pixd) (cm := 0) (nc := nc) (v := mkPixv w h d spp wpl xres yres inf spec 0 data) (cv := mkCmapv 0 0 0 0).
    all: cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data].
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- rw_cells _ _ ?A _ => lazymatch goal with FRx : rw_cells asegs _ A _ |- _ => exact FRx end
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => lia
         | |- forall e, In e _ -> In e _ => intros e He; rewrite LVH, ELV; right; right; exact He
         | |- pix_obj _ _ _ _ _ =>
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [lazymatch goal with |- rw_cells _ _ ?A _ => lazymatch goal with PX : rw_cells asegs _ A _ |- _ => exact PX end end|];
             split; [split; [exact INP| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [exact IND| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| left; reflexivity]
         | |- _ <> 0 => exact PDNZ
         | |- _ <= _ <= _ => lia
         | |- 0 < _ -> _ => intros NCP; exfalso; clear - NCP HNC; lia
         | |- _ = 0 -> _ => intros _; split; reflexivity
         | |- 4 * _ = _ => exact PSZ
         | |- live_destroy _ _ _ _ = _ =>
             rewrite LVH, ELV; apply live_destroy_new; [reflexivity| reflexivity| exact PDNZ| intros EE; apply DNE; symmetry; exact EE| exact FRESH]
         | |- forall p k, In (p, k) _ -> 0 < k =>
             rewrite LVH, ELV; intros p k [EE|[EE|Hp]]; [injection EE as <- <-; exact DAN| injection EE as <- <-; clear; lia| exact (LVP p k Hp)]
         | |- Z.of_nat _ <= _ => rewrite LVH, ELV; cbn [length]; clear; lia
         | |- ?g => idtac "CUT2a-LEFTOVER:" g
         end. }
  (* [comment removed for export] *)
  assert (NC0 : 0 < nc) by lia.
  destruct OWN as (dpp & dpk & DIN0 & DLO & DHI).
  pose proof (af_live_range RT AF Σ m dpp dpk ART0 DIN0) as (_ & DPR & _). unfold STACK_WIN in DPR.      (* [comment removed for export] *)
  ds_awalk.
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
  eapply cps_seq.
  { pose proof CMD as CM; unfold pixcmapDeserialize_cps in CM.
    eapply CM with (lo := lo) (dp := dp + 24) (ncolors := nc); rt_side idtac.
    all: lazymatch goal with
         | |- _ < _ <= _ => lia
         | |- _ mod 4 = 0 => clear - DPA; Z.div_mod_to_equations; lia
         | |- own_live _ _ _ => exists dpp, dpk; split; [rewrite LVH, ELV; right; right; exact DIN0| clear - DLO DHI PSZ DAN; lia]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "CMD-LEFTOVER:" g
         end. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LVH, ELV; right; right; exact He| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with H : ?p = 0 \/ _ |- _ => rename H into CMOBJ; set (cmap := p) in * end.
  lazymatch goal with H : rt_live RT _ = (if cmap =? 0 then _ else _) |- _ => rename H into LVH2 end.
  destruct (Z.eq_dec cmap 0) as [CZ|CNZ].
  { (* [comment removed for export] *)
    clear CMOBJ. rewrite CZ in *. change (0 =? 0) with true in LVH2. cbv iota in LVH2.
    ds_refresh RT AF GP.
    Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    split_at FRM 3%nat FRp. split_at FRp 1%nat FRtail.
    pose proof FSH as SHC. split_at SHC 10%nat SHC2. split_at SHC2 1%nat SHC3. clear SHC SHC3.
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
    at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
    eapply cps_seq.
    { pose proof DES as DY. unfold pixDestroy_cps in DY.
      eapply DY with (lo := lo) (pp := fr + 80) (pix := pixd) (v := mkPixv w h d spp wpl xres yres inf spec 0 data) (cv := mkCmapv 0 0 0 0)
                     (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; change (fs_size 1) with 128;
                 split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity|];
                 split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [clear - FR0; lia|]; split; [clear - FRTOP; lia|];
                 replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHC2 as [[_ B] _]; exact B
               | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FRSH; lia| right; clear - FRSEG; unfold SEGTOP_A; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact FRp
           | |- pix_obj _ _ _ _ _ =>
               unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
               split; [lazymatch goal with |- rw_cells _ _ ?A _ => lazymatch goal with PX : rw_cells asegs _ A _ |- _ => exact PX end end|];
               split; [split; [right; left; reflexivity| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
               split; [exact HOK|]; split; [right; split; [split; [left; reflexivity| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| left; reflexivity]
           | |- uctx _ _ _ _ =>
               unfold uctx; rewrite !unsigned_lit by (clear - SPT LOR LO0; lia);
               apply chain_ok_push with (fp1 := bv_unsigned s0);
               [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia
               | split; [exact RA4| apply bv_unsigned_in_range] | apply bv_unsigned_in_range
               | rewrite !Z_to_bv_bv_unsigned; exact FRrec3
               | eapply chain_ok_keep; [exact CHN|]; eapply agree_sub; [exact AGF|]; cbv beta; intros xx Hxx; left; exact Hxx ]
           | |- Forall _ _ => rewrite ?unsigned_lit by (clear; lia); exact TRS2
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           | |- ?g => idtac "DES2-LEFTOVER:" g
           end. }
    Time after_call RT AF.
    (* [comment removed for export] *)
    lazymatch goal with H : rt_live RT _ = live_destroy _ _ _ _ |- _ =>
      rewrite LVH2, LVH, ELV in H;
      rewrite (live_destroy_new pixd (mkPixv w h d spp wpl xres yres inf spec 0 data) (mkCmapv 0 0 0 0) data rs (rt_live RT Σ) eq_refl eq_refl PDNZ ltac:(intros EE; apply DNE; symmetry; exact EE) FRESH) in H end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                      [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; destruct (NFA _ Hx) as [N1 _]; split; [lia| exact I]]).
    ds_refresh RT AF GP.
    Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
    pose proof RERR as RE; unfold returnError_cps in RE.
    eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
    Time after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx);
                              [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]).
    ds_refresh RT AF GP.
    Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    (* [comment removed for export] *)
    lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 80) [C8 _], F3 : rw_cells asegs ?mm (fr + 88) _
                        |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (WFRn : wr_at asegs mm fr 120)
        by (apply (proj2 (wr_at_app mm fr 80 40 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
            apply (proj2 (wr_at_app mm (fr + 80) 8 32 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
            replace (fr + 80 + 8) with (fr + 88) by lia; exact (proj2 F3)) end.
    ds_to_epi RT AF AGF PFS NFA (usp + -176).
    eapply EPI with (pixr := 0) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (cv := mkCmapv 0 0 0 0).
    all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- rw_cells _ _ ?A _ => lazymatch goal with FRx : rw_cells asegs _ A _ |- _ => exact FRx end
         | |- wr_at _ _ _ 120 => exact WFRn
         | |- wr_at _ _ _ _ => lazymatch goal with FSx : rw_cells asegs _ (fr / 8 + 2147450880) _ |- _ => exact (proj2 FSx) end
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- forall e, In e _ -> In e _ => intros e He; exact He
         | |- _ \/ _ => left; reflexivity
         | |- 0 = 0 -> _ => intros _; reflexivity
         | |- 0 <> 0 -> _ => intros HH; contradiction
         | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
         | |- Z.of_nat _ <= _ => clear; lia
         | |- ?g => idtac "EPI2-LEFTOVER:" g
         end. }
  (* [comment removed for export] *)
  destruct CMOBJ as [CZ'|(CMO & CNV)]; [contradiction|].
  replace (cmap =? 0) with false in LVH2 by (symmetry; apply Z.eqb_neq; exact CNZ).
  lazymatch type of CMO with cmap_obj _ _ _ ?cc => set (cv := cc) in * end. clearbody cv.
  pose proof CMO as (_ & (CIN & CP0 & CP16 & _) & (AIN & AR0 & AR16 & ARN) & CMOK & ANE).
  set (arr := c_arr cv) in *. set (an := 4 * c_nalloc cv) in *.
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?X ?mm |- cps _ (ASTA RT ?X _ _) _ =>
    assert (LV4 : rt_live RT X = (arr, an) :: (cmap, 24) :: (data, rs) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVH2, LVH, ELV; reflexivity);
    assert (NE1 : cmap <> pixd) by (apply (live_pos_ne RT AF X mm [(arr, an); (cmap, 24); (data, rs)] pixd 64 (rt_live RT Σ) cmap 24 A LV4); [cbn [app In]; tauto| lia| lia]);
    assert (NE2 : arr <> pixd) by (apply (live_pos_ne RT AF X mm [(arr, an); (cmap, 24); (data, rs)] pixd 64 (rt_live RT Σ) arr an A LV4); [cbn [app In]; tauto| lia| exact ARN]);
    assert (NE3 : cmap <> data) by (apply (live_pos_ne RT AF X mm [(arr, an); (cmap, 24)] data rs ((pixd, 64) :: rt_live RT Σ) cmap 24 A LV4); [cbn [app In]; tauto| exact DAN| lia]);
    assert (NE4 : arr <> data) by (apply (live_pos_ne RT AF X mm [(arr, an); (cmap, 24)] data rs ((pixd, 64) :: rt_live RT Σ) arr an A LV4); [cbn [app In]; tauto| exact DAN| exact ARN]);
    assert (FRESH4 : forall e, In e (rt_live RT Σ) -> fst e <> pixd /\ fst e <> data /\ fst e <> cmap /\ fst e <> arr)
      by (intros [q j] He; cbn [fst]; pose proof (LVP q j He) as J; destruct (FRESH _ He) as [F1 F2]; cbn [fst] in F1, F2;
          split; [exact F1|]; split; [exact F2|]; split;
          [ apply (live_pos_ne RT AF X mm [(arr, an)] cmap 24 ((data, rs) :: (pixd, 64) :: rt_live RT Σ) q j A LV4); [cbn [app In]; tauto| lia| exact J]
          | apply (live_pos_ne RT AF X mm [] arr an ((cmap, 24) :: (data, rs) :: (pixd, 64) :: rt_live RT Σ) q j A LV4); [cbn [app In]; tauto| exact ARN| exact J] ]);
    (* [comment removed for export] *)
    assert (NCP : forall a, PF a -> a < pixd \/ pixd + 64 <= a)
      by (intros a Ha; apply (later_chunk_apart RT AF X mm pixd 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A);
          [ rewrite LV4; cbn [In]; tauto
          | intros q j Hq; split; [rewrite LV4; cbn [In]; tauto| exact (proj1 (FRESH (q, j) Hq))]
          | intros e He; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; right; exact He
          | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia
          | exact Ha ]);
    pose proof (live_apart RT AF X mm cmap 24 pixd 64 A ltac:(rewrite LV4; cbn [In]; tauto) ltac:(rewrite LV4; cbn [In]; tauto) NE1) as CMPX
  end.
  chunk_facts RT AF GP cmap 24.
  ds_refresh RT AF GP.
  Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC-BEFORE-SETC:" pc end.
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
  eapply cps_seq.
  { pose proof SETC as SC; unfold pixSetColormap_cps in SC.
    eapply SC with (lo := lo) (pix := pixd) (cmap := cmap) (v := mkPixv w h d spp wpl xres yres inf spec 0 data) (cv := cv); rt_side idtac.
    all: cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data].
    all: lazymatch goal with
         | |- pix_obj _ _ _ _ _ =>
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [lazymatch goal with |- rw_cells _ _ ?A _ => lazymatch goal with PX : rw_cells asegs _ A _ |- _ => exact PX end end|];
             split; [split; [rewrite LV4; cbn [In]; tauto| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [rewrite LV4; cbn [In]; tauto| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| left; reflexivity]
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- 0 = 0 => reflexivity
         | |- _ <> _ => first [exact PDNZ | exact NE1 | exact NE2 | exact NE3 | exact NE4]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "SETC-LEFTOVER:" g
         end. }
  Time after_call RT AF.
  (* [comment removed for export] *)
  lazymatch type of CMO with cmap_obj ?lv ?ma _ _ =>
    lazymatch goal with AGx : agree_on ?P ma ?mb |- _ =>
      assert (CMO2 : cmap_obj lv mb cmap cv)
        by (apply (cmap_obj_agree lv P ma mb cmap cv CMO AGx); intros a Ha; split;
            [ right; right; left; exists cmap, 24; split; [solve [in_live_tac]| exact Ha]
            | cbn [outside]; split; [clear - CMPX Ha; unfold parked in CMPX; lia| exact I] ]) end end.
  clear CMO.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                    [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [In]; tauto| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXC2 end.
  unfold pix_cells in PXC2. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXC2.
  ds_refresh RT AF GP.
  Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  (* [comment removed for export] *)
  repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H in CMO2 end.
  brfork HRV.
  1:{ (* [comment removed for export] *)
    cps_stop. art_now RT AF ltac:(ds_ivt).
    lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
    to_entry.
    eapply CUT2 with (pixd := pixd) (cm := cmap) (nc := nc) (v := mkPixv w h d spp wpl xres yres inf spec cmap data) (cv := cv).
    all: cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data].
    all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- rw_cells _ _ ?A _ => lazymatch goal with FRx : rw_cells asegs _ A _ |- _ => exact FRx end
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => lia
         | |- forall e, In e _ -> In e _ => intros e He; cbn [In]; tauto
         | |- pix_obj _ _ _ _ _ =>
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [lazymatch goal with |- rw_cells _ _ ?A _ => lazymatch goal with PX : rw_cells asegs _ A _ |- _ => exact PX end end|];
             split; [split; [cbn [In]; tauto| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [cbn [In]; tauto| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]|
                                         right; split; [exact CMO2| split; [exact NE1| split; [exact NE2| split; [exact NE3| exact NE4]]]]]
         | |- _ <> 0 => exact PDNZ
         | |- _ <= _ <= _ => lia
         | |- 0 < _ -> _ => intros _; split; [exact CNZ| reflexivity]
         | |- _ = 0 -> _ => intros NCE; exfalso; clear - NCE NC0; lia
         | |- 4 * _ = _ => exact PSZ
         | |- live_destroy _ _ _ _ = _ =>
             apply live_destroy_new_cmap; [reflexivity| reflexivity| reflexivity| exact CNZ| clear - AR0; lia| exact PDNZ| intros EE; apply DNE; symmetry; exact EE
                                          | exact NE1| exact NE3| exact NE2| exact NE4| exact ANE| exact FRESH4]
         | |- forall p k, In (p, k) _ -> 0 < k =>
             intros p k [EE|[EE|[EE|[EE|Hp]]]];
             [injection EE as <- <-; exact ARN| injection EE as <- <-; clear; lia| injection EE as <- <-; exact DAN| injection EE as <- <-; clear; lia| exact (LVP p k Hp)]
         | |- Z.of_nat _ <= _ => cbn [length]; clear; lia
         | |- ?g => idtac "CUT2b-LEFTOVER:" g
         end. }
  (* [comment removed for export] *)
  {
    ds_awalk.
    split_at FRM 3%nat FRp. split_at FRp 1%nat FRtail.
    pose proof FSH as SHC. split_at SHC 10%nat SHC2. split_at SHC2 1%nat SHC3. clear SHC SHC3.
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
    at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
    eapply cps_seq.
    { pose proof DES as DY. unfold pixDestroy_cps in DY.
      eapply DY with (lo := lo) (pp := fr + 80) (pix := pixd) (v := mkPixv w h d spp wpl xres yres inf spec cmap data) (cv := cv)
                     (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; change (fs_size 1) with 128;
                 split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity|];
                 split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [clear - FR0; lia|]; split; [clear - FRTOP; lia|];
                 replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHC2 as [[_ B] _]; exact B
               | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FRSH; lia| right; clear - FRSEG; unfold SEGTOP_A; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact FRp
           | |- pix_obj _ _ _ _ _ =>
               unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
               split; [lazymatch goal with |- rw_cells _ _ ?A _ => lazymatch goal with PX : rw_cells asegs _ A _ |- _ => exact PX end end|];
               split; [split; [cbn [In]; tauto| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
               split; [exact HOK|]; split; [right; split; [split; [cbn [In]; tauto| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]|
                                           right; split; [exact CMO2| split; [exact NE1| split; [exact NE2| split; [exact NE3| exact NE4]]]]]
           | |- uctx _ _ _ _ =>
               unfold uctx; rewrite !unsigned_lit by (clear - SPT LOR LO0; lia);
               apply chain_ok_push with (fp1 := bv_unsigned s0);
               [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia
               | split; [exact RA4| apply bv_unsigned_in_range] | apply bv_unsigned_in_range
               | rewrite !Z_to_bv_bv_unsigned; exact FRrec3
               | eapply chain_ok_keep; [exact CHN|]; eapply agree_sub; [exact AGF|]; cbv beta; intros xx Hxx; left; exact Hxx ]
           | |- Forall _ _ => rewrite ?unsigned_lit by (clear; lia); exact TRS1
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           | |- ?g => idtac "DES3-LEFTOVER:" g
           end. }
    Time after_call RT AF.
    (* [comment removed for export] *)
    lazymatch goal with H : rt_live RT _ = live_destroy _ _ _ _ |- _ =>
      repeat match goal with H2 : rt_live RT _ = _ |- _ => lazymatch H2 with H => fail | _ => rewrite H2 in H end end;
      rewrite (live_destroy_new_cmap pixd (mkPixv w h d spp wpl xres yres inf spec cmap data) cv cmap arr an data rs (rt_live RT Σ) eq_refl eq_refl eq_refl
                 CNZ ltac:(clear - AR0; lia) PDNZ ltac:(intros EE; apply DNE; symmetry; exact EE) NE1 NE3 NE2 NE4 ANE FRESH4) in H end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                      [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; destruct (NFA _ Hx) as [N1 _]; split; [lia| exact I]]).
    ds_refresh RT AF GP.
    Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
    pose proof RERR as RE; unfold returnError_cps in RE.
    eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
    Time after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx);
                              [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]).
    ds_refresh RT AF GP.
    Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    (* [comment removed for export] *)
    lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 80) [C8 _], F3 : rw_cells asegs ?mm (fr + 88) _
                        |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (WFRn : wr_at asegs mm fr 120)
        by (apply (proj2 (wr_at_app mm fr 80 40 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
            apply (proj2 (wr_at_app mm (fr + 80) 8 32 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
            replace (fr + 80 + 8) with (fr + 88) by lia; exact (proj2 F3)) end.
    ds_to_epi RT AF AGF PFS NFA (usp + -176).
    eapply EPI with (pixr := 0) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (cv := mkCmapv 0 0 0 0).
    all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- rw_cells _ _ ?A _ => lazymatch goal with FRx : rw_cells asegs _ A _ |- _ => exact FRx end
         | |- wr_at _ _ _ 120 => exact WFRn
         | |- wr_at _ _ _ _ => lazymatch goal with FSx : rw_cells asegs _ (fr / 8 + 2147450880) _ |- _ => exact (proj2 FSx) end
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- forall e, In e _ -> In e _ => intros e He; exact He
         | |- _ \/ _ => left; reflexivity
         | |- 0 = 0 -> _ => intros _; reflexivity
         | |- 0 <> 0 -> _ => intros HH; contradiction
         | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
         | |- Z.of_nat _ <= _ => clear; lia
         | |- ?g => idtac "EPI3-LEFTOVER:" g
         end. }
Qed.
End DESER1.

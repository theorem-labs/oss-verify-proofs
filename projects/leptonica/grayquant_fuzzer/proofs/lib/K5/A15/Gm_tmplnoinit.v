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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_deserkit Lept_gmax_defs D_iface D_defs Gm_iface Gm_kit Gm_livekit Gm_leaf.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition TN_JOIN : Z := 0x942c4.

Lemma tr_noinit_tmpl : In [RA_NOINIT_MALLOC; 0x941a4] CLIENT_TRACES.
Proof. apply ct_mem_In. vm_compute. reflexivity. Qed.
Lemma tr_cmapcopy_tmpl : In [RA_CMAPCOPY_CALLOC1; 0x94330] CLIENT_TRACES.
Proof. apply ct_mem_In. vm_compute. reflexivity. Qed.

Section TN.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis NIS : pixCreateNoInit_sure_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.
Hypothesis CCM : pixCopyColormap_cps RT.
Hypothesis SRN : stringReplace_null_cps RT.
Hypothesis PAD : pixSetPadBits_cps RT.

Theorem pixCreateTemplateNoInit_ok : pixCreateTemplateNoInit_cps RT.
Proof using AF RC GP NIS RERR CCM SRN PAD.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixs vs cvs FDO MST -> -> POS ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POS as (PXS & (PSIN & PS0 & PS16 & _) & HOKS & _ & PSCM).
  pose proof (hdr_args_ok_of vs HOKS) as HAOK.
  pose proof HOKS as (HD1 & HW1 & HH1 & HWPL & HRS).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixCreateTemplateNoInit, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, TEMPLATE_COST, RASTER_COST, TN_JOIN in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof NIS as NI. unfold pixCreateNoInit_sure_cps in NI. pose proof RERR as RE. unfold returnError_cps in RE.
  pose proof CCM as CM. unfold pixCopyColormap_cps in CM. pose proof SRN as SR. unfold stringReplace_null_cps in SR.
  pose proof PAD as PD. unfold pixSetPadBits_cps in PD.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a)
    by (intros q k a Hq Ha; right; right; left; exists q, k; split; [exact Hq| lia]).
  chunk_facts RT AF GP pixs 64.
  pose proof (af_acc_live RT AF Σ m pixs 64 ART0 PSIN) as (_ & ACCS).
  unfold pix_cells in PXS.
  assert (DBND : 1 <= p_d vs <= 32) by (cbn [In] in HD1; lia).
  hide POS. hide PSCM. hide HAOK. hide HOKS.
  carve_frame 32%nat ST.
  Time walk_to AF MST [(usp - 32, usp)] [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688].
  cwalk [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688].
  rewrite (sx32_small (p_w vs)), (sx32_small (p_h vs)), (sx32_small (p_d vs)) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  unfold hid in HAOK.
  eapply cps_seq.
  { eapply NI with (lo := lo) (w := p_w vs) (h := p_h vs) (d := p_d vs) (ras := @nil Z); rt_side idtac.
    all: lazymatch goal with
         | |- s32 _ _ => split; [lia| reflexivity]
         | |- hdr_args_ok _ _ _ => exact HAOK
         | |- uctx _ _ _ _ => unfold uctx; cbn [chain_ok]; unfold link_invalid; rewrite ?unsigned_lit by ul; left; lia
         | |- In _ CLIENT_TRACES => exact tr_noinit_tmpl
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold RASTER_COST; lres_tac
         | |- ?g => idtac "LEFT:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with H : pix_obj _ _ ?p ?vv _ |- _ => rename H into POD; set (pixd := p) in *; set (v1 := vv) in * end.
  lazymatch goal with H : rt_live RT _ = (p_data v1, _) :: _ |- _ => rename H into LVN end.
  lazymatch goal with H : p_w v1 = _ |- _ => rename H into VW end.
  lazymatch goal with H : p_h v1 = _ |- _ => rename H into VH end.
  lazymatch goal with H : p_d v1 = _ |- _ => rename H into VD end.
  lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into VDATA end.
  lazymatch goal with H : p_cmap v1 = 0 |- _ => rename H into VCMAP end.
  pose proof POD as (PXD & (PDIN & PD0 & PD16 & _) & HOKD & PDDATA & _).
  destruct PDDATA as [PDZ|((DIN & DA0 & DA16 & DAN) & DNE)]; [exfalso; exact (VDATA PDZ)|].
  set (dat := p_data v1) in *. set (rs := rsize v1) in *.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    assert (SUBP : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S) /\ fst e <> pixd)
      by (intros e He; split; [rewrite LVN; right; right; exact He|];
          apply (fresh_chunk_ne RT AF S mm [(dat, rs)] pixd 64 _ e A LVN); [ cbn [app]; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]);
    assert (SUBD : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S) /\ fst e <> dat)
      by (intros e He; split; [rewrite LVN; right; right; exact He|];
          apply (fresh_chunk_ne RT AF S mm [] dat rs _ e A LVN); [ cbn [app]; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]);
    assert (NCP : forall a, PF a -> a < pixd \/ pixd + 64 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF S mm pixd 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A PDIN SUBP);
          [ solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]);
    assert (NCD : forall a, PF a -> a < dat \/ dat + rs <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF S mm dat rs (rt_live RT Σ) (rt_frames RT Σ) usp a A DIN SUBD);
          [ solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
  assert (NPS : pixs <> pixd) by (exact (proj2 (SUBP (pixs, 64) PSIN))).
  assert (NDS : pixs <> dat) by (exact (proj2 (SUBD (pixs, 64) PSIN))).
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  unfold pix_cells in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  hide POD. hide SUBP. hide SUBD. hide HOKD.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 32, usp); (pixd, pixd + 64)] [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688; 0x942c4].
  cwalk [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688; 0x942c4].
  lazymatch goal with FRx : rw_cells asegs _ (usp + -32) ?cs, PX : rw_cells asegs _ pixd (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
    assert (CONT : forall (S : rts RT) (mE : mem) (sppw : word)
              (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
        ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -32) -> rw_cells asegs mE (usp + -32) cs ->
        LIBH mE -> io_ssp mE -> agree_on PF m mE -> wmono asegs m mE ->
        rw_cells asegs mE pixd (c0 :: c1 :: c2 :: C4 sppw :: rest) ->
        rt_live RT S = (dat, rs) :: (pixd, 64) :: rt_live RT Σ -> rt_frames RT S = rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
        rt_credit RT Σ - (2 * 67108864 + 16384 + 4 + 1) <= rt_credit RT S ->
        cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 pixs) (Z_to_bv 64 pixd)
                                        r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11
                                        r28 r29 r30 r31 F' fc' 0x942c4 mE))) QF) end.
  { intros S mE sppw r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
      ARTE MIE STE FRE LHE SSPE AGE WME PXE ELV EFR ESP0 ECR.
    clear AGF. rename AGE into AGF.
    repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | PXE => fail | _ => clear H end end.
    repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
    repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
    repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
    repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
    repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
    repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
    repeat match goal with H : munch _ _ _ |- _ => clear H end.
    repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
    repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
    repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
    repeat match goal with H : In _ (rt_live RT _) |- _ => lazymatch H with PSIN => fail | _ => clear H end end.
    clear_acc.
    unfold hid in POS.
    assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) by (intros e He; rewrite ELV; right; right; exact He).
    assert (POS1 : pix_obj (rt_live RT S) mE pixs vs cvs).
    { apply (pix_obj_mono (rt_live RT Σ) _ mE pixs vs cvs LSUB). apply (pix_obj_agree (rt_live RT Σ) PF m mE pixs vs cvs POS AGF PML).
      destruct POS as (PXS0 & _). apply (rw_cells_agree_nw asegs m mE _ _ PXS0). intros a Ha. apply AGF.
      apply (PML pixs 64 _ PSIN). unfold pix_cells in Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
    hide POS.
    assert (INPD : In (pixd, 64) (rt_live RT S)) by (rewrite ELV; right; left; reflexivity).
    assert (INDAT : In (dat, rs) (rt_live RT S)) by (rewrite ELV; left; reflexivity).
    assert (INPS : In (pixs, 64) (rt_live RT S)) by (exact (LSUB _ PSIN)).
    pose proof POS1 as (PXS & _). unfold pix_cells in PXS. hide POS1.
    pose proof (live_apart2 RT AF S mE pixs 64 pixd 64 ARTE INPS INPD ltac:(intros E; inversion E; exact (NPS ltac:(assumption)))) as DSP.
    pose proof (live_apart2 RT AF S mE pixs 64 dat rs ARTE INPS INDAT ltac:(intros E; inversion E; exact (NDS ltac:(assumption)))) as DSD.
    pose proof (live_apart2 RT AF S mE pixd 64 dat rs ARTE INPD INDAT ltac:(intros E; inversion E; unfold parked in *; lia)) as DPD.
    unfold entry_st.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 32, usp); (pixd, pixd + 64)] [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688].
    cwalk [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [exact INPD| lia]| exact I]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]).
    unfold hid in POS, HOKD.
    lazymatch goal with PX : rw_cells asegs ?mc pixd (_ :: _ :: _ :: C4 sppw :: _ :: _ :: C4 ?xw :: C4 ?yw :: _) |- _ =>
      set (vd1 := mkPixv (p_w vs) (p_h vs) (p_d vs) (bv_unsigned sppw) (p_wpl v1) (bv_unsigned xw) (bv_unsigned yw) (p_inf v1) (p_spec v1) 0 dat);
      assert (POD1 : pix_obj (rt_live RT S) mc pixd vd1 (mkCmapv 0 0 0 0))
        by (unfold pix_obj, pix_cells, chunk, pix_hdr_ok, rsize, vd1; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
            rewrite !Z_to_bv_bv_unsigned;
            split; [exact PX|]; split; [split; [exact INPD| split; [lia| split; [assumption| lia]]]|];
            split; [destruct HOKD as (Q1 & Q2 & Q3 & Q4 & Q5); rewrite VW, VH, VD in *; split; [exact Q1| split; [exact Q2| split; [exact Q3| split; [exact Q4| exact Q5]]]]|];
            replace (4 * (p_wpl v1 * p_h vs)) with rs by (unfold rs, rsize; rewrite VH; reflexivity);
            split; [right; split; [split; [exact INDAT| split; [lia| split; [assumption| lia]]]| unfold parked in *; lia]| left; reflexivity]);
      assert (POS2 : pix_obj (rt_live RT S) mc pixs vs cvs)
        by (apply (pix_obj_mono (rt_live RT Σ) _ mc pixs vs cvs LSUB); apply (pix_obj_agree (rt_live RT Σ) PF m mc pixs vs cvs POS AGF PML);
            unfold pix_cells; exact PXS) end.
    hide POS. hide HOKD.
    eapply cps_seq.
    { eapply CM with (lo := lo) (pixd := pixd) (pixs := pixs) (vd := vd1) (vs := vs) (cvd := mkCmapv 0 0 0 0) (cvs := cvs) (ras := @nil Z); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ (mkCmapv 0 0 0 0) => exact POD1
           | |- pix_obj _ _ _ _ _ => exact POS2
           | |- _ <> _ => intros E; apply NPS; symmetry; exact E
           | |- p_d _ = p_d _ => reflexivity
           | |- p_cmap _ = 0 => reflexivity
           | |- _ -> _ /\ _ =>
               intros _; split; [unfold uctx; cbn [chain_ok]; unfold link_invalid; rewrite ?unsigned_lit by ul; left; unfold parked in *; lia| exact tr_cmapcopy_tmpl]
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => unfold RASTER_COST; lres_tac
           | |- ?g => idtac "LEFT:" g
           end. }
    clear POD1 POS2.
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
    lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD2 end.
    lazymatch goal with H : rt_live RT ?S2 = (if ?c =? 0 then _ else _) |- _ => rename H into LV2; set (cmd := c) in * end.
    lazymatch goal with H : cmd = 0 \/ (cmap_obj _ _ cmd ?cv /\ _) |- _ => rename H into CMO; set (cvn := cv) in * end.
    lazymatch goal with H : p_cmap vs = 0 -> cmd = 0 |- _ => rename H into CMZ end.
    lazymatch goal with H : p_cmap vs <> 0 -> cmd <> 0 |- _ => rename H into CMNZ end.
    unfold pix_cells in PXD2. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data vd1] in PXD2.
    set (PC := fun a : Z => cmd <> 0 /\ cmd <= a < cmd + 24).
    lazymatch goal with A : ART RT ?S2 ?mm |- cps _ (ASTA RT ?S2 _ _) _ =>
      assert (LSUB2 : forall e, In e (rt_live RT S) -> In e (rt_live RT S2)) by (intros e He; rewrite LV2; destruct (cmd =? 0); [exact He| right; right; exact He]);
      pose proof (LSUB2 _ INPD) as INPD2; pose proof (LSUB2 _ INDAT) as INDAT2; pose proof (LSUB2 _ INPS) as INPS2;
      pose proof (agree_refl PC mm) as AGC;
      assert (CMF : cmd <> 0 -> In (cmd, 24) (rt_live RT S2) /\ In (c_arr cvn, 4 * c_nalloc cvn) (rt_live RT S2)
                 /\ 0 < cmd /\ 0 < c_arr cvn /\ 0 < 4 * c_nalloc cvn
                 /\ (cmd + 24 <= pixd \/ pixd + 64 <= cmd) /\ (cmd + 24 <= dat \/ dat + rs <= cmd)
                 /\ (c_arr cvn + 4 * c_nalloc cvn <= pixd \/ pixd + 64 <= c_arr cvn)
                 /\ (c_arr cvn + 4 * c_nalloc cvn <= dat \/ dat + rs <= c_arr cvn)
                 /\ cmd + 24 <= rt_sp0 RT Σ - 8388608 /\ c_arr cvn <> cmd)
        by (intros NZ; destruct CMO as [Z0|(CO & _)]; [exfalso; exact (NZ Z0)|];
            destruct CO as (_ & (CI & C0 & _ & _) & (AI & A0 & _ & AN) & _ & ANE);
            assert (LV2' : rt_live RT S2 = (c_arr cvn, 4 * c_nalloc cvn) :: (cmd, 24) :: rt_live RT S)
              by (rewrite LV2; replace (cmd =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); reflexivity);
            pose proof (af_live_disj RT AF S2 mm cmd 24 pixd 64 [(c_arr cvn, 4 * c_nalloc cvn)] (rt_live RT S) A LV2' ltac:(right; exact INPD)) as Q1;
            pose proof (af_live_disj RT AF S2 mm cmd 24 dat rs [(c_arr cvn, 4 * c_nalloc cvn)] (rt_live RT S) A LV2' ltac:(right; exact INDAT)) as Q2;
            pose proof (af_live_disj RT AF S2 mm (c_arr cvn) (4 * c_nalloc cvn) pixd 64 [] ((cmd, 24) :: rt_live RT S) A LV2' ltac:(right; exact INPD)) as Q3;
            pose proof (af_live_disj RT AF S2 mm (c_arr cvn) (4 * c_nalloc cvn) dat rs [] ((cmd, 24) :: rt_live RT S) A LV2' ltac:(right; exact INDAT)) as Q4;
            pose proof (af_live_range RT AF S2 mm cmd 24 A CI) as (_ & Q5 & _);
            repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in Q5 end; unfold STACK_WIN in Q5;
            repeat split; first [assumption | lia]) end.
    hide CMO. hide LV2.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 32, usp); (pixd, pixd + 64)] [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688].
    cwalk [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688].
    lazymatch goal with AGx : agree_on PC _ ?mm, MUx : munch _ ?mm _ |- _ =>
      agf_munch AGx MUx ltac:(fun Hx => destruct Hx as (NZ & Hx); destruct (CMF NZ) as (_ & _ & _ & _ & _ & Q1 & _ & _ & _ & Q5 & _);
                                        cbn [outside]; split; [lia| split; [lia| exact I]]) end.
    hide AGC.
    split_at PXD2 10%nat PTX2. split_at PTX2 1%nat PTX3.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [exact INPD2| lia]| exact I]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]).
    eapply cps_seq.
    { eapply SR with (lo := lo) (pd := pixd + 40); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ => unfold optrL, accok, own_live; split; [left; exists pixd, 64; split; [exact INPD2| lia]| unfold parked in *; unfold SEGTOP_A; repeat split; lia]
           | |- rw_cells _ _ _ [C8 _] => exact PTX2
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- ?g => idtac "LEFT:" g
           end. }
    clear PTX2.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S2 ?mm |- cps _ (ASTA RT ?S2 _ _) _ =>
      assert (LSUB3 : forall e, In e (rt_live RT S) -> In e (rt_live RT S2))
        by (intros e He; lazymatch goal with H : rt_live RT S2 = rt_live RT _ |- _ => rewrite H end; apply LSUB2; exact He);
      pose proof (LSUB3 _ INPD) as INPD3; pose proof (LSUB3 _ INDAT) as INDAT3; pose proof (LSUB3 _ INPS) as INPS3;
      assert (CMI3 : cmd <> 0 -> In (cmd, 24) (rt_live RT S2))
        by (intros NZ; lazymatch goal with H : rt_live RT S2 = rt_live RT _ |- _ => rewrite H end; exact (proj1 (CMF NZ))) end.
    unfold hid in AGC.
    lazymatch type of AGC with agree_on _ _ ?mm => lazymatch goal with AG : agree_on (fun _ => _ /\ _) mm _ |- _ =>
      agf_call AGC AG ltac:(fun Hx => destruct Hx as (NZ & Hx); destruct (CMF NZ) as (_ & _ & _ & _ & _ & Q1 & _);
                                      split; [right; right; left; exists cmd, 24; split; [exact (CMI3 NZ)| lia]| cbn [outside]; split; [lia| exact I]]) end end.
    hide AGC.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; apply LSUB3; apply LSUB; exact He| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
    lazymatch goal with P1 : rw_cells asegs ?mm pixd ?c1, P2 : rw_cells asegs ?mm (pixd + 40) ?c2, P3 : rw_cells asegs ?mm (pixd + 48) ?c3 |- _ =>
      assert (PXD3 : rw_cells asegs mm pixd (c1 ++ c2 ++ c3))
        by (apply (proj2 (rw_cells_app mm pixd c1 (c2 ++ c3))); split; [exact P1|];
            replace (pixd + Z.of_nat (cells_size c1)) with (pixd + 40) by (cbn [cells_size csize Nat.add]; lia);
            apply (proj2 (rw_cells_app mm (pixd + 40) c2 c3)); split; [exact P2|];
            replace (pixd + 40 + Z.of_nat (cells_size c2)) with (pixd + 48) by (cbn [cells_size csize Nat.add]; lia); exact P3);
      cbn [app] in PXD3; clear P1 P2 P3 end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 32, usp); (pixd, pixd + 64)] [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688].
    cwalk [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688].
    unfold hid in AGC.
    lazymatch type of AGC with agree_on _ _ ?mm => lazymatch goal with MUx : munch _ mm _ |- _ =>
      agf_munch AGC MUx ltac:(fun Hx => destruct Hx as (NZ & Hx); destruct (CMF NZ) as (_ & _ & _ & _ & _ & Q1 & _ & _ & _ & Q5 & _);
                                        cbn [outside]; split; [lia| split; [lia| exact I]]) end end.
    hide AGC.
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    lazymatch goal with H : rt_live RT ?S2 = rt_live RT _, A : ART RT ?S2 _ |- evt _ (fun _ => cps _ (ASTA RT ?S2 _ _) _) _ => rename H into LV3 end.
    assert (CMF2 : cmd <> 0 -> 0 < 4 * c_nalloc cvn /\ (cmd + 24 <= pixd \/ pixd + 64 <= cmd) /\ (cmd + 24 <= dat \/ dat + rs <= cmd)
               /\ (c_arr cvn + 4 * c_nalloc cvn <= pixd \/ pixd + 64 <= c_arr cvn)
               /\ (c_arr cvn + 4 * c_nalloc cvn <= dat \/ dat + rs <= c_arr cvn))
      by (intros NZ; destruct (CMF NZ) as (_ & _ & _ & _ & AN & Q1 & Q2 & Q3 & Q4 & _); repeat split; assumption).
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [exact INPD3| lia]| exact I]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]).
    unfold hid in HOKD, CMO, AGC.
    lazymatch goal with PX : rw_cells asegs ?mc pixd (_ :: _ :: _ :: C4 ?sw :: _ :: _ :: C4 ?xw :: C4 ?yw :: C4 ?iw :: _) |- cps _ (ASTA RT ?S3 _ _) _ =>
      set (vd3 := mkPixv (p_w vs) (p_h vs) (p_d vs) (bv_unsigned sw) (p_wpl v1) (bv_unsigned xw) (bv_unsigned yw) (bv_unsigned iw) (p_spec v1) cmd dat);
      assert (POD3 : pix_obj (rt_live RT S3) mc pixd vd3 cvn)
        by (pose proof PX as PX';
            unfold pix_obj, pix_cells, chunk, pix_hdr_ok, rsize, vd3; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
            rewrite ?Z_to_bv_bv_unsigned in PX'; rewrite ?Z_to_bv_bv_unsigned;
            split; [exact PX'|]; split; [split; [exact INPD3| split; [exact PD0| split; [exact PD16| lia]]]|];
            split; [destruct HOKD as (Q1 & Q2 & Q3 & Q4 & Q5); rewrite VD in Q1; rewrite VW in Q2; rewrite VH in Q3; rewrite VW, VD in Q4; rewrite VH in Q5; split; [exact Q1| split; [exact Q2| split; [exact Q3| split; [exact Q4| exact Q5]]]]|];
            replace (4 * (p_wpl v1 * p_h vs)) with rs by (unfold rs, rsize; rewrite VH; reflexivity);
            split; [right; split; [split; [exact INDAT3| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]|];
            exact (cmap_part_carry (rt_live RT x19) (rt_live RT S3) _ mc cmd cvn pixd dat rs _ CMO AGC ltac:(intros e He; rewrite LV3; exact He) CMF2 DAN)) end.
    hide HOKD. hide CMO. hide AGC.
    unfold hid in LV2.
    assert (LVX19 : Z.of_nat (length (rt_live RT x19)) <= Z.of_nat (length (rt_live RT Σ)) + 4
                    /\ (forall p n, In (p, n) (rt_live RT x19) -> 0 < n)).
    { rewrite LV2, ELV. destruct (Z.eq_dec cmd 0) as [Z0|NZ].
      - replace (cmd =? 0) with true by (symmetry; apply Z.eqb_eq; exact Z0). cbn [length]. split; [lia|].
        intros p n Hpn. cbn [In] in Hpn. destruct Hpn as [Hpn|[Hpn|Hpn]]; [injection Hpn as <- <-; exact DAN| injection Hpn as <- <-; lia| exact (LVP p n Hpn)].
      - replace (cmd =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). cbn [length]. split; [lia|].
        destruct (CMF NZ) as (_ & _ & _ & _ & AN & _).
        intros p n Hpn. cbn [In] in Hpn. destruct Hpn as [Hpn|[Hpn|[Hpn|[Hpn|Hpn]]]];
          [injection Hpn as <- <-; exact AN| injection Hpn as <- <-; lia| injection Hpn as <- <-; exact DAN| injection Hpn as <- <-; lia| exact (LVP p n Hpn)]. }
    destruct LVX19 as (LVX19 & LVP19).
    hide LV2.
    eapply cps_seq.
    { eapply PD with (lo := lo) (pix := pixd) (v := vd3) (cv := cvn); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POD3
           | |- p_data _ <> 0 => exact VDATA
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => unfold lres; rewrite LV3; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; unfold FRAMES_MAX, LIVE_MAX in *;
                                  split; [lia| split; [lia| split; [lia| exact LVP19]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear POD3. unfold vd3; clear vd3. cbn [p_data p_wpl p_h].
    replace (4 * (p_wpl v1 * p_h vs)) with rs by (unfold rs; rewrite VH; reflexivity).
    after_call RT AF.
    lazymatch goal with H : rt_live RT ?S2 = rt_live RT _, A : ART RT ?S2 _ |- cps _ (ASTA RT ?S2 _ _) _ => rename H into LV4 end.
    lazymatch goal with A : ART RT ?S2 ?mm |- cps _ (ASTA RT ?S2 _ _) _ =>
      assert (LSUB4 : forall e, In e (rt_live RT S) -> In e (rt_live RT S2)) by (intros e He; rewrite LV4; apply LSUB3; exact He);
      pose proof (LSUB4 _ INPD) as INPD4; pose proof (LSUB4 _ INDAT) as INDAT4; pose proof (LSUB4 _ INPS) as INPS4;
      assert (CMI4 : cmd <> 0 -> In (cmd, 24) (rt_live RT S2)) by (intros NZ; rewrite LV4; exact (CMI3 NZ)) end.
    unfold hid in AGC.
    lazymatch type of AGC with agree_on _ _ ?mm => lazymatch goal with AG : agree_on (fun _ => _ /\ _) mm _ |- _ =>
      agf_call AGC AG ltac:(fun Hx => destruct Hx as (NZ & Hx); destruct (CMF NZ) as (_ & _ & _ & _ & _ & _ & Q2 & _);
                                      split; [right; right; left; exists cmd, 24; split; [exact (CMI4 NZ)| clear - Hx; lia]| cbn [outside]; split; [clear - Hx Q2; clearbody rs; lia| exact I]]) end end.
    hide AGC.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; apply LSUB4; apply LSUB; exact He| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; pose proof (NCD _ Hx) as NCDx; split; [clear - NCDx; clearbody rs; lia| exact I]]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    Time walk_to AF MST [(usp - 32, usp)] (@nil Z).
    cwalk (@nil Z).
    try (lazymatch goal with ST' : stk asegs _ lo (usp + -32), FRx : rw_cells asegs _ (usp + -32) _ |- _ => release_frame FRx ST' usp end).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    unfold hid in AGC.
    lazymatch type of AGC with agree_on _ _ ?mm => lazymatch goal with MUx : munch _ mm _ |- _ =>
      agf_munch AGC MUx ltac:(fun Hx => destruct Hx as (NZ & Hx); destruct (CMF NZ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q5 & _);
                                        cbn [outside]; split; [lia| exact I]) end end.
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    unfold hid in HOKD, CMO, SUBP, SUBD, LV2.
    lazymatch goal with PX : rw_cells asegs ?mc pixd (_ :: _ :: _ :: C4 ?sw :: _ :: _ :: C4 ?xw :: C4 ?yw :: C4 ?iw :: _), A : ART RT ?S3 ?mc |- cps _ (ASTA RT ?S3 _ _) _ =>
      set (vdF := mkPixv (p_w vs) (p_h vs) (p_d vs) (bv_unsigned sw) (p_wpl v1) (bv_unsigned xw) (bv_unsigned yw) (bv_unsigned iw) (p_spec v1) cmd dat);
      assert (PODF : pix_obj (rt_live RT S3) mc pixd vdF cvn)
        by (pose proof PX as PX';
            unfold pix_obj, pix_cells, chunk, pix_hdr_ok, rsize, vdF; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
            rewrite ?Z_to_bv_bv_unsigned in PX'; rewrite ?Z_to_bv_bv_unsigned;
            split; [exact PX'|]; split; [split; [exact INPD4| split; [exact PD0| split; [exact PD16| lia]]]|];
            split; [destruct HOKD as (Q1 & Q2 & Q3 & Q4 & Q5); rewrite VD in Q1; rewrite VW in Q2; rewrite VH in Q3; rewrite VW, VD in Q4; rewrite VH in Q5;
                    split; [exact Q1| split; [exact Q2| split; [exact Q3| split; [exact Q4| exact Q5]]]]|];
            replace (4 * (p_wpl v1 * p_h vs)) with rs by (unfold rs, rsize; rewrite VH; reflexivity);
            split; [right; split; [split; [exact INDAT4| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]|];
            exact (cmap_part_carry (rt_live RT x19) (rt_live RT S3) _ mc cmd cvn pixd dat rs _ CMO AGC ltac:(intros e He; rewrite LV4, LV3; exact He) CMF2 DAN));
      assert (FRC : cmd <> 0 -> forall e, In e (rt_live RT Σ) -> fst e <> cmd /\ fst e <> c_arr cvn)
        by (intros NZ [q k] He; cbn [fst]; pose proof (LVP q k He) as KP; destruct (CMF NZ) as (_ & _ & _ & _ & AN & _);
            assert (LVF : rt_live RT S3 = (c_arr cvn, 4 * c_nalloc cvn) :: (cmd, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ)
              by (rewrite LV4, LV3, LV2, ELV; replace (cmd =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); reflexivity);
            pose proof (af_live_disj RT AF S3 mc cmd 24 q k [(c_arr cvn, 4 * c_nalloc cvn)] ((dat, rs) :: (pixd, 64) :: rt_live RT Σ) A LVF ltac:(right; right; right; exact He)) as Q1;
            pose proof (af_live_disj RT AF S3 mc (c_arr cvn) (4 * c_nalloc cvn) q k [] ((cmd, 24) :: (dat, rs) :: (pixd, 64) :: rt_live RT Σ) A LVF ltac:(right; right; right; exact He)) as Q2;
            clear - Q1 Q2 KP AN; split; lia)
    end.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S3 _ _ _ => exists S3, pixd, vdF, cvn end.
    split.
    2:{ split; [intros CZ; pose proof (CMZ CZ) as Z0; split; [exact Z0|];
                rewrite LV4, LV3, LV2, ELV, Z0; cbn [Z.eqb]; unfold rsize, vdF, rs; cbn [p_data p_wpl p_h]; rewrite VH; reflexivity|].
        (* [comment removed for export] *)
        split; [intros NZ; pose proof (CMNZ NZ) as NZ0; pose proof CMO as CMO'; unfold hid in CMO';
                destruct CMO' as [Z0|(_ & _ & CN)]; [exfalso; exact (NZ0 Z0)| exact CN]|].
        split; [rewrite LV4, LV3, LV2, ELV;
                apply (live_destroy_tmpl (rt_live RT Σ) pixd dat rs cmd (c_arr cvn) (4 * c_nalloc cvn) vdF cvn);
                [ reflexivity | reflexivity | intros _; reflexivity | exact VDATA | exact DNE
                | intros NZ; destruct (CMF NZ) as (_ & _ & _ & A0 & AN & Q1 & Q2 & Q3 & Q4 & _ & ANE); clear - A0 AN Q1 Q2 Q3 Q4 ANE DAN; clearbody rs; repeat split; lia
                | intros e He; split; [exact (proj2 (SUBP e He))| exact (proj2 (SUBD e He))]
                | exact FRC ]|].
        split; [rewrite LV4, LV3; exact LVP19|]. split; [rewrite LV4, LV3; exact LVX19|].
        repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
        unfold TEMPLATE_COST, RASTER_COST. repeat split; auto; lia. }
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { lazymatch goal with WMx : wmono asegs ?m0 ?mf |- wmono asegs ?m0 ?mf => exact WMx end. }
    split; [intros a Ha _; apply AGF; exact Ha|].
    split; [exact PODF|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity| exact VDATA].
  }
  brfork SPP.
  - try clear SPP.
    cwalk [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688; 0x942c4].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [exact PDIN| lia]| exact I]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]).
    eapply cps_seq.
    { eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | unfold RASTER_COST in *; lia]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
    lazymatch goal with A : ART RT ?S2 ?mm, PX : rw_cells asegs ?mm pixd (_ :: _ :: _ :: C4 ?sw :: _) |- cps _ (ASTA RT ?S2 _ _) _ =>
      eapply (CONT S2 mm sw) end.
    all: lazymatch goal with
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold RASTER_COST in *; lia
         | |- wmono asegs ?m0 ?mf => lazymatch goal with WMx : wmono asegs m0 mf |- _ => exact WMx end
         | |- _ => assumption
         end.
  - try clear SPP.
    cwalk [0x93410; 0x90c20; 0x90e84; 0x94854; 0x91118; 0x96688; 0x942c4].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pixd, 64; split; [exact PDIN| lia]| exact I]]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCP _ Hx); split; [lia| split; [lia| exact I]]) end.
    lazymatch goal with A : ART RT ?S2 ?mm, PX : rw_cells asegs ?mm pixd (_ :: _ :: _ :: C4 ?sw :: _) |- cps _ (ASTA RT ?S2 _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      eapply (CONT S2 mm sw) end.
    all: lazymatch goal with
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold RASTER_COST in *; lia
         | |- wmono asegs ?m0 ?mf => lazymatch goal with WMx : wmono asegs m0 mf |- _ => exact WMx end
         | |- _ => assumption
         end.
Qed.
End TN.

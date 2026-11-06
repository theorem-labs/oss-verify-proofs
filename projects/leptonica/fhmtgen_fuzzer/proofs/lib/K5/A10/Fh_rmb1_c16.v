(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_gmax_defs Lept_chain Gm_iface Gm_livekit Gm_livekit2 Fh_iface Gm_border_defs Gm_border_kit Fh_border1_defs Fh_border1_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= first [ zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac rmb_norm xw xh HWR HHR :=
  sx32_fix; rewrite ?(unsigned_lit xw) by (clear - HWR; lia); rewrite ?(unsigned_lit xh) by (clear - HHR; lia); swrap32_fix.

Section RBC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RE : returnError_cps RT e_returnErrorPtr.
Hypothesis CRE : pixCreate_cps RT.
Hypothesis CRES : pixCopyResolution_cps RT.
Hypothesis CSPP : pixCopySpp_cps RT.
Hypothesis CCM : pixCopyColormap_cps RT.
Hypothesis ROPS : pixRasterop_src1_cps RT.

Lemma rmborder1_c16 : rmborder1_case RT 16.
Proof using AF GP RE CRE CRES CSPP CCM ROPS.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pixs vs cvs ras
    FDO MST -> -> -> -> -> -> POBJ D8 VDATA HWB HHB TRC ENV RES AL.
  unfold lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold BORDER1_COST, RASTER_COST in *.
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _ & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixRemoveBorderGeneral, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF0 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (NW : hid (64 < p_w vs /\ p_w vs <= 20000 /\ 64 < p_h vs /\ p_h vs <= 20000))
    by (destruct POBJ as (_ & _ & (_ & A & B & _) & _); unfold hid; clear - A B HWB HHB; lia).
  chunk_facts RT AF GP pixs 64.
  chunk_facts RT AF GP (p_data vs) (rsize vs).
  unfold pix_cells in PXC.
  hide POBJ.
  carve_frame 176%nat ST.
  walk_to AF MST [(usp - 176, usp)] [e_stack_malloc 1%nat].

  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; clear - P LOR; split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 1%nat 128 pixs 64.
  fframe_chunk RT AF fr 1%nat 128 (p_data vs) (rsize vs).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 176, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x96a54].

  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                       destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCDP.
  park_disj.
  rewrite D8 in *.
  assert (NUMS : (0 < p_w vs <= 20000 /\ 0 < p_h vs <= 20000) /\ p_wpl vs = (p_w vs * 1 + 31) / 32 /\ 0 < 4 * (p_wpl vs * p_h vs) <= 67108864).
  { pose proof POBJ as PO. unfold hid in PO. destruct PO as (_ & _ & (_ & A & B & C & D) & _). rewrite D8 in C. clear - A B C D. tauto. }
  destruct NUMS as ((HWR & HHR) & EWPL & HSZ).
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x96aa8].
  rmb_norm (p_w vs) (p_h vs) HWR HHR.
  awalk [0x96abc].
  rmb_norm (p_w vs) (p_h vs) HWR HHR.
  awalk [e_pixCreate].
  rmb_norm (p_w vs) (p_h vs) HWR HHR.

  (* [comment removed for export] *)
  std_at_call RT AF PFS NFA LOR FR64.
  eapply cps_seq.
  { eapply CRE with (lo := lo) (w := p_w vs - 64) (h := p_h vs - 64) (d := 1); rt_side idtac.
    all: try (unfold s32; split; [clear - HWR HHR; lia | reflexivity]).
    - lenv_tac.
    - unfold RASTER_COST; lres_tac. }
  after_call RT AF.
  lazymatch goal with H : ?px = 0 \/ (pix_obj _ _ ?px ?v _ /\ _) |- _ => rename px into pixd; rename v into vd; rename H into PDIS end.
  lazymatch goal with H : rt_live RT ?S1 = (if pixd =? 0 then _ else _) |- _ => rename S1 into Σ1; rename H into LVD end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  unfold RASTER_COST in *.
  destruct PDIS as [PZ | (POBJD & EWd & EHd & EDd & VDD & VDC)].
  { (* [comment removed for export] *)
    subst pixd. change (0 =? 0) with true in LVD. cbv iota in LVD.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr].
    std_at_call RT AF PFS NFA LOR FR64.
    eapply cps_seq.
    { eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    epilogue_prep RT.
    walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x96d10].
    clear FSH FRM. try clear GSEV. clear_acc.
    frame_release_w RT AF GP MST Σ fr 1%nat 128 PF0 AGF PFS usp lo 0x96d18
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                      destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact Hx)
      ltac:(fun fl FLN => idtac).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 176, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -176) |- _ => release_frame FR ST' usp end.
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. exists 0, (mkPixv 0 0 0 0 0 0 0 0 0 0 0), (mkCmapv 0 0 0 0).
    split; [| split; [| split; [alg_tac| split; [alg_tac|]]]].
    2:{ lazymatch goal with |- new_pix1_live RT _ ?Sf _ _ _ => assert (ELV : rt_live RT Sf = rt_live RT Σ) by alg_tac; unfold new_pix1_live; rewrite ELV end.
        split; [intros _; reflexivity|]. split; [intros X; exfalso; apply X; reflexivity|]. split; [exact LVP| lia]. }
    2:{ credit_fin RT. }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split.
    { split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption].
      repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
    split; [| left; reflexivity].
    repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    intros a Ha Ho; exact (AGF a Ha). }
  (* [comment removed for export] *)
  pose proof POBJD as (PDC & (PDIN & PD0 & PD16 & _) & _ & PDATAD & _).
  destruct PDATAD as [DZd|((DDIN & DD0 & DD16 & DDSZ) & DDNE)]; [contradiction|].
  replace (pixd =? 0) with false in LVD by (symmetry; apply Z.eqb_neq; clear - PD0; lia).
  assert (FRS1 : rt_frames RT Σ1 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (SUBL : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1))
    by (intros e He; rewrite LVD; right; right; repeat match goal with H : rt_live RT x = _ |- _ => rewrite H end; exact He).
  chunk_facts RT AF GP pixd 64.
  chunk_facts RT AF GP (p_data vd) (rsize vd).
  fframe_chunk RT AF fr 1%nat 128 pixd 64.
  fframe_chunk RT AF fr 1%nat 128 (p_data vd) (rsize vd).
  park_disj.
  lazymatch goal with A1 : ART RT Σ1 ?m1 |- _ =>
    assert (NCD : forall a, PF0 a -> a < p_data vd \/ p_data vd + rsize vd <= a)
      by (intros a Ha; apply (new_chunk_apart RT AF Σ1 m1 (p_data vd) (rsize vd) ((pixd, 64) :: rt_live RT x) (rt_frames RT Σ1) usp a A1 LVD eq_refl);
          [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
          | apply (aclient_mono _ _ usp _ _ usp _ Ha); [intros e He; right; repeat match goal with H : rt_live RT x = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia] ]);
    assert (QPD : pixd + 64 <= p_data vd \/ p_data vd + rsize vd <= pixd)
      by (pose proof (af_live_disj RT AF Σ1 m1 (p_data vd) (rsize vd) pixd 64 [] ((pixd, 64) :: rt_live RT x) A1 LVD ltac:(left; reflexivity)) as X; clear - X; lia);
    assert (NCP : forall a, PF0 a -> a < pixd \/ pixd + 64 <= a)
      by (intros a Ha;
          pose proof (af_live_range RT AF Σ1 m1 pixd 64 A1 ltac:(solve [in_live_tac])) as (P0 & PHI & PSEG);
          repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in PHI end; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *;
          destruct Ha as [Hs|[Hs|[Hs|[Hs|Hs]]]];
          [ right; pose proof (PFS a (or_introl Hs)); lia
          | pose proof (client_static_below a Hs) as HB; unfold SEGTOP_A in HB; pose proof (client_static_lo a Hs) as HL; lia
          | destruct Hs as (p' & n' & Hin & Hp);
            pose proof (af_live_disj RT AF Σ1 m1 pixd 64 p' n' [(p_data vd, rsize vd)] (rt_live RT x) A1 LVD
                          ltac:(right; repeat match goal with H : rt_live RT x = _ |- _ => rewrite H end; exact Hin)) as D; lia
          | destruct Hs as (f & k & Hin & Hf);
            pose proof (af_frames_range RT AF Σ1 m1 f k A1 ltac:(rewrite FRS1; right; exact Hin)) as (_ & _ & _ & FLV);
            specialize (FLV pixd 64 ltac:(solve [in_live_tac])); lia
          | destruct Hs as (f & k & Hin & Hf);
            pose proof (af_fshadow_apart RT AF Σ1 m1 f k A1 ltac:(rewrite FRS1; right; exact Hin)) as (SA1 & _);
            specialize (SA1 pixd 64 ltac:(solve [in_live_tac])); lia ]);
    assert (QPP : pixs + 64 <= pixd \/ pixd + 64 <= pixs)
      by (pose proof (af_live_disj RT AF Σ1 m1 pixd 64 pixs 64 [(p_data vd, rsize vd)] (rt_live RT x) A1 LVD
                        ltac:(right; repeat match goal with H : rt_live RT x = _ |- _ => rewrite H end; exact PIN)) as X; clear - X; lia);
    assert (QPS : pixs + 64 <= p_data vd \/ p_data vd + rsize vd <= pixs)
      by (pose proof (af_live_disj RT AF Σ1 m1 (p_data vd) (rsize vd) pixs 64 [] ((pixd, 64) :: rt_live RT x) A1 LVD
                        ltac:(right; repeat match goal with H : rt_live RT x = _ |- _ => rewrite H end; exact PIN)) as X; clear - X; lia);
    assert (QDD : p_data vs + rsize vs <= p_data vd \/ p_data vd + rsize vd <= p_data vs)
      by (pose proof (af_live_disj RT AF Σ1 m1 (p_data vd) (rsize vd) (p_data vs) (rsize vs) [] ((pixd, 64) :: rt_live RT x) A1 LVD
                        ltac:(right; repeat match goal with H : rt_live RT x = _ |- _ => rewrite H end; exact DIN)) as X; clear - X; lia)
  end.
  assert (DNE2 : p_data vd <> p_data vs) by (clear - QDD DSZ DDSZ; unfold parked, rsize in *; lia).
  assert (PDS : pixd <> pixs).
  { clear - NCP PIN PX0. intros E. subst pixd. destruct (NCP pixs ltac:(right; right; left; exists pixs, 64; split; [exact PIN| lia])); lia. }
  assert (PDNZ : (pixd =? 0) = false) by (apply Z.eqb_neq; clear - PD0; lia).

  assert (CMIN : p_cmap vs <> 0 -> In (p_cmap vs, 24) (rt_live RT Σ)).
  { intros NZ. pose proof POBJ as PO'. unfold hid in PO'. destruct PO' as (_ & _ & _ & _ & [Z0|((_ & (CI & _) & _) & _)]); [contradiction| exact CI]. }
  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  unfold pix_cells in PDC.
  walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCopyResolution].
  std_at_call RT AF PFS NFA LOR FR64.
  regen_pxc PXC POBJ AGF PIN D8.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (POBJS1 : pix_obj (rt_live RT Σ1) mc pixs vs cvs)
      by (unfold hid in POBJ; apply (pix_obj_mono (rt_live RT Σ) (rt_live RT Σ1) mc pixs vs cvs SUBL); apply (pix_obj_agree_cm (rt_live RT Σ) PF0 m mc pixs vs cvs POBJ AGF); [intros NZ a Ha; right; right; left; exists (p_cmap vs), 24; split; [exact (CMIN NZ)| exact Ha] | unfold pix_cells; rewrite D8; exact PXC]);
    assert (POBJD1 : pix_obj (rt_live RT Σ1) mc pixd vd (mkCmapv 0 0 0 0))
      by (apply (pix_obj_nocmap (rt_live RT Σ1) (rt_live RT Σ1) _ mc pixd vd _ _ POBJD VDC (fun e He => He)); unfold pix_cells; exact PDC) end.
  eapply cps_seq.
  { eapply CRES with (lo := lo) (pixd := pixd) (pixs := pixs) (vd := vd) (vs := vs) (cvd := mkCmapv 0 0 0 0) (cvs := cvs); rt_side idtac;
      lazymatch goal with
      | |- pix_obj _ _ pixd _ _ => exact POBJD1
      | |- pix_obj _ _ pixs _ _ => exact POBJS1
      | |- pixd <> pixs => exact PDS
      | |- lenv _ _ _ _ _ _ => lenv_tac
      end. }
  after_call RT AF.
  lazymatch goal with H : rt_live RT ?S2 = rt_live RT Σ1 |- _ => rename S2 into Σ2; rename H into LV2 end.
  assert (SUBL2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2; exact (SUBL e He)).
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact SUBL2| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PDC2 end.
  unfold pix_cells in PDC2. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PDC2.

  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCopySpp].
  std_at_call RT AF PFS NFA LOR FR64.
  regen_pxc PXC POBJ AGF PIN D8.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (POBJS2 : pix_obj (rt_live RT Σ2) mc pixs vs cvs)
      by (unfold hid in POBJ; apply (pix_obj_mono (rt_live RT Σ) (rt_live RT Σ2) mc pixs vs cvs SUBL2); apply (pix_obj_agree_cm (rt_live RT Σ) PF0 m mc pixs vs cvs POBJ AGF); [intros NZ a Ha; right; right; left; exists (p_cmap vs), 24; split; [exact (CMIN NZ)| exact Ha] | unfold pix_cells; rewrite D8; exact PXC]);
    assert (POBJD2 : pix_obj (rt_live RT Σ2) mc pixd
                       (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) (p_cmap vd) (p_data vd)) (mkCmapv 0 0 0 0))
      by (apply (pix_obj_nocmap_fields (rt_live RT Σ1) (rt_live RT Σ2) _ mc pixd vd _ _ _ POBJD1 VDC ltac:(intros e He; rewrite LV2; exact He));
          try reflexivity; [exact VDC | unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PDC2]) end.
  eapply cps_seq.
  { eapply CSPP with (lo := lo) (pixd := pixd) (pixs := pixs)
      (vd := mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) (p_cmap vd) (p_data vd))
      (vs := vs) (cvd := mkCmapv 0 0 0 0) (cvs := cvs); rt_side idtac;
      lazymatch goal with
      | |- pix_obj _ _ pixd _ _ => exact POBJD2
      | |- pix_obj _ _ pixs _ _ => exact POBJS2
      | |- pixd <> pixs => exact PDS
      | |- lenv _ _ _ _ _ _ => lenv_tac
      | |- lres _ _ _ _ _ => lres_tac
      end. }
  after_call RT AF.
  lazymatch goal with H : rt_live RT ?S3 = rt_live RT Σ2 |- _ => rename S3 into Σ3; rename H into LV3 end.
  assert (SUBL3 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; exact (SUBL2 e He)).
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact SUBL3| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells (mkPixv _ _ _ ?sq _ _ _ _ _ _ _)) |- _ => rename H into PDC3; rename sq into sppd end.
  unfold pix_cells in PDC3. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PDC3.
  clear POBJS2 POBJD2.

  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCopyColormap].
  std_at_call RT AF PFS NFA LOR FR64.
  regen_pxc PXC POBJ AGF PIN D8.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (POBJS3 : pix_obj (rt_live RT Σ3) mc pixs vs cvs)
      by (unfold hid in POBJ; apply (pix_obj_mono (rt_live RT Σ) (rt_live RT Σ3) mc pixs vs cvs SUBL3); apply (pix_obj_agree_cm (rt_live RT Σ) PF0 m mc pixs vs cvs POBJ AGF); [intros NZ a Ha; right; right; left; exists (p_cmap vs), 24; split; [exact (CMIN NZ)| exact Ha] | unfold pix_cells; rewrite D8; exact PXC]);
    assert (POBJD3 : pix_obj (rt_live RT Σ3) mc pixd
                       (mkPixv (p_w vd) (p_h vd) (p_d vd) sppd (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) (p_cmap vd) (p_data vd)) (mkCmapv 0 0 0 0))
      by (apply (pix_obj_nocmap_fields (rt_live RT Σ1) (rt_live RT Σ3) _ mc pixd vd _ _ _ POBJD1 VDC ltac:(intros e He; rewrite LV3, LV2; exact He));
          try reflexivity; [exact VDC | unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PDC3]) end.
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
  eapply cps_seq.
  { eapply CCM with (lo := lo) (pixd := pixd) (pixs := pixs)
      (vd := mkPixv (p_w vd) (p_h vd) (p_d vd) sppd (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) (p_cmap vd) (p_data vd))
      (vs := vs) (cvd := mkCmapv 0 0 0 0) (cvs := cvs) (ras := bv_unsigned ra :: ras); rt_side idtac;
      lazymatch goal with
      | |- pix_obj _ _ pixd _ _ => exact POBJD3
      | |- pix_obj _ _ pixs _ _ => exact POBJS3
      | |- pixd <> pixs => exact PDS
      | |- p_d _ = p_d vs => cbn [p_d]; rewrite D8; exact EDd
      | |- p_cmap _ = 0 => exact VDC
      | |- p_cmap vs <> 0 -> _ =>
          let NZ := fresh "NZ" in intros NZ; destruct (TRC NZ) as (UCTX & TIN);
          pose proof (proj1 (Forall_inv (Forall_inv_tail (Forall_inv_tail (proj2 (client_trace_facts _ TIN)))))) as RA4096;
          split;
          [ unfold uctx in UCTX |- *; rewrite !unsigned_lit by ul;
            apply chain_ok_push with (fp1 := bv_unsigned s0);
            [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia
            | exact RA4096 | apply bv_unsigned_in_range
            | rewrite !Z_to_bv_bv_unsigned; exact FRrec3
            | eapply chain_ok_keep; [exact UCTX|]; eapply agree_sub; [exact AGF|]; cbv beta; intros xx Hxx; left; exact Hxx ]
          | rewrite ?unsigned_lit by (clear; lia); exact TIN ]
      | |- lenv _ _ _ _ _ _ => lenv_tac
      | |- lres _ _ _ _ _ => lres_tac
      | |- ?g => idtac "LEFTOVER:" g
      end. }
  after_call RT AF.
  lazymatch goal with H : p_cmap vs = 0 -> ?c = 0 |- _ => rename H into CMZ; rename c into cmapd end.
  lazymatch goal with H : p_cmap vs <> 0 -> cmapd <> 0 |- _ => rename H into CMNZ end.
  lazymatch goal with H : cmapd = 0 \/ (cmap_obj _ _ cmapd ?cv /\ _) |- _ => rename H into CMO; rename cv into cvn end.
  lazymatch goal with H : rt_live RT ?S4 = (if cmapd =? 0 then _ else _) |- _ => rename S4 into Σ4; rename H into LV4 end.
  assert (SUBL4 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ4))
    by (intros e He; rewrite LV4; destruct (cmapd =? 0); [exact (SUBL3 e He)| right; right; exact (SUBL3 e He)]).
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact SUBL3| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PDC4 end.
  unfold pix_cells in PDC4. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PDC4.
  clear SUBL SUBL2 POBJS1 POBJS3 POBJD3.
  destruct (Z.eq_dec cmapd 0) as [CZ|CNZ].
  - (* [comment removed for export] *)
    subst cmapd. change (0 =? 0) with true in LV4. cbv iota in LV4. clear CMO CMNZ SUBL3.
  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixRasterop].
  rop_pre RT AF PFS NFA LOR FR64.
  mk_pobjd POBJDc RT Σ1 pixd vd (mkPixv (p_w vd) (p_h vd) (p_d vd) sppd (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd)) POBJD1 VDC PDC4.
  regen_pxc PXC POBJ AGF PIN D8.
  lazymatch goal with SUB : (forall e, In e (rt_live RT Σ) -> In e (rt_live RT ?Sc)) |- cps _ (ASTA RT ?Sc _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (POBJSc : pix_obj (rt_live RT Sc) mc pixs vs cvs)
      by (unfold hid in POBJ; apply (pix_obj_mono (rt_live RT Σ) (rt_live RT Sc) mc pixs vs cvs SUB); apply (pix_obj_agree_cm (rt_live RT Σ) PF0 m mc pixs vs cvs POBJ AGF); [intros NZ a Ha; right; right; left; exists (p_cmap vs), 24; split; [exact (CMIN NZ)| exact Ha] | unfold pix_cells; rewrite D8; exact PXC]) end.
  lazymatch goal with P : rw_cells asegs _ (usp + -192) _ |- _ => pose proof P as PUSH; split_at PUSH 1%nat PUSH2; clear PUSH2 end.
  eapply cps_seq.
  { eapply ROPS with (lo := lo) (pixd := pixd) (pixs := pixs)
      (vd := mkPixv (p_w vd) (p_h vd) (p_d vd) sppd (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd))
      (vs := vs) (cvd := mkCmapv 0 0 0 0) (cvs := cvs) (dx := 0) (dy := 0) (dw := p_w vs - 64) (dh := p_h vs - 64) (sx := 32) (sy := 32); rt_side idtac;
      lazymatch goal with
      | |- pix_obj _ _ pixd _ _ => exact POBJDc
      | |- pix_obj _ _ pixs _ _ => exact POBJSc
      | |- rw_cells _ _ _ _ => exact PUSH
      | |- pixd <> pixs => exact PDS
      | |- p_d vs = 1 => exact D8
      | |- p_d _ = 1 => exact EDd
      | |- p_data vs <> 0 => exact VDATA
      | |- p_data _ <> 0 => exact VDD
      | |- p_data _ <> p_data vs => exact DNE2
      | |- _ mod 32 = 0 => reflexivity
      | |- rect_in 0 0 _ _ _ _ => unfold rect_in; cbn [p_w p_h]; rewrite EWd, EHd; clear - NW; unfold hid in NW; lia
      | |- rect_in 32 32 _ _ _ _ => unfold rect_in; clear - NW; unfold hid in NW; lia
      | |- lenv _ _ _ _ _ _ => lenv_tac
      | |- lres _ _ _ _ _ => lres_tac
      end. }
  after_call RT AF. clear POBJDc POBJSc PUSH.
  rop_post RT AF GP Σ usp NCD.

  (* [comment removed for export] *)
  regen_pxc PXC POBJ AGF PIN D8.
  walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x96cac].
  (* [comment removed for export] *)
  try (lazymatch goal with P : rw_cells asegs _ (usp + -192) _, ST' : stk asegs _ lo (usp + -192) |- _ => release_frame P ST' (usp + -176) end).
  try clear PXC. epilogue_prep RT.
  awalk [0x96d10].
  clear FSH FRM. try clear GSEV. clear_acc.
  frame_release_w RT AF GP MST Σ fr 1%nat 128 PF0 AGF PFS usp lo 0x96d18
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                      destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact Hx)
      ltac:(fun fl FLN => idtac).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 176, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -176) |- _ => release_frame FR ST' usp end.
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    exists pixd, (mkPixv (p_w vd) (p_h vd) (p_d vd) sppd (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd)), (mkCmapv 0 0 0 0).
    split; [| split; [| split; [alg_tac| split; [alg_tac|]]]].
    2:{ lazymatch goal with |- new_pix1_live RT _ ?Sf _ _ _ =>
          assert (ELV : rt_live RT Sf = (p_data vd, 4 * (p_wpl vd * p_h vd)) :: (pixd, 64) :: rt_live RT Σ)
            by (unfold rsize in *; rewrite ?PDNZ in *; alg_tac) end.
        assert (FRESH : forall e, In e (rt_live RT Σ) -> fst e <> pixd /\ fst e <> p_data vd).
        { intros [q k] He. cbn [fst]. pose proof (LVP q k He) as KP.
          assert (PQ : PF0 q) by (right; right; left; exists q, k; split; [exact He| lia]).
          pose proof (NCP q PQ) as N1. pose proof (NCD q PQ) as N2. unfold rsize in *. clear - N1 N2 DDSZ. lia. }
        unfold new_pix1_live. rewrite ELV.
        split; [intros E0; exfalso; clear - E0 PD0; lia|].
        split; [intros _; apply (live_destroy_tmpl (rt_live RT Σ) pixd (p_data vd) (4 * (p_wpl vd * p_h vd)) 0 0 0 _ (mkCmapv 0 0 0 0));
                [ reflexivity | reflexivity | intros X; exfalso; apply X; reflexivity | exact VDD | exact DDNE | intros X; exfalso; apply X; reflexivity
                | exact FRESH | intros X; exfalso; apply X; reflexivity ]|].
        split; [intros p n [E|[E|HI]]; [injection E as <- <-; unfold rsize in DDSZ; exact DDSZ| injection E as <- <-; lia| exact (LVP p n HI)]| cbn [length]; lia]. }
    2:{ credit_fin RT. }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split.
    { split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption].
      repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
    split.
    { repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. intros a Ha Ho; exact (AGF a Ha). }
    right. split.
    { lazymatch goal with |- pix_obj (rt_live RT ?Sf) ?mf _ _ _ =>
        apply (pix_obj_nocmap_fields (rt_live RT Σ1) (rt_live RT Sf) _ mf pixd vd _ _ _ POBJD1 VDC
                 ltac:(let e := fresh "e" in let He := fresh "He" in intros e He;
                       repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H end; exact He)) end;
        try reflexivity; unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PDC4. }
    cbn [p_w p_h p_d p_data p_cmap]. repeat split; first [assumption | lia].
  - (* [comment removed for export] *)
    destruct CMO as [Z0|(CO & CDEP)]; [exfalso; exact (CNZ Z0)|].
    replace (cmapd =? 0) with false in LV4 by (symmetry; apply Z.eqb_neq; exact CNZ).
    clear CMZ CMNZ.
    set (PC := fun a : Z => cmapd <> 0 /\ cmapd <= a < cmapd + 24).
    assert (INPD4 : In (pixd, 64) (rt_live RT Σ3)) by (rewrite LV3, LV2; exact PDIN).
    assert (INDD4 : In (p_data vd, rsize vd) (rt_live RT Σ3)) by (rewrite LV3, LV2; exact DDIN).
    assert (INFR4 : In (fr, 1%nat) (rt_frames RT Σ4)) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity).
    lazymatch goal with A : ART RT Σ4 ?mm |- cps _ (ASTA RT Σ4 _ _) _ =>
      pose proof (agree_refl PC mm) as AGC;
      pose proof CO as (_ & (CI & C0 & _ & _) & (AI & A0 & _ & AN) & _ & ANE);
      pose proof (af_live_disj RT AF Σ4 mm cmapd 24 pixd 64 [(c_arr cvn, 4 * c_nalloc cvn)] (rt_live RT Σ3) A LV4 ltac:(right; exact INPD4)) as Q1;
      pose proof (af_live_disj RT AF Σ4 mm cmapd 24 (p_data vd) (rsize vd) [(c_arr cvn, 4 * c_nalloc cvn)] (rt_live RT Σ3) A LV4 ltac:(right; exact INDD4)) as Q2;
      pose proof (af_live_disj RT AF Σ4 mm (c_arr cvn) (4 * c_nalloc cvn) pixd 64 [] ((cmapd, 24) :: rt_live RT Σ3) A LV4 ltac:(right; exact INPD4)) as Q3;
      pose proof (af_live_disj RT AF Σ4 mm (c_arr cvn) (4 * c_nalloc cvn) (p_data vd) (rsize vd) [] ((cmapd, 24) :: rt_live RT Σ3) A LV4 ltac:(right; exact INDD4)) as Q4;
      pose proof (af_live_range RT AF Σ4 mm cmapd 24 A CI) as (_ & Q5 & _);
      pose proof (af_frames_range RT AF Σ4 mm fr 1%nat A INFR4) as (_ & _ & _ & FLV); pose proof (FLV cmapd 24 CI) as QF1; clear FLV;
      pose proof (af_fshadow_apart RT AF Σ4 mm fr 1%nat A INFR4) as (SA1 & _); pose proof (SA1 cmapd 24 CI) as QF2; clear SA1 end.
    change (fs_size 1) with 128 in QF1, QF2. unfold shad, SHB in QF1, QF2.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in Q5 end. unfold STACK_WIN in Q5.
    assert (CMF2 : cmapd <> 0 -> 0 < 4 * c_nalloc cvn /\ (cmapd + 24 <= pixd \/ pixd + 64 <= cmapd) /\ (cmapd + 24 <= p_data vd \/ p_data vd + rsize vd <= cmapd)
               /\ (c_arr cvn + 4 * c_nalloc cvn <= pixd \/ pixd + 64 <= c_arr cvn)
               /\ (c_arr cvn + 4 * c_nalloc cvn <= p_data vd \/ p_data vd + rsize vd <= c_arr cvn))
      by (intros _; repeat split; assumption).
    assert (CMW : hid ((fr + 128 <= cmapd \/ cmapd + 24 <= fr) /\ (cmapd + 24 <= fr / 8 + 2147450880 \/ (fr + 128) / 8 + 2147450880 <= cmapd)
                       /\ cmapd + 24 <= rt_sp0 RT Σ - 8388608 /\ (cmapd + 24 <= p_data vd \/ p_data vd + rsize vd <= cmapd)))
      by (unfold hid; repeat split; assumption).
    clear Q1 Q2 Q3 Q4 Q5 QF1 QF2.
    (* [comment removed for export] *)
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixRasterop].
    lazymatch type of AGC with agree_on _ _ ?mm => lazymatch goal with MUx : munch _ mm _ |- _ =>
      agf_munch AGC MUx ltac:(fun Hx => destruct Hx as (_ & Hx); cbn [outside]; unfold hid in CMW; clear - Hx CMW LOW LOR FR64;
                                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end end.
    rop_pre RT AF PFS NFA LOR FR64.
    clear SUBL3.
    assert (SUB14 : forall e, In e (rt_live RT Σ1) -> In e (rt_live RT Σ4)) by (intros e He; rewrite LV4, LV3, LV2; right; right; exact He).
    lazymatch goal with |- cps _ (ASTA RT Σ4 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      assert (POBJDc : pix_obj (rt_live RT Σ4) mc pixd
                         (mkPixv (p_w vd) (p_h vd) (p_d vd) sppd (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) cmapd (p_data vd)) cvn)
        by (apply (pix_obj_with_cmap (rt_live RT Σ1) (rt_live RT Σ4) _ mc pixd vd _ _ cvn POBJD1 SUB14); try reflexivity;
            [ unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PDC4
            | cbn [p_cmap p_data];
              exact (cmap_part_carry (rt_live RT Σ4) (rt_live RT Σ4) _ mc cmapd cvn pixd (p_data vd) (rsize vd) _ (or_intror (conj CO CDEP)) AGC (fun e He => He) CMF2 DDSZ) ]) end.
    regen_pxc PXC POBJ AGF PIN D8.
    lazymatch goal with |- cps _ (ASTA RT Σ4 _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      assert (POBJSc : pix_obj (rt_live RT Σ4) mc pixs vs cvs)
        by (unfold hid in POBJ; apply (pix_obj_mono (rt_live RT Σ) (rt_live RT Σ4) mc pixs vs cvs SUBL4); apply (pix_obj_agree_cm (rt_live RT Σ) PF0 m mc pixs vs cvs POBJ AGF);
            [intros NZ a Ha; right; right; left; exists (p_cmap vs), 24; split; [exact (CMIN NZ)| exact Ha] | unfold pix_cells; rewrite D8; exact PXC]) end.
    lazymatch goal with P : rw_cells asegs _ (usp + -192) _ |- _ => pose proof P as PUSH; split_at PUSH 1%nat PUSH2; clear PUSH2 end.
    eapply cps_seq.
    { eapply ROPS with (lo := lo) (pixd := pixd) (pixs := pixs)
        (vd := mkPixv (p_w vd) (p_h vd) (p_d vd) sppd (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) cmapd (p_data vd))
        (vs := vs) (cvd := cvn) (cvs := cvs) (dx := 0) (dy := 0) (dw := p_w vs - 64) (dh := p_h vs - 64) (sx := 32) (sy := 32); rt_side idtac;
        lazymatch goal with
        | |- pix_obj _ _ pixd _ _ => exact POBJDc
        | |- pix_obj _ _ pixs _ _ => exact POBJSc
        | |- rw_cells _ _ _ _ => exact PUSH
        | |- pixd <> pixs => exact PDS
        | |- p_d vs = 1 => exact D8
        | |- p_d _ = 1 => exact EDd
        | |- p_data vs <> 0 => exact VDATA
        | |- p_data _ <> 0 => exact VDD
        | |- p_data _ <> p_data vs => exact DNE2
        | |- _ mod 32 = 0 => reflexivity
        | |- rect_in 0 0 _ _ _ _ => unfold rect_in; cbn [p_w p_h]; rewrite EWd, EHd; clear - NW; unfold hid in NW; lia
        | |- rect_in 32 32 _ _ _ _ => unfold rect_in; clear - NW; unfold hid in NW; lia
        | |- lenv _ _ _ _ _ _ => lenv_tac
        | |- lres _ _ _ _ _ => lres_tac
        | |- ?g => idtac "LEFTOVER:" g
        end. }
    after_call RT AF. clear POBJDc POBJSc PUSH.
    lazymatch type of AGC with agree_on _ _ ?mm => lazymatch goal with AG : agree_on (fun _ => _ /\ _) mm _ |- _ =>
      agf_call AGC AG ltac:(fun Hx => destruct Hx as (_ & Hx); unfold hid in CMW;
                                      split; [right; right; left; exists cmapd, 24; split; [lazymatch goal with HL : rt_live RT _ = rt_live RT Σ4 |- _ => rewrite HL end; exact CI| lia]
                                             | cbn [outside p_data]; unfold rsize in *; cbn [p_wpl p_h] in *; clear - Hx CMW; split; [lia| exact I]]) end end.
    rop_post RT AF GP Σ usp NCD.
    regen_pxc PXC POBJ AGF PIN D8.
    walk_to AF MST [(usp - 336, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x96cac].
    try (lazymatch goal with P : rw_cells asegs _ (usp + -192) _, ST' : stk asegs _ lo (usp + -192) |- _ => release_frame P ST' (usp + -176) end).
    try clear PXC. epilogue_prep RT.
    awalk [0x96d10].
    lazymatch type of AGC with agree_on _ _ ?mm => lazymatch goal with MUx : munch _ mm _ |- _ =>
      agf_munch AGC MUx ltac:(fun Hx => destruct Hx as (_ & Hx); cbn [outside]; unfold hid in CMW; clear - Hx CMW LOW LOR FR64;
                                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end end.
    hide AGC.
    clear FSH FRM. try clear GSEV. clear_acc.
    frame_release_w RT AF GP MST Σ fr 1%nat 128 PF0 AGF PFS usp lo 0x96d18
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                        destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact Hx)
        ltac:(fun fl FLN => idtac).
    unfold hid in AGC.
    lazymatch goal with MUx : munch [(?fl, _)] _ _, FA : ?fl < cmapd \/ cmapd + 24 <= ?fl |- _ =>
      agf_munch AGC MUx ltac:(fun Hx => destruct Hx as (_ & Hx); cbn [outside]; clear - Hx FA; split; [lia| exact I]) end.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 176, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -176) |- _ => release_frame FR ST' usp end.
    lazymatch type of AGC with agree_on _ _ ?mm => lazymatch goal with MUx : munch _ mm _ |- _ =>
      agf_munch AGC MUx ltac:(fun Hx => destruct Hx as (_ & Hx); cbn [outside]; unfold hid in CMW; clear - Hx CMW LOW LOR;
                                        repeat split; try exact I; lia) end end.
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    exists pixd, (mkPixv (p_w vd) (p_h vd) (p_d vd) sppd (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) cmapd (p_data vd)), cvn.
    split; [| split; [| split; [alg_tac| split; [alg_tac|]]]].
    2:{ lazymatch goal with |- new_pix1_live RT _ ?Sf _ _ _ =>
          assert (ELV : rt_live RT Sf = (c_arr cvn, 4 * c_nalloc cvn) :: (cmapd, 24) :: (p_data vd, 4 * (p_wpl vd * p_h vd)) :: (pixd, 64) :: rt_live RT Σ)
            by (unfold rsize in *; rewrite ?PDNZ in *; alg_tac) end.
        assert (FRESH : forall e, In e (rt_live RT Σ) -> fst e <> pixd /\ fst e <> p_data vd).
        { intros [q k] He. cbn [fst]. pose proof (LVP q k He) as KP.
          assert (PQ : PF0 q) by (right; right; left; exists q, k; split; [exact He| lia]).
          pose proof (NCP q PQ) as N1. pose proof (NCD q PQ) as N2. unfold rsize in *. clear - N1 N2 DDSZ. lia. }
        assert (FRC : cmapd <> 0 -> forall e, In e (rt_live RT Σ) -> fst e <> cmapd /\ fst e <> c_arr cvn).
        { intros _ [q k] He. cbn [fst]. pose proof (LVP q k He) as KP.
          lazymatch goal with A2 : ART RT ?Sf ?mf |- _ => lazymatch type of ELV with rt_live RT Sf = _ =>
            pose proof (af_live_disj RT AF Sf mf cmapd 24 q k [(c_arr cvn, 4 * c_nalloc cvn)] ((p_data vd, 4 * (p_wpl vd * p_h vd)) :: (pixd, 64) :: rt_live RT Σ) A2 ELV ltac:(right; right; right; exact He)) as Q1;
            pose proof (af_live_disj RT AF Sf mf (c_arr cvn) (4 * c_nalloc cvn) q k [] ((cmapd, 24) :: (p_data vd, 4 * (p_wpl vd * p_h vd)) :: (pixd, 64) :: rt_live RT Σ) A2 ELV ltac:(right; right; right; exact He)) as Q2 end end.
          clear - Q1 Q2 KP AN. split; lia. }
        unfold new_pix1_live. rewrite ELV.
        split; [intros E0; exfalso; clear - E0 PD0; lia|].
        split; [intros _;
                pose proof (live_destroy_tmpl (rt_live RT Σ) pixd (p_data vd) (4 * (p_wpl vd * p_h vd)) cmapd (c_arr cvn) (4 * c_nalloc cvn)
                              (mkPixv (p_w vd) (p_h vd) (p_d vd) sppd (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) cmapd (p_data vd)) cvn) as LD;
                replace (cmapd =? 0) with false in LD by (symmetry; apply Z.eqb_neq; exact CNZ); cbv iota in LD; apply LD;
                [ reflexivity | reflexivity | intros _; reflexivity | exact VDD | exact DDNE
                | intros NZ; destruct (CMF2 NZ) as (_ & Q1 & Q2 & Q3 & Q4); unfold rsize in *; clear - Q1 Q2 Q3 Q4 A0 AN ANE DDSZ; repeat split; lia
                | exact FRESH | exact FRC ]|].
        split; [intros p n [E|[E|[E|[E|HI]]]];
                [injection E as <- <-; exact AN| injection E as <- <-; lia| injection E as <- <-; unfold rsize in DDSZ; exact DDSZ| injection E as <- <-; lia| exact (LVP p n HI)]
               | cbn [length]; lia]. }
    2:{ credit_fin RT. }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split.
    { split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption].
      repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
    split.
    { repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. intros a Ha Ho; exact (AGF a Ha). }
    right. split.
    { lazymatch goal with |- pix_obj (rt_live RT ?Sf) ?mf _ _ _ =>
        assert (SUB4f : forall e, In e (rt_live RT Σ4) -> In e (rt_live RT Sf))
          by (intros e He; repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H end; exact He);
        apply (pix_obj_with_cmap (rt_live RT Σ1) (rt_live RT Sf) _ mf pixd vd _ _ cvn POBJD1 (fun e He => SUB4f e (SUB14 e He))); try reflexivity;
        [ unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PDC4
        | cbn [p_cmap p_data];
          exact (cmap_part_carry (rt_live RT Σ4) (rt_live RT Sf) _ mf cmapd cvn pixd (p_data vd) (rsize vd) _ (or_intror (conj CO CDEP)) AGC SUB4f CMF2 DDSZ) ] end. }
    cbn [p_w p_h p_d p_data p_cmap]. repeat split; first [assumption | lia].
Qed.
End RBC.

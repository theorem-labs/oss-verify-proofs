(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *) (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_gmax_defs Gm_iface Gm_border_defs Gm_border_kit LeptB_guard LeptB_guard2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tlia ::= sf_clear_big;
              first [ sf_unhide; unpark_all; zify_prune_sub; Zify.zify; xlia zchecker
                    | Zify.zify; xlia zchecker
                    | sf_unhide; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
Ltac word_arg_eq NW :=
  let NW' := fresh "NW" in pose proof NW as NW'; unfold hid in NW';
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - NW'; lia) end;
  f_equal; clear - NW'; lia.
(* [comment removed for export] *)
Local Ltac rop_uni ROPU xlo xpixd xv3 xdx xdy xdw xdh xop POBJDc HOP EDd VDD EWd EHd NW ::=
  eapply cps_seq;
  [ eapply ROPU with (lo := xlo) (pixd := xpixd) (vd := xv3) (cvd := mkCmapv 0 0 0 0) (dx := xdx) (dy := xdy) (dw := xdw) (dh := xdh) (op := xop); rt_side idtac;
      lazymatch goal with
      | |- pix_obj _ _ xpixd _ _ => exact POBJDc
      | |- _ \/ _ => exact HOP
      | |- p_d _ = 8 => exact EDd
      | |- p_data _ <> 0 => exact VDD
      | |- rect_in _ _ _ _ _ _ => unfold rect_in; cbn [p_w p_h]; rewrite EWd, EHd; clear - NW; unfold hid in NW; lia
      | |- lenv _ _ _ _ _ _ => lenv_tac
      | |- lres _ _ _ _ _ => lres_tac
      | |- @eq word _ _ => word_arg_eq NW
      end
  | ].

Local Ltac guard_fix ::= try sx32_fix; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end; swrap_fix; po_fix; al_fix; try mulh_fix.

Section ABC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RE : returnError_cps RT e_returnErrorPtr.
Hypothesis CRE : pixCreate_cps RT.
Hypothesis CRES : pixCopyResolution_cps RT.
Hypothesis CCM : pixCopyColormap_cps RT.
Hypothesis ROPU : pixRasterop_uni_cps RT.
Hypothesis ROPS : pixRasterop_src_cps RT.

Lemma addborder_c0 : addborder_case RT 0.
Proof using AF GP RE CRE CRES CCM ROPU ROPS.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pixs vs cvs val
    FDO MST -> -> -> -> -> -> -> HV POBJ D8 NOCM VDATA ENV RES AL.
  unfold lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold BORDER_COST, RASTER_COST in *.
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & _ & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixAddBorderGeneral, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
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
  assert (NW : hid (0 < p_w vs /\ p_w vs <= 20000 /\ 0 < p_h vs /\ p_h vs <= 20000))
    by (destruct POBJ as (_ & _ & (_ & A & B & _) & _); unfold hid; clear - A B; lia).
  chunk_facts RT AF GP pixs 64.
  chunk_facts RT AF GP (p_data vs) (rsize vs).
  unfold pix_cells in PXC.
  hide POBJ.
  carve_frame 192%nat ST.
  walk_to AF MST [(usp - 192, usp)] [e_stack_malloc 1%nat].

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
  walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x96d04].

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
  (* [comment removed for export] *)
  assert (NUMS : (0 < p_w vs <= 20000 /\ 0 < p_h vs <= 20000) /\ p_wpl vs = (p_w vs * 8 + 31) / 32 /\ 0 < 4 * (p_wpl vs * p_h vs) <= 67108864).
  { pose proof POBJ as PO. unfold hid in PO. destruct PO as (_ & _ & (_ & A & B & C & D) & _). rewrite D8 in C. clear - A B C D. tauto. }
  destruct NUMS as ((HWR & HHR) & EWPL & HSZ).
  walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCreate].

  (* [comment removed for export] *)
  sx32_fix. rewrite ?(unsigned_lit (p_w vs)) by (clear - HWR; lia). rewrite ?(unsigned_lit (p_h vs)) by (clear - HHR; lia).
  swrap32_fix. rewrite ?(Z.mod_small (p_w vs + 4)) by (clear - HWR; lia). rewrite ?(Z.mod_small (p_h vs + 2)) by (clear - HHR; lia).
  swrap32_fix.
  std_at_call RT AF PFS NFA LOR FR64.
  eapply cps_seq.
  { eapply CRE with (lo := lo) (w := p_w vs + 4 + 8) (h := p_h vs + 2 + 8) (d := 8); rt_side idtac.
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
    walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr].
    std_at_call RT AF PFS NFA LOR FR64.
    eapply cps_seq.
    { eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    epilogue_prep RT.
    walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x97044].
    clear FSH FRM. try clear GSEV. clear_acc.
    frame_release_w RT AF GP MST Σ fr 1%nat 128 PF0 AGF PFS usp lo 0x9704c
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                      destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact Hx)
      ltac:(fun fl FLN => idtac).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 192, usp)] (@nil Z).
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. exists 0, (mkPixv 0 0 0 0 0 0 0 0 0 0 0).
    split; [| split; [unfold new_pix8_live; change (0 =? 0) with true; cbv iota; alg_tac | split; [alg_tac| split; [alg_tac|]]]].
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

  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  unfold pix_cells in PDC.
  walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCopyResolution].
  std_at_call RT AF PFS NFA LOR FR64.
  regen_pxc PXC POBJ AGF PIN D8.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (POBJS1 : pix_obj (rt_live RT Σ1) mc pixs vs cvs)
      by (unfold hid in POBJ; apply (pix_obj_nocmap (rt_live RT Σ) (rt_live RT Σ1) m mc pixs vs cvs cvs POBJ NOCM SUBL); unfold pix_cells; rewrite D8; exact PXC);
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
  walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCopyColormap].
  std_at_call RT AF PFS NFA LOR FR64.
  regen_pxc PXC POBJ AGF PIN D8.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (POBJS2 : pix_obj (rt_live RT Σ2) mc pixs vs cvs)
      by (unfold hid in POBJ; apply (pix_obj_nocmap (rt_live RT Σ) (rt_live RT Σ2) m mc pixs vs cvs cvs POBJ NOCM SUBL2); unfold pix_cells; rewrite D8; exact PXC);
    assert (POBJD2 : pix_obj (rt_live RT Σ2) mc pixd
                       (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) (p_cmap vd) (p_data vd)) (mkCmapv 0 0 0 0))
      by (apply (pix_obj_nocmap_fields (rt_live RT Σ1) (rt_live RT Σ2) _ mc pixd vd _ _ _ POBJD1 VDC ltac:(intros e He; rewrite LV2; exact He));
          try reflexivity; [exact VDC | unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PDC2]) end.
  eapply cps_seq.
  { eapply CCM with (lo := lo) (pixd := pixd) (pixs := pixs)
      (vd := mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) (p_cmap vd) (p_data vd))
      (vs := vs) (cvd := mkCmapv 0 0 0 0) (cvs := cvs) (ras := @nil Z); rt_side idtac;
      lazymatch goal with
      | |- pix_obj _ _ pixd _ _ => exact POBJD2
      | |- pix_obj _ _ pixs _ _ => exact POBJS2
      | |- pixd <> pixs => exact PDS
      | |- p_d _ = p_d vs => cbn [p_d]; rewrite D8; exact EDd
      | |- p_cmap _ = 0 => exact VDC
      | |- p_cmap vs <> 0 -> _ => intros NZ; contradiction
      | |- lenv _ _ _ _ _ _ => lenv_tac
      | |- lres _ _ _ _ _ => lres_tac
      end. }
  after_call RT AF.
  lazymatch goal with H : p_cmap vs = 0 -> ?c = 0 |- _ => pose proof (H NOCM) as CM0; clear H; subst c end.
  lazymatch goal with H : rt_live RT ?S3 = (if 0 =? 0 then _ else _) |- _ => rename S3 into Σ3; rename H into LV3; change (0 =? 0) with true in LV3; cbv iota in LV3 end.
  assert (SUBL3 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; exact (SUBL2 e He)).
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact SUBL2| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PDC3 end.
  unfold pix_cells in PDC3. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PDC3.
  clear SUBL SUBL2 POBJS1 POBJS2 POBJD2.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x96dbc].
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    eapply (evt_cut segs (fun ms' => exists (op : Z) (u0 u1 u2 : word), (op = 0 \/ op = 15) /\
              ms' = MS (@bvmap_set 5 word (Z_to_bv 5 26) (Z_to_bv 64 op) (@bvmap_set 5 word (Z_to_bv 5 10) u0
                          (@bvmap_set 5 word (Z_to_bv 5 11) u1 (@bvmap_set 5 word (Z_to_bv 5 12) u2 R)))) F (Z_to_bv 64 0x96ecc) fc rv mm ro)) end.
  { destruct HV as [V0|V255]; subst val.
    - awalk [0x96ecc]. apply evt_done. exists 0. do 3 eexists. split; [left; reflexivity|]. norm_regset. reflexivity.
    - awalk [0x96ecc]. apply evt_done. exists 15. do 3 eexists. split; [right; reflexivity|]. norm_regset. reflexivity. }
  intros ms (op & ju0 & ju1 & ju2 & HOP & E). subst ms. norm_regset.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  awalk [e_pixRasterop].
  rop_pre RT AF PFS NFA LOR FR64.
  mk_pobjd POBJDc RT Σ1 pixd vd (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd)) POBJD1 VDC PDC3.
  rop_uni ROPU lo pixd (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd))
        0 0 4 (p_h vs + 10) op POBJDc HOP EDd VDD EWd EHd NW.
  after_call RT AF. clear POBJDc.
  rop_post RT AF GP Σ usp NCD.
  walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixRasterop].
  rop_pre RT AF PFS NFA LOR FR64.
  mk_pobjd POBJDc RT Σ1 pixd vd (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd)) POBJD1 VDC PDC3.
  rop_uni ROPU lo pixd (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd))
        (p_w vs + 4) 0 8 (p_h vs + 10) op POBJDc HOP EDd VDD EWd EHd NW.
  after_call RT AF. clear POBJDc.
  rop_post RT AF GP Σ usp NCD.
  walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixRasterop].
  rop_pre RT AF PFS NFA LOR FR64.
  mk_pobjd POBJDc RT Σ1 pixd vd (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd)) POBJD1 VDC PDC3.
  rop_uni ROPU lo pixd (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd))
        0 0 (p_w vs + 12) 2 op POBJDc HOP EDd VDD EWd EHd NW.
  after_call RT AF. clear POBJDc.
  rop_post RT AF GP Σ usp NCD.
  walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixRasterop].
  rop_pre RT AF PFS NFA LOR FR64.
  mk_pobjd POBJDc RT Σ1 pixd vd (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd)) POBJD1 VDC PDC3.
  rop_uni ROPU lo pixd (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd))
        0 (p_h vs + 2) (p_w vs + 12) 8 op POBJDc HOP EDd VDD EWd EHd NW.
  after_call RT AF. clear POBJDc.
  rop_post RT AF GP Σ usp NCD.

  (* [comment removed for export] *)
  walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixRasterop].
  sx32_fix.
  rop_pre RT AF PFS NFA LOR FR64.
  mk_pobjd POBJDc RT Σ1 pixd vd (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd)) POBJD1 VDC PDC3.
  regen_pxc PXC POBJ AGF PIN D8.
  lazymatch goal with SUB : (forall e, In e (rt_live RT Σ) -> In e (rt_live RT ?Sc)) |- cps _ (ASTA RT ?Sc _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (POBJSc : pix_obj (rt_live RT Sc) mc pixs vs cvs)
      by (unfold hid in POBJ; apply (pix_obj_nocmap (rt_live RT Σ) (rt_live RT Sc) m mc pixs vs cvs cvs POBJ NOCM SUB); unfold pix_cells; rewrite D8; exact PXC) end.
  lazymatch goal with P : rw_cells asegs _ (usp + -208) _ |- _ => pose proof P as PUSH; split_at PUSH 1%nat PUSH2; clear PUSH2 end.
  eapply cps_seq.
  { eapply ROPS with (lo := lo) (pixd := pixd) (pixs := pixs)
      (vd := mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd))
      (vs := vs) (cvd := mkCmapv 0 0 0 0) (cvs := cvs) (dx := 4) (dy := 2) (dw := p_w vs) (dh := p_h vs) (sx := 0) (sy := 0); rt_side idtac;
      lazymatch goal with
      | |- pix_obj _ _ pixd _ _ => exact POBJDc
      | |- pix_obj _ _ pixs _ _ => exact POBJSc
      | |- rw_cells _ _ _ _ => exact PUSH
      | |- pixd <> pixs => exact PDS
      | |- p_d vs = 8 => exact D8
      | |- p_d _ = 8 => exact EDd
      | |- p_data vs <> 0 => exact VDATA
      | |- p_data _ <> 0 => exact VDD
      | |- p_data _ <> p_data vs => exact DNE2
      | |- rect_in 4 2 _ _ _ _ => unfold rect_in; cbn [p_w p_h]; rewrite EWd, EHd; clear - NW; unfold hid in NW; lia
      | |- rect_in 0 0 _ _ _ _ => unfold rect_in; clear - NW; unfold hid in NW; lia
      | |- lenv _ _ _ _ _ _ => lenv_tac
      | |- lres _ _ _ _ _ => lres_tac
      | |- @eq word _ _ => word_arg_eq NW
      end. }
  after_call RT AF. clear POBJDc POBJSc PUSH.
  rop_post RT AF GP Σ usp NCD.

  (* [comment removed for export] *)
  walk_to AF MST [(usp - 352, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x96fe0].
  (* [comment removed for export] *)
  try (lazymatch goal with P : rw_cells asegs _ (usp + -208) _, ST' : stk asegs _ lo (usp + -208) |- _ => release_frame P ST' (usp + -192) end).
  try clear PXC. epilogue_prep RT.
  awalk [0x97044].
  clear FSH FRM. try clear GSEV. clear_acc.
  frame_release_w RT AF GP MST Σ fr 1%nat 128 PF0 AGF PFS usp lo 0x9704c
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                      destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact Hx)
      ltac:(fun fl FLN => idtac).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 192, usp)] (@nil Z).
  cps_stop.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  exists pixd, (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) 0 (p_data vd)).
  split; [| split; [unfold new_pix8_live, rsize; cbn [p_wpl p_h p_data]; rewrite PDNZ; unfold rsize in *; alg_tac | split; [alg_tac| split; [alg_tac|]]]].
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
      try reflexivity; unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PDC3. }
  cbn [p_w p_h p_d p_data p_cmap]. repeat split; first [assumption | lia].
Qed.
End ABC.

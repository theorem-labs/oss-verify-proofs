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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs D_libiface
  Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf LeptC_leaf Lept_objkit Lept_fuzzkit Ed_iface Ed_fuzz_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section FUZZ.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis DESER : pixDeserialize_cps RT.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis MEASURE : pixMeasureEdgeSmoothness_cps RT.

Lemma fuzz_c16 : fuzz_case RT 16.
Proof using AF RC GP DESER DESTROY MEASURE.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST -> -> -> RATOP DPOS BSL BYTES OWN FR0 LVP LVB CRB S0INV LIBm SSP ART0 MI ST LOW LOR SPT SPA SPB AL.
  destruct LIBm as ((LSEV & LALLOC & LDEALLOC) & (h0 & LHAND)).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, D_libiface.e_fuzz, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold D_libiface.FUZZ_STACK, D_libiface.FUZZ_COST, D_libiface.FUZZ_LIVE, LSTK, STDERR_STACK, RASTER_COST in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside D_libiface.LIB_FP a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  carve_frame 112%nat ST.
  walk_to AF MST [(usp - 112, usp)] [e_stack_malloc 1%nat; e_pixDeserialize; e_pixMeasureEdgeSmoothness; e_pixDestroy].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  destruct (Z_lt_ge_dec (Z.of_nat (length bs)) 3) as [SZ|SZ].
  + (* [comment removed for export] *)
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                 [e_stack_malloc 1%nat; e_pixDeserialize; e_pixMeasureEdgeSmoothness; e_pixDestroy; 0xe7264].
    frame_release_raw RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xe726c
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact (proj1 Hx)) LSEV LALLOC LDEALLOC LHAND.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 112, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end.   (* [comment removed for export] *)
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [assumption| split; assumption]|].
    split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
    unfold D_libiface.LIB_A.
    split; [split; [assumption| split; assumption]| exists h0; assumption].
  + (* [comment removed for export] *)
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (1868864, 1868872)]
                 [e_stack_malloc 1%nat; e_pixDeserialize; e_pixMeasureEdgeSmoothness; e_pixDestroy; 0xe7264].
    destruct OWN as [(p0 & n0 & OIN & OLO & OHI & DAL)| ->]; [| cbn [length] in SZ; lia].
    assert (LH : LIBH m2)
      by (unfold LIBH, LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler, e_devnull; split; [split; [|split]|]; assumption).
    clear LSEV LALLOC LDEALLOC LHAND.
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; static_tac | exact I]]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO];
                        unfold D_libiface.LIB_FP, g_stderr_handler in HxO; cbn [outside] in HxO; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
    pose proof DESER as DS. unfold pixDeserialize_cps in DS.
    eapply cps_seq.
    { eapply DS with (lo := lo) (dp := d) (n := Z.of_nat (length bs)) (ras := [RA_TOP]); rt_side idtac.
      - right. split; [exact DAL|]. exists p0, n0. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. split; [exact OIN | lia].
      - unfold uctx. (rewrite !unsigned_lit by lia). unfold parked in S0INV.
        (apply chain_ok_push with (fp1 := bv_unsigned s0)).
        + lia.
        + (clear - SPA; Z.div_mod_to_equations; lia).
        + (unfold USTACK_TOP; lia).
        + (unfold RA_TOP; lia).
        + (apply bv_unsigned_in_range).
        + (rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned).
          (lazymatch type of FRrec2 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end). (exact FRrec2).
        + (cbn [chain_ok]; unfold link_invalid; lia).
      - (exact tr_deser).
      - lenv_tac.
      - unfold RASTER_COST. lres_tac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with H : ?p = 0 \/ _ |- _ => rename H into POBJ; set (pix := p) in * end.
    lazymatch goal with H : pix = 0 -> rt_live RT _ = _ |- _ => rename H into LVZ end.
    lazymatch goal with H : pix <> 0 -> live_destroy _ _ _ _ = _ |- _ => rename H into LVD end.
    destruct (Z.eq_dec pix 0) as [PZ|PNZ].
    * (* [comment removed for export] *)
      clear POBJ LVD. pose proof (LVZ PZ) as LVE. clear LVZ. rewrite PZ in *.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixMeasureEdgeSmoothness; e_pixDestroy; 0xe7264].
      fz_frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xe726c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx)).
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 112, usp)] (@nil Z).
      lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end.   (* [comment removed for export] *)
      cps_stop.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      split; [| unfold RASTER_COST in *; alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [assumption| split; assumption]|].
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      lazymatch goal with LHx : LIBH ?mm |- D_libiface.LIB_A ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end.
    * (* [comment removed for export] *)
      destruct POBJ as [PZ|(POBJ & VDATA)]; [contradiction|]. clear LVZ. pose proof (LVD PNZ) as LVE. clear LVD.
      lazymatch type of POBJ with pix_obj _ _ _ ?vv ?cc => set (v := vv) in *; set (cv := cc) in * end.
      pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & HDROK & _).
      chunk_facts RT AF GP pix 64.
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (NCP : forall a, PF a -> a < pix \/ pix + 64 <= a)
          by (intros a [Ha _]; apply (inner_chunk_apart RT AF S mm pix 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A PIN);
              [ intros e He; apply (live_destroy_in pix v cv); rewrite LVE;
                repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He
              | intros e He; rewrite FR0 in He; destruct He
              | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
              | exact Ha ]) end.
      lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
        assert (FRSh : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ)
          by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
      fframe_chunk RT AF fr 1%nat 128 pix 64.
      clear PXC. hide POBJ.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixMeasureEdgeSmoothness; e_pixDestroy; 0xe7264].
      unfold hid in POBJ.
      (* [comment removed for export] *)
      pose proof FRM as FRA. split_at FRA 5%nat FRT2. split_last_CB FRT2 [24; 4; 12; 4; 12; 4; 20]%nat.
      split_at FRT2 1%nat CF1. split_at CF1 1%nat CG1. split_at CG1 1%nat CF2. split_at CF2 1%nat CG2. split_at CG2 1%nat CF3. split_at CF3 1%nat CG3.
      clear FRM.
      destruct (cb4_c4 _ _ _ CF1) as [o1 CE1]. destruct (cb4_c4 _ _ _ CF2) as [o2 CE2]. destruct (cb4_c4 _ _ _ CF3) as [o3 CE3]. clear CF1 CF2 CF3.
      pose proof FSH as SHc. split_at SHc 8%nat SB1. clear SHc. split_at SB1 1%nat SB1r. split_at SB1r 1%nat SB2. clear SB1r. split_at SB2 1%nat SB2r.
      split_at SB2r 1%nat SB3. clear SB2r. split_at SB3 1%nat SB3r. clear SB3r.
      pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
      destruct HDROK as (HDd & HW & HH & HWPL & HRS).
      pose proof (measure_cost_bound (p_w v) (p_h v) HW HH) as MCB.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      pose proof MEASURE as MSR. unfold pixMeasureEdgeSmoothness_cps in MSR.
      eapply cps_seq.
      { eapply MSR with (lo := lo) (pix := pix) (p1 := fr + 64) (p2 := fr + 80) (p3 := fr + 96) (v := v) (cv := cv) (o1 := o1) (o2 := o2) (o3 := o3)
                        (ras := [RA_TOP]); rt_side idtac.
        { lazymatch goal with A : ART RT ?Sx ?mm, MUx : munch ?W ?mm ?mc |- pix_obj _ ?mc _ _ _ =>
            eapply (pix_obj_keep _ mm mc pix v cv); [| exact POBJ];
            intros bb kk Hin aa Ha; apply MUx;
            apply (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk (bv_unsigned aa) A);
            [ rewrite FRSh; left; reflexivity
            | unfold STACK_WIN; repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; lia
            | exact Hin | exact Ha ] end. }
        all: lazymatch goal with
             | |- optrF _ _ _ ?p 4 =>
                 unfold optrF, own_frame, parked in *; split;
                 [ exists fr, 1%nat; rewrite FRSh; change (fs_size 1) with 128;
                   split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                   split; [lia|]; split; [lia|]; change (ushadow 4) with [Z_to_bv 8 4];
                   first [ replace (shad p) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SB1 as [[_ B] _]; exact B
                         | replace (shad p) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SB2 as [[_ B] _]; exact B
                         | replace (shad p) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SB3 as [[_ B] _]; exact B ]
                 | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
             | |- uctx _ _ _ _ =>
                 unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                 apply chain_ok_push with (fp1 := bv_unsigned s0);
                   [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                   | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec3
                   | cbn [chain_ok]; unfold link_invalid; lia ]
             | |- _ = [RA_TOP] => reflexivity
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ =>
                 unfold lres, FRAMES_MAX, LIVE_MAX, RASTER_COST in *; rewrite FRSh, FR0; cbn [length];
                 repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H in * end;
                 repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                 split; [lia| split; [lia| split; [lia| assumption]]]
             | |- ?g => idtac "LEFT:" g
             end.
        all: lazymatch goal with |- ?g => idtac "LEFT2:" g end. }
      idtac "MEASURE_APPLIED".
      (* [comment removed for export] *)
      lazymatch goal with A : ART RT ?Sx ?mm, MUx : munch ?W ?mm ?mc |- _ =>
        assert (KL : keeps_live (rt_live RT Sx) mm mc)
          by (intros bb kk Hin aa Ha; apply MUx;
              apply (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk (bv_unsigned aa) A);
              [ rewrite FRSh; left; reflexivity
              | unfold STACK_WIN; repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; lia
              | exact Hin | exact Ha ]);
        pose proof (pix_obj_keep _ _ mc pix v cv KL POBJ) as POBJ1 end.
      after_call RT AF.
      (* [comment removed for export] *)
      lazymatch goal with AGx : agree_on _ ?mc ?md, A : ART RT ?Sy ?md |- _ =>
        lazymatch type of POBJ1 with pix_obj (rt_live RT ?Sx) mc _ _ _ =>
          assert (KL2 : keeps_live (rt_live RT Sx) mc md)
            by (intros bb kk Hin aa Ha; apply AGx; split;
                [ right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; exact Hin | exact Ha]
                | lazymatch goal with A1 : ART RT Sx mc |- _ =>
                    pose proof (live_outside_frame1 RT AF Sx mc fr usp (usp - 112) bb kk (bv_unsigned aa) A1
                                  ltac:(rewrite FRSh; left; reflexivity)
                                  ltac:(unfold STACK_WIN; repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; lia) Hin Ha) as OW;
                    cbn [outside] in OW |- *; repeat split; try exact I; lia end ]);
          pose proof (pix_obj_keep _ _ md pix v cv KL2 POBJ1) as POBJ2 end end.
      clear KL KL2 POBJ POBJ1.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                                       [ intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in * end;
                                         first [ exact He | apply (live_destroy_in pix v cv); rewrite LVE; exact He ]
                                       | solve [frames_sub_tac] | lia ]
                                     | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; repeat split; try exact I; lia]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixMeasureEdgeSmoothness; e_pixDestroy; 0xe7264].
      (* [comment removed for export] *)
      split_at FRA 4%nat PPC2.   (* [comment removed for export] *)
      pose proof FSH as SHC. split_at SHC 4%nat SHC2. split_at SHC2 1%nat SHC3. clear SHC SHC3.
      pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec4. clear FRrec.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; pose proof (NCP _ Hx); unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
      eapply cps_seq.
      { eapply DY with (lo := lo) (pp := fr + 32) (pix := pix) (v := v) (cv := cv) (ras := [RA_TOP]); rt_side idtac.
        all: lazymatch goal with
             | |- optrL _ _ _ _ _ _ =>
                 unfold optrL, parked in *; split;
                 [ right; exists fr, 1%nat; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; change (fs_size 1) with 128;
                   split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                   split; [lia|]; split; [lia|];
                   replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                   destruct SHC2 as [[_ B] _]; exact B
                 | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
             | |- rw_cells _ _ _ [C8 _] => exact PPC2
             | |- pix_obj _ _ _ _ _ => first [exact POBJ2 | repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H in * end; exact POBJ2]
             | |- uctx _ _ _ _ =>
                 unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                 apply chain_ok_push with (fp1 := bv_unsigned s0);
                   [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                   | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec4
                   | cbn [chain_ok]; unfold link_invalid; lia ]
             | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; exact tr_destroy
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ =>
                 unfold lres, FRAMES_MAX, LIVE_MAX, RASTER_COST in *;
                 repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H in * end; rewrite ?FR0; cbn [length];
                 repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H in * end;
                 repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H in * end;
                 split; [cbn [length] in *; lia| split; [lia| split; [lia| assumption]]]
             | |- ?g => idtac "LEFT:" g
             end.
        all: lazymatch goal with |- ?g => idtac "LEFT2:" g end. }
      idtac "DESTROY_APPLIED".
      clear SB1 SB2 SB3. try clear SHC2. try clear PPC2.
      after_call RT AF.
      lazymatch goal with H : rt_live RT ?Sn = live_destroy pix v cv (rt_live RT ?So) |- _ =>
        repeat match goal with H2 : rt_live RT So = _ |- _ => rewrite H2 in H end; rewrite LVE in H end.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                      cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
      clear POBJ2 IN NCP.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                   [e_stack_malloc 1%nat; e_pixDeserialize; e_pixMeasureEdgeSmoothness; e_pixDestroy; 0xe7264].
      fz_frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xe726c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx)).
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 112, usp)] (@nil Z).
      lazymatch goal with ST' : stk asegs _ lo (usp + -112) |- _ => release_frame FR ST' usp end.   (* [comment removed for export] *)
      cps_stop.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
      split; [| unfold RASTER_COST in *; alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [assumption| split; assumption]|].
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      lazymatch goal with LHx : LIBH ?mm |- D_libiface.LIB_A ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end.
Qed.
End FUZZ.

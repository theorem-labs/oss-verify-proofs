(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit LeptL_gmax_loop Lept_gmax_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section GMAXC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis ZERO : pixZero_cps RT.

Lemma gmax_c0 : gmax_case RT 0.
Proof using AF GP ZERO.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix pmax v cv x
    FDO MST -> -> -> POBJ VDATA D8 OPM PMC ENV RES AL.
  unfold lpost, lenv, keeps, keepsL, lres, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). destruct OPM as (OWNF & PM0 & PM8 & PMSH & PMSEG).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixGetMaxColorIndex, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof ZERO as ZR. unfold pixZero_cps in ZR.
  (* [comment removed for export] *)
  set (PF0 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pmax, pmax + 4)] a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (OWN : accok (rt_live RT Σ) (rt_frames RT Σ) m pmax 4) by (right; exact OWNF).
  assert (PMCL : forall zz, pmax <= zz < pmax + 4 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp zz)
    by (intros zz Hzz; exact (accok_aclient _ _ m usp pmax 4 zz OWN Hzz)).
  assert (PMFF : forall zz, pmax <= zz < pmax + 4 -> in_fframe (rt_frames RT Σ) zz)
    by (intros zz Hzz; destruct OWNF as (f & k & Hin & H1 & H2 & _); exists f, k; split; [exact Hin| lia]).
  assert (PMLO : pmax + 4 <= lo).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _).
    pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN in R. lia. }
  assert (PMP : pmax + 4 <= pix \/ pix + 64 <= pmax).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). specialize (R pix 64 PIN). lia. }
  assert (PMD : pmax + 4 <= p_data v \/ p_data v + rsize v <= pmax).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). specialize (R (p_data v) (rsize v) DIN). lia. }
  chunk_facts RT AF GP pix 64.
  chunk_facts RT AF GP (p_data v) (rsize v).
  unfold pix_cells in PXC.
  pose proof (af_acc_live RT AF Σ m (p_data v) (rsize v) ART0 DIN) as (WRD & _).
  unfold rsize in *. apply wr_at_rw_CB in WRD; [| lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL.
  assert (DBND : 1 <= p_d v <= 32) by (cbn [In] in HD1; lia).
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a).
  { intros q k a Hq Ha. split; [right; right; left; exists q, k; split; [exact Hq| lia]|]. cbn [outside]. split; [| exact I].
    destruct OWNF as (f & kf & Hin & H1 & H2 & _).
    pose proof (af_frames_range RT AF Σ m f kf ART0 Hin) as (_ & _ & _ & R). specialize (R q k Hq). lia. }
  hide POBJ.
  carve_frame 160%nat ST.
  walk_to AF MST [(usp - 160, usp)] [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
  park OWNF.
  fframe_chunk RT AF fr 1%nat 128 pix 64.
  fframe_chunk RT AF fr 1%nat 128 (p_data v) (4 * (p_wpl v * p_h v)).
  fframe_optr RT AF fr 1%nat 128 OWN usp. park OWN.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 160, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x8f168].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    unpark_accok_munch OWN MUx (rt_live RT Σ) (rt_frames RT Σ) usp
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCDP. local_acc FSH fr 10%nat 80 FR64 FR1 ACCE.
  assert (AGF1 : agree_on PF m _) by (eapply agree_sub; [exact AGF| intros zz [Hz _]; exact Hz]). clear AGF. rename AGF1 into AGF.
  park_disj.
  assert (DC : p_d v = 1 \/ p_d v = 2 \/ p_d v = 4 \/ p_d v = 8) by (cbn [In] in HD1; lia).
  walk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pmax, pmax + 4)]
               [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4].
  sx32_fix.
  destruct DC as [D1|DL].
  + (* [comment removed for export] *)
    rewrite D1 in *.
    awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4].
    (* [comment removed for export] *)
    split_last_CB FRM [12%nat; 4%nat; 36%nat]. split_at FRM 10%nat FRE. split_at FRE 1%nat FRT.
    destruct (cb4_c4 _ _ _ FRE) as (xe & PEC). clear FRE.
    pose proof FSH as SHE. split_at SHE 10%nat SHE2. split_at SHE2 1%nat SHE3. clear SHE SHE3.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; apply (aclient_mono _ _ usp _ _ _ _ (PMCL zz Hzz)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; destruct Hx as [_ HxO];
                        cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
    unfold hid in POBJ.
    lazymatch type of AGF with agree_on _ _ ?mc =>
      assert (POBJ1 : pix_obj (rt_live RT Σ) mc pix v cv)
        by (apply (pix_obj_agree (rt_live RT Σ) PF m mc pix v cv POBJ AGF PML); unfold pix_cells; rewrite D1; exact PXC) end.
    eapply cps_seq.
    { eapply ZR with (lo := lo) (pix := pix) (pe := fr + 80) (v := v) (cv := cv); rt_side idtac.
      - repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. exact POBJ1.
      - unfold optrF, parked in *. split.
        + exists fr, 1%nat. rewrite FRS. change (fs_size 1) with 128.
          split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|].
          split; [lia|]. split; [lia|].
          replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
          destruct SHE2 as [[_ B] _]. exact B.
        + unfold SEGTOP_A. repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia].
      - lazymatch type of PEC with rw_cells _ _ ?a _ => replace (fr + 80) with a by lia end. exact PEC.
      - lenv_tac.
      - lres_tac. }
    clear SHE2. pose proof OWN as OWNP. park OWNP.
    after_call RT AF.
    unpark OWNP. rename OWNP into OWN.
    lazymatch goal with AGx : agree_on _ ?m3 ?m4 |- _ =>
      lazymatch type of OWN with accok _ _ m3 _ _ =>
        apply (fun h => accok_keep_fp (rt_live RT Σ) (rt_frames RT Σ) m3 m4 _ _ _ _ pmax 4 h AGx ltac:(lia) ltac:(solve [frames_sub_tac])
                 ltac:(intros zz Hzz; cbn [outside]; unfold shad, SHB, parked in *; split; [| exact I]; clear - Hzz FRSH PMLO LOR SPT PM0; Z.div_mod_to_equations; lia)) in OWN end end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; destruct (NFA _ (proj1 Hx)) as [N1 N2]; split; [lia| exact I]]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pmax, pmax + 4)]
                 [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4].
    frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8f4ec
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; apply (aclient_mono _ _ usp _ _ _ _ (PMCL zz Hzz)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; destruct Hx as [_ HxO];
                      cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact (proj1 Hx))
      ltac:(fun fl FLN =>
              assert (FLPM : fl < pmax \/ pmax + 4 <= fl)
                by (destruct (Z_lt_ge_dec fl pmax) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (pmax + 4)) as [FG2|]; [| right; lia];
                    exfalso; apply FLN; right; right; right; left; destruct (PMFF fl ltac:(lia)) as (f0 & k0 & Hin0 & Hr0); exists f0, k0;
                    split; [| exact Hr0]; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; right; exact Hin0)).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 160, usp)] (@nil Z).
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. do 2 eexists.
    split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
    split; [| eassumption].
    repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    intros a Ha Ho; exact (AGF a (conj Ha Ho)).
  + (* [comment removed for export] *)
    rewrite (sx32_small (p_w v)) in FRM by lia.
    pose proof FRM as WC. split_at WC 4%nat WC2. split_at WC2 1%nat WC3. clear WC WC3.
    destruct DL as [DV|[DV|DV]].
    * rewrite DV in *.
      awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4]. sx32_fix.
      awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4]. sx32_fix.
      replace (zx32 (Z_to_bv 64 2)) with (Z_to_bv 64 2) by (apply bv_eq; vm_compute; reflexivity).
      rewrite !(unsigned_lit 2) by lia. rewrite !Z.add_0_r. swrap32_fix.
      pose proof (u8arr_of_rw_cells asegs _ _ _ _ DBC) as [RB _].
      eapply evt_cut.
      { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
          epose proof (gmax_rows (Z.to_nat (p_h v)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (p_data v) (p_wpl v) (p_h v) (p_w v) _ (fr + 32) dbs) as GR end.
        replace (p_data v + 4 * (0 * p_wpl v)) with (p_data v) in GR by lia.
        eapply GR; unfold parked in *.
        all: lazymatch goal with
             | |- bytes_at _ _ _ _ => exact RB
             | |- rw_cells _ _ _ _ => exact WC2
             | |- acc _ _ _ _ => assumption
             | |- mem_inv _ _ => assumption
             | |- Z.of_nat (length _) = _ => rewrite DBL; lia
             | |- Z.of_nat (Z.to_nat _) = _ => rewrite Z2Nat.id by lia; lia
             | |- _ => first [ lia | (Z.div_mod_to_equations; lia) ]
             end. }
      intros ms' PO. unfold gmax_exit in PO.
      destruct PO as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & t3' & t4' & t5' & t6' & ->).
      clear RB WC2.
      awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4].
      frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8f4ec
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; apply (aclient_mono _ _ usp _ _ _ _ (PMCL zz Hzz)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; destruct Hx as [_ HxO];
                        cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN =>
                assert (FLPM : fl < pmax \/ pmax + 4 <= fl)
                  by (destruct (Z_lt_ge_dec fl pmax) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (pmax + 4)) as [FG2|]; [| right; lia];
                      exfalso; apply FLN; right; right; right; left; destruct (PMFF fl ltac:(lia)) as (f0 & k0 & Hin0 & Hr0); exists f0, k0;
                      split; [| exact Hr0]; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; right; exact Hin0)).
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 160, usp)] (@nil Z).
      cps_stop.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. do 2 eexists.
      split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [| eassumption].
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      intros a Ha Ho; exact (AGF a (conj Ha Ho)).
    * rewrite DV in *.
      awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4]. sx32_fix.
      awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4]. sx32_fix.
      replace (zx32 (Z_to_bv 64 4)) with (Z_to_bv 64 4) by (apply bv_eq; vm_compute; reflexivity).
      rewrite !(unsigned_lit 4) by lia. rewrite !Z.add_0_r. swrap32_fix.
      pose proof (u8arr_of_rw_cells asegs _ _ _ _ DBC) as [RB _].
      eapply evt_cut.
      { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
          epose proof (gmax_rows (Z.to_nat (p_h v)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (p_data v) (p_wpl v) (p_h v) (p_w v) _ (fr + 32) dbs) as GR end.
        replace (p_data v + 4 * (0 * p_wpl v)) with (p_data v) in GR by lia.
        eapply GR; unfold parked in *.
        all: lazymatch goal with
             | |- bytes_at _ _ _ _ => exact RB
             | |- rw_cells _ _ _ _ => exact WC2
             | |- acc _ _ _ _ => assumption
             | |- mem_inv _ _ => assumption
             | |- Z.of_nat (length _) = _ => rewrite DBL; lia
             | |- Z.of_nat (Z.to_nat _) = _ => rewrite Z2Nat.id by lia; lia
             | |- _ => first [ lia | (Z.div_mod_to_equations; lia) ]
             end. }
      intros ms' PO. unfold gmax_exit in PO.
      destruct PO as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & t3' & t4' & t5' & t6' & ->).
      clear RB WC2.
      awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4].
      frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8f4ec
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; apply (aclient_mono _ _ usp _ _ _ _ (PMCL zz Hzz)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; destruct Hx as [_ HxO];
                        cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN =>
                assert (FLPM : fl < pmax \/ pmax + 4 <= fl)
                  by (destruct (Z_lt_ge_dec fl pmax) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (pmax + 4)) as [FG2|]; [| right; lia];
                      exfalso; apply FLN; right; right; right; left; destruct (PMFF fl ltac:(lia)) as (f0 & k0 & Hin0 & Hr0); exists f0, k0;
                      split; [| exact Hr0]; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; right; exact Hin0)).
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 160, usp)] (@nil Z).
      cps_stop.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. do 2 eexists.
      split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [| eassumption].
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      intros a Ha Ho; exact (AGF a (conj Ha Ho)).
    * rewrite DV in *.
      awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4]. sx32_fix.
      awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4]. sx32_fix.
      replace (zx32 (Z_to_bv 64 8)) with (Z_to_bv 64 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite !(unsigned_lit 8) by lia. rewrite !Z.add_0_r. swrap32_fix.
      pose proof (u8arr_of_rw_cells asegs _ _ _ _ DBC) as [RB _].
      eapply evt_cut.
      { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
          epose proof (gmax_rows (Z.to_nat (p_h v)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (p_data v) (p_wpl v) (p_h v) (p_w v) _ (fr + 32) dbs) as GR end.
        replace (p_data v + 4 * (0 * p_wpl v)) with (p_data v) in GR by lia.
        eapply GR; unfold parked in *.
        all: lazymatch goal with
             | |- bytes_at _ _ _ _ => exact RB
             | |- rw_cells _ _ _ _ => exact WC2
             | |- acc _ _ _ _ => assumption
             | |- mem_inv _ _ => assumption
             | |- Z.of_nat (length _) = _ => rewrite DBL; lia
             | |- Z.of_nat (Z.to_nat _) = _ => rewrite Z2Nat.id by lia; lia
             | |- _ => first [ lia | (Z.div_mod_to_equations; lia) ]
             end. }
      intros ms' PO. unfold gmax_exit in PO.
      destruct PO as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & t3' & t4' & t5' & t6' & ->).
      clear RB WC2.
      awalk [e_stack_malloc 1%nat; e_pixZero; 0x8f2b8; 0x8f4e4].
      frame_release_w RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x8f4ec
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; apply (aclient_mono _ _ usp _ _ _ _ (PMCL zz Hzz)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; destruct Hx as [_ HxO];
                        cbn [outside] in HxO; unfold shad, SHB in *; repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN =>
                assert (FLPM : fl < pmax \/ pmax + 4 <= fl)
                  by (destruct (Z_lt_ge_dec fl pmax) as [|FG1]; [left; lia|]; destruct (Z_lt_ge_dec fl (pmax + 4)) as [FG2|]; [| right; lia];
                      exfalso; apply FLN; right; right; right; left; destruct (PMFF fl ltac:(lia)) as (f0 & k0 & Hin0 & Hr0); exists f0, k0;
                      split; [| exact Hr0]; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; right; exact Hin0)).
      refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      walk_to AF MST [(usp - 160, usp)] (@nil Z).
      cps_stop.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. do 2 eexists.
      split; [| alg_tac].
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [| eassumption].
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      intros a Ha Ho; exact (AGF a (conj Ha Ho)).
Qed.
End GMAXC.

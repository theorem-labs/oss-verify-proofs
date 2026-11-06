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
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit D_iface D_defs LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.





Section SC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.
Hypothesis VALID : pixcmapIsValid_cps RT.

Theorem pixSetColormap_ok : pixSetColormap_cps RT.
Proof using AF GP RERR VALID.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix cmap v cv
    FDO MST -> -> -> PO PCM0 PD CO NE1 NE2 NE3 NE4 ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct CO as ((pad & CMC) & (INC & CM0 & CM16 & _) & (INA & AR0 & AR16 & ARN) & CMOK & NEQ).
  destruct cv as [arr depth nalloc n]. cbn [c_arr c_depth c_nalloc c_n] in *. unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC.
  destruct PO as (PXC & (INP & PX0 & PX16 & _) & HOK & DAT & _).
  destruct DAT as [E|((IND & DA0 & DA16 & DAN) & DNE)]; [contradiction|].
  destruct v as [w h d spp wpl xres yres inf spec pcm data].
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in *. subst pcm.
  unfold pix_cells in PXC. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXC.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixSetColormap, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof RERR as RE. unfold returnError_cps in RE. pose proof VALID as VLD. unfold pixcmapIsValid_cps in VLD.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pix + 48, pix + 56)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pix 64. chunk_facts RT AF GP cmap 24.
  pose proof (live_apart RT AF Σ m cmap 24 pix 64 ART0 INC INP NE1) as CPD.
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  park_disj.
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    carve_frame 96%nat ST.
    clear_acc.
    Time walk_to AF MST [(usp - 96, usp)] [0x4b7dc].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
    eapply cps_seq.
    { eapply (gp_stack_malloc_1 RT GP) with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [auto| auto| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    fframe_chunk RT AF fr 1%nat 128 pix 64.
    fframe_chunk RT AF fr 1%nat 128 cmap 24.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x92e88].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -96) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -96) -> rw_cells asegs mE (usp + -96) cs ->
          wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> rw_cells asegs mE pix (pix_cells (mkPixv w h d spp wpl xres yres inf spec cmap data)) ->
          agree_on PF m mE -> wmono asegs m mE ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_live RT S = rt_live RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
          rt_credit RT Σ - 6 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) r24 s9 s10 s11 r28 r29 r30 r31 F' fc' 0x92f78 mE))) QF) end.   (* [comment removed for export] *)
    { intros S mE r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE PXE AGE WME EFR ELV ESP0 ECR.
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
      clear_acc.
      destruct (wr_at_rw_CB mE fr 120 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 120) with 120%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      unfold pix_cells in PXE. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXE.
      unfold entry_st.
      Time walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x92fd4].
      Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x92fdc
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN =>
                lazymatch type of FLN with ~ aclient ?lvS ?frsS _ _ =>
                  pose proof (flag_apart lvS frsS fl pix (pix + 64) FLN
                                ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                      right; right; left; exists pix, 64; split; [rewrite ELV; exact INP| lia])) as FPX
                end;
                repeat match goal with H : rw_cells asegs _ fr _ |- _ => clear H | H : rw_cells asegs _ (fr / 8 + 2147450880) _ |- _ => clear H end).
      Time walk_to AF MST [(usp - 96, usp)] (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. eexists.
      split.
      + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        * lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end.
        * split; [| unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; eassumption].
          intros a Ha Ho. apply AGF. split; [| exact Ho].
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in Ha end. exact Ha.
      + repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
        repeat split; auto; lia.
    }
    (* [comment removed for export] *)
    clear_acc.
    walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x92e9c].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x92ec4; 0x99b40].
    clear_acc.
    cwalk [0x92ecc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x99b40; 0x99404; 0x90718; 0x92f78].
    (* [comment removed for export] *)
    split_last_CB FRM [24; 4; 52]%nat. split_at FRM 6%nat FRv. split_at FRv 1%nat FRrest.
    destruct (cb4_c4 _ _ _ FRv) as (v0 & VC0). clear FRv.
    lazymatch type of FSH with rw_cells _ ?mm _ _ => assert (SHV : bytes_at asegs mm (shad (fr + 64)) (ushadow 4)) end.
    { pose proof (rw_cells_head _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _
                   (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ FSH))))))))) as [[_ X] _].
      cbn [cells_bytes cbytes app csize Z.of_nat Pos.of_succ_nat Pos.succ] in X.
      replace (shad (fr + 64)) with (fr / 8 + 2147450880 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) by (unfold shad, SHB; Z.div_mod_to_equations; lia). exact X. }
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { eapply VLD with (lo := lo) (cmap := cmap) (pix := 0) (pv := fr + 64) (cv := mkCmapv arr depth nalloc n)
                      (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (x := v0); rt_side idtac.
      all: lazymatch goal with
           | |- cmap_obj _ _ _ _ =>
               unfold cmap_obj, cmap_cells, chunk; cbn [c_arr c_depth c_nalloc c_n];
               split; [eexists; exact CMC|]; split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|];
               split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|]; split; [exact CMOK| assumption]
           | |- _ \/ _ => left; reflexivity
           | |- optrF _ _ _ _ _ =>
               unfold optrF, own_frame; unfold parked in *; split;
               [ exists fr, 1%nat; change (fs_size 1) with 128;
                 split; [solve [frames_in_tac]|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [ul| exact SHV]
               | split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [lia| right; ul] ]
           | |- rw_cells _ _ _ [C4 _] => exact VC0
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           | |- ?g => idtac "LEFTOVER:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 _]; destruct Hx as [Hx1 _];
                  first [ split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; split; [lia| exact I]]
                        | apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] ]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
    lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 64) [C4 _], F3 : rw_cells asegs ?mm (fr + 68) _ |- _ =>
      assert (WF120 : wr_at asegs mm fr 120)
        by (apply (proj2 (wr_at_app mm fr 64 56 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
            apply (proj2 (wr_at_app mm (fr + 64) 4 52 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
            replace (fr + 64 + 4) with (fr + 68) by lia; exact (proj2 F3)) end.
    walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x90718; 0x92f78].
    sx32_fix. brfork HV.
    1:{ (* [comment removed for export] *)
      cwalk [0x90718; 0x92f78].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
      eapply cps_seq.
      { eapply RE with (lo := lo); rt_side idtac.
        all: lazymatch goal with
             | |- exists l, In _ LEPT_LITS => rewrite ?unsigned_lit by lia; lit_in
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
             | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
             | |- ?g => idtac "LEFTOVER:" g
             end. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
      walk_to AF MST [(usp - 96, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x92f78].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 120 => eassumption
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- rw_cells asegs _ _ (pix_cells _) => exact PXC
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
    }
    cwalk [0x90718; 0x92f78].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 120 => eassumption
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- rw_cells asegs _ _ (pix_cells _) => exact PXC
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
  - (* [comment removed for export] *)
    carve_frame 112%nat ST.
    clear_acc.
    Time walk_to AF MST [(usp - 112, usp)] [0x4b7dc].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
    eapply cps_seq.
    { eapply (gp_stack_malloc_1 RT GP) with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [auto| auto| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
    fframe_chunk RT AF fr 1%nat 128 pix 64.
    fframe_chunk RT AF fr 1%nat 128 cmap 24.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x92e88].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
          wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> rw_cells asegs mE pix (pix_cells (mkPixv w h d spp wpl xres yres inf spec cmap data)) ->
          agree_on PF m mE -> wmono asegs m mE ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_live RT S = rt_live RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
          rt_credit RT Σ - 6 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) r24 s9 s10 s11 r28 r29 r30 r31 F' fc' 0x92f78 mE))) QF) end.   (* [comment removed for export] *)
    { intros S mE r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r24 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE PXE AGE WME EFR ELV ESP0 ECR.
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
      clear_acc.
      destruct (wr_at_rw_CB mE fr 120 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 120) with 120%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      unfold pix_cells in PXE. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXE.
      unfold entry_st.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x92fd4].
      Time frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x92fdc
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN =>
                lazymatch type of FLN with ~ aclient ?lvS ?frsS _ _ =>
                  pose proof (flag_apart lvS frsS fl pix (pix + 64) FLN
                                ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                      right; right; left; exists pix, 64; split; [rewrite ELV; exact INP| lia])) as FPX
                end;
                repeat match goal with H : rw_cells asegs _ fr _ |- _ => clear H | H : rw_cells asegs _ (fr / 8 + 2147450880) _ |- _ => clear H end).
      Time walk_to AF MST [(usp - 112, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -112), FR' : rw_cells asegs _ (usp + -112) _ |- _ => release_frame FR' ST' usp end.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. eexists.
      split.
      + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        * lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end.
        * split; [| unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; eassumption].
          intros a Ha Ho. apply AGF. split; [| exact Ho].
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in Ha end. exact Ha.
      + repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
        repeat split; auto; lia.
    }
    (* [comment removed for export] *)
    clear_acc.
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x92e9c].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x92ec4; 0x99b40].
    clear_acc.
    cwalk [0x92ecc].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x99b40; 0x99404; 0x90718; 0x92f78].
    (* [comment removed for export] *)
    split_last_CB FRM [24; 4; 52]%nat. split_at FRM 6%nat FRv. split_at FRv 1%nat FRrest.
    destruct (cb4_c4 _ _ _ FRv) as (v0 & VC0). clear FRv.
    lazymatch type of FSH with rw_cells _ ?mm _ _ => assert (SHV : bytes_at asegs mm (shad (fr + 64)) (ushadow 4)) end.
    { pose proof (rw_cells_head _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _
                   (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ FSH))))))))) as [[_ X] _].
      cbn [cells_bytes cbytes app csize Z.of_nat Pos.of_succ_nat Pos.succ] in X.
      replace (shad (fr + 64)) with (fr / 8 + 2147450880 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) by (unfold shad, SHB; Z.div_mod_to_equations; lia). exact X. }
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                  unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { eapply VLD with (lo := lo) (cmap := cmap) (pix := 0) (pv := fr + 64) (cv := mkCmapv arr depth nalloc n)
                      (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (x := v0); rt_side idtac.
      all: lazymatch goal with
           | |- cmap_obj _ _ _ _ =>
               unfold cmap_obj, cmap_cells, chunk; cbn [c_arr c_depth c_nalloc c_n];
               split; [eexists; exact CMC|]; split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|];
               split; [split; [solve [in_live_tac]| split; [assumption| split; [assumption| lia]]]|]; split; [exact CMOK| assumption]
           | |- _ \/ _ => left; reflexivity
           | |- optrF _ _ _ _ _ =>
               unfold optrF, own_frame; unfold parked in *; split;
               [ exists fr, 1%nat; change (fs_size 1) with 128;
                 split; [solve [frames_in_tac]|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [ul| exact SHV]
               | split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [lia| right; ul] ]
           | |- rw_cells _ _ _ [C4 _] => exact VC0
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           | |- ?g => idtac "LEFTOVER:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 _]; destruct Hx as [Hx1 _];
                  first [ split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; split; [lia| exact I]]
                        | apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] ]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
    lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 64) [C4 _], F3 : rw_cells asegs ?mm (fr + 68) _ |- _ =>
      assert (WF120 : wr_at asegs mm fr 120)
        by (apply (proj2 (wr_at_app mm fr 64 56 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
            apply (proj2 (wr_at_app mm (fr + 64) 4 52 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
            replace (fr + 64 + 4) with (fr + 68) by lia; exact (proj2 F3)) end.
    walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x90718; 0x92f78].
    sx32_fix. brfork HV.
    1:{ (* [comment removed for export] *)
      cwalk [0x90718; 0x92f78].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                           split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                    unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]).
      eapply cps_seq.
      { eapply RE with (lo := lo); rt_side idtac.
        all: lazymatch goal with
             | |- exists l, In _ LEPT_LITS => rewrite ?unsigned_lit by lia; lit_in
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- (_ < _)%nat => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia
             | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
             | |- ?g => idtac "LEFTOVER:" g
             end. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => destruct Hx as [Hx1 _]; apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
      walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (pix + 48, pix + 56)] [0x92f78].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 120 => eassumption
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- rw_cells asegs _ _ (pix_cells _) => exact PXC
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
    }
    cwalk [0x90718; 0x92f78].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                         split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ Hx2]; cbn [outside] in Hx2;
                                         unfold shad, SHB in *; repeat split; try exact I; first [tauto | lia | Z.div_mod_to_equations; lia]) end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 120 => eassumption
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- rw_cells asegs _ _ (pix_cells _) => exact PXC
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
Qed.
End SC.

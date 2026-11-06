(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.




(* [comment removed for export] *)
Ltac split_ins T i vsp vx K :=
  lazymatch T with
  | forall x : ?A, @?B x =>
      let y := fresh "y" in
      constr:(forall y : A, ltac:(
        let b := eval cbv beta in (B y) in
        let j := eval cbv in (S i) in
        let r := lazymatch j with
                 | 4%nat => split_ins b j y vx K
                 | 39%nat => split_ins b j vsp y K
                 | _ => split_ins b j vsp vx K
                 end in
        exact r))
  | _ => let p := K vsp vx in constr:(p -> T)
  end.
Section CV.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis STDERR : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorInt.
Hypothesis MAXIDX : pixGetMaxColorIndex_cps RT.

Definition pixcmapIsValid_ok_N0_stmt : Prop :=
  ltac:(let T := eval cbv delta [pixcmapIsValid_cps] beta in (pixcmapIsValid_cps RT) in
        let r := split_ins T 0%nat tt tt ltac:(fun sp pix => constr:(bv_unsigned sp mod 32 = 0 /\ pix = 0)) in exact r).
Lemma pixcmapIsValid_ok_N0 : pixcmapIsValid_ok_N0_stmt.
Proof using AF GP STDERR RERR MAXIDX.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cmap pix pv cv v x
    FDO MST -> -> -> -> CO PO OP PVC ENV RES CASEHX.
  destruct CASEHX as [CASEH CASEX].
  unfold lpost, lenv, lres, keeps, keepsL, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). destruct OP as (OWNF & PV0 & PV8 & PVH & PVS).
  assert (OWN : accok (rt_live RT Σ) (rt_frames RT Σ) m pv 4) by (right; exact OWNF).
  destruct CO as ((pad & CMC) & (INC & CM0 & CM16 & _) & (INA & AR0 & AR16 & ARN) & (HD & ENA & NB) & NEQ).
  destruct cv as [arr depth nalloc n]. cbn [c_arr c_depth c_nalloc c_n] in *. unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixcmapIsValid, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  pose proof RERR as RE. unfold returnError_cps in RE. pose proof STDERR as SE. unfold lept_stderr_cps in SE.
  pose proof MAXIDX as MXI. unfold pixGetMaxColorIndex_cps in MXI.
  (* [comment removed for export] *)
  set (PF0 := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pv, pv + 4)] a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (PVLO : pv + 4 <= lo).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _).
    pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN in R. lia. }
  (* [comment removed for export] *)
  assert (PVC1 : pv + 4 <= cmap \/ cmap + 24 <= pv).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). specialize (R cmap 24 INC). lia. }
  assert (PVC2 : pv + 4 <= arr \/ arr + 4 * nalloc <= pv).
  { destruct OWNF as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R). specialize (R arr (4 * nalloc) INA). lia. }
  (* [comment removed for export] *)
  assert (HPV : forall x, shad pv <= x < shad pv + (4 + 7) / 8 -> PF x).
  { destruct OWNF as (f & k & Hin & H1 & H2 & H8 & H0 & HT & Hb). intros zz Hx.
    pose proof (af_fshadow_apart RT AF Σ m f k ART0 Hin) as (_ & SA). specialize (SA f k Hin).
    split; [right; right; right; right; exists f, k; split; [exact Hin|]| cbn [outside]; split; [| exact I]].
    - clear - Hx H1 H2. unfold shad in *. Z.div_mod_to_equations. lia.
    - clear - Hx H1 H2 SA. unfold shad in *. Z.div_mod_to_equations. lia. }
  park OWNF.
  chunk_facts RT AF GP cmap 24.
  chunk_facts RT AF GP arr (4 * nalloc).
  assert (EBIT : Z.land (Z.shiftr 278 depth) 1 = 1) by (destruct HD as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
  assert (ESHL : bv_swrap 32 (1 ≪ ((depth mod 18446744073709551616) mod 32)) = nalloc)
    by (rewrite ENA; destruct HD as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
  assert (NA : 2 <= nalloc <= 256) by (rewrite ENA; destruct HD as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia).
  assert (DR : 1 <= depth <= 8) by (destruct HD as [<-|[<-|[<-|[<-|[]]]]]; lia).
  assert (ESHL2 : bv_swrap 32 (1 ≪ (depth mod 32)) = nalloc)
    by (rewrite ENA; destruct HD as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
  assert (PFS1 : forall a, PF a -> usp <= a \/ a < lo) by (intros a [Ha _]; exact (PFS a Ha)).
  pose proof OWN as OWN0. park OWN0.   (* [comment removed for export] *)
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct PO as [-> | (PO & PD & PCM0)].
  { (* [comment removed for export] *)
    destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    park_disj. carve_frame 128%nat ST.
    (* [comment removed for export] *)
    clear_acc. park OWN.
    Time walk_to AF MST [(usp - 128, usp)] [0x4b928].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
    unpark_accok OWN AGF.
    eapply cps_seq.
    { eapply (gp_stack_malloc_0 RT GP) with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [auto| auto| lia]).
    fframe_open RT AF PF0 (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact Ha).
    fframe_chunk RT AF fr 0%nat 64 cmap 24.
    fframe_chunk RT AF fr 0%nat 64 arr (4 * nalloc).
    fframe_optr RT AF fr 0%nat 64 OWN usp. park OWN.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 128, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x977ac].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      unpark_accok_munch OWN MUx (rt_live RT Σ) (rt_frames RT Σ) usp
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]);
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
    (* [comment removed for export] *)
    assert (AGF1 : agree_on PF m _) by (eapply agree_sub; [exact AGF| intros zz [Hz _]; exact Hz]). clear AGF. rename AGF1 into AGF.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -128) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem) (y : word)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r25 r26 r27 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -128) -> rw_cells asegs mE (usp + -128) cs ->
          wr_at asegs mE fr 56 -> wr_at asegs mE (fr / 8 + 2147450880) 8 ->
          LIBH mE -> io_ssp mE -> rw_cells asegs mE pv [C4 y] -> agree_on PF m mE -> wmono asegs m mE ->
          rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ -> rt_live RT S = rt_live RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
          rt_credit RT Σ - 4 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 r22 (Z_to_bv 64 fr)
                                          (Z_to_bv 64 (fr / 8 + 2147450880)) r25 r26 r27 r28 r29 r30 r31 F' fc' 0x97960 mE))) QF) end.
    { intros S mE y r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r25 r26 r27 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE PVE AGE WME EFR ELV ESP0 ECR.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | PVE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      clear_acc. clear OWN.
      destruct (wr_at_rw_CB mE fr 56 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 8 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 56) with 56%nat in FRME. change (Z.to_nat 8) with 8%nat in FSHE.
      unfold entry_st.
      Time walk_to AF MST [(usp - 128, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x9799c].
      Time frame_release_g RT AF GP MST Σ fr 0%nat 64 PF AGF PFS1 usp lo 0x979a4
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); destruct (NFA _ (proj1 Hx)) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN =>
                lazymatch type of FLN with ~ aclient ?lvS ?frsS _ _ =>
                  unpark OWN0;
                  pose proof (flag_apart lvS frsS fl pv (pv + 4) FLN
                                ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                      lazymatch type of OWN0 with accok ?lv ?frs ?mo _ _ =>
                                        apply (aclient_mono lv frs USTACK_TOP lvS frsS USTACK_TOP x (accok_aclient lv frs mo USTACK_TOP pv 4 x OWN0 Hx));
                                        [ solve [live_sub_tac] | solve [frames_sub_tac] | lia ] end)) as FPV;
                  clear OWN0
                end;
                repeat match goal with H : rw_cells asegs _ cmap _ |- _ => clear H | H : rw_cells asegs _ fr _ |- _ => clear H
                                     | H : rw_cells asegs _ (fr / 8 + 2147450880) _ |- _ => clear H end).
      Time walk_to AF MST [(usp - 128, usp)] (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ (proj1 Hx)); split; [lia| exact I]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. do 2 eexists.
      split.
      + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        * lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end.
        * split; [| eassumption]. intros a Ha Ho. apply AGF. split; [| exact Ho].
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in Ha end. exact Ha.
      + repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
        repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
        repeat split; auto; lia.
    }
    Time walk_to AF MST [(usp - 128, usp); (pv, pv + 4)] [0x90c54; 0x90c20; 0x99e60; 0x97960].
    cwalk [0x90c54; 0x90c20; 0x99e60; 0x97960].
    rewrite (Z.mod_small depth 64) by lia. rewrite EBIT. brF.
    cwalk [0x90c54; 0x90c20; 0x99e60; 0x97960].
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; aclient_tac| exact I]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; pose proof (PFS _ Hx1); split; [lia| tauto]) end.
    to_entry.
    eapply EPI; try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 56 => first [exact (proj2 FRM) | eassumption]
         | |- wr_at asegs _ _ 8 => exact (proj2 FSH)
         | |- _ <= _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ => idtac
         end.
  - (* [comment removed for export] *)
    exfalso. clear - AL CASEH. lia.
  }
  exfalso. destruct PO as (_ & (_ & PPOS & _) & _). clear - PPOS CASEX. lia.
Qed.
End CV.

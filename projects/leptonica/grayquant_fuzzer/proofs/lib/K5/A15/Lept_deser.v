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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Lept_iface_nz.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import LeptL_kit Lept_objkit Lept_deserkit LeptC_deser2_defs LeptC_deserm1_defs LeptC_deser_ctx LeptC_deser_tail.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section DESER.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis LSE : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis HDR : pixCreateHeader_cps RT.
Hypothesis CRE : pixCreate_cps RT.
Hypothesis DES : pixDestroy_cps RT.
Hypothesis CMD : pixcmapDeserialize_cps RT.
Hypothesis SETC : pixSetColormap_cps RT.
Hypothesis VAL : pixcmapIsValid_cps RT.

(* [comment removed for export] *)
Theorem pixDeserialize_nz_ok : pixDeserialize_nz_cps RT.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo dp n ras
    FDO MST -> -> -> NR DP0 OWN UCTX TRS ENV RES.
  assert (CTXF : 28 <= n -> dp mod 8 = 0 -> own_live (rt_live RT Σ) dp n ->
                 forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 (bv_unsigned sp) lo m dp n ras rdes).
  { intros H28 H8 HOWN. apply (deser_ctx_intro RT Σ PMc ra sp s0 lo m dp n ras FDO MST); try assumption. lia. }
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixDeserialize, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold uctx in UCTX.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    carve_frame 192%nat ST.
    walk_to AF MST [(usp - 192, usp)] [0x4ba9c].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                 [0x4ba9c; 0x90c54; 0x90e84; 0x937bc; 0x93e38; 0x932e4; 0x99908; 0x94f04; 0x60844; 0x976a0; 0xa81cc].
    (* [comment removed for export] *)
    assert (EPI : deser_epi_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr).
    { unfold deser_epi_stmt_0, deser_PF. fold PF.
      intros S mE pixr v cv jE.
      repeat lazymatch goal with |- forall _ : ?T, _ => lazymatch T with word => intro end end.
      intros F' fc' ARTE MIE STE FRE WFE WSE LHE SSPE AGE EFR ESP0 ECR LSUB HOBJ HL0 HL1 HLP HLN HNZ.
      change (agree_on PF m mE) in AGE.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => clear H end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 120 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 120) with 120%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      (* [comment removed for export] *)
      assert (LOUT : forall b k, In (b, k) (rt_live RT S) -> forall x, b <= x < b + k ->
                outside [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] x).
      { intros bb kk Hb zz Hz.
        pose proof (af_live_range RT AF S mE bb kk ARTE Hb) as LR.
        pose proof (af_frames_range RT AF S mE fr 1%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (_ & _ & _ & D1). specialize (D1 bb kk Hb).
        pose proof (af_fshadow_apart RT AF S mE fr 1%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (D2 & _). specialize (D2 bb kk Hb).
        change (fs_size 1) with 128 in D1, D2. unfold shad, SHB in D2. rewrite ESP0 in LR. unfold STACK_WIN in LR.
        cbn [outside].
        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]. }
      unfold entry_st.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa8230].
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      assert (PFS1 : forall a, PF a -> usp <= a \/ a < lo) by exact PFS.
      frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xa8238
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      walk_to AF MST [(usp - 192, usp)] (@nil Z).
      cps_stop.
      (* [comment removed for export] *)
      try (lazymatch goal with STx : stk asegs _ lo (usp + -192) |- _ => release_frame FRE STx usp end).
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEP3 : keeps_live (rt_live RT S) mm mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; cbn [outside]; split; [exact (proj1 (LOUT bb kk Hb _ Ha))| exact I]);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      lazymatch goal with K3 : keeps_live _ _ ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEPF : keeps_live (rt_live RT S) mE mc)
          by (eapply keeps_live_trans; [exact KEEP1|]; eapply keeps_live_trans; [exact KEEPR| exact K3]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', pixr, v, cv end.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; assumption]| split; assumption]|].
        split; [intros a Ha _; apply AGF; exact Ha|].
        destruct HOBJ as [HZ|(HO & HD)]; [left; exact HZ| right]. split; [| exact HD].
        rewrite LV2. exact (pix_obj_keep _ mE _ pixr v cv KEEPF HO). }
      rewrite LV2, FRS2, SP2, CR2.
      split; [exact HL0|]. split; [exact HL1|]. split; [reflexivity|]. split; [exact ESP0|]. split; [lia|]. split; [exact HLP|]. split; [exact HLN| exact HNZ]. }
    (* [comment removed for export] *)
    brfork HB0.
    1:{ ds_awalk.
        ds_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH LVP usp lo (usp + -192)
          [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
    ds_awalk.
    destruct (Z_lt_le_dec n 28) as [NS|NB].
    1:{ (* [comment removed for export] *)
        ds_awalk.
        ds_msg_call RT AF GP LSE AGF PFS NFA usp lo [true; false].
        ds_walk AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
        ds_to_epi RT AF AGF PFS NFA (usp + -192).
        ds_epi_null EPI FRM FSH AGF LVP. }
    (* [comment removed for export] *)
    try unfold parked in OWN. destruct OWN as [OWN|(DP8 & dpp & dpk & DIN & DLO & DHI)]; [lia|].
    pose proof (CTXF NB DP8 (ex_intro _ dpp (ex_intro _ dpk (conj DIN (conj DLO DHI))))) as CTX. clear CTXF.
    cps_stop.
    art_now RT AF ltac:(ds_ivt).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      assert (DINS : In (dpp, dpk) (rt_live RT S)) by (solve [in_live_tac]);
      pose proof (af_acc_live RT AF S mm dpp dpk A DINS) as (WRD & ACCD) end.
    chunk_facts RT AF GP dpp dpk.
    fframe_chunk RT AF fr 1%nat 128 dpp dpk. norm_fshadow.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (wr_at_sub mm dpp dpk dp 24 WRD ltac:(lia) ltac:(lia) ltac:(lia)) as WRH end.
    apply wr_at_rw_CB in WRH; [| lia]. destruct WRH as (hbs & HCB). change (Z.to_nat 24) with 24%nat in HCB.
    apply spix_hdr_cells in HCB. destruct HCB as (b0 & b1 & b2 & b3 & w1 & w2 & w3 & w4 & w5 & HDC).
    ds_refresh RT AF GP.
    ds_walk AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    (* [comment removed for export] *)
    lazymatch goal with |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u1 u2 u3 : word,
         ms' = MS (@bvmap_set 5 word (Z_to_bv 5 10) u1 (@bvmap_set 5 word (Z_to_bv 5 11) u2 (@bvmap_set 5 word (Z_to_bv 5 12) u3 R))) F (Z_to_bv 64 0xa7e1c) fc rv m ro
         \/ ms' = MS (@bvmap_set 5 word (Z_to_bv 5 10) u1 (@bvmap_set 5 word (Z_to_bv 5 11) u2 (@bvmap_set 5 word (Z_to_bv 5 12) u3 R))) F (Z_to_bv 64 0xa7d78) fc rv m ro)) end.
    { brfork HI0; [apply evt_done; do 3 eexists; left; norm_regset; reflexivity|].
      awalk [0xa7e1c; 0xa7d78].
      brfork HI1; [apply evt_done; do 3 eexists; left; norm_regset; reflexivity|].
      awalk [0xa7e1c; 0xa7d78].
      brfork HI2; [apply evt_done; do 3 eexists; left; norm_regset; reflexivity|].
      awalk [0xa7e1c; 0xa7d78].
      brfork HI3; [apply evt_done; do 3 eexists; left; norm_regset; reflexivity|].
      awalk [0xa7e1c; 0xa7d78].
      apply evt_done; do 3 eexists; right; norm_regset; reflexivity. }
    intros ms (u1 & u2 & u3 & [E|E]); subst ms; norm_regset.
    1:{ (* [comment removed for export] *)
        ds_awalk.
        ds_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH LVP usp lo (usp + -192)
          [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(ds_ivt).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
    lazymatch goal with FRx : rw_cells asegs _ (usp + -192) _ |- _ => merge_low FRx 14%nat end.
    split_last_CB FRM [8; 4; 44; 8; 32]%nat.
    merge_low FRM 4%nat.
    lazymatch type of FRM with rw_cells asegs ?mm fr (?c0 :: CB 4 ?b :: ?post) =>
      apply (cb4_c4_in mm fr [c0] post b) in FRM; destruct FRM as (vx & FRM); cbn [app] in FRM end.
    lazymatch type of FRM with rw_cells asegs ?mm fr (?c0 :: ?c1 :: ?c2 :: CB 8 ?b :: ?post) =>
      apply (cb8_c8_in mm fr [c0; c1; c2] post b) in FRM; cbn [app] in FRM end.
    to_entry.
    eapply (deser_front2_ok_0 RT AF RC GP LSE RERR HDR CRE DES CMD SETC VAL Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              usp lo m QF fr dp n ras CTX LVP EPI).
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => eassumption
         | |- rw_cells _ _ (_ / 8 + _) _ => exact FSH
         | |- rw_cells _ _ _ _ => eassumption
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
         end.
(* [comment removed for export] *)
  - (* [comment removed for export] *)
    carve_frame 208%nat ST.
    walk_to AF MST [(usp - 208, usp)] [0x4ba9c].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]
                 [0x4ba9c; 0x90c54; 0x90e84; 0x937bc; 0x93e38; 0x932e4; 0x99908; 0x94f04; 0x60844; 0x976a0; 0xa81cc].
    (* [comment removed for export] *)
    assert (EPI : deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr).
    { unfold deser_epi_stmt_16, deser_PF. fold PF.
      intros S mE pixr v cv jE.
      repeat lazymatch goal with |- forall _ : ?T, _ => lazymatch T with word => intro end end.
      intros F' fc' ARTE MIE STE FRE WFE WSE LHE SSPE AGE EFR ESP0 ECR LSUB HOBJ HL0 HL1 HLP HLN HNZ.
      change (agree_on PF m mE) in AGE.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => clear H end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 120 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 120) with 120%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      (* [comment removed for export] *)
      assert (LOUT : forall b k, In (b, k) (rt_live RT S) -> forall x, b <= x < b + k ->
                outside [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] x).
      { intros bb kk Hb zz Hz.
        pose proof (af_live_range RT AF S mE bb kk ARTE Hb) as LR.
        pose proof (af_frames_range RT AF S mE fr 1%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (_ & _ & _ & D1). specialize (D1 bb kk Hb).
        pose proof (af_fshadow_apart RT AF S mE fr 1%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (D2 & _). specialize (D2 bb kk Hb).
        change (fs_size 1) with 128 in D1, D2. unfold shad, SHB in D2. rewrite ESP0 in LR. unfold STACK_WIN in LR.
        cbn [outside].
        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]. }
      unfold entry_st.
      walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa8230].
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      assert (PFS1 : forall a, PF a -> usp <= a \/ a < lo) by exact PFS.
      frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xa8238
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      walk_to AF MST [(usp - 208, usp)] (@nil Z).
      cps_stop.
      (* [comment removed for export] *)
      try (lazymatch goal with STx : stk asegs _ lo (usp + -208) |- _ => release_frame FRE STx usp end).
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEP3 : keeps_live (rt_live RT S) mm mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; cbn [outside]; split; [exact (proj1 (LOUT bb kk Hb _ Ha))| exact I]);
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      lazymatch goal with K3 : keeps_live _ _ ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        assert (KEEPF : keeps_live (rt_live RT S) mE mc)
          by (eapply keeps_live_trans; [exact KEEP1|]; eapply keeps_live_trans; [exact KEEPR| exact K3]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', pixr, v, cv end.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; assumption]| split; assumption]|].
        split; [intros a Ha _; apply AGF; exact Ha|].
        destruct HOBJ as [HZ|(HO & HD)]; [left; exact HZ| right]. split; [| exact HD].
        rewrite LV2. exact (pix_obj_keep _ mE _ pixr v cv KEEPF HO). }
      rewrite LV2, FRS2, SP2, CR2.
      split; [exact HL0|]. split; [exact HL1|]. split; [reflexivity|]. split; [exact ESP0|]. split; [lia|]. split; [exact HLP|]. split; [exact HLN| exact HNZ]. }
    (* [comment removed for export] *)
    brfork HB0.
    1:{ ds_awalk.
        ds_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH LVP usp lo (usp + -208)
          [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
    ds_awalk.
    destruct (Z_lt_le_dec n 28) as [NS|NB].
    1:{ (* [comment removed for export] *)
        ds_awalk.
        ds_msg_call RT AF GP LSE AGF PFS NFA usp lo [true; false].
        ds_walk AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
        ds_to_epi RT AF AGF PFS NFA (usp + -208).
        ds_epi_null EPI FRM FSH AGF LVP. }
    (* [comment removed for export] *)
    try unfold parked in OWN. destruct OWN as [OWN|(DP8 & dpp & dpk & DIN & DLO & DHI)]; [lia|].
    pose proof (CTXF NB DP8 (ex_intro _ dpp (ex_intro _ dpk (conj DIN (conj DLO DHI))))) as CTX. clear CTXF.
    cps_stop.
    art_now RT AF ltac:(ds_ivt).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      assert (DINS : In (dpp, dpk) (rt_live RT S)) by (solve [in_live_tac]);
      pose proof (af_acc_live RT AF S mm dpp dpk A DINS) as (WRD & ACCD) end.
    chunk_facts RT AF GP dpp dpk.
    fframe_chunk RT AF fr 1%nat 128 dpp dpk. norm_fshadow.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (wr_at_sub mm dpp dpk dp 24 WRD ltac:(lia) ltac:(lia) ltac:(lia)) as WRH end.
    apply wr_at_rw_CB in WRH; [| lia]. destruct WRH as (hbs & HCB). change (Z.to_nat 24) with 24%nat in HCB.
    apply spix_hdr_cells in HCB. destruct HCB as (b0 & b1 & b2 & b3 & w1 & w2 & w3 & w4 & w5 & HDC).
    ds_refresh RT AF GP.
    ds_walk AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    (* [comment removed for export] *)
    lazymatch goal with |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u1 u2 u3 : word,
         ms' = MS (@bvmap_set 5 word (Z_to_bv 5 10) u1 (@bvmap_set 5 word (Z_to_bv 5 11) u2 (@bvmap_set 5 word (Z_to_bv 5 12) u3 R))) F (Z_to_bv 64 0xa7e1c) fc rv m ro
         \/ ms' = MS (@bvmap_set 5 word (Z_to_bv 5 10) u1 (@bvmap_set 5 word (Z_to_bv 5 11) u2 (@bvmap_set 5 word (Z_to_bv 5 12) u3 R))) F (Z_to_bv 64 0xa7d78) fc rv m ro)) end.
    { brfork HI0; [apply evt_done; do 3 eexists; left; norm_regset; reflexivity|].
      awalk [0xa7e1c; 0xa7d78].
      brfork HI1; [apply evt_done; do 3 eexists; left; norm_regset; reflexivity|].
      awalk [0xa7e1c; 0xa7d78].
      brfork HI2; [apply evt_done; do 3 eexists; left; norm_regset; reflexivity|].
      awalk [0xa7e1c; 0xa7d78].
      brfork HI3; [apply evt_done; do 3 eexists; left; norm_regset; reflexivity|].
      awalk [0xa7e1c; 0xa7d78].
      apply evt_done; do 3 eexists; right; norm_regset; reflexivity. }
    intros ms (u1 & u2 & u3 & [E|E]); subst ms; norm_regset.
    1:{ (* [comment removed for export] *)
        ds_awalk.
        ds_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH LVP usp lo (usp + -208)
          [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)]. }
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(ds_ivt).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
    lazymatch goal with FRx : rw_cells asegs _ (usp + -208) _ |- _ => merge_low FRx 15%nat end.
    split_last_CB FRM [8; 4; 44; 8; 32]%nat.
    merge_low FRM 4%nat.
    lazymatch type of FRM with rw_cells asegs ?mm fr (?c0 :: CB 4 ?b :: ?post) =>
      apply (cb4_c4_in mm fr [c0] post b) in FRM; destruct FRM as (vx & FRM); cbn [app] in FRM end.
    lazymatch type of FRM with rw_cells asegs ?mm fr (?c0 :: ?c1 :: ?c2 :: CB 8 ?b :: ?post) =>
      apply (cb8_c8_in mm fr [c0; c1; c2] post b) in FRM; cbn [app] in FRM end.
    to_entry.
    eapply (deser_front2_ok_16 RT AF RC GP LSE RERR HDR CRE DES CMD SETC VAL Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              usp lo m QF fr dp n ras CTX LVP EPI).
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => eassumption
         | |- rw_cells _ _ (_ / 8 + _) _ => exact FSH
         | |- rw_cells _ _ _ _ => eassumption
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
         end.
Qed.

(* [comment removed for export] *)
Theorem pixDeserialize_ok : pixDeserialize_cps RT.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
Proof. exact (pixDeserialize_cps_of_nz RT pixDeserialize_nz_ok). Qed.
End DESER.

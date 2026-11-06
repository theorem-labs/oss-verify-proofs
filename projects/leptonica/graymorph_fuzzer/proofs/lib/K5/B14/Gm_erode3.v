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
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_deserkit Lept_gmax_defs D_iface D_defs Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit Gm_leaf LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac gd_resync RT AF GP AGF PFS NFA :=
  cps_stop;
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]);
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end;
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; park_disj.


Section GE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis ADDB : pixAddBorderGeneral_cps RT.
Hypothesis RMB : pixRemoveBorderGeneral_cps RT.
Hypothesis K3H : gray3h_cps RT e_pixErodeGray3h.
Hypothesis KNULL : gm_null_cps RT e_pixErodeGray3h.
Hypothesis RMNULL : gm_null_cps RT e_pixRemoveBorderGeneral.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis DNULL : pixDestroy_null_cps RT.

Theorem pixErodeGray3_ok : gray3_cps RT e_pixErodeGray3.
Proof using AF RC GP RERR ADDB RMB K3H KNULL RMNULL DESTROY DNULL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixs vs cvs ras FDO MST -> -> -> -> POS SDNZ UCX TRS ENV RES.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold uctx in UCX.
  pose proof POS as (PXS & (PSIN & PS0 & PS16 & _) & HOKS & _ & PSCM).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0.
  unfold bv_modulus in RRA, RS0. change (2 ^ Z.of_N 64) with (2^64) in RRA, RS0.
  unfold entry_st, e_pixErodeGray3, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, GRAY3_COST, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pixs 64.
  unfold pix_cells in PXS.
  assert (DBND : 1 <= p_d vs <= 32) by (destruct HOKS as (HD1 & _); cbn [In] in HD1; lia).
  hide POS. hide PSCM. hide HOKS. hide TRS. hide UCX.
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)

    park_disj. carve_frame 128%nat ST.
    clear_acc.
    Time walk_to AF MST [(usp - 128, usp)] [e_stack_malloc 1%nat].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
    pose proof (proj2 FRM) as WRF0. cbn [cells_size csize Nat.add] in WRF0. change (Z.of_nat 120) with 120 in WRF0. hide WRF0.
    fframe_chunk RT AF fr 1%nat 128 pixs 64.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae618].
    gd_resync RT AF GP AGF PFS NFA.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -128) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem) (r : Z) (v : pixv)
                (r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r26 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -128) -> rw_cells asegs mE (usp + -128) cs ->
          wr_at asegs mE fr 8 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE ->
          (r = 0 \/ (pix_obj (rt_live RT S) mE r v (mkCmapv 0 0 0 0) /\ p_w v = p_w vs /\ p_h v = p_h vs /\ p_d v = 8 /\ p_data v <> 0 /\ p_cmap v = 0)) ->
          rt_live RT S = (if r =? 0 then rt_live RT Σ else (p_data v, rsize v) :: (r, 64) :: rt_live RT Σ) ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - GRAY3_COST <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          (Z_to_bv 64 r) r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 r22 r23 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) r26 s11 r28 r29 r30 r31 F' fc' 0xae754 mE))) QF) end.
    { intros S mE r v r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r26 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE HPR ELV EFR ESP0 ECR.
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
      repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S))
        by (intros e He; rewrite ELV; destruct (r =? 0); [exact He| right; right; exact He]).
      hide ELV. hide HPR.
      destruct (wr_at_rw_CB mE fr 8 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 8) with 8%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      assert (LOUT : forall b k, In (b, k) (rt_live RT S) -> forall x, b <= x < b + k ->
                outside [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] x)
        by (intros bb kk Hb zz Hz; exact (live_outside_frame1 RT AF S mE fr usp (usp - 128) bb kk zz ARTE ltac:(rewrite EFR; left; reflexivity) ltac:(rewrite ESP0; ul) Hb Hz)).
      unfold entry_st.
      Time walk_to AF MST [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae7b8].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      Time frame_release_k RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xae7c0
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact Hx)
        ltac:(fun fl FLN => idtac).
      Time walk_to AF MST [(usp - 128, usp)] (@nil Z).
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      cps_stop.
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
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', r, v end.
      unfold hid in ELV, HPR. unfold new_pix8, new_pix8_live.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; assumption]| split; assumption]|].
        split; [intros a Ha _; apply AGF; exact Ha|].
        rewrite LV2. destruct HPR as [HZ|(HO & HR)]; [left; exact HZ| right]. split; [| exact HR].
        exact (pix_obj_keep _ mE _ r v _ KEEPF HO). }
      rewrite LV2, FRS2, SP2, CR2. unfold GRAY3_COST, RASTER_COST in *.
      split; [exact ELV|]. split; [reflexivity|]. split; [exact ESP0| lia]. }
    split_last_CB FRM [8%nat; 8%nat; 24%nat; 8%nat; 24%nat; 8%nat; 16%nat].
    unfold hid in HOKS.
    destruct (Z.eq_dec (p_d vs) 8) as [D8|DN8].
    2:{ (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof RERR as RE. unfold returnError_cps in RE.
    eapply cps_seq.
    { eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae754].
    cwalk [0xae754].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := 0) (v := vs); try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ => left; reflexivity
         | |- rt_live _ _ = _ => change (0 =? 0) with true; cbv iota; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold GRAY3_COST, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- ?g => idtac "LEFT:" g
         end. }
    rewrite D8 in PXS.
    unfold hid in PSCM.
    destruct PSCM as [CM0|CMX].
    2:{ (* [comment removed for export] *)
    assert (CMNZ : p_cmap vs <> 0) by (destruct CMX as ((_ & (_ & C0 & _) & _) & _); lia).
    assert (CMR : 0 < p_cmap vs < 2^64) by (destruct CMX as ((_ & (CI & C0 & _) & _) & _); pose proof (af_live_range RT AF Σ m _ _ ART0 CI) as (_ & R & _); unfold STACK_WIN in R; lia).
    clear CMX.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof RERR as RE. unfold returnError_cps in RE.
    eapply cps_seq.
    { eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae754].
    cwalk [0xae754].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := 0) (v := vs); try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ => left; reflexivity
         | |- rt_live _ _ = _ => change (0 =? 0) with true; cbv iota; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold GRAY3_COST, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- ?g => idtac "LEFT:" g
         end. }
    rewrite CM0 in PXS.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a)
      by (intros q k a Hq Ha; right; right; left; exists q, k; split; [exact Hq| lia]).
    unfold hid in POS.
    lazymatch goal with PX : rw_cells asegs ?mc pixs _, A : ART RT ?S ?mc |- cps _ (ASTA RT ?S _ _) _ =>
      assert (POS1 : pix_obj (rt_live RT S) mc pixs vs cvs)
        by (apply (pix_obj_mono (rt_live RT Σ) (rt_live RT S) mc pixs vs cvs); [solve [live_sub_tac]|];
            apply (pix_obj_agree (rt_live RT Σ) PF m mc pixs vs cvs POS AGF PML); unfold pix_cells; rewrite D8, CM0; exact PX) end.
    pose proof ADDB as AB. unfold pixAddBorderGeneral_cps in AB.
    eapply cps_seq.
    { eapply AB with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs) (val := 255); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POS1
           | |- _ \/ _ => right; reflexivity
           | |- p_d _ = 8 => exact D8
           | |- p_cmap _ = 0 => exact CM0
           | |- p_data _ <> 0 => exact SDNZ
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => unfold BORDER_COST, RASTER_COST; lres_tac
           | |- ?g => idtac "LEFT:" g
           end. }
    clear POS1.
    after_call RT AF.
    unfold new_pix8, new_pix8_live in *.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S1 end.
    lazymatch goal with H : ?r = 0 \/ _ |- _ => rename H into PB; set (pixb := r) in * end.
    lazymatch goal with H : rt_live RT S1 = _ |- _ => rename H into LV1 end.
    repeat match goal with E : rt_live RT _ = rt_live RT Σ |- _ => rewrite E in LV1 end.
    assert (FRS1 : rt_frames RT S1 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL1 : rt_sp0 RT S1 - 8388608 <= usp - 256) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    destruct (Z.eq_dec pixb 0) as [BZ|BNZ].
    { (* [comment removed for export] *)
    clear PB.
    assert (LV1z : rt_live RT S1 = rt_live RT Σ) by (rewrite LV1, BZ; reflexivity).
    clear LV1. rewrite BZ in *.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof KNULL as KN. unfold gm_null_cps in KN.
    eapply cps_seq.
    { eapply KN with (lo := lo); rt_side idtac.
      all: lazymatch goal with
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS1; cbn [length]; lia| split; [rewrite LV1z; lia| split; [lia| intros p n H; rewrite LV1z in H; exact (LVP p n H)]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    lazymatch goal with H : _ <> _ -> ?x = Z_to_bv 64 0 |- _ => rewrite (H ltac:(unfold e_pixErodeGray3h, e_pixSetBorderVal; lia)) in *; clear H end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof RMNULL as RN. unfold gm_null_cps in RN.
    eapply cps_seq.
    { eapply RN with (lo := lo); rt_side idtac.
      all: lazymatch goal with
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length];
               split; [lia| split; [lia| split; [lia| exact LVP]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    lazymatch goal with H : _ <> _ -> ?x = _ |- _ => rewrite (H ltac:(unfold e_pixRemoveBorderGeneral, e_pixSetBorderVal; lia)) in *; clear H end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    split_at FRM 6%nat PPB. split_at PPB 1%nat FRMc.
    pose proof FSH as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with A : ART RT ?S _ |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
    eapply cps_seq.
    { eapply DN with (lo := lo) (pp := fr + 64); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB8b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PPB
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length];
               split; [lia| split; [lia| split; [lia| exact LVP]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear FRSn SHB8b.
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    split_at FRMc 1%nat PPBD. split_at PPBD 1%nat FRMd.
    pose proof FSH as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with A : ART RT ?S _ |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    eapply cps_seq.
    { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB12b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PPBD
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length];
               split; [lia| split; [lia| split; [lia| exact LVP]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear FRSn SHB12b.
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae754].
    cwalk [0xae754].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := 0) (v := vs); try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ => left; reflexivity
         | |- rt_live _ _ = _ => change (0 =? 0) with true; cbv iota; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold GRAY3_COST, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- ?g => idtac "LEFT:" g
         end. }
    destruct PB as [BZ|(POB & BW & BH & BD & BDATA & BCM)]; [exfalso; exact (BNZ BZ)|].
    replace (pixb =? 0) with false in LV1 by (symmetry; apply Z.eqb_neq; exact BNZ).
    lazymatch type of POB with pix_obj _ _ _ ?vv _ => set (vb := vv) in * end.
    hide POB.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POB.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 256) bb kk xx A ltac:(rewrite FRS1; left; reflexivity) SPL1 Hb Hx)) end end.
    pose proof (pix_obj_keep _ _ _ pixb vb _ KL POB) as POB1. clear POB KL.
    pose proof K3H as KH. unfold gray3h_cps in KH.
    pose proof (pix_obj_chunks _ _ _ _ _ POB1 BDATA) as (BIN & BDIN & BRS & B0 & BD0 & BDNE).
    assert (LVP1 : forall p n, In (p, n) (rt_live RT S1) -> 0 < n)
      by (intros p n H; rewrite LV1 in H; cbn [In] in H; destruct H as [H|[H|H]];
          [injection H as <- <-; exact BRS| injection H as <- <-; lia| exact (LVP p n H)]).
    eapply cps_seq.
    { eapply KH with (lo := lo) (pixs := pixb) (vs := vb) (cvs := mkCmapv 0 0 0 0); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POB1
           | |- p_d _ = 8 => exact BD
           | |- p_cmap _ = 0 => exact BCM
           | |- p_data _ <> 0 => exact BDATA
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS1; cbn [length]; lia| split; [rewrite LV1; cbn [length]; lia| split; [lia| exact LVP1]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
      assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S2 end.
    lazymatch goal with H : pix_obj (rt_live RT S2) _ ?r ?vv _ |- _ => rename H into POBD; set (pixbd := r) in *; set (vbd := vv) in * end.
    lazymatch goal with H : rt_live RT S2 = _ |- _ => rename H into LV2 end.
    rewrite LV1 in LV2.
    lazymatch goal with H : p_w vbd = _ |- _ => rename H into BDW end.
    lazymatch goal with H : p_h vbd = _ |- _ => rename H into BDH end.
    lazymatch goal with H : p_d vbd = _ |- _ => rename H into BDD end.
    lazymatch goal with H : p_data vbd <> 0 |- _ => rename H into BDDATA end.
    lazymatch goal with H : p_cmap vbd = 0 |- _ => rename H into BDCM end.
    assert (FRS2 : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL2 : rt_sp0 RT S2 - 8388608 <= usp - 256) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    pose proof (pix_obj_chunks _ _ _ _ _ POBD BDDATA) as (BDIN2 & BDDIN2 & BDRS & BD0' & BDD0 & BDDNE).
    assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n)
      by (intros p n H; rewrite LV2 in H; cbn [In] in H; destruct H as [H|[H|[H|[H|H]]]];
          [injection H as <- <-; exact BDRS| injection H as <- <-; lia| injection H as <- <-; exact BRS| injection H as <- <-; lia| exact (LVP p n H)]).
    lazymatch goal with A : ART RT S2 ?mb |- _ =>
      pose proof (pix_obj_carry (rt_live RT S1) _ (rt_live RT S2) _ mb pixb vb _ POB1 BCM BDATA KL BIN BDIN
                    ltac:(rewrite LV2; cbn [In]; tauto) ltac:(rewrite LV2; cbn [In]; tauto)) as POB2 end.
    clear POB1 KL BIN BDIN.
    hide POB2. hide POBD.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POB2, POBD.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 256) bb kk xx A ltac:(rewrite FRS2; left; reflexivity) SPL2 Hb Hx)) end end.
    pose proof (pix_obj_keep _ _ _ pixb vb _ KL POB2) as POB3. pose proof (pix_obj_keep _ _ _ pixbd vbd _ KL POBD) as POBD3. clear POB2 POBD KL.
    unfold hid in HOKS. pose proof HOKS as (_ & HSW & HSH & _).
    pose proof RMB as RB. unfold pixRemoveBorderGeneral_cps in RB.
    eapply cps_seq.
    { eapply RB with (lo := lo) (pixs := pixbd) (vs := vbd) (cvs := mkCmapv 0 0 0 0); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POBD3
           | |- p_d _ = 8 => exact BDD
           | |- p_cmap _ = 0 => exact BDCM
           | |- p_data _ <> 0 => exact BDDATA
           | |- 12 < _ => rewrite BDW, BW; clear - HSW; lia
           | |- 10 < _ => rewrite BDH, BH; clear - HSH; lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS2; cbn [length]; lia| split; [rewrite LV2; cbn [length]; lia| split; [lia| exact LVP2]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    unfold new_pix8, new_pix8_live in *.
    lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
      assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S3 end.
    lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT S3) _ ?r ?vv _ /\ _) |- _ => rename H into PR3; set (r3 := r) in *; set (v3 := vv) in * end.
    lazymatch goal with H : rt_live RT S3 = _ |- _ => rename H into LV3 end.
    rewrite LV2 in LV3.
    set (pre3 := if r3 =? 0 then @nil (Z * Z) else [(p_data v3, rsize v3); (r3, 64)]).
    assert (LV3' : rt_live RT S3 = pre3 ++ (p_data vbd, rsize vbd) :: (pixbd, 64) :: (p_data vb, rsize vb) :: (pixb, 64) :: rt_live RT Σ)
      by (rewrite LV3; unfold pre3; destruct (r3 =? 0); reflexivity).
    clear LV3. rename LV3' into LV3.
    assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL3 : rt_sp0 RT S3 - 8388608 <= usp - 256) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    assert (P3F : r3 <> 0 -> In (r3, 64) (rt_live RT S3) /\ In (p_data v3, rsize v3) (rt_live RT S3) /\ 0 < rsize v3)
      by (intros NZ; destruct PR3 as [Z0|(PO & _ & _ & _ & DNZ & _)]; [exfalso; exact (NZ Z0)|];
          destruct (pix_obj_chunks _ _ _ _ _ PO DNZ) as (I1 & I2 & I3 & _); repeat split; assumption).
    assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n).
    { intros p n H. rewrite LV3 in H. apply List.in_app_or in H. destruct H as [H|H].
      - unfold pre3 in H. destruct (Z.eq_dec r3 0) as [Z0|NZ].
        + replace (r3 =? 0) with true in H by (symmetry; apply Z.eqb_eq; exact Z0). destruct H.
        + replace (r3 =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact NZ). destruct (P3F NZ) as (_ & _ & R3).
          cbn [In] in H. destruct H as [H|[H|[]]]; [injection H as <- <-; exact R3| injection H as <- <-; lia].
      - cbn [In] in H. destruct H as [H|[H|[H|[H|H]]]];
          [injection H as <- <-; exact BDRS| injection H as <- <-; lia| injection H as <- <-; exact BRS| injection H as <- <-; lia| exact (LVP p n H)]. }
    lazymatch goal with A : ART RT S3 ?mb |- _ => pose proof (live_nodup RT AF S3 mb A LVP3) as ND3 end. rewrite LV3 in ND3.
    lazymatch goal with A : ART RT S3 ?mb |- _ =>
      pose proof (pix_obj_carry (rt_live RT S2) _ (rt_live RT S3) _ mb pixb vb _ POB3 BCM BDATA KL
                    ltac:(rewrite LV2; cbn [In]; tauto) ltac:(rewrite LV2; cbn [In]; tauto)
                    ltac:(rewrite LV3; apply List.in_or_app; right; cbn [In]; tauto) ltac:(rewrite LV3; apply List.in_or_app; right; cbn [In]; tauto)) as POB4;
      pose proof (pix_obj_carry (rt_live RT S2) _ (rt_live RT S3) _ mb pixbd vbd _ POBD3 BDCM BDDATA KL
                    ltac:(rewrite LV2; cbn [In]; tauto) ltac:(rewrite LV2; cbn [In]; tauto)
                    ltac:(rewrite LV3; apply List.in_or_app; right; cbn [In]; tauto) ltac:(rewrite LV3; apply List.in_or_app; right; cbn [In]; tauto)) as POBD4 end.
    clear POB3 POBD3 KL.
    hide POB4. hide POBD4. hide PR3. hide ND3. hide P3F.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    split_at FRM 6%nat PPB. split_at PPB 1%nat FRMc.
    pose proof FSH as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POB4, POBD4, PR3.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 256) bb kk xx A ltac:(rewrite FRS3; left; reflexivity) SPL3 Hb Hx)) end end.
    pose proof (pix_obj_keep _ _ _ pixb vb _ KL POB4) as POB5. pose proof (pix_obj_keep _ _ _ pixbd vbd _ KL POBD4) as POBD5.
    lazymatch goal with A : ART RT S3 ?mb, K : keeps_live _ _ ?mb |- _ =>
      pose proof (pix8_opt_carry (rt_live RT S3) _ (rt_live RT S3) _ mb r3 v3 _ _ _ PR3 KL
                    ltac:(intros NZ; unfold hid in P3F; destruct (P3F NZ) as (I1 & I2 & _); repeat split; assumption)) as PR5 end.
    clear POB4 POBD4 PR3 KL.
    unfold hid in TRS, UCX.
    assert (TR12 : Forall (fun f => In (f :: 0xae8cc :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS
                   /\ Forall (fun f => In (f :: 0xae8d4 :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS)
      by (lazymatch type of TRS with Forall _ ?l => let t := eval vm_compute in l in change l with t in TRS end;
          split; [exact (Forall_inv TRS)| exact (Forall_inv (Forall_inv_tail TRS))]).
    destruct TR12 as (TR1 & TR2).
    assert (RALO : 4096 <= bv_unsigned ra).
    { pose proof traces_ra_lo' as TLO. rewrite Forall_forall in TLO. unfold DESTROY_FREE_RAS in TR1. pose proof (Forall_inv TR1) as T1.
      specialize (TLO _ T1). apply Forall_inv_tail in TLO. apply Forall_inv_tail in TLO. apply Forall_inv in TLO. exact TLO. }
    assert (LEN3 : Z.of_nat (length (rt_live RT S3)) <= Z.of_nat (length (rt_live RT Σ)) + 6)
      by (rewrite LV3; rewrite List.length_app; unfold pre3; destruct (r3 =? 0); cbn [length]; lia).
    pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
    eapply cps_seq.
    { eapply DY with (lo := lo) (pp := fr + 64) (pix := pixb) (v := vb) (cv := mkCmapv 0 0 0 0) (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRS3; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB8b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PPB
           | |- pix_obj _ _ _ _ _ => exact POB5
           | |- uctx _ _ _ _ =>
               unfold uctx; rewrite ?unsigned_lit by ul;
               apply (chain_ok_push _ (usp + -128) usp (bv_unsigned ra) (bv_unsigned s0) ras);
                 [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | lia | lia
                 | rewrite !Z_to_bv_bv_unsigned; exact FRrec2 | ];
               apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
               eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
           | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; exact TR1
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS3; cbn [length]; lia| split; [lia| split; [lia| exact LVP3]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear POB5.
    after_call RT AF.
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S4 end.
    lazymatch goal with H : rt_live RT S4 = _ |- _ => rename H into LV4 end.
    assert (FRS4 : rt_frames RT S4 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL4 : rt_sp0 RT S4 - 8388608 <= usp - 256) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT S4 ?mb |- _ =>
      assert (KL : keeps_live lv ma mb)
        by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
            exact (live_outside_local RT AF S4 mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRS4; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
    unfold hid in ND3.
    assert (LV4' : rt_live RT S4 = pre3 ++ (p_data vbd, rsize vbd) :: (pixbd, 64) :: rt_live RT Σ
                   /\ List.NoDup (map fst (pre3 ++ (p_data vbd, rsize vbd) :: (pixbd, 64) :: rt_live RT Σ))).
    { rewrite LV4, LV3.
      repeat match goal with |- context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) end.
      repeat match type of ND3 with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in ND3 end.
      replace (pre3 ++ (p_data vbd, rsize vbd) :: (pixbd, 64) :: (p_data vb, rsize vb) :: (pixb, 64) :: rt_live RT Σ)
        with ((pre3 ++ [(p_data vbd, rsize vbd); (pixbd, 64)]) ++ (p_data vb, rsize vb) :: (pixb, 64) :: rt_live RT Σ) in *
        by (rewrite <- List.app_assoc; reflexivity).
      rewrite (live_destroy_mid pixb vb _ _ _ BCM BDATA ND3).
      pose proof (nodup_remove_mid _ _ _ (nodup_remove_mid _ _ _ ND3)) as ND4.
      rewrite <- List.app_assoc in *. cbn [app] in *. split; [reflexivity| exact ND4]. }
    destruct LV4' as (LV4' & ND4).
    clear LV4 ND3. rename LV4' into LV4.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LV4; apply List.in_or_app; right; right; right; exact He| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
    unfold hid in P3F.
    assert (P4F : r3 <> 0 -> In (r3, 64) (rt_live RT S4) /\ In (p_data v3, rsize v3) (rt_live RT S4))
      by (intros NZ; rewrite LV4; unfold pre3; replace (r3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); cbn [app In]; tauto).
    assert (BD4 : In (pixbd, 64) (rt_live RT S4) /\ In (p_data vbd, rsize vbd) (rt_live RT S4))
      by (rewrite LV4; split; apply List.in_or_app; right; cbn [In]; tauto).
    lazymatch goal with A : ART RT S4 ?mb |- _ =>
      pose proof (pix_obj_carry (rt_live RT S4) _ (rt_live RT S4) _ mb pixbd vbd _ POBD5 BDCM BDDATA KL (proj1 BD4) (proj2 BD4) (proj1 BD4) (proj2 BD4)) as POBD6;
      pose proof (pix8_opt_carry (rt_live RT S4) _ (rt_live RT S4) _ mb r3 v3 _ _ _ PR5 KL
                    ltac:(intros NZ; destruct (P4F NZ) as (I1 & I2); repeat split; assumption)) as PR6 end.
    clear POBD5 PR5 KL P3F.
    assert (LVP4 : forall p n, In (p, n) (rt_live RT S4) -> 0 < n)
      by (intros p n H; apply (LVP3 p n); rewrite LV3; rewrite LV4 in H; apply List.in_app_or in H; apply List.in_or_app;
          destruct H as [H|H]; [left; exact H| right; cbn [In] in H |- *; tauto]).
    hide POBD6. hide PR6. hide ND4. hide P4F.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    split_at FRMc 1%nat PPBD. split_at PPBD 1%nat FRMd.
    pose proof FSH as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POBD6, PR6.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 256) bb kk xx A ltac:(rewrite FRS4; left; reflexivity) SPL4 Hb Hx)) end end.
    pose proof (pix_obj_keep _ _ _ pixbd vbd _ KL POBD6) as POBD7.
    lazymatch goal with K : keeps_live _ _ ?mb |- _ =>
      pose proof (pix8_opt_carry (rt_live RT S4) _ (rt_live RT S4) _ mb r3 v3 _ _ _ PR6 KL
                    ltac:(intros NZ; unfold hid in P4F; destruct (P4F NZ) as (I1 & I2); repeat split; assumption)) as PR7 end.
    clear POBD6 PR6 KL.
    assert (LEN4 : Z.of_nat (length (rt_live RT S4)) <= Z.of_nat (length (rt_live RT Σ)) + 4)
      by (rewrite LV4; rewrite List.length_app; unfold pre3; destruct (r3 =? 0); cbn [length]; lia).
    eapply cps_seq.
    { eapply DY with (lo := lo) (pp := fr + 96) (pix := pixbd) (v := vbd) (cv := mkCmapv 0 0 0 0) (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRS4; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB12b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PPBD
           | |- pix_obj _ _ _ _ _ => exact POBD7
           | |- uctx _ _ _ _ =>
               unfold uctx; rewrite ?unsigned_lit by ul;
               apply (chain_ok_push _ (usp + -128) usp (bv_unsigned ra) (bv_unsigned s0) ras);
                 [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | lia | lia
                 | rewrite !Z_to_bv_bv_unsigned; exact FRrec2 | ];
               apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
               eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
           | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; exact TR2
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS4; cbn [length]; lia| split; [lia| split; [lia| exact LVP4]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear POBD7.
    after_call RT AF.
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S5 end.
    lazymatch goal with H : rt_live RT S5 = _ |- _ => rename H into LV5 end.
    assert (FRS5 : rt_frames RT S5 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL5 : rt_sp0 RT S5 - 8388608 <= usp - 256) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT S5 ?mb |- _ =>
      assert (KL : keeps_live lv ma mb)
        by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
            exact (live_outside_local RT AF S5 mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRS5; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
    unfold hid in ND4.
    assert (LV5' : rt_live RT S5 = pre3 ++ rt_live RT Σ).
    { rewrite LV5, LV4.
      repeat match goal with |- context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) end.
      repeat match type of ND4 with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in ND4 end.
      exact (live_destroy_mid pixbd vbd _ pre3 (rt_live RT Σ) BDCM BDDATA ND4). }
    clear LV5 ND4. rename LV5' into LV5.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LV5; apply List.in_or_app; right; exact He| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
    unfold hid in P4F.
    assert (P5F : r3 <> 0 -> In (r3, 64) (rt_live RT S5) /\ In (p_data v3, rsize v3) (rt_live RT S5))
      by (intros NZ; rewrite LV5; unfold pre3; replace (r3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); cbn [app In]; tauto).
    lazymatch goal with A : ART RT S5 ?mb |- _ =>
      pose proof (pix8_opt_carry (rt_live RT S5) _ (rt_live RT S5) _ mb r3 v3 _ _ _ PR7 KL
                    ltac:(intros NZ; destruct (P5F NZ) as (I1 & I2); repeat split; assumption)) as PR8 end.
    clear PR7 KL P4F.
    hide PR8. hide P5F.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae754].
    cwalk [0xae754].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    unfold hid in PR8, P5F.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 256) bb kk xx A ltac:(rewrite FRS5; left; reflexivity) SPL5 Hb Hx));
        pose proof (pix8_opt_carry (rt_live RT S5) _ (rt_live RT S5) _ mc r3 v3 _ _ _ PR8 KL
                      ltac:(intros NZ; destruct (P5F NZ) as (I1 & I2); repeat split; assumption)) as PR9 end end.
    clear PR8 KL.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := r3) (v := v3); try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ =>
             destruct PR9 as [Z0|(PO & EW3 & EH3 & R3)]; [left; exact Z0| right];
             split; [exact PO| split; [rewrite EW3, BDW, BW; clear; lia| split; [rewrite EH3, BDH, BH; clear; lia| exact R3]]]
         | |- rt_live _ _ = _ => rewrite LV5; unfold pre3; destruct (r3 =? 0); reflexivity
         | |- rt_frames _ _ = _ => exact FRS5
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold GRAY3_COST, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST in *; lia
         | |- ?g => idtac "LEFT:" g
         end.

  -

    park_disj. carve_frame 144%nat ST.
    clear_acc.
    Time walk_to AF MST [(usp - 144, usp)] [e_stack_malloc 1%nat].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
    pose proof (proj2 FRM) as WRF0. cbn [cells_size csize Nat.add] in WRF0. change (Z.of_nat 120) with 120 in WRF0. hide WRF0.
    fframe_chunk RT AF fr 1%nat 128 pixs 64.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 144, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae618].
    gd_resync RT AF GP AGF PFS NFA.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -144) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem) (r : Z) (v : pixv)
                (r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r26 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -144) -> rw_cells asegs mE (usp + -144) cs ->
          wr_at asegs mE fr 8 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE ->
          (r = 0 \/ (pix_obj (rt_live RT S) mE r v (mkCmapv 0 0 0 0) /\ p_w v = p_w vs /\ p_h v = p_h vs /\ p_d v = 8 /\ p_data v <> 0 /\ p_cmap v = 0)) ->
          rt_live RT S = (if r =? 0 then rt_live RT Σ else (p_data v, rsize v) :: (r, 64) :: rt_live RT Σ) ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - GRAY3_COST <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          (Z_to_bv 64 r) r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 r22 r23 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) r26 s11 r28 r29 r30 r31 F' fc' 0xae754 mE))) QF) end.
    { intros S mE r v r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r26 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE HPR ELV EFR ESP0 ECR.
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
      repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S))
        by (intros e He; rewrite ELV; destruct (r =? 0); [exact He| right; right; exact He]).
      hide ELV. hide HPR.
      destruct (wr_at_rw_CB mE fr 8 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 8) with 8%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      assert (LOUT : forall b k, In (b, k) (rt_live RT S) -> forall x, b <= x < b + k ->
                outside [(usp - 144, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] x)
        by (intros bb kk Hb zz Hz; exact (live_outside_frame1 RT AF S mE fr usp (usp - 144) bb kk zz ARTE ltac:(rewrite EFR; left; reflexivity) ltac:(rewrite ESP0; ul) Hb Hz)).
      unfold entry_st.
      Time walk_to AF MST [(usp - 144, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae7b8].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      Time frame_release_k RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xae7c0
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact Hx)
        ltac:(fun fl FLN => idtac).
      Time walk_to AF MST [(usp - 144, usp)] (@nil Z).
      lazymatch goal with ST' : stk asegs _ lo (usp + -144), FR' : rw_cells asegs _ (usp + -144) _ |- _ => release_frame FR' ST' usp end.
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      cps_stop.
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
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', r, v end.
      unfold hid in ELV, HPR. unfold new_pix8, new_pix8_live.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; assumption]| split; assumption]|].
        split; [intros a Ha _; apply AGF; exact Ha|].
        rewrite LV2. destruct HPR as [HZ|(HO & HR)]; [left; exact HZ| right]. split; [| exact HR].
        exact (pix_obj_keep _ mE _ r v _ KEEPF HO). }
      rewrite LV2, FRS2, SP2, CR2. unfold GRAY3_COST, RASTER_COST in *.
      split; [exact ELV|]. split; [reflexivity|]. split; [exact ESP0| lia]. }
    split_last_CB FRM [8%nat; 8%nat; 24%nat; 8%nat; 24%nat; 8%nat; 16%nat].
    unfold hid in HOKS.
    destruct (Z.eq_dec (p_d vs) 8) as [D8|DN8].
    2:{ (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof RERR as RE. unfold returnError_cps in RE.
    eapply cps_seq.
    { eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae754].
    cwalk [0xae754].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := 0) (v := vs); try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ => left; reflexivity
         | |- rt_live _ _ = _ => change (0 =? 0) with true; cbv iota; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold GRAY3_COST, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- ?g => idtac "LEFT:" g
         end. }
    rewrite D8 in PXS.
    unfold hid in PSCM.
    destruct PSCM as [CM0|CMX].
    2:{ (* [comment removed for export] *)
    assert (CMNZ : p_cmap vs <> 0) by (destruct CMX as ((_ & (_ & C0 & _) & _) & _); lia).
    assert (CMR : 0 < p_cmap vs < 2^64) by (destruct CMX as ((_ & (CI & C0 & _) & _) & _); pose proof (af_live_range RT AF Σ m _ _ ART0 CI) as (_ & R & _); unfold STACK_WIN in R; lia).
    clear CMX.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof RERR as RE. unfold returnError_cps in RE.
    eapply cps_seq.
    { eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae754].
    cwalk [0xae754].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := 0) (v := vs); try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ => left; reflexivity
         | |- rt_live _ _ = _ => change (0 =? 0) with true; cbv iota; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold GRAY3_COST, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- ?g => idtac "LEFT:" g
         end. }
    rewrite CM0 in PXS.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a)
      by (intros q k a Hq Ha; right; right; left; exists q, k; split; [exact Hq| lia]).
    unfold hid in POS.
    lazymatch goal with PX : rw_cells asegs ?mc pixs _, A : ART RT ?S ?mc |- cps _ (ASTA RT ?S _ _) _ =>
      assert (POS1 : pix_obj (rt_live RT S) mc pixs vs cvs)
        by (apply (pix_obj_mono (rt_live RT Σ) (rt_live RT S) mc pixs vs cvs); [solve [live_sub_tac]|];
            apply (pix_obj_agree (rt_live RT Σ) PF m mc pixs vs cvs POS AGF PML); unfold pix_cells; rewrite D8, CM0; exact PX) end.
    pose proof ADDB as AB. unfold pixAddBorderGeneral_cps in AB.
    eapply cps_seq.
    { eapply AB with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs) (val := 255); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POS1
           | |- _ \/ _ => right; reflexivity
           | |- p_d _ = 8 => exact D8
           | |- p_cmap _ = 0 => exact CM0
           | |- p_data _ <> 0 => exact SDNZ
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => unfold BORDER_COST, RASTER_COST; lres_tac
           | |- ?g => idtac "LEFT:" g
           end. }
    clear POS1.
    after_call RT AF.
    unfold new_pix8, new_pix8_live in *.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S1 end.
    lazymatch goal with H : ?r = 0 \/ _ |- _ => rename H into PB; set (pixb := r) in * end.
    lazymatch goal with H : rt_live RT S1 = _ |- _ => rename H into LV1 end.
    repeat match goal with E : rt_live RT _ = rt_live RT Σ |- _ => rewrite E in LV1 end.
    assert (FRS1 : rt_frames RT S1 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL1 : rt_sp0 RT S1 - 8388608 <= usp - 272) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    destruct (Z.eq_dec pixb 0) as [BZ|BNZ].
    { (* [comment removed for export] *)
    clear PB.
    assert (LV1z : rt_live RT S1 = rt_live RT Σ) by (rewrite LV1, BZ; reflexivity).
    clear LV1. rewrite BZ in *.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof KNULL as KN. unfold gm_null_cps in KN.
    eapply cps_seq.
    { eapply KN with (lo := lo); rt_side idtac.
      all: lazymatch goal with
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS1; cbn [length]; lia| split; [rewrite LV1z; lia| split; [lia| intros p n H; rewrite LV1z in H; exact (LVP p n H)]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    lazymatch goal with H : _ <> _ -> ?x = Z_to_bv 64 0 |- _ => rewrite (H ltac:(unfold e_pixErodeGray3h, e_pixSetBorderVal; lia)) in *; clear H end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof RMNULL as RN. unfold gm_null_cps in RN.
    eapply cps_seq.
    { eapply RN with (lo := lo); rt_side idtac.
      all: lazymatch goal with
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length];
               split; [lia| split; [lia| split; [lia| exact LVP]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    lazymatch goal with H : _ <> _ -> ?x = _ |- _ => rewrite (H ltac:(unfold e_pixRemoveBorderGeneral, e_pixSetBorderVal; lia)) in *; clear H end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    split_at FRM 6%nat PPB. split_at PPB 1%nat FRMc.
    pose proof FSH as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with A : ART RT ?S _ |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
    eapply cps_seq.
    { eapply DN with (lo := lo) (pp := fr + 64); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB8b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PPB
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length];
               split; [lia| split; [lia| split; [lia| exact LVP]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear FRSn SHB8b.
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    split_at FRMc 1%nat PPBD. split_at PPBD 1%nat FRMd.
    pose proof FSH as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with A : ART RT ?S _ |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    eapply cps_seq.
    { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB12b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PPBD
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length];
               split; [lia| split; [lia| split; [lia| exact LVP]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear FRSn SHB12b.
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae754].
    cwalk [0xae754].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := 0) (v := vs); try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ => left; reflexivity
         | |- rt_live _ _ = _ => change (0 =? 0) with true; cbv iota; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold GRAY3_COST, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- ?g => idtac "LEFT:" g
         end. }
    destruct PB as [BZ|(POB & BW & BH & BD & BDATA & BCM)]; [exfalso; exact (BNZ BZ)|].
    replace (pixb =? 0) with false in LV1 by (symmetry; apply Z.eqb_neq; exact BNZ).
    lazymatch type of POB with pix_obj _ _ _ ?vv _ => set (vb := vv) in * end.
    hide POB.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POB.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 272) bb kk xx A ltac:(rewrite FRS1; left; reflexivity) SPL1 Hb Hx)) end end.
    pose proof (pix_obj_keep _ _ _ pixb vb _ KL POB) as POB1. clear POB KL.
    pose proof K3H as KH. unfold gray3h_cps in KH.
    pose proof (pix_obj_chunks _ _ _ _ _ POB1 BDATA) as (BIN & BDIN & BRS & B0 & BD0 & BDNE).
    assert (LVP1 : forall p n, In (p, n) (rt_live RT S1) -> 0 < n)
      by (intros p n H; rewrite LV1 in H; cbn [In] in H; destruct H as [H|[H|H]];
          [injection H as <- <-; exact BRS| injection H as <- <-; lia| exact (LVP p n H)]).
    eapply cps_seq.
    { eapply KH with (lo := lo) (pixs := pixb) (vs := vb) (cvs := mkCmapv 0 0 0 0); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POB1
           | |- p_d _ = 8 => exact BD
           | |- p_cmap _ = 0 => exact BCM
           | |- p_data _ <> 0 => exact BDATA
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS1; cbn [length]; lia| split; [rewrite LV1; cbn [length]; lia| split; [lia| exact LVP1]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
      assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S2 end.
    lazymatch goal with H : pix_obj (rt_live RT S2) _ ?r ?vv _ |- _ => rename H into POBD; set (pixbd := r) in *; set (vbd := vv) in * end.
    lazymatch goal with H : rt_live RT S2 = _ |- _ => rename H into LV2 end.
    rewrite LV1 in LV2.
    lazymatch goal with H : p_w vbd = _ |- _ => rename H into BDW end.
    lazymatch goal with H : p_h vbd = _ |- _ => rename H into BDH end.
    lazymatch goal with H : p_d vbd = _ |- _ => rename H into BDD end.
    lazymatch goal with H : p_data vbd <> 0 |- _ => rename H into BDDATA end.
    lazymatch goal with H : p_cmap vbd = 0 |- _ => rename H into BDCM end.
    assert (FRS2 : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL2 : rt_sp0 RT S2 - 8388608 <= usp - 272) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    pose proof (pix_obj_chunks _ _ _ _ _ POBD BDDATA) as (BDIN2 & BDDIN2 & BDRS & BD0' & BDD0 & BDDNE).
    assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n)
      by (intros p n H; rewrite LV2 in H; cbn [In] in H; destruct H as [H|[H|[H|[H|H]]]];
          [injection H as <- <-; exact BDRS| injection H as <- <-; lia| injection H as <- <-; exact BRS| injection H as <- <-; lia| exact (LVP p n H)]).
    lazymatch goal with A : ART RT S2 ?mb |- _ =>
      pose proof (pix_obj_carry (rt_live RT S1) _ (rt_live RT S2) _ mb pixb vb _ POB1 BCM BDATA KL BIN BDIN
                    ltac:(rewrite LV2; cbn [In]; tauto) ltac:(rewrite LV2; cbn [In]; tauto)) as POB2 end.
    clear POB1 KL BIN BDIN.
    hide POB2. hide POBD.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POB2, POBD.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 272) bb kk xx A ltac:(rewrite FRS2; left; reflexivity) SPL2 Hb Hx)) end end.
    pose proof (pix_obj_keep _ _ _ pixb vb _ KL POB2) as POB3. pose proof (pix_obj_keep _ _ _ pixbd vbd _ KL POBD) as POBD3. clear POB2 POBD KL.
    unfold hid in HOKS. pose proof HOKS as (_ & HSW & HSH & _).
    pose proof RMB as RB. unfold pixRemoveBorderGeneral_cps in RB.
    eapply cps_seq.
    { eapply RB with (lo := lo) (pixs := pixbd) (vs := vbd) (cvs := mkCmapv 0 0 0 0); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POBD3
           | |- p_d _ = 8 => exact BDD
           | |- p_cmap _ = 0 => exact BDCM
           | |- p_data _ <> 0 => exact BDDATA
           | |- 12 < _ => rewrite BDW, BW; clear - HSW; lia
           | |- 10 < _ => rewrite BDH, BH; clear - HSH; lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS2; cbn [length]; lia| split; [rewrite LV2; cbn [length]; lia| split; [lia| exact LVP2]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    unfold new_pix8, new_pix8_live in *.
    lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
      assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S3 end.
    lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT S3) _ ?r ?vv _ /\ _) |- _ => rename H into PR3; set (r3 := r) in *; set (v3 := vv) in * end.
    lazymatch goal with H : rt_live RT S3 = _ |- _ => rename H into LV3 end.
    rewrite LV2 in LV3.
    set (pre3 := if r3 =? 0 then @nil (Z * Z) else [(p_data v3, rsize v3); (r3, 64)]).
    assert (LV3' : rt_live RT S3 = pre3 ++ (p_data vbd, rsize vbd) :: (pixbd, 64) :: (p_data vb, rsize vb) :: (pixb, 64) :: rt_live RT Σ)
      by (rewrite LV3; unfold pre3; destruct (r3 =? 0); reflexivity).
    clear LV3. rename LV3' into LV3.
    assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL3 : rt_sp0 RT S3 - 8388608 <= usp - 272) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    assert (P3F : r3 <> 0 -> In (r3, 64) (rt_live RT S3) /\ In (p_data v3, rsize v3) (rt_live RT S3) /\ 0 < rsize v3)
      by (intros NZ; destruct PR3 as [Z0|(PO & _ & _ & _ & DNZ & _)]; [exfalso; exact (NZ Z0)|];
          destruct (pix_obj_chunks _ _ _ _ _ PO DNZ) as (I1 & I2 & I3 & _); repeat split; assumption).
    assert (LVP3 : forall p n, In (p, n) (rt_live RT S3) -> 0 < n).
    { intros p n H. rewrite LV3 in H. apply List.in_app_or in H. destruct H as [H|H].
      - unfold pre3 in H. destruct (Z.eq_dec r3 0) as [Z0|NZ].
        + replace (r3 =? 0) with true in H by (symmetry; apply Z.eqb_eq; exact Z0). destruct H.
        + replace (r3 =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact NZ). destruct (P3F NZ) as (_ & _ & R3).
          cbn [In] in H. destruct H as [H|[H|[]]]; [injection H as <- <-; exact R3| injection H as <- <-; lia].
      - cbn [In] in H. destruct H as [H|[H|[H|[H|H]]]];
          [injection H as <- <-; exact BDRS| injection H as <- <-; lia| injection H as <- <-; exact BRS| injection H as <- <-; lia| exact (LVP p n H)]. }
    lazymatch goal with A : ART RT S3 ?mb |- _ => pose proof (live_nodup RT AF S3 mb A LVP3) as ND3 end. rewrite LV3 in ND3.
    lazymatch goal with A : ART RT S3 ?mb |- _ =>
      pose proof (pix_obj_carry (rt_live RT S2) _ (rt_live RT S3) _ mb pixb vb _ POB3 BCM BDATA KL
                    ltac:(rewrite LV2; cbn [In]; tauto) ltac:(rewrite LV2; cbn [In]; tauto)
                    ltac:(rewrite LV3; apply List.in_or_app; right; cbn [In]; tauto) ltac:(rewrite LV3; apply List.in_or_app; right; cbn [In]; tauto)) as POB4;
      pose proof (pix_obj_carry (rt_live RT S2) _ (rt_live RT S3) _ mb pixbd vbd _ POBD3 BDCM BDDATA KL
                    ltac:(rewrite LV2; cbn [In]; tauto) ltac:(rewrite LV2; cbn [In]; tauto)
                    ltac:(rewrite LV3; apply List.in_or_app; right; cbn [In]; tauto) ltac:(rewrite LV3; apply List.in_or_app; right; cbn [In]; tauto)) as POBD4 end.
    clear POB3 POBD3 KL.
    hide POB4. hide POBD4. hide PR3. hide ND3. hide P3F.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    split_at FRM 6%nat PPB. split_at PPB 1%nat FRMc.
    pose proof FSH as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POB4, POBD4, PR3.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 272) bb kk xx A ltac:(rewrite FRS3; left; reflexivity) SPL3 Hb Hx)) end end.
    pose proof (pix_obj_keep _ _ _ pixb vb _ KL POB4) as POB5. pose proof (pix_obj_keep _ _ _ pixbd vbd _ KL POBD4) as POBD5.
    lazymatch goal with A : ART RT S3 ?mb, K : keeps_live _ _ ?mb |- _ =>
      pose proof (pix8_opt_carry (rt_live RT S3) _ (rt_live RT S3) _ mb r3 v3 _ _ _ PR3 KL
                    ltac:(intros NZ; unfold hid in P3F; destruct (P3F NZ) as (I1 & I2 & _); repeat split; assumption)) as PR5 end.
    clear POB4 POBD4 PR3 KL.
    unfold hid in TRS, UCX.
    assert (TR12 : Forall (fun f => In (f :: 0xae8cc :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS
                   /\ Forall (fun f => In (f :: 0xae8d4 :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS)
      by (lazymatch type of TRS with Forall _ ?l => let t := eval vm_compute in l in change l with t in TRS end;
          split; [exact (Forall_inv TRS)| exact (Forall_inv (Forall_inv_tail TRS))]).
    destruct TR12 as (TR1 & TR2).
    assert (RALO : 4096 <= bv_unsigned ra).
    { pose proof traces_ra_lo' as TLO. rewrite Forall_forall in TLO. unfold DESTROY_FREE_RAS in TR1. pose proof (Forall_inv TR1) as T1.
      specialize (TLO _ T1). apply Forall_inv_tail in TLO. apply Forall_inv_tail in TLO. apply Forall_inv in TLO. exact TLO. }
    assert (LEN3 : Z.of_nat (length (rt_live RT S3)) <= Z.of_nat (length (rt_live RT Σ)) + 6)
      by (rewrite LV3; rewrite List.length_app; unfold pre3; destruct (r3 =? 0); cbn [length]; lia).
    pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
    eapply cps_seq.
    { eapply DY with (lo := lo) (pp := fr + 64) (pix := pixb) (v := vb) (cv := mkCmapv 0 0 0 0) (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRS3; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB8b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PPB
           | |- pix_obj _ _ _ _ _ => exact POB5
           | |- uctx _ _ _ _ =>
               unfold uctx; rewrite ?unsigned_lit by ul;
               apply (chain_ok_push _ (usp + -144) usp (bv_unsigned ra) (bv_unsigned s0) ras);
                 [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | lia | lia
                 | rewrite !Z_to_bv_bv_unsigned; exact FRrec2 | ];
               apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
               eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
           | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; exact TR1
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS3; cbn [length]; lia| split; [lia| split; [lia| exact LVP3]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear POB5.
    after_call RT AF.
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S4 end.
    lazymatch goal with H : rt_live RT S4 = _ |- _ => rename H into LV4 end.
    assert (FRS4 : rt_frames RT S4 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL4 : rt_sp0 RT S4 - 8388608 <= usp - 272) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT S4 ?mb |- _ =>
      assert (KL : keeps_live lv ma mb)
        by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
            exact (live_outside_local RT AF S4 mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRS4; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
    unfold hid in ND3.
    assert (LV4' : rt_live RT S4 = pre3 ++ (p_data vbd, rsize vbd) :: (pixbd, 64) :: rt_live RT Σ
                   /\ List.NoDup (map fst (pre3 ++ (p_data vbd, rsize vbd) :: (pixbd, 64) :: rt_live RT Σ))).
    { rewrite LV4, LV3.
      repeat match goal with |- context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) end.
      repeat match type of ND3 with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in ND3 end.
      replace (pre3 ++ (p_data vbd, rsize vbd) :: (pixbd, 64) :: (p_data vb, rsize vb) :: (pixb, 64) :: rt_live RT Σ)
        with ((pre3 ++ [(p_data vbd, rsize vbd); (pixbd, 64)]) ++ (p_data vb, rsize vb) :: (pixb, 64) :: rt_live RT Σ) in *
        by (rewrite <- List.app_assoc; reflexivity).
      rewrite (live_destroy_mid pixb vb _ _ _ BCM BDATA ND3).
      pose proof (nodup_remove_mid _ _ _ (nodup_remove_mid _ _ _ ND3)) as ND4.
      rewrite <- List.app_assoc in *. cbn [app] in *. split; [reflexivity| exact ND4]. }
    destruct LV4' as (LV4' & ND4).
    clear LV4 ND3. rename LV4' into LV4.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LV4; apply List.in_or_app; right; right; right; exact He| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
    unfold hid in P3F.
    assert (P4F : r3 <> 0 -> In (r3, 64) (rt_live RT S4) /\ In (p_data v3, rsize v3) (rt_live RT S4))
      by (intros NZ; rewrite LV4; unfold pre3; replace (r3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); cbn [app In]; tauto).
    assert (BD4 : In (pixbd, 64) (rt_live RT S4) /\ In (p_data vbd, rsize vbd) (rt_live RT S4))
      by (rewrite LV4; split; apply List.in_or_app; right; cbn [In]; tauto).
    lazymatch goal with A : ART RT S4 ?mb |- _ =>
      pose proof (pix_obj_carry (rt_live RT S4) _ (rt_live RT S4) _ mb pixbd vbd _ POBD5 BDCM BDDATA KL (proj1 BD4) (proj2 BD4) (proj1 BD4) (proj2 BD4)) as POBD6;
      pose proof (pix8_opt_carry (rt_live RT S4) _ (rt_live RT S4) _ mb r3 v3 _ _ _ PR5 KL
                    ltac:(intros NZ; destruct (P4F NZ) as (I1 & I2); repeat split; assumption)) as PR6 end.
    clear POBD5 PR5 KL P3F.
    assert (LVP4 : forall p n, In (p, n) (rt_live RT S4) -> 0 < n)
      by (intros p n H; apply (LVP3 p n); rewrite LV3; rewrite LV4 in H; apply List.in_app_or in H; apply List.in_or_app;
          destruct H as [H|H]; [left; exact H| right; cbn [In] in H |- *; tauto]).
    hide POBD6. hide PR6. hide ND4. hide P4F.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    cwalk [0x9097c; 0x96bd8; 0xae93c; 0x97110; 0x918bc; 0x935f4; 0xaf2cc].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    split_at FRMc 1%nat PPBD. split_at PPBD 1%nat FRMd.
    pose proof FSH as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POBD6, PR6.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 272) bb kk xx A ltac:(rewrite FRS4; left; reflexivity) SPL4 Hb Hx)) end end.
    pose proof (pix_obj_keep _ _ _ pixbd vbd _ KL POBD6) as POBD7.
    lazymatch goal with K : keeps_live _ _ ?mb |- _ =>
      pose proof (pix8_opt_carry (rt_live RT S4) _ (rt_live RT S4) _ mb r3 v3 _ _ _ PR6 KL
                    ltac:(intros NZ; unfold hid in P4F; destruct (P4F NZ) as (I1 & I2); repeat split; assumption)) as PR7 end.
    clear POBD6 PR6 KL.
    assert (LEN4 : Z.of_nat (length (rt_live RT S4)) <= Z.of_nat (length (rt_live RT Σ)) + 4)
      by (rewrite LV4; rewrite List.length_app; unfold pre3; destruct (r3 =? 0); cbn [length]; lia).
    eapply cps_seq.
    { eapply DY with (lo := lo) (pp := fr + 96) (pix := pixbd) (v := vbd) (cv := mkCmapv 0 0 0 0) (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRS4; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB12b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PPBD
           | |- pix_obj _ _ _ _ _ => exact POBD7
           | |- uctx _ _ _ _ =>
               unfold uctx; rewrite ?unsigned_lit by ul;
               apply (chain_ok_push _ (usp + -144) usp (bv_unsigned ra) (bv_unsigned s0) ras);
                 [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | lia | lia
                 | rewrite !Z_to_bv_bv_unsigned; exact FRrec2 | ];
               apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
               eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
           | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; exact TR2
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS4; cbn [length]; lia| split; [lia| split; [lia| exact LVP4]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear POBD7.
    after_call RT AF.
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S5 end.
    lazymatch goal with H : rt_live RT S5 = _ |- _ => rename H into LV5 end.
    assert (FRS5 : rt_frames RT S5 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
    assert (SPL5 : rt_sp0 RT S5 - 8388608 <= usp - 272) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
    lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT S5 ?mb |- _ =>
      assert (KL : keeps_live lv ma mb)
        by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
            exact (live_outside_local RT AF S5 mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRS5; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
    unfold hid in ND4.
    assert (LV5' : rt_live RT S5 = pre3 ++ rt_live RT Σ).
    { rewrite LV5, LV4.
      repeat match goal with |- context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) end.
      repeat match type of ND4 with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in ND4 end.
      exact (live_destroy_mid pixbd vbd _ pre3 (rt_live RT Σ) BDCM BDDATA ND4). }
    clear LV5 ND4. rename LV5' into LV5.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LV5; apply List.in_or_app; right; exact He| solve [frames_sub_tac]| lia]|
                                    cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
    unfold hid in P4F.
    assert (P5F : r3 <> 0 -> In (r3, 64) (rt_live RT S5) /\ In (p_data v3, rsize v3) (rt_live RT S5))
      by (intros NZ; rewrite LV5; unfold pre3; replace (r3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); cbn [app In]; tauto).
    lazymatch goal with A : ART RT S5 ?mb |- _ =>
      pose proof (pix8_opt_carry (rt_live RT S5) _ (rt_live RT S5) _ mb r3 v3 _ _ _ PR7 KL
                    ltac:(intros NZ; destruct (P5F NZ) as (I1 & I2); repeat split; assumption)) as PR8 end.
    clear PR7 KL P4F.
    hide PR8. hide P5F.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    Time walk_to AF MST [(usp - 272, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xae754].
    cwalk [0xae754].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    unfold hid in PR8, P5F.
    lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
        assert (KL : keeps_live (rt_live RT S) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame1 RT AF S mm fr usp (usp - 272) bb kk xx A ltac:(rewrite FRS5; left; reflexivity) SPL5 Hb Hx));
        pose proof (pix8_opt_carry (rt_live RT S5) _ (rt_live RT S5) _ mc r3 v3 _ _ _ PR8 KL
                      ltac:(intros NZ; destruct (P5F NZ) as (I1 & I2); repeat split; assumption)) as PR9 end end.
    clear PR8 KL.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := r3) (v := v3); try eassumption.
    all: lazymatch goal with
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ =>
             destruct PR9 as [Z0|(PO & EW3 & EH3 & R3)]; [left; exact Z0| right];
             split; [exact PO| split; [rewrite EW3, BDW, BW; clear; lia| split; [rewrite EH3, BDH, BH; clear; lia| exact R3]]]
         | |- rt_live _ _ = _ => rewrite LV5; unfold pre3; destruct (r3 =? 0); reflexivity
         | |- rt_frames _ _ = _ => exact FRS5
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => unfold GRAY3_COST, GRAY3H_COST, TEMPLATE_COST, BORDER_COST, RASTER_COST in *; lia
         | |- ?g => idtac "LEFT:" g
         end.

Qed.
End GE.

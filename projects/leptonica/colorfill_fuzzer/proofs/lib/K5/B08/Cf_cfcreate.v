(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf LeptL_kit Lept_objkit Lept_deserkit Cf_iface Cf_kit LeptB_guard LeptB_guard2 LeptB_guard3 D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac cfc_stops := constr:([0x48a00; 0x8da88; 0x8ee20; 0x8eb38; 0x8f30c; 0x5edec; 0x911c0; 0x8e240; 0x8dd78; 0x8e708; 0x93f94]).

Ltac cfc_ivt :=
  cbn [ivls_client]; let zz := fresh "zz" in let Hzz := fresh "Hzz" in
  split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]].
Ltac cfc_pft PFS NFA Hx :=
  let N1 := fresh "N1" in let N2 := fresh "N2" in
  cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Ltac cfc_refresh RT AF GP :=
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; park_disj.
(* [comment removed for export] *)
Ltac cfc_to_epi RT AF AGF PFS NFA A :=
  cps_stop; art_now RT AF ltac:(cfc_ivt);
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => cfc_pft PFS NFA Hx) end;
  lazymatch goal with FRx : rw_cells asegs _ A _ |- _ => merge_low FRx 13%nat end;
  to_entry.
(* [comment removed for export] *)
Ltac cfc_epi_side FRM FSH AGF :=
  lazymatch goal with
  | |- ART _ _ _ => eassumption
  | |- mem_inv _ _ => assumption
  | |- stk _ _ _ _ => eassumption
  | |- rw_cells _ _ _ (CB _ _ :: _) => eassumption
  | |- wr_at asegs _ _ 56 => exact (proj2 FRM)
  | |- wr_at asegs _ _ 8 => exact (proj2 FSH)
  | |- LIBH _ => assumption
  | |- io_ssp _ => assumption
  | |- agree_on _ _ _ => exact AGF
  | |- wmono _ ?m0 ?mf => lazymatch goal with WMx : wmono asegs m0 mf |- _ => exact WMx end
  | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
  | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
  | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
  | |- forall e, In e _ -> In e _ => first [solve [live_sub_tac] | solve [live_add_tac]]
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac cfc_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH PXC usp lo A W :=
  at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx);
  (let RE := fresh "RE" in pose proof RERR as RE; unfold returnError_cps in RE;
   eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |]);
  after_call RT AF;
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]);
  cfc_refresh RT AF GP;
  (let st := cfc_stops in walk_to AF MST W st);
  cfc_to_epi RT AF AGF PFS NFA A;
  eapply EPI with (cfr := 0) (c := mkCfv 0 0 0 0 0 0 0 0 0 0 0 0 0 0);
  cfc_epi_side FRM FSH AGF;
  lazymatch goal with
  | |- _ \/ _ => left; split; [reflexivity| split; [unfold pix_cells_rc; exact PXC|
                   repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity]]
  end.

(* [comment removed for export] *)
Ltac cfc_uctx ra s0 ras m UCTX AGF RA4096 SPA usp A :=
  unfold uctx; rewrite ?unsigned_lit by lia;
  lazymatch goal with FRx : rw_cells asegs ?mc A _ |- chain_ok ?mc _ _ _ =>
    let FRc := fresh "FRc" in let REC := fresh "REC" in
    pose proof FRx as FRc; split_before FRc (C8 s0) REC; clear FRc;
    replace (C8 s0) with (C8 (Z_to_bv 64 (bv_unsigned s0))) in REC by (rewrite Z_to_bv_bv_unsigned; reflexivity);
    replace (C8 ra) with (C8 (Z_to_bv 64 (bv_unsigned ra))) in REC by (rewrite Z_to_bv_bv_unsigned; reflexivity);
    apply (chain_ok_push mc _ usp (bv_unsigned ra) (bv_unsigned s0) ras);
    [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | exact RA4096 | apply bv_unsigned_in_range
    | exact REC
    | apply (chain_ok_keep ras m mc usp (bv_unsigned s0) UCTX); eapply agree_sub; [exact AGF|];
      let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbv beta;
      split; [left; exact Hx| cbn [outside]; unfold USTACK_TOP in Hx; split; [lia| exact I]] ] end.

(* [comment removed for export] *)
Ltac cfc_keep_mu RT Σ fr cf LOUTG H :=
  lazymatch goal with MUx : munch _ ?ma ?mc, A : ART RT ?S ?ma |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let FS := fresh "FS" in let SS := fresh "SS" in
    assert (FS : rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames _ _ = _ |- _ => rewrite E end; reflexivity);
    assert (SS : rt_sp0 RT S = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity);
    obj_keep_mu RT S H MUx ltac:(fun Ha =>
      let O1 := fresh "O" in let O2 := fresh "O" in let O3 := fresh "O" in
      lazymatch type of Ha with ?q <= _ < ?q + ?k =>
        destruct (LOUTG S ma A FS SS q k ltac:(solve [in_live_tac]) _ Ha) as (O1 & O2 & O3);
        cbn [outside]; repeat split; try assumption; try exact I;
        repeat match goal with AP : apartp q _ cf 88 |- _ => unfold apartp in AP end;
        let HH := fresh "HH" in intro HH; lia end);
    clear FS SS end.
(* [comment removed for export] *)
Ltac cfc_ivt_cf cf :=
  cbn [ivls_client]; let zz := fresh "zz" in let Hzz := fresh "Hzz" in
  split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
  split; [intros zz Hzz; right; right; left; exists cf, 88; split; [solve [in_live_tac]| lia]| exact I]]]].
Ltac cfc_pft_cf PFS NFA NCCF Hx :=
  let N1 := fresh "N1" in let N2 := fresh "N2" in let N3 := fresh "N3" in
  cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; pose proof (NCCF _ Hx) as N3; unfold shad, SHB in *;
  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].

Section CFCREATE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis BAC : boxaCreate_cps RT.
Hypothesis BC : boxCreate_cps RT.
Hypothesis BAB : boxaAddBox_cps RT.
Hypothesis PCL : pixClone_cps RT.
Hypothesis NAC : numaaCreate_cps RT.
Hypothesis DAC : l_dnaaCreate_cps RT.
Hypothesis PAC : pixaCreate_cps RT.

Theorem l_colorfillCreate_ok : l_colorfillCreate_cps RT.
Proof using AF GP RERR BAC BC BAB PCL NAC DAC PAC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> -> -> POBJ UCTX TRS ENV RES.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_colorfillCreate, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold uctx in UCTX.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  assert (RA4096 : 4096 <= bv_unsigned ra < 2^64).
  { pose proof client_traces_wf as W. rewrite forallb_forall in W. specialize (W _ (Forall_inv TRS)).
    apply andb_prop in W. destruct W as [_ W]. cbn [forallb] in W.
    apply andb_prop in W. destruct W as [_ W]. apply andb_prop in W. destruct W as [W _].
    apply andb_prop in W. destruct W as [W _]. apply andb_prop in W. destruct W as [W1 W2].
    apply Z.leb_le in W1. apply Z.ltb_lt in W2. lia. }
  park RA4096.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof POBJ as (PXC & PCH & (HD1 & HW1 & HH1 & _) & _). pose proof PCH as (PIN & PX0 & PX16 & _).
  unfold pix_cells in PXC.
  chunk_facts RT AF GP pix 64.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(pix + 20, pix + 24)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros xa [HXa _]. destruct (aclient_split RT AF Σ m usp xa ART0 HXa) as [HXS|HXS]; [left; exact HXS| right; unfold STACK_WIN in HXS; lia]. }
  assert (AL : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - (* [comment removed for export] *)
    carve_frame 192%nat ST.
    walk_to AF MST [(usp - 192, usp)] [0x48a00].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact (proj1 Ha)).
    fframe_chunk RT AF fr 0%nat 64 pix 64. norm_fshadow.
    assert (LOUTG : forall S0 mS, ART RT S0 mS -> rt_frames RT S0 = (fr, 0%nat) :: rt_frames RT Σ -> rt_sp0 RT S0 = rt_sp0 RT Σ ->
              forall bb kk, In (bb, kk) (rt_live RT S0) -> forall zz, bb <= zz < bb + kk ->
              ~ (usp - 256 <= zz < usp) /\ ~ (fr <= zz < fr + 56) /\ ~ (fr / 8 + 2147450880 <= zz < fr / 8 + 2147450880 + 8)).
    { intros S0 mS AS FS SS bb kk Hb zz Hz.
      pose proof (af_live_range RT AF S0 mS bb kk AS Hb) as LR.
      pose proof (af_frames_range RT AF S0 mS fr 0%nat AS ltac:(rewrite FS; left; reflexivity)) as (_ & _ & _ & D1). specialize (D1 bb kk Hb).
      pose proof (af_fshadow_apart RT AF S0 mS fr 0%nat AS ltac:(rewrite FS; left; reflexivity)) as (D2 & _). specialize (D2 bb kk Hb).
      change (fs_size 0) with 64 in D1, D2. unfold shad, SHB in D2. rewrite SS in LR. unfold STACK_WIN in LR.
      clear - LR D1 D2 Hz LOW LOR. repeat split; intro; first [lia | Z.div_mod_to_equations; lia]. }
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    (* [comment removed for export] *)
    clear_acc.
    walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x93c7c].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => let N1 := fresh "N1" in let N2 := fresh "N2" in
                                        cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP.
    (* [comment removed for export] *)
    split_last_CB FRM [8; 4; 12; 4; 4]%nat.
    lazymatch type of FRM with rw_cells asegs ?mm fr (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 4 ?b :: ?post) =>
      apply (cb4_c4_in mm fr [c0; c1; c2; c3] post b) in FRM; destruct FRM as (wx & FRM); cbn [app] in FRM end.
    lazymatch type of FRM with rw_cells asegs ?mm fr (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: CB 4 ?b :: ?post) =>
      apply (cb4_c4_in mm fr [c0; c1; c2; c3; c4; c5] post b) in FRM; destruct FRM as (hx & FRM); cbn [app] in FRM end.
    local_acc FSH fr 4%nat 32 FR64 ACW. local_acc FSH fr 6%nat 48 FR64 ACH.
    (* [comment removed for export] *)
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    assert (EPI : forall (S : rts RT) (mE : mem) (cfr : Z) (c : cfv) (jE : list byte)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r21 r23 r24 r25 r26 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -192) ->
          rw_cells asegs mE (usp + -192)
            (CB 88 jE :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
          wr_at asegs mE fr 56 -> wr_at asegs mE (fr / 8 + 2147450880) 8 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE -> wmono asegs m mE ->
          rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 2 <= rt_credit RT S ->
          (forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) ->
          ((cfr = 0 /\ rw_cells asegs mE pix (pix_cells_rc v 1) /\ rt_live RT S = rt_live RT Σ)
           \/ (cfr <> 0 /\ cf_obj (rt_live RT S) mE cfr c /\ cf_pix c = pix /\ rw_cells asegs mE pix (pix_cells_rc v 2)
               /\ rt_live RT S = cf_live cfr c (rt_live RT Σ))) ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) r20 r21
                                          (Z_to_bv 64 cfr) r23 r24 r25 r26 (Z_to_bv 64 fr) r28 r29 r30 r31 F' fc' 0x93f94 mE))) QF).
    { intros S mE cfr c jE r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r21 r23 r24 r25 r26 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE WME EFR ESP0 ECR LSUB PAY.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => clear H end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 56 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 8 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 56) with 56%nat in FRME. change (Z.to_nat 8) with 8%nat in FSHE.
      (* [comment removed for export] *)
      assert (LOUT : forall b k, In (b, k) (rt_live RT S) -> forall x, b <= x < b + k ->
                outside [(usp - 192, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] x).
      { intros bb kk Hb zz Hz.
        pose proof (af_live_range RT AF S mE bb kk ARTE Hb) as LR.
        pose proof (af_frames_range RT AF S mE fr 0%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (_ & _ & _ & D1). specialize (D1 bb kk Hb).
        pose proof (af_fshadow_apart RT AF S mE fr 0%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (D2 & _). specialize (D2 bb kk Hb).
        change (fs_size 0) with 64 in D1, D2. unfold shad, SHB in D2. rewrite ESP0 in LR. unfold STACK_WIN in LR.
        cbn [outside]. clear - LR D1 D2 Hz LOW LOR. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]. }
      unfold entry_st.
      walk_to AF MST [(usp - 192, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x93fd4].
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      frame_release RT AF GP MST Σ fr 0%nat 64 PF AGF PFS usp lo 0x93fdc
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => let N1 := fresh "N1" in let N2 := fresh "N2" in
                        cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      walk_to AF MST [(usp - 192, usp)] (@nil Z).
      cps_stop.
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
      assert (PINS : In (pix, 64) (rt_live RT S)) by (exact (LSUB _ PIN)).
      apply cps_finish. intros c0 Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', cfr, c end.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
        split; [intros xa HXa HXo; apply AGF; split; [exact HXa| exact HXo]|].
        destruct PAY as [(E0 & PX1 & _)|(NE0 & CFO & CFP & PX2 & EL)].
        - split; [intros _| intros HH; contradiction].
          apply (keeps_live_cells (rt_live RT S) mE _ pix 64 pix _ KEEPF PINS); [lia| cbn; lia| exact PX1].
        - split; [intros HH; contradiction| intros _].
          split; [rewrite LV2; exact (cf_obj_keep_all _ mE _ cfr c CFO KEEPF)|]. split; [exact CFP|].
          apply (keeps_live_cells (rt_live RT S) mE _ pix 64 pix _ KEEPF PINS); [lia| cbn; lia| exact PX2]. }
      rewrite LV2, FRS2, SP2, CR2.
      split; [| split; [reflexivity| split; [exact ESP0| lia]]].
      destruct PAY as [(E0 & _ & EL)|(NE0 & _ & _ & _ & EL)].
      - rewrite E0. change (0 =? 0) with true. cbv iota. exact EL.
      - replace (cfr =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0). exact EL. }
    assert (DR : 1 <= p_d v <= 32) by (clear - HD1; cbn [In] in HD1; lia).
    sx32_fix.
    destruct (Z.eq_dec (p_d v) 32) as [D32|DN32].
    2:{ (* [comment removed for export] *)
        let st := cfc_stops in awalk st.
        cfc_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH PXC usp lo (usp + -192)
          [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]. }
    let st := cfc_stops in awalk st.
    sx32_fix. rewrite (v_divw_1 (p_w v)) by lia.
    destruct (Z_lt_le_dec (p_w v) 10) as [WS|WB].
    1:{ (* [comment removed for export] *)
        let st := cfc_stops in awalk st.
        cfc_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH PXC usp lo (usp + -192)
          [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]. }
    let st := cfc_stops in awalk st.
    sx32_fix. rewrite (v_divw_1 (p_h v)) by lia.
    destruct (Z_lt_le_dec (p_h v) 10) as [HS|HB].
    1:{ (* [comment removed for export] *)
        let st := cfc_stops in awalk st.
        cfc_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH PXC usp lo (usp + -192)
          [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]. }
    let st := cfc_stops in awalk st.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    pose proof BAC as C1. unfold boxaCreate_cps in C1.
    eapply cps_seq.
    { eapply C1 with (lo := lo) (n := 1) (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= _ <= _ => lia
           | |- _ = [] -> _ => let E := fresh "E" in intros E; discriminate E
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           | |- In _ CLIENT_TRACES => exact (Forall_inv TRS)
           | |- uctx _ _ _ _ => cfc_uctx ra s0 ras m UCTX AGF RA4096 SPA usp (usp + -192)
           end. }
    after_call RT AF.
    lazymatch goal with H : boxa_new _ _ ?a 1 ?b |- _ => rename H into BN; set (ba := a) in *; set (barr := b) in * end.
    change (1 * 8) with 8 in *.
    destruct BN as (BE & BARR).
    pose proof BE as (_ & (IBA & _) & (IBARR & _) & _). change (8 * 1) with 8 in IBARR.
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT ?S ?mm, LV : rt_live RT ?S = (barr, 8) :: (ba, 24) :: _ |- _ =>
      assert (NCBA : forall a, PF a -> (a < ba \/ ba + 24 <= a) /\ (a < barr \/ barr + 8 <= a))
        by (let xa := fresh "xa" in let HXa := fresh "HXa" in intros xa [HXa _]; split;
            [ apply (fresh_chunk_apart RT AF S mm [(barr, 8)] ba 24 (rt_live RT Σ) (rt_frames RT S) usp xa A)
            | apply (fresh_chunk_apart RT AF S mm [] barr 8 ((ba, 24) :: rt_live RT Σ) (rt_frames RT S) usp xa A) ];
            [ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity | reflexivity
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ HXa); [auto| solve [frames_sub_tac]| lia]
            | repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity | reflexivity
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ HXa); [intros ee Hee; right; exact Hee| solve [frames_sub_tac]| lia] ]) end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    pose proof BC as C2. unfold boxCreate_cps in C2.
    eapply cps_seq.
    { eapply C2 with (lo := lo) (x := 0) (y := 0) (w := p_w v) (h := p_h v); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= _ < _ => lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    lazymatch goal with H : box_obj _ _ ?a _ _ _ _ |- _ => rename H into BOX; set (bx := a) in * end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BE AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    chunk_facts RT AF GP ba 24. chunk_facts RT AF GP barr 8.
    lazymatch goal with A : ART RT ?S ?mm, LV : rt_live RT ?S = (bx, 20) :: _ |- _ =>
      assert (FRSb : rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ)
        by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (LVb : rt_live RT S = (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APB : (ba + 24 <= pix \/ pix + 64 <= ba) /\ (barr + 8 <= pix \/ pix + 64 <= barr))
        by (split; [apply (af_live_disj RT AF S mm ba 24 pix 64 [(bx, 20); (barr, 8)] (rt_live RT Σ) A LVb)
                   | apply (af_live_disj RT AF S mm barr 8 pix 64 [(bx, 20)] ((ba, 24) :: rt_live RT Σ) A LVb)];
            cbn [app In]; auto) end.
    destruct APB as [APB1 APB2].
    fframe_chunk RT AF fr 0%nat 64 ba 24. fframe_chunk RT AF fr 0%nat 64 barr 8. norm_fshadow.
    park_disj.
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    pose proof BAB as C3. unfold boxaAddBox_cps in C3.
    eapply cps_seq.
    { eapply C3 with (lo := lo) (ba := ba) (arr := barr) (b := bx) (x := 0) (y := 0) (w := p_w v) (h := p_h v); rt_side idtac.
      all: lazymatch goal with
           | |- boxa_new _ _ _ _ _ => split; [exact BE| exact BARR]
           | |- box_obj _ _ _ _ _ _ _ => exact BOX
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- ?p <> ?q =>
               lazymatch goal with A : ART RT ?S ?mm, LV : rt_live RT ?S = (p, ?n) :: _, IQ : In (q, ?k) _ |- _ =>
                 let D1 := fresh "D" in
                 assert (D1 : p + n <= q \/ q + k <= p) by (apply (af_live_disj RT AF S mm p n q k [] _ A LV); cbn [app]; solve [in_live_tac]);
                 clear - D1; lia end
           end. }
    after_call RT AF.
    repeat match goal with H : parked ?T |- _ => lazymatch T with context [ba] => clear H | context [barr] => clear H end end.
    lazymatch goal with H : boxa_one _ _ _ _ _ _ _ _ _ |- _ => rename H into BO end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]|
                                   let HC := fresh "HC" in cbn [outside]; pose proof (NCBA _ Hx) as HC; repeat split; try exact I; lia]).
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 88); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= CALLOC_MAX => unfold CALLOC_MAX; lia
           | |- Z.of_nat (length _) < LIVE_MAX =>
               repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold LIVE_MAX in *; lia
           | |- unwind_okC _ _ _ _ =>
               unfold unwind_okC; exists (bv_unsigned ra :: ras); rewrite !unsigned_lit by lia;
               split; [cfc_uctx ra s0 ras m UCTX AGF RA4096 SPA usp (usp + -192)| exact (Forall_inv (Forall_inv_tail (Forall_inv_tail TRS)))]
           end. }
    after_call RT AF.
    change (1 * 88) with 88 in *.
    lazymatch goal with H : rt_live RT ?S = (?p, 88) :: _ |- _ => rename H into LVCF; set (cf := p) in * end.
    lazymatch goal with H : rw_cells asegs ?mm cf [CB (Z.to_nat 88) ?bs] |- _ =>
      pose proof (rw_cells_recell mm cf [CB (Z.to_nat 88) bs]
                    [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                     C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                     C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H
                    ltac:(cbn; tauto) eq_refl eq_refl) as CFC; clear H end.
    chunk_facts RT AF GP cf 88.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSc : rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ)
        by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (LVc : rt_live RT S = (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APCP : cf + 88 <= pix \/ pix + 64 <= cf)
        by (apply (af_live_disj RT AF S mm cf 88 pix 64 [] _ A LVc); cbn [app In]; auto);
      assert (APC1 : apartp ba 24 cf 88) by (unfold apartp; pose proof (af_live_disj RT AF S mm cf 88 ba 24 [] _ A LVc ltac:(cbn [app In]; auto)); lia);
      assert (APC2 : apartp barr 8 cf 88) by (unfold apartp; pose proof (af_live_disj RT AF S mm cf 88 barr 8 [] _ A LVc ltac:(cbn [app In]; auto)); lia);
      assert (APC3 : apartp bx 20 cf 88) by (unfold apartp; pose proof (af_live_disj RT AF S mm cf 88 bx 20 [] _ A LVc ltac:(cbn [app In]; auto)); lia);
      assert (NCCF : forall a, PF a -> a < cf \/ cf + 88 <= a)
        by (let xa := fresh "xa" in let HXa := fresh "HXa" in intros xa [HXa _];
            apply (fresh_chunk_apart RT AF S mm [] cf 88 ((bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ) (rt_frames RT S) usp xa A LVc eq_refl);
            [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ HXa); [intros ee Hee; cbn [In]; auto| solve [frames_sub_tac]| lia] ]) end.
    fframe_chunk RT AF fr 0%nat 64 cf 88. norm_fshadow.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BO AGx end.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    pose proof PCL as C5. unfold pixClone_cps in C5.
    eapply cps_seq.
    { eapply C5 with (lo := lo) (pix := pix) (v := v) (cv := cv) (rc := 1); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj_rc ?lv ?mc _ _ _ _ =>
               apply (pix_obj_rc_agree RT AF Σ m mc (rt_frames RT Σ) usp lv pix v cv 1 1 ART0 (proj2 (pix_obj_rc_1 _ _ _ _ _) POBJ) AGF);
               [ unfold pix_cells_rc; exact PXC | solve [live_add_tac] ]
           | |- _ <= _ < _ => lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           end. }
    after_call RT AF.
    lazymatch goal with H : rw_cells asegs _ pix (pix_cells_rc v (1 + 1)) |- _ =>
      rename H into PXC2; unfold pix_cells_rc in PXC2; change (1 + 1) with 2 in PXC2 end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (LVp : rt_live RT S = (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APP1 : apartp ba 24 pix 64)
        by (unfold apartp; exact (af_live_disj RT AF S mm ba 24 pix 64 [(cf, 88); (bx, 20); (barr, 8)] (rt_live RT Σ) A LVp ltac:(cbn [app In]; auto)));
      assert (APP2 : apartp barr 8 pix 64)
        by (unfold apartp; exact (af_live_disj RT AF S mm barr 8 pix 64 [(cf, 88); (bx, 20)] ((ba, 24) :: rt_live RT Σ) A LVp ltac:(cbn [app In]; auto)));
      assert (APP3 : apartp bx 20 pix 64)
        by (unfold apartp; exact (af_live_disj RT AF S mm bx 20 pix 64 [(cf, 88)] ((barr, 8) :: (ba, 24) :: rt_live RT Σ) A LVp ltac:(cbn [app In]; auto))) end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BO AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact (proj2 Hx)]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (cf, cf + 88)] st.
    cfc_keep_mu RT Σ fr cf LOUTG BO.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt_cf cf) ltac:(fun Hx => cfc_pft_cf PFS NFA NCCF Hx).
    pose proof NAC as C6. unfold numaaCreate_cps, parr16Create_cps in C6.
    eapply cps_seq.
    { eapply C6 with (lo := lo) (n := 1); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= _ <= _ => lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    change (1 * 8) with 8 in *.
    lazymatch goal with H : parr16_obj _ _ ?o 1 ?a |- _ => rename H into NAA; set (naa := o) in *; set (naarr := a) in * end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (LVn : rt_live RT S = (naarr, 8) :: (naa, 16) :: (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APN1 : apartp naarr 8 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm naarr 8 cf 88 [] _ A LVn ltac:(cbn [app In]; auto)));
      assert (APN2 : apartp naa 16 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm naa 16 cf 88 [(naarr, 8)] _ A LVn ltac:(cbn [app In]; auto))) end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BO AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (cf, cf + 88)] st.
    cfc_keep_mu RT Σ fr cf LOUTG BO. cfc_keep_mu RT Σ fr cf LOUTG NAA.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt_cf cf) ltac:(fun Hx => cfc_pft_cf PFS NFA NCCF Hx).
    pose proof DAC as C7. unfold l_dnaaCreate_cps, parr16Create_cps in C7.
    eapply cps_seq.
    { eapply C7 with (lo := lo) (n := 1); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= _ <= _ => lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    change (1 * 8) with 8 in *.
    lazymatch goal with H : parr16_obj (rt_live RT ?S) _ ?o 1 ?a |- cps _ (ASTA RT ?S _ _) _ => rename H into DNAA; set (dnaa := o) in *; set (dnarr := a) in * end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (LVd : rt_live RT S = (dnarr, 8) :: (dnaa, 16) :: (naarr, 8) :: (naa, 16) :: (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APD1 : apartp dnarr 8 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm dnarr 8 cf 88 [] _ A LVd ltac:(cbn [app In]; auto)));
      assert (APD2 : apartp dnaa 16 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm dnaa 16 cf 88 [(dnarr, 8)] _ A LVd ltac:(cbn [app In]; auto))) end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BO AGx; obj_keep RT S NAA AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (cf, cf + 88)] st.
    cfc_keep_mu RT Σ fr cf LOUTG BO. cfc_keep_mu RT Σ fr cf LOUTG NAA. cfc_keep_mu RT Σ fr cf LOUTG DNAA.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt_cf cf) ltac:(fun Hx => cfc_pft_cf PFS NFA NCCF Hx).
    pose proof PAC as C8. unfold pixaCreate_cps in C8.
    eapply cps_seq.
    { eapply C8 with (lo := lo) (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: lazymatch goal with
           | |- _ = [] -> _ => let E := fresh "E" in intros E; discriminate E
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           | |- In _ CLIENT_TRACES => exact (Forall_inv (Forall_inv_tail TRS))
           | |- uctx _ _ _ _ => cfc_uctx ra s0 ras m UCTX AGF RA4096 SPA usp (usp + -192)
           end. }
    after_call RT AF.
    lazymatch goal with H : pixa_obj (rt_live RT ?S) _ ?a 20 ?b ?c ?d |- cps _ (ASTA RT ?S _ _) _ =>
      rename H into PIXA; set (pxa := a) in *; set (pparr := b) in *; set (pba := c) in *; set (pbarr := d) in * end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (LVx : rt_live RT S = (pbarr, 160) :: (pba, 24) :: (pparr, 160) :: (pxa, 32) :: (dnarr, 8) :: (dnaa, 16) :: (naarr, 8) :: (naa, 16)
                                   :: (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APX1 : apartp pbarr 160 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm pbarr 160 cf 88 [] _ A LVx ltac:(cbn [app In]; auto 20)));
      assert (APX2 : apartp pba 24 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm pba 24 cf 88 [(pbarr, 160)] _ A LVx ltac:(cbn [app In]; auto 20)));
      assert (APX3 : apartp pparr 160 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm pparr 160 cf 88 [(pbarr, 160); (pba, 24)] _ A LVx ltac:(cbn [app In]; auto 20)));
      assert (APX4 : apartp pxa 32 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm pxa 32 cf 88 [(pbarr, 160); (pba, 24); (pparr, 160)] _ A LVx ltac:(cbn [app In]; auto 20))) end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      obj_keep RT S BO AGx; obj_keep RT S NAA AGx; obj_keep RT S DNAA AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (cf, cf + 88)] st.
    cfc_keep_mu RT Σ fr cf LOUTG BO. cfc_keep_mu RT Σ fr cf LOUTG NAA. cfc_keep_mu RT Σ fr cf LOUTG DNAA. cfc_keep_mu RT Σ fr cf LOUTG PIXA.
    (* [comment removed for export] *)
    cps_stop. art_now RT AF ltac:(cfc_ivt_cf cf).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cfc_pft_cf PFS NFA NCCF Hx) end.
    lazymatch goal with FRx : rw_cells asegs _ (usp + -192) _ |- _ => merge_low FRx 13%nat end.
    to_entry.
    eapply EPI with (cfr := cf) (c := mkCfv pix (p_w v) (p_h v) ba barr bx naa naarr dnaa dnarr pxa pparr pba pbarr).
    all: cfc_epi_side FRM FSH AGF.
    lazymatch goal with |- _ \/ _ => right | _ => idtac end.
    lazymatch goal with H0 : 0 < cf |- _ => split; [clear - H0; lia|] end.
    split; [| split; [reflexivity| split; [unfold pix_cells_rc; exact PXC2| unfold cf_live; cbn [cf_pix cf_tw cf_th cf_boxas cf_barr cf_box cf_naa cf_naarr cf_dnaa cf_dnarr cf_pixa cf_parr cf_pba cf_pbarr]; exact LVx]]].
    unfold cf_obj; cbn [cf_pix cf_tw cf_th cf_boxas cf_barr cf_box cf_naa cf_naarr cf_dnaa cf_dnarr cf_pixa cf_parr cf_pba cf_pbarr].
    split; [exists (repeat (Z_to_bv 8 0) 4); unfold cf_cells; cbn [cf_pix cf_tw cf_th cf_boxas cf_barr cf_box cf_naa cf_naarr cf_dnaa cf_dnarr cf_pixa cf_parr cf_pba cf_pbarr]; exact CFC|].
    split; [lazymatch goal with H0 : 0 < cf, H16 : cf mod 16 = 0 |- _ => unfold chunk; split; [solve [in_live_tac]| split; [exact H0| split; [exact H16| lia]]] end|].
    split; [exact BO|]. split; [exact NAA|]. split; [exact DNAA|]. split; [exact PIXA|].
    lazymatch goal with A : ART RT ?S ?mm, LV : rt_live RT ?S = (pbarr, 160) :: _ |- List.NoDup _ =>
      let ND := fresh "ND" in
      assert (ND : List.NoDup (map fst (rt_live RT S)))
        by (apply (live_nodup RT AF S mm A); let p := fresh "p" in let n := fresh "n" in let Hp := fresh "Hp" in
            intros p n Hp; rewrite LV in Hp; cbn [In] in Hp;
            repeat (destruct Hp as [Hp|Hp]; [injection Hp as <- <-; lia|]); exact (LVP _ _ Hp));
      rewrite LV in ND; cbn [map fst] in ND;
      unfold cf_live; cbn [map fst cf_pix cf_tw cf_th cf_boxas cf_barr cf_box cf_naa cf_naarr cf_dnaa cf_dnarr cf_pixa cf_parr cf_pba cf_pbarr];
      lazymatch type of ND with List.NoDup (?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?a7 :: ?a8 :: ?a9 :: ?a10 :: ?a11 :: ?a12 :: ?rest) =>
        exact (List.NoDup_app_remove_r [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12] rest ND) end end.
(* [comment removed for export] *)
  - (* [comment removed for export] *)
    carve_frame 208%nat ST.
    walk_to AF MST [(usp - 208, usp)] [0x48a00].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
    fframe_open RT AF PF (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => exact (proj1 Ha)).
    fframe_chunk RT AF fr 0%nat 64 pix 64. norm_fshadow.
    assert (LOUTG : forall S0 mS, ART RT S0 mS -> rt_frames RT S0 = (fr, 0%nat) :: rt_frames RT Σ -> rt_sp0 RT S0 = rt_sp0 RT Σ ->
              forall bb kk, In (bb, kk) (rt_live RT S0) -> forall zz, bb <= zz < bb + kk ->
              ~ (usp - 256 <= zz < usp) /\ ~ (fr <= zz < fr + 56) /\ ~ (fr / 8 + 2147450880 <= zz < fr / 8 + 2147450880 + 8)).
    { intros S0 mS AS FS SS bb kk Hb zz Hz.
      pose proof (af_live_range RT AF S0 mS bb kk AS Hb) as LR.
      pose proof (af_frames_range RT AF S0 mS fr 0%nat AS ltac:(rewrite FS; left; reflexivity)) as (_ & _ & _ & D1). specialize (D1 bb kk Hb).
      pose proof (af_fshadow_apart RT AF S0 mS fr 0%nat AS ltac:(rewrite FS; left; reflexivity)) as (D2 & _). specialize (D2 bb kk Hb).
      change (fs_size 0) with 64 in D1, D2. unfold shad, SHB in D2. rewrite SS in LR. unfold STACK_WIN in LR.
      clear - LR D1 D2 Hz LOW LOR. repeat split; intro; first [lia | Z.div_mod_to_equations; lia]. }
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    (* [comment removed for export] *)
    clear_acc.
    walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x93c7c].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => let N1 := fresh "N1" in let N2 := fresh "N2" in
                                        cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP.
    (* [comment removed for export] *)
    split_last_CB FRM [8; 4; 12; 4; 4]%nat.
    lazymatch type of FRM with rw_cells asegs ?mm fr (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 4 ?b :: ?post) =>
      apply (cb4_c4_in mm fr [c0; c1; c2; c3] post b) in FRM; destruct FRM as (wx & FRM); cbn [app] in FRM end.
    lazymatch type of FRM with rw_cells asegs ?mm fr (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: CB 4 ?b :: ?post) =>
      apply (cb4_c4_in mm fr [c0; c1; c2; c3; c4; c5] post b) in FRM; destruct FRM as (hx & FRM); cbn [app] in FRM end.
    local_acc FSH fr 4%nat 32 FR64 ACW. local_acc FSH fr 6%nat 48 FR64 ACH.
    (* [comment removed for export] *)
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    assert (EPI : forall (S : rts RT) (mE : mem) (cfr : Z) (c : cfv) (jE : list byte)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r21 r23 r24 r25 r26 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -208) ->
          rw_cells asegs mE (usp + -208)
            (CB 104 jE :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
          wr_at asegs mE fr 56 -> wr_at asegs mE (fr / 8 + 2147450880) 8 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE -> wmono asegs m mE ->
          rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 2 <= rt_credit RT S ->
          (forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) ->
          ((cfr = 0 /\ rw_cells asegs mE pix (pix_cells_rc v 1) /\ rt_live RT S = rt_live RT Σ)
           \/ (cfr <> 0 /\ cf_obj (rt_live RT S) mE cfr c /\ cf_pix c = pix /\ rw_cells asegs mE pix (pix_cells_rc v 2)
               /\ rt_live RT S = cf_live cfr c (rt_live RT Σ))) ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) r20 r21
                                          (Z_to_bv 64 cfr) r23 r24 r25 r26 (Z_to_bv 64 fr) r28 r29 r30 r31 F' fc' 0x93f94 mE))) QF).
    { intros S mE cfr c jE r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r21 r23 r24 r25 r26 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE WME EFR ESP0 ECR LSUB PAY.
      clear AGF. rename AGE into AGF.
      repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | _ => clear H end end.
      repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
      repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
      repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
      repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
      repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
      repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
      repeat match goal with H : wmono asegs _ _ |- _ => lazymatch H with WME => fail | _ => clear H end end.
      repeat match goal with H : munch _ _ _ |- _ => clear H end.
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => clear H end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 56 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 8 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 56) with 56%nat in FRME. change (Z.to_nat 8) with 8%nat in FSHE.
      (* [comment removed for export] *)
      assert (LOUT : forall b k, In (b, k) (rt_live RT S) -> forall x, b <= x < b + k ->
                outside [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] x).
      { intros bb kk Hb zz Hz.
        pose proof (af_live_range RT AF S mE bb kk ARTE Hb) as LR.
        pose proof (af_frames_range RT AF S mE fr 0%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (_ & _ & _ & D1). specialize (D1 bb kk Hb).
        pose proof (af_fshadow_apart RT AF S mE fr 0%nat ARTE ltac:(rewrite EFR; left; reflexivity)) as (D2 & _). specialize (D2 bb kk Hb).
        change (fs_size 0) with 64 in D1, D2. unfold shad, SHB in D2. rewrite ESP0 in LR. unfold STACK_WIN in LR.
        cbn [outside]. clear - LR D1 D2 Hz LOW LOR. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]. }
      unfold entry_st.
      walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0x93fd4].
      lazymatch goal with MUx : munch _ mE ?mc |- _ =>
        assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
          by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
              intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
      frame_release RT AF GP MST Σ fr 0%nat 64 PF AGF PFS usp lo 0x93fdc
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => let N1 := fresh "N1" in let N2 := fresh "N2" in
                        cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      walk_to AF MST [(usp - 208, usp)] (@nil Z).
      cps_stop.
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
      assert (PINS : In (pix, 64) (rt_live RT S)) by (exact (LSUB _ PIN)).
      apply cps_finish. intros c0 Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', cfr, c end.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
        { lazymatch goal with WMx : wmono asegs m ?mf |- wmono asegs m ?mf => exact WMx end. }
        split; [intros xa HXa HXo; apply AGF; split; [exact HXa| exact HXo]|].
        destruct PAY as [(E0 & PX1 & _)|(NE0 & CFO & CFP & PX2 & EL)].
        - split; [intros _| intros HH; contradiction].
          apply (keeps_live_cells (rt_live RT S) mE _ pix 64 pix _ KEEPF PINS); [lia| cbn; lia| exact PX1].
        - split; [intros HH; contradiction| intros _].
          split; [rewrite LV2; exact (cf_obj_keep_all _ mE _ cfr c CFO KEEPF)|]. split; [exact CFP|].
          apply (keeps_live_cells (rt_live RT S) mE _ pix 64 pix _ KEEPF PINS); [lia| cbn; lia| exact PX2]. }
      rewrite LV2, FRS2, SP2, CR2.
      split; [| split; [reflexivity| split; [exact ESP0| lia]]].
      destruct PAY as [(E0 & _ & EL)|(NE0 & _ & _ & _ & EL)].
      - rewrite E0. change (0 =? 0) with true. cbv iota. exact EL.
      - replace (cfr =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0). exact EL. }
    assert (DR : 1 <= p_d v <= 32) by (clear - HD1; cbn [In] in HD1; lia).
    sx32_fix.
    destruct (Z.eq_dec (p_d v) 32) as [D32|DN32].
    2:{ (* [comment removed for export] *)
        let st := cfc_stops in awalk st.
        cfc_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH PXC usp lo (usp + -208)
          [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]. }
    let st := cfc_stops in awalk st.
    sx32_fix. rewrite (v_divw_1 (p_w v)) by lia.
    destruct (Z_lt_le_dec (p_w v) 10) as [WS|WB].
    1:{ (* [comment removed for export] *)
        let st := cfc_stops in awalk st.
        cfc_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH PXC usp lo (usp + -208)
          [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]. }
    let st := cfc_stops in awalk st.
    sx32_fix. rewrite (v_divw_1 (p_h v)) by lia.
    destruct (Z_lt_le_dec (p_h v) 10) as [HS|HB].
    1:{ (* [comment removed for export] *)
        let st := cfc_stops in awalk st.
        cfc_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH PXC usp lo (usp + -208)
          [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)]. }
    let st := cfc_stops in awalk st.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    pose proof BAC as C1. unfold boxaCreate_cps in C1.
    eapply cps_seq.
    { eapply C1 with (lo := lo) (n := 1) (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= _ <= _ => lia
           | |- _ = [] -> _ => let E := fresh "E" in intros E; discriminate E
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           | |- In _ CLIENT_TRACES => exact (Forall_inv TRS)
           | |- uctx _ _ _ _ => cfc_uctx ra s0 ras m UCTX AGF RA4096 SPA usp (usp + -208)
           end. }
    after_call RT AF.
    lazymatch goal with H : boxa_new _ _ ?a 1 ?b |- _ => rename H into BN; set (ba := a) in *; set (barr := b) in * end.
    change (1 * 8) with 8 in *.
    destruct BN as (BE & BARR).
    pose proof BE as (_ & (IBA & _) & (IBARR & _) & _). change (8 * 1) with 8 in IBARR.
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT ?S ?mm, LV : rt_live RT ?S = (barr, 8) :: (ba, 24) :: _ |- _ =>
      assert (NCBA : forall a, PF a -> (a < ba \/ ba + 24 <= a) /\ (a < barr \/ barr + 8 <= a))
        by (let xa := fresh "xa" in let HXa := fresh "HXa" in intros xa [HXa _]; split;
            [ apply (fresh_chunk_apart RT AF S mm [(barr, 8)] ba 24 (rt_live RT Σ) (rt_frames RT S) usp xa A)
            | apply (fresh_chunk_apart RT AF S mm [] barr 8 ((ba, 24) :: rt_live RT Σ) (rt_frames RT S) usp xa A) ];
            [ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity | reflexivity
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ HXa); [auto| solve [frames_sub_tac]| lia]
            | repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity | reflexivity
            | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ HXa); [intros ee Hee; right; exact Hee| solve [frames_sub_tac]| lia] ]) end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    pose proof BC as C2. unfold boxCreate_cps in C2.
    eapply cps_seq.
    { eapply C2 with (lo := lo) (x := 0) (y := 0) (w := p_w v) (h := p_h v); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= _ < _ => lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    lazymatch goal with H : box_obj _ _ ?a _ _ _ _ |- _ => rename H into BOX; set (bx := a) in * end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BE AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    chunk_facts RT AF GP ba 24. chunk_facts RT AF GP barr 8.
    lazymatch goal with A : ART RT ?S ?mm, LV : rt_live RT ?S = (bx, 20) :: _ |- _ =>
      assert (FRSb : rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ)
        by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (LVb : rt_live RT S = (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APB : (ba + 24 <= pix \/ pix + 64 <= ba) /\ (barr + 8 <= pix \/ pix + 64 <= barr))
        by (split; [apply (af_live_disj RT AF S mm ba 24 pix 64 [(bx, 20); (barr, 8)] (rt_live RT Σ) A LVb)
                   | apply (af_live_disj RT AF S mm barr 8 pix 64 [(bx, 20)] ((ba, 24) :: rt_live RT Σ) A LVb)];
            cbn [app In]; auto) end.
    destruct APB as [APB1 APB2].
    fframe_chunk RT AF fr 0%nat 64 ba 24. fframe_chunk RT AF fr 0%nat 64 barr 8. norm_fshadow.
    park_disj.
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    pose proof BAB as C3. unfold boxaAddBox_cps in C3.
    eapply cps_seq.
    { eapply C3 with (lo := lo) (ba := ba) (arr := barr) (b := bx) (x := 0) (y := 0) (w := p_w v) (h := p_h v); rt_side idtac.
      all: lazymatch goal with
           | |- boxa_new _ _ _ _ _ => split; [exact BE| exact BARR]
           | |- box_obj _ _ _ _ _ _ _ => exact BOX
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- ?p <> ?q =>
               lazymatch goal with A : ART RT ?S ?mm, LV : rt_live RT ?S = (p, ?n) :: _, IQ : In (q, ?k) _ |- _ =>
                 let D1 := fresh "D" in
                 assert (D1 : p + n <= q \/ q + k <= p) by (apply (af_live_disj RT AF S mm p n q k [] _ A LV); cbn [app]; solve [in_live_tac]);
                 clear - D1; lia end
           end. }
    after_call RT AF.
    repeat match goal with H : parked ?T |- _ => lazymatch T with context [ba] => clear H | context [barr] => clear H end end.
    lazymatch goal with H : boxa_one _ _ _ _ _ _ _ _ _ |- _ => rename H into BO end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]|
                                   let HC := fresh "HC" in cbn [outside]; pose proof (NCBA _ Hx) as HC; repeat split; try exact I; lia]).
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 88); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= CALLOC_MAX => unfold CALLOC_MAX; lia
           | |- Z.of_nat (length _) < LIVE_MAX =>
               repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold LIVE_MAX in *; lia
           | |- unwind_okC _ _ _ _ =>
               unfold unwind_okC; exists (bv_unsigned ra :: ras); rewrite !unsigned_lit by lia;
               split; [cfc_uctx ra s0 ras m UCTX AGF RA4096 SPA usp (usp + -208)| exact (Forall_inv (Forall_inv_tail (Forall_inv_tail TRS)))]
           end. }
    after_call RT AF.
    change (1 * 88) with 88 in *.
    lazymatch goal with H : rt_live RT ?S = (?p, 88) :: _ |- _ => rename H into LVCF; set (cf := p) in * end.
    lazymatch goal with H : rw_cells asegs ?mm cf [CB (Z.to_nat 88) ?bs] |- _ =>
      pose proof (rw_cells_recell mm cf [CB (Z.to_nat 88) bs]
                    [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                     C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                     C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H
                    ltac:(cbn; tauto) eq_refl eq_refl) as CFC; clear H end.
    chunk_facts RT AF GP cf 88.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSc : rt_frames RT S = (fr, 0%nat) :: rt_frames RT Σ)
        by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (LVc : rt_live RT S = (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APCP : cf + 88 <= pix \/ pix + 64 <= cf)
        by (apply (af_live_disj RT AF S mm cf 88 pix 64 [] _ A LVc); cbn [app In]; auto);
      assert (APC1 : apartp ba 24 cf 88) by (unfold apartp; pose proof (af_live_disj RT AF S mm cf 88 ba 24 [] _ A LVc ltac:(cbn [app In]; auto)); lia);
      assert (APC2 : apartp barr 8 cf 88) by (unfold apartp; pose proof (af_live_disj RT AF S mm cf 88 barr 8 [] _ A LVc ltac:(cbn [app In]; auto)); lia);
      assert (APC3 : apartp bx 20 cf 88) by (unfold apartp; pose proof (af_live_disj RT AF S mm cf 88 bx 20 [] _ A LVc ltac:(cbn [app In]; auto)); lia);
      assert (NCCF : forall a, PF a -> a < cf \/ cf + 88 <= a)
        by (let xa := fresh "xa" in let HXa := fresh "HXa" in intros xa [HXa _];
            apply (fresh_chunk_apart RT AF S mm [] cf 88 ((bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ) (rt_frames RT S) usp xa A LVc eq_refl);
            [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
            | apply (aclient_mono _ _ usp _ _ usp _ HXa); [intros ee Hee; cbn [In]; auto| solve [frames_sub_tac]| lia] ]) end.
    fframe_chunk RT AF fr 0%nat 64 cf 88. norm_fshadow.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BO AGx end.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] st.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt) ltac:(fun Hx => cfc_pft PFS NFA Hx).
    pose proof PCL as C5. unfold pixClone_cps in C5.
    eapply cps_seq.
    { eapply C5 with (lo := lo) (pix := pix) (v := v) (cv := cv) (rc := 1); rt_side idtac.
      all: lazymatch goal with
           | |- pix_obj_rc ?lv ?mc _ _ _ _ =>
               apply (pix_obj_rc_agree RT AF Σ m mc (rt_frames RT Σ) usp lv pix v cv 1 1 ART0 (proj2 (pix_obj_rc_1 _ _ _ _ _) POBJ) AGF);
               [ unfold pix_cells_rc; exact PXC | solve [live_add_tac] ]
           | |- _ <= _ < _ => lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           end. }
    after_call RT AF.
    lazymatch goal with H : rw_cells asegs _ pix (pix_cells_rc v (1 + 1)) |- _ =>
      rename H into PXC2; unfold pix_cells_rc in PXC2; change (1 + 1) with 2 in PXC2 end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (LVp : rt_live RT S = (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APP1 : apartp ba 24 pix 64)
        by (unfold apartp; exact (af_live_disj RT AF S mm ba 24 pix 64 [(cf, 88); (bx, 20); (barr, 8)] (rt_live RT Σ) A LVp ltac:(cbn [app In]; auto)));
      assert (APP2 : apartp barr 8 pix 64)
        by (unfold apartp; exact (af_live_disj RT AF S mm barr 8 pix 64 [(cf, 88); (bx, 20)] ((ba, 24) :: rt_live RT Σ) A LVp ltac:(cbn [app In]; auto)));
      assert (APP3 : apartp bx 20 pix 64)
        by (unfold apartp; exact (af_live_disj RT AF S mm bx 20 pix 64 [(cf, 88)] ((barr, 8) :: (ba, 24) :: rt_live RT Σ) A LVp ltac:(cbn [app In]; auto))) end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BO AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact (proj2 Hx)]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (cf, cf + 88)] st.
    cfc_keep_mu RT Σ fr cf LOUTG BO.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt_cf cf) ltac:(fun Hx => cfc_pft_cf PFS NFA NCCF Hx).
    pose proof NAC as C6. unfold numaaCreate_cps, parr16Create_cps in C6.
    eapply cps_seq.
    { eapply C6 with (lo := lo) (n := 1); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= _ <= _ => lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    change (1 * 8) with 8 in *.
    lazymatch goal with H : parr16_obj _ _ ?o 1 ?a |- _ => rename H into NAA; set (naa := o) in *; set (naarr := a) in * end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (LVn : rt_live RT S = (naarr, 8) :: (naa, 16) :: (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APN1 : apartp naarr 8 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm naarr 8 cf 88 [] _ A LVn ltac:(cbn [app In]; auto)));
      assert (APN2 : apartp naa 16 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm naa 16 cf 88 [(naarr, 8)] _ A LVn ltac:(cbn [app In]; auto))) end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BO AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (cf, cf + 88)] st.
    cfc_keep_mu RT Σ fr cf LOUTG BO. cfc_keep_mu RT Σ fr cf LOUTG NAA.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt_cf cf) ltac:(fun Hx => cfc_pft_cf PFS NFA NCCF Hx).
    pose proof DAC as C7. unfold l_dnaaCreate_cps, parr16Create_cps in C7.
    eapply cps_seq.
    { eapply C7 with (lo := lo) (n := 1); rt_side idtac.
      all: lazymatch goal with
           | |- _ <= _ <= _ => lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           end. }
    after_call RT AF.
    change (1 * 8) with 8 in *.
    lazymatch goal with H : parr16_obj (rt_live RT ?S) _ ?o 1 ?a |- cps _ (ASTA RT ?S _ _) _ => rename H into DNAA; set (dnaa := o) in *; set (dnarr := a) in * end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (LVd : rt_live RT S = (dnarr, 8) :: (dnaa, 16) :: (naarr, 8) :: (naa, 16) :: (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APD1 : apartp dnarr 8 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm dnarr 8 cf 88 [] _ A LVd ltac:(cbn [app In]; auto)));
      assert (APD2 : apartp dnaa 16 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm dnaa 16 cf 88 [(dnarr, 8)] _ A LVd ltac:(cbn [app In]; auto))) end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ => obj_keep RT S BO AGx; obj_keep RT S NAA AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (cf, cf + 88)] st.
    cfc_keep_mu RT Σ fr cf LOUTG BO. cfc_keep_mu RT Σ fr cf LOUTG NAA. cfc_keep_mu RT Σ fr cf LOUTG DNAA.
    (* [comment removed for export] *)
    at_call RT AF ltac:(cfc_ivt_cf cf) ltac:(fun Hx => cfc_pft_cf PFS NFA NCCF Hx).
    pose proof PAC as C8. unfold pixaCreate_cps in C8.
    eapply cps_seq.
    { eapply C8 with (lo := lo) (ras := bv_unsigned ra :: ras); rt_side idtac.
      all: lazymatch goal with
           | |- _ = [] -> _ => let E := fresh "E" in intros E; discriminate E
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ => lres_tac
           | |- In _ CLIENT_TRACES => exact (Forall_inv (Forall_inv_tail TRS))
           | |- uctx _ _ _ _ => cfc_uctx ra s0 ras m UCTX AGF RA4096 SPA usp (usp + -208)
           end. }
    after_call RT AF.
    lazymatch goal with H : pixa_obj (rt_live RT ?S) _ ?a 20 ?b ?c ?d |- cps _ (ASTA RT ?S _ _) _ =>
      rename H into PIXA; set (pxa := a) in *; set (pparr := b) in *; set (pba := c) in *; set (pbarr := d) in * end.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
      assert (LVx : rt_live RT S = (pbarr, 160) :: (pba, 24) :: (pparr, 160) :: (pxa, 32) :: (dnarr, 8) :: (dnaa, 16) :: (naarr, 8) :: (naa, 16)
                                   :: (cf, 88) :: (bx, 20) :: (barr, 8) :: (ba, 24) :: rt_live RT Σ)
        by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      assert (APX1 : apartp pbarr 160 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm pbarr 160 cf 88 [] _ A LVx ltac:(cbn [app In]; auto 20)));
      assert (APX2 : apartp pba 24 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm pba 24 cf 88 [(pbarr, 160)] _ A LVx ltac:(cbn [app In]; auto 20)));
      assert (APX3 : apartp pparr 160 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm pparr 160 cf 88 [(pbarr, 160); (pba, 24)] _ A LVx ltac:(cbn [app In]; auto 20)));
      assert (APX4 : apartp pxa 32 cf 88) by (unfold apartp; exact (af_live_disj RT AF S mm pxa 32 cf 88 [(pbarr, 160); (pba, 24); (pparr, 160)] _ A LVx ltac:(cbn [app In]; auto 20))) end.
    lazymatch goal with AGx : agree_on _ _ ?mb |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      obj_keep RT S BO AGx; obj_keep RT S NAA AGx; obj_keep RT S DNAA AGx end.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_add_tac]| solve [frames_sub_tac]| lia]| exact I]).
    cfc_refresh RT AF GP.
    let st := cfc_stops in walk_to AF MST [(usp - 256, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (cf, cf + 88)] st.
    cfc_keep_mu RT Σ fr cf LOUTG BO. cfc_keep_mu RT Σ fr cf LOUTG NAA. cfc_keep_mu RT Σ fr cf LOUTG DNAA. cfc_keep_mu RT Σ fr cf LOUTG PIXA.
    (* [comment removed for export] *)
    cps_stop. art_now RT AF ltac:(cfc_ivt_cf cf).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cfc_pft_cf PFS NFA NCCF Hx) end.
    lazymatch goal with FRx : rw_cells asegs _ (usp + -208) _ |- _ => merge_low FRx 13%nat end.
    to_entry.
    eapply EPI with (cfr := cf) (c := mkCfv pix (p_w v) (p_h v) ba barr bx naa naarr dnaa dnarr pxa pparr pba pbarr).
    all: cfc_epi_side FRM FSH AGF.
    lazymatch goal with |- _ \/ _ => right | _ => idtac end.
    lazymatch goal with H0 : 0 < cf |- _ => split; [clear - H0; lia|] end.
    split; [| split; [reflexivity| split; [unfold pix_cells_rc; exact PXC2| unfold cf_live; cbn [cf_pix cf_tw cf_th cf_boxas cf_barr cf_box cf_naa cf_naarr cf_dnaa cf_dnarr cf_pixa cf_parr cf_pba cf_pbarr]; exact LVx]]].
    unfold cf_obj; cbn [cf_pix cf_tw cf_th cf_boxas cf_barr cf_box cf_naa cf_naarr cf_dnaa cf_dnarr cf_pixa cf_parr cf_pba cf_pbarr].
    split; [exists (repeat (Z_to_bv 8 0) 4); unfold cf_cells; cbn [cf_pix cf_tw cf_th cf_boxas cf_barr cf_box cf_naa cf_naarr cf_dnaa cf_dnarr cf_pixa cf_parr cf_pba cf_pbarr]; exact CFC|].
    split; [lazymatch goal with H0 : 0 < cf, H16 : cf mod 16 = 0 |- _ => unfold chunk; split; [solve [in_live_tac]| split; [exact H0| split; [exact H16| lia]]] end|].
    split; [exact BO|]. split; [exact NAA|]. split; [exact DNAA|]. split; [exact PIXA|].
    lazymatch goal with A : ART RT ?S ?mm, LV : rt_live RT ?S = (pbarr, 160) :: _ |- List.NoDup _ =>
      let ND := fresh "ND" in
      assert (ND : List.NoDup (map fst (rt_live RT S)))
        by (apply (live_nodup RT AF S mm A); let p := fresh "p" in let n := fresh "n" in let Hp := fresh "Hp" in
            intros p n Hp; rewrite LV in Hp; cbn [In] in Hp;
            repeat (destruct Hp as [Hp|Hp]; [injection Hp as <- <-; lia|]); exact (LVP _ _ Hp));
      rewrite LV in ND; cbn [map fst] in ND;
      unfold cf_live; cbn [map fst cf_pix cf_tw cf_th cf_boxas cf_barr cf_box cf_naa cf_naarr cf_dnaa cf_dnarr cf_pixa cf_parr cf_pba cf_pbarr];
      lazymatch type of ND with List.NoDup (?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?a7 :: ?a8 :: ?a9 :: ?a10 :: ?a11 :: ?a12 :: ?rest) =>
        exact (List.NoDup_app_remove_r [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12] rest ND) end end.
Qed.
End CFCREATE.

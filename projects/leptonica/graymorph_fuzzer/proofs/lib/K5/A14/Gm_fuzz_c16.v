(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_deserkit Lept_gmax_defs D_iface D_defs Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit Gm_drvkit2 Gm_fzkit Gm_leaf Gm_fuzz_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac fz_resync RT AF GP AGF PFS NFA :=
  cps_stop;
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]);
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end;
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; park_disj.

Section FZ.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis DESER : pixDeserialize_cps RT.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis DNULL : pixDestroy_null_cps RT.
Hypothesis PCOPY : pixCopy_cps RT.
Hypothesis GCLOSE : gray3_cps RT e_pixCloseGray3.
Hypothesis GDILATE : gray3_cps RT e_pixDilateGray3.
Hypothesis GERODE : gray3_cps RT e_pixErodeGray3.
Hypothesis GOPEN : gray3_cps RT e_pixOpenGray3.

Theorem fuzz_c16 : fuzz_case RT 16.
Proof using AF RC GP DESER DESTROY DNULL PCOPY GCLOSE GDILATE GERODE GOPEN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST -> -> -> RATOP DPOS BSL BYTES OWN FR0 LVP LVB CRB S0INV LIBm SSP ART0 MI ST LOW LOR SPT SPA SPB AL.
  destruct LIBm as ((LSEV & LALLOC & LDEALLOC) & (h0 & LHAND)).
  unfold g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler in *. clear BYTES.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_fuzz, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside Lept_iface.LIB_FP a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  hide S0INV.
  park_disj. carve_frame 112%nat ST.
  clear_acc.
  Time walk_to AF MST [(usp - 112, usp)] [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  destruct (Z_lt_ge_dec (Z.of_nat (length bs)) 3) as [SZ|SZ].
  - (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x905a4].
    frame_release_raw RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x905ac
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact (proj1 Hx)) LSEV LALLOC LDEALLOC LHAND.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 112, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -112), FR' : rw_cells asegs _ (usp + -112) _ |- _ => release_frame FR' ST' usp end.
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [assumption| split; assumption]|].
    split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
    unfold LIB, LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler.
    split; [split; [assumption| split; assumption]| exists h0; assumption].
  - (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (943680, 943688)]
                 [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    destruct OWN as [(p0 & n0 & OIN & OLO & OHI & DAL)| ->]; [| cbn [length] in SZ; lia].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (LH : LIBH mc)
        by (unfold LIBH, LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler, e_devnull; split; [split; [|split]|]; assumption) end.
    clear LSEV LALLOC LDEALLOC LHAND.
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; static_tac | exact I]]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO];
                        unfold Lept_iface.LIB_FP, g_stderr_handler in HxO; cbn [outside] in HxO; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
    pose proof DESER as DS. unfold pixDeserialize_cps in DS.
    unfold hid in S0INV.
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
    lazymatch goal with H : ?p = 0 \/ _ |- _ => rename H into POBJ; set (pixs := p) in * end.
    lazymatch goal with H : pixs = 0 -> rt_live RT _ = _ |- _ => rename H into LVZ end.
    lazymatch goal with H : pixs <> 0 -> live_destroy _ _ _ _ = _ |- _ => rename H into LVD end.
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into Sb end.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
          wr_at asegs mE fr 8 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE ->
          rt_live RT S = rt_live RT Σ ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 3 * 2 ^ 30 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 r22 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90548 mE))) QF) end.
    { intros S mE r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE ELV EFR ESP0 ECR.
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
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 8 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 8) with 8%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      unfold entry_st.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x905a4].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      Time frame_release_k RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x905ac
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN => idtac).
      Time walk_to AF MST [(usp - 112, usp)] (@nil Z).
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      lazymatch goal with ST' : stk asegs _ lo (usp + -112), FR' : rw_cells asegs _ (usp + -112) _ |- _ => release_frame FR' ST' usp end.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [assumption| split; assumption]|].
        split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
        lazymatch goal with LHx : LIBH ?mm |- LIB ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end. }
      rewrite LV2, FRS2, SP2, CR2.
      split; [exact ELV|]. split; [exact FR0|]. split; [exact ESP0| lia]. }
    destruct (Z.eq_dec pixs 0) as [PZ|PNZ].
    + (* [comment removed for export] *)
      clear POBJ LVD. pose proof (LVZ PZ) as LVE. clear LVZ. rewrite PZ in *.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x90548].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                           repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
      pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
      to_entry.
      eapply EPI; try eassumption.
      all: lazymatch goal with
           | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
           | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
           | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- _ <= rt_credit _ _ => unfold RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia
           | |- ?g => idtac "LEFT:" g
           end.
    + (* [comment removed for export] *)
      destruct POBJ as [PZ|(POBJ & VDATA)]; [contradiction|]. clear LVZ. pose proof (LVD PNZ) as LVE. clear LVD.
      lazymatch type of POBJ with pix_obj _ _ _ ?vv ?cc => set (vs := vv) in *; set (cvs := cc) in * end.
      lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sb) -> 0 < n |- _ => rename H into LVPb end.
      lazymatch goal with H : Z.of_nat (length (rt_live RT Sb)) <= _ |- _ => rename H into LVXb end.
      repeat match goal with E : rt_live RT _ = rt_live RT Σ |- _ => rewrite E in LVE end.
      repeat match goal with E : rt_live RT _ = rt_live RT Σ |- _ => rewrite E in LVXb end.
      assert (SUB0b : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Sb)) by (intros e He; rewrite <- LVE in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
      assert (PS0 : 0 < pixs) by (destruct POBJ as (_ & (_ & P0 & _) & _); exact P0).
      pose proof POBJ as (_ & (PSIN & _) & _). chunk_facts RT AF GP pixs 64.
      split_last_CB FRM [8%nat; 8%nat; 24%nat; 8%nat; 24%nat; 8%nat; 16%nat].
      split_at FRM 4%nat PSc. split_at PSc 1%nat F5c. split_at F5c 1%nat P1c. split_at P1c 1%nat F7c. split_at F7c 1%nat P2c. split_at P2c 1%nat F9c.
      split_at FRM 1%nat FRMh2.
      hide POBJ.
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (FIN : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 4 * (TEMPLATE_COST + GRAY3_COST + 2)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 pixs) (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90534 mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB4. split_at SHB4 4%nat SHB4b. split_at SHB4b 1%nat SHB4c. clear SHB4 SHB4c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 32) (pix := pixs) (v := vs) (cv := cvs) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite EFR; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB4b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact PSE
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POS1 SHB4b.
        after_call RT AF.
        lazymatch goal with H : rt_live RT ?Sx = live_destroy _ _ _ _ |- _ => rewrite ELV, LVE in H end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x90548].
        cwalk [0x90548].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
        lazymatch goal with MUx : munch _ ?mm _ |- _ =>
          agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                             repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
        to_entry.
        eapply EPI; try eassumption.
        all: lazymatch goal with
             | |- wr_at asegs _ _ 8 => exact (proj2 FHE)
             | |- wr_at asegs _ _ 16 => exact (proj2 FSE)
             | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; first [reflexivity | exact LVE]
             | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
             | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; lia
             | |- ?g => idtac "LEFT:" g
             end. }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT3 : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 3 * (TEMPLATE_COST + GRAY3_COST + 2)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 pixs) (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90504 mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        pose proof GOPEN as GK. unfold gray3_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pixs := p1) (vs := v1) (cvs := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ (GRAY3_DESTROY_RAS _) => rewrite ?unsigned_lit by ul; apply tr_gray3; unfold FUZZ_GRAY3_CALLS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        unfold new_pix8, new_pix8_live in *.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv _ /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in * end.
        lazymatch goal with H : rt_live RT Sd = _ |- _ => rename H into LVd end.
        set (pre_r := if rr =? 0 then @nil (Z * Z) else [(p_data vr, rsize vr); (rr, 64)]).
        assert (LVd' : rt_live RT Sd = pre_r ++ rt_live RT Sc) by (rewrite LVd; unfold pre_r; destruct (rr =? 0); reflexivity).
        clear LVd. rename LVd' into LVd.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (PRF : rr <> 0 -> In (rr, 64) pre_r /\ In (p_data vr, rsize vr) pre_r /\ 0 < rsize vr)
          by (intros NZ; destruct PRd as [Z0|(PO & _ & _ & _ & DNZ & _)]; [exfalso; exact (NZ Z0)|];
              destruct (pix_obj_chunks _ _ _ _ _ PO DNZ) as (_ & _ & I3 & _);
              unfold pre_r; replace (rr =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); cbn [In]; tauto).
        assert (PRE2 : Z.of_nat (length pre_r) <= 2) by (unfold pre_r; destruct (rr =? 0); cbn [length]; lia).
        assert (LVPd : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n).
        { intros p n H. rewrite LVd in H. apply List.in_app_or in H. destruct H as [H|H]; [| exact (LVPc p n H)].
          unfold pre_r in H. destruct (Z.eq_dec rr 0) as [Z0|NZ].
          - replace (rr =? 0) with true in H by (symmetry; apply Z.eqb_eq; exact Z0). destruct H.
          - replace (rr =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact NZ). destruct (PRF NZ) as (_ & _ & R3).
            cbn [In] in H. destruct H as [H|[H|[]]]; [injection H as <- <-; exact R3| injection H as <- <-; lia]. }
        lazymatch goal with A : ART RT Sd ?mb |- _ => pose proof (live_nodup RT AF Sd mb A LVPd) as NDd end. rewrite LVd in NDd.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1b) as PO1c.
        pose proof (prefix_fresh_obj pre_r (rt_live RT Sc) _ p1 v1 c1 NDd PO1c) as FRESH.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)) by (intros e He; rewrite LVd; apply List.in_or_app; right; exact He).
        pose proof (pix_obj_mono _ _ _ p1 v1 c1 SUBd PO1c) as PO1d.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS3) as POS4.
        lazymatch goal with A : ART RT Sd ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Sd) _ (rt_live RT Sd) _ mb rr vr _ _ _ PRd (keeps_live_refl _ mb)
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVd; repeat split; apply List.in_or_app; left; assumption)) as PRd2 end.
        clear PO1b PO1c POS3 KL PRd.
        hide PO1d. hide POS4. hide PRd2. hide NDd. hide FRESH. hide PRF.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd2, PRF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        lazymatch goal with K : keeps_live _ _ ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Sd) _ (rt_live RT Sd) _ mb rr vr _ _ _ PRd2 KL
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVd; repeat split; apply List.in_or_app; left; assumption)) as PRd3 end.
        clear PO1d POS4 PRd2 KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [rewrite LVd, List.length_app; lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear PO1e SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        unfold hid in FRESH. rewrite LVd, (live_destroy_app_fresh p1 v1 c1 pre_r (rt_live RT Sc) FRESH), LDS1 in LVe.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVe; apply List.in_or_app; right; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se)) by (intros e He; rewrite LVe; apply List.in_or_app; right; exact He).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        lazymatch goal with A : ART RT Se ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Se) _ (rt_live RT Se) _ mb rr vr _ _ _ PRd3 KL
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVe; repeat split; apply List.in_or_app; left; assumption)) as PRe end.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; apply List.in_app_or in H; destruct H as [H|H];
              [apply (LVPd p n); rewrite LVd; apply List.in_or_app; left; exact H| exact (LVPb p n H)]).
        lazymatch goal with A : ART RT Se ?mb |- _ => pose proof (live_nodup RT AF Se mb A LVPe) as NDe end. rewrite LVe in NDe.
        clear POS5 PRd3 KL.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRe NDe. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe; unfold pre_r; rewrite RZ; reflexivity).
          clear LVe. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply FIN; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRe as [Z0|(POR & _ & _ & _ & RDATA & RCM)]; [exfalso; exact (RNZ Z0)|].
          assert (LVe1 : rt_live RT Se = (p_data vr, rsize vr) :: (rr, 64) :: rt_live RT Sb)
            by (rewrite LVe; unfold pre_r; replace (rr =? 0) with false by (symmetry; apply Z.eqb_neq; exact RNZ); reflexivity).
          assert (NDe1 : List.NoDup (map fst ((p_data vr, rsize vr) :: (rr, 64) :: rt_live RT Sb)))
            by (unfold pre_r in NDe; replace (rr =? 0) with false in NDe by (symmetry; apply Z.eqb_neq; exact RNZ); exact NDe).
          clear LVe NDe.
          hide POS6. hide POR. hide NDe1.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, POR.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr _ KL POR) as POR2. clear POS6 POR KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := mkCmapv 0 0 0 0) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe1; cbn [length]; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in NDe1. rewrite LVe1 in LVf.
        repeat match type of LVf with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in LVf end.
        repeat match type of NDe1 with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in NDe1 end.
        rewrite (live_destroy_mid rr vr _ [] (rt_live RT Sb) RCM RDATA NDe1) in LVf. cbn [app] in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply FIN; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT2 : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 2 * (TEMPLATE_COST + GRAY3_COST + 2)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 pixs) (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x904d4 mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        pose proof GERODE as GK. unfold gray3_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pixs := p1) (vs := v1) (cvs := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ (GRAY3_DESTROY_RAS _) => rewrite ?unsigned_lit by ul; apply tr_gray3; unfold FUZZ_GRAY3_CALLS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        unfold new_pix8, new_pix8_live in *.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv _ /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in * end.
        lazymatch goal with H : rt_live RT Sd = _ |- _ => rename H into LVd end.
        set (pre_r := if rr =? 0 then @nil (Z * Z) else [(p_data vr, rsize vr); (rr, 64)]).
        assert (LVd' : rt_live RT Sd = pre_r ++ rt_live RT Sc) by (rewrite LVd; unfold pre_r; destruct (rr =? 0); reflexivity).
        clear LVd. rename LVd' into LVd.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (PRF : rr <> 0 -> In (rr, 64) pre_r /\ In (p_data vr, rsize vr) pre_r /\ 0 < rsize vr)
          by (intros NZ; destruct PRd as [Z0|(PO & _ & _ & _ & DNZ & _)]; [exfalso; exact (NZ Z0)|];
              destruct (pix_obj_chunks _ _ _ _ _ PO DNZ) as (_ & _ & I3 & _);
              unfold pre_r; replace (rr =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); cbn [In]; tauto).
        assert (PRE2 : Z.of_nat (length pre_r) <= 2) by (unfold pre_r; destruct (rr =? 0); cbn [length]; lia).
        assert (LVPd : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n).
        { intros p n H. rewrite LVd in H. apply List.in_app_or in H. destruct H as [H|H]; [| exact (LVPc p n H)].
          unfold pre_r in H. destruct (Z.eq_dec rr 0) as [Z0|NZ].
          - replace (rr =? 0) with true in H by (symmetry; apply Z.eqb_eq; exact Z0). destruct H.
          - replace (rr =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact NZ). destruct (PRF NZ) as (_ & _ & R3).
            cbn [In] in H. destruct H as [H|[H|[]]]; [injection H as <- <-; exact R3| injection H as <- <-; lia]. }
        lazymatch goal with A : ART RT Sd ?mb |- _ => pose proof (live_nodup RT AF Sd mb A LVPd) as NDd end. rewrite LVd in NDd.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1b) as PO1c.
        pose proof (prefix_fresh_obj pre_r (rt_live RT Sc) _ p1 v1 c1 NDd PO1c) as FRESH.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)) by (intros e He; rewrite LVd; apply List.in_or_app; right; exact He).
        pose proof (pix_obj_mono _ _ _ p1 v1 c1 SUBd PO1c) as PO1d.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS3) as POS4.
        lazymatch goal with A : ART RT Sd ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Sd) _ (rt_live RT Sd) _ mb rr vr _ _ _ PRd (keeps_live_refl _ mb)
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVd; repeat split; apply List.in_or_app; left; assumption)) as PRd2 end.
        clear PO1b PO1c POS3 KL PRd.
        hide PO1d. hide POS4. hide PRd2. hide NDd. hide FRESH. hide PRF.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd2, PRF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        lazymatch goal with K : keeps_live _ _ ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Sd) _ (rt_live RT Sd) _ mb rr vr _ _ _ PRd2 KL
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVd; repeat split; apply List.in_or_app; left; assumption)) as PRd3 end.
        clear PO1d POS4 PRd2 KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [rewrite LVd, List.length_app; lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear PO1e SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        unfold hid in FRESH. rewrite LVd, (live_destroy_app_fresh p1 v1 c1 pre_r (rt_live RT Sc) FRESH), LDS1 in LVe.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVe; apply List.in_or_app; right; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se)) by (intros e He; rewrite LVe; apply List.in_or_app; right; exact He).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        lazymatch goal with A : ART RT Se ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Se) _ (rt_live RT Se) _ mb rr vr _ _ _ PRd3 KL
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVe; repeat split; apply List.in_or_app; left; assumption)) as PRe end.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; apply List.in_app_or in H; destruct H as [H|H];
              [apply (LVPd p n); rewrite LVd; apply List.in_or_app; left; exact H| exact (LVPb p n H)]).
        lazymatch goal with A : ART RT Se ?mb |- _ => pose proof (live_nodup RT AF Se mb A LVPe) as NDe end. rewrite LVe in NDe.
        clear POS5 PRd3 KL.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRe NDe. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe; unfold pre_r; rewrite RZ; reflexivity).
          clear LVe. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT3; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRe as [Z0|(POR & _ & _ & _ & RDATA & RCM)]; [exfalso; exact (RNZ Z0)|].
          assert (LVe1 : rt_live RT Se = (p_data vr, rsize vr) :: (rr, 64) :: rt_live RT Sb)
            by (rewrite LVe; unfold pre_r; replace (rr =? 0) with false by (symmetry; apply Z.eqb_neq; exact RNZ); reflexivity).
          assert (NDe1 : List.NoDup (map fst ((p_data vr, rsize vr) :: (rr, 64) :: rt_live RT Sb)))
            by (unfold pre_r in NDe; replace (rr =? 0) with false in NDe by (symmetry; apply Z.eqb_neq; exact RNZ); exact NDe).
          clear LVe NDe.
          hide POS6. hide POR. hide NDe1.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, POR.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr _ KL POR) as POR2. clear POS6 POR KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := mkCmapv 0 0 0 0) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe1; cbn [length]; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in NDe1. rewrite LVe1 in LVf.
        repeat match type of LVf with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in LVf end.
        repeat match type of NDe1 with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in NDe1 end.
        rewrite (live_destroy_mid rr vr _ [] (rt_live RT Sb) RCM RDATA NDe1) in LVf. cbn [app] in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT3; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT1 : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r22 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 1 * (TEMPLATE_COST + GRAY3_COST + 2)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) r22 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x904a0 mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r22 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        pose proof GDILATE as GK. unfold gray3_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pixs := p1) (vs := v1) (cvs := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ (GRAY3_DESTROY_RAS _) => rewrite ?unsigned_lit by ul; apply tr_gray3; unfold FUZZ_GRAY3_CALLS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        unfold new_pix8, new_pix8_live in *.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv _ /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in * end.
        lazymatch goal with H : rt_live RT Sd = _ |- _ => rename H into LVd end.
        set (pre_r := if rr =? 0 then @nil (Z * Z) else [(p_data vr, rsize vr); (rr, 64)]).
        assert (LVd' : rt_live RT Sd = pre_r ++ rt_live RT Sc) by (rewrite LVd; unfold pre_r; destruct (rr =? 0); reflexivity).
        clear LVd. rename LVd' into LVd.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (PRF : rr <> 0 -> In (rr, 64) pre_r /\ In (p_data vr, rsize vr) pre_r /\ 0 < rsize vr)
          by (intros NZ; destruct PRd as [Z0|(PO & _ & _ & _ & DNZ & _)]; [exfalso; exact (NZ Z0)|];
              destruct (pix_obj_chunks _ _ _ _ _ PO DNZ) as (_ & _ & I3 & _);
              unfold pre_r; replace (rr =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); cbn [In]; tauto).
        assert (PRE2 : Z.of_nat (length pre_r) <= 2) by (unfold pre_r; destruct (rr =? 0); cbn [length]; lia).
        assert (LVPd : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n).
        { intros p n H. rewrite LVd in H. apply List.in_app_or in H. destruct H as [H|H]; [| exact (LVPc p n H)].
          unfold pre_r in H. destruct (Z.eq_dec rr 0) as [Z0|NZ].
          - replace (rr =? 0) with true in H by (symmetry; apply Z.eqb_eq; exact Z0). destruct H.
          - replace (rr =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact NZ). destruct (PRF NZ) as (_ & _ & R3).
            cbn [In] in H. destruct H as [H|[H|[]]]; [injection H as <- <-; exact R3| injection H as <- <-; lia]. }
        lazymatch goal with A : ART RT Sd ?mb |- _ => pose proof (live_nodup RT AF Sd mb A LVPd) as NDd end. rewrite LVd in NDd.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1b) as PO1c.
        pose proof (prefix_fresh_obj pre_r (rt_live RT Sc) _ p1 v1 c1 NDd PO1c) as FRESH.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)) by (intros e He; rewrite LVd; apply List.in_or_app; right; exact He).
        pose proof (pix_obj_mono _ _ _ p1 v1 c1 SUBd PO1c) as PO1d.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS3) as POS4.
        lazymatch goal with A : ART RT Sd ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Sd) _ (rt_live RT Sd) _ mb rr vr _ _ _ PRd (keeps_live_refl _ mb)
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVd; repeat split; apply List.in_or_app; left; assumption)) as PRd2 end.
        clear PO1b PO1c POS3 KL PRd.
        hide PO1d. hide POS4. hide PRd2. hide NDd. hide FRESH. hide PRF.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd2, PRF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        lazymatch goal with K : keeps_live _ _ ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Sd) _ (rt_live RT Sd) _ mb rr vr _ _ _ PRd2 KL
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVd; repeat split; apply List.in_or_app; left; assumption)) as PRd3 end.
        clear PO1d POS4 PRd2 KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [rewrite LVd, List.length_app; lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear PO1e SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        unfold hid in FRESH. rewrite LVd, (live_destroy_app_fresh p1 v1 c1 pre_r (rt_live RT Sc) FRESH), LDS1 in LVe.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVe; apply List.in_or_app; right; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se)) by (intros e He; rewrite LVe; apply List.in_or_app; right; exact He).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        lazymatch goal with A : ART RT Se ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Se) _ (rt_live RT Se) _ mb rr vr _ _ _ PRd3 KL
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVe; repeat split; apply List.in_or_app; left; assumption)) as PRe end.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; apply List.in_app_or in H; destruct H as [H|H];
              [apply (LVPd p n); rewrite LVd; apply List.in_or_app; left; exact H| exact (LVPb p n H)]).
        lazymatch goal with A : ART RT Se ?mb |- _ => pose proof (live_nodup RT AF Se mb A LVPe) as NDe end. rewrite LVe in NDe.
        clear POS5 PRd3 KL.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRe NDe. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe; unfold pre_r; rewrite RZ; reflexivity).
          clear LVe. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT2; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRe as [Z0|(POR & _ & _ & _ & RDATA & RCM)]; [exfalso; exact (RNZ Z0)|].
          assert (LVe1 : rt_live RT Se = (p_data vr, rsize vr) :: (rr, 64) :: rt_live RT Sb)
            by (rewrite LVe; unfold pre_r; replace (rr =? 0) with false by (symmetry; apply Z.eqb_neq; exact RNZ); reflexivity).
          assert (NDe1 : List.NoDup (map fst ((p_data vr, rsize vr) :: (rr, 64) :: rt_live RT Sb)))
            by (unfold pre_r in NDe; replace (rr =? 0) with false in NDe by (symmetry; apply Z.eqb_neq; exact RNZ); exact NDe).
          clear LVe NDe.
          hide POS6. hide POR. hide NDe1.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, POR.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr _ KL POR) as POR2. clear POS6 POR KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := mkCmapv 0 0 0 0) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe1; cbn [length]; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in NDe1. rewrite LVe1 in LVf.
        repeat match type of LVf with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in LVf end.
        repeat match type of NDe1 with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in NDe1 end.
        rewrite (live_destroy_mid rr vr _ [] (rt_live RT Sb) RCM RDATA NDe1) in LVf. cbn [app] in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT2; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT0 : forall (S : rts RT) (mE : mem) (jS j1 j2 : list byte)
                  (r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r20 r21 r22 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [CB 8 jS] -> rw_cells asegs mE (fr + 64) [CB 8 j1] -> rw_cells asegs mE (fr + 96) [CB 8 j2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 0 * (TEMPLATE_COST + GRAY3_COST + 2)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          (Z_to_bv 64 pixs) r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) r20 r21 r22 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90458 mE))) QF) end.
      { intros S mE jjS jj1 jj2 r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r20 r21 r22 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        pose proof GCLOSE as GK. unfold gray3_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pixs := p1) (vs := v1) (cvs := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ (GRAY3_DESTROY_RAS _) => rewrite ?unsigned_lit by ul; apply tr_gray3; unfold FUZZ_GRAY3_CALLS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        unfold new_pix8, new_pix8_live in *.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv _ /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in * end.
        lazymatch goal with H : rt_live RT Sd = _ |- _ => rename H into LVd end.
        set (pre_r := if rr =? 0 then @nil (Z * Z) else [(p_data vr, rsize vr); (rr, 64)]).
        assert (LVd' : rt_live RT Sd = pre_r ++ rt_live RT Sc) by (rewrite LVd; unfold pre_r; destruct (rr =? 0); reflexivity).
        clear LVd. rename LVd' into LVd.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (PRF : rr <> 0 -> In (rr, 64) pre_r /\ In (p_data vr, rsize vr) pre_r /\ 0 < rsize vr)
          by (intros NZ; destruct PRd as [Z0|(PO & _ & _ & _ & DNZ & _)]; [exfalso; exact (NZ Z0)|];
              destruct (pix_obj_chunks _ _ _ _ _ PO DNZ) as (_ & _ & I3 & _);
              unfold pre_r; replace (rr =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ); cbn [In]; tauto).
        assert (PRE2 : Z.of_nat (length pre_r) <= 2) by (unfold pre_r; destruct (rr =? 0); cbn [length]; lia).
        assert (LVPd : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n).
        { intros p n H. rewrite LVd in H. apply List.in_app_or in H. destruct H as [H|H]; [| exact (LVPc p n H)].
          unfold pre_r in H. destruct (Z.eq_dec rr 0) as [Z0|NZ].
          - replace (rr =? 0) with true in H by (symmetry; apply Z.eqb_eq; exact Z0). destruct H.
          - replace (rr =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact NZ). destruct (PRF NZ) as (_ & _ & R3).
            cbn [In] in H. destruct H as [H|[H|[]]]; [injection H as <- <-; exact R3| injection H as <- <-; lia]. }
        lazymatch goal with A : ART RT Sd ?mb |- _ => pose proof (live_nodup RT AF Sd mb A LVPd) as NDd end. rewrite LVd in NDd.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1b) as PO1c.
        pose proof (prefix_fresh_obj pre_r (rt_live RT Sc) _ p1 v1 c1 NDd PO1c) as FRESH.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)) by (intros e He; rewrite LVd; apply List.in_or_app; right; exact He).
        pose proof (pix_obj_mono _ _ _ p1 v1 c1 SUBd PO1c) as PO1d.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS3) as POS4.
        lazymatch goal with A : ART RT Sd ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Sd) _ (rt_live RT Sd) _ mb rr vr _ _ _ PRd (keeps_live_refl _ mb)
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVd; repeat split; apply List.in_or_app; left; assumption)) as PRd2 end.
        clear PO1b PO1c POS3 KL PRd.
        hide PO1d. hide POS4. hide PRd2. hide NDd. hide FRESH. hide PRF.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd2, PRF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        lazymatch goal with K : keeps_live _ _ ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Sd) _ (rt_live RT Sd) _ mb rr vr _ _ _ PRd2 KL
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVd; repeat split; apply List.in_or_app; left; assumption)) as PRd3 end.
        clear PO1d POS4 PRd2 KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [rewrite LVd, List.length_app; lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear PO1e SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        unfold hid in FRESH. rewrite LVd, (live_destroy_app_fresh p1 v1 c1 pre_r (rt_live RT Sc) FRESH), LDS1 in LVe.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVe; apply List.in_or_app; right; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se)) by (intros e He; rewrite LVe; apply List.in_or_app; right; exact He).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        lazymatch goal with A : ART RT Se ?mb |- _ =>
          pose proof (pix8_opt_carry (rt_live RT Se) _ (rt_live RT Se) _ mb rr vr _ _ _ PRd3 KL
                        ltac:(intros NZ; destruct (PRF NZ) as (I1 & I2 & _); rewrite LVe; repeat split; apply List.in_or_app; left; assumption)) as PRe end.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; apply List.in_app_or in H; destruct H as [H|H];
              [apply (LVPd p n); rewrite LVd; apply List.in_or_app; left; exact H| exact (LVPb p n H)]).
        lazymatch goal with A : ART RT Se ?mb |- _ => pose proof (live_nodup RT AF Se mb A LVPe) as NDe end. rewrite LVe in NDe.
        clear POS5 PRd3 KL.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRe NDe. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe; unfold pre_r; rewrite RZ; reflexivity).
          clear LVe. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT1; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRe as [Z0|(POR & _ & _ & _ & RDATA & RCM)]; [exfalso; exact (RNZ Z0)|].
          assert (LVe1 : rt_live RT Se = (p_data vr, rsize vr) :: (rr, 64) :: rt_live RT Sb)
            by (rewrite LVe; unfold pre_r; replace (rr =? 0) with false by (symmetry; apply Z.eqb_neq; exact RNZ); reflexivity).
          assert (NDe1 : List.NoDup (map fst ((p_data vr, rsize vr) :: (rr, 64) :: rt_live RT Sb)))
            by (unfold pre_r in NDe; replace (rr =? 0) with false in NDe by (symmetry; apply Z.eqb_neq; exact RNZ); exact NDe).
          clear LVe NDe.
          hide POS6. hide POR. hide NDe1.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        cwalk [e_pixDeserialize; 0x9309c; 0xa958c; 0xa7d74; 0xa6a38; 0xa90b0; 0x917e8].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, POR.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr _ KL POR) as POR2. clear POS6 POR KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := mkCmapv 0 0 0 0) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, GRAY3_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe1; cbn [length]; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in NDe1. rewrite LVe1 in LVf.
        repeat match type of LVf with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in LVf end.
        repeat match type of NDe1 with context [4 * (p_wpl ?v * p_h ?v)] => change (4 * (p_wpl v * p_h v)) with (rsize v) in NDe1 end.
        rewrite (live_destroy_mid rr vr _ [] (rt_live RT Sb) RCM RDATA NDe1) in LVf. cbn [app] in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT1; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      unfold hid in POBJ.
      to_entry.
      eapply CONT0; try eassumption.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POBJ
           | |- rt_live _ _ = _ => reflexivity
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, GRAY3_COST, RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia
           | |- ?g => idtac "LEFT:" g
           end.
Qed.
End FZ.

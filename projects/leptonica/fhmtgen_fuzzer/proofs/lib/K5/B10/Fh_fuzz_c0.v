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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_deserkit Lept_gmax_defs D_iface D_defs D_libiface Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit Gm_drvkit2 Gm_fzkit Gm_leaf Fh_iface Fh_sel_iface Fh_statics Fh_selkit Fh_fzlen Fh_fzkit Fh_fuzz_defs LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section FZ.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis DESER : pixDeserialize_cps RT.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis DNULL : pixDestroy_null_cps RT.
Hypothesis PCOPY : pixCopy_cps RT.
Hypothesis SAHM : selaAddHitMiss_cps RT.
Hypothesis SAD : selaDestroy_cps RT.
Hypothesis HMT : pixHMTDwa_1_cps RT.

Theorem fuzz_c0 : fuzz_case RT 0.
Proof using AF RC GP DESER DESTROY DNULL PCOPY SAHM SAD HMT.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST -> -> -> RATOP DPOS BSL BYTES OWN FR0 LVP LVB CRB S0INV LIBm SSP ART0 MI ST LOW LOR SPT SPA SPB AL.
  destruct LIBm as (((LSEV & LALLOC & LDEALLOC) & (h0 & LHAND)) & LSEL).
  unfold LIB_SEL, LIB_SEL_AT in LSEL. clear BYTES.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, D_libiface.e_fuzz, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold D_libiface.FUZZ_STACK, D_libiface.FUZZ_COST, D_libiface.FUZZ_LIVE, LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside Lept_iface.LIB_FP a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  hide S0INV. hide LSEL.
  park_disj. carve_frame 128%nat ST.
  clear_acc.
  Time walk_to AF MST [(usp - 128, usp)] [e_stack_malloc 2%nat].
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC:" pc end.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_2 RT GP) as SM2; unfold stack_malloc_contract' in SM2; eapply SM2 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 2%nat 256 ltac:(fun Ha => exact (proj1 Ha)).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "FRAME_OPEN".
  destruct (Z_lt_ge_dec (Z.of_nat (length bs)) 3) as [SZ|SZ].
  - (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x911e4].
    lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC:" pc end.
    unfold hid in LSEL.
    frame_release_raw RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0x911ec
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact (proj1 Hx)) LSEV LALLOC LDEALLOC LHAND LSEL.
    idtac "RELEASED".
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 128, usp)] (@nil Z).
    
    lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC:" pc end.
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [assumption| split; assumption]|].
    split; [intros a Ha Ho; apply (AGF a); split; [exact Ha| unfold D_libiface.LIB_FP, Lept_iface.LIB_FP, g_stderr_handler in *; cbn [outside] in *; tauto]|].
    split; [split; [split; [assumption| split; assumption]| exists h0; assumption]|].
    unfold hid in LSEL. exact (LIB_SEL_keep RT GP _ _ _ m _ LSEL AGF).
  - idtac "SMALL_ARM_DONE".
    Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32); (986848, 986856)]
                 [e_pixDeserialize; e_selaAddHitMiss; e_pixCopy; e_pixHMTDwa_1; e_pixDestroy; e_selaDestroy].
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
    { eapply DS with (lo := lo) (dp := d) (n := Z.of_nat (length bs)) (ras := [D_libiface.RA_TOP]); rt_side idtac.
      - right. split; [exact DAL|]. exists p0, n0. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. split; [exact OIN | lia].
      - unfold uctx. (rewrite !unsigned_lit by lia). unfold parked in S0INV.
        (apply chain_ok_push with (fp1 := bv_unsigned s0)).
        + lia.
        + (clear - SPA; Z.div_mod_to_equations; lia).
        + (unfold USTACK_TOP; lia).
        + (unfold D_libiface.RA_TOP; lia).
        + (apply bv_unsigned_in_range).
        + (rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned).
          (lazymatch type of FRrec2 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end). (exact FRrec2).
        + (cbn [chain_ok]; unfold link_invalid; lia).
      - (exact tr_deser).
      - lenv_tac.
      - unfold RASTER_COST. lres_tac. }
    idtac "DESER_APPLIED".
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with H : ?p = 0 \/ _ |- _ => rename H into POBJ; set (pixs := p) in * end.
    lazymatch goal with H : pixs = 0 -> rt_live RT _ = _ |- _ => rename H into LVZ end.
    lazymatch goal with H : pixs <> 0 -> live_destroy _ _ _ _ = _ |- _ => rename H into LVD end.
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into Sb end.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -128) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r24 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -128) -> rw_cells asegs mE (usp + -128) cs ->
          wr_at asegs mE fr 8 -> wr_at asegs mE (fr / 8 + 2147450880) 32 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE ->
          rt_live RT S = rt_live RT Σ ->
          rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 2 ^ 33 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 r22 r23 r24 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s11 r28 r29 r30 r31 F' fc' 0x91148 mE))) QF) end.
    { intros S mE r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r24 r28 r29 r30 r31 F' fc'
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
      destruct (wr_at_rw_CB mE fr 8 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 32 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 8) with 8%nat in FRME. change (Z.to_nat 32) with 32%nat in FSHE.
      unfold entry_st.
      Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x911e4].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      Time frame_release_k RT AF GP MST Σ fr 2%nat 256 PF AGF PFS usp lo 0x911ec
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN => idtac).
      Time walk_to AF MST [(usp - 128, usp)] (@nil Z).
      
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
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
        split; [intros a Ha Ho; apply (AGF a); split; [exact Ha| unfold D_libiface.LIB_FP, Lept_iface.LIB_FP, g_stderr_handler in *; cbn [outside] in *; tauto]|].
        split; [lazymatch goal with LHx : LIBH ?mm |- LIB_A0 ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end|].
        unfold hid in LSEL. exact (LIB_SEL_keep RT GP _ _ _ m _ LSEL AGF). }
      rewrite LV2, FRS2, SP2, CR2.
      split; [exact ELV|]. split; [exact FR0|]. split; [exact ESP0| lia]. }
    idtac "EPI_PROVED".
    destruct (Z.eq_dec pixs 0) as [PZ|PNZ].
    + (* [comment removed for export] *)
      clear POBJ LVD. pose proof (LVZ PZ) as LVE. clear LVZ. rewrite PZ in *.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x91148].
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
           | |- wr_at asegs _ _ 32 => exact (proj2 FSH)
           | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- _ <= rt_credit _ _ => unfold RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia
           | |- ?g => idtac "LEFT:" g
           end.
    + idtac "NULL_ARM_DONE".
      destruct POBJ as [PZ|(POBJ & VDATA)]; [contradiction|]. clear LVZ. pose proof (LVD PNZ) as LVE. clear LVD.
      lazymatch type of POBJ with pix_obj _ _ _ ?vv ?cc => set (vs := vv) in *; set (cvs := cc) in * end.
      lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sb) -> 0 < n |- _ => rename H into LVPb end.
      lazymatch goal with H : Z.of_nat (length (rt_live RT Sb)) <= _ |- _ => rename H into LVXb end.
      repeat match goal with E : rt_live RT _ = rt_live RT Σ |- _ => rewrite E in LVE end.
      repeat match goal with E : rt_live RT _ = rt_live RT Σ |- _ => rewrite E in LVXb end.
      assert (SUB0b : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Sb)) by (intros e He; rewrite <- LVE in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
      assert (PS0 : 0 < pixs) by (destruct POBJ as (_ & (_ & P0 & _) & _); exact P0).
      pose proof POBJ as (_ & (PSIN & _) & _). chunk_facts RT AF GP pixs 64.
      (* [comment removed for export] *)
      split_last_CB FRM [8%nat; 8%nat; 24%nat; 8%nat; 24%nat; 8%nat; 24%nat; 8%nat; 112%nat].
      lazymatch goal with H : rw_cells asegs _ (fr / 8 + 2147450880) ?c |- _ =>
        lazymatch c with context [CB 12 ?j] => set (js12 := j) in *; clearbody js12 end end.
      hide POBJ.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells asegs _ (usp + -128) ?cs |- _ =>
        assert (FIN : forall (S : rts RT) (mE : mem) (xr : word) (sela arr copy : Z) (sels : list (Z * selv * list byte)) (vc : pixv) (cc : cmapv)
                  (la lc : list (Z * Z)) (j8 j24a j24b j24c j24d j112 jsx : list byte)
                  (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r22 r23 r24 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -128) -> rw_cells asegs mE (usp + -128) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 109806); C8 (Z_to_bv 64 593736); CB 8 j8] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs); CB 24 j24a] -> rw_cells asegs mE (fr + 64) [C8 (Z_to_bv 64 sela); CB 24 j24b] ->
            rw_cells asegs mE (fr + 96) [C8 (Z_to_bv 64 copy); CB 24 j24c] -> rw_cells asegs mE (fr + 128) [C8 xr; CB 112 j112] ->
            rw_cells asegs mE (fr / 8 + 2147450880)
              [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
               C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
               C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); CB 12 jsx] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE ->
            pix_obj (rt_live RT Sb) mE pixs vs cvs -> pix_obj lc mE copy vc cc -> p_data vc <> 0 -> sela_obj la mE sela arr sels ->
            la = sela_live sela arr sels ++ rt_live RT Sb -> live_destroy copy vc cc lc = la -> rt_live RT S = lc ->
            (forall p n, In (p, n) lc -> 0 < n) -> Z.of_nat (length lc) <= LIVE_MAX -> Z.of_nat (length la) <= LIVE_MAX ->
            rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - (2 ^ 33 - 4) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 32)) r22 r23 r24
                                          (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) s11 r28 r29 r30 r31 F' fc' 0x91120 mE))) QF) end.
      { intros S mE xr sela arr copy sels vc cc la lc j8 j24a j24b j24c j24d j112 jsx r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r22 r23 r24 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE SLE CPE RE FSE LHE SSPE AGE POSE POCE VCDATA SAOE ELA ELD ELV LVPE LENE LENA EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | SLE => fail | CPE => fail | RE => fail | FSE => fail | _ => clear H end end.
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
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 128) by (rewrite ESP0; ul).
        hide POSE. hide POCE. hide SAOE. hide ELV.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDeserialize; e_selaAddHitMiss; e_pixCopy; e_pixHMTDwa_1; e_pixDestroy; e_selaDestroy].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHBc. split_at SHBc 12%nat SHBcb. split_at SHBcb 1%nat SHBcc. clear SHBc SHBcc.
        pose proof (rw_cells_head _ _ _ _ CPE) as CPE1.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE, POCE, SAOE, ELV.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame2 RT AF Sx mm fr usp (usp - 128) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL.
        assert (SUBLA : forall e, In e la -> In e lc) by (intros e He; rewrite <- ELD in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        assert (SUBSB : forall e, In e (rt_live RT Sb) -> In e la) by (intros e He; rewrite ELA; apply in_or_app; right; exact He).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBLA e (SUBSB e He))) POSE) as POS1.
        pose proof (pix_obj_keep _ _ _ copy vc cc KL POCE) as POC1.
        pose proof (sela_obj_keep2 la la _ _ sela arr sels SAOE (sela_live_in la _ sela arr sels SAOE) (keeps_live_sub _ _ _ _ KL SUBLA)) as SAO1.
        clear POSE POCE SAOE KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := copy) (v := vc) (cv := cc) (ras := [D_libiface.RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 2%nat; rewrite EFR; change (fs_size 2) with 256;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHBcb as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact CPE1
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POC1
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold D_libiface.RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPE]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        idtac "DESTROY_COPY_APPLIED".
        clear POC1 SHBcb CPE1.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into S1 end.
        lazymatch goal with H : rt_live RT S1 = live_destroy copy vc cc _ |- _ => rewrite ELV, ELD in H; rename H into LV1 end.
        assert (FRS1 : rt_frames RT S1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A1 : ART RT S1 ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF S1 mb fr 2%nat 96 bb kk xx A1 ltac:(rewrite FRS1; left; reflexivity) ltac:(lia) ltac:(change (fs_size 2) with 256; lia) Hb Hx)) end.
        rewrite LV1 in KL.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBSB) POS1) as POS2.
        pose proof (sela_obj_keep2 la la _ _ sela arr sels SAO1 (sela_live_in la _ sela arr sels SAO1) KL) as SAO2.
        clear POS1 SAO1 KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV1; apply SUBSB; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        assert (SPL1 : rt_sp0 RT S1 - 8388608 <= usp - 128) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (LVP1 : forall p n, In (p, n) la -> 0 < n) by (intros p n Hp; exact (LVPE p n (SUBLA _ Hp))).
        lazymatch goal with A1 : ART RT S1 ?mb |- _ => pose proof (live_nodup RT AF S1 mb A1 ltac:(rewrite LV1; exact LVP1)) as ND1 end. rewrite LV1, ELA in ND1.
        hide POS2. hide SAO2. hide LV1. hide ND1.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDeserialize; e_selaAddHitMiss; e_pixCopy; e_pixHMTDwa_1; e_pixDestroy; e_selaDestroy].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        (* [comment removed for export] *)
        pose proof FSE as SHBp. split_at SHBp 4%nat SHBpb. split_at SHBpb 1%nat SHBpc. clear SHBp SHBpc.
        pose proof (rw_cells_head _ _ _ _ PSE) as PSE1.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS2, SAO2, LV1.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame2 RT AF Sx mm fr usp (usp - 128) bb kk xx A ltac:(rewrite FRS1; left; reflexivity) SPL1 Hb Hx)) end end.
        rewrite LV1 in KL.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBSB) POS2) as POS3.
        pose proof (sela_obj_keep2 la la _ _ sela arr sels SAO2 (sela_live_in la _ sela arr sels SAO2) KL) as SAO3.
        clear POS2 SAO2 KL.
        pose proof DESTROY as DY2. unfold pixDestroy_cps in DY2.
        eapply cps_seq.
        { eapply DY2 with (lo := lo) (pp := fr + 32) (pix := pixs) (v := vs) (cv := cvs) (ras := [D_libiface.RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 2%nat; rewrite FRS1; change (fs_size 2) with 256;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHBpb as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact PSE1
               | |- pix_obj _ _ _ _ _ => rewrite LV1; exact (pix_obj_mono _ _ _ pixs vs cvs SUBSB POS3)
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold D_libiface.RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRS1, FR0; cbn [length]; lia| split; [rewrite LV1; lia| split; [lia| rewrite LV1; exact LVP1]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        idtac "DESTROY_PIXS_APPLIED".
        clear SHBpb PSE1.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into S2 end.
        lazymatch goal with H : rt_live RT S2 = live_destroy pixs vs cvs _ |- _ => rename H into LV2 end.
        assert (LV2' : rt_live RT S2 = sela_live sela arr sels ++ rt_live RT Σ).
        { rewrite LV2, LV1, ELA. unfold hid in ND1.
          rewrite (live_destroy_app_fresh pixs vs cvs (sela_live sela arr sels) (rt_live RT Sb) (prefix_fresh_obj _ _ _ pixs vs cvs ND1 POS3)).
          rewrite LVE. reflexivity. }
        assert (FRS2 : rt_frames RT S2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SUBS2 : forall e, In e (sela_live sela arr sels) -> In e (rt_live RT S2)) by (intros e He; rewrite LV2'; apply in_or_app; left; exact He).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A2 : ART RT S2 ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF S2 mb fr 2%nat 32 bb kk xx A2 ltac:(rewrite FRS2; left; reflexivity) ltac:(lia) ltac:(change (fs_size 2) with 256; lia) Hb Hx)) end.
        pose proof (sela_obj_keep2 la (rt_live RT S2) _ _ sela arr sels SAO3 SUBS2 KL) as SAO4.
        clear POS3 SAO3 KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV2'; apply in_or_app; right; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        assert (SPL2 : rt_sp0 RT S2 - 8388608 <= usp - 128) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (LVP2 : forall p n, In (p, n) (rt_live RT S2) -> 0 < n).
        { intros p n Hp. rewrite LV2' in Hp. apply in_app_or in Hp. destruct Hp as [Hp|Hp]; [exact (sela_obj_pos _ _ _ _ _ SAO4 p n Hp)| exact (LVP p n Hp)]. }
        lazymatch goal with A2 : ART RT S2 ?mb |- _ => pose proof (live_nodup RT AF S2 mb A2 LVP2) as ND2 end.
        clear LV2. hide SAO4. hide LV2'. hide ND2. hide LVP2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDeserialize; e_selaAddHitMiss; e_pixCopy; e_pixHMTDwa_1; e_pixDestroy; e_selaDestroy].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        (* [comment removed for export] *)
        pose proof FSE as SHBs. split_at SHBs 8%nat SHBsb. split_at SHBsb 1%nat SHBsc. clear SHBs SHBsc.
        pose proof (rw_cells_head _ _ _ _ SLE) as SLE1.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in SAO4, LV2', LVP2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame2 RT AF Sx mm fr usp (usp - 128) bb kk xx A ltac:(rewrite FRS2; left; reflexivity) SPL2 Hb Hx)) end end.
        pose proof (sela_obj_keep2 _ (rt_live RT S2) _ _ sela arr sels SAO4 SUBS2 KL) as SAO5.
        clear SAO4 KL.
        eapply cps_seq.
        { eapply SAD with (lo := lo) (pp := fr + 64) (sela := sela) (arr := arr) (sels := sels) (l1 := @nil (Z * Z)) (l2 := rt_live RT Σ); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL, parked in *; split;
                   [ right; exists fr, 2%nat; rewrite FRS2; change (fs_size 2) with 256;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHBsb as [[_ B] _]; exact B
                   | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact SLE1
               | |- sela_obj _ _ _ _ _ => exact SAO5
               | |- rt_live _ _ = _ => exact LV2'
               | |- forall _ _, In _ _ -> _ => exact LVP2
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- ?g => idtac "LEFT:" g
               end. }
        idtac "SAD_APPLIED".
        clear SHBsb SLE1 SAO5.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into S3 end.
        lazymatch goal with H : rt_live RT S3 = live_remove_all _ _ |- _ => rename H into LV3 end.
        assert (LV3' : rt_live RT S3 = rt_live RT Σ).
        { rewrite LV3, LV2'. unfold hid in ND2. rewrite LV2' in ND2.
          exact (sela_destroy_live sela arr sels [] (rt_live RT Σ) ND2). }
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV3'; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        clear LV3. hide LV3'.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x91148].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
        lazymatch goal with MUx : munch _ ?mm _ |- _ =>
          agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                             repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
        pose proof (rw_cells_head _ _ _ _ FHE) as FHE1.
        to_entry. unfold hid in LV3'.
        eapply EPI; try eassumption.
        - exact (proj2 FHE1).
        - lazymatch goal with H : rw_cells asegs _ (_ / 8 + 2147450880) _ |- _ => exact (proj2 H) end.
        - repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity.
        - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.
        - repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia. }
      idtac "FIN_PROVED".
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells asegs _ (usp + -128) ?cs |- _ =>
        assert (ROUND : forall (k : nat) (i : Z) (S : rts RT) (mE : mem) (xr : word) (sela arr copy : Z) (sels : list (Z * selv * list byte)) (vc : pixv) (cc : cmapv)
                  (la lc : list (Z * Z)) (j8 j24a j24b j24c j112 jsx : list byte)
                  (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
            Z.of_nat k = 10 - i -> (1 <= k)%nat -> 0 <= i ->
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -128) -> rw_cells asegs mE (usp + -128) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 109806); C8 (Z_to_bv 64 593736); CB 8 j8] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs); CB 24 j24a] -> rw_cells asegs mE (fr + 64) [C8 (Z_to_bv 64 sela); CB 24 j24b] ->
            rw_cells asegs mE (fr + 96) [C8 (Z_to_bv 64 copy); CB 24 j24c] -> rw_cells asegs mE (fr + 128) [C8 xr; CB 112 j112] ->
            rw_cells asegs mE (fr / 8 + 2147450880)
              [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
               C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
               C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); CB 12 jsx] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE ->
            pix_obj (rt_live RT Sb) mE pixs vs cvs -> pix_obj lc mE copy vc cc -> p_data vc <> 0 -> sela_obj la mE sela arr sels -> hm_sels_ok sels ->
            la = sela_live sela arr sels ++ rt_live RT Sb -> live_destroy copy vc cc lc = la -> rt_live RT S = lc ->
            (forall p n, In (p, n) lc -> 0 < n) -> Z.of_nat (length lc) + 12 <= LIVE_MAX -> Z.of_nat (length la) <= LIVE_MAX ->
            rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - ((RASTER_COST + 64) + TEMPLATE_COST + 1 + i * (HMT_COST + 2)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 10) (Z_to_bv 64 i) (Z_to_bv 64 (fr + 128))
                                          (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) s11 r28 r29 r30 r31 F' fc' 0x910ec mE))) QF) end.
      { induction k as [|k IH]; intros i S mE xr sela arr copy sels vc cc la lc j8 j24a j24b j24c j112 jsx r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
          HK HK1 HI ARTE MIE STE FRE FHE PSE SLE CPE RE FSE LHE SSPE AGE POSE POCE VCDATA SAOE HMOK ELA ELD ELV LVPE LENE LENA EFR ESP0 ECR.
        { lia. }
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | SLE => fail | CPE => fail | RE => fail | FSE => fail | _ => clear H end end.
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
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 128) by (rewrite ESP0; ul).
        assert (SUBLA : forall e, In e la -> In e lc) by (intros e He; rewrite <- ELD in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        assert (SUBSB : forall e, In e (rt_live RT Sb) -> In e la) by (intros e He; rewrite ELA; apply in_or_app; right; exact He).
        (* [comment removed for export] *)
        destruct HMOK as (HML & HMJ). pose proof (HMJ (Z.to_nat i) ltac:(lia)) as HMI. cbv zeta in HMI.
        set (ei := nth (Z.to_nat i) sels (0, mkSelv 0 0 0 0 0 0 [], [])) in *.
        assert (EIN : In ei sels) by (apply nth_In; lia).
        pose proof SAOE as (SAC & (SAIN & SA0 & SA16 & _) & (ARIN & AR0 & AR16 & _) & L50 & ARRC & SELS).
        pose proof (proj1 (Forall_forall _ _) SELS ei EIN) as SOI. cbv beta in SOI.
        destruct ei as [[seli vi] nmi] eqn:EEI. cbn [fst snd] in SOI, HMI. destruct HMI as (_ & _ & ENMI).
        pose proof SOI as ((SCI & (SIIN & SI0 & SI16 & _) & _) & NMBI & (NMIN & NM0 & NM16 & _) & NMLI).
        unfold sela_cells in SAC. unfold sel_cells in SCI. rewrite HML in SAC. change (Z.of_nat 10) with 10 in SAC.
        idtac "ROUND_SETUP".
        assert (INSA : In (sela, 16) lc) by (exact (SUBLA _ SAIN)). assert (INAR : In (arr, 400) lc) by (exact (SUBLA _ ARIN)).
        assert (INSI : In (seli, 32) lc) by (exact (SUBLA _ SIIN)). assert (INNM : In (s_name vi, 8) lc) by (exact (SUBLA _ NMIN)).
        hide POSE. hide POCE. hide SAOE. hide SOI.
        chunk_facts RT AF GP sela 16. chunk_facts RT AF GP arr 400. chunk_facts RT AF GP seli 32. chunk_facts RT AF GP (s_name vi) 8.
        replace (map (fun e : Z * selv * list byte => C8 (Z_to_bv 64 (fst (fst e)))) sels ++ repeat (C8 (Z_to_bv 64 0)) (50 - length sels))
          with (map C8 (map (fun e : Z * selv * list byte => Z_to_bv 64 (fst (fst e))) sels ++ repeat (Z_to_bv 64 0) (50 - length sels))) in ARRC
          by (rewrite map_app, map_map, map_repeat; reflexivity).
        apply rw_cells_C8s_u64arr in ARRC.
        set (ws := map (fun e : Z * selv * list byte => Z_to_bv 64 (fst (fst e))) sels ++ repeat (Z_to_bv 64 0) (50 - length sels)) in *.
        assert (UAL : Z.of_nat (length ws) = 50) by (unfold ws; rewrite length_app, length_map, repeat_length; lia).
        assert (NTH : nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 seli)).
        { unfold ws. rewrite nth_error_app1 by (rewrite length_map; lia). rewrite nth_error_map.
          rewrite (nth_error_nth' sels (n := Z.to_nat i) (0, mkSelv 0 0 0 0 0 0 [], [])) by lia.
          fold ei. rewrite EEI. reflexivity. }
        assert (SPLX : rt_sp0 RT S - 8388608 <= usp - 256) by (rewrite ESP0; ul).
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
        Time walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0xb0034].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        assert (I10 : 0 <= i < 10) by lia.
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u64arr_read asegs mm arr ws i (Z_to_bv 64 seli) (Z_to_bv 64 (arr + i * 8)) ARRC NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
        lstep. clear RD.
        Time awalk [0xb0144].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        Time awalk [e_pixHMTDwa_1].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        (* [comment removed for export] *)
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE, POCE, SAOE, SOI.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame2 RT AF Sx mm fr usp (usp - 256) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLX Hb Hx)) end end.
        rewrite ELV in KL.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBLA e (SUBSB e He))) POSE) as POS1.
        pose proof (pix_obj_keep _ _ _ copy vc cc KL POCE) as POC1.
        pose proof (sela_obj_keep2 la la _ _ sela arr sels SAOE (sela_live_in la _ sela arr sels SAOE) (keeps_live_sub _ _ _ _ KL SUBLA)) as SAO1.
        clear POSE POCE SAOE SOI KL.
        idtac "HMT_PRE".
        pose proof HMT as HM. unfold pixHMTDwa_1_cps in HM.
        eapply cps_seq.
        { eapply HM with (lo := lo) (pixs := copy) (name := s_name vi) (vs := vc) (cvs := cc) (i := Z.to_nat i) (ras := [D_libiface.RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POC1
               | |- p_data _ <> 0 => exact VCDATA
               | |- hm_name_arg _ _ _ _ _ => unfold hm_name_arg; split; [lia| split; [rewrite ELV; exact INNM| rewrite <- ENMI; exact NMBI]]
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold D_libiface.RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- bv_unsigned _ = _ => rewrite ?unsigned_lit by ul; reflexivity
               | |- _ = [_] => reflexivity
               | |- LIB_SEL _ => unfold hid in LSEL; exact (LIB_SEL_keep RT GP _ _ _ m _ LSEL AGF)
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [| rewrite ELV; exact LVPE]]];
                   pose proof fh_fuzz_need_ok as FNO; unfold FH_FUZZ_NEED, HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST, FUZZ_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end. }
        idtac "HMT_APPLIED".
        (* [comment removed for export] *)
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into S1 end.
        (* [comment removed for export] *)
        lazymatch goal with FRx : rw_cells asegs _ (usp + -128) ?cs |- _ =>
          assert (REND : forall (SY : rts RT) (mY : mem) (xrY : word) (k8y k24ay k24by k24cy k112y ksxy : list byte)
                    (qq1 qq5 qq6 qq7 qq10 qq11 qq12 qq13 qq14 qq15 qq16 qq17 qq28 qq29 qq30 qq31 : word) FY fcY,
              ART RT SY mY -> mem_inv asegs mY -> stk asegs mY lo (usp + -128) -> rw_cells asegs mY (usp + -128) cs ->
              rw_cells asegs mY fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 109806); C8 (Z_to_bv 64 593736); CB 8 k8y] ->
              rw_cells asegs mY (fr + 32) [C8 (Z_to_bv 64 pixs); CB 24 k24ay] -> rw_cells asegs mY (fr + 64) [C8 (Z_to_bv 64 sela); CB 24 k24by] ->
              rw_cells asegs mY (fr + 96) [C8 (Z_to_bv 64 copy); CB 24 k24cy] -> rw_cells asegs mY (fr + 128) [C8 xrY; CB 112 k112y] ->
              rw_cells asegs mY (fr / 8 + 2147450880)
                [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
                 C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
                 C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); CB 12 ksxy] ->
              LIBH mY -> io_ssp mY -> agree_on PF m mY ->
              pix_obj (rt_live RT Sb) mY pixs vs cvs -> pix_obj lc mY copy vc cc -> sela_obj la mY sela arr sels ->
              rt_live RT SY = lc ->
              rt_frames RT SY = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT SY = rt_sp0 RT Σ ->
              rt_credit RT Σ - ((RASTER_COST + 64) + TEMPLATE_COST + 1 + (i + 1) * (HMT_COST + 2)) <= rt_credit RT SY ->
              cps asegs (ASTA RT SY PMc (eq (entry_st qq1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) qq5 qq6 qq7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
                                            qq10 qq11 qq12 qq13 qq14 qq15 qq16 qq17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 10) (Z_to_bv 64 i) (Z_to_bv 64 (fr + 128))
                                            (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) s11 qq28 qq29 qq30 qq31 FY fcY 0x91118 mY))) QF) end.
        { intros SY mY xrY k8y k24ay k24by k24cy k112y ksxy qq1 qq5 qq6 qq7 qq10 qq11 qq12 qq13 qq14 qq15 qq16 qq17 qq28 qq29 qq30 qq31 FY fcY
            Y_ART Y_MI Y_ST Y_FR Y_FH Y_PS Y_SL Y_CP Y_R Y_FS Y_LH Y_SSP Y_AG Y_POS Y_POC Y_SAO Y_LV Y_FRS Y_SP0 Y_CR.
          clear AGF. rename Y_AG into AGF.
          repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with Y_FR => fail | Y_FH => fail | Y_PS => fail | Y_SL => fail | Y_CP => fail | Y_R => fail | Y_FS => fail | _ => clear H end end.
          repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
          repeat match goal with H : u64arr asegs _ _ _ |- _ => clear H end.
          repeat match goal with H : bytes_at asegs _ _ _ |- _ => clear H end.
          repeat match goal with H : ART RT _ _ |- _ => lazymatch H with Y_ART => fail | _ => clear H end end.
          repeat match goal with H : LIBH _ |- _ => lazymatch H with Y_LH => fail | _ => clear H end end.
          repeat match goal with H : io_ssp _ |- _ => lazymatch H with Y_SSP => fail | _ => clear H end end.
          repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with Y_ST => fail | _ => clear H end end.
          repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with Y_MI => fail | _ => clear H end end.
          repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
          repeat match goal with H : munch _ _ _ |- _ => clear H end.
          repeat match goal with H : agree_on _ _ _ |- _ => lazymatch H with AGF => fail | _ => clear H end end.
          repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with Y_FRS => fail | FR0 => fail | _ => clear H end end.
          repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with Y_LV => fail | _ => clear H end end.
          repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with Y_SP0 => fail | _ => clear H end end.
          repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
          repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with Y_CR => fail | _ => clear H end end.
          repeat match goal with H : new_pix1 _ _ _ _ _ _ _ _ _ |- _ => clear H end.
          repeat match goal with H : new_pix1_live _ _ _ _ _ _ |- _ => clear H end.
          clear_acc.
          pose proof Y_FR as FRrecY. split_before FRrecY (C8 s0) FRrecY2. clear FRrecY.
          assert (SPLY : rt_sp0 RT SY - 8388608 <= usp - 128) by (rewrite Y_SP0; ul).
          hide Y_POS. hide Y_POC. hide Y_SAO.
          unfold entry_st.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
          Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9111c].
          lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
          rewrite (swrap32_small (i + 1)) by lia.
          lstep.   (* [comment removed for export] *)
          destruct k as [|k'].
          { (* [comment removed for export] *)
            assert (I9 : i = 9) by lia.
            brF.
            lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
            cps_stop.
            art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
            lazymatch goal with MUx : munch _ ?mm _ |- _ =>
              agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                                 repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
            unfold hid in Y_POS, Y_POC, Y_SAO.
            to_entry.
            eapply FIN; try eassumption.
            all: lazymatch goal with |- ?g => idtac "LEFT:" g end.
            - lia.
            - pose proof fh_fuzz_need_ok as FNO. subst i. unfold FH_FUZZ_NEED, HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST, FUZZ_COST in *. lia. }
          idtac "REND_FIN_DONE".
          { (* [comment removed for export] *)
            brT.
            lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
            cps_stop.
            art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
            lazymatch goal with MUx : munch _ ?mm _ |- _ =>
              agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                                 repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
            unfold hid in Y_POS, Y_POC, Y_SAO.
            to_entry.
            eapply (IH (i + 1)); try eassumption.
            all: lazymatch goal with |- ?g => idtac "LEFT:" g end.
            - lia.
            - lia.
            - lia.
            - exact (conj HML HMJ). } }
        idtac "REND_PROVED".
        lazymatch goal with H : new_pix1 RT S S1 _ ?rr _ _ ?vv ?cc |- _ => rename rr into rH; rename vv into vH; rename cc into cH; rename H into NP end.
        lazymatch goal with H : new_pix1_live RT S S1 _ _ _ |- _ => rename H into NPL end.
        assert (FRS1 : rt_frames RT S1 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx; exact I) end.
        rewrite ELV in KL.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBLA e (SUBSB e He))) POS1) as POS2.
        pose proof (pix_obj_keep _ _ _ copy vc cc KL POC1) as POC2.
        pose proof (sela_obj_keep2 la la _ _ sela arr sels SAO1 (sela_live_in la _ sela arr sels SAO1) (keeps_live_sub _ _ _ _ KL SUBLA)) as SAO2.
        clear POS1 POC1 SAO1 KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUBLA; apply SUBSB; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; exact I]).
        assert (SPL1 : rt_sp0 RT S1 - 8388608 <= usp - 128) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (CR1 : rt_credit RT Σ - ((RASTER_COST + 64) + TEMPLATE_COST + 1 + i * (HMT_COST + 2) + HMT_COST) <= rt_credit RT S1)
          by (lazymatch goal with H : rt_credit RT S - HMT_COST <= rt_credit RT S1 |- _ => clear - H ECR; lia end).
        idtac "POST_HMT".
        destruct (Z.eq_dec rH 0) as [R0|RN].
        { (* [comment removed for export] *)
          destruct NPL as (NPL0 & _ & NPLP & NPLL). pose proof (NPL0 R0) as LV1. rewrite ELV in LV1. clear NP NPL0 NPLP NPLL.
          subst rH.
          hide POS2. hide POC2. hide SAO2.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
          Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDeserialize; e_selaAddHitMiss; e_pixCopy; e_pixHMTDwa_1; e_pixDestroy; e_selaDestroy].
          lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
          pose proof FSE as SHBr. split_at SHBr 16%nat SHBrb. split_at SHBrb 1%nat SHBrc. clear SHBr SHBrc.
          pose proof (rw_cells_head _ _ _ _ RE) as RE1.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          unfold hid in POS2, POC2, SAO2.
          lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
            lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
              assert (KL : keeps_live (rt_live RT Sx) mm mc)
                by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                    exact (live_outside_frame2 RT AF Sx mm fr usp (usp - 128) bb kk xx A ltac:(rewrite FRS1; left; reflexivity) SPL1 Hb Hx)) end end.
          rewrite LV1 in KL.
          pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBLA e (SUBSB e He))) POS2) as POS3.
          pose proof (pix_obj_keep _ _ _ copy vc cc KL POC2) as POC3.
          pose proof (sela_obj_keep2 la la _ _ sela arr sels SAO2 (sela_live_in la _ sela arr sels SAO2) (keeps_live_sub _ _ _ _ KL SUBLA)) as SAO3.
          clear POS2 POC2 SAO2 KL.
          pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
          eapply cps_seq.
          { eapply DN with (lo := lo) (pp := fr + 128); rt_side idtac.
            all: lazymatch goal with
                 | |- optrL _ _ _ _ _ _ =>
                     unfold optrL, parked in *; split;
                     [ right; exists fr, 2%nat; rewrite FRS1; change (fs_size 2) with 256;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 128)) with (fr / 8 + 2147450896) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHBrb as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact RE1
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, FRAMES_MAX, LIVE_MAX in *;
                     split; [rewrite FRS1, FR0; cbn [length]; lia| split; [rewrite LV1; lia| split; [| rewrite LV1; exact LVPE]]];
                     pose proof fh_fuzz_need_ok as FNO; unfold FH_FUZZ_NEED, HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST, FUZZ_COST in *; lia
                 | |- ?g => idtac "LEFT:" g
                 end. }
          idtac "DNULL_APPLIED".
          clear SHBrb RE1.
          after_call RT AF.
          lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into S2 end.
          lazymatch goal with H : rt_live RT S2 = rt_live RT S1 |- _ => rewrite LV1 in H; rename H into LV2 end.
          assert (FRS2 : rt_frames RT S2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
          lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
            assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx; exact I) end.
          rewrite LV2 in KL.
          pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBLA e (SUBSB e He))) POS3) as POS4.
          pose proof (pix_obj_keep _ _ _ copy vc cc KL POC3) as POC4.
          pose proof (sela_obj_keep2 la la _ _ sela arr sels SAO3 (sela_live_in la _ sela arr sels SAO3) (keeps_live_sub _ _ _ _ KL SUBLA)) as SAO4.
          clear POS3 POC3 SAO3 KL.
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV2; apply SUBLA; apply SUBSB; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; exact I]).
          rewrite ESP.
          eapply REND; try eassumption.
          - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.
          - lazymatch goal with H : rt_credit RT S1 - 1 <= rt_credit RT S2 |- _ => clear - H CR1; lia end. }
        idtac "R0_ARM_DONE".
        { (* [comment removed for export] *)
          destruct NP as [NP0|(POR & _)]; [exfalso; exact (RN NP0)|].
          destruct NPL as (_ & NPL1 & NPLP & NPLL). pose proof (NPL1 RN) as LV1. rewrite ELV in LV1, NPLL. clear NPL1.
          assert (SUB1 : forall e, In e lc -> In e (rt_live RT S1)) by (intros e He; rewrite <- LV1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
          hide POS2. hide POC2. hide SAO2. hide POR. hide LV1.
          refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
          Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDeserialize; e_selaAddHitMiss; e_pixCopy; e_pixHMTDwa_1; e_pixDestroy; e_selaDestroy].
          lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
          pose proof FSE as SHBr. split_at SHBr 16%nat SHBrb. split_at SHBrb 1%nat SHBrc. clear SHBr SHBrc.
          split_at RE 1%nat RE2.
          at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
          unfold hid in POS2, POC2, SAO2, POR, LV1.
          lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
            lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
              assert (KL : keeps_live (rt_live RT Sx) mm mc)
                by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                    exact (live_outside_frame2 RT AF Sx mm fr usp (usp - 128) bb kk xx A ltac:(rewrite FRS1; left; reflexivity) SPL1 Hb Hx)) end end.
          pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUB1 e (SUBLA e (SUBSB e He)))) POS2) as POS3.
          pose proof (pix_obj_keep _ _ _ copy vc cc (keeps_live_sub _ _ _ _ KL SUB1) POC2) as POC3.
          pose proof (sela_obj_keep2 la la _ _ sela arr sels SAO2 (sela_live_in la _ sela arr sels SAO2) (keeps_live_sub _ _ _ _ KL (fun e He => SUB1 e (SUBLA e He)))) as SAO3.
          pose proof (pix_obj_keep _ _ _ rH vH cH KL POR) as POR3.
          idtac "RN_PRE".
          pose proof DESTROY as DY3. unfold pixDestroy_cps in DY3.
          eapply cps_seq.
          { eapply DY3 with (lo := lo) (pp := fr + 128) (pix := rH) (v := vH) (cv := cH) (ras := [D_libiface.RA_TOP]); rt_side idtac.
            all: lazymatch goal with
                 | |- optrL _ _ _ _ _ _ =>
                     unfold optrL, parked in *; split;
                     [ right; exists fr, 2%nat; rewrite FRS1; change (fs_size 2) with 256;
                       split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                       split; [lia|]; split; [lia|];
                       replace (shad (fr + 128)) with (fr / 8 + 2147450896) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                       destruct SHBrb as [[_ B] _]; exact B
                     | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
                 | |- rw_cells _ _ _ [C8 _] => exact RE
                 | |- pix_obj _ _ _ _ _ => exact POR3
                 | |- uctx _ _ _ _ =>
                     unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                     apply chain_ok_push with (fp1 := bv_unsigned s0);
                       [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold D_libiface.RA_TOP; lia | apply bv_unsigned_in_range
                       | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                       | cbn [chain_ok]; unfold link_invalid; lia ]
                 | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
                 | |- lenv _ _ _ _ _ _ => lenv_tac
                 | |- lres _ _ _ _ _ =>
                     unfold lres, FRAMES_MAX, LIVE_MAX in *;
                     split; [rewrite FRS1, FR0; cbn [length]; lia| split; [lia| split; [| exact NPLP]]];
                     pose proof fh_fuzz_need_ok as FNO; unfold FH_FUZZ_NEED, HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST, FUZZ_COST in *; lia
                 | |- ?g => idtac "LEFT:" g
                 end. }
          idtac "DESTROY_R_APPLIED".
          after_call RT AF.
          lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into S2 end.
          lazymatch goal with H : rt_live RT S2 = live_destroy rH vH cH _ |- _ => rewrite LV1 in H; rename H into LV2 end.
          assert (FRS2 : rt_frames RT S2 = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
          idtac "AFTER_DESTROY_R".
          lazymatch goal with H : rw_cells asegs ?mm (fr + 128) [C8 ?z] |- _ =>
            assert (REJ : rw_cells asegs mm (fr + 128) ([C8 z] ++ [CB 112 j112]))
              by (apply rw_cells_app; split; [exact H| replace (fr + 128 + Z.of_nat (cells_size [C8 z])) with (fr + 136) by (cbn; lia); exact RE2]) end.
          cbn [app] in REJ.
          lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A2 : ART RT S2 ?mb |- _ =>
            assert (KL2 : keeps_live lv ma mb)
              by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                  exact (live_outside_local RT AF S2 mb fr 2%nat 128 bb kk xx A2 ltac:(rewrite FRS2; left; reflexivity) ltac:(lia) ltac:(change (fs_size 2) with 256; lia) Hb Hx)) end.
          rewrite LV2 in KL2.
          pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL2 (fun e He => SUBLA e (SUBSB e He))) POS3) as POS4.
          pose proof (pix_obj_keep _ _ _ copy vc cc KL2 POC3) as POC4.
          pose proof (sela_obj_keep2 la la _ _ sela arr sels SAO3 (sela_live_in la _ sela arr sels SAO3) (keeps_live_sub _ _ _ _ KL2 SUBLA)) as SAO4.
          idtac "RN_POST".
          clear POS3 POC3 SAO3 POR3 KL KL2.
          fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LV2; apply SUBLA; apply SUBSB; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                          cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
          rewrite ESP.
          eapply REND; try eassumption.
          - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.
          - lazymatch goal with H : rt_credit RT S1 - 1 <= rt_credit RT S2 |- _ => clear - H CR1; lia end. } }
      idtac "ROUND_PROVED".
      (* [comment removed for export] *)
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDeserialize; e_selaAddHitMiss; e_pixCopy; e_pixHMTDwa_1; e_pixDestroy; e_selaDestroy].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      assert (SPLb : rt_sp0 RT Sb - 8388608 <= usp - 128) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
      assert (FRSb : rt_frames RT Sb = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      unfold hid in POBJ.
      lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
        lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
          assert (KL : keeps_live (rt_live RT Sx) mm mc)
            by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                exact (live_outside_frame2 RT AF Sx mm fr usp (usp - 128) bb kk xx A ltac:(rewrite FRSb; left; reflexivity) SPLb Hb Hx)) end end.
      pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POBJ) as POS1.
      pose proof SAHM as SA. unfold selaAddHitMiss_cps in SA.
      eapply cps_seq.
      { eapply SA with (lo := lo); rt_side idtac.
        all: lazymatch goal with
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ =>
                 unfold lres, FRAMES_MAX, LIVE_MAX in *;
                 split; [rewrite FRSb, FR0; cbn [length]; lia| split; [lia| split; [| exact LVPb]]];
                 pose proof fh_fuzz_need_ok as FNO; unfold FH_FUZZ_NEED, HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST, FUZZ_COST in *; lia
             | |- ?g => idtac "LEFT:" g
             end. }
      idtac "SAHM_APPLIED".
      after_call RT AF.
      lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sa end.
      lazymatch goal with H : sela_obj (rt_live RT Sa) _ ?sl ?ar ?ss |- _ => rename sl into sela; rename ar into arr; rename ss into sels; rename H into SAO end.
      lazymatch goal with H : hm_sels_ok sels |- _ => rename H into HMOK end.
      lazymatch goal with H : rt_live RT Sa = _ ++ rt_live RT Sb |- _ => rename H into LVa end.
      assert (FRSa : rt_frames RT Sa = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
      assert (SPLa : rt_sp0 RT Sa - 8388608 <= usp - 128) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
      assert (SUBba : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sa)) by (intros e He; rewrite LVa; apply in_or_app; right; exact He).
      lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
        assert (KLa : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx; exact I) end.
      pose proof (pix_obj_keep _ _ _ pixs vs cvs KLa POS1) as POS2.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                      cbn [outside]; exact I]).
      idtac "AFTER_SAHM".
      pose proof SAO as (SAC & (SAIN & SA0 & SA16 & _) & _). pose proof HMOK as (HML & _).
      unfold sela_cells in SAC. rewrite HML in SAC. change (Z.of_nat 10) with 10 in SAC.
      hide LVa.
      chunk_facts RT AF GP sela 16. fframe_chunk RT AF fr 2%nat 256 sela 16.
      hide SAO. hide POS2.
      clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDeserialize; e_selaAddHitMiss; e_pixCopy; e_pixHMTDwa_1; e_pixDestroy; e_selaDestroy].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      (* [comment removed for export] *)
      unfold hid in LVa, SAO.
      assert (LENa : Z.of_nat (length (rt_live RT Sa)) = 74 + Z.of_nat (length (rt_live RT Sb)))
        by (rewrite LVa, length_app, (sela_live_len_hm _ _ _ _ _ SAO HMOK); lia).
      assert (LVPa : forall p n, In (p, n) (rt_live RT Sa) -> 0 < n).
      { intros p n Hp. rewrite LVa in Hp. apply in_app_or in Hp. destruct Hp as [Hp|Hp]; [exact (sela_obj_pos _ _ _ _ _ SAO p n Hp)| exact (LVPb p n Hp)]. }
      assert (SPLa2 : rt_sp0 RT Sa - 8388608 <= usp - 256) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
      hide LVa. hide SAO.
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
      unfold hid in POS2, SAO.
      lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
        lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
          assert (KLc : keeps_live (rt_live RT Sx) mm mc)
            by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                exact (live_outside_frame2 RT AF Sx mm fr usp (usp - 256) bb kk xx A ltac:(rewrite FRSa; left; reflexivity) SPLa2 Hb Hx)) end end.
      pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KLc SUBba) POS2) as POS3.
      pose proof (sela_obj_keep2 _ _ _ _ sela arr sels SAO (sela_live_in _ _ sela arr sels SAO) KLc) as SAO3.
      idtac "PCOPY_PRE".
      pose proof PCOPY as PC. unfold pixCopy_cps in PC.
      eapply cps_seq.
      { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
        all: lazymatch goal with
             | |- pix_obj _ _ _ _ _ => exact (pix_obj_mono _ _ _ pixs vs cvs SUBba POS3)
             | |- p_data _ <> 0 => exact VDATA
             | |- lenv _ _ _ _ _ _ => lenv_tac
             | |- lres _ _ _ _ _ =>
                 unfold lres, FRAMES_MAX, LIVE_MAX in *;
                 split; [rewrite FRSa, FR0; cbn [length]; lia| split; [lia| split; [| exact LVPa]]];
                 pose proof fh_fuzz_need_ok as FNO; unfold FH_FUZZ_NEED, HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST, FUZZ_COST in *;
                 repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia
             | |- ?g => idtac "LEFT:" g
             end. }
      idtac "PCOPY_APPLIED".
      after_call RT AF.
      lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
      lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?cp ?vv ?cc |- _ => rename H into POC; rename cp into copy; rename vv into vc; rename cc into ccp end.
      lazymatch goal with H : p_data vc <> 0 |- _ => rename H into VCDATA end.
      lazymatch goal with H : live_destroy copy vc ccp (rt_live RT Sc) = rt_live RT Sa |- _ => rename H into LVDc end.
      lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
      lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LENc end.
      assert (FRSc : rt_frames RT Sc = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
      assert (SUBac : forall e, In e (rt_live RT Sa) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LVDc in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
      lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
        assert (KLd : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx; exact I) end.
      pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KLd SUBba) POS3) as POS4.
      pose proof (sela_obj_keep2 _ _ _ _ sela arr sels SAO3 (sela_live_in _ _ sela arr sels SAO3) KLd) as SAO4.
      clear POS3 SAO3 KLd KLc.
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBba; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                      cbn [outside]; exact I]).
      idtac "AFTER_PCOPY".
      hide POS4. hide POC. hide SAO4. hide LVa. hide LVDc. hide SAO.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
      Time walk_to AF MST [(usp - 128, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x910ec].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                           repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
      unfold hid in POS4, POC, SAO4, LVa, LVDc.
      to_entry.
      (* [comment removed for export] *)
      assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 128) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
      lazymatch goal with MUx : munch ?W ?mm ?mc, A : ART RT Sc ?mm |- _ =>
        assert (KLe : keeps_live (rt_live RT Sc) mm mc)
          by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
              exact (live_outside_frame2 RT AF Sc mm fr usp (usp - 128) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end.
      pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KLe (fun e He => SUBac e (SUBba e He))) POS4) as POS5.
      pose proof (pix_obj_keep _ _ _ copy vc ccp KLe POC) as POC5.
      pose proof (sela_obj_keep2 _ _ _ _ sela arr sels SAO4 (sela_live_in _ _ sela arr sels SAO4) (keeps_live_sub _ _ _ _ KLe SUBac)) as SAO5.
      (* [comment removed for export] *)
      lazymatch goal with H : rw_cells asegs _ fr _ |- _ => rename H into FRMe end.
      split_at FRMe 4%nat PSe. split_at PSe 2%nat SLe. split_at SLe 2%nat CPe. split_at CPe 2%nat REe.
      apply rw_cells_CB8_C8 in REe.
      sx32_fix. rewrite ESP.
      eapply (ROUND 10%nat 0); try eassumption.
      all: lazymatch goal with
           | |- Z.of_nat _ = _ => lia
           | |- (_ <= _)%nat => lia
           | |- 0 <= 0 => lia
           | |- rt_live _ _ = rt_live _ _ => reflexivity
           | |- Z.of_nat (length _) + 12 <= LIVE_MAX => unfold LIVE_MAX in *; clear - LENc LENa LVXb LVB; lia
           | |- Z.of_nat (length _) <= LIVE_MAX => unfold LIVE_MAX in *; clear - LENc LENa LVXb LVB; lia
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- _ <= rt_credit _ _ => unfold RASTER_COST, TEMPLATE_COST, HMT_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia
           | |- ?g => idtac "LEFT:" g
           end.
Qed.

End FZ.

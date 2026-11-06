(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Km_setelem Km_iface Km_kit D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac rt_transport_extra m m' AG ::=
  lept_rt_transport_extra m m' AG;   (* [comment removed for export] *)
  repeat match goal with
  | H : u64arr asegs m ?A ?ws |- _ =>
      first [ apply (u64arr_agree_nw asegs m m' A ws) in H; [ | solve [agree_range AG A ltac:(fun A => acl_dispatch A)] ]
            | idtac "note: dropping u64arr:" H; clear H ]
  end.

Section KDESTROY.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
(* [comment removed for export] *)
Hypothesis TRK1 : In [0x9130c] CLIENT_TRACES.
Hypothesis TRK2 : In [0x9134c] CLIENT_TRACES.
Hypothesis TRK3 : In [0x91354] CLIENT_TRACES.

(* [comment removed for export] *)
Theorem kernelDestroy_ok : kernelDestroy_cps RT.
Proof using AF GP TRK1 TRK2 TRK3.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp kel sy sx cy cx data rows
    FDO MST -> -> OPP PPC HKEL ENV RES.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_kernelDestroy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof OPP as (OWNF & PP0 & PP8 & PPSH & PPSEG). unfold SEGTOP_A in PPSEG.
  assert (OWN : accok (@nil (Z * Z)) (rt_frames RT Σ) m pp 8) by (right; exact OWNF).
  assert (PPLO : pp + 8 <= lo /\ pp + 16 <= 2^47).
  { destruct OWNF as (ff & kk & HFin & HF1 & HF2 & _ & _ & HFT & _).
    pose proof (af_frames_range RT AF Σ m ff kk ART0 HFin) as (_ & R & _). unfold STACK_WIN in R. clear - HF1 HF2 HFT R LOW. lia. }
  destruct PPLO as [PPLO PPT].
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (LOUT : forall b k, In (b, k) (rt_live RT Σ) -> forall x, b <= x < b + k -> x < lo).
  { intros b k Hb x Hx. pose proof (af_live_range RT AF Σ m b k ART0 Hb) as LR. unfold STACK_WIN in LR. lia. }
  destruct HKEL as [K0|KOBJ].
  - subst kel. refresh RT AF.
    walk_to AF MST [(usp - 96, usp)] (@nil Z).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    apply cps_finish. intros c0 Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end. eexists.
    split.
    { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; assumption]| split; assumption]|].
      split; [intros a Ha Ho; apply AGF; exact Ha| exact PPC]. }
    change (0 =? 0) with true. cbv iota. repeat split; reflexivity.
  - destruct KOBJ as (KC & KCH & DA & DCH & LEN & ROWS & ND & SYB & SXB).
    pose proof KCH as (KIN & K0 & K16 & KN). pose proof DCH as (DIN & D0 & D16 & DN).
    chunk_facts RT AF GP kel 24. chunk_facts RT AF GP data (8 * sy).
    unfold kel_cells in KC.
    assert (WSN : forall j, 0 <= j < sy -> nth_error (map (Z_to_bv 64) rows) (Z.to_nat j) = Some (Z_to_bv 64 (nth (Z.to_nat j) rows 0))).
    { intros j Hj. rewrite nth_error_map. rewrite (nth_error_nth' rows 0) by lia. reflexivity. }
    assert (LENW : Z.of_nat (length (map (Z_to_bv 64) rows)) = sy) by (rewrite length_map; exact LEN).
    set (ws := map (Z_to_bv 64) rows) in DA, WSN, LENW. clearbody ws.
    clear AGF PFS. clear PF.
    set (LVF := km_unlive kel data rows (rt_live RT Σ)).
    set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pp, pp + 8)] a).
    pose proof (agree_refl PF m) as AGF.
    assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ))
      by (intros ee Hee; unfold LVF, km_unlive in Hee; apply live_remove_sub, live_remove_sub, rows_remove_sub in Hee; exact Hee).
    assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
    { intros xa [HXa _]. apply (aclient_mono _ _ usp (rt_live RT Σ) (rt_frames RT Σ) usp) in HXa; [| exact LVFS| auto| lia].
      destruct (aclient_split RT AF Σ m usp xa ART0 HXa) as [HXS|HXS]; [left; exact HXS| right; unfold STACK_WIN in HXS; lia]. }
    refresh RT AF.
    assert (EXIT : forall (Sx : rts RT) (mx : mem) (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x x5 x6 x7 x8 x9 t3x t4x t5x t6x : word)
                          (Fx : bvmap 5 word) (fcx : bv 32) (jk : list byte),
      ART RT Sx mx -> mem_inv asegs mx -> stk asegs mx lo (usp + -96) ->
      rw_cells asegs mx (usp + -96) [CB 8 jk; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mx kel [C4 (Z_to_bv 64 sy); C4 (Z_to_bv 64 sx); C4 (Z_to_bv 64 cy); C4 (Z_to_bv 64 cx); C8 (Z_to_bv 64 data)] ->
      rw_cells asegs mx pp [C8 (Z_to_bv 64 kel)] -> LIBH mx -> io_ssp mx -> agree_on PF m mx ->
      accok [] (rt_frames RT Σ) mx pp 8 ->
      rt_live RT Sx = rows_remove rows (rt_live RT Σ) -> rt_frames RT Sx = rt_frames RT Σ -> rt_sp0 RT Sx = rt_sp0 RT Σ ->
      rt_credit RT Sx = rt_credit RT Σ ->
      cps asegs (ASTA RT Sx PMc (eq (entry_st rax (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) t0x t1x t2x (Z_to_bv 64 pp) (Z_to_bv 64 kel)
                     a0x a1x a2x a3x a4x a5x a6x a7x (Z_to_bv 64 (kel + 16)) (Z_to_bv 64 (pp / 8 + SHB)) (Z_to_bv 64 SHB) x5 x6 x7 x8 x9 s10 s11
                     t3x t4x t5x t6x Fx fcx 0x91334 mx))) QF).
    { intros Sx mx rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x x5 x6 x7 x8 x9 t3x t4x t5x t6x Fx fcx jk
        ARTx MIx STx FRx KCx PPCx LHx SSPx AGFx OWNx LVx FRSx SPx CRx.
      clear ST STa STb MI LH SSP KC PPC ACC ACC0 ACC1 G1 G2 G3 G4 OWN AGF.
      unfold entry_st.
      pose proof ND as ND'. apply List.NoDup_cons_iff in ND' as (NK & ND'). apply List.NoDup_cons_iff in ND' as (NDD & NDR).
      assert (NEKD : kel <> data) by (intros E; apply NK; left; symmetry; exact E).
      assert (KINr : In (kel, 24) (rows_remove rows (rt_live RT Σ))) by (apply rows_remove_in; [exact KIN| cbn [fst]; intros Hr; apply NK; right; exact Hr]).
      assert (DINr : In (data, 8 * sy) (rows_remove rows (rt_live RT Σ))) by (apply rows_remove_in; [exact DIN| cbn [fst]; exact NDD]).
      assert (KINx : In (kel, 24) (rt_live RT Sx)) by (rewrite LVx; exact KINr).
      assert (DINx : In (data, 8 * sy) (rt_live RT Sx)) by (rewrite LVx; exact DINr).
      clear KIN DIN IN IN0.
      pose proof (acc_live RT AF Sx mx kel 24 ARTx KINx) as ACCK. pose proof (acc_live RT AF Sx mx data (8 * sy) ARTx DINx) as ACCD.
      refresh RT AF.
      park_disj.
      walk_to AF MST [(usp + -96, usp)] [e_free].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
      eapply cps_seq.
      { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := data) (n := 8 * sy); rt_side idtac.
        all: lazymatch goal with
             | |- In _ _ => exact DINx
             | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact TRK2| left; ul]
             | |- ?g => idtac "LEFT:" g
             end. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                               [ solve [let e := fresh "e" in let He := fresh "He" in intros e He;
                                        repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
                                        unfold LVF, km_unlive in He; apply live_remove_sub in He; exact He]
                               | solve [frames_sub_tac] | lia]).
      refresh RT AF. park_disj.
      walk_to AF MST [(usp + -96, usp)] [e_free].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
      eapply cps_seq.
      { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := kel) (n := 24); rt_side idtac.
        all: lazymatch goal with
             | |- In _ _ => solve [in_live_tac]
             | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact TRK3| left; ul]
             | |- ?g => idtac "LEFT:" g
             end. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                               [ solve [let e := fresh "e" in let He := fresh "He" in intros e He;
                                        repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
                                        unfold LVF, km_unlive in He; exact He]
                               | solve [frames_sub_tac] | lia]).
      refresh RT AF. park_disj.
      walk_to AF MST [(usp + -96, usp); (pp, pp + 8)] (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; aclient_tac| exact I]]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        agf_munch AGFx MUx ltac:(fun Hx => let HO := fresh "HO" in cbn [outside]; pose proof (PFS _ Hx); pose proof (proj2 Hx) as HO;
                                          cbn [outside] in HO; repeat split; try exact I; first [lia | tauto]) end.
      apply cps_finish. intros c0 Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end. eexists.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [split; [assumption| split; assumption]| split; assumption]|].
        split; [| exact PPCx].
        intros xa HXa HXo. apply AGFx. split; [| exact HXo].
        repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in HXa end. exact HXa. }
      replace (kel =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity|].
      split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity|].
      split; [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end. reflexivity.
    }
    assert (LOOP : forall k i, Z.to_nat (sy - i) = k -> 0 <= i < sy ->
      forall (Si : rts RT) (mi : mem) (rai t0i t1i t2i a0i a1i a2i a3i a4i a5i a6i a7i t3i t4i t5i t6i : word)
             (Fi : bvmap 5 word) (fci : bv 32) (jk : list byte),
      ART RT Si mi -> mem_inv asegs mi -> stk asegs mi lo (usp + -96) ->
      rw_cells asegs mi (usp + -96) [CB 8 jk; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mi kel [C4 (Z_to_bv 64 sy); C4 (Z_to_bv 64 sx); C4 (Z_to_bv 64 cy); C4 (Z_to_bv 64 cx); C8 (Z_to_bv 64 data)] ->
      u64arr asegs mi data ws ->
      rw_cells asegs mi pp [C8 (Z_to_bv 64 kel)] -> LIBH mi -> io_ssp mi -> agree_on PF m mi ->
      accok [] (rt_frames RT Σ) mi pp 8 ->
      rt_live RT Si = rows_remove (firstn (Z.to_nat i) rows) (rt_live RT Σ) -> rt_frames RT Si = rt_frames RT Σ ->
      rt_sp0 RT Si = rt_sp0 RT Σ -> rt_credit RT Si = rt_credit RT Σ ->
      cps asegs (ASTA RT Si PMc (eq (entry_st rai (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 TP_A) t0i t1i t2i (Z_to_bv 64 pp) (Z_to_bv 64 kel)
                     a0i a1i a2i a3i a4i a5i a6i a7i (Z_to_bv 64 (kel + 16)) (Z_to_bv 64 (pp / 8 + SHB)) (Z_to_bv 64 SHB)
                     (Z_to_bv 64 (kel / 8 + SHB)) (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i) (Z_to_bv 64 ((kel + 16) / 8 + SHB))
                     (Z_to_bv 64 (Z.land kel 7 + 3)) s10 s11 t3i t4i t5i t6i Fi fci 0x912e4 mi))) QF).
    { intros k. induction k as [k IH] using lt_wf_ind.
      intros i Hk Hi Si mi rai t0i t1i t2i a0i a1i a2i a3i a4i a5i a6i a7i t3i t4i t5i t6i Fi fci jk
        ARTi MIi STi FRi KCi DAi PPCi LHi SSPi AGFi OWNi LVi FRSi SPi CRi.
      clear ST STa STb MI LH SSP KC PPC DA ACC ACC0 ACC1 G1 G2 G3 G4 OWN AGF.
      unfold entry_st.
      pose proof ND as ND'. apply List.NoDup_cons_iff in ND' as (NK & ND'). apply List.NoDup_cons_iff in ND' as (NDD & NDR).
      assert (NEKD : kel <> data) by (intros E; apply NK; left; symmetry; exact E).
      assert (HiN : (Z.to_nat i < length rows)%nat) by lia.
      set (r := nth (Z.to_nat i) rows 0) in *.
      assert (RIN : In r rows) by (apply nth_In; exact HiN).
      assert (RCH : chunk (rt_live RT Σ) r (4 * sx)) by (rewrite Forall_forall in ROWS; exact (proj1 (ROWS r RIN))).
      destruct RCH as (RIN0 & R0 & R16 & RN).
      assert (NEKR : kel <> r) by (intros E; apply NK; right; rewrite E; exact RIN).
      assert (NEDR : data <> r) by (intros E; apply NDD; rewrite E; exact RIN).
      assert (RNF : ~ In r (firstn (Z.to_nat i) rows)) by (exact (nodup_nth_notin_firstn rows (Z.to_nat i) NDR HiN)).
      assert (KINr : In (kel, 24) (rows_remove (firstn (Z.to_nat i) rows) (rt_live RT Σ)))
        by (apply rows_remove_in; [exact KIN| cbn [fst]; intros Hr; apply NK; right;
            rewrite <- (firstn_skipn (Z.to_nat i) rows); apply in_or_app; left; exact Hr]).
      assert (DINr : In (data, 8 * sy) (rows_remove (firstn (Z.to_nat i) rows) (rt_live RT Σ)))
        by (apply rows_remove_in; [exact DIN| cbn [fst]; intros Hr; apply NDD;
            rewrite <- (firstn_skipn (Z.to_nat i) rows); apply in_or_app; left; exact Hr]).
      assert (RINr : In (r, 4 * sx) (rows_remove (firstn (Z.to_nat i) rows) (rt_live RT Σ)))
        by (apply rows_remove_in; [exact RIN0| cbn [fst]; exact RNF]).
      assert (KINi : In (kel, 24) (rt_live RT Si)) by (rewrite LVi; exact KINr).
      assert (DINi : In (data, 8 * sy) (rt_live RT Si)) by (rewrite LVi; exact DINr).
      assert (RINi : In (r, 4 * sx) (rt_live RT Si)) by (rewrite LVi; exact RINr).
      clear KIN DIN IN IN0.
      pose proof (acc_live RT AF Si mi kel 24 ARTi KINi) as ACCK. pose proof (acc_live RT AF Si mi data (8 * sy) ARTi DINi) as ACCD.
      refresh RT AF.
      park_disj.
      walk_to AF MST [(usp + -96, usp)] [e_free].
      pose proof (u64arr_read asegs mi data ws i (Z_to_bv 64 r) (Z_to_bv 64 (data + 8 * i)) DAi (WSN i Hi) (proj1 Hi)
                    ltac:(unfold wa; f_equal; lia)) as RD.
      lstep. clear RD.
      awalk [e_free].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
      eapply cps_seq.
      { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := r) (n := 4 * sx); rt_side idtac.
        all: lazymatch goal with
             | |- In _ _ => exact RINi
             | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact TRK1| left; ul]
             | |- ?g => idtac "LEFT:" g
             end. }
      after_call RT AF.
      assert (LVS : rows_remove (firstn (S (Z.to_nat i)) rows) (rt_live RT Σ) = live_remove r (rows_remove (firstn (Z.to_nat i) rows) (rt_live RT Σ)))
        by (exact (rows_remove_firstn_S rows (Z.to_nat i) (rt_live RT Σ) HiN)).
      fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx));
                               [ solve [let e := fresh "e" in let He := fresh "He" in intros e He;
                                        repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
                                        unfold LVF, km_unlive in He; apply live_remove_sub, live_remove_sub in He;
                                        rewrite <- LVS; exact (rows_remove_firstn_sub _ _ _ _ He)]
                               | solve [frames_sub_tac] | lia]).
      refresh RT AF. park_disj.
      walk_to AF MST [(usp + -96, usp)] [e_free; 0x912e4; 0x91334].
      rewrite (sx32_small sy) by lia.
      destruct (Z_lt_ge_dec (i + 1) sy) as [LT|GE].
      + brT.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
        lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          agf_munch AGFi MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
        to_entry.
        replace (8 * i + 8) with (8 * (i + 1)) by lia.
        eapply (IH (Z.to_nat (sy - (i + 1))) ltac:(lia) (i + 1) eq_refl ltac:(lia)).
        all: lazymatch goal with
             | |- rt_live RT _ = _ => repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end;
                                       replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; symmetry; exact LVS
             | |- rt_frames RT _ = _ => repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 RT _ = _ => repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_credit RT _ = _ => repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end; reflexivity
             | |- rw_cells _ _ _ (CB _ _ :: _) => eassumption
             | |- _ => assumption
             end.
      + brF.
        awalk [0x91334].
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
        lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          agf_munch AGFi MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
        to_entry.
        assert (FALL : rows_remove (firstn (S (Z.to_nat i)) rows) (rt_live RT Σ) = rows_remove rows (rt_live RT Σ))
          by (rewrite firstn_all2 by lia; reflexivity).
        eapply EXIT.
        all: lazymatch goal with
             | |- rt_live RT _ = _ => repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end;
                                       rewrite <- FALL; symmetry; exact LVS
             | |- rt_frames RT _ = _ => repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 RT _ = _ => repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_credit RT _ = _ => repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end; reflexivity
             | |- rw_cells _ _ _ (CB _ _ :: _) => eassumption
             | |- _ => assumption
             end.
    }
    park_disj.
    walk_to AF MST [(usp + -96, usp)] [0x912e4; e_free].
    rewrite (sx32_small sy) by (clear - SYB; lia).
    awalk [0x912e4; e_free].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    to_entry.
    eapply (LOOP _ 0 eq_refl ltac:(lia)).
    all: lazymatch goal with
         | |- rt_live RT _ = _ => reflexivity
         | |- rt_frames RT _ = _ => reflexivity
         | |- rt_sp0 RT _ = _ => reflexivity
         | |- rt_credit RT _ = _ => reflexivity
         | |- rw_cells _ _ _ (CB _ _ :: _) => eassumption
         | |- _ => assumption
         end.
Qed.
End KDESTROY.

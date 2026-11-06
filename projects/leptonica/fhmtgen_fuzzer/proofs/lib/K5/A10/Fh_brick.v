(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_statics Fh_selkit Fh_brick_loop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section BRICK.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis CRE : selCreate_cps RT.

Theorem selCreateBrick_ok : selCreateBrick_cps RT.
Proof using AF GP CRE.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo sy sx cy cx ty
    FDO MST -> -> -> -> -> -> HSY HSX HCY HCX HTY ENV RES.
  pose proof ENV as ENV0. pose proof RES as RES0.
  unfold lpost, lenv, lres, keeps, keepsL in ENV, RES |- *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_selCreateBrick, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  walk_to AF MST [(usp - 64, usp)] [e_selCreate].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply CRE with (lo := lo) (sy := sy) (sx := sx); rt_side idtac.
    - unfold s0_nolink. rewrite !unsigned_lit by lia. left. lia.
    - lenv_tac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact He| intros e He; exact He| lia]| exact I]).
  lazymatch goal with H : sel_body (rt_live RT ?S) _ ?p ?vv |- _ => rename H into SBODY; rename S into Σ1; rename p into sel; rename vv into v end.
  lazymatch goal with H : rt_live RT Σ1 = _ |- _ => rename H into LV1 end.
  destruct v as [vsy vsx vcy vcx arr vname rows]. cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows] in *. subst vsy vsx vcy vcx vname.
  destruct SBODY as (SC & (SIN & S0 & S16 & _) & _ & _ & HLEN & DC & (DIN & D0 & D16 & _) & ROWS & NDUP).
  cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows] in *. unfold sel_cells in SC. cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows] in SC.
  lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
    assert (NEWAP : forall p n, In (p, n) (tl (sel_live sel (mkSelv sy sx 0 0 arr 0 rows))) -> forall a, PF a -> a < p \/ p + n <= a)
      by (intros p n Hp a Ha; apply (new_chunks_apart RT AF Σ1 mm _ (rt_live RT Σ) (rt_frames RT Σ) usp A LV1 ltac:(assumption)
                                        ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul) p n a Hp Ha)) end.
  pose proof (NEWAP _ _ (sel_in_sel_live sel _)) as NCS. pose proof (NEWAP _ _ (data_in_sel_live sel _)) as NCD.
  cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows] in NCS, NCD.
  assert (LEN1 : Z.of_nat (length (rt_live RT Σ1)) = Z.of_nat (length (rt_live RT Σ)) + 2 + sy)
    by (rewrite LV1, tl_sel_live, !length_app, length_rev, length_map; cbn [length s_rows]; lia).
  assert (SUB1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV1; apply in_or_app; right; exact He).
  assert (QSD : sel + 32 <= arr \/ arr + 8 * sy <= sel).
  { lazymatch goal with A : ART RT Σ1 ?mm |- _ =>
      pose proof (af_live_disj RT AF Σ1 mm arr (8 * sy) sel 32 (rev (map (fun r => (r, 4 * sx)) rows)) ((sel, 32) :: rt_live RT Σ) A
                    ltac:(rewrite LV1, tl_sel_live, <- app_assoc; reflexivity) ltac:(apply in_or_app; right; left; reflexivity)) as X end.
    clear - X. lia. }
  assert (ROWAP : forall r, In r rows -> (r + 4 * sx <= sel \/ sel + 32 <= r) /\ (r + 4 * sx <= arr \/ arr + 8 * sy <= r)).
  { intros r Hr. lazymatch goal with A : ART RT Σ1 ?mm |- _ =>
      pose proof (af_live_disj RT AF Σ1 mm arr (8 * sy) r (4 * sx) (rev (map (fun r => (r, 4 * sx)) rows)) ((sel, 32) :: rt_live RT Σ) A
                    ltac:(rewrite LV1, tl_sel_live, <- app_assoc; reflexivity)
                    ltac:(apply in_or_app; left; apply -> in_rev; apply (in_map (fun r => (r, 4 * sx))); exact Hr)) as X1;
      pose proof (af_live_disj RT AF Σ1 mm sel 32 r (4 * sx) (rev (map (fun r => (r, 4 * sx)) rows) ++ [(arr, 8 * sy)]) (rt_live RT Σ) A
                    ltac:(rewrite LV1, tl_sel_live, <- !app_assoc; reflexivity)
                    ltac:(apply in_or_app; left; apply in_or_app; left; apply -> in_rev; apply (in_map (fun r => (r, 4 * sx))); exact Hr)) as X2 end.
    clear - X1 X2. lia. }
  hide LV1.
  rewrite <- (map_map (Z_to_bv 64) C8) in DC. apply rw_cells_C8s_u64arr in DC.
  remember (map (Z_to_bv 64) rows) as ws eqn:EWS.
  assert (ULEN : Z.of_nat (length ws) = sy) by (rewrite EWS, length_map; exact HLEN).
  chunk_facts RT AF GP sel 32.
  chunk_facts RT AF GP arr (8 * sy).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 64, usp); (sel, sel + 32)] [0xa7d00].
  lstep. shbr8_zero.
  awalk [0xa7d1c].
  rewrite (Z.div_mul sx 4294967296) by lia.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                      intros zz Hzz; right; right; left; exists sel, 32; split; [exact SIN| lia]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCS _ Hx); repeat split; lia)
  end.
  assert (ROWLOOP : forall (k : nat) (i : Z) (mc : mem) (t0' t1' t2' a1' a7' : word),
     Z.of_nat k = sy - i -> (1 <= k)%nat -> 0 <= i ->
     ART RT Σ1 mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -64) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
     rw_cells asegs mc (usp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))));
                                     C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     rw_cells asegs mc sel [C4 (Z_to_bv 64 sy); C4 (Z_to_bv 64 sx); C4 (Z_to_bv 64 cy); C4 (Z_to_bv 64 cx); C8 (Z_to_bv 64 arr); C8 z64] ->
     u64arr asegs mc arr ws ->
     cps asegs (ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 687280) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 D_defs.TP_A) t0' t1' t2'
          (Z_to_bv 64 2147450880) (Z_to_bv 64 ty) (Z_to_bv 64 sel) a1' (Z_to_bv 64 ty) (Z_to_bv 64 sy) (Z_to_bv 64 i) (Z_to_bv 64 arr)
          (Z_to_bv 64 sx) a7' (Z_to_bv 64 sy) (Z_to_bv 64 (sx * 4294967296)) (Z_to_bv 64 cy) (Z_to_bv 64 cx) s6 s7 s8 s9 s10 s11 x13 x14 x15 x16)
          x17 (Z_to_bv 64 0xa7d1c) x18 None mc (seg_rom asegs)))) QF).
  { clear AGF.
    repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : u64arr asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : munch _ _ _ |- _ => clear H end.
    repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ART RT _ _ |- _ => lazymatch type of H with ART RT Σ m => fail | _ => clear H end end.
    repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
    repeat match goal with H : mem_inv asegs _ |- _ => clear H end.
    repeat match goal with H : stk asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : LIBH _ |- _ => clear H end.
    repeat match goal with H : io_ssp _ |- _ => clear H end.
    induction k as [|k IH]; intros i mc t0' t1' t2' a1' a7' HK HK1 HI ARTk MIk STk LHk SSPk AGFk WMk FRc SC DC.
    { lia. }
    set (row := nth (Z.to_nat i) rows 0).
    assert (RIN0 : In row rows) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) ROWS row RIN0) as (RIN & R0 & R16 & _).
    pose proof (ROWAP row RIN0) as (RAPS & RAPD).
    pose proof (NEWAP _ _ (row_in_sel_live sel (mkSelv sy sx 0 0 arr 0 rows) row RIN0)) as NCR. cbn [s_sx] in NCR.
    assert (NTH : nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 row)) by (rewrite EWS; apply map_nth_error; unfold row; apply nth_error_nth'; lia).
    chunk_facts RT AF GP row (4 * sx).
    lazymatch goal with H : row + 4 * sx <= rt_sp0 RT Σ - 8388608 |- _ => rename H into RKR end.
    lazymatch goal with H : row + 4 * sx <= 65536 \/ _ |- _ => rename H into RKS end.
    lazymatch goal with H : row + 4 * sx <= 2147446784 \/ _ |- _ => rename H into RKH end.
    pose proof (proj1 (af_acc_live RT AF Σ1 mc row (4 * sx) ARTk RIN)) as WRR.
    apply wr_at_rw_CB in WRR; [| lia]. destruct WRR as (rbs & RBC).
    pose proof RBC as [[[RBL _] _] _]. cbn in RBL. apply u8arr_of_rw_cells in RBC.
    destruct (u8arr_u32arr mc row rbs sx RBC ltac:(rewrite RBL; lia)) as (rws & UAR & UARL).
    clear RBC RBL.
    refresh RT AF. unfold SHB in *.
    walk_to AF MST [(row, row + 4 * sx)] [0xa7d34].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u64arr_read asegs mm arr ws i (Z_to_bv 64 row) (Z_to_bv 64 (arr + i * 8)) DC NTH ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RD end.
    lstep. clear RD.
    awalk [0xa7d40].
    eapply evt_cut.
    { lazymatch goal with MIx : mem_inv asegs ?mm, ACCx : acc asegs ?mm row (4 * sx) |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        epose proof (brick_cols (Z.to_nat sx) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm row sx rws
                       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R0 ltac:(clear - R16; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)
                       ltac:(unfold SEGTOP_A; lia) UAR UARL ACCx MIx) as ZR end.
      unfold SHB in ZR. replace (sx - 0) with sx in ZR by lia. replace (row + 4 * 0) with row in ZR by lia. exact ZR. }
    intros ms' PO. unfold brick_cols_exit in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a7'' & m' & ws' & -> & MU' & WM' & MI' & UAR' & UARL').
    loop_art RT AF Σ1 m' lo MU'
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists row, (4 * sx); split; [exact RIN| lia]| exact I]).
    destruct DC as [DCB DCW].
    lazymatch type of MU' with munch _ ?mm m' =>
      loop_transport mm m' MU' ltac:(fun Hx => try rewrite u64s_length in Hx; clear - Hx RKR RKS RKH RAPS RAPD LOW LOR SPT ULEN; lia) end.
    assert (DC : u64arr asegs m' arr ws) by (split; assumption). clear DCB DCW.
    clear MU' WM'.
    destruct k as [|k'].
    - (* [comment removed for export] *)
      awalk (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists row, (4 * sx); split; [exact RIN| lia]| exact I]).
      lazymatch goal with
      | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
          is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (NCR _ Hx); split; [lia| exact I])
      end.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      exists Σ1, sel, (mkSelv sy sx cy cx arr 0 rows).
      cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows].
      split; [| repeat (split; [reflexivity|])].
      2:{ split; [unfold hid in LV1; exact LV1|]. split; [assumption| split; assumption]. }
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [intros a Ha _; apply AGFk; exact Ha|].
      unfold sel_body. cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows]. unfold sel_cells. cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows].
      split; [assumption|].
      split; [unfold chunk; split; [exact SIN| repeat split; first [assumption| lia]]|].
      split; [lia|]. split; [lia|]. split; [exact HLEN|].
      split; [rewrite <- (map_map (Z_to_bv 64) C8), <- EWS; apply u64arr_rw_cells_C8s; exact DC|].
      split; [unfold chunk; split; [exact DIN| repeat split; first [assumption| lia]]| split; [exact ROWS| exact NDUP]].
    - (* [comment removed for export] *)
      awalk [0xa7d1c].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists row, (4 * sx); split; [exact RIN| lia]| exact I]).
      lazymatch goal with
      | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
          is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (NCR _ Hx); split; [lia| exact I])
      end.
      eapply (IH (i + 1)); try eassumption.
      + clear - HK; lia.
      + lia.
      + lia. }
  eapply (ROWLOOP (Z.to_nat sy) 0); try eassumption.
  - lia.
  - lia.
  - lia.
Qed.
End BRICK.

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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_statics Fh_selkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma tr_selCreate_1 : In [0xa7444] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_selCreate_2 : In [0xa75e8] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_selCreate_3 : In [0xa7600] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.

Section SELC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem selCreate_ok : selCreate_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo sy sx
    FDO MST -> -> -> -> HSY HSX S0N ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_selCreate, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold s0_nolink in S0N. fold usp in S0N.
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  walk_to AF MST [(usp - 64, usp)] [e_calloc].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 32); rt_side idtac;
    [ unfold CALLOC_MAX; lia
    | apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_selCreate_1| clear - S0N USP; lia] ]. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  change (1 * 32) with 32 in *. change (Z.to_nat 32) with 32%nat in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 32) :: _ |- _ => rename H into LVS; rename S into Σ1; set (sel := p) in * end.
  assert (INS : In (sel, 32) (rt_live RT Σ1)) by (rewrite LVS; left; reflexivity).
  lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
    pose proof (af_live_range RT AF Σ1 mm sel 32 A INS) as (_ & PSHI & PSSEG);
    pose proof (gp_live_hi RT GP Σ1 mm sel 32 A INS) as PSSH;
    assert (NCS : forall a, PF a -> a < sel \/ sel + 32 <= a)
      by (intros a Ha; apply (new_chunk_apart RT AF Σ1 mm sel 32 (rt_live RT Σ) (rt_frames RT Σ) usp a A LVS);
          [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 64, usp); (sel, sel + 32)] [e_calloc].
  assert (SWM : forall x, -10001 < x - 10001 < 2147483648 -> 0 <= x -> bv_swrap 32 (x + 18446744073709541615) = x - 10001).
  { clear. intros x Hx Hx0. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
    Z.div_mod_to_equations. lia. }
  rewrite (SWM sx) by lia.
  brT.
  awalk [e_calloc].
  rewrite (SWM sy) by lia.
  brT.
  awalk [e_calloc].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                      intros zz Hzz; right; right; left; exists sel, 32; split; [exact INS| lia])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCS _ Hx); repeat split; lia).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := sy) (size := 8); rt_side idtac;
    [ unfold CALLOC_MAX; lia
    | rewrite LVS; cbn [length]; lia
    | apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_selCreate_2| left; ul] ]. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac]| solve [frames_sub_tac]| lia]).
  lazymatch goal with H : rt_live RT ?S = (?p, sy * 8) :: _ |- _ => rename H into LVD; rename S into Σ2; set (arr := p) in * end.
  assert (IND : In (arr, sy * 8) (rt_live RT Σ2)) by (rewrite LVD; left; reflexivity).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with A : ART RT Σ2 ?mm |- cps _ (ASTA RT Σ2 _ _) _ =>
    pose proof (af_live_range RT AF Σ2 mm arr (sy * 8) A IND) as (_ & PDHI & PDSEG);
    pose proof (gp_live_hi RT GP Σ2 mm arr (sy * 8) A IND) as PDSH;
    assert (NCD : forall a, PF a -> a < arr \/ arr + sy * 8 <= a)
      by (intros a Ha; apply (new_chunk_apart RT AF Σ2 mm arr (sy * 8) (rt_live RT Σ1) (rt_frames RT Σ1) usp a A LVD);
          [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
          | apply (aclient_mono _ _ usp _ _ _ _ Ha); [solve [live_add_tac]| solve [frames_sub_tac]| lia] ]);
    assert (QSD : sel + 32 <= arr \/ arr + sy * 8 <= sel)
      by (pose proof (af_live_disj RT AF Σ2 mm arr (sy * 8) sel 32 [] (rt_live RT Σ1) A LVD ltac:(cbn [app]; exact INS)) as X; clear - X; lia) end.
  lazymatch goal with H : rw_cells asegs ?mm arr [CB _ _] |- _ =>
    apply u8arr_of_rw_cells in H; destruct (u8arr_u64arr mm arr _ sy H ltac:(rewrite repeat_length; lia)) as (ws0 & UA & UAL); clear H end.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 64, usp); (sel, sel + 32)] [0xa75f4].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                      intros zz Hzz; right; right; left; exists sel, 32; split; [rewrite LVD; right; exact INS| lia]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCS _ Hx); repeat split; lia)
  end.
  lazymatch goal with H : rw_cells asegs _ sel _ |- _ => rename H into SELC end.
  change (skipn 4 (skipn 4 (repeat (Z_to_bv 8 0) 32))) with (repeat (Z_to_bv 8 0) 24) in SELC.
  assert (LOOP : forall (k : nat) (i c3 p4 : Z) (rows : list Z) (Σk : rts RT) (mc : mem) (ws : list word)
                 (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     Z.of_nat k = sy - i -> (1 <= k)%nat -> 0 <= i -> c3 = sy - i -> p4 = arr + 8 * i ->
     Z.of_nat (length rows) = i -> Forall (fun r => 0 < r /\ r mod 16 = 0) rows ->
     hid (rt_live RT Σk = rev (map (fun r => (r, sx * 4)) rows) ++ (arr, sy * 8) :: (sel, 32) :: rt_live RT Σ) ->
     (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σk)) ->
     In (sel, 32) (rt_live RT Σk) -> In (arr, sy * 8) (rt_live RT Σk) ->
     Z.of_nat (length (rt_live RT Σk)) = Z.of_nat (length (rt_live RT Σ)) + 2 + i ->
     rt_frames RT Σk = rt_frames RT Σ -> rt_sp0 RT Σk = rt_sp0 RT Σ -> rt_credit RT Σk = rt_credit RT Σ ->
     ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -64) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
     rw_cells asegs mc (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     rw_cells asegs mc sel [C4 (Z_to_bv 64 sy); C4 (Z_to_bv 64 sx); CB 24 (repeat (Z_to_bv 8 0) 24)] ->
     u64arr asegs mc arr ws -> Z.of_nat (length ws) = sy -> firstn (length rows) ws = map (Z_to_bv 64) rows ->
     cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 D_defs.TP_A) t0' t1' t2' (Z_to_bv 64 sel) (Z_to_bv 64 arr)
          a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 sx) (Z_to_bv 64 c3) (Z_to_bv 64 p4) (Z_to_bv 64 2147450880) (Z_to_bv 64 p4)
          s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0xa75f4) fc' None mc (seg_rom asegs)))) QF).
  { clear FR SELC UA UAL AGF WM LH SSP MU WM1 WM0 G1 G2 G3 G4 ACC.
    repeat match goal with H : ART RT _ _ |- _ => lazymatch type of H with ART RT Σ m => fail | _ => clear H end end.
    repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
    repeat match goal with H : mem_inv asegs _ |- _ => clear H end.
    repeat match goal with H : stk asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
    induction k as [|k IH]; intros i c3 p4 rows Σk mc ws ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc'
      HK HK1 HI -> -> HLEN ROWSOK LVK SUBK INSk INDk LENK FRK SPK CRK ARTk MIk STk LHk SSPk AGFk WMk FRc SELC UA UAL FIRSTN.
    { lia. }
    refresh RT AF. unfold SHB in *.
    walk_to AF MST [(usp - 64, usp); (arr, arr + sy * 8)] [e_calloc].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; right; right; left; exists arr, (sy * 8); split; [exact INDk| lia])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCD _ Hx); repeat split; lia).
    eapply cps_seq.
    { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := sx) (size := 4); rt_side idtac;
      [ unfold CALLOC_MAX; lia
      | apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_selCreate_3| left; ul] ]. }
    after_call RT AF.
    after_call RT AF.
    lazymatch goal with AG : agree_on ?P2 mc ?m1 |- _ =>
      pose proof (u64arr_agree P2 mc m1 arr ws UA AG ltac:(intros zz Hzz; right; right; left; exists arr, (sy * 8); split; [exact INDk| lia])) as UA1; clear UA end.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact SUBK| solve [frames_sub_tac]| lia]).
    lazymatch goal with H : rt_live RT ?S = (?p, sx * 4) :: _ |- _ => rename H into LVN; rename S into Σn; set (row := p) in * end.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *.
    pose proof firstn_upd_snoc as FUS.
    lazymatch goal with H1 : 0 < row, H2 : row mod 16 = 0 |- _ => pose proof (conj H1 H2) as ROWP end.
    lazymatch goal with H : rw_cells asegs _ row _ |- _ => clear H end.
    walk_to AF MST [(usp - 64, usp); (arr, arr + sy * 8); (sel, sel + 32)] [0xa7610].
    arr_sd arr i (arr + 8 * i).

    destruct k as [|k'].
    - (* [comment removed for export] *)
      assert (ILAST : i = sy - 1) by (clear - HK; lia).
      awalk (@nil Z).
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| split; [| exact I]]];
                          intros zz Hzz; right; right; left; [exists arr, (sy * 8)| exists sel, 32]; (split; [rewrite LVN; right; assumption| lia])).
      lazymatch goal with
      | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
          is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCS _ Hx); pose proof (NCD _ Hx); repeat split; lia)
      end.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      exists Σn, sel, (mkSelv sy sx 0 0 arr 0 (rows ++ [row])).
      cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows].
      split; [| repeat (split; [reflexivity|])].
      2:{ split; [| split; [congruence| split; congruence]].
          unfold sel_live. cbn [tl s_sy s_sx s_cy s_cx s_data s_name s_rows]. unfold hid in LVK. rewrite LVN, LVK, map_app, rev_app_distr. cbn [map rev app].
          replace (4 * sx) with (sx * 4) by lia. replace (8 * sy) with (sy * 8) by lia. rewrite <- app_assoc. reflexivity. }
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [intros a Ha _; apply AGFk; exact Ha|].
      unfold sel_body. cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows].
      split.
      { lazymatch goal with H : rw_cells asegs ?mm sel ?cs |- rw_cells asegs ?mm sel _ =>
          apply (rw_cells_recell _ _ _ _ H); [cbn; repeat split| | reflexivity] end.
        unfold sel_cells. cbn [cells_bytes cbytes s_sy s_sx s_cy s_cx s_data s_name]. do 2 f_equal. }
      split. { unfold chunk; split; [rewrite LVN; right; exact INSk| repeat split; first [assumption| lia]]. }
      split; [lia|]. split; [lia|].
      split. { rewrite length_app; cbn [length]; lia. }
      split.
      { rewrite <- (map_map (Z_to_bv 64) C8). apply u64arr_rw_cells_C8s.
        lazymatch goal with UAx : u64arr asegs ?mm arr ?w |- u64arr asegs ?mm arr ?w' => replace w' with w; [exact UAx|] end.
        rewrite <- (firstn_all (upd ws (Z.to_nat i) (Z_to_bv 64 row))). rewrite upd_length. replace (length ws) with (S (Z.to_nat i)) by lia.
        rewrite FUS by lia. replace (Z.to_nat i) with (length rows) by lia. rewrite FIRSTN, map_app. reflexivity. }
      split. { unfold chunk; split; [rewrite LVN; right; replace (8 * sy) with (sy * 8) by lia; exact INDk| repeat split; first [assumption| lia]]. }
      split.
      2:{ (* [comment removed for export] *)
        lazymatch goal with A : ART RT Σn ?mm |- _ =>
          pose proof (live_nodup_seg RT AF Σn mm ((row, sx * 4) :: rev (map (fun r => (r, sx * 4)) rows) ++ [(arr, sy * 8); (sel, 32)]) [] (rt_live RT Σ) A
                        ltac:(unfold hid in LVK; rewrite LVN, LVK; cbn [app]; rewrite <- app_assoc; reflexivity)) as ND end.
        assert (POS : forall p n, In (p, n) ((row, sx * 4) :: rev (map (fun r => (r, sx * 4)) rows) ++ [(arr, sy * 8); (sel, 32)]) -> 0 < n).
        { intros p n [E|Hin]; [injection E as _ <-; lia|]. apply in_app_or in Hin. destruct Hin as [Hin|[E|[E|[]]]]; try (injection E as _ <-; lia).
          apply in_rev in Hin. apply in_map_iff in Hin as (r0 & E & _). injection E as _ <-. lia. }
        specialize (ND POS). cbn [map fst] in ND. rewrite map_app, map_rev, map_map in ND. cbn [map fst] in ND.
        change (map (fun r : Z => fst (r, sx * 4)) rows) with (map (fun r : Z => r) rows) in ND. rewrite map_id in ND.
        apply NoDup_rev in ND. cbn [rev] in ND. rewrite rev_app_distr, rev_involutive in ND. cbn [rev app] in ND. exact ND. }
      apply Forall_app; split.
      + apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) ROWSOK r Hr) as (R0 & R16). unfold chunk.
        split; [| repeat split; first [assumption| lia]].
        rewrite LVN. right. unfold hid in LVK. rewrite LVK. apply in_or_app. left. apply -> in_rev. replace (4 * sx) with (sx * 4) by lia.
        apply (in_map (fun r => (r, sx * 4))). exact Hr.
      + constructor; [| constructor]. unfold chunk. split; [rewrite LVN; left; f_equal; lia| repeat split; first [apply ROWP | lia]].
    - (* [comment removed for export] *)
      awalk [0xa75f4].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| split; [| exact I]]];
                          intros zz Hzz; right; right; left; [exists arr, (sy * 8)| exists sel, 32]; (split; [rewrite LVN; right; assumption| lia])).
      lazymatch goal with
      | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
          is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCS _ Hx); pose proof (NCD _ Hx); repeat split; lia)
      end.
      eapply (IH (i + 1) _ _ (rows ++ [row]) Σn _ (upd ws (Z.to_nat i) (Z_to_bv 64 row))); try eassumption.
      + clear - HK; lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + rewrite length_app; cbn [length]; lia.
      + apply Forall_app; split; [exact ROWSOK| constructor; [exact ROWP| constructor]].
      + unfold hid in *. rewrite LVN, LVK, map_app, rev_app_distr. reflexivity.
      + intros e He. rewrite LVN. right. exact (SUBK e He).
      + rewrite LVN; right; exact INSk.
      + rewrite LVN; right; exact INDk.
      + rewrite LVN. cbn [length]. rewrite Nat2Z.inj_succ. lia.
      + congruence.
      + congruence.
      + rewrite upd_length; exact UAL.
      + rewrite length_app. cbn [length]. replace (length rows + 1)%nat with (S (length rows)) by lia.
        replace (Z.to_nat i) with (length rows) by lia. rewrite FUS by lia. rewrite FIRSTN, map_app. reflexivity. }
  eapply (LOOP (Z.to_nat sy) 0 _ _ [] Σ2 _ ws0); try eassumption.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - constructor.
  - unfold hid. rewrite LVD, LVS. reflexivity.
  - intros e He. rewrite LVD, LVS. right; right; exact He.
  - rewrite LVD; right; exact INS.
  - rewrite LVD, LVS. cbn [length]. rewrite !Nat2Z.inj_succ. lia.
  - congruence.
  - congruence.
  - reflexivity.
Qed.
End SELC.

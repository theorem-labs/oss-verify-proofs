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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_statics Fh_selkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= first [ zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section SELADD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis SN : stringNew_cps RT.

Theorem selaAddSel_ok : selaAddSel_cps RT.
Proof using AF GP SN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo sela arr sel sels v i live0
    FDO MST -> -> -> -> -> HI SAO LSELS SB NAME0 SHAPE ENV RES.
  pose proof ENV as ENV0. pose proof RES as RES0.
  unfold lpost, lenv, lres, keeps, keepsL in ENV, RES |- *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_selaAddSel, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof SAO as (SAC & (SAIN & SA0 & SA16 & _) & (ARIN & AR0 & AR16 & _) & L50 & ARRC & SELS).
  pose proof SB as (SC & (SIN & S0 & S16 & _) & HSY & HSX & HLEN & DC & (DIN & D0 & D16 & _) & ROWS & NDUP).
  unfold sel_cells in SC. rewrite NAME0 in SC. unfold sela_cells in SAC.
  set (n := Z.of_nat (length sels)) in *.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(sel + 24, sel + 32); (sela, sela + 4); (arr, arr + 400)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  (* [comment removed for export] *)
  assert (QSA : (sel + 32 <= sela \/ sela + 16 <= sel) /\ (sel + 32 <= arr \/ arr + 400 <= sel) /\ (arr + 400 <= sela \/ sela + 16 <= arr)).
  { split; [| split].
    - apply (live_segs_disj RT AF Σ m [] _ _ _ ART0 SHAPE sel 32 sela 16 (sel_in_sel_live sel v)). unfold sela_live. apply in_or_app. right. right. left. reflexivity.
    - apply (live_segs_disj RT AF Σ m [] _ _ _ ART0 SHAPE sel 32 arr 400 (sel_in_sel_live sel v)). unfold sela_live. apply in_or_app. right. left. reflexivity.
    - apply (af_live_disj RT AF Σ m arr 400 sela 16 (tl (sel_live sel v) ++ flat_map (fun e => sel_live (fst (fst e)) (snd (fst e))) (rev sels)) ((sela, 16) :: live0) ART0).
      + rewrite SHAPE. unfold sela_live. rewrite <- !app_assoc. reflexivity.
      + apply in_or_app. right. left. reflexivity. }
  destruct QSA as (QSA1 & QSA2 & QSA3).
  hide SHAPE.
  (* [comment removed for export] *)
  set (ws := map (fun e : Z * selv * list byte => Z_to_bv 64 (fst (fst e))) sels ++ repeat (Z_to_bv 64 0) (50 - length sels)).
  assert (ARRU : u64arr asegs m arr ws).
  { apply rw_cells_C8s_u64arr. unfold ws. rewrite map_app, map_map, map_repeat. exact ARRC. }
  assert (UAL : Z.of_nat (length ws) = 50) by (unfold ws; rewrite length_app, length_map, repeat_length; lia).
  clear ARRC DC.
  chunk_facts RT AF GP sel 32. chunk_facts RT AF GP sela 16. chunk_facts RT AF GP arr 400.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 112, usp)] [e_stringNew].
  unfold HM_NAME_LIT in *.
  brT.
  awalk [e_stringNew].
  destruct (hm_name_shape i HI) as (str & ESTR & LSTR & NZSTR).
  pose proof (hm_name_lit_ro i HI) as ROB. rewrite ESTR in ROB. pose proof (hm_name_lit_in i HI) as INL. unfold HM_NAME_LIT in ROB, INL.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply SN with (lo := lo) (src := 159616 + 32 * i) (str := str); rt_side idtac.
    lenv_tac. }
  after_call RT AF.
  lazymatch goal with AG : agree_on ?P2 ?ma ?mb, UA : u64arr asegs ?ma arr ws |- _ =>
    pose proof (u64arr_agree P2 ma mb arr ws UA AG ltac:(intros zz Hzz; split; [right; right; left; exists arr, 400; split; [exact ARIN| lia]| exact I])) as ARRU1; clear UA end.
  fold_ag ltac:(fun Hx => split; [destruct Hx as [Hx _]; apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact He| intros e He; exact He| lia]| exact I]).
  lazymatch goal with H : rt_live RT ?S = (?p, 8) :: _ |- _ => rename H into LVN; rename S into Σ1; set (dest := p) in * end.
  lazymatch goal with H : bytes_at asegs _ dest _ |- _ => rename H into NMB end.
  assert (INN : In (dest, 8) (rt_live RT Σ1)) by (rewrite LVN; left; reflexivity).
  lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
    assert (QN : (sel + 32 <= dest \/ dest + 8 <= sel) /\ (sela + 16 <= dest \/ dest + 8 <= sela) /\ (arr + 400 <= dest \/ dest + 8 <= arr))
      by (pose proof (af_live_disj RT AF Σ1 mm dest 8 sel 32 [] (rt_live RT Σ) A LVN SIN) as X1;
          pose proof (af_live_disj RT AF Σ1 mm dest 8 sela 16 [] (rt_live RT Σ) A LVN SAIN) as X2;
          pose proof (af_live_disj RT AF Σ1 mm dest 8 arr 400 [] (rt_live RT Σ) A LVN ARIN) as X3; clear - X1 X2 X3; lia) end.
  destruct QN as (QN1 & QN2 & QN3).
  assert (SUB1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LVN; right; exact He).
  pose proof (SUB1 _ SIN) as SIN1. pose proof (SUB1 _ SAIN) as SAIN1. pose proof (SUB1 _ ARIN) as ARIN1.
  hide LVN.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 112, usp); (sel + 24, sel + 32); (sela, sela + 4); (arr, arr + 400)] [0xa836c].
  assert (NR : 0 <= n < 10) by (unfold n; lia).
  sx32_fix. brT.
  awalk [0xa836c].
  arr_sd arr n (arr + n * 8).
  sx32_fix.
  awalk (@nil Z).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| split; [| split; [| exact I]]]];
                      intros zz Hzz; right; right; left; [exists sel, 32; split; [exact SIN1| lia]| exists sela, 16; split; [exact SAIN1| lia]| exists arr, 400; split; [exact ARIN1| lia]]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; first [lia | tauto])
  end.
  apply cps_finish; intros c Hc; subst QF; cbv beta zeta.
  exists Σ1, dest.
  split; [| unfold hid in LVN; split; [exact LVN| split; [assumption| split; assumption]]].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
  split; [intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
  assert (LENS : length (sels ++ [(sel, mkSelv (s_sy v) (s_sx v) (s_cy v) (s_cx v) (s_data v) dest (s_rows v), hm_name (Z.to_nat i))]) = S (length sels))
    by (rewrite length_app; cbn [length]; lia).
  unfold sela_obj. rewrite LENS.
  lazymatch goal with H : rw_cells asegs _ sela _ |- _ =>
    rewrite (unsigned_lit n) in H by lia; rewrite (bv_swrap_small 32 n) in H by (change (bv_half_modulus 32) with (2^31); lia) end.
  split. { unfold sela_cells. replace (Z.of_nat (S (length sels))) with (n + 1) by (unfold n; lia). assumption. }
  split. { unfold chunk; split; [exact SAIN1| repeat split; first [assumption| lia]]. }
  split. { unfold chunk; split; [exact ARIN1| repeat split; first [assumption| lia]]. }
  split. { lia. }
  split.
  { (* [comment removed for export] *)
    lazymatch goal with UAx : u64arr asegs m1 arr ?w |- _ => apply u64arr_rw_cells_C8s in UAx; rename UAx into ARRF end.
    replace (Z.to_nat n) with (length (map (fun e : Z * selv * list byte => Z_to_bv 64 (fst (fst e))) sels)) in ARRF by (rewrite length_map; unfold n; lia).
    unfold ws in ARRF. rewrite upd_app_len in ARRF by (replace (50 - length sels)%nat with (S (50 - S (length sels))) by lia; discriminate).
    replace (50 - length sels)%nat with (S (50 - S (length sels))) in ARRF by lia. cbn [repeat tl] in ARRF.
    rewrite map_app, map_map in ARRF. cbn [map] in ARRF. rewrite map_repeat in ARRF.
    rewrite map_app. cbn [map fst snd]. rewrite <- app_assoc. cbn [app]. exact ARRF. }
  unfold hid in SHAPE.
  assert (INLIVE : forall p k, In (p, k) (sela_live sela arr sels) -> In (p, k) (rt_live RT Σ)).
  { intros p k Hp. rewrite SHAPE. apply in_or_app. right. apply in_or_app. left. exact Hp. }
  assert (INLIVE2 : forall p k, In (p, k) (tl (sel_live sel v)) -> In (p, k) (rt_live RT Σ)).
  { intros p k Hp. rewrite SHAPE. apply in_or_app. left. exact Hp. }
  apply Forall_app. split.
  - (* [comment removed for export] *)
    apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) SELS e He) as SO. cbv beta in SO.
    apply (sel_obj_agree (rt_live RT Σ) (rt_live RT Σ1) m m1 _ _ _ SO SUB1).
    eapply agree_sub; [exact AGF|]. intros x Hx. destruct Hx as (p & k & Hp & Hx).
    assert (HpF : In (p, k) (flat_map (fun e0 : Z * selv * list byte => sel_live (fst (fst e0)) (snd (fst e0))) (rev sels)))
      by (apply in_flat_map; exists e; split; [apply -> in_rev; exact He| exact Hp]).
    assert (HpL : In (p, k) (rt_live RT Σ)) by (apply INLIVE; unfold sela_live; apply in_or_app; left; exact HpF).
    pose proof (live_segs_disj RT AF Σ m [] _ _ _ ART0 SHAPE sel 32 p k (sel_in_sel_live sel v) ltac:(unfold sela_live; apply in_or_app; left; exact HpF)) as D1.
    assert (SHAPE2 : rt_live RT Σ = tl (sel_live sel v) ++ flat_map (fun e0 : Z * selv * list byte => sel_live (fst (fst e0)) (snd (fst e0))) (rev sels) ++ [(arr, 400); (sela, 16)] ++ live0)
      by (rewrite SHAPE; unfold sela_live; rewrite <- !app_assoc; reflexivity).
    pose proof (live_segs_disj RT AF Σ m _ _ _ _ ART0 SHAPE2 p k arr 400 HpF ltac:(left; reflexivity)) as D2.
    pose proof (live_segs_disj RT AF Σ m _ _ _ _ ART0 SHAPE2 p k sela 16 HpF ltac:(right; left; reflexivity)) as D3.
    split; [right; right; left; exists p, k; split; [exact HpL| exact Hx]|].
    cbn [outside]. clear - Hx D1 D2 D3. repeat split; lia.
  - (* [comment removed for export] *)
    constructor; [| constructor]. cbn [fst snd].
    assert (NED : s_data v <> sel) by (apply NoDup_cons_iff in NDUP as (N1 & _); intros E; apply N1; left; exact E).
    pose proof (live_addr_disj RT AF Σ m (s_data v) (8 * s_sy v) sel 32 ART0 DIN SIN NED) as DD1.
    pose proof (live_segs_disj RT AF Σ m [] _ _ _ ART0 SHAPE (s_data v) (8 * s_sy v) arr 400 (data_in_sel_live sel v) ltac:(unfold sela_live; apply in_or_app; right; left; reflexivity)) as DD2.
    pose proof (live_segs_disj RT AF Σ m [] _ _ _ ART0 SHAPE (s_data v) (8 * s_sy v) sela 16 (data_in_sel_live sel v) ltac:(unfold sela_live; apply in_or_app; right; right; left; reflexivity)) as DD3.
    unfold sel_obj. split; [| split; [| split]].
    + (* [comment removed for export] *)
      unfold sel_body. cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows]. unfold sel_cells. cbn [s_sy s_sx s_cy s_cx s_data s_name s_rows].
      split; [assumption|].
      split; [unfold chunk; split; [exact SIN1| repeat split; first [assumption| lia]]|].
      pose proof SB as (_ & _ & HSY' & HSX' & HLEN' & _).
      split; [exact HSY'|]. split; [exact HSX'|]. split; [exact HLEN'|].
      split.
      { pose proof SB as (_ & _ & _ & _ & _ & DC0 & _).
        apply (rw_cells_agree_nw asegs m m1 (s_data v) _ DC0). eapply agree_sub; [exact AGF|]. cbv beta. intros x Hx.
        rewrite (cells_size_C8map Z (Z_to_bv 64) (s_rows v)) in Hx.
        split; [right; right; left; exists (s_data v), (8 * s_sy v); split; [exact DIN| lia]|].
        cbn [outside]. clear - Hx DD1 DD2 DD3 HLEN'. repeat split; lia. }
      split; [unfold chunk; split; [exact (SUB1 _ DIN)| repeat split; first [assumption| lia]]|].
      split; [| exact NDUP].
      eapply Forall_impl; [| exact ROWS]. intros r Hr. exact (chunk_mono _ _ _ _ Hr SUB1).
    + cbn [s_name]. rewrite ESTR. assumption.
    + cbn [s_name]. unfold chunk; split; [exact INN| repeat split; first [assumption| lia]].
    + rewrite ESTR, length_app, LSTR. reflexivity.
Qed.
End SELADD.

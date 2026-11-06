(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
     Sj_num_akit Sj_num_amem Sj_num_aframe Sj_num_lm_kit Pj_defsA Pj_rtkA Pj_tocharsA_defs Pj_tocharsA_a Pj_tocharsA_r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma u8arr_after_dst : forall (m m' : mem) A (bs0 : list byte) d (bs : list byte),
  u8arr asegs m A bs0 -> length bs0 = 40%nat -> A <= d -> d + Z.of_nat (length bs) <= A + 40 ->
  agree_on (fun x => A <= x < A + 40 /\ ~ (d <= x < d + Z.of_nat (length bs))) m m' -> wmono asegs m m' ->
  bytes_at asegs m' d bs ->
  exists bs', u8arr asegs m' A bs' /\ length bs' = 40%nat.
Proof.
  intros m m' A bs0 d bs UA L0 HA HD AG WM BY.
  destruct (u8arr_range_split asegs m A bs0 (Z.to_nat (d - A)) (Z.to_nat (d - A) + length bs) UA ltac:(lia) ltac:(lia))
    as (b1 & mid & b3 & L1 & L2 & L3 & U1 & MID & U3).
  assert (U1' : u8arr asegs m' A b1).
  { apply (u8arr_agree m m' A b1 U1); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. rewrite L1 in Hx. lia. }
  assert (U3' : u8arr asegs m' (A + Z.of_nat (Z.to_nat (d - A) + length bs)) b3).
  { apply (u8arr_agree m m' _ b3 U3); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. rewrite L3, L0 in Hx. lia. }
  assert (MID' : rw_cells asegs m' (A + Z.of_nat (length b1)) [CB (length bs) bs]).
  { rewrite L1. replace (A + Z.of_nat (Z.to_nat (d - A))) with d by lia. apply rw_cells_CB_intro; [exact BY|].
    destruct MID as [_ W2]. cbn [cells_size csize Nat.add] in W2. rewrite Nat.add_0_r in W2.
    replace (A + Z.of_nat (Z.to_nat (d - A))) with d in W2 by lia.
    replace (Z.to_nat (d - A) + length bs - Z.to_nat (d - A))%nat with (length bs) in W2 by lia.
    exact (wr_at_transport asegs m m' d _ W2 WM). }
  destruct (u8arr_range_join asegs m' A b1 (length bs) bs b3 U1' MID') as (bs' & LB & UB).
  { rewrite L1. replace (A + Z.of_nat (Z.to_nat (d - A)) + Z.of_nat (length bs)) with (A + Z.of_nat (Z.to_nat (d - A) + length bs)) by lia. exact U3'. }
  exists bs'. split; [exact UB|]. rewrite LB, L1, L3, L0. lia.
Qed.

Section TCK.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis MST : mat_stable PMc.
Variables (Σ Σ1 : rts RT) (J : tcI) (fN : Z) (kN : nat).
Hypothesis OK : tc_ok J.

Notation q := (ti_q J). Notation spq := (ti_spq J). Notation NB := (ti_NB J). Notation f := (ti_f J). Notation Sh := (ti_S J). Notation lo := (ti_lo J).

Hypothesis EF : rt_frames RT Σ1 = (ti_f J, 1%nat) :: rt_frames RT Σ.
Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ.
Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ.
Hypothesis INF : In (fN, kN) (rt_frames RT Σ).
Hypothesis NBF : fN <= ti_NB J /\ ti_NB J + 40 <= fN + fs_size kN - 8.
Hypothesis LOR : rt_sp0 RT Σ - STACK_WIN <= ti_lo J.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition BASE (m0 mb : mem) : Prop :=
  ART RT Σ1 mb /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(NB, NB + 40)] m0 mb /\ bytes_at asegs mb (shad NB) (repeat z8 5).

Lemma inF1 : In (ti_f J, 1%nat) (rt_frames RT Σ1).
Proof using EF. rewrite EF. left. reflexivity. Qed.
Lemma inFN1 : In (fN, kN) (rt_frames RT Σ1).
Proof using EF INF. rewrite EF. right. exact INF. Qed.

Lemma fpW : fp_ok RT Σ1 spq (tc_W J).
Proof using OK EF INF NBF.
  pose proof inF1 as IN1. pose proof inFN1 as IN2. ti_envX OK. unfold fp_ok, tc_W, ti_spq, ti_S.
  apply Forall_cons; [cbn [fst snd]; left; ul|].
  apply Forall_cons; [cbn [fst snd]; right; right; left; exists fN, kN; split; [exact IN2| lia]|].
  apply Forall_cons; [cbn [fst snd]; right; right; left; exists (ti_f J), 1%nat; split; [exact IN1| rewrite fs1; lia]|].
  apply Forall_cons; [cbn [fst snd]; right; right; left; exists (ti_f J), 1%nat; split; [exact IN1| rewrite fs1; lia]|].
  apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]; right; right; right. exists (ti_f J), 1%nat. split; [exact IN1|]. rewrite fs1s. unfold shad, SHB. lia.
Qed.

Lemma W_out : forall (mb : mem) a, ART RT Σ1 mb -> aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (NB <= a < NB + 40) -> outside (tc_W J) a.
Proof using AF OK EF EL ES LOR.
  intros mb a ART1 Ha Hnb. ti_envX OK.
  assert (ELi : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL; auto).
  destruct (newframe_apartI RT AF Σ Σ1 mb (ti_f J) 1%nat q a ART1 EF ELi ES ltac:(lia) Ha) as [N1 N2].
  rewrite ?fs1s, ?fs1 in N2. rewrite ?fs1 in N1. unfold shad, SHB, fs_size in N1, N2. cbn [Z.shiftl Z.of_nat Pos.of_succ_nat Pos.succ Pos.iter Z.mul Pos.mul] in N1, N2.
  assert (SPL : q <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
  { destruct (aclient_split_c RT AF Σ1 mb q a ART1) as [H|H]; [| left; exact H| right; rewrite <- ES; exact H].
    rewrite EF. eapply aclient_mono; [exact Ha| exact ELi| intros x Hx; right; exact Hx| lia]. }
  unfold tc_W, ti_spq, ti_S. cbn [outside]. repeat split; lia.
Qed.

Lemma base_art : forall m0 mb mm shc, BASE m0 mb -> TINV J shc mb mm -> ART RT Σ1 mm.
Proof using AF OK EF INF NBF LOR ES.
  intros m0 mb mm shc (ART1 & _ & _) TI. ti_open TI. pose proof OK as OK'. destruct OK' as [Cd _ Croom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  apply (art_of_munch RT AF Σ1 mb mm spq (tc_W J) ART1); [rewrite ES; unfold ti_spq; lia| exact fpW| exact MU| exact WM].
Qed.

Lemma base_pres : forall m0 mb mm, BASE m0 mb -> munch (tc_W J) mb mm -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(NB, NB + 40)] m0 mm.
Proof using AF OK EF EL ES LOR.
  intros m0 mb mm (ART1 & PRES & _) MU.
  eapply pres_fp_trans; [exact PRES|]. apply (pres_fp_of_munch _ _ _ _ _ _ _ MU).
  intros a Ha Ho. apply (W_out mb a ART1 Ha). cbn [outside] in Ho. lia.
Qed.

Lemma base_nbsh : forall m0 mb mm, BASE m0 mb -> munch (tc_W J) mb mm -> bytes_at asegs mm (shad NB) (repeat z8 5).
Proof using OK.
  intros m0 mb mm (_ & _ & SHN) MU. ti_envX OK.
  apply (bytes_at_agree asegs mb mm _ _ SHN). apply (agree_of_munch _ _ _ _ MU).
  intros x Hx. rewrite repeat_length in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. unfold tc_W, ti_spq, ti_S. cbn [outside].
  repeat split; lia.
Qed.

Lemma base_shpn : forall m0 mb, BASE m0 mb -> nb_shz J mb.
Proof using OK.
  intros m0 mb B m' MU WM. pose proof (base_nbsh m0 mb m' B MU) as SHN. ti_envX OK.
  change 40 with (8 * Z.of_nat 5). apply shz_run0; [exact Cnb8| lia| exact SHN].
Qed.

Lemma base_shpd : forall m0 mb, BASE m0 mb -> dig_shz J mb.
Proof using AF OK EF INF NBF LOR ES.
  intros m0 mb (ART1 & _) m' MU WM. pose proof OK as OK'. destruct OK' as [Cd _ Croom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  assert (ART' : ART RT Σ1 m').
  { apply (art_of_munch RT AF Σ1 mb m' spq (tc_W J) ART1); [rewrite ES; unfold ti_spq; lia| exact fpW| exact MU| exact WM]. }
  change 200 with (8 * (200 / 8)). apply shz_of_acc; [| reflexivity| lia].
  apply (acc_lit RT AF Σ1 m' 0x29df0 200 ART'). unfold ACC_LITS. cbn [In]. repeat (first [left; reflexivity | right]).
Qed.

Lemma tinv_rebase_k : forall mb mm m' shc, TINV J shc mb mm -> cells_size shc = 16%nat ->
  munch [(spq - 16, spq)] mm m' -> wmono asegs mm m' -> mem_inv asegs m' -> stk asegs m' lo spq -> TINV J shc m' m'.
Proof using OK.
  intros mb mm m' shc TI SZ MUK WMK MI' ST'. ti_open TI. ti_envX OK.
  assert (AG : forall P : Z -> Prop, (forall x, P x -> ~ (q - 128 - ti_d J - 16 <= x < q - 128 - ti_d J)) -> agree_on P mm m').
  { intros P HP a Ha. apply MUK. cbn [outside]. split; [| exact I]. apply HP. exact Ha. }
  split. { exists j7, t17, jd. apply (rw_cells_agree asegs mm m' _ _ LOC); [| exact WMK]. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  split. { apply (rw_cells_agree asegs mm m' _ _ SAVED); [| exact WMK]. apply AG. intros x Hx. cbn [cells_size csize Nat.add tc_saved] in Hx. lia. }
  split. { exists h0, h1, h2. apply (rw_cells_agree asegs mm m' _ _ HDR); [| exact WMK]. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  split. { exists tmp. split; [| exact TL]. apply (u8arr_agree mm m' _ _ TA); [| exact WMK]. apply AG. intros x Hx. rewrite TL in Hx. cbn in Hx. lia. }
  split. { apply (rw_cells_agree asegs mm m' _ _ SH); [| exact WMK]. apply AG. intros x Hx. rewrite SZ in Hx. cbn in Hx. lia. }
  split. { exists nb. split; [| exact NL]. apply (u8arr_agree mm m' _ _ NA); [| exact WMK]. apply AG. intros x Hx. rewrite NL in Hx. cbn in Hx. lia. }
  split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST'].
Qed.

Lemma base_rebase_k : forall m0 mb mm m' shc, BASE m0 mb -> TINV J shc mb mm ->
  munch [(spq - 16, spq)] mm m' -> ART RT Σ1 m' -> BASE m0 m'.
Proof using AF OK EF EL ES LOR.
  intros m0 mb mm m' shc B TI MUK ART'. pose proof B as (ART1 & _ & _). ti_open TI. ti_envX OK.
  split; [exact ART'|]. split.
  - eapply pres_fp_trans; [exact (base_pres m0 mb mm B MU)|].
    apply (pres_fp_of_munch _ _ _ _ _ _ _ MUK). intros a Ha Ho. cbn [outside]. split; [| exact I].
    assert (ELi : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL; auto).
    destruct (aclient_split_c RT AF Σ1 mb q a ART1) as [H|H]; [| lia| rewrite ES in H; lia].
    rewrite EF. eapply aclient_mono; [exact Ha| exact ELi| intros x Hx; right; exact Hx| lia].
  - apply (bytes_at_agree asegs mm m' _ _ (base_nbsh m0 mb mm B MU)). apply (agree_of_munch _ _ _ _ MUK).
    intros x Hx. rewrite repeat_length in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. unfold shad, SHB in Hx. cbn [outside]. split; [lia| exact I].
Qed.

Lemma tinv_client : forall x,
  (spq <= x < q) \/ (NB <= x < NB + 40) \/ (f <= x < f + 72) \/ (Sh <= x < Sh + 16) ->
  aclient (rt_live RT Σ1) (rt_frames RT Σ1) spq x.
Proof using OK EF INF NBF.
  intros x Hx. pose proof inF1 as IN1. pose proof inFN1 as IN2. ti_envX OK.
  destruct Hx as [H|[H|[H|H]]].
  - left. ul.
  - right; right; right; left. exists fN, kN. split; [exact IN2| lia].
  - right; right; right; left. exists (ti_f J), 1%nat. split; [exact IN1| rewrite fs1; lia].
  - right; right; right; right. exists (ti_f J), 1%nat. split; [exact IN1|]. rewrite fs1s. unfold shad, SHB. lia.
Qed.

Lemma tinv_after_nb : forall mb mm m' shc d k (bs : list byte), TINV J shc mb mm -> cells_size shc = 16%nat ->
  rt_after RT Σ1 spq lo mm m' -> rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) spq d k mm m' ->
  bytes_at asegs m' d bs -> Z.of_nat (length bs) = k -> NB <= d -> d + k <= NB + 40 ->
  TINV J shc m' m'.
Proof using OK EF INF NBF.
  intros mb mm m' shc d k bs TI SZ (ART' & MI' & WM' & ST') PR BY LK D1 D2. subst k. ti_open TI. ti_envX OK.
  assert (AG : forall P : Z -> Prop,
    (forall x, P x -> ((q - 128 - ti_d J <= x < q) \/ (NB <= x < NB + 40) \/ (f <= x < f + 72) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16))
                      /\ ~ (d <= x < d + Z.of_nat (length bs))) -> agree_on P mm m').
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply (PR a); [| exact H2]. apply tinv_client. unfold ti_spq, ti_S. exact H1. }
  split. { exists j7, t17, jd. apply (rw_cells_agree asegs mm m' _ _ LOC); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; lia. }
  split. { apply (rw_cells_agree asegs mm m' _ _ SAVED); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add tc_saved] in Hx. split; lia. }
  split. { exists h0, h1, h2. apply (rw_cells_agree asegs mm m' _ _ HDR); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; lia. }
  split. { exists tmp. split; [| exact TL]. apply (u8arr_agree mm m' _ _ TA); [| exact WM']. apply AG. intros x Hx. rewrite TL in Hx. cbn in Hx. split; lia. }
  split. { apply (rw_cells_agree asegs mm m' _ _ SH); [| exact WM']. apply AG. intros x Hx. rewrite SZ in Hx. cbn in Hx. split; lia. }
  split. { apply (u8arr_after_dst mm m' _ nb d bs NA NL D1 D2); [| exact WM'| exact BY]. apply AG. intros x [Hx1 Hx2]. split; [lia| exact Hx2]. }
  split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST'].
Qed.

Lemma tinv_after_tmp : forall mb mm m' shc (bs : list byte), TINV J shc mb mm -> cells_size shc = 16%nat ->
  rt_after RT Σ1 spq lo mm m' -> rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) spq (spq + 15) 17 mm m' ->
  bytes_at asegs m' (spq + 15) bs -> length bs = 17%nat ->
  TINV J shc m' m'.
Proof using OK EF INF NBF.
  intros mb mm m' shc bs TI SZ (ART' & MI' & WM' & ST') PR BY LB. ti_open TI. ti_envX OK.
  assert (AG : forall P : Z -> Prop,
    (forall x, P x -> ((q - 128 - ti_d J <= x < q) \/ (NB <= x < NB + 40) \/ (f <= x < f + 72) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16))
                      /\ ~ (q - 128 - ti_d J + 15 <= x < q - 128 - ti_d J + 15 + 17)) -> agree_on P mm m').
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply (PR a); [| unfold ti_spq; exact H2]. apply tinv_client. unfold ti_spq, ti_S. exact H1. }
  split.
  { destruct (proj1 (num_rw_cells_app asegs mm _ [_; _] _) LOC) as [L1 L23]. cbn [cells_size csize Nat.add] in L23.
    destruct (proj1 (num_rw_cells_app asegs mm _ [_] _) L23) as [L2 L3]. cbn [cells_size csize Nat.add] in L3.
    exists j7, bs, jd.
    apply (proj2 (num_rw_cells_app asegs m' _ [_; _] _)). split.
    { apply (rw_cells_agree asegs mm m' _ _ L1); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; lia. }
    cbn [cells_size csize Nat.add]. apply (proj2 (num_rw_cells_app asegs m' _ [_] _)). split.
    { rewrite <- LB. apply rw_cells_CB_intro; [replace (q - 128 - ti_d J + Z.of_nat 15) with (q - 128 - ti_d J + 15) by lia; exact BY|].
      rewrite LB. destruct L2 as [_ W2]. cbn [cells_size csize Nat.add] in W2. exact (wr_at_transport asegs mm m' _ _ W2 WM'). }
    cbn [cells_size csize Nat.add].
    apply (rw_cells_agree asegs mm m' _ _ L3); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [lia|].
    destruct Cd as [Ed|Ed]; rewrite Ed in Hx; cbn in Hx; lia. }
  split. { apply (rw_cells_agree asegs mm m' _ _ SAVED); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add tc_saved] in Hx. split; lia. }
  split. { exists h0, h1, h2. apply (rw_cells_agree asegs mm m' _ _ HDR); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; lia. }
  split. { exists tmp. split; [| exact TL]. apply (u8arr_agree mm m' _ _ TA); [| exact WM']. apply AG. intros x Hx. rewrite TL in Hx. cbn in Hx. split; lia. }
  split. { apply (rw_cells_agree asegs mm m' _ _ SH); [| exact WM']. apply AG. intros x Hx. rewrite SZ in Hx. cbn in Hx. split; lia. }
  split. { exists nb. split; [| exact NL]. apply (u8arr_agree mm m' _ _ NA); [| exact WM']. apply AG. intros x Hx. rewrite NL in Hx. cbn in Hx. split; lia. }
  split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST'].
Qed.

Lemma base_after_call : forall m0 mb mm m' shc d k, BASE m0 mb -> TINV J shc mb mm ->
  ART RT Σ1 m' -> rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) spq d k mm m' ->
  ((NB <= d /\ d + k <= NB + 40) \/ (d = spq + 15 /\ k = 17)) ->
  BASE m0 m'.
Proof using AF OK EF EL ES INF NBF LOR.
  intros m0 mb mm m' shc d k B TI ART' PR HD. pose proof B as (ART1 & _ & _).
  pose proof (base_pres m0 mb mm B ltac:(destruct TI as (_ & _ & _ & _ & _ & _ & _ & MU & _); exact MU)) as PRES.
  pose proof (base_nbsh m0 mb mm B ltac:(destruct TI as (_ & _ & _ & _ & _ & _ & _ & MU & _); exact MU)) as SHN.
  pose proof inFN1 as IN2. ti_envX OK.
  assert (ELi : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL; auto).
  split; [exact ART'|]. split.
  - eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply (PR a).
    + rewrite EF. eapply aclient_mono; [exact Ha| exact ELi| intros x Hx; right; exact Hx| lia].
    + cbn [outside] in Ho. destruct HD as [[D1 D2]|[-> ->]]; [lia|].
      destruct (aclient_split_c RT AF Σ1 mb q (bv_unsigned a) ART1) as [H|H]; [| lia| rewrite ES in H; lia].
      rewrite EF. eapply aclient_mono; [exact Ha| exact ELi| intros x Hx; right; exact Hx| lia].
  - apply (bytes_at_agree asegs mm m' _ _ SHN). intros a Ha. rewrite repeat_length in Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    apply (PR a).
    + right; right; right; right. exists fN, kN. split; [exact IN2|].
      pose proof (Z.div_le_mono fN NB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (NB + 48) (fN + fs_size kN) 8 ltac:(lia) ltac:(lia)).
      unfold shad, SHB. Z.div_mod_to_equations. lia.
    + destruct HD as [[D1 D2]|[-> ->]]; lia.
Qed.

Section Fin.
Variable K : config -> Prop.
Variable m0 : mem.

Hypothesis HK : forall (Σ' : rts RT) (e : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (nb : list byte),
  frm0 fc' -> ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo q ->
  rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(NB, NB + 40)] m0 m' ->
  NB < e <= NB + 27 -> rw_cells asegs m' NB [CB 40 nb] ->
  aevt RT PMc Σ' K (MS (mkR (ti_ra J) (Z_to_bv 64 q) (ti_gp J) (Z_to_bv 64 TPV_A) t0' t1' t2' (ti_s0 J) (ti_s1 J) (Z_to_bv 64 e) a1' a2' a3' a4' a5' a6' a7'
                        (ti_s2 J) (ti_s3 J) (ti_s4 J) (ti_s5 J) (ti_s6 J) (ti_s7 J) (ti_s8 J) (ti_s9 J) (ti_s10 J) (ti_s11 J) t3' t4' t5' t6')
                   F' (ret_pc (ti_ra J)) fc' None m' (seg_rom asegs)).
Hypothesis EC : rt_credit RT Σ1 = rt_credit RT Σ - 1.

Lemma tc_finA : forall mb, BASE m0 mb -> tc_rel_k J mb (fun ms => aevt RT PMc Σ1 K ms).
Proof using AF MST OK EF EL ES INF NBF LOR HK EC.
  intros mb B. pose proof B as (ARTb & _ & _). unfold tc_rel_k. intros until mm. intros TI FRM HE.
  pose proof inFN1 as IN2. pose proof OK as OK'. destruct OK' as [Cd Clo Croom Cqtop _ Cnblo Cnbhi _ Cflo Cfhi _ _ _ _ _ _ _ _ _].
  assert (ELi : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL; auto).
  apply (tc_rel1 J OK mb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TI). intros mm1 TI1.
  pose proof (base_art m0 mb mm1 sh_f5 B TI1) as ART1.
  destruct (af_frame_release RT AF Σ1 mm1 (ti_f J) 1%nat (rt_frames RT Σ) ART1 EF) as (Σ2 & fl & FLAG & NAC & FL0 & FL1 & LAST & REL).
  rewrite fs1 in LAST. replace (ti_f J + 128 - 8) with (ti_f J + 120) in LAST by lia. rewrite ES in FL1.
  eapply (tc_rel2 J OK mb _ e fl); [exact TI1| exact LAST| exact FLAG| exact FL0| clear - FL1 LOR; lia| |].
  { destruct (Z_lt_dec fl NB) as [D|D]; [left; lia|]. destruct (Z_le_dec (NB + 40) fl) as [D'|D']; [right; lia|].
    exfalso. apply NAC. right; right; right; left. exists fN, kN. split; [exact IN2| lia]. }
  intros xt0' xa1' mm2 nb MU2 WM2 MI2 ST2 FLAG2 NBC2.
  destruct (REL mm2 MU2 WM2 FLAG2) as (ART2 & EFR2 & EL2 & ES2 & EC2 & EA2 & EM2).
  apply (aevt_switch RT PMc Σ1 Σ2 _ _ EA2 EM2).
  apply (HK Σ2 e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xfc mm2 nb FRM ART2 MI2 ST2);
    [rewrite EL2, EL; reflexivity| exact EFR2| rewrite ES2, ES; reflexivity| rewrite EC2, EC; lia| | exact HE| exact NBC2].
  eapply pres_fp_trans; [exact (base_pres m0 mb mm1 B ltac:(destruct TI1 as (_ & _ & _ & _ & _ & _ & _ & MU & _); exact MU))|].
  intros a Ha _. apply MU2. cbn [outside]. split; [| exact I].
  destruct (aclient_split_c RT AF Σ1 mb q (bv_unsigned a) ARTb) as [H|H].
  - rewrite EF. eapply aclient_mono; [exact Ha| exact ELi| intros x Hx; right; exact Hx| lia].
  - clear - H FL1 LOR Croom. lia.
  - intros [Hin1 Hin2]. apply NAC. replace fl with (bv_unsigned a) by (clear - Hin1 Hin2; lia).
    destruct Ha as [S|[S|[S|[S|S]]]].
    + exfalso. rewrite ES in H. unfold STACK_WIN in *. lia.
    + right; left. exact S.
    + right; right; left. destruct S as (p & n & Hp & Hr). exists p, n. split; [apply ELi; exact Hp| exact Hr].
    + right; right; right; left. destruct S as (f' & k' & Hf & Hr). exists f', k'. split; [rewrite EF; right; exact Hf| exact Hr].
    + right; right; right; right. destruct S as (f' & k' & Hf & Hr). exists f', k'. split; [rewrite EF; right; exact Hf| exact Hr].
Qed.
End Fin.
End TCK.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
     Pj_defsA Pj_rtkA Pj_tocharsA_defs Pj_fmtB_defs Pj_fmtB_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma u8arr_after_dstB : forall (m m' : mem) A (bs0 : list byte) d (bs : list byte),
  u8arr bsegs m A bs0 -> length bs0 = 40%nat -> A <= d -> d + Z.of_nat (length bs) <= A + 40 ->
  agree_on (fun x => A <= x < A + 40 /\ ~ (d <= x < d + Z.of_nat (length bs))) m m' -> wmono bsegs m m' ->
  bytes_at bsegs m' d bs ->
  exists bs', u8arr bsegs m' A bs' /\ length bs' = 40%nat.
Proof.
  intros m m' A bs0 d bs UA L0 HA HD AG WM BY.
  destruct (u8arr_range_split bsegs m A bs0 (Z.to_nat (d - A)) (Z.to_nat (d - A) + length bs) UA ltac:(lia) ltac:(lia))
    as (b1 & mid & b3 & L1 & L2 & L3 & U1 & MID & U3).
  assert (U1' : u8arr bsegs m' A b1).
  { apply (u8arr_agree m m' A b1 U1); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. rewrite L1 in Hx. lia. }
  assert (U3' : u8arr bsegs m' (A + Z.of_nat (Z.to_nat (d - A) + length bs)) b3).
  { apply (u8arr_agree m m' _ b3 U3); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. rewrite L3, L0 in Hx. lia. }
  assert (MID' : rw_cells bsegs m' (A + Z.of_nat (length b1)) [CB (length bs) bs]).
  { rewrite L1. replace (A + Z.of_nat (Z.to_nat (d - A))) with d by lia. apply rw_cells_CB_intro; [exact BY|].
    destruct MID as [_ W2]. cbn [cells_size csize Nat.add] in W2. rewrite Nat.add_0_r in W2.
    replace (A + Z.of_nat (Z.to_nat (d - A))) with d in W2 by lia.
    replace (Z.to_nat (d - A) + length bs - Z.to_nat (d - A))%nat with (length bs) in W2 by lia.
    exact (wr_at_transport bsegs m m' d _ W2 WM). }
  destruct (u8arr_range_join bsegs m' A b1 (length bs) bs b3 U1' MID') as (bs' & LB & UB).
  { rewrite L1. replace (A + Z.of_nat (Z.to_nat (d - A)) + Z.of_nat (length bs)) with (A + Z.of_nat (Z.to_nat (d - A) + length bs)) by lia. exact U3'. }
  exists bs'. split; [exact UB|]. rewrite LB, L1, L3, L0. lia.
Qed.

Lemma wr_at_subB : forall (m : mem) A n a k, wr_at bsegs m A n -> A <= a -> a + k <= A + n -> 0 <= k -> wr_at bsegs m a k.
Proof.
  intros m A n a k (H0 & H1 & H) Ha Hk K0. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + i) with (A + (a - A + i)) by lia. apply H. lia.
Qed.

Section FMT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Section Calls.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Variables (Σ : rts RT) (J : fmI) (fN : Z) (kN : nat) (K : config -> Prop) (fc : bv 32) (m0 : mem).
Hypothesis OK : fm_ok J.
Notation p := (fi_p J). Notation NB := (fi_NB J). Notation sg := (fi_sg J). Notation n := (fi_n J). Notation e := (fi_e J). Notation lo := (fi_lo J).
Hypothesis INF : In (fN, kN) (rt_frames RT Σ).
Hypothesis NBF : fN <= fi_NB J /\ fi_NB J + 40 <= fN + fs_size kN - 8.
Hypothesis NB8 : fi_NB J mod 8 = 0.
Hypothesis P16 : fi_p J mod 16 = 0.
Hypothesis NBSN : fi_NB J + 40 <= shad (fi_NB J) \/ shad (fi_NB J) + 5 <= fi_NB J.
Hypothesis LOR : rt_sp0 RT Σ - STACK_WIN <= fi_lo J.

Hypothesis HK : forall (e' : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (nb' : list byte),
  ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo p ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) p [(NB, NB + 40)] m0 m' ->
  NB + sg < e' <= NB + sg + 26 -> u8arr bsegs m' NB nb' -> length nb' = 40%nat ->
  aevt RT PMc Σ K (MS (mkR (fi_ra J) (Z_to_bv 64 p) (fi_gp J) (Z_to_bv 64 TPV_A) t0' t1' t2' (fi_s0 J) (fi_s1 J) (Z_to_bv 64 e') a1' a2' a3' a4' a5' a6' a7'
                      (fi_s2 J) (fi_s3 J) (fi_s4 J) (fi_s5 J) (fi_s6 J) (fi_s7 J) (fi_s8 J) (fi_s9 J) (fi_s10 J) (fi_s11 J) t3' t4' t5' t6')
                   F' (ret_pc (fi_ra J)) fc None m' (seg_rom bsegs)).

Notation Q := (fun ms : machine_state => aevt RT PMc Σ K ms).
Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition BASE (mb : mem) : Prop :=
  ART RT Σ mb /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) p [(NB, NB + 40)] m0 mb /\ bytes_at bsegs mb (shad NB) (repeat z8 5).

Lemma fpW : fp_ok RT Σ (p - 80) (fm_W J).
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  fi_env OK. unfold fp_ok, fm_W.
  apply Forall_cons; [cbn [fst snd]; left; ul|].
  apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]; right; right; left. exists fN, kN. split; [exact INF| lia].
Qed.

Lemma base_art : forall mb mm, BASE mb -> FINV J mb mm -> ART RT Σ mm.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm (ART1 & _ & _) TI. fi_open TI. fi_env OK.
  apply (art_of_munch RT AF Σ mb mm (p - 80) (fm_W J) ART1); [ul| exact fpW| exact MU| exact WM].
Qed.

Lemma W_out : forall (mb : mem) a, ART RT Σ mb -> aclient (rt_live RT Σ) (rt_frames RT Σ) p a -> ~ (NB <= a < NB + 40) -> outside (fm_W J) a.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb a ART1 Ha Hnb. fi_env OK. destruct (aclient_split_c RT AF Σ mb p a ART1 Ha); unfold fm_W; cbn [outside]; repeat split; ul.
Qed.

Lemma base_pres : forall mb mm, BASE mb -> munch (fm_W J) mb mm -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) p [(NB, NB + 40)] m0 mm.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm (ART1 & PRES & _) MU. eapply pres_fp_trans; [exact PRES|]. apply (pres_fp_of_munch _ _ _ _ _ _ _ MU).
  intros a Ha Ho. apply (W_out mb a ART1 Ha). cbn [outside] in Ho. lia.
Qed.

Lemma base_nbsh : forall mb mm, BASE mb -> munch (fm_W J) mb mm -> bytes_at bsegs mm (shad NB) (repeat z8 5).
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm (ART1 & _ & SHN) MU. fi_env OK. pose proof (af_sp0_win RT AF Σ mb ART1) as SPW.
  assert (SH1 : (NB + 40) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia| ul]).
  apply (bytes_at_agree bsegs mb mm _ _ SHN). apply (agree_of_munch _ _ _ _ MU).
  intros x Hx. rewrite repeat_length in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. unfold fm_W. cbn [outside]. unfold shad, SHB in *.
  pose proof (Z.div_le_mono NB (NB + 40) 8 ltac:(lia) ltac:(lia)). repeat split; ul.
Qed.

Lemma base_shpn : forall mb, BASE mb -> nb_shzB J mb.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb B m' MU WM. pose proof (base_nbsh mb m' B MU) as SHN. fi_env OK.
  change 40 with (8 * Z.of_nat 5). apply shz_run0; [exact NB8| lia| exact SHN].
Qed.

Lemma fm_call_ok : forall mb mm, FINV J mb mm -> call_ok RT Σ mm (Z_to_bv 64 (p + -80)) lo.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm TI. fi_open TI. fi_env OK. unfold call_ok. rewrite unsigned_lit by ul.
  split; [exact ST|]. split; [ul|]. split; [ul|]. split; [ul|].
  replace (p + -80) with (p + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact P16.
Qed.

Lemma nb_checked_dst : forall mb mm d k, BASE mb -> FINV J mb mm -> NB <= d -> d + k <= NB + 40 -> 0 <= k ->
  checked_dst RT Σ mm (Z_to_bv 64 (p + -80)) d k.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm d k B TI D1 D2 K0.
  pose proof (base_nbsh mb mm B ltac:(destruct TI as (_ & _ & _ & _ & MU & _); exact MU)) as SHN.
  fi_open TI. fi_env OK. unfold checked_dst. rewrite unsigned_lit by ul. split; [| split].
  - intros _. split.
    + apply (acc_sub bsegs mm NB 40 d k); [| lia| lia]. change 40 with (8 * Z.of_nat 5). apply (acc_zero_run bsegs mm NB 5 NB8 ltac:(lia) SHN).
    + right; left. exists fN, kN. split; [exact INF| lia].
  - intros i Hi. right; right; right; left. exists fN, kN. split; [exact INF| lia].
  - destruct NA as [_ W]. rewrite NL in W. apply (wr_at_subB mm NB 40 d k W); lia.
Qed.

Lemma nb_checked_src : forall mb mm s k, BASE mb -> FINV J mb mm -> NB <= s -> s + k <= NB + 40 ->
  checked_src RT Σ mm (Z_to_bv 64 (p + -80)) lo s k.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm s k B TI S1 S2.
  pose proof (base_nbsh mb mm B ltac:(destruct TI as (_ & _ & _ & _ & MU & _); exact MU)) as SHN.
  fi_open TI. fi_env OK. unfold checked_src. rewrite unsigned_lit by ul. split; [| left; lia].
  intros _. split.
  - apply (acc_sub bsegs mm NB 40 s k); [| lia| lia]. change 40 with (8 * Z.of_nat 5). apply (acc_zero_run bsegs mm NB 5 NB8 ltac:(lia) SHN).
  - right; left. exists fN, kN. split; [exact INF| lia].
Qed.

Lemma nb_bytes : forall (mm : mem) nb (k j : nat), u8arr bsegs mm NB nb -> length nb = 40%nat -> (k + j <= 40)%nat ->
  bytes_at bsegs mm (NB + Z.of_nat k) (firstn j (skipn k nb)) /\ length (firstn j (skipn k nb)) = j.
Proof.
  intros mm nb k j UA L Hk. split; [apply (bytes_at_sub bsegs mm NB nb k j (proj1 UA)); rewrite L; exact Hk|].
  rewrite length_firstn, length_skipn, L. lia.
Qed.

Lemma tmp17_facts : forall mb mm, BASE mb -> FINV J mb mm ->
  exists t17, bytes_at bsegs mm (p + -80 + 7) t17 /\ length t17 = 17%nat /\ wr_at bsegs mm (p + -80 + 7) 17
    /\ checked_src RT Σ mm (Z_to_bv 64 (p + -80)) lo (p + -80 + 7) 17
    /\ checked_dst RT Σ mm (Z_to_bv 64 (p + -80)) (p + -80 + 7) 17.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm B TI. pose proof (base_art mb mm B TI) as ART1. fi_open TI. fi_env OK.
  destruct (proj1 (num_rw_cells_app bsegs mm _ [_] _) LOC) as [_ L2]. cbn [cells_size csize Nat.add] in L2.
  pose proof (rw_cells_bytes_at bsegs mm _ _ L2) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  assert (LT : length t17 = 17%nat) by (destruct L2 as [[Hwf _] _]; cbn in Hwf; tauto).
  destruct L2 as [_ W2]. cbn [cells_size csize Nat.add] in W2.
  assert (ACC : acc bsegs mm (p + -80 + Z.of_nat 7) 17) by (apply (af_acc_stack RT AF Σ mm _ 17 ART1); ul).
  replace (p + -80 + Z.of_nat 7) with (p + -80 + 7) in BY, W2, ACC by lia.
  exists t17. split; [exact BY|]. split; [exact LT|]. split; [exact W2|]. split.
  - unfold checked_src. rewrite unsigned_lit by ul. split; [| right; lia]. intros _. split; [exact ACC|]. right; right; left. ul.
  - unfold checked_dst. rewrite unsigned_lit by ul. split; [| split; [| exact W2]].
    + intros _. split; [exact ACC|]. right; right; left. ul.
    + intros i Hi. left. ul.
Qed.

Lemma finv_after_nb : forall mb mm m' d k (bs : list byte), FINV J mb mm ->
  rt_after RT Σ (p + -80) lo mm m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (p + -80) d k mm m' ->
  bytes_at bsegs m' d bs -> Z.of_nat (length bs) = k -> NB <= d -> d + k <= NB + 40 ->
  FINV J m' m'.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm m' d k bs TI (ART' & MI' & WM' & ST') PR BY LK D1 D2. subst k. fi_open TI. fi_env OK.
  assert (AG : forall P : Z -> Prop,
    (forall x, P x -> ((p + -80 <= x < p) \/ (NB <= x < NB + 40)) /\ ~ (d <= x < d + Z.of_nat (length bs))) -> agree_on P mm m').
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply (PR a); [| exact H2].
    destruct H1 as [H1|H1]; [left; ul| right; right; right; left; exists fN, kN; split; [exact INF| lia]]. }
  split. { exists j7, t17. apply (rw_cells_agree bsegs mm m' _ _ LOC); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; lia. }
  split. { apply (rw_cells_agree bsegs mm m' _ _ SAVED); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add fm_saved] in Hx. split; lia. }
  split. { apply (u8arr_after_dstB mm m' _ nb d bs NA NL D1 D2); [| exact WM'| exact BY]. apply AG. intros x [Hx1 Hx2]. split; [lia| exact Hx2]. }
  split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST'].
Qed.

Lemma finv_after_tmp : forall mb mm m' (bs : list byte), FINV J mb mm ->
  rt_after RT Σ (p + -80) lo mm m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (p + -80) (p + -80 + 7) 17 mm m' ->
  bytes_at bsegs m' (p + -80 + 7) bs -> length bs = 17%nat ->
  FINV J m' m'.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm m' bs TI (ART' & MI' & WM' & ST') PR BY LB. fi_open TI. fi_env OK.
  assert (AG : forall P : Z -> Prop,
    (forall x, P x -> ((p + -80 <= x < p) \/ (NB <= x < NB + 40)) /\ ~ (p + -80 + 7 <= x < p + -80 + 7 + 17)) -> agree_on P mm m').
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply (PR a); [| exact H2].
    destruct H1 as [H1|H1]; [left; ul| right; right; right; left; exists fN, kN; split; [exact INF| lia]]. }
  split.
  { destruct (proj1 (num_rw_cells_app bsegs mm _ [_] _) LOC) as [L1 L2]. cbn [cells_size csize Nat.add] in L2.
    exists j7, bs. apply (proj2 (num_rw_cells_app bsegs m' _ [_] _)). split.
    { apply (rw_cells_agree bsegs mm m' _ _ L1); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; lia. }
    cbn [cells_size csize Nat.add]. rewrite <- LB. apply rw_cells_CB_intro; [replace (p + -80 + Z.of_nat 7) with (p + -80 + 7) by lia; exact BY|].
    rewrite LB. destruct L2 as [_ W2]. cbn [cells_size csize Nat.add] in W2. exact (wr_at_transport bsegs mm m' _ _ W2 WM'). }
  split. { apply (rw_cells_agree bsegs mm m' _ _ SAVED); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add fm_saved] in Hx. split; lia. }
  split. { exists nb. split; [| exact NL]. apply (u8arr_agree mm m' _ _ NA); [| exact WM']. apply AG. intros x Hx. rewrite NL in Hx. cbn in Hx. split; lia. }
  split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST'].
Qed.

Lemma base_after_call : forall mb mm m' d k, BASE mb -> FINV J mb mm -> ART RT Σ m' ->
  rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (p + -80) d k mm m' ->
  ((NB <= d /\ d + k <= NB + 40) \/ (d = p + -80 + 7 /\ k = 17)) -> BASE m'.
Proof using AF OK INF NBF NB8 P16 NBSN LOR.
  intros mb mm m' d k B TI ART' PR HD. pose proof B as (ART1 & _ & _).
  pose proof (base_pres mb mm B ltac:(destruct TI as (_ & _ & _ & _ & MU & _); exact MU)) as PRES.
  pose proof (base_nbsh mb mm B ltac:(destruct TI as (_ & _ & _ & _ & MU & _); exact MU)) as SHN.
  fi_env OK. split; [exact ART'|]. split.
  - eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply (PR a).
    + eapply aclient_mono; [exact Ha| auto| auto| lia].
    + cbn [outside] in Ho. destruct HD as [[D1 D2]|[-> ->]]; [lia|].
      destruct (aclient_split_c RT AF Σ mb p (bv_unsigned a) ART1 Ha); ul.
  - apply (bytes_at_agree bsegs mm m' _ _ SHN). intros a Ha. rewrite repeat_length in Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    apply (PR a).
    + right; right; right; right. exists fN, kN. split; [exact INF|].
      pose proof (Z.div_le_mono fN NB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (NB + 48) (fN + fs_size kN) 8 ltac:(lia) ltac:(lia)).
      unfold shad, SHB in *. Z.div_mod_to_equations. lia.
    + pose proof (af_sp0_win RT AF Σ mb ART1) as SPW.
      assert (SH1 : (NB + 40) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia| ul]).
      unfold shad, SHB in *. destruct HD as [[D1 D2]|[-> ->]]; ul.
Qed.

Lemma fm_exitB : forall mb, BASE mb -> fm_exit_k J fc mb Q.
Proof using AF OK INF NBF NB8 P16 NBSN LOR HK.
  intros mb B. unfold fm_exit_k. intros until mm. intros TI HE.
  pose proof (base_art mb mm B TI) as ART1. pose proof (base_pres mb mm B ltac:(destruct TI as (_ & _ & _ & _ & MU & _); exact MU)) as PRES.
  pose proof TI as TI0. fi_open TI.
  apply (fm_epi J OK fc mb Q e' xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 xF mm TI0).
  intros nb' ST' NA' NL'. apply (HK e' _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF mm nb' ART1 MI ST' PRES HE NA' NL').
Qed.

Notation BSHPN mb B := (base_shpn mb B).

Lemma fm_expB : forall mb, BASE mb -> fm_exp_k J fc mb Q.
Proof using AF OK INF NBF NB8 P16 NBSN LOR HK.
  intros mb B. unfold fm_exp_k. intros until mm. intros TI HD.
  eapply (fm_exp J OK fc mb Q (fm_exitB mb B) (BSHPN mb B)); [exact TI| exact HD].
Qed.

Lemma fm_lay1B : forall mb, BASE mb -> fm_l1_k J fc mb Q.
Proof using AF RC FDO MST OK INF NBF NB8 P16 NBSN LOR HK.
  intros mb B. unfold fm_l1_k. intros until mm. intros TI P15. fi_env OK.
  pose proof (base_art mb mm B TI) as ART1. pose proof (fm_call_ok mb mm TI) as COK.
  pose proof (nb_checked_dst mb mm (NB + sg + n) 16 B TI ltac:(lia) ltac:(lia) ltac:(lia)) as CD.
  pose proof TI as TI0. fi_open TI.
  apply evt_done.
  eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF fc mm (NB + sg + n) 16 (Z_to_bv 8 48) lo);
    [reflexivity| reflexivity| reflexivity| ul| lia| exact CD| exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : FINV J m3 m3).
  { eapply (finv_after_nb mb mm m3 (NB + sg + n) 16); [exact TI0| exact RA3| exact PR3| exact BY3| rewrite repeat_length; reflexivity| lia| lia]. }
  assert (B3 : BASE m3) by (eapply (base_after_call mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| left; lia]).
  rewrite (ret_pc_even 0xc06a8) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (fm_l1b J OK fc m3 Q (fm_exitB m3 B3) (BSHPN m3 B3)); [exact TI3| exact P15].
Qed.

Lemma fm_lay2B : forall mb, BASE mb -> fm_l2_k J fc mb Q.
Proof using AF RC FDO MST OK INF NBF NB8 P16 NBSN LOR HK.
  intros mb B. unfold fm_l2_k. intros until mm. intros TI P15. fi_env OK.
  pose proof (base_art mb mm B TI) as ART1. pose proof (fm_call_ok mb mm TI) as COK.
  pose proof (nb_checked_dst mb mm (NB + sg + (n + e) + 1) 16 B TI ltac:(lia) ltac:(lia) ltac:(lia)) as CD.
  pose proof (nb_checked_src mb mm (NB + sg + (n + e)) 16 B TI ltac:(lia) ltac:(lia)) as CS.
  pose proof TI as TI0. fi_open TI.
  destruct (nb_bytes mm nb (Z.to_nat (sg + (n + e))) 16 NA NL ltac:(lia)) as [SRC LS].
  replace (NB + Z.of_nat (Z.to_nat (sg + (n + e)))) with (NB + sg + (n + e)) in SRC by lia.
  set (bs := firstn 16 (skipn (Z.to_nat (sg + (n + e))) nb)) in *. clearbody bs.
  apply evt_done.
  eapply (aevt_memmoveP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF fc mm (NB + sg + (n + e) + 1) (NB + sg + (n + e)) bs lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : FINV J m3 m3).
  { eapply (finv_after_nb mb mm m3 (NB + sg + (n + e) + 1) 16); [exact TI0| exact RA3| exact PR3| exact BY3| rewrite LS; reflexivity| lia| lia]. }
  assert (B3 : BASE m3) by (eapply (base_after_call mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| left; lia]).
  rewrite (ret_pc_even 0xc0768) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (fm_l2b J OK fc m3 Q (fm_exitB m3 B3) (BSHPN m3 B3)); [exact TI3| exact P15].
Qed.

Lemma fm_lay4B : forall mb, BASE mb -> fm_l4_k J fc mb Q.
Proof using AF RC FDO MST OK INF NBF NB8 P16 NBSN LOR HK.
  intros mb B. unfold fm_l4_k. intros until mm. intros TI HN2. fi_env OK.
  pose proof (base_art mb mm B TI) as ART1. pose proof (fm_call_ok mb mm TI) as COK.
  pose proof (nb_checked_dst mb mm (NB + sg + 2) 16 B TI ltac:(lia) ltac:(lia) ltac:(lia)) as CD.
  pose proof (nb_checked_src mb mm (NB + sg + 1) 16 B TI ltac:(lia) ltac:(lia)) as CS.
  pose proof TI as TI0. fi_open TI.
  destruct (nb_bytes mm nb (Z.to_nat (sg + 1)) 16 NA NL ltac:(lia)) as [SRC LS].
  replace (NB + Z.of_nat (Z.to_nat (sg + 1))) with (NB + sg + 1) in SRC by lia.
  set (bs := firstn 16 (skipn (Z.to_nat (sg + 1)) nb)) in *. clearbody bs.
  apply evt_done.
  eapply (aevt_memmoveP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF fc mm (NB + sg + 2) (NB + sg + 1) bs lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : FINV J m3 m3).
  { eapply (finv_after_nb mb mm m3 (NB + sg + 2) 16); [exact TI0| exact RA3| exact PR3| exact BY3| rewrite LS; reflexivity| lia| lia]. }
  assert (B3 : BASE m3) by (eapply (base_after_call mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| left; lia]).
  rewrite (ret_pc_even 0xc08ac) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (fm_l4b J OK fc m3 Q (fm_expB m3 B3) (BSHPN m3 B3)); [exact TI3| exact HN2].
Qed.

Lemma fm_lay3cB : forall mb, BASE mb -> fm_l3c_k J fc mb Q.
Proof using AF RC FDO MST OK INF NBF NB8 P16 NBSN LOR HK.
  intros mb B. unfold fm_l3c_k. intros until mm. intros TI P3. fi_env OK.
  pose proof (base_art mb mm B TI) as ART1. pose proof (fm_call_ok mb mm TI) as COK.
  pose proof (nb_checked_dst mb mm (NB + sg + 2 - (n + e)) 17 B TI ltac:(lia) ltac:(lia) ltac:(lia)) as CD.
  destruct (tmp17_facts mb mm B TI) as (t17 & SRC & LS & _ & CS & _).
  pose proof TI as TI0. fi_open TI.
  apply evt_done.
  eapply (aevt_memcpyP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF fc mm (NB + sg + 2 - (n + e)) (p + -80 + 7) t17 lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| rewrite LS; left; lia
    | exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : FINV J m3 m3).
  { eapply (finv_after_nb mb mm m3 (NB + sg + 2 - (n + e)) 17); [exact TI0| exact RA3| exact PR3| exact BY3| rewrite LS; reflexivity| lia| lia]. }
  assert (B3 : BASE m3) by (eapply (base_after_call mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| left; lia]).
  rewrite (ret_pc_even 0xc0840) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (fm_l3c J OK fc m3 Q (fm_exitB m3 B3) (BSHPN m3 B3)); [exact TI3| exact P3].
Qed.

Lemma fm_lay3B : forall mb, BASE mb -> fm_l3_k J fc mb Q.
Proof using AF RC FDO MST OK INF NBF NB8 P16 NBSN LOR HK.
  intros mb B. unfold fm_l3_k. intros until mm. intros TI P3. fi_env OK.
  pose proof (base_art mb mm B TI) as ART1. pose proof (fm_call_ok mb mm TI) as COK.
  pose proof (nb_checked_src mb mm (NB + sg) 17 B TI ltac:(lia) ltac:(lia)) as CS.
  destruct (tmp17_facts mb mm B TI) as (t17 & _ & _ & _ & _ & CD).
  pose proof TI as TI0. fi_open TI.
  destruct (nb_bytes mm nb (Z.to_nat sg) 17 NA NL ltac:(lia)) as [SRC LS].
  replace (NB + Z.of_nat (Z.to_nat sg)) with (NB + sg) in SRC by lia.
  set (bs := firstn 17 (skipn (Z.to_nat sg) nb)) in *. clearbody bs.
  apply evt_done.
  eapply (aevt_memcpyP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF fc mm (p + -80 + 7) (NB + sg) bs lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| rewrite LS; right; lia
    | exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : FINV J m3 m3) by (eapply (finv_after_tmp mb mm m3 bs); [exact TI0| exact RA3| exact PR3| exact BY3| exact LS]).
  assert (B3 : BASE m3) by (eapply (base_after_call mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| right; split; reflexivity]).
  rewrite (ret_pc_even 0xc07a4) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (fm_l3b J OK fc m3 Q (BSHPN m3 B3) (fm_lay3cB m3 B3)); [exact TI3| exact P3].
Qed.
End Calls.

Local Ltac ul0 := unfold FMT_STACK_B in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem fmt_okB : fdfs_only PMc -> mat_stable PMc -> fmt_cpsB RT PMc.
Proof using AF RC.
  intros FDO MST. unfold fmt_cpsB.
  intros Σ K p lo NB sg n e fN kN ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nb
         _ _ INF FLE FHI NB8 NA NL NBSH HSG HN HE ART0 MI ST LOR ROOM PT P16 HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SPR. pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  pose proof (af_frames_range RT AF Σ m fN kN ART0 INF) as (FN0 & FN1 & _ & _).
  pose proof (af_frames_align RT AF Σ m fN kN ART0 INF) as (_ & FNLO).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fN kN ART0 INF) fN kN INF) as FNSH.
  assert (FSZ : 0 <= fs_size kN) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  unfold SF_EMIN, SF_EMAX in HE.
  set (J := mkFI p NB sg n e lo ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  assert (OK : fm_ok J) by (subst J; constructor; cbn; ul0).
  assert (NBSN : NB + 40 <= shad NB \/ shad NB + 5 <= NB).
  { pose proof (Z.div_le_mono fN NB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (NB + 48) (fN + fs_size kN) 8 ltac:(lia) ltac:(lia)).
    unfold shad, SHB in *. destruct FNSH as [HS|HS]; [left| right]; Z.div_mod_to_equations; lia. }
  assert (B0 : BASE Σ J m m). { split; [exact ART0|]. split; [intros a _ _; reflexivity| exact NBSH]. }
  apply (aevt_evt RT AF PMc MST).
  assert (NBF : fN <= fi_NB J /\ fi_NB J + 40 <= fN + fs_size kN - 8) by (subst J; cbn; lia).
  eapply (fm_entry J OK fc m (fun ms => aevt RT PMc Σ K ms)
            (fm_exitB Σ J fN kN K fc m OK INF NBF NB8 P16 NBSN LOR HK m B0)
            (fm_expB Σ J fN kN K fc m OK INF NBF NB8 P16 NBSN LOR HK m B0)
            (fm_lay1B FDO MST Σ J fN kN K fc m OK INF NBF NB8 P16 NBSN LOR HK m B0)
            (fm_lay2B FDO MST Σ J fN kN K fc m OK INF NBF NB8 P16 NBSN LOR HK m B0)
            (fm_lay3B FDO MST Σ J fN kN K fc m OK INF NBF NB8 P16 NBSN LOR HK m B0)
            (fm_lay4B FDO MST Σ J fN kN K fc m OK INF NBF NB8 P16 NBSN LOR HK m B0)
            (base_shpn Σ J fN kN m OK INF NBF NB8 P16 NBSN LOR m B0));
    [exact NA| exact NL| exact MI| exact ST| exact (af_client_consts RT AF Σ m ART0)].
Qed.
End FMT.

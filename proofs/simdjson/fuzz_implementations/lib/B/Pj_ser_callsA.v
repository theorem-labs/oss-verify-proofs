(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_trefA Pj_ser_defsA Pj_ser_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma stk_wr_at : forall (m : mem) lo hi a n, stk bsegs m lo hi -> lo <= a -> a + n <= hi -> wr_at bsegs m a n.
Proof.
  intros m lo hi a n (S0 & S1 & S) Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (S (a + i) ltac:(lia))).
Qed.

Section Calls.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Notation aevt := (aevt RT PMc).
Local Ltac dlia := Z.div_mod_to_equations; lia.

Lemma buf_factsA : forall E D I Σc st m sp, pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st m ->
  sa_buf st + sa_cap st <= pa_lo E /\ 0 < sa_buf st
  /\ (forall n, 0 <= n <= sa_cap st -> rng_class RT Σc (sa_buf st) n)
  /\ (forall y, sa_buf st <= y < sa_buf st + sa_cap st -> aclient (rt_live RT Σc) (rt_frames RT Σc) sp y)
  /\ (forall y, sa_buf st <= y < sa_buf st + sa_cap st ->
        ~ (si_f I <= y < si_f I + 512) /\ ~ (SHFA I <= y < SHFA I + 64) /\ ~ (pa_SB E + 64 <= y < pa_SB E + 88)
        /\ ~ (shad (pa_SB E) <= y < shad (pa_SB E) + 11)).
Proof using AF.
  intros E D I Σc st m sp OK CX (ART0 & LV & FR & SP & _ & _ & PU & _).
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & B32 & F64 & FS & B1 & B2 & _ & _ & FL & LO & _).
  pose proof (env_div8 E D I OK CX) as (_ & EF & Ef & ESB & EFS & Efs & FS64 & _).
  pose proof (c_F4 E D I CX) as IN4. pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1. pose proof (c_F_shF E D I CX) as FSH3.
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR; right; exact IN4).
  assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σc)) by (rewrite FR; left; reflexivity).
  destruct R3 as [(BL & HP)|(EB & EC & HP)].
  - assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σc)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INF3) as (_ & _ & _ & F3CH). specialize (F3CH _ _ INB). rewrite fs3 in F3CH.
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INF4) as (_ & _ & _ & F4CH). specialize (F4CH _ _ INB).
    pose proof (proj1 (af_fshadow_apart RT AF Σc m _ _ ART0 INF3) _ _ INB) as F3SH. rewrite fs3 in F3SH. unfold shad, SHB in F3SH.
    replace ((si_f I + 512) / 8) with (si_f I / 8 + 64) in F3SH by (clear - Ef; dlia).
    pose proof (proj1 (af_fshadow_apart RT AF Σc m _ _ ART0 INF4) _ _ INB) as F4SH. unfold shad, SHB in F4SH. rewrite EFS in F4SH.
    split; [exact BL|]. split; [exact R0|].
    split. { intros n Hn. left. exists (sa_buf st), (sa_cap st). split; [exact INB| clear - Hn; lia]. }
    split. { intros y Hy. right; right; left. exists (sa_buf st), (sa_cap st). split; [exact INB| clear - Hy; lia]. }
    intros y Hy. split; [clear - Hy F3CH; lia|]. split; [clear - Hy F3SH; lia|]. split; [clear - Hy F4CH B1 B2; lia|].
    unfold shad, SHB. clear - Hy F4SH ESB EF Efs B1 B2. lia.
  - rewrite EB, EC. unfold SEGTOP_A in FS. split; [clear - B2 FL; lia|]. split; [clear - FS B1; lia|].
    split. { intros n Hn. right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - B1 B2 Hn; lia]. }
    split. { intros y Hy. right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - B1 B2 Hy; lia]. }
    intros y Hy. split; [clear - Hy FF B1 B2; lia|]. split; [clear - Hy FSH1 B1 B2; lia|]. split; [clear - Hy; lia|].
    unfold shad, SHB. clear - Hy FSH3 ESB EF Efs B1 B2. lia.
Qed.

Lemma SERMA_after_call : forall E D I w xs shp isobj Σ Σ' st st' m m' W,
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w xs shp isobj Σ st m ->
  (forall x, outside (serWA E I st) x -> outside W x) ->
  (forall x, si_b I <= x < si_q I \/ si_f I <= x < si_f I + 24 \/ si_f I + 304 <= x < si_f I + 320 \/ SHFA I <= x < SHFA I + 64 -> outside W x) ->
  rt_pres_fp (pa_L E) (rt_frames RT Σ) (si_b I) W m m' ->
  ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) (si_b I) ->
  rt_live RT Σ' = sbchunkA st' ++ pa_L E -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
  sb_pureA E st' -> bytes_at bsegs m' (shad (pa_SB E)) (repeat z8 11) ->
  rw_cells bsegs m' (pa_SB E + 64) [C8 (wz (sa_buf st')); C8 (wz (sa_size st')); C8 (wz (sa_cap st'))] -> 0 <= sa_size st' <= sa_cap st' ->
  stk bsegs m' (sa_buf st') (sa_buf st' + sa_cap st') -> stk bsegs m' (pa_SB E) (pa_SB E + 64) -> stk bsegs m' (si_f I + 24) (si_f I + 304) ->
  SERMA RT E I w xs shp isobj Σ' st' m'.
Proof using AF.
  intros until W. intros OK CX HSM SUB SPARE PRES ART' MI' ST' LV' FR' SP' PU' SBSH' SV' SZ' BUFS' INLS' F3S'.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0).
  destruct HC as (FRc & GAP & FS & (h0 & h1 & h2 & FH) & F3S & IS & ISL & SHF & SHL & SHT & _).
  pose proof (env_div8 E D I OK CX) as (ED & EF & Ef & ESB & EFS & Efs & FS64 & _).
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & S0 & SL & S16 & D8 & B32 & F64 & FSg & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT. unfold USTACK_TOP in QT. pose proof (c_F4 E D I CX) as IN4.
  pose proof (ok_tape E OK) as (_ & TN & _ & _ & INT). pose proof (ok_sbuf E OK) as (_ & SN & _ & _ & INS).
  assert (E512 : (si_f I + 512) / 8 = si_f I / 8 + 64) by (clear - Ef; dlia).
  assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σ)) by (rewrite FR; left; reflexivity).
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σ)) by (rewrite FR; right; exact IN4).
  pose proof (agree_of_pres_fp _ _ _ _ _ _ (fun x => aclient (pa_L E) (rt_frames RT Σ) (si_b I) x /\ outside W x) PRES ltac:(intros x Hx; exact Hx)) as AG.

  assert (XST : forall A n, si_b I <= A -> A + n <= si_q I -> agree_on (fun x => A <= x < A + n) m m').
  { intros A n HA Hn. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
    split; [left; clear - Hx HA Hn QT; unfold USTACK_TOP; lia| apply SPARE; left; clear - Hx HA Hn; lia]. }
  assert (XF3 : forall A n, (si_f I <= A /\ A + n <= si_f I + 24) \/ (si_f I + 304 <= A /\ A + n <= si_f I + 320) -> agree_on (fun x => A <= x < A + n) m m').
  { intros A n HA. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta. split.
    - right; right; right; left. exists (si_f I), 3%nat. split; [exact INF3| rewrite fs3; clear - HA Hx; lia].
    - apply SPARE. destruct HA as [HA|HA]; [right; left| right; right; left]; clear - HA Hx; lia. }
  assert (XSH : agree_on (fun x => SHFA I <= x < SHFA I + 64) m m').
  { eapply agree_sub; [exact AG|]. intros x Hx. cbv beta. split; [| apply SPARE; right; right; right; clear - Hx; lia].
    right; right; right; right. exists (si_f I), 3%nat. split; [exact INF3| unfold shad, SHB; rewrite fs3, E512; clear - Hx; lia]. }
  split.
  -
    unfold SREFA. split; [exact ART'|]. split; [exact LV'|]. split; [rewrite FR'; exact FR|]. split; [rewrite SP'; exact SP|].
    split. { eapply DOCREPA_agree; [exact DR|]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
             split; [| apply SUB; eapply docrep_outside; eassumption].
             destruct Hx as [Hx|[Hx|[Hx|Hx]]].
             - right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx D1 D2; lia].
             - right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hx |- *. rewrite EFS. clear - Hx ED EF Efs D1 D2. lia.
             - right; right; left. exists (pa_TAPE E), (pa_NT E). split; [exact INT| clear - Hx TN; lia].
             - right; right; left. exists (pa_SBUF E), (pa_NS E). split; [exact INS| clear - Hx SN; lia]. }
    split; [exact SBSH'|]. split; [exact PU'|].
    intros a CA OUT. rewrite <- (PRES0 a CA OUT). apply PRES.
    + eapply aclient_mono; [exact CA| intros e He; exact He| intros e He; rewrite FR; right; exact He| unfold si_b; clear - DD; lia].
    + apply SUB. eapply serWA_below; eassumption.
  -
    unfold SCURA. split.
    { eapply rw_cells_agree_nw; [exact FRc|]. rewrite ser_frameA_size. apply XST; unfold si_b; clear - DD; lia. }
    split. { pose proof GAP as (G0 & G1 & _). destruct DD as [DD|DD].
             - unfold si_b in *. rewrite DD in *. replace (si_q I - 416 - 0 + 312) with (si_q I - 104) by (clear; lia). apply stk_nil. clear - G0 G1; lia.
             - eapply stk_agree_nw; [exact GAP|]. unfold si_b in *. rewrite DD in *.
               eapply agree_sub; [apply (XST (si_q I - 416 - 16 + 312) 16); clear; lia|]. intros x Hx. cbv beta in Hx |- *. clear - Hx. lia. }
    split. { eapply rw_cells_agree_nw; [exact FS|]. rewrite ser_savedA_size. apply XST; unfold si_b; clear - DD; lia. }
    split. { exists h0, h1, h2. eapply rw_cells_agree_nw; [exact FH|]. apply XF3. left. cbn. clear; lia. }
    split; [exact F3S'|].
    split. { eapply u8arr_agree_nw; [exact IS|]. rewrite ISL. apply XF3. right. cbn. clear; lia. }
    split; [exact ISL|].
    split. { eapply u8arr_agree_nw; [exact SHF|]. rewrite SHL. eapply agree_sub; [exact XSH|]. intros x Hx. cbv beta in Hx |- *. clear - Hx. lia. }
    split; [exact SHL|].
    split. { eapply stk_agree_nw; [exact SHT|]. eapply agree_sub; [exact XSH|]. intros x Hx. cbv beta in Hx |- *. clear - Hx. lia. }
    split; [exact SV'|]. split; [exact SZ'|]. split; [exact BUFS'|]. split; [exact INLS'|]. split; [exact MI'| exact ST'].
Qed.

Lemma ser_req_okA : forall E D I w xs shp isobj Σc st m need, pjenvA_ok E -> sctxA E D I ->
  SERMA RT E I w xs shp isobj Σc st m -> sa_cap st < need -> need <= PJ_OUTMAX (pa_len E) ->
  2 * sa_cap st <= Z.max (2 * sa_cap st) need <= PJ_CAPMAX (pa_len E).
Proof.
  intros until need. intros OK CX HSM H1 H2. eapply grow_request_okA; [exact OK| eapply SBINVA_of_SERMA; [exact OK| exact CX| exact HSM]| exact H1| exact H2].
Qed.
Lemma ser_req_ok2A : forall E D I w xs shp isobj Σc st m, pjenvA_ok E -> sctxA E D I ->
  SERMA RT E I w xs shp isobj Σc st m -> sa_cap st < PJ_OUTMAX (pa_len E) ->
  2 * sa_cap st <= 2 * sa_cap st <= PJ_CAPMAX (pa_len E).
Proof.
  intros until m. intros OK CX HSM H1. pose proof (SBINVA_cap_pos E m st (SBINVA_of_SERMA RT E D I _ _ _ _ Σc st m OK CX HSM)).
  unfold PJ_CAPMAX. lia.
Qed.

Lemma ser_growA : forall E D I w xs shp isobj Σ st m (K : config -> Prop) (z X rpc : Z) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w xs shp isobj Σ st m ->
  2 * sa_cap st <= z <= PJ_CAPMAX (pa_len E) -> CREDA RT E I Σ X st -> 0 <= X ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (Σ' : rts RT) (NEW : Z) (m' : mem) (F' : bvmap 5 word) (yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     SERMA RT E I w xs shp isobj Σ' (sb_grownA st NEW z) m' -> CREDA RT E I Σ' X (sb_grownA st NEW z) ->
     aevt Σ' K (SSTA I rpc (wz rpc) yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6 F' fc m')) ->
  aevt Σ K (SSTA I PJ_GROW_A (wz rpc) xt0 xt1 xt2 (wz (pa_SB E)) (wz z) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
Proof using AF GROW.
  intros until xt6. intros OK CX HSM ZB CR X0 RP0 RP2 HK.
  pose proof (SBINVA_of_SERMA RT E D I _ _ _ _ Σ st m OK CX HSM) as INV. pose proof (pa_live_of_SERMA RT E D I _ _ _ _ Σ st m CX HSM) as PL.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0).
  pose proof HC as (_ & _ & _ & _ & F3S & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & ST).
  pose proof (c_lo E D I CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT.
  pose proof (c_b32 E D I CX) as B32. pose proof (c_L E D I CX) as LL. pose proof (c_R E D I CX) as R0.
  pose proof (SBINVA_k E m st OK INV) as KB. pose proof (SBINVA_cap_pos E m st INV) as C64.
  pose proof (pj_psi_grow (pa_len E) st 0 z KB C64 ZB) as PSI.
  assert (PSI' : 0 <= pj_psi (pa_len E) (sb_grownA st 0 z)) by (unfold pj_psi, sb_grownA; cbn [sa_cap sa_k]; rewrite PJ_GROWC_val; lia).
  assert (PSIE : forall NEW, pj_psi (pa_len E) (sb_grownA st NEW z) = pj_psi (pa_len E) (sb_grownA st 0 z)) by (intros; reflexivity).
  unfold CREDA in CR.
  eapply (GROW Σ K E st z (si_b I) (wz rpc) (si_gp I) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I)) xa2 xa3 xa4 xa5 xa6 xa7
            xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m OK PL INV ZB ART0 MI ST).
  - unfold PJ_GROW_STACK_A, RT_STACK, si_b. clear - LOQ DD. lia.
  - unfold USTACK_TOP in QT |- *. unfold si_b. clear - QT DD. lia.
  - clear - B32. dlia.
  - rewrite LV, length_app. unfold sbchunkA. clear - LL. destruct (sa_heap st); cbn [length]; lia.
  - clear - PSI PSI' CR R0 X0. lia.
  - intros Σ' NEW t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' ART' MI' ST' INV' PL' FR' SP' CR' PRES'.
    rewrite (ret_pc_even rpc RP0 RP2). apply (HK Σ' NEW m' F').
    + pose proof INV' as (SV' & SZ' & (bs' & BUF') & (ji' & INL') & SBSH' & PK' & PH').
      pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & B1 & B2 & _ & _ & FL & _).
      pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1.
      eapply (SERMA_after_call E D I w xs shp isobj Σ Σ' st (sb_grownA st NEW z) m m' [(pa_SB E + 64, pa_SB E + 88)]);
        [exact OK| exact CX| exact HSM| | | exact PRES'| exact ART'| exact MI'| exact ST'| exact (proj1 PL')| exact FR'| exact SP'
        | exact (conj PK' PH')| exact SBSH'| exact SV'| exact SZ'| | | ].
      * intros x Hx. unfold serWA in Hx. cbn [outside] in Hx |- *. split; [lia| exact Logic.I].
      * intros x Hx. cbn [outside]. split; [| exact Logic.I]. unfold si_b in *. clear - Hx FF FSH1 B1 B2 FL LOQ DD. lia.
      * pose proof (stk_of_rw_cells bsegs _ _ _ BUF') as S. cbn [cells_size csize Nat.add] in S. unfold sb_grownA in *. cbn [sa_buf sa_cap] in *.
        rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
      * pose proof (stk_of_rw_cells bsegs _ _ _ INL') as S. cbn [cells_size csize Nat.add] in S. exact S.
      * eapply stk_agree_nw; [exact F3S|]. eapply agree_of_pres_fp; [exact PRES'|]. intros x Hx. cbv beta. split.
        -- right; right; right; left. exists (si_f I), 3%nat. split; [rewrite FR; left; reflexivity| rewrite fs3; lia].
        -- cbn [outside]. split; [| exact Logic.I]. clear - Hx FF B1 B2. lia.
    + unfold CREDA. rewrite PSIE. clear - CR CR' PSI R0 X0. lia.
Qed.

Lemma ser_copyA : forall E D I w xs shp isobj Σ st m (K : config -> Prop) (Src n rpc : Z) (bs : list byte)
    (F : bvmap 5 word) (fc : bv 32) (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w xs shp isobj Σ st m ->
  bytes_at bsegs m Src bs -> Z.of_nat (length bs) = n -> 0 <= n -> sa_size st + n <= sa_cap st ->
  (0 < n -> acc bsegs m Src n /\ rng_class RT Σ Src n) -> 0 < Src -> Src + n <= pa_lo E ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (F' : bvmap 5 word) (yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     SERMA RT E I w xs shp isobj Σ st m' -> bytes_at bsegs m' (sa_buf st + sa_size st) bs ->
     aevt Σ K (SSTA I rpc (wz rpc) yt0 yt1 yt2 (wz (Src + n)) (wz (sa_buf st + sa_size st + n)) ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                     yt3 yt4 yt5 yt6 F' fc m')) ->
  aevt Σ K (SSTA I PJ_COPY_S_A (wz rpc) xt0 xt1 xt2 (wz Src) (wz (Src + n)) (wz (sa_buf st + sa_size st)) xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST.
  intros until xt6. intros OK CX HSM BY LEN N0 ROOM SRCOK S0 SLO RP0 RP2 HK.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0).
  pose proof HC as (_ & _ & _ & _ & F3S & _ & _ & _ & _ & _ & SV & SZ & BUFS & INLS & MI & ST).
  pose proof (buf_factsA E D I Σ st m (si_b I) OK CX HR) as (BL & B0 & RCB & CLB & APB).
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (c_lo E D I CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT.
  unfold USTACK_TOP in QT.
  pose proof (c_b32 E D I CX) as B32. pose proof (c_sp0 E D I CX) as (W1 & W2). pose proof (ok_lo E OK) as LOW.
  pose proof (acc_buf_mu RT AF E D I OK CX Σ st m m HR (munch_refl _ m) (wmono_refl bsegs m)) as ACCB.
  subst n.
  eapply (copy_okA RT AF RC PMc FDO MST PJ_COPY_S_A (or_intror eq_refl) Σ K (si_b I) (pa_lo E) Src (sa_buf st + sa_size st) (Z.of_nat (length bs)) bs
            (wz rpc) (si_gp I) (wz TPV_A) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I)) xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m
            BY eq_refl); [| exact S0| exact SLO| | | exact SRCOK| | | | exact ART0| exact MI| exact ST| rewrite SP; exact W1| | | |].
  - clear - ROOM SZ R1. lia.
  - clear - B0 SZ. lia.
  - clear - BL SZ ROOM. lia.
  - intros _. split; [apply (acc_sub bsegs m _ _ _ _ ACCB); clear - SZ ROOM; lia|].
    destruct R3 as [(BL' & HP)|(EB & EC & HP)].
    + left. exists (sa_buf st), (sa_cap st). split; [rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity| clear - SZ ROOM; lia].
    + right; left. exists (pa_F E), (pa_kF E). pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
      split; [rewrite FR; right; exact (c_F4 E D I CX)| clear - EB EC SZ ROOM B1 B2; lia].
  - intros sp i Hi. destruct (buf_factsA E D I Σ st m sp OK CX HR) as (_ & _ & _ & CL & _). apply CL. clear - Hi SZ ROOM. lia.
  - apply (stk_wr_at m _ _ _ _ BUFS); clear - SZ ROOM; lia.
  - unfold PJ_COPY_STACK_A, RT_STACK, si_b. clear - LOQ DD. lia.
  - unfold si_b, USTACK_TOP. clear - QT DD. lia.
  - clear - B32. unfold si_b in *. dlia.
  - intros t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' ART' MI' ST' WM' BY' PRES'.
    rewrite (ret_pc_even rpc RP0 RP2). apply HK; [| exact BY'].
    assert (AGB : forall P : Z -> Prop,
              (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (si_b I) x /\ ~ (sa_buf st + sa_size st <= x < sa_buf st + sa_size st + Z.of_nat (length bs))) ->
              agree_on P m m').
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (PRES' a H1 H2). }
    assert (PRESW : rt_pres_fp (pa_L E) (rt_frames RT Σ) (si_b I) [(sa_buf st + sa_size st, sa_buf st + sa_size st + Z.of_nat (length bs))] m m').
    { intros a Ha Ho. apply PRES'; [| cbn [outside] in Ho; exact (proj1 Ho)].
      eapply aclient_mono; [exact Ha| rewrite LV; intros e He; apply in_or_app; right; exact He| intros e He; exact He| clear; lia]. }
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & B1 & B2 & _ & _ & FL & _).
    pose proof (env_div8 E D I OK CX) as (_ & EF & Ef & ESB & EFS & Efs & _).
    pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1. pose proof (c_F4 E D I CX) as IN4.
    assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σ)) by (rewrite FR; right; exact IN4).
    assert (BUFS' : stk bsegs m' (sa_buf st) (sa_buf st + sa_cap st)).
    { destruct (stk_split bsegs m _ (sa_buf st + sa_size st) _ BUFS ltac:(clear - SZ ROOM; lia)) as [SLO' SREST].
      destruct (stk_split bsegs m _ (sa_buf st + sa_size st + Z.of_nat (length bs)) _ SREST ltac:(clear - SZ ROOM; lia)) as [SMID SHI].
      eapply stk_merge; [eapply stk_agree_nw; [exact SLO'| apply AGB; intros x Hx; split; [apply CLB; clear - Hx SZ ROOM; lia| clear - Hx; lia]]| | clear - SZ ROOM; lia].
      eapply stk_merge; [apply (stk_of_bytes_wmono m m' _ bs BY' SMID WM')| | clear - SZ ROOM; lia].
      eapply stk_agree_nw; [exact SHI| apply AGB; intros x Hx; split; [apply CLB; clear - Hx SZ ROOM; lia| clear - Hx; lia]]. }
    eapply (SERMA_after_call E D I w xs shp isobj Σ Σ st st m m' [(sa_buf st + sa_size st, sa_buf st + sa_size st + Z.of_nat (length bs))]);
      [exact OK| exact CX| exact HSM| | | exact PRESW| exact ART'| exact MI'| exact ST'| exact LV| reflexivity| reflexivity| exact PU| | | exact SZ| exact BUFS'| | ].
    + intros x Hx. unfold serWA in Hx. cbn [outside] in Hx |- *. split; [clear - Hx SZ ROOM; lia| exact Logic.I].
    + intros x Hx. cbn [outside]. split; [| exact Logic.I]. intros C.
      destruct (APB x ltac:(clear - C SZ ROOM; lia)) as (A1 & A2 & _). unfold si_b in Hx. clear - Hx C A1 A2 BL LOQ DD SZ ROOM. lia.
    + eapply bytes_at_agree; [exact SBSH|]. apply AGB. intros x Hx. rewrite repeat_length in Hx. split.
      * right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hx |- *. rewrite EFS. clear - Hx ESB EF Efs B1 B2. lia.
      * intros C. destruct (APB x ltac:(clear - C SZ ROOM; lia)) as (_ & _ & _ & A4). exact (A4 Hx).
    + eapply rw_cells_agree_nw; [exact SV|]. apply AGB. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
      * right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
      * intros C. destruct (APB x ltac:(clear - C SZ ROOM; lia)) as (_ & _ & A3 & _). apply A3. clear - Hx. lia.
    + destruct R3 as [(BL' & HP)|(EB & EC & HP)].
      * eapply stk_agree_nw; [exact INLS|]. apply AGB. intros x Hx. split.
        -- right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
        -- intros C. assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σ)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
           pose proof (af_frames_range RT AF Σ m _ _ ART0 INF4) as (_ & _ & _ & F4CH). specialize (F4CH _ _ INB). clear - Hx C F4CH B1 B2 SZ ROOM. lia.
      * rewrite <- EB, <- EC. exact BUFS'.
    + eapply stk_agree_nw; [exact F3S|]. apply AGB. intros x Hx. split.
      * right; right; right; left. exists (si_f I), 3%nat. split; [rewrite FR; left; reflexivity| rewrite fs3; clear - Hx; lia].
      * intros C. destruct (APB x ltac:(clear - C SZ ROOM; lia)) as (A1 & _). apply A1. clear - Hx. lia.
Qed.

Lemma ser_icopyA : forall (entry : Z) E D I w xs shp isobj Σ st m (K : config -> Prop) (Src n rpc : Z) (bs : list byte)
    (F : bvmap 5 word) (fc : bv 32) (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  entry = e_asan_memcpy \/ entry = e_asan_memmove ->
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w xs shp isobj Σ st m ->
  bytes_at bsegs m Src bs -> Z.of_nat (length bs) = n -> 1 <= n -> sa_size st + n <= sa_cap st ->
  acc bsegs m Src n -> rng_class RT Σ Src n -> 0 <= Src -> Src + n <= pa_lo E ->
  (entry = e_asan_memcpy -> sa_buf st + sa_size st + n <= Src \/ Src + n <= sa_buf st + sa_size st) ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (F' : bvmap 5 word) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     SERMA RT E I w xs shp isobj Σ st m' -> bytes_at bsegs m' (sa_buf st + sa_size st) bs ->
     aevt Σ K (SSTA I rpc (wz rpc) yt0 yt1 yt2 (wz (sa_buf st + sa_size st)) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                     yt3 yt4 yt5 yt6 F' fc m')) ->
  aevt Σ K (SSTA I entry (wz rpc) xt0 xt1 xt2 (wz (sa_buf st + sa_size st)) (wz Src) (wz n) xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST.
  intros until xt6. intros HE OK CX HSM BY LEN N1 ROOM AC RG S0 SLO SEP RP0 RP2 HK.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0).
  pose proof HC as (_ & _ & _ & _ & F3S & _ & _ & _ & _ & _ & SV & SZ & BUFS & INLS & MI & ST).
  pose proof (buf_factsA E D I Σ st m (si_b I) OK CX HR) as (BL & B0 & RCB & CLB & APB).
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (c_lo E D I CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT.
  unfold USTACK_TOP in QT.
  pose proof (c_b32 E D I CX) as B32. pose proof (c_sp0 E D I CX) as (W1 & W2). pose proof (ok_lo E OK) as LOW.
  pose proof (acc_buf_mu RT AF E D I OK CX Σ st m m HR (munch_refl _ m) (wmono_refl bsegs m)) as ACCB.
  assert (EU : bv_unsigned (wz (si_b I)) = si_b I) by (apply unsigned_lit; unfold si_b; clear - LOQ DD QT LOW; lia).
  subst n.
  assert (CS : checked_src RT Σ m (wz (si_b I)) (pa_lo E) Src (Z.of_nat (length bs))).
  { unfold checked_src. rewrite EU. split; [intros _; split; [exact AC| exact RG]| left; exact SLO]. }
  assert (CD : checked_dst RT Σ m (wz (si_b I)) (sa_buf st + sa_size st) (Z.of_nat (length bs))).
  { unfold checked_dst. rewrite EU. split; [| split].
    - intros _. split; [apply (acc_sub bsegs m _ _ _ _ ACCB); clear - SZ ROOM; lia|].
      destruct R3 as [(BL' & HP)|(EB & EC & HP)].
      + left. exists (sa_buf st), (sa_cap st). split; [rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity| clear - SZ ROOM; lia].
      + right; left. exists (pa_F E), (pa_kF E). pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
        split; [rewrite FR; right; exact (c_F4 E D I CX)| clear - EB EC SZ ROOM B1 B2; lia].
    - intros i Hi. apply CLB. clear - Hi SZ ROOM. lia.
    - apply (stk_wr_at m _ _ _ _ BUFS); clear - SZ ROOM; lia. }
  assert (COK : call_ok RT Σ m (wz (si_b I)) (pa_lo E)).
  { unfold call_ok. rewrite EU, SP. split; [exact ST|]. split; [exact W1|]. split; [unfold si_b, RT_STACK; clear - LOQ DD; lia|].
    split; [unfold si_b, USTACK_TOP; clear - QT DD; lia| clear - B32; dlia]. }
  assert (POST : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem),
    rt_after RT Σ (bv_unsigned (wz (si_b I))) (pa_lo E) m m' ->
    rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (wz (si_b I))) (sa_buf st + sa_size st) (Z.of_nat (length bs)) m m' ->
    bytes_at bsegs m' (sa_buf st + sa_size st) bs ->
    aevt Σ K (MS (mkR (wz rpc) (wz (si_b I)) (si_gp I) (wz TPV_A) t0' t1' t2' (wz (si_q I)) (wz (si_b I)) (wz (sa_buf st + sa_size st)) a1' a2' a3' a4' a5' a6' a7'
                      xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6') F' (ret_pc (wz rpc)) fc None m' (seg_rom bsegs))).
  { intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (ART' & MI' & WM' & ST') PRES' BY'. rewrite EU in ST', PRES'.
    rewrite (ret_pc_even rpc RP0 RP2). apply HK; [| exact BY'].
    assert (PRESW : rt_pres_fp (pa_L E) (rt_frames RT Σ) (si_b I) [(sa_buf st + sa_size st, sa_buf st + sa_size st + Z.of_nat (length bs))] m m').
    { intros a Ha Ho. apply PRES'; [| cbn [outside] in Ho; exact (proj1 Ho)].
      eapply aclient_mono; [exact Ha| rewrite LV; intros e He; apply in_or_app; right; exact He| intros e He; exact He| clear; lia]. }
    assert (AGB : forall P : Z -> Prop,
              (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (si_b I) x /\ ~ (sa_buf st + sa_size st <= x < sa_buf st + sa_size st + Z.of_nat (length bs))) ->
              agree_on P m m').
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (PRES' a H1 H2). }
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & B1 & B2 & _ & _ & FL & _).
    pose proof (env_div8 E D I OK CX) as (_ & EF & Ef & ESB & EFS & Efs & _).
    pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1. pose proof (c_F4 E D I CX) as IN4.
    assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σ)) by (rewrite FR; right; exact IN4).
    assert (BUFS' : stk bsegs m' (sa_buf st) (sa_buf st + sa_cap st)).
    { destruct (stk_split bsegs m _ (sa_buf st + sa_size st) _ BUFS ltac:(clear - SZ ROOM; lia)) as [SLO' SREST].
      destruct (stk_split bsegs m _ (sa_buf st + sa_size st + Z.of_nat (length bs)) _ SREST ltac:(clear - SZ ROOM; lia)) as [SMID SHI].
      eapply stk_merge; [eapply stk_agree_nw; [exact SLO'| apply AGB; intros x Hx; split; [apply CLB; clear - Hx SZ ROOM; lia| clear - Hx; lia]]| | clear - SZ ROOM; lia].
      eapply stk_merge; [apply (stk_of_bytes_wmono m m' _ bs BY' SMID WM')| | clear - SZ ROOM; lia].
      eapply stk_agree_nw; [exact SHI| apply AGB; intros x Hx; split; [apply CLB; clear - Hx SZ ROOM; lia| clear - Hx; lia]]. }
    eapply (SERMA_after_call E D I w xs shp isobj Σ Σ st st m m' [(sa_buf st + sa_size st, sa_buf st + sa_size st + Z.of_nat (length bs))]);
      [exact OK| exact CX| exact HSM| | | exact PRESW| exact ART'| exact MI'| exact ST'| exact LV| reflexivity| reflexivity| exact PU| | | exact SZ| exact BUFS'| | ].
    - intros x Hx. unfold serWA in Hx. cbn [outside] in Hx |- *. split; [clear - Hx SZ ROOM; lia| exact Logic.I].
    - intros x Hx. cbn [outside]. split; [| exact Logic.I]. intros C.
      destruct (APB x ltac:(clear - C SZ ROOM; lia)) as (A1 & A2 & _). unfold si_b in Hx. clear - Hx C A1 A2 BL LOQ DD SZ ROOM. lia.
    - eapply bytes_at_agree; [exact SBSH|]. apply AGB. intros x Hx. rewrite repeat_length in Hx. split.
      + right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hx |- *. rewrite EFS. clear - Hx ESB EF Efs B1 B2. lia.
      + intros C. destruct (APB x ltac:(clear - C SZ ROOM; lia)) as (_ & _ & _ & A4). exact (A4 Hx).
    - eapply rw_cells_agree_nw; [exact SV|]. apply AGB. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
      + right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
      + intros C. destruct (APB x ltac:(clear - C SZ ROOM; lia)) as (_ & _ & A3 & _). apply A3. clear - Hx. lia.
    - destruct R3 as [(BL' & HP)|(EB & EC & HP)].
      + eapply stk_agree_nw; [exact INLS|]. apply AGB. intros x Hx. split.
        * right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
        * intros C. assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σ)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
          pose proof (af_frames_range RT AF Σ m _ _ ART0 INF4) as (_ & _ & _ & F4CH). specialize (F4CH _ _ INB). clear - Hx C F4CH B1 B2 SZ ROOM. lia.
      + rewrite <- EB, <- EC. exact BUFS'.
    - eapply stk_agree_nw; [exact F3S|]. apply AGB. intros x Hx. split.
      + right; right; right; left. exists (si_f I), 3%nat. split; [rewrite FR; left; reflexivity| rewrite fs3; clear - Hx; lia].
      + intros C. destruct (APB x ltac:(clear - C SZ ROOM; lia)) as (A1 & _). apply A1. clear - Hx. lia. }
  destruct HE as [-> | ->].
  - eapply (aevt_memcpyP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (sa_buf st + sa_size st) Src bs (pa_lo E)
              eq_refl eq_refl eq_refl); [| | | exact BY| exact CS| exact CD| | exact ART0| exact MI| exact COK| exact POST].
    + clear - B0 BL SZ ROOM LOQ QT LOW. lia.
    + clear - S0 SLO LOQ QT LOW. lia.
    + clear - ROOM SZ R1. lia.
    + destruct (SEP eq_refl); [left| right]; assumption.
  - eapply (aevt_memmoveP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (sa_buf st + sa_size st) Src bs (pa_lo E)
              eq_refl eq_refl eq_refl); [| | | exact BY| exact CS| exact CD| exact ART0| exact MI| exact COK| exact POST].
    + clear - B0 BL SZ ROOM LOQ QT LOW. lia.
    + clear - S0 SLO LOQ QT LOW. lia.
    + clear - ROOM SZ R1. lia.
Qed.

Lemma sbuf_srcA : forall E D I w xs shp isobj Σc st m o n, pjenvA_ok E -> sctxA E D I ->
  SERMA RT E I w xs shp isobj Σc st m -> 0 <= o -> 0 <= n -> o + n <= pa_sn E ->
  exists src, bytes_at bsegs m (pa_SBUF E + o) src /\ Z.of_nat (length src) = n
    /\ acc bsegs m (pa_SBUF E + o) n /\ rng_class RT Σc (pa_SBUF E + o) n /\ 0 <= pa_SBUF E + o /\ pa_SBUF E + o + n <= pa_lo E.
Proof using AF.
  intros until n. intros OK CX [HR _] Ho Hn Hb. pose proof HR as (ART0 & LV & _ & _ & (_ & _ & _ & SBUFB) & _).
  pose proof (ok_sbuf E OK) as (_ & SN & S0 & SL & INS).
  assert (INS' : In (pa_SBUF E, pa_NS E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INS).
  exists (firstn (Z.to_nat n) (skipn (Z.to_nat o) (map (Z_to_bv 8) (pa_sbs E)))). split; [| split; [| split; [| split; [| lia]]]].
  - pose proof SBUFB as (B0 & B1 & BB). rewrite length_map in B1.
    split; [lia|]. split; [rewrite length_firstn, length_skipn, length_map; lia|].
    intros i Hi. rewrite length_firstn, length_skipn, length_map in Hi.
    replace (pa_SBUF E + o + Z.of_nat i) with (pa_SBUF E + Z.of_nat (Z.to_nat o + i)) by lia.
    rewrite BB by (rewrite length_map; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec i (Z.to_nat n)) as [L|L]; [| lia]. rewrite nth_error_skipn. reflexivity.
  - rewrite length_firstn, length_skipn, length_map. lia.
  - apply (acc_sub bsegs m (pa_SBUF E) (pa_NS E)); [exact (proj2 (af_acc_live RT AF Σc m _ _ ART0 INS'))| lia| lia].
  - left. exists (pa_SBUF E), (pa_NS E). split; [exact INS'| lia].
Qed.

Lemma f3_rngA : forall E D I w xs shp isobj Σc st m Src n, pjenvA_ok E -> sctxA E D I ->
  SERMA RT E I w xs shp isobj Σc st m -> si_f I + 24 <= Src -> 0 <= n -> Src + n <= si_f I + 304 ->
  rng_class RT Σc Src n /\ 0 <= Src /\ Src + n <= pa_lo E /\ exists src, bytes_at bsegs m Src src /\ Z.of_nat (length src) = n.
Proof.
  intros until n. intros OK CX [HR HC] H1 Hn H2. pose proof HR as (_ & _ & FR & _). pose proof HC as (_ & _ & _ & _ & F3S & _).
  pose proof (c_f E D I CX) as (F0 & _ & _ & FLO).
  split. { right; left. exists (si_f I), 3%nat. split; [rewrite FR; left; reflexivity| rewrite fs3; lia]. }
  split; [lia|]. split; [lia|].
  destruct (stk_split bsegs m _ Src _ F3S ltac:(lia)) as [_ S1].
  destruct (stk_split bsegs m _ (Src + n) _ S1 ltac:(lia)) as [S2 _].
  destruct (stk_bytes bsegs m _ _ S2 ltac:(lia)) as (bs & HL & HB).
  exists bs. split; [exact HB|]. rewrite HL. lia.
Qed.

Lemma ser_call_contA : forall (k : bool) (d' : nat) E D I w xs shp isobj Σ st m (K : config -> Prop) (i e n c c' X rpc : Z)
    (F : bvmap 5 word) (fc : bv 32) (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  cont_cpsA RT PMc k d' -> (d' + 16 <= D)%nat ->
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w xs shp isobj Σ st m -> frm0 fc ->
  ty (pa_T E) i = (if k then t_obj else t_arr) -> tnext (pa_T E i) = e + 1 -> ty (pa_T E) e = end_ty k ->
  tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) k d') (i + 1) e n c c' ->
  1 <= i -> e + 1 <= pa_n E -> 0 <= c -> c' <= pa_sn E -> sb_acc1A st i c ->
  CREDA RT E I Σ X st -> 2 * (e - i) <= X ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     frm0 fc' -> SERMA RT E I w xs shp isobj Σ' st' m' -> sb_accA st' (e + 1) c' -> CREDA RT E I Σ' (X - 2 * (e - i)) st' ->
     aevt Σ' K (SSTA I rpc (wz rpc) yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6 F' fc' m')) ->
  aevt Σ K (SSTA I (if k then PJ_APPEND_OBJ_A else PJ_APPEND_ARR_A) (wz rpc) xt0 xt1 xt2 (wz (pa_SB E)) (wz (pa_DOC E)) (wz i) xa3 xa4 xa5 xa6 xa7
                xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
Proof using AF FDO MST.
  intros until xt6. intros CONT HD OK CX HSM FRM TY TN TE TILES I1 E1 C0 C1 ACC CR X2 RP0 RP2 HK.
  pose proof (SBINVA_of_SERMA RT E D I _ _ _ _ Σ st m OK CX HSM) as INV. pose proof (pa_live_of_SERMA RT E D I _ _ _ _ Σ st m CX HSM) as PL.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0).
  pose proof HC as (_ & _ & _ & _ & F3S & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & ST).
  pose proof (c_lo E D I CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT.
  pose proof (c_b32 E D I CX) as B32. pose proof (c_L E D I CX) as LL. pose proof (c_R E D I CX) as R0.
  pose proof (c_fr3 E D I CX) as FR3. pose proof (c_frl E D I CX) as FRL.
  pose proof (sb_pureA_psi E st OK PU) as PSI0. unfold CREDA in CR.
  eapply (CONT Σ K E st i e n c c' (si_b I) (wz rpc) (si_gp I) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I)) xa3 xa4 xa5 xa6 xa7
            xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m FDO MST OK PL INV DR TY TN TE TILES I1 E1 C0 C1 ACC ART0 MI ST).
  - unfold cont_needA, ser_needA, PJ_TC_STACK_A, RT_STACK, si_b. clear - LOQ DD HD. lia.
  - unfold USTACK_TOP in QT |- *. unfold si_b. clear - QT DD. lia.
  - clear - B32. dlia.
  - exact FRM.
  - rewrite FR, fcount_cons. cbn [Nat.eqb]. clear - FR3 HD. lia.
  - rewrite FR. cbn [length]. clear - FRL HD. lia.
  - exact LL.
  - clear - CR X2 R0; lia.
  - intros Σ' st' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' ART' MI' ST' INV' DR' ACC' PL' FR' SP' CR' PRES'.
    rewrite (ret_pc_even rpc RP0 RP2). apply (HK Σ' st' m' F' fc'); [exact FRM'| | exact ACC'| unfold CREDA; clear - CR CR'; lia].
    pose proof INV' as (SV' & SZ' & (bs' & BUF') & (ji' & INL') & SBSH' & PK' & PH').
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & B1 & B2 & _ & _ & FL & _).
    pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1.
    pose proof (sb_pureA_ranges E st' OK (conj PK' PH')) as (_ & R1' & _).
    eapply (SERMA_after_call E D I w xs shp isobj Σ Σ' st st' m m' [(pa_SB E, pa_SB E + 88)]);
      [exact OK| exact CX| exact HSM| | | exact PRES'| exact ART'| exact MI'| exact ST'| exact (proj1 PL')| exact FR'| exact SP'
      | exact (conj PK' PH')| exact SBSH'| exact SV'| exact SZ'| | | ].
    + intros x Hx. unfold serWA in Hx. cbn [outside] in Hx |- *. split; [lia| exact Logic.I].
    + intros x Hx. cbn [outside]. split; [| exact Logic.I]. unfold si_b in *. clear - Hx FF FSH1 B1 B2 FL LOQ DD. lia.
    + pose proof (stk_of_rw_cells bsegs _ _ _ BUF') as S. cbn [cells_size csize Nat.add] in S. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
    + pose proof (stk_of_rw_cells bsegs _ _ _ INL') as S. cbn [cells_size csize Nat.add] in S. exact S.
    + eapply stk_agree_nw; [exact F3S|]. eapply agree_of_pres_fp; [exact PRES'|]. intros x Hx. cbv beta. split.
      * right; right; right; left. exists (si_f I), 3%nat. split; [rewrite FR; left; reflexivity| rewrite fs3; lia].
      * cbn [outside]. split; [| exact Logic.I]. clear - Hx FF B1 B2. lia.
Qed.

Lemma stackwin_not_client : forall E D I Σc st m a sp, pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st m ->
  aclient (pa_L E) (rt_frames RT Σc) sp a -> pa_lo E <= a < sp -> False.
Proof using AF.
  intros E D I Σc st m a sp OK CX (ART0 & LV & FR & SP & _) CA Ha.
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & _ & _ & _ & _ & FL & LO & _).
  pose proof (c_sp0 E D I CX) as (W1 & W2). unfold STACK_WIN in W1. unfold SEGTOP_A in FS.
  destruct CA as [CA|[CA|[CA|[CA|CA]]]].
  - clear - CA Ha. lia.
  - apply client_static_range in CA. unfold SEGTOP_A in CA. destruct (fs_size_64 (pa_kF E)) as (qF & EF4 & QF1). clear - CA Ha FS FL EF4 QF1. lia.
  - destruct CA as (p & n & INp & Hp).
    assert (INp' : In (p, n) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INp).
    pose proof (af_live_range RT AF Σc m _ _ ART0 INp') as (_ & PR & _). unfold STACK_WIN in PR. clear - Hp PR W1 SP Ha. lia.
  - destruct CA as (g & k & INg' & Hg).
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INg') as (_ & GR & _). unfold STACK_WIN in GR. clear - Hg GR W1 SP Ha. lia.
  - destruct CA as (g & k & INg' & Hg). unfold shad, SHB in Hg.
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INg') as (G0 & GR & _). unfold STACK_WIN in GR.
    pose proof (af_frames_align RT AF Σc m _ _ ART0 INg') as [G64 _].
    destruct (fs_size_64 k) as (qk & EK & QK1). rewrite EK in Hg, GR.
    assert (EGK : (g + 64 * qk) / 8 = g / 8 + 8 * qk) by (clear - G64; dlia). rewrite EGK in Hg.
    pose proof (af_sp0_range RT AF Σc m ART0) as SPR. unfold USTACK_TOP, SEGTOP_A, STACK_WIN in SPR.
    clear - Hg GR SPR LO QK1 G0 G64 Ha W1 SP. dlia.
Qed.

Lemma ser_trefA : forall E D I w xs shp isobj Σc st m idx (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w xs shp isobj Σc st m -> 0 <= idx <= pa_n E ->
  evt bsegs (fun ms => exists (m' : mem) (ya4 : word),
      ms = MS (mkR xra (wz (si_b I)) (si_gp I) (wz TPV_A) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I))
                   (wz (pa_TAPE E + 8 * idx)) (wz 0) (wz (pa_TAPE E)) (wz 1152921504606846976) ya4 xa5 xa6 xa7
                   xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (ret_pc xra) fc None m' (seg_rom bsegs)
      /\ SERMA RT E I w xs shp isobj Σc st m')
    (SSTA I PJ_TREF_A xra xt0 xt1 xt2 (wz (pa_DOC E)) (wz idx) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
Proof using AF.
  intros until xt6. intros OK CX HSM HI.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0). pose proof DR as (DC0 & SHD & _).
  pose proof HC as (FRc & GAP & FS & (h0 & h1 & h2 & FH) & F3S & IS & ISL & SHF & SHL & SHT & SV & SZ & BUFS & INLS & MI & ST).
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & _ & _ & _ & D8 & _ & _ & FS0 & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (env_div8 E D I OK CX) as (ED & EF & Ef & ESB & EFS & Efs & _).
  pose proof (c_lo E D I CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_qtop E D I CX) as QT.
  unfold USTACK_TOP in QT. pose proof (c_sp0 E D I CX) as (W1 & W2). unfold SEGTOP_A in FS0. pose proof (c_f E D I CX) as (F0 & _ & FSG & FLO).
  pose proof (buf_factsA E D I Σc st m (si_b I) OK CX HR) as (BL & _).
  assert (DC1 : rw_cells bsegs m (pa_DOC E) [C8 (wz (pa_TAPE E))])
    by (exact (proj1 (proj1 (rw_cells_app bsegs m (pa_DOC E) [C8 (wz (pa_TAPE E))] [C8 (wz (pa_SBUF E))]) DC0))).
  eapply evt_mono.
  { eapply (tref_walk (pa_DOC E) (pa_TAPE E) idx (si_b I) (pa_lo E) xra (si_gp I) (wz TPV_A) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I))
              xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m ST);
      [unfold si_b; clear - LOQ DD; lia| clear - LO; lia| unfold si_b; clear - QT DD; lia| exact (af_client_consts RT AF Σc m ART0)
      | clear - FS0 D1; lia| clear - D2 FL LOQ QT; lia| exact D8| exact SHD| exact DC1| exact T0| clear - T16; dlia| clear - HI; lia
      | clear - HI TL LOQ QT; lia| left; unfold si_b; clear - D2 FL LOQ DD; lia| exact MI]. }
  cbv beta. intros ms' (m' & a4' & -> & MU & WM & MI' & ST').
  exists m', a4'. split; [reflexivity|].

  assert (AG : forall P : Z -> Prop, (forall x, P x -> ~ (si_b I - 16 <= x < si_b I)) -> agree_on P m m').
  { intros P HP. eapply agree_of_munch; [exact MU|]. intros x Hx. cbn [outside]. split; [exact (HP _ Hx)| exact Logic.I]. }
  assert (ART' : ART RT Σc m').
  { apply (art_client_write RT AF Σc m m' (si_b I - 16) ART0); [rewrite SP; unfold si_b; clear - LOQ DD W1; lia| | exact WM].
    apply AG. intros x Hx C. apply Hx. left. unfold USTACK_TOP, si_b in *. clear - C QT DD. lia. }
  assert (PRESW : rt_pres_fp (pa_L E) (rt_frames RT Σc) (si_b I) [] m m').
  { intros a Ha _. apply MU. cbn [outside]. split; [| exact Logic.I]. intros C.
    eapply (stackwin_not_client E D I Σc st m (bv_unsigned a) (si_b I)); [exact OK| exact CX| exact HR| exact Ha| unfold si_b in *; clear - C LOQ DD; lia]. }
  eapply (SERMA_after_call E D I w xs shp isobj Σc Σc st st m m' []);
    [exact OK| exact CX| exact HSM| intros x _; exact Logic.I| intros x _; exact Logic.I| exact PRESW| exact ART'| exact MI'| exact ST'
    | exact LV| reflexivity| reflexivity| exact PU| | | exact SZ| | | ].
  - eapply bytes_at_agree; [exact SBSH|]. apply AG. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB, si_b in *.
    clear - Hx ESB B1 B2 FL LOQ DD QT LO EF Efs EFS. lia.
  - eapply rw_cells_agree_nw; [exact SV|]. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold si_b in *. clear - Hx B2 FL LOQ DD. lia.
  - eapply stk_agree_nw; [exact BUFS|]. apply AG. intros x Hx. unfold si_b in *. clear - Hx BL LOQ DD. lia.
  - eapply stk_agree_nw; [exact INLS|]. apply AG. intros x Hx. unfold si_b in *. clear - Hx B2 FL LOQ DD. lia.
  - eapply stk_agree_nw; [exact F3S|]. apply AG. intros x Hx. unfold si_b in *. clear - Hx FLO LOQ DD. lia.
Qed.

End Calls.

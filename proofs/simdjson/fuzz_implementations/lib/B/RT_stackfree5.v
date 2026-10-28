(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts RT_release R_fs_ok RT_artfacts RT_stackmalloc R_fsfree5 HandoffImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Lemma ro_cells_C8_inj : forall (m : mem) A (x y : word), ro_cells bsegs m A [C8 x] -> ro_cells bsegs m A [C8 y] -> x = y.
Proof.
  intros m A x y Hx Hy.
  pose proof (ro_cells_read bsegs m A [C8 x] 0 (C8 x) Hx eq_refl) as Rx. pose proof (ro_cells_read bsegs m A [C8 y] 0 (C8 y) Hy eq_refl) as Ry.
  cbn [csize] in Rx, Ry. rewrite Rx in Ry.
  assert (E : cbytes (C8 x) = cbytes (C8 y)) by (congruence). change (le8 x = le8 y) in E.
  rewrite <- (le_bytes_to_word_le8 x), <- (le_bytes_to_word_le8 y), E. reflexivity.
Qed.

Lemma sf_shad_add8 : forall a x, a mod 8 = 0 -> x mod 8 = 0 -> shad (a + x) = shad a + x / 8.
Proof.
  intros a x Ha Hx. unfold shad. apply Z.mod_divide in Ha, Hx; try (clear; lia). destruct Ha as [qa Ea]. destruct Hx as [qx Ex]. subst a x.
  replace (qa * 8 + qx * 8) with ((qa + qx) * 8) by ring. rewrite !Z.div_mul by lia. lia.
Qed.

Lemma sf_CB_of_wr : forall (m : mem) a (k : nat), wr_at bsegs m a (Z.of_nat k) -> exists bs, rw_cells bsegs m a [CB k bs].
Proof.
  intros m a k Wr. pose proof (RT_facts.wr_at_stk m a (Z.of_nat k) Wr ltac:(lia)) as St.
  destruct (HandoffImage.stk_bytes bsegs m a k St) as (bs & Hl & Hbs). exists bs.
  split; [split; [cbn; split; [exact Hl | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hbs]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact Wr.
Qed.

Definition flag_back (m m' : mem) (fl : Z) : mem := fun a => if Z.eqb (bv_unsigned a) fl then m a else m' a.

Lemma flag_back_wmono : forall (m m' : mem) fl, wmono bsegs m m' -> wmono bsegs m (flag_back m m' fl).
Proof.
  intros m m' fl WM x Hx. unfold wview, flag_back in *. destruct (Z.eqb_spec (bv_unsigned x) fl) as [E|E]; [exact Hx | exact (WM x Hx)].
Qed.

Lemma flag_back_wmono' : forall (m m' : mem) fl, wview bsegs m (wa fl) <> None -> 0 <= fl < 2 ^ 64 -> wmono bsegs m m' ->
  wmono bsegs (flag_back m m' fl) m'.
Proof.
  intros m m' fl Hfl Rfl WM x Hx. unfold wview, flag_back in Hx. destruct (Z.eqb_spec (bv_unsigned x) fl) as [E|E]; [|exact Hx].
  apply WM. unfold wview. exact Hx.
Qed.

Lemma sf_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RTA Σ mo /\ PMc mo).
Proof. intros Σ PMc H. apply mat_stable_and; [exact (rta_mat_stable Σ) | exact H]. Qed.

Theorem rta_stack_free_5 : stack_free_contract RTA 5.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo
    FDO MST _ -> -> HF ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW.
  set (usp := bv_unsigned sp) in *.
  destruct (sm_pre Σ m 5%nat lo ART0 ltac:(lia) LOW) as (_ & _ & CF & _ & _ & _ & _ & _ & _ & _ & _ & M2S & FSOK & HLO & FSL & _).

  destruct (rel_slot Σ m f 5 fr ART0 HF) as (_ & p & Hp & Hf & Hb). change (Z.of_nat 5) with 5 in *. rewrite NF_5 in Hp.
  pose proof (rel_flags_ok Σ m ART0 5%nat ltac:(lia)) as (Hlen & _). change (Z.of_nat 5) with 5 in Hlen. rewrite NF_5 in Hlen.
  set (FSB := l_FSB (lay Σ)) in *.
  set (fl := fl_base FSB 5 + p).
  assert (Hpl : (Z.to_nat p < length (fss_flags (fs_of Σ 5)))%nat) by (apply Nat2Z.inj_lt; rewrite Hlen, Z2Nat.id by lia; lia).
  assert (Hbyte : rw_cells bsegs m fl [C1 (Z_to_bv 8 1)]).
  { unfold fs_flags in CF. change (Z.of_nat 5) with 5 in CF.
    assert (Hnth : nth_error (map b8 (fss_flags (fs_of Σ 5))) (Z.to_nat p) = Some (Z_to_bv 8 1))
      by (rewrite nth_error_map, (nth_error_nth' _ 0 Hpl), Hb; reflexivity).
    pose proof (u8arr_byte m _ _ _ _ CF Hnth) as X. rewrite Z2Nat.id in X by lia. exact X. }
  pose proof (ART_fs Σ m ART0) as FS. destruct FS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FB). unfold fs_busy in FB. rewrite HF in FB.
  apply Forall_cons_iff in FB as [FB0 _]. destruct FB0 as (p' & Hf' & _ & FWs0 & Cw). cbn [fst snd] in *.
  change (Z.of_nat 5) with 5 in *.
  rewrite Hf in Hf'. apply (frame_addr_inj _ _ _ _ ltac:(left; reflexivity)) in Hf'. subst p'.
  assert (Hlast : ro_cells bsegs m (f + 2040) [C8 (Z_to_bv 64 fl)]) by (replace (f + 2040) with (f + fs_size 5 - 8) by (change (fs_size 5) with 2048; lia); exact (proj1 Cw)).
  clear Cw. change (fs_size 5) with 2048 in *. change (2048 / 8) with 256 in FWs0.
  pose proof (fsb_grant Σ m ART0) as (G1 & G2 & G3 & G4 & G5). fold FSB in G1, G2, G3, G4, G5.
  pose proof (rta_sp0_range Σ m ART0) as Hr. pose proof (rta_sp0_win Σ m ART0) as Hw. unfold rtA_sp0 in *.
  assert (Hfr : FSB + 0x9000 <= f /\ f + 2048 <= FSB + 0xb09000 /\ FSB + 0x1000 <= fl /\ fl + 1 <= FSB + 0x9000 /\ f mod 8 = 0).
  { rewrite Hf. unfold fl, fl_base, frame_addr, fsz, flags_off.
    change (64 * 2 ^ 5) with 2048. change (32768 - 2 ^ (15 - 5)) with 31744. change (5 * 2 ^ 20) with 5242880.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    apply Z.mod_divide in G2; [|lia]. destruct G2 as [q Hq]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (q * 512 + 4608 + 5 * 2 ^ 17 + 256 * p). lia. }
  destruct Hfr as (F1 & F2 & F3 & F4 & F8).
  assert (ESH : shad (f + 2048) = shad f + 256) by (apply (sf_shad_add8 f 2048 F8); reflexivity).
  assert (Hsh : SHB <= shad f /\ shad f + 256 <= 2 ^ 44 + SHB).
  { split; [unfold shad; pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); lia|]. rewrite <- ESH. unfold shad.
    assert ((f + 2048) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold l_ACEIL, USTACK_TOP, STACK_WIN, SEGTOP_A in *; lia). lia. }
  assert (HACE : 2 ^ 44 + SHB <= l_ACEIL (lay Σ)) by (unfold l_ACEIL, SHB, USTACK_TOP, STACK_WIN in *; lia).
  assert (HLOA : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL in *; lia).
  destruct (sf_CB_of_wr m (shad f) 256 FWs0) as (shj & SHJ).
  assert (W1 : evt bsegs (sf5_post ra sp gp (Z_to_bv 64 0x6be3e8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f fl lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc e_stack_free_5 m)).
  { unfold entry_st.
    apply (stack_free_5_spec ra sp gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             f fl lo (Z_to_bv 8 1) shj Hlast Hbyte SHJ M2S).
    - apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia.
    - unfold SEGTOP_A in *. lia. - unfold kFakeStackSize in *. lia. - unfold SEGTOP_A in *. lia. - unfold kFakeStackSize in *. lia. - lia.
    - left. lia.
    - unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
    - unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
    - exact ST. - unfold RT_STACK in *. lia. - unfold USTACK_TOP in *. lia. - exact MI0. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sf_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sf5_post in Hc1.
  apply AST_exI in Hc1 as (y0 & Hc1). apply AST_exI in Hc1 as (y1 & Hc1). apply AST_exI in Hc1 as (y2 & Hc1). apply AST_exI in Hc1 as (y3 & Hc1).
  apply AST_exI in Hc1 as (y4 & Hc1). apply AST_exI in Hc1 as (y5 & Hc1). apply AST_exI in Hc1 as (y6 & Hc1). apply AST_exI in Hc1 as (y7 & Hc1).
  apply AST_exI in Hc1 as (y8 & Hc1). apply AST_exI in Hc1 as (y9 & Hc1). apply AST_exI in Hc1 as (y10 & Hc1). apply AST_exI in Hc1 as (y11 & Hc1).
  apply AST_exI in Hc1 as (y12 & Hc1). apply AST_exI in Hc1 as (y13 & Hc1). apply AST_exI in Hc1 as (y14 & Hc1). apply AST_exI in Hc1 as (m' & Hc1).
  pose proof Hc1 as (_ & (_ & MU & WM & MI' & ST' & FZ) & _ & _).

  set (mA := flag_back m m' fl).
  assert (INF : In (f, 5%nat) (frames Σ)) by (rewrite HF; left; reflexivity).
  assert (ARTA : ART_A Σ mA).
  { apply (af_frame RTA rta_art_facts Σ m mA (usp - 16) ART0).
    - cbn [rt_sp0 RTA]. unfold rtA_sp0, RT_STACK in *. lia.
    - intros a Ha. unfold mA, flag_back. destruct (Z.eqb_spec (bv_unsigned a) fl) as [E|E]; [reflexivity|].
      apply MU. cbn [outside]. split; [lia|]. split; [|split; [|exact I]].
      + intros X. apply Ha. right; right; right; right. exists f, 5%nat. split; [exact INF|]. change (fs_size 5) with 2048. rewrite ESH. exact X.
      + intros X. apply Ha. left. unfold USTACK_TOP in *. lia.
    - exact (flag_back_wmono m m' fl WM). }

  destruct (rta_frame_release Σ mA f 5 fr ARTA HF) as (Σ' & fl' & _ & Hncl & Hfl0' & Hfl1' & Hlast' & REL).
  assert (AGA : forall a : word, bv_unsigned a <> fl -> ~ (shad f <= bv_unsigned a < shad f + 256) -> ~ (usp - 16 <= bv_unsigned a < usp) -> mA a = m a).
  { intros a N1 N2 N3. unfold mA, flag_back. destruct (Z.eqb_spec (bv_unsigned a) fl) as [E|E]; [reflexivity|].
    apply MU. cbn [outside]. split; [lia|]. split; [exact N2|]. split; [exact N3 | exact I]. }
  assert (HlastA : ro_cells bsegs mA (f + 2040) [C8 (Z_to_bv 64 fl)]).
  { apply (D_kit.ro_cells_agree bsegs m mA _ _ Hlast). intros a Ha. cbn [cells_size csize Nat.add Z.of_nat] in Ha. apply AGA.
    - lia.
    - unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
    - unfold RT_STACK, kFakeStackSize in *. lia. }
  replace (f + fs_size 5 - 8) with (f + 2040) in Hlast' by (change (fs_size 5) with 2048; lia).
  pose proof (ro_cells_C8_inj mA (f + 2040) _ _ Hlast' HlastA) as EFL.
  assert (Efl : fl' = fl).
  { assert (R1 : 0 <= fl < 2 ^ 64) by (unfold SEGTOP_A, l_ACEIL, USTACK_TOP, STACK_WIN in *; lia).
    assert (R2 : 0 <= fl' < 2 ^ 64) by (cbn [rt_sp0 RTA] in Hfl1'; unfold rtA_sp0, USTACK_TOP, STACK_WIN in *; lia).
    rewrite <- (unsigned_lit fl' R2), <- (unsigned_lit fl R1), EFL. reflexivity. }
  subst fl'.
  assert (R1 : 0 <= fl < 2 ^ 64) by (unfold SEGTOP_A, l_ACEIL, USTACK_TOP, STACK_WIN in *; lia).
  destruct (REL m') as (ART' & EF' & EL' & ES' & EC' & EA' & EM').
  { intros a Ha. cbn [outside] in Ha. unfold mA, flag_back. destruct (Z.eqb_spec (bv_unsigned a) fl) as [E|E]; [exfalso; lia | reflexivity]. }
  { apply (flag_back_wmono' m m' fl); [|exact R1 | exact WM].
    destruct Hbyte as (_ & (_ & _ & Hwv)). specialize (Hwv 0 ltac:(cbn; lia)). rewrite Z.add_0_r in Hwv. exact Hwv. }
  { exact FZ. }

  assert (SHM : forall x y, x <= y -> shad x <= shad y) by (intros x y H; unfold shad; pose proof (Z.div_le_mono x y 8 ltac:(lia) H); lia).
  assert (PRES : rt_pres (live Σ) fr usp m m').
  { intros a Ha. apply MU. unfold RT_STACK in LOR.
    assert (HaF : aclient (live Σ) (frames Σ) usp (bv_unsigned a)).
    { rewrite HF. destruct Ha as [H|[H|[H|[H|H]]]]; [left; exact H | right; left; exact H | right; right; left; exact H | |].
      - right; right; right; left. destruct H as (f' & k' & Hin & Hx). exists f', k'. split; [right; exact Hin | exact Hx].
      - right; right; right; right. destruct H as (f' & k' & Hin & Hx). exists f', k'. split; [right; exact Hin | exact Hx]. }
    assert (SHT : forall f' k', In (f', k') (frames Σ) -> shad (f' + fs_size k') <= lo).
    { intros f' k' Hin. destruct (rta_frames_range Σ m ART0 f' k' Hin) as (Y1 & Y2 & _). unfold rtA_sp0 in Y2.
      assert ((f' + fs_size k') / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold USTACK_TOP, STACK_WIN in *; lia). unfold shad. lia. }
    cbn [outside].
    split; [|split; [|split; [|exact I]]].
    -
      intros X. assert (E : bv_unsigned a = fl) by lia. apply Hncl. rewrite <- E.
      destruct HaF as [H|H]; [exfalso; unfold kFakeStackSize, RT_STACK in *; lia | right; exact H].
    -
      intros X. destruct Ha as [H|[H|[H|[H|H]]]].
      + lia.
      + destruct H as ((lo0 & hi0 & Hin & Hx) & _). unfold CLIENT_STATIC in Hin.
        destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold SHB in *; lia.
      + destruct H as (p0 & n0 & Hin & Hx). destruct (rta_fshadow_apart Σ m ART0 f 5%nat INF) as (A1 & _).
        destruct (A1 p0 n0 Hin) as [Y|Y]; change (fs_size 5) with 2048 in Y; rewrite ?ESH in Y; lia.
      + destruct H as (f' & k' & Hin & Hx). destruct (rta_fshadow_apart Σ m ART0 f 5%nat INF) as (_ & A2).
        destruct (A2 f' k' ltac:(rewrite HF; right; exact Hin)) as [Y|Y]; change (fs_size 5) with 2048 in Y; rewrite ?ESH in Y; lia.
      + destruct H as (f' & k' & Hin & Hx).
        pose proof (rta_frames_disj Σ m ART0 f 5%nat f' k' [] fr HF Hin) as D. change (fs_size 5) with 2048 in D.
        destruct D as [D|D]; [pose proof (SHM _ _ D) as Y; rewrite ESH in Y; lia | pose proof (SHM _ _ D) as Y; lia].
    -
      intros X. destruct HaF as [H|[H|[H|[H|H]]]].
      + lia.
      + destruct H as ((lo0 & hi0 & Hin & Hx) & _). unfold CLIENT_STATIC in Hin.
        destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold RT_STACK in *; lia.
      + destruct H as (p0 & n0 & Hin & Hx). destruct (rta_live_range Σ m p0 n0 ART0 Hin) as (Y1 & Y2 & _). unfold rtA_sp0, RT_STACK in *. lia.
      + destruct H as (f' & k' & Hin & Hx). destruct (rta_frames_range Σ m ART0 f' k' Hin) as (Y1 & Y2 & _). unfold rtA_sp0, RT_STACK in *. lia.
      + destruct H as (f' & k' & Hin & Hx). pose proof (SHT f' k' Hin). unfold RT_STACK in *. lia. }
  exists Σ', y3.
  split; [|split; [exact EF' | split; [exact EL' | split; [exact ES' | exact EC']]]].
  unfold ASTA. change (rt_allow RTA Σ') with (rtA_allow Σ'). rewrite EA'.
  eapply AST_conseq; [exact Hc1 | | intros mo (H1 & H2); split; [exact (EM' mo H1) | exact H2]].
  intros ms (-> & _). exists m'.
  split; [exists y0, y1, y2, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F; reflexivity|].
  split; [split; [exact ART' | split; [exact MI' | split; [exact WM | exact ST']]] | exact (rt_pres_vis _ _ _ _ _ _ PRES)].
Qed.

End GWIN.

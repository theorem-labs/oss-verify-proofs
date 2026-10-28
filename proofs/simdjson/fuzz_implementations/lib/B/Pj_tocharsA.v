(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface I_lkit D_rlkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_kitA Pj_ser_callsA Pj_ser_ncallsA Pj_tocharsA_defs RT_iface4 Pj_dboxB Pj_fmtB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
  | |- _ => reflexivity
  end.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma tcb_sx32_e : forall e, SF_EMIN <= e <= SF_EMAX -> sx32 (Z_to_bv 64 (e mod 4294967296)) = Z_to_bv 64 e.
Proof.
  intros e H. unfold SF_EMIN, SF_EMAX in H. unfold sx32. f_equal. rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
  rewrite swrap32_Z. Z.div_mod_to_equations. lia.
Qed.
Lemma tcb_sx32_n : forall n, 0 <= n < 2147483648 -> sx32 (Z_to_bv 64 n) = Z_to_bv 64 n.
Proof. intros n H. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply swrap32_id. lia. Qed.

Section TC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis HDB : dbox_cpsB RT PMc.
Hypothesis HFM : fmt_cpsB RT PMc.
Notation aevt := (aevt RT PMc).
Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Local Ltac nb_store NA NL k :=
  lazymatch type of NA with u8arr _ ?mm ?A ?l =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok bsegs mm A l k (wa (A + k)) NA ltac:(rewrite NL; lia) eq_refl) as SOK;
    step;
    let NA1 := fresh "NA" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mw ?a (le1 ?v)) _) =>
      let E := addr_expr a in
      (lazymatch a with wa _ => idtac | _ => change (write_to_mem mw a (le1 v)) with (write_to_mem mw (wa E) (le1 v)) end);
      pose proof (u8arr_write_le1 mm A l k v (wa E) NA ltac:(rewrite NL; lia) ltac:(unfold wa; f_equal; lia)) as NA1 end;
    store_done; try clear NA; try clear SOK;
    let NL1 := fresh "NL" in
    lazymatch type of NA1 with u8arr _ _ _ ?l1 => assert (NL1 : length l1 = 40%nat) by (rewrite upd_length; exact NL) end;
    try clear NL; rename NA1 into NA; rename NL1 into NL
  end.

Theorem tochars_okB : tochars_cpsA RT PMc.
Proof using AF RC FDO MST HDB HFM.
  unfold tochars_cpsA.
  intros Σ K NB q lo fN kN ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fcw m junk
         FDO' MST' INN NLE NHI N8 NBC NSH ART0 MI0 ST0 SPLO LOQ QT Q16 FRM FRL CR HK.
  unfold PJ_TC_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT. unfold PJ_TOCHARS_A.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _ & _). pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
  pose proof (af_frames_range RT AF Σ m fN kN ART0 INN) as (N0 & NWIN & _ & _). pose proof (af_frames_align RT AF Σ m fN kN ART0 INN) as [_ NSEG].
  pose proof (af_fshadow_apart RT AF Σ m fN kN ART0 INN) as [_ NSF].
  assert (FSZN : 0 <= fs_size kN) by (unfold fs_size; apply Z.shiftl_nonneg; clear; lia).
  assert (GLO : 0x6e0000 <= lo) by (clear - SPLO SPW; ul).
  assert (GN : 0x6e0000 <= NB) by (clear - NSEG NLE; ul).
  assert (NLO : NB + 40 <= lo) by (clear - NHI NWIN SPLO; lia).
  assert (SNLO : shad NB + 5 <= lo) by (unfold shad, SHB; clear - NLO SPLO SPW; unfold STACK_WIN in *; Z.div_mod_to_equations; lia).
  assert (SNN : shad NB + 5 <= NB \/ NB + 40 <= shad NB).
  { destruct (NSF fN kN INN) as [H|H]; [right| left]; unfold shad, SHB in *; clear - H NLE NHI; Z.div_mod_to_equations; lia. }
  assert (SNIN : shad fN <= shad NB /\ shad NB + 5 <= shad (fN + fs_size kN)) by (unfold shad; clear - NLE NHI; Z.div_mod_to_equations; lia).
  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0 Ha) as [H|H]; [left; exact H| right; clear - H SPLO; lia]. }
  assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; clear - LOQ GLO QT; lia).
  change (repeat z8 5) with [z8; z8; z8; z8; z8] in NSH.
  pose proof (u8arr_of_rw_cells bsegs _ _ _ _ NBC) as NA.
  assert (NL : length junk = 40%nat) by (destruct NBC as [[Hwf _] _]; cbn in Hwf; clear - Hwf; tauto). clear NBC.

  assert (RDN : forall (mm : mem) k, bytes_at bsegs mm (shad NB) [z8; z8; z8; z8; z8] -> 0 <= k <= 3 -> ov_read_bytes bsegs mm (wa (shad (NB + k))) 1 = Some [z8]).
  { intros mm k HB Hk. replace (shad (NB + k)) with (shad NB + 0) by (unfold shad; clear - Hk N8; Z.div_mod_to_equations; lia).
    exact (bytes_at_read bsegs mm (shad NB) [z8; z8; z8; z8; z8] 0 1 HB ltac:(clear; lia) ltac:(cbn; clear; lia)). }

  assert (ARTW : forall W (m1 m2 : mem), ART RT Σ m1 -> munch W m1 m2 -> wmono bsegs m1 m2 ->
            (forall a, outside W a \/ (q - 32 <= a < q \/ NB <= a < NB + 40)) -> ART RT Σ m2).
  { intros W m1 m2 A1 MU WM HW. apply (art_client_write RT AF Σ m1 m2 (q - 32) A1); [clear - SPLO LOQ; lia| | exact WM].
    intros a Hna. apply MU. destruct (HW (bv_unsigned a)) as [H|[H|H]]; [exact H| exfalso; apply Hna..].
    - left. unfold USTACK_TOP. clear - H QT. lia.
    - right; right; right; left. exists fN, kN. split; [exact INN| clear - H NLE NHI; lia]. }
  set (PRESq := fun mm : mem => forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (NB <= bv_unsigned a < NB + 40) -> mm a = m a).
  assert (PRESW : forall W (m1 m2 : mem), PRESq m1 -> munch W m1 m2 -> (forall a, outside W a \/ (q - 32 <= a < q \/ NB <= a < NB + 40)) -> PRESq m2).
  { intros W m1 m2 P1 MU HW a Ha Hn. rewrite <- (P1 a Ha Hn). apply MU. destruct (HW (bv_unsigned a)) as [H|[H|H]]; [exact H| | exfalso; exact (Hn H)].
    exfalso. destruct (CSEP _ Ha); clear - H H0 NLO LOQ; lia. }

  set (TB := fun mm : mem =>
    (exists j c0 c1, rw_cells bsegs mm (q + -32) [CB 8 j; CB 4 c0; CB 4 c1; C8 s0; C8 ra]) /\ (exists nb, u8arr bsegs mm NB nb /\ length nb = 40%nat)
    /\ bytes_at bsegs mm (shad NB) [z8; z8; z8; z8; z8] /\ ART RT Σ mm /\ mem_inv bsegs mm /\ stk bsegs mm lo (q + -32) /\ PRESq mm).

  assert (KZ : forall (sg : Z) (m1 : mem) (F1 : bvmap 5 word) (fc1 : bv 32) (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    TB m1 -> frm0 fc1 -> 0 <= sg <= 1 ->
    aevt Σ K (MS (mkR xra (wz (q + -32)) gp (wz TPV_A) xt0 xt1 xt2 (wz (NB + sg)) s1 xa0 xa1 (wz 2147450880) xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                 F1 (wz 0xbff70) fc1 None m1 (seg_rom bsegs))).
  { intros sg m1 F1 fc1 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 ((j & c0 & c1 & FR) & (nb & NA1 & NL1) & NSH1 & ART1 & MI1 & ST1 & PR1) FRM1 HSG.
    clear NA NL. rename NA1 into NA. rename NL1 into NL.
    apply (aevt_evt RT AF PMc MST). unfold TPV_A.
    pose proof (munch_refl [(NB, NB + 40)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.

    zstep. zstep. step. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc GN NLO LOQ QT HSG; lia| clear Kc].
    pose proof (RDN m1 sg NSH1 ltac:(clear - HSG; lia)) as RD.
    zstep. pjnorm. zstep. change (wz ((NB + sg) / 8 + 2147450880)) with (wz (shad (NB + sg))). zstep. clear RD.
    replace (sxb z8) with (wz 0) by reflexivity. zstep. try if_false.

    zstep. zstep. nb_store NA NL sg.
    step. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc GN NLO LOQ QT HSG; lia| clear Kc].

    pose proof (RDN _ (sg + 1) NSH1 ltac:(clear - HSG; lia)) as RD. replace (NB + (sg + 1)) with (NB + sg + 1) in RD by (clear; lia).
    zstep. pjnorm. zstep. change (wz ((NB + sg + 1) / 8 + 2147450880)) with (wz (shad (NB + sg + 1))). zstep. clear RD.
    replace (sxb z8) with (wz 0) by reflexivity. zstep. try if_false.

    zstep. pjnorm. zstep. zstep. nb_store NA NL (sg + 1).
    step. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc GN NLO LOQ QT HSG; lia| clear Kc].

    pose proof (RDN _ (sg + 2) NSH1 ltac:(clear - HSG; lia)) as RD. replace (NB + (sg + 2)) with (NB + sg + 2) in RD by (clear; lia).
    zstep. pjnorm. zstep. change (wz ((NB + sg + 2) / 8 + 2147450880)) with (wz (shad (NB + sg + 2))). zstep. clear RD.
    replace (sxb z8) with (wz 0) by reflexivity. zstep. try if_false.

    zstep. pjnorm. zstep. nb_store NA NL (sg + 2).

    zstep. zstep. zstep. replace (q + -32 + 32) with q by (clear; lia). zstep.
    release_frame FR ST1 q.
    pose proof (ARTW _ _ _ ART1 MU WM ltac:(intros a; cbn [outside]; clear; lia)) as ART2.
    pose proof (PRESW _ _ _ PR1 MU ltac:(intros a; cbn [outside]; clear; lia)) as PR2.
    pose proof (rw_cells_of_u8arr bsegs _ _ _ NA) as NBC. rewrite NL in NBC.
    apply evt_done.
    eapply (HK Σ (NB + sg + 3) _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 _ _ FRM1 ART2); [eassumption| exact ST1| reflexivity| reflexivity| reflexivity| clear; lia
      | intros a Ha Ho; cbn [outside] in Ho; apply PR2; [exact Ha| clear - Ho; lia]| clear - HSG; lia| exact NBC]. }

  assert (KNZ : forall (sg : Z) (m1 : mem) (F1 : bvmap 5 word) (fc1 : bv 32) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    TB m1 -> frm0 fc1 -> 0 <= sg <= 1 ->
    aevt Σ K (MS (mkR xra (wz (q + -32)) gp (wz TPV_A) xt0 xt1 xt2 (wz (NB + sg)) s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                 F1 (wz 0xc0020) fc1 None m1 (seg_rom bsegs))).
  { intros sg m1 F1 fc1 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 ((j & c0 & c1 & FR) & (nb & NA1 & NL1) & NSH1 & ART1 & MI1 & ST1 & PR1) FRM1 HSG.
    clear NA NL. rename NA1 into NA. rename NL1 into NL.
    apply (aevt_evt RT AF PMc MST). unfold TPV_A.
    pose proof (munch_refl [(q + -32, q)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.

    step. step. zstep. pjnorm. zstep. pjnorm. zstep. zstep.
    pose proof (ARTW _ _ _ ART1 MU WM ltac:(intros a; cbn [outside]; clear; lia)) as ART2.
    pose proof (PRESW _ _ _ PR1 MU ltac:(intros a; cbn [outside]; clear; lia)) as PR2.
    lazymatch type of FR with rw_cells _ ?mm _ [?cj; ?cc0; ?cc1; ?cs0; ?cra] =>
      pose proof (proj1 (rw_cells_app bsegs mm (q + -32) [cj] [cc0; cc1; cs0; cra]) FR) as [F0 F1r];
      cbn [cells_size csize Nat.add] in F1r; replace (q + -32 + Z.of_nat 8) with (q + -24) in F1r by (clear; lia);
      pose proof (proj1 (rw_cells_app bsegs mm (q + -24) [cc0; cc1] [cs0; cra]) F1r) as [CEL SAV];
      cbn [cells_size csize Nat.add] in SAV; replace (q + -24 + Z.of_nat 8) with (q + -16) in SAV by (clear; lia) end.
    clear FR F1r. apply evt_done.
    eapply aevt_eq; [| eapply (HDB Σ K (q + -32) lo NB sg fN kN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 _ nb _ _ FDO MST INN NLE NHI N8 NA NL NSH1 HSG)];
      [pj_st_eq| replace (q + -32 + 8) with (q + -24) by (clear; lia); exact CEL| exact ART2| exact MI1| exact ST1| exact SPLO
      | unfold DBOX_STACK_B, RT_STACK; clear - LOQ; lia| unfold USTACK_TOP; clear - QT; lia| clear - Q16; Z.div_mod_to_equations; lia| exact FRM1
      | exact FRL| exact CR|].
    intros Σ1 n e yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F2 fc2 mD nbD FRM2 ART3 MI3 ST3 LV3 FRS3 SP3 CR3 PRX HN HE CEL2 NA2 NL2 NSH2.
    replace (q + -32 + 8) with (q + -24) in CEL2 by (clear; lia). rewrite (ret_pc_even 0xc0038) by (clear; lia).
    lazymatch type of SAV with rw_cells _ ?mc _ _ =>
    assert (AG2 : forall (P : Z -> Prop), (forall y, P y -> (q - 32 <= y < q - 24 \/ q - 16 <= y < q)) -> agree_on P mc mD) end.
    { intros P HP a Ha. apply PRX; [left; unfold USTACK_TOP; clear - Ha HP QT; pose proof (HP _ Ha); lia|].
      cbn [outside]. pose proof (HP _ Ha). clear - H NLO LOQ. repeat split; try exact Logic.I; lia. }
    assert (F02 : rw_cells bsegs mD (q + -32) [CB 8 j]) by (eapply rw_cells_agree_nw; [exact F0|]; apply AG2; intros y Hy; cbn [cells_size csize Nat.add] in Hy; left; clear - Hy; lia).
    assert (SAV2 : rw_cells bsegs mD (q + -16) [C8 s0; C8 ra]) by (eapply rw_cells_agree_nw; [exact SAV|]; apply AG2; intros y Hy; cbn [cells_size csize Nat.add] in Hy; right; clear - Hy; lia).
    clear F0 SAV CEL AG2.

    apply (aevt_evt RT AF PMc MST).
    zstep. zstep. rewrite (tcb_sx32_e e HE). rewrite (tcb_sx32_n n) by (clear - HN; lia). zstep. zstep. zstep. zstep.
    apply evt_done.
    eapply aevt_eq; [| eapply (HFM Σ1 K (q + -32) lo NB sg n e fN kN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mD nbD FDO MST)];
      [pj_st_eq| rewrite FRS3; exact INN| exact NLE| exact NHI| exact N8| exact NA2| exact NL2| exact NSH2| exact HSG| exact HN| exact HE| exact ART3| exact MI3| exact ST3
      | rewrite SP3; exact SPLO| unfold FMT_STACK_B, RT_STACK; clear - LOQ; lia| unfold USTACK_TOP; clear - QT; lia| clear - Q16; Z.div_mod_to_equations; lia|].
    intros e' zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 F3 mF nbF ART4 MI4 ST4 PRY HE' NA3 NL3.
    rewrite (ret_pc_even 0xc0050) by (clear; lia).
    assert (AG3 : forall (P : Z -> Prop), (forall y, P y -> q - 32 <= y < q) -> agree_on P mD mF).
    { intros P HP a Ha. apply PRY; [left; unfold USTACK_TOP; clear - Ha HP QT; pose proof (HP _ Ha); lia|].
      cbn [outside]. pose proof (HP _ Ha). clear - H NLO LOQ. repeat split; try exact Logic.I; lia. }
    assert (FR3 : rw_cells bsegs mF (q + -32) [CB 8 j; C4 (wz (e mod 4294967296)); C4 (wz n); C8 s0; C8 ra]).
    { apply (proj2 (rw_cells_app bsegs mF (q + -32) [CB 8 j] [C4 (wz (e mod 4294967296)); C4 (wz n); C8 s0; C8 ra])). split.
      - eapply rw_cells_agree_nw; [exact F02|]. apply AG3. intros y Hy. cbn [cells_size csize Nat.add] in Hy. clear - Hy; lia.
      - cbn [cells_size csize Nat.add]. replace (q + -32 + Z.of_nat 8) with (q + -24) by (clear; lia).
        apply (proj2 (rw_cells_app bsegs mF (q + -24) [C4 (wz (e mod 4294967296)); C4 (wz n)] [C8 s0; C8 ra])). split.
        + eapply rw_cells_agree_nw; [exact CEL2|]. apply AG3. intros y Hy. cbn [cells_size csize Nat.add] in Hy. clear - Hy; lia.
        + cbn [cells_size csize Nat.add]. replace (q + -24 + Z.of_nat 8) with (q + -16) by (clear; lia).
          eapply rw_cells_agree_nw; [exact SAV2|]. apply AG3. intros y Hy. cbn [cells_size csize Nat.add] in Hy. clear - Hy; lia. }
    clear F02 SAV2 CEL2.

    apply (aevt_evt RT AF PMc MST).
    zstep. zstep. zstep. replace (q + -32 + 32) with q by (clear; lia). zstep.
    release_frame FR3 ST4 q.
    pose proof (rw_cells_of_u8arr bsegs _ _ _ NA3) as NBC. rewrite NL3 in NBC.
    apply evt_done.
    eapply (HK Σ1 e' _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc2 _ _ FRM2 ART4 MI4 ST4 LV3 FRS3 SP3 CR3); [| clear - HE' HSG; lia| exact NBC].
    intros a Ha Ho. cbn [outside] in Ho.
    rewrite (PRY a); [| rewrite LV3, FRS3; eapply aclient_mono; [exact Ha| intros x Hx; exact Hx| intros x Hx; exact Hx| clear; lia]
                     | cbn [outside]; clear - Ho; repeat split; try exact Logic.I; lia].
    rewrite (PRX a); [| eapply aclient_mono; [exact Ha| intros x Hx; exact Hx| intros x Hx; exact Hx| clear; lia]
                     | cbn [outside]; destruct (CSEP _ Ha) as [H|H]; clear - H Ho NLO LOQ; repeat split; try exact Logic.I; lia].
    apply PR2; [exact Ha| clear - Ho; lia]. }

  apply (aevt_evt RT AF PMc MST). unfold TPV_A.
  pose proof (munch_refl [(q + -32, q); (NB, NB + 40)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

  zstep. carve_frame 32%nat ST0.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 4; 4; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let jj := fresh "j" in set (jj := t) in FR; clearbody jj end.
  zstep. zstep.

  zstep. zstep. zstep. zstep.
  step. if_cases KS; clear KS.
  -
    zstep. zstep. step. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc GN NLO LOQ QT; lia| clear Kc].
    pose proof (RDN _ 0 NSH ltac:(clear; lia)) as RD. replace (NB + 0) with NB in RD by (clear; lia).
    zstep. pjnorm. zstep. change (wz (NB / 8 + 2147450880)) with (wz (shad NB)). zstep. clear RD.
    replace (sxb z8) with (wz 0) by reflexivity. zstep. try if_false.

    zstep. zstep. nb_store NA NL 0. zstep. zstep.
    pose proof (ARTW _ _ _ ART0 MU WM ltac:(intros a; cbn [outside]; clear; lia)) as ART1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (PR1 : PRESq mm) by (eapply (PRESW _ m _); [intros a _ _; reflexivity| exact MU| intros a; cbn [outside]; clear; lia]) end.
    step. if_cases KZ0; clear KZ0; apply evt_done.
    + eapply aevt_eq; [| eapply (KZ 1)]; [pj_st_eq| | exact FRM| clear; lia].
      split; [do 3 eexists; exact FR|]. split; [eexists; split; [exact NA| exact NL]|]. split; [exact NSH|]. split; [exact ART1|]. split; [exact MI0|]. split; [exact ST0| exact PR1].
    + eapply aevt_eq; [| eapply (KNZ 1)]; [pj_st_eq| | exact FRM| clear; lia].
      split; [do 3 eexists; exact FR|]. split; [eexists; split; [exact NA| exact NL]|]. split; [exact NSH|]. split; [exact ART1|]. split; [exact MI0|]. split; [exact ST0| exact PR1].
  -
    zstep. zstep. zstep.
    pose proof (ARTW _ _ _ ART0 MU WM ltac:(intros a; cbn [outside]; clear; lia)) as ART1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (PR1 : PRESq mm) by (eapply (PRESW _ m _); [intros a _ _; reflexivity| exact MU| intros a; cbn [outside]; clear; lia]) end.
    step. if_cases KZ0; clear KZ0; apply evt_done.
    + eapply aevt_eq; [| eapply (KNZ 0)]; [pj_st_eq| | exact FRM| clear; lia].
      split; [do 3 eexists; exact FR|]. split; [eexists; split; [exact NA| exact NL]|]. split; [exact NSH|]. split; [exact ART1|]. split; [exact MI0|]. split; [exact ST0| exact PR1].
    + eapply aevt_eq; [| eapply (KZ 0)]; [pj_st_eq| | exact FRM| clear; lia].
      split; [do 3 eexists; exact FR|]. split; [eexists; split; [exact NA| exact NL]|]. split; [exact NSH|]. split; [exact ART1|]. split; [exact MI0|]. split; [exact ST0| exact PR1].
Qed.
End TC.

Theorem tochars_okA : forall RT, art_facts RT -> rt_contracts RT -> stack_malloc1z_contract RT -> forall PMc, tochars_cpsA RT PMc.
Proof.
  intros RT AF RC SM1Z PMc. unfold tochars_cpsA.
  intros Σ K NB q lo fN kN ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk FDO MST.
  pose proof (tochars_okB RT AF RC PMc FDO MST (dbox_okB RT AF RC SM1Z PMc FDO MST) (fmt_okB RT AF RC PMc FDO MST)) as H.
  unfold tochars_cpsA in H.
  exact (H Σ K NB q lo fN kN ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk FDO MST).
Qed.

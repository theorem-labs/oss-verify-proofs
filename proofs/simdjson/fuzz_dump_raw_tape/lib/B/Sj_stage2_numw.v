(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_iface Sj_num_akit
  Sj_stage2_defs Sj_stage2_main Sj_stage2_world.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac wE_norm :=
  unfold Sj_stage2_main.wE, wm in *;
  cbn [env_at fst snd e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA
       e_bs e_idxs e_iws e_tcap e_scap e_vptr e_p12 e_nxt0 e_p28 e_capv e_p50 e_dcap e_j0 e_j256 e_m0 e_tws e_sbs s2_ghost gapp gpatch] in *.

Lemma u8arr_agree' : forall (m m' : mem) A bs, u8arr bsegs m A bs ->
  agree_on (fun x => A <= x < A + Z.of_nat (length bs)) m m' -> wmono bsegs m m' -> u8arr bsegs m' A bs.
Proof.
  intros m m' A bs [HB HW] AG WM. split.
  - exact (bytes_at_agree bsegs m m' A bs HB AG).
  - exact (wr_at_transport bsegs m m' A _ HW WM).
Qed.

Lemma tape_img_agree : forall E tws sbs (m m' : mem), tape_img E tws sbs m ->
  agree_on (fun x => e_TAPE E <= x < e_TAPE E + 8 * e_tcap E) m m' -> agree_on (fun x => e_SBUF E <= x < e_SBUF E + e_scap E) m m' ->
  wmono bsegs m m' -> tape_img E tws sbs m'.
Proof.
  intros E tws sbs m m' (T1 & T2 & T3 & T4 & S1 & S2 & SB) A1 A2 WM.
  pose proof (Zle_0_nat (length tws)). pose proof (Zle_0_nat (length sbs)).
  split; [|split; [|split; [exact T3|split; [exact T4|split; [|split; [|exact SB]]]]]].
  - apply (bytes_at_agree bsegs m m' _ _ T1). eapply agree_sub; [exact A1|]. intros x Hx. cbv beta in *. rewrite twords_length in Hx. lia.
  - apply (bytes_at_agree bsegs m m' _ _ T2). eapply agree_sub; [exact A2|]. intros x Hx. cbv beta in *. rewrite zbytes_length in Hx. lia.
  - exact (stk_agree bsegs m m' _ _ S1 A1 WM).
  - exact (stk_agree bsegs m m' _ _ S2 A2 WM).
Qed.

Section NumW.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Variable E0 : s2env.
  Hypothesis OK0 : env_ok E0.
  Variable K : config -> Prop.
  Variable good : WD RT -> Z -> Prop.
  Hypothesis GNUM : g_num RT E0 good.
  Hypothesis GSTEP : g_step RT E0 good.
  Notation wE := (Sj_stage2_main.wE E0 (WD RT) (wm RT)).
  Notation wQ := (Sj_stage2_world.wQ RT PMc K).

  Lemma numw_call : forall (entry r1 r0 RA : Z), numwa_cps RT entry r1 r0 -> (0 <= RA < 2^64)%Z -> (RA mod 2 = 0)%Z ->
    forall (w : WD RT) (kk off : Z), good w kk -> (0 <= kk <= e_n E0)%Z -> (0 <= off <= e_len E0)%Z ->
    forall (nxt : word) (sc : list (bool * Z)) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 c168 c176 c184 c192 c200 c272 c288 : cell) (j304 : list byte) (tws sbs : list Z),
    Forall (fun c => csize c = 8%nat) [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288] ->
    forall (t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI (s2_ghost (wE w) tws sbs) nxt [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288; CB 8 j304] sc fc m1 ->
    (forall (w' : WD RT) (flag : bool) (v : word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
        good w' (kk + 1) ->
        MEMI (s2_ghost (wE w') tws sbs) nxt [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288; C8 v] sc fc' (wm RT w') ->
        wQ w' (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0' t1' t2' s0 s1 (Z_to_bv 64 (if flag then r1 else r0)) a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 RA) fc' None (wm RT w') (seg_rom bsegs))) ->
    wQ w (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0 t1 t2 s0 s1 (Z_to_bv 64 (e_BUF E0 + off)) (Z_to_bv 64 (e_spa E0 + 304)) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m1 (seg_rom bsegs)).
  Proof using AF FDO MST OK0 GNUM GSTEP.
    intros entry r1 r0 RA HC HRA HRA2 w kk off HG HKK HOFF nxt sc c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 c168 c176 c184 c192 c200 c272 c288 j304 tws sbs HCS.
    intros t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HM HK.
    destruct (GNUM w kk HG HKK) as [NART NFR NCR NWIN NROOM NTOP NTP (p & n & PIN & P8 & PLO & PHI) NCL NFNZ].
    destruct w as [m0 Σ]. cbn [snd fst] in *.
    pose proof (ok_bytes _ OK0) as BOK. s2_env OK0.
    assert (EU : bv_unsigned (Z_to_bv 64 (e_spa E0)) = e_spa E0) by (apply unsigned_lit; lia).
    assert (HAL16 : e_spa E0 mod 16 = 0 /\ (e_spa E0 + 304) mod 8 = 0).
    { pose proof (ok_al_spa _ OK0) as A32. clear - A32. split; Z.div_mod_to_equations; lia. }
    s2_open_mem HM. wE_norm.

    assert (ART1 : ART RT Σ m1).
    { apply (art_client_write RT AF Σ m0 m1 (e_lo E0) NART NWIN); [| exact WM].
      apply (agree_of_munch _ m0 m1 _ MU). intros x NC.
      assert (CL : forall y, s2_region E0 y -> aclient (rt_live RT Σ) (rt_frames RT Σ) (e_lo E0) y).
      { intros y Hy. eapply aclient_mono; [exact (NCL y Hy) | auto | auto | lia]. }
      cbn [outside]. unfold USTACK_TOP in *.
      repeat split; try exact I; intro HI; apply NC.
      - left. unfold USTACK_TOP. lia.
      - apply CL. unfold s2_region. right; left. lia.
      - apply CL. unfold s2_region. do 5 right; left. lia.
      - apply CL. unfold s2_region. do 6 right; left. lia.
      - apply CL. unfold s2_region. do 7 right; left. lia.
      - apply CL. unfold s2_region. do 8 right; left. lia.
      - apply CL. unfold s2_region. do 9 right. lia. }

    repeat match goal with H : Forall _ (_ :: _) |- _ => let E8 := fresh "E8" in inversion H as [|? ? E8 H']; clear H; subst; rename H' into HCS' end.
    lazymatch type of FR with rw_cells _ _ _ ?l =>
      rewrite (app_removelast_last (CB 0 []) (l := l)) in FR by discriminate end.
    cbn [removelast last] in FR.
    apply rw_cells_app in FR. destruct FR as [FRa FRb].
    lazymatch type of FRb with rw_cells _ _ (_ + Z.of_nat ?sz) _ =>
      assert (SZ : Z.of_nat sz = 304) by (cbn [cells_size csize]; repeat match goal with H : csize _ = 8%nat |- _ => rewrite H; clear H end; reflexivity) end.
    rewrite SZ in FRb.

    unfold Sj_stage2_world.wQ, aevt. cbn [snd]. intros T c Hc Hk.
    assert (HB0 : B (e_bs E0) (e_len E0) = 0) by (apply B_pad; lia).
    apply (HC Σ PMc (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0 t1 t2 s0 s1 (Z_to_bv 64 (e_BUF E0 + off)) (Z_to_bv 64 (e_spa E0 + 304)) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (e_BUF E0) off (e_len E0) (e_spa E0 + 304) (e_lo E0) p n (padded_bytes (e_bs E0))
             (Z_to_bv 8 (B (e_bs E0) (e_len E0))) j304 FDO MST eq_refl eq_refl NTP FRM NFR NFNZ NCR ART1 MI) with (T := T) (c := c);
      rewrite ?EU; try assumption; try lia.
    { apply nth_error_padded. lia. }
    { rewrite HB0. reflexivity. }

    intros c' (Σ' & HA & EFR & ELV & ESP & ECR).
    destruct (ASTA_unpack RT Σ' PMc _ c' HA) as (ms' & (m' & v & flag & RS & F0 & RAF & PR & OUTC) & HA').
    destruct RAF as (ART' & MI' & WM' & ST').
    assert (HG' : good (m', Σ') (kk + 1)).
    { apply (GSTEP (m0, Σ) (m', Σ') kk HG HKK). exists m1. cbn [snd fst]. wE_norm.
      split; [exact MU|]. split; [exact WM|]. split; [exact ART1|]. split; [exact (conj ART' (conj MI' (conj WM' ST')))|].
      split; [exact PR|]. split; [exact EFR|]. split; [exact ELV|]. split; [exact ESP| exact ECR]. }

    assert (AG : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (e_spa E0) x /\ ~ (e_spa E0 + 304 <= x < e_spa E0 + 304 + 8)) m1 m').
    { intros a [H1 H2]. exact (PR a H1 H2). }
    assert (SIDE : forall x, s2_region E0 x -> ~ (e_spa E0 + 304 <= x < e_spa E0 + 304 + 8) ->
              aclient (rt_live RT Σ) (rt_frames RT Σ) (e_spa E0) x /\ ~ (e_spa E0 + 304 <= x < e_spa E0 + 304 + 8)).
    { intros x H1 H2. split; [exact (NCL x H1) | exact H2]. }
    pose proof (ok_iwl _ OK0) as EK_iwl2.
    Ltac reg_pick := unfold s2_region;
      first [ left; lia | right; left; lia | do 2 right; left; lia | do 3 right; left; lia | do 4 right; left; lia | do 5 right; left; lia
            | do 6 right; left; lia | do 7 right; left; lia | do 8 right; left; lia | do 9 right; lia ].
    pose proof FRa as FRa'. apply (rw_cells_agree bsegs m1 m') in FRa'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite SZ in Hx; apply SIDE; [reg_pick | lia] | exact WM'].
    pose proof SAV as SAV'. apply (rw_cells_agree bsegs m1 m') in SAV'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply SIDE; [reg_pick | lia] | exact WM'].
    pose proof GAP as GAP'. apply (stk_agree_nw bsegs m1 m') in GAP'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; apply SIDE; [reg_pick | lia]].
    assert (FFW' := wr_at_transport bsegs m1 m' _ _ FFW WM').
    pose proof IMPL as IMPL'. apply (rw_cells_agree bsegs m1 m') in IMPL'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply SIDE; [reg_pick | lia] | exact WM'].
    pose proof DOCC as DOCC'. apply (rw_cells_agree bsegs m1 m') in DOCC'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply SIDE; [reg_pick | lia] | exact WM'].
    pose proof IDXA as IDXA'. apply (u32arr_agree m1 m') in IDXA'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; apply SIDE; [reg_pick | lia] | exact WM'].
    pose proof BUFRO as BUFRO'. apply (bytes_at_agree bsegs m1 m') in BUFRO'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite PBL in Hx; apply SIDE; [reg_pick | lia]].
    assert (TAPEW' := wr_at_transport bsegs m1 m' _ _ TAPEW WM').
    assert (SBUFW' := wr_at_transport bsegs m1 m' _ _ SBUFW WM').
    pose proof OCA as OCA'. apply (u32arr_agree m1 m') in OCA'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite OCL in Hx; apply SIDE; [reg_pick | lia] | exact WM'].
    pose proof TIMG as TIMG'. apply (tape_img_agree _ _ _ m1 m') in TIMG'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; cbn [e_TAPE e_SBUF e_tcap e_scap s2_ghost env_at] in Hx; apply SIDE; [reg_pick | lia] | eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; cbn [e_TAPE e_SBUF e_tcap e_scap s2_ghost env_at] in Hx; apply SIDE; [reg_pick | lia] | exact WM'].
    pose proof IAA as IAA'. apply (u8arr_agree' m1 m') in IAA'; [| eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in Hx; rewrite IAL in Hx; apply SIDE; [reg_pick | lia] | exact WM'].
    assert (FR' : rw_cells bsegs m' (e_spa E0)
                    ([c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200;
                      C8 (Z_to_bv 64 (e_THIS E0 + 16)); C8 (Z_to_bv 64 (e_THIS E0 + 8)); C8 (Z_to_bv 64 (SHA (e_THIS E0 + 16))); C8 (Z_to_bv 64 (SHA (e_THIS E0 + 8)));
                      C8 (Z_to_bv 64 (SHA (e_THIS E0 + 88))); C8 (Z_to_bv 64 (e_THIS E0 + 88)); C8 (Z_to_bv 64 (e_THIS E0)); C8 (Z_to_bv 64 (e_FF E0)); c272;
                      C8 (Z_to_bv 64 2147450880); c288; C8 (Z_to_bv 64 (e_FF E0))] ++ [C8 v])).
    { apply rw_cells_app. split; [exact FRa'|]. rewrite SZ. exact OUTC. }

    destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    cbn [ms_fcsr] in F0. rewrite (ret_pc_even RA HRA HRA2) in HA'.
    refine (HK (m', Σ') flag v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' HG' _ T c' HA' Hk).
    unfold MEMI. wE_norm. unfold fr_cells, saved_cells, impl_cells, doc_cells, s2_W.
    split; [exact F0|]. split; [exact FR'|]. split; [exact SAV'|]. split; [exact GAP'|]. split; [exact FFW'|]. split; [exact IMPL'|]. split; [exact DOCC'|].
    split; [exact IDXA'|]. split; [exact BUFRO'|]. split; [exact TAPEW'|]. split; [exact SBUFW'|].
    split; [exists ocs; split; [exact OCA'| split; [exact OCL| exact OCR]]|].
    split; [exists ias; split; [exact IAA'| split; [exact IAL| exact IAR]]|].
    split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact ST'| exact TIMG'].
  Qed.
End NumW.

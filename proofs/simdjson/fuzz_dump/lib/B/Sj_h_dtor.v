(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_docdtor : Z := 0xb20cc.

Definition shb_consts (m : mem) : Prop :=
  ro_cells bsegs m 1499600 [C8 (Z_to_bv 64 1536312)] /\ ro_cells bsegs m 1536312 [C8 (Z_to_bv 64 2147450880)].

Definition doc_shz (W : list ivl) (m0 : mem) (DOC : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono bsegs m0 m' -> shz m' DOC 24.

Definition dd_W (usp DOC : Z) : list ivl := [(usp - 32, usp); (DOC, DOC + 24)].

Lemma dd_walk1 : forall (usp DOC tape sbuf lo : Z) (dcap : word)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x6cd000 <= lo -> usp < 2^63 -> 0 < DOC -> DOC + 24 <= lo -> 0 < sbuf < 2^64 ->
  shb_consts m -> doc_shz (dd_W usp DOC) m DOC ->
  rw_cells bsegs m DOC [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 dcap] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' : word) (j : list byte),
      ms = entry_st (Z_to_bv 64 0xb2114) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 DOC) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 sbuf) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_delarr m1
      /\ munch (dd_W usp DOC) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
      /\ rw_cells bsegs m1 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]
      /\ rw_cells bsegs m1 DOC [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 0); C8 dcap])
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DOC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_docdtor m).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO SB (G1 & G2) SHZ DOCC MI.
  unfold entry_st, e_docdtor, e_delarr, dd_W in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp); (DOC, DOC + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep. clear G1 G2. zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (DOC + 8) ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. lstep. zstep.
  if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| eassumption].
Qed.

Lemma dd_walk2 : forall (usp DOC tape lo : Z) (dcap : word) (j : list byte)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c s1c rac : word) F fc (m : mem),
  stk bsegs m lo (usp + -32) -> lo <= usp - 32 -> 0x6cd000 <= lo -> usp < 2^63 -> 0 < DOC -> DOC + 24 <= lo -> 0 < tape < 2^64 ->
  shz m DOC 24 ->
  rw_cells bsegs m (usp + -32) [CB 8 j; C8 s1c; C8 s0c; C8 rac] ->
  rw_cells bsegs m DOC [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 0); C8 dcap] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 tape) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_delarr m1
      /\ munch [(DOC, DOC + 24)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 dcap])
    (MS (mkR (Z_to_bv 64 0xb2114) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 DOC) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb2114) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO TP SHZ FR DOCC MI.
  unfold entry_st, e_delarr.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(DOC, DOC + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ DOC ltac:(lia)) as RD0.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. lstep. zstep.
  if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

Section DocDtor.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis DEL : del_cps RT e_delarr.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition docdtor_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (DOC tape sbuf nt ns : Z) (dcap : word) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 DOC -> tp = Z_to_bv 64 0x6ab368 ->
  fobj RT Σ m DOC 24 -> rw_cells bsegs m DOC [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 dcap] ->
  In (sbuf, ns) (rt_live RT Σ) -> In (tape, nt) (rt_live RT Σ) -> sbuf <> tape -> 0 <= ns -> 0 <= nt ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 32 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_docdtor m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) [(DOC, DOC + 24)] m m'
         /\ rw_cells bsegs m' DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 dcap] /\ fobj RT Σ' m' DOC 24) c
       /\ rt_live RT Σ' = live_remove tape (live_remove sbuf (rt_live RT Σ)) /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Theorem docdtor_ok : docdtor_cps.
Proof using AF DEL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m DOC tape sbuf nt ns dcap lo
    FDO MST -> -> FOBJ0 DOCC0 INS INT NEQ NS0 NT0 ART0 MI0 ST0 LOW LOR SPT SPA UOK FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (D8 & _ & (f & k & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f k ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_live_range RT AF Σ m sbuf ns ART0 INS) as (SB0 & SB1 & _).
  pose proof (af_live_range RT AF Σ m tape nt ART0 INT) as (TP0 & TP1 & _).
  assert (FPC : fp_client RT Σ lo (dd_W usp DOC)).
  { unfold dd_W. constructor; [left; cbn [fst snd]; ul|]. constructor; [| constructor].
    right; right. exists f, k. cbn [fst snd]. split; [exact INF| lia]. }
  assert (SHZ0 : doc_shz (dd_W usp DOC) m DOC).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)|].
    exact (fobj_munch RT AF Σ m m' lo _ DOC 24 ART0 LOW FPC MU FOBJ0). }

  pose proof (dd_walk1 usp DOC tape sbuf lo dcap ra gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(ul) (conj G1 G2) SHZ0 DOCC0 MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a1' & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & DOCC1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ DOC 24 ART0 LOW FPC MU1 FOBJ0) as FOBJ1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).

  apply (DEL Σ PMc (Z_to_bv 64 0xb2114) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6ab368) t0 t1 t2 (Z_to_bv 64 DOC) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 sbuf) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 sbuf ns lo FDO MST INS);
    try reflexivity; try assumption; [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -32) with (usp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - unfold unwind_ok. rewrite EU2, unsigned_lit by ul. left. ul.
  - intros c2 ((Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0xb2114) in Hc2' by lia.
    assert (FR2 : rw_cells bsegs m2 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_pres _ _ _ _ _ _ PRES2). pres_tac. }
    assert (DOCC2 : rw_cells bsegs m2 DOC [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 0); C8 dcap]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ DOCC1). apply (agree_of_pres _ _ _ _ _ _ PRES2). pres_tac. }
    pose proof (fobj_pres RT AF Σ Σ1 _ _ m1 m2 DOC 24 ART1 FOBJ1 PRES2 FRS1) as FOBJ2.
    assert (INF1 : In (f, k) (rt_frames RT Σ1)) by (rewrite FRS1; exact INF).
    assert (INT1 : In (tape, nt) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact INT| cbn [fst]; lia]).

    pose proof (dd_walk2 usp DOC tape lo dcap j gp (Z_to_bv 64 0x6ab368) u0 u1 u2 v1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 s1 ra F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(ul)
                  (fobj_shz RT AF Σ1 m2 DOC 24 ART2 FOBJ2) FR2 DOCC2 MI2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ST3 & DOCC3) & Hc3'). clear Hc3.
    assert (FPC3 : fp_client RT Σ1 lo [(DOC, DOC + 24)]).
    { constructor; [| constructor]. right; right. exists f, k. cbn [fst snd]. split; [exact INF1| lia]. }
    pose proof (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 ltac:(rewrite SP1; exact LOW) FPC3 MU3 WM3) as ART3.
    pose proof (fobj_munch RT AF Σ1 m2 m3 lo _ DOC 24 ART2 ltac:(rewrite SP1; exact LOW) FPC3 MU3 FOBJ2) as FOBJ3.

    rewrite <- ESP in Hc3'.
    apply (DEL Σ1 PMc ra sp gp (Z_to_bv 64 0x6ab368) u0 u1 u2 s0 s1 (Z_to_bv 64 tape) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6 F2 fc2 m3 tape nt lo FDO MST INT1); try reflexivity; try assumption;
      [.. | split; [exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
    + unfold call_ok. fold usp. rewrite SP1. split; [exact ST3|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA].
    + intros c4 ((Σ2 & v2 & Hc4 & LV2 & FRS2 & SP2 & CR2) & FC4).
      apply Hk. split; [| exact FC4]. exists Σ2, v2. split; [| split; [rewrite LV2, LV1; reflexivity| split; [rewrite FRS2, FRS1; reflexivity|
                                          split; [rewrite SP2, SP1; reflexivity| rewrite CR2, CR1; reflexivity]]]].
      eapply ASTA_conseq; [exact Hc4|]. intros ms (m4 & RS4 & AFT4 & PRES4). fold usp in AFT4, PRES4. exists m4.
      split; [exact RS4|]. split; [exact AFT4|].
      destruct AFT4 as (ART4 & MI4 & ST4).
      assert (SUB2 : forall e, In e (rt_live RT Σ2) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV2 in He; exact (live_remove_sub _ _ _ He)).
      assert (SUB1 : forall e, In e (rt_live RT Σ1) -> In e (rt_live RT Σ)) by (intros e He; rewrite LV1 in He; exact (live_remove_sub _ _ _ He)).
      split; [| split].
      * intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO & _).
        assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]).
        pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha0) as SPL.
        rewrite (PRES4 a), (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
        -- unfold dd_W. cbn [outside]. split; [ul|]. split; [exact HO| exact I].
        -- apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUB2| auto| lia].
        -- cbn [outside]. split; [exact HO| exact I].
        -- rewrite FRS1. exact Ha.
      * apply (rw_cells_agree_nw bsegs m3 m4 _ _ DOCC3). apply (agree_of_pres _ _ _ _ _ _ PRES4).
        intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right; right; left. exists f, k. split; [exact INF1| lia].
      * exact (fobj_pres RT AF Σ1 Σ2 _ _ m3 m4 DOC 24 ART3 FOBJ3 PRES4 FRS2).
Qed.

End DocDtor.

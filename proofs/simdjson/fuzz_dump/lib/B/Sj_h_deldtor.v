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
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_h_dtor.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_deldtor : Z := 0xe7388.

Definition dl_cells (vptr : word) (pre8 : list byte) (idx : word) (mid : list byte) (oc ia : word) (rest : list byte) : list cell :=
  [C8 vptr; CB 8 pre8; C8 idx; CB 32 mid; C8 oc; C8 ia; CB 24 rest].

Definition dl_shz (W : list ivl) (m0 : mem) (THIS : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono bsegs m0 m' -> shz m' THIS 96.

Definition dl_W (usp THIS : Z) : list ivl := [(usp - 32, usp); (THIS, THIS + 96)].

Lemma dl_walk1 : forall (usp THIS ia lo : Z) (vptr idx oc : word) (pre8 mid rest : list byte)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x6cd000 <= lo -> usp < 2^63 -> 0 < THIS -> THIS + 96 <= lo -> 0 < ia < 2^64 ->
  shb_consts m -> dl_shz (dl_W usp THIS) m THIS ->
  rw_cells bsegs m THIS (dl_cells vptr pre8 idx mid oc (Z_to_bv 64 ia) rest) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' : word) (j : list byte),
      ms = entry_st (Z_to_bv 64 0xe73d0) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 ia) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_delarr m1
      /\ munch (dl_W usp THIS) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
      /\ rw_cells bsegs m1 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]
      /\ rw_cells bsegs m1 THIS (dl_cells vptr pre8 idx mid oc (Z_to_bv 64 0) rest))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_deldtor m).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO SB (G1 & G2) SHZ THC MI.
  unfold entry_st, e_deldtor, e_delarr, dl_W, dl_cells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp); (THIS, THIS + 96)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep. clear G1 G2. zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (THIS + 64) ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. lstep. zstep.
  if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| eassumption].
Qed.

Lemma dl_walk2 : forall (usp THIS oc lo : Z) (vptr idx : word) (pre8 mid rest : list byte)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  lo <= usp - 32 -> 0x6cd000 <= lo -> usp < 2^63 -> 0 < THIS -> THIS + 96 <= lo -> 0 < oc < 2^64 ->
  shz m THIS 96 ->
  rw_cells bsegs m THIS (dl_cells vptr pre8 idx mid (Z_to_bv 64 oc) (Z_to_bv 64 0) rest) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' : word),
      ms = entry_st (Z_to_bv 64 0xe73f8) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 oc) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_delarr m1
      /\ munch [(THIS, THIS + 96)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 THIS (dl_cells vptr pre8 idx mid (Z_to_bv 64 0) (Z_to_bv 64 0) rest))
    (MS (mkR (Z_to_bv 64 0xe73d0) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe73d0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LO GLO SPH D0 DLO OCP SHZ THC MI.
  unfold entry_st, e_delarr, dl_cells in *.
  pose proof (munch_refl [(THIS, THIS + 96)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ (THIS + 56) ltac:(lia)) as RD0.
  zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. lstep. zstep.
  if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.

Lemma dl_walk3 : forall (usp THIS idx lo : Z) (vptr : word) (pre8 mid rest : list byte)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  lo <= usp - 32 -> 0x6cd000 <= lo -> usp < 2^63 -> 0 < THIS -> THIS + 96 <= lo -> 0 < idx < 2^64 ->
  dl_shz [(THIS, THIS + 96)] m THIS ->
  rw_cells bsegs m THIS (dl_cells vptr pre8 (Z_to_bv 64 idx) mid (Z_to_bv 64 0) (Z_to_bv 64 0) rest) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' : word),
      ms = entry_st (Z_to_bv 64 0xe743c) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 idx) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_delarr m1
      /\ munch [(THIS, THIS + 96)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 THIS (dl_cells (Z_to_bv 64 0x168b98) pre8 (Z_to_bv 64 0) mid (Z_to_bv 64 0) (Z_to_bv 64 0) rest))
    (MS (mkR (Z_to_bv 64 0xe73f8) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe73f8) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LO GLO SPH D0 DLO IXP SHZ THC MI.
  unfold entry_st, e_delarr, dl_cells in *.
  pose proof (munch_refl [(THIS, THIS + 96)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ m MU WM THIS ltac:(lia)) as RD0.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. lstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (THIS + 16) ltac:(lia)) as RD1 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. lstep. zstep.
  if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.

Lemma dl_walk4 : forall (usp THIS lo : Z) (j : list byte)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c s1c rac : word) F fc (m : mem),
  stk bsegs m lo (usp + -32) -> lo <= usp - 32 -> 0x6cd000 <= lo -> usp < 2^63 -> 0 < THIS < 2^63 ->
  rw_cells bsegs m (usp + -32) [CB 8 j; C8 s1c; C8 s0c; C8 rac] -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = entry_st rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 THIS) (Z_to_bv 64 96) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_del m
      /\ stk bsegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xe743c) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe743c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH TH FR MI.
  unfold entry_st, e_del.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. split; [cbv delta [mkR]; reflexivity| exact ST].
Qed.

Section DelDtor.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis DEL1 : del_cps RT e_del.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition deldtor_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (THIS idx oc ia nidx noc nia : Z) (vptr : word) (pre8 mid rest : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 THIS -> tp = Z_to_bv 64 0x6ab368 ->
  In (THIS, 96) (rt_live RT Σ) -> THIS mod 8 = 0 ->
  rw_cells bsegs m THIS (dl_cells vptr pre8 (Z_to_bv 64 idx) mid (Z_to_bv 64 oc) (Z_to_bv 64 ia) rest) ->
  In (ia, nia) (rt_live RT Σ) -> In (oc, noc) (rt_live RT Σ) -> In (idx, nidx) (rt_live RT Σ) ->
  ia <> oc -> ia <> idx -> ia <> THIS -> oc <> idx -> oc <> THIS -> idx <> THIS -> 0 <= nia -> 0 <= noc -> 0 <= nidx ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 32 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_deldtor m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) [] m m') c
       /\ rt_live RT Σ' = live_remove THIS (live_remove idx (live_remove oc (live_remove ia (rt_live RT Σ))))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Theorem deldtor_ok : deldtor_cps.
Proof using AF DELA DEL1.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    THIS idx oc ia nidx noc nia vptr pre8 mid rest lo
    FDO MST -> -> INT T8 TH0 INA INO INI N1 N2 N3 N4 N5 N6 NA0 NO0 NI0 ART0 MI0 ST0 LOW LOR SPT SPA UOK FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_live_range RT AF Σ m THIS 96 ART0 INT) as (TP0 & TP1 & _).
  pose proof (af_live_range RT AF Σ m ia nia ART0 INA) as (IA0 & IA1 & _).
  pose proof (af_live_range RT AF Σ m oc noc ART0 INO) as (OC0 & OC1 & _).
  pose proof (af_live_range RT AF Σ m idx nidx ART0 INI) as (IX0 & IX1 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (FPT : forall Σx, In (THIS, 96) (rt_live RT Σx) -> fp_client RT Σx lo [(THIS, THIS + 96)]).
  { intros Σx Hin. constructor; [| constructor]. right; left. exists THIS, 96. cbn [fst snd]. split; [exact Hin| lia]. }
  assert (FPW : fp_client RT Σ lo (dl_W usp THIS)).
  { unfold dl_W. constructor; [left; cbn [fst snd]; ul|]. exact (FPT Σ INT). }
  assert (SHZ0 : dl_shz (dl_W usp THIS) m THIS).
  { intros m' MU WM. exact (shz_live RT AF Σ m' THIS 96 (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPW MU WM) INT T8). }

  pose proof (dl_walk1 usp THIS ia lo vptr (Z_to_bv 64 idx) (Z_to_bv 64 oc) pre8 mid rest ra gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) ltac:(ul) (conj G1 G2) SHZ0 TH0 MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a1' & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & TH1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPW MU1 WM1) as ART1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -32) mod 16 = 0) by (replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  assert (EUT : bv_unsigned (Z_to_bv 64 THIS) = THIS) by (apply unsigned_lit; ul).

  apply (DELA Σ PMc (Z_to_bv 64 0xe73d0) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6ab368) t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 ia) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 ia nia lo FDO MST INA);
    try reflexivity; try assumption; [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA2].
  - unfold unwind_ok. rewrite EU2, EUT. left. ul.
  - intros c2 ((Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0xe73d0) in Hc2' by lia.
    assert (INT1 : In (THIS, 96) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact INT| cbn [fst]; lia]).
    assert (INO1 : In (oc, noc) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact INO| cbn [fst]; lia]).
    assert (INI1 : In (idx, nidx) (rt_live RT Σ1)) by (rewrite LV1; apply live_remove_keep; [exact INI| cbn [fst]; lia]).
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (FR2 : rw_cells bsegs m2 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_pres _ _ _ _ _ _ PRES2). pres_tac. }
    assert (TH2 : rw_cells bsegs m2 THIS (dl_cells vptr pre8 (Z_to_bv 64 idx) mid (Z_to_bv 64 oc) (Z_to_bv 64 0) rest)).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ TH1). apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. unfold dl_cells in Hx. cbn [cells_size csize Nat.add] in Hx. right; right; left. exists THIS, 96. split; [exact INT1| lia]. }

    pose proof (dl_walk2 usp THIS oc lo vptr (Z_to_bv 64 idx) pre8 mid rest gp (Z_to_bv 64 0x6ab368) u0 u1 u2 v1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 F2 fc2 m2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) ltac:(ul)
                  (shz_live RT AF Σ1 m2 THIS 96 ART2 INT1 T8) TH2 MI2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & a1'' & -> & MU3 & WM3 & MI3 & TH3) & Hc3'). clear Hc3.
    pose proof (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 LOW1 (FPT Σ1 INT1) MU3 WM3) as ART3.
    assert (AG23 : agree_on (fun x => ~ (THIS <= x < THIS + 96)) m2 m3).
    { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
    assert (FR3 : rw_cells bsegs m3 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx.
      cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
    assert (ST3 : stk bsegs m3 lo (usp + -32)).
    { apply (stk_agree bsegs m2 m3 _ _ ST2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbv beta in *. ul. }

    apply (DELA Σ1 PMc (Z_to_bv 64 0xe73f8) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6ab368) u0 u1 u2 (Z_to_bv 64 THIS) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 oc) a1'' b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 oc noc lo FDO MST INO1);
      try reflexivity; try assumption; [.. | split; [exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
    + unfold call_ok. rewrite EU2, SP1. split; [exact ST3|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA2].
    + unfold unwind_ok. rewrite EU2, EUT. left. ul.
    + intros c4 ((Σ2 & v2 & Hc4 & LV2 & FRS2 & SP2 & CR2) & FC4).
      destruct (ASTA_unpack_f RT Σ2 _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4) & FRM4 & Hc4'). clear Hc4.
      destruct RS4 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
      cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4.
      rewrite (ret_pc_even 0xe73f8) in Hc4' by lia.
      assert (INT2 : In (THIS, 96) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact INT1| cbn [fst]; lia]).
      assert (INI2 : In (idx, nidx) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact INI1| cbn [fst]; lia]).
      assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2, SP1; exact LOW).
      assert (FR4 : rw_cells bsegs m4 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
      { apply (rw_cells_agree_nw bsegs m3 m4 _ _ FR3). apply (agree_of_pres _ _ _ _ _ _ PRES4). pres_tac. }
      assert (TH4 : rw_cells bsegs m4 THIS (dl_cells vptr pre8 (Z_to_bv 64 idx) mid (Z_to_bv 64 0) (Z_to_bv 64 0) rest)).
      { apply (rw_cells_agree_nw bsegs m3 m4 _ _ TH3). apply (agree_of_pres _ _ _ _ _ _ PRES4).
        intros x Hx. unfold dl_cells in Hx. cbn [cells_size csize Nat.add] in Hx. right; right; left. exists THIS, 96. split; [exact INT2| lia]. }
      assert (SHZ4 : dl_shz [(THIS, THIS + 96)] m4 THIS).
      { intros m' MU WM. exact (shz_live RT AF Σ2 m' THIS 96 (art_fp_client RT AF Σ2 m4 m' lo _ ART4 LOW2 (FPT Σ2 INT2) MU WM) INT2 T8). }

      pose proof (dl_walk3 usp THIS idx lo vptr pre8 mid rest gp (Z_to_bv 64 0x6ab368) w0 w1 w2 v2 d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    w3 w4 w5 w6 F4 fc4 m4 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) ltac:(ul) SHZ4 TH4 MI4) as W3.
      lazymatch type of W3 with evt bsegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes bsegs _ _ _ c4 (asta_evt_c RT AF Σ2 PMc _ _ MST W3') Hc4'). clear W3'. intros c5 Hc5.
      destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & a1t & -> & MU5 & WM5 & MI5 & TH5) & Hc5'). clear Hc5.
      pose proof (art_fp_client RT AF Σ2 m4 m5 lo _ ART4 LOW2 (FPT Σ2 INT2) MU5 WM5) as ART5.
      assert (AG45 : agree_on (fun x => ~ (THIS <= x < THIS + 96)) m4 m5).
      { apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
      assert (FR5 : rw_cells bsegs m5 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
      { apply (rw_cells_agree bsegs m4 m5 _ _ FR4); [| exact WM5]. eapply agree_sub; [exact AG45|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (ST5 : stk bsegs m5 lo (usp + -32)).
      { apply (stk_agree bsegs m4 m5 _ _ ST4); [| exact WM5]. eapply agree_sub; [exact AG45|]. intros x Hx. cbv beta in *. ul. }

      apply (DELA Σ2 PMc (Z_to_bv 64 0xe743c) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6ab368) w0 w1 w2 (Z_to_bv 64 THIS) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 idx) a1t d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m5 idx nidx lo FDO MST INI2);
        try reflexivity; try assumption; [.. | split; [exact Hc5'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c5 Hc5'); intros ms0 <-; exact FRM4] |].
      * unfold call_ok. rewrite EU2, SP2, SP1. split; [exact ST5|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA2].
      * unfold unwind_ok. rewrite EU2, EUT. left. ul.
      * intros c6 ((Σ3 & v3 & Hc6 & LV3 & FRS3 & SP3 & CR3) & FC6).
        destruct (ASTA_unpack_f RT Σ3 _ _ c6 Hc6 FC6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & ST6) & PRES6) & FRM6 & Hc6'). clear Hc6.
        destruct RS6 as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F6 & fc6 & ->).
        cbn [ms_fcsr] in FRM6. rewrite EU2 in ST6, PRES6.
        rewrite (ret_pc_even 0xe743c) in Hc6' by lia.
        assert (INT3 : In (THIS, 96) (rt_live RT Σ3)) by (rewrite LV3; apply live_remove_keep; [exact INT2| cbn [fst]; lia]).
        assert (FR6 : rw_cells bsegs m6 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
        { apply (rw_cells_agree_nw bsegs m5 m6 _ _ FR5). apply (agree_of_pres _ _ _ _ _ _ PRES6). pres_tac. }

        pose proof (dl_walk4 usp THIS lo j gp (Z_to_bv 64 0x6ab368) y0 y1 y2 v3 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      y3 y4 y5 y6 s0 s1 ra F6 fc6 m6 ST6 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) FR6 MI6) as W4.
        lazymatch type of W4 with evt bsegs _ ?X =>
          assert (W4' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W4) end.
        clear W4.
        apply (cps_realizes bsegs _ _ _ c6 (asta_evt_c RT AF Σ3 PMc _ _ MST W4') Hc6'). clear W4'. intros c7 Hc7.
        destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (-> & ST7) & Hc7'). clear Hc7.

        rewrite <- ESP in Hc7'.
        apply (DEL1 Σ3 PMc ra sp gp (Z_to_bv 64 0x6ab368) y0 y1 y2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 96) e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 y3 y4 y5 y6 F6 fc6 m6 THIS 96 lo FDO MST INT3); try reflexivity; try assumption;
          [.. | split; [exact Hc7'| apply (cfrm0_of_asta RT Σ3 PMc (eq _) c7 Hc7'); intros ms0 <-; exact FRM6] |].
        -- unfold call_ok. fold usp. rewrite SP3, SP2, SP1. split; [exact ST7|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA].
        -- intros c8 ((Σ4 & v4 & Hc8 & LV4 & FRS4 & SP4 & CR4) & FC8).
           apply Hk. split; [| exact FC8]. exists Σ4, v4.
           split; [| split; [rewrite LV4, LV3, LV2, LV1; reflexivity| split; [rewrite FRS4, FRS3, FRS2, FRS1; reflexivity|
                      split; [rewrite SP4, SP3, SP2, SP1; reflexivity| rewrite CR4, CR3, CR2, CR1; reflexivity]]]].
           eapply ASTA_conseq; [exact Hc8|]. intros ms (m8 & RS8 & AFT8 & PRES8). fold usp in AFT8, PRES8. exists m8.
           split; [exact RS8|]. split; [exact AFT8|].
           assert (SUB4 : forall e, In e (rt_live RT Σ4) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV4 in He; exact (live_remove_sub _ _ _ He)).
           assert (SUB3 : forall e, In e (rt_live RT Σ3) -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV3 in He; exact (live_remove_sub _ _ _ He)).
           assert (SUB2 : forall e, In e (rt_live RT Σ2) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV2 in He; exact (live_remove_sub _ _ _ He)).
           assert (SUB1 : forall e, In e (rt_live RT Σ1) -> In e (rt_live RT Σ)) by (intros e He; rewrite LV1 in He; exact (live_remove_sub _ _ _ He)).
           intros a Ha _.
           assert (NT : ~ (THIS <= bv_unsigned a < THIS + 96)).
           { apply (freed_apart RT AF Σ m THIS 96 (rt_live RT Σ4) usp (bv_unsigned a) ART0 INT ltac:(lia)); [| ul | exact Ha].
             intros e He. split; [exact (SUB1 _ (SUB2 _ (SUB3 _ (SUB4 _ He))))|]. rewrite LV4 in He. exact (live_remove_neq _ _ _ He). }
           assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]).
           pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha0) as SPL.
           rewrite (PRES8 a), (PRES6 a), (MU5 a), (PRES4 a), (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | | | | |].
           ++ unfold dl_W. cbn [outside]. split; [ul|]. split; [exact NT| exact I].
           ++ apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (SUB2 _ (SUB3 _ (SUB4 _ He)))| auto| lia].
           ++ cbn [outside]. split; [exact NT| exact I].
           ++ rewrite FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (SUB3 _ (SUB4 _ He))| auto| lia].
           ++ cbn [outside]. split; [exact NT| exact I].
           ++ rewrite FRS2, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUB4| auto| lia].
           ++ rewrite FRS3, FRS2, FRS1. exact Ha.
Qed.

End DelDtor.

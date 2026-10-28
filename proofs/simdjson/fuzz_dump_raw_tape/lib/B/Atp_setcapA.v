(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_h_dtor Sj_h_alloc Atp_fzwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_setcap : Z := 0xe7338.
Definition sc_idx (cap : Z) : Z := 4 * (roundup64 cap + 9).

Definition impl_cells (vptr nsi : word) (p12 : list byte) (idx : word) (p24 : list byte) (cap : word) (rest : list byte) : list cell :=
  [C8 vptr; C4 nsi; CB 4 p12; C8 idx; CB 8 p24; C8 cap; CB 56 rest].

Definition sc_frame (ra s0 s1 s2 s3 s4 : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma sc_walk1 : forall (usp THIS cap lo : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 48 -> 0x6ce000 <= lo -> usp < 2^63 -> 0 < THIS < 2^63 -> 0 <= cap < 2^32 ->
  shb_consts m -> cli_got_nothrow m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a2' : word),
      ms = entry_st (Z_to_bv 64 0xe73a0) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 cap) (Z_to_bv 64 THIS)
             (Z_to_bv 64 (sc_idx cap)) (Z_to_bv 64 0x2d450) a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_newarr_nt m1
      /\ munch [(usp - 48, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -48)
      /\ rw_cells bsegs m1 (usp + -48) (sc_frame ra s0 s1 s2 s3 s4))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 cap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_setcap m).
Proof.
  intros until m. intros ST LO GLO SPH T0 C0 (G1 & G2) GN MI.
  unfold entry_st, e_setcap, e_newarr_nt, sc_frame, sc_idx, cli_got_nothrow in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 48, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  do 6 zstep. zstep. zstep.
  assert (SH : Z.shiftr cap 32 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  rewrite SH. zstep. if_true.
  do 11 zstep.
  change 18446744073709551616 with (2 ^ 64). rewrite <- (Z.land_ones _ 64) by lia. change (Z.ones 64) with 18446744073709551615.
  rewrite (idx_size_eq cap) by lia.
  zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Definition sc_shz (W : list ivl) (m0 : mem) (THIS p : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono bsegs m0 m' -> shz m' THIS 96 /\ shz m' p 8.

Lemma sc_walk2 : forall (usp THIS cap p lo : Z) (vptr nsi cap0 : word) (p12 p24 rest jp : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rac s0c s1c s2c s3c s4c : word) F fc (m : mem),
  stk bsegs m lo (usp + -48) -> lo <= usp - 48 -> 0x6ce000 <= lo -> usp < 2^63 ->
  0 < THIS -> THIS + 96 <= lo -> 0 < p -> p + 4 <= lo -> (THIS + 96 <= p \/ p + 4 <= THIS) -> 0 <= cap < 2^32 ->
  sc_shz [(usp - 48, usp); (THIS, THIS + 96); (p, p + 4)] m THIS p -> p mod 16 = 0 ->
  rw_cells bsegs m (usp + -48) (sc_frame rac s0c s1c s2c s3c s4c) ->
  rw_cells bsegs m THIS (impl_cells vptr nsi p12 (Z_to_bv 64 0) p24 cap0 rest) -> rw_cells bsegs m p [CB 4 jp] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
      /\ ms_fcsr ms = fc /\ munch [(usp - 48, usp); (THIS, THIS + 96); (p, p + 4)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' THIS (impl_cells vptr (Z_to_bv 64 0) p12 (Z_to_bv 64 p) p24 (Z_to_bv 64 cap) rest)
      /\ rw_cells bsegs m' p [C4 (Z_to_bv 64 0)])
    (MS (mkR (Z_to_bv 64 0xe73a0) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 cap) (Z_to_bv 64 THIS) (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 2147450880) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe73a0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH T0 TLO P0 PLO SEP C0 SHZ P16 FR TH PC MI.
  unfold sc_frame, impl_cells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 48, usp); (THIS, THIS + 96); (p, p + 4)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  pose proof (proj1 (SHZ m MU WM) (THIS + 16) ltac:(lia)) as RD0.
  zstep. rewrite (land3_aligned p) by (first [lia| exact P16]). zstep. if_false.
  zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_true.
  zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep. rewrite (land3_aligned p) by (first [lia| exact P16]). zstep. if_false.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (proj2 (SHZ mm MU' WM') p ltac:(lia)) as RD1 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (proj1 (SHZ mm MU' WM') (THIS + 8) ltac:(lia)) as RD2 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (proj1 (SHZ mm MU' WM') (THIS + 32) ltac:(lia)) as RD3 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  do 6 zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; eassumption.
Qed.

Lemma sc_idx_bounds : forall cap, 0 <= cap <= 2^26 -> 36 <= sc_idx cap <= 0x20001000.
Proof. intros cap H. unfold sc_idx, roundup64. change (2^26) with 67108864 in H. Z.div_mod_to_equations. lia. Qed.

Section SetcapCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition setcap_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (THIS cap : Z) (vptr nsi cap0 : word) (p12 p24 rest : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 cap -> tp = Z_to_bv 64 0x6abde8 ->
  0 <= cap <= 2^26 ->
  In (THIS, 96) (rt_live RT Σ) -> THIS mod 8 = 0 -> rw_cells bsegs m THIS (impl_cells vptr nsi p12 (Z_to_bv 64 0) p24 cap0 rest) ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (sc_idx cap) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 80 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                       t3 t4 t5 t6 F fc e_setcap m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(THIS, THIS + 96)] m m'
         /\ rw_cells bsegs m' THIS (impl_cells vptr (Z_to_bv 64 0) p12 (Z_to_bv 64 p) p24 (Z_to_bv 64 cap) rest)
         /\ wr_at bsegs m' p (sc_idx cap)) c
       /\ rt_live RT Σ' = (p, sc_idx cap) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (sc_idx cap) /\ 0 < p /\ p mod 16 = 0).

Theorem setcap_ok : setcap_cps.
Proof using AF NEWA AFC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m THIS cap vptr nsi cap0 p12 p24 rest lo
    FDO MST -> -> -> CAP INT T8 TH0 LVB CR0 ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (sc_idx_bounds cap CAP) as IXB.
  pose proof (af_live_range RT AF Σ m THIS 96 ART0 INT) as (TP0 & TP1 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (FP1 : fp_client RT Σ lo [(usp - 48, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).

  pose proof (sc_walk1 usp THIS cap lo ra gp (Z_to_bv 64 0x6abde8) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(change (2^26) with 67108864 in CAP; lia) (conj G1 G2) (AFC Σ m ART0) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a2' & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FP1 MU1 WM1) as ART1.
  assert (TH1 : rw_cells bsegs m1 THIS (impl_cells vptr nsi p12 (Z_to_bv 64 0) p24 cap0 rest)).
  { apply (rw_cells_agree bsegs m m1 _ _ TH0); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1).
    intros x Hx. unfold impl_cells in Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I]. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -48) mod 16 = 0) by (replace (usp + -48) with (usp + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  apply (NEWA Σ PMc (Z_to_bv 64 0xe73a0) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0x6abde8) t0 t1 t2 (Z_to_bv 64 cap) (Z_to_bv 64 THIS)
           (Z_to_bv 64 (sc_idx cap)) (Z_to_bv 64 0x2d450) a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m1 (sc_idx cap) lo FDO MST); try reflexivity; try assumption;
    [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - lia.
  - rewrite EU2. exact ST1.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact SPA2.
  - intros c2 ((Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PTOP) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRP & _) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xe73a0) in Hc2' by lia.
    assert (INP1 : In (p, sc_idx cap) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
    assert (INT1 : In (THIS, 96) (rt_live RT Σ1)) by (rewrite LV1; right; exact INT).
    pose proof (af_live_range RT AF Σ1 m2 p _ ART2 INP1) as (_ & PR1 & _). rewrite SP1 in PR1.
    assert (SEP : THIS + 96 <= p \/ p + 4 <= THIS).
    { destruct (af_live_disj RT AF Σ1 m2 p (sc_idx cap) THIS 96 [] (rt_live RT Σ) ART2 LV1 INT); lia. }
    assert (FR2 : rw_cells bsegs m2 (usp + -48) (sc_frame ra s0 s1 s2 s3 s4)).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). unfold sc_frame. pres_tac. }
    assert (TH2 : rw_cells bsegs m2 THIS (impl_cells vptr nsi p12 (Z_to_bv 64 0) p24 cap0 rest)).
    { apply (rw_cells_agree bsegs m1 m2 _ _ TH1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). unfold impl_cells. pres_tac. }
    destruct (wr_at_rw_CB m2 p 4 (wr_at_sub m2 p (sc_idx cap) p 4 WRP ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jp & PC2).
    change (Z.to_nat 4) with 4%nat in PC2.
    assert (FPW : fp_client RT Σ1 lo [(usp - 48, usp); (THIS, THIS + 96); (p, p + 4)]).
    { constructor; [left; cbn [fst snd]; ul|]. constructor; [right; left; exists THIS, 96; cbn [fst snd]; split; [exact INT1| lia]|].
      constructor; [right; left; exists p, (sc_idx cap); cbn [fst snd]; split; [exact INP1| lia]| constructor]. }
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (SHZ2 : sc_shz [(usp - 48, usp); (THIS, THIS + 96); (p, p + 4)] m2 THIS p).
    { intros m' MU WM. pose proof (art_fp_client RT AF Σ1 m2 m' lo _ ART2 LOW1 FPW MU WM) as ART'. split.
      - exact (shz_live RT AF Σ1 m' THIS 96 ART' INT1 T8).
      - eapply shz_sub; [exact (shz_live RT AF Σ1 m' p _ ART' INP1 ltac:(Z.div_mod_to_equations; lia))| lia|].
        pose proof (Z.div_mod (sc_idx cap) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sc_idx cap) 8 ltac:(lia)). lia. }
    pose proof (sc_walk2 usp THIS cap p lo vptr nsi cap0 p12 p24 rest jp gp (Z_to_bv 64 0x6abde8) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 ra s0 s1 s2 s3 s4 F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) TP0 ltac:(ul) P0 ltac:(ul) SEP
                  ltac:(change (2^26) with 67108864 in CAP; lia) SHZ2 P16 FR2 TH2 PC2 MI2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c3 Hc3); intros ms (m3 & _ & E3 & _); rewrite E3; exact FRM2].
    exists Σ1, p.
    split; [| split; [exact LV1| split; [exact FRS1| split; [exact SP1| split; [exact CR1| split; assumption]]]]].
    eapply ASTA_conseq; [exact Hc3|]. intros ms (m3 & RS3 & _ & MU3 & WM3 & MI3 & ST3 & TH3 & _). exists m3.
    split; [rewrite ESP; exact RS3|].
    split; [split; [exact (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 LOW1 FPW MU3 WM3)| split; [exact MI3| split; [| exact ST3]]]|].
    { exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)). }
    split; [| split; [exact TH3| exact (wr_at_transport bsegs m2 m3 _ _ WRP WM3)]].
    intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO & _).
    pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    assert (NP : ~ (p <= bv_unsigned a < p + 4)).
    { intros Hp. destruct Ha as [H|[H|[H|[H|H]]]].
      - ul.
      - pose proof (client_static_range _ H). pose proof (af_live_range RT AF Σ1 m2 p _ ART2 INP1) as (_ & _ & [X|X]); unfold SEGTOP_A in *; lia.
      - destruct H as (q & n & Hin & Hq). destruct (af_live_disj RT AF Σ1 m2 p (sc_idx cap) q n [] (rt_live RT Σ) ART2 LV1 Hin); lia.
      - destruct H as (f & k & Hin & Hf). rewrite <- FRS1 in Hin.
        pose proof (af_frames_range RT AF Σ1 m2 f k ART2 Hin) as (_ & _ & _ & X). destruct (X p _ INP1); lia.
      - destruct H as (f & k & Hin & Hf). rewrite <- FRS1 in Hin.
        pose proof (proj1 (af_fshadow_apart RT AF Σ1 m2 f k ART2 Hin) p _ INP1) as X. lia. }
    rewrite (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | |].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
    + cbn [outside]. split; [ul|]. split; [exact HO|]. split; [exact NP| exact I].
Qed.

End SetcapCPS.

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
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_h_dtor.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_allocate : Z := 0xafe94.

Definition cli_got_nothrow (m : mem) : Prop := ro_cells bsegs m 0x16f428 [C8 (Z_to_bv 64 0x2d450)].

Definition al_sbuf (cap : Z) : Z := roundup64 (5 * (cap / 3) + 64).
Definition al_tape (cap : Z) : Z := 8 * roundup64 (cap + 3).

Definition al_frame (ra s0 s1 s2 s3 s4 s5 : word) (j : list byte) : list cell := [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma al_walk1 : forall (usp DOC cap lo : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 64 -> 0x6ce000 <= lo -> usp < 2^63 -> 0 < DOC < 2^63 -> 0 < cap < 2^32 ->
  shb_consts m -> cli_got_nothrow m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (j : list byte),
      ms = entry_st (Z_to_bv 64 0xaff7c) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 DOC) (Z_to_bv 64 cap)
             (Z_to_bv 64 (al_sbuf cap)) (Z_to_bv 64 0x2d450) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (DOC + 8)) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_newarr_nt m1
      /\ munch [(usp - 64, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -64)
      /\ rw_cells bsegs m1 (usp + -64) (al_frame ra s0 s1 s2 s3 s4 s5 j))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DOC) (Z_to_bv 64 cap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_allocate m).
Proof.
  intros until m. intros ST LO GLO SPH D0 C0 (G1 & G2) GN MI.
  unfold entry_st, e_allocate, e_newarr_nt, al_frame, al_sbuf, cli_got_nothrow in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  do 7 zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
  zstep. zstep.
  assert (SH : Z.shiftr cap 32 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  rewrite SH. if_true.
  do 10 zstep.
  change 18446744073709551616 with (2 ^ 64). rewrite <- (Z.land_ones _ 64) by lia. change (Z.ones 64) with 18446744073709551615.
  rewrite (sbuf_size_eq cap) by lia.
  zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma al_walk2 : forall (DOC cap sbuf sp' : Z) (dcap : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6ce000 <= DOC < 2^63 -> 0 < cap < 2^32 -> 0 <= sbuf < 2^64 ->
  shz m DOC 24 -> cli_got_nothrow m ->
  rw_cells bsegs m DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 dcap] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a2' : word),
      ms = entry_st (Z_to_bv 64 0xaffc4) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 DOC) (Z_to_bv 64 cap)
             (Z_to_bv 64 (al_tape cap)) (Z_to_bv 64 0x2d450) a2' a3 a4 a5 a6 a7 (Z_to_bv 64 (DOC + 8)) (Z_to_bv 64 ((DOC + 8) / 8 + 2147450880))
             (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_newarr_nt m1
      /\ munch [(DOC, DOC + 24)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 sbuf); C8 dcap])
    (MS (mkR (Z_to_bv 64 0xaff7c) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 DOC) (Z_to_bv 64 cap) (Z_to_bv 64 sbuf) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (DOC + 8)) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xaff7c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros D0 C0 SB SHZ GN DOCC MI.
  unfold entry_st, e_newarr_nt, al_tape, cli_got_nothrow in *.
  pose proof (munch_refl [(DOC, DOC + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ (DOC + 8) ltac:(lia)) as RD0.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. if_true.
  do 6 zstep.
  change 18446744073709551616 with (2 ^ 64). rewrite <- (Z.land_ones _ 64) by lia. change (Z.ones 64) with 18446744073709551615.
  rewrite (tape_size_eq cap) by lia.
  zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma al_walk3 : forall (usp DOC cap sbuf tape lo : Z) (dcap : word) (j : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rac s0c s1c s2c s3c s4c s5c : word) F fc (m : mem),
  stk bsegs m lo (usp + -64) -> lo <= usp - 64 -> 0x6ce000 <= lo -> usp < 2^63 ->
  0x6ce000 <= DOC -> DOC + 24 <= lo -> 0 < cap < 2^32 -> 0 < sbuf < 2^64 -> 0 < tape < 2^64 -> tape mod 16 = 0 ->
  doc_shz [(usp - 64, usp); (DOC, DOC + 24)] m DOC ->
  rw_cells bsegs m (usp + -64) (al_frame rac s0c s1c s2c s3c s4c s5c j) ->
  rw_cells bsegs m DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 sbuf); C8 dcap] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
      /\ ms_fcsr ms = fc /\ munch [(usp - 64, usp); (DOC, DOC + 24)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' DOC [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap)])
    (MS (mkR (Z_to_bv 64 0xaffc4) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 DOC) (Z_to_bv 64 cap) (Z_to_bv 64 tape) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (DOC + 8)) (Z_to_bv 64 ((DOC + 8) / 8 + 2147450880)) (Z_to_bv 64 2147450880) s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xaffc4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO C0 SB TP TP16 SHZ FR DOCC MI.
  unfold al_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 64, usp); (DOC, DOC + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUT : bv_unsigned (Z_to_bv 64 tape) = tape) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 sbuf) = sbuf) by (apply unsigned_lit; lia).
  pose proof (SHZ m MU WM DOC ltac:(lia)) as RD0.

  zstep. rewrite (land7_aligned tape) by (first [lia| exact TP16]). zstep. if_false.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_true.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' (DOC + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' DOC ltac:(lia)) as RD2;
    pose proof (SHZ mm MU' WM' (DOC + 16) ltac:(lia)) as RD3 end.
  zstep. shz_norm. zstep. if_false. zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep. shz_norm. zstep. if_false. zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep.
  zstep. do 7 zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

Lemma al_sbuf_bounds : forall cap, 32 <= cap <= 2^26 -> 64 <= al_sbuf cap <= 0x20001000.
Proof. intros cap H. unfold al_sbuf, roundup64. change (2^26) with 67108864 in H. Z.div_mod_to_equations. lia. Qed.
Lemma al_tape_bounds : forall cap, 32 <= cap <= 2^26 -> 64 <= al_tape cap <= 0x20001000.
Proof. intros cap H. unfold al_tape, roundup64. change (2^26) with 67108864 in H. Z.div_mod_to_equations. lia. Qed.

Lemma mcost_nonneg : forall n, 0 <= n -> 0 <= mcost n.
Proof. intros n H. unfold mcost, DCOST. destruct (n <=? 64512); lia. Qed.

Section AllocCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition allocate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (DOC cap : Z) (dcap : word) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 DOC -> a1 = Z_to_bv 64 cap -> tp = Z_to_bv 64 0x6abde8 ->
  32 <= cap <= 2^26 ->
  fobj RT Σ m DOC 24 -> rw_cells bsegs m DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 dcap] ->
  Z.of_nat (length (rt_live RT Σ)) + 2 <= LIVE_MAX -> mcost (al_sbuf cap) + mcost (al_tape cap) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 96 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                       t3 t4 t5 t6 F fc e_allocate m)))
    (fun c => exists (Σ' : rts RT) (sbuf tape : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(DOC, DOC + 24)] m m'
         /\ rw_cells bsegs m' DOC [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap)] /\ fobj RT Σ' m' DOC 24) c
       /\ rt_live RT Σ' = (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (al_sbuf cap) - mcost (al_tape cap)
       /\ 0 < sbuf /\ sbuf mod 16 = 0 /\ 0 < tape /\ tape mod 16 = 0).

Theorem allocate_ok : allocate_cps.
Proof using AF NEWA AFC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m DOC cap dcap lo
    FDO MST -> -> -> CAP FOBJ0 DOCC0 LVB CR0 ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (al_sbuf_bounds cap CAP) as SBB. pose proof (al_tape_bounds cap CAP) as TPB.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (D8 & _ & (f & k & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f k ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_align RT AF Σ m f k ART0 INF) as (_ & FSEG).
  assert (FPS : forall Σx, rt_frames RT Σx = rt_frames RT Σ -> fp_client RT Σx lo [(usp - 64, usp); (DOC, DOC + 24)]).
  { intros Σx E. constructor; [left; cbn [fst snd]; ul|]. constructor; [| constructor].
    right; right. exists f, k. cbn [fst snd]. split; [rewrite E; exact INF| lia]. }
  assert (FPD : forall Σx, rt_frames RT Σx = rt_frames RT Σ -> fp_client RT Σx lo [(DOC, DOC + 24)]).
  { intros Σx E. constructor; [| constructor]. right; right. exists f, k. cbn [fst snd]. split; [rewrite E; exact INF| lia]. }
  assert (FP1 : fp_client RT Σ lo [(usp - 64, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).

  pose proof (al_walk1 usp DOC cap lo ra gp (Z_to_bv 64 0x6abde8) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(change (2^26) with 67108864 in CAP; lia) (conj G1 G2) (AFC Σ m ART0) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FP1 MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ DOC 24 ART0 LOW FP1 MU1 FOBJ0) as FOBJ1.
  assert (DOCC1 : rw_cells bsegs m1 DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 dcap]).
  { apply (rw_cells_agree bsegs m m1 _ _ DOCC0); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1).
    intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I]. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -64)) = usp + -64) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -64) mod 16 = 0) by (replace (usp + -64) with (usp + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).

  apply (NEWA Σ PMc (Z_to_bv 64 0xaff7c) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6abde8) t0 t1 t2 (Z_to_bv 64 DOC) (Z_to_bv 64 cap)
           (Z_to_bv 64 (al_sbuf cap)) (Z_to_bv 64 0x2d450) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (DOC + 8)) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m1 (al_sbuf cap) lo FDO MST); try reflexivity; try assumption;
    [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - lia.
  - lia.
  - pose proof (mcost_nonneg (al_tape cap) ltac:(lia)). lia.
  - rewrite EU2. exact ST1.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact SPA2.
  - intros c2 ((Σ1 & sbuf & Hc2 & LV1 & FRS1 & SP1 & CR1 & SB0 & SB16 & SBTOP) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & _ & _) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xaff7c) in Hc2' by lia.
    assert (FR2 : rw_cells bsegs m2 (usp + -64) (al_frame ra s0 s1 s2 s3 s4 s5 j)).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). unfold al_frame. pres_tac. }
    assert (DOCC2 : rw_cells bsegs m2 DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 dcap]).
    { apply (rw_cells_agree bsegs m1 m2 _ _ DOCC1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). pres_tac. }
    pose proof (fobj_pres RT AF Σ Σ1 _ _ m1 m2 DOC 24 ART1 FOBJ1 PRES2 FRS1) as FOBJ2.

    pose proof (al_walk2 DOC cap sbuf (usp + -64) dcap gp (Z_to_bv 64 0x6abde8) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s3 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                  F2 fc2 m2 ltac:(ul) ltac:(change (2^26) with 67108864 in CAP; lia) ltac:(ul) (fobj_shz RT AF Σ1 m2 DOC 24 ART2 FOBJ2)
                  (AFC Σ1 m2 ART2) DOCC2 MI2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & a2' & -> & MU3 & WM3 & MI3 & DOCC3) & Hc3'). clear Hc3.
    pose proof (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 ltac:(rewrite SP1; exact LOW) (FPD Σ1 FRS1) MU3 WM3) as ART3.
    pose proof (fobj_munch RT AF Σ1 m2 m3 lo _ DOC 24 ART2 ltac:(rewrite SP1; exact LOW) (FPD Σ1 FRS1) MU3 FOBJ2) as FOBJ3.
    assert (AG23 : agree_on (fun x => ~ (DOC <= x < DOC + 24)) m2 m3).
    { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
    assert (FR3 : rw_cells bsegs m3 (usp + -64) (al_frame ra s0 s1 s2 s3 s4 s5 j)).
    { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. unfold al_frame in Hx.
      cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
    assert (ST3 : stk bsegs m3 lo (usp + -64)).
    { apply (stk_agree bsegs m2 m3 _ _ ST2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbv beta in *. ul. }

    apply (NEWA Σ1 PMc (Z_to_bv 64 0xaffc4) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6abde8) u0 u1 u2 (Z_to_bv 64 DOC) (Z_to_bv 64 cap)
             (Z_to_bv 64 (al_tape cap)) (Z_to_bv 64 0x2d450) a2' b3 b4 b5 b6 b7 (Z_to_bv 64 (DOC + 8)) (Z_to_bv 64 ((DOC + 8) / 8 + 2147450880))
             (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 (al_tape cap) lo FDO MST); try reflexivity; try assumption;
      [.. | split; [exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
    + lia.
    + rewrite LV1. cbn [length]. lia.
    + rewrite CR1. lia.
    + rewrite EU2. exact ST3.
    + rewrite SP1. exact LOW.
    + rewrite EU2. ul.
    + rewrite EU2. ul.
    + rewrite EU2. exact SPA2.
    + intros c4 ((Σ2 & tape & Hc4 & LV2 & FRS2 & SP2 & CR2 & TP0 & TP16 & TPTOP) & FC4).
      destruct (ASTA_unpack_f RT Σ2 _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & _ & _) & FRM4 & Hc4'). clear Hc4.
      destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
      cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even 0xaffc4) in Hc4' by lia.
      assert (INF1 : In (f, k) (rt_frames RT Σ1)) by (rewrite FRS1; exact INF).
      assert (FR4 : rw_cells bsegs m4 (usp + -64) (al_frame ra s0 s1 s2 s3 s4 s5 j)).
      { apply (rw_cells_agree bsegs m3 m4 _ _ FR3); [| exact WM4]. apply (agree_of_pres _ _ _ _ _ _ PRES4). unfold al_frame. pres_tac. }
      assert (DOCC4 : rw_cells bsegs m4 DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 sbuf); C8 dcap]).
      { apply (rw_cells_agree bsegs m3 m4 _ _ DOCC3); [| exact WM4]. apply (agree_of_pres _ _ _ _ _ _ PRES4). pres_tac. }
      pose proof (fobj_pres RT AF Σ1 Σ2 _ _ m3 m4 DOC 24 ART3 FOBJ3 PRES4 FRS2) as FOBJ4.
      assert (FRS2' : rt_frames RT Σ2 = rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
      assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2, SP1; exact LOW).

      assert (SHZ4 : doc_shz [(usp - 64, usp); (DOC, DOC + 24)] m4 DOC).
      { intros m' MU WM. apply (fobj_shz RT AF Σ2 m'); [exact (art_fp_client RT AF Σ2 m4 m' lo _ ART4 LOW2 (FPS Σ2 FRS2') MU WM)|].
        exact (fobj_munch RT AF Σ2 m4 m' lo _ DOC 24 ART4 LOW2 (FPS Σ2 FRS2') MU FOBJ4). }
      pose proof (al_walk3 usp DOC cap sbuf tape lo dcap j gp (Z_to_bv 64 0x6abde8) w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6
                    ra s0 s1 s2 s3 s4 s5 F4 fc4 m4 ST4 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia)
                    ltac:(change (2^26) with 67108864 in CAP; lia) ltac:(ul) ltac:(ul) TP16 SHZ4 FR4 DOCC4 MI4) as W3.
      lazymatch type of W3 with evt bsegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes bsegs _ _ _ c4 (asta_evt_c RT AF Σ2 PMc _ _ MST W3') Hc4'). clear W3'. intros c5 Hc5.
      apply Hk. split; [| apply (cfrm0_of_asta RT Σ2 PMc _ c5 Hc5); intros ms (m5 & _ & E5 & _); rewrite E5; exact FRM4].
      exists Σ2, sbuf, tape.
      split; [| split; [rewrite LV2, LV1; reflexivity| split; [exact FRS2'| split; [rewrite SP2, SP1; reflexivity|
                  split; [rewrite CR2, CR1; lia| repeat split; assumption]]]]].
      eapply ASTA_conseq; [exact Hc5|]. intros ms (m5 & RS5 & _ & MU5 & WM5 & MI5 & ST5 & DOCC5). exists m5.
      split; [rewrite ESP; exact RS5|].
      split; [split; [exact (art_fp_client RT AF Σ2 m4 m5 lo _ ART4 LOW2 (FPS Σ2 FRS2') MU5 WM5)| split; [exact MI5| split; [| exact ST5]]]|].
      { exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM3 (wmono_trans _ _ _ _ WM4 WM5)))). }
      split; [| split; [exact DOCC5| exact (fobj_munch RT AF Σ2 m4 m5 lo _ DOC 24 ART4 LOW2 (FPS Σ2 FRS2') MU5 FOBJ4)]].
      intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO & _).
      pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
      assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -64) (bv_unsigned a)).
      { apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; intros e He; right; exact He| rewrite FRS1; auto| lia]. }
      rewrite (MU5 a), (PRES4 a Ha1), (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
      * cbn [outside]. split; [ul| exact I].
      * apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
      * cbn [outside]. split; [exact HO| exact I].
      * cbn [outside]. split; [ul|]. split; [exact HO| exact I].
Qed.

End AllocCPS.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Atp_hkit5A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition gr_regs (pc : Z) (ra : word) (q : Z) (gp t0 t1 t2 : word) (us0 : word) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (z SB : Z) (s2 s3 : word) (s5 s6 s7 s8 s9 s10 s11 : word)
    (t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (q - 64)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 z) (Z_to_bv 64 SB) a0 a1 a2 a3 a4 a5 a6 a7
          s2 s3 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma grow_walk0 : forall (q lo z SB : Z) (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo q -> lo <= q - 64 -> 0x6e0000 <= lo -> q < 2^63 -> 0 <= z < 2^64 -> 0 <= SB < 2^64 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (j0 : list byte),
      ms = gr_regs OPNEWARR_A (Z_to_bv 64 0xbddd8) q gp t0 t1 t2 s0 (Z_to_bv 64 z) (Z_to_bv 64 g_shadow_memory_dynamic_address) a2 a3 a4 a5 a6 a7 z SB s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(q - 64, q)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (q - 64)
      /\ rw_cells bsegs m1 (q - 64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 SB) (Z_to_bv 64 z) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_GROW_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO QH ZR SBR (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold gr_regs, PJ_GROW_A, OPNEWARR_A, SHB.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 64, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  do 7 zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  replace (q + -64) with (q - 64) in * by lia.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma grow_walk1 : forall (q z SB NEW buf size cap : Z) (gp t0 t1 t2 us0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < SB -> SB + 88 < 2^63 -> SB mod 8 = 0 -> 0 <= NEW < 2^64 -> 0 < buf -> 0 <= size -> buf + size < 2^63 -> 0 <= cap < 2^64 ->
  shz m SB 88 -> rw_cells bsegs m (SB + 64) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 cap)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists a3',
      ms = gr_regs PJ_COPY_G_A (Z_to_bv 64 0xbde2c) q gp t0 t1 t2 us0 (Z_to_bv 64 buf) (Z_to_bv 64 (buf + size)) (Z_to_bv 64 NEW) a3' a4 a5 a6 a7 z SB
                   (Z_to_bv 64 (SB + 64)) (Z_to_bv 64 NEW) (Z_to_bv 64 ((SB + 64) / 8 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (gr_regs 0xbddd8 (Z_to_bv 64 0xbddd8) q gp t0 t1 t2 us0 (Z_to_bv 64 NEW) a1 a2 a3 a4 a5 a6 a7 z SB s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros SB0 SBH SB8 NR BR SR BSH CR SHZ SC MI. unfold gr_regs, PJ_COPY_G_A, SHB in *.
  pose proof (SHZ (SB + 72) ltac:(lia)) as RD0. pose proof (SHZ (SB + 64) ltac:(lia)) as RD1.
  assert (ES : bv_unsigned (Z_to_bv 64 (SB + 64)) = SB + 64) by (apply unsigned_lit; lia).

  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.

  zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.

  zstep. zstep. zstep. gtrap.

  zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

  zstep. zstep.
  try replace (size + buf) with (buf + size) by lia.
  apply evt_done. eexists. cbv delta [mkR]. reflexivity.
Qed.

Lemma grow_walk3 : forall (q z SB NEW buf size cap : Z) (ra gp t0 t1 t2 us0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < SB -> SB + 88 < 2^63 -> SB mod 8 = 0 -> 0 <= NEW < 2^64 -> 0 < buf < 2^64 -> 0 <= size < 2^64 -> 0 <= cap < 2^64 ->
  shz m SB 88 -> rw_cells bsegs m (SB + 64) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 cap)] -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      (buf = SB /\ ms = gr_regs 0xbde44 ra q gp t0 t1 t2 us0 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 z SB
                                 (Z_to_bv 64 (SB + 64)) (Z_to_bv 64 NEW) (Z_to_bv 64 ((SB + 64) / 8 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      \/ (buf <> SB /\ ms = gr_regs OPDELARR_A (Z_to_bv 64 0xbde44) q gp t0 t1 t2 us0 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 z SB
                                   (Z_to_bv 64 (SB + 64)) (Z_to_bv 64 NEW) (Z_to_bv 64 ((SB + 64) / 8 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m))
    (gr_regs 0xbde2c ra q gp t0 t1 t2 us0 a0 a1 a2 a3 a4 a5 a6 a7 z SB (Z_to_bv 64 (SB + 64)) (Z_to_bv 64 NEW) (Z_to_bv 64 ((SB + 64) / 8 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros SB0 SBH SB8 NR BR SR CR SHZ SC MI. unfold gr_regs, OPDELARR_A, SHB in *.
  assert (ES : bv_unsigned (Z_to_bv 64 SB) = SB) by (apply unsigned_lit; lia).
  shz_pose SHZ (SB + 64).
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K.
  - apply evt_done. left. split; [lia| cbv delta [mkR]; reflexivity].
  - zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. apply evt_done. right. split; [lia| cbv delta [mkR]; reflexivity].
Qed.

Lemma grow_walk5 : forall (q lo z SB NEW buf size cap : Z) (ra gp t0 t1 t2 us0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (cra cs0 cs1 cs2 cs3 cs4 cs5 : word) (j0 : list byte) F fc (m : mem),
  0 < SB -> SB + 88 < 2^63 -> SB mod 8 = 0 -> 0 <= NEW < 2^64 -> 0 <= z < 2^64 -> 0 <= buf < 2^64 -> 0 <= size < 2^64 -> 0 <= cap < 2^64 ->
  0x6e0000 <= lo -> lo <= q - 64 -> q < 2^63 -> (SB + 88 <= lo \/ q <= SB) ->
  (forall m', munch [(SB + 64, SB + 72); (SB + 80, SB + 88)] m m' -> wmono bsegs m m' -> shz m' SB 88) ->
  rw_cells bsegs m (SB + 64) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 cap)] ->
  stk bsegs m lo (q - 64) -> rw_cells bsegs m (q - 64) [CB 8 j0; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a1' : word),
      ms = MS (mkR cra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 cs0 cs1 (Z_to_bv 64 (SB + 80)) a1' a2 a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc cra) fc None m' (seg_rom bsegs)
      /\ munch [(SB + 64, SB + 72); (SB + 80, SB + 88)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo q
      /\ rw_cells bsegs m' (SB + 64) [C8 (Z_to_bv 64 NEW); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 z)])
    (gr_regs 0xbde44 ra q gp t0 t1 t2 us0 a0 a1 a2 a3 a4 a5 a6 a7 z SB (Z_to_bv 64 (SB + 64)) (Z_to_bv 64 NEW) (Z_to_bv 64 ((SB + 64) / 8 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros SB0 SBH SB8 NR ZR BR SR CR GLO LO QH SEP SHZ SC ST FR MI. unfold gr_regs, SHB in *.
  pose proof (munch_refl [(SB + 64, SB + 72); (SB + 80, SB + 88)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 SB) = SB) by (apply unsigned_lit; lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 64)) = q - 64) by (apply unsigned_lit; lia).
  shz_pose SHZ (SB + 64).
  zstep. shz_norm. zstep. if_false.
  zstep.
  shz_pose SHZ (SB + 80).
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  do 7 zstep. zstep.
  pose proof (stk_release bsegs _ _ _ _ ST FR ltac:(lia)) as ST1. cbn [cells_size csize Nat.add] in ST1. replace (q - 64 + Z.of_nat 64) with q in ST1 by lia.
  zstep. replace (q - 64 + 64) with q by lia.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST1| eassumption].
Qed.

Section Grow.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold PJ_GROW_STACK_A in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, LIVE_MAX in *; lia.

Lemma live_remove_second : forall p z b c (L : list (Z * Z)), p <> b -> (forall e, In e L -> fst e <> b) ->
  live_remove b ((p, z) :: (b, c) :: L) = (p, z) :: L.
Proof.
  intros p z b c L NE HL. unfold live_remove. cbn.
  replace (p =? b) with false by (symmetry; apply Z.eqb_neq; exact NE). rewrite Z.eqb_refl. cbn.
  f_equal. exact (live_remove_none L b HL).
Qed.

Theorem grow_okA : grow_cpsA RT PMc.
Proof using AF RC FDO MST.
  intros Σ K E st z q ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    OK LV I0 ZB ART0 MI0 ST0 LOQ QT Q16 LVB CR0 HK.
  pose proof (ok_sb E OK) as (SB32 & SBF & SBE). pose proof (ok_frame E OK) as (F64 & FSEG & FLO). pose proof (ok_lo E OK) as LOW.
  pose proof (ok_len E OK) as LEN. pose proof (PJ_CAPMAX_bound (pa_len E) LEN) as CAPB. pose proof (ok_Lpos E OK) as LPOS.
  pose proof LV as (LVE & INF & SPLO).
  pose proof I0 as (SC0 & SZC & _ & _ & SH0 & (K0 & KC & KM) & HB0).
  pose proof (SBINVA_cap_pos E m st I0) as CAP64. pose proof (SBINVA_k E m st OK I0) as KB.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_client_consts RT AF Σ m ART0) as CC0.
  pose proof (proj2 (af_fshadow_apart RT AF Σ m (pa_F E) (pa_kF E) ART0 INF) (pa_F E) (pa_kF E) INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m (pa_F E) (pa_kF E) ART0 INF) as (_ & _ & FSZ & _ & SHT).
  assert (SHSB : shad (pa_F E) <= shad (pa_SB E) /\ shad (pa_SB E) + 11 <= shad ((pa_F E) + fs_size (pa_kF E))) by (unfold shad; Z.div_mod_to_equations; lia).
  assert (BUF1 : 0 < sa_buf st /\ sa_buf st + sa_cap st <= (pa_lo E)).
  { destruct (sa_heap st); [destruct HB0 as (B1 & B2 & B3); split; [exact B1| exact B3]|]. destruct HB0 as (-> & -> & _). ul. }
  assert (Z1 : 1 <= z <= 0x20001000) by lia.
  assert (EU : bv_unsigned (Z_to_bv 64 (q - 64)) = q - 64) by (apply unsigned_lit; ul).

  assert (CLF : forall L sp x, (pa_SB E) <= x < (pa_SB E) + 88 -> aclient L (rt_frames RT Σ) sp x).
  { intros L sp x Hx. right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF| lia]. }
  assert (CLS : forall L sp x, shad (pa_SB E) <= x < shad (pa_SB E) + 11 -> aclient L (rt_frames RT Σ) sp x).
  { intros L sp x Hx. right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF| lia]. }
  assert (CLB : forall sp x, sa_buf st <= x < sa_buf st + sa_cap st -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp x).
  { intros sp x Hx. destruct (sa_heap st) eqn:HP.
    - right; right; left. exists (sa_buf st), (sa_cap st). split; [rewrite LVE; unfold sbchunkA; rewrite HP; left; reflexivity| lia].
    - destruct HB0 as (B1 & B2 & _). apply CLF. lia. }
  assert (CLR : forall sp x, sbinv_rng E st x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp x).
  { intros sp x [Hx|[Hx|Hx]]; [apply CLF; exact Hx| apply CLS; exact Hx| apply CLB; exact Hx]. }
  assert (RNGLO : forall x, sbinv_rng E st x -> x < (pa_lo E)) by (intros x [Hx|[Hx|Hx]]; lia).

  assert (CSEP : forall a, aclient (pa_L E) (rt_frames RT Σ) q a -> q <= a \/ a < (pa_lo E)).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0) as [H|H]; [| left; exact H| right; lia].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (grow_walk0 q (pa_lo E) z (pa_SB E) ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0);
                   [ul| ul| ul| ul| ul| exact CC0| exact MI0]|].
  cbv beta. intros ms1 (m1 & j0 & -> & MU1 & WM1 & MI1 & ST1 & FR1). apply evt_done. unfold gr_regs.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 64) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (I1 : SBINVA E m1 st).
  { apply (SBINVA_agree E m m1 st I0). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. pose proof (RNGLO x Hx). cbn [outside]. split; [ul| exact I]. }
  assert (PRES1 : forall a : word, aclient (pa_L E) (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. destruct (CSEP _ Ha); ul. }
  clear MU1 WM1 ST0 MI0 I0 SC0 SH0.

  eapply (aevt_newarr RT AF RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (q - 64) z (pa_lo E) Z1 eq_refl
            ltac:(lia) CR0 ART1 MI1 ST1 SPLO ltac:(ul) ltac:(ul) ltac:(Z.div_mod_to_equations; lia)).
  intros Σ1 p v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F1 m2 ART2 MI2 WM2 ST2 PRES2 WR2 ACC2 LV1 FRS1 SP1 CR1 P0 P16 PTOP.
  rewrite (ret_pc_even 0xbddd8) by lia.
  pose proof (af_live_range RT AF Σ1 m2 p z ART2 ltac:(rewrite LV1; left; reflexivity)) as (_ & PZ & _). rewrite SP1 in PZ.
  assert (FRESH : forall sp a, (pa_lo E) <= sp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> ~ (p <= a < p + z)).
  { intros sp a Hsp Ha. apply (fresh_apart_l RT AF Σ1 m2 [(p, z)] (rt_live RT Σ) p z sp a ART2 LV1 ltac:(left; reflexivity) ltac:(rewrite SP1; lia)).
    rewrite FRS1. exact Ha. }
  assert (I2 : SBINVA E m2 st).
  { apply (SBINVA_agree E m1 m2 st I1). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. apply CLR. exact Hx. }
  assert (FR2 : rw_cells bsegs m2 (q - 64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact FR1|]. apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
  assert (PRES2' : forall a : word, aclient (pa_L E) (rt_frames RT Σ) q (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite <- (PRES1 a Ha). apply PRES2.
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }
  pose proof I2 as (SC2 & _ & (bs2 & BUF2) & (ji2 & ARR2) & SH2 & _).
  pose proof (SBINVA_shz E m2 st OK I2) as SHZ2.
  assert (ACCB2 : acc bsegs m2 (sa_buf st) (sa_cap st)).
  { destruct (sa_heap st) eqn:HP.
    - apply (proj2 (af_acc_live RT AF Σ1 m2 (sa_buf st) (sa_cap st) ART2 ltac:(rewrite LV1, LVE; unfold sbchunkA; rewrite HP; right; left; reflexivity))).
    - destruct HB0 as (B1 & B2 & _). rewrite B1, B2. replace 64 with (8 * Z.of_nat 8) by reflexivity.
      apply (acc_sub bsegs m2 (pa_SB E) 88); [| lia| change (8 * Z.of_nat 8) with 64; lia].
      apply (acc_zero_run bsegs m2 (pa_SB E) 11); [Z.div_mod_to_equations; lia| ul| exact SH2]. }
  assert (RCB : forall n, 0 <= n <= sa_cap st -> rng_class RT Σ1 (sa_buf st) n).
  { intros n Hn. destruct (sa_heap st) eqn:HP.
    - left. exists (sa_buf st), (sa_cap st). split; [rewrite LV1, LVE; unfold sbchunkA; rewrite HP; right; left; reflexivity| lia].
    - destruct HB0 as (B1 & B2 & _). right; left. exists (pa_F E), (pa_kF E). split; [rewrite FRS1; exact INF| lia]. }
  clear PRES1 PRES2 FR1 ST1 MI1 I1 ART1.

  assert (TAIL5 : forall (Σy : rts RT) (my : mem) (ra' w0 w1 w2 us0 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 : word) (Fy : bvmap 5 word),
    rt_live RT Σy = (p, z) :: pa_L E -> rt_frames RT Σy = rt_frames RT Σ -> rt_sp0 RT Σy = rt_sp0 RT Σ -> rt_credit RT Σ - mcost z <= rt_credit RT Σy ->
    ART RT Σy my -> mem_inv bsegs my -> stk bsegs my (pa_lo E) (q - 64) ->
    rw_cells bsegs my ((pa_SB E) + 64) [C8 (Z_to_bv 64 (sa_buf st)); C8 (Z_to_bv 64 (sa_size st)); C8 (Z_to_bv 64 (sa_cap st))] ->
    (exists ji, rw_cells bsegs my (pa_SB E) [CB 64 ji]) -> bytes_at bsegs my (shad (pa_SB E)) (repeat z8 11) -> wr_at bsegs my p z ->
    rw_cells bsegs my (q - 64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (forall a : word, aclient (pa_L E) (rt_frames RT Σ) q (bv_unsigned a) -> outside [((pa_SB E) + 64, (pa_SB E) + 88)] (bv_unsigned a) -> my a = m a) ->
    aevt RT PMc Σy K (gr_regs 0xbde44 ra' q gp w0 w1 w2 us0 b0 b1 b2 b3 b4 b5 b6 b7 z (pa_SB E) (Z_to_bv 64 ((pa_SB E) + 64)) (Z_to_bv 64 p) (Z_to_bv 64 (((pa_SB E) + 64) / 8 + SHB))
                               s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 Fy fc my)).
  { intros Σy my ra' w0 w1 w2 us0 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 Fy LVy FRSy SPy CRy ARTy MIy STy SCy (jiy & ARRy) SHy WRy FRy PRESy.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (grow_walk5 q (pa_lo E) z (pa_SB E) p (sa_buf st) (sa_size st) (sa_cap st) ra' gp w0 w1 w2 us0 b0 b1 b2 b3 b4 b5 b6 b7 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6
                               ra s0 s1 s2 s3 s4 s5 j0 Fy fc my); [ul| ul| lia| ul| ul| ul| lia| lia| ul| ul| ul| left; lia| | exact SCy| exact STy| exact FRy| exact MIy]|].
    { intros m' MU WM. replace 88 with (8 * Z.of_nat 11) by reflexivity. apply (shz_of_zero_run m' (pa_SB E) 11); [Z.div_mod_to_equations; lia| ul|].
      apply (bytes_at_agree bsegs my m' _ _ SHy). apply (agree_of_munch _ _ _ _ MU). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. repeat split; lia. }
    cbv beta. intros ms5 (m5 & b1' & -> & MU5 & WM5 & MI5 & ST5 & SC5). apply evt_done.
    assert (ART5 : ART RT Σy m5).
    { apply (art_client_write RT AF Σy my m5 (q - 64) ARTy ltac:(rewrite SPy; ul)); [| exact WM5].
      intros a Ha. apply MU5. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha; rewrite FRSy; apply CLF; lia. }
    apply (HK Σy p w0 w1 w2 (Z_to_bv 64 ((pa_SB E) + 80)) b1' b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 Fy m5 ART5 MI5 ST5); [| | exact FRSy| exact SPy| exact CRy|].
    - unfold SBINVA. cbn [sa_buf sa_size sa_cap sa_heap sa_k sb_grownA]. split; [exact SC5|]. split; [lia|]. split; [| split; [| split; [| split; [| split; [lia| split; [lia| lia]]]]]].
      + apply (wr_at_rw_CB m5 p z); [exact (wr_at_transport bsegs my m5 p z WRy WM5)| lia].
      + exists jiy. eapply rw_cells_agree_nw; [exact ARRy|]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. repeat split; lia.
      + apply (bytes_at_agree bsegs my m5 _ _ SHy). apply (agree_of_munch _ _ _ _ MU5). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. repeat split; lia.
      + split; [lia|]. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
    - unfold pa_live. cbn [sbchunkA sb_grownA sa_heap sa_buf sa_cap]. rewrite LVy, FRSy, SPy. split; [reflexivity|]. split; [exact INF| exact SPLO].
    - intros a Ha Ho. rewrite (MU5 a); [exact (PRESy a Ha Ho)|]. cbn [outside] in *. destruct Ho as [Ho _]. repeat split; lia. }

  assert (TAIL3 : forall (mx : mem) (ra' w0 w1 w2 us0 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 : word) (Fx : bvmap 5 word),
    ART RT Σ1 mx -> mem_inv bsegs mx -> stk bsegs mx (pa_lo E) (q - 64) -> SBINVA E mx st -> wr_at bsegs mx p z ->
    rw_cells bsegs mx (q - 64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (forall a : word, aclient (pa_L E) (rt_frames RT Σ) q (bv_unsigned a) -> outside [((pa_SB E) + 64, (pa_SB E) + 88)] (bv_unsigned a) -> mx a = m a) ->
    aevt RT PMc Σ1 K (gr_regs 0xbde2c ra' q gp w0 w1 w2 us0 b0 b1 b2 b3 b4 b5 b6 b7 z (pa_SB E) (Z_to_bv 64 ((pa_SB E) + 64)) (Z_to_bv 64 p) (Z_to_bv 64 (((pa_SB E) + 64) / 8 + SHB))
                               s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 Fx fc mx)).
  { intros mx ra' w0 w1 w2 us0 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 Fx ARTx MIx STx Ix WRx FRx PRESx.
    pose proof Ix as (SCx & _ & _ & ARRx & SHx & _ & HBx). pose proof (SBINVA_shz E mx st OK Ix) as SHZx.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (grow_walk3 q z (pa_SB E) p (sa_buf st) (sa_size st) (sa_cap st) ra' gp w0 w1 w2 us0 b0 b1 b2 b3 b4 b5 b6 b7 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 Fx fc mx);
                     [ul| ul| lia| ul| ul| lia| lia| exact SHZx| exact SCx| exact MIx]|].
    cbv beta. intros ms3 [(EB & ->)|(NB & ->)]; apply evt_done.
    -
      apply (TAIL5 Σ1 mx); [rewrite LV1, LVE; unfold sbchunkA; destruct (sa_heap st) eqn:HP; [exfalso| reflexivity];
                             pose proof (af_frames_range RT AF Σ1 mx (pa_F E) (pa_kF E) ARTx ltac:(rewrite FRS1; exact INF)) as (_ & _ & _ & FLV);
                             specialize (FLV (sa_buf st) (sa_cap st) ltac:(rewrite LV1, LVE; unfold sbchunkA; rewrite HP; right; left; reflexivity)); lia
                           | exact FRS1| exact SP1| lia| exact ARTx| exact MIx| exact STx| exact SCx| exact ARRx| exact SHx| exact WRx| exact FRx| exact PRESx].
    -
      destruct (sa_heap st) eqn:HP; [| destruct HBx as (B1 & _); exfalso; exact (NB B1)]. destruct HBx as (B1 & B2 & B3).
      assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σ1)) by (rewrite LV1, LVE; unfold sbchunkA; rewrite HP; right; left; reflexivity).
      unfold gr_regs.
      eapply (aevt_delarr RT AF RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fx fc mx (sa_buf st) (sa_cap st) (pa_lo E) INB eq_refl ARTx MIx).
      { unfold call_ok. rewrite EU, SP1. split; [exact STx|]. split; [lia|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
      { unfold unwind_ok. rewrite EU, unsigned_lit by lia. left. ul. }
      intros Σ2 v w0' w1' w2' c1 c2 c3 c4 c5 c6 c7 w3' w4' w5' w6' F3 m4 (ART4 & MI4 & ST4) PRES4 LV2 FRS2 SP2 CR2.
      rewrite EU in ST4, PRES4. rewrite (ret_pc_even 0xbde44) by lia.
      assert (LV2' : rt_live RT Σ2 = (p, z) :: pa_L E).
      { rewrite LV2, LV1, LVE. unfold sbchunkA. rewrite HP. cbn [app]. apply live_remove_second.
        - intros E0. apply (FRESH (pa_lo E) (sa_buf st) ltac:(lia) (CLB (pa_lo E) (sa_buf st) ltac:(lia))). lia.
        - intros [b c] Hin Eb. cbn [fst] in Eb. subst b. pose proof (LPOS _ _ Hin) as CP.
          destruct (af_live_disj RT AF Σ1 m2 (sa_buf st) (sa_cap st) (sa_buf st) c [(p, z)] (pa_L E) ART2
                      ltac:(rewrite LV1, LVE; unfold sbchunkA; rewrite HP; reflexivity) ltac:(apply in_or_app; right; exact Hin)); lia. }
      assert (AG4 : forall P : Z -> Prop, (forall x, P x -> (q - 64 <= x < q) \/ ((pa_SB E) <= x < (pa_SB E) + 88) \/ (shad (pa_SB E) <= x < shad (pa_SB E) + 11)) -> agree_on P mx m4).
      { intros P HPP a Ha. apply PRES4. rewrite FRS1. destruct (HPP _ Ha) as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
      apply (TAIL5 Σ2 m4 _ _ _ _ s0); [exact LV2'| rewrite FRS2; exact FRS1| rewrite SP2; exact SP1| rewrite CR2, CR1; lia| exact ART4| exact MI4| exact ST4| | | | | |].
      + eapply rw_cells_agree_nw; [exact SCx|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia.
      + destruct ARRx as (jix & ARRx'). exists jix. eapply rw_cells_agree_nw; [exact ARRx'|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia.
      + apply (bytes_at_agree bsegs mx m4 _ _ SHx). apply AG4. intros x Hx. rewrite repeat_length in Hx. lia.
      + eapply wr_at_agree_nw; [exact WRx|]. intros a Ha. apply PRES4. right; right; left. exists p, z. split; [rewrite LV2'; left; reflexivity| lia].
      + eapply rw_cells_agree_nw; [exact FRx|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia.
      + intros a Ha Ho. rewrite <- (PRESx a Ha Ho). apply PRES4.
        apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV2'; intros e He; right; exact He| rewrite FRS1; intros e He; exact He| lia]. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (grow_walk1 q z (pa_SB E) p (sa_buf st) (sa_size st) (sa_cap st) gp v0 v1 v2 s0 e1 e2 e3 e4 e5 e6 e7 s2 s3 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc m2);
                   [ul| ul| lia| ul| lia| lia| ul| lia| exact SHZ2| exact SC2| exact MI2]|].
  cbv beta. intros ms2 (a3' & ->). apply evt_done. unfold gr_regs.

  pose proof BUF2 as [[[LB2 _] BY2] _]. cbn [cells_wf cell_wf cells_bytes cbytes] in LB2, BY2. rewrite app_nil_r in BY2.
  set (n := Z.to_nat (sa_size st)).
  assert (BYn : bytes_at bsegs m2 (sa_buf st) (firstn n bs2)).
  { rewrite <- (firstn_skipn n bs2) in BY2. apply bytes_at_app in BY2. exact (proj1 BY2). }
  assert (LENn : Z.of_nat (length (firstn n bs2)) = sa_size st) by (rewrite length_firstn, Nat.min_l by lia; lia).
  assert (SRCOK : 0 < sa_size st -> acc bsegs m2 (sa_buf st) (sa_size st) /\ rng_class RT Σ1 (sa_buf st) (sa_size st)).
  { intros Hs. split; [apply (acc_sub bsegs m2 _ _ _ _ ACCB2); lia| apply RCB; lia]. }
  assert (DSTOK : 0 < sa_size st -> acc bsegs m2 p (sa_size st) /\ rng_class RT Σ1 p (sa_size st)).
  { intros Hs. split; [apply (acc_sub bsegs m2 _ _ _ _ ACC2); lia|]. left. exists p, z. split; [rewrite LV1; left; reflexivity| lia]. }
  assert (CLD : forall sp i, 0 <= i < sa_size st -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp (p + i)).
  { intros sp i Hi. right; right; left. exists p, z. split; [rewrite LV1; left; reflexivity| lia]. }
  assert (WRD : wr_at bsegs m2 p (sa_size st)) by (apply (wr_at_sub m2 p z); [exact WR2| lia| lia| lia]).
  eapply (copy_okA RT AF RC PMc FDO MST PJ_COPY_G_A (or_introl eq_refl) Σ1 K (q - 64) (pa_lo E) (sa_buf st) p (sa_size st) (firstn n bs2)
            _ gp _ v0 v1 v2 _ _ a3' e4 e5 e6 e7 _ _ _ _ s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F1 fc m2 BYn LENn ltac:(lia) ltac:(lia) ltac:(lia) P0 ltac:(lia)
            SRCOK DSTOK CLD WRD ART2 MI2 ST2 ltac:(rewrite SP1; exact SPLO) ltac:(unfold PJ_COPY_STACK_A; ul) ltac:(ul) ltac:(Z.div_mod_to_equations; lia)).
  intros w0 w1 w2 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m3 ART3 MI3 ST3 WM3 BY3 PRES3.
  rewrite (ret_pc_even 0xbde2c) by lia.
  assert (AG3 : forall P : Z -> Prop, (forall x, P x -> (q - 64 <= x < q) \/ sbinv_rng E st x) -> agree_on P m2 m3).
  { intros P HP a Ha. destruct (HP _ Ha) as [H|H]; apply PRES3.
    - left. ul.
    - ul.
    - rewrite FRS1. apply (aclient_mono _ _ _ _ _ _ _ (CLR (q - 64) _ H)); [rewrite LV1; intros e He; right; exact He| intros e He; exact He| lia].
    - pose proof (FRESH (q - 64) _ ltac:(ul) (CLR (q - 64) _ H)). lia. }
  apply (TAIL3 m3 _ _ _ _ s0); [exact ART3| exact MI3| exact ST3| | exact (wr_at_transport bsegs m2 m3 p z WR2 WM3)| |].
  - apply (SBINVA_agree E m2 m3 st I2). apply AG3. intros x Hx. right. exact Hx.
  - eapply rw_cells_agree_nw; [exact FR2|]. apply AG3. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia.
  - intros a Ha _. rewrite <- (PRES2' a Ha). apply PRES3.
    + rewrite FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1, LVE; intros e He; right; apply in_or_app; right; exact He| intros e He; exact He| lia].
    + pose proof (FRESH q _ ltac:(ul) (aclient_mono _ _ _ (rt_live RT Σ) (rt_frames RT Σ) q _ Ha ltac:(rewrite LVE; intros e He; apply in_or_app; right; exact He) ltac:(intros e He; exact He) ltac:(lia))). lia.
Qed.

End Grow.

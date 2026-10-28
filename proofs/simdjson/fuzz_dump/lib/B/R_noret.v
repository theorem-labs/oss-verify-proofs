(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread R_leaves R_cache_defs R_prim_defs F_memset R_setshadow R_poison R_tlsgetaddr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition noret_entry : Z := 0x8788c.
Definition g_asan_inited : Z := 0x177e18.
Definition g_got_platform_unpoison : Z := 0x16e210.

Definition noret_cells (T FSB : Z) (m : mem) : Prop :=
  rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m g_got_platform_unpoison [C8 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0x16e1b0 [C8 (Z_to_bv 64 0x206be0)] /\ rw_cells bsegs m 0x206be0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m (T + 72) [C8 (Z_to_bv 64 FSB)].

Definition noret_bottom (usp : Z) : Z := ((usp - 64 - 4096) / 4096) * 4096.

Definition noret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB bot top lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(shad bot, shad bot + (top - bot) / 8); (FSB + 0x60, FSB + 0x61); (lo, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (shad bot) [CB (Z.to_nat ((top - bot) / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat ((top - bot) / 8)))]
    /\ u8arr bsegs m' (FSB + 0x60) [Z_to_bv 8 1]
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma platform_unpoison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  rw_cells bsegs m g_got_platform_unpoison [C8 (Z_to_bv 64 1)] ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z -> (0x6cd000 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 80, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x82718) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros GPU ST HLO HLO2 MI. unfold g_got_platform_unpoison in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 80%nat ST.
  do 3 zstep.
  do 3 zstep. ifT.
  do 3 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. zstep.
  apply evt_done. unfold frame_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma land_m4096 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = ((x / 4096) * 4096)%Z.
Proof.
  intros x Hx. change 18446744073709547520%Z with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^12)%Z with 4096%Z. lia.
Qed.
Lemma land_rup8 : forall x, (0 <= x < 2^28)%Z -> (x mod 8 = 0)%Z -> Z.land (x + 7) 268435448 = x.
Proof.
  intros x Hx H8. change 268435448%Z with (Z.ldiff (Z.ones 28) (Z.ones 3)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^3)%Z with 8%Z. Z.div_mod_to_equations. lia.
Qed.

Definition hnr_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(FSB + 0x60, FSB + 0x61)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ u8arr bsegs m' (FSB + 0x60) [Z_to_bv 8 1].
Lemma fs_handle_noreturn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB : Z) (g : byte),
  u8arr bsegs m (FSB + 0x60) [g] -> (0x6cd000 <= FSB)%Z -> (FSB + 0xb09000 <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (hnr_post ra sp gp tp s0 s1 (Z_to_bv 64 FSB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FSB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x644b8) fc None m (seg_rom bsegs)).
Proof.
  intros until g. intros GB H0 H1 MI.
  pose proof (munch_refl [(FSB + 0x60, FSB + 0x61)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_store_ok bsegs mm (FSB + 0x60) [g] 0 (wa (FSB + 0x60 + 0)) GB ltac:(cbn; lia) ltac:(f_equal; lia)) as SOK;
    pose proof (u8arr_write bsegs mm (FSB + 0x60) [g] 0 (Z_to_bv 8 1) GB ltac:(cbn; lia)) as GB2 end.
  rewrite Z.add_0_r in SOK, GB2. cbn [upd Z.to_nat] in GB2.
  zstep. change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1]. clear GB. store_done.
  zstep.
  apply evt_done. unfold hnr_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact GB2].
Qed.

Local Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc | |- ?g => idtac "NOEVT" g end.
Local Ltac amem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Lemma handle_no_return_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (TCX T top FSB bot lo : Z) (g : byte) (shj : list byte),
  bot = noret_bottom (bv_unsigned sp) ->
  noret_cells T FSB m -> thread_cells TCX T m -> stack_cells T top (top - 0x800000) m -> ps_cells m ->
  u8arr bsegs m (FSB + 0x60) [g] ->
  (TCX + 0x10000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= TCX)%Z -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
  (T + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= T)%Z -> (0 < T)%Z -> (T + 4096 <= lo)%Z ->
  (FSB + 0xb09000 <= 0x7fff7000 \/ kHighShadowEnd < FSB)%Z -> (0x6cd000 <= FSB)%Z -> (FSB + 0xb09000 <= lo)%Z ->
  (top mod 4096 = 0)%Z -> (bv_unsigned sp + 16 <= top)%Z -> (top <= 2^47)%Z -> (top - 0x800000 <= bv_unsigned sp)%Z ->
  rw_cells bsegs m (shad bot) [CB (Z.to_nat ((top - bot) / 8)) shj] ->
  stk bsegs m lo (bv_unsigned sp) -> (lo + 0x3000 <= bv_unsigned sp)%Z -> (0x6cd000 <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp mod 16 = 0)%Z ->
  mem_inv bsegs m ->
  evt bsegs (noret_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB bot top lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 noret_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until shj. intros Ebot NC TC SC PS GC HTCX0 HTCX1 HTCX HT0 HT1 HT HFSB HFSB1 HFSBL TOP4K TOPLO TOPHI BOT SHJ ST HLO HLO2 HLOH SP16 MI.
  destruct NC as (AI & GPU & GPS & PSZ & TF).
  unfold noret_entry, g_asan_inited, g_got_platform_unpoison, tpA in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HB : bot mod 4096 = 0 /\ bv_unsigned sp - 4160 - 4095 <= bot <= bv_unsigned sp - 4160).
  { subst bot. unfold noret_bottom. Z.div_mod_to_equations. lia. }
  unfold kHighShadowEnd in HLOH, HFSB. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in HTCX0, HT0.
  assert (PA : ps_args_ok bot (top - bot)).
  { unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [Z.div_mod_to_equations; lia | lia]. }
  pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4). unfold kHighShadowEnd in SR2.
  destruct SC as [S1 S2]. unfold off_t_stack_top, off_t_stack_switching in S1, S2.
  destruct TC as ((KI & K & TS & T0) & TX). unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(shad bot, shad bot + (top - bot) / 8); (FSB + 0x60, FSB + 0x61); (lo, bv_unsigned sp)] m) as MU.
  carve_frame 40%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST.
  do 6 zstep.

  do 6 zstep. ifF.

  zstep. sp_facts.
  call (platform_unpoison_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  rename POST into ST.
  zstep. ifF.

  do 2 zstep.
  lazymatch goal with |- context [Z_to_bv 64 12297829382473034410] => set (vpat := Z_to_bv 64 12297829382473034410) in * end.
  do 2 zstep. zstep. sp_facts.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1: exact (conj (conj KI (conj K (conj TS T0))) TX).
  all: rewrite ?Esp in *; try lia; try eassumption.
  rename POST into ST.
  zstep. ifF.

  do 3 zstep. zstep. ifT.

  zstep. sp_facts.
  call (stack_top_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ T top (top - 0x800000)%Z).
  1: exact (conj S1 S2).
  all: rewrite ?Esp in *; try lia; try eassumption.
  do 6 zstep. rewrite land_m4096 by lia.
  replace ((bv_unsigned sp + -64 - 4096) / 4096 * 4096)%Z with bot by (rewrite Ebot; unfold noret_bottom; f_equal; f_equal; lia).
  zstep. do 4 zstep. ifT.
  do 4 zstep. rewrite land_rup8 by (Z.div_mod_to_equations; lia).
  do 2 zstep.

  let mm := amem in
  pose proof (ps_cells_framed m mm _ PS MU WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi, shad, SHB; lia)) as PSm.
  zstep. sp_facts.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ bot (top - bot)%Z 0 lo shj).
  all: rewrite ?Esp in *; try lia; try eassumption.
  clear PSm. rename POST into ST.

  zstep. sp_facts.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1: exact (conj (conj KI (conj K (conj TS T0))) TX).
  all: rewrite ?Esp in *; try lia; try eassumption.
  rename POST into ST.
  zstep. ifF.
  zstep. zstep. ifF.
  zstep. do 3 zstep.
  rewrite (proj2 (Z.ltb_ge FSB 2)) by lia. cbn [Z.b2z].
  change ((0 + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z.
  replace (Z.land 18446744073709551615 FSB) with FSB by (rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  zstep. ifF.

  zstep.
  call (fs_handle_noreturn_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ FSB g).
  all: rewrite ?Esp in *; try lia; try eassumption.

  do 6 zstep.
  release_frame FR4 ST (bv_unsigned sp + -72)%Z. release_frame FR3 ST (bv_unsigned sp + -64)%Z. release_frame FR2 ST (bv_unsigned sp + -56)%Z.
  release_frame FR1 ST (bv_unsigned sp + -48)%Z. release_frame FR0 ST (bv_unsigned sp + -40)%Z. release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. unfold noret_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact PC|]. split; [exact POST| exact ST].
Qed.

Definition unwicpt_entry : Z := 0x73ec4.
Definition g_real_unwind_raise : Z := 0x170170.
Definition real_unwind_raise_A : Z := 0x147724.

Definition unwicpt_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB top lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (Z_to_bv 64 real_unwind_raise_A) fc None m' (seg_rom bsegs)
    /\ munch [(shad (noret_bottom (bv_unsigned sp - 32)), shad (noret_bottom (bv_unsigned sp - 32)) + (top - noret_bottom (bv_unsigned sp - 32)) / 8);
              (FSB + 0x60, FSB + 0x61); (lo, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (shad (noret_bottom (bv_unsigned sp - 32)))
         [CB (Z.to_nat ((top - noret_bottom (bv_unsigned sp - 32)) / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat ((top - noret_bottom (bv_unsigned sp - 32)) / 8)))]
    /\ u8arr bsegs m' (FSB + 0x60) [Z_to_bv 8 1]
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma unwind_icpt_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (TCX T top FSB lo : Z) (g : byte) (shj : list byte),
  noret_cells T FSB m -> thread_cells TCX T m -> stack_cells T top (top - 0x800000) m -> ps_cells m ->
  u8arr bsegs m (FSB + 0x60) [g] -> ro_cells bsegs m g_real_unwind_raise [C8 (Z_to_bv 64 real_unwind_raise_A)] ->
  (TCX + 0x10000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= TCX)%Z -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
  (T + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= T)%Z -> (0 < T)%Z -> (T + 4096 <= lo)%Z ->
  (FSB + 0xb09000 <= 0x7fff7000 \/ kHighShadowEnd < FSB)%Z -> (0x6cd000 <= FSB)%Z -> (FSB + 0xb09000 <= lo)%Z ->
  (top mod 4096 = 0)%Z -> (bv_unsigned sp + 16 <= top)%Z -> (top <= 2^47)%Z -> (top - 0x800000 <= bv_unsigned sp - 32)%Z ->
  rw_cells bsegs m (shad (noret_bottom (bv_unsigned sp - 32))) [CB (Z.to_nat ((top - noret_bottom (bv_unsigned sp - 32)) / 8)) shj] ->
  stk bsegs m lo (bv_unsigned sp) -> (lo + 0x3020 <= bv_unsigned sp)%Z -> (0x6cd000 <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp mod 16 = 0)%Z ->
  mem_inv bsegs m ->
  evt bsegs (unwicpt_post ra sp gp (Z_to_bv 64 tpA) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB top lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 unwicpt_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until shj. intros NC TC SC PS GC UR HTCX0 HTCX1 HTCX HT0 HT1 HT HFSB HFSB1 HFSBL TOP4K TOPLO TOPHI BOT SHJ ST HLO HLO2 HLOH SP16 MI.
  unfold unwicpt_entry, g_real_unwind_raise, real_unwind_raise_A, tpA in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold kHighShadowEnd in HLOH, HFSB. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in HTCX0, HT0.
  set (bot := noret_bottom (bv_unsigned sp - 32)) in *.
  assert (HB : bot mod 4096 = 0 /\ bv_unsigned sp - 32 - 4160 - 4095 <= bot <= bv_unsigned sp - 32 - 4160).
  { subst bot. unfold noret_bottom. Z.div_mod_to_equations. lia. }
  assert (Ebot : bot = noret_bottom (bv_unsigned sp - 32)) by reflexivity. clearbody bot.
  destruct NC as (AI & GPU & GPS & PSZ & TF). unfold g_asan_inited, g_got_platform_unpoison in AI, GPU.
  destruct SC as [S1 S2]. unfold off_t_stack_top, off_t_stack_switching in S1, S2.
  destruct TC as ((KI & K & TS & T0) & TX). unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  assert (PA : ps_args_ok bot (top - bot)).
  { unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [Z.div_mod_to_equations; lia | lia]. }
  pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4). unfold kHighShadowEnd in SR2.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(shad bot, shad bot + (top - bot) / 8); (FSB + 0x60, FSB + 0x61); (lo, bv_unsigned sp)] m) as MU.
  carve_frame 24%nat ST. carve_frame 8%nat ST.
  do 4 zstep.
  do 3 zstep. ifF.
  zstep. zstep. sp_facts.
  let mm := amem in
  pose proof (ps_cells_framed m mm _ PS MU WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi, shad, SHB; lia)) as PSm.
  call (handle_no_return_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T top FSB bot lo g shj).
  1: rewrite Ebot, ?Esp; unfold noret_bottom; f_equal; f_equal; lia.
  1: exact (conj AI (conj GPU (conj GPS (conj PSZ TF)))).
  1: exact (conj (conj KI (conj K (conj TS T0))) TX).
  1: exact (conj S1 S2).
  all: rewrite ?Esp in *; try lia; try eassumption.
  rename POST into ST.

  do 6 zstep.
  release_frame FR0 ST (bv_unsigned sp + -24)%Z. release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. unfold unwicpt_post. rewrite <- Ebot. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|]. split; [exact PC0| exact ST].
Qed.

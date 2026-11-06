(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2 Gq_rgb.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ONE := (Z_to_bv 64 1) (only parsing).
(* [comment removed for export] *)
Notation D32_W datad n sa fr :=
  [(datad, datad + n); (sa - 16, sa); (fr + 176, fr + 176 + 4); (fr + 192, fr + 192 + 4); (fr + 208, fr + 208 + 4); (sa + 16, sa + 192)]%Z (only parsing).

(* [comment removed for export] *)
Definition d32_slots (c16 c24 c32 c40 : word) (wpls wpld acc datas : Z) (l88 : word) (datad fr : Z) : list cell :=
  [C8 c16; C8 c24; C8 c32; C8 c40; C8 (Z_to_bv 64 wpls); C8 (Z_to_bv 64 wpld); C8 (Z_to_bv 64 (fr + 48)); C8 (Z_to_bv 64 acc);
   C8 (Z_to_bv 64 datas); C8 l88; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 1);
   C8 (Z_to_bv 64 (fr + 160)); C8 (Z_to_bv 64 (fr + 112)); C8 (Z_to_bv 64 (fr + 144)); C8 (Z_to_bv 64 (fr + 96)); C8 (Z_to_bv 64 (fr + 128)); C8 (Z_to_bv 64 (fr + 80));
   C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 (fr + 32))].
(* [comment removed for export] *)
Definition d32_fcells (w h : Z) (dw : word) (r1 g1 b1 r2 g2 b2 : Z) (rv gv bv : word) (p : list (list byte)) : list cell :=
  [C4 (Z_to_bv 64 w); CB 12 (nth 0 p []); C4 (Z_to_bv 64 h); CB 12 (nth 1 p []); C4 dw; CB 12 (nth 2 p []);
   C4 (Z_to_bv 64 r1); CB 12 (nth 3 p []); C4 (Z_to_bv 64 g1); CB 12 (nth 4 p []); C4 (Z_to_bv 64 b1); CB 12 (nth 5 p []);
   C4 (Z_to_bv 64 r2); CB 12 (nth 6 p []); C4 (Z_to_bv 64 g2); CB 12 (nth 7 p []); C4 (Z_to_bv 64 b2); CB 12 (nth 8 p []);
   C4 rv; CB 12 (nth 9 p []); C4 gv; CB 12 (nth 10 p []); C4 bv].

(* [comment removed for export] *)
Definition d32_geom (lo sa fr datas datad wpls wpld w h r1 g1 b1 r2 g2 b2 : Z) : Prop :=
  0 < w <= 20000 /\ w <= wpls /\ w <= 32 * wpld /\ 0 < wpls <= 2^20 /\ 0 < wpld <= 2^20 /\ 0 < h <= 2^20
  /\ wpls * h <= 2^24 /\ wpld * h <= 2^24
  /\ 0 < datas /\ datas mod 8 = 0 /\ datas + 4 * (wpls * h) <= 2^47 /\ (datas + 4 * (wpls * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas)
  /\ (datas + 4 * (wpls * h) <= 0x10000 \/ SEGTOP_A <= datas)
  /\ 0 < datad /\ datad mod 8 = 0 /\ datad + 4 * (wpld * h) <= 2^47 /\ (datad + 4 * (wpld * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad)
  /\ (datad + 4 * (wpld * h) <= 0x10000 \/ SEGTOP_A <= datad)
  /\ (datas + 4 * (wpls * h) <= datad \/ datad + 4 * (wpld * h) <= datas)
  /\ 0 < fr /\ fr mod 8 = 0 /\ SEGTOP_A <= fr /\ (fr + 224 <= 0x7fff7000 \/ 0x10007fff8000 <= fr)
  /\ (fr + 224 <= datad \/ datad + 4 * (wpld * h) <= fr) /\ (fr + 224 <= datas \/ datas + 4 * (wpls * h) <= fr)
  /\ fr + 224 <= lo /\ datad + 4 * (wpld * h) <= lo /\ datas + 4 * (wpls * h) <= lo
  /\ 0x10007fff8000 <= lo /\ lo <= sa - 16 /\ sa mod 8 = 0 /\ sa + 192 <= 2^47
  /\ 0 <= r1 <= 255 /\ 0 <= g1 <= 255 /\ 0 <= b1 <= 255 /\ 0 <= r2 <= 255 /\ 0 <= g2 <= 255 /\ 0 <= b2 <= 255.

(* [comment removed for export] *)
Definition d32_row_exit (gp tp t1 t2 s0 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo sa fr datas datad wpls wpld w h i : Z) (ws : list word) (c16 c24 c32 c40 l88 : word)
    (dw : word) (r1 g1 b1 r2 g2 b2 : Z) (p : list (list byte)) : machine_state -> Prop :=
  fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s8' s10' : word) (m' : mem) (wd' : list word) (rv' gv' bv' : word),
    ms' = MS (mkR ra' (Z_to_bv 64 sa) gp tp (Z_to_bv 64 SHB) t1 t2 s0 (Z_to_bv 64 sa) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) (Z_to_bv 64 (datad + 4 * (i * wpld))) s5' (Z_to_bv 64 (fr + 176)) s7' s8' (Z_to_bv 64 1) s10'
                  (Z_to_bv 64 (datas + 4 * (i * wpls))) t3 t4 t5 t6)
             F (Z_to_bv 64 0xa2fd8) fc None m' (seg_rom asegs)
    /\ munch (D32_W datad (4 * (wpld * h)) sa fr) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sa
    /\ ro_cells asegs m' g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
    /\ ro_cells asegs m' g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpls * h))
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpld * h /\ acc asegs m' datad (4 * (wpld * h))
    /\ rw_cells asegs m' (sa + 16) (d32_slots c16 c24 c32 c40 wpls wpld (i * wpls) datas l88 datad fr)
    /\ rw_cells asegs m' (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv' gv' bv' p)
    /\ acc asegs m' (fr + 176) 4 /\ acc asegs m' (fr + 192) 4 /\ acc asegs m' (fr + 208) 4.

(* [comment removed for export] *)
Lemma swrap32_mod64 : forall d, -2147483648 <= d < 2147483648 -> bv_swrap 32 (d mod 18446744073709551616) = d.
Proof.
  intros d Hd. change (d mod 18446744073709551616) with (bv_wrap 64 d).
  rewrite <- (bv_swrap_wrap 32 (bv_wrap 64 d)). rewrite (bv_wrap_bv_wrap 32 64) by (clear; lia). rewrite bv_swrap_wrap.
  apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. exact Hd.
Qed.
Ltac abs_blk_tac d K :=
  destruct (Z_lt_ge_dec d 0) as [NEG|NN];
  [ lstep; brF; lstep; lstep; brF; lstep;
    replace (bv_swrap 32 (0 - d mod 18446744073709551616)) with (Z.abs d);
    [ apply K
    | rewrite <- (bv_swrap_wrap 32 (0 - d mod 18446744073709551616)); unfold bv_wrap; change (bv_modulus 32) with 4294967296;
      replace ((0 - d mod 18446744073709551616) mod 4294967296) with (- d) by (Z.div_mod_to_equations; lia);
      rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648; lia); lia ]
  | lstep; brT; replace d with (Z.abs d) by lia; apply K ].
Lemma d32_abs1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mq : mem) Q (d : Z),
  -2147483648 < d < 2147483648 ->
  (forall a1' : word, evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.abs d)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0xa3160) fc None mq (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xa3150) fc None mq (seg_rom asegs)).
Proof. intros until d. intros Hd K. abs_blk_tac d K. Qed.

Lemma d32_abs2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mq : mem) Q (d : Z),
  -2147483648 < d < 2147483648 ->
  (forall a2' : word, evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (Z.abs d)) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0xa3184) fc None mq (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 d) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xa3174) fc None mq (seg_rom asegs)).
Proof. intros until d. intros Hd K. abs_blk_tac d K. Qed.

Lemma d32_abs3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mq : mem) Q (d : Z),
  -2147483648 < d < 2147483648 ->
  (forall a3' : word, evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (Z.abs d)) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0xa31ac) fc None mq (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 d) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xa319c) fc None mq (seg_rom asegs)).
Proof. intros until d. intros Hd K. abs_blk_tac d K. Qed.

Lemma d32_abs4 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mq : mem) Q (d : Z),
  -2147483648 < d < 2147483648 ->
  (forall a4' : word, evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 (Z.abs d)) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0xa31d0) fc None mq (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 d) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xa31c0) fc None mq (seg_rom asegs)).
Proof. intros until d. intros Hd K. abs_blk_tac d K. Qed.

Lemma d32_abs5 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mq : mem) Q (d : Z),
  -2147483648 < d < 2147483648 ->
  (forall a6' : word, evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (Z.abs d)) a5 a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0xa31f8) fc None mq (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 d) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xa31e8) fc None mq (seg_rom asegs)).
Proof. intros until d. intros Hd K. abs_blk_tac d K. Qed.

Lemma d32_abs6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mq : mem) Q (d : Z),
  -2147483648 < d < 2147483648 ->
  (forall a5' : word, evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5' (Z_to_bv 64 (Z.abs d)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0xa321c) fc None mq (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 d) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xa320c) fc None mq (seg_rom asegs)).
Proof. intros until d. intros Hd K. abs_blk_tac d K. Qed.

(* [comment removed for export] *)
Local Ltac gen_abs d H1 H2 := let e := fresh "e" in let E := fresh "E" in let B := fresh "HE" in
  remember (Z.abs d) as e eqn:E; assert (B : 0 <= e <= 255) by (clear - E H1 H2; lia); clear E.

Lemma discr32_pixels : forall (k : nat) (j : Z)
    (ra gp tp t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem)
    (lo sa fr datas datad wpls wpld w h : Z) (ws wd : list word) (c16 c24 c32 c40 l88 : word) (i : Z)
    (dw : word) (r1 g1 b1 r2 g2 b2 : Z) (rv gv bv : word) (p : list (list byte)),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> 0 <= i < h -> d32_geom lo sa fr datas datad wpls wpld w h r1 g1 b1 r2 g2 b2 ->
  mem_inv asegs m -> stk asegs m lo sa ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpls * h -> acc asegs m datas (4 * (wpls * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpld * h -> acc asegs m datad (4 * (wpld * h)) ->
  rw_cells asegs m (sa + 16) (d32_slots c16 c24 c32 c40 wpls wpld (i * wpls) datas l88 datad fr) ->
  rw_cells asegs m (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv gv bv p) ->
  acc asegs m (fr + 176) 4 -> acc asegs m (fr + 192) 4 -> acc asegs m (fr + 208) 4 ->
  evt asegs (d32_row_exit gp tp t1 t2 s0 t3 t4 t5 t6 F fc m lo sa fr datas datad wpls wpld w h i ws c16 c24 c32 c40 l88 dw r1 g1 b1 r2 g2 b2 p)
    (MS (mkR ra (Z_to_bv 64 sa) gp tp (Z_to_bv 64 SHB) t1 t2 s0 (Z_to_bv 64 sa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) (Z_to_bv 64 (datad + 4 * (i * wpld))) (Z_to_bv 64 j) (Z_to_bv 64 (fr + 176))
             (Z_to_bv 64 (datas + 4 * (i * wpls + j))) (Z_to_bv 64 j) (Z_to_bv 64 1) (Z_to_bv 64 (datas + 4 * (i * wpls + j)))
             (Z_to_bv 64 (datas + 4 * (i * wpls))) t3 t4 t5 t6)
        F (Z_to_bv 64 0xa30e0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra gp tp t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m lo sa fr datas datad wpls wpld w h ws wd
    c16 c24 c32 c40 l88 i dw r1 g1 b1 r2 g2 b2 rv gv bv p
    HK HJ HK1 HI GEO MI ST G1 G2 UAS UASL ACCS UA UAL ACCD SL FA ARV AGV ABV.
  { exfalso; clear - HK1; lia. }
  pose proof GEO as (HW & WS & WD & WPLS & WPLD & HH & SH & DH & S0 & S8 & SHI & SSH & SSEG & D0 & D8 & DHI & DSH & DSEG & SEP
                     & FR0 & FR8 & FRSEG & FRSH & FRD & FRS & FRLO & DLO & SLO & LOH & LOS & SA8 & SAHI & HR1 & HG1 & HB1 & HR2 & HG2 & HB2).
  assert (NS : i * wpls + wpls <= wpls * h) by (clear - HI WPLS; nia).
  assert (NS0 : 0 <= i * wpls) by (clear - HI WPLS; nia).
  assert (ND : i * wpld + wpld <= wpld * h) by (clear - HI WPLD; nia).
  assert (ND0 : 0 <= i * wpld) by (clear - HI WPLD; nia).
  assert (JD : 0 <= j / 32 < wpld) by (clear - HJ HK WD HW; Z.div_mod_to_equations; lia).
  unfold d32_slots in SL. unfold d32_fcells in FA.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl (D32_W datad (4 * (wpld * h)) sa fr) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT : forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' : word) (mm : mem) (wd' : list word) (rv' gv' bv' : word),
    munch (D32_W datad (4 * (wpld * h)) sa fr) m mm -> wmono asegs m mm -> mem_inv asegs mm -> stk asegs mm lo sa ->
    ro_cells asegs mm 965088 [C8 (Z_to_bv 64 1013304)] -> ro_cells asegs mm 1013304 [C8 (Z_to_bv 64 2147450880)] ->
    u32arr asegs mm datas ws -> acc asegs mm datas (4 * (wpls * h)) ->
    u32arr asegs mm datad wd' -> Z.of_nat (length wd') = wpld * h -> acc asegs mm datad (4 * (wpld * h)) ->
    rw_cells asegs mm (sa + 16)
      [C8 c16; C8 c24; C8 c32; C8 c40; C8 (Z_to_bv 64 wpls); C8 (Z_to_bv 64 wpld); C8 (Z_to_bv 64 (fr + 48)); C8 (Z_to_bv 64 (i * wpls));
       C8 (Z_to_bv 64 datas); C8 l88; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 1);
       C8 (Z_to_bv 64 (fr + 160)); C8 (Z_to_bv 64 (fr + 112)); C8 (Z_to_bv 64 (fr + 144)); C8 (Z_to_bv 64 (fr + 96)); C8 (Z_to_bv 64 (fr + 128)); C8 (Z_to_bv 64 (fr + 80));
       C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 (fr + 32))] ->
    rw_cells asegs mm (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv' gv' bv' p) ->
    acc asegs mm (fr + 176) 4 -> acc asegs mm (fr + 192) 4 -> acc asegs mm (fr + 208) 4 ->
    evt asegs (d32_row_exit gp tp t1 t2 s0 t3 t4 t5 t6 F fc m lo sa fr datas datad wpls wpld w h i ws c16 c24 c32 c40 l88 dw r1 g1 b1 r2 g2 b2 p)
      (MS (mkR ra' (Z_to_bv 64 sa) gp tp (Z_to_bv 64 2147450880) t1 t2 s0 (Z_to_bv 64 sa) a0' a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) (Z_to_bv 64 (datad + 4 * (i * wpld))) (Z_to_bv 64 j) (Z_to_bv 64 (fr + 176))
               (Z_to_bv 64 (datas + 4 * (i * wpls + j))) (Z_to_bv 64 j) (Z_to_bv 64 1) (Z_to_bv 64 (datas + 4 * (i * wpls + j)))
               (Z_to_bv 64 (datas + 4 * (i * wpls))) t3 t4 t5 t6)
          F (Z_to_bv 64 0xa30c4) fc None mm (seg_rom asegs))).
  { intros ra' a0' a1' a2' a3' a4' a5' a6' a7' mm wd' rv' gv' bv' MU1 WM1 MI1 ST1 G11 G21 UAS1 ACCS1 UA1 UAL1 ACCD1 SL1 FA1 ARV1 AGV1 ABV1.
    clear MI ST G1 G2 UAS ACCS UA UAL ACCD SL FA ARV AGV ABV MU WM.
    unfold d32_fcells in FA1.
    lwalk [0xa30e0; 0xa2fd8]. sx32_fix.
    replace (datas + 4 * (i * wpls + j) + 4) with (datas + 4 * (i * wpls + (j + 1))) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold d32_row_exit, d32_slots, d32_fcells, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB.
      do 13 eexists. exists mm, wd', rv', gv', bv'. split; [reflexivity|].
      repeat (split; [assumption|]). assumption.
    - brF.
      eapply evt_cut.
      + eapply (IH (j + 1)) with (ws := ws) (wd := wd') (h := h) (lo := lo) (l88 := l88) (c16 := c16) (c24 := c24) (c32 := c32) (c40 := c40)
                                 (dw := dw) (r1 := r1) (g1 := g1) (b1 := b1) (r2 := r2) (g2 := g2) (b2 := b2) (rv := rv') (gv := gv') (bv := bv') (p := p);
          try eassumption; try lia.
      + intros ms' PO. apply evt_done. unfold d32_row_exit in PO |- *.
        destruct PO as (ra'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & s5'' & s7'' & s8'' & s10'' & m' & wd'' & rv'' & gv'' & bv'' & E & MU' & WM' & R).
        exists ra'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', s5'', s7'', s8'', s10'', m', wd'', rv'', gv'', bv''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU1 MU')|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact R]. }
  idtac "MARK CONT".
  (* [comment removed for export] *)
  lwalk [0xa3108; 0xa3378].
  destruct (u32arr_nth ws (i * wpls + j) ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datas ws (i * wpls + j) wv _ UAS NTH ltac:(lia) eq_refl) as R.
  lstep. clear R.
  park_disj. unfold parked in FRD, FRS.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  lwalk [0xa311c; 0x96f4c; 0x96f60; 0x96f74].
  idtac "MARK leaf".
  (* [comment removed for export] *)
  set (uu := bv_unsigned (sx32 wv)) in *.
  rewrite (swrap32_small (bv_wrap 32 uu / 16777216)) in * by (pose proof (rgb_r_range uu) as RR; unfold rgb_r in RR; clear - RR; lia).
  change (bv_wrap 32 uu / 16777216) with (rgb_r uu) in *.
  change ((uu * 1099511627776) mod 18446744073709551616 / 72057594037927936) with (rgb_g uu) in *.
  change ((uu * 281474976710656) mod 18446744073709551616 / 72057594037927936) with (rgb_b uu) in *.
  pose proof (rgb_r_range uu) as XR. pose proof (rgb_g_range uu) as XG. pose proof (rgb_b_range uu) as XB.
  remember (rgb_r uu) as xr eqn:E; clear E. remember (rgb_g uu) as xg eqn:E; clear E. remember (rgb_b uu) as xb eqn:E; clear E.
  (* [comment removed for export] *)
  lwalk [0xa3148; 0xa3234; 0xa35dc].
  rewrite ?(sx32_small r1), ?(sx32_small xr) by lia. rewrite ?(unsigned_lit r1), ?(unsigned_lit xr) by lia.
  rewrite (swrap32_small (r1 - xr)) by lia. rewrite Z.lxor_nilpotent. change (0 <? 0) with false. change (Z.b2z false) with 0.
  lwalk [0xa3150; 0xa35dc]. rewrite Z.add_0_r. rewrite (swrap32_mod64 (r1 - xr)) by lia.
  apply d32_abs1; [clear - HR1 XR; lia| intros ax1]. gen_abs (r1 - xr) HR1 XR.
  idtac "MARK abs1".
  (* [comment removed for export] *)
  lwalk [0xa3170; 0xa35dc]. rewrite ?(sx32_small r2), ?(unsigned_lit r2), ?(unsigned_lit xr) by lia. rewrite (swrap32_small (r2 - xr)) by lia.
  lwalk [0xa3174; 0xa35dc]. apply d32_abs2; [clear - HR2 XR; lia| intros ax2]. gen_abs (r2 - xr) HR2 XR.
  lwalk [0xa3198; 0xa35dc]. rewrite ?(sx32_small g1), ?(sx32_small xg), ?(unsigned_lit g1), ?(unsigned_lit xg) by lia. rewrite (swrap32_small (g1 - xg)) by lia.
  lwalk [0xa319c; 0xa35dc]. apply d32_abs3; [clear - HG1 XG; lia| intros ax3]. gen_abs (g1 - xg) HG1 XG.
  lwalk [0xa31bc; 0xa35dc]. rewrite ?(sx32_small g2), ?(unsigned_lit g2), ?(unsigned_lit xg) by lia. rewrite (swrap32_small (g2 - xg)) by lia.
  lwalk [0xa31c0; 0xa35dc]. apply d32_abs4; [clear - HG2 XG; lia| intros ax4]. gen_abs (g2 - xg) HG2 XG.
  lwalk [0xa31e4; 0xa35dc]. rewrite ?(sx32_small b1), ?(sx32_small xb), ?(unsigned_lit b1), ?(unsigned_lit xb) by lia. rewrite (swrap32_small (b1 - xb)) by lia.
  lwalk [0xa31e8; 0xa35dc]. apply d32_abs5; [clear - HB1 XB; lia| intros ax5]. gen_abs (b1 - xb) HB1 XB.
  lwalk [0xa3208; 0xa35dc]. rewrite ?(sx32_small b2), ?(unsigned_lit b2), ?(unsigned_lit xb) by lia. rewrite (swrap32_small (b2 - xb)) by lia.
  lwalk [0xa320c; 0xa35dc]. apply d32_abs6; [clear - HB2 XB; lia| intros ax6]. gen_abs (b2 - xb) HB2 XB.
  idtac "MARK abs6".
  (* [comment removed for export] *)
  lwalk [0xa322c; 0xa35dc].
  idtac "MARK at bgeu".
  swrap_fix.
  lwalk [0xa30c4; 0xa331c; 0xa35dc].
  brfork DD; [solve [eapply CONT; eassumption]|].
  idtac "MARK DD".
  (* [comment removed for export] *)
  lwalk [0xa3328; 0xa35dc].
  rewrite !(srliw_idx j 32) by lia.
  replace (datad + 4 * (i * wpld) + j / 32 * 4) with (datad + 4 * (i * wpld + j / 32)) by lia.
  rewrite ?(Z.mod_small (datad + 4 * (i * wpld + j / 32)) 18446744073709551616) by lia.
  remember (i * wpld + j / 32) as idx eqn:EI.
  assert (IDX : 0 <= idx /\ i * wpld <= idx /\ idx + 1 <= wpld * h) by (subst idx; clear - ND ND0 JD; lia).
  unfold parked in DSH, DSEG.
  lwalk [0xa30b0; 0xa3628; 0xa35dc].
  idtac "MARK at lw dest".
  clear EI JD.
  lazymatch goal with UAx : u32arr asegs ?mm datad ?wdx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (u32arr_nth wdx idx ltac:(lia)) as (dv & NTHD);
    pose proof (u32arr_read asegs mm datad wdx idx dv _ UAx NTHD ltac:(lia) eq_refl) as R end.
  lstep. clear R.
  lwalk [0xa30c0].
  unfold parked in SEP.
  arr_sw datad idx (datad + 4 * idx).
  idtac "MARK arr_sw".
  eapply CONT; eassumption.
Qed.

(* [comment removed for export] *)
Definition d32_exit (gp tp t1 t2 s0 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo sa fr datas datad wpls wpld w h : Z) (ws : list word) (c16 c24 c32 c40 : word)
    (dw : word) (r1 g1 b1 r2 g2 b2 : Z) (p : list (list byte)) : machine_state -> Prop :=
  fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s7' s8' s10' s11' : word) (m' : mem) (wd' : list word) (rv' gv' bv' l88' : word) (acc' : Z),
    ms' = MS (mkR ra' (Z_to_bv 64 sa) gp tp (Z_to_bv 64 SHB) t1 t2 s0 (Z_to_bv 64 sa) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) s4' s5' (Z_to_bv 64 (fr + 176)) s7' s8' (Z_to_bv 64 1) s10' s11' t3 t4 t5 t6)
             F (Z_to_bv 64 0xa35c8) fc None m' (seg_rom asegs)
    /\ munch (D32_W datad (4 * (wpld * h)) sa fr) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sa
    /\ ro_cells asegs m' g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
    /\ ro_cells asegs m' g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpls * h))
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpld * h /\ acc asegs m' datad (4 * (wpld * h))
    /\ rw_cells asegs m' (sa + 16) (d32_slots c16 c24 c32 c40 wpls wpld acc' datas l88' datad fr)
    /\ rw_cells asegs m' (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv' gv' bv' p)
    /\ acc asegs m' (fr + 176) 4 /\ acc asegs m' (fr + 192) 4 /\ acc asegs m' (fr + 208) 4.

Lemma discr32_rows : forall (k : nat) (i : Z)
    (ra gp tp t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s4 s5 s7 s8 s10 t3 t4 t5 t6 : word) F fc (m : mem)
    (lo sa fr datas datad wpls wpld w h : Z) (ws wd : list word) (c16 c24 c32 c40 l88 : word)
    (dw : word) (r1 g1 b1 r2 g2 b2 : Z) (rv gv bv : word) (p : list (list byte)),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> d32_geom lo sa fr datas datad wpls wpld w h r1 g1 b1 r2 g2 b2 ->
  mem_inv asegs m -> stk asegs m lo sa ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpls * h -> acc asegs m datas (4 * (wpls * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpld * h -> acc asegs m datad (4 * (wpld * h)) ->
  rw_cells asegs m (sa + 16) (d32_slots c16 c24 c32 c40 wpls wpld (i * wpls) datas l88 datad fr) ->
  rw_cells asegs m (fr + 32) (d32_fcells w h dw r1 g1 b1 r2 g2 b2 rv gv bv p) ->
  acc asegs m (fr + 176) 4 -> acc asegs m (fr + 192) 4 -> acc asegs m (fr + 208) 4 ->
  evt asegs (d32_exit gp tp t1 t2 s0 t3 t4 t5 t6 F fc m lo sa fr datas datad wpls wpld w h ws c16 c24 c32 c40 dw r1 g1 b1 r2 g2 b2 p)
    (MS (mkR ra (Z_to_bv 64 sa) gp tp (Z_to_bv 64 SHB) t1 t2 s0 (Z_to_bv 64 sa) a0 a1 (Z_to_bv 64 i) a3 a4 a5 a6 a7
             (Z_to_bv 64 (fr + 192)) (Z_to_bv 64 (fr + 208)) s4 s5 (Z_to_bv 64 (fr + 176)) s7 s8 (Z_to_bv 64 1) s10 (Z_to_bv 64 wpls) t3 t4 t5 t6)
        F (Z_to_bv 64 0xa2ffc) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra gp tp t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s4 s5 s7 s8 s10 t3 t4 t5 t6 F fc m lo sa fr datas datad wpls wpld w h ws wd
    c16 c24 c32 c40 l88 dw r1 g1 b1 r2 g2 b2 rv gv bv p
    HK HI HK1 GEO MI ST G1 G2 UAS UASL ACCS UA UAL ACCD SL FA ARV AGV ABV.
  { exfalso; clear - HK1; lia. }
  pose proof GEO as (HW & WS & WD & WPLS & WPLD & HH & SH & DH & S0 & S8 & SHI & SSH & SSEG & D0 & D8 & DHI & DSH & DSEG & SEP
                     & FR0 & FR8 & FRSEG & FRSH & FRD & FRS & FRLO & DLO & SLO & LOH & LOS & SA8 & SAHI & HR1 & HG1 & HB1 & HR2 & HG2 & HB2).
  assert (NS0 : 0 <= i * wpls /\ i * wpls + wpls <= wpls * h) by (clear - HI HK HH WPLS SH; nia).
  assert (ND0 : 0 <= i * wpld /\ i * wpld + wpld <= wpld * h) by (clear - HI HK HH WPLD DH; nia).
  unfold d32_slots in SL. unfold d32_fcells in FA.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl (D32_W datad (4 * (wpld * h)) sa fr) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj. unfold parked in FRD, FRS.
  (* [comment removed for export] *)
  lwalk [0xa30e0; 0xa2fd8; 0xa35dc].
  idtac "MARK row head walked".
  rewrite !Z.add_0_r. rewrite !(Z.mod_small (i * wpld)), !(Z.mod_small (i * wpls)) by lia.
  replace (datad + i * wpld * 4) with (datad + 4 * (i * wpld)) by lia.
  replace (datas + i * wpls * 4) with (datas + 4 * (i * wpls)) by lia.
  (* [comment removed for export] *)
  assert (Q1 : Z.of_nat (Z.to_nat w) = w - 0) by (clear - HW; lia).
  assert (Q3 : (1 <= Z.to_nat w)%nat) by (clear - HW; lia).
  assert (Q4 : 0 <= i < h) by (clear - HI HK; lia).
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm, STx : stk asegs ?mm lo sa, G1x : ro_cells asegs ?mm 965088 _, G2x : ro_cells asegs ?mm 1013304 _,
        UASx : u32arr asegs ?mm datas ws, ACCSx : acc asegs ?mm datas _, UAx : u32arr asegs ?mm datad ?wdx, ACCDx : acc asegs ?mm datad _,
        SLx : rw_cells asegs ?mm (sa + 16) _, FAx : rw_cells asegs ?mm (fr + 32) _,
        ARVx : acc asegs ?mm (fr + 176) 4, AGVx : acc asegs ?mm (fr + 192) 4, ABVx : acc asegs ?mm (fr + 208) 4
        |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (discr32_pixels (Z.to_nat w) 0 _ gp tp t1 t2 s0 _ _ _ _ _ _ _ _ t3 t4 t5 t6 F0 fc0 mm lo sa fr datas datad wpls wpld w h ws wdx
                     c16 c24 c32 c40 _ i dw r1 g1 b1 r2 g2 b2 rv gv bv p
                     Q1 ltac:(clear; lia) Q3 Q4 GEO MIx STx G1x G2x UASx UASL ACCSx UAx UAL ACCDx SLx FAx ARVx AGVx ABVx) as ZR end.
    unfold SHB in ZR.
    replace (datas + 4 * (i * wpls + 0)) with (datas + 4 * (i * wpls)) in ZR by (clear; lia).
    exact ZR. }
  idtac "MARK pixels applied".
  intros ms' PO. unfold d32_row_exit in PO.
  destruct PO as (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s5' & s7' & s8' & s10' & m' & wd' & rv' & gv' & bv' & -> & MU' & WM' & MI' & ST'
                  & G1' & G2' & UAS' & ACCS' & UA' & UAL' & ACCD' & SL' & FA' & ARV' & AGV' & ABV').
  lazymatch type of MU' with munch _ ?mo _ =>
    lazymatch goal with MUo : munch _ m mo, WMo : wmono asegs m mo |- _ =>
      pose proof (munch_trans _ _ _ _ MUo MU') as MUc; pose proof (wmono_trans asegs _ _ _ WMo WM') as WMc; clear MUo WMo MU' WM' end;
    repeat match goal with
    | H : rw_cells asegs mo _ _ |- _ => clear H | H : u32arr asegs mo _ _ |- _ => clear H | H : acc asegs mo _ _ |- _ => clear H
    | H : ro_cells asegs mo _ _ |- _ => clear H | H : stk asegs mo _ _ |- _ => clear H | H : mem_inv asegs mo |- _ => clear H end end.
  unfold d32_slots, d32_fcells, SHB, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  idtac "MARK row end".
  (* [comment removed for export] *)
  lwalk [0xa2ff4; 0xa35c8; 0xa2ffc].
  idtac "MARK at acc store".
  rewrite (sx32_small h) by lia.
  swrap_fix.
  replace (i * wpls + wpls) with ((i + 1) * wpls) by (clear; lia).
  lstep.
  lstep.
  destruct k as [|k].
  - assert (EI : i + 1 = h) by lia. rewrite EI in *.
    brT. apply evt_done. unfold d32_exit, d32_slots, d32_fcells, SHB, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address.
    do 15 eexists. lazymatch goal with |- exists (m' : mem), _ => idtac end.
    eexists. exists wd', rv', gv', bv'. do 2 eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
    repeat (split; [eassumption|]). eassumption.
  - brF.
    idtac "MARK before IH".
    eapply evt_cut.
    + eapply (IH (i + 1)) with (ws := ws) (wd := wd') (w := w) (lo := lo) (dw := dw) (r1 := r1) (g1 := g1) (b1 := b1) (r2 := r2) (g2 := g2) (b2 := b2)
                               (rv := rv') (gv := gv') (bv := bv') (p := p) (c16 := c16) (c24 := c24) (c32 := c32) (c40 := c40);
        try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold d32_exit in PO |- *.
      destruct PO as (ra'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & s4'' & s5'' & s7'' & s8'' & s10'' & s11'' & m'' & wd'' & rv'' & gv'' & bv'' & l88'' & acc'' & E & MU'' & WM'' & R).
      exists ra'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', s4'', s5'', s7'', s8'', s10'', s11'', m'', wd'', rv'', gv'', bv'', l88'', acc''.
      split; [exact E|].
      lazymatch goal with MUx : munch _ m ?mx, WMx : wmono asegs m ?mx |- _ =>
        split; [exact (munch_trans _ _ _ _ MUx MU'')|]; split; [exact (wmono_trans asegs _ _ _ WMx WM'')| exact R] end.
Qed.

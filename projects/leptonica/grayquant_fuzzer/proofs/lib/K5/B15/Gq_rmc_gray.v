(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import FpBound.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptGrayFP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Ed_fpkit Gq_numa Gq_rmc_statics LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition fa2 : bv 5 := Z_to_bv 5 12.
Definition fa3 : bv 5 := Z_to_bv 5 13.
Definition fa4 : bv 5 := Z_to_bv 5 14.
Definition fa5 : bv 5 := Z_to_bv 5 15.
Definition gray_consts (F : bvmap 5 word) : Prop :=
  bv_unsigned (unbox_s (reg_get F fa0)) = GC_05f /\ bv_unsigned (unbox_s (reg_get F fa5)) = GC_03f /\ bv_unsigned (unbox_s (reg_get F fa4)) = GC_02f
  /\ bv_unsigned (reg_get F fa3) = GC_05d /\ bv_unsigned (reg_get F fa2) = GC_m1d /\ bv_unsigned (reg_get F fa1) = GC_2p32d.

Definition bytew (w : word) : Prop := bv_unsigned w <= 255.

(* [comment removed for export] *)
Definition gray_exit (ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (sb gm rmap n : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a2' a3' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) s0 (Z_to_bv 64 sb) (Z_to_bv 64 gm) (Z_to_bv 64 (rmap + 4 * n)) a2' a3'
                  (Z_to_bv 64 1) (Z_to_bv 64 (4 * n)) (Z_to_bv 64 rmap) (Z_to_bv 64 (4 * n)) (Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0x9c114) (frm_clear fc') None m' (seg_rom asegs)
    /\ munch [(gm, gm + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

(* [comment removed for export] *)
Lemma u32_lit : forall z, 0 <= z < 2 ^ 32 -> bv_unsigned (Z_to_bv 32 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact Hz. Qed.
Lemma sx32_bytew : forall w : word, bv_unsigned w <= 255 -> bv_unsigned (sx32 w) = bv_unsigned w.
Proof. intros w Hw. unfold sx32. pose proof (bv_unsigned_in_range 64 w). rewrite swrap32_small by lia. apply unsigned_lit. lia. Qed.

(* [comment removed for export] *)
Lemma gray_chain_eq : forall (w0 w5 w4 w3 xr xg xb : word),
  bv_unsigned (unbox_s w0) = GC_05f -> bv_unsigned (unbox_s w5) = GC_03f -> bv_unsigned (unbox_s w4) = GC_02f -> bv_unsigned w3 = GC_05d ->
  0 <= bv_unsigned xr < 256 -> 0 <= bv_unsigned xg < 256 -> 0 <= bv_unsigned xb < 256 ->
  bv_unsigned (fadd_d RNE (fcvt_d_s RNE (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 xb)) w4 (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 xr)) w5 (fmul_s RNE (fcvt_s_w RNE (sx32 xg)) w0)))) w3)
  = gray_5 RNE (bv_unsigned xr) (bv_unsigned xg) (bv_unsigned xb).
Proof.
  intros w0 w5 w4 w3 xr xg xb E0 E5 E4 E3 Hr Hg Hb.
  unfold fadd_d, fcvt_d_s, fma_s, fmul_s, fcvt_s_w, fma_opnds. cbn [fst snd]. rewrite !unbox_nan_box.
  rewrite E0, E5, E4, E3. rewrite !sx32_bytew by lia.
  change (fst (fp_of_int fmt_single RNE true 32 (bv_unsigned xg))) with (gray_i RNE (bv_unsigned xg)).
  change (fst (fp_of_int fmt_single RNE true 32 (bv_unsigned xr))) with (gray_i RNE (bv_unsigned xr)).
  change (fst (fp_of_int fmt_single RNE true 32 (bv_unsigned xb))) with (gray_i RNE (bv_unsigned xb)).
  rewrite !(u32_lit (gray_i RNE _)) by (first [exact (FB_range_single _ _ (gray_i_FB RNE _ Hg)) | exact (FB_range_single _ _ (gray_i_FB RNE _ Hr)) | exact (FB_range_single _ _ (gray_i_FB RNE _ Hb))]).
  change (fst (fp_mul fmt_single RNE (gray_i RNE (bv_unsigned xg)) GC_05f)) with (gray_1 RNE (bv_unsigned xg)).
  rewrite (u32_lit (gray_1 RNE _)) by (exact (FB_range_single _ _ (gray_1_FB RNE _ Hg))).
  change (fst (fp_fma fmt_single RNE (gray_i RNE (bv_unsigned xr)) GC_03f (gray_1 RNE (bv_unsigned xg)))) with (gray_2 RNE (bv_unsigned xr) (bv_unsigned xg)).
  rewrite (u32_lit (gray_2 RNE _ _)) by (exact (FB_range_single _ _ (gray_2_FB RNE _ _ Hr Hg))).
  change (fst (fp_fma fmt_single RNE (gray_i RNE (bv_unsigned xb)) GC_02f (gray_2 RNE (bv_unsigned xr) (bv_unsigned xg)))) with (gray_3 RNE (bv_unsigned xr) (bv_unsigned xg) (bv_unsigned xb)).
  rewrite (u32_lit (gray_3 RNE _ _ _)) by (exact (FB_range_single _ _ (gray_3_FB RNE _ _ _ Hr Hg Hb))).
  change (fst (fp_convert fmt_single fmt_double RNE (gray_3 RNE (bv_unsigned xr) (bv_unsigned xg) (bv_unsigned xb)))) with (gray_4 RNE (bv_unsigned xr) (bv_unsigned xg) (bv_unsigned xb)).
  rewrite (unsigned_lit (gray_4 RNE _ _ _)) by (exact (FB_range_double _ _ (gray_4_FB RNE _ _ _ Hr Hg Hb))).
  change (fst (fp_add fmt_double RNE (gray_4 RNE (bv_unsigned xr) (bv_unsigned xg) (bv_unsigned xb)) GC_05d)) with (gray_5 RNE (bv_unsigned xr) (bv_unsigned xg) (bv_unsigned xb)).
  apply unsigned_lit. exact (FB_range_double _ _ (gray_5_FB RNE _ _ _ Hr Hg Hb)).
Qed.

(* [comment removed for export] *)
Lemma gray_cast_lo : forall (w0 w5 w4 w3 w2 xr xg xb : word),
  bv_unsigned (unbox_s w0) = GC_05f -> bv_unsigned (unbox_s w5) = GC_03f -> bv_unsigned (unbox_s w4) = GC_02f -> bv_unsigned w3 = GC_05d -> bv_unsigned w2 = GC_m1d ->
  bv_unsigned xr <= 255 -> bv_unsigned xg <= 255 -> bv_unsigned xb <= 255 ->
  flt_d w2 (fadd_d RNE (fcvt_d_s RNE (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 xb)) w4 (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 xr)) w5 (fmul_s RNE (fcvt_s_w RNE (sx32 xg)) w0)))) w3) = true.
Proof.
  intros w0 w5 w4 w3 w2 xr xg xb E0 E5 E4 E3 E2 BR BG BB.
  pose proof (bv_unsigned_in_range 64 xr). pose proof (bv_unsigned_in_range 64 xg). pose proof (bv_unsigned_in_range 64 xb).
  unfold flt_d. rewrite E2. rewrite (gray_chain_eq w0 w5 w4 w3 xr xg xb E0 E5 E4 E3) by lia.
  apply (gray_guard_lo RNE); lia.
Qed.
Lemma gray_cast_hi : forall (w0 w5 w4 w3 w1 xr xg xb : word),
  bv_unsigned (unbox_s w0) = GC_05f -> bv_unsigned (unbox_s w5) = GC_03f -> bv_unsigned (unbox_s w4) = GC_02f -> bv_unsigned w3 = GC_05d -> bv_unsigned w1 = GC_2p32d ->
  bv_unsigned xr <= 255 -> bv_unsigned xg <= 255 -> bv_unsigned xb <= 255 ->
  flt_d (fadd_d RNE (fcvt_d_s RNE (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 xb)) w4 (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 xr)) w5 (fmul_s RNE (fcvt_s_w RNE (sx32 xg)) w0)))) w3) w1 = true.
Proof.
  intros w0 w5 w4 w3 w1 xr xg xb E0 E5 E4 E3 E1 BR BG BB.
  pose proof (bv_unsigned_in_range 64 xr). pose proof (bv_unsigned_in_range 64 xg). pose proof (bv_unsigned_in_range 64 xb).
  unfold flt_d. rewrite E1. rewrite (gray_chain_eq w0 w5 w4 w3 xr xg xb E0 E5 E4 E3) by lia.
  apply (gray_guard_hi RNE); lia.
Qed.

(* [comment removed for export] *)
Lemma gray_consts_set01 : forall (G : bvmap 5 word) (x y : word), gray_consts G -> gray_consts (bvmap_set (Z_to_bv 5 0) x (bvmap_set (Z_to_bv 5 1) y G)).
Proof.
  intros G x y (E0 & E5 & E4 & E3 & E2 & E1). unfold gray_consts, fa0, fa1, fa2, fa3, fa4, fa5 in *.
  rewrite !reg_get_set_other; [repeat split; assumption | ..];
  (intros H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H).
Qed.

Lemma gray_loop : forall (k : nat) (i : Z)
    (ra sp gp tp s0 a2 a3 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (sb pg pb rmap gmap bmap gm n : Z) (rs gs bs ws : list word),
  Z.of_nat k = n - i -> 0 <= i -> (1 <= k)%nat -> n <= 256 -> gray_consts F ->
  u32arr asegs m rmap rs -> Z.of_nat (length rs) = n -> acc asegs m rmap (4 * n) -> Forall bytew rs ->
  0 < rmap -> rmap mod 8 = 0 -> rmap + 4 * n <= 2^47 -> (rmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= rmap) -> (rmap + 4 * n <= 0x10000 \/ SEGTOP_A <= rmap) ->
  u32arr asegs m gmap gs -> Z.of_nat (length gs) = n -> acc asegs m gmap (4 * n) -> Forall bytew gs ->
  0 < gmap -> gmap mod 8 = 0 -> gmap + 4 * n <= 2^47 -> (gmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= gmap) -> (gmap + 4 * n <= 0x10000 \/ SEGTOP_A <= gmap) ->
  u32arr asegs m bmap bs -> Z.of_nat (length bs) = n -> acc asegs m bmap (4 * n) -> Forall bytew bs ->
  0 < bmap -> bmap mod 8 = 0 -> bmap + 4 * n <= 2^47 -> (bmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= bmap) -> (bmap + 4 * n <= 0x10000 \/ SEGTOP_A <= bmap) ->
  u32arr asegs m gm ws -> Z.of_nat (length ws) = 256 -> acc asegs m gm 1024 ->
  0 < gm -> gm mod 8 = 0 -> gm + 1024 <= 2^47 -> (gm + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gm) -> (gm + 1024 <= 0x10000 \/ SEGTOP_A <= gm) ->
  (gm + 1024 <= rmap \/ rmap + 4 * n <= gm) -> (gm + 1024 <= gmap \/ gmap + 4 * n <= gm) -> (gm + 1024 <= bmap \/ bmap + 4 * n <= gm) ->
  rw_cells asegs m (sb + 56) [C8 (Z_to_bv 64 pb); C8 (Z_to_bv 64 pg)] -> rw_cells asegs m pg [C8 (Z_to_bv 64 gmap)] -> rw_cells asegs m pb [C8 (Z_to_bv 64 bmap)] ->
  0 < sb -> sb + 72 <= 2^47 -> (gm + 1024 <= sb + 56 \/ sb + 72 <= gm) -> 0x10007fff8000 <= sb ->
  0 < pg -> pg + 8 <= 2^47 -> (gm + 1024 <= pg \/ pg + 8 <= gm) -> (pg + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= pg) ->
  0 < pb -> pb + 8 <= 2^47 -> (gm + 1024 <= pb \/ pb + 8 <= gm) -> (pb + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= pb) ->
  mem_inv asegs m ->
  evt asegs (gray_exit ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 sb gm rmap n m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) s0 (Z_to_bv 64 sb) (Z_to_bv 64 gm) (Z_to_bv 64 (rmap + 4 * i)) a2 a3
             (Z_to_bv 64 1) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 rmap) (Z_to_bv 64 (4 * n)) (Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9bf6c) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp s0 a2 a3 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sb pg pb rmap gmap bmap gm n rs gs bs ws
    HK HI HK1 HN GC
    UAR UARL ACCR BYR R0 R8 RHI RSH RSEG UAG UAGL ACCG BYG G0 G8 GHI GSH GSEG UAB UABL ACCB BYB B0 B8 BHI BSH BSEG UAW UAWL ACCW W0 W8 WHI WSH WSEG
    SWR SWG SWB SL PG PB SB0 SBHI SBW SBH PG0 PGHI PGW PGSH PB0 PBHI PBW PBSH MI.
  { exfalso; clear - HK1; lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(gm, gm + 1024)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  pose proof GC as (E0 & E5 & E4 & E3 & E2 & E1).
  (* [comment removed for export] *)
  lwalk [0x9bfec; 0x9d5cc; 0x9c0dc].
  destruct (u32arr_nth rs i ltac:(lia)) as (rv & NTHR).
  pose proof (u32arr_read asegs m rmap rs i rv _ UAR NTHR ltac:(lia) eq_refl) as R.
  lstep. clear R.
  pose proof (proj1 (Forall_forall bytew rs) BYR rv (nth_error_In _ _ NTHR)) as BR. unfold bytew in BR.
  (* [comment removed for export] *)
  lwalk [0x9c040; 0x9d5cc; 0x9c0ec].
  destruct (u32arr_nth gs i ltac:(lia)) as (gv & NTHG).
  pose proof (u32arr_read asegs m gmap gs i gv _ UAG NTHG ltac:(lia) eq_refl) as R.
  lstep. clear R.
  pose proof (proj1 (Forall_forall bytew gs) BYG gv (nth_error_In _ _ NTHG)) as BG. unfold bytew in BG.
  (* [comment removed for export] *)
  lwalk [0x9c04c; 0x9d5cc; 0x9c0fc].
  destruct (u32arr_nth bs i ltac:(lia)) as (bvv & NTHB).
  pose proof (u32arr_read asegs m bmap bs i bvv _ UAB NTHB ltac:(lia) eq_refl) as R.
  lstep. clear R.
  pose proof (proj1 (Forall_forall bytew bs) BYB bvv (nth_error_In _ _ NTHB)) as BB. unfold bytew in BB.
  (* [comment removed for export] *)
  lwalk [0x9c070; 0x9d5cc].
  lazymatch goal with |- context [bword (flt_d ?w2 (fadd_d RNE (fcvt_d_s RNE (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 ?xb)) ?w4 (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 ?xr)) ?w5 (fmul_s RNE (fcvt_s_w RNE (sx32 ?xg)) ?w0)))) ?w3))] =>
    rewrite (gray_cast_lo w0 w5 w4 w3 w2 xr xg xb E0 E5 E4 E3 E2 BR BG BB) end.
  cbn [bword].
  (* [comment removed for export] *)
  lwalk [0x9c07c; 0x9d5cc].
  lazymatch goal with |- context [bword (flt_d (fadd_d RNE (fcvt_d_s RNE (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 ?xb)) ?w4 (fma_s F_MADD RNE (fcvt_s_w RNE (sx32 ?xr)) ?w5 (fmul_s RNE (fcvt_s_w RNE (sx32 ?xg)) ?w0)))) ?w3) ?w1)] =>
    rewrite (gray_cast_hi w0 w5 w4 w3 w1 xr xg xb E0 E5 E4 E3 E1 BR BG BB) end.
  cbn [bword].
  (* [comment removed for export] *)
  lwalk [0x9c0c0; 0x9d5cc; 0x9c10c].
  unpark WSH. unpark SWR. unpark SWG. unpark SWB. unpark SBW. unpark PGW. unpark PBW.
  arr_sw gm i (gm + 4 * i).
  park WSH. park SWR. park SWG. park SWB. park SBW. park PGW. park PBW.
  (* [comment removed for export] *)
  lwalk [0x9bf6c; 0x9c114; 0x9d5cc].
  replace (4 * i + 4) with (4 * (i + 1)) by (clear; lia).
  replace (rmap + 4 * i + 4) with (rmap + 4 * (i + 1)) by (clear; lia).
  destruct k as [|k].
  - assert (EI : i + 1 = n) by (clear - HK; lia). rewrite EI.
    brF. lwalk [0x9c114].
    apply evt_done. unfold gray_exit. do 6 eexists. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM| exact MI].
  - brT.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (n := n) (pg := pg) (pb := pb) (gmap := gmap) (bmap := bmap); try eassumption; try (clear - HK HI HN; lia).
      (* [comment removed for export] *)
      eapply gray_consts_set01. exact GC.
    + intros ms' PO. apply evt_done. unfold gray_exit in PO |- *.
      destruct PO as (a2' & a3' & t3' & t4' & t5' & t6' & F' & fc' & m' & E & MU' & WM' & MI').
      exists a2', a3', t3', t4', t5', t6', F', fc', m'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact MI'].
Qed.

(* [comment removed for export] *)
Lemma gray_loop0 : forall
    (ra sp gp tp s0 a2 a3 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (sb pg pb rmap gmap bmap gm n : Z) (rs gs bs ws : list word),
  0 < n <= 256 -> gray_consts F ->
  u32arr asegs m rmap rs -> Z.of_nat (length rs) = n -> acc asegs m rmap (4 * n) -> Forall bytew rs ->
  0 < rmap -> rmap mod 8 = 0 -> rmap + 4 * n <= 2^47 -> (rmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= rmap) -> (rmap + 4 * n <= 0x10000 \/ SEGTOP_A <= rmap) ->
  u32arr asegs m gmap gs -> Z.of_nat (length gs) = n -> acc asegs m gmap (4 * n) -> Forall bytew gs ->
  0 < gmap -> gmap mod 8 = 0 -> gmap + 4 * n <= 2^47 -> (gmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= gmap) -> (gmap + 4 * n <= 0x10000 \/ SEGTOP_A <= gmap) ->
  u32arr asegs m bmap bs -> Z.of_nat (length bs) = n -> acc asegs m bmap (4 * n) -> Forall bytew bs ->
  0 < bmap -> bmap mod 8 = 0 -> bmap + 4 * n <= 2^47 -> (bmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= bmap) -> (bmap + 4 * n <= 0x10000 \/ SEGTOP_A <= bmap) ->
  u32arr asegs m gm ws -> Z.of_nat (length ws) = 256 -> acc asegs m gm 1024 ->
  0 < gm -> gm mod 8 = 0 -> gm + 1024 <= 2^47 -> (gm + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gm) -> (gm + 1024 <= 0x10000 \/ SEGTOP_A <= gm) ->
  (gm + 1024 <= rmap \/ rmap + 4 * n <= gm) -> (gm + 1024 <= gmap \/ gmap + 4 * n <= gm) -> (gm + 1024 <= bmap \/ bmap + 4 * n <= gm) ->
  rw_cells asegs m (sb + 56) [C8 (Z_to_bv 64 pb); C8 (Z_to_bv 64 pg)] -> rw_cells asegs m pg [C8 (Z_to_bv 64 gmap)] -> rw_cells asegs m pb [C8 (Z_to_bv 64 bmap)] ->
  0 < sb -> sb + 72 <= 2^47 -> (gm + 1024 <= sb + 56 \/ sb + 72 <= gm) -> 0x10007fff8000 <= sb ->
  0 < pg -> pg + 8 <= 2^47 -> (gm + 1024 <= pg \/ pg + 8 <= gm) -> (pg + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= pg) ->
  0 < pb -> pb + 8 <= 2^47 -> (gm + 1024 <= pb \/ pb + 8 <= gm) -> (pb + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= pb) ->
  mem_inv asegs m ->
  evt asegs (gray_exit ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 sb gm rmap n m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) s0 (Z_to_bv 64 sb) (Z_to_bv 64 gm) (Z_to_bv 64 rmap) a2 a3
             (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 rmap) (Z_to_bv 64 (4 * n)) (Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9bf6c) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  intros until ws. intros HN GC UAR UARL ACCR BYR R0 R8 RHI RSH RSEG UAG UAGL ACCG BYG G0 G8 GHI GSH GSEG UAB UABL ACCB BYB B0 B8 BHI BSH BSEG
    UAW UAWL ACCW W0 W8 WHI WSH WSEG SWR SWG SWB SL PG PB SB0 SBHI SBW SBH PG0 PGHI PGW PGSH PB0 PBHI PBW PBSH MI.
  pose proof (gray_loop (Z.to_nat n) 0 ra sp gp tp s0 a2 a3 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sb pg pb rmap gmap bmap gm n rs gs bs ws
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) GC UAR UARL ACCR BYR R0 R8 RHI RSH RSEG UAG UAGL ACCG BYG G0 G8 GHI GSH GSEG UAB UABL ACCB BYB B0 B8 BHI BSH BSEG
                UAW UAWL ACCW W0 W8 WHI WSH WSEG SWR SWG SWB SL PG PB SB0 SBHI SBW SBH PG0 PGHI PGW PGSH PB0 PBHI PBW PBSH MI) as L.
  replace (rmap + 4 * 0) with rmap in L by lia. replace (4 * 0) with 0 in L by lia. exact L.
Qed.

(* [comment removed for export] *)
Ltac gray_consts_tac :=
  unfold gray_consts, fa0, fa1, fa2, fa3, fa4, fa5; repeat split;
  repeat (first [ rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity) ]);
  vm_compute; reflexivity.

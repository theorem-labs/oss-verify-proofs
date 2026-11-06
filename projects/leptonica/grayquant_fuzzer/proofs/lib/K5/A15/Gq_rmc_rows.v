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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


(* [comment removed for export] *)
Lemma L1020 : forall y, 0 <= y -> exists ix, 0 <= ix < 256 /\ Z.land y 1020 = 4 * ix.
Proof.
  intros y Hy. exists (Z.land (Z.shiftr y 2) 255). split.
  - change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - replace (4 * Z.land (Z.shiftr y 2) 255) with (Z.shiftl (Z.land (Z.shiftr y 2) 255) 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    destruct (Z_lt_ge_dec n 2) as [L|G].
    + rewrite Z.shiftl_spec_low by lia.
      assert (E : Z.testbit 1020 n = false) by (assert (n = 0 \/ n = 1) as [->| ->] by lia; reflexivity). rewrite E. apply andb_false_r.
    + rewrite Z.shiftl_spec by lia. rewrite Z.land_spec, Z.shiftr_spec by lia. replace (n - 2 + 2) with n by lia. f_equal.
      change 1020 with (Z.shiftl 255 2). rewrite Z.shiftl_spec by lia. reflexivity.
Qed.

Notation RM_W datad n := [(datad, datad + n)]%Z (only parsing).

(* [comment removed for export] *)
Definition rmc_words_exit (ra sp gp tp s0 s1 a0 a6 a7 s2 s3 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datas datad gm wpl w h spw wa : Z) (ws gws : list word) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a4' a5' s4' s5' s8' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' (Z_to_bv 64 (4 * (w / 4))) a4' a5' a6 a7 s2 s3 s4' s5' s6 s7 s8' s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9be14) fc None m' (seg_rom asegs)
    /\ munch (RM_W datad (4 * (wpl * h))) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpl * h))
    /\ u32arr asegs m' gm gws /\ acc asegs m' gm 1024
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpl * h /\ acc asegs m' datad (4 * (wpl * h))
    /\ rw_cells asegs m' spw [C8 (Z_to_bv 64 wa)] /\ rw_cells asegs m' wa [C4 (Z_to_bv 64 w)].

Lemma rmc_words : forall (k : nat) (c : Z)
    (ra sp gp tp t2 s0 s1 a0 a3 a4 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 : word) F fc (m : mem)
    (datas datad gm wpl w h i spw wa : Z) (ws wd gws : list word),
  Z.of_nat k = w / 4 - c -> 0 <= c -> (1 <= k)%nat -> 0 < w <= 20000 -> wpl = (w * 8 + 31) / 32 ->
  0 < h <= 20000 -> 0 <= i < h -> 4 * (wpl * h) <= 0x4000000 ->
  bv_unsigned s1 + 176 = spw ->
  0 < datas -> datas mod 8 = 0 -> datas + 4 * (wpl * h) <= 2^47 -> (datas + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  (datas + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datas) ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * (wpl * h) <= 2^47 -> (datad + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datad) ->
  0 < gm -> gm mod 8 = 0 -> gm + 1024 <= 2^47 -> (gm + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gm) -> (gm + 1024 <= 0x10000 \/ SEGTOP_A <= gm) ->
  (datas + 4 * (wpl * h) <= datad \/ datad + 4 * (wpl * h) <= datas) ->
  (gm + 1024 <= datad \/ datad + 4 * (wpl * h) <= gm) ->
  0 < wa -> wa + 4 <= 2^47 -> (wa + 4 <= datad \/ datad + 4 * (wpl * h) <= wa) ->
  0 < spw -> spw + 8 <= 2^47 -> (spw + 8 <= datad \/ datad + 4 * (wpl * h) <= spw) ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpl * h -> acc asegs m datas (4 * (wpl * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpl * h -> acc asegs m datad (4 * (wpl * h)) ->
  u32arr asegs m gm gws -> Z.of_nat (length gws) = 256 -> acc asegs m gm 1024 ->
  rw_cells asegs m spw [C8 (Z_to_bv 64 wa)] -> rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> mem_inv asegs m ->
  evt asegs (rmc_words_exit ra sp gp tp s0 s1 a0 a6 a7 (Z_to_bv 64 SHB) s3 (Z_to_bv 64 (datad + 4 * (i * wpl))) (Z_to_bv 64 gm) s9 s10 s11
                            (Z_to_bv 64 (datas + 4 * (i * wpl))) t4 (Z_to_bv 64 (datas + 4 * (i * wpl))) (Z_to_bv 64 wa) F fc m datas datad gm wpl w h spw wa ws gws)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (datad + 4 * (i * wpl + c))) (Z_to_bv 64 (4 * c)) t2 s0 s1 a0
             (Z_to_bv 64 (datas + 4 * (i * wpl + c))) (Z_to_bv 64 (datad + 4 * (i * wpl + c))) a3 a4 (Z_to_bv 64 (datas + 4 * (i * wpl + c))) a6 a7
             (Z_to_bv 64 SHB) s3 s4 s5 (Z_to_bv 64 (datad + 4 * (i * wpl))) (Z_to_bv 64 gm) s8 s9 s10 s11
             (Z_to_bv 64 (datas + 4 * (i * wpl))) t4 (Z_to_bv 64 (datas + 4 * (i * wpl))) (Z_to_bv 64 wa))
        F (Z_to_bv 64 0x9b6e8) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c ra sp gp tp t2 s0 s1 a0 a3 a4 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 F fc m datas datad gm wpl w h i spw wa ws wd gws
    HK HC HK1 HW EWPL HH HI RSB ESPW S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG W0 WHI WSEP P0 PHI PSEP
    UAS UASL ACCS UA UAL ACCD UAGM UAGL ACCG PC WC MI.
  { lia. }
  assert (WPL4 : w <= 4 * wpl /\ 4 * wpl <= w + 3 /\ 0 < wpl <= 5000) by (rewrite EWPL; clear - HW; Z.div_mod_to_equations; lia).
  assert (NS : i * wpl + wpl <= wpl * h) by (clear - HI WPL4; nia).
  assert (NS0 : 0 <= i * wpl) by (clear - HI WPL4; nia).
  assert (CW : 0 <= c < wpl /\ 4 * c + 3 < w) by (clear - HK HC HK1 WPL4 HW; Z.div_mod_to_equations; lia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (RM_W datad (4 * (wpl * h))) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  lwalk [0x9b6f8; 0x9be14].
  destruct (u32arr_nth ws (i * wpl + c) ltac:(lia)) as (sv & NTHS).
  pose proof (u32arr_read asegs m datas ws (i * wpl + c) sv _ UAS NTHS ltac:(lia) eq_refl) as R.
  lstep. clear R.
  step. step. step.
  assert (XR : 0 <= bv_unsigned (zx32 sv) < 2^32).
  { clear. unfold zx32. pose proof (Z.mod_pos_bound (bv_unsigned sv) (2^32) ltac:(lia)) as Q. rewrite unsigned_lit by lia. exact Q. }
  set (x := bv_unsigned (zx32 sv)) in *.
  assert (IX1 : bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 x ≫ 24))) ≪ 2 = 4 * (x / 2^24) /\ 0 <= x / 2^24 < 256).
  { clear - XR. assert (Q : 0 <= x / 2^24 < 256) by (Z.div_mod_to_equations; lia). split; [| exact Q].
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). rewrite (Z.mod_small x) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
    rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. lia. }
  destruct IX1 as (IX1 & IX1R). rewrite !IX1. clear IX1.
  set (i1 := x / 2^24) in *.
  lwalk [0x9b730; 0x9be14].
  destruct (u32arr_nth gws i1 ltac:(lia)) as (g1 & NTH1).
  pose proof (u32arr_read asegs m gm gws i1 g1 _ UAGM NTH1 ltac:(lia) eq_refl) as R.
  fold x.
  destruct (L1020 (x / 16384) ltac:(clear - XR; Z.div_mod_to_equations; lia)) as (i2 & I2R & I2E). rewrite !I2E. clear I2E.
  lwalk [0x9b730; 0x9be14].
  lstep. clear R.
  lwalk [0x9b750; 0x9be14].
  fold x.
  destruct (L1020 (x / 64) ltac:(clear - XR; Z.div_mod_to_equations; lia)) as (i3 & I3R & I3E). rewrite !I3E. clear I3E.
  lwalk [0x9b750; 0x9be14].
  destruct (u32arr_nth gws i2 ltac:(lia)) as (g2 & NTH2).
  pose proof (u32arr_read asegs m gm gws i2 g2 _ UAGM NTH2 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9b770; 0x9be14].
  fold x.
  assert (I4R : 0 <= Z.land x 255 < 256) by (clear - XR; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  replace (Z.land x 255 * 4) with (4 * Z.land x 255) by (clear; lia).
  set (i4 := Z.land x 255) in *.
  lwalk [0x9b770; 0x9be14].
  destruct (u32arr_nth gws i3 ltac:(lia)) as (g3 & NTH3).
  pose proof (u32arr_read asegs m gm gws i3 g3 _ UAGM NTH3 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9b784; 0x9be14].
  destruct (u32arr_nth gws i4 ltac:(lia)) as (g4 & NTH4).
  pose proof (u32arr_read asegs m gm gws i4 g4 _ UAGM NTH4 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9b7a8; 0x9be14].
  unpark DSH. unpark SEP. unpark SEPG. unpark WSEP. unpark PSEP.
  arr_sw datad (i * wpl + c) (datad + 4 * (i * wpl + c)).
  park DSH. park SEP. park SEPG. park WSEP. park PSEP.
  lwalk [0x9b7b0; 0x9be14].
  rewrite <- ESPW in PC.
  lwalk [0x9b7b0; 0x9be14].
  lwalk [0x9b6e8; 0x9b7d0; 0x9be14].
  rewrite ESPW in PC.
  rewrite !(bv_swrap_small 32 (4 * c + 7)) by (change (bv_half_modulus 32) with (2^31); clear - CW HW; lia).
  rewrite !(bv_swrap_small 32 (4 * c + 4)) by (change (bv_half_modulus 32) with (2^31); clear - CW HW; lia).
  rewrite !(sx32_small w) by (clear - HW; lia).
  destruct k as [|k].
  - assert (EC : c + 1 = w / 4) by lia.
    assert (GE : w <= 4 * c + 7) by (clear - EC HW; Z.div_mod_to_equations; lia).
    brF. lwalk [0x9be14].
    replace (4 * c + 4) with (4 * (w / 4)) by (clear - EC; lia).
    apply evt_done. unfold rmc_words_exit. do 10 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    repeat (split; [assumption|]). assumption.
  - assert (LT : 4 * c + 7 < w) by (clear - HK HC HW; Z.div_mod_to_equations; lia).
    brT.
    replace (datas + 4 * (i * wpl + c) + 4) with (datas + 4 * (i * wpl + (c + 1))) by (clear; lia).
    replace (datad + 4 * (i * wpl + c) + 4) with (datad + 4 * (i * wpl + (c + 1))) by (clear; lia).
    replace (4 * c + 4) with (4 * (c + 1)) by (clear; lia).
    eapply evt_cut.
    + eapply (IH (c + 1)) with (ws := ws) (wd := aws) (gws := gws) (h := h) (w := w) (spw := spw); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold rmc_words_exit in PO |- *.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a4' & a5' & s4' & s5' & s8' & m' & wd' & E & MU' & WM' & R).
      exists t0', t1', t2', a1', a2', a4', a5', s4', s5', s8', m', wd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition rmc_tail_exit (ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datas datad gm wpl w h wa gva : Z) (ws gws : list word) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' a4' a5' gv' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9b1f0) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + 4 * (wpl * h)); (gva, gva + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpl * h))
    /\ u32arr asegs m' gm gws /\ acc asegs m' gm 1024
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpl * h /\ acc asegs m' datad (4 * (wpl * h))
    /\ rw_cells asegs m' wa [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' gva [C4 gv'].

Lemma rmc_tail : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s9 s10 s11 t4 t5 : word) F fc (m : mem)
    (datas datad gm wpl w h i wa gva : Z) (ws wd gws : list word) (gv : word),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> 0 < w <= 20000 -> wpl = (w * 8 + 31) / 32 ->
  0 < h <= 20000 -> 0 <= i < h -> 4 * (wpl * h) <= 0x4000000 ->
  0 < datas -> datas mod 8 = 0 -> datas + 4 * (wpl * h) <= 2^47 -> (datas + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  (datas + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datas) ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * (wpl * h) <= 2^47 -> (datad + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datad) ->
  0 < gm -> gm mod 8 = 0 -> gm + 1024 <= 2^47 -> (gm + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gm) -> (gm + 1024 <= 0x10000 \/ SEGTOP_A <= gm) ->
  (datas + 4 * (wpl * h) <= datad \/ datad + 4 * (wpl * h) <= datas) ->
  (gm + 1024 <= datad \/ datad + 4 * (wpl * h) <= gm) ->
  0 < wa -> wa + 4 <= 2^47 -> (wa + 4 <= datad \/ datad + 4 * (wpl * h) <= wa) ->
  0 < gva -> gva + 4 <= 2^47 -> (gva + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= gva) -> (gva + 4 <= 0x10000 \/ SEGTOP_A <= gva) ->
  (gva + 4 <= datad \/ datad + 4 * (wpl * h) <= gva) -> (gva + 4 <= datas \/ datas + 4 * (wpl * h) <= gva) ->
  (gva + 4 <= gm \/ gm + 1024 <= gva) -> (gva + 4 <= wa \/ wa + 4 <= gva) ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpl * h -> acc asegs m datas (4 * (wpl * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpl * h -> acc asegs m datad (4 * (wpl * h)) ->
  u32arr asegs m gm gws -> Z.of_nat (length gws) = 256 -> acc asegs m gm 1024 ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs m gva [C4 gv] -> mem_inv asegs m ->
  evt asegs (rmc_tail_exit ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 (Z_to_bv 64 SHB) s3 s4 s5 (Z_to_bv 64 (datad + 4 * (i * wpl))) (Z_to_bv 64 gm) (Z_to_bv 64 gva) s9 s10 s11
                           (Z_to_bv 64 (datas + 4 * (i * wpl))) t4 t5 (Z_to_bv 64 wa) F fc m datas datad gm wpl w h wa gva ws gws)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 j) a4 a5 a6 a7
             (Z_to_bv 64 SHB) s3 s4 s5 (Z_to_bv 64 (datad + 4 * (i * wpl))) (Z_to_bv 64 gm) (Z_to_bv 64 gva) s9 s10 s11
             (Z_to_bv 64 (datas + 4 * (i * wpl))) t4 t5 (Z_to_bv 64 wa))
        F (Z_to_bv 64 0x9be24) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s9 s10 s11 t4 t5 F fc m datas datad gm wpl w h i wa gva ws wd gws gv
    HK HJ HK1 HW EWPL HH HI RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG W0 WHI WSEP V0 VHI VSH VSEG VSEP VSEPS VSEPG VSEPW
    UAS UASL ACCS UA UAL ACCD UAGM UAGL ACCG WC VC MI.
  { lia. }
  assert (WPL4 : w <= 4 * wpl /\ 4 * wpl <= w + 3 /\ 0 < wpl <= 5000) by (rewrite EWPL; clear - HW; Z.div_mod_to_equations; lia).
  assert (NS : i * wpl + wpl <= wpl * h) by (clear - HI WPL4; nia).
  assert (NS0 : 0 <= i * wpl) by (clear - HI WPL4; nia).
  assert (JW : 0 <= j < w) by (clear - HK HJ HK1; lia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(datad, datad + 4 * (wpl * h)); (gva, gva + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (lxor3_eq (datas + 4 * (i * wpl) + j)) as LXS.
  pose proof (lxor3_eq (datad + 4 * (i * wpl) + j)) as LXD.
  pose proof (proj1 UAS) as HBS.
  assert (HBL : Z.of_nat (length (u32s ws)) = 4 * (wpl * h)) by (rewrite u32s_length; clear - UASL; lia).
  park_disj.
  lwalk [0x9be3c; 0x9b1f0].
  destruct (bytes_at_read1 m datas (u32s ws) (Z.lxor (datas + 4 * (i * wpl) + j) 3 - datas) HBS ltac:(lia)) as (sb & R).
  replace (datas + (Z.lxor (datas + 4 * (i * wpl) + j) 3 - datas)) with (Z.lxor (datas + 4 * (i * wpl) + j) 3) in R by lia.
  lstep. clear R.
  lwalk [0x9be58; 0x9b1f0].
  assert (SBR : 0 <= bv_unsigned sb < 256) by (pose proof (bv_unsigned_in_range 8 sb) as Q; unfold bv_modulus in Q; change (2 ^ Z.of_N 8) with 256 in Q; exact Q).
  replace (bv_unsigned sb * 4) with (4 * bv_unsigned sb) by (clear; lia).
  set (ix := bv_unsigned sb) in *.
  rewrite !(Z.mod_small (gm + 4 * ix) 18446744073709551616) by (clear - SBR G0 GHI; lia).
  lwalk [0x9be58; 0x9b1f0].
  destruct (u32arr_nth gws ix ltac:(lia)) as (g1 & NTH1).
  pose proof (u32arr_read asegs m gm gws ix g1 _ UAGM NTH1 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9be64; 0x9b1f0].
  unpark VSH. unpark VSEP. unpark VSEPS. unpark VSEPG. unpark VSEPW.
  lstep.
  park VSH. park VSEP. park VSEPS. park VSEPG. park VSEPW.
  lwalk [0x9be78; 0x9b1f0].
  lazymatch goal with U : u32arr asegs ?mm datad ?wsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_u8arr mm datad wsx U) as UA8;
    assert (UAL8 : Z.of_nat (length (u32s wsx)) = 4 * (wpl * h)) by (rewrite u32s_length; clear - UAL; lia);
    clear U UAL end.
  unfold sx32.
  unpark DSH. unpark SEP. unpark SEPG. unpark WSEP. unpark VSEP.
  replace (Z.lxor (datad + 4 * (i * wpl) + j) 3) with (datad + (4 * (i * wpl) + j + 3 - 2 * ((datad + 4 * (i * wpl) + j) mod 4))) by (clear - LXD; lia).
  arr_sb datad (4 * (i * wpl) + j + 3 - 2 * ((datad + 4 * (i * wpl) + j) mod 4)) (datad + (4 * (i * wpl) + j + 3 - 2 * ((datad + 4 * (i * wpl) + j) mod 4))).
  park DSH. park SEP. park SEPG. park WSEP. park VSEP.
  lazymatch goal with U : u8arr asegs ?mm datad ?bsx |- _ =>
    destruct (u8arr_u32arr mm datad bsx (wpl * h) U UAL8) as (wd1 & UA & UAL); clear U UAL8 end.
  lwalk [0x9be24; 0x9be84; 0x9b1f0].
  lstep.
  rewrite !(sx32_small w) by (clear - HW; lia).
  destruct k as [|k].
  - assert (EJ : j + 1 = w) by lia.
    brF. lwalk [0x9b1f0].
    apply evt_done. unfold rmc_tail_exit.
    do 6 eexists. lazymatch goal with UAx : u32arr asegs ?mm datad ?wdx |- _ => exists mm, wdx end.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. repeat (split; [assumption|]). eassumption.
  - assert (LT : j + 1 < w) by lia.
    brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (ws := ws) (gws := gws) (h := h) (w := w); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold rmc_tail_exit in PO |- *.
      destruct PO as (a1' & a2' & a3' & a4' & a5' & gv' & m' & wd' & E & MU' & WM' & R).
      exists a1', a2', a3', a4', a5', gv', m', wd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition rmc_rows_exit (sp gp tp s0 s1 s2 s3 s7 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datas datad gm wpl w h fr sb : Z) (ws gws : list word) (x160 : word) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' t3' t4' t5' gv' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4' s5' s6' s7 s8' s9 s10 s11 t3' t4' t5' t6)
             F (Z_to_bv 64 0x9c04c) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + 4 * (wpl * h)); (fr + 48, fr + 48 + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpl * h))
    /\ u32arr asegs m' gm gws /\ acc asegs m' gm 1024
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpl * h /\ acc asegs m' datad (4 * (wpl * h))
    /\ rw_cells asegs m' (fr + 80) [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' (fr + 48) [C4 gv']
    /\ rw_cells asegs m' (fr + 96) [C4 (Z_to_bv 64 h)] /\ rw_cells asegs m' (fr + 112) [C4 (Z_to_bv 64 8)]
    /\ rw_cells asegs m' (sb + 56) [C8 (Z_to_bv 64 wpl); C8 (Z_to_bv 64 datas)]
    /\ rw_cells asegs m' (sb + 96) [C8 (Z_to_bv 64 (fr + 96))]
    /\ rw_cells asegs m' (sb + 128) [C8 (Z_to_bv 64 (4 * wpl)); C8 (Z_to_bv 64 (4 * wpl)); C8 (Z_to_bv 64 0x7ffffff); C8 (Z_to_bv 64 0xfffffff); C8 x160;
                                    C8 (Z_to_bv 64 (fr + 112)); C8 (Z_to_bv 64 (fr + 80)); C8 (Z_to_bv 64 (fr + 48))].

(* [comment removed for export] *)
Ltac row_xport H MU WM side :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
  lazymatch type of H with rw_cells _ ma ?A ?cs =>
    let D := fresh "DJ" in
    assert (D : disjoint_from W A (Z.of_nat (cells_size cs))) by (cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; side);
    apply (fun h => rw_cells_transport asegs W ma mb A cs h MU WM D) in H; clear D
  end end.

Lemma rmc_rows : forall (k : nat) (i : Z)
    (sp gp tp t0 t2 s0 a0 a1 a2 a3 a4 a5 s3 s4 s5 s8 s9 s10 s11 : word) F fc (m : mem)
    (datas datad gm wpl w h fr sb : Z) (ws wd gws : list word) (gv x160 : word),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> 0 < w <= 20000 -> wpl = (w * 8 + 31) / 32 ->
  0 < h <= 20000 -> 4 * (wpl * h) <= 0x4000000 ->
  0 < datas -> datas mod 8 = 0 -> datas + 4 * (wpl * h) <= 2^47 -> (datas + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  (datas + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datas) ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * (wpl * h) <= 2^47 -> (datad + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datad) ->
  0 < gm -> gm mod 8 = 0 -> gm + 1024 <= 2^47 -> (gm + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gm) -> (gm + 1024 <= 0x10000 \/ SEGTOP_A <= gm) ->
  (datas + 4 * (wpl * h) <= datad \/ datad + 4 * (wpl * h) <= datas) ->
  (gm + 1024 <= datad \/ datad + 4 * (wpl * h) <= gm) ->
  0 < fr -> fr mod 32 = 0 -> fr + 320 <= 2^47 -> (fr + 320 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) -> (fr + 320 <= 0x10000 \/ SEGTOP_A <= fr) ->
  (fr + 320 <= datad \/ datad + 4 * (wpl * h) <= fr) -> (fr + 320 <= datas \/ datas + 4 * (wpl * h) <= fr) -> (fr + 320 <= gm \/ gm + 1024 <= fr) ->
  0 < sb -> sb mod 8 = 0 -> sb + 192 <= 2^47 ->
  (sb + 192 <= datad \/ datad + 4 * (wpl * h) <= sb) -> (sb + 192 <= fr \/ fr + 320 <= sb) ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpl * h -> acc asegs m datas (4 * (wpl * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpl * h -> acc asegs m datad (4 * (wpl * h)) ->
  u32arr asegs m gm gws -> Z.of_nat (length gws) = 256 -> acc asegs m gm 1024 ->
  rw_cells asegs m (fr + 80) [C4 (Z_to_bv 64 w)] -> rw_cells asegs m (fr + 48) [C4 gv] ->
  rw_cells asegs m (fr + 96) [C4 (Z_to_bv 64 h)] -> rw_cells asegs m (fr + 112) [C4 (Z_to_bv 64 8)] ->
  rw_cells asegs m (sb + 56) [C8 (Z_to_bv 64 wpl); C8 (Z_to_bv 64 datas)] ->
  rw_cells asegs m (sb + 96) [C8 (Z_to_bv 64 (fr + 96))] ->
  rw_cells asegs m (sb + 128) [C8 (Z_to_bv 64 (4 * wpl)); C8 (Z_to_bv 64 (4 * wpl)); C8 (Z_to_bv 64 0x7ffffff); C8 (Z_to_bv 64 0xfffffff); C8 x160;
                               C8 (Z_to_bv 64 (fr + 112)); C8 (Z_to_bv 64 (fr + 80)); C8 (Z_to_bv 64 (fr + 48))] ->
  mem_inv asegs m ->
  evt asegs (rmc_rows_exit sp gp tp s0 (Z_to_bv 64 sb) (Z_to_bv 64 SHB) s3 (Z_to_bv 64 gm) s9 s10 s11 (Z_to_bv 64 (fr + 80)) F fc m datas datad gm wpl w h fr sb ws gws x160)
    (MS (mkR (Z_to_bv 64 (datad + 4 * (i * wpl))) sp gp tp t0 (Z_to_bv 64 (fr + 112)) t2 s0 (Z_to_bv 64 sb) a0 a1 a2 a3 a4 a5
             (Z_to_bv 64 i) (Z_to_bv 64 (datad + 4 + 4 * (i * wpl)))
             (Z_to_bv 64 SHB) s3 s4 s5 (Z_to_bv 64 (datad + 4 * (i * wpl))) (Z_to_bv 64 gm) s8 s9 s10 s11
             (Z_to_bv 64 (datas + 4 * (i * wpl))) (Z_to_bv 64 (4 * (i * wpl))) (Z_to_bv 64 (datas + 4 * (i * wpl))) (Z_to_bv 64 (fr + 80)))
        F (Z_to_bv 64 0x9b220) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i sp gp tp t0 t2 s0 a0 a1 a2 a3 a4 a5 s3 s4 s5 s8 s9 s10 s11 F fc m datas datad gm wpl w h fr sb ws wd gws gv x160
    HK HI HK1 HW EWPL HH RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG
    F0 F32 FHI FSH FSEG FSD FSS FSG B0 B8 BHI BSD BSF
    UAS UASL ACCS UA UAL ACCD UAGM UAGL ACCG WC VC HC DC Q56 Q96 Q128 MI.
  { lia. }
  assert (WPL4 : w <= 4 * wpl /\ 4 * wpl <= w + 3 /\ 0 < wpl <= 5000) by (rewrite EWPL; clear - HW; Z.div_mod_to_equations; lia).
  assert (HIH : 0 <= i < h) by (clear - HK HI HK1; lia).
  assert (NS : i * wpl + wpl <= wpl * h) by (clear - HIH WPL4; nia).
  assert (NS0 : 0 <= i * wpl) by (clear - HIH WPL4; nia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(datad, datad + 4 * (wpl * h)); (fr + 48, fr + 48 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  (* [comment removed for export] *)
  lwalk [0x9b6d0; 0x9c04c].
  (* [comment removed for export] *)
  lstep.
  rewrite !(sx32_small w) by (clear - HW; lia).
  assert (ESPW : bv_unsigned (Z_to_bv 64 sb) + 176 = sb + 176) by (rewrite unsigned_lit by (clear - B0 BHI; lia); reflexivity).
  (* [comment removed for export] *)
  eapply (evt_cut asegs (rmc_words_exit (Z_to_bv 64 (datad + 4 * (i * wpl))) sp gp tp s0 (Z_to_bv 64 sb) (Z_to_bv 64 4) (Z_to_bv 64 i) (Z_to_bv 64 (datad + 4 + 4 * (i * wpl)))
                              (Z_to_bv 64 2147450880) s3 (Z_to_bv 64 (datad + 4 * (i * wpl))) (Z_to_bv 64 gm) s9 s10 s11
                              (Z_to_bv 64 (datas + 4 * (i * wpl))) (Z_to_bv 64 (4 * (i * wpl))) (Z_to_bv 64 (datas + 4 * (i * wpl))) (Z_to_bv 64 (fr + 80))
                              F fc _ datas datad gm wpl w h (sb + 176) (fr + 80) ws gws)).
  { destruct (Z_lt_ge_dec w 4) as [WL|WG].
    - (* [comment removed for export] *)
      brT. lwalk [0x9be14; 0x9c04c].
      apply evt_done. unfold rmc_words_exit.
      replace (4 * (w / 4)) with 0 by (clear - WL HW; Z.div_mod_to_equations; lia).
      do 10 eexists. lazymatch goal with UAx : u32arr asegs ?mm datad ?wdx |- _ => exists mm, wdx end.
      pose proof Q128 as T. split_at T 6%nat PWC. split_at PWC 1%nat T2. clear T T2.
      split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      repeat (split; [assumption|]). assumption.
    - brF. lwalk [0x9b6e8; 0x9c04c].
      pose proof Q128 as T. split_at T 6%nat PWC. split_at PWC 1%nat T2. clear T T2.
      assert (Q1 : Z.of_nat (Z.to_nat (w / 4)) = w / 4 - 0) by (clear - WG HW; Z.div_mod_to_equations; lia).
      assert (Q3 : (1 <= Z.to_nat (w / 4))%nat) by (clear - WG HW; Z.div_mod_to_equations; lia).
      lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?FF _ ?ffc None ?mm _) =>
        epose proof (rmc_words (Z.to_nat (w / 4)) 0 (Z_to_bv 64 (datad + 4 * (i * wpl))) sp gp tp _ s0 (Z_to_bv 64 sb) (Z_to_bv 64 4) _ _ (Z_to_bv 64 i)
                       (Z_to_bv 64 (datad + 4 + 4 * (i * wpl))) s3 _ _ _ s9 s10 s11 (Z_to_bv 64 0) (Z_to_bv 64 (4 * (i * wpl))) (Z_to_bv 64 0) FF ffc mm
                       datas datad gm wpl w h i (sb + 176) (fr + 80) ws _ gws
                       Q1 ltac:(clear; lia) Q3 HW EWPL HH HIH RSB ESPW S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG
                       ltac:(clear - F0; lia) ltac:(clear - FHI; lia) ltac:(clear - FSD; unpark FSD; lia) ltac:(clear - B0; lia) ltac:(clear - BHI; lia) ltac:(clear - BSD; unpark BSD; lia)
                       UAS UASL ACCS ltac:(eassumption) ltac:(eassumption) ACCD UAGM UAGL ACCG PWC WC MIx) as ZR end.
      unfold SHB in ZR.
      replace (i * wpl + 0) with (i * wpl) in ZR by (clear; lia).
      replace (4 * 0) with 0 in ZR by (clear; lia).
      exact ZR. }
  clear UA UAL ACCD MI.
  intros ms1 PO1. unfold rmc_words_exit in PO1.
  destruct PO1 as (t0a & t1a & t2a & a1a & a2a & a4a & a5a & s4a & s5a & s8a & ma & wda & -> & MUa & WMa & MIa & UASa & ACCSa & UAGMa & ACCGa & UAa & UALa & ACCDa & PWCa & WCa).
  row_xport Q56 MUa WMa ltac:(repeat split; try exact I; clear - BSD BSF; unpark BSD; unpark BSF; lia).
  row_xport Q96 MUa WMa ltac:(repeat split; try exact I; clear - BSD BSF; unpark BSD; unpark BSF; lia).
  row_xport Q128 MUa WMa ltac:(repeat split; try exact I; clear - BSD BSF; unpark BSD; unpark BSF; lia).
  row_xport HC MUa WMa ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  row_xport DC MUa WMa ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  row_xport VC MUa WMa ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  (* [comment removed for export] *)
  lwalk [0x9be20; 0x9c04c]. lstep.
  rewrite !(sx32_small w) by (clear - HW; lia).
  (* [comment removed for export] *)
  eapply (evt_cut asegs (rmc_tail_exit (Z_to_bv 64 (datad + 4 * (i * wpl))) sp gp tp t0a (Z_to_bv 64 (fr + 112)) t2a s0 (Z_to_bv 64 sb) (Z_to_bv 64 4)
                              (Z_to_bv 64 i) (Z_to_bv 64 (datad + 4 + 4 * (i * wpl))) (Z_to_bv 64 2147450880) s3 s4a s5a
                              (Z_to_bv 64 (datad + 4 * (i * wpl))) (Z_to_bv 64 gm) (Z_to_bv 64 (fr + 48)) s9 s10 s11
                              (Z_to_bv 64 (datas + 4 * (i * wpl))) (Z_to_bv 64 (4 * (i * wpl))) (Z_to_bv 64 (datas + 4 * (i * wpl))) (Z_to_bv 64 (fr + 80))
                              F fc ma datas datad gm wpl w h (fr + 80) (fr + 48) ws gws)).
  { destruct (Z.eq_dec (w mod 4) 0) as [WZ|WNZ].
    - (* [comment removed for export] *)
      assert (GE : w <= 4 * (w / 4)) by (clear - WZ HW; Z.div_mod_to_equations; lia).
      brT.
      apply evt_done. unfold rmc_tail_exit.
      do 6 eexists. exists ma, wda.
      split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      repeat (split; [assumption|]). first [assumption | eassumption].
    - assert (LTW : 4 * (w / 4) < w) by (clear - WNZ HW; Z.div_mod_to_equations; lia).
      brF.
      assert (T1 : Z.of_nat (Z.to_nat (w - 4 * (w / 4))) = w - 4 * (w / 4)) by (clear - LTW; lia).
      assert (T3 : (1 <= Z.to_nat (w - 4 * (w / 4)))%nat) by (clear - LTW; lia).
      epose proof (rmc_tail (Z.to_nat (w - 4 * (w / 4))) (4 * (w / 4)) (Z_to_bv 64 (datad + 4 * (i * wpl))) sp gp tp t0a (Z_to_bv 64 (fr + 112)) t2a s0 (Z_to_bv 64 sb)
                     (Z_to_bv 64 4) _ _ _ _ (Z_to_bv 64 i) (Z_to_bv 64 (datad + 4 + 4 * (i * wpl))) s3 s4a s5a s9 s10 s11 (Z_to_bv 64 (4 * (i * wpl))) (Z_to_bv 64 (datas + 4 * (i * wpl)))
                     F fc ma datas datad gm wpl w h i (fr + 80) (fr + 48) ws wda gws _
                     T1 ltac:(clear - HW; Z.div_mod_to_equations; lia) T3 HW EWPL HH HIH RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG
                     ltac:(clear - F0; lia) ltac:(clear - FHI; lia) ltac:(clear - FSD; unpark FSD; lia)
                     ltac:(clear - F0; lia) ltac:(clear - FHI; lia) ltac:(clear - FSH; unpark FSH; lia) ltac:(clear - FSEG; unpark FSEG; unfold SEGTOP_A; lia)
                     ltac:(clear - FSD; unpark FSD; lia) ltac:(clear - FSS; unpark FSS; lia) ltac:(clear - FSG; unpark FSG; lia) ltac:(clear; lia)
                     UASa UASL ACCSa UAa UALa ACCDa UAGMa UAGL ACCGa WCa VC MIa) as ZT.
      unfold SHB in ZT. exact ZT. }
  clear UAa UALa ACCDa MIa VC UASa ACCSa UAGMa ACCGa WCa.
  intros ms2 PO2. unfold rmc_tail_exit in PO2.
  destruct PO2 as (a1b & a2b & a3b & a4b & a5b & gvb & mb & wdb & -> & MUb & WMb & MIb & UASb & ACCSb & UAGMb & ACCGb & UAb & UALb & ACCDb & WCb & VCb).
  row_xport Q56 MUb WMb ltac:(repeat split; try exact I; clear - BSD BSF; unpark BSD; unpark BSF; lia).
  row_xport Q96 MUb WMb ltac:(repeat split; try exact I; clear - BSD BSF; unpark BSD; unpark BSF; lia).
  row_xport Q128 MUb WMb ltac:(repeat split; try exact I; clear - BSD BSF; unpark BSD; unpark BSF; lia).
  row_xport HC MUb WMb ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  row_xport DC MUb WMb ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  row_xport PWCa MUb WMb ltac:(repeat split; try exact I; clear - BSD BSF; unpark BSD; unpark BSF; lia).
  pose proof (munch_trans _ _ _ _ (munch_weaken [(datad, datad + 4 * (wpl * h))] [(datad, datad + 4 * (wpl * h)); (fr + 48, fr + 48 + 4)] m ma ltac:(subfp_tac) MUa) MUb) as MUab.
  pose proof (wmono_trans asegs _ _ _ WMa WMb) as WMab.
  pose proof (munch_trans _ _ _ _ MU MUab) as MU2. pose proof (wmono_trans asegs _ _ _ WM WMab) as WM2.
  clear MUa MUb WMa WMb MUab WMab MU WM. rename MU2 into MU. rename WM2 into WM.
  (* [comment removed for export] *)
  lwalk [0x9b21c; 0x9c04c]. lstep.
  rewrite !(sx32_small h) by (clear - HH; lia).
  destruct k as [|k].
  - assert (EI : i + 1 = h) by lia.
    brT.
    apply evt_done. unfold rmc_rows_exit.
    do 20 eexists. exists mb, wdb.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    repeat (split; [first [assumption | eassumption]|]). first [assumption | eassumption].
  - assert (LT : i + 1 < h) by lia.
    brF.
    replace (datad + 4 * (i * wpl) + 4 * wpl) with (datad + 4 * ((i + 1) * wpl)) by (clear; ring).
    replace (datad + 4 + 4 * (i * wpl) + 4 * wpl) with (datad + 4 + 4 * ((i + 1) * wpl)) by (clear; ring).
    replace (datas + 4 * (i * wpl) + 4 * wpl) with (datas + 4 * ((i + 1) * wpl)) by (clear; ring).
    replace (4 * (i * wpl) + 4 * wpl) with (4 * ((i + 1) * wpl)) by (clear; ring).
    eapply evt_cut.
    + eapply (IH (i + 1)) with (ws := ws) (gws := gws) (wd := wdb) (gv := gvb) (w := w); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold rmc_rows_exit in PO |- *.
      destruct PO as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & s5' & s6' & s8' & t3' & t4' & t5' & gv' & m' & wd' & E & MU' & WM' & R).
      exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', s4', s5', s6', s8', t3', t4', t5', gv', m', wd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

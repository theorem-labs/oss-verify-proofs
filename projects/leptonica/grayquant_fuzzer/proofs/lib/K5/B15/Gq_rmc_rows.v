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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Gq_rgb LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ONE := (Z_to_bv 64 1) (only parsing).
Notation NGM gm := (Z_to_bv 64 (Z.lxor gm 18446744073709551615)) (only parsing).
Notation RM_W datad n := [(datad, datad + n)]%Z (only parsing).

(* [comment removed for export] *)
Definition rmc_words_exit (sp gp tp s0 s9 t5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (sb datas datad gm wpl w h i wa gva da : Z) (ws gws : list word) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a5' a7' s3' s5' s7' s8' t3' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR (Z_to_bv 64 (datad + 4 * (i * wpl))) sp gp tp ONE ONE (NGM gm) s0 (Z_to_bv 64 sb) (Z_to_bv 64 gm) a1' a2' (Z_to_bv 64 (4 * (w / 4))) ONE a5'
                  (Z_to_bv 64 (4 * (w / 4))) a7' (Z_to_bv 64 SHB) s3' (Z_to_bv 64 (datas + 4 * (i * wpl))) s5' (Z_to_bv 64 2147483648) s7' s8' s9 ONE
                  (Z_to_bv 64 (4 * (i * wpl))) t3' (Z_to_bv 64 (datas + 4 * (i * wpl))) t5 (Z_to_bv 64 (datad + 4 * (i * wpl))))
             F (Z_to_bv 64 0x9d2a0) fc None m' (seg_rom asegs)
    /\ munch (RM_W datad (4 * (wpl * h))) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpl * h))
    /\ u32arr asegs m' gm gws /\ acc asegs m' gm 1024
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpl * h /\ acc asegs m' datad (4 * (wpl * h))
    /\ rw_cells asegs m' (sb + 152) [C8 (Z_to_bv 64 gva); C8 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' (sb + 168) [C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 da); C8 (Z_to_bv 64 wa)]
    /\ rw_cells asegs m' wa [C4 (Z_to_bv 64 w)].

Lemma rmc_words : forall (k : nat) (c : Z)
    (sp gp tp s0 a1 a2 a5 a7 s3 s5 s7 s8 s9 t3 t5 : word) F fc (m : mem)
    (sb datas datad gm wpl w h i wa gva da : Z) (ws wd gws : list word),
  Z.of_nat k = w / 4 - c -> 0 <= c -> (1 <= k)%nat -> 0 < w <= 20000 -> wpl = (w * 8 + 31) / 32 ->
  0 < h <= 20000 -> 0 <= i < h -> 4 * (wpl * h) <= 0x4000000 ->
  0 < datas -> datas mod 8 = 0 -> datas + 4 * (wpl * h) <= 2^47 -> (datas + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  (datas + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datas) ->
  0 < datad -> datad mod 8 = 0 -> datad + 4 * (wpl * h) <= 2^47 -> (datad + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + 4 * (wpl * h) <= 0x10000 \/ SEGTOP_A <= datad) ->
  0 < gm -> gm mod 8 = 0 -> gm + 1024 <= 2^47 -> (gm + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gm) -> (gm + 1024 <= 0x10000 \/ SEGTOP_A <= gm) ->
  (datas + 4 * (wpl * h) <= datad \/ datad + 4 * (wpl * h) <= datas) ->
  (gm + 1024 <= datad \/ datad + 4 * (wpl * h) <= gm) ->
  0 < wa -> wa + 4 <= 2^47 -> (wa + 4 <= datad \/ datad + 4 * (wpl * h) <= wa) ->
  0x10007fff8000 <= sb -> sb + 192 <= 2^47 -> datad + 4 * (wpl * h) <= sb ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpl * h -> acc asegs m datas (4 * (wpl * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpl * h -> acc asegs m datad (4 * (wpl * h)) ->
  u32arr asegs m gm gws -> Z.of_nat (length gws) = 256 -> acc asegs m gm 1024 ->
  rw_cells asegs m (sb + 152) [C8 (Z_to_bv 64 gva); C8 (Z_to_bv 64 1)] ->
  rw_cells asegs m (sb + 168) [C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 da); C8 (Z_to_bv 64 wa)] ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> mem_inv asegs m ->
  evt asegs (rmc_words_exit sp gp tp s0 s9 t5 F fc m sb datas datad gm wpl w h i wa gva da ws gws)
    (MS (mkR (Z_to_bv 64 (datad + 4 * (i * wpl))) sp gp tp ONE ONE (NGM gm) s0 (Z_to_bv 64 sb) (Z_to_bv 64 gm) a1 a2 (Z_to_bv 64 (4 * c)) ONE a5
             (Z_to_bv 64 (4 * c)) a7 (Z_to_bv 64 SHB) s3 (Z_to_bv 64 (datas + 4 * (i * wpl))) s5 (Z_to_bv 64 2147483648) s7 s8 s9 ONE
             (Z_to_bv 64 (4 * (i * wpl))) t3 (Z_to_bv 64 (datas + 4 * (i * wpl))) t5 (Z_to_bv 64 (datad + 4 * (i * wpl))))
        F (Z_to_bv 64 0x9c864) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c sp gp tp s0 a1 a2 a5 a7 s3 s5 s7 s8 s9 t3 t5 F fc m sb datas datad gm wpl w h i wa gva da ws wd gws
    HK HC HK1 HW EWPL HH HI RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG W0 WHI WSEP SBLO SBHI SBD
    UAS UASL ACCS UA UAL ACCD UAGM UAGL ACCG FL PW WC MI.
  { exfalso; clear - HK1; lia. }
  assert (WPL4 : w <= 4 * wpl /\ 4 * wpl <= w + 3 /\ 0 < wpl <= 5000) by (rewrite EWPL; clear - HW; Z.div_mod_to_equations; lia).
  assert (NS : i * wpl + wpl <= wpl * h) by (clear - HI WPL4; nia).
  assert (NS0 : 0 <= i * wpl) by (clear - HI WPL4; nia).
  assert (CW : 0 <= c < wpl /\ 4 * c + 3 < w) by (clear - HK HC HK1 WPL4 HW; Z.div_mod_to_equations; lia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (RM_W datad (4 * (wpl * h))) m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  (* [comment removed for export] *)
  lwalk [0x9c88c; 0x9d5cc; 0x9c9ac].
  replace (datas + 4 * (i * wpl) + 4 * c) with (datas + 4 * (i * wpl + c)) by (clear; lia).
  destruct (u32arr_nth ws (i * wpl + c) ltac:(lia)) as (sv & NTHS).
  pose proof (u32arr_read asegs m datas ws (i * wpl + c) sv _ UAS NTHS ltac:(lia) eq_refl) as R.
  lstep. clear R.
  assert (XR : 0 <= bv_unsigned (zx32 sv) < 2^32).
  { clear. unfold zx32. pose proof (Z.mod_pos_bound (bv_unsigned sv) (2^32) ltac:(lia)) as Q. rewrite unsigned_lit by lia. exact Q. }
  set (x := bv_unsigned (zx32 sv)) in *.
  (* [comment removed for export] *)
  lwalk [0x9c89c; 0x9d5cc].
  fold x.
  assert (I1R : 0 <= x / 16777216 < 256) by (clear - XR; Z.div_mod_to_equations; lia).
  replace (bv_swrap 32 (bv_wrap 32 x / 16777216) mod 18446744073709551616 * 4) with (4 * (x / 16777216)).
  2:{ clear - XR I1R. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small x) by lia.
      rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648; lia). rewrite Z.mod_small by lia. lia. }
  set (i1 := x / 16777216) in *.
  (* [comment removed for export] *)
  lwalk [0x9c8c4; 0x9d5cc].
  fold x. change ((x * 1099511627776) mod 18446744073709551616 / 72057594037927936) with (rgb_g x).
  pose proof (rgb_g_range x) as I2R. set (i2 := rgb_g x) in *.
  replace (i2 * 4) with (4 * i2) by (clear; lia).
  lwalk [0x9c8d4; 0x9d5cc].
  fold x. change ((x * 281474976710656) mod 18446744073709551616 / 72057594037927936) with (rgb_b x).
  pose proof (rgb_b_range x) as I3R. set (i3 := rgb_b x) in *.
  replace (i3 * 4) with (4 * i3) by (clear; lia).
  lwalk [0x9c8e0; 0x9d5cc].
  fold x.
  assert (I4R : 0 <= Z.land x 255 < 256) by (clear - XR; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  set (i4 := Z.land x 255) in *.
  replace (i4 * 4) with (4 * i4) by (clear; lia).
  (* [comment removed for export] *)
  lwalk [0x9c904; 0x9d5cc; 0x9c9bc].
  destruct (u32arr_nth gws i2 ltac:(lia)) as (g2 & NTH2).
  pose proof (u32arr_read asegs m gm gws i2 g2 _ UAGM NTH2 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9c91c; 0x9d5cc; 0x9c9cc].
  destruct (u32arr_nth gws i1 ltac:(lia)) as (g1 & NTH1).
  pose proof (u32arr_read asegs m gm gws i1 g1 _ UAGM NTH1 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9c934; 0x9d5cc; 0x9c9dc].
  destruct (u32arr_nth gws i3 ltac:(lia)) as (g3 & NTH3).
  pose proof (u32arr_read asegs m gm gws i3 g3 _ UAGM NTH3 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  lwalk [0x9c95c; 0x9d5cc; 0x9c9ec].
  destruct (u32arr_nth gws i4 ltac:(lia)) as (g4 & NTH4).
  pose proof (u32arr_read asegs m gm gws i4 g4 _ UAGM NTH4 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  (* [comment removed for export] *)
  lwalk [0x9c980; 0x9d5cc; 0x9c9fc].
  replace (datad + 4 * (i * wpl) + 4 * c) with (datad + 4 * (i * wpl + c)) by (clear; lia).
  unpark DSH. unpark SEP. unpark SEPG. unpark WSEP.
  arr_sw datad (i * wpl + c) (datad + 4 * (i * wpl + c)).
  park DSH. park SEP. park SEPG. park WSEP.
  (* [comment removed for export] *)
  lwalk [0x9c864; 0x9d2a0; 0x9d5cc].
  rewrite !(Z.mod_small (4 * c + 4) 18446744073709551616) by (clear - CW HW; lia).
  destruct k as [|k].
  - assert (EC : c + 1 = w / 4) by (clear - HK; lia).
    assert (GE : w <= 4 * c + 7) by (clear - EC HW; Z.div_mod_to_equations; lia).
    brF. lwalk [0x9d2a0].
    replace (4 * c + 4) with (4 * (w / 4)) by (clear - EC; lia).
    apply evt_done. unfold rmc_words_exit. do 9 eexists. do 2 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    repeat (split; [eassumption|]). eassumption.
  - assert (LT : 4 * c + 7 < w) by (clear - HK HC HW; Z.div_mod_to_equations; lia).
    brT.
    replace (4 * c + 4) with (4 * (c + 1)) by (clear; lia).
    eapply evt_cut.
    + eapply (IH (c + 1)) with (ws := ws) (gws := gws) (h := h) (w := w) (wa := wa) (gva := gva) (da := da) (i := i) (datas := datas) (gm := gm);
        try eassumption; try (clear - HK HC HW EWPL HH HI RSB LT CW; lia).
    + intros ms' PO. apply evt_done. unfold rmc_words_exit in PO |- *.
      destruct PO as (a1' & a2' & a5' & a7' & s3' & s5' & s7' & s8' & t3' & m' & wd' & E & MU' & WM' & R).
      exists a1', a2', a5', a7', s3', s5', s7', s8', t3', m', wd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition rmc_tail_exit (sp gp tp s0 a7 s3 s5 s7 s8 s9 t3 t5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (sb datas datad gm wpl w h i wa gva da : Z) (ws gws : list word) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' a5' a6' gv' : word) (m' : mem) (wd' : list word),
    ms' = MS (mkR (Z_to_bv 64 (datad + 4 * (i * wpl))) sp gp tp ONE ONE (NGM gm) s0 (Z_to_bv 64 sb) (Z_to_bv 64 gm) a1' a2' a3' ONE a5' a6' a7
                  (Z_to_bv 64 SHB) s3 (Z_to_bv 64 (datas + 4 * (i * wpl))) s5 (Z_to_bv 64 2147483648) s7 s8 s9 ONE
                  (Z_to_bv 64 (4 * (i * wpl))) t3 (Z_to_bv 64 (datas + 4 * (i * wpl))) t5 (Z_to_bv 64 (datad + 4 * (i * wpl))))
             F (Z_to_bv 64 0x9c178) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + 4 * (wpl * h)); (gva, gva + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpl * h))
    /\ u32arr asegs m' gm gws /\ acc asegs m' gm 1024
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpl * h /\ acc asegs m' datad (4 * (wpl * h))
    /\ rw_cells asegs m' (sb + 152) [C8 (Z_to_bv 64 gva); C8 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' (sb + 168) [C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 da); C8 (Z_to_bv 64 wa)]
    /\ rw_cells asegs m' wa [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' gva [C4 gv'].

Lemma rmc_tail : forall (k : nat) (j : Z)
    (sp gp tp s0 a1 a2 a5 a6 a7 s3 s5 s7 s8 s9 t3 t5 : word) F fc (m : mem)
    (sb datas datad gm wpl w h i wa gva da : Z) (ws wd gws : list word) (gv : word),
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
  0 < gva -> gva mod 4 = 0 -> gva + 4 <= 2^47 -> (gva + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= gva) -> (gva + 4 <= 0x10000 \/ SEGTOP_A <= gva) ->
  (gva + 4 <= datad \/ datad + 4 * (wpl * h) <= gva) -> (gva + 4 <= datas \/ datas + 4 * (wpl * h) <= gva) ->
  (gva + 4 <= gm \/ gm + 1024 <= gva) -> (gva + 4 <= wa \/ wa + 4 <= gva) ->
  0x10007fff8000 <= sb -> sb + 192 <= 2^47 -> datad + 4 * (wpl * h) <= sb -> gva + 4 <= sb ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpl * h -> acc asegs m datas (4 * (wpl * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpl * h -> acc asegs m datad (4 * (wpl * h)) ->
  u32arr asegs m gm gws -> Z.of_nat (length gws) = 256 -> acc asegs m gm 1024 ->
  rw_cells asegs m (sb + 152) [C8 (Z_to_bv 64 gva); C8 (Z_to_bv 64 1)] ->
  rw_cells asegs m (sb + 168) [C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 da); C8 (Z_to_bv 64 wa)] ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs m gva [C4 gv] -> mem_inv asegs m ->
  evt asegs (rmc_tail_exit sp gp tp s0 a7 s3 s5 s7 s8 s9 t3 t5 F fc m sb datas datad gm wpl w h i wa gva da ws gws)
    (MS (mkR (Z_to_bv 64 (datad + 4 * (i * wpl))) sp gp tp ONE ONE (NGM gm) s0 (Z_to_bv 64 sb) (Z_to_bv 64 gm) a1 a2 (Z_to_bv 64 j) ONE a5 a6 a7
             (Z_to_bv 64 SHB) s3 (Z_to_bv 64 (datas + 4 * (i * wpl))) s5 (Z_to_bv 64 2147483648) s7 s8 s9 ONE
             (Z_to_bv 64 (4 * (i * wpl))) t3 (Z_to_bv 64 (datas + 4 * (i * wpl))) t5 (Z_to_bv 64 (datad + 4 * (i * wpl))))
        F (Z_to_bv 64 0x9d2b0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j sp gp tp s0 a1 a2 a5 a6 a7 s3 s5 s7 s8 s9 t3 t5 F fc m sb datas datad gm wpl w h i wa gva da ws wd gws gv
    HK HJ HK1 HW EWPL HH HI RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG W0 WHI WSEP V0 V4 VHI VSH VSEG VSEP VSEPS VSEPG VSEPW
    SBLO SBHI SBD SBV UAS UASL ACCS UA UAL ACCD UAGM UAGL ACCG FL PW WC VC MI.
  { exfalso; clear - HK1; lia. }
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
  (* [comment removed for export] *)
  lwalk [0x9d2dc; 0x9d5cc; 0x9d36c].
  destruct (bytes_at_read1 m datas (u32s ws) (Z.lxor (datas + 4 * (i * wpl) + j) 3 - datas) HBS ltac:(lia)) as (sbb & R).
  replace (datas + (Z.lxor (datas + 4 * (i * wpl) + j) 3 - datas)) with (Z.lxor (datas + 4 * (i * wpl) + j) 3) in R by lia.
  lstep. clear R.
  (* [comment removed for export] *)
  lwalk [0x9d2e8; 0x9d5cc].
  assert (SBR : 0 <= bv_unsigned sbb < 256) by (pose proof (bv_unsigned_in_range 8 sbb) as Q; unfold bv_modulus in Q; change (2 ^ Z.of_N 8) with 256 in Q; exact Q).
  replace (bv_unsigned sbb * 4) with (4 * bv_unsigned sbb) by (clear; lia).
  set (ix := bv_unsigned sbb) in *.
  rewrite ?(Z.mod_small (gm + 4 * ix) 18446744073709551616) by (clear - SBR G0 GHI; lia).
  lwalk [0x9d314; 0x9d5cc; 0x9d380].
  destruct (u32arr_nth gws ix ltac:(lia)) as (g1 & NTH1).
  pose proof (u32arr_read asegs m gm gws ix g1 _ UAGM NTH1 ltac:(lia) eq_refl) as R.
  lstep. clear R.
  (* [comment removed for export] *)
  lwalk [0x9d324; 0x9d5cc].
  unpark VSH. unpark VSEP. unpark VSEPS. unpark VSEPG. unpark VSEPW.
  lstep.
  park VSH. park VSEP. park VSEPS. park VSEPG. park VSEPW.
  (* [comment removed for export] *)
  lwalk [0x9d34c; 0x9d5cc; 0x9d38c].
  lazymatch goal with U : u32arr asegs ?mm datad ?wsx |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_u8arr mm datad wsx U) as UA8;
    assert (UAL8 : Z.of_nat (length (u32s wsx)) = 4 * (wpl * h)) by (rewrite u32s_length; clear - UAL; lia);
    clear U UAL end.
  unfold sx32.
  unpark DSH. unpark SEP. unpark SEPG. unpark WSEP. unpark VSEP. unpark SBD.
  replace (Z.lxor (datad + 4 * (i * wpl) + j) 3) with (datad + (4 * (i * wpl) + j + 3 - 2 * ((datad + 4 * (i * wpl) + j) mod 4))) by (clear - LXD; lia).
  arr_sb datad (4 * (i * wpl) + j + 3 - 2 * ((datad + 4 * (i * wpl) + j) mod 4)) (datad + (4 * (i * wpl) + j + 3 - 2 * ((datad + 4 * (i * wpl) + j) mod 4))).
  park DSH. park SEP. park SEPG. park WSEP. park VSEP. park SBD.
  lazymatch goal with U : u8arr asegs ?mm datad ?bsx |- _ =>
    destruct (u8arr_u32arr mm datad bsx (wpl * h) U UAL8) as (wd1 & UA & UAL); clear U UAL8 end.
  (* [comment removed for export] *)
  lwalk [0x9d2b0; 0x9c178; 0x9d5cc].
  destruct k as [|k].
  - assert (EJ : j + 1 = w) by (clear - HK; lia).
    brF. lwalk [0x9c178].
    apply evt_done. unfold rmc_tail_exit.
    do 6 eexists. lazymatch goal with UAx : u32arr asegs ?mm datad ?wdx |- _ => exists mm, wdx end.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. repeat (split; [assumption|]). eassumption.
  - assert (LT : j + 1 < w) by (clear - HK HJ; lia).
    brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (ws := ws) (gws := gws) (h := h) (w := w) (wa := wa) (gva := gva) (da := da) (i := i) (datas := datas) (gm := gm);
        try eassumption; try (clear - HK HJ HW EWPL HH HI RSB LT JW; lia).
    + intros ms' PO. apply evt_done. unfold rmc_tail_exit in PO |- *.
      destruct PO as (a1' & a2' & a3' & a5' & a6' & gv' & m' & wd' & E & MU' & WM' & R).
      exists a1', a2', a3', a5', a6', gv', m', wd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Ltac row_xport H MU WM side :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
  lazymatch type of H with rw_cells _ ma ?A ?cs =>
    let D := fresh "DJ" in
    assert (D : disjoint_from W A (Z.of_nat (cells_size cs))) by (cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; side);
    apply (fun h => rw_cells_transport asegs W ma mb A cs h MU WM D) in H; clear D
  end end.

(* [comment removed for export] *)
Definition rmc_rows_exit (sp gp tp s0 s9 t5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (sb datas datad gm wpl w h fr : Z) (ws gws : list word) (c72 : word) : machine_state -> Prop :=
  fun ms' => exists (ra' a1' a2' a3' a5' a6' a7' s3' s4' s5' s6' s7' s8' s11' t3' t4' t6' gv' : word) (l104 iac : Z) (m' : mem) (wd' : list word),
    ms' = MS (mkR ra' sp gp tp ONE ONE (NGM gm) s0 (Z_to_bv 64 sb) (Z_to_bv 64 gm) a1' a2' a3' ONE a5' a6' a7' (Z_to_bv 64 SHB) s3' s4' s5' s6' s7' s8' s9 ONE s11' t3' t4' t5 t6')
             F (Z_to_bv 64 0x9d4d8) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + 4 * (wpl * h)); (fr + 48, fr + 48 + 4); (sb + 104, sb + 128)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' datas ws /\ acc asegs m' datas (4 * (wpl * h))
    /\ u32arr asegs m' gm gws /\ acc asegs m' gm 1024
    /\ u32arr asegs m' datad wd' /\ Z.of_nat (length wd') = wpl * h /\ acc asegs m' datad (4 * (wpl * h))
    /\ rw_cells asegs m' (fr + 80) [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' (fr + 48) [C4 gv']
    /\ rw_cells asegs m' (fr + 96) [C4 (Z_to_bv 64 h)] /\ rw_cells asegs m' (fr + 112) [C4 (Z_to_bv 64 8)]
    /\ rw_cells asegs m' (sb + 48) [C8 (Z_to_bv 64 wpl)] /\ rw_cells asegs m' (sb + 72) [C8 c72]
    /\ rw_cells asegs m' (sb + 88) [C8 (Z_to_bv 64 (fr + 96)); C8 (Z_to_bv 64 wpl); C8 (Z_to_bv 64 l104); C8 (Z_to_bv 64 iac); C8 (Z_to_bv 64 iac); C8 (Z_to_bv 64 datad)]
    /\ rw_cells asegs m' (sb + 152) [C8 (Z_to_bv 64 (fr + 48)); C8 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' (sb + 168) [C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 (fr + 112)); C8 (Z_to_bv 64 (fr + 80))].

Lemma rmc_rows : forall (k : nat) (i : Z)
    (ra sp gp tp s0 a1 a2 a3 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (sb datas datad gm wpl w h fr : Z) (ws wd gws : list word) (gv c72 : word) (l104 : Z),
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
  0x10007fff8000 <= sb -> sb + 192 <= 2^47 -> datad + 4 * (wpl * h) <= sb -> fr + 320 <= sb ->
  datas + 4 * (wpl * h) <= sb -> gm + 1024 <= sb ->
  u32arr asegs m datas ws -> Z.of_nat (length ws) = wpl * h -> acc asegs m datas (4 * (wpl * h)) ->
  u32arr asegs m datad wd -> Z.of_nat (length wd) = wpl * h -> acc asegs m datad (4 * (wpl * h)) ->
  u32arr asegs m gm gws -> Z.of_nat (length gws) = 256 -> acc asegs m gm 1024 ->
  rw_cells asegs m (fr + 80) [C4 (Z_to_bv 64 w)] -> rw_cells asegs m (fr + 48) [C4 gv] ->
  rw_cells asegs m (fr + 96) [C4 (Z_to_bv 64 h)] -> rw_cells asegs m (fr + 112) [C4 (Z_to_bv 64 8)] ->
  rw_cells asegs m (sb + 48) [C8 (Z_to_bv 64 wpl)] -> rw_cells asegs m (sb + 72) [C8 c72] ->
  rw_cells asegs m (sb + 88) [C8 (Z_to_bv 64 (fr + 96)); C8 (Z_to_bv 64 wpl); C8 (Z_to_bv 64 l104); C8 (Z_to_bv 64 (i * wpl)); C8 (Z_to_bv 64 (i * wpl)); C8 (Z_to_bv 64 datad)] ->
  rw_cells asegs m (sb + 152) [C8 (Z_to_bv 64 (fr + 48)); C8 (Z_to_bv 64 1)] ->
  rw_cells asegs m (sb + 168) [C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 (fr + 112)); C8 (Z_to_bv 64 (fr + 80))] ->
  mem_inv asegs m ->
  evt asegs (rmc_rows_exit sp gp tp s0 s9 t5 F fc m sb datas datad gm wpl w h fr ws gws c72)
    (MS (mkR ra sp gp tp ONE ONE (NGM gm) s0 (Z_to_bv 64 sb) (Z_to_bv 64 gm) a1 a2 a3 ONE (Z_to_bv 64 wpl) (Z_to_bv 64 i) a7
             (Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 ONE s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9c1b0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp s0 a1 a2 a3 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m sb datas datad gm wpl w h fr ws wd gws gv c72 l104
    HK HI HK1 HW EWPL HH RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG
    F0 F32 FHI FSH FSEG FSD FSS FSG SBLO SBHI SBD SBF SBS SBG
    UAS UASL ACCS UA UAL ACCD UAGM UAGL ACCG WC VC HC DC C48 C72 C88 FL PW MI.
  { exfalso; clear - HK1; lia. }
  assert (WPL4 : w <= 4 * wpl /\ 4 * wpl <= w + 3 /\ 0 < wpl <= 5000) by (rewrite EWPL; clear - HW; Z.div_mod_to_equations; lia).
  assert (HIH : 0 <= i < h) by (clear - HK HI HK1; lia).
  assert (NS : i * wpl + wpl <= wpl * h) by (clear - HIH WPL4; nia).
  assert (NS0 : 0 <= i * wpl <= 0x1000000) by (clear - HIH WPL4 HH RSB; nia).
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(datad, datad + 4 * (wpl * h)); (fr + 48, fr + 48 + 4); (sb + 104, sb + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  (* [comment removed for export] *)
  lwalk [0x9c854; 0x9d5cc; 0x9d5bc; 0x9cd1c; 0x9c284].
  rewrite !Z.add_0_r. rewrite !(Z.mod_small (i * wpl) 18446744073709551616) by (clear - NS0; lia).
  replace (datad + i * wpl * 4) with (datad + 4 * (i * wpl)) by (clear; lia).
  replace (datas + i * wpl * 4) with (datas + 4 * (i * wpl)) by (clear; lia).
  replace (i * wpl * 4) with (4 * (i * wpl)) by (clear; lia).
  rewrite !(sx32_small w) by (clear - HW; lia).
  lstep.
  (* [comment removed for export] *)
  eapply (evt_cut asegs (rmc_words_exit sp gp tp s0 s9 t5 F fc _ sb datas datad gm wpl w h i (fr + 80) (fr + 48) (fr + 112) ws gws)).
  { destruct (Z_lt_ge_dec w 4) as [WL|WG].
    - (* [comment removed for export] *)
      brT. lwalk [0x9d2a0; 0x9d5cc].
      apply evt_done. unfold rmc_words_exit.
      replace (4 * (w / 4)) with 0 by (clear - WL HW; Z.div_mod_to_equations; lia).
      do 9 eexists. lazymatch goal with UAx : u32arr asegs ?mm datad ?wdx |- _ => exists mm, wdx end.
      split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      repeat (split; [assumption|]). assumption.
    - brF. lwalk [0x9c864; 0x9d5cc].
      assert (Q1 : Z.of_nat (Z.to_nat (w / 4)) = w / 4 - 0) by (clear - WG HW; Z.div_mod_to_equations; lia).
      assert (Q3 : (1 <= Z.to_nat (w / 4))%nat) by (clear - WG HW; Z.div_mod_to_equations; lia).
      lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?FF _ ?ffc None ?mm _) =>
        epose proof (rmc_words (Z.to_nat (w / 4)) 0 sp gp tp s0 _ _ _ _ _ _ _ _ s9 _ t5 FF ffc mm
                       sb datas datad gm wpl w h i (fr + 80) (fr + 48) (fr + 112) ws _ gws
                       Q1 ltac:(clear; lia) Q3 HW EWPL HH HIH RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG
                       ltac:(clear - F0; lia) ltac:(clear - FHI; lia) ltac:(clear - FSD; unpark FSD; lia) SBLO SBHI SBD
                       UAS UASL ACCS ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) UAGM UAGL ACCG FL PW WC MIx) as ZR end.
      unfold SHB in ZR.
      replace (4 * 0) with 0 in ZR by (clear; lia).
      exact ZR. }
  clear UA UAL ACCD MI.
  intros ms1 PO1. unfold rmc_words_exit in PO1.
  destruct PO1 as (a1a & a2a & a5a & a7a & s3a & s5a & s7a & s8a & t3a & ma & wda & -> & MUa & WMa & MIa & UASa & ACCSa & UAGMa & ACCGa & UAa & UALa & ACCDa & FLa & PWa & WCa).
  row_xport C48 MUa WMa ltac:(repeat split; try exact I; clear - SBD; lia).
  row_xport C72 MUa WMa ltac:(repeat split; try exact I; clear - SBD; lia).
  row_xport C88 MUa WMa ltac:(repeat split; try exact I; clear - SBD; lia).
  row_xport HC MUa WMa ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  row_xport DC MUa WMa ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  row_xport VC MUa WMa ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  clear FL PW WC.
  (* [comment removed for export] *)
  lwalk [0x9d2b0; 0x9c178; 0x9d5cc]. 
  rewrite ?(sx32_small w) by (clear - HW; lia).
  (* [comment removed for export] *)
  eapply (evt_cut asegs (rmc_tail_exit sp gp tp s0 a7a s3a s5a s7a s8a s9 t3a t5 F fc ma sb datas datad gm wpl w h i (fr + 80) (fr + 48) (fr + 112) ws gws)).
  { destruct (Z.eq_dec (w mod 4) 0) as [WZ|WNZ].
    - (* [comment removed for export] *)
      assert (GE : w <= 4 * (w / 4)) by (clear - WZ HW; Z.div_mod_to_equations; lia).
      brF. lwalk [0x9c178].
      apply evt_done. unfold rmc_tail_exit.
      do 6 eexists. exists ma, wda.
      split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      repeat (split; [assumption|]). first [assumption | eassumption].
    - assert (LTW : 4 * (w / 4) < w) by (clear - WNZ HW; Z.div_mod_to_equations; lia).
      brT.
      assert (T1 : Z.of_nat (Z.to_nat (w - 4 * (w / 4))) = w - 4 * (w / 4)) by (clear - LTW; lia).
      assert (T3 : (1 <= Z.to_nat (w - 4 * (w / 4)))%nat) by (clear - LTW; lia).
      epose proof (rmc_tail (Z.to_nat (w - 4 * (w / 4))) (4 * (w / 4)) sp gp tp s0 _ _ _ _ a7a s3a s5a s7a s8a s9 t3a t5 F fc ma
                     sb datas datad gm wpl w h i (fr + 80) (fr + 48) (fr + 112) ws wda gws _
                     T1 ltac:(clear - HW; Z.div_mod_to_equations; lia) T3 HW EWPL HH HIH RSB S0 S8 SHI SSH SSEG D0 D8 DHI DSH DSEG G0 G8 GHI GSH GSEG SEP SEPG
                     ltac:(clear - F0; lia) ltac:(clear - FHI; lia) ltac:(clear - FSD; unpark FSD; lia)
                     ltac:(clear - F0; lia) ltac:(clear - F32; Z.div_mod_to_equations; lia) ltac:(clear - FHI; lia) ltac:(clear - FSH; unpark FSH; lia) ltac:(clear - FSEG; unpark FSEG; unfold SEGTOP_A; lia)
                     ltac:(clear - FSD; unpark FSD; lia) ltac:(clear - FSS; unpark FSS; lia) ltac:(clear - FSG; unpark FSG; lia) ltac:(clear; lia)
                     SBLO SBHI SBD ltac:(clear - SBF; lia)
                     UASa UASL ACCSa UAa UALa ACCDa UAGMa UAGL ACCGa FLa PWa WCa VC MIa) as ZT.
      unfold SHB in ZT. exact ZT. }
  clear UAa UALa ACCDa MIa VC UASa ACCSa UAGMa ACCGa WCa FLa PWa.
  intros ms2 PO2. unfold rmc_tail_exit in PO2.
  destruct PO2 as (a1b & a2b & a3b & a5b & a6b & gvb & mb & wdb & -> & MUb & WMb & MIb & UASb & ACCSb & UAGMb & ACCGb & UAb & UALb & ACCDb & FLb & PWb & WCb & VCb).
  row_xport C48 MUb WMb ltac:(repeat split; try exact I; clear - SBD SBF; lia).
  row_xport C72 MUb WMb ltac:(repeat split; try exact I; clear - SBD SBF; lia).
  row_xport C88 MUb WMb ltac:(repeat split; try exact I; clear - SBD SBF; lia).
  row_xport HC MUb WMb ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  row_xport DC MUb WMb ltac:(repeat split; try exact I; clear - FSD; unpark FSD; lia).
  lazymatch type of MUa with munch _ ?mq ?mr =>
    pose proof (munch_trans _ _ _ _ MU (munch_weaken [(datad, datad + 4 * (wpl * h))] [(datad, datad + 4 * (wpl * h)); (fr + 48, fr + 48 + 4); (sb + 104, sb + 128)] mq mr ltac:(subfp_tac) MUa)) as MU1 end.
  lazymatch type of MUb with munch _ ?mq ?mr =>
    pose proof (munch_trans _ _ _ _ MU1 (munch_weaken [(datad, datad + 4 * (wpl * h)); (fr + 48, fr + 48 + 4)] [(datad, datad + 4 * (wpl * h)); (fr + 48, fr + 48 + 4); (sb + 104, sb + 128)] mq mr ltac:(subfp_tac) MUb)) as MU2 end.
  lazymatch type of WM with wmono _ _ ?mx => pose proof (wmono_trans asegs _ _ _ WM (wmono_trans asegs _ _ _ WMa WMb)) as WM2 end.
  clear MUa MUb WMa WMb MU1 MU WM. rename MU2 into MU. rename WM2 into WM.
  (* [comment removed for export] *)
  lwalk [0x9c194; 0x9d5cc].
  rewrite ?(sx32_small h) by (clear - HH; lia).
  swrap_fix.
  replace (i * wpl + wpl) with ((i + 1) * wpl) by (clear; lia).
  lstep.
  lwalk [0x9c1a4; 0x9d5cc].
  rewrite ?(sx32_small h) by (clear - HH; lia).
  swrap_fix.
  replace (i * wpl + wpl) with ((i + 1) * wpl) by (clear; lia).
  lstep.
  lstep.
  destruct k as [|k].
  - assert (EI : i + 1 = h) by (clear - HK; lia).
    brF. lwalk [0x9d4d8].
    apply evt_done. unfold rmc_rows_exit.
    do 18 eexists. exists i, ((i + 1) * wpl). lazymatch goal with UAx : u32arr asegs ?mm datad ?wdx |- _ => exists mm, wdx end.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    repeat (split; [first [assumption | eassumption]|]). first [assumption | eassumption].
  - assert (LT : i + 1 < h) by (clear - HK HI; lia).
    brT.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (ws := ws) (gws := gws) (wd := wdb) (gv := gvb) (w := w) (datas := datas) (datad := datad) (gm := gm) (fr := fr) (l104 := i);
        try eassumption; try (clear - HK HI LT; lia).
    + intros ms' PO. apply evt_done. unfold rmc_rows_exit in PO |- *.
      destruct PO as (ra' & a1' & a2' & a3' & a5' & a6' & a7' & s3' & s4' & s5' & s6' & s7' & s8' & s11' & t3' & t4' & t6' & gv' & l104' & iac' & m' & wd' & E & MU' & WM' & R).
      exists ra', a1', a2', a3', a5', a6', a7', s3', s4', s5', s6', s7', s8', s11', t3', t4', t6', gv', l104', iac', m', wd'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

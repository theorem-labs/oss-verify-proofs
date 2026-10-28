(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bdefs Sj_num_abig.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section AFrame.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma new_frame_facts : forall Σ (m : mem) f k n lo, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> In (f, k) (rt_frames RT Σ) ->
  n = fs_size k - 8 -> n mod 8 = 0 -> 0 <= n ->
  f mod 64 = 0 /\ 0x6e0000 <= f /\ f + n <= lo
  /\ (f + n <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + n / 8 <= f)
  /\ 0 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + n / 8 <= lo.
Proof using AF.
  intros Σ m f k n lo HA LO Hin -> N8 N0.
  pose proof (af_frames_align RT AF Σ m f k HA Hin) as (F64 & _).
  split; [exact F64|].
  apply (fframe_obj_facts RT AF Σ m f (fs_size k - 8) lo HA LO); [Z.div_mod_to_equations; lia| exact N0| exact N8|].
  exists f, k. split; [exact Hin| lia].
Qed.

Lemma frames_sep : forall Σ (m : mem) f k fr X n, ART RT Σ m -> rt_frames RT Σ = (f, k) :: fr ->
  X mod 8 = 0 -> 0 <= n -> n mod 8 = 0 ->
  (exists g kg, In (g, kg) fr /\ g <= X /\ X + n <= g + fs_size kg - 8) ->
  let S := f / 8 + 2147450880 in let XS := X / 8 + 2147450880 in let fn := fs_size k in
  (X + n <= f \/ f + fn <= X) /\ (X + n <= S \/ S + fn / 8 <= X) /\ (XS + n / 8 <= f \/ f + fn <= XS) /\ (XS + n / 8 <= S \/ S + fn / 8 <= XS).
Proof using AF.
  intros Σ m f k fr X n HA EFR X8 N0 N8 (g & kg & Hg & G1 & G2). cbv zeta.
  assert (HinF : In (f, k) (rt_frames RT Σ)) by (rewrite EFR; left; reflexivity).
  assert (HinG : In (g, kg) (rt_frames RT Σ)) by (rewrite EFR; right; exact Hg).
  pose proof (af_frames_disj RT AF Σ m f k g kg [] fr HA EFR Hg) as D1.
  pose proof (af_fshadow_apart RT AF Σ m f k HA HinF) as (_ & AFf). specialize (AFf g kg HinG).
  pose proof (af_fshadow_apart RT AF Σ m g kg HA HinG) as (_ & AFg). specialize (AFg f k HinF).
  pose proof (fframe_ranges RT AF Σ m f k HA HinF) as (F0 & _ & FSZ & _).
  pose proof (fframe_ranges RT AF Σ m g kg HA HinG) as (G0 & _ & GSZ & _).
  pose proof (af_frames_align RT AF Σ m f k HA HinF) as (F64 & _).
  pose proof (af_frames_align RT AF Σ m g kg HA HinG) as (G64 & _).
  assert (FS8 : fs_size k mod 8 = 0).
  { unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ Z.of_nat k) with (8 * 2 ^ Z.of_nat k * 8) by lia. apply Z.mod_mul. lia. }
  assert (GS8 : fs_size kg mod 8 = 0).
  { unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ Z.of_nat kg) with (8 * 2 ^ Z.of_nat kg * 8) by lia. apply Z.mod_mul. lia. }
  unfold shad, SHB in *.
  set (fn := fs_size k) in *. set (gn := fs_size kg) in *. clearbody fn gn.
  repeat split; Z.div_mod_to_equations; lia.
Qed.

End AFrame.

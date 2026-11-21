(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.cks Require Import CkTables CkMathAdler.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Abbreviation RSEGS := Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition AMAG : Z := 0x10568.
Definition RO_LO : Z := 0x10568.
Definition RO_HI : Z := 0x10570.

Definition img_ok (m : word -> option byte) : Prop :=
  forall i, (RO_LO <= i < RO_HI)%Z -> m (Z_to_bv 64 i) = None.

Lemma img_ok_of_range : forall m (lo hi : Z),
  (forall i, (lo <= i < hi)%Z -> m (Z_to_bv 64 i) = None) -> (lo <= RO_LO)%Z -> (RO_HI <= hi)%Z -> img_ok m.
Proof. intros m lo hi H Hlo Hhi i Hi. apply H. unfold RO_LO, RO_HI in *. lia. Qed.

Lemma wview_ro_none : forall m x, (0x10000 <= x < 0x14000)%Z ->
  m (Z_to_bv 64 x) = None -> wview RSEGS m (Z_to_bv 64 x) = None.
Proof.
  intros m x Hx Hm. unfold wview. rewrite Hm. rewrite u64_lit by lia.
  cbn [find_segment M.loaded_segments Src_zlib_zlib_uncompress2_fuzzer_repro_loaded_segments seg_base seg_size
       Src_zlib_zlib_uncompress2_fuzzer_repro_segment_000 Z.of_N].
  replace ((65536 <=? x)%Z && (x + 1 <=? 65536 + 16384)%Z)%bool with true
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma store_ok_off_ro : forall m lo (N : nat),
  store_ok RSEGS m (Z_to_bv 64 lo) N = true -> (0 <= lo)%Z -> (lo + Z.of_nat N <= 2 ^ 64)%Z ->
  (0 < Z.of_nat N)%Z ->
  img_ok m -> (RO_HI <= lo \/ lo + Z.of_nat N <= RO_LO)%Z.
Proof.
  intros m lo N Hok Hlo Hhi HN Himg.
  destruct (Z.le_gt_cases RO_HI lo) as [|H1]; [left; assumption|].
  destruct (Z.le_gt_cases (lo + Z.of_nat N) RO_LO) as [|H2]; [right; assumption|].
  exfalso. unfold RO_LO, RO_HI in *.
  set (x := Z.max lo 0x10568).
  assert (Hx1 : (lo <= x < lo + Z.of_nat N)%Z) by (subst x; lia).
  assert (Hx2 : (0x10568 <= x < 0x10570)%Z) by (subst x; lia).
  apply (store_ok_all RSEGS m N (Z_to_bv 64 lo) ltac:(rewrite u64_lit by lia; lia) Hok (Z_to_bv 64 x)).
  - rewrite !u64_lit by lia. lia.
  - apply wview_ro_none; [lia|]. apply Himg. unfold RO_LO, RO_HI. lia.
Qed.

Lemma img_ok_wbytes : forall m (wa : word) bs,
  img_ok m ->
  (bv_unsigned wa + Z.of_nat (length bs) <= RO_LO \/ RO_HI <= bv_unsigned wa)%Z ->
  (bv_unsigned wa + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  img_ok (wbytes m wa bs).
Proof.
  intros m wa bs Hi Hout Hnw i Hr. unfold RO_LO, RO_HI in *.
  rewrite wbytes_outside; [apply Hi; exact Hr | | exact Hnw].
  unfold in_rng. rewrite u64_lit by lia. lia.
Qed.

Definition amag_bs : list byte :=
  match rdn RSEGS (fun _ => None) (Z_to_bv 64 AMAG) 8 return list byte with Some bs => bs | None => @nil byte end.

Lemma rd_amag_rom : rdn RSEGS (fun _ => None) (Z_to_bv 64 AMAG) 8 = Some amag_bs.
Proof. vm_compute. reflexivity. Qed.

Lemma rd_amag : forall m, img_ok m -> rdn RSEGS m (Z_to_bv 64 AMAG) 8 = Some amag_bs.
Proof.
  intros m Hm. rewrite (rdn_img RSEGS m AMAG 8 RO_LO RO_HI Hm); [apply rd_amag_rom | | | |]; unfold AMAG, RO_LO, RO_HI; cbn; lia.
Qed.

Lemma amag_bs_val : bytes_le_to_Z amag_bs = AMAGIC.
Proof. vm_compute. reflexivity. Qed.

Lemma amag_bs_v : bytes_le_to_Z amag_bs = bv_unsigned (Z_to_bv 64 AMAGIC).
Proof. rewrite amag_bs_val. reflexivity. Qed.
End FXG.

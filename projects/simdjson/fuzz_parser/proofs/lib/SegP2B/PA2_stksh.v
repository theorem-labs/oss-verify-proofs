(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Mem Cells RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells ABase AMalloc_iface AU_iface AU_kit Stdio_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Notation SH := 2147450880%Z (only parsing).

(* [comment removed for export] *)
Lemma shad_of_16 : forall SP16 k, 0 <= 16 * SP16 - k -> k mod 8 = 0 -> shad (16 * SP16 - k) = SH + 2 * SP16 - k / 8.
Proof.
  intros SP16 k H1 H2. rewrite shad_div. unfold ASHOFF.
  replace (16 * SP16 - k) with ((2 * SP16 - k / 8) * 8) by (Z.div_mod_to_equations; lia). rewrite Z.div_mul by lia. lia.
Qed.

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma acr_stksh : forall (CI : list (Z * Z)) LB SP SP16, ATOP <= 16 * SP16 - 8640 -> 16 * SP16 <= 2^47 ->
  aclient_range CI LB SP (SH + 2 * SP16 - 1080) 1080.
Proof.
  intros CI LB SP SP16 H1 H2. unfold aclient_range. right. right. left. unfold ASHOFF. split; lia.
Qed.

(* [comment removed for export] *)
Lemma wstk_of_shclean : forall m lo hi RLO RHI SP16, shclean m lo hi RLO RHI -> lo <= 16 * SP16 - 8640 -> 16 * SP16 <= hi ->
  0 <= 16 * SP16 - 8640 -> wr_at bsegs m (SH + 2 * SP16 - 1080) 1080.
Proof.
  intros m lo hi RLO RHI SP16 HC Hlo Hhi H0.
  pose proof (shclean_hull _ _ _ _ _ HC) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof (shclean_wr _ _ _ _ _ HC) as W.
  assert (E1 : shad RLO <= SH + 2 * SP16 - 1080).
  { rewrite shad_div. unfold ASHOFF. assert (RLO / 8 <= (16 * SP16 - 8640) / 8) by (apply Z.div_le_mono; lia).
    assert (E : (16 * SP16 - 8640) / 8 = 2 * SP16 - 1080) by (Z.div_mod_to_equations; lia). lia. }
  assert (E2 : SH + 2 * SP16 <= shad RHI).
  { rewrite shad_div. unfold ASHOFF. assert (16 * SP16 / 8 <= RHI / 8) by (apply Z.div_le_mono; lia).
    assert (E : 16 * SP16 / 8 = 2 * SP16) by (Z.div_mod_to_equations; lia). lia. }
  apply (wr_at_sub m _ _ _ _ W); lia.
Qed.

Lemma wstk_of_rclean : forall m r SP16, rclean m r -> r_lo r <= 16 * SP16 - 8640 -> 16 * SP16 <= r_hi r -> 0 <= 16 * SP16 - 8640 ->
  wr_at bsegs m (SH + 2 * SP16 - 1080) 1080.
Proof. intros m r SP16 HC H1 H2 H3. exact (wstk_of_shclean m _ _ _ _ SP16 (rclean_shclean _ _ HC) H1 H2 H3). Qed.

(* [comment removed for export] *)
Lemma wstk_pres : forall (CI : list (Z * Z)) LB SP m m' SP16, aheap_pres CI LB SP m m' -> ATOP <= 16 * SP16 - 8640 -> 16 * SP16 <= 2^47 ->
  wr_at bsegs m (SH + 2 * SP16 - 1080) 1080 -> wr_at bsegs m' (SH + 2 * SP16 - 1080) 1080.
Proof. intros CI LB SP m m' SP16 HP H1 H2 W. exact (aheap_pres_wr_at CI LB SP m m' _ _ HP W (acr_stksh CI LB SP SP16 H1 H2)). Qed.
End CANSEC.

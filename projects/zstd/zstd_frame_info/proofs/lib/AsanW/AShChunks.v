(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase ABytes FsKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. Local Ltac2 Set LiaHints.tbl := fun () => "0040>2110276096.14 22615015996.144856259436.12 48935769329.1200000100;00B00ISS2H12H22HiS2W22H2S2H02H1".
split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma chunks_ablock_shadow : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
  (n mod 8 <> 0 -> rw_cells asegs m (shad A + n / 8) [C1 (Z_to_bv 8 (n mod 8))]) ->
  ablock_shadow m A n.
Proof.
  intros m A n Hn AL A0 AH BODY LAST g Hg0 Hg.
  Local Ltac2 Set LiaHints.tbl := fun () => "0090>22846284697.2023027050969.1327238400069.1929784460807.1341537595851.2241607817466.2048685608068.2249737587287.2267335594273.1400000=00G00N00O00c01001801F01JS2Hn2S02S12GTS2AL2A02AHS2Hg2D6SS2B13Hg02S02S12D32LES2Hg2D22D32GTS2B13Hg0S2B13Hg02D32LES2Hn".
assert (S0 : 0x5f6000 <= shad A /\ shad A + n / 8 < 2^62) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (DB : 0 <= n / 8 /\ 8 * (n / 8) <= n /\ n < 8 * (n / 8) + 8 /\ n mod 8 = n - 8 * (n / 8)) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  destruct DB as (D1 & D2 & D3 & D6). destruct S0 as [S0 S1].
  destruct (Z.leb_spec (8 * g + 8) n) as [LE|GT].
  - (* [comment removed for export] *)
    destruct BODY as [[_ [B0 [B1 BR]]] _]. cbn [cells_bytes cbytes] in B1, BR. rewrite app_nil_r in B1, BR.
    rewrite repeat_length in B1, BR.
    specialize (BR (Z.to_nat g) ltac:(lia)). rewrite Z2Nat.id in BR by lia. rewrite <- mrd_high by lia. rewrite BR.
    rewrite nth_error_repeat by lia. reflexivity.
  - (* [comment removed for export] *)
    assert (g = n / 8) as -> by lia. assert (NE : n mod 8 <> 0) by lia.
    rewrite <- mrd_high by lia. pose proof (rw_cells_read asegs m _ _ 0%nat (C1 (Z_to_bv 8 (n mod 8))) (LAST NE) eq_refl) as R.
    cbn [csize cbytes] in R. rewrite Z.add_0_r in R.
    (* [comment removed for export] *)
    rewrite ov_rdn in R. cbn [rdn] in R.
    destruct (mrd asegs m (wa (shad A + n / 8))) as [b|] eqn:E; [| unfold mrd in E; rewrite E in R; discriminate].
    unfold mrd in E. rewrite E in R. injection R as ->. rewrite <- D6. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.

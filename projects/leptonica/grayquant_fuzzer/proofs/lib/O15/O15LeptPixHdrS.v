(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15LeptStderr O15LeptBase.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15CL7a.
Import O15CL7a.O15LeptErr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15CL8a.
Import O15CL8a.O15LeptPixHdr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15_code_gqR_pixhdr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixHdr.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  #[local] Definition FR6 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
       (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)).

  (* [comment removed for export] *)
  Lemma ph_A : forall regs m (s w h d : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 64)%Z -> dval d ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x16868 : word) m rom) (mkst regs' (0x168a4 : word) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 Hd DV SOK H2 H1 H10 H11 H12. pose proof (dval_range d DV). unfold FR6.
    eexists. split.
    - zv F_16810 D_16810 (Z_to_bv 64 (s - 48)).
      stepST F_16814 D_16814 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16818 D_16818 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1681c D_1681c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_16820 D_16820 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_16824 D_16824 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_16828 D_16828 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      sn F_1682c D_1682c.
      stepb_ft F_16830 D_16830 ltac:(condZ).
      sn F_16834 D_16834. sn F_16838 D_16838. sn F_1683c D_1683c.
      sn F_16840 D_16840. sn F_16844 D_16844.
      stepb_ft F_16848 D_16848 ltac:(pin; apply depth_test_ok; exact DV).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Abad : forall regs m (s w h d : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 64)%Z -> ~ dval d ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x16868 : word) m rom) (mkst regs' (0x169dc : word) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 Hd ND SOK H2 H1 H10 H11 H12. unfold FR6.
    destruct (Z_lt_ge_dec 32 d) as [Hbig|Hsmall].
    - eexists. split.
      + zv F_16810 D_16810 (Z_to_bv 64 (s - 48)).
        stepST F_16814 D_16814 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
        stepST F_16818 D_16818 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
        stepST F_1681c D_1681c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
        stepST F_16820 D_16820 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
        stepST F_16824 D_16824 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
        stepST F_16828 D_16828 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
        sn F_1682c D_1682c.
        stepb_tk F_16830 D_16830 ltac:(condZ).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + zv F_16810 D_16810 (Z_to_bv 64 (s - 48)).
        stepST F_16814 D_16814 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
        stepST F_16818 D_16818 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
        stepST F_1681c D_1681c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
        stepST F_16820 D_16820 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
        stepST F_16824 D_16824 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
        stepST F_16828 D_16828 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
        sn F_1682c D_1682c.
        stepb_ft F_16830 D_16830 ltac:(condZ).
        sn F_16834 D_16834. sn F_16838 D_16838. sn F_1683c D_1683c.
        sn F_16840 D_16840. sn F_16844 D_16844.
        stepb_tk F_16848 D_16848 ltac:(pin; apply depth_test_bad; [lia | exact ND]).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_B : forall regs m (s w h d : Z),
    (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> dval d ->
    getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x168a4 : word) m rom) (mkst regs' (0x16a2c : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (4 * (wpl_of w d * h)) /\ getr regs' 14 = Z_to_bv 64 0x4000001 /\ getr regs' 8 = Z_to_bv 64 (wpl_of w d)
      /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [8; 13; 14]%list) regs regs'.
  Proof.
    intros regs m s w h d Hw Hh Hwh DV H10 H11 H12. pose proof (dval_range d DV). pose proof (wpl_of_range w d Hw DV) as Hwpl.
    assert (Hdw : (0 <= d * w <= 32 * 1000000)%Z) by nia.
    assert (Hsz : (4 * (wpl_of w d * h) < 2 ^ 31)%Z).
    { unfold wpl_of in *. assert ((w * d + 31) / 32 * 8 <= w * d + 31)%Z by (pose proof (Z.mul_div_le (w * d + 31) 32 ltac:(lia)); lia). nia. }
    eexists. split.
    - stepb_ft F_1684c D_1684c ltac:(condZ).
      stepb_ft F_16850 D_16850 ltac:(condZ).
      zv F_16854 D_16854 (Z_to_bv 64 (d * w)).
      sn F_16858 D_16858. sn F_1685c D_1685c.
      stepb_tk F_16860 D_16860 ltac:(condZ).
      zv F_16910 D_16910 (Z_to_bv 64 (d * w + 31)).
      sn F_16914 D_16914. fixv (Z_to_bv 64 (wpl_of w d)) ltac:(unfold wpl_of; rewrite zbv_srli by lia; f_equal; change (2 ^ 5)%Z with 32%Z; f_equal; lia).
      zv F_16918 D_16918 (Z_to_bv 64 (wpl_of w d * h)).
      stepiv F_1691c D_1691c (Z_to_bv 64 (4 * (wpl_of w d * h))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_16920 D_16920. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srli by lia; f_equal; apply Z.div_small; lia).
      stepb_tk F_16924 D_16924 ltac:(condZ).
      sn F_169cc D_169cc. sn F_169d0 D_169d0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_C : forall regs m (sz : Z),
    (0 <= sz <= 67108864)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    exists regs',
      msteps SEGS (mkst regs (0x16a2c : word) m rom) (mkst regs' (0x16a60 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 20001 /\ regs_agree (fun r => In r [13]%list) regs regs'.
  Proof.
    intros regs m sz Hsz H13 H14. eexists. split.
    - stepb_tk F_169d4 D_169d4 ltac:(condZ). sn F_16a00 D_16a00. sn F_16a04 D_16a04. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Cbad : forall regs m (sz : Z),
    (67108864 < sz < 2 ^ 64)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    rdn SEGS m (Z_to_bv 64 0x2c780) 8 = Some (Z_to_le_bytes 8 0x2d7f0) -> rdn SEGS m (Z_to_bv 64 0x2d7f0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x16a2c : word) m rom) (mkst regs' (0x153dc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10454 /\ getr regs' 11 = Z_to_bv 64 0x1093b /\ getr regs' 1 = Z_to_bv 64 0x16ab8
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m sz Hsz H13 H14 Rg Rs. eexists. split.
    - stepb_ft F_169d4 D_169d4 ltac:(condZ).
      sn F_169d8 D_169d8.
      stepLD F_169dc D_169dc (Z_to_le_bytes 8 0x2d7f0) (Z_to_bv 64 0x2d7f0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_169e0 D_169e0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_169e4 D_169e4.
      stepb_ft F_169e8 D_169e8 ltac:(condZ).
      sn F_169ec D_169ec. sn F_169f0 D_169f0. sn F_169f4 D_169f4. sn F_169f8 D_169f8. sn F_169fc D_169fc.
      sn F_16a5c D_16a5c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ph_D : forall regs m (w : Z),
    (1 <= w <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    msteps SEGS (mkst regs (0x16a60 : word) m rom) (mkst regs (0x16a8c : word) m rom).
  Proof. intros regs m w Hw H10 H13. stepb_tk F_16a08 D_16a08 ltac:(condZ). apply mst_refl. Qed.

  Lemma ph_Dbad : forall regs m (w : Z),
    (20000 < w < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (Z_to_bv 64 0x2c780) 8 = Some (Z_to_le_bytes 8 0x2d7f0) -> rdn SEGS m (Z_to_bv 64 0x2d7f0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x16a60 : word) m rom) (mkst regs' (0x153dc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x1124f /\ getr regs' 11 = Z_to_bv 64 0x1093b /\ getr regs' 1 = Z_to_bv 64 0x16ab8
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m w Hw H10 H13 Rg Rs. eexists. split.
    - stepb_ft F_16a08 D_16a08 ltac:(condZ).
      sn F_16a0c D_16a0c.
      stepLD F_16a10 D_16a10 (Z_to_le_bytes 8 0x2d7f0) (Z_to_bv 64 0x2d7f0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16a14 D_16a14 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16a18 D_16a18.
      stepb_ft F_16a1c D_16a1c ltac:(condZ).
      sn F_16a20 D_16a20. sn F_16a24 D_16a24. sn F_16a28 D_16a28. sn F_16a2c D_16a2c. sn F_16a30 D_16a30.
      sn F_16a5c D_16a5c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_E : forall regs m (w h d : Z),
    (1 <= h <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d -> getr regs 13 = Z_to_bv 64 20001 ->
    exists regs',
      msteps SEGS (mkst regs (0x16a8c : word) m rom) (mkst regs' (0x20ea0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 64 /\ getr regs' 1 = Z_to_bv 64 0x16af8
      /\ getr regs' 19 = Z_to_bv 64 w /\ getr regs' 18 = Z_to_bv 64 h /\ getr regs' 20 = Z_to_bv 64 d /\ getr regs' 9 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m w h d Hh H10 H11 H12 H13. eexists. split.
    - stepb_tk F_16a34 D_16a34 ltac:(condZ).
      sn F_16a84 D_16a84. sn F_16a88 D_16a88. sn F_16a8c D_16a8c. sn F_16a90 D_16a90. sn F_16a94 D_16a94. sn F_16a98 D_16a98.
      sn F_16a9c D_16a9c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ph_Ebad : forall regs m (h : Z),
    (20000 < h < 2 ^ 64)%Z -> getr regs 11 = Z_to_bv 64 h -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (Z_to_bv 64 0x2c780) 8 = Some (Z_to_le_bytes 8 0x2d7f0) -> rdn SEGS m (Z_to_bv 64 0x2d7f0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x16a8c : word) m rom) (mkst regs' (0x153dc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10d7a /\ getr regs' 11 = Z_to_bv 64 0x1093b /\ getr regs' 1 = Z_to_bv 64 0x16ab8
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m h Hh H11 H13 Rg Rs. eexists. split.
    - stepb_ft F_16a34 D_16a34 ltac:(condZ).
      sn F_16a38 D_16a38.
      stepLD F_16a3c D_16a3c (Z_to_le_bytes 8 0x2d7f0) (Z_to_bv 64 0x2d7f0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16a40 D_16a40 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16a44 D_16a44.
      stepb_ft F_16a48 D_16a48 ltac:(condZ).
      sn F_16a4c D_16a4c. sn F_16a50 D_16a50. sn F_16a54 D_16a54. sn F_16a58 D_16a58.
      sn F_16a5c D_16a5c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_R0 : forall regs m (s : Z) (ret s0v s1v s2v s3v s4v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs',
      msteps SEGS (mkst regs (0x16ab8 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v Hs Hs64 Hret R8 R16 R24 R32 R40 R48 H2. eexists. split.
    - sn F_16a60 D_16a60.
      stepLD8 F_16a64 D_16a64 ret. stepLD8 F_16a68 D_16a68 s0v. stepLD8 F_16a6c D_16a6c s1v.
      stepLD8 F_16a70 D_16a70 s2v. stepLD8 F_16a74 D_16a74 s3v. stepLD8 F_16a78 D_16a78 s4v.
      zv F_16a7c D_16a7c (Z_to_bv 64 s).
      stepret F_16a80 D_16a80 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_H : forall regs m (s msg : Z) (ret s0v s1v s2v s3v s4v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 0x1093b ->
    exists regs',
      msteps SEGS (mkst regs (0x16a00 : word) m rom) (mkst regs' (0x15478 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x1093b
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s msg ret s0v s1v s2v s3v s4v Hs Hs64 R8 R16 R24 R32 R40 R48 H2 H10 H11. eexists. split.
    - sn F_169a8 D_169a8.
      stepLD8 F_169ac D_169ac ret. stepLD8 F_169b0 D_169b0 s0v. stepLD8 F_169b4 D_169b4 s1v.
      stepLD8 F_169b8 D_169b8 s2v. stepLD8 F_169bc D_169bc s3v. stepLD8 F_169c0 D_169c0 s4v.
      zv F_169c4 D_169c4 (Z_to_bv 64 s).
      sn F_169c8 D_169c8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_G : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x2c780) 8 = Some (Z_to_le_bytes 8 0x2d7f0) -> rdn SEGS m (Z_to_bv 64 0x2d7f0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x169dc : word) m rom) (mkst regs' (0x16a00 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x105c4 /\ getr regs' 11 = Z_to_bv 64 0x1093b
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m Rg Rs. eexists. split.
    - sn F_16984 D_16984.
      stepLD F_16988 D_16988 (Z_to_le_bytes 8 0x2d7f0) (Z_to_bv 64 0x2d7f0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_1698c D_1698c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16990 D_16990.
      stepb_ft F_16994 D_16994 ltac:(condZ).
      sn F_16998 D_16998. sn F_1699c D_1699c. sn F_169a0 D_169a0. sn F_169a4 D_169a4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Fbad : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x2c780) 8 = Some (Z_to_le_bytes 8 0x2d7f0) -> rdn SEGS m (Z_to_bv 64 0x2d7f0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x16af8 : word) m rom) (mkst regs' (0x16a00 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x1051f /\ getr regs' 11 = Z_to_bv 64 0x1093b
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_16aa0 D_16aa0 ltac:(condZ).
      sn F_16ac8 D_16ac8.
      stepLD F_16acc D_16acc (Z_to_le_bytes 8 0x2d7f0) (Z_to_bv 64 0x2d7f0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16ad0 D_16ad0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16ad4 D_16ad4.
      stepb_ft F_16ad8 D_16ad8 ltac:(condZ).
      sn F_16adc D_16adc. sn F_16ae0 D_16ae0. sn F_16ae4 D_16ae4. sn F_16ae8 D_16ae8. sn F_16aec D_16aec.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_F : forall regs m (s w h d pix : Z) (ret s0v s1v s2v s3v s4v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> dval d -> (1 <= w <= 20000)%Z -> (1 <= h <= 20000)%Z ->
    (4096 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z -> (pix + 64 <= s - 48 \/ s <= pix)%Z ->
    store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pix ->
    getr regs 19 = Z_to_bv 64 w -> getr regs 18 = Z_to_bv 64 h -> getr regs 20 = Z_to_bv 64 d -> getr regs 9 = Z_to_bv 64 1 ->
    getr regs 8 = Z_to_bv 64 (wpl_of w d) ->
    exists regs',
      msteps SEGS (mkst regs (0x16af8 : word) m rom)
        (mkst regs' ret
          (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
             (Z_to_bv 64 pix) (word_to_le_bytes 4 (Z_to_bv 64 w)))
             (Z_to_bv 64 (pix + 4)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
             (Z_to_bv 64 (pix + 8)) (word_to_le_bytes 4 (Z_to_bv 64 d)))
             (Z_to_bv 64 (pix + 16)) (word_to_le_bytes 4 (Z_to_bv 64 (wpl_of w d))))
             (Z_to_bv 64 (pix + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (spp_of d))))
             (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
             (Z_to_bv 64 (pix + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s w h d pix ret s0v s1v s2v s3v s4v Hs Hs64 Hret DV Hw Hh Hpix Hpix64 DJ SOK R8 R16 R24 R32 R40 R48 H2 H10 H19 H18 H20 H9 H8.
    pose proof (dval_range d DV). pose proof (wpl_of_range w d ltac:(lia) DV).
    unfold spp_of. destruct ((d =? 24) || (d =? 32))%bool eqn:E; eexists; split.
    - 
      stepb_ft F_16aa0 D_16aa0 ltac:(condZ).
      sn F_16aa4 D_16aa4.
      sn F_16aa8 D_16aa8.
      stepST F_16aac D_16aac (Z_to_bv 64 pix) (Z_to_bv 64 w) ltac:(sok_in SOK).
      stepST F_16ab0 D_16ab0 (Z_to_bv 64 (pix + 4)) (Z_to_bv 64 h) ltac:(sok_in SOK).
      stepST F_16ab4 D_16ab4 (Z_to_bv 64 (pix + 8)) (Z_to_bv 64 d) ltac:(sok_in SOK).
      stepST F_16ab8 D_16ab8 (Z_to_bv 64 (pix + 16)) (Z_to_bv 64 (wpl_of w d)) ltac:(sok_in SOK).
      stepb_tk F_16abc D_16abc ltac:(pin; rewrite (spp_test d DV); exact E).
        sn F_16af0 D_16af0.
        stepST F_16af4 D_16af4 (Z_to_bv 64 (pix + 12)) (Z_to_bv 64 3) ltac:(sok_in SOK).
        stepfence F_16af8 D_16af8.
        stepST F_16afc D_16afc (Z_to_bv 64 (pix + 20)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_16b00 D_16b00.
        stepST F_16b04 D_16b04 (Z_to_bv 64 (pix + 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
        sn F_16b08 D_16b08.
        stepLD8 F_16a64 D_16a64 ret. stepLD8 F_16a68 D_16a68 s0v. stepLD8 F_16a6c D_16a6c s1v.
        stepLD8 F_16a70 D_16a70 s2v. stepLD8 F_16a74 D_16a74 s3v. stepLD8 F_16a78 D_16a78 s4v.
        zv F_16a7c D_16a7c (Z_to_bv 64 s).
        stepret F_16a80 D_16a80 ret ltac:(bveq).
        apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - 
      stepb_ft F_16aa0 D_16aa0 ltac:(condZ).
      sn F_16aa4 D_16aa4.
      sn F_16aa8 D_16aa8.
      stepST F_16aac D_16aac (Z_to_bv 64 pix) (Z_to_bv 64 w) ltac:(sok_in SOK).
      stepST F_16ab0 D_16ab0 (Z_to_bv 64 (pix + 4)) (Z_to_bv 64 h) ltac:(sok_in SOK).
      stepST F_16ab4 D_16ab4 (Z_to_bv 64 (pix + 8)) (Z_to_bv 64 d) ltac:(sok_in SOK).
      stepST F_16ab8 D_16ab8 (Z_to_bv 64 (pix + 16)) (Z_to_bv 64 (wpl_of w d)) ltac:(sok_in SOK).
      stepb_ft F_16abc D_16abc ltac:(pin; rewrite (spp_test d DV); exact E).
        sn F_16ac0 D_16ac0. sn F_16ac4 D_16ac4.
        stepST F_16af4 D_16af4 (Z_to_bv 64 (pix + 12)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_16af8 D_16af8.
        stepST F_16afc D_16afc (Z_to_bv 64 (pix + 20)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_16b00 D_16b00.
        stepST F_16b04 D_16b04 (Z_to_bv 64 (pix + 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
        sn F_16b08 D_16b08.
        stepLD8 F_16a64 D_16a64 ret. stepLD8 F_16a68 D_16a68 s0v. stepLD8 F_16a6c D_16a6c s1v.
        stepLD8 F_16a70 D_16a70 s2v. stepLD8 F_16a74 D_16a74 s3v. stepLD8 F_16a78 D_16a78 s4v.
        zv F_16a7c D_16a7c (Z_to_bv 64 s).
        stepret F_16a80 D_16a80 ret ltac:(bveq).
        apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
Definition cells6 (m : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v).

Lemma cells6_FR6 : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells6 (FR6 m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20).
Proof. intros m s ret regs Hs Hs64. unfold cells6, FR6. repeat split; rdn_solve. Qed.

Lemma cells6_frm : forall C s' m m' s ret s0v s1v s2v s3v s4v, Cok C -> FRM C s' m m' ->
  (s' <= s - 48)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z ->
  cells6 m s ret s0v s1v s2v s3v s4v -> cells6 m' s ret s0v s1v s2v s3v s4v.
Proof.
  intros C s' m m' s ret s0v s1v s2v s3v s4v CK F Hs' Hlo Hs64 (R1 & R2 & R3 & R4 & R5 & R6). unfold cells6.
  rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
Qed.

Lemma str_pixCreateHeader : str16 0x1093b 15. Proof. str16_tac. Qed.
Lemma str_msg_64mb : str16 0x10454 47. Proof. str16_tac. Qed.
Lemma str_msg_w20k : str16 0x1124f 51. Proof. str16_tac. Qed.
Lemma str_msg_h20k : str16 0x10d7a 52. Proof. str16_tac. Qed.
Lemma str_msg_depth : str16 0x105c4 38. Proof. str16_tac. Qed.
Lemma str_msg_pixd : str16 0x1051f 13. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Theorem pixCreateHeader_sure_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3db50 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h d ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_hdr <= kR)%Z -> (RB_hdr <= bR)%Z ->
  (forall A' m' vm' regs' (pix : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pix -> pix_new C A A' m' pix (pix_hdr w h d) ->
     aroom A' vm' (kR - RK_hdr) (bR - RB_hdr) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x16868 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw1 Hh1 HOK0 kR bR Hrm Hrk Hrb HK.
  destruct HOK0 as (DV & Hw20 & Hh20 & Hsz0).
  assert (Hw : (1 <= w <= 1000000)%Z) by lia. assert (Hh : (1 <= h <= 1000000)%Z) by lia.
  assert (Hwh : (w * h <= 400000000)%Z) by nia. assert (Hd : (0 <= d < 2 ^ 64)%Z) by (pose proof (dval_range d DV); lia).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (RR0 : forall x, In x cs_rest -> getr regs x = getr regs x) by (intros; reflexivity).
  - (* [comment removed for export] *)
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    destruct (ph_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) Hd DV SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q10 & Q11 & Q12 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (WP1 : W C A (FR6 m s ret regs) md /\ POSTM C A s m (FR6 m s ret regs)) by (unfold FR6; wp_win CK).
    destruct WP1 as [HW1 PM1]. set (M1 := FR6 m s ret regs) in *.
    pose proof (cells6_FR6 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
    destruct (ph_B al_rom r1 M1 s w h d Hw Hh Hwh DV Q10 Q11 Q12) as (r2 & RUN2 & P13 & P14 & P8 & P10 & P11 & P12 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    assert (RR2 : forall x, In x cs_rest -> getr r2 x = getr regs x) by rest_solve.
    assert (P2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (Hszhi : (4 * (wpl_of w d * h) < 2 ^ 64)%Z) by nia.
    assert (SMALL : (67108864 >= 4 * (wpl_of w d * h))%Z) by lia.
    destruct (ph_C al_rom r2 M1 (4 * (wpl_of w d * h)) ltac:(lia) P13 P14) as (r3 & RUN3 & V13 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    assert (RR3 : forall x, In x cs_rest -> getr r3 x = getr regs x) by rest_solve.
    assert (V10 : getr r3 10 = Z_to_bv 64 w) by (csr; reflexivity).
    assert (V11 : getr r3 11 = Z_to_bv 64 h) by (csr; reflexivity).
    assert (V12 : getr r3 12 = Z_to_bv 64 d) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (WOK : (20000 >= w)%Z) by lia.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (ph_D al_rom r3 M1 w ltac:(lia) V10 V13) |].
    assert (HOK : (20000 >= h)%Z) by lia.
    (* [comment removed for export] *)
    destruct (ph_E al_rom r3 M1 w h d ltac:(lia) V10 V11 V12 V13) as (r4 & RUN4 & X10 & X11 & X1 & X19 & X18 & X20 & X9 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
    assert (X4 : getr r4 4 = Z_to_bv 64 0x3db50) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (X8 : getr r4 8 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
    replace (0x20ea0 : word) with (Z_to_bv 64 0x20ea0) by (apply bv_eq; reflexivity).
    apply (W_calloc16_sure C A M1 md r4 1 64 kR bR (Z_to_bv 64 0x16af8) (s - 48) S CK HW1 X10 X11 ltac:(lia) ltac:(lia) ltac:(lia) Hrm ltac:(unfold RK_hdr in Hrk; lia) ltac:(rewrite (alloc_margin_small (1 * 64)) by lia; unfold RB_hdr in Hrb; lia) ltac:(unfold ROOM_NMAX; lia) X1
             ltac:(red; apply bv_eq; reflexivity) X4 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r5 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hrma.
    replace (Z_to_bv 64 0x16af8) with (0x16af8 : word) by (apply bv_eq; reflexivity).
    assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
    pose proof (cells6_frm C (s - 48) M1 m1 s _ _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
    + (* [comment removed for export] *)
      assert (Hpx : (4096 <= u res)%Z /\ (u res + 64 <= alloc_top (c_vm C))%Z).
      { destruct (blk_range C A1 m1 _ res (1 * 64) CK HWa L1 ltac:(lia)) as [G1 G2]. lia. }
      pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
      assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
      set (pix := u res) in *. clearbody pix.
      rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
      assert (PX0 : PIXat m1 pix pix0).
      { apply PIXat_zero; [lia | lia |]. intros i Hi. unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
      destruct CE2 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
      assert (Y19 : getr r5 19 = Z_to_bv 64 w) by (csr; reflexivity).
      assert (Y18 : getr r5 18 = Z_to_bv 64 h) by (csr; reflexivity).
      assert (Y20 : getr r5 20 = Z_to_bv 64 d) by (csr; reflexivity).
      assert (Y9 : getr r5 9 = Z_to_bv 64 1) by (csr; reflexivity).
      assert (Y8 : getr r5 8 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
      assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      destruct (ph_F al_rom r5 m1 s w h d pix ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ltac:(lia) ltac:(lia) Hret DV ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        as (r6 & RUN6 & V2' & V10' & V1' & V8' & V9' & V18' & V19' & V20' & AG6).
      { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
        unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m1 pix pix0 x PX0 ltac:(lia) E). }
      { exact Z1. } { exact Z2. } { exact Z3. } { exact Z4. } { exact Z5. } { exact Z6. }
      { exact Y2. } { exact Hres. } { exact Y19. } { exact Y18. } { exact Y20. } { exact Y9. } { exact Y8. }
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
      match goal with |- realizes _ (mkCfg (mkst _ _ ?MM _) _) _ => set (M7 := MM) end.
      assert (WP7 : W C A1 M7 (with_vmmaps vm1 md) /\ POSTM C A s m M7).
      { subst M7.
        repeat (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pix) _ 64); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
        split; [exact HWa | exact PMa']. }
      destruct WP7 as [HW7 PM7].
      pose proof (spp_of_range d) as Hspp.
      assert (PX7 : PIXat M7 pix (pix_hdr w h d)).
      { subst M7. unfold pix_hdr.
        apply (PIX_wr_fmt _ pix (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 0 0) 0); [|lia].
        apply (PIX_wr_rc _ pix (PIXV w h d (spp_of d) (wpl_of w d) 0 0 0 0 0 0 0 0) 1); [|lia].
        apply (PIX_wr_spp _ pix (PIXV w h d 0 (wpl_of w d) 0 0 0 0 0 0 0 0) (spp_of d)); [|lia].
        apply (PIX_wr_wpl _ pix (PIXV w h d 0 0 0 0 0 0 0 0 0 0) (wpl_of w d)); [|lia].
        apply (PIX_wr_d _ pix (PIXV w h 0 0 0 0 0 0 0 0 0 0 0) d); [|lia].
        apply (PIX_wr_h _ pix (PIXV w 0 0 0 0 0 0 0 0 0 0 0 0) h); [|lia].
        apply (PIX_wr_w _ pix pix0 w); [exact PX0|lia]. }
      apply (HK A1 M7 vm1 r6 pix HW7).
      * apply cs_kept_of_rest; [csr; reflexivity | csr; reflexivity | csr; reflexivity |]. rest_solve.
      * exact PM7.
      * exact V10'.
      * unfold pix_new. do 7 (split; [first [assumption | lia] |]). exact PX7.
      * rewrite (alloc_margin_small (1 * 64)) in Hrma by lia. apply (aroom_mono _ _ _ _ _ _ Hrma); unfold RK_hdr, RB_hdr in *; lia.
Qed.



End PixHdr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

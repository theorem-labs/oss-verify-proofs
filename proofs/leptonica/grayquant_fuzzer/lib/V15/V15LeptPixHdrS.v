(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptStderr V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL7a.
Import V15CL7a.V15LeptErr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15_code_gqR_pixhdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixHdr.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
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
      msteps SEGS (mkst regs (0x16d34 : word) m rom) (mkst regs' (0x16d70 : word) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 Hd DV SOK H2 H1 H10 H11 H12. pose proof (dval_range d DV). unfold FR6.
    eexists. split.
    - zv F_16c30 D_16c30 (Z_to_bv 64 (s - 48)).
      stepST F_16c34 D_16c34 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16c38 D_16c38 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_16c3c D_16c3c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_16c40 D_16c40 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_16c44 D_16c44 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_16c48 D_16c48 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      sn F_16c4c D_16c4c.
      stepb_ft F_16c50 D_16c50 ltac:(condZ).
      sn F_16c54 D_16c54. sn F_16c58 D_16c58. sn F_16c5c D_16c5c.
      sn F_16c60 D_16c60. sn F_16c64 D_16c64.
      stepb_ft F_16c68 D_16c68 ltac:(pin; apply depth_test_ok; exact DV).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Abad : forall regs m (s w h d : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 64)%Z -> ~ dval d ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x16d34 : word) m rom) (mkst regs' (0x16ea8 : word) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 Hd ND SOK H2 H1 H10 H11 H12. unfold FR6.
    destruct (Z_lt_ge_dec 32 d) as [Hbig|Hsmall].
    - eexists. split.
      + zv F_16c30 D_16c30 (Z_to_bv 64 (s - 48)).
        stepST F_16c34 D_16c34 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
        stepST F_16c38 D_16c38 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
        stepST F_16c3c D_16c3c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
        stepST F_16c40 D_16c40 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
        stepST F_16c44 D_16c44 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
        stepST F_16c48 D_16c48 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
        sn F_16c4c D_16c4c.
        stepb_tk F_16c50 D_16c50 ltac:(condZ).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + zv F_16c30 D_16c30 (Z_to_bv 64 (s - 48)).
        stepST F_16c34 D_16c34 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
        stepST F_16c38 D_16c38 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
        stepST F_16c3c D_16c3c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
        stepST F_16c40 D_16c40 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
        stepST F_16c44 D_16c44 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
        stepST F_16c48 D_16c48 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
        sn F_16c4c D_16c4c.
        stepb_ft F_16c50 D_16c50 ltac:(condZ).
        sn F_16c54 D_16c54. sn F_16c58 D_16c58. sn F_16c5c D_16c5c.
        sn F_16c60 D_16c60. sn F_16c64 D_16c64.
        stepb_tk F_16c68 D_16c68 ltac:(pin; apply depth_test_bad; [lia | exact ND]).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_B : forall regs m (s w h d : Z),
    (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> dval d ->
    getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x16d70 : word) m rom) (mkst regs' (0x16ef8 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (4 * (wpl_of w d * h)) /\ getr regs' 14 = Z_to_bv 64 0x4000001 /\ getr regs' 20 = Z_to_bv 64 (wpl_of w d)
      /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [20; 13; 14]%list) regs regs'.
  Proof.
    intros regs m s w h d Hw Hh Hwh DV H10 H11 H12. pose proof (dval_range d DV). pose proof (wpl_of_range w d Hw DV) as Hwpl.
    assert (Hdw : (0 <= d * w <= 32 * 1000000)%Z) by nia.
    assert (Hsz : (4 * (wpl_of w d * h) < 2 ^ 31)%Z).
    { unfold wpl_of in *. assert ((w * d + 31) / 32 * 8 <= w * d + 31)%Z by (pose proof (Z.mul_div_le (w * d + 31) 32 ltac:(lia)); lia). nia. }
    eexists. split.
    - stepb_ft F_16c6c D_16c6c ltac:(condZ).
      stepb_ft F_16c70 D_16c70 ltac:(condZ).
      zv F_16c74 D_16c74 (Z_to_bv 64 (d * w)).
      sn F_16c78 D_16c78. sn F_16c7c D_16c7c.
      stepb_tk F_16c80 D_16c80 ltac:(condZ).
      zv F_16d30 D_16d30 (Z_to_bv 64 (d * w + 31)).
      sn F_16d34 D_16d34. fixv (Z_to_bv 64 (wpl_of w d)) ltac:(unfold wpl_of; rewrite zbv_srli by lia; f_equal; change (2 ^ 5)%Z with 32%Z; f_equal; lia).
      zv F_16d38 D_16d38 (Z_to_bv 64 (wpl_of w d * h)).
      stepiv F_16d3c D_16d3c (Z_to_bv 64 (4 * (wpl_of w d * h))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_16d40 D_16d40. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srli by lia; f_equal; apply Z.div_small; lia).
      stepb_tk F_16d44 D_16d44 ltac:(condZ).
      sn F_16dec D_16dec. sn F_16df0 D_16df0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_C : forall regs m (sz : Z),
    (0 <= sz <= 67108864)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    exists regs',
      msteps SEGS (mkst regs (0x16ef8 : word) m rom) (mkst regs' (0x16f2c : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 20001 /\ regs_agree (fun r => In r [13]%list) regs regs'.
  Proof.
    intros regs m sz Hsz H13 H14. eexists. split.
    - stepb_tk F_16df4 D_16df4 ltac:(condZ). sn F_16e20 D_16e20. sn F_16e24 D_16e24. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Cbad : forall regs m (sz : Z),
    (67108864 < sz < 2 ^ 64)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x16ef8 : word) m rom) (mkst regs' (0x15520 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10454 /\ getr regs' 11 = Z_to_bv 64 0x1093b /\ getr regs' 1 = Z_to_bv 64 0x16f84
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m sz Hsz H13 H14 Rg Rs. eexists. split.
    - stepb_ft F_16df4 D_16df4 ltac:(condZ).
      sn F_16df8 D_16df8.
      stepLD F_16dfc D_16dfc (Z_to_le_bytes 8 0x35268) (Z_to_bv 64 0x35268) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16e00 D_16e00 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16e04 D_16e04.
      stepb_ft F_16e08 D_16e08 ltac:(condZ).
      sn F_16e0c D_16e0c. sn F_16e10 D_16e10. sn F_16e14 D_16e14. sn F_16e18 D_16e18. sn F_16e1c D_16e1c.
      sn F_16e7c D_16e7c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ph_D : forall regs m (w : Z),
    (1 <= w <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    msteps SEGS (mkst regs (0x16f2c : word) m rom) (mkst regs (0x16f58 : word) m rom).
  Proof. intros regs m w Hw H10 H13. stepb_tk F_16e28 D_16e28 ltac:(condZ). apply mst_refl. Qed.

  Lemma ph_Dbad : forall regs m (w : Z),
    (20000 < w < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x16f2c : word) m rom) (mkst regs' (0x15520 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x1124f /\ getr regs' 11 = Z_to_bv 64 0x1093b /\ getr regs' 1 = Z_to_bv 64 0x16f84
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m w Hw H10 H13 Rg Rs. eexists. split.
    - stepb_ft F_16e28 D_16e28 ltac:(condZ).
      sn F_16e2c D_16e2c.
      stepLD F_16e30 D_16e30 (Z_to_le_bytes 8 0x35268) (Z_to_bv 64 0x35268) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16e34 D_16e34 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16e38 D_16e38.
      stepb_ft F_16e3c D_16e3c ltac:(condZ).
      sn F_16e40 D_16e40. sn F_16e44 D_16e44. sn F_16e48 D_16e48. sn F_16e4c D_16e4c. sn F_16e50 D_16e50.
      sn F_16e7c D_16e7c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_E : forall regs m (w h d : Z),
    (1 <= h <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d -> getr regs 13 = Z_to_bv 64 20001 ->
    exists regs',
      msteps SEGS (mkst regs (0x16f58 : word) m rom) (mkst regs' (0x2891c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 64 /\ getr regs' 1 = Z_to_bv 64 0x16fc0
      /\ getr regs' 19 = Z_to_bv 64 w /\ getr regs' 9 = Z_to_bv 64 h /\ getr regs' 8 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 19]%list) regs regs'.
  Proof.
    intros regs m w h d Hh H10 H11 H12 H13. eexists. split.
    - stepb_tk F_16e54 D_16e54 ltac:(condZ).
      sn F_16ea4 D_16ea4. sn F_16ea8 D_16ea8. sn F_16eac D_16eac. sn F_16eb0 D_16eb0. sn F_16eb4 D_16eb4.
      sn F_16eb8 D_16eb8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ph_Ebad : forall regs m (h : Z),
    (20000 < h < 2 ^ 64)%Z -> getr regs 11 = Z_to_bv 64 h -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x16f58 : word) m rom) (mkst regs' (0x15520 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10d7a /\ getr regs' 11 = Z_to_bv 64 0x1093b /\ getr regs' 1 = Z_to_bv 64 0x16f84
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m h Hh H11 H13 Rg Rs. eexists. split.
    - stepb_ft F_16e54 D_16e54 ltac:(condZ).
      sn F_16e58 D_16e58.
      stepLD F_16e5c D_16e5c (Z_to_le_bytes 8 0x35268) (Z_to_bv 64 0x35268) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16e60 D_16e60 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16e64 D_16e64.
      stepb_ft F_16e68 D_16e68 ltac:(condZ).
      sn F_16e6c D_16e6c. sn F_16e70 D_16e70. sn F_16e74 D_16e74. sn F_16e78 D_16e78.
      sn F_16e7c D_16e7c.
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
      msteps SEGS (mkst regs (0x16f84 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v Hs Hs64 Hret R8 R16 R24 R32 R40 R48 H2. eexists. split.
    - sn F_16e80 D_16e80.
      stepLD8 F_16e84 D_16e84 ret. stepLD8 F_16e88 D_16e88 s0v. stepLD8 F_16e8c D_16e8c s1v.
      stepLD8 F_16e90 D_16e90 s2v. stepLD8 F_16e94 D_16e94 s3v. stepLD8 F_16e98 D_16e98 s4v.
      zv F_16e9c D_16e9c (Z_to_bv 64 s).
      stepret F_16ea0 D_16ea0 ret ltac:(bveq).
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
      msteps SEGS (mkst regs (0x16ecc : word) m rom) (mkst regs' (0x155bc : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x1093b
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s msg ret s0v s1v s2v s3v s4v Hs Hs64 R8 R16 R24 R32 R40 R48 H2 H10 H11. eexists. split.
    - sn F_16dc8 D_16dc8.
      stepLD8 F_16dcc D_16dcc ret. stepLD8 F_16dd0 D_16dd0 s0v. stepLD8 F_16dd4 D_16dd4 s1v.
      stepLD8 F_16dd8 D_16dd8 s2v. stepLD8 F_16ddc D_16ddc s3v. stepLD8 F_16de0 D_16de0 s4v.
      zv F_16de4 D_16de4 (Z_to_bv 64 s).
      sn F_16de8 D_16de8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_G : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x16ea8 : word) m rom) (mkst regs' (0x16ecc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x105c4 /\ getr regs' 11 = Z_to_bv 64 0x1093b
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m Rg Rs. eexists. split.
    - sn F_16da4 D_16da4.
      stepLD F_16da8 D_16da8 (Z_to_le_bytes 8 0x35268) (Z_to_bv 64 0x35268) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16dac D_16dac (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16db0 D_16db0.
      stepb_ft F_16db4 D_16db4 ltac:(condZ).
      sn F_16db8 D_16db8. sn F_16dbc D_16dbc. sn F_16dc0 D_16dc0. sn F_16dc4 D_16dc4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Fbad : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x16fc0 : word) m rom) (mkst regs' (0x16ecc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x1051f /\ getr regs' 11 = Z_to_bv 64 0x1093b
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_16ebc D_16ebc ltac:(condZ).
      sn F_16f0c D_16f0c.
      stepLD F_16f10 D_16f10 (Z_to_le_bytes 8 0x35268) (Z_to_bv 64 0x35268) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16f14 D_16f14 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16f18 D_16f18.
      stepb_ft F_16f1c D_16f1c ltac:(condZ).
      sn F_16f20 D_16f20. sn F_16f24 D_16f24. sn F_16f28 D_16f28. sn F_16f2c D_16f2c. sn F_16f30 D_16f30.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_F : forall regs m (s w h d pix wpl : Z) (ret s0v s1v s2v s3v s4v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> dval d -> (1 <= w <= 20000)%Z -> (1 <= h <= 20000)%Z -> (0 <= wpl < 2 ^ 31)%Z ->
    (4096 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z -> (pix + 64 <= s - 48 \/ s <= pix)%Z -> (pix mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pix ->
    getr regs 19 = Z_to_bv 64 w -> getr regs 9 = Z_to_bv 64 h -> getr regs 8 = Z_to_bv 64 d -> getr regs 20 = Z_to_bv 64 wpl ->
    exists regs',
      msteps SEGS (mkst regs (0x16fc0 : word) m rom)
        (mkst regs' ret
          (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
             (Z_to_bv 64 pix) (word_to_le_bytes 4 (Z_to_bv 64 w)))
             (Z_to_bv 64 (pix + 4)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
             (Z_to_bv 64 (pix + 8)) (word_to_le_bytes 4 (Z_to_bv 64 d)))
             (Z_to_bv 64 (pix + 16)) (word_to_le_bytes 4 (Z_to_bv 64 wpl)))
             (Z_to_bv 64 (pix + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (spp_of d))))
             (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
             (Z_to_bv 64 (pix + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s w h d pix wpl ret s0v s1v s2v s3v s4v Hs Hs64 Hret DV Hw Hh Hwpl Hpix Hpix64 DJ AL8 SOK R8 R16 R24 R32 R40 R48 H2 H10 H19 H9 H8 H20.
    pose proof (dval_range d DV).
    Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).
    unfold spp_of. destruct ((d =? 24) || (d =? 32))%bool eqn:E; eexists; split.
    - stepb_ft F_16ebc D_16ebc ltac:(condZ).
      sn F_16ec0 D_16ec0. sn F_16ec4 D_16ec4. sn F_16ec8 D_16ec8.
      (* [comment removed for export] *)
      stepb_ft F_176a8 D_176a8 ltac:(condZ). guard8 F_176ac D_176ac AL8.
      stepb_ft F_176b0 D_176b0 ltac:(condZ). stepb_ft F_176b4 D_176b4 ltac:(condZ).
      stepST F_176b8 D_176b8 (Z_to_bv 64 pix) (Z_to_bv 64 w) ltac:(sok_in SOK).
      sn F_176bc D_176bc. stepret F_176c0 D_176c0 (0x16fd0 : word) ltac:(bveq).
      sn F_16ecc D_16ecc. sn F_16ed0 D_16ed0. sn F_16ed4 D_16ed4.
      (* [comment removed for export] *)
      stepb_ft F_17730 D_17730 ltac:(condZ). guard8 F_17734 D_17734 AL8.
      stepb_ft F_17738 D_17738 ltac:(condZ). stepb_ft F_1773c D_1773c ltac:(condZ).
      stepST F_17740 D_17740 (Z_to_bv 64 (pix + 4)) (Z_to_bv 64 h) ltac:(sok_in SOK).
      sn F_17744 D_17744. stepret F_17748 D_17748 (0x16fdc : word) ltac:(bveq).
      sn F_16ed8 D_16ed8. sn F_16edc D_16edc. sn F_16ee0 D_16ee0.
      (* [comment removed for export] *)
      stepb_ft F_177b8 D_177b8 ltac:(condZ). stepb_ft F_177bc D_177bc ltac:(condZ). guard8 F_177c0 D_177c0 AL8.
      stepb_ft F_177c4 D_177c4 ltac:(condZ).
      stepST F_177c8 D_177c8 (Z_to_bv 64 (pix + 8)) (Z_to_bv 64 d) ltac:(sok_in SOK).
      sn F_177cc D_177cc. stepret F_177d0 D_177d0 (0x16fe8 : word) ltac:(bveq).
      guard8 F_16ee4 D_16ee4 AL8. stepb_ft F_16ee8 D_16ee8 ltac:(condZ).
      sn F_16eec D_16eec.
      stepST F_16ef0 D_16ef0 (Z_to_bv 64 (pix + 16)) (Z_to_bv 64 wpl) ltac:(sok_in SOK).
      sn F_16ef4 D_16ef4. sn F_16ef8 D_16ef8. sn F_16efc D_16efc.
      stepb_tk F_16f00 D_16f00 ltac:(pin; rewrite (spp_test d DV); exact E).
        sn F_16f34 D_16f34.
        stepST F_16f38 D_16f38 (Z_to_bv 64 (pix + 12)) (Z_to_bv 64 3) ltac:(sok_in SOK).
        stepfence F_16f3c D_16f3c.
        stepST F_16f40 D_16f40 (Z_to_bv 64 (pix + 20)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_16f44 D_16f44.
        stepST F_16f48 D_16f48 (Z_to_bv 64 (pix + 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
        sn F_16f4c D_16f4c.
        stepLD8 F_16e84 D_16e84 ret. stepLD8 F_16e88 D_16e88 s0v. stepLD8 F_16e8c D_16e8c s1v.
        stepLD8 F_16e90 D_16e90 s2v. stepLD8 F_16e94 D_16e94 s3v. stepLD8 F_16e98 D_16e98 s4v.
        zv F_16e9c D_16e9c (Z_to_bv 64 s).
        stepret F_16ea0 D_16ea0 ret ltac:(bveq).
        apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - stepb_ft F_16ebc D_16ebc ltac:(condZ).
      sn F_16ec0 D_16ec0. sn F_16ec4 D_16ec4. sn F_16ec8 D_16ec8.
      stepb_ft F_176a8 D_176a8 ltac:(condZ). guard8 F_176ac D_176ac AL8.
      stepb_ft F_176b0 D_176b0 ltac:(condZ). stepb_ft F_176b4 D_176b4 ltac:(condZ).
      stepST F_176b8 D_176b8 (Z_to_bv 64 pix) (Z_to_bv 64 w) ltac:(sok_in SOK).
      sn F_176bc D_176bc. stepret F_176c0 D_176c0 (0x16fd0 : word) ltac:(bveq).
      sn F_16ecc D_16ecc. sn F_16ed0 D_16ed0. sn F_16ed4 D_16ed4.
      stepb_ft F_17730 D_17730 ltac:(condZ). guard8 F_17734 D_17734 AL8.
      stepb_ft F_17738 D_17738 ltac:(condZ). stepb_ft F_1773c D_1773c ltac:(condZ).
      stepST F_17740 D_17740 (Z_to_bv 64 (pix + 4)) (Z_to_bv 64 h) ltac:(sok_in SOK).
      sn F_17744 D_17744. stepret F_17748 D_17748 (0x16fdc : word) ltac:(bveq).
      sn F_16ed8 D_16ed8. sn F_16edc D_16edc. sn F_16ee0 D_16ee0.
      stepb_ft F_177b8 D_177b8 ltac:(condZ). stepb_ft F_177bc D_177bc ltac:(condZ). guard8 F_177c0 D_177c0 AL8.
      stepb_ft F_177c4 D_177c4 ltac:(condZ).
      stepST F_177c8 D_177c8 (Z_to_bv 64 (pix + 8)) (Z_to_bv 64 d) ltac:(sok_in SOK).
      sn F_177cc D_177cc. stepret F_177d0 D_177d0 (0x16fe8 : word) ltac:(bveq).
      guard8 F_16ee4 D_16ee4 AL8. stepb_ft F_16ee8 D_16ee8 ltac:(condZ).
      sn F_16eec D_16eec.
      stepST F_16ef0 D_16ef0 (Z_to_bv 64 (pix + 16)) (Z_to_bv 64 wpl) ltac:(sok_in SOK).
      sn F_16ef4 D_16ef4. sn F_16ef8 D_16ef8. sn F_16efc D_16efc.
      stepb_ft F_16f00 D_16f00 ltac:(pin; rewrite (spp_test d DV); exact E).
        sn F_16f04 D_16f04. sn F_16f08 D_16f08.
        stepST F_16f38 D_16f38 (Z_to_bv 64 (pix + 12)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_16f3c D_16f3c.
        stepST F_16f40 D_16f40 (Z_to_bv 64 (pix + 20)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_16f44 D_16f44.
        stepST F_16f48 D_16f48 (Z_to_bv 64 (pix + 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
        sn F_16f4c D_16f4c.
        stepLD8 F_16e84 D_16e84 ret. stepLD8 F_16e88 D_16e88 s0v. stepLD8 F_16e8c D_16e8c s1v.
        stepLD8 F_16e90 D_16e90 s2v. stepLD8 F_16e94 D_16e94 s3v. stepLD8 F_16e98 D_16e98 s4v.
        zv F_16e9c D_16e9c (Z_to_bv 64 s).
        stepret F_16ea0 D_16ea0 ret ltac:(bveq).
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
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h d ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_hdr <= kR)%Z -> (RB_hdr <= bR)%Z ->
  (forall A' m' vm' regs' (pix : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pix -> pix_new C A A' m' pix (pix_hdr w h d) ->
     aroom A' vm' (kR - RK_hdr) (bR - RB_hdr) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x16d34 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw1 Hh1 HOK0 kR bR Hrm Hrk Hrb HK.
  destruct HOK0 as (DV & Hw20 & Hh20 & Hsz0).
  assert (Hw : (1 <= w <= 1000000)%Z) by lia. assert (Hh : (1 <= h <= 1000000)%Z) by lia.
  assert (Hwh : (w * h <= 400000000)%Z) by nia. assert (Hd : (0 <= d < 2 ^ 64)%Z) by (pose proof (dval_range d DV); lia).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
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
    assert (RR2 : forall x, In x [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr regs x) by (unfold cs_rest in RR0; rest_solve).
    assert (P2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (Hszhi : (4 * (wpl_of w d * h) < 2 ^ 64)%Z) by nia.
    assert (SMALL : (67108864 >= 4 * (wpl_of w d * h))%Z) by lia.
    destruct (ph_C al_rom r2 M1 (4 * (wpl_of w d * h)) ltac:(lia) P13 P14) as (r3 & RUN3 & V13 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    assert (RR3 : forall x, In x [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r3 x = getr regs x) by rest_solve.
    assert (V10 : getr r3 10 = Z_to_bv 64 w) by (csr; reflexivity).
    assert (V11 : getr r3 11 = Z_to_bv 64 h) by (csr; reflexivity).
    assert (V12 : getr r3 12 = Z_to_bv 64 d) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (WOK : (20000 >= w)%Z) by lia.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (ph_D al_rom r3 M1 w ltac:(lia) V10 V13) |].
    assert (HOK : (20000 >= h)%Z) by lia.
    (* [comment removed for export] *)
    destruct (ph_E al_rom r3 M1 w h d ltac:(lia) V10 V11 V12 V13) as (r4 & RUN4 & X10 & X11 & X1 & X19 & X9 & X8 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
    assert (X4 : getr r4 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (X20 : getr r4 20 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
    replace (0x2891c : word) with (Z_to_bv 64 0x2891c) by (apply bv_eq; reflexivity).
    apply (W_calloc16_sure C A M1 md r4 1 64 kR bR (Z_to_bv 64 0x16fc0) (s - 48) S CK HW1 X10 X11 ltac:(lia) ltac:(lia) ltac:(lia) Hrm ltac:(unfold RK_hdr in Hrk; lia) ltac:(rewrite (alloc_margin_small (1 * 64)) by lia; unfold RB_hdr in Hrb; lia) ltac:(unfold ROOM_NMAX; lia) X1
             ltac:(red; apply bv_eq; reflexivity) X4 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r5 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hrma.
    replace (Z_to_bv 64 0x16fc0) with (0x16fc0 : word) by (apply bv_eq; reflexivity).
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
      assert (Y9 : getr r5 9 = Z_to_bv 64 h) by (csr; reflexivity).
      assert (Y8 : getr r5 8 = Z_to_bv 64 d) by (csr; reflexivity).
      assert (Y20 : getr r5 20 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
      assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact AL16 | reflexivity]).
      destruct (ph_F al_rom r5 m1 s w h d pix (wpl_of w d) ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ltac:(lia) ltac:(lia) Hret DV ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AL8)
        as (r6 & RUN6 & V2' & V10' & V1' & V8' & V9' & V18' & V19' & V20' & AG6).
      { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
        unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m1 pix pix0 x PX0 ltac:(lia) E). }
      { exact Z1. } { exact Z2. } { exact Z3. } { exact Z4. } { exact Z5. } { exact Z6. }
      { exact Y2. } { exact Hres. } { exact Y19. } { exact Y9. } { exact Y8. } { exact Y20. }
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

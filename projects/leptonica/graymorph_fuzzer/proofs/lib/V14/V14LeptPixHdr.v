(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptStderr V14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14CL7a.
Import V14CL7a.V14LeptErr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14_code_15000_16000 V14_code_16000_17000 V14_code_29000_2a000.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixHdr.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V14Pins}.
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
      msteps SEGS (mkst regs (0x15984 : word) m rom) (mkst regs' (0x159c0 : word) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 Hd DV SOK H2 H1 H10 H11 H12. pose proof (dval_range d DV). unfold FR6.
    eexists. split.
    - zv F_15888 D_15888 (Z_to_bv 64 (s - 48)).
      stepST F_1588c D_1588c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15890 D_15890 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15894 D_15894 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_15898 D_15898 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_1589c D_1589c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_158a0 D_158a0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      sn F_158a4 D_158a4.
      stepb_ft F_158a8 D_158a8 ltac:(condZ).
      sn F_158ac D_158ac. sn F_158b0 D_158b0. sn F_158b4 D_158b4.
      sn F_158b8 D_158b8. sn F_158bc D_158bc.
      stepb_ft F_158c0 D_158c0 ltac:(pin; apply depth_test_ok; exact DV).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Abad : forall regs m (s w h d : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 64)%Z -> ~ dval d ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x15984 : word) m rom) (mkst regs' (0x15af8 : word) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 Hd ND SOK H2 H1 H10 H11 H12. unfold FR6.
    destruct (Z_lt_ge_dec 32 d) as [Hbig|Hsmall].
    - eexists. split.
      + zv F_15888 D_15888 (Z_to_bv 64 (s - 48)).
        stepST F_1588c D_1588c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
        stepST F_15890 D_15890 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
        stepST F_15894 D_15894 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
        stepST F_15898 D_15898 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
        stepST F_1589c D_1589c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
        stepST F_158a0 D_158a0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
        sn F_158a4 D_158a4.
        stepb_tk F_158a8 D_158a8 ltac:(condZ).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + zv F_15888 D_15888 (Z_to_bv 64 (s - 48)).
        stepST F_1588c D_1588c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
        stepST F_15890 D_15890 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
        stepST F_15894 D_15894 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
        stepST F_15898 D_15898 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
        stepST F_1589c D_1589c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
        stepST F_158a0 D_158a0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
        sn F_158a4 D_158a4.
        stepb_ft F_158a8 D_158a8 ltac:(condZ).
        sn F_158ac D_158ac. sn F_158b0 D_158b0. sn F_158b4 D_158b4.
        sn F_158b8 D_158b8. sn F_158bc D_158bc.
        stepb_tk F_158c0 D_158c0 ltac:(pin; apply depth_test_bad; [lia | exact ND]).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_B : forall regs m (s w h d : Z),
    (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> dval d ->
    getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x159c0 : word) m rom) (mkst regs' (0x15b48 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (4 * (wpl_of w d * h)) /\ getr regs' 14 = Z_to_bv 64 0x4000001 /\ getr regs' 20 = Z_to_bv 64 (wpl_of w d)
      /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [20; 13; 14]%list) regs regs'.
  Proof.
    intros regs m s w h d Hw Hh Hwh DV H10 H11 H12. pose proof (dval_range d DV). pose proof (wpl_of_range w d Hw DV) as Hwpl.
    assert (Hdw : (0 <= d * w <= 32 * 1000000)%Z) by nia.
    assert (Hsz : (4 * (wpl_of w d * h) < 2 ^ 31)%Z).
    { unfold wpl_of in *. assert ((w * d + 31) / 32 * 8 <= w * d + 31)%Z by (pose proof (Z.mul_div_le (w * d + 31) 32 ltac:(lia)); lia). nia. }
    eexists. split.
    - stepb_ft F_158c4 D_158c4 ltac:(condZ).
      stepb_ft F_158c8 D_158c8 ltac:(condZ).
      zv F_158cc D_158cc (Z_to_bv 64 (d * w)).
      sn F_158d0 D_158d0. sn F_158d4 D_158d4.
      stepb_tk F_158d8 D_158d8 ltac:(condZ).
      zv F_15988 D_15988 (Z_to_bv 64 (d * w + 31)).
      sn F_1598c D_1598c. fixv (Z_to_bv 64 (wpl_of w d)) ltac:(unfold wpl_of; rewrite zbv_srli by lia; f_equal; change (2 ^ 5)%Z with 32%Z; f_equal; lia).
      zv F_15990 D_15990 (Z_to_bv 64 (wpl_of w d * h)).
      stepiv F_15994 D_15994 (Z_to_bv 64 (4 * (wpl_of w d * h))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_15998 D_15998. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srli by lia; f_equal; apply Z.div_small; lia).
      stepb_tk F_1599c D_1599c ltac:(condZ).
      sn F_15a44 D_15a44. sn F_15a48 D_15a48.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_C : forall regs m (sz : Z),
    (0 <= sz <= 67108864)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    exists regs',
      msteps SEGS (mkst regs (0x15b48 : word) m rom) (mkst regs' (0x15b7c : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 20001 /\ regs_agree (fun r => In r [13]%list) regs regs'.
  Proof.
    intros regs m sz Hsz H13 H14. eexists. split.
    - stepb_tk F_15a4c D_15a4c ltac:(condZ). sn F_15a78 D_15a78. sn F_15a7c D_15a7c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Cbad : forall regs m (sz : Z),
    (67108864 < sz < 2 ^ 64)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x15b48 : word) m rom) (mkst regs' (0x154b0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x1041e /\ getr regs' 11 = Z_to_bv 64 0x1096a /\ getr regs' 1 = Z_to_bv 64 0x15bd4
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m sz Hsz H13 H14 Rg Rs. eexists. split.
    - stepb_ft F_15a4c D_15a4c ltac:(condZ).
      sn F_15a50 D_15a50.
      stepLD F_15a54 D_15a54 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_15a58 D_15a58 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15a5c D_15a5c.
      stepb_ft F_15a60 D_15a60 ltac:(condZ).
      sn F_15a64 D_15a64. sn F_15a68 D_15a68. sn F_15a6c D_15a6c. sn F_15a70 D_15a70. sn F_15a74 D_15a74.
      sn F_15ad4 D_15ad4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ph_D : forall regs m (w : Z),
    (1 <= w <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    msteps SEGS (mkst regs (0x15b7c : word) m rom) (mkst regs (0x15ba8 : word) m rom).
  Proof. intros regs m w Hw H10 H13. stepb_tk F_15a80 D_15a80 ltac:(condZ). apply mst_refl. Qed.

  Lemma ph_Dbad : forall regs m (w : Z),
    (20000 < w < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x15b7c : word) m rom) (mkst regs' (0x154b0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x111ab /\ getr regs' 11 = Z_to_bv 64 0x1096a /\ getr regs' 1 = Z_to_bv 64 0x15bd4
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m w Hw H10 H13 Rg Rs. eexists. split.
    - stepb_ft F_15a80 D_15a80 ltac:(condZ).
      sn F_15a84 D_15a84.
      stepLD F_15a88 D_15a88 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_15a8c D_15a8c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15a90 D_15a90.
      stepb_ft F_15a94 D_15a94 ltac:(condZ).
      sn F_15a98 D_15a98. sn F_15a9c D_15a9c. sn F_15aa0 D_15aa0. sn F_15aa4 D_15aa4. sn F_15aa8 D_15aa8.
      sn F_15ad4 D_15ad4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_E : forall regs m (w h d : Z),
    (1 <= h <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d -> getr regs 13 = Z_to_bv 64 20001 ->
    exists regs',
      msteps SEGS (mkst regs (0x15ba8 : word) m rom) (mkst regs' (0x2a0e8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 64 /\ getr regs' 1 = Z_to_bv 64 0x15c10
      /\ getr regs' 19 = Z_to_bv 64 w /\ getr regs' 9 = Z_to_bv 64 h /\ getr regs' 8 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 19]%list) regs regs'.
  Proof.
    intros regs m w h d Hh H10 H11 H12 H13. eexists. split.
    - stepb_tk F_15aac D_15aac ltac:(condZ).
      sn F_15afc D_15afc. sn F_15b00 D_15b00. sn F_15b04 D_15b04. sn F_15b08 D_15b08. sn F_15b0c D_15b0c.
      sn F_15b10 D_15b10.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ph_Ebad : forall regs m (h : Z),
    (20000 < h < 2 ^ 64)%Z -> getr regs 11 = Z_to_bv 64 h -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x15ba8 : word) m rom) (mkst regs' (0x154b0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10d2c /\ getr regs' 11 = Z_to_bv 64 0x1096a /\ getr regs' 1 = Z_to_bv 64 0x15bd4
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m h Hh H11 H13 Rg Rs. eexists. split.
    - stepb_ft F_15aac D_15aac ltac:(condZ).
      sn F_15ab0 D_15ab0.
      stepLD F_15ab4 D_15ab4 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_15ab8 D_15ab8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15abc D_15abc.
      stepb_ft F_15ac0 D_15ac0 ltac:(condZ).
      sn F_15ac4 D_15ac4. sn F_15ac8 D_15ac8. sn F_15acc D_15acc. sn F_15ad0 D_15ad0.
      sn F_15ad4 D_15ad4.
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
      msteps SEGS (mkst regs (0x15bd4 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v Hs Hs64 Hret R8 R16 R24 R32 R40 R48 H2. eexists. split.
    - sn F_15ad8 D_15ad8.
      stepLD8 F_15adc D_15adc ret. stepLD8 F_15ae0 D_15ae0 s0v. stepLD8 F_15ae4 D_15ae4 s1v.
      stepLD8 F_15ae8 D_15ae8 s2v. stepLD8 F_15aec D_15aec s3v. stepLD8 F_15af0 D_15af0 s4v.
      zv F_15af4 D_15af4 (Z_to_bv 64 s).
      stepret F_15af8 D_15af8 ret ltac:(bveq).
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
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 0x1096a ->
    exists regs',
      msteps SEGS (mkst regs (0x15b1c : word) m rom) (mkst regs' (0x1554c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x1096a
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s msg ret s0v s1v s2v s3v s4v Hs Hs64 R8 R16 R24 R32 R40 R48 H2 H10 H11. eexists. split.
    - sn F_15a20 D_15a20.
      stepLD8 F_15a24 D_15a24 ret. stepLD8 F_15a28 D_15a28 s0v. stepLD8 F_15a2c D_15a2c s1v.
      stepLD8 F_15a30 D_15a30 s2v. stepLD8 F_15a34 D_15a34 s3v. stepLD8 F_15a38 D_15a38 s4v.
      zv F_15a3c D_15a3c (Z_to_bv 64 s).
      sn F_15a40 D_15a40.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_G : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x15af8 : word) m rom) (mkst regs' (0x15b1c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10566 /\ getr regs' 11 = Z_to_bv 64 0x1096a
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m Rg Rs. eexists. split.
    - sn F_159fc D_159fc.
      stepLD F_15a00 D_15a00 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_15a04 D_15a04 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15a08 D_15a08.
      stepb_ft F_15a0c D_15a0c ltac:(condZ).
      sn F_15a10 D_15a10. sn F_15a14 D_15a14. sn F_15a18 D_15a18. sn F_15a1c D_15a1c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Fbad : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x15c10 : word) m rom) (mkst regs' (0x15b1c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x104bd /\ getr regs' 11 = Z_to_bv 64 0x1096a
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_15b14 D_15b14 ltac:(condZ).
      sn F_15b64 D_15b64.
      stepLD F_15b68 D_15b68 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_15b6c D_15b6c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15b70 D_15b70.
      stepb_ft F_15b74 D_15b74 ltac:(condZ).
      sn F_15b78 D_15b78. sn F_15b7c D_15b7c. sn F_15b80 D_15b80. sn F_15b84 D_15b84. sn F_15b88 D_15b88.
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
      msteps SEGS (mkst regs (0x15c10 : word) m rom)
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
    - stepb_ft F_15b14 D_15b14 ltac:(condZ).
      sn F_15b18 D_15b18. sn F_15b1c D_15b1c. sn F_15b20 D_15b20.
      (* [comment removed for export] *)
      stepb_ft F_164ac D_164ac ltac:(condZ). guard8 F_164b0 D_164b0 AL8.
      stepb_ft F_164b4 D_164b4 ltac:(condZ). stepb_ft F_164b8 D_164b8 ltac:(condZ).
      stepST F_164bc D_164bc (Z_to_bv 64 pix) (Z_to_bv 64 w) ltac:(sok_in SOK).
      sn F_164c0 D_164c0. stepret F_164c4 D_164c4 (0x15c20 : word) ltac:(bveq).
      sn F_15b24 D_15b24. sn F_15b28 D_15b28. sn F_15b2c D_15b2c.
      (* [comment removed for export] *)
      stepb_ft F_16534 D_16534 ltac:(condZ). guard8 F_16538 D_16538 AL8.
      stepb_ft F_1653c D_1653c ltac:(condZ). stepb_ft F_16540 D_16540 ltac:(condZ).
      stepST F_16544 D_16544 (Z_to_bv 64 (pix + 4)) (Z_to_bv 64 h) ltac:(sok_in SOK).
      sn F_16548 D_16548. stepret F_1654c D_1654c (0x15c2c : word) ltac:(bveq).
      sn F_15b30 D_15b30. sn F_15b34 D_15b34. sn F_15b38 D_15b38.
      (* [comment removed for export] *)
      stepb_ft F_165bc D_165bc ltac:(condZ). stepb_ft F_165c0 D_165c0 ltac:(condZ). guard8 F_165c4 D_165c4 AL8.
      stepb_ft F_165c8 D_165c8 ltac:(condZ).
      stepST F_165cc D_165cc (Z_to_bv 64 (pix + 8)) (Z_to_bv 64 d) ltac:(sok_in SOK).
      sn F_165d0 D_165d0. stepret F_165d4 D_165d4 (0x15c38 : word) ltac:(bveq).
      guard8 F_15b3c D_15b3c AL8. stepb_ft F_15b40 D_15b40 ltac:(condZ).
      sn F_15b44 D_15b44.
      stepST F_15b48 D_15b48 (Z_to_bv 64 (pix + 16)) (Z_to_bv 64 wpl) ltac:(sok_in SOK).
      sn F_15b4c D_15b4c. sn F_15b50 D_15b50. sn F_15b54 D_15b54.
      stepb_tk F_15b58 D_15b58 ltac:(pin; rewrite (spp_test d DV); exact E).
        sn F_15b8c D_15b8c.
        stepST F_15b90 D_15b90 (Z_to_bv 64 (pix + 12)) (Z_to_bv 64 3) ltac:(sok_in SOK).
        stepfence F_15b94 D_15b94.
        stepST F_15b98 D_15b98 (Z_to_bv 64 (pix + 20)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_15b9c D_15b9c.
        stepST F_15ba0 D_15ba0 (Z_to_bv 64 (pix + 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
        sn F_15ba4 D_15ba4.
        stepLD8 F_15adc D_15adc ret. stepLD8 F_15ae0 D_15ae0 s0v. stepLD8 F_15ae4 D_15ae4 s1v.
        stepLD8 F_15ae8 D_15ae8 s2v. stepLD8 F_15aec D_15aec s3v. stepLD8 F_15af0 D_15af0 s4v.
        zv F_15af4 D_15af4 (Z_to_bv 64 s).
        stepret F_15af8 D_15af8 ret ltac:(bveq).
        apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - stepb_ft F_15b14 D_15b14 ltac:(condZ).
      sn F_15b18 D_15b18. sn F_15b1c D_15b1c. sn F_15b20 D_15b20.
      stepb_ft F_164ac D_164ac ltac:(condZ). guard8 F_164b0 D_164b0 AL8.
      stepb_ft F_164b4 D_164b4 ltac:(condZ). stepb_ft F_164b8 D_164b8 ltac:(condZ).
      stepST F_164bc D_164bc (Z_to_bv 64 pix) (Z_to_bv 64 w) ltac:(sok_in SOK).
      sn F_164c0 D_164c0. stepret F_164c4 D_164c4 (0x15c20 : word) ltac:(bveq).
      sn F_15b24 D_15b24. sn F_15b28 D_15b28. sn F_15b2c D_15b2c.
      stepb_ft F_16534 D_16534 ltac:(condZ). guard8 F_16538 D_16538 AL8.
      stepb_ft F_1653c D_1653c ltac:(condZ). stepb_ft F_16540 D_16540 ltac:(condZ).
      stepST F_16544 D_16544 (Z_to_bv 64 (pix + 4)) (Z_to_bv 64 h) ltac:(sok_in SOK).
      sn F_16548 D_16548. stepret F_1654c D_1654c (0x15c2c : word) ltac:(bveq).
      sn F_15b30 D_15b30. sn F_15b34 D_15b34. sn F_15b38 D_15b38.
      stepb_ft F_165bc D_165bc ltac:(condZ). stepb_ft F_165c0 D_165c0 ltac:(condZ). guard8 F_165c4 D_165c4 AL8.
      stepb_ft F_165c8 D_165c8 ltac:(condZ).
      stepST F_165cc D_165cc (Z_to_bv 64 (pix + 8)) (Z_to_bv 64 d) ltac:(sok_in SOK).
      sn F_165d0 D_165d0. stepret F_165d4 D_165d4 (0x15c38 : word) ltac:(bveq).
      guard8 F_15b3c D_15b3c AL8. stepb_ft F_15b40 D_15b40 ltac:(condZ).
      sn F_15b44 D_15b44.
      stepST F_15b48 D_15b48 (Z_to_bv 64 (pix + 16)) (Z_to_bv 64 wpl) ltac:(sok_in SOK).
      sn F_15b4c D_15b4c. sn F_15b50 D_15b50. sn F_15b54 D_15b54.
      stepb_ft F_15b58 D_15b58 ltac:(pin; rewrite (spp_test d DV); exact E).
        sn F_15b5c D_15b5c. sn F_15b60 D_15b60.
        stepST F_15b90 D_15b90 (Z_to_bv 64 (pix + 12)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_15b94 D_15b94.
        stepST F_15b98 D_15b98 (Z_to_bv 64 (pix + 20)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_15b9c D_15b9c.
        stepST F_15ba0 D_15ba0 (Z_to_bv 64 (pix + 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
        sn F_15ba4 D_15ba4.
        stepLD8 F_15adc D_15adc ret. stepLD8 F_15ae0 D_15ae0 s0v. stepLD8 F_15ae4 D_15ae4 s1v.
        stepLD8 F_15ae8 D_15ae8 s2v. stepLD8 F_15aec D_15aec s3v. stepLD8 F_15af0 D_15af0 s4v.
        zv F_15af4 D_15af4 (Z_to_bv 64 s).
        stepret F_15af8 D_15af8 ret ltac:(bveq).
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

Lemma str_pixCreateHeader : str16 0x1096a 15. Proof. str16_tac. Qed.
Lemma str_msg_64mb : str16 0x1041e 47. Proof. str16_tac. Qed.
Lemma str_msg_w20k : str16 0x111ab 51. Proof. str16_tac. Qed.
Lemma str_msg_h20k : str16 0x10d2c 52. Proof. str16_tac. Qed.
Lemma str_msg_depth : str16 0x10566 38. Proof. str16_tac. Qed.
Lemma str_msg_pixd : str16 0x104bd 13. Proof. str16_tac. Qed.

Definition hdr_ok (w h d : Z) : Prop := dval d /\ (w <= 20000)%Z /\ (h <= 20000)%Z /\ (4 * (wpl_of w d * h) <= 67108864)%Z.
Definition pix_hdr (w h d : Z) : pixv := PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 0 0.
Definition pix_new (C : lctx) (A A' : AS) (m' : word -> option byte) (pix : Z) (v : pixv) : Prop :=
  (4096 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (pix mod 16 = 0)%Z /\
  live A (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 pix) = None /\ live A' (Z_to_bv 64 pix) = Some 64%Z /\
  (forall q, q <> Z_to_bv 64 pix -> live A' q = live A q) /\ PIXat m' pix v.

(* [comment removed for export] *)
Lemma ph_lerror_W : forall C A m M md regs r (s fmt : Z) kf (ret : word) (S : TSet),
  Cok C -> W C A M md -> POSTM C A s m M ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  cells6 M s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 1 = Z_to_bv 64 0x15bd4 -> getr r 10 = Z_to_bv 64 fmt -> getr r 11 = Z_to_bv 64 0x1096a ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x) ->
  In fmt (SSP.ls_fmts1 LU16) -> str16 fmt kf ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ False)) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (0x154b0 : word) M al_rom) md) S.
Proof.
  intros C A m M md regs r s fmt kf ret S CK HW PM Hs16 Hlo Hhi Hret CE R2 R1 R10 R11 RR Hin Sf HK H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  apply (lept_stderr1_W C A M md r (s - 48) fmt 0x1096a kf 15 (Z_to_bv 64 0x15bd4) S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) R1 ltac:(red; apply bv_eq; reflexivity)
           R10 R11 Hin Sf str_pixCreateHeader).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  replace (Z_to_bv 64 0x15bd4) with (0x15bd4 : word) by (apply bv_eq; reflexivity).
  assert (PM2 : POSTM C A s m m2).
  { eapply POSTM_trans; [exact PM|]. eapply (POSTM_range C A M md m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia]. }
  destruct (cells6_frm C (s - 48) M m2 s _ _ _ _ _ _ CK ltac:(intros a _ _ _ _ H5; apply OUT2; unfold scratch in H5; lia) ltac:(lia) ltac:(lia) ltac:(lia) CE)
    as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  destruct (ph_R0 al_rom r2 m2 s ret _ _ _ _ _ ltac:(lia) ltac:(lia) Hret Q1 Q2 Q3 Q4 Q5 Q6 ltac:(csr; reflexivity))
    as (r3 & RUN3 & V2 & V10 & V1 & V8 & V9 & V18 & V19 & V20 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  rewrite <- (with_vmmaps_same md). apply (HK A m2 (m_vmmaps md) r3).
  - rewrite with_vmmaps_same. exact HW2.
  - apply cs_kept_of_rest; [rewrite V2, H2; reflexivity | exact V8 | exact V9 |].
    rest_solve.
  - exact PM2.
  - left. split; [exact V10 | intros q; reflexivity].
  - room_tac.
Qed.

(* [comment removed for export] *)
Lemma ph_eptr_W : forall C A A1 m M md (vm0 : VmMaps) regs r (s msg : Z) km (ret : word) (S : TSet),
  Cok C -> W C A1 M md -> POSTM C A s m M -> (forall q, live A1 q = live A q) ->
  roomtr A vm0 A1 (m_vmmaps md) RK_hdr RB_hdr ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  cells6 M s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 10 = Z_to_bv 64 msg -> getr r 11 = Z_to_bv 64 0x1096a ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x) -> str16 msg km ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ False)) ->
     roomtr A vm0 A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (0x15b1c : word) M al_rom) md) S.
Proof.
  intros C A A1 m M md vm0 regs r s msg km ret S CK HW PM LQ RT0 Hs16 Hlo Hhi Hret CE R2 R10 R11 RR Sm HK H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  destruct CE as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  destruct (ph_H al_rom r M s msg ret _ _ _ _ _ ltac:(lia) ltac:(lia) Q1 Q2 Q3 Q4 Q5 Q6 R2 R10 R11)
    as (r1 & RUN1 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & V20 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (returnErrorPtr_W C A1 M md r1 s msg 0x1096a km 15 ret (Z_to_bv 64 0) S CK HW V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           V10 V11 V12 Sm str_pixCreateHeader).
  intros m2 r2 HW2 OUT2 GR2 CS2 A10. unfold LSF in OUT2.
  rewrite <- (with_vmmaps_same md). apply (HK A1 m2 (m_vmmaps md) r2).
  - rewrite with_vmmaps_same. exact HW2.
  - apply cs_kept_of_rest; [csr; reflexivity | csr; reflexivity | csr; reflexivity |]. rest_solve.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LQ|].
    eapply (POSTM_range C A1 M md m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia].
  - left. split; [exact A10 | exact LQ].
  - exact RT0.
Qed.

Theorem pixCreateHeader_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x44140 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ (hdr_ok w h d /\ pix_new C A A' m' pix (pix_hdr w h d)))) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15984 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  (* [comment removed for export] *)
  assert (HK0 : forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q) \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ False)) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S).
  { intros A' m' vm' regs' X1 X2 X3 X4 X5. apply (HK A' m' vm' regs' X1 X2 X3); [| exact X5]. destruct X4 as [L|(pix & _ & [])]. left; exact L. }
  assert (RR0 : forall x, In x cs_rest -> getr regs x = getr regs x) by (intros; reflexivity).
  destruct (dval_dec d) as [DV|ND].
  all: cycle 1.
  - (* [comment removed for export] *)
    destruct (ph_Abad al_rom regs m s w h d ret ltac:(lia) ltac:(lia) Hd ND SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (WP1 : W C A (FR6 m s ret regs) md /\ POSTM C A s m (FR6 m s ret regs)) by (unfold FR6; wp_win CK).
    destruct WP1 as [HW1 PM1].
    destruct (ph_G al_rom r1 (FR6 m s ret regs) (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r2 & RUN2 & P10 & P11 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    apply (ph_eptr_W C A A m (FR6 m s ret regs) md (m_vmmaps md) regs r2 s 0x10566 38 ret S CK HW1 PM1 ltac:(intros; reflexivity) ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret
             (cells6_FR6 m s ret regs ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity) P10 P11 ltac:(rest_solve)
             str_msg_depth HK0 H2).
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
    destruct (Z_lt_ge_dec 67108864 (4 * (wpl_of w d * h))) as [BIG|SMALL].
    { (* [comment removed for export] *)
      destruct (ph_Cbad al_rom r2 M1 (4 * (wpl_of w d * h)) ltac:(lia) P13 P14 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r3 & RUN3 & V10 & V11 & V1 & AG3).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
      apply (ph_lerror_W C A m M1 md regs r3 s 0x1041e 47 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
               ltac:(csr; reflexivity) V1 V10 V11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_64mb HK0 H2). }
    destruct (ph_C al_rom r2 M1 (4 * (wpl_of w d * h)) ltac:(lia) P13 P14) as (r3 & RUN3 & V13 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    assert (RR3 : forall x, In x [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r3 x = getr regs x) by rest_solve.
    assert (V10 : getr r3 10 = Z_to_bv 64 w) by (csr; reflexivity).
    assert (V11 : getr r3 11 = Z_to_bv 64 h) by (csr; reflexivity).
    assert (V12 : getr r3 12 = Z_to_bv 64 d) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    destruct (Z_lt_ge_dec 20000 w) as [WBIG|WOK].
    { (* [comment removed for export] *)
      destruct (ph_Dbad al_rom r3 M1 w ltac:(lia) V10 V13 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r4 & RUN4 & X10 & X11 & X1 & AG4).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
      apply (ph_lerror_W C A m M1 md regs r4 s 0x111ab 51 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
               ltac:(csr; reflexivity) X1 X10 X11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_w20k HK0 H2). }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (ph_D al_rom r3 M1 w ltac:(lia) V10 V13) |].
    destruct (Z_lt_ge_dec 20000 h) as [HBIG|HOK].
    { (* [comment removed for export] *)
      destruct (ph_Ebad al_rom r3 M1 h ltac:(lia) V11 V13 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r4 & RUN4 & X10 & X11 & X1 & AG4).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
      apply (ph_lerror_W C A m M1 md regs r4 s 0x10d2c 52 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
               ltac:(csr; reflexivity) X1 X10 X11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_h20k HK0 H2). }
    (* [comment removed for export] *)
    destruct (ph_E al_rom r3 M1 w h d ltac:(lia) V10 V11 V12 V13) as (r4 & RUN4 & X10 & X11 & X1 & X19 & X9 & X8 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
    assert (X4 : getr r4 4 = Z_to_bv 64 0x44140) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (X20 : getr r4 20 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
    replace (0x2a0e8 : word) with (Z_to_bv 64 0x2a0e8) by (apply bv_eq; reflexivity).
    apply (W_calloc16 C A M1 md r4 1 64 (Z_to_bv 64 0x15c10) (s - 48) S CK HW1 X10 X11 ltac:(lia) ltac:(lia) ltac:(lia) X1
             ltac:(red; apply bv_eq; reflexivity) X4 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r5 res HWa Hres CSa OUTa PMa HRTa.
    replace (Z_to_bv 64 0x15c10) with (0x15c10 : word) by (apply bv_eq; reflexivity).
    assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
    pose proof (cells6_frm C (s - 48) M1 m1 s _ _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
    destruct OUTa as [[Hres0 LIVEQ] | (Hnz & L0 & L1 & L00 & LEQ & ZERO & AL16 & TOP)].
    + (* [comment removed for export] *)
      rewrite Hres0 in Hres.
      destruct (ph_Fbad al_rom r5 m1 (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) Hres) as (r6 & RUN6 & Y10 & Y11 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      apply (ph_eptr_W C A A1 m m1 (with_vmmaps vm1 md) (m_vmmaps md) regs r6 s 0x104bd 13 ret S CK HWa PMa' LIVEQ ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret CE2
               ltac:(csr; reflexivity) Y10 Y11 ltac:(rest_solve) str_msg_pixd).
      * intros A' m' vm' regs' HW' CS' PM' OUT' RT'. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW'.
        exact (HK0 A' m' vm' regs' HW' CS' PM' OUT' RT').
      * exact H2.
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
      apply (HK A1 M7 vm1 r6 HW7).
      * apply cs_kept_of_rest; [csr; reflexivity | csr; reflexivity | csr; reflexivity |]. rest_solve.
      * exact PM7.
      * right. exists pix. split; [exact V10'|]. split; [unfold hdr_ok; repeat split; try assumption; lia|].
        unfold pix_new. do 7 (split; [first [assumption | lia] |]). exact PX7.
      * room_tac.
Qed.



End PixHdr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

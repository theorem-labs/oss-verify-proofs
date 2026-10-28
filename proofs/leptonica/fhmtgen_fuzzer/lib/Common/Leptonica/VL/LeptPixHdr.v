(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_237d4_24000 RCodeVL_24000_25000.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.VL Require Import LeptStderr LeptBase LeptErr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac zval ::= rl_zval.      (* [comment removed for export] *)
#[local] Ltac condZ ::= rl_condZ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixHdr.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC} {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvVL RLOC} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLG} {P16 : PinsG}.
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
      msteps SEGS (mkst regs (rl dVL_239c0 0x239c0) m rom) (mkst regs' (rl dVL_239c0 0x239fc) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 Hd DV SOK H2 H1 H10 H11 H12. pose proof (dval_range d DV). unfold FR6.
    eexists. split.
    - zv F_239c0 D_239c0 (Z_to_bv 64 (s - 48)).
      stepST F_239c4 D_239c4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_239c8 D_239c8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_239cc D_239cc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_239d0 D_239d0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_239d4 D_239d4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_239d8 D_239d8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      sn F_239dc D_239dc.
      stepb_ft F_239e0 D_239e0 ltac:(condZ).
      sn F_239e4 D_239e4. sn F_239e8 D_239e8. sn F_239ec D_239ec.
      sn F_239f0 D_239f0. sn F_239f4 D_239f4.
      stepb_ft F_239f8 D_239f8 ltac:(pin; apply depth_test_ok; exact DV).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Abad : forall regs m (s w h d : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 64)%Z -> ~ dval d ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x239c0) m rom) (mkst regs' (rl dVL_239c0 0x23b34) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 Hd ND SOK H2 H1 H10 H11 H12. unfold FR6.
    destruct (Z_lt_ge_dec 32 d) as [Hbig|Hsmall].
    - eexists. split.
      + zv F_239c0 D_239c0 (Z_to_bv 64 (s - 48)).
        stepST F_239c4 D_239c4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
        stepST F_239c8 D_239c8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
        stepST F_239cc D_239cc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
        stepST F_239d0 D_239d0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
        stepST F_239d4 D_239d4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
        stepST F_239d8 D_239d8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
        sn F_239dc D_239dc.
        stepb_tk F_239e0 D_239e0 ltac:(condZ).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + zv F_239c0 D_239c0 (Z_to_bv 64 (s - 48)).
        stepST F_239c4 D_239c4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
        stepST F_239c8 D_239c8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
        stepST F_239cc D_239cc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
        stepST F_239d0 D_239d0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
        stepST F_239d4 D_239d4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
        stepST F_239d8 D_239d8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
        sn F_239dc D_239dc.
        stepb_ft F_239e0 D_239e0 ltac:(condZ).
        sn F_239e4 D_239e4. sn F_239e8 D_239e8. sn F_239ec D_239ec.
        sn F_239f0 D_239f0. sn F_239f4 D_239f4.
        stepb_tk F_239f8 D_239f8 ltac:(pin; apply depth_test_bad; [lia | exact ND]).
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_B : forall regs m (s w h d : Z),
    (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> dval d ->
    getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x239fc) m rom) (mkst regs' (rl dVL_239c0 0x23b84) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (4 * (wpl_of w d * h)) /\ getr regs' 14 = Z_to_bv 64 0x4000001 /\ getr regs' 20 = Z_to_bv 64 (wpl_of w d)
      /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [20; 13; 14]%list) regs regs'.
  Proof.
    intros regs m s w h d Hw Hh Hwh DV H10 H11 H12. pose proof (dval_range d DV). pose proof (wpl_of_range w d Hw DV) as Hwpl.
    assert (Hdw : (0 <= d * w <= 32 * 1000000)%Z) by nia.
    assert (Hsz : (4 * (wpl_of w d * h) < 2 ^ 31)%Z).
    { unfold wpl_of in *. assert ((w * d + 31) / 32 * 8 <= w * d + 31)%Z by (pose proof (Z.mul_div_le (w * d + 31) 32 ltac:(lia)); lia). nia. }
    eexists. split.
    - stepb_ft F_239fc D_239fc ltac:(condZ).
      stepb_ft F_23a00 D_23a00 ltac:(condZ).
      zv F_23a04 D_23a04 (Z_to_bv 64 (d * w)).
      sn F_23a08 D_23a08. sn F_23a0c D_23a0c.
      stepb_tk F_23a10 D_23a10 ltac:(condZ).
      zv F_23ac0 D_23ac0 (Z_to_bv 64 (d * w + 31)).
      sn F_23ac4 D_23ac4. fixv (Z_to_bv 64 (wpl_of w d)) ltac:(unfold wpl_of; rewrite zbv_srli by lia; f_equal; change (2 ^ 5)%Z with 32%Z; f_equal; lia).
      zv F_23ac8 D_23ac8 (Z_to_bv 64 (wpl_of w d * h)).
      stepiv F_23acc D_23acc (Z_to_bv 64 (4 * (wpl_of w d * h))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_23ad0 D_23ad0. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srli by lia; f_equal; apply Z.div_small; lia).
      stepb_tk F_23ad4 D_23ad4 ltac:(condZ).
      sn F_23b7c D_23b7c. sn F_23b80 D_23b80.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_C : forall regs m (sz : Z),
    (0 <= sz <= 67108864)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x23b84) m rom) (mkst regs' (rl dVL_239c0 0x23bb8) m rom)
      /\ getr regs' 13 = Z_to_bv 64 20001 /\ regs_agree (fun r => In r [13]%list) regs regs'.
  Proof.
    intros regs m sz Hsz H13 H14. eexists. split.
    - stepb_tk F_23b84 D_23b84 ltac:(condZ). sn F_23bb0 D_23bb0. sn F_23bb4 D_23bb4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Cbad : forall regs m (sz : Z),
    (67108864 < sz < 2 ^ 64)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x23b84) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dVLS_1035b 0x1035b /\ getr regs' 11 = rl dVLS_10553 0x10553 /\ getr regs' 1 = rl dVL_239c0 0x23c10
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVLS_1035b :: dVLS_10553 :: nil).
    intros regs m sz Hsz H13 H14 Rg Rs. eexists. split.
    - stepb_ft F_23b84 D_23b84 ltac:(condZ).
      sn F_23b88 D_23b88.
      stepLD F_23b8c D_23b8c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_23b90 D_23b90 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_23b94 D_23b94.
      stepb_ft F_23b98 D_23b98 ltac:(condZ).
      sn F_23b9c D_23b9c. sn F_23ba0 D_23ba0. sn F_23ba4 D_23ba4. sn F_23ba8 D_23ba8. sn F_23bac D_23bac.
      sn F_23c0c D_23c0c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ph_D : forall regs m (w : Z),
    (1 <= w <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    msteps SEGS (mkst regs (rl dVL_239c0 0x23bb8) m rom) (mkst regs (rl dVL_239c0 0x23be4) m rom).
  Proof. intros regs m w Hw H10 H13. stepb_tk F_23bb8 D_23bb8 ltac:(condZ). apply mst_refl. Qed.

  Lemma ph_Dbad : forall regs m (w : Z),
    (20000 < w < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x23bb8) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dVLS_10991 0x10991 /\ getr regs' 11 = rl dVLS_10553 0x10553 /\ getr regs' 1 = rl dVL_239c0 0x23c10
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVLS_10553 :: dVLS_10991 :: nil).
    intros regs m w Hw H10 H13 Rg Rs. eexists. split.
    - stepb_ft F_23bb8 D_23bb8 ltac:(condZ).
      sn F_23bbc D_23bbc.
      stepLD F_23bc0 D_23bc0 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_23bc4 D_23bc4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_23bc8 D_23bc8.
      stepb_ft F_23bcc D_23bcc ltac:(condZ).
      sn F_23bd0 D_23bd0. sn F_23bd4 D_23bd4. sn F_23bd8 D_23bd8. sn F_23bdc D_23bdc. sn F_23be0 D_23be0.
      sn F_23c0c D_23c0c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_E : forall regs m (w h d : Z),
    (1 <= h <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d -> getr regs 13 = Z_to_bv 64 20001 ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x23be4) m rom) (mkst regs' (rl dF_15a00 0x15a00) m rom)
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 64 /\ getr regs' 1 = rl dVL_239c0 0x23c4c
      /\ getr regs' 19 = Z_to_bv 64 w /\ getr regs' 9 = Z_to_bv 64 h /\ getr regs' 8 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 19]%list) regs regs'.
  Proof.
    intros regs m w h d Hh H10 H11 H12 H13. eexists. split.
    - stepb_tk F_23be4 D_23be4 ltac:(condZ).
      sn F_23c34 D_23c34. sn F_23c38 D_23c38. sn F_23c3c D_23c3c. sn F_23c40 D_23c40. sn F_23c44 D_23c44.
      sn F_23c48 D_23c48.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ph_Ebad : forall regs m (h : Z),
    (20000 < h < 2 ^ 64)%Z -> getr regs 11 = Z_to_bv 64 h -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x23be4) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dVLS_1075b 0x1075b /\ getr regs' 11 = rl dVLS_10553 0x10553 /\ getr regs' 1 = rl dVL_239c0 0x23c10
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVLS_10553 :: dVLS_1075b :: nil).
    intros regs m h Hh H11 H13 Rg Rs. eexists. split.
    - stepb_ft F_23be4 D_23be4 ltac:(condZ).
      sn F_23be8 D_23be8.
      stepLD F_23bec D_23bec (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_23bf0 D_23bf0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_23bf4 D_23bf4.
      stepb_ft F_23bf8 D_23bf8 ltac:(condZ).
      sn F_23bfc D_23bfc. sn F_23c00 D_23c00. sn F_23c04 D_23c04. sn F_23c08 D_23c08.
      sn F_23c0c D_23c0c.
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
      msteps SEGS (mkst regs (rl dVL_239c0 0x23c10) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v Hs Hs64 Hret R8 R16 R24 R32 R40 R48 H2. eexists. split.
    - sn F_23c10 D_23c10.
      stepLD8 F_23c14 D_23c14 ret. stepLD8 F_23c18 D_23c18 s0v. stepLD8 F_23c1c D_23c1c s1v.
      stepLD8 F_23c20 D_23c20 s2v. stepLD8 F_23c24 D_23c24 s3v. stepLD8 F_23c28 D_23c28 s4v.
      zv F_23c2c D_23c2c (Z_to_bv 64 s).
      stepret F_23c30 D_23c30 ret ltac:(bveq).
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
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = rl dVLS_10553 0x10553 ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x23b58) m rom) (mkst regs' (rl dF_13730 0x13730) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = rl dVLS_10553 0x10553
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20]%list) regs regs'.
  Proof. rl_dbounds (dVLS_10553 :: nil).
    intros regs m s msg ret s0v s1v s2v s3v s4v Hs Hs64 R8 R16 R24 R32 R40 R48 H2 H10 H11. eexists. split.
    - sn F_23b58 D_23b58.
      stepLD8 F_23b5c D_23b5c ret. stepLD8 F_23b60 D_23b60 s0v. stepLD8 F_23b64 D_23b64 s1v.
      stepLD8 F_23b68 D_23b68 s2v. stepLD8 F_23b6c D_23b6c s3v. stepLD8 F_23b70 D_23b70 s4v.
      zv F_23b74 D_23b74 (Z_to_bv 64 s).
      sn F_23b78 D_23b78.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_G : forall regs m,
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x23b34) m rom) (mkst regs' (rl dVL_239c0 0x23b58) m rom)
      /\ getr regs' 10 = rl dVLS_1041b 0x1041b /\ getr regs' 11 = rl dVLS_10553 0x10553
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVLS_1041b :: dVLS_10553 :: nil).
    intros regs m Rg Rs. eexists. split.
    - sn F_23b34 D_23b34.
      stepLD F_23b38 D_23b38 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_23b3c D_23b3c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_23b40 D_23b40.
      stepb_ft F_23b44 D_23b44 ltac:(condZ).
      sn F_23b48 D_23b48. sn F_23b4c D_23b4c. sn F_23b50 D_23b50. sn F_23b54 D_23b54.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ph_Fbad : forall regs m,
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_239c0 0x23c4c) m rom) (mkst regs' (rl dVL_239c0 0x23b58) m rom)
      /\ getr regs' 10 = rl dVLS_103c3 0x103c3 /\ getr regs' 11 = rl dVLS_10553 0x10553
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVLS_103c3 :: dVLS_10553 :: nil).
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_23c4c D_23c4c ltac:(condZ).
      sn F_23c9c D_23c9c.
      stepLD F_23ca0 D_23ca0 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_23ca4 D_23ca4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_23ca8 D_23ca8.
      stepb_ft F_23cac D_23cac ltac:(condZ).
      sn F_23cb0 D_23cb0. sn F_23cb4 D_23cb4. sn F_23cb8 D_23cb8. sn F_23cbc D_23cbc. sn F_23cc0 D_23cc0.
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
      msteps SEGS (mkst regs (rl dVL_239c0 0x23c4c) m rom)
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
    - stepb_ft F_23c4c D_23c4c ltac:(condZ).
      sn F_23c50 D_23c50. sn F_23c54 D_23c54. sn F_23c58 D_23c58.
      (* [comment removed for export] *)
      stepb_ft F_23fbc D_23fbc ltac:(condZ). guard8 F_23fc0 D_23fc0 AL8.
      stepb_ft F_23fc4 D_23fc4 ltac:(condZ). stepb_ft F_23fc8 D_23fc8 ltac:(condZ).
      stepST F_23fcc D_23fcc (Z_to_bv 64 pix) (Z_to_bv 64 w) ltac:(sok_in SOK).
      sn F_23fd0 D_23fd0. stepretF F_23fd4 D_23fd4 F_23c5c.
      sn F_23c5c D_23c5c. sn F_23c60 D_23c60. sn F_23c64 D_23c64.
      (* [comment removed for export] *)
      stepb_ft F_24044 D_24044 ltac:(condZ). guard8 F_24048 D_24048 AL8.
      stepb_ft F_2404c D_2404c ltac:(condZ). stepb_ft F_24050 D_24050 ltac:(condZ).
      stepST F_24054 D_24054 (Z_to_bv 64 (pix + 4)) (Z_to_bv 64 h) ltac:(sok_in SOK).
      sn F_24058 D_24058. stepretF F_2405c D_2405c F_23c68.
      sn F_23c68 D_23c68. sn F_23c6c D_23c6c. sn F_23c70 D_23c70.
      (* [comment removed for export] *)
      stepb_ft F_240cc D_240cc ltac:(condZ). stepb_ft F_240d0 D_240d0 ltac:(condZ). guard8 F_240d4 D_240d4 AL8.
      stepb_ft F_240d8 D_240d8 ltac:(condZ).
      stepST F_240dc D_240dc (Z_to_bv 64 (pix + 8)) (Z_to_bv 64 d) ltac:(sok_in SOK).
      sn F_240e0 D_240e0. stepretF F_240e4 D_240e4 F_23c74.
      guard8 F_23c74 D_23c74 AL8. stepb_ft F_23c78 D_23c78 ltac:(condZ).
      sn F_23c7c D_23c7c.
      stepST F_23c80 D_23c80 (Z_to_bv 64 (pix + 16)) (Z_to_bv 64 wpl) ltac:(sok_in SOK).
      sn F_23c84 D_23c84. sn F_23c88 D_23c88. sn F_23c8c D_23c8c.
      stepb_tk F_23c90 D_23c90 ltac:(pin; rewrite (spp_test d DV); exact E).
        sn F_23cc4 D_23cc4.
        stepST F_23cc8 D_23cc8 (Z_to_bv 64 (pix + 12)) (Z_to_bv 64 3) ltac:(sok_in SOK).
        stepfence F_23ccc D_23ccc.
        stepST F_23cd0 D_23cd0 (Z_to_bv 64 (pix + 20)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_23cd4 D_23cd4.
        stepST F_23cd8 D_23cd8 (Z_to_bv 64 (pix + 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
        sn F_23cdc D_23cdc.
        stepLD8 F_23c14 D_23c14 ret. stepLD8 F_23c18 D_23c18 s0v. stepLD8 F_23c1c D_23c1c s1v.
        stepLD8 F_23c20 D_23c20 s2v. stepLD8 F_23c24 D_23c24 s3v. stepLD8 F_23c28 D_23c28 s4v.
        zv F_23c2c D_23c2c (Z_to_bv 64 s).
        stepret F_23c30 D_23c30 ret ltac:(bveq).
        apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - stepb_ft F_23c4c D_23c4c ltac:(condZ).
      sn F_23c50 D_23c50. sn F_23c54 D_23c54. sn F_23c58 D_23c58.
      stepb_ft F_23fbc D_23fbc ltac:(condZ). guard8 F_23fc0 D_23fc0 AL8.
      stepb_ft F_23fc4 D_23fc4 ltac:(condZ). stepb_ft F_23fc8 D_23fc8 ltac:(condZ).
      stepST F_23fcc D_23fcc (Z_to_bv 64 pix) (Z_to_bv 64 w) ltac:(sok_in SOK).
      sn F_23fd0 D_23fd0. stepretF F_23fd4 D_23fd4 F_23c5c.
      sn F_23c5c D_23c5c. sn F_23c60 D_23c60. sn F_23c64 D_23c64.
      stepb_ft F_24044 D_24044 ltac:(condZ). guard8 F_24048 D_24048 AL8.
      stepb_ft F_2404c D_2404c ltac:(condZ). stepb_ft F_24050 D_24050 ltac:(condZ).
      stepST F_24054 D_24054 (Z_to_bv 64 (pix + 4)) (Z_to_bv 64 h) ltac:(sok_in SOK).
      sn F_24058 D_24058. stepretF F_2405c D_2405c F_23c68.
      sn F_23c68 D_23c68. sn F_23c6c D_23c6c. sn F_23c70 D_23c70.
      stepb_ft F_240cc D_240cc ltac:(condZ). stepb_ft F_240d0 D_240d0 ltac:(condZ). guard8 F_240d4 D_240d4 AL8.
      stepb_ft F_240d8 D_240d8 ltac:(condZ).
      stepST F_240dc D_240dc (Z_to_bv 64 (pix + 8)) (Z_to_bv 64 d) ltac:(sok_in SOK).
      sn F_240e0 D_240e0. stepretF F_240e4 D_240e4 F_23c74.
      guard8 F_23c74 D_23c74 AL8. stepb_ft F_23c78 D_23c78 ltac:(condZ).
      sn F_23c7c D_23c7c.
      stepST F_23c80 D_23c80 (Z_to_bv 64 (pix + 16)) (Z_to_bv 64 wpl) ltac:(sok_in SOK).
      sn F_23c84 D_23c84. sn F_23c88 D_23c88. sn F_23c8c D_23c8c.
      stepb_ft F_23c90 D_23c90 ltac:(pin; rewrite (spp_test d DV); exact E).
        sn F_23c94 D_23c94. sn F_23c98 D_23c98.
        stepST F_23cc8 D_23cc8 (Z_to_bv 64 (pix + 12)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_23ccc D_23ccc.
        stepST F_23cd0 D_23cd0 (Z_to_bv 64 (pix + 20)) (Z_to_bv 64 1) ltac:(sok_in SOK).
        stepfence F_23cd4 D_23cd4.
        stepST F_23cd8 D_23cd8 (Z_to_bv 64 (pix + 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
        sn F_23cdc D_23cdc.
        stepLD8 F_23c14 D_23c14 ret. stepLD8 F_23c18 D_23c18 s0v. stepLD8 F_23c1c D_23c1c s1v.
        stepLD8 F_23c20 D_23c20 s2v. stepLD8 F_23c24 D_23c24 s3v. stepLD8 F_23c28 D_23c28 s4v.
        zv F_23c2c D_23c2c (Z_to_bv 64 s).
        stepret F_23c30 D_23c30 ret ltac:(bveq).
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

Lemma str_pixCreateHeader : str16 (0x10553 + dVLS_10553) 15. Proof. rl_dbounds (dVLS_10553 :: nil). str16_tac. Qed.
Lemma str_msg_64mb : str16 (0x1035b + dVLS_1035b) 47. Proof. rl_dbounds (dVLS_1035b :: nil). str16_tac. Qed.
Lemma str_msg_w20k : str16 (0x10991 + dVLS_10991) 51. Proof. rl_dbounds (dVLS_10991 :: nil). str16_tac. Qed.
Lemma str_msg_h20k : str16 (0x1075b + dVLS_1075b) 52. Proof. rl_dbounds (dVLS_1075b :: nil). str16_tac. Qed.
Lemma str_msg_depth : str16 (0x1041b + dVLS_1041b) 38. Proof. rl_dbounds (dVLS_1041b :: nil). str16_tac. Qed.
Lemma str_msg_pixd : str16 (0x103c3 + dVLS_103c3) 13. Proof. rl_dbounds (dVLS_103c3 :: nil). str16_tac. Qed.

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
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 1 = rl dVL_239c0 0x23c10 -> getr r 10 = Z_to_bv 64 fmt -> getr r 11 = rl dVLS_10553 0x10553 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x) ->
  In fmt (SSP.ls_fmts1 LG) -> str16 fmt kf ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ False)) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (rl dF_13694 0x13694) M al_rom) md) S.
Proof. rl_dbounds (dVLS_10553 :: nil).
  intros C A m M md regs r s fmt kf ret S CK HW PM Hs16 Hlo Hhi Hret CE R2 R1 R10 R11 RR Hin Sf HK H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  apply (lept_stderr1_W C A M md r (s - 48) fmt (0x10553 + dVLS_10553) kf 15 (rl dVL_239c0 0x23c10) S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) R1 ltac:(rl_ret_ok_VL)
           R10 R11 Hin Sf str_pixCreateHeader).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
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
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 10 = Z_to_bv 64 msg -> getr r 11 = rl dVLS_10553 0x10553 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x) -> str16 msg km ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ False)) ->
     roomtr A vm0 A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (rl dVL_239c0 0x23b58) M al_rom) md) S.
Proof. rl_dbounds (dVLS_10553 :: nil).
  intros C A A1 m M md vm0 regs r s msg km ret S CK HW PM LQ RT0 Hs16 Hlo Hhi Hret CE R2 R10 R11 RR Sm HK H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  destruct CE as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  destruct (ph_H al_rom r M s msg ret _ _ _ _ _ ltac:(lia) ltac:(lia) Q1 Q2 Q3 Q4 Q5 Q6 R2 R10 R11)
    as (r1 & RUN1 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & V20 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (returnErrorPtr_W C A1 M md r1 s msg (0x10553 + dVLS_10553) km 15 ret (Z_to_bv 64 0) S CK HW V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
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
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ (hdr_ok w h d /\ pix_new C A A' m' pix (pix_hdr w h d)))) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdr ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_239c0 0x239c0) m al_rom) md) S.
Proof. rl_dbounds (dVLS_1035b :: dVLS_103c3 :: dVLS_1041b :: dVLS_1075b :: dVLS_10991 :: nil).
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
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
    apply (ph_eptr_W C A A m (FR6 m s ret regs) md (m_vmmaps md) regs r2 s (0x1041b + dVLS_1041b) 38 ret S CK HW1 PM1 ltac:(intros; reflexivity) ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret
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
      apply (ph_lerror_W C A m M1 md regs r3 s (0x1035b + dVLS_1035b) 47 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
               ltac:(csr; reflexivity) V1 V10 V11 ltac:(rest_solve) ltac:(cbn; do 1 right; left; reflexivity) str_msg_64mb HK0 H2). }
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
      apply (ph_lerror_W C A m M1 md regs r4 s (0x10991 + dVLS_10991) 51 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
               ltac:(csr; reflexivity) X1 X10 X11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_w20k HK0 H2). }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (ph_D al_rom r3 M1 w ltac:(lia) V10 V13) |].
    destruct (Z_lt_ge_dec 20000 h) as [HBIG|HOK].
    { (* [comment removed for export] *)
      destruct (ph_Ebad al_rom r3 M1 h ltac:(lia) V11 V13 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r4 & RUN4 & X10 & X11 & X1 & AG4).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
      apply (ph_lerror_W C A m M1 md regs r4 s (0x1075b + dVLS_1075b) 52 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
               ltac:(csr; reflexivity) X1 X10 X11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_h20k HK0 H2). }
    (* [comment removed for export] *)
    destruct (ph_E al_rom r3 M1 w h d ltac:(lia) V10 V11 V12 V13) as (r4 & RUN4 & X10 & X11 & X1 & X19 & X9 & X8 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
    assert (X4 : getr r4 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (X20 : getr r4 20 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
    apply (W_calloc16 C A M1 md r4 1 64 (rl dVL_239c0 0x23c4c) (s - 48) S CK HW1 X10 X11 ltac:(lia) ltac:(lia) ltac:(lia) X1
             ltac:(rl_ret_ok_VL) X4 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r5 res HWa Hres CSa OUTa PMa HRTa.
    assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
    pose proof (cells6_frm C (s - 48) M1 m1 s _ _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
    destruct OUTa as [[Hres0 LIVEQ] | (Hnz & L0 & L1 & L00 & LEQ & ZERO & AL16 & TOP)].
    + (* [comment removed for export] *)
      rewrite Hres0 in Hres.
      destruct (ph_Fbad al_rom r5 m1 (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) Hres) as (r6 & RUN6 & Y10 & Y11 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      apply (ph_eptr_W C A A1 m m1 (with_vmmaps vm1 md) (m_vmmaps md) regs r6 s (0x103c3 + dVLS_103c3) 13 ret S CK HWa PMa' LIVEQ ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret CE2
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

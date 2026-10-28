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
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptStderr V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL7a.
Import V15CL7a.V15LeptErr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptPadBitsW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15Kit.
Import V15Kit.V15Memset.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15_code_15000_16000 V15_code_16000_17000 V15_code_18000_19000 V15_code_28000_29000 V15_code_32000_32c30.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom14.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixCreate.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  #[local] Definition FR4 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).

  (* [comment removed for export] *)
  Lemma pn_A : forall regs m (s w h d : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x16bec : word) m rom) (mkst regs' (0x16d34 : word) (FR4 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x16c04 /\ getr regs' 10 = Z_to_bv 64 w
      /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 9 = Z_to_bv 64 h
      /\ regs_agree (fun r => In r [1; 2; 9]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 SOK H2 H1 H10 H11 H12. unfold FR4.
    eexists. split.
    - zv F_16ae8 D_16ae8 (Z_to_bv 64 (s - 32)).
      stepST F_16aec D_16aec (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16af0 D_16af0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_16af4 D_16af4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_16af8 D_16af8. sn F_16afc D_16afc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_F1 : forall regs m (s : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x16c04 : word) m rom) (mkst regs' (0x155bc : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x1051f /\ getr regs' 11 = Z_to_bv 64 0x106ce
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Rg Rs R8 R16 R24 H2 H10. eexists. split.
    - stepb_tk F_16b00 D_16b00 ltac:(condZ).
      sn F_16b50 D_16b50.
      stepLD F_16b54 D_16b54 (Z_to_le_bytes 8 0x35268) (Z_to_bv 64 0x35268) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16b58 D_16b58 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16b5c D_16b5c.
      stepb_ft F_16b60 D_16b60 ltac:(condZ).
      sn F_16b64 D_16b64. sn F_16b68 D_16b68. sn F_16b6c D_16b6c. sn F_16b70 D_16b70. sn F_16b74 D_16b74.
      stepLD8 F_16b78 D_16b78 ret. stepLD8 F_16b7c D_16b7c s0v. stepLD8 F_16b80 D_16b80 s1v.
      zv F_16b84 D_16b84 (Z_to_bv 64 s).
      sn F_16b88 D_16b88.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_B : forall regs m (s h pix : Z) (v : pixv),
    PIXat m pix v -> p_h v = h -> (1 <= h <= 20000)%Z -> (1 <= p_wpl v <= 20000)%Z -> (4096 <= pix)%Z -> (pix mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 0x35278) 8 = Some (Z_to_le_bytes 8 0x28b94) ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 9 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (0x16c04 : word) m rom) (mkst regs' (0x28b94 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (4 * (p_wpl v * h)) /\ getr regs' 1 = Z_to_bv 64 0x16c3c /\ getr regs' 8 = Z_to_bv 64 pix
      /\ getr regs' 9 = Z_to_bv 64 0x35278
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s h pix v PX Hh Rh Rwpl Hpix AL8 Rpmm H10 H9. pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (HM : (0 <= 4 * (p_wpl v * h) <= 1600000000)%Z) by nia.
    eexists. split.
    - stepb_ft F_16b00 D_16b00 ltac:(condZ).
      sn F_16b04 D_16b04.
      guard8 F_16b08 D_16b08 AL8. stepb_ft F_16b0c D_16b0c ltac:(condZ).
      stepLD F_16b10 D_16b10 (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl v)) by lia.
      stepiv F_16b14 D_16b14 (Z_to_bv 64 (4 * p_wpl v)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_16b18 D_16b18. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_16b1c D_16b1c (Z_to_bv 64 (4 * (p_wpl v * h))).
      sn F_16b20 D_16b20. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_16b24 D_16b24 ltac:(condZ).
      sn F_16b28 D_16b28. sn F_16b2c D_16b2c.
      stepLD F_16b30 D_16b30 (Z_to_le_bytes 8 0x28b94) (Z_to_bv 64 0x28b94) ltac:(addr_norm; exact Rpmm) ltac:(apply lez8; lia).
      stepjr F_16b34 D_16b34 (Z_to_bv 64 0x28b94) ltac:(gres; reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_C : forall regs m (pix data : Z),
    (4096 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z -> (1 <= data < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 10 = Z_to_bv 64 data -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x16c3c : word) m rom)
                  (mkst regs' (0x181ac : word) (wbytes m (Z_to_bv 64 (pix + 56)) (word_to_le_bytes 8 (Z_to_bv 64 data))) rom)
      /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x16c50 /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pix data Hpix Hpix64 Hd SOK H10 H8. eexists. split.
    - stepb_ft F_16b38 D_16b38 ltac:(condZ).
      stepST F_16b3c D_16b3c (Z_to_bv 64 (pix + 56)) (Z_to_bv 64 data) ltac:(sok_in SOK).
      sn F_16b40 D_16b40. sn F_16b44 D_16b44. sn F_16b48 D_16b48.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_D : forall regs m (s pix : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x16c50 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pix
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pix ret s0v s1v Hs Hs64 Hret R8 R16 R24 H2 H8. eexists. split.
    - sn F_16b4c D_16b4c. sn F_16c14 D_16c14.
      stepLD8 F_16c18 D_16c18 ret. stepLD8 F_16c1c D_16c1c s0v. stepLD8 F_16c20 D_16c20 s1v.
      zv F_16c24 D_16c24 (Z_to_bv 64 s).
      stepret F_16c28 D_16c28 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_F2 : forall regs m (s pix : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_rc v = 1%Z -> p_data v = 0%Z -> p_text v = 0%Z -> p_cmap v = 0%Z ->
    (4096 <= pix)%Z -> (pix mod 16 = 0)%Z -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    store_ok SEGS m (Z_to_bv 64 pix) 64 = true -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x16c3c : word) m rom)
                  (mkst regs' (0x28a54 : word)
                     (wbytes (wbytes m (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                             (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x16ce0 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pix v Hs Hs64 PX Hrc Hdat Ht Hc Hpix Hal DJ SOKp SOK H2 H10 H8. pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - stepb_tk F_16b38 D_16b38 ltac:(condZ).
      zv F_16b8c D_16b8c (Z_to_bv 64 (pix + 20)).
      sn F_16b90 D_16b90.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_16b94 eq_refl D_16b94);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; rewrite <- Hrc; exact (PIX_rd_rc SEGS _ _ _ PX)
          | apply lez4; lia
          | gres; sok_in SOKp ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 1) by lia.
      sn F_16b98 D_16b98.
      stepb_ft F_16b9c D_16b9c ltac:(condZ).
      stepLD F_16ba0 D_16ba0 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; repeat rdn_peel1; rewrite <- Hdat; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_16ba4 D_16ba4 ltac:(condZ).
      stepLD F_16bb0 D_16bb0 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; repeat rdn_peel1; rewrite <- Ht; exact (PIX_rd_text SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_16bb4 D_16bb4 ltac:(condZ).
      stepLD F_16bbc D_16bbc (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; repeat rdn_peel1; rewrite <- Hc; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepST F_16bc0 D_16bc0 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_16bc4 D_16bc4 ltac:(condZ).
      sn F_16bd4 D_16bd4. sn F_16bd8 D_16bd8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_F3 : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x16ce0 : word) m rom) (mkst regs' (0x155bc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x110e7 /\ getr regs' 11 = Z_to_bv 64 0x106ce /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x16d0c
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs. eexists. split.
    - sn F_16bdc D_16bdc.
      stepLD F_16be0 D_16be0 (Z_to_le_bytes 8 0x35268) (Z_to_bv 64 0x35268) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16be4 D_16be4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16be8 D_16be8.
      stepb_ft F_16bec D_16bec ltac:(condZ).
      sn F_16bf0 D_16bf0. sn F_16bf4 D_16bf4. sn F_16bf8 D_16bf8. sn F_16bfc D_16bfc. sn F_16c00 D_16c00. sn F_16c04 D_16c04.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_F4 : forall regs m (s : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x16d0c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret R8 R16 R24 H2 H10. eexists. split.
    - sn F_16c08 D_16c08. sn F_16c0c D_16c0c. sn F_16c14 D_16c14.
      stepLD8 F_16c18 D_16c18 ret. stepLD8 F_16c1c D_16c1c s0v. stepLD8 F_16c20 D_16c20 s1v.
      zv F_16c24 D_16c24 (Z_to_bv 64 s).
      stepret F_16c28 D_16c28 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_A : forall regs m (s : Z) (ret : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret ->
    exists regs',
      msteps SEGS (mkst regs (0x16b48 : word) m rom)
                  (mkst regs' (0x16bec : word) (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x16b58
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 11 = getr regs 11 /\ getr regs' 12 = getr regs 12
      /\ regs_agree (fun r => In r [1; 2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1. eexists. split.
    - zv F_16a44 D_16a44 (Z_to_bv 64 (s - 16)).
      stepST F_16a48 D_16a48 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16a4c D_16a4c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      sn F_16a50 D_16a50. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pk_F : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268) -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x16b58 : word) m rom) (mkst regs' (0x155bc : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x1051f /\ getr regs' 11 = Z_to_bv 64 0x1084c
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Rg Rs R8 R16 H2 H10. eexists. split.
    - stepb_tk F_16a54 D_16a54 ltac:(condZ).
      sn F_16a98 D_16a98.
      stepLD F_16a9c D_16a9c (Z_to_le_bytes 8 0x35268) (Z_to_bv 64 0x35268) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16aa0 D_16aa0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16aa4 D_16aa4.
      stepb_ft F_16aa8 D_16aa8 ltac:(condZ).
      sn F_16aac D_16aac. sn F_16ab0 D_16ab0. sn F_16ab4 D_16ab4. sn F_16ab8 D_16ab8. sn F_16abc D_16abc.
      stepLD8 F_16ac0 D_16ac0 ret. stepLD8 F_16ac4 D_16ac4 s0v.
      zv F_16ac8 D_16ac8 (Z_to_bv 64 s).
      sn F_16acc D_16acc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pk_B : forall regs m (pix : Z) (v : pixv),
    PIXat m pix v -> (4096 <= pix)%Z -> (1 <= p_h v <= 20000)%Z -> (1 <= p_wpl v <= 20000)%Z -> (pix mod 8 = 0)%Z ->
    getr regs 10 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x16b58 : word) m rom) (mkst regs' (0x32ac8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl v * p_h v))
      /\ getr regs' 1 = Z_to_bv 64 0x16b94 /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m pix v PX Hpix Rh Rw AL8 H10. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF).
    assert (HM : (0 <= 4 * (p_wpl v * p_h v) <= 1600000000)%Z) by nia.
    eexists. split.
    - stepb_ft F_16a54 D_16a54 ltac:(condZ).
      guard8 F_16a58 D_16a58 AL8. stepb_ft F_16a5c D_16a5c ltac:(condZ).
      stepLD F_16a60 D_16a60 (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepLD F_16a64 D_16a64 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepiv F_16a68 D_16a68 (Z_to_bv 64 (4 * p_wpl v)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_16a6c D_16a6c. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_16a70 D_16a70 (Z_to_bv 64 (4 * (p_wpl v * p_h v))).
      sn F_16a74 D_16a74. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_16a78 D_16a78 ltac:(condZ).
      stepLD F_16a7c D_16a7c (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      sn F_16a80 D_16a80. sn F_16a84 D_16a84. sn F_16a88 D_16a88. sn F_16a8c D_16a8c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pk_C : forall regs m (s pix : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x16b94 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s pix ret s0v Hs Hs64 Hret R8 R16 H2 H8. eexists. split.
    - sn F_16a90 D_16a90. sn F_16a94 D_16a94.
      stepLD8 F_16ad4 D_16ad4 ret. stepLD8 F_16ad8 D_16ad8 s0v.
      zv F_16adc D_16adc (Z_to_bv 64 s).
      stepret F_16ae0 D_16ae0 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.

Definition cells4 (m : word -> option byte) (s : Z) (ret s0v s1v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v).

Lemma cells4_FR4 : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells4 (FR4 m s ret regs) s ret (getr regs 8) (getr regs 9).
Proof. intros m s ret regs Hs Hs64. unfold cells4, FR4. repeat split; rdn_solve. Qed.

Lemma cells4_frm : forall C s' m m' s ret s0v s1v, Cok C -> FRM C s' m m' ->
  (s' <= s - 24)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z ->
  cells4 m s ret s0v s1v -> cells4 m' s ret s0v s1v.
Proof.
  intros C s' m m' s ret s0v s1v CK F Hs' Hlo Hs64 (R1 & R2 & R3). unfold cells4.
  rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
Qed.

Lemma cells4_out : forall m m' (lo hi s : Z) ret s0v s1v,
  (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 24)%Z -> (24 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells4 m s ret s0v s1v -> cells4 m' s ret s0v s1v.
Proof.
  intros m m' lo hi s ret s0v s1v OUT Hhi Hs Hs64 (R1 & R2 & R3). unfold cells4.
  repeat split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption]).
Qed.

Lemma str_pixCreateNoInit : str16 0x106ce 15. Proof. str16_tac. Qed.
Lemma str_msg_pixd : str16 0x1051f 13. Proof. str16_tac. Qed.
Lemma str_msg_datafail : str16 0x110e7 28. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Definition pixr_new (C : lctx) (A A' : AS) (m' : word -> option byte) (pix data : Z) (v : pixv) : Prop :=
  (4096 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (pix mod 16 = 0)%Z /\
  (4096 <= data)%Z /\ (data + 4 * (p_wpl v * p_h v) <= alloc_top (c_vm C))%Z /\ (data mod 16 = 0)%Z /\ pix <> data /\
  live A (Z_to_bv 64 pix) = None /\ live A (Z_to_bv 64 data) = None /\
  live (c_A0 C) (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 data) = None /\
  live A' (Z_to_bv 64 pix) = Some 64%Z /\ live A' (Z_to_bv 64 data) = Some (4 * (p_wpl v * p_h v))%Z /\
  (forall q, q <> Z_to_bv 64 pix -> q <> Z_to_bv 64 data -> live A' q = live A q) /\
  PIXat m' pix v /\ p_data v = data.

Theorem pixCreateNoInit_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix data, getr regs' 10 = Z_to_bv 64 pix /\ hdr_ok w h d /\ pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data))) ->
     roomtr A (m_vmmaps md) A' vm' RK_pix RB_pix14 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x16bec : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pn_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR4 m s ret regs) md /\ POSTM C A s m (FR4 m s ret regs)) by (unfold FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR4 m s ret regs) in *.
  pose proof (cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  apply (pixCreateHeader_W C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x16c04) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw Hh Hwh Hd).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x16c04) with (0x16c04 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (cells4_frm C (s - 32) M1 m1 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 h) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pix & Hres & HOK & PN)].
  - (* [comment removed for export] *)
    destruct CE2 as (Z1 & Z2 & Z3).
    destruct (pn_F1 al_rom r2 m1 s ret _ _ ltac:(lia) ltac:(lia) (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) Z1 Z2 Z3 E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m1 _ r3 s 0x1051f 0x106ce 13 15 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd str_pixCreateNoInit).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m1 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + room_tac.
  - (* [comment removed for export] *)
    destruct HOK as (DV & Hw2 & Hh2 & Hsz). destruct PN as (Gp & TOPp & ALp & L0 & L00 & L1 & LEQ & PX1).
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
    destruct (pn_B al_rom r2 m1 s h pix (pix_hdr w h d) PX1 eq_refl ltac:(lia) ltac:(cbn; lia) Gp AL8 (W_pmm_malloc C A1 m1 _ HWa) Hres E9)
      as (r3 & RUN3 & V10 & V1 & V8 & V9 & AG3).
    cbn [p_wpl pix_hdr] in V10.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    assert (V4 : getr r3 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    replace (0x28b94 : word) with (Z_to_bv 64 0x28b94) by (apply bv_eq; reflexivity).
    apply (W_malloc16 C A1 m1 _ r3 (4 * (wpl_of w d * h)) (Z_to_bv 64 0x16c3c) (s - 32) S CK HWa V10 ltac:(lia) V1
             ltac:(red; apply bv_eq; reflexivity) V4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res HWb Hres2 CSb OUTb PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
    replace (Z_to_bv 64 0x16c3c) with (0x16c3c : word) by (apply bv_eq; reflexivity).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (PMb' : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
    pose proof (cells4_frm C (s - 32) m1 m2 s _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (PX2 : PIXat m2 pix (pix_hdr w h d)).
    { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. pose proof (proj2 PMb (Z_to_bv 64 pix) 64%Z (u x - pix)%Z L1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
    assert (X8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (X4 : getr r4 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    assert (SOKp : store_ok SEGS m2 (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m2 pix _ x PX2 ltac:(lia) E). }
    destruct OUTb as [[Hres0 LIVEQ] | (Hnz & K0 & K1 & K00 & KEQ & AL16 & TOP)].
    + (* [comment removed for export] *)
      rewrite Hres0 in Hres2.
      destruct (pn_F2 al_rom r4 m2 s pix (pix_hdr w h d) ltac:(lia) ltac:(lia) PX2 eq_refl eq_refl eq_refl eq_refl Gp ALp ltac:(lia) SOKp
                  (W_sok_win C A2 m2 _ (s - 32) 32 CK HWb ltac:(lia) ltac:(cbn; lia)) X2 Hres2 X8)
        as (r5 & RUN5 & Y2 & Y1 & Y10 & Y8 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
      match goal with |- realizes _ (mkCfg (mkst _ _ ?MM _) _) _ => set (M3 := MM) end.
      assert (Lp2 : live A2 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite LIVEQ; exact L1).
      assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A s m M3).
      { subst M3. apply (WP_win C A2 A m _ _ _ _ s CK); [| exact (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LIVEQ)) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
        apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pix) _ 64); [exact CK | | exact Lp2 | exact L0 | exact L00 | exact (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LIVEQ)) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
        split; [exact HWb | exact PMb']. }
      destruct WP3 as [HW3 PM3].
      assert (Y4 : getr r5 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
      replace (0x28a54 : word) with (Z_to_bv 64 0x28a54) by (apply bv_eq; reflexivity).
      apply (W_free16 C A2 M3 _ r5 (Z_to_bv 64 pix) (Z_to_bv 64 0x16ce0) 64 (s - 32) S CK HW3 Y10 Lp2 L00 Y1
               ltac:(red; apply bv_eq; reflexivity) Y4 Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
      intros A3 m3 vm3 r6 HWc CSc Lc LEQc PMc HRTc. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWc.
      replace (Z_to_bv 64 0x16ce0) with (0x16ce0 : word) by (apply bv_eq; reflexivity).
      destruct (pn_F3 al_rom r6 m3 (W_sev_got C A3 m3 _ HWc) (W_sev C A3 m3 _ HWc)) as (r7 & RUN7 & Z10 & Z11 & Z12 & Z1' & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWc)) | exact (mp_lazy _ (w_pure _ _ _ _ HWc)) | exact RUN7 |].
      assert (Z2' : getr r7 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      apply (returnErrorPtr_W C A3 m3 _ r7 (s - 32) 0x110e7 0x106ce 28 15 (Z_to_bv 64 0x16d0c) (Z_to_bv 64 0) S CK HWc Z2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Z1' ltac:(red; apply bv_eq; reflexivity)
               Z10 Z11 Z12 str_msg_datafail str_pixCreateNoInit).
      intros m4 r8 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
      replace (Z_to_bv 64 0x16d0c) with (0x16d0c : word) by (apply bv_eq; reflexivity).
      assert (LIVEQ3 : forall q, live A3 q = live A q).
      { intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 pix)) as [->|NE]; [rewrite Lc, L0; reflexivity|]. rewrite (LEQc q NE), LIVEQ. apply LEQ. exact NE. }
      assert (PM4 : POSTM C A s m m4).
      { eapply POSTM_trans; [exact PM3|].
        eapply POSTM_trans; [apply (POSTM_sub C A A3); [apply sub_live_eq; exact LIVEQ3 | eapply POSTM_mono; [|exact PMc]; lia]|].
        apply (POSTM_sub C A A3); [apply sub_live_eq; exact LIVEQ3|].
        eapply (POSTM_range C A3 m3 _ m4); [exact CK | exact HWc | exact OUT4 | lia | lia | lia]. }
      assert (CE4 : cells4 m4 s ret (getr regs 8) (getr regs 9)).
      { apply (cells4_out m3 m4 (s - 32 - (16 + 3376)) (s - 32) s); [exact OUT4 | lia | lia | lia |].
        apply (cells4_frm C (s - 32) M3 m3 s); [exact CK | exact (proj1 PMc) | lia | lia | lia |].
        subst M3. destruct CE3 as (C1 & C2 & C3). unfold cells4.
        repeat split; repeat rdn_peel1; assumption. }
      destruct CE4 as (C1 & C2 & C3).
      assert (W2 : getr r8 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      destruct (pn_F4 al_rom r8 m4 s ret _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 W2 A10) as (r9 & RUN9 & U2 & U1 & U10 & U8 & U9 & AG9).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN9 |].
      apply (HK A3 m4 vm3 r9 HW4).
      * apply cs_kept_intro; csr; try reflexivity.
      * exact PM4.
      * left. split; [exact U10 | exact LIVEQ3].
      * room_tac.
    + (* [comment removed for export] *)
      assert (Hdat : (4096 <= u res)%Z /\ (u res + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z).
      { destruct (blk_range C A2 m2 _ res _ CK HWb K1 ltac:(lia)) as [G1 G2]. lia. }
      assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
      set (data := u res) in *. clearbody data.
      rewrite Eres in Hres2, K0, K1, K00, KEQ.
      assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 data) by (intros E; rewrite E in L1; congruence).
      assert (NEpd' : pix <> data) by (intros E; apply NEpd; rewrite E; reflexivity).
      assert (Lp2 : live A2 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (KEQ _ NEpd); exact L1).
      assert (LAd : live A (Z_to_bv 64 data) = None) by (rewrite <- (LEQ _ (not_eq_sym NEpd)); exact K0).
      assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
      destruct (pn_C al_rom r4 m2 pix data Gp ltac:(lia) ltac:(lia) SOKp Hres2 X8) as (r5 & RUN5 & Y10 & Y11 & Y1 & Y8 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
      match goal with |- realizes _ (mkCfg (mkst _ _ ?MM _) _) _ => set (M3 := MM) end.
      assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A s m M3).
      { subst M3. apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pix) _ 64); [exact CK | | exact Lp2 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
        split; [exact HWb | exact PMb']. }
      destruct WP3 as [HW3 PM3].
      assert (PX3 : PIXat M3 pix (set_data (pix_hdr w h d) data)) by (subst M3; apply PIX_wr_data; [exact PX2 | lia]).
      assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      apply (padbits_W C A A2 M3 _ r5 (s - 32) pix (set_data (pix_hdr w h d) data) (Z_to_bv 64 0x16c50) S CK HW3 SUBb Y2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11
               PX3 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl Lp2).
      { cbn. exact K1. } { cbn. exact LAd. } { cbn. exact K00. } { cbn. exact NEpd. }
      intros m5 r6 HW5 CS5 PM5 PX5 OUT5 A10.
      replace (Z_to_bv 64 0x16c50) with (0x16c50 : word) by (apply bv_eq; reflexivity).
      assert (CE5 : cells4 m5 s ret (getr regs 8) (getr regs 9)).
      { apply (cells4_frm C (s - 32) M3 m5 s); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
        subst M3. destruct CE3 as (C1 & C2 & C3). unfold cells4. repeat split; repeat rdn_peel1; assumption. }
      destruct CE5 as (C1 & C2 & C3).
      assert (W2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      assert (W8 : getr r6 8 = Z_to_bv 64 pix) by (csr; reflexivity).
      destruct (pn_D al_rom r6 m5 s pix ret _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 W2 W8) as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
      apply (HK A2 m5 vm2 r7 HW5).
      * apply cs_kept_intro; csr; try reflexivity.
      * eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PM5]; lia].
      * right. exists pix, data. split; [exact U10|]. split; [split; [exact DV | lia]|].
        unfold pixr_new. cbn [p_wpl p_h p_data set_data pix_hdr].
        do 15 (try (split; [first [assumption | lia | idtac] |])).
        all: try assumption; try lia; try reflexivity.
        all: intros q N1 N2; rewrite (KEQ q N2); apply LEQ; exact N1.
      * room_tac.
Qed.

Lemma str_pixCreate : str16 0x1084c 9. Proof. str16_tac. Qed.

Theorem pixCreate_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix data, getr regs' 10 = Z_to_bv 64 pix /\ hdr_ok w h d /\ pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data))) ->
     roomtr A (m_vmmaps md) A' vm' RK_pix RB_pix14 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x16b48 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pk_A al_rom regs m s ret ltac:(lia) ltac:(lia) SOK H2 H1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  rewrite H10 in Q10. rewrite H11 in Q11. rewrite H12 in Q12.
  apply (pixCreateNoInit_W C A M1 md r1 (s - 16) w h d (Z_to_bv 64 0x16b58) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw Hh Hwh Hd).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x16b58) with (0x16b58 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pix & data & Hres & HOK & PN)].
  - destruct (pk_F al_rom r2 m1 s ret (getr regs 8) ltac:(lia) ltac:(lia) (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) R8 R16 E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m1 _ r3 s 0x1051f 0x1084c 13 9 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd str_pixCreate).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5 HW4).
    + apply cs_kept_intro; csr; try reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m1 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + room_tac.
  - destruct HOK as (DV & Hw2 & Hh2 & Hsz).
    destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0 & K0 & L00 & K00 & L1 & K1 & LEQ & PX1 & Hdata).
    cbn [p_wpl p_h p_data set_data pix_hdr] in TOPd, K1, Hdata.
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
    destruct (pk_B al_rom r2 m1 pix _ PX1 Gp ltac:(cbn; lia) ltac:(cbn; lia) AL8 Hres) as (r3 & RUN3 & V10 & V11 & V12 & V1 & V8 & AG3).
    cbn [p_wpl p_h p_data set_data pix_hdr] in V10, V12.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    assert (SOKd : store_ok SEGS m1 (Z_to_bv 64 data) (Z.to_nat (4 * (wpl_of w d * h))) = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
      unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso.
      destruct (blk_byte C A1 m1 _ (Z_to_bv 64 data) _ x CK HWa K1 ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
    apply (memset_at (with_vmmaps vm1 md) r3 m1 al_rom data (4 * (wpl_of w d * h)) (Z_to_bv 64 0x16b94) S
             (md_pure_with_vmmaps _ _ (w_pure _ _ _ _ HW)) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12).
    intros r4 A10' AG4.
    replace (Z_to_bv 64 0x16b94) with (0x16b94 : word) by (apply bv_eq; reflexivity).
    set (M5 := zf m1 data [(0, 4 * (wpl_of w d * h))%Z]).
    assert (OUT5 : forall x : word, (u x < data \/ data + 4 * (wpl_of w d * h) <= u x)%Z -> M5 x = m1 x).
    { intros x Hx. subst M5. apply zf_outside. apply inzr_falseP. cbn [inzrP]. lia. }
    assert (CH : forall a, M5 a <> m1 a -> scratch C s a \/ (exists p n, live A1 p = Some n /\ live A p = None /\ (u p <= u a < u p + n)%Z)).
    { intros a NE. right. exists (Z_to_bv 64 data), (4 * (wpl_of w d * h))%Z. rewrite u_Z2bv by lia. split; [exact K1 | split; [exact K0|]].
      destruct (Z_lt_ge_dec (u a) data); [exfalso; apply NE; apply OUT5; lia|].
      destruct (Z_lt_ge_dec (u a) (data + 4 * (wpl_of w d * h))); [lia | exfalso; apply NE; apply OUT5; lia]. }
    assert (HW5 : W C A1 M5 (with_vmmaps vm1 md)).
    { apply (W_local C A1 m1 _ M5 s CK HWa Hhi); [| subst M5; apply zf_grows].
      intros a NE. destruct (CH a NE) as [X|(p & n & L & _ & R)]; [left; exact X | right; exists p, n]. split; [exact L | split; [| exact R]].
      destruct (bv_eq_dec _ p (Z_to_bv 64 data)) as [->|NE']; [exact K00|].
      exfalso. (* [comment removed for export] *) apply NE. apply OUT5.
      pose proof (ai_live_disjoint A1 m1 _ _ _ _ _ (w_inv _ _ _ _ HWa) L K1 NE') as D. rewrite u_Z2bv in D by lia.
      pose proof (ai_live_hull A1 m1 _ _ _ (w_inv _ _ _ _ HWa) L) as (Hn0 & _). pose proof (round16_ge n Hn0).
      pose proof (round16_ge (4 * (wpl_of w d * h)) ltac:(lia)). lia. }
    assert (PM5 : POSTM C A s m M5).
    { eapply POSTM_trans; [exact PMa'|]. exact (POSTM_local C A A1 m1 _ M5 s CK HWa (sub_live_new2 _ _ _ _ _ _ L0 K0 L1 K1 LEQ) CH). }
    assert (PX5 : PIXat M5 pix (set_data (pix_hdr w h d) data)).
    { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. apply OUT5.
      pose proof (ai_live_disjoint A1 m1 _ _ _ _ _ (w_inv _ _ _ _ HWa) L1 K1 (zneq_w pix data ltac:(lia) ltac:(lia) NEpd)) as D. rewrite !u_Z2bv in D by lia.
      unfold round16 in D at 1. change ((64 + 15) / 16)%Z with 4%Z in D. pose proof (round16_ge (4 * (wpl_of w d * h)) ltac:(lia)). lia. }
    assert (W2 : getr r4 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
    assert (W8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    destruct (pk_C al_rom r4 M5 s pix ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r5 & RUN5 & U2 & U1 & U10 & U8 & AG5).
    { rewrite <- R8. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT5. lia. }
    { rewrite <- R16. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT5. lia. }
    { exact W2. } { exact W8. }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN5 |].
    apply (HK A1 M5 vm1 r5 HW5).
    + apply cs_kept_intro; csr; try reflexivity.
    + exact PM5.
    + right. exists pix, data. split; [exact U10|]. split; [split; [exact DV | lia]|].
      unfold pixr_new. cbn [p_wpl p_h p_data set_data pix_hdr]. repeat (split; [first [assumption | lia] |]); try assumption.
      all: first [exact PX5 | reflexivity | assumption].
    + room_tac.
Qed.

End PixCreate.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_237d4_24000.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.VL Require Import LeptStderr LeptBase LeptErr LeptPixHdr LeptPadBitsW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import Memset.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
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

Section PixCreate.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC} {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvVL RLOC} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLG} {P16 : PinsG}.
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
      msteps SEGS (mkst regs (rl dVL_23878 0x23878) m rom) (mkst regs' (rl dVL_239c0 0x239c0) (FR4 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = rl dVL_23878 0x23890 /\ getr regs' 10 = Z_to_bv 64 w
      /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 9 = Z_to_bv 64 h
      /\ regs_agree (fun r => In r [1; 2; 9]%list) regs regs'.
  Proof.
    intros regs m s w h d ret Hs Hs64 SOK H2 H1 H10 H11 H12. unfold FR4.
    eexists. split.
    - zv F_23878 D_23878 (Z_to_bv 64 (s - 32)).
      stepST F_2387c D_2387c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_23880 D_23880 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_23884 D_23884 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_23888 D_23888. sn F_2388c D_2388c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_F1 : forall regs m (s : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (rl dA_1e3b0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23878 0x23890) m rom) (mkst regs' (rl dF_13730 0x13730) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = rl dVLS_103c3 0x103c3 /\ getr regs' 11 = rl dVLS_1046c 0x1046c
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3b0 :: dA_1f3f8 :: dVLS_103c3 :: dVLS_1046c :: nil).
    intros regs m s ret s0v s1v Hs Hs64 Rg Rs R8 R16 R24 H2 H10. eexists. split.
    - stepb_tk F_23890 D_23890 ltac:(condZ).
      sn F_238e0 D_238e0.
      stepLD F_238e4 D_238e4 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_238e8 D_238e8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_238ec D_238ec.
      stepb_ft F_238f0 D_238f0 ltac:(condZ).
      sn F_238f4 D_238f4. sn F_238f8 D_238f8. sn F_238fc D_238fc. sn F_23900 D_23900. sn F_23904 D_23904.
      stepLD8 F_23908 D_23908 ret. stepLD8 F_2390c D_2390c s0v. stepLD8 F_23910 D_23910 s1v.
      zv F_23914 D_23914 (Z_to_bv 64 s).
      sn F_23918 D_23918.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_B : forall regs m (s h pix : Z) (v : pixv),
    PIXat m pix v -> p_h v = h -> (1 <= h <= 20000)%Z -> (1 <= p_wpl v <= 20000)%Z -> (4096 <= pix)%Z -> (pix mod 8 = 0)%Z ->
    rdn SEGS m (rl dA_1f430 0x1f430) 8 = Some (Z_to_le_bytes 8 (0x15b3c + dF_15b3c)) ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 9 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23878 0x23890) m rom) (mkst regs' (rl dF_15b3c 0x15b3c) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (4 * (p_wpl v * h)) /\ getr regs' 1 = rl dVL_23878 0x238c8 /\ getr regs' 8 = Z_to_bv 64 pix
      /\ getr regs' 9 = rl dA_1f430 0x1f430
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dA_1f430 :: dF_15b3c :: nil).
    intros regs m s h pix v PX Hh Rh Rwpl Hpix AL8 Rpmm H10 H9. pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (HM : (0 <= 4 * (p_wpl v * h) <= 1600000000)%Z) by nia.
    eexists. split.
    - stepb_ft F_23890 D_23890 ltac:(condZ).
      sn F_23894 D_23894.
      guard8 F_23898 D_23898 AL8. stepb_ft F_2389c D_2389c ltac:(condZ).
      stepLD F_238a0 D_238a0 (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl v)) by lia.
      stepiv F_238a4 D_238a4 (Z_to_bv 64 (4 * p_wpl v)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_238a8 D_238a8. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_238ac D_238ac (Z_to_bv 64 (4 * (p_wpl v * h))).
      sn F_238b0 D_238b0. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_238b4 D_238b4 ltac:(condZ).
      sn F_238b8 D_238b8. sn F_238bc D_238bc.
      stepLD F_238c0 D_238c0 (Z_to_le_bytes 8 (0x15b3c + dF_15b3c)) (rl dF_15b3c 0x15b3c) ltac:(addr_norm; exact Rpmm) ltac:(apply lez8; lia).
      assert (RLJR : ret_ok (rl dF_15b3c 0x15b3c)) by rl_ret_ok_VL. stepjr F_238c4 D_238c4 (rl dF_15b3c 0x15b3c) ltac:(gres; reflexivity). rl_jr_fix. rl_norm. clear RLJR.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_C : forall regs m (pix data : Z),
    (4096 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z -> (1 <= data < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 10 = Z_to_bv 64 data -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23878 0x238c8) m rom)
                  (mkst regs' (rl dVL_242cc 0x242cc) (wbytes m (Z_to_bv 64 (pix + 56)) (word_to_le_bytes 8 (Z_to_bv 64 data))) rom)
      /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 1 = rl dVL_23878 0x238dc /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pix data Hpix Hpix64 Hd SOK H10 H8. eexists. split.
    - stepb_ft F_238c8 D_238c8 ltac:(condZ).
      stepST F_238cc D_238cc (Z_to_bv 64 (pix + 56)) (Z_to_bv 64 data) ltac:(sok_in SOK).
      sn F_238d0 D_238d0. sn F_238d4 D_238d4. sn F_238d8 D_238d8.
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
      msteps SEGS (mkst regs (rl dVL_23878 0x238dc) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pix
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pix ret s0v s1v Hs Hs64 Hret R8 R16 R24 H2 H8. eexists. split.
    - sn F_238dc D_238dc. sn F_239a4 D_239a4.
      stepLD8 F_239a8 D_239a8 ret. stepLD8 F_239ac D_239ac s0v. stepLD8 F_239b0 D_239b0 s1v.
      zv F_239b4 D_239b4 (Z_to_bv 64 s).
      stepret F_239b8 D_239b8 ret ltac:(bveq).
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
      msteps SEGS (mkst regs (rl dVL_23878 0x238c8) m rom)
                  (mkst regs' (rl dF_15b38 0x15b38)
                     (wbytes (wbytes m (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                             (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = rl dVL_23878 0x2396c /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_dbounds (dF_15b38 :: nil).
    intros regs m s pix v Hs Hs64 PX Hrc Hdat Ht Hc Hpix Hal DJ SOKp SOK H2 H10 H8. pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - stepb_tk F_238c8 D_238c8 ltac:(condZ).
      zv F_2391c D_2391c (Z_to_bv 64 (pix + 20)).
      sn F_23920 D_23920.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_23924 eq_refl D_23924);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; rewrite <- Hrc; exact (PIX_rd_rc SEGS _ _ _ PX)
          | apply lez4; lia
          | gres; sok_in SOKp ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; rl_vmc_VL).
      rewrite (v_lw_small 1) by lia.
      sn F_23928 D_23928.
      stepb_ft F_2392c D_2392c ltac:(condZ).
      stepLD F_23930 D_23930 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; repeat rdn_peel1; rewrite <- Hdat; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_23934 D_23934 ltac:(condZ).
      stepLD F_23940 D_23940 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; repeat rdn_peel1; rewrite <- Ht; exact (PIX_rd_text SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_23944 D_23944 ltac:(condZ).
      stepLD F_2394c D_2394c (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; repeat rdn_peel1; rewrite <- Hc; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepST F_23950 D_23950 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_23954 D_23954 ltac:(condZ).
      sn F_23964 D_23964. sn F_23968 D_23968.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pn_F3 : forall regs m,
    rdn SEGS m (rl dA_1e3b0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23878 0x2396c) m rom) (mkst regs' (rl dF_13730 0x13730) m rom)
      /\ getr regs' 10 = rl dVLS_108f4 0x108f4 /\ getr regs' 11 = rl dVLS_1046c 0x1046c /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = rl dVL_23878 0x23998
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3b0 :: dA_1f3f8 :: dVLS_1046c :: dVLS_108f4 :: nil).
    intros regs m Rg Rs. eexists. split.
    - sn F_2396c D_2396c.
      stepLD F_23970 D_23970 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_23974 D_23974 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_23978 D_23978.
      stepb_ft F_2397c D_2397c ltac:(condZ).
      sn F_23980 D_23980. sn F_23984 D_23984. sn F_23988 D_23988. sn F_2398c D_2398c. sn F_23990 D_23990. sn F_23994 D_23994.
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
      msteps SEGS (mkst regs (rl dVL_23878 0x23998) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret R8 R16 R24 H2 H10. eexists. split.
    - sn F_23998 D_23998. sn F_2399c D_2399c. sn F_239a4 D_239a4.
      stepLD8 F_239a8 D_239a8 ret. stepLD8 F_239ac D_239ac s0v. stepLD8 F_239b0 D_239b0 s1v.
      zv F_239b4 D_239b4 (Z_to_bv 64 s).
      stepret F_239b8 D_239b8 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_A : forall regs m (s : Z) (ret : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_237d4 0x237d4) m rom)
                  (mkst regs' (rl dVL_23878 0x23878) (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = rl dVL_237d4 0x237e4
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 11 = getr regs 11 /\ getr regs' 12 = getr regs 12
      /\ regs_agree (fun r => In r [1; 2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1. eexists. split.
    - zv F_237d4 D_237d4 (Z_to_bv 64 (s - 16)).
      stepST F_237d8 D_237d8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_237dc D_237dc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      sn F_237e0 D_237e0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pk_F : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (rl dA_1e3b0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_237d4 0x237e4) m rom) (mkst regs' (rl dF_13730 0x13730) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = rl dVLS_103c3 0x103c3 /\ getr regs' 11 = rl dVLS_104e2 0x104e2
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3b0 :: dA_1f3f8 :: dVLS_103c3 :: dVLS_104e2 :: nil).
    intros regs m s ret s0v Hs Hs64 Rg Rs R8 R16 H2 H10. eexists. split.
    - stepb_tk F_237e4 D_237e4 ltac:(condZ).
      sn F_23828 D_23828.
      stepLD F_2382c D_2382c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_23830 D_23830 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_23834 D_23834.
      stepb_ft F_23838 D_23838 ltac:(condZ).
      sn F_2383c D_2383c. sn F_23840 D_23840. sn F_23844 D_23844. sn F_23848 D_23848. sn F_2384c D_2384c.
      stepLD8 F_23850 D_23850 ret. stepLD8 F_23854 D_23854 s0v.
      zv F_23858 D_23858 (Z_to_bv 64 s).
      sn F_2385c D_2385c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pk_B : forall regs m (pix : Z) (v : pixv),
    PIXat m pix v -> (4096 <= pix)%Z -> (1 <= p_h v <= 20000)%Z -> (1 <= p_wpl v <= 20000)%Z -> (pix mod 8 = 0)%Z ->
    getr regs 10 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_237d4 0x237e4) m rom) (mkst regs' (rl dF_1cdb8 0x1cdb8) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl v * p_h v))
      /\ getr regs' 1 = rl dVL_237d4 0x23820 /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof. rl_dbounds (dF_1cdb8 :: nil).
    intros regs m pix v PX Hpix Rh Rw AL8 H10. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF).
    assert (HM : (0 <= 4 * (p_wpl v * p_h v) <= 1600000000)%Z) by nia.
    eexists. split.
    - stepb_ft F_237e4 D_237e4 ltac:(condZ).
      guard8 F_237e8 D_237e8 AL8. stepb_ft F_237ec D_237ec ltac:(condZ).
      stepLD F_237f0 D_237f0 (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepLD F_237f4 D_237f4 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepiv F_237f8 D_237f8 (Z_to_bv 64 (4 * p_wpl v)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_237fc D_237fc. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_23800 D_23800 (Z_to_bv 64 (4 * (p_wpl v * p_h v))).
      sn F_23804 D_23804. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_23808 D_23808 ltac:(condZ).
      stepLD F_2380c D_2380c (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      sn F_23810 D_23810. sn F_23814 D_23814. sn F_23818 D_23818. sn F_2381c D_2381c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pk_C : forall regs m (s pix : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_237d4 0x23820) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s pix ret s0v Hs Hs64 Hret R8 R16 H2 H8. eexists. split.
    - sn F_23820 D_23820. sn F_23824 D_23824.
      stepLD8 F_23864 D_23864 ret. stepLD8 F_23868 D_23868 s0v.
      zv F_2386c D_2386c (Z_to_bv 64 s).
      stepret F_23870 D_23870 ret ltac:(bveq). apply mst_refl.
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

Lemma str_pixCreateNoInit : str16 (0x1046c + dVLS_1046c) 15. Proof. rl_dbounds (dVLS_1046c :: nil). str16_tac. Qed.
Lemma str_msg_pixd : str16 (0x103c3 + dVLS_103c3) 13. Proof. rl_dbounds (dVLS_103c3 :: nil). str16_tac. Qed.
Lemma str_msg_datafail : str16 (0x108f4 + dVLS_108f4) 28. Proof. rl_dbounds (dVLS_108f4 :: nil). str16_tac. Qed.

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
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix data, getr regs' 10 = Z_to_bv 64 pix /\ hdr_ok w h d /\ pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data))) ->
     roomtr A (m_vmmaps md) A' vm' RK_pix RB_pix ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_23878 0x23878) m al_rom) md) S.
Proof. rl_dbounds (dVLS_103c3 :: dVLS_1046c :: dVLS_108f4 :: nil).
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pn_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR4 m s ret regs) md /\ POSTM C A s m (FR4 m s ret regs)) by (unfold FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR4 m s ret regs) in *.
  pose proof (cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Q4 : getr r1 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
  apply (pixCreateHeader_W C A M1 md r1 (s - 32) w h d (rl dVL_23878 0x23890) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(rl_ret_ok_VL) Q4 Q10 Q11 Q12 Hw Hh Hwh Hd).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (cells4_frm C (s - 32) M1 m1 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 h) by (csr; reflexivity).
  assert (E4 : getr r2 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pix & Hres & HOK & PN)].
  - (* [comment removed for export] *)
    destruct CE2 as (Z1 & Z2 & Z3).
    destruct (pn_F1 al_rom r2 m1 s ret _ _ ltac:(lia) ltac:(lia) (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) Z1 Z2 Z3 E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m1 _ r3 s (0x103c3 + dVLS_103c3) (0x1046c + dVLS_1046c) 13 15 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
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
    assert (V4 : getr r3 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    apply (W_malloc16 C A1 m1 _ r3 (4 * (wpl_of w d * h)) (rl dVL_23878 0x238c8) (s - 32) S CK HWa V10 ltac:(lia) V1
             ltac:(rl_ret_ok_VL) V4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res HWb Hres2 CSb OUTb PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (PMb' : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
    pose proof (cells4_frm C (s - 32) m1 m2 s _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (PX2 : PIXat m2 pix (pix_hdr w h d)).
    { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. pose proof (proj2 PMb (Z_to_bv 64 pix) 64%Z (u x - pix)%Z L1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
    assert (X8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (X4 : getr r4 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
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
      assert (Y4 : getr r5 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
      apply (W_free16 C A2 M3 _ r5 (Z_to_bv 64 pix) (rl dVL_23878 0x2396c) 64 (s - 32) S CK HW3 Y10 Lp2 L00 Y1
               ltac:(rl_ret_ok_VL) Y4 Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
      intros A3 m3 vm3 r6 HWc CSc Lc LEQc PMc HRTc. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWc.
      destruct (pn_F3 al_rom r6 m3 (W_sev_got C A3 m3 _ HWc) (W_sev C A3 m3 _ HWc)) as (r7 & RUN7 & Z10 & Z11 & Z12 & Z1' & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWc)) | exact (mp_lazy _ (w_pure _ _ _ _ HWc)) | exact RUN7 |].
      assert (Z2' : getr r7 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      apply (returnErrorPtr_W C A3 m3 _ r7 (s - 32) (0x108f4 + dVLS_108f4) (0x1046c + dVLS_1046c) 28 15 (rl dVL_23878 0x23998) (Z_to_bv 64 0) S CK HWc Z2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Z1' ltac:(rl_ret_ok_VL)
               Z10 Z11 Z12 str_msg_datafail str_pixCreateNoInit).
      intros m4 r8 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
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
      apply (padbits_W C A A2 M3 _ r5 (s - 32) pix (set_data (pix_hdr w h d) data) (rl dVL_23878 0x238dc) S CK HW3 SUBb Y2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(rl_ret_ok_VL) Y10 Y11
               PX3 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl Lp2).
      { cbn. exact K1. } { cbn. exact LAd. } { cbn. exact K00. } { cbn. exact NEpd. }
      intros m5 r6 HW5 CS5 PM5 PX5 A10.
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

Lemma str_pixCreate : str16 (0x104e2 + dVLS_104e2) 9. Proof. rl_dbounds (dVLS_104e2 :: nil). str16_tac. Qed.

Theorem pixCreate_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix data, getr regs' 10 = Z_to_bv 64 pix /\ hdr_ok w h d /\ pixr_new C A A' m' pix data (set_data (pix_hdr w h d) data))) ->
     roomtr A (m_vmmaps md) A' vm' RK_pix RB_pix ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_237d4 0x237d4) m al_rom) md) S.
Proof. rl_dbounds (dVLS_103c3 :: dVLS_104e2 :: nil).
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pk_A al_rom regs m s ret ltac:(lia) ltac:(lia) SOK H2 H1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
  rewrite H10 in Q10. rewrite H11 in Q11. rewrite H12 in Q12.
  apply (pixCreateNoInit_W C A M1 md r1 (s - 16) w h d (rl dVL_237d4 0x237e4) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(rl_ret_ok_VL) Q4 Q10 Q11 Q12 Hw Hh Hwh Hd).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
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
    apply (returnErrorPtr_W C A1 m1 _ r3 s (0x103c3 + dVLS_103c3) (0x104e2 + dVLS_104e2) 13 9 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
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
    apply (memset_at (with_vmmaps vm1 md) r3 m1 al_rom data (4 * (wpl_of w d * h)) (rl dVL_237d4 0x23820) S
             (md_pure_with_vmmaps _ _ (w_pure _ _ _ _ HW)) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(rl_ret_ok_VL) V1 V10 V11 V12).
    intros r4 A10' AG4.
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

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptStderr O17LeptBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17CL7a.
Import O17CL7a.O17LeptErr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptCmap O17LeptCmapDeser.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17CL3a.
Import O17CL3a.O17MaxIndex.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17_code_132e8_14000 O17_code_14000_15000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section CmapValid.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  #[local] Definition FR5 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

  (* [comment removed for export] *)
  Lemma pv_A : forall regs m (s cm pv : Z) (cv : cmapv) (pix ret : word),
    (48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= 2 ^ 64)%Z -> CMAPat m cm cv ->
    (c_d cv = 1 \/ c_d cv = 2 \/ c_d cv = 4 \/ c_d cv = 8)%Z -> c_nalloc cv = (2 ^ c_d cv)%Z -> (1 <= c_n cv <= c_nalloc cv)%Z ->
    (1 <= c_arr cv)%Z -> (1 <= cm)%Z -> (cm + 24 <= s - 48)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = pix -> getr regs 12 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (0x146cc : word) m rom)
                  (mkst regs' (0x14734 : word) (wbytes (FR5 m s ret regs) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 (c_d cv) /\ getr regs' 18 = Z_to_bv 64 cm
      /\ getr regs' 13 = Z_to_bv 64 (c_nalloc cv) /\ getr regs' 14 = Z_to_bv 64 (c_n cv) /\ getr regs' 10 = Z_to_bv 64 1
      /\ getr regs' 11 = pix /\ getr regs' 12 = Z_to_bv 64 pv
      /\ regs_agree (fun r => In r [2; 8; 10; 13; 14; 18]%list) regs regs'.
  Proof.
    intros regs m s cm pv cv pix ret Hs Hpv Hpv64 CM Hd Hna Hn Harr Hcm Hcmhi SOK SOKp H2 H1 H10 H11 H12.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF). pose proof (cf_d _ CWF). pose proof (cf_nalloc _ CWF). pose proof (cf_n _ CWF).
    assert (Hpow : (2 <= 2 ^ c_d cv <= 256)%Z) by (destruct Hd as [E|[E|[E|E]]]; rewrite E; cbn; lia).
    unfold FR5. eexists. split.
    - zv F_145d0 D_145d0 (Z_to_bv 64 (s - 48)).
      stepST F_145d4 D_145d4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_145d8 D_145d8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_145dc D_145dc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_145e0 D_145e0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_145e4 D_145e4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_145e8 D_145e8 ltac:(condZ).
      stepST F_145ec D_145ec (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(sok_in SOKp).
      stepb_ft F_145f0 D_145f0 ltac:(condZ).
      stepLD F_145f4 D_145f4 (Z_to_le_bytes 8 (c_arr cv)) (Z_to_bv 64 (c_arr cv)) ltac:(addr_norm; repeat rdn_peel1; exact (CMAP_rd_arr SEGS _ _ _ CM)) ltac:(apply lez8; lia).
      stepb_ft F_145f8 D_145f8 ltac:(condZ).
      stepLD F_145fc D_145fc (Z_to_le_bytes 4 (c_d cv)) (Z_to_bv 64 (c_d cv)) ltac:(addr_norm; repeat rdn_peel1; exact (CMAP_rd_d SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_d cv)) by lia.
      sn F_14600 D_14600.
      stepb_ft F_14604 D_14604 ltac:(condZ).
      sn F_14608 D_14608. sn F_1460c D_1460c. sn F_14610 D_14610.
      stepb_ft F_14614 D_14614 ltac:(pin; apply cdepth_test_ok; exact Hd).
      sn F_14618 D_14618.
      stepLD F_1461c D_1461c (Z_to_le_bytes 4 (c_nalloc cv)) (Z_to_bv 64 (c_nalloc cv)) ltac:(addr_norm; repeat rdn_peel1; exact (CMAP_rd_nalloc SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_nalloc cv)) by lia.
      sn F_14620 D_14620.
      sn F_14624 D_14624. rewrite (sllw_1 _ Hd), <- Hna.
      stepb_ft F_14628 D_14628 ltac:(condZ).
      stepLD F_1462c D_1462c (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; repeat rdn_peel1; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepb_ft F_14630 D_14630 ltac:(condZ).
      stepb_ft F_14634 D_14634 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Definition pv_cells (m : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) : Prop :=
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v).

  (* [comment removed for export] *)
  Lemma pv_Z : forall regs m (s pv : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    pv_cells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (0x14734 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pv ret s0v s1v s2v s3v Hs Hpv Hpv64 Hret SOKp (R1 & R2 & R3 & R4 & R5) H2 H11 H12. eexists. split.
    - stepb_tk F_14638 D_14638 ltac:(condZ).
      sn F_14890 D_14890. sn F_14894 D_14894.
      stepST F_14898 D_14898 (Z_to_bv 64 pv) (Z_to_bv 64 1) ltac:(sok_in SOKp).
      sn F_1489c D_1489c.
      stepLD8 F_1471c D_1471c ret. stepLD8 F_14720 D_14720 s0v. stepLD8 F_14724 D_14724 s1v. stepLD8 F_14728 D_14728 s2v. stepLD8 F_1472c D_1472c s3v.
      zv F_14730 D_14730 (Z_to_bv 64 s). stepret F_14734 D_14734 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_B : forall regs m (pix pv : Z) (v : pixv),
    PIXat m pix v -> (4096 <= pix)%Z ->
    getr regs 11 = Z_to_bv 64 pix -> getr regs 12 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (0x14734 : word) m rom) (mkst regs' (0x14750 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_d v) /\ getr regs' 11 = Z_to_bv 64 9 /\ getr regs' 13 = Z_to_bv 64 (p_d v)
      /\ getr regs' 19 = Z_to_bv 64 pv /\ getr regs' 9 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 13; 19]%list) regs regs'.
  Proof.
    intros regs m pix pv v PX Hpix H11 H12. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF).
    eexists. split.
    - stepb_ft F_14638 D_14638 ltac:(condZ).
      sn F_1463c D_1463c. sn F_14640 D_14640. sn F_14644 D_14644. sn F_14648 D_14648.
      stepb_ft F_1417c D_1417c ltac:(condZ).
      stepLD F_14180 D_14180 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d v)) by lia.
      stepret F_14184 D_14184 (0x14748 : word) ltac:(bveq).
      sn F_1464c D_1464c. sn F_14650 D_14650. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_P1 : forall regs m (dp : Z),
    (9 <= dp < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) -> rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 9 -> getr regs 13 = Z_to_bv 64 dp ->
    exists regs',
      msteps SEGS (mkst regs (0x14750 : word) m rom) (mkst regs' (0x13a04 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x105f7 /\ getr regs' 11 = Z_to_bv 64 0x10415 /\ getr regs' 1 = Z_to_bv 64 0x148c8
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m dp Hdp Rg Rs H10 H11 H13. eexists. split.
    - stepb_ft F_14654 D_14654 ltac:(condZ).
      sn F_14658 D_14658.
      stepLD F_1465c D_1465c (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_14660 D_14660 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_14664 D_14664. stepb_ft F_14668 D_14668 ltac:(condZ).
      sn F_1466c D_1466c. sn F_14670 D_14670. sn F_14674 D_14674. sn F_14678 D_14678. sn F_1467c D_1467c. sn F_14680 D_14680.
      sn F_147c8 D_147c8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_P2 : forall regs m (dp d' : Z),
    (0 <= dp <= 8)%Z -> (0 <= d' < dp)%Z ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) -> rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 9 -> getr regs 13 = Z_to_bv 64 dp -> getr regs 8 = Z_to_bv 64 d' ->
    exists regs',
      msteps SEGS (mkst regs (0x14750 : word) m rom) (mkst regs' (0x13a04 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x106d6 /\ getr regs' 11 = Z_to_bv 64 0x10415 /\ getr regs' 1 = Z_to_bv 64 0x14890
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m dp d' Hdp Hd Rg Rs H10 H11 H13 H8. eexists. split.
    - stepb_tk F_14654 D_14654 ltac:(condZ).
      sn F_147d4 D_147d4. stepb_ft F_147d8 D_147d8 ltac:(condZ).
      sn F_147dc D_147dc.
      stepLD F_147e0 D_147e0 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_147e4 D_147e4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_147e8 D_147e8. stepb_ft F_147ec D_147ec ltac:(condZ).
      sn F_147f0 D_147f0. sn F_147f4 D_147f4. sn F_147f8 D_147f8. sn F_147fc D_147fc. sn F_14800 D_14800.
      sn F_1475c D_1475c. sn F_14760 D_14760. sn F_14764 D_14764. sn F_14790 D_14790. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_D : forall regs m (cm dp d' : Z) (cv : cmapv),
    (dp = 1 \/ dp = 2 \/ dp = 4 \/ dp = 8)%Z -> (dp <= d' < 2 ^ 31)%Z -> CMAPat m cm cv -> (1 <= c_n cv)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 9 -> getr regs 13 = Z_to_bv 64 dp -> getr regs 8 = Z_to_bv 64 d' -> getr regs 18 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (0x14750 : word) m rom) (mkst regs' (0x1490c : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (2 ^ dp) /\ getr regs' 12 = Z_to_bv 64 (c_n cv) /\ getr regs' 10 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [10; 12; 13]%list) regs regs'.
  Proof.
    intros regs m cm dp d' cv Hdp Hd CM Hn H10 H11 H13 H8 H18. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF).
    eexists. split.
    - stepb_tk F_14654 D_14654 ltac:(condZ).
      sn F_147d4 D_147d4. stepb_tk F_147d8 D_147d8 ltac:(condZ).
      stepLD F_14804 D_14804 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepb_ft F_14808 D_14808 ltac:(condZ).
      sn F_1480c D_1480c. rewrite (sllw_1 _ Hdp).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_P4 : forall regs m (k n : Z),
    (0 <= k < n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) -> rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 13 = Z_to_bv 64 k -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x1490c : word) m rom) (mkst regs' (0x13a04 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10883 /\ getr regs' 11 = Z_to_bv 64 0x10415 /\ getr regs' 1 = Z_to_bv 64 0x14890
      /\ regs_agree (fun r => In r [1; 10; 11; 14]%list) regs regs'.
  Proof.
    intros regs m k n Hk Hn Rg Rs H13 H12. eexists. split.
    - stepb_ft F_14810 D_14810 ltac:(condZ).
      sn F_14814 D_14814.
      stepLD F_14818 D_14818 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_1481c D_1481c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_14820 D_14820. sn F_14824 D_14824. stepb_ft F_14828 D_14828 ltac:(condZ).
      sn F_1482c D_1482c. sn F_14830 D_14830. sn F_14834 D_14834. sn F_14838 D_14838. sn F_1483c D_1483c.
      sn F_14790 D_14790. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_E : forall regs m (s pix k n : Z),
    (0 <= n <= k)%Z -> (k < 2 ^ 64)%Z -> (48 <= s)%Z ->
    getr regs 13 = Z_to_bv 64 k -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 9 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x1490c : word) m rom) (mkst regs' (0x14c88 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 (s - 44) /\ getr regs' 1 = Z_to_bv 64 0x1497c
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pix k n Hn Hk Hs H13 H12 H2 H9. eexists. split.
    - stepb_tk F_14810 D_14810 ltac:(condZ).
      zv F_14874 D_14874 (Z_to_bv 64 (s - 44)). sn F_14878 D_14878. sn F_1487c D_1487c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_G : forall regs m (s cm mx pv : Z) (cv : cmapv) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= 2 ^ 64)%Z -> ret_ok ret -> CMAPat m cm cv -> (0 <= mx < c_n cv)%Z -> (cm + 24 <= s - 48)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (Z_to_le_bytes 4 mx) -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    pv_cells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 18 = Z_to_bv 64 cm -> getr regs 19 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (0x1497c : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s cm mx pv cv ret s0v s1v s2v s3v Hs Hpv Hpv64 Hret CM Hmx Hcm Rmx SOKp (R1 & R2 & R3 & R4 & R5) H2 H18 H19.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF).
    eexists. split.
    - stepLD F_14880 D_14880 (Z_to_le_bytes 4 mx) (Z_to_bv 64 mx) ltac:(addr_norm; exact Rmx) ltac:(apply lez4; lia).
      rewrite (v_lw_small mx) by lia.
      stepLD F_14884 D_14884 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      sn F_14888 D_14888. stepb_ft F_1488c D_1488c ltac:(condZ).
      sn F_14890 D_14890. sn F_14894 D_14894.
      stepST F_14898 D_14898 (Z_to_bv 64 pv) (Z_to_bv 64 1) ltac:(sok_in SOKp).
      sn F_1489c D_1489c.
      stepLD8 F_1471c D_1471c ret. stepLD8 F_14720 D_14720 s0v. stepLD8 F_14724 D_14724 s1v. stepLD8 F_14728 D_14728 s2v. stepLD8 F_1472c D_1472c s3v.
      zv F_14730 D_14730 (Z_to_bv 64 s). stepret F_14734 D_14734 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_P5 : forall regs m (s cm mx : Z) (cv : cmapv),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> CMAPat m cm cv -> (c_n cv <= mx < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (Z_to_le_bytes 4 mx) ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) -> rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 18 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (0x1497c : word) m rom) (mkst regs' (0x13a04 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10739 /\ getr regs' 11 = Z_to_bv 64 0x10415 /\ getr regs' 1 = Z_to_bv 64 0x14890
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m s cm mx cv Hs Hs64 CM Hmx Rmx Rg Rs H2 H18. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF).
    eexists. split.
    - stepLD F_14880 D_14880 (Z_to_le_bytes 4 mx) (Z_to_bv 64 mx) ltac:(addr_norm; exact Rmx) ltac:(apply lez4; lia).
      rewrite (v_lw_small mx) by lia.
      stepLD F_14884 D_14884 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      sn F_14888 D_14888. stepb_tk F_1488c D_1488c ltac:(condZ).
      sn F_148a0 D_148a0.
      stepLD F_148a4 D_148a4 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_148a8 D_148a8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_148ac D_148ac. sn F_148b0 D_148b0. stepb_ft F_148b4 D_148b4 ltac:(condZ).
      sn F_148b8 D_148b8. sn F_148bc D_148bc. sn F_148c0 D_148c0. sn F_148c4 D_148c4. sn F_148c8 D_148c8.
      sn F_1478c D_1478c. sn F_14790 D_14790. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_T : forall (pc : Z) regs m (s : Z) (ret s0v s1v s2v s3v : word),
    (pc = 0x148c8 \/ pc = 0x14890)%Z -> (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pv_cells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 1
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros pc regs m s ret s0v s1v s2v s3v Hpc Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
    destruct Hpc as [-> | ->]; eexists; split.
    - replace (Z_to_bv 64 0x148c8) with (0x148c8 : word) by (apply bv_eq; reflexivity).
      sn F_147cc D_147cc. sn F_147d0 D_147d0.
      stepLD8 F_1471c D_1471c ret. stepLD8 F_14720 D_14720 s0v. stepLD8 F_14724 D_14724 s1v. stepLD8 F_14728 D_14728 s2v. stepLD8 F_1472c D_1472c s3v.
      zv F_14730 D_14730 (Z_to_bv 64 s). stepret F_14734 D_14734 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - replace (Z_to_bv 64 0x14890) with (0x14890 : word) by (apply bv_eq; reflexivity).
      sn F_14794 D_14794. sn F_14798 D_14798.
      stepLD8 F_1471c D_1471c ret. stepLD8 F_14720 D_14720 s0v. stepLD8 F_14724 D_14724 s1v. stepLD8 F_14728 D_14728 s2v. stepLD8 F_1472c D_1472c s3v.
      zv F_14730 D_14730 (Z_to_bv 64 s). stepret F_14734 D_14734 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
Definition frame5 (s : Z) (ret : word) (regs : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9); ((s - 32)%Z, getr regs 18); ((s - 40)%Z, getr regs 19)].

Lemma cells_FR5 : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FR5 m s ret regs) (frame5 s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frame5, FR5. cbn [cellsZ]. repeat split; rdn_solve. Qed.

(* [comment removed for export] *)
Definition cmap_ok (cv : cmapv) : Prop :=
  (c_d cv = 1 \/ c_d cv = 2 \/ c_d cv = 4 \/ c_d cv = 8)%Z /\ c_nalloc cv = (2 ^ c_d cv)%Z /\ (1 <= c_n cv <= c_nalloc cv)%Z /\ (1 <= c_arr cv)%Z.

(* [comment removed for export] *)
Definition pv_post (C : lctx) (A : AS) (s : Z) (m m' : word -> option byte) (pv valid : Z) : Prop :=
  POSTM C A s (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 valid))) m'.

(* [comment removed for export] *)
Lemma POSTM_store_same : forall C A s X M (a : word) bs0 bs,
  length bs0 = length bs -> (u a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  POSTM C A s (wbytes X a bs0) M -> POSTM C A s (wbytes X a bs) (wbytes M a bs).
Proof.
  intros C A s X M a bs0 bs Hlen Ha [F L]. split.
  - intros x N1 N2 N3 N4 N5.
    destruct (Z_lt_le_dec (u x) (u a)) as [B|B]; [rewrite !wbytes_outside by lia; rewrite <- (wbytes_outside bs0 X a x) by lia; exact (F x N1 N2 N3 N4 N5)|].
    destruct (Z_lt_le_dec (u x) (u a + Z.of_nat (length bs))) as [B2|B2]; [rewrite !wbytes_inside by lia; reflexivity|].
    rewrite !wbytes_outside by lia. rewrite <- (wbytes_outside bs0 X a x) by lia. exact (F x N1 N2 N3 N4 N5).
  - intros q k i Lq Hi.
    destruct (Z_lt_le_dec (u (at_ q i)) (u a)) as [B|B]; [rewrite !wbytes_outside by lia; rewrite <- (wbytes_outside bs0 X a (at_ q i)) by lia; exact (L q k i Lq Hi)|].
    destruct (Z_lt_le_dec (u (at_ q i)) (u a + Z.of_nat (length bs))) as [B2|B2]; [rewrite !wbytes_inside by lia; reflexivity|].
    rewrite !wbytes_outside by lia. rewrite <- (wbytes_outside bs0 X a (at_ q i)) by lia. exact (L q k i Lq Hi).
Qed.

Lemma POSTM_store_new : forall C A s X M (a : word) bs,
  (u a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  POSTM C A s X M -> POSTM C A s (wbytes X a bs) (wbytes M a bs).
Proof.
  intros C A s X M a bs Ha [F L]. split.
  - intros x N1 N2 N3 N4 N5.
    destruct (Z_lt_le_dec (u x) (u a)) as [B|B]; [rewrite !wbytes_outside by lia; exact (F x N1 N2 N3 N4 N5)|].
    destruct (Z_lt_le_dec (u x) (u a + Z.of_nat (length bs))) as [B2|B2]; [rewrite !wbytes_inside by lia; reflexivity|].
    rewrite !wbytes_outside by lia. exact (F x N1 N2 N3 N4 N5).
  - intros q k i Lq Hi.
    destruct (Z_lt_le_dec (u (at_ q i)) (u a)) as [B|B]; [rewrite !wbytes_outside by lia; exact (L q k i Lq Hi)|].
    destruct (Z_lt_le_dec (u (at_ q i)) (u a + Z.of_nat (length bs))) as [B2|B2]; [rewrite !wbytes_inside by lia; reflexivity|].
    rewrite !wbytes_outside by lia. exact (L q k i Lq Hi).
Qed.

Theorem pixcmapIsValid_null_W : forall C A m md regs (s cm pv : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 pv ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> pv_post C A s m m' pv 1 -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x146cc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s cm pv cv ret S CK HW H2 Hs16 Hlo Hpv Hpvhi H1 Hret H10 H11 H12 CM (Hd & Hna & Hn & Harr) Lcm HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *.
  pose proof CM as (Hc0 & Hc64 & CWF & _).
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (W_sok_win C A m md pv 4 CK HW ltac:(lia) ltac:(cbn; lia)) as SOKp.
  destruct (pv_A al_rom regs m s cm pv cv (Z_to_bv 64 0) ret ltac:(lia) Hpv ltac:(lia) CM Hd Hna Hn Harr ltac:(lia) ltac:(lia) SOK SOKp H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q8 & Q18 & Q13 & Q14 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR5 m s ret regs) md /\ POSTM C A s m (FR5 m s ret regs)) by (unfold FR5; wp_win CK).
  destruct WP1 as [HW1 PM1].
  set (M1 := wbytes (FR5 m s ret regs) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) in RUN1 |- *.
  assert (HW2 : W C A M1 md) by (subst M1; apply (W_store_win C A _ md _ _ CK HW1); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
  assert (PM2 : pv_post C A s m M1 pv 0).
  { subst M1. apply POSTM_store_new; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | exact PM1]. }
  assert (CE1 : cellsZ M1 (frame5 s ret regs)).
  { subst M1. eapply (cellsZ_out _ _ pv (pv + 4)).
    - intros x Hx. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - unfold frame5. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil.
    - apply cells_FR5; lia. }
  unfold frame5 in CE1. cbn [cellsZ] in CE1. destruct CE1 as (C1 & C2 & C3 & C4 & C5 & _).
  destruct (pv_Z al_rom r1 M1 s pv ret _ _ _ _ ltac:(lia) Hpv ltac:(lia) Hret
              (W_sok_win C A M1 md pv 4 CK HW2 ltac:(lia) ltac:(cbn; lia))
              (conj C1 (conj C2 (conj C3 (conj C4 C5)))) Q2 Q11 Q12)
    as (r2 & RUN2 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN2 |].
  apply (HK _ r2).
  - apply (W_store_win C A _ md _ _ CK HW2); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
  - apply cs_kept_intro; csr; reflexivity.
  - eapply (POSTM_store_same C A s m M1); [| | exact PM2]; [rewrite !length_N_to_le_bytes; reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
  - exact V10.
Qed.

Lemma str_pixcmapIsValid : str16 0x10415 14. Proof. str16_tac. Qed.
Lemma str_pv_d8 : str16 0x105f7 30. Proof. str16_tac. Qed.
Lemma str_pv_dd : str16 0x106d6 50. Proof. str16_tac. Qed.
Lemma str_pv_ent : str16 0x10883 57. Proof. str16_tac. Qed.
Lemma str_pv_max : str16 0x10739 76. Proof. str16_tac. Qed.

#[local] Definition pv_rest : list (bv 5) := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma pv_msg_W : forall C A m M md regs r (s pv fmt retpc : Z) kf (ret : word) (S : TSet),
  Cok C -> W C A M md -> pv_post C A s m M pv 0 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  cellsZ M (frame5 s ret regs) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 1 = Z_to_bv 64 retpc -> (retpc = 0x148c8 \/ retpc = 0x14890)%Z ->
  getr r 10 = Z_to_bv 64 fmt -> getr r 11 = Z_to_bv 64 0x10415 ->
  (forall x, In x pv_rest -> getr r x = getr regs x) ->
  In fmt (SSP.ls_fmts1 L17) -> str16 fmt kf ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     (exists valid, (valid = 0 \/ valid = 1)%Z /\ pv_post C A s m m' pv valid /\ getr regs' 10 = Z_to_bv 64 (1 - valid)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (0x13a04 : word) M al_rom) md) S.
Proof.
  intros C A m M md regs r s pv fmt retpc kf ret S CK HW PM Hs16 Hlo Hhi Hret CE R2 R1 Hrp R10 R11 RR Hin Sf HK H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold LSF in *.
  assert (RETOK : ret_ok (Z_to_bv 64 retpc)) by (destruct Hrp as [-> | ->]; red; apply bv_eq; reflexivity).
  apply (lept_stderr1_W C A M md r (s - 48) fmt 0x10415 kf 14 (Z_to_bv 64 retpc) S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) R1 RETOK
           R10 R11 Hin Sf str_pixcmapIsValid).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (PM2 : pv_post C A s m m2 pv 0).
  { eapply POSTM_trans; [exact PM|]. eapply (POSTM_range C A M md m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia]. }
  assert (CE2 : cellsZ m2 (frame5 s ret regs)).
  { eapply (cellsZ_out M m2 (s - 48 - 3376) (s - 48)); [exact OUT2 | | exact CE].
    unfold frame5. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  unfold frame5 in CE2. cbn [cellsZ] in CE2. destruct CE2 as (C1 & C2 & C3 & C4 & C5 & _).
  destruct (pv_T al_rom retpc r2 m2 s ret _ _ _ _ Hrp ltac:(lia) ltac:(lia) Hret (conj C1 (conj C2 (conj C3 (conj C4 C5)))) ltac:(csr; reflexivity))
    as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  apply (HK m2 r3 HW2).
  - apply cs_kept_intro; unfold pv_rest in RR; csr; reflexivity.
  - exists 0%Z. split; [lia|]. split; [exact PM2 | exact V10].
Qed.

Theorem pixcmapIsValid_pix_W : forall C A m md regs (s cm pix pv : Z) (cv : cmapv) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 pix -> getr regs 12 = Z_to_bv 64 pv ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z ->
  PIXat m pix v -> live A (Z_to_bv 64 pix) = Some 64%Z ->
  dval (p_d v) -> (1 <= p_w v <= 20000)%Z -> (1 <= p_h v <= 20000)%Z -> p_wpl v = wpl_of (p_w v) (p_d v) ->
  live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     (exists valid, (valid = 0 \/ valid = 1)%Z /\ pv_post C A s m m' pv valid /\ getr regs' 10 = Z_to_bv 64 (1 - valid)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x146cc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s cm pix pv cv v ret S CK HW H2 Hs16 Hlo Hpv Hpvhi H1 Hret H10 H11 H12 CM CMOK Lcm PX Lp DV Hw Hh Hwpl Ld HK.
  pose proof CMOK as (Hd & Hna & Hn & Harr).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold LSF in *.
  pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat.
  pose proof (dval_range _ DV) as Hd32. pose proof (wpl_of_range (p_w v) (p_d v) ltac:(lia) DV) as Hwr. rewrite <- Hwpl in Hwr.
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) _ CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (W_sok_win C A m md pv 4 CK HW ltac:(lia) ltac:(cbn; lia)) as SOKp.
  destruct (pv_A al_rom regs m s cm pv cv (Z_to_bv 64 pix) ret ltac:(lia) Hpv ltac:(lia) CM Hd Hna Hn Harr ltac:(lia) ltac:(lia) SOK SOKp H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q8 & Q18 & Q13 & Q14 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR5 m s ret regs) md /\ POSTM C A s m (FR5 m s ret regs)) by (unfold FR5; wp_win CK).
  destruct WP1 as [HW1 PM1].
  set (M1 := wbytes (FR5 m s ret regs) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) in RUN1 |- *.
  assert (HW2 : W C A M1 md) by (subst M1; apply (W_store_win C A _ md _ _ CK HW1); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
  assert (PM2 : pv_post C A s m M1 pv 0).
  { subst M1. apply POSTM_store_new; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | exact PM1]. }
  assert (CE1 : cellsZ M1 (frame5 s ret regs)).
  { subst M1. eapply (cellsZ_out _ _ pv (pv + 4)).
    - intros x Hx. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - unfold frame5. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil.
    - apply cells_FR5; lia. }
  assert (PX1 : PIXat M1 pix v).
  { subst M1. unfold FR5. repeat (apply PIXat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (CM1 : CMAPat M1 cm cv).
  { subst M1. unfold FR5. repeat (apply CMAPat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact CM. }
  assert (RR1 : forall x, In x pv_rest -> getr r1 x = getr regs x) by (unfold pv_rest; rest_solve).
  (* [comment removed for export] *)
  destruct (pv_B al_rom r1 M1 pix pv v PX1 Gp Q11 Q12) as (r2 & RUN2 & V10 & V11 & V13 & V19 & V9 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN2 |].
  assert (RR2 : forall x, In x pv_rest -> getr r2 x = getr regs x) by (unfold pv_rest; rest_solve).
  destruct (Z_lt_ge_dec 8 (p_d v)) as [DBIG|DSMALL].
  { (* [comment removed for export] *)
    destruct (pv_P1 al_rom r2 M1 (p_d v) ltac:(lia) (W_sev_got C A M1 md HW2) (W_sev C A M1 md HW2) V10 V11 V13) as (r3 & RUN3 & U10 & U11 & U1 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    apply (pv_msg_W C A m M1 md regs r3 s pv 0x105f7 0x148c8 30 ret S CK HW2 PM2 Hs16 ltac:(unfold LSF; lia) ltac:(lia) Hret CE1
             ltac:(csr; reflexivity) U1 ltac:(left; reflexivity) U10 U11 ltac:(unfold pv_rest; rest_solve)
             ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right]); fail) str_pv_d8 HK H2). }
  assert (Hdp4 : (p_d v = 1 \/ p_d v = 2 \/ p_d v = 4 \/ p_d v = 8)%Z) by (unfold dval in DV; lia).
  assert (E8 : getr r2 8 = Z_to_bv 64 (c_d cv)) by (csr; reflexivity).
  pose proof (cf_d _ CWF) as Hcd. pose proof (cf_n _ CWF) as Hcn.
  destruct (Z_lt_ge_dec (c_d cv) (p_d v)) as [P2|Dok].
  { (* [comment removed for export] *)
    destruct (pv_P2 al_rom r2 M1 (p_d v) (c_d cv) ltac:(lia) ltac:(lia) (W_sev_got C A M1 md HW2) (W_sev C A M1 md HW2) V10 V11 V13 E8) as (r3 & RUN3 & U10 & U11 & U1 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    apply (pv_msg_W C A m M1 md regs r3 s pv 0x106d6 0x14890 50 ret S CK HW2 PM2 Hs16 ltac:(unfold LSF; lia) ltac:(lia) Hret CE1
             ltac:(csr; reflexivity) U1 ltac:(right; reflexivity) U10 U11 ltac:(unfold pv_rest; rest_solve)
             ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right]); fail) str_pv_dd HK H2). }
  assert (E18 : getr r2 18 = Z_to_bv 64 cm) by (csr; reflexivity).
  destruct (pv_D al_rom r2 M1 cm (p_d v) (c_d cv) cv Hdp4 ltac:(lia) CM1 ltac:(lia) V10 V11 V13 E8 E18) as (r3 & RUN3 & U13 & U12 & U10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  assert (RR3 : forall x, In x pv_rest -> getr r3 x = getr regs x) by (unfold pv_rest; rest_solve).
  assert (Hpow : (2 <= 2 ^ p_d v <= 256)%Z) by (destruct Hdp4 as [E|[E|[E|E]]]; rewrite E; cbn; lia).
  destruct (Z_lt_ge_dec (2 ^ p_d v) (c_n cv)) as [P4|Nok].
  { (* [comment removed for export] *)
    destruct (pv_P4 al_rom r3 M1 (2 ^ p_d v) (c_n cv) ltac:(lia) ltac:(lia) (W_sev_got C A M1 md HW2) (W_sev C A M1 md HW2) U13 U12) as (r4 & RUN4 & Y10 & Y11 & Y1 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
    apply (pv_msg_W C A m M1 md regs r4 s pv 0x10883 0x14890 57 ret S CK HW2 PM2 Hs16 ltac:(unfold LSF; lia) ltac:(lia) Hret CE1
             ltac:(csr; reflexivity) Y1 ltac:(right; reflexivity) Y10 Y11 ltac:(unfold pv_rest; rest_solve)
             ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right]); fail) str_pv_ent HK H2). }
  (* [comment removed for export] *)
  destruct (pv_E al_rom r3 M1 s pix (2 ^ p_d v) (c_n cv) ltac:(lia) ltac:(lia) ltac:(lia) U13 U12 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r4 & RUN4 & Y10 & Y11 & Y1 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
  assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  destruct (blk_rdn C A M1 md (Z_to_bv 64 (p_data v)) _ (p_data v) (Z.to_nat (4 * (p_wpl v * p_h v))) CK HW2 Ld ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)) as [rbs Hrbs].
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof (W_sok_win C A M1 md (s - 48 - 144) 144 CK HW2 ltac:(lia) ltac:(cbn; lia)) as SOKf.
  pose proof (W_sok_win C A M1 md (s - 44) 4 CK HW2 ltac:(lia) ltac:(cbn; lia)) as SOKq.
  pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh. pose proof (wf_d _ WF) as Rd. pose proof (wf_wpl _ WF) as Rwpl.
  assert (PRE : SSP.spec_pre SEGS (SSP.spec_maxindex 0x14c88 144) [pix; s - 44; p_w v; p_h v; p_d v; p_wpl v; p_data v]%Z r4 M1).
  { unfold SSP.spec_maxindex. SSP.spec_unfold. cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
    rewrite Y10, Y11, Y2, Y1. rewrite !u_Z2bv by lia. rewrite !Z.add_0_r.
    split; [|split; [|split]].
    - split; [split; [reflexivity | lia]|]. split; [lia|].
      split; [split; [lia | rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]]|].
      split; [split; [reflexivity | lia]|]. split; [lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_w SEGS M1 pix v PX1)]]]|]. split; [lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_h SEGS M1 pix v PX1)]]]|]. split; [lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_d SEGS M1 pix v PX1)]]]|].
      split; [cbn [In]; lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_wpl SEGS M1 pix v PX1)]]]|].
      split; [rewrite Hwpl; reflexivity|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_data SEGS M1 pix v PX1)]]]|]. split; [lia|].
      split; [split; [lia | rewrite <- (Z.add_0_r (p_data v)); apply mod16_plus_mod4; [exact ALd | reflexivity]]|].
      split; [split; [unfold SSP.flatZ; lia | exists rbs; exact Hrbs]|]. split; [lia|].
      split; [split; [unfold SSP.flatZ; lia | exact SOKq]|].
      split; [split; [lia | replace (s - 44)%Z with (s + (-44))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]]|].
      split; [right; lia|].
      split; [split; [lia | rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity]|]. split; exact I.
    - split; [lia|]. split; [unfold SSP.flatZ; lia|]. split; [exact SOKf|]. split; [cbn; lia|]. split; [unfold SSP.flatZ; cbn; lia | exact I].
    - split; [|exact I]. split; [left; cbn; lia|]. split; [left; cbn; lia|]. split; [left; cbn; lia|]. split; [left; cbn; lia|].
      split; [left; cbn; lia|]. split; [left; lia|]. split; [right; lia | exact I].
    - red. apply bv_eq. reflexivity. }
  pose proof (maxindex_contract (fx:=fx)) as CT. unfold SSP.sum_contract in CT.
  destruct (CT [pix; s - 44; p_w v; p_h v; p_d v; p_wpl v; p_data v]%Z r4 M1 al_rom eq_refl PRE) as (outs & R' & M' & Hlen & RUN & POST).
  destruct outs as [|mx [|? ?]]; try discriminate Hlen. clear Hlen.
  unfold SSP.spec_maxindex in POST. SSP.spec_unfold_in POST.
  cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_maxindex app] in RUN, POST.
  destruct POST as (KEPT & _ & FRMx & GR & (_ & CELL & _) & Hmx & _).
  rewrite Y2, u_Z2bv in FRMx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul] in FRMx, CELL. rewrite !Z.add_0_r in FRMx, CELL.
  destruct CELL as [_ Rmx]. rewrite Z.mod_small in Rmx by lia.
  assert (OUT : forall x : word, ~ (s - 48 - 144 <= u x < s - 40)%Z -> M' x = M1 x).
  { intros x Hx. apply FRMx. split; [lia | split; [lia | exact I]]. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | |].
  { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 0x14c88) by (apply bv_eq; reflexivity) end. exact RUN. }
  rewrite Y1. replace (Z_to_bv 64 0x1497c) with (0x1497c : word) by (apply bv_eq; reflexivity).
  destruct KEPT as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & _).
  assert (HW3 : W C A M' md).
  { apply (W_mod_local C A M1 M' md CK HW2).
    - intros a Ha. left. unfold win. destruct (Z_lt_ge_dec (u a) (s - 48 - 144)); [exfalso; apply Ha; apply OUT; lia|].
      destruct (Z_lt_ge_dec (u a) (s - 40)); [lia|]. exfalso; apply Ha; apply OUT; lia.
    - exact GR.
    - intros a Ha. destruct (Z_lt_ge_dec (u a) (s - 48 - 144)); [rewrite OUT in Ha by lia; exact Ha|].
      destruct (Z_lt_ge_dec (u a) (s - 40)); [|rewrite OUT in Ha by lia; exact Ha]. apply (w_win _ _ _ _ HW2). unfold win. lia. }
  assert (PM3 : pv_post C A s m M' pv 0).
  { eapply POSTM_trans; [exact PM2|]. eapply (POSTM_range C A M1 md M'); [exact CK | exact HW2 | exact OUT | lia | lia | lia]. }
  assert (CE3 : cellsZ M' (frame5 s ret regs)).
  { eapply (cellsZ_out M1 M' (s - 48 - 144) (s - 40)); [exact OUT | | exact CE1].
    unfold frame5. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (CM3 : CMAPat M' cm cv) by (apply (CMAPat_frame M1 M' cm cv CM1); intros x Hx; apply OUT; lia).
  assert (Z2 : getr R' 2 = Z_to_bv 64 (s - 48)) by (rewrite K2; exact Y2).
  assert (Z18 : getr R' 18 = Z_to_bv 64 cm) by (csr; reflexivity).
  assert (Z19 : getr R' 19 = Z_to_bv 64 pv) by (csr; reflexivity).
  assert (RR4 : forall x, In x pv_rest -> getr r4 x = getr regs x) by (unfold pv_rest; rest_solve).
  destruct (Z_lt_ge_dec mx (c_n cv)) as [OKmx|BAD].
  - (* [comment removed for export] *)
    pose proof CE3 as CE4. unfold frame5 in CE4. cbn [cellsZ] in CE4. destruct CE4 as (C1 & C2 & C3 & C4 & C5 & _).
    destruct (pv_G al_rom R' M' s cm mx pv cv ret _ _ _ _ ltac:(lia) Hpv ltac:(lia) Hret CM3 ltac:(lia) ltac:(lia) Rmx
                (W_sok_win C A M' md pv 4 CK HW3 ltac:(lia) ltac:(cbn; lia)) (conj C1 (conj C2 (conj C3 (conj C4 C5)))) Z2 Z18 Z19)
      as (r5 & RUN5 & V2' & V1' & V10' & V8' & V9' & V18' & V19' & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (HK _ r5).
    + apply (W_store_win C A _ md _ _ CK HW3); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    + apply cs_kept_intro; unfold pv_rest in RR4; csr; reflexivity.
    + exists 1%Z. split; [lia|]. split; [| exact V10'].
      eapply (POSTM_store_same C A s m M'); [| | exact PM3]; [rewrite !length_N_to_le_bytes; reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
  - (* [comment removed for export] *)
    destruct (pv_P5 al_rom R' M' s cm mx cv ltac:(lia) ltac:(lia) CM3 ltac:(lia) Rmx (W_sev_got C A M' md HW3) (W_sev C A M' md HW3) Z2 Z18)
      as (r5 & RUN5 & V10' & V11' & V1' & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (pv_msg_W C A m M' md regs r5 s pv 0x10739 0x14890 76 ret S CK HW3 PM3 Hs16 ltac:(unfold LSF; lia) ltac:(lia) Hret CE3
             ltac:(csr; reflexivity) V1' ltac:(right; reflexivity) V10' V11' ltac:(unfold pv_rest in RR4 |- *; rest_solve)
             ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right]); fail) str_pv_max HK H2).
Qed.



Section Segs2.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma sc_A : forall regs m (s pix cm : Z) (v : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_cmap v = 0%Z -> (1 <= pix)%Z -> (pix + 64 <= s - 48)%Z -> (1 <= cm < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (0x14154 : word) m rom)
                  (mkst regs' (0x146cc : word)
                     (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                        (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                        (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
                        (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                        (Z_to_bv 64 (pix + 48)) (word_to_le_bytes 8 (Z_to_bv 64 cm))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x141a4 /\ getr regs' 10 = Z_to_bv 64 cm
      /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 36)
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pix cm v ret Hs Hs64 PX Hcm0 Hpix Hpixhi Hcm SOK SOKx H2 H1 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - zv F_14058 D_14058 (Z_to_bv 64 (s - 48)).
      stepST F_1405c D_1405c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14060 D_14060 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14064 D_14064 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_14068 D_14068 ltac:(condZ).
      stepb_ft F_1406c D_1406c ltac:(condZ).
      stepLD F_14070 D_14070 (Z_to_le_bytes 8 (p_cmap v)) (Z_to_bv 64 (p_cmap v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      rewrite Hcm0.
      stepST F_14074 D_14074 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_14078 D_14078 ltac:(condZ).
      stepST F_14094 D_14094 (Z_to_bv 64 (pix + 48)) (Z_to_bv 64 cm) ltac:(sok_in SOKx).
      zv F_14098 D_14098 (Z_to_bv 64 (s - 36)).
      sn F_1409c D_1409c. sn F_140a0 D_140a0.
      sn F_140a4 D_140a4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_B : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs',
      msteps SEGS (mkst regs (0x141a4 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret Rv R1 R2 R3 H2. eexists. split.
    - stepLD F_140a8 D_140a8 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_ft F_140ac D_140ac ltac:(condZ).
      sn F_140b0 D_140b0. sn F_140b4 D_140b4.
      stepLD8 F_14128 D_14128 ret. stepLD8 F_1412c D_1412c s0v. stepLD8 F_14130 D_14130 s1v.
      zv F_14134 D_14134 (Z_to_bv 64 s). stepret F_14138 D_14138 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs2.

(* [comment removed for export] *)
Lemma POSTM_absorb : forall C Ar A M md m2 (s s' : Z) (a : word) bs, Cok C -> W C A M md -> sub_live Ar A ->
  (s' <= s)%Z -> (c_top C - LSTK <= u a)%Z -> (u a + Z.of_nat (length bs) <= s)%Z -> (s <= c_top C)%Z ->
  POSTM C A s' (wbytes M a bs) m2 -> POSTM C Ar s M m2.
Proof.
  intros C Ar A M md m2 s s' a bs CK HW SUB Hss Hlo Hhi Hs [F L]. pose proof CK as [T1 T2 T3 T4 T5]. laypins. split.
  - intros x N1 N2 N3 N4 N5. rewrite (F x N1 N2 N3 N4 ltac:(unfold scratch in *; lia)). apply wbytes_outside; [lia|]. unfold scratch in N5. lia.
  - intros q k i Lq Hi. pose proof (SUB q k Lq) as LqA. rewrite (L q k i LqA Hi).
    assert (RR : (u q <= u (at_ q i) < u q + k)%Z).
    { unfold at_. pose proof (alloc_top_lt (m_vmmaps md)) as AT. unfold two_pow_64 in AT.
      pose proof (ai_live_hull A M (m_vmmaps md) q k (w_inv _ _ _ _ HW) LqA) as (Hk0 & _ & TOP & _). pose proof (round16_ge k Hk0).
      rewrite u_Z2bv by (pose proof (u64_range q); lia). lia. }
    destruct (blk_byte C A M md q k (at_ q i) CK HW LqA RR) as (_ & _ & _ & NW & _).
    apply wbytes_outside; [lia|]. unfold win in NW. lia.
Qed.

Theorem pixSetColormap_W : forall C Ar A m md regs (s pix cm : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 cm ->
  PIXat m pix v -> p_cmap v = 0%Z ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live Ar (Z_to_bv 64 pix) = None -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> Z_to_bv 64 pix <> Z_to_bv 64 cm ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      PIXat m' pix (set_cmap v cm) -> CMAPat m' cm cv -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14154 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix cm v cv ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 PX Hpc Lp LpR Lp0 CM CMOK Lcm NE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof CM as (Hc0 & Hc64 & CWF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
  assert (DISJ : (pix + 64 <= cm \/ cm + 24 <= pix)%Z).
  { destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Lcm NE) as [X|X]; rewrite !u_Z2bv in X by lia;
      [left; pose proof (round16_ge 64 ltac:(lia)); lia | right; pose proof (round16_ge 24 ltac:(lia)); lia]. }
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (SOKx : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix _ x PX ltac:(lia) E). }
  destruct (sc_A al_rom regs m s pix cm v ret ltac:(lia) ltac:(lia) PX Hpc ltac:(lia) ltac:(lia) ltac:(lia) SOK SOKx H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) (Z_to_bv 64 (s - 32)) _).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C Ar s m M0).
  { subst M0. wp_win CK. }
  destruct (WP_blk C Ar A m M0 md (Z_to_bv 64 pix) (Z_to_bv 64 (pix + 48)) 64 (word_to_le_bytes 8 (Z_to_bv 64 cm)) s CK WP0 Lp LpR Lp0 SUB
              ltac:(rewrite !u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia)) as [HW1 PM1].
  fold M1 in HW1, PM1. destruct WP0 as [HW0 PM0].
  assert (PX1 : PIXat M1 pix (set_cmap v cm)).
  { subst M1. apply PIX_wr_cmap; [|lia]. subst M0. repeat (apply PIXat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (CM1 : CMAPat M1 cm cv).
  { subst M1 M0. repeat (apply CMAPat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact CM. }
  apply (pixcmapIsValid_null_W C A M1 md r1 (s - 48) cm (s - 36) cv (Z_to_bv 64 0x141a4) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 CM1 CMOK Lcm).
  intros m2 r2 HW2 CS2 PV2 A10.
  replace (Z_to_bv 64 0x141a4) with (0x141a4 : word) by (apply bv_eq; reflexivity).
  pose proof PV2 as [F2 L2].
  assert (Rv : rdn SEGS m2 (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1)).
  { rewrite (FRM_rdn16 C (s - 48) _ m2 (s - 36) 4 CK F2) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (CE : cellsZ m2 [((s - 8)%Z, ret); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9)]).
  { apply (cellsZ_frm C (s - 48) _ m2 _ CK F2 ltac:(lia)); [repeat (apply Forall_cons; [cbn [fst snd]; lia |]); apply Forall_nil|].
    eapply (cellsZ_out M1 _ (s - 36) (s - 32)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
      | repeat (apply Forall_cons; [cbn [fst snd]; lia |]); apply Forall_nil |].
    subst M1 M0. cbn [cellsZ]. repeat split; rdn_solve. }
  cbn [cellsZ] in CE. destruct CE as (C1 & C2 & C3 & _).
  destruct (sc_B al_rom r2 m2 s ret _ _ ltac:(lia) ltac:(lia) Hret Rv C1 C2 C3 ltac:(csr; reflexivity))
    as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (EQb : forall (p n : Z) (x : word), live A (Z_to_bv 64 p) = Some n -> (0 <= p)%Z -> (p + n <= alloc_top (c_vm C))%Z ->
            (p <= u x < p + n)%Z -> m2 x = M1 x).
  { intros p n x L G0 TP Hx. pose proof (L2 (Z_to_bv 64 p) n (u x - p)%Z L ltac:(lia)) as E.
    replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
    rewrite E. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  apply (HK m2 r3 HW2).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1|].
    unshelve (eapply (POSTM_absorb C Ar A M1 md m2 s (s - 48) _ _ CK HW1 SUB ltac:(lia) _ _ Hhi PV2)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
  - apply (PIXat_frame M1 m2 pix _ PX1). intros x Hx. exact (EQb pix 64%Z x Lp ltac:(lia) TOPp Hx).
  - apply (CMAPat_frame M1 m2 cm _ CM1). intros x Hx. exact (EQb cm 24%Z x Lcm ltac:(lia) TOPc Hx).
  - exact V10.
Qed.


End CmapValid.

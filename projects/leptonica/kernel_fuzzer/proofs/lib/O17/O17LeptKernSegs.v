(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptStderr O17LeptBase O17_code_132e8_14000 O17_code_14000_15000 O17_code_15000_16000.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Lemma or_2_2 : v_or (Z_to_bv 64 2) (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section KernSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Definition KF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) (w h d : Z) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 44)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 52)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 44)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
      (Z_to_bv 64 (s - 52)) (word_to_le_bytes 4 (Z_to_bv 64 d)).

  Lemma KF_out : forall m s ret regs w h d (x : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 64 <= u x < s)%Z -> KF m s ret regs w h d x = m x.
  Proof.
    intros m s ret regs w h d x Hs Hs64 N1. unfold KF.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition kcells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) (w h : Z) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
    rdn SEGS M (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
    rdn SEGS M (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)).

  Lemma kcells_KF : forall m s ret regs w h d, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    kcells (KF m s ret regs w h d) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) w h.
  Proof.
    intros m s ret regs w h d Hs Hs64. unfold kcells, KF. repeat split; rdn_chain.
  Qed.

  Lemma kcells_frame : forall M M' s ret s0v s1v s2v s3v w h, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    kcells M s ret s0v s1v s2v s3v w h -> (forall x : word, (s - 48 <= u x < s)%Z -> M' x = M x) -> kcells M' s ret s0v s1v s2v s3v w h.
  Proof.
    intros M M' s ret s0v s1v s2v s3v w h Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6 & C7) E.
    unfold kcells. repeat split;
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5 | rewrite <- C6 | rewrite <- C7];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_A : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (0x20560 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> (4096 <= pix)%Z -> (pix + 64 <= s - 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 2 -> getr regs 12 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x158e8 : word) m rom) (mkst regs' (0x15928 : word) (KF m s ret regs (p_w v) (p_h v) (p_d v)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = Z_to_bv 64 pix /\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 2
      /\ getr regs' 10 = Z_to_bv 64 (p_d v) /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12; 13; 14; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 PX Gp Hpix SOK H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF). pose proof (wf_d _ WF).
    eexists. split.
    - zv F_157ec D_157ec (Z_to_bv 64 (s - 64)).
      stepST F_157f0 D_157f0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_157f4 D_157f4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_157f8 D_157f8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_157fc D_157fc (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_15800 D_15800 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_15804 D_15804 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15808 D_15808. sn F_1580c D_1580c. sn F_15810 D_15810.
      zv F_15814 D_15814 (Z_to_bv 64 (s - 44)). zv F_15818 D_15818 (Z_to_bv 64 (s - 48)). zv F_1581c D_1581c (Z_to_bv 64 (s - 52)).
      sn F_15820 D_15820.
      (* [comment removed for export] *)
      stepb_ft F_13fd8 D_13fd8 ltac:(condZ).
      stepST F_13fdc D_13fdc (Z_to_bv 64 (s - 44)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_13fe0 D_13fe0 ltac:(condZ).
      stepST F_13fe4 D_13fe4 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_13fe8 D_13fe8 ltac:(condZ).
      stepST F_13fec D_13fec (Z_to_bv 64 (s - 52)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_13ff0 D_13ff0 ltac:(condZ).
      stepb_ft F_13ff4 D_13ff4 ltac:(condZ).
      stepLD F_13ff8 D_13ff8 (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_13ffc D_13ffc (Z_to_bv 64 (s - 44)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_14000 D_14000 ltac:(condZ).
      stepLD F_14004 D_14004 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_14008 D_14008 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      sn F_1400c D_1400c.
      stepb_ft F_14010 D_14010 ltac:(condZ).
      stepLD F_14014 D_14014 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d v)) by lia.
      stepST F_14018 D_14018 (Z_to_bv 64 (s - 52)) (Z_to_bv 64 (p_d v)) ltac:(sok_in SOK).
      sn F_1401c D_1401c.
      stepret F_14020 D_14020 (0x15920 : word) ltac:(bveq).
      stepLD F_15824 D_15824 (word_to_le_bytes 4 (Z_to_bv 64 (p_d v))) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_d v)) by lia.
      sn F_15828 D_15828.
      unfold KF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_B : forall regs m (s w h : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= w < 2 ^ 31)%Z -> (3 <= h < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 8 -> getr regs 11 = Z_to_bv 64 8 ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x15928 : word) m rom) (mkst regs' (0x15528 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x15948 /\ getr regs' 10 = Z_to_bv 64 h /\ getr regs' 11 = Z_to_bv 64 w
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s w h Hs Hs64 Hw Hh Rw Rh H2 H10 H11 H18 H19. eexists. split.
    - stepb_ft F_1582c D_1582c ltac:(condZ).                                          (* [comment removed for export] *)
      stepat F_15830 D_15830 (Z_to_bv 64 2) ltac:(gres; pin; imm_norm; exact or_2_2).  (* [comment removed for export] *)
      stepb_ft F_15834 D_15834 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_15838 D_15838 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      stepb_ft F_1583c D_1583c ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_15840 D_15840 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      stepb_ft F_15844 D_15844 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15848 D_15848.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_Bd : forall regs m (s d : Z),
    (0 <= d < 2 ^ 31)%Z -> d <> 8%Z ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) ->
    rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 8 ->
    exists regs',
      msteps SEGS (mkst regs (0x15928 : word) m rom) (mkst regs' (0x13aa0 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x159f4
      /\ getr regs' 10 = Z_to_bv 64 0x10ba0 /\ getr regs' 11 = Z_to_bv 64 0x10b17 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s d Hd NE Rg Rs H2 H10 H11. eexists. split.
    - stepb_tk F_1582c D_1582c ltac:(condZ).
      sn F_158a4 D_158a4.
      stepLD F_158a8 D_158a8 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_158ac D_158ac (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_158b0 D_158b0.
      stepb_ft F_158b4 D_158b4 ltac:(condZ).
      sn F_158b8 D_158b8. sn F_158bc D_158bc. sn F_158c0 D_158c0. sn F_158c4 D_158c4. sn F_158c8 D_158c8.
      sn F_158f0 D_158f0. sn F_158f4 D_158f4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_Bc : forall regs m (s w h : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z -> (h <= 2 \/ w <= 2)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) ->
    rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 8 -> getr regs 11 = Z_to_bv 64 8 ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x15928 : word) m rom) (mkst regs' (0x13aa0 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x159f4
      /\ getr regs' 10 = Z_to_bv 64 0x10a74 /\ getr regs' 11 = Z_to_bv 64 0x10b17 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s w h Hs Hs64 Hw Hh HC Rw Rh Rg Rs H2 H10 H11 H18 H19.
    destruct (Z_lt_ge_dec 2 h) as [Hh3|Hh2].
    - assert (Hw2 : (w <= 2)%Z) by lia. eexists. split.
      + stepb_ft F_1582c D_1582c ltac:(condZ).
        stepat F_15830 D_15830 (Z_to_bv 64 2) ltac:(gres; pin; imm_norm; exact or_2_2).
        stepb_ft F_15834 D_15834 ltac:(condZ).
        stepLD F_15838 D_15838 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small h) by lia.
        stepb_ft F_1583c D_1583c ltac:(condZ).
        stepLD F_15840 D_15840 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small w) by lia.
        stepb_tk F_15844 D_15844 ltac:(condZ).                                        (* [comment removed for export] *)
        sn F_158cc D_158cc.
        stepLD F_158d0 D_158d0 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_158d4 D_158d4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_158d8 D_158d8.
        stepb_ft F_158dc D_158dc ltac:(condZ).
        sn F_158e0 D_158e0. sn F_158e4 D_158e4. sn F_158e8 D_158e8. sn F_158ec D_158ec.
        sn F_158f0 D_158f0. sn F_158f4 D_158f4.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + stepb_ft F_1582c D_1582c ltac:(condZ).
        stepat F_15830 D_15830 (Z_to_bv 64 2) ltac:(gres; pin; imm_norm; exact or_2_2).
        stepb_ft F_15834 D_15834 ltac:(condZ).
        stepLD F_15838 D_15838 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small h) by lia.
        stepb_tk F_1583c D_1583c ltac:(condZ).                                        (* [comment removed for export] *)
        sn F_158cc D_158cc.
        stepLD F_158d0 D_158d0 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_158d4 D_158d4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_158d8 D_158d8.
        stepb_ft F_158dc D_158dc ltac:(condZ).
        sn F_158e0 D_158e0. sn F_158e4 D_158e4. sn F_158e8 D_158e8. sn F_158ec D_158ec.
        sn F_158f0 D_158f0. sn F_158f4 D_158f4.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_X0 : forall regs m (s : Z) (ret s0v s1v s2v s3v : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x159f4 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v Hs Hs64 Hret R1 R2 R3 R4 R5 H2 H10. eexists. split.
    - sn F_158f8 D_158f8. sn F_158fc D_158fc.
      sn F_15904 D_15904.
      stepLD8 F_15908 D_15908 ret. stepLD8 F_1590c D_1590c s0v. stepLD8 F_15910 D_15910 s1v. stepLD8 F_15914 D_15914 s2v. stepLD8 F_15918 D_15918 s3v.
      zv F_1591c D_1591c (Z_to_bv 64 s).
      stepret F_15920 D_15920 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_X2 : forall regs m (s : Z) (ret s0v s1v s2v s3v kel : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 9 = kel ->
    exists regs',
      msteps SEGS (mkst regs (0x15a00 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = kel
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v kel Hs Hs64 Hret R1 R2 R3 R4 R5 H2 H9. eexists. split.
    - sn F_15904 D_15904.
      stepLD8 F_15908 D_15908 ret. stepLD8 F_1590c D_1590c s0v. stepLD8 F_15910 D_15910 s1v. stepLD8 F_15914 D_15914 s2v. stepLD8 F_15918 D_15918 s3v.
      zv F_1591c D_1591c (Z_to_bv 64 s).
      stepret F_15920 D_15920 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_C1 : forall regs m (kel : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (kel + 8)) 8 = true ->
    getr regs 10 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x15948 : word) m rom)
                  (mkst regs' (0x15a4c : word) (wbytes (wbytes m (Z_to_bv 64 (kel + 8)) (word_to_le_bytes 4 (Z_to_bv 64 2)))
                                                      (Z_to_bv 64 (kel + 12)) (word_to_le_bytes 4 (Z_to_bv 64 2))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 9 = Z_to_bv 64 kel
      /\ regs_agree (fun r => In r [9]%list) regs regs'.
  Proof.
    intros regs m kel Hk Hk64 SOK H10 H18 H19. eexists. split.
    - sn F_1584c D_1584c.
      stepb_ft F_15850 D_15850 ltac:(condZ).
      stepST F_15854 D_15854 (Z_to_bv 64 (kel + 8)) (Z_to_bv 64 2) ltac:(sok_in SOK).
      stepST F_15858 D_15858 (Z_to_bv 64 (kel + 12)) (Z_to_bv 64 2) ltac:(sok_in SOK).
      sn F_1585c D_1585c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_C0 : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) ->
    rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x15948 : word) m rom) (mkst regs' (0x139d0 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15a4c /\ getr regs' 9 = Z_to_bv 64 0
      /\ getr regs' 10 = Z_to_bv 64 0x103e8 /\ getr regs' 11 = Z_to_bv 64 0x104ab /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - sn F_1584c D_1584c.
      stepb_tk F_15850 D_15850 ltac:(condZ).
      sn F_15924 D_15924.
      stepLD F_15928 D_15928 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_1592c D_1592c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15930 D_15930.
      stepb_ft F_15934 D_15934 ltac:(condZ).
      sn F_15938 D_15938. sn F_1593c D_1593c. sn F_15940 D_15940. sn F_15944 D_15944. sn F_15948 D_15948. sn F_1594c D_1594c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_D : forall regs m (s w h : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x15a4c : word) m rom) (mkst regs' (0x15a70 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s w h Hs Hs64 Hw Hh Rw Rh H2. eexists. split.
    - stepLD F_15950 D_15950 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      stepb_ft F_15954 D_15954 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_15958 D_15958 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      sn F_1595c D_1595c. sn F_15960 D_15960.
      stepb_ft F_1596c D_1596c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15970 D_15970.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L1 : forall regs m (s i j : Z) (pix : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 8 = pix -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x15a70 : word) m rom) (mkst regs' (0x14338 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x15a84 /\ getr regs' 10 = pix
      /\ getr regs' 11 = Z_to_bv 64 j /\ getr regs' 12 = Z_to_bv 64 i /\ getr regs' 13 = Z_to_bv 64 (s - 56)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s i j pix Hs Hs64 H2 H8 H18 H19. eexists. split.
    - zv F_15974 D_15974 (Z_to_bv 64 (s - 56)).
      sn F_15978 D_15978. sn F_1597c D_1597c. sn F_15980 D_15980. sn F_15984 D_15984.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L2 : forall regs m (s val : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= val < 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 56)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 val)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x15a84 : word) m rom) (mkst regs' (0x15a88 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 10 = Z_to_bv 64 val
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s val Hs Hs64 Hv Rv H2. eexists. split.
    - stepLD F_15988 D_15988 (word_to_le_bytes 4 (Z_to_bv 64 val)) (Z_to_bv 64 val) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L3 : forall regs m (i j : Z) (kel : word),
    getr regs 9 = kel -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x15a8c : word) m rom) (mkst regs' (0x15818 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15a9c /\ getr regs' 10 = kel
      /\ getr regs' 11 = Z_to_bv 64 i /\ getr regs' 12 = Z_to_bv 64 j
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m i j kel H9 H18 H19. eexists. split.
    - sn F_15990 D_15990. sn F_15994 D_15994. sn F_15998 D_15998. sn F_1599c D_1599c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L4a : forall regs m (s w h i j : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (0 <= j)%Z -> (j + 1 < w)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x15a9c : word) m rom) (mkst regs' (0x15a70 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 18 = Z_to_bv 64 i /\ getr regs' 19 = Z_to_bv 64 (j + 1)
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 11; 19]%list) regs regs'.
  Proof.
    intros regs m s w h i j Hs Hs64 Hw Hj Hj1 Rw H2 H18 H19. eexists. split.
    - stepLD F_159a0 D_159a0 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      stepiv F_159a4 D_159a4 (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_tk F_159a8 D_159a8 ltac:(condZ).                                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L4b : forall regs m (s w h i j : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= j)%Z -> (j + 1 = w)%Z -> (0 <= i)%Z -> (i + 1 < h)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x15a9c : word) m rom) (mkst regs' (0x15a70 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 18 = Z_to_bv 64 (i + 1) /\ getr regs' 19 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s w h i j Hs Hs64 Hw Hh Hj Hj1 Hi Hi1 Rw Rh H2 H18 H19. eexists. split.
    - stepLD F_159a0 D_159a0 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      stepiv F_159a4 D_159a4 (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_ft F_159a8 D_159a8 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_159ac D_159ac (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      sn F_159b0 D_159b0.
      stepiv F_15964 D_15964 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_ft F_15968 D_15968 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_1596c D_1596c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15970 D_15970.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L4c : forall regs m (s w h i j : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= j)%Z -> (j + 1 = w)%Z -> (0 <= i)%Z -> (i + 1 = h)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x15a9c : word) m rom) (mkst regs' (0x15a00 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s w h i j Hs Hs64 Hw Hh Hj Hj1 Hi Hi1 Rw Rh H2 H18 H19. eexists. split.
    - stepLD F_159a0 D_159a0 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      stepiv F_159a4 D_159a4 (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_ft F_159a8 D_159a8 ltac:(condZ).
      stepLD F_159ac D_159ac (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      sn F_159b0 D_159b0.
      stepiv F_15964 D_15964 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_tk F_15968 D_15968 ltac:(condZ).                                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
End KernSegs.

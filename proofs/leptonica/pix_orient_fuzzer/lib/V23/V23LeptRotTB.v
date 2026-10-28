(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptExec LeptExecW LeptExecFP LeptExecB LeptExecX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23_code_r90a_rottb.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma tb_and3 : forall p : Z, (0 <= p < 2 ^ 64)%Z -> (p mod 4 = 0)%Z ->
  alu64 ALU_AND (Z_to_bv 64 p) (Z_to_bv 64 3) = Z_to_bv 64 0.
Proof.
  intros p Hp Hm. rewrite alu_and. unfold v_and. rewrite !u_Z2bv by lia.
  change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z. rewrite Hm. reflexivity.
Qed.

Lemma tb_and7 : forall p : Z, (0 <= p < 2 ^ 64)%Z -> (p mod 8 = 0)%Z ->
  alu64 ALU_AND (Z_to_bv 64 p) (Z_to_bv 64 7) = Z_to_bv 64 0.
Proof.
  intros p Hp Hm. rewrite alu_and. unfold v_and. rewrite !u_Z2bv by lia.
  change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z. rewrite Hm. reflexivity.
Qed.

Ltac tb_modtac :=
  first [ assumption
        | (apply al16_mod8; assumption) | (apply al16_mod4; assumption)
        | (apply al16_plus_mod4; [assumption | reflexivity]) | (apply al16_plus_mod8; [assumption | reflexivity])
        | lia ].
Ltac tb_and0 := first [ rewrite (tb_and3 _) by (first [lia | tb_modtac]) | rewrite (tb_and7 _) by (first [lia | tb_modtac]) ].
Ltac tb_sc_hook :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ => repeat tb_and0; vm_compute; reflexivity
  end.
#[local] Ltac exB_sc_hook ::= tb_sc_hook.

Lemma tb_and_m1 : forall x, (0 <= x < 2 ^ 64)%Z -> v_and (Z_to_bv 64 (-1)) (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold v_and. rewrite (u_Z2bv x) by lia.
  change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma tb_clamp : forall x, (0 <= x < 2 ^ 31)%Z ->
  v_and (v_subw (Z_to_bv 64 0) (v_slt (Z_to_bv 64 0) (Z_to_bv 64 x))) (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. rewrite v_slt_Z by lia.
  destruct (Z.ltb_spec 0 x) as [Hp | Hn].
  - replace (v_subw (Z_to_bv 64 0) (Z_to_bv 64 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
    apply tb_and_m1. lia.
  - assert (x = 0)%Z as -> by lia. apply bv_eq. vm_compute. reflexivity.
Qed.

Ltac tb_zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
Ltac tb_fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac tb_condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac tb_cond := first [ condZ | tb_condR ].
Ltac tb_seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
Ltac tb_sltu0 F D := sn F D; tb_fixv' (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
Ltac tb_slti0 F D := sn F D; tb_fixv' (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).

Definition PC_pixFlipTB : Z := 0x997e0.

(* [comment removed for export] *)
Definition FRTB (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).
(* [comment removed for export] *)
Definition DIMTB (m : word -> option byte) (s : Z) (h d : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 d)).
(* [comment removed for export] *)
Definition PCFTB (m : word -> option byte) (s pix : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0x99868)))
    (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 pix)))
    (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 pix)))
    (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (getr regs 19)).
Definition MTB_A (m : word -> option byte) (s pix : Z) (v : pixv) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  PCFTB (DIMTB (FRTB m s ret regs) s (p_h v) (p_d v)) s pix regs.

Section RotTB.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma tb_A : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pix)%Z -> (pix mod 16 = 0)%Z -> PIXat m pix v ->
    (pix + 64 <= s - 160 \/ s <= pix)%Z -> p_d v = 1%Z -> (1 <= p_h v <= 2 ^ 26)%Z -> (1 <= p_wpl v <= 2 ^ 26)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x997e0 : word) m rom) (mkst regs' (0x10e6e0 : word) (MTB_A m s pix v ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x99890
      /\ getr regs' 10 = Z_to_bv 64 (p_wpl v) /\ getr regs' 11 = Z_to_bv 64 4
      /\ getr regs' 8 = Z_to_bv 64 pix /\ getr regs' 9 = Z_to_bv 64 (p_data v) /\ getr regs' 18 = Z_to_bv 64 (p_wpl v)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 Hs16 Hp ALp PX DJ Hd Hh Hwpl SOK H2 H1 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Hdat.
    pose proof (PIX_rd_h SEGS _ _ _ PX) as Ch. pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd.
    pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    rewrite Hd in Cd. unfold MTB_A. rewrite Hd. unfold PCFTB, DIMTB, FRTB. subst ret.
    replace (0x997e0 : word) with (Z_to_bv 64 0x997e0) by (apply bv_eq; reflexivity).
    replace (0x10e6e0 : word) with (Z_to_bv 64 0x10e6e0) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pix; p_h v; p_wpl v; p_data v] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pix; p_h v; p_wpl v; p_data v]) m
      [KWr (SA (EVar 32) (-160)) 160; KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 65);
       KWord (SA (EVar 33) 4) 4 (EVar 34); KWord (SA (EVar 33) 8) 4 (ELit 1); KWord (SA (EVar 33) 16) 4 (EVar 35);
       KWord (SA (EVar 33) 56) 8 (EVar 36);
       KRange (EVar 34) 1 (2 ^ 26); KRange (EVar 35) 1 (2 ^ 26); KRange (EVar 36) 0 (2 ^ 64 - 1);
       KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-160)) 160]%Z) by (ex_know regs).
    ex_run 400%nat [0x10e6e0%Z] (SCR [false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem2 regs Hms.
    - repeat split; try (exB_reg regs HR'); ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma tb_B : forall regs m (s h wpl data b : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= h)%Z -> (1 <= wpl)%Z -> (4 * wpl * h <= 2 ^ 26)%Z -> (1 <= data < 2 ^ 64)%Z ->
    (1 <= b < 2 ^ 64)%Z -> (b mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 h) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 b -> getr regs 9 = Z_to_bv 64 data -> getr regs 18 = Z_to_bv 64 wpl ->
    exists regs',
      msteps SEGS (mkst regs (0x99890 : word) m rom) (mkst regs' (0x998e0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (h - 1) /\ getr regs' 19 = Z_to_bv 64 b /\ getr regs' 20 = Z_to_bv 64 (4 * wpl)
      /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 24 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 (h / 2) /\ getr regs' 26 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [10; 11; 12; 19; 20; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s h wpl data b Hs Hs64 Hh Hw Hsz Hd Hb ALb RH H2 H10 H9 H18.
    assert (Hwh : (h <= wpl * h)%Z) by nia. assert (Hhw : (wpl <= wpl * h)%Z) by nia.
    assert (Hh2 : (0 <= h / 2 <= h)%Z) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    eexists. split.
    - stepb_ft F_99890 D_99890 ltac:(condZ).
      sn F_99894 D_99894.
      tb_zlit F_99898 D_99898 (Z_to_bv 64 536870912).
      zv F_9989c D_9989c (Z_to_bv 64 (wpl + 536870912)).
      sn F_998a0 D_998a0. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srliw_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_998a4 D_998a4 ltac:(condZ).
      stepLD F_998a8 D_998a8 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(addr_norm; exact RH) ltac:(apply lez4; lia).
      sn F_998ac D_998ac. fixv (Z_to_bv 64 h) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_998b0 D_998b0. fixv (Z_to_bv 64 (h - 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepb_ft F_998b4 D_998b4 ltac:(condZ).
      zv F_998b8 D_998b8 (Z_to_bv 64 0).
      sn F_998bc D_998bc. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srli by lia; f_equal; apply Z.div_small; lia).
      sn F_998c0 D_998c0. fixv (Z_to_bv 64 (4 * wpl)) ltac:(rewrite v_slliw_2, sw32_small by lia; f_equal; lia).
      guard4 F_998c4 D_998c4 ALb.
      zv F_998c8 D_998c8 (Z_to_bv 64 h).
      sn F_998cc D_998cc. fixv (Z_to_bv 64 (h / 2)) ltac:(rewrite zbv_sraiw_small by lia; reflexivity).
      sn F_998d0 D_998d0. sn F_998d4 D_998d4. sn F_998d8 D_998d8.
      fixv (Z_to_bv 64 (h / 2)) ltac:(apply tb_clamp; lia).
      sn F_998dc D_998dc. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma tb_H : forall regs m (h wpl data b i : Z),
    (2 <= h)%Z -> (1 <= wpl)%Z -> (4 * wpl * h <= 2 ^ 26)%Z -> (1 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 63)%Z -> (data mod 4 = 0)%Z ->
    (1 <= b < 2 ^ 64)%Z -> (b mod 4 = 0)%Z -> (0 <= i)%Z -> (2 * i + 2 <= h)%Z ->
    getr regs 9 = Z_to_bv 64 data -> getr regs 18 = Z_to_bv 64 wpl -> getr regs 19 = Z_to_bv 64 b -> getr regs 20 = Z_to_bv 64 (4 * wpl) ->
    getr regs 23 = Z_to_bv 64 i -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 (h / 2) -> getr regs 26 = Z_to_bv 64 1 ->
    getr regs 10 = Z_to_bv 64 (h - 1 - i) ->
    exists regs',
      msteps SEGS (mkst regs (0x998e0 : word) m rom) (mkst regs' (0x11e154 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x9996c /\ getr regs' 10 = Z_to_bv 64 b /\ getr regs' 11 = Z_to_bv 64 (data + 4 * wpl * i)
      /\ getr regs' 12 = Z_to_bv 64 (4 * wpl)
      /\ getr regs' 21 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 22 = Z_to_bv 64 (data + 4 * wpl * (h - 1 - i))
      /\ getr regs' 27 = Z_to_bv 64 (h - 1 - i)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 21; 22; 27]%list) regs regs'.
  Proof.
    intros regs m h wpl data b i Hh Hw Hsz Hd Hd64 ALd Hb ALb Hi Hih H9 H18 H19 H20 H23 H24 H25 H26 H10.
    assert (Hwh : (h <= wpl * h)%Z) by nia.
    assert (Hcnt : (i + 1 <= h / 2)%Z) by (apply Z.div_le_lower_bound; lia).
    assert (Hh2 : (h / 2 <= h)%Z) by (apply Z.div_le_upper_bound; lia).
    assert (Hiw : (0 <= i * wpl /\ 4 * (i * wpl) + 4 * wpl <= 4 * wpl * h)%Z) by nia.
    assert (Hjw : (0 <= (h - 1 - i) * wpl /\ 4 * ((h - 1 - i) * wpl) + 4 * wpl <= 4 * wpl * h)%Z) by nia.
    assert (ALt : ((data + 4 * (i * wpl)) mod 4 = 0)%Z).
    { rewrite (Z.mul_comm 4 (i * wpl)), Z_mod_plus_full. exact ALd. }
    eexists. split.
    - stepb_ft F_998e0 D_998e0 ltac:(condZ).
      sn F_998e4 D_998e4.
      zv F_998e8 D_998e8 (Z_to_bv 64 (i * wpl)).
      sn F_998ec D_998ec. fixv (Z_to_bv 64 (i * wpl)) ltac:(rewrite zbv_mulw_small by lia; reflexivity).
      stepb_ft F_998f0 D_998f0 ltac:(tb_cond).
      sn F_998f4 D_998f4. fixv (Z_to_bv 64 (i * wpl)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepiv F_998f8 D_998f8 (Z_to_bv 64 (4 * (i * wpl))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_998fc D_998fc (Z_to_bv 64 (data + 4 * (i * wpl))).
      tb_seqz0 F_99900 D_99900.
      stepb_ft F_99904 D_99904 ltac:(tb_cond).
      tb_sltu0 F_99908 D_99908.
      tb_slti0 F_9990c D_9990c.
      sn F_99910 D_99910. sn F_99914 D_99914.
      stepb_ft F_99918 D_99918 ltac:(tb_condR).
      zv F_9991c D_9991c (Z_to_bv 64 ((h - 1 - i) * wpl)).
      sn F_99920 D_99920. fixv (Z_to_bv 64 ((h - 1 - i) * wpl)) ltac:(rewrite zbv_mulw_small by lia; reflexivity).
      stepb_ft F_99924 D_99924 ltac:(tb_cond).
      sn F_99928 D_99928. fixv (Z_to_bv 64 ((h - 1 - i) * wpl)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepiv F_9992c D_9992c (Z_to_bv 64 (4 * ((h - 1 - i) * wpl))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_99930 D_99930 (Z_to_bv 64 (data + 4 * ((h - 1 - i) * wpl))).
      tb_seqz0 F_99934 D_99934.
      stepb_ft F_99938 D_99938 ltac:(tb_cond).
      tb_sltu0 F_9993c D_9993c.
      tb_slti0 F_99940 D_99940.
      sn F_99944 D_99944. sn F_99948 D_99948.
      stepb_ft F_9994c D_9994c ltac:(tb_condR).
      guard4 F_99950 D_99950 ALt.
      sn F_99954 D_99954.
      stepb_ft F_99958 D_99958 ltac:(tb_condR).
      sn F_9995c D_9995c. sn F_99960 D_99960. sn F_99964 D_99964. sn F_99968 D_99968.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try (f_equal; lia). solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma tb_X : forall regs m (h b : Z),
    getr regs 19 = Z_to_bv 64 b -> getr regs 23 = Z_to_bv 64 (h / 2) -> getr regs 25 = Z_to_bv 64 (h / 2) ->
    exists regs',
      msteps SEGS (mkst regs (0x998e0 : word) m rom) (mkst regs' (0x10e818 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x99a08 /\ getr regs' 10 = Z_to_bv 64 b
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m h b H19 H23 H25. eexists. split.
    - stepb_tk F_998e0 D_998e0 ltac:(tb_cond).
      sn F_99a00 D_99a00. sn F_99a04 D_99a04.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma tb_L1 : forall regs m,
    exists regs',
      msteps SEGS (mkst regs (0x9996c : word) m rom) (mkst regs' (0x11e154 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x9997c /\ getr regs' 10 = getr regs 21 /\ getr regs' 11 = getr regs 22 /\ getr regs' 12 = getr regs 20
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_9996c D_9996c. sn F_99970 D_99970. sn F_99974 D_99974. sn F_99978 D_99978.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma tb_L2 : forall regs m,
    exists regs',
      msteps SEGS (mkst regs (0x9997c : word) m rom) (mkst regs' (0x11e154 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x9998c /\ getr regs' 10 = getr regs 22 /\ getr regs' 11 = getr regs 19 /\ getr regs' 12 = getr regs 20
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_9997c D_9997c. sn F_99980 D_99980. sn F_99984 D_99984. sn F_99988 D_99988.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma tb_L3 : forall regs m (h i : Z),
    (0 <= i)%Z -> (2 * i + 2 <= h)%Z -> (h < 2 ^ 31)%Z ->
    getr regs 27 = Z_to_bv 64 (h - 1 - i) -> getr regs 23 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x9998c : word) m rom) (mkst regs' (0x998e0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (h - 1 - (i + 1)) /\ getr regs' 23 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun r => In r [10; 23]%list) regs regs'.
  Proof.
    intros regs m h i Hi Hih Hh H27 H23. eexists. split.
    - sn F_9998c D_9998c. fixv (Z_to_bv 64 (h - 1 - (i + 1))) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_99990 D_99990. fixv (Z_to_bv 64 (i + 1)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepb_tk F_99994 D_99994 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma tb_D : forall regs m (s : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    cellsZ m [(s - 8, ret); (s - 16, v8); (s - 24, v9); (s - 32, v18); (s - 40, v19); (s - 48, v20); (s - 56, v21);
              (s - 64, v22); (s - 72, v23); (s - 80, v24); (s - 88, v25); (s - 96, v26); (s - 104, v27)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs',
      msteps SEGS (mkst regs (0x99a08 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8
      /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20
      /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25
      /\ getr regs' 26 = v26 /\ getr regs' 27 = v27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hs Hs64 Hret
      (R8 & R16 & R24 & R32 & R40 & R48 & R56 & R64 & R72 & R80 & R88 & R96 & R104 & _) H2.
    eexists. split.
    - sn F_99a08 D_99a08. sn F_99a64 D_99a64. sn F_99a68 D_99a68.
      stepLD8 F_99aa0 D_99aa0 ret. stepLD8 F_99aa4 D_99aa4 v8. stepLD8 F_99aa8 D_99aa8 v9.
      stepLD8 F_99aac D_99aac v18. stepLD8 F_99ab0 D_99ab0 v19. stepLD8 F_99ab4 D_99ab4 v20.
      stepLD8 F_99ab8 D_99ab8 v21. stepLD8 F_99abc D_99abc v22. stepLD8 F_99ac0 D_99ac0 v23.
      stepLD8 F_99ac4 D_99ac4 v24. stepLD8 F_99ac8 D_99ac8 v25. stepLD8 F_99acc D_99acc v26.
      stepLD8 F_99ad0 D_99ad0 v27.
      zv F_99ad4 D_99ad4 (Z_to_bv 64 s). stepret F_99ad8 D_99ad8 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End RotTB.

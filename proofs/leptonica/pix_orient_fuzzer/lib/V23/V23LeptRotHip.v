(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib LeptExec LeptExecX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRotHip.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PC_rasteropHipLowS : Z := 0x875f4.

(* [comment removed for export] *)
Definition LOCHIP (m : word -> option byte) (s data shift wpl : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 216)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 wpl)))
    (Z_to_bv 64 (s - 232)) (word_to_le_bytes 8 (Z_to_bv 64 (wpl - 1))))
    (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 (32 - shift))))
    (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 (4 * (wpl - 1)))))
    (Z_to_bv 64 (s - 240)) (word_to_le_bytes 8 (Z_to_bv 64 data)))
    (Z_to_bv 64 (s - 224)) (word_to_le_bytes 8 (Z_to_bv 64 (1 - wpl))))
    (Z_to_bv 64 (s - 168)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (Z_to_bv 64 (4 * (32 - shift)))))
    (Z_to_bv 64 (s - 200)) (word_to_le_bytes 8 (Z_to_bv 64 0x1f440)))
    (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 (4 * (32 - shift) + 0x1f440))))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 (4 * shift))))
    (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 0x1f4c4)))
    (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 (4 * shift + 0x1f4c4))).
Definition MHIP_A (m : word -> option byte) (s data shift wpl : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  LOCHIP (FRHIP m s ret regs) s data shift wpl.

Section RotHip.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  Lemma v23hhA_wrap32 : forall a : Z, (0 <= a < 2 ^ 32)%Z -> bv_wrap 32 a = a.
  Proof. intros a Ha. apply bv_wrap_small. exact Ha. Qed.

  Lemma v23hhA_addw : forall a b : Z, (- 2 ^ 31 <= a + b < 2 ^ 31)%Z -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
  Proof. intros a b H. rewrite v_addw_Z, sw32_small by lia. reflexivity. Qed.

  Lemma v23hhA_subw : forall a b : Z, (- 2 ^ 31 <= a - b < 2 ^ 31)%Z -> v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
  Proof. intros a b H. rewrite v_subw_Z, sw32_small by lia. reflexivity. Qed.

  Lemma v23hhA_mulw : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> (0 <= a * b < 2 ^ 31)%Z ->
    v_mulw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof. intros a b Ha Hb Hab. unfold v_mulw. rewrite !u_Z2bv by lia. rewrite (sw32_eq (a * b)), (sw32_small (a * b)) by lia. reflexivity. Qed.

  Lemma v23hhA_add : forall a b : Z, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
  Proof. intros a b. rewrite <- alu_add. apply ex_ptr_val. Qed.

  Lemma v23hhA_srlw5 : forall a : Z, (0 <= a < 32)%Z -> v_srlw (Z_to_bv 64 a) (Z_to_bv 64 5) = Z_to_bv 64 0.
  Proof.
    intros a Ha. unfold v_srlw. rewrite !u_Z2bv by lia. rewrite v23hhA_wrap32 by lia.
    change (5 mod 32)%Z with 5%Z. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
  Qed.

  Lemma v23hhA_srlw_m1 : v_srlw (Z_to_bv 64 (-1)) (Z_to_bv 64 27) = Z_to_bv 64 31.
  Proof. unfold v_srlw. f_equal; vm_compute; reflexivity. Qed.

  Lemma v23hhA_sraw5 : forall a : Z, (0 <= a < 32)%Z -> v_sraw (Z_to_bv 64 a) (Z_to_bv 64 5) = Z_to_bv 64 0.
  Proof.
    intros a Ha. unfold v_sraw. rewrite !u_Z2bv by lia. rewrite (sw32_eq a), (sw32_small a) by lia.
    change (5 mod 32)%Z with 5%Z. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
  Qed.

  Lemma v23hhA_sraw_neg31 : forall a : Z, (- 2 ^ 31 <= a < 0)%Z -> v_sraw (Z_to_bv 64 a) (Z_to_bv 64 31) = Z_to_bv 64 (-1).
  Proof.
    intros a Ha. unfold v_sraw. rewrite (u_zbv a), zx_neg by lia. rewrite (u_Z2bv 31) by lia.
    rewrite (sw32_eq (a + 2 ^ 64)). replace (a + 2 ^ 64)%Z with (a + 2 ^ 32 * 2 ^ 32)%Z by lia. rewrite (sw32_mod a (2 ^ 32)), (sw32_small a) by lia.
    change (31 mod 32)%Z with 31%Z. rewrite Z.shiftr_div_pow2 by lia.
    rewrite <- (Z.div_unique a (2 ^ 31) (-1) (a + 2 ^ 31)) by lia. reflexivity.
  Qed.

  Lemma v23hhA_land31 : forall w : Z, (0 <= w)%Z -> Z.land w 31 = (w mod 32)%Z.
  Proof. intros w Hw. change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

  Lemma v23hhA_andneg : forall sh : Z, (1 <= sh <= 31)%Z -> v_and (Z_to_bv 64 (-1 * sh)) (Z_to_bv 64 31) = Z_to_bv 64 (32 - sh).
  Proof.
    intros sh Hsh. unfold v_and. rewrite (u_zbv (-1 * sh)), zx_neg by lia. rewrite (u_Z2bv 31) by lia.
    rewrite v23hhA_land31 by lia. f_equal. symmetry. apply (Z.mod_unique (-1 * sh + 2 ^ 64) 32 (2 ^ 59 - 1) (32 - sh)); lia.
  Qed.

  Lemma v23hhA_and31 : forall a : Z, (0 <= a < 32)%Z -> v_and (Z_to_bv 64 a) (Z_to_bv 64 31) = Z_to_bv 64 a.
  Proof. intros a Ha. unfold v_and. rewrite !u_Z2bv by lia. rewrite v23hhA_land31 by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

  Lemma v23hhA_xor_eq : forall a b : Z, a = b -> v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
  Proof. intros a b <-. unfold v_xor. rewrite Z.lxor_nilpotent. reflexivity. Qed.

  Lemma v23hhA_sltu00 : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0) = Z_to_bv 64 0.
  Proof. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

  Lemma v23hhA_slt_lt : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z -> (a < b)%Z ->
    v_slt (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
  Proof.
    intros a b Ha Hb Hab. unfold v_slt. rewrite hip_lts by lia.
    replace (a <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  Ltac v23hhA_norm :=
    rewrite ?w_mulw, ?m_mul;
    repeat first [ rewrite v23hhA_srlw_m1 | rewrite v23hhA_sltu00
                 | rewrite v23hhA_andneg by lia | rewrite v23hhA_sraw_neg31 by lia
                 | rewrite v23hhA_sraw5 by lia | rewrite v23hhA_srlw5 by lia | rewrite v23hhA_and31 by lia
                 | rewrite v23hhA_mulw by lia | rewrite zbv_mul | rewrite v23hhA_add
                 | rewrite v23hhA_subw by lia | rewrite v23hhA_addw by lia
                 | rewrite v23hhA_xor_eq by lia | rewrite v23hhA_slt_lt by lia ].

  Ltac v23hhA_fin := ex_vnorm; v23hhA_norm; first [reflexivity | f_equal; lia].

  Ltac v23hhA_beq regs :=
    first [ reflexivity
          | solve [ex_bytes_eq regs]
          | solve [f_equal; ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
                   repeat (match goal with H : getr regs _ = _ |- _ => rewrite H end); v23hhA_fin] ].

  Ltac v23hhA_mem regs Hms :=
    eapply ex_msteps_mem; [exact Hms | cbn [mem_denot s_log e_addr e_width e_val]; unfold MHIP_A, LOCHIP, FRHIP;
      repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | v23hhA_beq regs ]); reflexivity].

  Ltac v23hhA_sc := ex_vnorm; v23hhA_norm; ex_br.

  (* [comment removed for export] *)
  Lemma hip_A : forall regs m (s data wpl h shift : Z) (ret : word),
    (4096 + 240 <= s < 2 ^ 48)%Z -> (1 <= shift <= 31)%Z -> (1 <= wpl < 2 ^ 25)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= data < 2 ^ 48)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 1 ->
    getr regs 13 = Z_to_bv 64 wpl -> getr regs 14 = Z_to_bv 64 0 -> getr regs 15 = Z_to_bv 64 h -> getr regs 16 = Z_to_bv 64 shift ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 PC_rasteropHipLowS) m rom) (mkst regs' (Z_to_bv 64 0x877c4) (MHIP_A m s data shift wpl ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 240) /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 5 /\ getr regs' 13 = Z_to_bv 64 wpl
      /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 h /\ getr regs' 17 = Z_to_bv 64 wpl
      /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 4 /\ getr regs' 21 = Z_to_bv 64 data /\ getr regs' 22 = Z_to_bv 64 (wpl - 1)
      /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 24 = Z_to_bv 64 (4 * (wpl - 1)) /\ getr regs' 26 = Z_to_bv 64 shift
      /\ getr regs' 29 = Z_to_bv 64 (wpl - 1) /\ getr regs' 30 = Z_to_bv 64 shift /\ getr regs' 31 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s data wpl h shift ret Hs Hsh Hwpl Hh Hd SOK H2 H1 H10 H11 H12 H13 H14 H15 H16.
    ex_entry regs [s; data; h; wpl; shift]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; data; h; wpl; shift]%Z) m
      [KRange (EVar 32) (4096 + 240) (2 ^ 48); KWr (SA (EVar 32) (-240)) 240;
       KRange (EVar 33) 0 (2 ^ 48); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 1 (2 ^ 25 - 1); KRange (EVar 36) 1 31]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 800%nat [0x877c4]%Z (SCR [false; true; false; false; false] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R'. split.
      - v23hhA_mem regs Hms.
      - repeat split. all: try (ex_reg regs HR'; v23hhA_fin).
        ex_agree HR HR'. }
    all: v23hhA_sc.
  Qed.

  Lemma v23hhR_sltu : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
    v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if (a <? b)%Z then 1 else 0).
  Proof. intros a b Ha Hb. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_Z2bv by lia. destruct (a <? b)%Z; reflexivity. Qed.

  Lemma v23hhR_slt : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
    v_slt (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if (a <? b)%Z then 1 else 0).
  Proof. intros a b Ha Hb. unfold v_slt, c_lts, bv_lts. rewrite !GrayLib.bv_signed_Zs by lia. destruct (a <? b)%Z; reflexivity. Qed.

  Lemma v23hhR_xor : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
  Proof. intros a b Ha Hb. unfold v_xor. rewrite !u_Z2bv by lia. reflexivity. Qed.

  Ltac v23hhR_dec :=
    match goal with |- context [(?a <? ?b)%Z] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) by (first [lia | nia])
            | rewrite (proj2 (Z.ltb_ge a b)) by (first [lia | nia]) ] end.

  Ltac v23hhR_lx :=
    match goal with |- context [Z.lxor ?a ?b] =>
      lazymatch a with Z0 => idtac | Zpos _ => idtac end;
      lazymatch b with Z0 => idtac | Zpos _ => idtac end;
      let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v end.

  Ltac v23hhR_sc :=
    rewrite ?w_addw, ?w_subw, ?w_mulw, ?m_mul, ?alu_add, ?alu_sub, ?alu_xor, ?alu_sltu, ?alu_slt, ?alu_and;
    repeat first
      [ rewrite zbv_mul
      | rewrite zbv_add
      | rewrite zbv_sub
      | rewrite zbv_addi
      | rewrite v_addw_Z
      | rewrite v_subw_Z
      | rewrite zbv_mulw_small by (first [lia | nia])
      | rewrite sw32_small by (first [lia | nia])
      | rewrite v23hhR_sltu by (first [lia | nia])
      | rewrite v23hhR_slt by (first [lia | nia])
      | v23hhR_dec
      | v23hhR_lx
      | rewrite Z.lxor_0_l
      | rewrite Z.lxor_0_r
      | rewrite v23hhR_xor by (first [lia | nia]) ].

  Ltac v23hhR_sc2 := solve [v23hhR_sc; ex_br].

  Ltac v23hhR_reg regs HR' :=
    lazymatch goal with
    | |- getr _ ?k = _ =>
        rewrite (reg_val _ _ _ k HR');
        match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
        ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
        repeat match goal with H : getr regs _ = _ |- _ => rewrite H end;
        v23hhR_sc; first [reflexivity | (f_equal; first [lia | nia])]
    end.

  (* [comment removed for export] *)
  Lemma hip_R2 : forall regs m (s data wpl h shift i : Z),
    (4096 + 240 <= s < 2 ^ 48)%Z -> (2 <= wpl < 2 ^ 25)%Z -> (1 <= shift <= 31)%Z -> (0 <= i < h)%Z -> (4 * wpl * h <= 2 ^ 26)%Z ->
    (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z -> (data mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * (wpl - 1)))) ->
    rdn SEGS m (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (1 - wpl))) ->
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 8 = Z_to_bv 64 (wpl * i) -> getr regs 9 = Z_to_bv 64 5 -> getr regs 13 = Z_to_bv 64 wpl ->
    getr regs 14 = Z_to_bv 64 i -> getr regs 15 = Z_to_bv 64 0 -> getr regs 16 = Z_to_bv 64 h -> getr regs 17 = Z_to_bv 64 wpl ->
    getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 4 -> getr regs 21 = Z_to_bv 64 data -> getr regs 22 = Z_to_bv 64 (wpl - 1) ->
    getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 (4 * (wpl - 1)) -> getr regs 26 = Z_to_bv 64 shift ->
    getr regs 29 = Z_to_bv 64 (wpl - 1) -> getr regs 30 = Z_to_bv 64 shift -> getr regs 31 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x877c4) m rom) (mkst regs' (Z_to_bv 64 0x87878) m rom)
      /\ getr regs' 7 = Z_to_bv 64 (1 - wpl) /\ getr regs' 10 = Z_to_bv 64 (data + 4 * (wpl * i) + 4 * (wpl - 1))
      /\ getr regs' 25 = Z_to_bv 64 (data + 4 * (wpl * i) + 4 * (wpl - 1)) /\ getr regs' 11 = Z_to_bv 64 shift /\ getr regs' 18 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [7; 10; 11; 12; 18; 25; 27]%list) regs regs'.
  Proof.
    intros regs m s data wpl h shift i Hs Hw Hsh Hi Hwh Hd Hd2 Hda R112 R120 R224 H2 H8 H9 H13 H14 H15 H16 H17 H19 H20 H21 H22 H23 H24 H26 H29 H30 H31.
    assert (Hr : (wpl <= 2 ^ 24)%Z /\ (h <= 2 ^ 23)%Z /\ (0 <= wpl * i)%Z /\ (wpl * i + wpl <= wpl * h)%Z /\ (4 * (wpl * h) <= 2 ^ 26)%Z) by (repeat split; nia).
    ex_entry regs [s; data; h; wpl; shift; i; wpl * i; 4 * (wpl - 1); 1 - wpl]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; data; h; wpl; shift; i; wpl * i; 4 * (wpl - 1); 1 - wpl]%Z) m
      [KRange (EVar 32) (4096 + 240) (2 ^ 48); KWord (SA (EVar 32) (-112)) 8 (ELit 0);
       KWord (SA (EVar 32) (-120)) 8 (EVar 39); KWord (SA (EVar 32) (-224)) 8 (EVar 40);
       KRange (EVar 33) 4096 (2 ^ 48); KAlign (EVar 33) 4; KRange (EVar 34) 1 (2 ^ 23); KRange (EVar 35) 2 (2 ^ 24); KRange (EVar 36) 1 31;
       KRange (EVar 37) 0 (2 ^ 23); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 39) 4 (2 ^ 26)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 800%nat [0x87878]%Z (SCR [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    all: try v23hhR_sc2.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (v23hhR_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma hip_R1 : forall regs m (s data wpl h shift i : Z),
    (4096 + 240 <= s < 2 ^ 48)%Z -> (wpl = 1)%Z -> (1 <= shift <= 31)%Z -> (0 <= i < h)%Z -> (4 * wpl * h <= 2 ^ 26)%Z ->
    (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * (wpl - 1)))) ->
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 8 = Z_to_bv 64 (wpl * i) -> getr regs 9 = Z_to_bv 64 5 -> getr regs 13 = Z_to_bv 64 wpl ->
    getr regs 14 = Z_to_bv 64 i -> getr regs 15 = Z_to_bv 64 0 -> getr regs 16 = Z_to_bv 64 h -> getr regs 17 = Z_to_bv 64 wpl ->
    getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 4 -> getr regs 21 = Z_to_bv 64 data -> getr regs 22 = Z_to_bv 64 (wpl - 1) ->
    getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 (4 * (wpl - 1)) -> getr regs 26 = Z_to_bv 64 shift ->
    getr regs 29 = Z_to_bv 64 (wpl - 1) -> getr regs 30 = Z_to_bv 64 shift -> getr regs 31 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x877c4) m rom) (mkst regs' (Z_to_bv 64 0x879b0) m rom)
      /\ getr regs' 1 = Z_to_bv 64 (data + 4 * (wpl * i)) /\ getr regs' 10 = Z_to_bv 64 (data + 4 * (wpl * i))
      /\ getr regs' 25 = Z_to_bv 64 (data + 4 * (wpl * i)) /\ getr regs' 11 = Z_to_bv 64 shift
      /\ regs_agree (fun r => In r [1; 7; 10; 11; 12; 18; 25; 27]%list) regs regs'.
  Proof.
    intros regs m s data wpl h shift i Hs Hw Hsh Hi Hwh Hd Hd2 R112 R120 H2 H8 H9 H13 H14 H15 H16 H17 H19 H20 H21 H22 H23 H24 H26 H29 H30 H31.
    assert (Hr : (h <= 2 ^ 24)%Z /\ (0 <= wpl * i)%Z /\ (wpl * i + wpl <= wpl * h)%Z /\ (4 * (wpl * h) <= 2 ^ 26)%Z) by (subst wpl; repeat split; lia).
    ex_entry regs [s; data; h; wpl; shift; i; wpl * i; 4 * (wpl - 1)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; data; h; wpl; shift; i; wpl * i; 4 * (wpl - 1)]%Z) m
      [KRange (EVar 32) (4096 + 240) (2 ^ 48); KWord (SA (EVar 32) (-112)) 8 (ELit 0);
       KWord (SA (EVar 32) (-120)) 8 (EVar 39);
       KRange (EVar 33) 4096 (2 ^ 48); KRange (EVar 34) 1 (2 ^ 24); KRange (EVar 35) 1 1; KRange (EVar 36) 1 31;
       KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 39) 0 0]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 800%nat [0x879b0]%Z (SCR [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    all: try v23hhR_sc2.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (v23hhR_reg regs HR'). ex_agree HR HR'.
  Qed.

  Lemma v23hhIF_uneg : forall z : Z, (- 2 ^ 64 < z < 0)%Z -> bv_unsigned (Z_to_bv 64 z) = (z + 2 ^ 64)%Z.
  Proof.
    intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z.
    rewrite <- (Z_mod_plus_full z 1 (2 ^ 64)). rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma v23hhIF_bne : forall z : Z, (- 2 ^ 63 <= z < 0)%Z -> Sem.branch_taken BC_NE (Z_to_bv 64 z) (Z_to_bv 64 0) = true.
  Proof.
    intros z Hz. cbn [Sem.branch_taken]. unfold bv_eqb. rewrite v23hhIF_uneg by lia. rewrite u_Z2bv by lia.
    first [ (apply negb_true_iff; apply Z.eqb_neq; lia) | (apply Z.eqb_neq; lia)
          | (destruct (Z.eqb_spec (z + 2 ^ 64) 0); [lia | reflexivity]) ].
  Qed.

  Lemma v23hhIF_beq : forall z : Z, z = 0%Z -> Sem.branch_taken BC_NE (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
  Proof. intros z Hz. subst z. vm_compute. reflexivity. Qed.

  Lemma v23hhIF_and3 : forall d : Z, (d mod 4 = 0)%Z -> (0 <= d < 2 ^ 64)%Z ->
    v_and (Z_to_bv 64 d) (Z_to_bv 64 3) = Z_to_bv 64 0.
  Proof.
    intros d Hd Hr. unfold v_and. rewrite !u_Z2bv by lia.
    change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z. rewrite Hd. reflexivity.
  Qed.

  Ltac v23hhIF_sc :=
    rewrite ?w_addw, ?ex_ptr_val, ?alu_add, ?alu_sltu, ?alu_and;
    repeat first
      [ rewrite zbv_addi
      | rewrite v_addw_Z
      | rewrite sw32_small by lia
      | rewrite zbv_snez by lia
      | rewrite v23hhIF_and3 by (first [assumption | lia]) ].

  Ltac v23hhIF_at H :=
    match goal with |- context [Z_to_bv 64 ?a] =>
      match type of H with context [Z_to_bv 64 ?a'] =>
        replace a with a' by (rewrite ?Z.add_0_r; first [reflexivity | lia]); exact H end end.

  Ltac v23hhIF_sc2 :=
    first
      [ solve [match goal with H : rdn _ _ _ _ = Some ?bs, Eb : bytes_le_to_Z ?bs = _ |- exists _, _ =>
                 exists bs; split; [v23hhIF_sc; v23hhIF_at H | rewrite Eb; first [reflexivity | (unfold extz; reflexivity)]] end]
      | solve [lazymatch goal with |- store_ok _ _ _ _ = true =>
                 v23hhIF_sc; match goal with H : store_ok _ _ _ _ = true |- _ => v23hhIF_at H end end]
      | solve [lazymatch goal with |- Sem.branch_taken _ _ _ = _ =>
                 v23hhIF_sc; first [ (apply v23hhIF_bne; lia) | (apply v23hhIF_beq; lia) | ex_br | reflexivity ] end]
      | solve [v23hhIF_sc; rewrite ?u_Z2bv by lia; repeat split; lia] ].

  Ltac v23hhIF_reg regs HR' :=
    lazymatch goal with
    | |- getr _ ?k = _ =>
        rewrite (reg_val _ _ _ k HR');
        match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
        ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
        repeat match goal with H : getr regs _ = _ |- _ => rewrite H end;
        v23hhIF_sc; first [reflexivity | (f_equal; first [lia | nia])]
    end.

  Ltac v23hhIF_addr regs :=
    ex_unfoldE; unfold adenot; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
    v23hhIF_sc; rewrite ?Z.add_0_r; reflexivity.

  (* [comment removed for export] *)
  Lemma hip_I : forall (last : bool) regs m (line wpl shift k : Z) (bs5 bs2 : list byte) (v5 v2 : word),
    (2 <= wpl < 2 ^ 25)%Z -> (1 <= shift <= 31)%Z -> (0 <= k)%Z -> (if last then k = wpl - 2 else k < wpl - 2)%Z ->
    (4096 <= line)%Z -> (line + 4 * wpl < 2 ^ 48)%Z ->
    rdn SEGS m (Z_to_bv 64 (line + 4 * (wpl - 2 - k))) 4 = Some bs5 -> bytes_le_to_Z bs5 = bv_unsigned v5 ->
    rdn SEGS m (Z_to_bv 64 (line + 4 * (wpl - 1 - k))) 4 = Some bs2 -> bytes_le_to_Z bs2 = bv_unsigned v2 ->
    store_ok SEGS m (Z_to_bv 64 (line + 4 * (wpl - 1 - k))) 4 = true ->
    getr regs 7 = Z_to_bv 64 (k + 1 - wpl) -> getr regs 10 = Z_to_bv 64 (line + 4 * (wpl - 1 - k)) ->
    getr regs 25 = Z_to_bv 64 (line + 4 * (wpl - 1 - k)) -> getr regs 11 = Z_to_bv 64 shift ->
    getr regs 9 = Z_to_bv 64 5 -> getr regs 18 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 4 -> getr regs 30 = Z_to_bv 64 shift ->
    exists regs' (wv : word),
      msteps SEGS (mkst regs (Z_to_bv 64 0x87878) m rom)
                  (mkst regs' (Z_to_bv 64 (if last then 0x879b0 else 0x87878)) (wbytes m (Z_to_bv 64 (line + 4 * (wpl - 1 - k))) (word_to_le_bytes 4 wv)) rom)
      /\ getr regs' 7 = Z_to_bv 64 (k + 2 - wpl) /\ getr regs' 1 = Z_to_bv 64 (line + 4 * (wpl - 2 - k))
      /\ getr regs' 10 = Z_to_bv 64 (line + 4 * (wpl - 2 - k)) /\ getr regs' 25 = Z_to_bv 64 (line + 4 * (wpl - 2 - k))
      /\ regs_agree (fun r => In r [1; 7; 10; 12; 25; 27]%list) regs regs'.
  Proof.
    intros last regs m line wpl shift k bs5 bs2 v5 v2 Hw Hsh Hk Hlast Hl Hl2 Rd5 E5 Rd2 E2 SOK H7 H10 H25 H11 H9 H18 H20 H30.
    assert (Hkk : (k <= wpl - 2)%Z) by (destruct last; lia).
    ex_entry regs [line; wpl; shift; k; k + 1 - wpl; line + 4 * (wpl - 1 - k); extz true 4 (u v5); u v2]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [line; wpl; shift; k; k + 1 - wpl; line + 4 * (wpl - 1 - k); extz true 4 (u v5); u v2]%Z) m
      [KRange (EVar 37) 4100 (2 ^ 48); KRange (EVar 34) 1 31]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    destruct last; cbv iota in Hlast |- *.
    - ex_run 300%nat [0x87878; 0x879b0]%Z (SCR [false; false] [EVar 38; EVar 39] []) HR HK R' HR' Hms.
      all: try v23hhIF_sc2.
      exists R'. eexists. split.
      + eapply ex_msteps_mem; [exact Hms |]. cbn [mem_denot s_log e_addr e_width e_val].
        apply ex_wbytes_eq; [reflexivity | v23hhIF_addr regs | reflexivity].
      + repeat split; try (v23hhIF_reg regs HR'). ex_agree HR HR'.
    - ex_run 300%nat [0x87878; 0x879b0]%Z (SCR [false; true] [EVar 38; EVar 39] []) HR HK R' HR' Hms.
      all: try v23hhIF_sc2.
      exists R'. eexists. split.
      + eapply ex_msteps_mem; [exact Hms |]. cbn [mem_denot s_log e_addr e_width e_val].
        apply ex_wbytes_eq; [reflexivity | v23hhIF_addr regs | reflexivity].
      + repeat split; try (v23hhIF_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma hip_F : forall (last : bool) regs m (s data wpl h shift i : Z) (bs0 bsm : list byte) (v0 vm : word),
    (4096 + 240 <= s < 2 ^ 48)%Z -> (1 <= wpl < 2 ^ 25)%Z -> (1 <= shift <= 31)%Z -> (0 <= i)%Z ->
    (if last then i + 1 = h else i + 1 < h)%Z -> (4 * wpl * h <= 2 ^ 26)%Z ->
    (4096 <= data)%Z -> (data + 4 * wpl * h <= s - 240)%Z ->
    (data mod 4 = 0)%Z -> (data + 4 * wpl * h <= 0x1f4c4 \/ 0x1f4c4 + 128 <= data)%Z ->
    rdn SEGS m (Z_to_bv 64 (data + 4 * (wpl * i))) 4 = Some bs0 -> bytes_le_to_Z bs0 = bv_unsigned v0 ->
    rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * shift))) ->
    rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f4c4)) ->
    rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * shift + 0x1f4c4))) ->
    rdn SEGS m (Z_to_bv 64 (4 * shift + 0x1f4c4)) 4 = Some bsm -> bytes_le_to_Z bsm = bv_unsigned vm ->
    store_ok SEGS m (Z_to_bv 64 (data + 4 * (wpl * i))) 4 = true ->
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 1 = Z_to_bv 64 (data + 4 * (wpl * i)) ->
    getr regs 10 = Z_to_bv 64 (data + 4 * (wpl * i)) -> getr regs 25 = Z_to_bv 64 (data + 4 * (wpl * i)) ->
    getr regs 11 = Z_to_bv 64 shift -> getr regs 8 = Z_to_bv 64 (wpl * i) -> getr regs 9 = Z_to_bv 64 5 -> getr regs 13 = Z_to_bv 64 wpl ->
    getr regs 14 = Z_to_bv 64 i -> getr regs 16 = Z_to_bv 64 h -> getr regs 17 = Z_to_bv 64 wpl -> getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 4 -> getr regs 21 = Z_to_bv 64 data -> getr regs 26 = Z_to_bv 64 shift -> getr regs 30 = Z_to_bv 64 shift ->
    exists regs' (w1 w2 : word),
      msteps SEGS (mkst regs (Z_to_bv 64 0x879b0) m rom)
                  (mkst regs' (Z_to_bv 64 (if last then 0x87b80 else 0x877c4))
                     (wbytes (wbytes m (Z_to_bv 64 (data + 4 * (wpl * i))) (word_to_le_bytes 4 w1)) (Z_to_bv 64 (data + 4 * (wpl * i))) (word_to_le_bytes 4 w2)) rom)
      /\ getr regs' 8 = Z_to_bv 64 (wpl * (i + 1)) /\ getr regs' 14 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun r => In r [1; 7; 8; 10; 11; 12; 14; 18; 25; 27]%list) regs regs'.
  Proof.
    intros last regs m s data wpl h shift i bs0 bsm v0 vm Hs Hw Hsh Hi Hlast Hwh Hd Hd2 Hd4 Htab Rd0 E0 R144 R152 R160 Rdm Em SOK
      H2 H1 H10 H25 H11 H8 H9 H13 H14 H16 H17 H19 H20 H21 H26 H30.
    assert (Hih : (i + 1 <= h)%Z) by (destruct last; lia).
    assert (Hrow : (0 <= wpl * i)%Z /\ (wpl * i + wpl <= wpl * h)%Z /\ (h <= 2 ^ 24)%Z /\ (wpl * h <= 2 ^ 24)%Z) by (repeat split; nia).
    assert (Hp4 : ((data + 4 * (wpl * i)) mod 4 = 0)%Z) by (rewrite (Z.mul_comm 4 (wpl * i)), Z_mod_plus_full; exact Hd4).
    ex_entry regs [s; data; wpl; h; shift; i; wpl * i; data + 4 * (wpl * i); 4 * shift; 4 * shift + 0x1f4c4; extz true 4 (u v0); extz true 4 (u vm)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; data; wpl; h; shift; i; wpl * i; data + 4 * (wpl * i); 4 * shift; 4 * shift + 0x1f4c4; extz true 4 (u v0); extz true 4 (u vm)]%Z) m
      [KRange (EVar 32) (4096 + 240) (2 ^ 48);
       KWord (SA (EVar 32) (-144)) 8 (EVar 40); KWord (SA (EVar 32) (-152)) 8 (ELit 0x1f4c4); KWord (SA (EVar 32) (-160)) 8 (EVar 41);
       KRange (EVar 34) 1 (2 ^ 25); KRange (EVar 35) 1 (2 ^ 31 - 1); KRange (EVar 36) 1 31; KRange (EVar 37) 0 (2 ^ 31 - 2);
       KRange (EVar 38) 0 (2 ^ 24); KRange (EVar 39) 4096 (2 ^ 48); KRange (EVar 40) 4 124; KRange (EVar 41) (0x1f4c4 + 4) (0x1f4c4 + 124)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    destruct last; cbv iota in Hlast |- *.
    - ex_run 400%nat [0x877c4; 0x87b80]%Z (SCR [false; false; false; false] [EVar 42; EVar 43] []) HR HK R' HR' Hms.
      all: try v23hhIF_sc2.
      exists R'. eexists. eexists. split.
      + eapply ex_msteps_mem; [exact Hms |]. cbn [mem_denot s_log e_addr e_width e_val].
        apply ex_wbytes_eq; [apply ex_wbytes_eq; [reflexivity | v23hhIF_addr regs | reflexivity] | v23hhIF_addr regs | reflexivity].
      + repeat split; try (v23hhIF_reg regs HR'). ex_agree HR HR'.
    - ex_run 400%nat [0x877c4; 0x87b80]%Z (SCR [false; false; false; true] [EVar 42; EVar 43] []) HR HK R' HR' Hms.
      all: try v23hhIF_sc2.
      exists R'. eexists. eexists. split.
      + eapply ex_msteps_mem; [exact Hms |]. cbn [mem_denot s_log e_addr e_width e_val].
        apply ex_wbytes_eq; [apply ex_wbytes_eq; [reflexivity | v23hhIF_addr regs | reflexivity] | v23hhIF_addr regs | reflexivity].
      + repeat split; try (v23hhIF_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma hip_E : forall regs m (s : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
    (4096 + 240 <= s < 2 ^ 48)%Z -> ret_ok ret ->
    cellsZ m [(s - 8, ret); (s - 16, v8); (s - 24, v9); (s - 32, v18); (s - 40, v19); (s - 48, v20); (s - 56, v21); (s - 64, v22);
              (s - 72, v23); (s - 80, v24); (s - 88, v25); (s - 96, v26); (s - 104, v27)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 240) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x87b80) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20
      /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26
      /\ getr regs' 27 = v27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hs Hret HC H2.
    cbn [cellsZ] in HC.
    destruct HC as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & _).
    ex_entryL [ret; v8; v9; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27] regs [s] HR.
    assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27] regs [s]) m
                   [KRange (EVar 45) (4096 + 240) (2 ^ 48);
                    KWord (SA (EVar 45) (-8)) 8 (EVar 0); KWord (SA (EVar 45) (-16)) 8 (EVar 1);
                    KWord (SA (EVar 45) (-24)) 8 (EVar 2); KWord (SA (EVar 45) (-32)) 8 (EVar 3);
                    KWord (SA (EVar 45) (-40)) 8 (EVar 4); KWord (SA (EVar 45) (-48)) 8 (EVar 5);
                    KWord (SA (EVar 45) (-56)) 8 (EVar 6); KWord (SA (EVar 45) (-64)) 8 (EVar 7);
                    KWord (SA (EVar 45) (-72)) 8 (EVar 8); KWord (SA (EVar 45) (-80)) 8 (EVar 9);
                    KWord (SA (EVar 45) (-88)) 8 (EVar 10); KWord (SA (EVar 45) (-96)) 8 (EVar 11);
                    KWord (SA (EVar 45) (-104)) 8 (EVar 12)]%Z) by (ex_know regs).
    ex_run 300%nat (@nil Z) (SCR [] [] []) HR HK R' HR' Hms.
    assert (AG : regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs R') by (ex_agree HR HR').
    assert (G1 : getr R' 1 = ret) by (ex_reg regs HR').
    assert (G2 : getr R' 2 = Z_to_bv 64 s) by (ex_reg regs HR').
    assert (G8 : getr R' 8 = v8) by (ex_reg regs HR').
    assert (G9 : getr R' 9 = v9) by (ex_reg regs HR').
    assert (G18 : getr R' 18 = v18) by (ex_reg regs HR').
    assert (G19 : getr R' 19 = v19) by (ex_reg regs HR').
    assert (G20 : getr R' 20 = v20) by (ex_reg regs HR').
    assert (G21 : getr R' 21 = v21) by (ex_reg regs HR').
    assert (G22 : getr R' 22 = v22) by (ex_reg regs HR').
    assert (G23 : getr R' 23 = v23) by (ex_reg regs HR').
    assert (G24 : getr R' 24 = v24) by (ex_reg regs HR').
    assert (G25 : getr R' 25 = v25) by (ex_reg regs HR').
    assert (G26 : getr R' 26 = v26) by (ex_reg regs HR').
    assert (G27 : getr R' 27 = v27) by (ex_reg regs HR').
    cbn [mem_denot] in Hms.
    exists R'. split.
    - eapply msteps_trans; [exact Hms|].
      lazymatch type of Hms with msteps _ _ (mkst _ (Z_to_bv 64 ?p) _ _) => ex_fetch SEGS p F D end.
      lazymatch type of D with decode_any ?w = _ =>
        assert (Dj : decode_any w = Some (Jalr 0 1 0, 4%Z)) by (rewrite D; f_equal; f_equal; f_equal; apply bv_eq; reflexivity) end.
      eapply mst_step; [reflexivity | eapply step_jalr_x0; [exact F | reflexivity | exact Dj | exact G1] |].
      match goal with |- msteps _ (mkst _ ?t _ _) _ => replace t with ret by (symmetry; exact (Hret : v_jalr ret 0 = ret)) end.
      apply mst_refl.
    - repeat split; assumption.
  Qed.

End Segs.
End RotHip.

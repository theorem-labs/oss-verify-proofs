(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRot90cw.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23_code_r90cw_loop V23ExecUb.
Import ListNotations. Import SX2. Import SX2S.
#[local] Ltac exB_sc_hook ::= v23_sc_hook.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac cwc_pcs :=
  repeat match goal with
  | |- context [mkst _ ?a _ _] =>
      lazymatch a with
      | Z_to_bv _ _ => fail
      | _ => let z := eval vm_compute in (bv_unsigned a) in
             replace a with (Z_to_bv 64 z) by (apply bv_eq; reflexivity)
      end
  end.

Section Rot90cw.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma cwa_srlw_hi : forall a : Z, (0 <= a < 2 ^ 26)%Z ->
  v_srlw (Z_to_bv 64 (a + 67108864)) (Z_to_bv 64 27) = Z_to_bv 64 0.
Proof.
  intros a Ha. unfold v_srlw. rewrite !u_Z2bv by lia. change (27 mod 32)%Z with 27%Z.
  rewrite bv_wrap_small by (change (bv_modulus 32) with (2 ^ 32)%Z; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma cwa_div32 : forall x : Z, (0 <= x < 2 ^ 31)%Z ->
  v_sraw (v_add (v_srl (Sem.mul_div M_MUL (Z_to_bv 64 2) (Z_to_bv 64 x)) (Z_to_bv 64 59)) (Z_to_bv 64 x)) (Z_to_bv 64 5) = Z_to_bv 64 (x / 32).
Proof.
  intros x Hx. rewrite m_mul, zbv_mul. unfold v_srl. rewrite !u_Z2bv by lia. change (59 mod 64)%Z with 59%Z.
  rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (2 * x)) by lia. rewrite zbv_add, Z.add_0_l.
  unfold v_sraw. rewrite !u_Z2bv by lia. change (5 mod 32)%Z with 5%Z.
  rewrite (swrap32_small x) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5)%Z with 32%Z.
  rewrite swrap32_small by lia. reflexivity.
Qed.
Lemma cwa_and_srl : forall j : Z, (0 <= j < 2 ^ 31)%Z ->
  v_and (v_srl (Z_to_bv 64 j) (Z_to_bv 64 3)) (Z_to_bv 64 (-4)) = Z_to_bv 64 (4 * (j / 32)).
Proof.
  intros j Hj. rewrite <- (r90_andi_m4_j8 j Hj). unfold v_srl. rewrite !u_Z2bv by lia. change (3 mod 64)%Z with 3%Z.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
  unfold v_and, v_andi. f_equal.
Qed.
Lemma cwa_ovf : forall p k i : Z, (0 <= p)%Z -> (0 <= k)%Z -> (p + k < 2 ^ 64)%Z -> (0 <= i < 2 ^ 31)%Z ->
  Sem.branch_taken BC_NE (Sem.alu64 ALU_XOR (Sem.alu64 ALU_XOR (Sem.alu64 ALU_SLTU (Z_to_bv 64 (p + k)) (Z_to_bv 64 p))
    (Sem.alu64 ALU_SLT (Z_to_bv 64 i) (Z_to_bv 64 0))) (Z_to_bv 64 1)) (Z_to_bv 64 0) = true.
Proof.
  intros p k i Hp Hk Hpk Hi. rewrite !alu_xor, alu_sltu, alu_slt.
  rewrite WalksLib.v_sltu_Z by lia. rewrite WalksLib.v_slt_Z by lia.
  rewrite (proj2 (Z.ltb_ge (p + k) p)) by lia. rewrite (proj2 (Z.ltb_ge i 0)) by lia.
  vm_compute. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Ltac cw_sc :=
  cbn [Sem.branch_taken];
  rewrite ?m_mul, ?zbv_mul, ?alu_add, ?zbv_add, ?alu_sltu, ?alu_xor;
  rewrite ?WalksLib.v_sltu_Z by lia;
  unfold bv_eqb, bv_ltu; rewrite ?u_Z2bv by lia;
  repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b); try lia end;
  vm_compute; reflexivity.
#[local] Ltac cw_fin HR HR' :=
  lazymatch goal with
  | |- Sem.branch_taken _ _ _ = _ => cw_sc
  | |- regs_agree _ _ _ => ex_agree HR HR'
  | |- _ => rewrite ?zbv_addw_small by lia; first [reflexivity | (f_equal; lia)]
  end.
#[local] Ltac cw_norm := rewrite ?m_mul, ?zbv_mul, ?ex_ptr_val, ?alu_add, ?zbv_add, ?zbv_addi.
#[local] Ltac cw_side :=
  lazymatch goal with
  | |- Sem.branch_taken _ _ _ = _ => cw_sc
  | |- _ => cw_norm; rewrite ?u_Z2bv by lia; lia
  end.
#[local] Ltac cw_rd H :=
  lazymatch type of H with rdn _ _ ?a _ = Some ?bs =>
  lazymatch goal with |- exists _, rdn _ _ _ _ = Some _ /\ _ =>
    exists bs; split; [match goal with |- rdn _ _ ?a' _ = _ => replace a' with a by (cw_norm; f_equal; lia) end; exact H | ]
  end end.
#[local] Ltac cw_st H :=
  lazymatch type of H with ?f _ _ ?a _ = true =>
  lazymatch goal with |- f _ _ ?a' _ = true => replace a' with a by (cw_norm; f_equal; lia); exact H end end.
#[local] Ltac cw_nz H :=
  let Heq := fresh "Heq" in
  rewrite Z_to_bv_bv_unsigned; cbn [Sem.branch_taken]; unfold bv_eqb; apply Z.eqb_neq; intro Heq; apply H; apply bv_eq; exact Heq.
#[local] Ltac cw_sgn H9 Hb :=
  rewrite ?H9, ?w_sllw; cbn [Sem.branch_taken]; unfold c_lts in Hb; rewrite Hb; reflexivity.
Lemma cwb_srlw_or : forall a b : Z, (0 <= a < 2 ^ 27)%Z -> (0 <= b < 2 ^ 27)%Z ->
  v_srlw (v_or (Z_to_bv 64 a) (Z_to_bv 64 b)) (Z_to_bv 64 27) = Z_to_bv 64 0.
Proof.
  intros a b Ha Hb. unfold v_or. rewrite !u_Z2bv by lia.
  assert (H0 : (0 <= Z.lor a b)%Z) by (apply Z.lor_nonneg; lia).
  assert (Hs : (Z.lor a b / 2 ^ 27 = 0)%Z).
  { rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_lor, !Z.shiftr_div_pow2 by lia. rewrite !Z.div_small by lia. reflexivity. }
  assert (Hl : (Z.lor a b < 2 ^ 27)%Z).
  { pose proof (Z.div_mod (Z.lor a b) (2 ^ 27) ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (Z.lor a b) (2 ^ 27) ltac:(lia)) as Hm. lia. }
  unfold v_srlw. rewrite !u_Z2bv by lia. change (27 mod 32)%Z with 27%Z.
  rewrite bv_wrap_small by (change (bv_modulus 32) with (2 ^ 32)%Z; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma cwc_sra5 : forall i : Z, (0 <= i < 2 ^ 31)%Z ->
  sext 64 (Sem.alu32 ALU_SRA (Sem.low32 (Z_to_bv 64 i)) (Sem.low32 (Z_to_bv 64 5))) = Z_to_bv 64 (i / 32).
Proof.
  intros i Hi. rewrite w_sraw. unfold v_sraw. rewrite !u_Z2bv by lia. change (5 mod 32)%Z with 5%Z.
  rewrite (swrap32_small i) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5)%Z with 32%Z.
  rewrite swrap32_small by lia. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma cwc_addr : forall lines i : Z, (0 <= i < 2 ^ 31)%Z ->
  Sem.alu64 ALU_ADD (Z_to_bv 64 lines)
    (Sem.mul_div M_MUL (Z_to_bv 64 4) (sext 64 (Sem.alu32 ALU_SRA (Sem.low32 (Z_to_bv 64 i)) (Sem.low32 (Z_to_bv 64 5)))))
  = Z_to_bv 64 (lines + 4 * (i / 32)).
Proof. intros lines i Hi. rewrite cwc_sra5 by lia. rewrite m_mul, zbv_mul. apply ex_ptr_val. Qed.
Lemma cwc_bit : forall (w : word) (i : Z),
  Sem.branch_taken BC_EQ
    (Sem.alu64 ALU_AND (sext 64 (Sem.alu32 ALU_SRL (Sem.low32 w) (Sem.low32 (Sem.alu64 ALU_XOR (Z_to_bv 64 i) (Z_to_bv 64 (-1))))))
       (Z_to_bv 64 1)) (Z_to_bv 64 0)
  = c_eq (v_andi (v_srlw w (v_xori (Z_to_bv 64 i) (-1))) 1) (Z_to_bv 64 0).
Proof. intros w i. rewrite w_srlw, alu_and, alu_xor. reflexivity. Qed.
Lemma cwc_lt : forall a b : Z, (0 <= a < 2 ^ 63)%Z -> (0 <= b < 2 ^ 63)%Z ->
  Sem.branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof.
  intros a b Ha Hb. pose proof (v_slt_Z a b Ha Hb) as H. unfold v_slt in H.
  change (Sem.branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b)) with (c_lts (Z_to_bv 64 a) (Z_to_bv 64 b)).
  destruct (c_lts (Z_to_bv 64 a) (Z_to_bv 64 b)); destruct (a <? b)%Z; try reflexivity;
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.
Ltac cwc_side Hi Hq Hb RS BS RT BT SOK :=
  rewrite ?Z_to_bv_bv_unsigned; rewrite ?cwc_addr by lia;
  first
  [ (rewrite cwc_bit; exact Hb)
  | (eexists; split; [rewrite v_addi_0; exact RS | unfold extz, v_lw; rewrite BS; reflexivity])
  | (eexists; split; [rewrite Z.add_0_r; exact RT | unfold extz, v_lw; rewrite BT; reflexivity])
  | (rewrite Z.add_0_r; exact SOK)
  | (rewrite !u_Z2bv by lia; lia)
  | (rewrite sltu1_nz by lia; vm_compute; reflexivity)
  | (rewrite cwc_sra5 by lia; rewrite alu_sltu, zbv_sltu_ge by lia; rewrite alu_slt, v_slt_Z by lia;
     rewrite (proj2 (Z.ltb_ge _ _)) by lia; vm_compute; reflexivity) ].
Ltac cwc_lsc :=
  first [ (rewrite w_addw, zbv_addw_small, ex_sx32, cwc_lt by lia; first [apply Z.ltb_lt | apply Z.ltb_ge]; lia)
        | (rewrite alu_sltu, zbv_sltu_ge by lia; vm_compute; reflexivity) ].

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma cw_S : forall regs m (s wd hd wpld datas : Z),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= wd < 2 ^ 31)%Z -> (1 <= hd < 2 ^ 31)%Z -> (1 <= wpld < 2 ^ 25)%Z -> (1 <= datas < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)) ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)) ->
    store_ok SEGS m (Z_to_bv 64 (s - 144)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 8 = Z_to_bv 64 datas ->
    exists regs',
      msteps SEGS (mkst regs (0x9726c : word) m rom)
        (mkst regs' (0x9733c : word) (wbytes m (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 hd))) rom)
      /\ getr regs' 31 = Z_to_bv 64 wd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 hd
      /\ getr regs' 14 = Z_to_bv 64 0x4000000 /\ getr regs' 15 = Z_to_bv 64 (4 * wpld) /\ getr regs' 7 = Z_to_bv 64 (128 * wpld)
      /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 17 = Z_to_bv 64 32 /\ getr regs' 6 = Z_to_bv 64 0x4000001 /\ getr regs' 30 = Z_to_bv 64 0
      /\ getr regs' 28 = Z_to_bv 64 (hd / 32) /\ getr regs' 29 = Z_to_bv 64 (32 * (hd / 32))
      /\ regs_agree (fun r => In r [6; 7; 9; 11; 12; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s wd hd wpld datas Hs Hs64 Hwd Hhd Hwp Hda RW RH SOK H2 H10 H8.
    replace (0x9726c : word) with (Z_to_bv 64 0x9726c) by (apply bv_eq; reflexivity).
    replace (0x9733c : word) with (Z_to_bv 64 0x9733c) by (apply bv_eq; reflexivity).
    ex_entry regs [s; wd; hd; wpld; datas] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; wd; hd; wpld; datas]) m
      [KWr (SA (EVar 32) (-144)) 8; KWord (SA (EVar 32) (-108)) 4 (EVar 33); KWord (SA (EVar 32) (-112)) 4 (EVar 34);
       KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1);
       KRange (EVar 35) 1 (2 ^ 25 - 1); KRange (EVar 36) 1 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x9733c]%Z (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - eapply ex_msteps_mem; [exact Hms|].
      cbn [mem_denot s_log e_addr e_width e_val].
      apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs |].
      f_equal. ex_unfoldE. cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite ex_sx32 by lia. reflexivity.
    - repeat split; try (ex_reg regs HR').
      all: rewrite ?ex_sx32 by lia; rewrite ?cwa_div32 by lia; rewrite ?cwa_srlw_hi by lia;
           rewrite ?ex_sllw_small by lia; rewrite ?m_mul, ?zbv_mul.
      all: first [ reflexivity | (apply zbv_snez; lia) | (f_equal; lia) | ex_agree HR HR' ].
  Qed.

  (* [comment removed for export] *)
  Ltac cw_nrm := repeat first [ rewrite w_addw | rewrite w_mulw | rewrite m_mul | rewrite zbv_mul | rewrite ex_ptr_val | rewrite zbv_add
    | rewrite LeptRop.addw_fit by lia | rewrite zbv_mulw_small by lia ].

  Lemma cw_Jw : forall regs m (s wd hd datas wpls wpld datad j : Z),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= j < wd)%Z -> (wd < 2 ^ 31)%Z -> (32 <= hd < 2 ^ 31)%Z -> (0 <= wpls)%Z -> (wpls * wd <= 2 ^ 24)%Z ->
    (0 <= wpld < 2 ^ 63)%Z -> (1 <= datas)%Z -> (datas + 4 * wpls * wd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)) ->
    rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datad)) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 11 = Z_to_bv 64 j -> getr regs 12 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 wd ->
    getr regs 18 = Z_to_bv 64 wpls -> getr regs 8 = Z_to_bv 64 datas -> getr regs 10 = Z_to_bv 64 wpld ->
    getr regs 16 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 32 ->
    exists regs',
      msteps SEGS (mkst regs (0x9733c : word) m rom) (mkst regs' (0x973c8 : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 (4 * (j / 32)) /\ getr regs' 31 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j))
      /\ getr regs' 20 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 datad /\ getr regs' 22 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [13; 19; 20; 21; 22; 23; 31]%list) regs regs'.
  Proof.
    intros regs m s wd hd datas wpls wpld datad j Hs Hs64 Hj Hwd Hhd Hwp Hsz Hwpd Hda Hdend RH RD H2 H11 H12 H31 H18 H8 H10 H16 H17.
    assert (Hww : (wpls <= wpls * wd)%Z) by (rewrite <- (Z.mul_1_r wpls) at 1; apply Z.mul_le_mono_nonneg_l; lia).
    assert (Hw0 : (0 <= wpls * wd)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hm1 : (0 <= (wd - 1 - j) * wpls)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hm3 : (0 <= (1 + j) * wpls)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    replace (0x9733c : word) with (Z_to_bv 64 0x9733c) by (apply bv_eq; reflexivity).
    replace (0x973c8 : word) with (Z_to_bv 64 0x973c8) by (apply bv_eq; reflexivity).
    ex_entry regs [s; wd; hd; datas; wpls; wpld; datad; j] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; wd; hd; datas; wpls; wpld; datad; j]) m
      [KWord (SA (EVar 32) (-144)) 8 (EVar 34); KWord (SA (EVar 32) (-136)) 8 (EVar 38);
       KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 32 (2 ^ 31 - 1);
       KRange (EVar 35) 1 (2 ^ 64 - 1); KRange (EVar 36) 0 (2 ^ 24); KRange (EVar 37) 0 (2 ^ 63 - 1);
       KRange (EVar 39) 0 (2 ^ 31 - 2)]%Z) by (ex_know regs).
    ex_run 400%nat [0x973c8]%Z (SCR [true; true; true; true] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    exists R'. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR'); try (ex_agree HR HR')].
    all: try (apply cwa_and_srl; lia).
    all: try (rewrite WalksLib.v_slt_Z by lia; rewrite (proj2 (Z.ltb_ge wpld 0)) by lia; reflexivity).
    all: cw_nrm.
    all: try (f_equal; lia).
    all: try (apply cwa_ovf; lia).
    all: try (rewrite sltu1_nz by lia; reflexivity).
    all: apply v23_eq_t; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cw_Jt : forall regs m (s wd hd datas wpls wpld datad j : Z),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= j < wd)%Z -> (wd < 2 ^ 31)%Z -> (0 <= hd < 32)%Z -> (0 <= wpls)%Z -> (wpls * wd <= 2 ^ 24)%Z ->
    (0 <= wpld < 2 ^ 63)%Z -> (1 <= datas)%Z -> (datas + 4 * wpls * wd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)) ->
    rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datad)) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 11 = Z_to_bv 64 j -> getr regs 12 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 wd ->
    getr regs 18 = Z_to_bv 64 wpls -> getr regs 8 = Z_to_bv 64 datas -> getr regs 10 = Z_to_bv 64 wpld ->
    getr regs 16 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 32 ->
    exists regs',
      msteps SEGS (mkst regs (0x9733c : word) m rom) (mkst regs' (0x974e4 : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 (4 * (j / 32)) /\ getr regs' 31 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j))
      /\ getr regs' 20 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 datad
      /\ regs_agree (fun r => In r [13; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    intros regs m s wd hd datas wpls wpld datad j Hs Hs64 Hj Hwd Hhd Hwp Hsz Hwpd Hda Hdend RH RD H2 H11 H12 H31 H18 H8 H10 H16 H17.
    assert (Hww : (wpls <= wpls * wd)%Z) by (rewrite <- (Z.mul_1_r wpls) at 1; apply Z.mul_le_mono_nonneg_l; lia).
    assert (Hw0 : (0 <= wpls * wd)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hm1 : (0 <= (wd - 1 - j) * wpls)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hm3 : (0 <= (1 + j) * wpls)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    replace (0x9733c : word) with (Z_to_bv 64 0x9733c) by (apply bv_eq; reflexivity).
    replace (0x974e4 : word) with (Z_to_bv 64 0x974e4) by (apply bv_eq; reflexivity).
    ex_entry regs [s; wd; hd; datas; wpls; wpld; datad; j] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; wd; hd; datas; wpls; wpld; datad; j]) m
      [KWord (SA (EVar 32) (-144)) 8 (EVar 34); KWord (SA (EVar 32) (-136)) 8 (EVar 38);
       KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 0 31;
       KRange (EVar 35) 1 (2 ^ 64 - 1); KRange (EVar 36) 0 (2 ^ 24); KRange (EVar 37) 0 (2 ^ 63 - 1);
       KRange (EVar 39) 0 (2 ^ 31 - 2)]%Z) by (ex_know regs).
    ex_run 400%nat [0x974e4]%Z (SCR [true; true; true; true] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    exists R'. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR'); try (ex_agree HR HR')].
    all: try (apply cwa_and_srl; lia).
    all: try (rewrite WalksLib.v_slt_Z by lia; rewrite (proj2 (Z.ltb_ge wpld 0)) by lia; reflexivity).
    all: cw_nrm.
    all: try (f_equal; lia).
    all: try (apply cwa_ovf; lia).
    all: try (rewrite sltu1_nz by lia; reflexivity).
    all: apply v23_eq_t; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cw_Kz : forall regs m (lines lined wpld k datas : Z) (bs : list byte) (v : word),
    rdn SEGS m (Z_to_bv 64 (lines + 4 * k)) 4 = Some bs -> bytes_le_to_Z bs = bv_unsigned v -> v_lw v = Z_to_bv 64 0 ->
    (0 <= k < 2 ^ 30)%Z -> (1 <= datas <= lines)%Z -> (lines + 4 * k + 4 <= 2 ^ 64)%Z -> (lines mod 4 = 0)%Z ->
    (1 <= lined)%Z -> (0 <= wpld)%Z -> (lined + 128 * wpld < 2 ^ 64)%Z ->
    getr regs 22 = Z_to_bv 64 k -> getr regs 31 = Z_to_bv 64 lines -> getr regs 21 = Z_to_bv 64 lined -> getr regs 7 = Z_to_bv 64 (128 * wpld) ->
    getr regs 16 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 datas -> getr regs 30 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x973c8 : word) m rom) (mkst regs' (0x973c0 : word) m rom)
      /\ getr regs' 21 = Z_to_bv 64 (lined + 128 * wpld)
      /\ regs_agree (fun r => In r [9; 21; 24; 25]%list) regs regs'.
  Proof.
    intros regs m lines lined wpld k datas bs v Hrd Hbs Hv0 Hk Hda Hle Hla Hl Hw Hlw H22 H31 H21 H7 H16 H8 H30 H20.
    replace (0x973c8 : word) with (Z_to_bv 64 0x973c8) by (apply bv_eq; reflexivity).
    replace (0x973c0 : word) with (Z_to_bv 64 0x973c0) by (apply bv_eq; reflexivity).
    ex_entry regs [k; lines; lined; (128 * wpld)%Z; datas] HR.
    assert (HK : know_ok SEGS (ex_env regs [k; lines; lined; (128 * wpld)%Z; datas]) m
      [KRange (EVar 32) 0 (2 ^ 30 - 1); KRange (EVar 33) 1 (2 ^ 64 - 1); KAlign (EVar 33) 4;
       KRange (EVar 34) 1 (2 ^ 64 - 1); KRange (EVar 35) 0 (2 ^ 64 - 1); KRange (EVar 36) 1 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x973c0]%Z (SCR [true; true; true; true] [ELit 0] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R'. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR')].
      all: cw_fin HR HR'. }
    all: first [ (cw_rd Hrd; rewrite Hbs; exact Hv0) | cw_side ].
  Qed.

  (* [comment removed for export] *)
  Lemma cw_Knz : forall regs m (lines lined k datas : Z) (bs : list byte) (v : word),
    rdn SEGS m (Z_to_bv 64 (lines + 4 * k)) 4 = Some bs -> bytes_le_to_Z bs = bv_unsigned v -> v_lw v <> Z_to_bv 64 0 ->
    (0 <= k < 2 ^ 25)%Z -> (1 <= datas <= lines)%Z -> (lines + 4 * k + 4 <= 2 ^ 64)%Z -> (lines mod 4 = 0)%Z ->
    (0 <= lined < 2 ^ 64)%Z -> (lined mod 4 = 0)%Z ->
    getr regs 22 = Z_to_bv 64 k -> getr regs 31 = Z_to_bv 64 lines -> getr regs 21 = Z_to_bv 64 lined ->
    getr regs 16 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 datas -> getr regs 6 = Z_to_bv 64 0x4000001 -> getr regs 14 = Z_to_bv 64 0x4000000 ->
    exists regs',
      msteps SEGS (mkst regs (0x973c8 : word) m rom) (mkst regs' (0x97420 : word) m rom)
      /\ getr regs' 9 = v_lw v /\ getr regs' 24 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 0 /\ getr regs' 26 = Z_to_bv 64 lined
      /\ regs_agree (fun r => In r [9; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m lines lined k datas bs v Hrd Hbs Hv0 Hk Hda Hle Hla Hl Hlm H22 H31 H21 H16 H8 H6 H14.
    replace (0x973c8 : word) with (Z_to_bv 64 0x973c8) by (apply bv_eq; reflexivity).
    replace (0x97420 : word) with (Z_to_bv 64 0x97420) by (apply bv_eq; reflexivity).
    ex_entry regs [k; lines; lined; datas; u (v_lw v)] HR.
    assert (HK : know_ok SEGS (ex_env regs [k; lines; lined; datas; u (v_lw v)]) m
      [KRange (EVar 32) 0 (2 ^ 25 - 1); KRange (EVar 33) 1 (2 ^ 64 - 1); KAlign (EVar 33) 4;
       KRange (EVar 34) 0 (2 ^ 64 - 1); KAlign (EVar 34) 4; KRange (EVar 35) 1 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x97420]%Z (SCR [true; true; false] [EVar 36] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R'. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR')].
      all: first [ apply Z_to_bv_bv_unsigned | (rewrite cwb_srlw_or by lia; reflexivity) | cw_fin HR HR' ]. }
    all: first [ (cw_rd Hrd; rewrite Hbs; rewrite Z_to_bv_bv_unsigned; reflexivity) | cw_nz Hv0 | cw_side ].
  Qed.

  (* [comment removed for export] *)
  Lemma cw_M : forall (b : bool) regs m (lined off mm : Z) (v : word) (bt : list byte) (vt : word),
    c_lts (v_sllw (v_lw v) (Z_to_bv 64 mm)) (Z_to_bv 64 0) = b ->
    (1 <= lined)%Z -> (0 <= off)%Z -> (lined + off + 4 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (lined + off)) 4 = Some bt -> bytes_le_to_Z bt = bv_unsigned vt ->
    store_ok SEGS m (Z_to_bv 64 (lined + off)) 4 = true ->
    getr regs 9 = v_lw v -> getr regs 24 = Z_to_bv 64 mm -> getr regs 26 = Z_to_bv 64 lined -> getr regs 21 = Z_to_bv 64 lined ->
    getr regs 19 = Z_to_bv 64 off -> getr regs 25 = Z_to_bv 64 0 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x97420 : word) m rom) (mkst regs' (0x9746c : word) m' rom)
      /\ (if b then exists wv : word, m' = wbytes m (Z_to_bv 64 (lined + off)) (word_to_le_bytes 4 wv) else m' = m)
      /\ getr regs' 27 = Z_to_bv 64 lined
      /\ regs_agree (fun r => In r [1; 5; 27]%list) regs regs'.
  Proof.
    intros b regs m lined off mm v bt vt Hb Hl Ho Hlo Hrd Hbt SOK H9 H24 H26 H21 H19 H25.
    replace (0x97420 : word) with (Z_to_bv 64 0x97420) by (apply bv_eq; reflexivity).
    replace (0x9746c : word) with (Z_to_bv 64 0x9746c) by (apply bv_eq; reflexivity).
    ex_entry regs [lined; off; mm; extz true 4 (u vt)] HR.
    assert (HK : know_ok SEGS (ex_env regs [lined; off; mm; extz true 4 (u vt)]) m
      [KRange (EVar 32) 1 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    destruct b.
    - ex_run 400%nat [0x9746c]%Z (SCR [false; true; true] [EVar 35] []) HR HK R' HR' Hms.
      all: cycle -1.
      { exists R'. eexists. split; [exact Hms | split; [ | split]].
        - hnf. eexists. cbn [mem_denot s_log e_addr e_width e_val]. apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity].
        - ex_reg regs HR'.
        - ex_agree HR HR'. }
      all: first [ (cw_rd Hrd; rewrite Hbt; reflexivity) | cw_st SOK | cw_sgn H9 Hb | cw_side ].
    - ex_run 400%nat [0x9746c]%Z (SCR [true] [EVar 35] []) HR HK R' HR' Hms.
      all: cycle -1.
      { exists R', m. split; [ex_mem regs Hms | split; [reflexivity | split; [ex_reg regs HR' | ex_agree HR HR']]]. }
      all: first [ cw_sgn H9 Hb | cw_side ].
  Qed.

  (* [comment removed for export] *)
  Lemma cw_Mn : forall regs m (mm lined wpld : Z), (0 <= mm)%Z -> (mm + 1 < 32)%Z ->
    (1 <= lined)%Z -> (0 <= wpld)%Z -> (lined + 4 * wpld < 2 ^ 64)%Z ->
    getr regs 24 = Z_to_bv 64 mm -> getr regs 21 = Z_to_bv 64 lined -> getr regs 26 = Z_to_bv 64 lined -> getr regs 27 = Z_to_bv 64 lined ->
    getr regs 15 = Z_to_bv 64 (4 * wpld) -> getr regs 17 = Z_to_bv 64 32 -> getr regs 20 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x9746c : word) m rom) (mkst regs' (0x97420 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (mm + 1) /\ getr regs' 21 = Z_to_bv 64 (lined + 4 * wpld) /\ getr regs' 26 = Z_to_bv 64 (lined + 4 * wpld)
      /\ regs_agree (fun r => In r [1; 5; 13; 21; 24; 26]%list) regs regs'.
  Proof.
    intros regs m mm lined wpld Hm0 Hm1 Hl Hw Hlw H24 H21 H26 H27 H15 H17 H20.
    replace (0x9746c : word) with (Z_to_bv 64 0x9746c) by (apply bv_eq; reflexivity).
    replace (0x97420 : word) with (Z_to_bv 64 0x97420) by (apply bv_eq; reflexivity).
    ex_entry regs [mm; lined; (4 * wpld)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [mm; lined; (4 * wpld)%Z]) m
      [KRange (EVar 32) 0 30; KRange (EVar 33) 1 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x97420]%Z (SCR [true; true] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    exists R'. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR')].
    all: cw_fin HR HR'.
  Qed.

  Lemma cw_Mx : forall regs m (mm lined wpld : Z), (mm + 1 = 32)%Z ->
    (1 <= lined)%Z -> (0 <= wpld)%Z -> (lined + 4 * wpld < 2 ^ 64)%Z ->
    getr regs 24 = Z_to_bv 64 mm -> getr regs 21 = Z_to_bv 64 lined -> getr regs 26 = Z_to_bv 64 lined -> getr regs 27 = Z_to_bv 64 lined ->
    getr regs 15 = Z_to_bv 64 (4 * wpld) -> getr regs 17 = Z_to_bv 64 32 -> getr regs 20 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x9746c : word) m rom) (mkst regs' (0x973c0 : word) m rom)
      /\ getr regs' 21 = Z_to_bv 64 (lined + 4 * wpld)
      /\ regs_agree (fun r => In r [1; 5; 13; 21; 24; 26]%list) regs regs'.
  Proof.
    intros regs m mm lined wpld Hm1 Hl Hw Hlw H24 H21 H26 H27 H15 H17 H20.
    assert (mm = 31)%Z by lia. subst mm.
    replace (0x9746c : word) with (Z_to_bv 64 0x9746c) by (apply bv_eq; reflexivity).
    replace (0x973c0 : word) with (Z_to_bv 64 0x973c0) by (apply bv_eq; reflexivity).
    ex_entry regs [lined; (4 * wpld)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [lined; (4 * wpld)%Z]) m
      [KRange (EVar 32) 1 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x973c0]%Z (SCR [true; true] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    exists R'. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR')].
    all: cw_fin HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma cw_Kn : forall regs m (k nsw : Z), (0 <= k)%Z -> (k + 1 < nsw < 2 ^ 31)%Z ->
    getr regs 22 = Z_to_bv 64 k -> getr regs 28 = Z_to_bv 64 nsw ->
    exists regs',
      msteps SEGS (mkst regs (0x973c0 : word) m rom) (mkst regs' (0x973c8 : word) m rom)
      /\ getr regs' 22 = Z_to_bv 64 (k + 1)
      /\ regs_agree (fun r => In r [22]%list) regs regs'.
  Proof.
    intros regs m k nsw Hk Hn H22 H28.
    replace (0x973c0 : word) with (Z_to_bv 64 0x973c0) by (apply bv_eq; reflexivity).
    replace (0x973c8 : word) with (Z_to_bv 64 0x973c8) by (apply bv_eq; reflexivity).
    ex_entry regs [k; nsw] HR.
    assert (HK : know_ok SEGS (ex_env regs [k; nsw]) m [KRange (EVar 32) 0 (2 ^ 31 - 3); KRange (EVar 33) 2 (2 ^ 31 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x973c8]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R'. split; [ex_mem regs Hms | split; [ex_reg regs HR' | ex_agree HR HR']].
      rewrite LeptRop.addw_fit by lia. reflexivity. }
    rewrite w_addw, LeptRop.addw_fit by lia. ex_br.
  Qed.

  Lemma cw_Kx : forall regs m (s k nsw hd : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= k)%Z -> (k + 1 = nsw)%Z -> (nsw < 2 ^ 31)%Z -> (0 <= hd < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 22 = Z_to_bv 64 k -> getr regs 28 = Z_to_bv 64 nsw ->
    exists regs',
      msteps SEGS (mkst regs (0x973c0 : word) m rom) (mkst regs' (0x974e4 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 hd /\ getr regs' 22 = Z_to_bv 64 nsw
      /\ regs_agree (fun r => In r [9; 22]%list) regs regs'.
  Proof.
    intros regs m s k nsw hd Hs Hs64 Hk Hkn Hn Hhd RH H2 H22 H28.
    replace (0x973c0 : word) with (Z_to_bv 64 0x973c0) by (apply bv_eq; reflexivity).
    replace (0x974e4 : word) with (Z_to_bv 64 0x974e4) by (apply bv_eq; reflexivity).
    ex_entry regs [s; k; nsw; hd] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; k; nsw; hd]) m
      [KWord (SA (EVar 32) (-112)) 4 (EVar 35); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 2);
       KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x974e4]%Z (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR'); try (ex_agree HR HR')].
    - apply ex_sx32. lia.
    - rewrite LeptRop.addw_fit by lia. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cw_T0e : forall regs m (hd a7 : Z), (0 <= hd < 2 ^ 31)%Z -> (0 <= a7 < 2 ^ 31)%Z -> (hd <= a7)%Z ->
    getr regs 29 = Z_to_bv 64 a7 -> getr regs 9 = Z_to_bv 64 hd ->
    exists regs',
      msteps SEGS (mkst regs (0x974e4 : word) m rom) (mkst regs' (0x97328 : word) m rom)
      /\ regs_agree (fun r => In r ([] : list (bv 5))%list) regs regs'.
  Proof.
    intros regs m hd a7 Hhd Ha7 Hle H29 H9.
    replace (0x974e4 : word) with (Z_to_bv 64 0x974e4) by (apply bv_eq; reflexivity).
    replace (0x97328 : word) with (Z_to_bv 64 0x97328) by (apply bv_eq; reflexivity).
    ex_entry regs [hd; a7] HR.
    assert (HK : know_ok SEGS (ex_env regs [hd; a7]) m [KRange (EVar 32) 0 (2 ^ 31 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x97328]%Z (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms | ex_agree HR HR'].
  Qed.

  Lemma cw_T0s : forall regs m (hd a7 lined : Z), (0 <= hd < 2 ^ 31)%Z -> (0 <= a7 < 2 ^ 31)%Z -> (a7 < hd)%Z ->
    (0 <= lined < 2 ^ 64)%Z -> (lined mod 4 = 0)%Z ->
    getr regs 29 = Z_to_bv 64 a7 -> getr regs 9 = Z_to_bv 64 hd -> getr regs 21 = Z_to_bv 64 lined ->
    exists regs',
      msteps SEGS (mkst regs (0x974e4 : word) m rom) (mkst regs' (0x974fc : word) m rom)
      /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 24 = Z_to_bv 64 lined /\ getr regs' 25 = Z_to_bv 64 a7
      /\ regs_agree (fun r => In r [13; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs m hd a7 lined Hhd Ha7 Hlt Hl Hl4 H29 H9 H21.
    replace (0x974e4 : word) with (Z_to_bv 64 0x974e4) by (apply bv_eq; reflexivity).
    replace (0x974fc : word) with (Z_to_bv 64 0x974fc) by (apply bv_eq; reflexivity).
    ex_entry regs [hd; a7; lined] HR.
    assert (HK : know_ok SEGS (ex_env regs [hd; a7; lined]) m
      [KRange (EVar 32) 1 (2 ^ 31 - 1); KRange (EVar 33) 0 (2 ^ 31 - 2); KRange (EVar 34) 0 (2 ^ 64 - 1); KAlign (EVar 34) 4]%Z) by (ex_know regs).
    ex_run 400%nat [0x974fc]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR'); try (ex_agree HR HR')].
  Qed.

  (* [comment removed for export] *)
  Lemma cw_T : forall (b : bool) regs m (lines lined i off datas : Z) (bs : list byte) (v : word) (bt : list byte) (vt : word),
    (0 <= i < 2 ^ 31)%Z -> (1 <= datas <= lines)%Z -> (lines + 4 * (i / 32) + 4 <= 2 ^ 64)%Z -> (lines mod 4 = 0)%Z ->
    (1 <= lined)%Z -> (0 <= off)%Z -> (lined + off + 4 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (lines + 4 * (i / 32))) 4 = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
    c_eq (v_andi (v_srlw (v_lw v) (v_xori (Z_to_bv 64 i) (-1))) 1) (Z_to_bv 64 0) = b ->
    rdn SEGS m (Z_to_bv 64 (lined + off)) 4 = Some bt -> bytes_le_to_Z bt = bv_unsigned vt ->
    store_ok SEGS m (Z_to_bv 64 (lined + off)) 4 = true ->
    getr regs 25 = Z_to_bv 64 i -> getr regs 31 = Z_to_bv 64 lines -> getr regs 21 = Z_to_bv 64 lined -> getr regs 24 = Z_to_bv 64 lined ->
    getr regs 19 = Z_to_bv 64 off -> getr regs 23 = Z_to_bv 64 0 -> getr regs 16 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 datas ->
    exists regs' m',
      msteps SEGS (mkst regs (0x974fc : word) m rom) (mkst regs' (0x97598 : word) m' rom)
      /\ (if b then m' = m else exists wv : word, m' = wbytes m (Z_to_bv 64 (lined + off)) (word_to_le_bytes 4 wv))
      /\ getr regs' 9 = Z_to_bv 64 lined
      /\ regs_agree (fun r => In r [5; 9; 13; 26]%list) regs regs'.
  Proof.
    intros b regs m lines lined i off datas bs v bt vt Hi Hd Hlr Hla Hl Ho Hlo RS BS Hb RT BT SOK H25 H31 H21 H24 H19 H23 H16 H8.
    cwc_pcs.
    ex_entry regs [lines; lined; i; off; datas; u (v_lw v); u (v_lw vt)] HR.
    assert (HK : know_ok SEGS (ex_env regs [lines; lined; i; off; datas; u (v_lw v); u (v_lw vt)]) m
      [KAlign (EVar 32) 4;
       KRange (EVar 32) 1 (2 ^ 64 - 4); KRange (EVar 33) 1 (2 ^ 64 - 4); KRange (EVar 34) 0 (2 ^ 31 - 1);
       KRange (EVar 35) 0 (2 ^ 64 - 5); KRange (EVar 36) 1 (2 ^ 64 - 4)]%Z) by (ex_know regs).
    assert (Hq : (0 <= i / 32 <= i)%Z) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    destruct b.
    - match goal with |- context [msteps _ _ (mkst _ (Z_to_bv 64 ?z) _ _)] =>
        ex_run 400%nat [z]%Z (SCR [true; true; true] [EVar 37] []) HR HK R' HR' Hms end.
      Unshelve.
      all: try (cwc_side Hi Hq Hb RS BS RT BT SOK).
      exists R', m. split; [ex_mem regs Hms|]. split; [reflexivity|]. split.
      + ex_reg regs HR'.
      + ex_agree HR HR'.
    - match goal with |- context [msteps _ _ (mkst _ (Z_to_bv 64 ?z) _ _)] =>
        ex_run 400%nat [z]%Z (SCR [true; true; false; true; true] [EVar 37; EVar 38] []) HR HK R' HR' Hms end.
      Unshelve.
      all: try (cwc_side Hi Hq Hb RS BS RT BT SOK).
      do 2 eexists. split; [exact Hms|]. split; [|split].
      + cbn [mem_denot s_log e_addr e_width e_val]. eexists.
        apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity].
      + ex_reg regs HR'.
      + ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma cw_Tn : forall regs m (s i hd lined wpld : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < hd < 2 ^ 31)%Z ->
    (1 <= lined)%Z -> (0 <= wpld)%Z -> (lined + 4 * wpld < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 25 = Z_to_bv 64 i -> getr regs 9 = Z_to_bv 64 lined ->
    getr regs 21 = Z_to_bv 64 lined -> getr regs 24 = Z_to_bv 64 lined -> getr regs 15 = Z_to_bv 64 (4 * wpld) -> getr regs 20 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x97598 : word) m rom) (mkst regs' (0x974fc : word) m rom)
      /\ getr regs' 25 = Z_to_bv 64 (i + 1) /\ getr regs' 21 = Z_to_bv 64 (lined + 4 * wpld) /\ getr regs' 24 = Z_to_bv 64 (lined + 4 * wpld)
      /\ getr regs' 9 = Z_to_bv 64 hd
      /\ regs_agree (fun r => In r [5; 9; 13; 21; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s i hd lined wpld Hs Hs64 Hi Hhd Hl Hw Hlw RH H2 H25 H9 H21 H24 H15 H20.
    cwc_pcs.
    ex_entry regs [s; i; hd; lined; (4 * wpld)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; i; hd; lined; (4 * wpld)%Z]) m
      [KWord (SA (EVar 32) (-112)) 4 (EVar 34);
       KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 3); KRange (EVar 34) 2 (2 ^ 31 - 1);
       KRange (EVar 35) 1 (2 ^ 64 - 1); KRange (EVar 36) 0 (2 ^ 64 - 2)]%Z) by (ex_know regs).
    match goal with |- context [msteps _ _ (mkst _ (Z_to_bv 64 ?z) _ _)] =>
      ex_run 400%nat [z]%Z (SCR [true; true; true] [] []) HR HK R' HR' Hms end.
    Unshelve.
    all: try cwc_lsc.
    exists R'. split; [ex_mem regs Hms|].
    repeat split.
    all: try (ex_reg regs HR').
    - rewrite zbv_addw_small by lia. reflexivity.
    - apply ex_sx32. lia.
    - ex_agree HR HR'.
  Qed.

  Lemma cw_Tx : forall regs m (s i hd lined wpld : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = hd)%Z -> (hd < 2 ^ 31)%Z ->
    (1 <= lined)%Z -> (0 <= wpld)%Z -> (lined + 4 * wpld < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 25 = Z_to_bv 64 i -> getr regs 9 = Z_to_bv 64 lined ->
    getr regs 21 = Z_to_bv 64 lined -> getr regs 24 = Z_to_bv 64 lined -> getr regs 15 = Z_to_bv 64 (4 * wpld) -> getr regs 20 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x97598 : word) m rom) (mkst regs' (0x97328 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 hd
      /\ regs_agree (fun r => In r [5; 9; 13; 21; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s i hd lined wpld Hs Hs64 Hi Hhd Hhd2 Hl Hw Hlw RH H2 H25 H9 H21 H24 H15 H20.
    replace (0x97598 : word) with (Z_to_bv 64 0x97598) by (apply bv_eq; reflexivity).
    replace (0x97328 : word) with (Z_to_bv 64 0x97328) by (apply bv_eq; reflexivity).
    ex_entry regs [s; i; hd; lined; (4 * wpld)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; i; hd; lined; (4 * wpld)%Z]) m
      [KWord (SA (EVar 32) (-112)) 4 (EVar 34);
       KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 2); KRange (EVar 34) 1 (2 ^ 31 - 1);
       KRange (EVar 35) 1 (2 ^ 64 - 1); KRange (EVar 36) 0 (2 ^ 64 - 2)]%Z) by (ex_know regs).
    ex_run 400%nat [0x97328]%Z (SCR [true; true; false] [] []) HR HK R' HR' Hms.
    Unshelve.
    all: try cwc_lsc.
    exists R'. split; [ex_mem regs Hms|].
    repeat split.
    all: try (ex_reg regs HR').
    all: try (apply ex_sx32; lia).
    all: ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma cw_Rn : forall regs m (s j wd : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= j)%Z -> (j + 1 < wd < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 11 = Z_to_bv 64 j -> getr regs 12 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x97328 : word) m rom) (mkst regs' (0x9733c : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 (j + 1) /\ getr regs' 12 = Z_to_bv 64 (j + 1) /\ getr regs' 31 = Z_to_bv 64 wd
      /\ regs_agree (fun r => In r [11; 12; 31]%list) regs regs'.
  Proof.
    intros regs m s j wd Hs Hs64 Hj Hwd RW H2 H11 H12.
    eexists. split.
    - stepLD F_97328 D_97328 (word_to_le_bytes 4 (Z_to_bv 64 wd)) (Z_to_bv 64 wd)
        ltac:(addr_norm; exact RW) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small wd) by lia.
      stepiv F_9732c D_9732c (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      zv F_97330 D_97330 (Z_to_bv 64 (j + 1)).
      stepb_tk F_97334 D_97334 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma cw_Rx : forall regs m (s j wd : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= j)%Z -> (j + 1 = wd)%Z -> (wd < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 11 = Z_to_bv 64 j -> getr regs 12 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x97328 : word) m rom) (mkst regs' (0x98a2c : word) m rom)
      /\ regs_agree (fun r => In r [11; 12; 31]%list) regs regs'.
  Proof.
    intros regs m s j wd Hs Hs64 Hj Hwd Hwd2 RW H2 H11 H12.
    eexists. split.
    - stepLD F_97328 D_97328 (word_to_le_bytes 4 (Z_to_bv 64 wd)) (Z_to_bv 64 wd)
        ltac:(addr_norm; exact RW) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small wd) by lia.
      stepiv F_9732c D_9732c (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      zv F_97330 D_97330 (Z_to_bv 64 (j + 1)).
      stepb_ft F_97334 D_97334 ltac:(condZ).
      sn F_97338 D_97338.
      apply mst_refl.
    - solve_regs_agree.
  Qed.

End Segs.
End Rot90cw.

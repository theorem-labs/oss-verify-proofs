(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV FPStepsB Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib DitherLoop LeptExec LeptExecX LeptExecFP LeptExecB LeptFPB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpSiteB.
From stdpp.bitvector Require Import tactics.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bw_low32 : forall z, low32 (Z_to_bv 64 z) = Z_to_bv 32 z.
Proof. intros z. unfold low32. bv_solve. Qed.
Lemma bw_alu32_add : forall a b, alu32 ALU_ADD (Z_to_bv 32 a) (Z_to_bv 32 b) = Z_to_bv 32 (a + b).
Proof. intros a b. unfold alu32, alu. bv_solve. Qed.
Lemma bw_alu32_sub : forall a b, alu32 ALU_SUB (Z_to_bv 32 a) (Z_to_bv 32 b) = Z_to_bv 32 (a - b).
Proof. intros a b. unfold alu32, alu. bv_solve. Qed.
Lemma bw_md32_mul : forall a b, mul_div M_MUL (Z_to_bv 32 a) (Z_to_bv 32 b) = Z_to_bv 32 (a * b).
Proof. intros a b. unfold mul_div. bv_solve. Qed.
Lemma bw_sext64 : forall z, (- 2 ^ 31 <= z < 2 ^ 31)%Z -> sext 64 (Z_to_bv 32 z) = Z_to_bv 64 z.
Proof. intros z H. unfold sext. apply bv_eq. rewrite bv_sign_extend_unsigned. bv_solve. Qed.
Lemma bw_md32_div : forall a b, (- 2 ^ 31 <= a < 2 ^ 31)%Z -> (0 < b < 2 ^ 31)%Z ->
  mul_div M_DIV (Z_to_bv 32 a) (Z_to_bv 32 b) = Z_to_bv 32 (Z.quot a b).
Proof.
  intros a b Ha Hb. unfold mul_div. cbv zeta.
  assert (E : bv_unsigned (Z_to_bv 32 b) = b) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
  rewrite E. destruct (Z.eqb_spec b 0) as [|NE]; [lia|].
  apply bv_eq. rewrite bv_quots_unsigned, !Z_to_bv_unsigned, !Z_to_bv_signed.
  rewrite !bv_swrap_small by (replace (bv_half_modulus 32) with (2 ^ 31)%Z by reflexivity; lia). reflexivity.
Qed.
Lemma br_ne_same : forall x y, x = y -> branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y ->. unfold branch_taken, bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma quot9_rng : forall a, (-2295 <= a <= 2295)%Z -> (-255 <= Z.quot a 9 <= 255)%Z.
Proof.
  intros a H. destruct (Z_le_gt_dec 0 a) as [H0|H0].
  - rewrite Z.quot_div_nonneg by lia.
    assert (0 <= a / 9)%Z by (apply Z.div_pos; lia). assert (a / 9 <= 255)%Z by (apply Z.div_le_upper_bound; lia). lia.
  - replace a with (- (- a))%Z by lia. rewrite Z.quot_opp_l by lia. rewrite Z.quot_div_nonneg by lia.
    assert (0 <= - a / 9)%Z by (apply Z.div_pos; lia). assert (- a / 9 <= 255)%Z by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma bw_sext64_quot9 : forall a, (-2295 <= a <= 2295)%Z -> sext 64 (Z_to_bv 32 (Z.quot a 9)) = Z_to_bv 64 (Z.quot a 9).
Proof. intros a H. pose proof (quot9_rng a H). apply bw_sext64. lia. Qed.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac bw_norm :=
  repeat first [ rewrite ex_sx32 by lia | rewrite bw_low32 | rewrite bw_alu32_add | rewrite bw_alu32_sub
               | rewrite bw_md32_mul | rewrite bw_md32_div by lia | rewrite bw_sext64_quot9 by lia | rewrite bw_sext64 by lia
               | rewrite alu_add | rewrite alu_sub | rewrite m_mul | rewrite zbv_add | rewrite zbv_sub | rewrite zbv_mul ].
Ltac bw_quot :=
  repeat match goal with |- context [Z.quot ?a 9] =>
    let Q := fresh "Q" in let q := fresh "q" in
    pose proof (quot9_rng a ltac:(lia)) as Q; set (q := Z.quot a 9) in *; clearbody q end.
Ltac bw_ovf := rewrite ?alu_add, ?alu_sltu, ?alu_slt, ?alu_xor, ?m_mul; rewrite ?zbv_mul, ?zbv_add;
  rewrite ?exB_ovf_idiom by lia; rewrite ?zbv_sltu_ge by lia; ex_br.
Ltac bw_sok :=
  lazymatch goal with |- RiscvSemantics.store_ok _ _ _ _ = true =>
    rewrite ?alu_add, ?m_mul; rewrite ?zbv_mul, ?zbv_add, ?zbv_addi;
    match goal with H : RiscvSemantics.store_ok _ _ (Z_to_bv 64 _) _ = true |- RiscvSemantics.store_ok _ _ (Z_to_bv 64 _) _ = true =>
      eapply store_ok_sub; [ | exact H | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
    end
  end.
Ltac bw_lin := rewrite ?alu_add, ?m_mul; rewrite ?zbv_mul, ?zbv_add, ?zbv_addi; rewrite ?u_Z2bv by lia; lia.
Ltac bw_hook := first [ (bw_norm; bw_quot; bw_norm; apply br_ne_same; lia) | bw_ovf | bw_sok | bw_lin ].

Definition kfr_ok (kf : Z) (M : word -> option byte) : Prop := forall v, (0 <= v < 256)%Z -> exists x, rdn SEGS M (Z_to_bv 64 (kf + 4 * v)) 4 = Some (Z_to_le_bytes 4 x) /\ kfr_le1 x.
Definition kcell_ok (arr n : Z) (M : word -> option byte) : Prop :=
  forall i, (0 <= i < n)%Z -> exists x, rdn SEGS M (Z_to_bv 64 (arr + 4 * i)) 4 = Some (Z_to_le_bytes 4 x) /\ FB fmt_single 1 x.

Section XB.
Variable segs : list Segment.

Lemma xb_fp : forall E m rom ms0 (fx fx' : FPState) pc sr log,
  ex_st segs E m rom ms0 fx pc sr log ->
  (forall R, regs_ok E sr R ->
     RiscvSemantics.step segs (@mkst fx R (Z_to_bv 64 pc) (mem_denot E m log) rom) =
     MachineOk (@mkst fx' R (v_addi (Z_to_bv 64 pc) 4) (mem_denot E m log) rom)) ->
  ex_st segs E m rom ms0 fx' (pc + 4) sr log.
Proof.
  intros E m rom ms0 fx fx' pc sr log (R & HR & Hlf & Hms) HS.
  exists R; split; [exact HR|]; split; [exact Hlf|].
  exact (exf_snoc segs fx fx' rom R R pc _ _ ms0 Hms (HS R HR)).
Qed.

Lemma xb_fari : forall E m rom ms0 fr cs pc sr log w op fmt rd rs1 rs2 (rm : bv 3) md,
  ex_st segs E m rom ms0 (mkFP fr cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fari op fmt rd rs1 rs2 rm, 4%Z) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  ex_st segs E m rom ms0
    (mkFP (bvmap_set rd (fpv_box fmt (fst (fpv_ari op fmt md (fpv_read fr fmt rs1) (fpv_read fr fmt rs2)))) fr)
          (fpv_acc cs (snd (fpv_ari op fmt md (fpv_read fr fmt rs1) (fpv_read fr fmt rs2))))) (pc + 4) sr log.
Proof.
  intros E m rom ms0 fr cs pc sr log w op fmt rd rs1 rs2 rm md ST F Ec D FZ RM.
  eapply xb_fp; [exact ST|]. intros R HR.
  exact (fpv_step_fari (mkFP fr cs) segs R (Z_to_bv 64 pc) _ rom w op fmt rd rs1 rs2 rm md F Ec D FZ RM).
Qed.

Lemma xb_fsgnj : forall E m rom ms0 fr cs pc sr log w op fmt rd rs1 rs2,
  ex_st segs E m rom ms0 (mkFP fr cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fsgnj op fmt rd rs1 rs2, 4%Z) ->
  ex_st segs E m rom ms0 (mkFP (bvmap_set rd (fpv_sgnj op fmt (reg_get fr rs1) (reg_get fr rs2)) fr) cs) (pc + 4) sr log.
Proof.
  intros E m rom ms0 fr cs pc sr log w op fmt rd rs1 rs2 ST F Ec D.
  eapply xb_fp; [exact ST|]. intros R HR.
  exact (fpv_step_fsgnj (mkFP fr cs) segs R (Z_to_bv 64 pc) _ rom w op fmt rd rs1 rs2 F Ec D).
Qed.

Lemma xb_fcvt_fx : forall E m rom ms0 fr cs pc sr log w dst src rd rs1 (rm : bv 3) md df sgn bits (v : Z),
  ex_st segs E m rom ms0 (mkFP fr cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_S /\ df = FMT_S \/ dst = FC_D /\ df = FMT_D) ->
  (src = FC_W /\ sgn = true /\ bits = 32%Z \/ src = FC_WU /\ sgn = false /\ bits = 32%Z \/
   src = FC_L /\ sgn = true /\ bits = 64%Z \/ src = FC_LU /\ sgn = false /\ bits = 64%Z) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  edenot E (sr_get sr rs1) = Z_to_bv 64 v ->
  ex_st segs E m rom ms0
    (mkFP (bvmap_set rd (fpv_box df (fst (fp_of_int (fp_format df) md sgn bits (bv_unsigned (Z_to_bv 64 v))))) fr)
          (fpv_acc cs (snd (fp_of_int (fp_format df) md sgn bits (bv_unsigned (Z_to_bv 64 v)))))) (pc + 4) sr log.
Proof.
  intros E m rom ms0 fr cs pc sr log w dst src rd rs1 rm md df sgn bits v ST F Ec D Hd Hs FZ RM Hv.
  eapply xb_fp; [exact ST|]. intros R HR.
  rewrite (fpv_step_fcvt_f_of_x (mkFP fr cs) segs R (Z_to_bv 64 pc) _ rom w dst src rd rs1 rm md df sgn bits F Ec D Hd Hs FZ RM).
  rewrite (HR rs1), Hv. reflexivity.
Qed.

Lemma xb_fcmp : forall E m rom ms0 fr cs pc sr log w op fmt rd rs1 rs2 (b : bool),
  ex_st segs E m rom ms0 (mkFP fr cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
  fst (fpv_cmp op fmt (fpv_read fr fmt rs1) (fpv_read fr fmt rs2)) = b -> bv_eqb rd 0 = false ->
  ex_st segs E m rom ms0 (mkFP fr (fpv_acc cs (snd (fpv_cmp op fmt (fpv_read fr fmt rs1) (fpv_read fr fmt rs2))))) (pc + 4)
    (sr_upd sr (ridx rd) (ELit (if b then 1 else 0))) log.
Proof.
  intros E m rom ms0 fr cs pc sr log w op fmt rd rs1 rs2 b (R & HR & Hlf & Hms) F Ec D B RD.
  exists (regupd R rd (if b then Z_to_bv 64 1 else Z_to_bv 64 0)). split.
  - pose proof (regs_ok_upd E sr R rd (if b then Z_to_bv 64 1 else Z_to_bv 64 0) (ELit (if b then 1 else 0)) HR) as H.
    rewrite RD in H. apply H. destruct b; reflexivity.
  - split; [exact Hlf|].
    refine (exf_snoc segs (mkFP fr cs) _ rom R _ pc _ _ ms0 Hms _).
    rewrite (fpv_step_fcmp (mkFP fr cs) segs R (Z_to_bv 64 pc) _ rom w op fmt rd rs1 rs2 F Ec D).
    cbn [fp_regs fp_csr]. rewrite RD, B. reflexivity.
Qed.
End XB.

Ltac xb_fd ST F D := lazymatch type of ST with ex_st ?segs _ _ _ _ _ ?pc _ _ => ex_fetch segs pc F D end.
Ltac xb_ec := first [ reflexivity | (vm_compute; reflexivity) ].

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KIdx.
Variables (s nc kx minv maxv : Z) (ncv : Z -> Z) (M0 : word -> option byte).
Definition RK : list (Z * Z) := [(kx, 1024%Z)].

(* [comment removed for export] *)
Definition kidx_ok (M : word -> option byte) : Prop :=
  forall v, (0 <= v < 256)%Z -> exists kv, rdn SEGS M (Z_to_bv 64 (kx + 4 * v)) 4 = Some (Z_to_le_bytes 4 kv) /\ (0 <= kv <= 8)%Z.

End KIdx.
End Segs.

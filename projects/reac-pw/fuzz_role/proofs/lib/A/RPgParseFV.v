(* reac_role_prop_parse 0x82ef0 of reac-pw/fuzz_role's ASan image A, segment FV: the inlined reac_float_nearest double
   steps 0x832ac .. 0x832ec from the cut FV to T (or to the shared epilogue 0x832f0 with -1). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YN2e.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require ParseFP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Modified by Theorem Labs, 2026-10: the exact flt.d / fcvt.d.wu steps of proofs/libreac/fuzz_disco/lib/Rt/FpStep.v at
   origin/ossv/recipes a34e09bd40c1 (fp_step_flt_d, fp_step_fcvt_d_wu) restated for fle.d, fcvt.d.s, fadd.d, fcvt.l.d and
   fcvt.d.l. *)
(* ---- exact steps of the double instructions (any float state F / fc) ---- *)
Lemma fv_step_fcvt_d_s : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs : bv 5) (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt FC_D FC_S rd rs rm, 4%Z) -> bv_unsigned rm = 0 ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (FP.fcvt_d_s RNE (Sem.reg_get F rs)) F)
      (Z_to_bv 32 (Z.lor (bv_unsigned fc)
         (fflags_bits (snd (fp_convert fmt_single fmt_double RNE (bv_unsigned (unbox_s (Sem.reg_get F rs)))))))))
    regs (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs rm Hf He Hd Hrm.
fp_pipeline Hf He Hd.
replace (rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned fc) 5) 7)) with (Some RNE)
  by (unfold rmode_of_field, rmode_of_Z; rewrite Hrm; reflexivity).
cbv beta iota. change (fp_format FMT_S) with fmt_single. change (fp_format FMT_D) with fmt_double. unfold FP.fcvt_d_s.
destruct (fp_convert fmt_single fmt_double RNE _) as [v fl]. cbn [fst snd]. rewrite b_npc4. reflexivity.
Qed.

Lemma fv_step_fadd_d : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs1 rs2 : bv 5) (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fari F_ADD FMT_D rd rs1 rs2 rm, 4%Z) -> bv_unsigned rm = 7 -> frm_zero fc ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (FP.fadd_d RNE (Sem.reg_get F rs1) (Sem.reg_get F rs2)) F)
      (Z_to_bv 32 (Z.lor (bv_unsigned fc)
         (fflags_bits (snd (fp_add fmt_double RNE (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2))))))))
    regs (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs1 rs2 rm Hf He Hd Hrm Hz.
fp_pipeline Hf He Hd.
unfold frm_zero in Hz.
replace (rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned fc) 5) 7)) with (Some RNE)
  by (unfold rmode_of_field; rewrite Hrm, Hz; reflexivity).
cbv beta iota. change (fp_format FMT_D) with fmt_double. unfold FP.fadd_d.
destruct (fp_add fmt_double RNE _ _) as [v fl]. cbn [fst snd]. rewrite b_npc4. reflexivity.
Qed.

Lemma fv_step_fle_d : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs1 rs2 : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp F_LE FMT_D rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP F (Z_to_bv 32 (Z.lor (bv_unsigned fc)
      (fflags_bits (FP.fcmp_fl F_LE fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))))))
    (if bv_eqb rd 0 then regs else regupd regs rd (if FP.fle_d (Sem.reg_get F rs1) (Sem.reg_get F rs2) then Z_to_bv 64 1 else Z_to_bv 64 0))
    (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs1 rs2 Hf He Hd.
assert (E1 : FP.fcmp_fl F_LE fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2))
  = snd (fp_le fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))) by reflexivity.
assert (E2 : FP.fle_d (Sem.reg_get F rs1) (Sem.reg_get F rs2)
  = fst (fp_le fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))) by reflexivity.
rewrite E1, E2.
fp_pipeline Hf He Hd.
cbv beta iota. change (fp_format FMT_D) with fmt_double.
destruct (fp_le fmt_double _ _) as [v fl]. cbn [fst snd].
rewrite b_npc4. unfold regupd. destruct (is_x0 rd); reflexivity.
Qed.

Lemma fv_step_flt_d : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs1 rs2 : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp F_LT FMT_D rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP F (Z_to_bv 32 (Z.lor (bv_unsigned fc)
      (fflags_bits (FP.fcmp_fl F_LT fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))))))
    (if bv_eqb rd 0 then regs else regupd regs rd (if FP.flt_d (Sem.reg_get F rs1) (Sem.reg_get F rs2) then Z_to_bv 64 1 else Z_to_bv 64 0))
    (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs1 rs2 Hf He Hd.
assert (E1 : FP.fcmp_fl F_LT fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2))
  = snd (fp_lt fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))) by reflexivity.
assert (E2 : FP.flt_d (Sem.reg_get F rs1) (Sem.reg_get F rs2)
  = fst (fp_lt fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))) by reflexivity.
rewrite E1, E2.
fp_pipeline Hf He Hd.
cbv beta iota. change (fp_format FMT_D) with fmt_double.
destruct (fp_lt fmt_double _ _) as [v fl]. cbn [fst snd].
rewrite b_npc4. unfold regupd. destruct (is_x0 rd); reflexivity.
Qed.

Lemma fv_step_fcvt_l_d : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs : bv 5) (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt FC_L FC_D rd rs rm, 4%Z) -> bv_unsigned rm = 1 ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP F (Z_to_bv 32 (Z.lor (bv_unsigned fc)
      (fflags_bits (snd (fp_to_int fmt_double RTZ true 64 (bv_unsigned (Sem.reg_get F rs))))))))
    (if bv_eqb rd 0 then regs else regupd regs rd (FP.fcvt_l_d RTZ (Sem.reg_get F rs)))
    (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs rm Hf He Hd Hrm.
fp_pipeline Hf He Hd.
replace (rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned fc) 5) 7)) with (Some RTZ)
  by (unfold rmode_of_field, rmode_of_Z; rewrite Hrm; reflexivity).
cbv beta iota. change (fp_format FMT_D) with fmt_double. unfold FP.fcvt_l_d.
destruct (fp_to_int fmt_double RTZ true 64 _) as [v fl]. cbn [fst snd].
rewrite b_npc4. unfold regupd. destruct (is_x0 rd); reflexivity.
Qed.

Lemma fv_step_fcvt_d_l : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs : bv 5) (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt FC_D FC_L rd rs rm, 4%Z) -> bv_unsigned rm = 7 -> frm_zero fc ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (FP.fcvt_d_l RNE (getr regs rs)) F)
      (Z_to_bv 32 (Z.lor (bv_unsigned fc)
         (fflags_bits (snd (fp_of_int fmt_double RNE true 64 (bv_unsigned (getr regs rs))))))))
    regs (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs rm Hf He Hd Hrm Hz.
fp_pipeline Hf He Hd.
unfold frm_zero in Hz.
replace (rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned fc) 5) 7)) with (Some RNE)
  by (unfold rmode_of_field; rewrite Hrm, Hz; reflexivity).
cbv beta iota. change (fp_format FMT_D) with fmt_double.
replace (if is_x0 rs then Z_to_bv 64 0 else Sem.reg_get regs rs) with (getr regs rs) by reflexivity.
unfold FP.fcvt_d_l.
destruct (fp_of_int fmt_double RNE true 64 _) as [v fl]. cbn [fst snd]. rewrite b_npc4. reflexivity.
Qed.

(* ---- reading a value back out of memory ---- *)
Definition fv_bytes (n : nat) (v : Z) : list byte := map (fun k => Z_to_bv 8 (le_byte v n k)) (seq 0 n).

Lemma fv_bytes_Z : forall n v, bytes_le_to_Z (fv_bytes n v) = v mod 2 ^ (8 * Z.of_nat n).
Proof.
intros n v. pose proof (YN2e.bytes_le_to_Z_le_list_gen n v 0) as H.
cbn [Nat.add] in H. change (8 * Z.of_nat 0) with 0 in H. rewrite Z.shiftr_0_r in H. exact H.
Qed.

Lemma fv_rdn8 : forall segs m a v, val_mem segs m a 8 v -> rdn segs m (Z_to_bv 64 a) 8 = Some (fv_bytes 8 v).
Proof.
intros segs m a v H. apply (mbytes_at_rdn segs m a (fv_bytes 8 v)).
intros j Hj. cbn [length fv_bytes map seq] in Hj.
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; cbn [nth_error fv_bytes map seq]; apply H; lia.
Qed.

Lemma fv_rdn4 : forall segs m a v, val_mem segs m a 4 v -> rdn segs m (Z_to_bv 64 a) 4 = Some (fv_bytes 4 v).
Proof.
intros segs m a v H. apply (mbytes_at_rdn segs m a (fv_bytes 4 v)).
intros j Hj. cbn [length fv_bytes map seq] in Hj.
destruct j as [|[|[|[|j]]]]; try lia; cbn [nth_error fv_bytes map seq]; apply H; lia.
Qed.

Lemma fv_word8 : forall v, 0 <= v < 2 ^ 64 -> le_bytes_to_word (fv_bytes 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. rewrite le_bytes_to_word_Z, fv_bytes_Z. change (8 * Z.of_nat 8) with 64.
rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma fv_word4 : forall v, 0 <= v < 2 ^ 32 -> le_bytes_to_word (fv_bytes 4 v) = Z_to_bv 64 v.
Proof.
intros v Hv. rewrite le_bytes_to_word_Z, fv_bytes_Z. change (8 * Z.of_nat 4) with 32.
rewrite Z.mod_small by lia. reflexivity.
Qed.

(* ---- pc and address arithmetic ---- *)
Lemma fv_addi_lit : forall z i, v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof.
intros z i. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.

Lemma fv_auipc_lit : forall z i, v_auipc (Z_to_bv 64 z) i = Z_to_bv 64 (i + z).
Proof.
intros z i. unfold v_auipc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_r.
Qed.

(* ---- one instruction of the walk, in the form the step chain keeps: pc and next pc as literals ---- *)
Lemma fv_beq_eq : forall a b : word, branch_taken BC_EQ a b = bv_eqb a b.
Proof. reflexivity. Qed.

Lemma fvw_ld : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a v,
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Load SZ8 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm ->
  val_mem rsegs mem a 8 v -> 0 <= v < 2 ^ 64 ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs (regupd regs rd (Z_to_bv 64 v)) (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a v Hc He Hd Hrd Hq Hrs Ha HM Hv.
rewrite (step_ld rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm (fv_bytes 8 v) (Z_to_bv 64 v)
  (parse_tbl_ok p wz Hc) He Hd).
- rewrite Hrd, Hq, fv_addi_lit. reflexivity.
- rewrite Hrs, fv_addi_lit, <- Ha. apply fv_rdn8. exact HM.
- rewrite fv_bytes_Z. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_small by lia.
  symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

Lemma fvw_addi : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) (v : word),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 ->
  v = v_addi (getr regs rs) (bv_signed imm) ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs (regupd regs rd v) (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm v Hc He Hd Hrd Hq Hv.
rewrite (step_addi rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm
  (parse_tbl_ok p wz Hc) He Hd).
rewrite Hrd, Hq, fv_addi_lit, Hv. reflexivity.
Qed.

Lemma fvw_auipc : forall (fs : YK11.FPState) regs mem rom p q wz rd (imm : bv 20) (t : Z),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Auipc rd imm, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 -> t = Z.shiftl (bv_signed imm) 12 + p ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs (regupd regs rd (Z_to_bv 64 t)) (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd imm t Hc He Hd Hrd Hq Ht.
rewrite (step_auipc rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd imm
  (parse_tbl_ok p wz Hc) He Hd).
rewrite Hrd, Hq, fv_addi_lit, fv_auipc_lit, Ht. reflexivity.
Qed.

Lemma fvw_subw : forall (fs : YK11.FPState) regs mem rom p q wz rd rs1 rs2 (v : word),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 ->
  v = v_subw (getr regs rs1) (getr regs rs2) ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs (regupd regs rd v) (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs1 rs2 v Hc He Hd Hrd Hq Hv.
rewrite (step_subw rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs1 rs2
  (parse_tbl_ok p wz Hc) He Hd).
rewrite Hrd, Hq, fv_addi_lit, Hv. reflexivity.
Qed.

Lemma fvw_jal0 : forall (fs : YK11.FPState) regs mem rom p q wz (imm : bv 21),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Jal 0 imm, 4%Z) -> q = p + bv_signed imm ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz imm Hc He Hd Hq.
rewrite (step_jal_x0 rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) imm
  (parse_tbl_ok p wz Hc) He Hd).
unfold btgt. rewrite fv_addi_lit, Hq. reflexivity.
Qed.

Lemma fvw_beq_tk : forall (fs : YK11.FPState) regs mem rom p q wz rs1 rs2 (imm : bv 13),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  getr regs rs1 = getr regs rs2 -> q = p + bv_signed imm ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rs1 rs2 imm Hc He Hd Hr Hq.
rewrite (step_branch_tk_gen rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) BC_EQ rs1 rs2 imm
  (parse_tbl_ok p wz Hc) He Hd).
- unfold btgt. rewrite fv_addi_lit, Hq. reflexivity.
- rewrite fv_beq_eq, Hr. apply bv_eqb_refl.
Qed.

Lemma fvw_beq_ft : forall (fs : YK11.FPState) regs mem rom p q wz rs1 rs2 (imm : bv 13) (u v : Z),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  getr regs rs1 = Z_to_bv 64 u -> getr regs rs2 = Z_to_bv 64 v ->
  0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> u <> v -> q = p + 4 ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rs1 rs2 imm u v Hc He Hd H1 H2 Hu Hv Hne Hq.
rewrite (step_branch_ft_gen rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) BC_EQ rs1 rs2 imm
  (parse_tbl_ok p wz Hc) He Hd).
- rewrite Hq, fv_addi_lit. reflexivity.
- rewrite fv_beq_eq, H1, H2. unfold bv_eqb.
  rewrite !unsigned_lit_small by assumption. apply Z.eqb_neq. exact Hne.
Qed.

Lemma fvw_ret : forall (fs : YK11.FPState) regs mem rom p wz rs1 (imm : bv 12) (t : word),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Jalr 0 rs1 imm, 4%Z) ->
  bv_signed imm = 0 -> getr regs rs1 = t -> YK0s.ret_ok t ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs t mem rom).
Proof.
intros fs regs mem rom p wz rs1 imm t Hc He Hd Himm Hr Hok.
rewrite (step_jalr_x0 rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rs1 imm t
  (parse_tbl_ok p wz Hc) He Hd Hr).
rewrite Himm. unfold YK0s.ret_ok in Hok. rewrite Hok. reflexivity.
Qed.

(* ---- the float instructions, in the same form ---- *)
Lemma fvw_flw : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a v,
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (FLoad FMT_S rd rs imm, 4%Z) -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm ->
  0 <= v < 2 ^ 32 -> val_mem rsegs mem a 4 v ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (Z_to_bv 32 v)) (@fp_regs fs)) (@fp_csr fs))
    regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a v Hc He Hd Hq Hrs Ha Hv HM.
rewrite (fp_step_flw fs rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm
  (v_addi (getr regs rs) (bv_signed imm)) (fv_bytes 4 v)
  (parse_tbl_ok p wz Hc) He Hd eq_refl).
- cbn [fp_regs fp_csr]. rewrite Hq, fv_addi_lit, fv_word4 by lia.
  change (bv_extract 0 32 (Z_to_bv 64 v)) with (low32 (Z_to_bv 64 v)). rewrite low32_lit. reflexivity.
- rewrite Hrs, fv_addi_lit, <- Ha. apply fv_rdn4. exact HM.
Qed.

Lemma fvw_fld : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a v,
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (FLoad FMT_D rd rs imm, 4%Z) -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm ->
  0 <= v < 2 ^ 64 -> val_mem rsegs mem a 8 v ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (Z_to_bv 64 v) (@fp_regs fs)) (@fp_csr fs))
    regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a v Hc He Hd Hq Hrs Ha Hv HM.
rewrite (fp_step_fld fs rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm
  (v_addi (getr regs rs) (bv_signed imm)) (fv_bytes 8 v)
  (parse_tbl_ok p wz Hc) He Hd eq_refl).
- cbn [fp_regs fp_csr]. rewrite Hq, fv_addi_lit, fv_word8 by lia.
  rewrite bv_extract_0_64. reflexivity.
- rewrite Hrs, fv_addi_lit, <- Ha. apply fv_rdn8. exact HM.
Qed.

(* ---- register reads after a chain of writes ---- *)
Lemma fv_getr_upd : forall regs (r r' : bv 5) v, bv_eqb r' r = false -> getr (regupd regs r v) r' = getr regs r'.
Proof.
intros regs r r' v H. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other; [reflexivity|].
intros E. unfold bv_eqb in H. apply Z.eqb_neq in H. apply H. rewrite E. reflexivity.
Qed.

Lemma fv_getr_set : forall regs (r r' : bv 5) v, bv_eqb r' r = true -> bv_eqb r' 0 = false ->
  getr (regupd regs r v) r' = v.
Proof.
intros regs r r' v H H0. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq in H. subst r'.
unfold getr, regupd. rewrite H0. unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.

Ltac fv_reg := repeat (rewrite fv_getr_upd by (vm_compute; reflexivity));
  try (rewrite fv_getr_set by (vm_compute; reflexivity)).

Lemma fv_u64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. cbn [Z.of_N] in H. exact H. Qed.

(* ---- the double instructions in the same form; the fcsr is kept abstract (only its rounding field matters) ---- *)
Lemma fvw_fcvt_d_s : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs (rm : bv 3) (src : word),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcvt FC_D FC_S rd rs rm, 4%Z) ->
  bv_unsigned rm = 0 -> q = p + 4 -> Sem.reg_get F rs = src -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP (bvmap_set rd (FP.fcvt_d_s RNE src) F) C') regs (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs rm src Hc He Hd Hrm Hq Hsrc HC. eexists. split.
- rewrite (fv_step_fcvt_d_s F C rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs rm
    (parse_tbl_ok p wz Hc) He Hd Hrm).
  rewrite Hq, fv_addi_lit, Hsrc. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma fvw_fadd_d : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs1 rs2 (rm : bv 3) (x y : word),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fari F_ADD FMT_D rd rs1 rs2 rm, 4%Z) ->
  bv_unsigned rm = 7 -> q = p + 4 -> Sem.reg_get F rs1 = x -> Sem.reg_get F rs2 = y -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP (bvmap_set rd (FP.fadd_d RNE x y) F) C') regs (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs1 rs2 rm x y Hc He Hd Hrm Hq Hx Hy HC. eexists. split.
- rewrite (fv_step_fadd_d F C rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs1 rs2 rm
    (parse_tbl_ok p wz Hc) He Hd Hrm HC).
  rewrite Hq, fv_addi_lit, Hx, Hy. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma fvw_fle_d : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs1 rs2 (x y : word),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcmp F_LE FMT_D rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 -> Sem.reg_get F rs1 = x -> Sem.reg_get F rs2 = y -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP F C')
      (regupd regs rd (if FP.fle_d x y then Z_to_bv 64 1 else Z_to_bv 64 0)) (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs1 rs2 x y Hc He Hd Hrd Hq Hx Hy HC. eexists. split.
- rewrite (fv_step_fle_d F C rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs1 rs2
    (parse_tbl_ok p wz Hc) He Hd).
  rewrite Hrd, Hq, fv_addi_lit, Hx, Hy. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma fvw_flt_d : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs1 rs2 (x y : word),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcmp F_LT FMT_D rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 -> Sem.reg_get F rs1 = x -> Sem.reg_get F rs2 = y -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP F C')
      (regupd regs rd (if FP.flt_d x y then Z_to_bv 64 1 else Z_to_bv 64 0)) (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs1 rs2 x y Hc He Hd Hrd Hq Hx Hy HC. eexists. split.
- rewrite (fv_step_flt_d F C rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs1 rs2
    (parse_tbl_ok p wz Hc) He Hd).
  rewrite Hrd, Hq, fv_addi_lit, Hx, Hy. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma fvw_fcvt_l_d : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs (rm : bv 3) (x : word),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcvt FC_L FC_D rd rs rm, 4%Z) ->
  bv_unsigned rm = 1 -> bv_eqb rd 0 = false -> q = p + 4 -> Sem.reg_get F rs = x -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP F C') (regupd regs rd (FP.fcvt_l_d RTZ x)) (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs rm x Hc He Hd Hrm Hrd Hq Hx HC. eexists. split.
- rewrite (fv_step_fcvt_l_d F C rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs rm
    (parse_tbl_ok p wz Hc) He Hd Hrm).
  rewrite Hrd, Hq, fv_addi_lit, Hx. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma fvw_fcvt_d_l : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs (rm : bv 3) (x : word),
  clookup parse_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcvt FC_D FC_L rd rs rm, 4%Z) ->
  bv_unsigned rm = 7 -> q = p + 4 -> getr regs rs = x -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP (bvmap_set rd (FP.fcvt_d_l RNE x) F) C') regs (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs rm x Hc He Hd Hrm Hq Hx HC. eexists. split.
- rewrite (fv_step_fcvt_d_l F C rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs rm
    (parse_tbl_ok p wz Hc) He Hd Hrm HC).
  rewrite Hq, fv_addi_lit, Hx. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

(* ======================= the float path of reac_role_prop_parse ======================= *)
Definition D_HALF : Z := 0x3fe0000000000000.
Definition D_LO : Z := 0xc1e0000000000000.
Definition D_HI : Z := 0x41e0000000000000.
Definition A_C_HALF : Z := 0x10378.
Definition A_C_LO : Z := 0x103e0.
Definition A_C_HI : Z := 0x10330.
Definition PC_M1 : Z := 0x832f0.

Lemma fv_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.

Ltac fv_dec := first [ (vm_compute; reflexivity) | vm_refl_bv ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma fv_frame_range : forall x, pre_ok B x -> 0x10400 < x_F x /\ x_F x + FRAME = x_sp x /\ x_F x + FRAME < 2 ^ 64.
Proof.
intros x Hpre.
pose proof (pre_stack B x Hpre) as (Hceil & Hsp0 & H47 & Hal16 & Hwin).
pose proof alloc_ceiling_value as [[Hcl Hch] _].
unfold x_F, FRAME, T_parse_STK, ESTACK in *. lia.
Qed.

Lemma fv_cell : forall x regs2 mem2 md2 a v, pre_ok B x -> FI B x regs2 mem2 md2 -> In (a, v) role_A_dcs ->
  val_mem rsegs (mrestrict (w_H (x_W x)) mem2) a 8 v.
Proof.
intros x regs2 mem2 md2 a v Hpre HFI Hin.
pose proof (pre_stack B x Hpre) as (Hceil & Hsp0 & H47 & Hal16 & Hwin).
pose proof alloc_ceiling_value as [[Hcl Hch] _].
pose proof Hpre as Hp. destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
assert (Hav : val_mem rsegs (mrestrict (w_H (x_W x)) (x_memc x)) a 8 v).
{ unfold rl_ro_cells in Hro. rewrite Forall_forall in Hro. exact (Hro (a, v) Hin). }
assert (Hr : 0 <= a /\ a + 8 <= 0x10400).
{ unfold role_A_dcs in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[]]]]; injection E as E1 E2; subst a; cbv; split; congruence. }
apply (val_mem_kept rsegs (w_H (x_W x)) (w_H (x_W x)) (x_memc x) mem2 a 8 v); [|exact Hav].
intros k Hk. apply (kept_view B x regs2 mem2 md2 (a + k) HFI); cbn [Z.of_nat] in Hk; lia.
Qed.


(* ---- the shared epilogue at 0x832f0: a1 = a0 = -1, the ten saved words back, sp += 0x60, ret ---- *)
Lemma fv_getr_cast : forall regs (r r' : bv 5), bv_unsigned r = bv_unsigned r' -> getr regs r = getr regs r'.
Proof. intros regs r r' H. f_equal. apply bv_eq. exact H. Qed.

Lemma fv_ret_m1 : forall x (fs : YK11.FPState) regs regs2 mem2 md2,
  pre_ok (fx := fx) B x -> FI B x regs2 mem2 md2 -> rl_fxk [13; 14; 15] fx fs ->
  x_res x = (None, -1) ->
  getr regs 2 = w64 (x_F x) ->
  (forall r, r = 3 \/ r = 4 \/ r = 25 \/ r = 26 \/ r = 27 ->
     getr regs (Z_to_bv 5 r) = getr (x_regs x) (Z_to_bv 5 r)) ->
  SRr rsegs (x_W x) (mkCfg (@mkst fs regs (Z_to_bv 64 PC_M1) mem2 (seg_rom rsegs)) md2)
    (PPOST (fx := fx) B MT x false).
Proof.
intros x fs regs regs2 mem2 md2 Hpre HFI Hfxk Hres Hsp Hcs.
change (w64 (x_F x)) with (Z_to_bv 64 (x_F x)) in Hsp.
pose proof (fv_frame_range x Hpre) as (HF0 & HFsp & HF64).
pose proof HFI as (HJ & Hio & HK & HSV & _).
pose proof Hpre as Hp. destruct Hp as ((_ & Hra & _) & _).
unfold SAVED in HSV.
inversion HSV as [|c1 l1 V1 HS1]; subst. inversion HS1 as [|c2 l2 V2 HS2]; subst.
inversion HS2 as [|c3 l3 V3 HS3]; subst. inversion HS3 as [|c4 l4 V4 HS4]; subst.
inversion HS4 as [|c5 l5 V5 HS5]; subst. inversion HS5 as [|c6 l6 V6 HS6]; subst.
inversion HS6 as [|c7 l7 V7 HS7]; subst. inversion HS7 as [|c8 l8 V8 HS8]; subst.
inversion HS8 as [|c9 l9 V9 HS9]; subst. inversion HS9 as [|c10 l10 V10 _]; subst.
cbn [fst snd] in V1, V2, V3, V4, V5, V6, V7, V8, V9, V10.
clear HSV HS1 HS2 HS3 HS4 HS5 HS6 HS7 HS8 HS9.
eapply (SRr_msteps rsegs parse_wx).
{ rewrite restrict_mkst_fx. unfold PC_M1.
  (* 0x832f0 addi a1,zero,-1 *)
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_addi fs _ _ _ 0x832f0 0x832f4 4293920147 11 0 4095 (Z_to_bv 64 (-1)));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | ]
  | ].
  { rewrite getr_zero, fv_addi_lit. f_equal; vm_compute; reflexivity. }
  (* 0x832f4 mv a0,a1 *)
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_addi fs _ _ _ 0x832f4 0x832f8 361747 10 11 0 (Z_to_bv 64 (-1)));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | ]
  | ].
  { fv_reg. rewrite fv_addi_lit. f_equal; vm_compute; reflexivity. }
  (* 0x832f8 .. 0x8331c: the ten ld's *)
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x832f8 0x832fc 92352643 1 2 88 (x_F x) (x_F x + 88));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V1. }
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x832fc 0x83300 83964931 8 2 80 (x_F x) (x_F x + 80));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V2. }
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x83300 0x83304 75576451 9 2 72 (x_F x) (x_F x + 72));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V3. }
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x83304 0x83308 67188995 18 2 64 (x_F x) (x_F x + 64));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V4. }
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x83308 0x8330c 58800515 19 2 56 (x_F x) (x_F x + 56));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V5. }
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x8330c 0x83310 50412035 20 2 48 (x_F x) (x_F x + 48));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V6. }
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x83310 0x83314 42023555 21 2 40 (x_F x) (x_F x + 40));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V7. }
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x83314 0x83318 33635075 22 2 32 (x_F x) (x_F x + 32));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V8. }
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x83318 0x8331c 25246595 23 2 24 (x_F x) (x_F x + 24));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V9. }
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ld fs _ _ _ 0x8331c 0x83320 16858115 24 2 16 (x_F x) (x_F x + 16));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | | reflexivity | | apply fv_u64 ]
  | ].
  { fv_reg. exact Hsp. } { exact V10. }
  (* 0x83320 addi sp,sp,0x60 *)
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_addi fs _ _ _ 0x83320 0x83324 100729107 2 2 96 (Z_to_bv 64 (x_sp x)));
    [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | ]
  | ].
  { fv_reg. rewrite Hsp, fv_addi_lit. unfold FRAME in HFsp. rewrite <- HFsp.
    f_equal; f_equal; vm_compute; reflexivity. }
  (* 0x83324 ret *)
  eapply mst_step;
  [ reflexivity
  | eapply (fvw_ret fs _ _ _ 0x83324 32871 1 0 (getr (x_regs x) 1));
    [ fv_dec | fv_dec | fv_dec | vm_compute; reflexivity | | exact Hra ]
  | ].
  { fv_reg. rewrite Z_to_bv_bv_unsigned.
    apply fv_getr_cast; vm_compute; reflexivity. }
  apply mst_refl. }
intros md' Hsame Hcl.
rewrite (same_but_materialized_wvb md2 md' Hsame), unrestrict_mkst_mrestrict.
apply SRr_ret.
assert (Hpr : rl_parse_res false (x_bs x) = (None, -1)).
{ unfold rl_parse_res. unfold x_res in Hres. exact Hres. }
eapply ppost_intro.
- exact MTL.
- eapply ajournal_materialize; first [exact LAWS | exact parse_segs_low | exact HJ].
- eapply same_io_trans; [exact Hio | apply fv_same_io_wvb].
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
          r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
  fv_reg;
  first [ apply Z_to_bv_bv_unsigned
        | (unfold x_sp, spZ; rewrite Z_to_bv_bv_unsigned; apply fv_getr_cast; vm_compute; reflexivity)
        | (apply Hcs; tauto) ].
- exact Hfxk.
- intros a Ha Hns _. exact (HK a Ha Hns).
- rewrite Hpr. cbn [snd]. fv_reg. reflexivity.
- rewrite Hpr. cbn [fst]. exact I.
Qed.

(* ---- the float registers along the path (f15 = the value, f14 / f13 the constants) ---- *)
Definition fvG1 (b : Z) (F : bvmap 5 word) : bvmap 5 word := bvmap_set 15 (nan_box (Z_to_bv 32 b)) F.
Definition fvG2 (b : Z) (F : bvmap 5 word) : bvmap 5 word := bvmap_set 14 (Z_to_bv 64 D_HALF) (fvG1 b F).
Definition fvG3 (b : Z) (F : bvmap 5 word) : bvmap 5 word := bvmap_set 13 (Z_to_bv 64 D_LO) (fvG2 b F).
Definition fvG4 (b : Z) (F : bvmap 5 word) : bvmap 5 word :=
  bvmap_set 15 (FP.fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) (fvG3 b F).
Definition fvG5 (b : Z) (F : bvmap 5 word) : bvmap 5 word :=
  bvmap_set 15 (FP.fadd_d RNE (FP.fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) (Z_to_bv 64 D_HALF)) (fvG4 b F).
Definition fvR0 (regs : bvmap 5 word) : bvmap 5 word := regupd regs 10 (Z_to_bv 64 0x102b4).
Definition fvR1 (regs : bvmap 5 word) (b : Z) : bvmap 5 word :=
  regupd (fvR0 regs) 10 (if FP.fle_d (Z_to_bv 64 D_LO) (ParseFP.rfn_d b) then Z_to_bv 64 1 else Z_to_bv 64 0).

Lemma fv_other_z : forall (j k : bv 5) (z : Z), bv_unsigned j = z -> z <> bv_unsigned k -> bv_eqb j k = false.
Proof. intros j k z Hj Hk. unfold bv_eqb. apply Z.eqb_neq. rewrite Hj. exact Hk. Qed.

Lemma fv_upd_z : forall (j k : bv 5) (z : Z), bv_unsigned j = z -> z <> bv_unsigned k -> bv_eqb k j = false.
Proof. intros j k z Hj Hk. unfold bv_eqb. apply Z.eqb_neq. rewrite Hj. intros E. apply Hk. symmetry. exact E. Qed.

Ltac fv_freg := repeat (rewrite FP.freg_get_other by (vm_compute; reflexivity));
  try (rewrite FP.freg_get_same by (vm_compute; reflexivity)).

Lemma fv_g5_15 : forall b F, Sem.reg_get (fvG5 b F) 15 = ParseFP.rfn_d b.
Proof.
intros b F. unfold fvG5. rewrite (FP.freg_get_same _ 15 15 _ eq_refl).
unfold ParseFP.rfn_d, D_HALF. reflexivity.
Qed.

Lemma fv_g5_kept : forall b F k, bv_unsigned k <> 13 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 ->
  Sem.reg_get (fvG5 b F) k = Sem.reg_get F k.
Proof.
intros b F k H13 H14 H15. unfold fvG5, fvG4, fvG3, fvG2, fvG1.
rewrite !FP.freg_get_other by (eapply fv_other_z; [vm_compute; reflexivity | lia]). reflexivity.
Qed.

Lemma fv_r1_10 : forall regs b,
  getr (fvR1 regs b) 10 = (if FP.fle_d (Z_to_bv 64 D_LO) (ParseFP.rfn_d b) then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof. intros regs b. unfold fvR1. apply fv_getr_set; vm_compute; reflexivity. Qed.

Lemma fv_r1_kept : forall regs b (r : bv 5), bv_unsigned r <> 10 -> getr (fvR1 regs b) r = getr regs r.
Proof.
intros regs b r H. unfold fvR1, fvR0.
rewrite !fv_getr_upd by (eapply fv_upd_z; [vm_compute; reflexivity | lia]). reflexivity.
Qed.

(* ---- 0x832ac .. 0x832c4: f15 = (double)f + 0.5, a0 = (lo <= f15) ---- *)
Lemma fv_head : forall (fs : YK11.FPState) (regs : bvmap 5 word) M (b base2 : Z),
  frm_zero (@fp_csr fs) ->
  getr regs 2 = Z_to_bv 64 base2 -> getr regs 12 = Z_to_bv 64 A_FV_A2 ->
  0 <= b < 2 ^ 32 -> val_mem rsegs M (base2 + 8) 4 b ->
  val_mem rsegs M A_C_HALF 8 D_HALF -> val_mem rsegs M A_C_LO 8 D_LO ->
  exists C' : bv 32,
    msteps rsegs (@mkst fs regs (Z_to_bv 64 PC_FV) M (seg_rom rsegs))
      (@mkst (mkFP (fvG5 b (@fp_regs fs)) C') (fvR1 regs b) (Z_to_bv 64 0x832c8) M (seg_rom rsegs))
    /\ frm_zero C'.
Proof.
intros fs regs M b base2 HC0 Hsp Ha2 Hb Hvb Hhalf Hlo.
assert (S1 : RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 PC_FV) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP (fvG1 b (@fp_regs fs)) (@fp_csr fs)) regs (Z_to_bv 64 0x832b0) M (seg_rom rsegs))).
{ unfold PC_FV. apply (fvw_flw fs regs M (seg_rom rsegs) 0x832ac 0x832b0 8464263 15 2 8 base2 (base2 + 8) b);
  [ fv_dec | fv_dec | fv_dec | reflexivity | exact Hsp | vm_compute; reflexivity | exact Hb | exact Hvb ]. }
assert (S2 : RiscvSemantics.step rsegs (@mkst (mkFP (fvG1 b (@fp_regs fs)) (@fp_csr fs)) regs (Z_to_bv 64 0x832b0) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP (fvG2 b (@fp_regs fs)) (@fp_csr fs)) regs (Z_to_bv 64 0x832b4) M (seg_rom rsegs))).
{ apply (fvw_fld (mkFP (fvG1 b (@fp_regs fs)) (@fp_csr fs)) regs M (seg_rom rsegs)
    0x832b0 0x832b4 226899719 14 12 216 A_FV_A2 A_C_HALF D_HALF);
  [ fv_dec | fv_dec | fv_dec | reflexivity | exact Ha2 | vm_compute; reflexivity | cbv; split; congruence | exact Hhalf ]. }
assert (S3 : RiscvSemantics.step rsegs (@mkst (mkFP (fvG2 b (@fp_regs fs)) (@fp_csr fs)) regs (Z_to_bv 64 0x832b4) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP (fvG2 b (@fp_regs fs)) (@fp_csr fs)) (fvR0 regs) (Z_to_bv 64 0x832b8) M (seg_rom rsegs))).
{ apply (fvw_auipc (mkFP (fvG2 b (@fp_regs fs)) (@fp_csr fs)) regs M (seg_rom rsegs)
    0x832b4 0x832b8 4294497559 10 1048461 0x102b4);
  [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | vm_compute; reflexivity ]. }
assert (S4 : RiscvSemantics.step rsegs (@mkst (mkFP (fvG2 b (@fp_regs fs)) (@fp_csr fs)) (fvR0 regs) (Z_to_bv 64 0x832b8) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP (fvG3 b (@fp_regs fs)) (@fp_csr fs)) (fvR0 regs) (Z_to_bv 64 0x832bc) M (seg_rom rsegs))).
{ apply (fvw_fld (mkFP (fvG2 b (@fp_regs fs)) (@fp_csr fs)) (fvR0 regs) M (seg_rom rsegs)
    0x832b8 0x832bc 314914439 13 10 300 0x102b4 A_C_LO D_LO);
  [ fv_dec | fv_dec | fv_dec | reflexivity
  | unfold fvR0; apply fv_getr_set; vm_compute; reflexivity
  | vm_compute; reflexivity | cbv; split; congruence | exact Hlo ]. }
destruct (fvw_fcvt_d_s (fvG3 b (@fp_regs fs)) (@fp_csr fs) (fvR0 regs) M (seg_rom rsegs)
  0x832bc 0x832c0 1107789779 15 15 0 (nan_box (Z_to_bv 32 b))
  ltac:(fv_dec) ltac:(fv_dec) ltac:(fv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold fvG3, fvG2, fvG1; fv_freg; reflexivity) HC0) as (C1 & S5 & HC1).
destruct (fvw_fadd_d (fvG4 b (@fp_regs fs)) C1 (fvR0 regs) M (seg_rom rsegs)
  0x832c0 0x832c4 48756691 15 15 14 7
  (FP.fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) (Z_to_bv 64 D_HALF)
  ltac:(fv_dec) ltac:(fv_dec) ltac:(fv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold fvG4; fv_freg; reflexivity)
  ltac:(unfold fvG4, fvG3, fvG2, fvG1; fv_freg; reflexivity) HC1) as (C2 & S6 & HC2).
destruct (fvw_fle_d (fvG5 b (@fp_regs fs)) C2 (fvR0 regs) M (seg_rom rsegs)
  0x832c4 0x832c8 2734064979 10 13 15 (Z_to_bv 64 D_LO) (ParseFP.rfn_d b)
  ltac:(fv_dec) ltac:(fv_dec) ltac:(fv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold fvG5, fvG4, fvG3; fv_freg; reflexivity)
  ltac:(apply fv_g5_15) HC2) as (C3 & S7 & HC3).
exists C3. split; [|exact HC3].
eapply mst_step; [reflexivity | exact S1 | ].
eapply mst_step; [reflexivity | exact S2 | ].
eapply mst_step; [reflexivity | exact S3 | ].
eapply mst_step; [reflexivity | exact S4 | ].
eapply mst_step; [reflexivity | exact S5 | ].
eapply mst_step; [reflexivity | exact S6 | ].
eapply mst_step; [reflexivity | exact S7 | ].
apply mst_refl.
Qed.

(* ---- 0x832c8 .. 0x832d4 (the low test passed): a0 = (f15 < hi) ---- *)
Lemma fv_mid : forall (F : bvmap 5 word) (C : bv 32) (regs : bvmap 5 word) M (b : Z),
  frm_zero C -> Sem.reg_get F 15 = ParseFP.rfn_d b -> getr regs 10 = Z_to_bv 64 1 ->
  val_mem rsegs M A_C_HI 8 D_HI ->
  exists C' : bv 32,
    msteps rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 0x832c8) M (seg_rom rsegs))
      (@mkst (mkFP (bvmap_set 14 (Z_to_bv 64 D_HI) F) C')
         (regupd (regupd regs 10 (Z_to_bv 64 0x102cc)) 10
            (if FP.flt_d (ParseFP.rfn_d b) (Z_to_bv 64 D_HI) then Z_to_bv 64 1 else Z_to_bv 64 0))
         (Z_to_bv 64 0x832d8) M (seg_rom rsegs))
    /\ frm_zero C'.
Proof.
intros F C regs M b HC H15 H10 Hhi.
assert (S1 : RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 0x832c8) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP F C) regs (Z_to_bv 64 0x832cc) M (seg_rom rsegs))).
{ apply (fvw_beq_ft (mkFP F C) regs M (seg_rom rsegs) 0x832c8 0x832cc 33883235 10 0 40 1 0);
  [ fv_dec | fv_dec | fv_dec | exact H10 | apply getr_zero | cbv; split; congruence
  | cbv; split; congruence | lia | reflexivity ]. }
assert (S2 : RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 0x832cc) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP F C) (regupd regs 10 (Z_to_bv 64 0x102cc)) (Z_to_bv 64 0x832d0) M (seg_rom rsegs))).
{ apply (fvw_auipc (mkFP F C) regs M (seg_rom rsegs) 0x832cc 0x832d0 4294497559 10 1048461 0x102cc);
  [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | vm_compute; reflexivity ]. }
assert (S3 : RiscvSemantics.step rsegs (@mkst (mkFP F C) (regupd regs 10 (Z_to_bv 64 0x102cc)) (Z_to_bv 64 0x832d0) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP (bvmap_set 14 (Z_to_bv 64 D_HI) F) C) (regupd regs 10 (Z_to_bv 64 0x102cc))
      (Z_to_bv 64 0x832d4) M (seg_rom rsegs))).
{ apply (fvw_fld (mkFP F C) (regupd regs 10 (Z_to_bv 64 0x102cc)) M (seg_rom rsegs)
    0x832d0 0x832d4 105199367 14 10 100 0x102cc A_C_HI D_HI);
  [ fv_dec | fv_dec | fv_dec | reflexivity | apply fv_getr_set; vm_compute; reflexivity
  | vm_compute; reflexivity | cbv; split; congruence | exact Hhi ]. }
destruct (fvw_flt_d (bvmap_set 14 (Z_to_bv 64 D_HI) F) C (regupd regs 10 (Z_to_bv 64 0x102cc)) M (seg_rom rsegs)
  0x832d4 0x832d8 2733086035 10 15 14 (ParseFP.rfn_d b) (Z_to_bv 64 D_HI)
  ltac:(fv_dec) ltac:(fv_dec) ltac:(fv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(fv_freg; exact H15) ltac:(fv_freg; reflexivity) HC) as (C' & S4 & HC').
exists C'. split; [|exact HC'].
eapply mst_step; [reflexivity | exact S1 | ].
eapply mst_step; [reflexivity | exact S2 | ].
eapply mst_step; [reflexivity | exact S3 | ].
eapply mst_step; [reflexivity | exact S4 | ].
apply mst_refl.
Qed.

(* ---- 0x832d8 .. 0x832ec (both tests passed): a0 = t - (f15 < (double)t), then the jump to T ---- *)
Lemma fv_rfn_t : forall b, FP.fcvt_l_d RTZ (ParseFP.rfn_d b) = ParseFP.rfn_t b.
Proof. reflexivity. Qed.

Lemma fv_subw_r : forall b, - 2 ^ 31 <= ParseFP.rfn_r b < 2 ^ 31 ->
  v_subw (ParseFP.rfn_t b)
    (if FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) then Z_to_bv 64 1 else Z_to_bv 64 0)
  = Z_to_bv 64 (ParseFP.rfn_r b).
Proof.
intros b Hb.
destruct (FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b))) eqn:Ef.
- assert (Hrr : ParseFP.rfn_r b = bv_signed (ParseFP.rfn_t b) - 1)
    by (unfold ParseFP.rfn_r; rewrite Ef; reflexivity).
  unfold v_subw. rewrite (unsigned_lit_small 1) by lia.
  rewrite (reac_role_prop_parse.pc_subw (ParseFP.rfn_t b) 1) by lia. rewrite <- Hrr. reflexivity.
- assert (Hrr : ParseFP.rfn_r b = bv_signed (ParseFP.rfn_t b) - 0)
    by (unfold ParseFP.rfn_r; rewrite Ef; reflexivity).
  unfold v_subw. rewrite (unsigned_lit_small 0) by lia.
  rewrite (reac_role_prop_parse.pc_subw (ParseFP.rfn_t b) 0) by lia. rewrite <- Hrr. reflexivity.
Qed.

Lemma fv_tail : forall (F : bvmap 5 word) (C : bv 32) (regs : bvmap 5 word) M (b : Z),
  frm_zero C -> Sem.reg_get F 15 = ParseFP.rfn_d b -> getr regs 10 = Z_to_bv 64 1 ->
  - 2 ^ 31 <= ParseFP.rfn_r b < 2 ^ 31 ->
  exists (C' : bv 32) (G : bvmap 5 word) (R : bvmap 5 word),
    msteps rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 0x832d8) M (seg_rom rsegs))
      (@mkst (mkFP G C') R (Z_to_bv 64 PC_T) M (seg_rom rsegs))
    /\ frm_zero C'
    /\ (forall k : bv 5, bv_unsigned k <> 14 -> Sem.reg_get G k = Sem.reg_get F k)
    /\ getr R 10 = Z_to_bv 64 (ParseFP.rfn_r b)
    /\ (forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr R r = getr regs r).
Proof.
intros F C regs M b HC H15 H10 Hb.
assert (S1 : RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 0x832d8) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP F C) regs (Z_to_bv 64 0x832dc) M (seg_rom rsegs))).
{ apply (fvw_beq_ft (mkFP F C) regs M (seg_rom rsegs) 0x832d8 0x832dc 330851 10 0 24 1 0);
  [ fv_dec | fv_dec | fv_dec | exact H10 | apply getr_zero | cbv; split; congruence
  | cbv; split; congruence | lia | reflexivity ]. }
destruct (fvw_fcvt_l_d F C regs M (seg_rom rsegs) 0x832dc 0x832e0 3257374035 10 15 1 (ParseFP.rfn_d b)
  ltac:(fv_dec) ltac:(fv_dec) ltac:(fv_dec) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  eq_refl ltac:(exact H15) HC) as (C1 & S2 & HC1).
rewrite fv_rfn_t in S2.
destruct (fvw_fcvt_d_l F C1 (regupd regs 10 (ParseFP.rfn_t b)) M (seg_rom rsegs)
  0x832e0 0x832e4 3525670739 14 10 7 (ParseFP.rfn_t b)
  ltac:(fv_dec) ltac:(fv_dec) ltac:(fv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(apply fv_getr_set; vm_compute; reflexivity) HC1) as (C2 & S3 & HC2).
destruct (fvw_flt_d (bvmap_set 14 (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) F) C2
  (regupd regs 10 (ParseFP.rfn_t b)) M (seg_rom rsegs)
  0x832e4 0x832e8 2733086163 11 15 14 (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b))
  ltac:(fv_dec) ltac:(fv_dec) ltac:(fv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(fv_freg; exact H15) ltac:(fv_freg; reflexivity) HC2) as (C3 & S4 & HC3).
assert (S5 : RiscvSemantics.step rsegs
    (@mkst (mkFP (bvmap_set 14 (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) F) C3)
       (regupd (regupd regs 10 (ParseFP.rfn_t b)) 11
          (if FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) then Z_to_bv 64 1 else Z_to_bv 64 0))
       (Z_to_bv 64 0x832e8) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP (bvmap_set 14 (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) F) C3)
       (regupd (regupd (regupd regs 10 (ParseFP.rfn_t b)) 11
          (if FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) then Z_to_bv 64 1 else Z_to_bv 64 0))
          10 (Z_to_bv 64 (ParseFP.rfn_r b)))
       (Z_to_bv 64 0x832ec) M (seg_rom rsegs))).
{ apply (fvw_subw (mkFP (bvmap_set 14 (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) F) C3) _ M (seg_rom rsegs)
    0x832e8 0x832ec 1085605179 10 10 11 (Z_to_bv 64 (ParseFP.rfn_r b)));
  [ fv_dec | fv_dec | fv_dec | fv_dec | reflexivity | ].
  rewrite (fv_getr_upd _ 11 10) by (vm_compute; reflexivity).
  rewrite (fv_getr_set _ 10 10) by (vm_compute; reflexivity).
  rewrite (fv_getr_set _ 11 11) by (vm_compute; reflexivity).
  symmetry. apply fv_subw_r. exact Hb. }
assert (S6 : RiscvSemantics.step rsegs
    (@mkst (mkFP (bvmap_set 14 (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) F) C3)
       (regupd (regupd (regupd regs 10 (ParseFP.rfn_t b)) 11
          (if FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) then Z_to_bv 64 1 else Z_to_bv 64 0))
          10 (Z_to_bv 64 (ParseFP.rfn_r b)))
       (Z_to_bv 64 0x832ec) M (seg_rom rsegs))
  = MachineOk (@mkst (mkFP (bvmap_set 14 (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) F) C3)
       (regupd (regupd (regupd regs 10 (ParseFP.rfn_t b)) 11
          (if FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) then Z_to_bv 64 1 else Z_to_bv 64 0))
          10 (Z_to_bv 64 (ParseFP.rfn_r b)))
       (Z_to_bv 64 PC_T) M (seg_rom rsegs))).
{ unfold PC_T. apply (fvw_jal0 (mkFP (bvmap_set 14 (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) F) C3) _ M (seg_rom rsegs)
    0x832ec 0x83224 4087345263 2096952);
  [ fv_dec | fv_dec | fv_dec | vm_compute; reflexivity ]. }
eexists. eexists. eexists. split; [|split; [exact HC3 | split; [|split]]].
- eapply mst_step; [reflexivity | exact S1 | ].
  eapply mst_step; [reflexivity | exact S2 | ].
  eapply mst_step; [reflexivity | exact S3 | ].
  eapply mst_step; [reflexivity | exact S4 | ].
  eapply mst_step; [reflexivity | exact S5 | ].
  eapply mst_step; [reflexivity | exact S6 | ].
  apply mst_refl.
- intros k Hk. apply FP.freg_get_other. eapply fv_other_z; [vm_compute; reflexivity | lia].
- apply fv_getr_set; vm_compute; reflexivity.
- intros r H10r H11r.
  rewrite (fv_getr_upd _ 10 r) by (eapply fv_upd_z; [vm_compute; reflexivity | lia]).
  rewrite (fv_getr_upd _ 11 r) by (eapply fv_upd_z; [vm_compute; reflexivity | lia]).
  rewrite (fv_getr_upd _ 10 r) by (eapply fv_upd_z; [vm_compute; reflexivity | lia]).
  reflexivity.
Qed.

(* ---- the model: nearest's answer is the hardware's ---- *)
Lemma fv_near_bounds : forall b lo hi r, Nearest.nearest b lo hi = Some r -> lo <= r <= hi.
Proof.
intros b lo hi r H. unfold Nearest.nearest in H.
destruct (Nearest.near_f32 b) as [q|]; [|discriminate].
destruct ((lo <=? q) && (q <=? hi)) eqn:E; [|discriminate]. injection H as <-.
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(* the facts of a cut, after the model's lazy backing was materialized *)
Lemma fv_FI_mat : forall x regs0 mem0 md0 X, FI B x regs0 mem0 md0 ->
  FI B x regs0 mem0 (with_vm_backing (m_vm_lazy md0) X md0).
Proof.
intros x regs0 mem0 md0 X (HJ & Hio & HK & HSV & H2 & Hc & H8 & H19).
split; [eapply ajournal_materialize; first [exact LAWS | exact parse_segs_low | exact HJ]|].
split; [eapply same_io_trans; [exact Hio | apply fv_same_io_wvb]|].
split; [exact HK|]. split; [exact HSV|]. split; [exact H2|]. split; [exact Hc|].
split; [exact H8 | exact H19].
Qed.

(* the facts of a cut hold of any register file that keeps everything but a0 / a1 *)
Lemma fv_FI_regs : forall x regs0 regs3 mem0 md0, FI B x regs0 mem0 md0 ->
  (forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr regs3 r = getr regs0 r) ->
  FI B x regs3 mem0 md0.
Proof.
intros x regs0 regs3 mem0 md0 (HJ & Hio & HK & HSV & H2 & Hc & H8 & H19) HR.
split; [exact HJ|]. split; [exact Hio|]. split; [exact HK|]. split; [exact HSV|].
split.
{ rewrite HR by (vm_compute; lia). exact H2. }
split.
{ intros r Hr. assert (Hz : bv_unsigned (Z_to_bv 5 r) = r) by (destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; reflexivity).
  rewrite HR by (rewrite Hz; lia). exact (Hc r Hr). }
split.
{ rewrite HR by (vm_compute; lia). exact H8. }
rewrite HR by (vm_compute; lia). exact H19.
Qed.

Lemma fv_fxk_intro : forall (fa fb : YK11.FPState),
  (forall k : bv 5, bv_unsigned k <> 13 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 ->
     Sem.reg_get (@fp_regs fb) k = Sem.reg_get (@fp_regs fa) k) ->
  frm_zero (@fp_csr fb) -> rl_fxk [13; 14; 15] fa fb.
Proof.
intros fa fb H HC. split; [|exact HC].
intros k Hk. apply H; intros E; apply Hk; cbn [In]; lia.
Qed.

(* ======================= the segment ======================= *)
Theorem segFV_ok : segFV_stmt B MT.
Proof using MTL LAWS.
unfold segFV_stmt. intros x b Hpre HT regs2 mem2 md2 HFV.
pose proof HFV as (HFI & Hb8 & Ha2 & Hbr & Hres).
pose proof HFI as (HJ & Hio & HK & HSV & HR2 & HRc & HR8 & HR19).
pose proof Hpre as Hp0. destruct Hp0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm).
pose proof (fv_cell x regs2 mem2 md2 A_C_HALF D_HALF Hpre HFI ltac:(cbn [In]; left; reflexivity)) as CHALF.
pose proof (fv_cell x regs2 mem2 md2 A_C_LO D_LO Hpre HFI ltac:(cbn [In]; right; left; reflexivity)) as CLO.
pose proof (fv_cell x regs2 mem2 md2 A_C_HI D_HI Hpre HFI ltac:(cbn [In]; right; right; left; reflexivity)) as CHI.
destruct ParseFP.role_consts as (RC1 & RC2 & _ & _).
pose proof (ParseFP.rfn_hw_nearest b Nearest.INT32_MIN Nearest.INT32_MAX (Z_to_bv 64 D_LO) (Z_to_bv 64 D_HI)
  Hbr ltac:(unfold Nearest.INT32_MIN; lia) ltac:(unfold Nearest.INT32_MAX; lia)
  ltac:(unfold D_LO, Nearest.INT32_MIN; exact RC1)
  ltac:(unfold D_HI, Nearest.INT32_MAX; exact RC2)) as Hnear.
change (w64 (x_F x)) with (Z_to_bv 64 (x_F x)) in HR2.
change (w64 A_FV_A2) with (Z_to_bv 64 A_FV_A2) in Ha2.
destruct (fv_head fx regs2 (mrestrict (w_H (x_W x)) mem2) b (x_F x) Hfrm HR2 Ha2 Hbr Hb8 CHALF CLO)
  as (C1 & P1 & HC1).
unfold cfg_at. change (w64 PC_FV) with (Z_to_bv 64 PC_FV).
destruct (FP.fle_d (Z_to_bv 64 D_LO) (ParseFP.rfn_d b)) eqn:Efle.
- (* the low test passed *)
  assert (H10 : getr (fvR1 regs2 b) 10 = Z_to_bv 64 1) by (rewrite fv_r1_10, Efle; reflexivity).
  destruct (fv_mid (fvG5 b (@fp_regs fx)) C1 (fvR1 regs2 b) (mrestrict (w_H (x_W x)) mem2) b
    HC1 (fv_g5_15 b (@fp_regs fx)) H10 CHI) as (C2 & P2 & HC2).
  destruct (FP.flt_d (ParseFP.rfn_d b) (Z_to_bv 64 D_HI)) eqn:Eflt.
  + (* in range: the value reaches T *)
    assert (Hin : ParseFP.rfn_in b (Z_to_bv 64 D_LO) (Z_to_bv 64 D_HI) = true)
      by (unfold ParseFP.rfn_in; rewrite Efle, Eflt; reflexivity).
    rewrite Hin in Hnear.
    assert (Hrg : - 2 ^ 31 <= ParseFP.rfn_r b < 2 ^ 31).
    { pose proof (fv_near_bounds b Nearest.INT32_MIN Nearest.INT32_MAX (ParseFP.rfn_r b) Hnear) as HB.
      unfold Nearest.INT32_MIN, Nearest.INT32_MAX in HB. lia. }
    assert (H10' : getr (regupd (regupd (fvR1 regs2 b) 10 (Z_to_bv 64 0x102cc)) 10 (Z_to_bv 64 1)) 10
       = Z_to_bv 64 1) by (apply fv_getr_set; vm_compute; reflexivity).
    destruct (fv_tail (bvmap_set 14 (Z_to_bv 64 D_HI) (fvG5 b (@fp_regs fx))) C2 _
      (mrestrict (w_H (x_W x)) mem2) b HC2
      ltac:(fv_freg; apply fv_g5_15) H10' Hrg) as (C3 & G3 & R3 & P3 & HC3 & HG3 & HR3v & HR3k).
    eapply (SRr_msteps rsegs parse_wx).
    { rewrite restrict_mkst_fx.
      eapply msteps_trans; [exact P1|]. eapply msteps_trans; [exact P2|]. exact P3. }
    intros md' Hsame Hcl.
    rewrite (same_but_materialized_wvb md2 md' Hsame), unrestrict_mkst_mrestrict.
    assert (HRk : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr R3 r = getr regs2 r).
    { intros r Ha Hb'. rewrite (HR3k r Ha Hb').
      rewrite !fv_getr_upd by (eapply fv_upd_z; [vm_compute; reflexivity | lia]).
      apply fv_r1_kept. exact Ha. }
    apply (HT (ParseFP.rfn_r b) (mkFP G3 C3) R3 mem2 _).
    split; [|split; [|split; [|split]]].
    * apply fv_FI_regs with (regs0 := regs2); [apply fv_FI_mat; exact HFI | exact HRk].
    * rewrite HR3v. reflexivity.
    * exact Hrg.
    * apply fv_fxk_intro; [|exact HC3].
      intros k H13 H14 H15. cbn [fp_regs]. rewrite (HG3 k H14).
      rewrite FP.freg_get_other by (eapply fv_other_z; [vm_compute; reflexivity | lia]).
      apply fv_g5_kept; assumption.
    * rewrite Hres, Hnear. reflexivity.
  + (* above the range: -1 *)
    assert (Hin : ParseFP.rfn_in b (Z_to_bv 64 D_LO) (Z_to_bv 64 D_HI) = false)
      by (unfold ParseFP.rfn_in; rewrite Efle, Eflt; reflexivity).
    rewrite Hin in Hnear.
    assert (Hres1 : x_res x = (None, -1)) by (rewrite Hres, Hnear; reflexivity).
    assert (SB : RiscvSemantics.step rsegs
        (@mkst (mkFP (bvmap_set 14 (Z_to_bv 64 D_HI) (fvG5 b (@fp_regs fx))) C2)
           (regupd (regupd (fvR1 regs2 b) 10 (Z_to_bv 64 0x102cc)) 10 (Z_to_bv 64 0))
           (Z_to_bv 64 0x832d8) (mrestrict (w_H (x_W x)) mem2) (seg_rom rsegs))
      = MachineOk (@mkst (mkFP (bvmap_set 14 (Z_to_bv 64 D_HI) (fvG5 b (@fp_regs fx))) C2)
           (regupd (regupd (fvR1 regs2 b) 10 (Z_to_bv 64 0x102cc)) 10 (Z_to_bv 64 0))
           (Z_to_bv 64 PC_M1) (mrestrict (w_H (x_W x)) mem2) (seg_rom rsegs))).
    { unfold PC_M1. apply (fvw_beq_tk _ _ _ _ 0x832d8 0x832f0 330851 10 0 24);
      [ fv_dec | fv_dec | fv_dec | | vm_compute; reflexivity ].
      rewrite fv_getr_set by (vm_compute; reflexivity). rewrite getr_zero. reflexivity. }
    eapply (SRr_msteps rsegs parse_wx).
    { rewrite restrict_mkst_fx.
      eapply msteps_trans; [exact P1|]. eapply msteps_trans; [exact P2|].
      eapply mst_step; [reflexivity | exact SB | ]. apply mst_refl. }
    intros md' Hsame Hcl.
    rewrite (same_but_materialized_wvb md2 md' Hsame), unrestrict_mkst_mrestrict.
    apply (fv_ret_m1 x (mkFP (bvmap_set 14 (Z_to_bv 64 D_HI) (fvG5 b (@fp_regs fx))) C2) _ regs2 mem2 _).
    * exact Hpre.
    * apply fv_FI_mat. exact HFI.
    * apply fv_fxk_intro; [|exact HC2].
      intros k H13 H14 H15. cbn [fp_regs].
      rewrite FP.freg_get_other by (eapply fv_other_z; [vm_compute; reflexivity | lia]).
      apply fv_g5_kept; assumption.
    * exact Hres1.
    * rewrite !fv_getr_upd by (vm_compute; reflexivity).
      rewrite fv_r1_kept by (vm_compute; lia). exact HR2.
    * intros r Hr.
      assert (Hz : bv_unsigned (Z_to_bv 5 r) = r) by (destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; reflexivity).
      assert (Hne : r <> 10 /\ r <> 11) by (destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; split; congruence).
      destruct Hne as [Hn10 Hn11].
      rewrite !fv_getr_upd by (eapply fv_upd_z; [vm_compute; reflexivity | rewrite Hz; lia]).
      rewrite fv_r1_kept by (rewrite Hz; lia).
      exact (HRc r Hr).
- (* below the range: -1 *)
  assert (Hin : ParseFP.rfn_in b (Z_to_bv 64 D_LO) (Z_to_bv 64 D_HI) = false)
    by (unfold ParseFP.rfn_in; rewrite Efle; reflexivity).
  rewrite Hin in Hnear.
  assert (Hres1 : x_res x = (None, -1)) by (rewrite Hres, Hnear; reflexivity).
  assert (SB : RiscvSemantics.step rsegs
      (@mkst (mkFP (fvG5 b (@fp_regs fx)) C1) (fvR1 regs2 b) (Z_to_bv 64 0x832c8)
         (mrestrict (w_H (x_W x)) mem2) (seg_rom rsegs))
    = MachineOk (@mkst (mkFP (fvG5 b (@fp_regs fx)) C1) (fvR1 regs2 b) (Z_to_bv 64 PC_M1)
         (mrestrict (w_H (x_W x)) mem2) (seg_rom rsegs))).
  { unfold PC_M1. apply (fvw_beq_tk _ _ _ _ 0x832c8 0x832f0 33883235 10 0 40);
    [ fv_dec | fv_dec | fv_dec | | vm_compute; reflexivity ].
    rewrite fv_r1_10, Efle, getr_zero. reflexivity. }
  eapply (SRr_msteps rsegs parse_wx).
  { rewrite restrict_mkst_fx.
    eapply msteps_trans; [exact P1|].
    eapply mst_step; [reflexivity | exact SB | ]. apply mst_refl. }
  intros md' Hsame Hcl.
  rewrite (same_but_materialized_wvb md2 md' Hsame), unrestrict_mkst_mrestrict.
  apply (fv_ret_m1 x (mkFP (fvG5 b (@fp_regs fx)) C1) _ regs2 mem2 _).
  * exact Hpre.
  * apply fv_FI_mat. exact HFI.
  * apply fv_fxk_intro; [|exact HC1].
    intros k H13 H14 H15. cbn [fp_regs]. apply fv_g5_kept; assumption.
  * exact Hres1.
  * rewrite fv_r1_kept by (vm_compute; lia). exact HR2.
  * intros r Hr.
    assert (Hz : bv_unsigned (Z_to_bv 5 r) = r) by (destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; reflexivity).
    assert (Hne : r <> 10) by (destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; congruence).
    rewrite fv_r1_kept by (rewrite Hz; lia).
    exact (HRc r Hr).
Qed.

End b.

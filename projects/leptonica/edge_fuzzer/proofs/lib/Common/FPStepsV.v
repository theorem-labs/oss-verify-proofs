(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec RefMemcpyLib FPSteps.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition fpv_read (fr : bvmap 5 word) (fmt : ffmt) (r : reg) : Z :=
  match fmt with FMT_S => bv_unsigned (unbox_s (reg_get fr r)) | FMT_D => bv_unsigned (reg_get fr r) end.
(* [comment removed for export] *)
Definition fpv_box (fmt : ffmt) (v : Z) : word :=
  match fmt with FMT_S => nan_box (Z_to_bv 32 v) | FMT_D => Z_to_bv 64 v end.

Definition fpv_cmp (op : fcmpop) (fmt : ffmt) (a b : Z) : bool * fflags :=
  match op with F_EQ => fp_eq (fp_format fmt) a b | F_LT => fp_lt (fp_format fmt) a b | F_LE => fp_le (fp_format fmt) a b end.

Definition fpv_fma_args (op : fmaop) (f : format) (a z : Z) : Z * Z :=
  match op with F_MADD => (a, z) | F_MSUB => (a, fp_neg f z) | F_NMSUB => (fp_neg f a, z) | F_NMADD => (fp_neg f a, fp_neg f z) end.

(* [comment removed for export] *)
Definition fpv_acc (cs : bv 32) (fl : fflags) : bv 32 := Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl)).
Lemma fpv_frm_acc : forall cs fl, frm_zero cs -> frm_zero (fpv_acc cs fl).
Proof. intros cs fl Hz. apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]. Qed.

Definition fpv_ari (op : fariop) (fmt : ffmt) (md : rmode) (a b : Z) : Z * fflags :=
  match op with F_ADD => fp_add (fp_format fmt) md a b | F_SUB => fp_sub (fp_format fmt) md a b
              | F_MUL => fp_mul (fp_format fmt) md a b | F_DIV => fp_div (fp_format fmt) md a b end.
Definition fpv_fma (op : fmaop) (fmt : ffmt) (md : rmode) (a b z : Z) : Z * fflags :=
  let '(a', z') := fpv_fma_args op (fp_format fmt) a z in fp_fma (fp_format fmt) md a' b z'.
Definition fpv_x_of_f (sf : ffmt) (md : rmode) (sgn : bool) (bits : Z) (a : Z) : word :=
  let v := fst (fp_to_int (fp_format sf) md sgn bits a) in if Z.eqb bits 32 then sext 64 (Z_to_bv 32 v) else Z_to_bv 64 v.

Lemma fpv_rm_dyn : rmode_of_field (bv_unsigned (7 : bv 3)) 0 = Some RNE.
Proof. reflexivity. Qed.
Lemma fpv_rm_rtz : rmode_of_field (bv_unsigned (1 : bv 3)) 0 = Some RTZ.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fpv_get_same : forall (fr : bvmap 5 word) (r : reg) v, reg_get (bvmap_set r v fr) r = v.
Proof. intros fr r v. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma fpv_get_other : forall (fr : bvmap 5 word) (r r' : reg) v, r' <> r -> reg_get (bvmap_set r v fr) r' = reg_get fr r'.
Proof. intros fr r r' v H. unfold reg_get. rewrite bvmap_get_set_other by congruence. reflexivity. Qed.

Lemma fpv_nan_box_unsigned : forall v : bv 32, bv_unsigned (nan_box v) = ((2 ^ 32 - 1) * 2 ^ 32 + bv_unsigned v)%Z.
Proof.
  intros v. unfold nan_box. rewrite bv_concat_unsigned by reflexivity.
  pose proof (bv_unsigned_in_range _ v) as Hv. unfold bv_modulus in Hv. change (Z.of_N 32) with 32%Z in *.
  change (bv_unsigned (Z_to_bv 32 (-1))) with (2 ^ 32 - 1)%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (Z.add_lor_land ((2 ^ 32 - 1) * 2 ^ 32) (bv_unsigned v)) as E.
  assert (L : Z.land ((2 ^ 32 - 1) * 2 ^ 32) (bv_unsigned v) = 0%Z).
  { assert (Ev : bv_unsigned v = Z.land (bv_unsigned v) (Z.ones 32)) by (rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    rewrite Ev. rewrite (Z.land_comm (bv_unsigned v)), Z.land_assoc. rewrite (Z.land_ones ((2 ^ 32 - 1) * 2 ^ 32) 32) by lia.
    rewrite Z_mod_mult. apply Z.land_0_l. }
  rewrite L, Z.add_0_r in E. exact E.
Qed.

Lemma fpv_low32_box : forall v : bv 32, low32 (nan_box v) = v.
Proof.
  intros v. apply bv_eq. rewrite low32_unsigned, fpv_nan_box_unsigned.
  pose proof (bv_unsigned_in_range _ v) as Hv. unfold bv_modulus in Hv. change (Z.of_N 32) with 32%Z in *.
  unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32%Z.
  rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma fpv_unbox_box : forall v : bv 32, unbox_s (nan_box v) = v.
Proof.
  intros v. unfold unbox_s.
  assert (E : bv_unsigned (bv_extract 32 32 (nan_box v)) = Z.ones 32).
  { rewrite bv_extract_unsigned, fpv_nan_box_unsigned.
    pose proof (bv_unsigned_in_range _ v) as Hv. unfold bv_modulus in Hv. change (Z.of_N 32) with 32%Z in *.
    unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32%Z.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (bv_unsigned v)) by lia.
    rewrite Z.add_0_r. reflexivity. }
  rewrite E, Z.eqb_refl. apply fpv_low32_box.
Qed.

Lemma fpv_read_S_box : forall (fr : bvmap 5 word) (r : reg) (v : bv 32), fpv_read (bvmap_set r (nan_box v) fr) FMT_S r = bv_unsigned v.
Proof. intros fr r v. unfold fpv_read. rewrite fpv_get_same, fpv_unbox_box. reflexivity. Qed.
Lemma fpv_read_D_same : forall (fr : bvmap 5 word) (r : reg) (v : word), fpv_read (bvmap_set r v fr) FMT_D r = bv_unsigned v.
Proof. intros fr r v. unfold fpv_read. rewrite fpv_get_same. reflexivity. Qed.
Lemma fpv_read_other : forall (fr : bvmap 5 word) fmt (r r' : reg) v, r' <> r -> fpv_read (bvmap_set r v fr) fmt r' = fpv_read fr fmt r'.
Proof. intros fr fmt r r' v H. unfold fpv_read. rewrite fpv_get_other by exact H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fpv_flw_bytes : forall bs : list byte, length bs = 4%nat ->
  Z_to_le_bytes 4 (bv_unsigned (low32 (nan_box (bv_extract 0 32 (le_bytes_to_word bs))))) = bs.
Proof.
  intros bs L. rewrite fpv_low32_box. unfold le_bytes_to_word.
  pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1. rewrite L in H1. change (8 * Z.of_nat 4)%Z with 32%Z in H1.
  rewrite bv_extract_unsigned, Z_to_bv_unsigned. change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z. change (Z.of_N 32) with 32%Z.
  rewrite (Z.mod_small (bytes_le_to_Z bs) (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
  rewrite <- L. apply RefMemcpyLib.Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fpv_sgnj (op : fsgnop) (fmt : ffmt) (a b : word) : word :=
  match fmt with FMT_S => nan_box (sgnj_val op (unbox_s a) (unbox_s b)) | FMT_D => sgnj_val op a b end.
Lemma fpv_step_fsgnj : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsgnj op fmt rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (fpv_sgnj op fmt (reg_get (@fp_regs fx) rs1) (reg_get (@fp_regs fx) rs2)) (@fp_regs fx)) (@fp_csr fx))
                   regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd.
  destruct fmt; fp_pipeline Hf He Hd; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fpv_step_fcmp : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (@fp_regs fx) (fpv_acc (@fp_csr fx) (snd (fpv_cmp op fmt (fpv_read (@fp_regs fx) fmt rs1) (fpv_read (@fp_regs fx) fmt rs2)))))
               (if bv_eqb rd 0 then regs
                else regupd regs rd (if fst (fpv_cmp op fmt (fpv_read (@fp_regs fx) fmt rs1) (fpv_read (@fp_regs fx) fmt rs2)) then Z_to_bv 64 1 else Z_to_bv 64 0))
               (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  fp_pipeline Hf He Hd.
  unfold fpv_cmp, fpv_read, fpv_acc.
  destruct op, fmt; cbv beta iota;
  match goal with |- context [let '(_, _) := ?p in _] => destruct p as [v fl] eqn:E; cbv beta iota end;
  cbn [fst snd]; (destruct (is_x0 rd); [ rewrite b_npc4; reflexivity | destruct v; cbv beta iota; rewrite b_npc4; reflexivity ]).
Qed.

(* [comment removed for export] *)
Lemma fpv_step_fari : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2 (rm : bv 3) md,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fari op fmt rd rs1 rs2 rm, 4%Z) ->
  frm_zero (@fp_csr fx) -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (fpv_box fmt (fst (fpv_ari op fmt md (fpv_read (@fp_regs fx) fmt rs1) (fpv_read (@fp_regs fx) fmt rs2)))) (@fp_regs fx))
                         (fpv_acc (@fp_csr fx) (snd (fpv_ari op fmt md (fpv_read (@fp_regs fx) fmt rs1) (fpv_read (@fp_regs fx) fmt rs2)))))
                   regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op fmt rd rs1 rs2 rm md Hf He Hd Hz Hmd.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  fp_pipeline Hf He Hd. unfold frm_zero in Hz. rewrite Hz, Hmd. cbv beta iota.
  unfold fpv_box, fpv_read, fpv_ari, fpv_acc.
  destruct op, fmt; cbv beta iota;
    (match goal with |- context [let '(_, _) := ?p in _] => destruct p as [v fl] eqn:E; cbv beta iota end;
     cbn [fst snd]; rewrite b_npc4; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma fpv_step_fcvt_f_of_x : forall (fx : FPState) segs regs pc mem rom w dst src rd rs1 (rm : bv 3) md df sgn bits,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_S /\ df = FMT_S \/ dst = FC_D /\ df = FMT_D) ->
  (src = FC_W /\ sgn = true /\ bits = 32%Z \/ src = FC_WU /\ sgn = false /\ bits = 32%Z \/
   src = FC_L /\ sgn = true /\ bits = 64%Z \/ src = FC_LU /\ sgn = false /\ bits = 64%Z) ->
  frm_zero (@fp_csr fx) -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (fpv_box df (fst (fp_of_int (fp_format df) md sgn bits (bv_unsigned (getr regs rs1))))) (@fp_regs fx))
                         (fpv_acc (@fp_csr fx) (snd (fp_of_int (fp_format df) md sgn bits (bv_unsigned (getr regs rs1))))))
                   regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w dst src rd rs1 rm md df sgn bits Hf He Hd Hdst Hsrc Hz Hmd.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  fp_pipeline Hf He Hd. unfold frm_zero in Hz. rewrite Hz, Hmd. cbv beta iota.
  unfold getr, fpv_box, fpv_acc; rewrite ?bv_eqb0_is_x0.
  destruct Hdst as [[-> ->] | [-> ->]];
  destruct Hsrc as [(-> & -> & ->) | [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]]]; cbv beta iota;
    (destruct (is_x0 rs1); cbv beta iota;
     match goal with |- context [let '(_, _) := ?p in _] => destruct p as [v fl] eqn:E; cbv beta iota end;
     cbn [fst snd]; rewrite b_npc4; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma fpv_step_fcvt_f_of_f : forall (fx : FPState) segs regs pc mem rom w dst src rd rs1 (rm : bv 3) md df sf,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_S /\ df = FMT_S \/ dst = FC_D /\ df = FMT_D) ->
  (src = FC_S /\ sf = FMT_S \/ src = FC_D /\ sf = FMT_D) ->
  frm_zero (@fp_csr fx) -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (fpv_box df (fst (fp_convert (fp_format sf) (fp_format df) md (fpv_read (@fp_regs fx) sf rs1)))) (@fp_regs fx))
                         (fpv_acc (@fp_csr fx) (snd (fp_convert (fp_format sf) (fp_format df) md (fpv_read (@fp_regs fx) sf rs1)))))
                   regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w dst src rd rs1 rm md df sf Hf He Hd Hdst Hsrc Hz Hmd.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  fp_pipeline Hf He Hd. unfold frm_zero in Hz. rewrite Hz, Hmd. cbv beta iota.
  unfold fpv_box, fpv_read, fpv_acc.
  destruct Hdst as [[-> ->] | [-> ->]]; destruct Hsrc as [[-> ->] | [-> ->]]; cbv beta iota;
    (match goal with |- context [let '(_, _) := ?p in _] => destruct p as [v fl] eqn:E; cbv beta iota end;
     cbn [fst snd]; rewrite b_npc4; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma fpv_step_fcvt_x_of_f : forall (fx : FPState) segs regs pc mem rom w dst src rd rs1 (rm : bv 3) md sf sgn bits,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_W /\ sgn = true /\ bits = 32%Z \/ dst = FC_WU /\ sgn = false /\ bits = 32%Z \/
   dst = FC_L /\ sgn = true /\ bits = 64%Z \/ dst = FC_LU /\ sgn = false /\ bits = 64%Z) ->
  (src = FC_S /\ sf = FMT_S \/ src = FC_D /\ sf = FMT_D) ->
  frm_zero (@fp_csr fx) -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (@fp_regs fx) (fpv_acc (@fp_csr fx) (snd (fp_to_int (fp_format sf) md sgn bits (fpv_read (@fp_regs fx) sf rs1)))))
                   (if bv_eqb rd 0 then regs else regupd regs rd (fpv_x_of_f sf md sgn bits (fpv_read (@fp_regs fx) sf rs1)))
                   (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w dst src rd rs1 rm md sf sgn bits Hf He Hd Hdst Hsrc Hz Hmd.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  fp_pipeline Hf He Hd. unfold frm_zero in Hz. rewrite Hz, Hmd. cbv beta iota.
  unfold fpv_read, fpv_acc, fpv_x_of_f.
  destruct Hdst as [(-> & -> & ->) | [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]]]; destruct Hsrc as [[-> ->] | [-> ->]]; cbv beta iota;
    (match goal with |- context [let '(_, _) := ?p in _] => destruct p as [v fl] eqn:E; cbv beta iota zeta end;
     cbn [fst snd Z.eqb Pos.eqb]; destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma fpv_step_fma : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2 rs3 (rm : bv 3) md,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fma op fmt rd rs1 rs2 rs3 rm, 4%Z) ->
  frm_zero (@fp_csr fx) -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (fpv_box fmt (fst (fpv_fma op fmt md (fpv_read (@fp_regs fx) fmt rs1) (fpv_read (@fp_regs fx) fmt rs2) (fpv_read (@fp_regs fx) fmt rs3)))) (@fp_regs fx))
                         (fpv_acc (@fp_csr fx) (snd (fpv_fma op fmt md (fpv_read (@fp_regs fx) fmt rs1) (fpv_read (@fp_regs fx) fmt rs2) (fpv_read (@fp_regs fx) fmt rs3)))))
                   regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op fmt rd rs1 rs2 rs3 rm md Hf He Hd Hz Hmd.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  fp_pipeline Hf He Hd. unfold frm_zero in Hz. rewrite Hz, Hmd. cbv beta iota.
  unfold fpv_box, fpv_read, fpv_fma, fpv_fma_args, fpv_acc.
  destruct op, fmt; cbv beta iota;
    (match goal with |- context [let '(_, _) := ?p in _] => destruct p as [v fl] eqn:E; cbv beta iota end;
     cbn [fst snd]; rewrite b_npc4; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma fp_step_fma : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2 rs3 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fma op fmt rd rs1 rs2 rs3 rm, 4%Z) ->
  frm_zero (@fp_csr fx) ->
  (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  exists fr' cs',
    frm_zero cs' /\
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP fr' cs') regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op fmt rd rs1 rs2 rs3 rm Hf He Hd Hz Hrm.
  destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd]. pose proof Hz as Hz0. unfold frm_zero in Hz0. rewrite Hz0 in Hmd.
  eexists _, _. split; [| exact (fpv_step_fma fx segs regs pc mem rom w op fmt rd rs1 rs2 rs3 rm md Hf He Hd Hz Hmd)].
  apply fpv_frm_acc. exact Hz.
Qed.

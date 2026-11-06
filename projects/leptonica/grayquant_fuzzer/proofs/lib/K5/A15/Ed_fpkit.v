(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import LiaTuning PropExec MState Mem Cells Exec FP Step StepFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fma_opnds (op : fmaop) (f : format) (a z : Z) : Z * Z :=
  match op with
  | F_MADD => (a, z)
  | F_MSUB => (a, fp_neg f z)
  | F_NMSUB => (fp_neg f a, z)
  | F_NMADD => (fp_neg f a, fp_neg f z)
  end.

Definition fma_d (op : fmaop) (md : rmode) (a b z : word) : word :=
  Z_to_bv 64 (fst (fp_fma fmt_double md (fst (fma_opnds op fmt_double (bv_unsigned a) (bv_unsigned z)))
                                        (bv_unsigned b)
                                        (snd (fma_opnds op fmt_double (bv_unsigned a) (bv_unsigned z))))).
Definition fma_s (op : fmaop) (md : rmode) (a b z : word) : word :=
  nan_box (Z_to_bv 32 (fst (fp_fma fmt_single md (fst (fma_opnds op fmt_single (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s z))))
                                                  (bv_unsigned (unbox_s b))
                                                  (snd (fma_opnds op fmt_single (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s z))))))).
Definition fma_fl (op : fmaop) (f : format) (md : rmode) (a b z : Z) : fflags :=
  snd (fp_fma f md (fst (fma_opnds op f a z)) b (snd (fma_opnds op f a z))).

Lemma exec_fma_d : forall sz op rd rs1 rs2 rs3 rm c md,
  rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fma op FMT_D rd rs1 rs2 rs3 rm) c =
  EDone (fset rd (fma_d op md (fget c rs1) (fget c rs2) (fget c rs3))
          (accrue (fma_fl op fmt_double md (bv_unsigned (fget c rs1)) (bv_unsigned (fget c rs2)) (bv_unsigned (fget c rs3)))
                  (with_pc (c_pc c + sz) c))).
Proof.
  intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
  cbn [fp_format fread fwrite]. unfold fma_d, fma_fl, fma_opnds.
  destruct op; cbn [fst snd]; destruct (fp_fma _ _ _ _ _); reflexivity.
Qed.

Lemma exec_fma_s : forall sz op rd rs1 rs2 rs3 rm c md,
  rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fma op FMT_S rd rs1 rs2 rs3 rm) c =
  EDone (fset rd (fma_s op md (fget c rs1) (fget c rs2) (fget c rs3))
          (accrue (fma_fl op fmt_single md (bv_unsigned (unbox_s (fget c rs1))) (bv_unsigned (unbox_s (fget c rs2))) (bv_unsigned (unbox_s (fget c rs3))))
                  (with_pc (c_pc c + sz) c))).
Proof.
  intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
  cbn [fp_format fread fwrite]. unfold fma_s, fma_fl, fma_opnds.
  destruct op; cbn [fst snd]; destruct (fp_fma _ _ _ _ _); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fcvt_w_s (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_single md true 32 (bv_unsigned (unbox_s a))))).
Definition fcvt_wu_s (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_single md false 32 (bv_unsigned (unbox_s a))))).
Definition fcvt_l_s (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s a)))).
Definition fcvt_lu_s (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_single md false 64 (bv_unsigned (unbox_s a)))).

Local Ltac fcvt_tac H :=
  unfold exec, resolve_rm; unfold frm_of in *; cbn [c_fcsr with_pc]; rewrite H;
  cbn [fp_format fread fwrite Z.eqb Pos.eqb];
  first [ destruct (fp_to_int _ _ _ _ _); reflexivity
        | destruct (fp_of_int _ _ _ _ _); reflexivity
        | destruct (fp_convert _ _ _ _); reflexivity ].

Lemma exec_fcvt_w_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_W FC_S rd rs1 rm) c =
  EDone (rset rd (fcvt_w_s md (fget c rs1)) (accrue (snd (fp_to_int fmt_single md true 32 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_w_s. fcvt_tac H. Qed.
Lemma exec_fcvt_wu_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_WU FC_S rd rs1 rm) c =
  EDone (rset rd (fcvt_wu_s md (fget c rs1)) (accrue (snd (fp_to_int fmt_single md false 32 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_wu_s. fcvt_tac H. Qed.
Lemma exec_fcvt_l_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_L FC_S rd rs1 rm) c =
  EDone (rset rd (fcvt_l_s md (fget c rs1)) (accrue (snd (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_l_s. fcvt_tac H. Qed.
Lemma exec_fcvt_lu_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_LU FC_S rd rs1 rm) c =
  EDone (rset rd (fcvt_lu_s md (fget c rs1)) (accrue (snd (fp_to_int fmt_single md false 64 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_lu_s. fcvt_tac H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac exec_pre_fp2 i :=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fma ?op FMT_D ?rd ?rs1 ?rs2 ?rs3 ?rm => let H := rm_proof rm c in rewrite (exec_fma_d sz op rd rs1 rs2 rs3 rm c _ H)
    | Fma ?op FMT_S ?rd ?rs1 ?rs2 ?rs3 ?rm => let H := rm_proof rm c in rewrite (exec_fma_s sz op rd rs1 rs2 rs3 rm c _ H)
    | Fcvt FC_W FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_s sz rd rs1 rm c _ H)
    | Fcvt FC_WU FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_s sz rd rs1 rm c _ H)
    | Fcvt FC_L FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_s sz rd rs1 rm c _ H)
    | Fcvt FC_LU FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_s sz rd rs1 rm c _ H)
    | _ => idtac
    end
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac exec_pre_lib i :=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
    | Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
    | Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv zeta
    | Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
    | Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
    | Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
    | Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
    | Csr ?op ?rd ?rs1 ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
            simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | CsrI ?op ?rd ?uimm ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
            let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
            try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | _ => idtac
    end
  | |- _ => idtac   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Ltac exec_pre_frm :=
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

Ltac exec_pre i ::= exec_pre_lib i; exec_pre_fp2 i; exec_pre_frm.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma fk_land31 : forall x, 0 <= x -> 0 <= Z.land x 31 <= 31.
Proof.
  intros x Hx. assert (E : Z.land x 31 = x mod 32). { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
  rewrite E. assert (B : 0 < 32) by lia. pose proof (Z.mod_pos_bound x 32 B). lia.
Qed.
Lemma fk_clear_unsigned : forall fc, bv_unsigned (frm_clear fc) = Z.land (bv_unsigned fc) 31.
Proof.
  intros fc. unfold frm_clear. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 32 fc) as HR. pose proof (fk_land31 (bv_unsigned fc) ltac:(lia)).
  rewrite bv_wrap_small by (unfold bv_modulus; lia). reflexivity.
Qed.
Lemma fk_clear_idem : forall fc, frm_clear (frm_clear fc) = frm_clear fc.
Proof. intros fc. unfold frm_clear at 1. rewrite fk_clear_unsigned. rewrite <- Z.land_assoc. reflexivity. Qed.
(* [comment removed for export] *)
Lemma frm0_frm_clear : forall fc, frm0 (frm_clear fc).
Proof.
  intros fc. unfold frm0. rewrite fk_clear_unsigned.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.shiftr_spec, Z.land_spec, Z.bits_0 by lia.
  change 31 with (Z.ones 5). change 7 with (Z.ones 3).
  destruct (Z.lt_ge_cases i 3).
  - rewrite (Z.ones_spec_high 5 (i + 5)) by lia. rewrite andb_false_r. reflexivity.
  - rewrite (Z.ones_spec_high 3 i) by lia. apply andb_false_r.
Qed.
(* [comment removed for export] *)
Lemma frm_clear_accrue : forall fc fl,
  Z_to_bv 32 (Z.lor (bv_unsigned (frm_clear fc)) (fflags_bits fl)) = frm_clear (Z_to_bv 32 (Z.lor (bv_unsigned fc) (fflags_bits fl))).
Proof.
  intros fc fl. unfold frm_clear at 2. rewrite fk_clear_unsigned. f_equal.
  rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 32 fc) as HR. unfold bv_modulus in HR.
  pose proof (fflags_bits_range fl) as HB.
  rewrite bv_wrap_small by (unfold bv_modulus; apply Z_lor_lt_pow2; lia).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, !Z.land_spec, Z.lor_spec by lia.
  change 31 with (Z.ones 5). destruct (Z.lt_ge_cases i 5).
  - rewrite Z.ones_spec_low by lia. rewrite !andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite !andb_false_r. cbn.
    destruct (Z.eq_dec (fflags_bits fl) 0) as [E|E]. { rewrite E, Z.bits_0. reflexivity. }
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 5; [apply Z.log2_lt_pow2; lia|lia].
Qed.
(* [comment removed for export] *)
Lemma frm_clear_small : forall fc, bv_unsigned fc < 32 -> frm_clear fc = fc.
Proof.
  intros fc H. apply bv_eq. rewrite fk_clear_unsigned. pose proof (bv_unsigned_in_range 32 fc).
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Ltac rm_proof rm c ::=
  let z := eval vm_compute in (bv_unsigned rm) in
  lazymatch z with
  | 7%Z =>
      lazymatch c with
      | Core _ _ _ ?fc _ =>
          lazymatch fc with
          | frm_clear ?x => constr:(rmode_dyn rm c (@eq_refl Z 7%Z) (frm0_frm_clear x))
          | _ =>
            lazymatch goal with
            | FRM : frm0 fc |- _ => constr:(rmode_dyn rm c (@eq_refl Z 7%Z) FRM)
            | _ => fail 100 "FP instruction with dynamic rounding mode: fcsr" fc "is neither [frm_clear _] nor covered by a hypothesis [frm0 _]"
            end
          end
      end
  | _ =>
      let md := eval vm_compute in (match rmode_of_Z z with Some md => md | None => RNE end) in
      constr:(rmode_static rm c md (@eq_refl bool false) (@eq_refl (option rmode) (Some md)))
  end.

(* [comment removed for export] *)
Ltac norm_fcsr_lib :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ ?fce _ _ _) =>
      tryif is_var fce then idtac else
      (let fcn := fresh "fc" in
       let E := fresh "Efc" in
       tryif (let H := fresh "FRM" in
              assert (H : frm0 fce) by prove_frm0;
              repeat match goal with
              | H' : frm0 ?f |- _ => lazymatch f with fce => fail | _ => clear H' end
              end;
              remember fce as fcn eqn:E; clear E;
              try rename H into FRM)
       then idtac
       else (remember fce as fcn eqn:E; clear E))
  | _ => idtac
  end.
Ltac norm_fcsr ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ ?fce _ _ _) =>
      lazymatch fce with
      | frm_clear ?x => tryif is_var x then idtac else (let fcn := fresh "fc" in let E := fresh "Efc" in remember x as fcn eqn:E; clear E)
      | Z_to_bv 32 (Z.lor (bv_unsigned (frm_clear ?x)) (fflags_bits ?fl)) =>
          rewrite (frm_clear_accrue x fl);
          let fcn := fresh "fc" in let E := fresh "Efc" in
          remember (Z_to_bv 32 (Z.lor (bv_unsigned x) (fflags_bits fl))) as fcn eqn:E; clear E
      | _ => norm_fcsr_lib
      end
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac frm_now :=
  repeat match goal with H : frm0 _ |- _ => clear H end;
  match goal with
  | |- context [MS _ _ _ (frm_clear ?x) _ _ _] => pose proof (frm0_frm_clear x) as FRM
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fbr :=
  lazymatch goal with
  | |- context [bword ?b] => let B := fresh "fb" in remember b as B eqn:?; destruct B
  end.
(* [comment removed for export] *)

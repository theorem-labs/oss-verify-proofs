(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec SeqExec.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fcsr_frm (fc : bv 32) : Z := Z.land (Z.shiftr (bv_unsigned fc) 5) 7.
Definition fcsr_ok (fc : bv 32) : Prop := (bv_unsigned fc <? 32)%Z = true.

Lemma fcsr_ok_frm : forall fc, fcsr_ok fc -> fcsr_frm fc = 0%Z.
Proof.
  intros fc H. unfold fcsr_ok, fcsr_frm in *. apply Z.ltb_lt in H.
  pose proof (bv_unsigned_in_range _ fc) as [H0 _].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5)%Z with 32%Z.
  rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma fcsr_ok_of_FP : forall FP : FPState, fcsr_ok (fp_csr (FPState:=FP)).
Proof. intros FP. exact fp_csr_ok. Qed.

(* [comment removed for export] *)
Definition rm_of (rm : bv 3) (fc : bv 32) : option rmode :=
  rmode_of_field (bv_unsigned rm) (fcsr_frm fc).
Definition rm_static (rm : bv 3) : option rmode := rmode_of_field (bv_unsigned rm) 0.

Lemma rm_of_static : forall rm fc, fcsr_ok fc -> rm_of rm fc = rm_static rm.
Proof. intros rm fc H. unfold rm_of. rewrite (fcsr_ok_frm fc H). reflexivity. Qed.

Lemma rm_of_FP : forall (FP : FPState) rm, rm_of rm fp_csr = rm_static rm.
Proof. intros FP rm. apply rm_of_static. apply fcsr_ok_of_FP. Qed.

Definition fcsr_accrue (fl : fflags) (fc : bv 32) : bv 32 :=
  Z_to_bv 32 (Z.lor (bv_unsigned fc) (fflags_bits fl)).

Lemma fflags_bits_range : forall fl, (0 <= fflags_bits fl < 32)%Z.
Proof. intros [[|] [|] [|] [|] [|]]; vm_compute; easy. Qed.

Lemma u32_range : forall x : bv 32, (0 <= bv_unsigned x < 2^32)%Z.
Proof. intro x. pose proof (bv_unsigned_in_range _ x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma lor_small_bound : forall a b n, (0 <= a < 2^n)%Z -> (0 <= b < 2^n)%Z -> (0 <= n)%Z ->
  (0 <= Z.lor a b < 2^n)%Z.
Proof.
  intros a b n Ha Hb Hn. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma fcsr_accrue_unsigned : forall fl fc,
  bv_unsigned (fcsr_accrue fl fc) = Z.lor (bv_unsigned fc) (fflags_bits fl).
Proof.
  intros fl fc. unfold fcsr_accrue. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. pose proof (u32_range fc). pose proof (fflags_bits_range fl).
  apply (lor_small_bound _ _ 32); lia.
Qed.

Lemma fcsr_accrue_ok : forall fl fc, fcsr_ok fc -> fcsr_ok (fcsr_accrue fl fc).
Proof.
  intros fl fc H. unfold fcsr_ok in *. apply Z.ltb_lt in H. apply Z.ltb_lt.
  rewrite fcsr_accrue_unsigned. pose proof (fflags_bits_range fl). pose proof (u32_range fc).
  apply (lor_small_bound _ _ 5); cbn; lia.
Qed.

(* [comment removed for export] *)
Definition fp_with_regs (fr : bvmap 5 word) (FP : FPState) : FPState :=
  FPS fr (fp_csr (FPState:=FP)) (fp_csr_ok (FPState:=FP)).
Definition fp_setreg (rd : reg) (v : word) (FP : FPState) : FPState :=
  fp_with_regs (bvmap_set rd v (fp_regs (FPState:=FP))) FP.
Definition fp_accrue (fl : fflags) (FP : FPState) : FPState :=
  FPS (fp_regs (FPState:=FP)) (fcsr_accrue fl (fp_csr (FPState:=FP)))
      (fcsr_accrue_ok fl _ (fp_csr_ok (FPState:=FP))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fval (fmt : ffmt) (x : word) : Z :=
  match fmt with FMT_S => bv_unsigned (unbox_s x) | FMT_D => bv_unsigned x end.
Definition fword (fmt : ffmt) (v : Z) : word :=
  match fmt with FMT_S => nan_box (Z_to_bv 32 v) | FMT_D => Z_to_bv 64 v end.

Definition fmt_bytes (fmt : ffmt) : nat := match fmt with FMT_S => 4%nat | FMT_D => 8%nat end.

Definition fari_raw (op : fariop) (f : format) (md : rmode) (a b : Z) : Z * fflags :=
  match op with
  | F_ADD => fp_add f md a b | F_SUB => fp_sub f md a b
  | F_MUL => fp_mul f md a b | F_DIV => fp_div f md a b
  end.
Definition fari_res (op : fariop) (fmt : ffmt) (md : rmode) (x y : word) : word :=
  fword fmt (fst (fari_raw op (fp_format fmt) md (fval fmt x) (fval fmt y))).
Definition fari_fl (op : fariop) (fmt : ffmt) (md : rmode) (x y : word) : fflags :=
  snd (fari_raw op (fp_format fmt) md (fval fmt x) (fval fmt y)).

Definition fma_raw (op : fmaop) (f : format) (md : rmode) (a b c : Z) : Z * fflags :=
  match op with
  | F_MADD => fp_fma f md a b c
  | F_MSUB => fp_fma f md a b (fp_neg f c)
  | F_NMSUB => fp_fma f md (fp_neg f a) b c
  | F_NMADD => fp_fma f md (fp_neg f a) b (fp_neg f c)
  end.
Definition fma_res (op : fmaop) (fmt : ffmt) (md : rmode) (x y z : word) : word :=
  fword fmt (fst (fma_raw op (fp_format fmt) md (fval fmt x) (fval fmt y) (fval fmt z))).
Definition fma_fl (op : fmaop) (fmt : ffmt) (md : rmode) (x y z : word) : fflags :=
  snd (fma_raw op (fp_format fmt) md (fval fmt x) (fval fmt y) (fval fmt z)).

Definition fsqrt_res (fmt : ffmt) (md : rmode) (x : word) : word :=
  fword fmt (fst (fp_sqrt (fp_format fmt) md (fval fmt x))).
Definition fsqrt_fl (fmt : ffmt) (md : rmode) (x : word) : fflags :=
  snd (fp_sqrt (fp_format fmt) md (fval fmt x)).

Definition minmax_is_max (op : fminmaxop) : bool :=
  match op with F_MIN => false | F_MAX => true end.
Definition fminmax_res (op : fminmaxop) (fmt : ffmt) (x y : word) : word :=
  fword fmt (fst (fp_minmax (fp_format fmt) (minmax_is_max op) (fval fmt x) (fval fmt y))).
Definition fminmax_fl (op : fminmaxop) (fmt : ffmt) (x y : word) : fflags :=
  snd (fp_minmax (fp_format fmt) (minmax_is_max op) (fval fmt x) (fval fmt y)).

Definition fcmp_raw (op : fcmpop) (f : format) (a b : Z) : bool * fflags :=
  match op with F_EQ => fp_eq f a b | F_LT => fp_lt f a b | F_LE => fp_le f a b end.
Definition fcmp_bool (op : fcmpop) (fmt : ffmt) (x y : word) : bool :=
  fst (fcmp_raw op (fp_format fmt) (fval fmt x) (fval fmt y)).
Definition bool_word (b : bool) : word := if b then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition fcmp_res (op : fcmpop) (fmt : ffmt) (x y : word) : word :=
  bool_word (fcmp_bool op fmt x y).
Definition fcmp_fl (op : fcmpop) (fmt : ffmt) (x y : word) : fflags :=
  snd (fcmp_raw op (fp_format fmt) (fval fmt x) (fval fmt y)).

Definition fclass_res (fmt : ffmt) (x : word) : word :=
  Z_to_bv 64 (fp_class (fp_format fmt) (fval fmt x)).

Definition fsgnj_res (op : fsgnop) (fmt : ffmt) (x y : word) : word :=
  match fmt with
  | FMT_S => nan_box (sgnj_val op (unbox_s x) (unbox_s y))
  | FMT_D => sgnj_val op x y
  end.

(* [comment removed for export] *)
Definition fcvt_fty (t : fcvt_ty) : option ffmt :=
  match t with FC_S => Some FMT_S | FC_D => Some FMT_D | _ => None end.
Definition fcvt_ity (t : fcvt_ty) : option (bool * Z) :=
  match t with
  | FC_W => Some (true, 32%Z) | FC_WU => Some (false, 32%Z)
  | FC_L => Some (true, 64%Z) | FC_LU => Some (false, 64%Z)
  | _ => None
  end.

Definition fcvt_ff_res (sf df : ffmt) (md : rmode) (x : word) : word :=
  fword df (fst (fp_convert (fp_format sf) (fp_format df) md (fval sf x))).
Definition fcvt_ff_fl (sf df : ffmt) (md : rmode) (x : word) : fflags :=
  snd (fp_convert (fp_format sf) (fp_format df) md (fval sf x)).

(* [comment removed for export] *)
Definition fcvt_fi_val (sf : ffmt) (sgn : bool) (bits : Z) (md : rmode) (x : word) : Z :=
  fst (fp_to_int (fp_format sf) md sgn bits (fval sf x)).
(* [comment removed for export] *)
Definition int_word (bits : Z) (v : Z) : word :=
  if Z.eqb bits 32 then sext 64 (Z_to_bv 32 v) else Z_to_bv 64 v.
Definition fcvt_fi_res (sf : ffmt) (sgn : bool) (bits : Z) (md : rmode) (x : word) : word :=
  int_word bits (fcvt_fi_val sf sgn bits md x).
Definition fcvt_fi_fl (sf : ffmt) (sgn : bool) (bits : Z) (md : rmode) (x : word) : fflags :=
  snd (fp_to_int (fp_format sf) md sgn bits (fval sf x)).

Definition fcvt_if_res (df : ffmt) (sgn : bool) (bits : Z) (md : rmode) (x : word) : word :=
  fword df (fst (fp_of_int (fp_format df) md sgn bits (bv_unsigned x))).
Definition fcvt_if_fl (df : ffmt) (sgn : bool) (bits : Z) (md : rmode) (x : word) : fflags :=
  snd (fp_of_int (fp_format df) md sgn bits (bv_unsigned x)).

(* [comment removed for export] *)
Definition fmv_xf_res (fmt : ffmt) (x : word) : word :=
  match fmt with FMT_S => sext 64 (low32 x) | FMT_D => x end.
Definition fmv_fx_res (fmt : ffmt) (x : word) : word :=
  match fmt with FMT_S => nan_box (low32 x) | FMT_D => x end.

(* [comment removed for export] *)
Definition fload_res (fmt : ffmt) (bs : list byte) : word :=
  match fmt with
  | FMT_S => nan_box (bv_extract 0 32 (le_bytes_to_word bs))
  | FMT_D => bv_extract 0 64 (le_bytes_to_word bs)
  end.

(* [comment removed for export] *)
Lemma fload_res_val : forall fmt bs,
  length bs = fmt_bytes fmt ->
  fload_res fmt bs = fmv_fx_res fmt (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
  intros fmt bs Hlen. unfold fload_res, fmv_fx_res, le_bytes_to_word, low32.
  destruct fmt; [reflexivity|].
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac step_pipeline_fp Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.with_fregs Sem.with_fcsr
     Sem.fget Sem.fset Sem.fread Sem.fwrite Sem.resolve_rm Sem.frm_of Sem.accrue
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_fregs ms_fcsr ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst fp_regs fp_csr
     fp_setreg fp_with_regs fp_accrue
     rm_of fcsr_frm fcsr_accrue
     fval fword fari_res fari_fl fari_raw fma_res fma_fl fma_raw fsqrt_res fsqrt_fl
     fminmax_res fminmax_fl minmax_is_max fcmp_res fcmp_bool fcmp_fl fcmp_raw bool_word fclass_res
     fsgnj_res fcvt_ff_res fcvt_ff_fl fcvt_fi_res fcvt_fi_val fcvt_fi_fl int_word
     fcvt_if_res fcvt_if_fl fmv_xf_res fmv_fx_res fload_res fmt_bytes];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
Ltac pair_finish :=
  rewrite ?b_npc4;
  first
    [ reflexivity
    | match goal with
      | |- context [let '(_, _) := ?X in _] => destruct X; cbv beta iota; rewrite ?b_npc4; reflexivity
      end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPSteps.
Context {FP : FPState}.
Let fr : bvmap 5 word := fp_regs.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma step_fload : forall segs regs pc mem rom w fmt rd rs (imm : bv 12) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FLoad fmt rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (fmt_bytes fmt) = Some bs ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_setreg rd (fload_res fmt bs) FP) regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w fmt rd rs imm bs Hfetch Hecall Hdecode Hread.
  destruct FP as [fr0 fc0 Hfc0].
  step_pipeline_fp Hfetch Hecall Hdecode.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  destruct fmt; cbn [fmt_bytes] in Hread; cbv beta iota;
    rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

Lemma step_fstore : forall segs regs pc mem rom w fmt (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FStore fmt rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) (fmt_bytes fmt) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes (fmt_bytes fmt) (reg_get fp_regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w fmt rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  destruct FP as [fr0 fc0 Hfc0].
  step_pipeline_fp Hfetch Hecall Hdecode.
  unfold getr in Hok |- *; rewrite ?bv_eqb0_is_x0 in Hok |- *.
  rewrite b_addsext.
  destruct fmt; cbn [fmt_bytes] in Hok; cbv beta iota; rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, b_npc4; [rewrite store_bytes_low32|]; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma step_fmv_xf : forall segs regs pc mem rom w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_X_F fmt rd rs1, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (fmv_xf_res fmt (reg_get fp_regs rs1)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w fmt rd rs1 Hfetch Hecall Hdecode.
  destruct FP as [fr0 fc0 Hfc0].
  step_pipeline_fp Hfetch Hecall Hdecode.
  destruct fmt; destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

Lemma step_fmv_fx : forall segs regs pc mem rom w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_F_X fmt rd rs1, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_setreg rd (fmv_fx_res fmt (getr regs rs1)) FP) regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w fmt rd rs1 Hfetch Hecall Hdecode.
  destruct FP as [fr0 fc0 Hfc0].
  step_pipeline_fp Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct fmt; destruct (is_x0 rs1); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma step_fsgnj : forall segs regs pc mem rom w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsgnj op fmt rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_setreg rd (fsgnj_res op fmt (reg_get fp_regs rs1) (reg_get fp_regs rs2)) FP)
                  regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op fmt rd rs1 rs2 Hfetch Hecall Hdecode.
  destruct FP as [fr0 fc0 Hfc0].
  step_pipeline_fp Hfetch Hecall Hdecode.
  destruct fmt; cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma step_fari : forall segs regs pc mem rom w op fmt rd rs1 rs2 rm md,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fari op fmt rd rs1 rs2 rm, 4%Z) ->
  rm_static rm = Some md ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_setreg rd (fari_res op fmt md (reg_get fr rs1) (reg_get fr rs2))
                           (fp_accrue (fari_fl op fmt md (reg_get fr rs1) (reg_get fr rs2)) FP))
                  regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op fmt rd rs1 rs2 rm md Hfetch Hecall Hdecode Hrm.
  rewrite <- (rm_of_FP FP) in Hrm. unfold rm_of, fcsr_frm in Hrm. subst fr.
  destruct FP as [fr0 fc0 Hfc0]. cbn [fp_csr fp_regs] in Hrm |- *.
  step_pipeline_fp Hfetch Hecall Hdecode.
  rewrite Hrm. cbv beta iota.
  destruct op; destruct fmt; cbv beta iota delta [fp_format]; pair_finish.
Qed.

Lemma step_fsqrt : forall segs regs pc mem rom w fmt rd rs1 rm md,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsqrt fmt rd rs1 rm, 4%Z) ->
  rm_static rm = Some md ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_setreg rd (fsqrt_res fmt md (reg_get fr rs1))
                           (fp_accrue (fsqrt_fl fmt md (reg_get fr rs1)) FP))
                  regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w fmt rd rs1 rm md Hfetch Hecall Hdecode Hrm.
  rewrite <- (rm_of_FP FP) in Hrm. unfold rm_of, fcsr_frm in Hrm. subst fr.
  destruct FP as [fr0 fc0 Hfc0]. cbn [fp_csr fp_regs] in Hrm |- *.
  step_pipeline_fp Hfetch Hecall Hdecode.
  rewrite Hrm. cbv beta iota.
  destruct fmt; cbv beta iota delta [fp_format]; pair_finish.
Qed.

Lemma step_fma : forall segs regs pc mem rom w op fmt rd rs1 rs2 rs3 rm md,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fma op fmt rd rs1 rs2 rs3 rm, 4%Z) ->
  rm_static rm = Some md ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_setreg rd (fma_res op fmt md (reg_get fr rs1) (reg_get fr rs2) (reg_get fr rs3))
                           (fp_accrue (fma_fl op fmt md (reg_get fr rs1) (reg_get fr rs2) (reg_get fr rs3)) FP))
                  regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op fmt rd rs1 rs2 rs3 rm md Hfetch Hecall Hdecode Hrm.
  rewrite <- (rm_of_FP FP) in Hrm. unfold rm_of, fcsr_frm in Hrm. subst fr.
  destruct FP as [fr0 fc0 Hfc0]. cbn [fp_csr fp_regs] in Hrm |- *.
  step_pipeline_fp Hfetch Hecall Hdecode.
  rewrite Hrm. cbv beta iota.
  destruct op; destruct fmt; cbv beta iota delta [fp_format]; pair_finish.
Qed.

Lemma step_fminmax : forall segs regs pc mem rom w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fminmax op fmt rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_setreg rd (fminmax_res op fmt (reg_get fr rs1) (reg_get fr rs2))
                           (fp_accrue (fminmax_fl op fmt (reg_get fr rs1) (reg_get fr rs2)) FP))
                  regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op fmt rd rs1 rs2 Hfetch Hecall Hdecode. subst fr.
  destruct FP as [fr0 fc0 Hfc0]. cbn [fp_csr fp_regs].
  step_pipeline_fp Hfetch Hecall Hdecode.
  destruct op; destruct fmt; cbv beta iota delta [fp_format]; pair_finish.
Qed.

(* [comment removed for export] *)

Lemma step_fcmp : forall segs regs pc mem rom w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_accrue (fcmp_fl op fmt (reg_get fr rs1) (reg_get fr rs2)) FP)
                  (if bv_eqb rd 0 then regs else regupd regs rd (fcmp_res op fmt (reg_get fr rs1) (reg_get fr rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op fmt rd rs1 rs2 Hfetch Hecall Hdecode. subst fr.
  destruct FP as [fr0 fc0 Hfc0]. cbn [fp_csr fp_regs].
  step_pipeline_fp Hfetch Hecall Hdecode.
  destruct op; destruct fmt; cbv beta iota delta [fp_format];
  match goal with
  | |- context [let '(_, _) := ?X in _] => destruct X as [[|] ?]
  end; destruct (is_x0 rd); cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_fclass : forall segs regs pc mem rom w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass fmt rd rs1, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (fclass_res fmt (reg_get fr rs1)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w fmt rd rs1 Hfetch Hecall Hdecode. subst fr.
  destruct FP as [fr0 fc0 Hfc0]. cbn [fp_csr fp_regs].
  step_pipeline_fp Hfetch Hecall Hdecode.
  destruct fmt; destruct (is_x0 rd); cbv beta iota delta [fp_format]; rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma step_fcvt_ff : forall segs regs pc mem rom w dst src rd rs1 rm md df sf,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  rm_static rm = Some md ->
  fcvt_fty dst = Some df -> fcvt_fty src = Some sf ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_setreg rd (fcvt_ff_res sf df md (reg_get fr rs1))
                           (fp_accrue (fcvt_ff_fl sf df md (reg_get fr rs1)) FP))
                  regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w dst src rd rs1 rm md df sf Hfetch Hecall Hdecode Hrm Hd Hs.
  rewrite <- (rm_of_FP FP) in Hrm. unfold rm_of, fcsr_frm in Hrm. subst fr.
  destruct FP as [fr0 fc0 Hfc0]. cbn [fp_csr fp_regs] in Hrm |- *.
  step_pipeline_fp Hfetch Hecall Hdecode.
  rewrite Hrm. cbv beta iota.
  destruct dst; try discriminate Hd; destruct src; try discriminate Hs;
    injection Hd as <-; injection Hs as <-; cbv beta iota delta [fp_format]; pair_finish.
Qed.

Lemma step_fcvt_fi : forall segs regs pc mem rom w dst src rd rs1 rm md sgn bits sf,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  rm_static rm = Some md ->
  fcvt_ity dst = Some (sgn, bits) -> fcvt_fty src = Some sf ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_accrue (fcvt_fi_fl sf sgn bits md (reg_get fr rs1)) FP)
                  (if bv_eqb rd 0 then regs else regupd regs rd (fcvt_fi_res sf sgn bits md (reg_get fr rs1)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w dst src rd rs1 rm md sgn bits sf Hfetch Hecall Hdecode Hrm Hd Hs.
  rewrite <- (rm_of_FP FP) in Hrm. unfold rm_of, fcsr_frm in Hrm. subst fr.
  destruct FP as [fr0 fc0 Hfc0]. cbn [fp_csr fp_regs] in Hrm |- *.
  step_pipeline_fp Hfetch Hecall Hdecode.
  rewrite Hrm. cbv beta iota.
  destruct dst; try discriminate Hd; destruct src; try discriminate Hs;
    injection Hd as <- <-; injection Hs as <-; cbv beta iota delta [fp_format];
  match goal with
  | |- context [let '(_, _) := ?X in _] => destruct X
  end; destruct (is_x0 rd); cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_fcvt_if : forall segs regs pc mem rom w dst src rd rs1 rm md df sgn bits,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  rm_static rm = Some md ->
  fcvt_fty dst = Some df -> fcvt_ity src = Some (sgn, bits) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (FP:=fp_setreg rd (fcvt_if_res df sgn bits md (getr regs rs1))
                           (fp_accrue (fcvt_if_fl df sgn bits md (getr regs rs1)) FP))
                  regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w dst src rd rs1 rm md df sgn bits Hfetch Hecall Hdecode Hrm Hd Hs.
  rewrite <- (rm_of_FP FP) in Hrm. unfold rm_of, fcsr_frm in Hrm. subst fr.
  destruct FP as [fr0 fc0 Hfc0]. cbn [fp_csr fp_regs] in Hrm |- *.
  step_pipeline_fp Hfetch Hecall Hdecode.
  rewrite Hrm. cbv beta iota.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct dst; try discriminate Hd; destruct src; try discriminate Hs;
    injection Hd as <-; injection Hs as <- <-; destruct (is_x0 rs1); cbv beta iota delta [fp_format]; pair_finish.
Qed.

End FPSteps.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition getf2_prog (B : Z) : RStep.ptree :=
  PNode 92%Z
  (PNode 44%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 14 0 4095 4
        (PJ_Lui_nn 4 17 32767 4
        (PJ_ShiftImm_ALU_SRL_nnn 8 16 14 1 4
        (PJ_Op_ALU_AND_nnn 12 15 11 16 4
        (PJ_ShiftImm_ALU_SLL_nnn 16 17 17 36 4
        (PJ_Branch_BC_EQ_nnn 20 15 17 20 4
        (PJ_Op_ALU_SLTU_nnn 24 17 17 15 4
        (PJ_Branch_BC_EQ_nnn 28 17 0 20 4
        (PJ_OpImm_ALU_ADD_nnn 32 10 14 0 4
        (PJ_Jalr_nnn 36 0 1 0 4
        (PJ_Op_ALU_SLTU_nnn 40 17 0 10 4 nil))))))))))))
    (PLeaf
        (PJ_Branch_BC_NE_nnn 44 17 0 8180 4
        (PJ_Op_ALU_AND_nnn 48 16 13 16 4
        (PJ_Lui_nn 52 17 32767 4
        (PJ_ShiftImm_ALU_SLL_nnn 56 17 17 36 4
        (PJ_Branch_BC_EQ_nnn 60 16 17 16 4
        (PJ_Op_ALU_SLTU_nnn 64 17 17 16 4
        (PJ_Branch_BC_EQ_nnn 68 17 0 16 4
        (PJ_Jal_nn 72 0 2097112 4
        (PJ_Op_ALU_SLTU_nnn 76 17 0 12 4
        (PJ_Branch_BC_NE_nnn 80 17 0 8144 4
        (PJ_Op_ALU_OR_nnn 84 17 12 10 4
        (PJ_Op_ALU_OR_nnn 88 15 16 15 4 nil))))))))))))))
  (PNode 140%Z
    (PLeaf
        (PJ_Op_ALU_OR_nnn 92 15 17 15 4
        (PJ_Branch_BC_EQ_nnn 96 15 0 28 4
        (PJ_Op_ALU_AND_nnn 100 15 13 11 4
        (PJ_Branch_BC_LT_nnn 104 15 0 28 4
        (PJ_Branch_BC_EQ_nnn 108 11 13 40 4
        (PJ_Op_ALU_SLT_nnn 112 15 11 13 4
        (PJ_Branch_BC_NE_nnn 116 15 0 8108 4
        (PJ_Jal_nn 120 0 48 4
        (PJ_OpImm_ALU_ADD_nnn 124 10 0 0 4
        (PJ_Jalr_nnn 128 0 1 0 4
        (PJ_Branch_BC_EQ_nnn 132 11 13 28 4
        (PJ_Op_ALU_SLT_nnn 136 15 13 11 4 nil)))))))))))))
    (PLeaf
        (PJ_Branch_BC_NE_nnn 140 15 0 8084 4
        (PJ_Jal_nn 144 0 24 4
        (PJ_Op_ALU_SLTU_nnn 148 15 10 12 4
        (PJ_Branch_BC_NE_nnn 152 15 0 8072 4
        (PJ_Jal_nn 156 0 12 4
        (PJ_Op_ALU_SLTU_nnn 160 15 12 10 4
        (PJ_Branch_BC_NE_nnn 164 15 0 8060 4
        (PJ_Op_ALU_XOR_nnn 168 10 10 12 4
        (PJ_Op_ALU_XOR_nnn 172 11 11 13 4
        (PJ_Op_ALU_OR_nnn 176 10 10 11 4
        (PJ_Op_ALU_SLTU_nnn 180 10 0 10 4
        (PJ_Jalr_nnn 184 0 1 0 4 nil)))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_getf2 (IMG : RImg) := getf2_prog (sym 0x1b314).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_getf2 : CodeAtT img_segs (sym 0x1b314) (PROGAT_CODE_getf2 IMG)}.
  Context {RB_getf2 : RelCode (sym 0x1b314) 188}.
  Collection ImgHyps := IMG CODE_getf2 RB_getf2.



(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition getf2_entry := (sym 0x1b314)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ge_isnan_w (lo hi : Z) : bool :=
  (let absHi := Z.land hi ABS_HI in
   if absHi =? INF_HI then negb (lo =? 0) else INF_HI <? absHi)%Z.

(* [comment removed for export] *)
Definition ge_isless (a_lo a_hi b_lo b_hi : Z) : bool :=
  (if negb (is_neg64 (Z.land b_hi a_hi)) then
     (if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
   else
     (if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi))%Z.

Definition ge_tail (il : bool) (a_lo a_hi b_lo b_hi : Z) : Z :=
  if il then (-1)%Z else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).

Definition ge_core (a_lo a_hi b_lo b_hi : Z) : Z :=
  (if Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi ABS_HI) (Z.land a_hi ABS_HI)) =? 0 then 0
   else ge_tail (ge_isless a_lo a_hi b_lo b_hi) a_lo a_hi b_lo b_hi)%Z.


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
(* [comment removed for export] *)
Ltac decide_test1_f t := replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia); cbn [andb orb negb].
Ltac decide_test1_t t := replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia); cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
  intros lo hi H. unfold lo64. rewrite wrap64_mod.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
  intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
  rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma f128_ge_split : forall a_lo a_hi b_lo b_hi,
  (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z -> (0 <= b_lo < 2^64)%Z -> (0 <= b_hi < 2^64)%Z ->
  f128_ge (a_lo + 2^64 * a_hi) (b_lo + 2^64 * b_hi) =
  if ge_isnan_w a_lo a_hi then (-1)%Z
  else if ge_isnan_w b_lo b_hi then (-1)%Z
  else ge_core a_lo a_hi b_lo b_hi.
Proof.
  intros. unfold f128_ge. rewrite !lo64_words, !hi64_words by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma b2z_snez : forall x, (0 <= x)%Z -> Z.b2z (0 <? x)%Z = nez64 x.
Proof.
  intros x Hx. unfold nez64, b2z. destruct (Z.ltb_spec0 0 x); destruct (Z.eqb_spec x 0); cbn; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition getf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv img_segs m.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono img_segs m m := wmono_refl img_segs m.

  Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
  Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
  Notation POST r := (getf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m).
  (* [comment removed for export] *)
  Notation ST pc x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom img_segs)).
  Notation M63 := 9223372036854775807%Z.

  (* [comment removed for export] *)
  Lemma getf2_L54 : forall (a4 a5 a6 a7 : word) (r : Z),
    r = nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)) ->
    evt img_segs (POST r) (ST (sym 0x1b314 + 168) a4 a5 a6 a7).
  Proof using MI ImgHyps.
    intros a4 a5 a6 a7 r HR. subst r.
    do 5 zstep. rewrite b2z_snez by zrange_nonneg. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma getf2_Lcc : forall (a5 a6 a7 : word) (r : Z),
    r = (-1)%Z ->
    evt img_segs (POST r) (ST (sym 0x1b314 + 32) (Z_to_bv 64 (-1)) a5 a6 a7).
  Proof using MI ImgHyps.
    intros a5 a6 a7 r HR. subst r. zstep. zstep. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma getf2_L00 : forall (a7 : word) (r : Z),
    r = ge_core a_lo a_hi b_lo b_hi ->
    evt img_segs (POST r) (ST (sym 0x1b314 + 84) (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.land a_hi M63)) (Z_to_bv 64 (Z.land b_hi M63)) a7).
  Proof using MI ImgHyps.
    intros a7 r HR. subst r. unfold ge_core, ABS_HI.
    zr_pose (Z.land b_hi a_hi).
    do 4 zstep.
    if_cases Kz; zify_cond Kz.
    - (* [comment removed for export] *)
      zstep. zstep. decide_test1 ((Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi 9223372036854775807) (Z.land a_hi 9223372036854775807))) =? 0%Z)%Z. finish.
    - decide_test1 ((Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi 9223372036854775807) (Z.land a_hi 9223372036854775807))) =? 0%Z)%Z. unfold ge_isless, ge_tail, is_neg64, lt_s64, SIGN64.
      zstep. zstep. if_cases Kn; zify_cond Kn; [ decide_test1_f ((Z.land b_hi a_hi ≫ 63)%Z =? 0%Z)%Z | decide_test1_t ((Z.land b_hi a_hi ≫ 63)%Z =? 0%Z)%Z ].
      + (* [comment removed for export] *)
        zstep. if_cases Ke; zify_cond Ke; [ decide_test1_t (a_hi =? b_hi)%Z | decide_test1_f (a_hi =? b_hi)%Z ].
        * (* [comment removed for export] *) zstep. zstep. if_cases Kl; zify_cond Kl; [ decide_test1_t (b_lo <? a_lo)%Z | decide_test1_f (b_lo <? a_lo)%Z ].
          -- apply getf2_Lcc. reflexivity.
          -- apply getf2_L54. reflexivity.
        * zstep. zstep. if_cases Kl; zify_cond Kl; [ decide_test1_t ((Z.lxor b_hi 9223372036854775808) <? (Z.lxor a_hi 9223372036854775808))%Z | decide_test1_f ((Z.lxor b_hi 9223372036854775808) <? (Z.lxor a_hi 9223372036854775808))%Z ].
          -- apply getf2_Lcc. reflexivity.
          -- zstep. apply getf2_L54. reflexivity.
      + zstep. if_cases Ke; zify_cond Ke; [ decide_test1_t (a_hi =? b_hi)%Z | decide_test1_f (a_hi =? b_hi)%Z ].
        * zstep. zstep. if_cases Kl; zify_cond Kl; [ decide_test1_t (a_lo <? b_lo)%Z | decide_test1_f (a_lo <? b_lo)%Z ].
          -- apply getf2_Lcc. reflexivity.
          -- zstep. apply getf2_L54. reflexivity.
        * zstep. zstep. if_cases Kl; zify_cond Kl; [ decide_test1_t ((Z.lxor a_hi 9223372036854775808) <? (Z.lxor b_hi 9223372036854775808))%Z | decide_test1_f ((Z.lxor a_hi 9223372036854775808) <? (Z.lxor b_hi 9223372036854775808))%Z ].
          -- apply getf2_Lcc. reflexivity.
          -- zstep. apply getf2_L54. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma getf2_Ldc : forall (a7 : word) (r : Z),
    r = (if ge_isnan_w b_lo b_hi then (-1)%Z else ge_core a_lo a_hi b_lo b_hi) ->
    evt img_segs (POST r) (ST (sym 0x1b314 + 48) (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.land a_hi M63)) (Z_to_bv 64 M63) a7).
  Proof using MI ImgHyps.
    intros a7 r HR. unfold ge_isnan_w, ABS_HI, INF_HI in HR.
    do 4 zstep.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases Kl; zify_cond Kl.
      + (* [comment removed for export] *) apply getf2_Lcc. rewrite HR. decide_test1_try ((Z.land b_hi 9223372036854775807) =? 9223090561878065152%Z)%Z; decide_test1_try (b_lo =? 0%Z)%Z. reflexivity.
      + apply getf2_L00. rewrite HR. decide_test1_try ((Z.land b_hi 9223372036854775807) =? 9223090561878065152%Z)%Z; decide_test1_try (b_lo =? 0%Z)%Z. reflexivity.
    - zstep. zstep. if_cases Kl; zify_cond Kl.
      + apply getf2_L00. rewrite HR. decide_test1_try ((Z.land b_hi 9223372036854775807) =? 9223090561878065152%Z)%Z; decide_test1_try (9223090561878065152%Z <? (Z.land b_hi 9223372036854775807))%Z. reflexivity.
      + zstep. apply getf2_Lcc. rewrite HR. decide_test1_try ((Z.land b_hi 9223372036854775807) =? 9223090561878065152%Z)%Z; decide_test1_try (9223090561878065152%Z <? (Z.land b_hi 9223372036854775807))%Z. reflexivity.
  Qed.
End Proofs.

Lemma getf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (getf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (f128_ge (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b314)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  rewrite f128_ge_split by (pose proof (bv_unsigned_in_range 64 a0); pose proof (bv_unsigned_in_range 64 a1);
                            pose proof (bv_unsigned_in_range 64 a2); pose proof (bv_unsigned_in_range 64 a3);
                            unfold bv_modulus in *; lia).
  remember (if ge_isnan_w (bv_unsigned a0) (bv_unsigned a1) then _ else _) as r eqn:HR.
  unfold ge_isnan_w at 1, ABS_HI, INF_HI in HR.
  do 6 zstep.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 2 zstep. if_cases Kl; zify_cond Kl.
    + apply getf2_Lcc; [exact MI|]. rewrite HR. decide_test1_try ((Z.land (bv_unsigned a1) 9223372036854775807) =? 9223090561878065152%Z)%Z; decide_test1_try ((bv_unsigned a0) =? 0%Z)%Z. reflexivity.
    + apply getf2_Ldc; [exact MI|]. rewrite HR. decide_test1_try ((Z.land (bv_unsigned a1) 9223372036854775807) =? 9223090561878065152%Z)%Z; decide_test1_try ((bv_unsigned a0) =? 0%Z)%Z. reflexivity.
  - do 2 zstep. if_cases Kl; zify_cond Kl.
    + apply getf2_Ldc; [exact MI|]. rewrite HR. decide_test1_try ((Z.land (bv_unsigned a1) 9223372036854775807) =? 9223090561878065152%Z)%Z; decide_test1_try (9223090561878065152%Z <? (Z.land (bv_unsigned a1) 9223372036854775807))%Z. reflexivity.
    + apply getf2_Lcc; [exact MI|]. rewrite HR. decide_test1_try ((Z.land (bv_unsigned a1) 9223372036854775807) =? 9223090561878065152%Z)%Z; decide_test1_try (9223090561878065152%Z <? (Z.land (bv_unsigned a1) 9223372036854775807))%Z. reflexivity.
Qed.

(* [comment removed for export] *)
Definition getf2_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (getf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (f128_ge (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b314)) fc None m (seg_rom img_segs)).
Lemma getf2_contract_ok : getf2_contract.
Proof. exact getf2_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_f t := replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia); cbn [andb orb negb].
Ltac decide_test1_t t := replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia); cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

(* [comment removed for export] *)
Existing Class getf2_contract.

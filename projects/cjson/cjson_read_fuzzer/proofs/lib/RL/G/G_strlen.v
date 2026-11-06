(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition strlen_prog (B K_ones K_highs : Z) : RStep.ptree :=
  PNode 72%Z
  (PNode 36%Z
    (PLeaf
        (PJ_OpImm_ALU_AND_nnn 0 11 10 7 4
        (PJ_OpImm_ALU_ADD_nnn 4 12 10 0 4
        (PJ_Branch_BC_EQ_nnn 8 11 0 52 4
        (PJ_Load_SZ1_false_nnn 12 11 10 0 4
        (PJ_Branch_BC_EQ_nnn 16 11 0 120 4
        (PJ_OpImm_ALU_ADD_nnn 20 12 10 1 4
        (PJ_OpImm_ALU_ADD_nnn 24 11 10 0 4
        (PJ_OpImm_ALU_ADD_nnn 28 13 11 1 4
        (PJ_OpImm_ALU_AND_nnn 32 13 13 7 4 nil))))))))))
    (PLeaf
        (PJ_Branch_BC_EQ_nnn 36 13 0 24 4
        (PJ_Load_SZ1_false_nnn 40 13 12 0 4
        (PJ_OpImm_ALU_ADD_nnn 44 12 12 1 4
        (PJ_OpImm_ALU_ADD_nnn 48 11 11 1 4
        (PJ_Branch_BC_NE_nnn 52 13 0 8168 4
        (PJ_Jal_nn 56 0 72 4
        (PJ_Auipc_nt 60 11 (hi20 (K_ones - (B + 60))) 4
        (PJ_Auipc_nt 64 14 (hi20 (K_highs - (B + 64))) 4
        (PJ_Load_SZ8_true_nnt 68 13 11 (lo12 (K_ones - (B + 60))) 4 nil)))))))))))
  (PNode 108%Z
    (PLeaf
        (PJ_Load_SZ8_true_nnt 72 14 14 (lo12 (K_highs - (B + 64))) 4
        (PJ_OpImm_ALU_ADD_nnn 76 11 12 4087 4
        (PJ_OpImm_ALU_ADD_nnn 80 12 12 4088 4
        (PJ_Load_SZ8_true_nnn 84 15 12 8 4
        (PJ_OpImm_ALU_ADD_nnn 88 12 12 8 4
        (PJ_Op_ALU_SUB_nnn 92 16 13 15 4
        (PJ_Op_ALU_OR_nnn 96 15 16 15 4
        (PJ_Op_ALU_AND_nnn 100 15 15 14 4
        (PJ_OpImm_ALU_ADD_nnn 104 11 11 8 4 nil))))))))))
    (PLeaf
        (PJ_Branch_BC_EQ_nnn 108 15 14 8168 4
        (PJ_Load_SZ1_false_nnn 112 13 12 0 4
        (PJ_OpImm_ALU_ADD_nnn 116 12 12 1 4
        (PJ_OpImm_ALU_ADD_nnn 120 11 11 1 4
        (PJ_Branch_BC_NE_nnn 124 13 0 8180 4
        (PJ_Op_ALU_SUB_nnn 128 10 11 10 4
        (PJ_Jalr_nnn 132 0 1 0 4
        (PJ_Op_ALU_SUB_nnn 136 10 10 10 4
        (PJ_Jalr_nnn 140 0 1 0 4 nil))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_strlen (IMG : RImg) := strlen_prog (sym 0x21830) (sym 0x103f8) (sym 0x103e8).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_strlen : CodeAtT img_segs (sym 0x21830) (PROGAT_CODE_strlen IMG)}.
  Context {RB_strlen : RelCode (sym 0x21830) 144}.
  Context {RO_103f8 : RoB img_segs (sym 0x103f8) ([BV 8 0; BV 8 1; BV 8 1; BV 8 1; BV 8 1; BV 8 1; BV 8 1; BV 8 1])}.
  Context {RO_103e8 : RoB img_segs (sym 0x103e8) ([BV 8 128; BV 8 128; BV 8 128; BV 8 128; BV 8 128; BV 8 128; BV 8 128; BV 8 128])}.
  Context {RS_K_ones : RelSym (sym 0x103f8)}.
  Context {RS_K_highs : RelSym (sym 0x103e8)}.
  Collection ImgHyps := IMG CODE_strlen RB_strlen RO_103f8 RO_103e8 RS_K_ones RS_K_highs.



Definition strlen_entry := (sym 0x21830)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ bytes_at img_segs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
  Hypothesis MI : mem_inv img_segs m.
  Hypothesis STR : bytes_at img_segs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono img_segs m m := wmono_refl img_segs m.

  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m).
  (* [comment removed for export] *)
  Notation ST pc x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom img_segs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof. rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B. lia. Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma strlen_tail : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i <= len)%Z ->
    evt img_segs POST (ST (sym 0x21830 + 112) (Z_to_bv 64 (A + i - 1)) (Z_to_bv 64 (A + i)) a3 a4 a5 a6).
  Proof.
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read img_segs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_false. zstep. zstep.
      replace (A + len - 1 + 1 - A)%Z with len by lia. finish.
    - (nelim (full_nth_lt i ltac:(lia)) 3%nat; intros b Hn Hb).
      pose proof (u8ro_read img_segs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
      replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
      replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply (IH (i + 1)%Z); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_words : forall (k : nat) (j : Z) (a5 a6 : word),
    (Z.to_nat (len - j) = k) -> (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evt img_segs POST (ST (sym 0x21830 + 84) (Z_to_bv 64 (A + j - 9)) (Z_to_bv 64 (A + j - 8)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) a5 a6).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros j a5 a6 Hk Hj Hal; pose proof A_bound as AB.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read img_segs m A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 7 zstep.
    replace (A + j - 8 + 8)%Z with (A + j)%Z by lia.
    replace (A + j - 9 + 8)%Z with (A + j - 1)%Z by lia.
    rewrite (load8_le_val chunk CL).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      replace (A + j - 1)%Z with (A + (j + 8) - 9)%Z by lia.
      replace (Z_to_bv 64 (A + j)) with (Z_to_bv 64 (A + (j + 8) - 8)) by (f_equal; lia).
      apply (IH (Z.to_nat (len - (j + 8)))); try lia. all: Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      apply (strlen_tail (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_wentry : forall (j : Z) (a1 a3 a4 a5 a6 : word),
    (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evt img_segs POST (ST (sym 0x21830 + 60) a1 (Z_to_bv 64 (A + j)) a3 a4 a5 a6).
  Proof.
    intros j a1 a3 a4 a5 a6 Hj Hal. pose proof A_bound as AB.
    do 6 zstep.
    replace (A + j + -9)%Z with (A + j - 9)%Z by lia.
    replace (A + j + -8)%Z with (A + j - 8)%Z by lia.
    apply (strlen_words (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_head : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i < len)%Z ->
    evt img_segs POST (ST (sym 0x21830 + 28) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 a6).
  Proof.
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB; [lia|].
    do 3 zstep. if_cases Kal; zify_cond Kal.
    - replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply strlen_wentry; [lia|]. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
    - destruct (Z.eq_dec (i + 1) len) as [E|NE].
      + pose proof (u8ro_read img_segs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
        do 4 zstep. if_false. do 3 zstep.
        replace (A + i + 1 - A)%Z with len by lia. finish.
      + (nelim (full_nth_lt (i + 1) ltac:(lia)) 3%nat; intros b Hn Hb).
        pose proof (u8ro_read img_segs m A full (i + 1) b _ STR Hn ltac:(lia) eq_refl) as RD.
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); lia.
  Qed.
End Proofs.

Lemma strlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte),
  bytes_at img_segs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv img_segs m ->
  evt img_segs (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21830)) fc None m (seg_rom img_segs)).
Proof.
  intros until slack. intros STR NONUL PAD MI.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  do 3 zstep. if_cases Kal; zify_cond Kal.
  - (* [comment removed for export] *)
    eapply evt_eq.
    2:{ eapply (strlen_wentry _ _ _ _ _ _ _ _ _ a0) with (j := 0%Z); try eassumption; try lia.
        revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
    unfold mkR. rewrite Z_to_bv_plus0. reflexivity.
  - destruct str as [|c str'] eqn:Es.
    + (* [comment removed for export] *)
      pose proof (u8ro_read img_segs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_true. do 2 zstep.
      replace (bv_unsigned a0 - bv_unsigned a0)%Z with 0%Z by lia. finish.
    + assert (Hc : bv_unsigned c <> 0%Z).
      { intros Hc. apply NONUL. left. apply bv_eq. rewrite Hc. reflexivity. }
      pose proof (u8ro_read img_segs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_cases K; zify_cond K. { exfalso. exact (Hc K). }
      do 2 zstep.
      eapply evt_eq.
      2:{ eapply (strlen_head _ _ _ _ _ _ _ _ _ a0) with (i := 0%Z) (k := length (c :: str')); try eassumption; cbn [length]; lia. }
      unfold mkR. rewrite Z.add_0_r, Z_to_bv_lit_self. reflexivity.
Qed.

(* [comment removed for export] *)
Definition strlen_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte),
  bytes_at img_segs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv img_segs m ->
  evt img_segs (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21830)) fc None m (seg_rom img_segs)).
Lemma strlen_contract_ok : strlen_contract.
Proof. exact strlen_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class strlen_contract.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "valuation"; "sprop"; "holds"; "sv_below"; "SLit"; "SAlu"; "ext_low"; "soff"; "SPBranch"; "SPNot"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "True"; "or"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_signed"; "@Corelib.Init.Datatypes"; "bool"; "true"; "prod"; "list"; "Some"; "option"; "fst"; "pair"; "snd"; "nat"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.V"; "in_itv"; "dgv_ok"; "sumZ"; "tbl_ok"; "bits_ok"; "cls_ok"; "nes_ok"; "sv_size"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "modulo"; "add"; "lt"; "land"; "sub"; "lor"; "lxor"; "of_N"; "testbit"; "div"; "eqb"; "max"; "mul"; "opp"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "fdig"; "bfact"; "cfact"; "decision"; "nfact"; "dg_facts"; "tbl_entry"; "atoms_of"; "canon_prop"; "ctx0"; "dg_tbl"; "ifact"; "is_lit0"; "itv_t"; "lit_fold_t"; "mk_aluw_f_t"; "mk_ext_f_t"; "remove_atom"; "sum_atoms"; "sum_of"; "align_round"; "and_lit"; "and_lo"; "bit_pair"; "bit_refine"; "bit_refine1"; "bit_refine_iter"; "bit_test"; "bits_refine"; "bits_refine_iter"; "canon_branch"; "classify_fact"; "cls_itv"; "cls_shift"; "dg_bits"; "dg_cls"; "dg_nes"; "dg_with_tbl"; "fact_itv"; "fact_lookup"; "facts_itv"; "itv_body"; "itv_decide"; "itv_decide_t"; "itv_meet"; "itv_node"; "mk_aluw_f"; "mk_aluw_s"; "mk_bits"; "mk_cls"; "mk_ext_f"; "mk_ext_s"; "mk_nes"; "ne_lit"; "ne_pair"; "ne_refine"; "nes_refine"; "pow2_j"; "shift_itv"; "shift_refine"; "shifted_of"; "slt_xor_fold"; "small_u_t"; "snorm"; "tbl_find"; "tbl_shift"; "top_itv"; "xor_same_base"; "@Stdlib.Lists.List"; "forallb"; "fold_right"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "low32"; "branch_taken"; "alu32"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_ADD"; "branch_cond"; "ALU_AND"; "ALU_SLTU"; "ALU_OR"; "ALU_XOR"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma holds_dec : ltac2:(tb__ "0|1|
S5S6S14S7R2R1A2M0S11G0A1A2Fp;Frho;").
Proof.
  intros rho p. induction p; cbn.
  - destruct (branch_taken c (eval rho a) (eval rho b)); [left; reflexivity | right; discriminate].
  - tauto.
  - destruct (Z_lt_dec (bv_unsigned (eval rho a)) (bv_unsigned (eval rho b))); tauto.
  - destruct (Z_le_dec (bv_unsigned (eval rho a)) (bv_unsigned (eval rho b))); tauto.
  - destruct (decide (eval rho a = eval rho b)); tauto.
  - left; exact I.
  - destruct (Z_le_dec 0 a), (Z.eq_dec (bv_unsigned (rw rho i) mod 2 ^ a) 0); tauto.
Qed.

Lemma canon_branch_sound : ltac2:(tb__ "0|0|
S5S89S3S3S12S7R4S5bR3R2R1A3A2S7R4SdR3R2R1A3A2A2Fb;Fa;Fc;Frho;").
Proof.
  intros rho c a b. destruct c; cbn; try tauto.
  - destruct (bv_eqb (eval rho a) (eval rho b)); cbn; split; intros H; try congruence; auto; try (intros E; discriminate).
  - destruct (bv_lts (eval rho a) (eval rho b)); cbn; split; intros H; try congruence; auto; try (intros E; discriminate).
  - destruct (bv_ltu (eval rho a) (eval rho b)); cbn; split; intros H; try congruence; auto; try (intros E; discriminate).
Qed.

Lemma canon_prop_sound : ltac2:(tb__ "0|0|
S5S6S12S7R2S45R1A1A2S7R2R1A2A2Fp;Frho;").
Proof.
  intros rho p. induction p; try (cbn; split; intros H; exact H).
  - apply canon_branch_sound.
  - cbn [canon_prop]. pose proof (holds_dec rho (canon_prop p)) as D.
    destruct IHp as [IH1 IH2].
    destruct (canon_prop p); cbn [holds] in *;
    try (split; [intros H Hp; exact (H (IH2 Hp)) | intros H Hc; exact (H (IH1 Hc))]).

    split.
    + intros Hr Hp. exact (IH2 Hp Hr).
    + intros Hnp. destruct D as [Dn|Dnn].
      * exfalso. apply Hnp. apply IH1. exact Dn.
      * destruct (holds_dec rho s) as [Hs|Hns]; [exact Hs|]. exfalso. apply Dnn. exact Hns.
Qed.

Lemma canon_prop_not : ltac2:(tb__ "0|0|
S5S6S12S7R2S45SeR1A1A1A2S11S7R2R1A2A1A2Fp;Frho;").
Proof.
  intros rho p. pose proof (canon_prop_sound rho (SPNot p)) as [A B]. cbn [holds] in A, B.
  split; [exact A | exact B].
Qed.

Section V.
Variable segs : list Segment.

Lemma fact_lookup_sound : ltac2:(tb__ "0|1|
S5S1cS6A1S6S3cS6S7R3A1R2A3S40OLx;S64R3R2A2S7R4R2A2M0S11G0A1S13X40x3F_;Fp;Ffacts;Frho;").
Proof using .
  intros rho facts p Hall. induction facts as [|f rest IH]; [exact I|].
  inversion Hall as [|f' rest' Hf Hrest]; subst. cbn [fact_lookup].
  destruct (sprop_eqb (canon_prop f) (canon_prop p)) eqn:E1.
  - apply canon_prop_sound. rewrite <- (sprop_eqb_sound _ _ E1). apply canon_prop_sound. exact Hf.
  - destruct (sprop_eqb (canon_prop f) (canon_prop (SPNot p))) eqn:E2.
    + apply (canon_prop_not rho p). rewrite <- (sprop_eqb_sound _ _ E2). apply canon_prop_sound. exact Hf.
    + apply IH. exact Hrest.
Qed.

Definition sumZ (rho : valuation) (atoms : list sv) : Z := ltac2:(tb__ "0|0|
S82S0S3S3S0S2fS15Q40S4Vrho;R2A2A2R1A2Lacc;La;Z0Vatoms;A5").

Lemma atoms_of_sound : ltac2:(tb__ "0|2|
S5S3S1cS3A1M0S0G0S0SfS1bG0S0A2S44R5R4R3A3S20G0S0R2R1A4A3SfS0S2eS2fS26R7R3A2R2A2S2dZ2Z40A2M1A2S2eS2fS2fS15Q40S4R7R6A2A2S26R7R5A2A2R4A2G1A2A3F_;Fc';Fatoms;Fc;Facc;Fe;Frho;").
Proof using .
  intros rho e. induction e; intros acc c atoms c' H; cbn in H;
    try (inversion H; subst; cbn [sumZ fold_right]; f_equal; lia).
  - inversion H; subst. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
    replace (z mod 2 ^ 64 + sumZ rho atoms + c) with (z mod 2 ^ 64 + (sumZ rho atoms + c)) by lia.
    rewrite Zplus_mod_idemp_l. f_equal. lia.
  - destruct op; try (inversion H; subst; cbn [sumZ fold_right]; f_equal; lia).
    destruct (atoms_of e1 acc c) as [acc1 c1] eqn:E1.
    specialize (IHe1 acc c acc1 c1 E1). specialize (IHe2 acc1 c1 atoms c' H).
    rewrite IHe2. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. rewrite two64.
    replace (bv_unsigned (eval rho e2) + sumZ rho acc1 + c1) with (bv_unsigned (eval rho e2) + (sumZ rho acc1 + c1)) by lia.
    rewrite <- Zplus_mod_idemp_r, IHe1, Zplus_mod_idemp_r.
    replace ((bv_unsigned (eval rho e1) + bv_unsigned (eval rho e2)) mod 2 ^ 64 + sumZ rho acc + c)
      with ((bv_unsigned (eval rho e1) + bv_unsigned (eval rho e2)) mod 2 ^ 64 + (sumZ rho acc + c)) by lia.
    rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma sum_atoms_sound : ltac2:(tb__ "0|0|
S5S1cS3A1SfS0S15Q40S4R2S4fR1A1A2A2S2eS26R2R1A2S2dZ2Z40A2A2A3Fatoms;Frho;").
Proof using .
  intros rho atoms. induction atoms as [|a rest IH].
  - cbn [sum_atoms sumZ fold_right eval]. rewrite Z_to_bv_unsigned. reflexivity.
  - cbn [sum_atoms]. destruct rest as [|a2 rest2].
    + cbn [sumZ fold_right]. rewrite Z.add_0_r. symmetry. apply Z.mod_small. apply urange.
    + cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, IH. unfold bv_wrap. rewrite two64.
      rewrite Zplus_mod_idemp_r. cbn [sumZ fold_right]. f_equal.
Qed.

Lemma sum_of_sound : ltac2:(tb__ "0|0|
S5S1cS3A1S0SfS0S15Q40S4R3S50R2R1A2A2A2S2eS2fS26R3R2A2R1A2S2dZ2Z40A2A2A3Fc;Fatoms;Frho;").
Proof using .
  intros rho atoms c. unfold sum_of. destruct atoms as [|a rest].
  - cbn [sumZ fold_right eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, Z.mod_mod by lia. f_equal.
  - rewrite mk_addk_sound, bv_add_unsigned, Z_to_bv_unsigned, sum_atoms_sound. unfold bv_wrap. rewrite two64.
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma remove_atom_sound : ltac2:(tb__ "0|1|
S5S3S1cS3A1M0G0SfS1eG0A1S4eR3R2A2S1dG0R1A2A3SfS0S26R5R3A2S2fS15Q40S4R5R4A2A2S26R5R2A2A2A3F_;Frest;Fatoms;Fb;Frho;").
Proof using .
  intros rho b atoms. induction atoms as [|a t IH]; intros rest H; cbn in H; [discriminate|].
  destruct (sv_eqb a b) eqn:E.
  - inversion H; subst. rewrite (sv_eqb_sound _ _ E). reflexivity.
  - destruct (remove_atom b t) as [rest'|] eqn:Er; [|discriminate]. inversion H; subst.
    cbn [sumZ fold_right]. specialize (IH rest' eq_refl). unfold sumZ in IH. rewrite IH. lia.
Qed.

Lemma remove_atom_below : ltac2:(tb__ "0|1|
S1S3S1cS3A1M0G0SfS19S81S3S8R4A1R2A3S1aA3SfS1eG0A1S4eR4R3A2S1dG0R2A2A3SfS19S81S3S8R6A1R3A3S1aA3F_;F_;Frest;Fatoms;Fb;Fn;").
Proof using .
  intros n b atoms. induction atoms as [|a t IH]; intros rest Hb H; cbn in H; [discriminate|].
  cbn in Hb. apply andb_prop in Hb as [Ha Ht].
  destruct (sv_eqb a b).
  - inversion H; subst. exact Ht.
  - destruct (remove_atom b t) as [rest'|] eqn:Er; [|discriminate]. inversion H; subst.
    cbn. rewrite Ha. apply IH; [exact Ht | reflexivity].
Qed.

Lemma atoms_of_below : ltac2:(tb__ "0|1|
S1S3S1cS3A1M0S0G0S0SfS19S8R6R5A2S1aA3SfS19S81S3S8R7A1R5A3S1aA3SfS1bG0S0A2S44R7R6R5A3S20G0S0R4R3A4A3SfS19S81S3S8R9A1R5A3S1aA3F_;F_;F_;Fc';Fatoms;Fc;Facc;Fe;Fn;").
Proof using .
  intros n e. induction e; intros acc c atoms c' He Hacc H; cbn in H;
    try (inversion H; subst; cbn [forallb]; rewrite He; exact Hacc).
  - inversion H; subst. exact Hacc.
  - pose proof He as He0. cbn in He. apply andb_prop in He as [He1 He2].
    destruct op; try (inversion H; subst; cbn [forallb]; rewrite He0; exact Hacc).
    destruct (atoms_of e1 acc c) as [acc1 c1] eqn:E1.
    eapply IHe2; [exact He2 | | exact H]. eapply IHe1; eauto.
Qed.

Lemma sum_atoms_below : ltac2:(tb__ "0|0|
S1S1cS3A1SfS19S81S3S8R2A1R1A3S1aA3SfS19S8R3S4fR2A1A2S1aA3F_;Fatoms;Fn;").
Proof using .
  intros n atoms. induction atoms as [|a rest IH]; intros H; [reflexivity|].
  cbn in H. apply andb_prop in H as [Ha Hr]. cbn [sum_atoms]. destruct rest.
  - exact Ha.
  - apply below_SAlu; [exact Ha | apply IH; exact Hr].
Qed.

Lemma sum_of_below : ltac2:(tb__ "0|0|
S1S1cS3A1S0SfS19S81S3S8R3A1R2A3S1aA3SfS19S8R4S50R3R2A2A2S1aA3F_;Fc;Fatoms;Fn;").
Proof using .
  intros n atoms c H. unfold sum_of. destruct atoms as [|a rest]; [reflexivity|].
  apply mk_addk_below. apply sum_atoms_below. exact H.
Qed.

Definition in_itv (p : Z * Z) (v : Z) : Prop := ltac2:(tb__ "0|0|
S10S2cS1fS0S0Vp;A3Vv;A2S2cVv;S21S0S0Vp;A3A2A2").

Lemma in_top : ltac2:(tb__ "0|1|
S16Q40M0A1S24S7fS15G0R1A2A2Fv;").
Proof using . intros v. unfold in_itv, top_itv. cbn. pose proof (urange v). lia. Qed.

Lemma in_meet : ltac2:(tb__ "0|1|
S1bS0S0A2M0G0S0S24R3R1A2S24R3R2A2S24S69R5R4A2R3A2F_;F_;Fv;Fq;Fp;").
Proof using . intros [a b] [c d] v [H1 H2] [H3 H4]. unfold in_itv, itv_meet. cbn in *. lia. Qed.

Lemma lit_unsigned : ltac2:(tb__ "0|1|
S0SfS0S15Q40M0S17G0R1A2A2S2eR1S2dZ2Z40A2A2A3Fc;").
Proof using . intros. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. reflexivity. Qed.

Lemma signed_neg_iff : ltac2:(tb__ "0|1|
S16Q40M0A1S12S30S18G0R1A2Z0A2S2cS2dZ2Z3fA2S15G0R1A2A2A2Fv;").
Proof using .
  intros v. pose proof (urange v). unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). rewrite two64.
  split; intros H1.
  - destruct (Z_lt_ge_dec (bv_unsigned v) (2 ^ 63)); [|lia].
    rewrite Z.mod_small in H1 by lia. lia.
  - replace (bv_unsigned v + 2 ^ 63) with ((bv_unsigned v - 2 ^ 63) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma signed_small : ltac2:(tb__ "0|1|
S16Q40M0A1S30S15G0R1A2S2dZ2Z3fA2A2SfS0S18G0R2A2S15G0R2A2A3F_;Fv;").
Proof using .
  intros v H. pose proof (urange v). unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). rewrite two64. rewrite Z.mod_small by lia. lia.
Qed.

Lemma signed_lit0 : bv_signed (Z_to_bv 64 0) = 0.
Proof using . reflexivity. Qed.

Ltac cls_tac Hf :=
  rewrite ?zmod64_eq; unfold MAXU, M63;
  cbn [holds eval branch_taken] in Hf; cbn [eval];
  unfold bv_ltu, bv_eqb, bv_lts in Hf;
  rewrite ?signed_lit0 in Hf;
  first
    [ apply Z.ltb_lt in Hf
    | apply Z.eqb_eq in Hf
    | apply Bool.negb_true_iff in Hf; first [apply Z.ltb_ge in Hf | apply Z.eqb_neq in Hf]
    | match type of Hf with
      | ~ (?x = true) => apply Bool.not_true_iff_false in Hf;
          first [ apply Z.ltb_ge in Hf
                | apply Z.eqb_neq in Hf
                | apply Bool.negb_false_iff in Hf; first [apply Z.ltb_lt in Hf | apply Z.eqb_eq in Hf] ]
      end
    | idtac ];
  try match goal with |- _ <= bv_unsigned ?v <= _ => pose proof (urange v) end;
  try (match type of Hf with
       | context [bv_signed ?v] => pose proof (signed_neg_iff v)
       end);
  rewrite ?lit_unsigned in *;
  try change (0 mod 2 ^ 64) with 0 in *;
  try match goal with |- context [?z mod 2 ^ 64] => pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)) end;
  try match type of Hf with context [?z mod 2 ^ 64] => pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)) end;
  lia.

Lemma sltu0_cases : ltac2:(tb__ "0|7|
S16Q40M0A1M1S14S10SfG1S83S8bS17G0Z0M2A2M3R1A3M4S17G0Z1M5A2A3S2cG5S15G0R1A2M6A2A2S10SfG1G4G3A3SfS0G6G2A3A2A2Fv;").
Proof using .
  intros v. unfold alu64, alu, bv_ltu. rewrite lit_unsigned. change (0 mod 2 ^ 64) with 0.
  pose proof (urange v). destruct (Z.ltb_spec 0 (bv_unsigned v)); [left|right]; split; try reflexivity; lia.
Qed.

Ltac sltu_tac Hf :=
  rewrite ?zmod64_eq; unfold MAXU, M63;
  cbn [holds eval branch_taken] in Hf; cbn [eval];
  match type of Hf with
  | context [alu64 ALU_SLTU (Z_to_bv 64 0) ?v] =>
      pose proof (urange v);
      destruct (sltu0_cases v) as [[EE BB]|[EE BB]]; rewrite EE in Hf;
      unfold bv_eqb in Hf; rewrite ?lit_unsigned in Hf; cbn in Hf;
      first [lia | exfalso; apply Hf; reflexivity | discriminate]
  end.

Lemma classify_fact_sound : ltac2:(tb__ "0|1|
S5S6S7R2R1A2S48OLx;S5cR2A1S3S0S0S10S2cR2S15Q40S4R6R3A2A2M0A2S2cG0R1A2A2Lhi;Llo;Lx;S13X48x2F_;Ff;Frho;").
Proof using .
  intros rho f Hf.
  destruct f as [c a b|p|a b|a b|a b| |i al]; try exact I.
  - destruct c; destruct a as [za| |oa a1 a2| | | | |]; destruct b as [zb| | | | | | |]; try exact I;
    cbn [classify_fact]; try exact I;
    repeat match goal with
      | |- context [match ?o with ALU_ADD => _ | _ => _ end] => destruct o; try exact I
      | |- context [match ?e with SLit _ => _ | _ => _ end] => destruct e; try exact I
      | |- context [match ?z with 0 => _ | _ => _ end] => destruct z; try exact I
      end.
    all: first [sltu_tac Hf | cls_tac Hf].
  - destruct p as [c a b|p|a b|a b|a b| |i al]; try exact I.
    + destruct c; destruct a as [za| |oa a1 a2| | | | |]; destruct b as [zb| | | | | | |]; try exact I;
      cbn [classify_fact]; try exact I;
      repeat match goal with
        | |- context [match ?o with ALU_ADD => _ | _ => _ end] => destruct o; try exact I
        | |- context [match ?e with SLit _ => _ | _ => _ end] => destruct e; try exact I
        | |- context [match ?z with 0 => _ | _ => _ end] => destruct z; try exact I
        end.
      all: first [sltu_tac Hf | cls_tac Hf].
    + destruct b as [zb| | | | | | |]; try exact I; cbn [classify_fact]. unfold MAXU.
      destruct zb; try exact I. cbn [holds eval] in Hf. cbn [eval].
      pose proof (urange (eval rho a)) as R.
      assert (NE : bv_unsigned (eval rho a) <> 0).
      { intros E. apply Hf. apply bv_eq. rewrite E, lit_unsigned. reflexivity. }
      lia.
  - destruct a as [za| | | | | | |]; destruct b as [zb| | | | | | |]; try exact I; cbn [classify_fact]; cls_tac Hf.
  - destruct a as [za| | | | | | |]; destruct b as [zb| | | | | | |]; try exact I; cbn [classify_fact]; cls_tac Hf.
  - destruct b as [zb| | | | | | |]; try exact I; cbn [classify_fact]. rewrite ?zmod64_eq.
    all: cbn [holds eval] in Hf; cbn [eval]; apply (f_equal bv_unsigned) in Hf; rewrite ?lit_unsigned in *; lia.
Qed.

Lemma fact_itv_sound : ltac2:(tb__ "0|0|
S5S3S6S7R3R1A2S24S63R3R2A2S15Q40S4R4R3A2A2A2F_;Ff;Fe;Frho;").
Proof using .
  intros rho e f Hf. unfold fact_itv.
  pose proof (classify_fact_sound rho f Hf) as C.
  destruct (classify_fact f) as [x lo hi|]; [|apply in_top].
  destruct (sv_eqb x e) eqn:E; [|apply in_top].
  rewrite <- (sv_eqb_sound _ _ E). unfold in_itv. cbn. exact C.
Qed.

Lemma facts_itv_sound : ltac2:(tb__ "0|0|
S5S1cS6A1S3S3cS6S7R3A1R2A3S24S65R3R2A2S15Q40S4R4R2A2A2A2F_;Fe;Ffacts;Frho;").
Proof using .
  intros rho facts e H. induction facts as [|f rest IH]; cbn [facts_itv]; [apply in_top|].
  inversion H; subst. apply in_meet; [apply fact_itv_sound; assumption | apply IH; assumption].
Qed.

Lemma land_le_l : ltac2:(tb__ "0|1|
S0S0S2cZ0R2A2M0G0S2cS31R4R3A2R4A2F_;F_;Fb;Fa;").
Proof using .
  intros a b Ha Hb.
  pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as E. rewrite Z.lor_ldiff_and in E.
  assert (Z0 : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  pose proof (Z.ldiff_nonneg a b). lia.
Qed.
Lemma land_le_r : ltac2:(tb__ "0|1|
S0S0S2cZ0R2A2M0G0S2cS31R4R3A2R3A2F_;F_;Fb;Fa;").
Proof using . intros. rewrite Z.land_comm. apply land_le_l; assumption. Qed.

Lemma add_lit_val : ltac2:(tb__ "0|1|
S16Q40M0A1S0SfS0S15G0S83S88R2S17G0R1A2A3A2S2eS2fS15G0R2A2S7cR1A1A2S2dZ2Z40A2A2A3Fc;Fx;").
Proof using .
  intros x c. unfold alu64, alu. rewrite bv_add_unsigned, lit_unsigned. unfold bv_wrap. rewrite two64.
  rewrite <- (snorm_mod c). apply Zplus_mod_idemp_r.
Qed.

Lemma ne_pair_sound : ltac2:(tb__ "0|1|
S5S6S3S0S7R4R3A2SfS1eS1bS3S0A2M0A1S73R4A1S1dG0S20S3S0R3R2A4A2A3S11SfS16Q40A1S4R6R4A2S4R6S9R3A1A2A3A1F_;F_;Fc;Fa;Ff;Frho;").
Proof using .
  intros rho f a c Hf H. unfold ne_pair in H.
  destruct f as [cnd x y|p|x y|x y|x y| |i al]; try discriminate.
  - destruct cnd; try discriminate.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf.
    destruct x as [zx| | | | | | |]; destruct y as [zy| | | | | | |]; cbn in H; try discriminate;
      injection H as <- <-; intros X; apply Hf; rewrite X; reflexivity.
  - destruct p as [cnd x y|p|x y|x y|x y| |i al]; try discriminate.
    + destruct cnd; try discriminate.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf.
      destruct x as [zx| | | | | | |]; destruct y as [zy| | | | | | |]; cbn in H; try discriminate;
        injection H as <- <-; intros X; apply Hf; rewrite X; apply Z.eqb_refl.
    + cbn [holds] in Hf.
      destruct x as [zx| | | | | | |]; destruct y as [zy| | | | | | |]; cbn in H; try discriminate;
        injection H as <- <-; intros X; apply Hf; rewrite X; reflexivity.
Qed.

Lemma ne_lit_sound : ltac2:(tb__ "0|0|
S5S3S6S0S7R4R2A2SfS1eS0A1S72R4R3A2S1dS0R2A2A3S11SfS0S15Q40S4R6R5A2A2R3A3A1F_;F_;Fc;Ff;Fe;Frho;").
Proof using .
  intros rho e f c Hf H. unfold ne_lit in H.
  destruct (ne_pair f) as [[a z]|] eqn:E; [|discriminate].
  destruct (sv_eqb a e) eqn:Q; [|discriminate]. injection H as <-.
  pose proof (ne_pair_sound rho f a z Hf E) as NE. rewrite (sv_eqb_sound _ _ Q) in NE.
  intros X. apply NE. apply bv_eq. cbn [eval]. rewrite lit_unsigned. rewrite zmod64_eq in X. exact X.
Qed.

Lemma ne_refine_sound : ltac2:(tb__ "0|1|
S5S1cS6A1S3S1bS0S0A2S3cS6S7R4A1R3A3S24R2S15Q40M0S4R5R3A2A2A2S24S74R5R4R3A3S15G0S4R6R4A2A2A2F_;F_;Fp;Fe;Ffacts;Frho;").
Proof using .
  intros rho facts e p Hf. revert p. induction facts as [|f rest IH]; intros p Hp; cbn [ne_refine]; [exact Hp|].
  inversion Hf as [|f' rest' Hf1 Hrest]; subst. apply (IH Hrest).
  destruct (ne_lit e f) as [c|] eqn:E; [|exact Hp].
  pose proof (ne_lit_sound rho e f c Hf1 E) as NE. unfold in_itv in *.
  destruct (Z.eqb_spec c (fst p)); [cbn [fst snd]; lia|].
  destruct (Z.eqb_spec c (snd p)); [cbn [fst snd]; lia|]. exact Hp.
Qed.

Lemma round_up_le : ltac2:(tb__ "0|1|
S0S0S0S30Z0M0R1A2S2cR4R3A2SfS0S2eR4R3A2G0A3S2cS2fR6S2eS3bR6A1R4A2A2R5A2F_;F_;F_;Fm;Fv;Fl;").
Proof using .
  intros l v m Hm Hlv Hv.
  assert (E : (v - l) mod m = (- l) mod m).
  { replace (v - l) with (- l + v) by lia. rewrite <- Zplus_mod_idemp_r, Hv, Z.add_0_r. reflexivity. }
  pose proof (Z.mod_le (v - l) m ltac:(lia) Hm). lia.
Qed.

Lemma round_down_ge : ltac2:(tb__ "0|1|
S0S0S0S30Z0M0R1A2S2cR3R4A2SfS0S2eR4R3A2G0A3S2cR5S32R6S2eR6R4A2A2A2F_;F_;F_;Fm;Fv;Fh;").
Proof using .
  intros h v m Hm Hvh Hv.
  assert (E : (h - v) mod m = h mod m).
  { rewrite Zminus_mod, Hv, Z.sub_0_r, Z.mod_mod by lia. reflexivity. }
  pose proof (Z.mod_le (h - v) m ltac:(lia) Hm). lia.
Qed.

Lemma align_round_sound : ltac2:(tb__ "0|1|
S5S1cS6A1S3S1bS0S0A2S3cS6S7R4A1R3A3S24R2S15Q40M0S4R5R3A2A2A2S24S51R5R4R3A3S15G0S4R6R4A2A2A2F_;F_;Fp;Fe;Ffacts;Frho;").
Proof using .
  intros rho facts e p Hf Hp. unfold align_round. destruct e as [|j| | | | | |]; try exact Hp.
  destruct ((0 <? align_of facts j) && (align_of facts j <=? 64))%bool eqn:E; [|exact Hp].
  apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.leb_le in E2.
  pose proof (align_of_sound rho facts j Hf) as [_ HA]. cbn [eval] in *.
  assert (P : 0 < 2 ^ align_of facts j) by (apply Z.pow_pos_nonneg; lia).
  unfold in_itv in *. cbn [fst snd]. destruct Hp as [H1 H2].
  split; [apply round_up_le; assumption | apply round_down_ge; assumption].
Qed.

Lemma and_lo_sound : ltac2:(tb__ "0|1|
S0S0S0S10S2cZ0R2A2S30R2S2dZ2Z40A2M0A2A2S2cR4R3A2S2cS53R5R3A2S31R4S2eR3G0A2A2A2F_;F_;Fm;Fx;Fl;").
Proof using .
  intros l x m Hx Hlx. unfold and_lo.
  destruct (high_mask_j m) as [j|] eqn:E.
  - destruct (high_mask_j_sound m j E) as [Hj Hm]. rewrite Hm.
    assert (Hj64 : j <= 64).
    { destruct (Z.le_gt_cases j 64) as [|Hgt]; [assumption|]. exfalso.
      pose proof (Z.mod_pos_bound m (2 ^ 64) ltac:(lia)).
      assert (2 ^ 64 < 2 ^ j) by (apply Z.pow_lt_mono_r; lia). lia. }
    rewrite land_high_mask by lia.
    assert (P : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    rewrite (Z.mod_eq l (2 ^ j)) by lia. rewrite (Z.mod_eq x (2 ^ j)) by lia.
    pose proof (Z.div_le_mono l x (2 ^ j) P Hlx). nia.
  - apply Z.land_nonneg. lia.
Qed.

Lemma land_pow2_testbit : ltac2:(tb__ "0|2|
S0S0S2cZ0M0R2A2M1G1S12S11SfS0S31R4S2dZ2R3A2A2G0A3A1SfS19S36R4R3A2S1aA3A2F_;F_;Fj;Fv;").
Proof using .
  intros v j Hv Hj. split.
  - intros H. destruct (Z.testbit v j) eqn:E; [reflexivity|]. exfalso. apply H.
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec j n); [subst; rewrite E; reflexivity | apply Bool.andb_false_r].
  - intros H E. pose proof (f_equal (fun x => Z.testbit x j) E) as X. cbn beta in X.
    rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb, H, Z.eqb_refl in X by lia. discriminate.
Qed.

Lemma mod_pow2_succ : ltac2:(tb__ "0|3|
S0S0S2cZ0R2A2M0G0SfS0S2eR4S2dZ2M1S2fR3Z1A2A2A2S2fS3aS2dG1R3A2M2S2eS37R4G2A2G1A2A2S2eR4G2A2A2A3F_;F_;Fj;Fv;").
Proof using .
  intros v j Hv Hj.
  assert (P : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r, Z.pow_1_r by lia.
  rewrite Z.rem_mul_r by lia. lia.
Qed.

Lemma testbit_mod : ltac2:(tb__ "0|2|
S0S0S2cZ0R2A2M0G0S12SfS19S36R4R3A2S1aA3S2cS2dZ2M1R3A2S2eR4S2dG1S2fR3Z1A2A2A2A2A2F_;F_;Fj;Fv;").
Proof using .
  intros v j Hv Hj. rewrite Z.testbit_true by lia. rewrite mod_pow2_succ by lia.
  assert (P : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound (v / 2 ^ j) 2 ltac:(lia)) as A. pose proof (Z.mod_pos_bound v (2 ^ j) P) as B.
  set (q := (v / 2 ^ j) mod 2) in *. set (r := v mod 2 ^ j) in *. set (H := 2 ^ j) in *. clearbody q r H.
  assert (q = 0 \/ q = 1) as [-> | ->] by lia; lia.
Qed.

Lemma pow2_j_sound : ltac2:(tb__ "0|1|
S0S0SfS1eS0A1S76R2A1S1dS0R1A2A3S10S2cZ0R2A2SfS0S2eR3S2dZ2M0Z40A2A2S2dG0R2A2A3A2F_;Fj;Fm;").
Proof using .
  intros m j H. unfold pow2_j in H. rewrite zmod64_eq in H.
  destruct (0 <? m mod 2 ^ 64) eqn:E1; [|discriminate].
  destruct (m mod 2 ^ 64 =? 2 ^ Z.log2 (m mod 2 ^ 64)) eqn:E2; [|discriminate].
  injection H as <-. apply Z.ltb_lt in E1. apply Z.eqb_eq in E2.
  split; [apply Z.log2_nonneg | exact E2].
Qed.

Lemma and_lit_sound : ltac2:(tb__ "0|1|
S3S3S0SfS1eS1bS3S0A2M0A1S52R3A1S1dG0S20S3S0R2R1A4A2A3SfS3R4SaS8aR3S9R2A1A3A3F_;Fm;Fa;Fe;").
Proof using .
  intros e a m H. unfold and_lit in H. destruct e as [| |op e1 e2| | | | |]; try discriminate.
  destruct op; try discriminate. destruct e2; try discriminate. injection H as <- <-. reflexivity.
Qed.

Lemma is_lit0_sound : ltac2:(tb__ "0|0|
S5S3SfS19S49R1A1S1aA3SfS0S15Q40S4R3R2A2A2Z0A3F_;Fe;Frho;").
Proof using .
  intros rho e H. unfold is_lit0 in H. destruct e; try discriminate. apply Z.eqb_eq in H.
  cbn [eval]. rewrite lit_unsigned. rewrite zmod64_eq in H. exact H.
Qed.

Lemma bit_test_some : ltac2:(tb__ "0|2|
S19S3S3S3S0S19SfS1eS1bS1bS3S0A2M0S19A2M1A1S58R6R5R4A3S1dG1S20G0S19S20S3S0R3R2A4R1A4A2A3S10SfS19S49R5A1S1aA3S10SfS3R6SaS8aR4S9R3A1A3A3SfS19R2R7A3A2A2F_;Fb;Fm;Fa;Fy;Fx;Fpos;").
Proof using .
  intros pos x y a m b H. unfold bit_test in H. destruct (is_lit0 y) eqn:Hy; [|discriminate].
  destruct (and_lit x) as [[a' m']|] eqn:Hx; [|discriminate]. injection H as <- <- <-.
  split; [reflexivity|]. split; [apply and_lit_sound; exact Hx | reflexivity].
Qed.

Lemma bit_pair_sound : ltac2:(tb__ "0|3|
S5S6S3S0S19S7R5R4A2SfS1eS1bS1bS3S0A2M0S19A2M1A1S54R5A1S1dG1S20G0S19S20S3S0R4R3A4R2A4A2A3S19OLb;R3S11SfS0S31S15Q40S4R7R5A2A2S2eR4S2dZ2Z40A2A2A2Z0A3M2A1G2X19x2F_;F_;Fb;Fm;Fa;Ff;Frho;").
Proof using .
  intros rho f a m b Hf H.
  assert (V : bv_unsigned (eval rho (SAlu ALU_AND a (SLit m))) = Z.land (bv_unsigned (eval rho a)) (m mod 2 ^ 64)).
  { cbn [eval]. rewrite and_val, lit_unsigned. reflexivity. }
  rewrite <- V. unfold bit_pair in H.
  destruct f as [c x y|p|x y|x y|x y| |i al]; try discriminate.
  - destruct c; try discriminate; destruct (bit_test_some _ _ _ _ _ _ H) as (Hy & -> & ->);
      cbn [holds branch_taken] in Hf; unfold bv_eqb in Hf; rewrite (is_lit0_sound rho y Hy) in Hf.
    + apply Z.eqb_eq in Hf. exact Hf.
    + apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf. exact Hf.
  - destruct p as [c x y|p|x y|x y|x y| |i al]; try discriminate.
    + destruct c; try discriminate; destruct (bit_test_some _ _ _ _ _ _ H) as (Hy & -> & ->);
        cbn [holds branch_taken] in Hf; unfold bv_eqb in Hf; rewrite (is_lit0_sound rho y Hy) in Hf.
      * intros E. apply Hf. rewrite E. reflexivity.
      * destruct (Z.eqb_spec (bv_unsigned (eval rho (SAlu ALU_AND a (SLit m)))) 0) as [E|E]; [exact E | exfalso; apply Hf; reflexivity].
    + destruct (bit_test_some _ _ _ _ _ _ H) as (Hy & -> & ->). cbn [holds] in Hf.
      intros E. apply Hf. apply bv_eq. rewrite E. symmetry. exact (is_lit0_sound rho y Hy).
  - destruct (bit_test_some _ _ _ _ _ _ H) as (Hy & -> & ->). cbn [holds] in Hf.
    rewrite Hf. exact (is_lit0_sound rho y Hy).
Qed.

Lemma bit_refine1_sound : ltac2:(tb__ "0|3|
S0S19S1bS0S0A2S0S2cZ0R4A2S24R3R2A2S19OLb;R5S2cS2dZ2M0R6A2M1S2eR3S2dG0S2fR6Z1A2A2A2M2A2S30G2G1A2X19x2S24S56R7R6R5A3R4A2F_;F_;F_;Fv;Fp;Fb;Fj;").
Proof using .
  intros j b [l h] v Hj [Hl Hh] Hb. unfold bit_refine1, in_itv. cbn [fst snd] in *.
  assert (HP : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r, Z.pow_1_r in * by lia.
  set (H := 2 ^ j) in *. set (P := H * 2) in *.
  pose proof (Z.div_mod v P ltac:(lia)) as Dv. pose proof (Z.mod_pos_bound v P ltac:(lia)) as Mv.
  pose proof (Z.div_mod l P ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound l P ltac:(lia)) as Ml.
  pose proof (Z.div_mod h P ltac:(lia)) as Dh. pose proof (Z.mod_pos_bound h P ltac:(lia)) as Mh.
  set (cv := v / P) in *. set (rv := v mod P) in *.
  set (cl := l / P) in *. set (rl := l mod P) in *.
  set (ch := h / P) in *. set (rh := h mod P) in *.
  clearbody cv rv cl rl ch rh H P.
  assert (Mono : forall a b, a <= b -> P * a <= P * b) by (intros; apply Z.mul_le_mono_nonneg_l; lia).
  destruct b; cbn [fst snd].
  - split.
    + destruct (Z.ltb_spec rl H); [|lia].
      destruct (Z.lt_trichotomy cv cl) as [C|[C|C]].
      * pose proof (Mono (cv + 1) cl ltac:(lia)). lia.
      * subst cv. lia.
      * pose proof (Mono (cl + 1) cv ltac:(lia)). lia.
    + destruct (Z.ltb_spec rh H); [|lia].
      destruct (Z.lt_trichotomy cv ch) as [C|[C|C]].
      * pose proof (Mono (cv + 1) ch ltac:(lia)). lia.
      * subst cv. lia.
      * pose proof (Mono (ch + 1) cv ltac:(lia)). lia.
  - split.
    + destruct (Z.ltb_spec rl H); [lia|].
      destruct (Z.lt_trichotomy cv cl) as [C|[C|C]].
      * pose proof (Mono (cv + 1) cl ltac:(lia)). lia.
      * subst cv. lia.
      * pose proof (Mono (cl + 1) cv ltac:(lia)). lia.
    + destruct (Z.ltb_spec rh H); [lia|].
      destruct (Z.lt_trichotomy cv ch) as [C|[C|C]].
      * pose proof (Mono (cv + 1) ch ltac:(lia)). lia.
      * subst cv. lia.
      * pose proof (Mono (ch + 1) cv ltac:(lia)). lia.
Qed.

Lemma bit_refine_sound : ltac2:(tb__ "0|1|
S5S1cS6A1S3S1bS0S0A2S3cS6S7R4A1R3A3S24R2S15Q40M0S4R5R3A2A2A2S24S55R5R4R3A3S15G0S4R6R4A2A2A2F_;F_;Fp;Fe;Ffacts;Frho;").
Proof using .
  intros rho facts e p Hf. revert p. induction facts as [|f rest IH]; intros p Hp; cbn [bit_refine]; [exact Hp|].
  inversion Hf as [|f' rest' Hf1 Hrest]; subst. apply (IH Hrest).
  destruct (bit_pair f) as [[[a m] b]|] eqn:E; [|exact Hp].
  destruct (sv_eqb a e) eqn:Q; [|exact Hp].
  destruct (pow2_j m) as [j|] eqn:Ej; [|exact Hp].
  destruct (pow2_j_sound m j Ej) as [Hj Hm].
  pose proof (bit_pair_sound rho f a m b Hf1 E) as B. rewrite (sv_eqb_sound _ _ Q), Hm in B.
  pose proof (urange (eval rho e)) as R.
  apply bit_refine1_sound; [exact Hj | exact Hp |].
  set (u := bv_unsigned (eval rho e)) in *. assert (Hu : 0 <= u) by lia.
  destruct b.
  - apply (proj1 (testbit_mod u j Hu Hj)). apply (proj1 (land_pow2_testbit u j Hu Hj)). exact B.
  - destruct (Z.le_gt_cases (2 ^ j) (u mod 2 ^ (j + 1))) as [Hge|Hlt]; [|lia].
    exfalso. apply (proj2 (testbit_mod u j Hu Hj)) in Hge.
    apply (proj2 (land_pow2_testbit u j Hu Hj)) in Hge. exact (Hge B).
Qed.

Lemma bit_refine_iter_sound : ltac2:(tb__ "0|1|
S5S22S1cS6A1S3S1bS0S0A2S3cS6S7R5A1R3A3S24R2S15Q40M0S4R6R3A2A2A2S24S57R6R5R4R3A4S15G0S4R7R4A2A2A2F_;F_;Fp;Fe;Ffacts;Ffuel;Frho;").
Proof using .
  intros rho fuel facts e. induction fuel as [|fuel IH]; intros p Hf Hp; cbn [bit_refine_iter]; [exact Hp|].
  destruct ((fst (bit_refine facts e p) =? fst p) && (snd (bit_refine facts e p) =? snd p))%bool; [exact Hp|].
  apply IH; [exact Hf|]. apply bit_refine_sound; assumption.
Qed.

Lemma lxor_ones64 : ltac2:(tb__ "0|2|
S0S10S2cZ0R1A2S30R1S2dZ2Z40A2M0A2A2SfS0S34R2S32G0Z1A2M1A2S32G1R2A2A3F_;Fu;").
Proof using .
  intros u Hu.
  replace (2 ^ 64 - 1 - u) with ((Z.lnot u) mod 2 ^ 64).
  2:{ unfold Z.lnot. replace (Z.pred (- u)) with ((2 ^ 64 - 1 - u) + (-1) * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec.
  change (2 ^ 64 - 1) with (Z.ones 64).
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
    apply Bool.xorb_true_r.
  - rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia.
    destruct (Z.eq_dec u 0) as [->|Hnz]; [rewrite Z.bits_0; reflexivity|].
    rewrite (Z.bits_above_log2 u i); [reflexivity | lia |].
    assert (Z.log2 u < 64) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma lor_bounds : ltac2:(tb__ "0|2|
S0S0S2cZ0R2A2M0G0S10S2cS39R4R3A2S33R4R3A2M1A2S2cG1S2fR4R3A2A2A2F_;F_;Fb;Fa;").
Proof using .
  intros a b Ha Hb.
  pose proof (Z.lor_nonneg a b).
  assert (E : Z.lor a b + Z.land a b = a + b).
  { pose proof (Z.add_lor_land a b). lia. }
  pose proof (Z.land_nonneg a b).
  assert (a <= Z.lor a b).
  {
    pose proof (Z.add_lor_land a (Z.ldiff b a)) as X.
    assert (Z.land a (Z.ldiff b a) = 0).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0. destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
    assert (Z.lor a (Z.ldiff b a) = Z.lor a b).
    { apply Z.bits_inj'. intros n Hn. rewrite !Z.lor_spec, Z.ldiff_spec. destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
    pose proof (Z.ldiff_nonneg b a). lia. }
  assert (b <= Z.lor a b).
  { pose proof (Z.add_lor_land b (Z.ldiff a b)) as X.
    assert (Z.land b (Z.ldiff a b) = 0).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0. destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
    assert (Z.lor b (Z.ldiff a b) = Z.lor a b).
    { apply Z.bits_inj'. intros n Hn. rewrite !Z.lor_spec, Z.ldiff_spec. destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
    pose proof (Z.ldiff_nonneg a b). lia. }
  lia.
Qed.

Lemma xor_val : ltac2:(tb__ "0|2|
S16Q40M0A1M1G1SfS0S15G0S83S8dR2R1A3A2S34S15G0R2A2S15G0R1A2A2A3Fy;Fx;").
Proof using . intros. unfold alu64, alu. rewrite bv_xor_unsigned. reflexivity. Qed.
Lemma or_val : ltac2:(tb__ "0|2|
S16Q40M0A1M1G1SfS0S15G0S83S8cR2R1A3A2S33S15G0R2A2S15G0R1A2A2A3Fy;Fx;").
Proof using . intros. unfold alu64, alu. rewrite bv_or_unsigned. reflexivity. Qed.

Lemma shift_itv_sound : ltac2:(tb__ "0|2|
S5S3S0S1bS0S0A2M0G0S24R2S15Q40M1S4R5R4A2A2A2S24R2S15G1S4R6SaS88R5S9R4A1A3A2A2A2S24S77R5R4R3A3S15G1S4R7R6A2A2A2F_;F_;Fp;Fpe;Fc;Fe;Frho;").
Proof using .
  intros rho e c [le he] [lo hi] He H. unfold shift_itv. cbn [fst snd].
  unfold in_itv in H, He. cbn [fst snd eval] in H, He. rewrite add_lit_val in H.
  pose proof (urange (eval rho e)) as R. pose proof (snorm_range c) as Rc.
  set (u := bv_unsigned (eval rho e)) in *. set (c' := snorm c) in *.
  destruct (Z.leb_spec lo hi); cbn [negb]; [|apply in_top].
  destruct ((c' <? 0) && ((hi - c' <? 2 ^ 64) || (0 <=? le + c')))%bool eqn:E1.
  - apply andb_prop in E1 as [A B]. apply Z.ltb_lt in A.
    assert (B' : hi - c' < 2 ^ 64 \/ 0 <= le + c').
    { apply orb_prop in B as [B|B]; [left; apply Z.ltb_lt in B | right; apply Z.leb_le in B]; exact B. }
    unfold in_itv; cbn [fst snd].
    destruct (Z.le_gt_cases 0 (u + c')).
    + rewrite Z.mod_small in H by lia. lia.
    + replace (u + c') with ((u + c' + 2 ^ 64) + (-1) * 2 ^ 64) in H by lia.
      rewrite Z.mod_add in H by lia. rewrite Z.mod_small in H by lia. lia.
  - destruct ((0 <? c') && ((c' <=? lo) || (he + c' <? 2 ^ 64)))%bool eqn:E2; [|apply in_top].
    apply andb_prop in E2 as [A B]. apply Z.ltb_lt in A.
    assert (B' : c' <= lo \/ he + c' < 2 ^ 64).
    { apply orb_prop in B as [B|B]; [left; apply Z.leb_le in B | right; apply Z.ltb_lt in B]; exact B. }
    unfold in_itv; cbn [fst snd].
    destruct (Z.lt_ge_cases (u + c') (2 ^ 64)).
    + rewrite Z.mod_small in H by lia. lia.
    + replace (u + c') with ((u + c' - 2 ^ 64) + 1 * 2 ^ 64) in H by lia.
      rewrite Z.mod_add in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.

Lemma shifted_of_sound : ltac2:(tb__ "0|1|
S3S6S3S0SfS1eS1bS3S0A2M0A1S79R4R3A2S1dG0S20S3S0R2R1A4A2A3SfS3R3SaS88R5S9R2A1A3A3F_;Fc;Fx;Ff;Fe;").
Proof using .
  intros e f x c H. unfold shifted_of in H.
  destruct (classify_fact f) as [x0 lo hi|]; [|discriminate].
  destruct x0 as [| |op a b| | | | |]; try discriminate. destruct op; try discriminate.
  destruct b; try discriminate. destruct (sv_eqb a e) eqn:Q; [|discriminate].
  injection H as <- <-. rewrite (sv_eqb_sound _ _ Q). reflexivity.
Qed.

Lemma shift_refine_sound : ltac2:(tb__ "0|2|
S5S1cS6A1M0G0S3S1bS0S0A2S3cS6S7R5A1R4A3S24R2S15Q40M1S4R6R3A2A2A2S24S78R6R5R4R3A4S15G1S4R7R4A2A2A2F_;F_;Fp;Fe;Ffacts;Fall;Frho;").
Proof using .
  intros rho all facts e. induction facts as [|f rest IH]; intros p Hall Hp; cbn [shift_refine]; [exact Hp|].
  apply IH; [exact Hall|].
  destruct (shifted_of e f) as [[x c]|] eqn:E; [|exact Hp].
  rewrite (shifted_of_sound e f x c E).
  apply in_meet; [exact Hp|]. apply shift_itv_sound; [exact Hp|]. apply facts_itv_sound. exact Hall.
Qed.

Lemma low32_small : ltac2:(tb__ "0|1|
S16Q40M0A1S30S15G0R1A2S2dZ2Z20A2A2SfS0S15Q20S84R2A1A2S15G0R2A2A3F_;Fv;").
Proof using .
  intros v H. pose proof (urange v). unfold low32. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0.
  rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). apply Z.mod_small. lia.
Qed.

Lemma sext64_32_small : ltac2:(tb__ "0|2|
S16Q20M0A1S30S15G0R1A2S2dZ2Z1fA2A2SfS0S15Q40M1S8fG0G1R2A3A2S15G0R2A2A3F_;Fv;").
Proof using .
  intros v H. pose proof (bv_unsigned_in_range _ v) as R. change (bv_modulus 32) with (2 ^ 32) in R.
  unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). rewrite two64.
  rewrite (Z.mod_small (bv_unsigned v + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma low32_umod : ltac2:(tb__ "0|1|
S16Q40M0A1SfS0S15Q20S84R1A1A2S2eS15G0R1A2S2dZ2Z20A2A2A3Fw;").
Proof using .
  intros w. unfold low32. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Definition cls_ok (rho : valuation) (cf : cfact) : Prop := ltac2:(tb__ "0|3|
S10S2cS1fS0S0S21S3S1bS0S0A2M0Vcf;A3M1A3S15Q40S4Vrho;S1fS3G0Vcf;A3A2A2M2A2S2cG2S21S0S0G1A3A2A2").
Definition nes_ok (rho : valuation) (nf : nfact) : Prop := ltac2:(tb__ "0|0|
S11SfS0S15Q40S4Vrho;S1fS3S0Vnf;A3A2A2S21S3S0Vnf;A3A3A1").
Definition bits_ok (rho : valuation) (bf : bfact) : Prop := ltac2:(tb__ "0|4|
S1bS1bS3S0A2M0S19A2OLbf;Vbf;G0S19G0OLp;R2S3S0S10S2cZ0R1A2S19OLb;R3S2cS2dZ2M1R1A2M2S2eS15Q40S4Vrho;R2A2A2S2dG1S2fR1Z1A2A2A2M3A2S30G3G2A2X19x2A2Lj;La;X1bx1Lb;Lp;X1bx1").

Lemma mk_cls_sound : ltac2:(tb__ "0|0|
S5S1cS6A1S3cS6S7R2A1R1A3S3cS3fS29R3A1S6eR2A1A3F_;Ffacts;Frho;").
Proof using .
  intros rho facts Hf. induction facts as [|f rest IH]; cbn [mk_cls]; [constructor|].
  inversion Hf as [|f' r Hf1 Hrest]; subst. pose proof (classify_fact_sound rho f Hf1) as C.
  destruct (classify_fact f) as [x lo hi|]; [|apply IH; assumption].
  constructor; [exact C | apply IH; assumption].
Qed.

Lemma cls_itv_sound : ltac2:(tb__ "0|0|
S5S1cS3fA1S3S3cS3fS29R3A1R2A3S24S5dR3R2A2S15Q40S4R4R2A2A2A2F_;Fe;Fcls;Frho;").
Proof using .
  intros rho cls e H. induction cls as [|[x p] rest IH]; cbn [cls_itv]; [apply in_top|].
  inversion H as [|y r Hy Hrest]; subst. destruct (sv_eqb x e) eqn:E; [|apply IH; assumption].
  apply in_meet; [|apply IH; assumption]. rewrite <- (sv_eqb_sound _ _ E). unfold cls_ok in Hy. exact Hy.
Qed.

Lemma cls_shift_sound : ltac2:(tb__ "0|2|
S5S1cS3fA1M0G0S3S1bS0S0A2S3cS3fS29R5A1R4A3S24R2S15Q40M1S4R6R3A2A2A2S24S5eR6R5R4R3A4S15G1S4R7R4A2A2A2F_;F_;Fp;Fe;Fcls;Fall;Frho;").
Proof using .
  intros rho all cls e. induction cls as [|[x px] rest IH]; intros p Hall Hp; cbn [cls_shift]; [exact Hp|].
  destruct x as [| |op a b| | | | |]; try (apply IH; assumption).
  destruct op; try (apply IH; assumption). destruct b as [c| | | | | | |]; try (apply IH; assumption).
  apply IH; [exact Hall|]. destruct (sv_eqb a e) eqn:E; [|exact Hp].
  apply in_meet; [exact Hp|]. apply shift_itv_sound; [exact Hp|]. rewrite <- (sv_eqb_sound _ _ E).
  apply cls_itv_sound. exact Hall.
Qed.

Lemma mk_nes_sound : ltac2:(tb__ "0|0|
S5S1cS6A1S3cS6S7R2A1R1A3S3cS41S2aR3A1S71R2A1A3F_;Ffacts;Frho;").
Proof using .
  intros rho facts Hf. induction facts as [|f rest IH]; cbn [mk_nes]; [constructor|].
  inversion Hf as [|f' r Hf1 Hrest]; subst.
  destruct (ne_pair f) as [[a c]|] eqn:E; [|apply IH; assumption].
  constructor; [|apply IH; assumption]. unfold nes_ok. cbn [fst snd].
  pose proof (ne_pair_sound rho f a c Hf1 E) as NE. rewrite zmod64_eq.
  intros X. apply NE. apply bv_eq. cbn [eval]. rewrite lit_unsigned. exact X.
Qed.

Lemma nes_refine_sound : ltac2:(tb__ "0|1|
S5S1cS41A1S3S1bS0S0A2S3cS41S2aR4A1R3A3S24R2S15Q40M0S4R5R3A2A2A2S24S75R5R4R3A3S15G0S4R6R4A2A2A2F_;F_;Fp;Fe;Fnes;Frho;").
Proof using .
  intros rho nes e. induction nes as [|[a c] rest IH]; intros p Hn Hp; cbn [nes_refine]; [exact Hp|].
  inversion Hn as [|y r Hy Hrest]; subst. apply (IH _ Hrest).
  destruct (sv_eqb a e) eqn:E; [|exact Hp]. unfold nes_ok in Hy. cbn [fst snd] in Hy. rewrite (sv_eqb_sound _ _ E) in Hy.
  unfold in_itv in *.
  destruct (Z.eqb_spec c (fst p)); [cbn [fst snd]; lia|].
  destruct (Z.eqb_spec c (snd p)); [cbn [fst snd]; lia|]. exact Hp.
Qed.

Lemma mk_bits_sound : ltac2:(tb__ "0|0|
S5S1cS6A1S3cS6S7R2A1R1A3S3cS3eS28R3A1S6dR2A1A3F_;Ffacts;Frho;").
Proof using .
  intros rho facts Hf. induction facts as [|f rest IH]; cbn [mk_bits]; [constructor|].
  inversion Hf as [|f' r Hf1 Hrest]; subst.
  destruct (bit_pair f) as [[[a m] b]|] eqn:E; [|apply IH; assumption].
  destruct (pow2_j m) as [j|] eqn:Ej; [|apply IH; assumption].
  constructor; [|apply IH; assumption].
  destruct (pow2_j_sound m j Ej) as [Hj Hm].
  pose proof (bit_pair_sound rho f a m b Hf1 E) as B. rewrite Hm in B. unfold bits_ok.
  pose proof (urange (eval rho a)) as R. set (u := bv_unsigned (eval rho a)) in *.
  assert (Hu : 0 <= u) by lia. split; [exact Hj|].
  destruct b.
  - apply (proj1 (testbit_mod u j Hu Hj)). apply (proj1 (land_pow2_testbit u j Hu Hj)). exact B.
  - destruct (Z.le_gt_cases (2 ^ j) (u mod 2 ^ (j + 1))) as [Hge|Hlt]; [|lia].
    exfalso. apply (proj2 (testbit_mod u j Hu Hj)) in Hge.
    apply (proj2 (land_pow2_testbit u j Hu Hj)) in Hge. exact (Hge B).
Qed.

Lemma bits_refine_sound : ltac2:(tb__ "0|1|
S5S1cS3eA1S3S1bS0S0A2S3cS3eS28R4A1R3A3S24R2S15Q40M0S4R5R3A2A2A2S24S59R5R4R3A3S15G0S4R6R4A2A2A2F_;F_;Fp;Fe;Fbits;Frho;").
Proof using .
  intros rho bits e. induction bits as [|[[a j] b] rest IH]; intros p Hb Hp; cbn [bits_refine]; [exact Hp|].
  inversion Hb as [|y r Hy Hrest]; subst. apply (IH _ Hrest).
  destruct (sv_eqb a e) eqn:E; [|exact Hp]. unfold bits_ok in Hy. rewrite (sv_eqb_sound _ _ E) in Hy.
  destruct Hy as [Hj Hy]. apply bit_refine1_sound; [exact Hj | exact Hp | exact Hy].
Qed.

Lemma bits_refine_iter_sound : ltac2:(tb__ "0|1|
S5S22S1cS3eA1S3S1bS0S0A2S3cS3eS28R5A1R3A3S24R2S15Q40M0S4R6R3A2A2A2S24S5aR6R5R4R3A4S15G0S4R7R4A2A2A2F_;F_;Fp;Fe;Fbits;Ffuel;Frho;").
Proof using .
  intros rho fuel bits e. induction fuel as [|fuel IH]; intros p Hb Hp; cbn [bits_refine_iter]; [exact Hp|].
  destruct ((fst (bits_refine bits e p) =? fst p) &&& (snd (bits_refine bits e p) =? snd p)); [exact Hp|].
  apply IH; [exact Hb|]. apply bits_refine_sound; assumption.
Qed.

Definition U (rho : valuation) (e : sv) : Z := bv_unsigned (eval rho e).

Definition entry_ok (rho : valuation) (en : tbl_entry) : Prop := ltac2:(tb__ "0|6|
S10S24S1fS1bS0S0A2M0G0S21S3S1bG0G0A2M1Ven;A3M2A3S15Q40S4Vrho;S1fS3G1Ven;A3M3A2A2A2S10S2cS1fS0S0S21G0G0G2A3M4A3ScVrho;G3A2M5A2S2cG5S21S0S0G4A3A2A2A2").

Definition tbl_ok (rho : valuation) (tbl : list tbl_entry) : Prop := Forall (entry_ok rho) tbl.

Definition dgv_ok (rho : valuation) (dg : fdig) : Prop := ltac2:(tb__ "0|0|
S10S3cS6S7Vrho;A1S42Vdg;A1A3S10S3cS3fS29Vrho;A1S60Vdg;A1A3S10S3cS41S2aVrho;A1S61Vdg;A1A3S10S3cS3eS28Vrho;A1S5fVdg;A1A3S27Vrho;S47Vdg;A1A2A2A2A2A2").

Lemma dgv_facts : ltac2:(tb__ "0|0|
S5S3dS25R2R1A2S3cS6S7R3A1S42R2A1A3F_;Fdg;Frho;").
Proof using . intros rho dg H. exact (proj1 H). Qed.
Lemma dgv_tbl : ltac2:(tb__ "0|0|
S5S3dS25R2R1A2S27R3S47R2A1A2F_;Fdg;Frho;").
Proof using . intros rho dg (_ & _ & _ & _ & H). exact H. Qed.
Lemma dgv_with_tbl : ltac2:(tb__ "0|0|
S5S3dS1cS43A1S25R3R2A2S27R4R2A2S25R5S62R4R3A2A2F_;F_;Ftbl;Fdg;Frho;").
Proof using . intros rho dg tbl (A & B & C & D & E) Ht. unfold dgv_ok, dg_with_tbl. cbn. repeat split; assumption. Qed.

Lemma tbl_find_sound : ltac2:(tb__ "0|4|
S5S1cS43A1S3S1bS1bS0S0A2M0G0A2M1S27R4R3A2SfS1eG1A1S7dR4R3A2S1dG1R2A2A3S10S24S1fG0G0R3A3S15Q40S4R6R4A2A2A2S10S2cS1fS0S0S21G0G0R3A3M2A3ScR6R4A2M3A2S2cG3S21S0S0G2A3A2A2A2F_;F_;Fv;Fe;Ftbl;Frho;").
Proof using .
  intros rho tbl e v Ht. induction tbl as [|[x vx] rest IH]; cbn [tbl_find]; intros H; [discriminate|].
  inversion Ht as [|y l [H1 H2] Hrest]; subst.
  destruct (sv_eqb x e) eqn:E.
  - injection H as <-. rewrite <- (sv_eqb_sound _ _ E). cbn [fst snd] in H1, H2. split; assumption.
  - apply IH; assumption.
Qed.

Lemma tbl_shift_sound : ltac2:(tb__ "0|1|
S5S1cS43A1S3S1bS0S0A2S27R4R3A2S24R2S15Q40M0S4R5R3A2A2A2S24S7eR5R4R3A3S15G0S4R6R4A2A2A2F_;F_;Fp;Fe;Ftbl;Frho;").
Proof using .
  intros rho tbl e. induction tbl as [|[x [pu ps]] rest IH]; intros p Ht Hp; cbn [tbl_shift]; [exact Hp|].
  inversion Ht as [|y l [H1 H2] Hrest]; subst. cbn [fst snd] in H1, H2.
  destruct x as [| |op a b| | | | |]; try (apply IH; assumption).
  destruct op; try (apply IH; assumption). destruct b as [c| | | | | | |]; try (apply IH; assumption).
  apply IH; [assumption|]. destruct (sv_eqb a e) eqn:E; [|exact Hp].
  apply in_meet; [exact Hp|]. apply shift_itv_sound; [exact Hp|]. rewrite <- (sv_eqb_sound _ _ E). exact H1.
Qed.

Fixpoint sv_size (e : sv) : nat :=
  match e with
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => S (sv_size a + sv_size b)
  | SExt _ _ a => S (sv_size a)
  | SLBytes _ i _ => S (sv_size i)
  | _ => 1%nat
  end.

Lemma ext_low_small : ltac2:(tb__ "0|4|
S19S2S16Q40M0A1M1S10S30Z0S35R2A1M2A2S2cG2Z40A2A2S30S15G0R2A2S2dZ2S19S0Lsgn;R4S32S35R3A1M3Z1A2G3X19x2A2A2SfG1SbR5R4R3A3R3A3F_;F_;Fv;Fw;Fsgn;").
Proof using .
  intros sgn w v Hw Hv. pose proof (urange v) as R. apply bv_eq. unfold ext_low.
  assert (HE : bv_unsigned (bv_extract 0 w v) = bv_unsigned v).
  { rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
    apply Z.mod_small. destruct sgn; [|lia].
    split; [lia|]. eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia. }
  destruct sgn.
  - unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed, bv_swrap, bv_wrap. rewrite HE.
    unfold bv_half_modulus, bv_modulus. rewrite two64_N || idtac.
    assert (P : 2 ^ Z.of_N w = 2 * 2 ^ (Z.of_N w - 1)).
    { replace (Z.of_N w) with (Z.of_N w - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia. }
    rewrite P. replace (2 * 2 ^ (Z.of_N w - 1) / 2) with (2 ^ (Z.of_N w - 1)) by (symmetry; rewrite Z.mul_comm; apply Z.div_mul; lia).
    rewrite (Z.mod_small (bv_unsigned v + _)) by lia.
    replace (Z.of_N 64) with 64 by reflexivity.
    rewrite Z.mod_small by lia. lia.
  - unfold zext. rewrite bv_zero_extend_unsigned'. unfold bv_wrap. rewrite HE. unfold bv_modulus.
    replace (Z.of_N 64) with 64 by reflexivity. apply Z.mod_small. lia.
Qed.

Lemma itv_body_sound : ltac2:(tb__ "0|1|
S5S3dS3S1bS0S0A2Fx;S3S25R4R3A2S3S8eS2bR1A1S2bR3A1A2S24R5R2A1S15Q40M0S4R7R2A2A2A2F_;Fa;S24S66R4R5R3A3S15G0S4R6R3A2A2A2F_;F_;Fe;Frec;Fdg;Frho;").
Proof using .
  intros rho dg rec e Hd Hrec. pose proof Hd as (Hf & Hcls & Hnes & Hbits & Ht). set (facts := dg_facts dg) in *.
  unfold itv_body; apply align_round_sound; try assumption; apply bits_refine_iter_sound; try assumption;
    apply nes_refine_sound; try assumption; apply tbl_shift_sound; try assumption;
    apply cls_shift_sound; try assumption;
    apply in_meet; try apply cls_itv_sound; try assumption.
  unfold M64, MAXU in *. rewrite ?zmod64_eq, ?snormc_eq.
  destruct e; try apply in_top.
  -   cbn [eval]. rewrite zmod64_eq, lit_unsigned. unfold in_itv; cbn. lia.
  -
    pose proof (urange (eval rho e1)) as R1. pose proof (urange (eval rho e2)) as R2.
    pose proof (urange (eval rho (SAlu op e1 e2))) as R.
    pose proof (Hrec e1 ltac:(cbn; lia)) as IHe1. pose proof (Hrec e2 ltac:(cbn; lia)) as IHe2.
    destruct (rec e1) as [la ha] eqn:I1. destruct (rec e2) as [lb hb] eqn:I2.
    unfold in_itv in IHe1, IHe2. cbn [fst snd] in IHe1, IHe2.
    destruct op; try apply in_top.
    +   destruct e2 as [c| | | | | | |].
      1: { rewrite snormc_eq. pose proof (snorm_range c) as Hs.
           destruct (Z.leb_spec 0 (snorm c)).
           - destruct (Z.ltb_spec (ha + snorm c) (2 ^ 64)); [|apply in_top].
             unfold in_itv; cbn [fst snd eval]. rewrite add_lit_val. rewrite Z.mod_small by lia. lia.
           - destruct (Z.leb_spec 0 (la + snorm c)).
             + unfold in_itv; cbn [fst snd eval]. rewrite add_lit_val. rewrite Z.mod_small by lia. lia.
             + destruct ((la <=? ha) && (ha + snorm c <? 0))%bool eqn:E; [|apply in_top].
               apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
               unfold in_itv; cbn [fst snd eval]. rewrite add_lit_val.
               replace (bv_unsigned (eval rho e1) + snorm c) with ((bv_unsigned (eval rho e1) + snorm c + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
               rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
      all: destruct (Z.ltb_spec (ha + hb) (2 ^ 64)); [|apply in_top]; unfold in_itv; cbn [fst snd eval];
           cbn [eval] in IHe2, R2; rewrite add_val; rewrite Z.mod_small by lia; lia.
    +   destruct (Z.leb_spec hb la).
      { unfold in_itv; cbn [fst snd eval]. rewrite sub_val. rewrite Z.mod_small by lia. lia. }

      destruct (Z.leb_spec la ha) as [E1|E1]; [|apply in_top]. destruct (Z.leb_spec lb hb) as [E2|E2]; [|apply in_top].
      destruct (Z.ltb_spec ha lb) as [E3|E3]; [|apply in_top]. destruct (Z.ltb_spec hb (2 ^ 64)) as [E4|E4]; [|apply in_top].

      unfold in_itv; cbn [fst snd eval]. cbn [eval] in IHe2, R2. rewrite sub_val.
      replace ((bv_unsigned (eval rho e1) - bv_unsigned (eval rho e2)) mod 2 ^ 64)
        with (bv_unsigned (eval rho e1) - bv_unsigned (eval rho e2) + 2 ^ 64)
        by (apply (Z.mod_unique _ _ (-1)); lia).
      lia.
    +   destruct e2 as [k| | | | | | |]; try apply in_top.
      destruct (Z.ltb_spec (Z.shiftl ha (k mod 64)) (2 ^ 64)); [|apply in_top]. unfold in_itv; cbn [fst snd eval].
      rewrite sll_val. pose proof (Z.mod_pos_bound k 64 ltac:(lia)).
      rewrite !Z.shiftl_mul_pow2 in * by lia.
      assert (0 < 2 ^ (k mod 64)) by (apply Z.pow_pos_nonneg; lia).
      set (p := 2 ^ (k mod 64)) in *.
      assert (bv_unsigned (eval rho e1) * p <= ha * p) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (la * p <= bv_unsigned (eval rho e1) * p) by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite Z.mod_small by nia. lia.
    +
      assert (V : bv_unsigned (eval rho (SAlu ALU_SLT e1 e2)) = (if bv_signed (eval rho e1) <? bv_signed (eval rho e2) then 1 else 0)).
      { cbn [eval]. unfold alu64, alu, bv_lts. destruct (bv_signed (eval rho e1) <? bv_signed (eval rho e2)); rewrite lit_unsigned; reflexivity. }
      unfold in_itv, M63. rewrite V.
      destruct (negb ((la <=? ha) && (lb <=? hb) && (ha <? 2 ^ 63) && (hb <? 2 ^ 63))) eqn:En; [cbn [fst snd]; destruct (_ <? _); lia|].
      apply Bool.negb_false_iff in En. apply andb_prop in En as [En Eh2]. apply andb_prop in En as [En Eh1]. apply andb_prop in En as [Ea Eb].
      apply Z.leb_le in Ea. apply Z.leb_le in Eb. apply Z.ltb_lt in Eh1. apply Z.ltb_lt in Eh2.
      rewrite !signed_small by lia.
      destruct (Z.ltb_spec ha lb); [cbn [fst snd]; destruct (Z.ltb_spec (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2))); lia|].
      destruct (Z.leb_spec hb la); cbn [fst snd]; destruct (Z.ltb_spec (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2))); lia.
    +
      assert (V : bv_unsigned (eval rho (SAlu ALU_SLTU e1 e2)) = (if bv_unsigned (eval rho e1) <? bv_unsigned (eval rho e2) then 1 else 0)).
      { cbn [eval]. unfold alu64, alu, bv_ltu. destruct (bv_unsigned (eval rho e1) <? bv_unsigned (eval rho e2)); rewrite lit_unsigned; reflexivity. }
      unfold in_itv. rewrite V.
      destruct (negb ((la <=? ha) && (lb <=? hb))) eqn:En; [cbn [fst snd]; destruct (_ <? _); lia|].
      apply Bool.negb_false_iff in En. apply andb_prop in En as [Ea Eb]. apply Z.leb_le in Ea. apply Z.leb_le in Eb.
      destruct (Z.ltb_spec ha lb); [cbn [fst snd]; destruct (Z.ltb_spec (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2))); lia|].
      destruct (Z.leb_spec hb la); cbn [fst snd]; destruct (Z.ltb_spec (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2))); lia.
    +
      assert (XP : forall x y u, 0 <= x <= u -> 0 <= y <= u -> Z.lxor x y <= 2 ^ (Z.log2 (Z.max 1 u) + 1) - 1).
      { intros x y u Hx Hy.
        set (L := Z.log2 (Z.max 1 u)). pose proof (Z.log2_nonneg (Z.max 1 u)) as HL. fold L in HL.
        pose proof (Z.log2_spec (Z.max 1 u) ltac:(lia)) as [S1 S2]. fold L in S1, S2. rewrite <- Z.add_1_r in S2.
        assert (NN : 0 <= Z.lxor x y) by (apply (proj2 (Z.lxor_nonneg x y)); lia).
        destruct (Z.eq_dec (Z.lxor x y) 0) as [E|E]; [rewrite E; pose proof (Z.pow_pos_nonneg 2 (L + 1)); lia|].
        pose proof (Z.log2_lxor x y ltac:(lia) ltac:(lia)) as LL.
        assert (Lx : Z.log2 x < L + 1).
        { destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
        assert (Ly : Z.log2 y < L + 1).
        { destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
        assert (Z.lxor x y < 2 ^ (L + 1)); [|lia]. apply Z.log2_lt_pow2; lia. }
      assert (XS : forall x y, 0 <= x -> 0 <= y -> 0 <= Z.lxor x y <= x + y).
      { intros x y Hx Hy. pose proof (Z.lxor_nonneg x y). pose proof (Z.sub_lor_land x y). pose proof (Z.add_lor_land x y).
        pose proof (Z.land_nonneg x y). split; [tauto|lia]. }
      assert (GEN : in_itv (if (la <=? ha) &&& ((lb <=? hb) &&& (ha + hb <? M64)) then (0, Z.min (ha + hb) (2 ^ (Z.log2 (Z.max 1 (Z.max ha hb)) + 1) - 1)) else top_itv)
                           (bv_unsigned (eval rho (SAlu ALU_XOR e1 e2)))).
      { destruct (Z.leb_spec la ha); [|apply in_top]. destruct (Z.leb_spec lb hb); [|apply in_top].
        destruct (Z.ltb_spec (ha + hb) M64); [|apply in_top]. unfold M64 in *.
        unfold in_itv; cbn [fst snd eval]. rewrite xor_val. cbn [eval] in IHe2.
        pose proof (XS (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2)) ltac:(lia) ltac:(lia)).
        pose proof (XP (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2)) (Z.max ha hb) ltac:(lia) ltac:(lia)). lia. }
      destruct e2 as [m| | | | | | |]; try exact GEN. rewrite zmod64_eq.
      destruct (Z.eqb_spec (m mod 2 ^ 64) (2 ^ 64 - 1)) as [Em|].
      * unfold in_itv; cbn [fst snd eval]. rewrite xor_val, lit_unsigned, Em.
        rewrite lxor_ones64 by lia. lia.
      * destruct (Z.leb_spec la ha); [|apply in_top]. destruct (Z.ltb_spec (ha + m mod 2 ^ 64) (2 ^ 64)); [|apply in_top].
        unfold in_itv; cbn [fst snd eval]. rewrite xor_val, lit_unsigned.
        pose proof (Z.mod_pos_bound m (2 ^ 64) ltac:(lia)).
        pose proof (XS (bv_unsigned (eval rho e1)) (m mod 2 ^ 64) ltac:(lia) ltac:(lia)).
        pose proof (XP (bv_unsigned (eval rho e1)) (m mod 2 ^ 64) (Z.max ha (m mod 2 ^ 64)) ltac:(lia) ltac:(lia)). lia.
    +   destruct e2 as [k| | | | | | |]; try apply in_top. unfold in_itv; cbn [fst snd eval].
      rewrite srl_val. pose proof (Z.mod_pos_bound k 64 ltac:(lia)).
      rewrite !Z.shiftr_div_pow2 by lia.
      assert (0 < 2 ^ (k mod 64)) by (apply Z.pow_pos_nonneg; lia).
      split; apply Z.div_le_mono; lia.
    +   destruct e2 as [k| | | | | | |]; try apply in_top. unfold M63.
      destruct (Z.leb_spec la ha); [|apply in_top]. destruct (Z.ltb_spec ha (2 ^ 63)); [|apply in_top].
      unfold in_itv; cbn [fst snd eval]. unfold alu64, alu. rewrite bv_ashiftr_unsigned, shamt_val.
      rewrite signed_small by lia. unfold bv_wrap. rewrite two64.
      pose proof (Z.mod_pos_bound k 64 ltac:(lia)). rewrite !Z.shiftr_div_pow2 by lia.
      assert (0 < 2 ^ (k mod 64)) by (apply Z.pow_pos_nonneg; lia).
      assert (D1 : la / 2 ^ (k mod 64) <= bv_unsigned (eval rho e1) / 2 ^ (k mod 64)) by (apply Z.div_le_mono; lia).
      assert (D2 : bv_unsigned (eval rho e1) / 2 ^ (k mod 64) <= ha / 2 ^ (k mod 64)) by (apply Z.div_le_mono; lia).
      assert (D3 : 0 <= bv_unsigned (eval rho e1) / 2 ^ (k mod 64)) by (apply Z.div_pos; lia).
      assert (D4 : bv_unsigned (eval rho e1) / 2 ^ (k mod 64) <= bv_unsigned (eval rho e1)) by (apply Z.div_le_upper_bound; [lia|]; nia).
      rewrite (Z.mod_small (_ / _)) by lia. lia.
    +   unfold in_itv; cbn [fst snd eval]. rewrite or_val.
      pose proof (lor_bounds (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2)) ltac:(lia) ltac:(lia)).
      cbn [eval] in R. rewrite or_val in R. lia.
    +   destruct e2 as [m| | | | | | |].
      1: { rewrite zmod64_eq. unfold in_itv; cbn [fst snd eval]. rewrite and_val, lit_unsigned.
           pose proof (Z.mod_pos_bound m (2^64) ltac:(lia)).
           pose proof (land_le_l (bv_unsigned (eval rho e1)) (m mod 2^64) ltac:(lia) ltac:(lia)).
           pose proof (land_le_r (bv_unsigned (eval rho e1)) (m mod 2^64) ltac:(lia) ltac:(lia)).
           pose proof (Z.land_nonneg (bv_unsigned (eval rho e1)) (m mod 2^64)).
           pose proof (and_lo_sound la (bv_unsigned (eval rho e1)) m R1 ltac:(lia)).
           destruct e1; cbn [fst snd]; try lia.
           all: lia. }
      all: destruct e1 as [m| | | | | | |]; rewrite ?zmod64_eq; unfold in_itv; cbn [fst snd eval];
           cbn [eval] in IHe1, IHe2, R1, R2; rewrite and_val;
           first
             [ rewrite lit_unsigned;
               pose proof (Z.mod_pos_bound m (2^64) ltac:(lia));
               match goal with |- context [Z.land ?a ?b] => rewrite (Z.land_comm a b) end;
               match goal with |- context [Z.land ?a ?b] =>
                 pose proof (land_le_l a b ltac:(lia) ltac:(lia)); pose proof (land_le_r a b ltac:(lia) ltac:(lia));
                 pose proof (Z.land_nonneg a b);
                 pose proof (and_lo_sound lb a m R2 ltac:(lia)) end; lia
             |
               match goal with |- context [Z.land ?a ?b] =>
                 pose proof (land_le_l a b ltac:(lia) ltac:(lia)); pose proof (land_le_r a b ltac:(lia) ltac:(lia));
                 pose proof (Z.land_nonneg a b) end;
               destruct (Z.leb_spec la ha); destruct (Z.leb_spec lb hb); cbn [fst snd]; unfold top_itv; cbn [fst snd]; lia ].
  -
    pose proof (urange (eval rho e1)) as R1.
    pose proof (Hrec e1 ltac:(cbn; lia)) as IHe1.
    destruct (rec e1) as [la ha] eqn:I1.
    unfold in_itv in IHe1. cbn [fst snd] in IHe1.
    destruct op; try apply in_top. destruct e2 as [k| | | | | | |]; try apply in_top.
    destruct (Z.leb_spec la ha); [|apply in_top]. destruct (Z.ltb_spec ha (2 ^ 32)); [|apply in_top].
    destruct (Z.leb_spec 1 k); [|apply in_top]. destruct (Z.ltb_spec k 32); [|apply in_top].
    unfold in_itv; cbn [fst snd eval]. unfold alu32, alu.
    assert (M : bv_unsigned (bv_and (low32 (Z_to_bv 64 k)) (Z_to_bv 32 31)) = k).
    { rewrite bv_and_unsigned, low32_umod. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
      change (bv_modulus 32) with (2 ^ 32).
      rewrite (Z.mod_small k (2 ^ 64)) by lia. rewrite (Z.mod_small k (2 ^ 32)) by lia.
      change (31 mod 2 ^ 32) with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    assert (R : bv_unsigned (bv_shiftr (low32 (eval rho e1)) (bv_and (low32 (Z_to_bv 64 k)) (Z_to_bv 32 31)))
                = Z.shiftr (bv_unsigned (eval rho e1)) k).
    { rewrite bv_shiftr_unsigned, M, low32_umod. rewrite (Z.mod_small (bv_unsigned (eval rho e1))) by lia. reflexivity. }
    assert (B : 0 <= Z.shiftr (bv_unsigned (eval rho e1)) k < 2 ^ 31).
    { split; [apply Z.shiftr_nonneg; lia|].
      rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      apply (Z.lt_le_trans _ (2 ^ 32)); [lia|]. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
    rewrite sext64_32_small by (rewrite R; lia). rewrite R.
    rewrite !Z.shiftr_div_pow2 by lia. assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    split; apply Z.div_le_mono; lia.
  -
    pose proof (urange (eval rho e1)) as R1. pose proof (urange (eval rho e2)) as R2.
    pose proof (Hrec e1 ltac:(cbn; lia)) as IHe1. pose proof (Hrec e2 ltac:(cbn; lia)) as IHe2.
    destruct (rec e1) as [la ha] eqn:I1. destruct (rec e2) as [lb hb] eqn:I2.
    unfold in_itv in IHe1, IHe2. cbn [fst snd] in IHe1, IHe2.
    destruct op; try apply in_top.
    + destruct (Z.ltb_spec (ha * hb) (2 ^ 64)); [|apply in_top]. unfold in_itv; cbn [fst snd eval].
      rewrite mul_val.
      assert (bv_unsigned (eval rho e1) * bv_unsigned (eval rho e2) <= ha * hb) by (apply Z.mul_le_mono_nonneg; lia).
      assert (Z.max 0 la * Z.max 0 lb <= bv_unsigned (eval rho e1) * bv_unsigned (eval rho e2)) by (apply Z.mul_le_mono_nonneg; lia).
      rewrite Z.mod_small by nia. lia.
    +   unfold M63.
      destruct (Z.leb_spec la ha); [|apply in_top]. destruct (Z.leb_spec lb hb); [|apply in_top].
      destruct (Z.ltb_spec ha (2 ^ 63)); [|apply in_top]. destruct (Z.ltb_spec hb (2 ^ 63)); [|apply in_top].
      unfold in_itv; cbn [fst snd eval]. unfold mul_div, bv_mulhss. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
      rewrite !signed_small by lia. change (Z.of_N 64) with 64. rewrite !Z.shiftr_div_pow2 by lia.
      set (p := bv_unsigned (eval rho e1) * bv_unsigned (eval rho e2)).
      assert (P1 : Z.max 0 la * Z.max 0 lb <= p) by (subst p; apply Z.mul_le_mono_nonneg; lia).
      assert (P2 : p <= ha * hb) by (subst p; apply Z.mul_le_mono_nonneg; lia).
      assert (P3 : ha * hb < 2 ^ 63 * 2 ^ 63) by (apply Z.mul_lt_mono_nonneg; lia).
      assert (D1 : Z.max 0 la * Z.max 0 lb / 2 ^ 64 <= p / 2 ^ 64) by (apply Z.div_le_mono; lia).
      assert (D2 : p / 2 ^ 64 <= ha * hb / 2 ^ 64) by (apply Z.div_le_mono; lia).
      assert (D3 : 0 <= p / 2 ^ 64) by (apply Z.div_pos; nia).
      assert (D4 : ha * hb / 2 ^ 64 < 2 ^ 62) by (apply Z.div_lt_upper_bound; [lia|]; change (2 ^ 64 * 2 ^ 62) with (2 ^ 63 * 2 ^ 63); lia).
      rewrite (Z.mod_small (_ / _)) by lia. lia.
    +   unfold M64. destruct e2 as [c| | | | | | |]; try apply in_top. cbv zeta.
      destruct (Z.leb_spec la ha); [|apply in_top]. destruct (Z.leb_spec (zmod64 c) (zmod64 c)); [|apply in_top].
      destruct (Z.ltb_spec ha (2 ^ 64)); [|apply in_top]. destruct (Z.ltb_spec (zmod64 c) (2 ^ 64)); [|apply in_top].
      unfold in_itv; cbn [fst snd]. rewrite zmod64_eq in *.
      change (bv_unsigned (eval rho (SMd M_MULHU e1 (SLit c)))) with (bv_unsigned (mul_div M_MULHU (eval rho e1) (eval rho (SLit c)))).
      unfold mul_div, bv_mulhuu. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
      change (Z.of_N 64) with 64. rewrite !Z.shiftr_div_pow2 by lia.
      assert (Lc : bv_unsigned (eval rho (SLit c)) = c mod 2 ^ 64) by (cbn [eval]; apply lit_unsigned).
      rewrite Lc. pose proof (Z.mod_pos_bound c (2 ^ 64) ltac:(lia)) as Rc.
      set (q := bv_unsigned (eval rho e1) * (c mod 2 ^ 64)).
      assert (P1 : Z.max 0 la * Z.max 0 (c mod 2 ^ 64) <= q) by (subst q; apply Z.mul_le_mono_nonneg; lia).
      assert (P2 : q <= ha * (c mod 2 ^ 64)) by (subst q; apply Z.mul_le_mono_nonneg; lia).
      assert (P3 : ha * (c mod 2 ^ 64) < 2 ^ 64 * 2 ^ 64) by (apply Z.mul_lt_mono_nonneg; lia).
      assert (D1 : Z.max 0 la * Z.max 0 (c mod 2 ^ 64) / 2 ^ 64 <= q / 2 ^ 64) by (apply Z.div_le_mono; lia).
      assert (D2 : q / 2 ^ 64 <= ha * (c mod 2 ^ 64) / 2 ^ 64) by (apply Z.div_le_mono; lia).
      assert (D3 : 0 <= q / 2 ^ 64) by (apply Z.div_pos; LiaFast.nia_noeuclid).
      assert (D4 : ha * (c mod 2 ^ 64) / 2 ^ 64 < 2 ^ 64) by (apply Z.div_lt_upper_bound; lia).
      rewrite (Z.mod_small (_ / _)) by lia. lia.
    +   destruct (Z.leb_spec la ha); [|apply in_top]. destruct (Z.ltb_spec 0 lb); [|apply in_top].
      unfold in_itv; cbn [fst snd eval]. unfold mul_div.
      destruct (Z.eqb_spec (bv_unsigned (eval rho e2)) 0); [lia|].
      rewrite bv_modu_unsigned.
      pose proof (Z.mod_pos_bound (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2)) ltac:(lia)).
      pose proof (Z.mod_le (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2)) ltac:(lia) ltac:(lia)). lia.
  -
    pose proof (urange (eval rho e1)) as R1. pose proof (urange (eval rho e2)) as R2.
    pose proof (Hrec e1 ltac:(cbn; lia)) as IHe1. pose proof (Hrec e2 ltac:(cbn; lia)) as IHe2.
    destruct (rec e1) as [la ha] eqn:I1. destruct (rec e2) as [lb hb] eqn:I2.
    unfold in_itv in IHe1, IHe2. cbn [fst snd] in IHe1, IHe2.
    destruct op; try apply in_top.
    destruct (Z.leb_spec la ha); [|apply in_top]. destruct (Z.ltb_spec 0 lb); [|apply in_top].
    destruct (Z.ltb_spec hb (2 ^ 31)); [|apply in_top].
    unfold in_itv; cbn [fst snd eval]. unfold mul_div.
    rewrite !low32_umod. rewrite (Z.mod_small (bv_unsigned (eval rho e2))) by lia.
    destruct (Z.eqb_spec (bv_unsigned (eval rho e2)) 0); [lia|].
    pose proof (Z.mod_pos_bound (bv_unsigned (eval rho e1)) (2 ^ 32) ltac:(lia)) as M1.
    set (a' := bv_unsigned (eval rho e1) mod 2 ^ 32) in *.
    assert (A' : a' <= bv_unsigned (eval rho e1)) by (subst a'; apply Z.mod_le; lia).
    assert (HM : bv_unsigned (bv_modu (low32 (eval rho e1)) (low32 (eval rho e2))) = a' mod bv_unsigned (eval rho e2)).
    { rewrite bv_modu_unsigned, !low32_umod. rewrite (Z.mod_small (bv_unsigned (eval rho e2))) by lia. reflexivity. }
    pose proof (Z.mod_pos_bound a' (bv_unsigned (eval rho e2)) ltac:(lia)) as MB.
    pose proof (Z.mod_le a' (bv_unsigned (eval rho e2)) ltac:(lia) ltac:(lia)) as ML.
    rewrite sext64_32_small by (rewrite HM; lia). rewrite HM. lia.
  -
    pose proof (urange (eval rho e)) as R1.
    pose proof (Hrec e ltac:(cbn; lia)) as IHe.
    destruct (rec e) as [l h] eqn:I1. unfold in_itv in IHe. cbn [fst snd] in IHe.
    destruct sgn.
    {
      destruct (Z.leb_spec l h); [|apply in_top]. destruct (Z.ltb_spec 0 (Z.of_N w)); [|apply in_top].
      destruct (Z.leb_spec (Z.of_N w) 64); [|apply in_top]. destruct (Z.ltb_spec h (2 ^ (Z.of_N w - 1))); [|apply in_top].
      unfold in_itv; cbn [fst snd eval]. rewrite (ext_low_small true w) by lia. lia. }
    assert (V : bv_unsigned (eval rho (SExt false w e)) = (bv_unsigned (eval rho e) mod 2 ^ Z.of_N w) mod 2 ^ 64).
    { cbn [eval]. unfold ext_low, zext. rewrite bv_zero_extend_unsigned', bv_extract_unsigned.
      unfold bv_wrap. rewrite two64. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
      unfold bv_modulus. reflexivity. }
    assert (P : 0 < 2 ^ Z.of_N w) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.ltb_spec h (2 ^ Z.of_N w)).
    + unfold in_itv; cbn [fst snd]. rewrite V. rewrite (Z.mod_small _ (2 ^ Z.of_N w)) by lia.
      rewrite Z.mod_small by lia. lia.
    + destruct (Z.leb_spec (Z.of_N w) 64); [|apply in_top].
      unfold in_itv; cbn [fst snd]. rewrite V.
      pose proof (Z.mod_pos_bound (bv_unsigned (eval rho e)) (2 ^ Z.of_N w) P).
      assert (2 ^ Z.of_N w <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
      rewrite Z.mod_small by lia. lia.
Qed.

Lemma itv_t_sound_n : ltac2:(tb__ "0|0|
S5S3dS22S3S25R4R3A2S8eS2bR2A1R3A2S24S4aR5R3A2S15Q40S4R6R3A2A2A2F_;F_;Fe;Fn;Fdg;Frho;").
Proof using .
  intros rho dg n. induction n as [|n IH]; intros e Hd Hn; [lia|]. pose proof (dgv_tbl _ _ Hd) as Ht.
  assert (STEP : itv_t dg e = match tbl_find (dg_tbl dg) e with
                                | Some v => fst v
                                | None => itv_body (fun a => itv_t dg a) dg e
                                end) by (destruct e; reflexivity).
  rewrite STEP. destruct (tbl_find (dg_tbl dg) e) as [v|] eqn:Hfind.
  - exact (proj1 (tbl_find_sound rho _ _ _ Ht Hfind)).
  - apply itv_body_sound; [exact Hd |]. intros a Ha. apply IH; [exact Hd | lia].
Qed.

Lemma itv_t_sound : ltac2:(tb__ "0|0|
S5S3dS3S25R3R2A2S24S4aR3R2A2S15Q40S4R4R2A2A2A2F_;Fe;Fdg;Frho;").
Proof using . intros rho dg e Hd. apply (itv_t_sound_n rho dg (S (sv_size e))); [exact Hd | lia]. Qed.

Lemma itv_node_sound : ltac2:(tb__ "0|0|
S5S3dS3S25R3R2A2S24S6aR3R2A2S15Q40S4R4R2A2A2A2F_;Fe;Fdg;Frho;").
Proof using .
  intros rho dg e Hd. unfold itv_node. apply itv_body_sound; [exact Hd |].
  intros a _. apply itv_t_sound; assumption.
Qed.

Lemma ctx0_facts : ltac2:(tb__ "0|1|
S1cS6A1M0SfG0S42S46R1A1A1R1A3Ffacts;").
Proof using . reflexivity. Qed.
Lemma ctx0_ok : ltac2:(tb__ "0|0|
S5S1cS6A1S3cS6S7R2A1R1A3S25R3S46R2A1A2F_;Ffacts;Frho;").
Proof using .
  intros rho facts Hf. unfold dgv_ok, ctx0. cbn. repeat split.
  - exact Hf.
  - apply mk_cls_sound. exact Hf.
  - apply mk_nes_sound. exact Hf.
  - apply mk_bits_sound. exact Hf.
  - constructor.
Qed.

Lemma itv_decide_t_sound : ltac2:(tb__ "0|1|
S5S3dS89S3S3S25R5R4A2S40OLx;S68R5R4R3R2A4SfS19S85R4S4R6R3A2S4R6R2A2A3M0S1aA3SfS19G0S23A3S13X40x3F_;Fb;Fa;Fc;Fdg;Frho;").
Proof using .
  intros rho dg c a b Hd. unfold itv_decide_t, M63.
  pose proof (itv_t_sound rho dg a Hd) as Ha. pose proof (itv_t_sound rho dg b Hd) as Hb.
  destruct (itv_t dg a) as [la ha]. destruct (itv_t dg b) as [lb hb].
  unfold in_itv in Ha, Hb. cbn [fst snd] in Ha, Hb.
  destruct ((la <=? ha) && (lb <=? hb))%bool; [|exact I]. cbn [negb].
  destruct c; cbn [branch_taken]; unfold bv_ltu, bv_eqb, bv_lts.
  - destruct (Z.ltb_spec ha lb); [|destruct (Z.ltb_spec hb la)]; cbn [orb];
      [apply Z.eqb_neq; lia | apply Z.eqb_neq; lia |].
    destruct ((la =? ha) && (lb =? hb) && (la =? lb))%bool eqn:E; [|exact I].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. apply Z.eqb_eq. lia.
  - destruct (Z.ltb_spec ha lb); [|destruct (Z.ltb_spec hb la)]; cbn [orb negb];
      [rewrite (proj2 (Z.eqb_neq _ _)) by lia; reflexivity | rewrite (proj2 (Z.eqb_neq _ _)) by lia; reflexivity |].
    destruct ((la =? ha) && (lb =? hb) && (la =? lb))%bool eqn:E; [|exact I].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3.
    rewrite (proj2 (Z.eqb_eq _ _)) by lia. reflexivity.
  - destruct ((ha <? 2 ^ 63) && (hb <? 2 ^ 63))%bool eqn:E; cbn [negb]; [|exact I].
    apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
    rewrite !signed_small by lia.
    destruct (Z.ltb_spec ha lb); [apply Z.ltb_lt; lia|].
    destruct (Z.leb_spec hb la); [apply Z.ltb_ge; lia | exact I].
  - destruct ((ha <? 2 ^ 63) && (hb <? 2 ^ 63))%bool eqn:E; cbn [negb]; [|exact I].
    apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
    rewrite !signed_small by lia.
    destruct (Z.ltb_spec ha lb); [cbn; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity|].
    destruct (Z.leb_spec hb la); [cbn; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity | exact I].
  - destruct (Z.ltb_spec ha lb); [apply Z.ltb_lt; lia|].
    destruct (Z.leb_spec hb la); [apply Z.ltb_ge; lia | exact I].
  - destruct (Z.ltb_spec ha lb); [cbn; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity|].
    destruct (Z.leb_spec hb la); [cbn; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity | exact I].
Qed.

Lemma itv_decide_sound : ltac2:(tb__ "0|1|
S5S1cS6A1S89S3S3S3cS6S7R5A1R4A3S40OLx;S67R5R4R3R2A4SfS19S85R4S4R6R3A2S4R6R2A2A3M0S1aA3SfS19G0S23A3S13X40x3F_;Fb;Fa;Fc;Ffacts;Frho;").
Proof using . intros rho facts c a b Hf. unfold itv_decide. apply itv_decide_t_sound. apply ctx0_ok. exact Hf. Qed.

Lemma small_u_t_sound : ltac2:(tb__ "0|1|
S5S3dS3S0S25R4R3A2SfS19S7bR4R3R2A3S1aA3S10S2cZ0S15Q40S4R6R4A2A2M0A2S30G0S2dZ2R3A2A2A2F_;F_;Fw;Fe;Fdg;Frho;").
Proof using .
  intros rho dg e w Hd H. unfold small_u_t in H.
  pose proof (itv_t_sound rho dg e Hd) as I. destruct (itv_t dg e) as [l h].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold in_itv in I. cbn in I. pose proof (urange (eval rho e)). lia.
Qed.

Lemma lit_fold_t_sound : ltac2:(tb__ "0|0|
S5S3dS3S25R3R2A2SfS16Q40A1S4R4S4bR3R2A2A2S4R4R2A2A3F_;Fe;Fdg;Frho;").
Proof using .
  intros rho dg e Hd.
  assert (G : eval rho (let '(lo, hi) := itv_t dg e in if lo =? hi then SLit lo else e) = eval rho e).
  { pose proof (itv_t_sound rho dg e Hd) as I. destruct (itv_t dg e) as [lo hi].
    unfold in_itv in I; cbn [fst snd] in I.
    destruct (Z.eqb_spec lo hi); [|reflexivity]. cbn [eval].
    rewrite <- (Z_to_bv_bv_unsigned 64 (eval rho e)). apply Z_to_bv64_eq_iff. f_equal. lia. }
  unfold lit_fold_t. destruct e; first [reflexivity | exact G].
Qed.

Lemma lit_fold_t_below : ltac2:(tb__ "0|0|
S1S3dS3SfS19S8R3R1A2S1aA3SfS19S8R4S4bR3R2A2A2S1aA3F_;Fe;Fdg;Fn;").
Proof using .
  intros n dg e H.
  assert (G : sv_below n (let '(lo, hi) := itv_t dg e in if lo =? hi then SLit lo else e) = true).
  { destruct (itv_t dg e) as [lo hi]. destruct (lo =? hi); [reflexivity | exact H]. }
  unfold lit_fold_t. destruct e; first [exact H | exact G].
Qed.

Lemma mk_ext_f_t_sound : ltac2:(tb__ "0|0|
S5S3dS19S2S3S25R5R4A2SfS16Q40A1S4R6S4dR5R4R3R2A4A2SbR4R3S4R6R2A2A3A3F_;Fa;Fw;Fsgn;Fdg;Frho;").
Proof using .
  intros rho dg sgn w a Hd. unfold mk_ext_f_t.
  destruct ((0 <? Z.of_N w) && (Z.of_N w <=? 64) && small_u_t dg a (if sgn then Z.of_N w - 1 else Z.of_N w))%bool eqn:E;
    [|apply mk_ext_sound].
  apply andb_prop in E as [E Hs]. apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.leb_le in E2.
  symmetry. apply ext_low_small; [lia|]. exact (proj2 (small_u_t_sound rho dg a _ Hd Hs)).
Qed.

Lemma mk_ext_f_t_below : ltac2:(tb__ "0|0|
S1S3dS19S2S3SfS19S8R5R1A2S1aA3SfS19S8R6S4dR5R4R3R2A4A2S1aA3F_;Fa;Fw;Fsgn;Fdg;Fn;").
Proof using .
  intros. unfold mk_ext_f_t. destruct (_ && _ && _)%bool; [assumption | apply mk_ext_below; assumption].
Qed.

Lemma mk_ext_s_below : ltac2:(tb__ "0|0|
S1S3dS19S2S3SfS19S8R5R1A2S1aA3SfS19S8R6S70R5R4R3R2A4A2S1aA3F_;Fa;Fw;Fsgn;Fdg;Fn;").
Proof using .
  intros. unfold mk_ext_s. destruct (sgn && _)%bool; [|apply mk_ext_below; assumption].
  cbn zeta. destruct (_ && _)%bool; [assumption | apply mk_ext_below; assumption].
Qed.
Lemma mk_ext_f_below : ltac2:(tb__ "0|0|
S1S1cS6A1S19S2S3SfS19S8R5R1A2S1aA3SfS19S8R6S6fR5R4R3R2A4A2S1aA3F_;Fa;Fw;Fsgn;Ffacts;Fn;").
Proof using .
  intros. unfold mk_ext_f.
  pose proof (mk_ext_f_t_below n (ctx0 facts) sgn w a H).
  destruct (mk_ext_f_t (ctx0 facts) sgn w a); try assumption.
  pose proof (mk_ext_f_t_below n (mk_ctx facts) sgn w a H).
  destruct (mk_ext_f_t (mk_ctx facts) sgn w a); try assumption. apply mk_ext_s_below. assumption.
Qed.

Lemma mk_aluw_f_t_sound : ltac2:(tb__ "0|1|
S5S3dS87S3S3S25R5R4A2SfS16Q40M0A1S4R6S4cR5R4R3R2A4A2S8fQ20G0S86R4S84S4R6R3A2A1S84S4R6R2A2A1A3A3A3F_;Fb;Fa;Fop;Fdg;Frho;").
Proof using .
  intros rho dg op a b Hd. unfold mk_aluw_f_t. rewrite (lit_fold_t_sound rho) by assumption.
  assert (ADDSUB : forall op', (op' = ALU_ADD \/ op' = ALU_SUB) ->
     eval rho (let r := mk_alu op' a b in
               if small_u_t dg r 31 then r else mk_aluw op' a b)
     = sext 64 (alu32 op' (low32 (eval rho a)) (low32 (eval rho b)))).
  { intros op' Hop. cbn zeta.
    destruct (small_u_t dg (mk_alu op' a b) 31) eqn:Er; [|apply mk_aluw_sound].
    pose proof (small_u_t_sound rho dg (mk_alu op' a b) 31 Hd Er) as Br. rewrite mk_alu_sound in Br |- *.
    pose proof (urange (eval rho a)) as Ra. pose proof (urange (eval rho b)) as Rb.
    assert (D : (2 ^ 32 | 2 ^ 64)%Z) by (exists (2 ^ 32); reflexivity).

    assert (L : bv_unsigned (alu32 op' (low32 (eval rho a)) (low32 (eval rho b)))
                = bv_unsigned (alu64 op' (eval rho a) (eval rho b)) mod 2 ^ 32).
    { unfold alu32, alu64, alu. destruct Hop as [-> | ->].
      - rewrite !bv_add_unsigned, !low32_umod. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite two64.
        rewrite (Z.mod_mod_divide _ _ _ D). rewrite <- Z.add_mod by lia. reflexivity.
      - rewrite !bv_sub_unsigned, !low32_umod. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite two64.
        rewrite (Z.mod_mod_divide _ _ _ D). rewrite <- Zminus_mod. reflexivity. }
    apply bv_eq. rewrite sext64_32_small by (rewrite L, Z.mod_small; lia).
    rewrite L. rewrite Z.mod_small by lia. reflexivity. }
  destruct op; try apply mk_aluw_sound.
  - apply ADDSUB. left; reflexivity.
  - destruct (sv_eqb a b) eqn:E; [|apply ADDSUB; right; reflexivity]. rewrite (sv_eqb_sound _ _ E).
    cbn [eval]. unfold alu32, alu. apply bv_eq. rewrite Z_to_bv_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
    rewrite bv_sub_signed. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma mk_aluw_f_t_below : ltac2:(tb__ "0|0|
S1S3dS87S3S3SfS19S8R5R2A2S1aA3SfS19S8R6R2A2S1aA3SfS19S8R7S4cR6R5R4R3A4A2S1aA3F_;F_;Fb;Fa;Fop;Fdg;Fn;").
Proof using .
  intros. unfold mk_aluw_f_t. apply lit_fold_t_below. destruct op; try (apply mk_aluw_below; assumption).
  - cbn zeta. destruct (small_u_t _ _ _); [apply mk_alu_below; assumption | apply mk_aluw_below; assumption].
  - destruct (sv_eqb a b); [reflexivity|]. cbn zeta.
    destruct (small_u_t _ _ _); [apply mk_alu_below; assumption | apply mk_aluw_below; assumption].
Qed.

Lemma mk_aluw_s_below : ltac2:(tb__ "0|0|
S1S3dS87S3S3SfS19S8R5R2A2S1aA3SfS19S8R6R2A2S1aA3SfS19S8R7S6cR6R5R4R3A4A2S1aA3F_;F_;Fb;Fa;Fop;Fdg;Fn;").
Proof using .
  intros. unfold mk_aluw_s. destruct op; try (apply mk_aluw_below; assumption);
  cbn zeta; destruct (_ && _)%bool; first [apply mk_alu_below; assumption | apply mk_aluw_below; assumption].
Qed.
Lemma mk_aluw_f_below : ltac2:(tb__ "0|0|
S1S1cS6A1S87S3S3SfS19S8R5R2A2S1aA3SfS19S8R6R2A2S1aA3SfS19S8R7S6bR6R5R4R3A4A2S1aA3F_;F_;Fb;Fa;Fop;Ffacts;Fn;").
Proof using .
  intros. unfold mk_aluw_f.
  pose proof (mk_aluw_f_t_below n (ctx0 facts) op a b H H0).
  destruct (mk_aluw_f_t (ctx0 facts) op a b); try assumption.
  pose proof (mk_aluw_f_t_below n (mk_ctx facts) op a b H H0).
  destruct (mk_aluw_f_t (mk_ctx facts) op a b); try assumption. apply mk_aluw_s_below; assumption.
Qed.

Lemma xor_same_base_sound : ltac2:(tb__ "0|0|
S5S3S19SfS1eS19A1S80R2A1S1dS19R1A2A3SfS19S38S15Q40S4R4R3A2A2Z0A2R2A3F_;Fz;Fe;Frho;").
Proof using .
  intros rho e z H. unfold xor_same_base in H.
  destruct e as [| |op x y| | | | |]; try discriminate. destruct op; try discriminate.
  assert (G : forall (bx : sv) kx ky, eval rho x = (eval rho bx + Z_to_bv 64 kx)%bv -> eval rho y = (eval rho bx + Z_to_bv 64 ky)%bv ->
             (bv_unsigned (eval rho (SAlu ALU_XOR x y)) =? 0) = ((kx - ky) mod 2 ^ 64 =? 0)).
  { intros bx kx ky Hx Hy. cbn [eval]. unfold alu64, alu. rewrite bv_xor_unsigned, Hx, Hy, !bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. rewrite two64. set (u := bv_unsigned (eval rho bx)). pose proof (urange (eval rho bx)).
    pose proof (Z.mod_pos_bound (u + kx mod 2^64) (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound (u + ky mod 2^64) (2^64) ltac:(lia)).
    rewrite !Zplus_mod_idemp_r.
    destruct (Z.eqb_spec ((kx - ky) mod 2 ^ 64) 0) as [E|E].
    - apply Z.eqb_eq. apply Z.lxor_eq_0_iff.
      replace (u + kx) with ((u + ky) + (kx - ky)) by lia. rewrite <- (Zplus_mod_idemp_r (kx - ky)), E, Z.add_0_r. reflexivity.
    - apply Z.eqb_neq. intros X. pose proof (proj1 (Z.lxor_eq_0_iff _ _) X) as X'. apply E.
      replace (kx - ky) with ((u + kx) - (u + ky)) by lia.
      rewrite <- Zminus_mod_idemp_l, X', <- Zminus_mod_idemp_r, Z.sub_diag. reflexivity. }
  destruct (as_addlit x) as [[bx kx]|] eqn:Ex; destruct (as_addlit y) as [[by_ ky]|] eqn:Ey.
  - destruct (sv_eqb bx by_) eqn:Eb; [|discriminate]. injection H as <-. apply sv_eqb_sound in Eb. subst by_.
    apply (G bx); eapply as_addlit_sound; eauto.
  - destruct (sv_eqb bx y) eqn:Eb; [|discriminate]. injection H as <-. apply sv_eqb_sound in Eb. subst y.
    rewrite <- (Z.sub_0_r kx). apply (G bx); [eapply as_addlit_sound; eauto | symmetry; apply bv_add_0_r].
  - destruct (sv_eqb x by_) eqn:Eb; [|discriminate]. injection H as <-. apply sv_eqb_sound in Eb. subst by_.
    replace (ky mod 2 ^ 64 =? 0) with ((0 - ky) mod 2 ^ 64 =? 0).
    2:{ rewrite Z.sub_0_l.
        destruct (Z.eqb_spec (ky mod 2^64) 0) as [E|E], (Z.eqb_spec ((- ky) mod 2^64) 0) as [F|F]; try reflexivity; exfalso.
        - apply F. apply Z.mod_divide; [lia|]. apply Z.divide_opp_r. apply Z.mod_divide; [lia|]. exact E.
        - apply E. apply Z.mod_divide; [lia|]. apply Z.divide_opp_r. apply Z.mod_divide; [lia|]. exact F. }
    apply (G x); [symmetry; apply bv_add_0_r | eapply as_addlit_sound; eauto].
  - discriminate.
Qed.

Lemma slt_xor_fold_sound : ltac2:(tb__ "0|0|
S5S3S3S3SfS1eS3A1S7aR3R2A2S1dS3R1A2A3SfS16Q40A1S4R5R2A2S83S8bS4R5R4A2S4R5R3A2A3A3F_;Fr;Fb;Fa;Frho;").
Proof using .
  intros rho a b r H. unfold slt_xor_fold in H.
  assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by (rewrite Z_to_bv_small; [reflexivity | unfold bv_modulus; cbn; lia]).
  assert (U1 : bv_unsigned (Z_to_bv 64 1) = 1) by (rewrite Z_to_bv_small; [reflexivity | unfold bv_modulus; cbn; lia]).
  assert (CASE2 : match b with
      | SLit 1 => match xor_same_base a with
                  | Some iszero => Some (SLit (if iszero then 1 else 0))
                  | None => None end
      | _ => None end = Some r -> eval rho r = alu64 ALU_SLTU (eval rho a) (eval rho b)).
  { clear H. intros H. destruct b as [zb| | | | | | |]; try discriminate.
    destruct zb as [|pb|]; try discriminate; destruct pb; try discriminate.
    destruct (xor_same_base a) as [z|] eqn:E; [|discriminate]. injection H as <-.
    pose proof (xor_same_base_sound rho a z E) as X. pose proof (urange (eval rho a)) as R.
    cbn [eval]. unfold alu64, alu, bv_ltu. rewrite U1.
    destruct z; [apply Z.eqb_eq in X | apply Z.eqb_neq in X];
    match goal with |- _ = (if ?c then _ else _) => destruct c eqn:C end;
    try reflexivity; exfalso; first [apply Z.ltb_lt in C | apply Z.ltb_ge in C]; lia. }
  destruct a as [za| | | | | | |]; try (apply CASE2; exact H).
  destruct za as [|pa|]; try (apply CASE2; exact H).
  destruct (xor_same_base b) as [z|] eqn:E; [|discriminate]. injection H as <-.
  pose proof (xor_same_base_sound rho b z E) as X. pose proof (urange (eval rho b)) as R.
  cbn [eval]. unfold alu64, alu, bv_ltu. rewrite U0.
  destruct z; [apply Z.eqb_eq in X | apply Z.eqb_neq in X];
  match goal with |- _ = (if ?c then _ else _) => destruct c eqn:C end;
  try reflexivity; exfalso; first [apply Z.ltb_lt in C | apply Z.ltb_ge in C]; lia.
Qed.

End V.

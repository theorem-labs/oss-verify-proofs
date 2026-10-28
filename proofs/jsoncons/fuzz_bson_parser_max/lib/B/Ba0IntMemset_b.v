(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemsetLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r71154_71230_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lor_lt_pow2 : forall a b k, (0 <= a < 2 ^ k)%Z -> (0 <= b < 2 ^ k)%Z -> (0 <= Z.lor a b < 2 ^ k)%Z.
Proof.
  intros a b k Ha Hb.
  assert (Hk : (0 <= k)%Z \/ (k < 0)%Z) by lia. destruct Hk as [Hk|Hk]; [|rewrite Z.pow_neg_r in Ha by lia; lia].
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land15_lor : forall a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Z.land (Z.lor a b) 15 = 0 <-> a mod 16 = 0 /\ b mod 16 = 0)%Z.
Proof.
  intros a b Ha Hb. rewrite Z.land_lor_distr_l.
  change 15%Z with (Z.ones 4). rewrite !Z.land_ones by lia. change (2 ^ 4)%Z with 16%Z.
  rewrite Z.lor_eq_0_iff. tauto.
Qed.

Lemma lor_disjoint_shift : forall k a b, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros k a b Hk Ha Hb.
  assert (Hl : Z.land (a * 2 ^ k) b = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k).
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
    - rewrite (Z_testbit_high k b) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma v_or_slli : forall (x : word) k, (0 <= k)%Z -> (0 <= bv_unsigned x < 2 ^ k)%Z ->
  (bv_unsigned x * 2 ^ k + bv_unsigned x < 2 ^ 64)%Z ->
  v_or (v_slli x k) x = Z_to_bv 64 (bv_unsigned x * (2 ^ k + 1)).
Proof.
  intros x k Hk Hx Hw. unfold v_or, v_slli. f_equal.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by nia.
  rewrite lor_disjoint_shift by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.

Section Walk.
  Variable mem0 : word -> option byte.
  Variables d cv ret : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).

  #[local] Ltac msb F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sb ASEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | lia | lia]
      | step_simpl].
  #[local] Ltac msd F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sd ASEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb8_c64
        | lia | lia]
      | step_simpl].
  #[local] Ltac mret := stepret F_8b0a4 D_8b0a4 ret ltac:(rwH; reflexivity).
  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.

  #[local] Ltac ms_cov_eq :=
    intros i Hi; rewrite !ms_cov_cons;
    match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
    rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
    apply eq_true_iff_eq; rewrite ?orb_true_iff, !ms_inb_true; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bloop_run : forall (q : nat) regs L a,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = at_ d n -> getr regs 13 = at_ d a -> getr regs 1 = ret ->
    (0 <= a)%Z -> (a + Z.of_nat q + 1 = n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x8b478 : word) (CF L) rom)
                   (mkst regs' (0x8b484 : word) (CF ((a, Z.of_nat q + 1)%Z :: L)) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 1 = ret /\ ms_agree regs regs'.
  Proof.
    induction q as [|q IH]; intros regs L a H10 H11 H12 H13 H1 Ha Hq; pose proof (u64_range d) as Hd.
    - eexists. split.
      + msb F_8b060 D_8b060 a.                                                      (* [comment removed for export] *)
        stepiv F_8b064 D_8b064 (at_ d (a + 1)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).   (* [comment removed for export] *)
        stepb_ft F_8b068 D_8b068 ltac:(cond).                                        (* [comment removed for export] *)
        replace (CF ((a, Z.of_nat 0 + 1)%Z :: L)) with (CF ((a, 1)%Z :: L)) by (apply cfill_ext; ms_cov_eq).
        apply mst_refl.
      + post.
    - eapply (runs_trans ASEGS _
                (fun rg => mkst rg (0x8b478 : word) (CF ((a, 1)%Z :: L)) rom)
                (fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = cv /\ getr rg 12 = at_ d n /\ getr rg 13 = at_ d (a + 1)
                           /\ getr rg 1 = ret /\ ms_agree regs rg)).
      + cbv beta. eexists. split.
        * msb F_8b060 D_8b060 a.
          stepiv F_8b064 D_8b064 (at_ d (a + 1)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
          stepb_tk F_8b068 D_8b068 ltac:(cond).                                      (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R10 & R11 & R12 & R13 & R1 & AG).
        destruct (IH r1 ((a, 1)%Z :: L) (a + 1)%Z R10 R11 R12 R13 R1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
        exists r2. split.
        * replace (CF ((a, Z.of_nat (S q) + 1)%Z :: L))
            with (CF ((a + 1, Z.of_nat q + 1)%Z :: (a, 1)%Z :: L)) by (apply cfill_ext; ms_cov_eq).
          exact RUN.
        * repeat split; try assumption. eapply ms_agree_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wloop_run : forall (q : nat) regs L a,
    getr regs 10 = at_ d 0 -> getr regs 11 = c64 cv -> getr regs 12 = at_ d n -> getr regs 13 = at_ d a -> getr regs 1 = ret ->
    (0 <= a)%Z -> (a + 16 * (Z.of_nat q + 1) = n)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x8b4ac : word) (CF L) rom)
                   (mkst regs' (0x8b4bc : word) (CF ((a, 16 * (Z.of_nat q + 1))%Z :: L)) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 1 = ret /\ ms_agree regs regs'.
  Proof.
    induction q as [|q IH]; intros regs L a H10 H11 H12 H13 H1 Ha Hq; pose proof (u64_range d) as Hd.
    - eexists. split.
      + msd F_8b094 D_8b094 a.                                                      (* [comment removed for export] *)
        msd F_8b098 D_8b098 (a + 8)%Z.                                              (* [comment removed for export] *)
        stepiv F_8b09c D_8b09c (at_ d (a + 16)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).  (* [comment removed for export] *)
        stepb_ft F_8b0a0 D_8b0a0 ltac:(cond).                                        (* [comment removed for export] *)
        replace (CF ((a, 16 * (Z.of_nat 0 + 1))%Z :: L)) with (CF ((a + 8, 8)%Z :: (a, 8)%Z :: L)) by (apply cfill_ext; ms_cov_eq).
        apply mst_refl.
      + post.
    - eapply (runs_trans ASEGS _
                (fun rg => mkst rg (0x8b4ac : word) (CF ((a + 8, 8)%Z :: (a, 8)%Z :: L)) rom)
                (fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = c64 cv /\ getr rg 12 = at_ d n /\ getr rg 13 = at_ d (a + 16)
                           /\ getr rg 1 = ret /\ ms_agree regs rg)).
      + cbv beta. eexists. split.
        * msd F_8b094 D_8b094 a.
          msd F_8b098 D_8b098 (a + 8)%Z.
          stepiv F_8b09c D_8b09c (at_ d (a + 16)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
          stepb_tk F_8b0a0 D_8b0a0 ltac:(cond).                                      (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R10 & R11 & R12 & R13 & R1 & AG).
        destruct (IH r1 ((a + 8, 8)%Z :: (a, 8)%Z :: L) (a + 16)%Z R10 R11 R12 R13 R1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
        exists r2. split.
        * replace (CF ((a, 16 * (Z.of_nat (S q) + 1))%Z :: L))
            with (CF ((a + 16, 16 * (Z.of_nat q + 1))%Z :: (a + 8, 8)%Z :: (a, 8)%Z :: L)) by (apply cfill_ext; ms_cov_eq).
          exact RUN.
        * repeat split; try assumption. eapply ms_agree_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma v_add_dn : v_add d (Z_to_bv 64 n) = at_ d n.
  Proof.
    pose proof (u64_range d). unfold v_add, at_. f_equal. rewrite !u_Z2bv by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[local] Ltac cond15 H :=
    rwH; unfold v_andi, v_or, c_eq, bv_eqb; change (bv_wrap 64 15) with 15%Z; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq]; exact H.

  Theorem int_memset_run : forall regs,
    getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (bv_unsigned cv < 256)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x8b460 : word) mem0 rom)
                   (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10 = d /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hcv. pose proof (u64_range d) as Hd. pose proof (u64_range cv) as Hcvr.
    replace (mkst regs (0x8b460 : word) mem0 rom) with (mkst regs (0x8b460 : word) (CF []) rom)
      by (rewrite (cfill_nil mem0 d n (cbyte cv)); reflexivity).
    assert (Hlor : (0 <= Z.lor n (bv_unsigned d) < 2 ^ 64)%Z) by (apply lor_lt_pow2; lia).
    assert (Hland : (0 <= Z.land (Z.lor n (bv_unsigned d)) 15 <= 15)%Z).
    { split; [apply Z.land_nonneg; right; lia|].
      change 15%Z with (Z.ones 4) at 1. rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound (Z.lor n (bv_unsigned d)) (2 ^ 4) ltac:(lia)). lia. }
    destruct (Z.eq_dec (Z.land (Z.lor n (bv_unsigned d)) 15) 0) as [Hal|Hnal].
    - (* [comment removed for export] *)
      pose proof (proj1 (land15_lor n (bv_unsigned d) Hn ltac:(lia)) Hal) as [Hn16 Hd16].
      destruct (Z.eq_dec n 0) as [Hn0|Hn0].
      + eexists. split.
        * stepi F_8b048 D_8b048.                                           (* [comment removed for export] *)
          stepi F_8b04c D_8b04c.                                           (* [comment removed for export] *)
          stepb_tk F_8b050 D_8b050 ltac:(cond15 Hal).                     (* [comment removed for export] *)
          stepb_tk F_8b070 D_8b070 ltac:(cond).                            (* [comment removed for export] *)
          mret.
          rewrite (cfill_full mem0 d n (cbyte cv) Hn Hnw []) by (intros i Hi; lia).
          apply mst_refl.
        * post.
      + assert (Hq : exists q : nat, (16 * (Z.of_nat q + 1) = n)%Z).
        { exists (Z.to_nat (n / 16 - 1)). pose proof (Z.div_mod n 16 ltac:(lia)). rewrite Z2Nat.id; lia. }
        destruct Hq as (q & Hq).
        assert (Hc64 : v_or (v_slli (v_or (v_slli (v_or (v_slli cv 8) cv) 16) (v_or (v_slli cv 8) cv)) 32)
                            (v_or (v_slli (v_or (v_slli cv 8) cv) 16) (v_or (v_slli cv 8) cv)) = c64 cv).
        { rewrite (v_or_slli cv 8) by lia.
          assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned cv * (2 ^ 8 + 1))) = (bv_unsigned cv * 257)%Z) by (rewrite u_Z2bv; lia).
          rewrite (v_or_slli _ 16); [| lia | rewrite U1; lia | rewrite U1; lia]. rewrite U1.
          assert (U2 : bv_unsigned (Z_to_bv 64 (bv_unsigned cv * 257 * (2 ^ 16 + 1))) = (bv_unsigned cv * 16843009)%Z) by (rewrite u_Z2bv; lia).
          rewrite (v_or_slli _ 32); [| lia | rewrite U2; lia | rewrite U2; lia]. rewrite U2.
          unfold c64, cbz. f_equal. rewrite Z.mod_small by lia. lia. }
        eapply (runs_trans ASEGS _
                  (fun rg => mkst rg (0x8b4ac : word) (CF []) rom)
                  (fun rg => getr rg 10 = d /\ getr rg 11 = c64 cv /\ getr rg 12 = at_ d n /\ getr rg 13 = d
                             /\ getr rg 1 = ret /\ ms_agree regs rg)).
        * cbv beta. eexists. split.
          -- stepi F_8b048 D_8b048.
             stepi F_8b04c D_8b04c.
             stepb_tk F_8b050 D_8b050 ltac:(cond15 Hal).
             stepb_ft F_8b070 D_8b070 ltac:(cond).                         (* [comment removed for export] *)
             stepiv F_8b074 D_8b074 (at_ d n) ltac:(gres; rwH; apply v_add_dn).   (* [comment removed for export] *)
             stepi F_8b078 D_8b078. stepi F_8b07c D_8b07c.                 (* [comment removed for export] *)
             stepi F_8b080 D_8b080. stepi F_8b084 D_8b084.
             stepi F_8b088 D_8b088.
             stepi F_8b08c D_8b08c.
             stepiv F_8b090 D_8b090 d ltac:(gres; rwH; imm_norm; apply v_addi_0).   (* [comment removed for export] *)
             apply mst_refl.
          -- repeat split; gres; rwH; rewrite ?Hc64; try reflexivity; solve_ms_agree.
        * cbv beta. intros r1 (R10 & R11 & R12 & R13 & R1 & AG).
          rewrite <- (at_0 d) in R10, R13.
          destruct (wloop_run q r1 [] 0 R10 R11 R12 R13 R1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
          exists r2. split; [|split; [rewrite at_0 in P10; exact P10 | eapply ms_agree_trans; eassumption]].
          eapply msteps_trans; [exact RUN|].
          rewrite (cfill_full mem0 d n (cbyte cv) Hn Hnw [(0, 16 * (Z.of_nat q + 1))%Z])
            by (intros i Hi; rewrite ms_cov_cons; apply orb_true_iff; left; apply ms_inb_true; lia).
          stepret F_8b0a4 D_8b0a4 ret ltac:(rewrite P1; reflexivity).
          apply mst_refl.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hn0|Hn0].
      + eexists. split.
        * stepi F_8b048 D_8b048.
          stepi F_8b04c D_8b04c.
          stepb_ft F_8b050 D_8b050 ltac:(cond15 Hnal).
          stepb_tk F_8b054 D_8b054 ltac:(cond).                            (* [comment removed for export] *)
          mret.
          rewrite (cfill_full mem0 d n (cbyte cv) Hn Hnw []) by (intros i Hi; lia).
          apply mst_refl.
        * post.
      + assert (Hq : exists q : nat, (Z.of_nat q + 1 = n)%Z) by (exists (Z.to_nat (n - 1)); rewrite Z2Nat.id; lia).
        destruct Hq as (q & Hq).
        eapply (runs_trans ASEGS _
                  (fun rg => mkst rg (0x8b478 : word) (CF []) rom)
                  (fun rg => getr rg 10 = d /\ getr rg 11 = cv /\ getr rg 12 = at_ d n /\ getr rg 13 = d
                             /\ getr rg 1 = ret /\ ms_agree regs rg)).
        * cbv beta. eexists. split.
          -- stepi F_8b048 D_8b048.
             stepi F_8b04c D_8b04c.
             stepb_ft F_8b050 D_8b050 ltac:(cond15 Hnal).
             stepb_ft F_8b054 D_8b054 ltac:(cond).                         (* [comment removed for export] *)
             stepiv F_8b058 D_8b058 (at_ d n) ltac:(gres; rwH; apply v_add_dn).   (* [comment removed for export] *)
             stepiv F_8b05c D_8b05c d ltac:(gres; rwH; imm_norm; apply v_addi_0).  (* [comment removed for export] *)
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R10 & R11 & R12 & R13 & R1 & AG).
          rewrite <- (at_0 d) in R10, R13.
          destruct (bloop_run q r1 [] 0 R10 R11 R12 R13 R1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
          exists r2. split; [|split; [rewrite at_0 in P10; exact P10 | eapply ms_agree_trans; eassumption]].
          eapply msteps_trans; [exact RUN|].
          rewrite (cfill_full mem0 d n (cbyte cv) Hn Hnw [(0, Z.of_nat q + 1)%Z])
            by (intros i Hi; rewrite ms_cov_cons; apply orb_true_iff; left; apply ms_inb_true; lia).
          stepj F_8b06c D_8b06c.                                           (* [comment removed for export] *)
          stepret F_8b0a4 D_8b0a4 ret ltac:(rewrite P1; reflexivity).
          apply mst_refl.
  Qed.
End Walk.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0MemcpyBase_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r71154_71230_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint wbrev (m : word -> option byte) (a : word) (bs : list byte) : word -> option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (wbrev m (a + 1) rest) a [b]
  end.

Lemma wbrev_out : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbrev m a bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [reflexivity|].
  cbn [wbrev] in *. change (length (b :: rest)) with (S (length rest)) in *. rewrite Nat2Z.inj_succ in *.
  pose proof (u64_range a). pose proof (u64_range x).
  assert (STEP : wbytes (wbrev m (a + 1) rest) a [b] x = wbrev m (a + 1) rest x).
  { destruct Hx as [Hx|Hx].
    - rewrite wbytes_below; [reflexivity | cbn [length Z.of_nat Pos.to_nat]; lia | lia].
    - rewrite wbytes_above by (cbn [length Z.of_nat Pos.to_nat]; lia). reflexivity. }
  rewrite STEP. destruct rest as [|b2 rest2]; [reflexivity|].
  change (length (b2 :: rest2)) with (S (length rest2)) in *. rewrite Nat2Z.inj_succ in *.
  assert (Ea1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (rewrite word_succ_at; apply at_u; lia).
  apply IH; try change (length (b2 :: rest2)) with (S (length rest2)); rewrite ?Nat2Z.inj_succ; rewrite ?Ea1; lia.
Qed.

Lemma wbrev_grows : forall bs m a, mem_grows m (wbrev m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a; cbn [wbrev]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [apply IH | apply wbytes_grows].
Qed.

(* [comment removed for export] *)
Lemma wbrev_pw : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  wbrev m a bs x = wbytes m a bs x.
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw; [reflexivity|].
  change (length (b :: rest)) with (S (length rest)) in *. rewrite Nat2Z.inj_succ in *.
  cbn [wbrev wbytes]. pose proof (u64_range a). pose proof (u64_range x).
  destruct (bv_eqb x a) eqn:E.
  - (* [comment removed for export] *)
    apply (proj1 (Fs.bv_eqb_eq x a)) in E. subst x.
    destruct rest as [|b2 rest2]; [cbn [wbrev wbytes]; rewrite bv_eqb_refl; reflexivity|].
    change (length (b2 :: rest2)) with (S (length rest2)) in *. rewrite Nat2Z.inj_succ in *.
    assert (Ea1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (rewrite word_succ_at; apply at_u; lia).
    rewrite wbytes_below; [| try change (length (b2 :: rest2)) with (S (length rest2)); rewrite ?Nat2Z.inj_succ; rewrite ?Ea1; lia | rewrite Ea1; lia].
    rewrite bv_eqb_refl. reflexivity.
  - assert (IH' : wbrev m (a + 1) rest x = wbytes m (a + 1) rest x).
    { destruct rest as [|b2 rest2]; [reflexivity|].
      change (length (b2 :: rest2)) with (S (length rest2)) in *. rewrite Nat2Z.inj_succ in *.
      assert (Ea1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (rewrite word_succ_at; apply at_u; lia).
      apply IH. try change (length (b2 :: rest2)) with (S (length rest2)). rewrite ?Nat2Z.inj_succ. rewrite ?Ea1. lia. }
    rewrite IH'.
    (* [comment removed for export] *)
    revert E. generalize (a + 1) as a1. intros a1 E.
    assert (GEN : forall l (m1 m2 : word -> option byte) (c : word), (forall y, y <> a -> m1 y = m2 y) -> forall y, y <> a -> wbytes m1 c l y = wbytes m2 c l y).
    { induction l as [|b' l' IHl]; intros m1 m2 c Hm y Hy; cbn [wbytes]; [apply Hm; exact Hy|].
      apply IHl; [|exact Hy]. intros z Hz. destruct (bv_eqb z c); [reflexivity | apply Hm; exact Hz]. }
    apply GEN.
    + intros y Hy. rewrite (bv_eqb_neq _ _ Hy). reflexivity.
    + intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

Section ALL.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.
  Hypothesis Hn63 : (n < 2 ^ 63)%Z.               (* [comment removed for export] *)

  #[local] Notation MK := (memk mem0 dst bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hlen : length bs = Z.to_nat n := Hlen _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.
  Let Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z := Hdisj _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition mm_result : word -> option byte :=
    if (bv_unsigned dst <? bv_unsigned src)%Z then wbytes mem0 dst bs else wbrev mem0 dst bs.
  Lemma mm_result_pw : forall x, mm_result x = wbytes mem0 dst bs x.
  Proof.
    intros x. unfold mm_result. destruct (bv_unsigned dst <? bv_unsigned src)%Z; [reflexivity|].
    apply wbrev_pw. rewrite Hlen. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition memb (k : Z) : word -> option byte := wbrev mem0 (at_ dst (n - k)) (skipn (Z.to_nat (n - k)) bs).

  Lemma memb_0 : memb 0 = mem0.
  Proof. unfold memb. rewrite Z.sub_0_r, skipn_all2 by (rewrite Hlen; lia). reflexivity. Qed.
  Lemma memb_n : memb n = wbrev mem0 dst bs.
  Proof. unfold memb. rewrite Z.sub_diag, at_0. reflexivity. Qed.

  Lemma memb_out : forall k (x : word), (0 <= k <= n)%Z ->
    (bv_unsigned x < bv_unsigned dst \/ bv_unsigned dst + n <= bv_unsigned x)%Z -> memb k x = mem0 x.
  Proof.
    intros k x Hk Hx. unfold memb. pose proof (u64_range dst).
    apply wbrev_out; rewrite length_skipn, Hlen, at_u; lia.
  Qed.

  Lemma rdb_src1 : forall k j, (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    rdn RSEGS (memb k) (at_ src j) 1%nat = Some [b_ bs j].
  Proof.
    intros k j Hk Hj Hj1. pose proof (u64_range src). pose proof (u64_range dst).
    rewrite (rdn_ext RSEGS 1 (memb k) mem0); [| rewrite at_u; cbn; lia |].
    - rewrite <- (memk_0 mem0 dst bs). apply (rd_src1 mem0 dst src n bs HOK); lia.
    - intros x Hx. rewrite at_u in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply memb_out; lia.
  Qed.

  Lemma wrb_dst : forall k j, (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    store_ok RSEGS (memb k) (at_ dst j) 1%nat = true.
  Proof.
    intros k j Hk Hj Hj1. apply (store_ok_mono _ _ mem0 (memb k) _ ltac:(unfold memb; apply wbrev_grows)).
    rewrite <- (memk_0 mem0 dst bs). apply (wr_dst mem0 dst src n bs HOK); lia.
  Qed.

  Lemma memb_extend1 : forall k (b : byte), (0 <= k)%Z -> (k + 1 <= n)%Z -> b = b_ bs (n - k - 1) ->
    wbytes (memb k) (at_ dst (n - k - 1)) [b] = memb (k + 1).
  Proof.
    intros k b Hk Hk1 ->. unfold memb, b_.
    replace (n - (k + 1))%Z with (n - k - 1)%Z by lia.
    rewrite (skipn_nth bs (Z.to_nat (n - k - 1)) (Z_to_bv 8 0)) by (rewrite Hlen; lia).
    cbn [wbrev]. f_equal. f_equal.
    - rewrite word_succ_at, at_at. f_equal. lia.
    - f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mb_lbu : forall regs pc w rd rs (imm : bv 12) k j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (memb k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ bs j))) (v_addi pc 4) (memb k) rom).
  Proof.
    intros regs pc w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rdb_src1; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mb_sb : forall regs pc w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = n - k - 1)%Z ->
    getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b_ bs (n - k - 1) ->
    (0 <= k)%Z -> (k + 1 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (memb k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memb (k + 1)) rom).
  Proof.
    intros regs pc w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
    rewrite <- (memb_extend1 k (b_ bs (n - k - 1))) by (lia || reflexivity).
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wrb_dst; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  (* [comment removed for export] *)
  Ltac mblbu F D jj :=
    chain_step; [reflexivity
      | eapply mb_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | unfold v_add, at_; unorm; f_equal; lia] | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mbsb F D kk valtac :=
    chain_step; [reflexivity
      | eapply mb_sb with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | unfold v_add, at_; unorm; f_equal; lia] | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac cond :=
    rwH; rewrite ?at_addi; unfold at_, v_addi, v_add, c_eq, c_ltu, c_lts, bv_eqb, bv_ltu, bv_lts; imm_norm; unorm; rewrite ?signed64_small by lia;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.

  (* [comment removed for export] *)
  Lemma floop_run : forall (q : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = at_ dst n ->
    (0 <= k)%Z -> (k + Z.of_nat q + 1 = n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x8b418 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hq;
      pose proof (u64_range src); pose proof (u64_range dst).
    - eexists. split.
      + mlbu F_8b000 D_8b000 k.                                  (* [comment removed for export] *)
        msb F_8b004 D_8b004 k ltac:(apply sb_val_plain).         (* [comment removed for export] *)
        stepn F_8b008 D_8b008.                                   (* [comment removed for export] *)
        stepn F_8b00c D_8b00c.                                   (* [comment removed for export] *)
        stepb_ft F_8b010 D_8b010 ltac:(cond).                    (* [comment removed for export] *)
        stepn F_8b014 D_8b014.                                   (* [comment removed for export] *)
        stepret F_8b044 D_8b044 ret ltac:(rwH; reflexivity).
        replace (MK (k + 1)) with (MK n) by (f_equal; lia).
        apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x8b418 : word) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = at_ dst n /\ keeps regs r)).
      + eexists. split.
        * mlbu F_8b000 D_8b000 k.
          msb F_8b004 D_8b004 k ltac:(apply sb_val_plain).
          stepn F_8b008 D_8b008.
          stepn F_8b00c D_8b00c.
          stepb_tk F_8b010 D_8b010 ltac:(cond).                  (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma bloop_run : forall (q : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 (n - k - 1) ->
    (0 <= k)%Z -> (k + Z.of_nat q + 1 = n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x8b440 : word) (memb k) rom) (mkst regs' ret (memb n) rom)
      /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k Hret H1 H10 H11 H12 H13 Hk Hq;
      pose proof (u64_range src); pose proof (u64_range dst).
    - eexists. split.
      + stepiv F_8b028 D_8b028 (at_ src (n - k - 1)) ltac:(gres; rwH; unfold v_add, at_; unorm; f_equal; lia).   (* [comment removed for export] *)
        mblbu F_8b02c D_8b02c (n - k - 1)%Z.                                                                     (* [comment removed for export] *)
        stepiv F_8b030 D_8b030 (at_ dst (n - k - 1)) ltac:(gres; rwH; unfold v_add, at_; unorm; f_equal; lia).   (* [comment removed for export] *)
        stepiv F_8b034 D_8b034 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).   (* [comment removed for export] *)
        stepn F_8b038 D_8b038.                                                                                   (* [comment removed for export] *)
        mbsb F_8b03c D_8b03c k ltac:(apply sb_val_plain).                                                       (* [comment removed for export] *)
        stepb_ft F_8b040 D_8b040 ltac:(cond).                                                                    (* [comment removed for export] *)
        stepret F_8b044 D_8b044 ret ltac:(rwH; reflexivity).
        replace (memb (k + 1)) with (memb n) by (f_equal; lia).
        apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x8b440 : word) (memb (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 1 /\ getr r 13 = Z_to_bv 64 (n - (k + 1) - 1) /\ keeps regs r)).
      + eexists. split.
        * stepiv F_8b028 D_8b028 (at_ src (n - k - 1)) ltac:(gres; rwH; unfold v_add, at_; unorm; f_equal; lia).
          mblbu F_8b02c D_8b02c (n - k - 1)%Z.
          stepiv F_8b030 D_8b030 (at_ dst (n - k - 1)) ltac:(gres; rwH; unfold v_add, at_; unorm; f_equal; lia).
          stepiv F_8b034 D_8b034 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
          stepiv F_8b038 D_8b038 (Z_to_bv 64 (n - (k + 1) - 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
          mbsb F_8b03c D_8b03c k ltac:(apply sb_val_plain).
          stepb_tk F_8b040 D_8b040 ltac:(cond).                                                                  (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R13 & K1).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R10 R11 R12 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  Theorem int_memmove_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x8b408 : word) mem0 rom) (mkst regs' ret mm_result rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12. pose proof (u64_range src) as Us; pose proof (u64_range dst) as Ud.
    unfold mm_result.
    destruct (Z.ltb_spec (bv_unsigned dst) (bv_unsigned src)) as [Hlt|Hge].
    - (* [comment removed for export] *)
      rewrite <- (memk_n mem0 dst src n bs HOK).
      replace (mkst regs (0x8b408 : word) mem0 rom) with (mkst regs (0x8b408 : word) (MK 0) rom) by reflexivity.
      destruct (Z.eq_dec n 0) as [Hz|Hz].
      + eexists. split.
        * stepb_ft F_8aff0 D_8aff0 ltac:(cond).                  (* [comment removed for export] *)
          stepb_tk F_8aff4 D_8aff4 ltac:(cond).                  (* [comment removed for export] *)
          stepret F_8b044 D_8b044 ret ltac:(rwH; reflexivity).
          replace (MK 0) with (MK n) by (f_equal; lia).
          apply mst_refl.
        * post.
      + assert (Hq : exists q : nat, (Z.of_nat q + 1 = n)%Z) by (exists (Z.to_nat (n - 1)); rewrite Z2Nat.id; lia).
        destruct Hq as (q & Hq).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x8b418 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = at_ dst n /\ keeps regs r)).
        * eexists. split.
          -- stepb_ft F_8aff0 D_8aff0 ltac:(cond).               (* [comment removed for export] *)
             stepb_ft F_8aff4 D_8aff4 ltac:(cond).               (* [comment removed for export] *)
             stepn F_8aff8 D_8aff8.                              (* [comment removed for export] *)
             stepn F_8affc D_8affc.                              (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. all: rewrite ?at_0; try reflexivity. all: unfold v_add, at_; f_equal; unorm; lia.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (floop_run q r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      rewrite <- memb_n. rewrite <- memb_0.
      destruct (Z.eq_dec n 0) as [Hz|Hz].
      + destruct (Z.eq_dec (bv_unsigned src) (bv_unsigned dst)) as [Heq|Hne].
        * eexists. split.
          -- stepb_tk F_8aff0 D_8aff0 ltac:(cond).               (* [comment removed for export] *)
             stepb_tk F_8b018 D_8b018 ltac:(cond).               (* [comment removed for export] *)
             stepret F_8b044 D_8b044 ret ltac:(rwH; reflexivity).
             replace (memb 0) with (memb n) by (f_equal; lia).
             apply mst_refl.
          -- post.
        * eexists. split.
          -- stepb_tk F_8aff0 D_8aff0 ltac:(cond).
             stepb_ft F_8b018 D_8b018 ltac:(cond).               (* [comment removed for export] *)
             stepb_tk F_8b01c D_8b01c ltac:(cond).               (* [comment removed for export] *)
             stepret F_8b044 D_8b044 ret ltac:(rwH; reflexivity).
             replace (memb 0) with (memb n) by (f_equal; lia).
             apply mst_refl.
          -- post.
      + assert (Hq : exists q : nat, (Z.of_nat q + 1 = n)%Z) by (exists (Z.to_nat (n - 1)); rewrite Z2Nat.id; lia).
        destruct Hq as (q & Hq).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x8b440 : word) (memb 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 1 /\ getr r 13 = Z_to_bv 64 (n - 0 - 1) /\ keeps regs r)).
        * eexists. split.
          -- stepb_tk F_8aff0 D_8aff0 ltac:(cond).               (* [comment removed for export] *)
             stepb_ft F_8b018 D_8b018 ltac:(cond).               (* [comment removed for export] *)
             stepb_ft F_8b01c D_8b01c ltac:(cond).               (* [comment removed for export] *)
             stepiv F_8b020 D_8b020 (Z_to_bv 64 (n - 0 - 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).   (* [comment removed for export] *)
             stepn F_8b024 D_8b024.                              (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & R13 & K1).
          destruct (bloop_run q r1 ret 0 Hret R1 R10 R11 R12 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.
End ALL.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import BothMemcpyBase BothMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VBothMuslStrLib VBothMusl_code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition strlen_clob : list reg := [10; 11; 12; 13; 14; 15; 16]%list.

(* [comment removed for export] *)
Definition hd (u : Z) : Z := ((8 - u mod 8) mod 8)%Z.
(* [comment removed for export] *)
Definition strlen_span (u I : Z) : Z :=
  if (I <? hd u)%Z then (I + 1)%Z else ((u + I) - (u + I) mod 8 + 8 - u)%Z.

Definition b_ (buf : list byte) (j : Z) : byte := nth (Z.to_nat j) buf B0.

(* [comment removed for export] *)
Definition TW0 (x : word) : word := v_and (v_or (v_sub (Z_to_bv 64 Mc) x) x) (Z_to_bv 64 Hc).
Lemma TW0_TW : forall x, TW0 x = TW x.
Proof. intros x. unfold TW0, TW. rewrite !v_xor_0. reflexivity. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma hd_facts : forall u, (0 <= u)%Z ->
  exists q, (0 <= hd u < 8)%Z /\ (u + hd u = 8 * q)%Z /\
            (forall j, (0 <= j < hd u)%Z -> ((u + j) mod 8 <> 0)%Z).
Proof.
  intros u Hu. unfold hd.
  pose proof (Z.div_mod u 8 ltac:(lia)) as E. pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as B.
  set (r := (u mod 8)%Z) in *. set (q := (u / 8)%Z) in *.
  destruct (Z.eq_dec r 0) as [Hr|Hr].
  - exists q. rewrite Hr. replace ((8 - 0) mod 8)%Z with 0%Z by reflexivity. repeat split; try lia.
  - exists (q + 1)%Z. rewrite (Z.mod_small (8 - r) 8) by lia. repeat split; lia.
Qed.

Lemma span_word : forall u I, (0 <= u)%Z -> (hd u <= I)%Z ->
  exists t, (strlen_span u I = 8 * t + 8 - u)%Z /\ (8 * t <= u + I < 8 * t + 8)%Z.
Proof.
  intros u I Hu HI. unfold strlen_span.
  replace (I <? hd u)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  exists ((u + I) / 8)%Z.
  pose proof (Z.div_mod (u + I) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (u + I) 8 ltac:(lia)).
  pose proof (hd_facts u Hu) as (q & A & B & C). lia.
Qed.

Lemma span_head : forall u I, (I < hd u)%Z -> strlen_span u I = (I + 1)%Z.
Proof. intros u I H. unfold strlen_span. replace (I <? hd u)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma strlen_span_le : forall u I, (0 <= u)%Z -> (0 <= I)%Z -> (I + 1 <= strlen_span u I <= I + 8)%Z.
Proof.
  intros u I Hu HI. pose proof (hd_facts u Hu) as (q & A & B & C).
  destruct (Z_lt_le_dec I (hd u)) as [Hl|Hl].
  - rewrite span_head by lia. lia.
  - destruct (span_word u I Hu Hl) as (t & E & R). lia.
Qed.

Lemma strlen_span_mono : forall u I K, (0 <= u)%Z -> (0 <= I <= K)%Z -> (strlen_span u I <= strlen_span u K)%Z.
Proof.
  intros u I K Hu HIK. pose proof (hd_facts u Hu) as (q & A & B & C).
  destruct (Z_lt_le_dec I (hd u)) as [Hl|Hl]; [rewrite (span_head u I) by lia|destruct (span_word u I Hu Hl) as (t & -> & R)];
  destruct (Z_lt_le_dec K (hd u)) as [Hk|Hk]; try rewrite (span_head u K) by lia;
  try destruct (span_word u K Hu Hk) as (t' & -> & R'); lia.
Qed.

(* [comment removed for export] *)
Lemma al_le : forall t t' x, (8 * t <= x < 8 * t + 8)%Z -> (8 * t' <= x)%Z -> (t' <= t)%Z.
Proof. intros; lia. Qed.
Lemma mod8_mul : forall x q, (x = 8 * q)%Z -> (x mod 2 ^ 3 = 0)%Z.
Proof. intros x q ->. change (2 ^ 3)%Z with 8%Z. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma mod8_C : forall x, ((x mod 8 <> 0) -> (x mod 2 ^ 3 =? 0) = false)%Z.
Proof. intros x H. apply Z.eqb_neq. exact H. Qed.
Lemma mod8_range : forall x, (0 <= x mod 2 ^ 3 < 2 ^ 64)%Z.
Proof. intros x. pose proof (Z.mod_pos_bound x (2 ^ 3) ltac:(lia)). lia. Qed.
Lemma hd0_mod : forall u, (0 <= u)%Z -> hd u = 0%Z -> (u mod 2 ^ 3 = 0)%Z.
Proof. intros u Hu H. unfold hd in H. change (2 ^ 3)%Z with 8%Z. pose proof (Z.mod_pos_bound u 8 ltac:(lia)).
  destruct (Z.eq_dec (u mod 8) 0) as [E|E]; [exact E|]. rewrite Z.mod_small in H by lia. lia. Qed.
Lemma hdnz_mod : forall u, (0 <= u)%Z -> hd u <> 0%Z -> ((u mod 2 ^ 3 =? 0) = false)%Z.
Proof. intros u Hu H. apply Z.eqb_neq. intros E. apply H. unfold hd. change (2 ^ 3)%Z with 8%Z in E.
  rewrite E. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma first_zero : forall (buf : list byte) (n : nat),
  bv_unsigned (nth n buf B0) = 0%Z ->
  exists i : nat, (i <= n)%nat /\ bv_unsigned (nth i buf B0) = 0%Z
                  /\ forall j : nat, (j < i)%nat -> bv_unsigned (nth j buf B0) <> 0%Z.
Proof.
  intros buf n. induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros Hz.
  destruct (existsb (fun j => (bv_unsigned (nth j buf B0) =? 0)%Z) (seq 0 n)) eqn:E.
  - apply existsb_exists in E as (j & Hj & Ej). apply in_seq in Hj. apply Z.eqb_eq in Ej.
    destruct (IH j ltac:(lia) Ej) as (i & Hi & Zi & NZ). exists i. repeat split; try assumption. lia.
  - exists n. repeat split; [lia | exact Hz |]. intros j Hj Zj.
    assert (existsb (fun j => (bv_unsigned (nth j buf B0) =? 0)%Z) (seq 0 n) = true); [|congruence].
    apply existsb_exists. exists j. split; [apply in_seq; lia | apply Z.eqb_eq; exact Zj].
Qed.

(* [comment removed for export] *)
Record slH (mem : word -> option byte) (s : word) (buf : list byte) (K : Z) : Prop := SLH {
  Hbuf : rdn SEGS mem s (length buf) = Some buf;
  Hspan : (strlen_span (bv_unsigned s) K <= Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (b_ buf K) = 0%Z;
  Hro  : rodata_clear mem }.

(* [comment removed for export] *)
Lemma slH_of_window : forall mem (s : word) (buf : list byte) (K : Z),
  rdn SEGS mem s (length buf) = Some buf ->
  (0 <= K)%Z -> (K + 8 <= Z.of_nat (length buf))%Z ->
  (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z ->
  bv_unsigned (b_ buf K) = 0%Z -> rodata_clear mem ->
  slH mem s buf K.
Proof.
  intros mem s buf K Hb HK HL Hnw Hz Hro. pose proof (u64_range s).
  pose proof (strlen_span_le (bv_unsigned s) K ltac:(lia) HK).
  constructor; try assumption. lia.
Qed.

Section SL.
  Variable mem : word -> option byte.
  Variable s : word.
  Variable buf : list byte.
  Variable K : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : slH mem s buf K.

  #[local] Notation L := (Z.of_nat (length buf)).
  #[local] Notation u := (bv_unsigned s).
  #[local] Notation B j := (b_ buf j).
  Definition sb_ (j : Z) (m : nat) : list byte := sub buf (Z.to_nat j) m.

  Let Hbuf := Hbuf _ _ _ _ HOK.
  Let Hspan : (strlen_span u K <= L)%Z := Hspan _ _ _ _ HOK.
  Let Hnw : (u + L < 2 ^ 64)%Z := Hnw _ _ _ _ HOK.
  Let HK0 : (0 <= K)%Z := HK0 _ _ _ _ HOK.
  Let Hro := Hro _ _ _ _ HOK.

  #[using="K HOK Hbuf"] Lemma rd_w : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z ->
    rdn SEGS mem (at_ s j) m = Some (sb_ j m).
  Proof.
    intros j m Hj Hm. unfold sb_.
    replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
    apply (rdn_sub SEGS mem (length buf)); [exact Hbuf | lia].
  Qed.

  #[using="K HOK Hbuf"] Lemma rd_b : forall j, (0 <= j)%Z -> (j + 1 <= L)%Z -> rdn SEGS mem (at_ s j) 1 = Some [B j].
  Proof.
    intros j Hj H1. rewrite (rd_w j 1) by lia. unfold sb_, b_. rewrite sub_nth; [reflexivity | lia].
  Qed.

  #[using="Type"] Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z -> length (sb_ j m) = m.
  Proof. intros j m Hj Hm. unfold sb_. apply sub_length. lia. Qed.

  #[using="Type"] Lemma sb_nth : forall j (i : nat), (0 <= j)%Z -> (i < 8)%nat -> (j + 8 <= L)%Z ->
    nth i (sb_ j 8) B0 = B (j + Z.of_nat i).
  Proof. intros j i Hj Hi H8. unfold sb_, b_. rewrite nth_sub by lia. f_equal. lia. Qed.

  #[using="K HOK Hbuf"] Lemma m_lbu : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 1 <= L)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (B j))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_b; lia.
  Qed.

  #[using="K HOK Hbuf"] Lemma m_ld : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 8 <= L)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sb_ j 8))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj8.
    eapply step_ld; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_w j 8); lia.
    - symmetry. apply u_LDv. apply sb_len; lia.
  Qed.

  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply m_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mld F D jj :=
    chain_step; [reflexivity
      | eapply m_ld with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac ldc F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (apply bv_eq; vm_compute; reflexivity) end end;
          exact RD
        | assumption ]
      | step_simpl]; vnorm.
  Ltac cond := try unfold v_addi; cond_lia.
  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia);
               try (unfold v_addi; unorm; f_equal; lia).

  Section FIRST.
    (* [comment removed for export] *)
    Variable I : Z.
    Hypothesis HI : (0 <= I <= K)%Z.
    Hypothesis Hz : bv_unsigned (B I) = 0%Z.
    Hypothesis Hnz : forall j, (0 <= j < I)%Z -> bv_unsigned (B j) <> 0%Z.

    #[using="mem K HOK Hspan HI"] Lemma IL : (strlen_span u I <= L)%Z.
    Proof.
      pose proof (u64_range s). pose proof (strlen_span_mono u I K ltac:(lia) HI). clear -H H0 Hspan. lia.
    Qed.
    #[using="mem s K HOK Hspan HI"] Lemma IL1 : (I + 1 <= L)%Z.
    Proof. pose proof (u64_range s). pose proof IL. pose proof (strlen_span_le u I ltac:(lia) ltac:(lia)). lia. Qed.

    Ltac condb :=
      rwH; rewrite c_eq_LBv_0;
      first [ apply Z.eqb_eq; rewrite <- Hz; f_equal; unfold b_; f_equal; lia
            | apply Z.eqb_neq; apply Hnz; lia ].
    Ltac condw lem :=
      rwH;
      lazymatch goal with |- c_eq (v_and (v_or (v_sub _ ?x) _) _) _ = ?b =>
        change (c_eq (TW0 x) (Z_to_bv 64 Hc) = b); rewrite TW0_TW end;
      apply lem; lia.

    (* [comment removed for export] *)
    #[using="mem buf K HOK Hspan Hnw HI"] Lemma ret_val : v_sub (at_ s I) s = Z_to_bv 64 I.
    Proof.
      pose proof (u64_range s). pose proof IL1. unfold v_sub. rewrite at_u by lia. f_equal. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="K HOK Hbuf Hspan Hnw HI Hz Hnz"] Lemma t_loop : forall (n : nat) regs (ret : word) p,
      (Z.of_nat n = I - p)%Z -> (0 <= p <= I)%Z ->
      (forall j, (0 <= j < p)%Z -> bv_unsigned (B j) <> 0%Z) ->
      ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
      getr regs 12 = at_ s p -> getr regs 11 = at_ s (p - 1) ->
      exists regs',
        msteps SEGS (mkst regs (0xa2ea8 : word) mem rom) (mkst regs' ret mem rom)
        /\ regs_agree (fun x => In x strlen_clob) regs regs' /\ getr regs' 10 = Z_to_bv 64 I.
    Proof.
      pose proof IL1 as HIL. pose proof (u64_range s).
      induction n as [|n IH]; intros regs ret p Hn Hp Hpre Hret H1 H10 H12 H11.
      - assert (p = I) by lia. subst p.
        eexists. split; [|split].
        + mlbu F_a2ea8 D_a2ea8 I.                    (* [comment removed for export] *)
          stepn F_a2eac D_a2eac.                     (* [comment removed for export] *)
          stepn F_a2eb0 D_a2eb0.                     (* [comment removed for export] *)
          stepb_ft F_a2eb4 D_a2eb4 ltac:(condb).     (* [comment removed for export] *)
          stepn F_a2eb8 D_a2eb8.                     (* [comment removed for export] *)
          stepret F_a2ebc D_a2ebc ret ltac:(rwH; reflexivity). apply mst_refl.
        + unfold strlen_clob. solve_regs_agree.
        + gres. rwH. rewrite at_addi. replace (I - 1 + 1)%Z with I by lia. apply ret_val.
      - eapply (runs_trans SEGS _ (fun r => mkst r (0xa2ea8 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (p + 1) /\ getr r 11 = at_ s (p + 1 - 1)
                           /\ regs_agree (fun x => In x strlen_clob) regs r)).
        + eexists. split.
          * mlbu F_a2ea8 D_a2ea8 p.
            stepn F_a2eac D_a2eac.
            stepn F_a2eb0 D_a2eb0.
            stepb_tk F_a2eb4 D_a2eb4 ltac:(condb).   (* [comment removed for export] *)
            apply mst_refl.
          * post. unfold strlen_clob. solve_regs_agree.
        + cbv beta. intros r1 (R1 & R10 & R12 & R11 & AG).
          destruct (IH r1 ret (p + 1)%Z ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & V); try assumption.
          { intros j Hj. destruct (Z.eq_dec j p) as [->|]; [apply Hnz; lia | apply Hpre; lia]. }
          exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact V]].
    Qed.

    (* [comment removed for export] *)
    #[using="Hz Hnz"] Lemma tw_hit : forall j, (0 <= j <= I)%Z -> (I < j + 8)%Z -> (j + 8 <= L)%Z ->
      c_eq (TW (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = false.
    Proof.
      intros j Hj HIj HL.
      apply (TW_haszero _ (Z.to_nat (I - j))).
      - apply sb_len; lia.
      - lia.
      - rewrite sb_nth by lia. rewrite <- Hz. f_equal. unfold b_. f_equal. lia.
      - intros jj Hjj. rewrite sb_nth by lia. apply Hnz. lia.
    Qed.

    #[using="Hnz"] Lemma tw_miss : forall j, (0 <= j)%Z -> (j + 8 <= I)%Z -> (j + 8 <= L)%Z ->
      c_eq (TW (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = true.
    Proof.
      intros j Hj HIj HL. apply TW_nozero.
      - apply sb_len; lia.
      - intros i Hi. rewrite sb_nth by lia. apply Hnz. lia.
    Qed.

    #[using="K HOK Hbuf Hspan Hnw HI Hz Hnz"] Lemma w_loop : forall (n : nat) regs (ret : word) ow t,
      (Z.of_nat n = (I - ow) / 8)%Z -> (0 <= ow <= I)%Z -> (u + ow = 8 * t)%Z -> (hd u <= I)%Z ->
      (forall j, (0 <= j < ow)%Z -> bv_unsigned (B j) <> 0%Z) ->
      ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
      getr regs 12 = at_ s (ow - 8) -> getr regs 11 = at_ s (ow - 9) ->
      getr regs 13 = Z_to_bv 64 Mc -> getr regs 14 = Z_to_bv 64 Hc ->
      exists regs',
        msteps SEGS (mkst regs (0xa2e8c : word) mem rom) (mkst regs' ret mem rom)
        /\ regs_agree (fun x => In x strlen_clob) regs regs' /\ getr regs' 10 = Z_to_bv 64 I.
    Proof.
      pose proof IL as HIL. pose proof (u64_range s) as Hs.
      induction n as [|n IH]; intros regs ret ow t Hn How Ht Hh Hpre Hret H1 H10 H12 H11 H13 H14;
        destruct (span_word u I ltac:(lia) Hh) as (tI & EI & RI);
        pose proof (al_le tI t (u + I) RI ltac:(lia)) as Htle;
        assert (HR : (ow + 8 <= L)%Z) by (clear Hpre; lia).
      - (* [comment removed for export] *)
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (HI8 : (I < ow + 8)%Z) by (clear -Hn How; lia).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        eapply (runs_trans SEGS _ (fun r => mkst r (0xa2ea8 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s ow /\ getr r 11 = at_ s (ow - 1)
                           /\ regs_agree (fun x => In x strlen_clob) regs r)).
        + eexists. split.
          * mld F_a2e8c D_a2e8c ow.                  (* [comment removed for export] *)
            stepn F_a2e90 D_a2e90.                   (* [comment removed for export] *)
            stepn F_a2e94 D_a2e94.                   (* [comment removed for export] *)
            stepn F_a2e98 D_a2e98.                   (* [comment removed for export] *)
            stepn F_a2e9c D_a2e9c.                   (* [comment removed for export] *)
            stepn F_a2ea0 D_a2ea0.                   (* [comment removed for export] *)
            stepb_ft F_a2ea4 D_a2ea4 ltac:(condw tw_hit).   (* [comment removed for export] *)
            apply mst_refl.
          * post. unfold strlen_clob. solve_regs_agree.
        + cbv beta. intros r1 (R1 & R10 & R12 & R11 & AG).
          destruct (t_loop (Z.to_nat (I - ow)) r1 ret ow ltac:(lia) ltac:(lia) Hpre Hret R1 R10 R12 R11) as (r2 & RUN & AG2 & V).
          exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact V]].
      - (* [comment removed for export] *)
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (HI8 : (ow + 8 <= I)%Z) by (clear -Hn How; lia).
        assert (Hn' : (Z.of_nat n = (I - (ow + 8)) / 8)%Z) by (clear -Hn How HI8; lia).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        eapply (runs_trans SEGS _ (fun r => mkst r (0xa2e8c : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (ow + 8 - 8) /\ getr r 11 = at_ s (ow + 8 - 9)
                           /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                           /\ regs_agree (fun x => In x strlen_clob) regs r)).
        + eexists. split.
          * mld F_a2e8c D_a2e8c ow.
            stepn F_a2e90 D_a2e90.
            stepn F_a2e94 D_a2e94.
            stepn F_a2e98 D_a2e98.
            stepn F_a2e9c D_a2e9c.
            stepn F_a2ea0 D_a2ea0.
            stepb_tk F_a2ea4 D_a2ea4 ltac:(condw tw_miss).  (* [comment removed for export] *)
            apply mst_refl.
          * post. unfold strlen_clob. solve_regs_agree.
        + cbv beta. intros r1 (R1 & R10 & R12 & R11 & R13 & R14 & AG).
          destruct (IH r1 ret (ow + 8)%Z (t + 1)%Z Hn' ltac:(lia) ltac:(lia) Hh) as (r2 & RUN & AG2 & V); try assumption.
          { intros j Hj. destruct (Z_lt_le_dec j ow) as [Hl|Hl]; [apply Hpre; lia | apply Hnz; lia]. }
          exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact V]].
    Qed.

    (* [comment removed for export] *)
    #[using="K HOK Hbuf Hspan Hnw Hro HI Hz Hnz"] Lemma w_setup : forall regs (ret : word) q,
      (hd u <= I)%Z -> (u + hd u = 8 * q)%Z ->
      (forall j, (0 <= j < hd u)%Z -> bv_unsigned (B j) <> 0%Z) ->
      ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s (hd u) ->
      exists regs',
        msteps SEGS (mkst regs (0xa2e74 : word) mem rom) (mkst regs' ret mem rom)
        /\ regs_agree (fun x => In x strlen_clob) regs regs' /\ getr regs' 10 = Z_to_bv 64 I.
    Proof.
      intros regs ret q Hh Hq Hpre Hret H1 H10 H12.
      pose proof (u64_range s) as Hs. pose proof (hd_facts u ltac:(lia)) as (q' & A & Bq & C).
      destruct (rd_const_M mem Hro) as (bsM & RM & EM).
      destruct (rd_const_H mem Hro) as (bsH & RH & EH).
      eapply (runs_trans SEGS _ (fun r => mkst r (0xa2e8c : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (hd u - 8) /\ getr r 11 = at_ s (hd u - 9)
                         /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                         /\ regs_agree (fun x => In x strlen_clob) regs r)).
      - eexists. split.
        + stepn F_a2e74 D_a2e74.                     (* [comment removed for export] *)
          stepn F_a2e78 D_a2e78.                     (* [comment removed for export] *)
          ldc F_a2e7c D_a2e7c (Z_to_bv 64 Mc) RM.    (* [comment removed for export] *)
          ldc F_a2e80 D_a2e80 (Z_to_bv 64 Hc) RH.    (* [comment removed for export] *)
          stepn F_a2e84 D_a2e84.                     (* [comment removed for export] *)
          stepn F_a2e88 D_a2e88.                     (* [comment removed for export] *)
          apply mst_refl.
        + post. unfold strlen_clob. solve_regs_agree.
      - cbv beta. intros r1 (R1 & R10 & R12 & R11 & R13 & R14 & AG).
        destruct (w_loop (Z.to_nat ((I - hd u) / 8)) r1 ret (hd u) q
                    ltac:(clear -Hh; pose proof (Z.div_pos (I - hd u) 8); lia) ltac:(lia) Hq Hh Hpre Hret R1 R10 R12 R11 R13 R14)
          as (r2 & RUN & AG2 & V).
        exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact V]].
    Qed.

    (* [comment removed for export] *)
    #[using="K HOK Hbuf Hspan Hnw Hro HI Hz Hnz"] Lemma h_loop : forall (n : nat) regs (ret : word) j q,
      (Z.of_nat n = hd u - 1 - j)%Z -> (0 <= j)%Z -> (j + 1 <= hd u)%Z -> (u + hd u = 8 * q)%Z ->
      (forall jj, (0 <= jj <= j)%Z -> bv_unsigned (B jj) <> 0%Z) ->
      ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
      getr regs 11 = at_ s j -> getr regs 12 = at_ s (j + 1) ->
      exists regs',
        msteps SEGS (mkst regs (0xa2e54 : word) mem rom) (mkst regs' ret mem rom)
        /\ regs_agree (fun x => In x strlen_clob) regs regs' /\ getr regs' 10 = Z_to_bv 64 I.
    Proof.
      pose proof IL1 as HIL. pose proof (u64_range s) as Hs. pose proof (hd_facts u ltac:(lia)) as (q' & A & Bq & C).
      induction n as [|n IH]; intros regs ret j q Hn Hj Hjh Hq Hpre Hret H1 H10 H11 H12.
      - (* [comment removed for export] *)
        assert (Hj1 : (j + 1 = hd u)%Z) by lia.
        assert (HjI : (j < I)%Z).
        { destruct (Z_lt_le_dec j I) as [|Hge]; [assumption|]. exfalso. apply (Hpre I); [lia | exact Hz]. }
        eapply (runs_trans SEGS _ (fun r => mkst r (0xa2e74 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (hd u)
                           /\ regs_agree (fun x => In x strlen_clob) regs r)).
        + eexists. split.
          * stepn F_a2e54 D_a2e54.                   (* [comment removed for export] *)
            stepiv F_a2e58 D_a2e58 (Z_to_bv 64 0)
              ltac:(gres; rwH; rewrite at_addi; imm_norm; unfold v_andi, at_; unorm;
                    change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; f_equal;
                    apply (mod8_mul _ q); lia).   (* [comment removed for export] *)
            stepb_tk F_a2e5c D_a2e5c ltac:(cond_lia).   (* [comment removed for export] *)
            apply mst_refl.
          * post. unfold strlen_clob. solve_regs_agree.
        + cbv beta. intros r1 (R1 & R10 & R12 & AG).
          destruct (w_setup r1 ret q ltac:(lia) Hq) as (r2 & RUN & AG2 & V); try assumption.
          { intros jj Hjj. apply Hpre. lia. }
          exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact V]].
      - (* [comment removed for export] *)
        assert (HjI : (j < I)%Z).
        { destruct (Z_lt_le_dec j I) as [|Hge]; [assumption|]. exfalso. apply (Hpre I); [lia | exact Hz]. }
        destruct (Z.eq_dec (j + 1) I) as [HjI1|HjI1].
        + (* [comment removed for export] *)
          eexists. split; [|split].
          * stepn F_a2e54 D_a2e54.                   (* [comment removed for export] *)
            stepn F_a2e58 D_a2e58.                   (* [comment removed for export] *)
            stepb_ft F_a2e5c D_a2e5c
              ltac:(rwH; rewrite at_addi; unfold c_eq, bv_eqb, v_andi, at_; unorm;
                    change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia;
                    pose proof (mod8_range (bv_unsigned s + (j + 1))); unorm;
                    apply mod8_C; apply (C (j + 1)%Z); lia).   (* [comment removed for export] *)
            mlbu F_a2e60 D_a2e60 (j + 1)%Z.          (* [comment removed for export] *)
            stepn F_a2e64 D_a2e64.                   (* [comment removed for export] *)
            stepn F_a2e68 D_a2e68.                   (* [comment removed for export] *)
            stepb_ft F_a2e6c D_a2e6c ltac:(condb).   (* [comment removed for export] *)
            stepn F_a2e70 D_a2e70.                   (* [comment removed for export] *)
            stepn F_a2eb8 D_a2eb8.                   (* [comment removed for export] *)
            stepret F_a2ebc D_a2ebc ret ltac:(rwH; reflexivity). apply mst_refl.
          * unfold strlen_clob. solve_regs_agree.
          * gres. rwH. rewrite at_addi. rewrite HjI1. apply ret_val.
        + eapply (runs_trans SEGS _ (fun r => mkst r (0xa2e54 : word) mem rom)
                   (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s (j + 1) /\ getr r 12 = at_ s (j + 1 + 1)
                             /\ regs_agree (fun x => In x strlen_clob) regs r)).
          * eexists. split.
            -- stepn F_a2e54 D_a2e54.
               stepn F_a2e58 D_a2e58.
               stepb_ft F_a2e5c D_a2e5c
                 ltac:(rwH; rewrite at_addi; unfold c_eq, bv_eqb, v_andi, at_; unorm;
                       change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia;
                       pose proof (mod8_range (bv_unsigned s + (j + 1))); unorm;
                       apply mod8_C; apply (C (j + 1)%Z); lia).
               mlbu F_a2e60 D_a2e60 (j + 1)%Z.
               stepn F_a2e64 D_a2e64.
               stepn F_a2e68 D_a2e68.
               stepb_tk F_a2e6c D_a2e6c ltac:(condb).   (* [comment removed for export] *)
               apply mst_refl.
            -- post. unfold strlen_clob. solve_regs_agree.
          * cbv beta. intros r1 (R1 & R10 & R11 & R12 & AG).
            destruct (IH r1 ret (j + 1)%Z q ltac:(lia) ltac:(lia) ltac:(lia) Hq) as (r2 & RUN & AG2 & V); try assumption.
            { intros jj Hjj. destruct (Z.eq_dec jj (j + 1)) as [->|]; [apply Hnz; lia | apply Hpre; lia]. }
            exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact V]].
    Qed.

    (* [comment removed for export] *)
    #[using="buf K HOK Hbuf Hspan Hnw Hro HI Hz Hnz"] Lemma sl_main : forall regs (ret : word),
      ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
      exists regs',
        msteps SEGS (mkst regs (0xa2e38 : word) mem rom) (mkst regs' ret mem rom)
        /\ regs_agree (fun x => In x strlen_clob) regs regs' /\ getr regs' 10 = Z_to_bv 64 I.
    Proof.
      intros regs ret Hret H1 H10.
      pose proof IL1 as HIL. pose proof (u64_range s) as Hs. pose proof (hd_facts u ltac:(lia)) as (q & A & Bq & C).
      destruct (Z.eq_dec (hd u) 0) as [Hh0|Hh0].
      - (* [comment removed for export] *)
        eapply (runs_trans SEGS _ (fun r => mkst r (0xa2e74 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (hd u)
                           /\ regs_agree (fun x => In x strlen_clob) regs r)).
        + eexists. split.
          * stepiv F_a2e38 D_a2e38 (Z_to_bv 64 0)
              ltac:(gres; rwH; imm_norm; unfold v_andi; change (bv_wrap 64 7) with (Z.ones 3);
                    rewrite Z.land_ones by lia; f_equal; apply hd0_mod; lia).   (* [comment removed for export] *)
            stepn F_a2e3c D_a2e3c.                   (* [comment removed for export] *)
            stepb_tk F_a2e40 D_a2e40 ltac:(cond_lia).   (* [comment removed for export] *)
            apply mst_refl.
          * post; try (rewrite Hh0, at_0; reflexivity). unfold strlen_clob. solve_regs_agree.
        + cbv beta. intros r1 (R1 & R10 & R12 & AG).
          destruct (w_setup r1 ret q ltac:(lia) Bq ltac:(intros; lia) Hret R1 R10 R12) as (r2 & RUN & AG2 & V).
          exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact V]].
      - (* [comment removed for export] *)
        destruct (Z.eq_dec I 0) as [HI0|HI0].
        + eexists. split; [|split].
          * stepn F_a2e38 D_a2e38.                   (* [comment removed for export] *)
            stepn F_a2e3c D_a2e3c.                   (* [comment removed for export] *)
            stepb_ft F_a2e40 D_a2e40
              ltac:(rwH; unfold c_eq, bv_eqb, v_andi; change (bv_wrap 64 7) with (Z.ones 3);
                    rewrite Z.land_ones by lia; pose proof (mod8_range (bv_unsigned s)); unorm;
                    apply hdnz_mod; lia).
            chain_step; [reflexivity
              | eapply m_lbu with (j := 0%Z);
                [exact F_a2e44 | reflexivity | exact D_a2e44 | gres; rwH; symmetry; apply at_0 | imm_norm; lia | lia | lia]
              | step_simpl]; vnorm.                   (* [comment removed for export] *)
            stepb_tk F_a2e48 D_a2e48
              ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_eq; replace (B 0) with (B I) by (rewrite HI0; reflexivity); exact Hz).
                                                     (* [comment removed for export] *)
            stepn F_a2ec0 D_a2ec0.                   (* [comment removed for export] *)
            stepret F_a2ec4 D_a2ec4 ret ltac:(rwH; reflexivity). apply mst_refl.
          * unfold strlen_clob. solve_regs_agree.
          * gres. rwH. rewrite HI0. unfold v_sub. f_equal. lia.
        + eapply (runs_trans SEGS _ (fun r => mkst r (0xa2e54 : word) mem rom)
                   (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s 0 /\ getr r 12 = at_ s (0 + 1)
                             /\ regs_agree (fun x => In x strlen_clob) regs r)).
          * eexists. split.
            -- stepn F_a2e38 D_a2e38.
               stepn F_a2e3c D_a2e3c.
               stepb_ft F_a2e40 D_a2e40
                 ltac:(rwH; unfold c_eq, bv_eqb, v_andi; change (bv_wrap 64 7) with (Z.ones 3);
                       rewrite Z.land_ones by lia; pose proof (mod8_range (bv_unsigned s)); unorm;
                       apply hdnz_mod; lia).
               chain_step; [reflexivity
                 | eapply m_lbu with (j := 0%Z);
                   [exact F_a2e44 | reflexivity | exact D_a2e44 | gres; rwH; symmetry; apply at_0 | imm_norm; lia | lia | lia]
                 | step_simpl]; vnorm.
               stepb_ft F_a2e48 D_a2e48 ltac:(condb).   (* [comment removed for export] *)
               stepn F_a2e4c D_a2e4c.                   (* [comment removed for export] *)
               stepn F_a2e50 D_a2e50.                   (* [comment removed for export] *)
               apply mst_refl.
            -- post; try (rewrite ?at_0; reflexivity); try (unfold at_; rewrite ?v_addi_0; f_equal; lia).
               all: try (unfold strlen_clob; solve_regs_agree).
          * cbv beta. intros r1 (R1 & R10 & R11 & R12 & AG).
            destruct (h_loop (Z.to_nat (hd u - 1)) r1 ret 0%Z q ltac:(lia) ltac:(lia) ltac:(lia) Bq) as (r2 & RUN & AG2 & V); try assumption.
            { intros jj Hjj. apply Hnz. lia. }
            exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact V]].
    Qed.
  End FIRST.

  #[using="HOK Hbuf Hspan Hnw HK0 Hro"] Theorem ref_strlen : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
    exists regs' (i : Z),
      msteps SEGS (mkst regs (0xa2e38 : word) mem rom) (mkst regs' ret mem rom)
      /\ regs_agree (fun x => In x strlen_clob) regs regs'
      /\ (0 <= i <= K)%Z /\ bv_unsigned (B i) = 0%Z
      /\ (forall j, (0 <= j < i)%Z -> bv_unsigned (B j) <> 0%Z)
      /\ getr regs' 10 = Z_to_bv 64 i.
  Proof.
    intros regs ret Hret H1 H10.
    destruct (first_zero buf (Z.to_nat K) (Hzero _ _ _ _ HOK)) as (i & Hi & Zi & NZi).
    destruct (sl_main (Z.of_nat i) ltac:(lia) ltac:(unfold b_; rewrite Nat2Z.id; exact Zi)
                ltac:(intros j Hj; unfold b_; apply NZi; lia) regs ret Hret H1 H10) as (r2 & RUN & AG & V).
    exists r2, (Z.of_nat i). repeat split; try assumption; try lia.
    - unfold b_. rewrite Nat2Z.id. exact Zi.
    - intros j Hj. unfold b_. apply NZi. lia.
  Qed.
End SL.

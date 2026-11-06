(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bsub (a b : Z) : Prop := forall i, 0 <= i -> Z.testbit a i = true -> Z.testbit b i = true.

Lemma bsub_refl : forall a, bsub a a.
Proof. intros a i _ H. exact H. Qed.

Lemma bsub_trans : forall a b c, bsub a b -> bsub b c -> bsub a c.
Proof. intros a b c H1 H2 i Hi Ha. apply H2; [exact Hi|]. apply H1; assumption. Qed.

Lemma bsub_lor : forall a b c d, bsub a b -> bsub c d -> bsub (Z.lor a c) (Z.lor b d).
Proof.
  intros a b c d H1 H2 i Hi H. rewrite Z.lor_spec in *. apply orb_true_iff in H as [H|H].
  - rewrite (H1 i Hi H). reflexivity.
  - rewrite (H2 i Hi H). apply orb_true_r.
Qed.

Lemma bsub_shiftr : forall a b k, 0 <= k -> bsub a b -> bsub (Z.shiftr a k) (Z.shiftr b k).
Proof.
  intros a b k Hk H i Hi Ha. rewrite Z.shiftr_spec in * by lia. apply H; [lia | exact Ha].
Qed.

Lemma bsub_antisym : forall a b, bsub a b -> bsub b a -> a = b.
Proof.
  intros a b H1 H2. apply Z.bits_inj'. intros i Hi.
  destruct (Z.testbit a i) eqn:Ea.
  - symmetry. exact (H1 i Hi Ea).
  - destruct (Z.testbit b i) eqn:Eb; [|reflexivity]. rewrite (H2 i Hi Eb) in Ea. discriminate.
Qed.

Definition zsm1 (a k : Z) : Z := Z.lor a (Z.shiftr a k).
Fixpoint zsm (a : Z) (ks : list Z) : Z :=
  match ks with [] => a | k :: ks' => zsm (zsm1 a k) ks' end.

Lemma bsub_zsm : forall ks a b, Forall (fun k => 0 <= k) ks -> bsub a b -> bsub (zsm a ks) (zsm b ks).
Proof.
  induction ks as [|k ks IH]; intros a b Hks H; cbn [zsm]; [exact H|].
  inversion Hks; subst. apply IH; [assumption|]. unfold zsm1. apply bsub_lor; [exact H|]. apply bsub_shiftr; assumption.
Qed.

Lemma testbit_true_ge : forall y i, 0 <= y -> 0 <= i -> Z.testbit y i = true -> 2 ^ i <= y.
Proof.
  intros y i Hy Hi H. apply Z.testbit_true in H; [|exact Hi].
  assert (Hp : 0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.lt_ge_cases y (2 ^ i)) as [Hlt|Hge]; [|exact Hge].
  rewrite Z.div_small in H by lia. cbn in H. discriminate.
Qed.

Lemma bsub_range_ones : forall y n, 0 <= n -> 0 <= y < 2 ^ n -> bsub y (Z.ones n).
Proof.
  intros y n Hn Hy i Hi H. pose proof (testbit_true_ge y i ltac:(lia) Hi H) as G.
  destruct (Z.lt_ge_cases i n) as [Hl|Hge].
  - rewrite Z.ones_spec_low; [reflexivity | lia].
  - exfalso. assert (2 ^ n <= 2 ^ i) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma bsub_pow2 : forall y n, 0 <= n -> 2 ^ n <= y < 2 ^ (n + 1) -> bsub (2 ^ n) y.
Proof.
  intros y n Hn Hy i Hi H. rewrite Z.pow2_bits_eqb in H by lia. apply Z.eqb_eq in H. subst i.
  apply Z.testbit_true; [lia|]. rewrite Z.pow_add_r in Hy by lia. change (2 ^ 1) with 2 in Hy.
  assert (Hp : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  replace (y / 2 ^ n) with 1; [reflexivity|].
  apply (Z.div_unique y (2 ^ n) 1 (y - 2 ^ n)); lia.
Qed.

Lemma zsm_nonneg : forall ks a, 0 <= a -> Forall (fun k => 0 <= k) ks -> 0 <= zsm a ks.
Proof.
  induction ks as [|k ks IH]; intros a Ha Hks; cbn [zsm]; [exact Ha|].
  inversion Hks; subst. apply IH; [|assumption]. unfold zsm1. apply Z.lor_nonneg. split; [exact Ha|].
  apply Z.shiftr_nonneg. exact Ha.
Qed.

(* [comment removed for export] *)
Definition SM_KS : list Z := [1; 2; 4; 8; 16].

Lemma zsm_lo_val : Z.shiftr (zsm (2 ^ 46) SM_KS) 15 = 2 ^ 32 - 1.
Proof. vm_compute. reflexivity. Qed.
Lemma zsm_hi_val : Z.shiftr (zsm (Z.ones 47) SM_KS) 15 = 2 ^ 32 - 1.
Proof. vm_compute. reflexivity. Qed.

Theorem smear15 : forall y, 2 ^ 46 <= y < 2 ^ 47 -> Z.shiftr (zsm y SM_KS) 15 = 2 ^ 32 - 1.
Proof.
  intros y Hy.
  assert (KS : Forall (fun k => 0 <= k) SM_KS) by (repeat constructor; cbn; lia).
  assert (L : bsub (Z.shiftr (zsm (2 ^ 46) SM_KS) 15) (Z.shiftr (zsm y SM_KS) 15)).
  { apply bsub_shiftr; [lia|]. apply bsub_zsm; [exact KS|]. apply (bsub_pow2 y 46); [lia|].
    change (46 + 1) with 47. exact Hy. }
  assert (U : bsub (Z.shiftr (zsm y SM_KS) 15) (Z.shiftr (zsm (Z.ones 47) SM_KS) 15)).
  { apply bsub_shiftr; [lia|]. apply bsub_zsm; [exact KS|]. apply bsub_range_ones; lia. }
  rewrite zsm_lo_val in L. rewrite zsm_hi_val in U. symmetry. apply bsub_antisym; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint esm (e : expr) (ks : list Z) : expr :=
  match ks with [] => e | k :: ks' => esm (EAlu ALU_OR e (EAlu ALU_SRL e (ELit k))) ks' end.

Lemma edenot_esm : forall E ks e,
  Forall (fun k => 0 <= k < 64) ks ->
  bv_unsigned (edenot E (esm e ks)) = zsm (bv_unsigned (edenot E e)) ks.
Proof.
  intros E ks. induction ks as [|k ks IH]; intros e Hks; cbn [esm zsm]; [reflexivity|].
  inversion Hks as [|k' ks' Hk Hks']; subst. rewrite (IH _ Hks'). f_equal.
  cbn [edenot]. unfold zsm1. rewrite u_or64, u_srl64. f_equal.
  cbn [edenot]. rewrite u_lit64, two64_eq, (Z.mod_small k) by lia. rewrite (Z.mod_small k) by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition smear_reg (xe : expr) : expr :=
  EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EAlu ALU_SRL (esm xe SM_KS) (ELit 15))) (ELit 32767).

Theorem smear_reg_val : forall E xe,
  2 ^ 46 <= bv_unsigned (edenot E xe) < 2 ^ 47 ->
  edenot E (smear_reg xe) = Z_to_bv 64 (2 ^ 47 - 1).
Proof.
  intros E xe Hx. apply bv_eq. unfold smear_reg. cbn [edenot].
  rewrite u_add64, u_mul64, u_srl64.
  rewrite (edenot_esm E SM_KS xe) by (repeat constructor; cbn; lia).
  change (bv_unsigned (Z_to_bv 64 32768)) with 32768. change (bv_unsigned (Z_to_bv 64 32767)) with 32767.
  change (bv_unsigned (Z_to_bv 64 15) mod 64) with 15.
  rewrite <- Z.shiftr_div_pow2 by lia. rewrite (smear15 _ Hx). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kimg_cut1 (lo hi : Z) (K : kentry) : list kentry :=
  match K with
  | KImg a b =>
      if ((hi <=? a) || (b <=? lo))%Z then [K]
      else (if (a <? lo)%Z then [KImg a lo] else []) ++ (if (hi <? b)%Z then [KImg hi b] else [])
  | _ => [K]
  end.

Definition kimg_cut (lo hi : Z) (kn : list kentry) : list kentry := flat_map (kimg_cut1 lo hi) kn.

Lemma know_kimg_cut : forall segs E M lo hi kn,
  know_ok segs E M kn -> know_ok segs E M (kimg_cut lo hi kn).
Proof.
  intros segs E M lo hi kn HK. unfold kimg_cut. apply Forall_forall. intros K Hin.
  apply in_flat_map in Hin as (K0 & Hin0 & HK0).
  pose proof (proj1 (Forall_forall _ _) HK K0 Hin0) as OK0.
  destruct K0 as [| | |a b| | | | | |]; cbn [kimg_cut1] in HK0;
    try (destruct HK0 as [<-|[]]; exact OK0).
  destruct ((hi <=? a) || (b <=? lo))%Z eqn:E0; [destruct HK0 as [<-|[]]; exact OK0|].
  apply orb_false_iff in E0 as [Ea Eb]. apply Z.leb_gt in Ea. apply Z.leb_gt in Eb.
  cbn [kentry_ok] in OK0. destruct OK0 as (Ha & Hb & Himg).
  apply in_app_or in HK0 as [H1 | H2].
  - destruct (a <? lo)%Z eqn:E1; [|destruct H1]. apply Z.ltb_lt in E1. destruct H1 as [<-|[]].
    cbn [kentry_ok]. split; [lia|]. split; [lia | intros i Hi; apply Himg; lia].
  - destruct (hi <? b)%Z eqn:E1; [|destruct H2]. apply Z.ltb_lt in E1. destruct H2 as [<-|[]].
    cbn [kentry_ok]. split; [lia|]. split; [lia | intros i Hi; apply Himg; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim.

Lemma ts_msteps_no_lazy : forall segs ms ms' model,
  m_vm_lazy model = [] ->
  msteps segs ms ms' -> to_spin segs ms' model -> to_spin segs ms model.
Proof.
  intros segs ms ms' model Hlazy Hms Hsp.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hrest IH]; [exact Hsp|].
  eapply ts_step_no_lazy; [exact Hsvc | exact Hlazy | exact Hstep | exact (IH Hsp)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import StdioSymDrive.

Definition junk_c (R' : bvmap 5 word) (clob : list reg) : list word := map (fun r => getr R' r) clob.

Fixpoint sr_after_call_c (sr : list expr) (clob : list reg) (j : nat) : list expr :=
  match clob with
  | [] => sr
  | r :: cl => sr_after_call_c (sr_upd sr (ridx r) (EVar j)) cl (S j)
  end.

Lemma expr_vars_lt_weaken : forall b b' e, (b <= b')%nat -> expr_vars_lt b e = true -> expr_vars_lt b' e = true.
Proof.
  intros b b' e Hb. induction e; cbn [expr_vars_lt]; intros H; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity);
    try (apply IHe; exact H).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

Lemma sr_vars_lt_weaken : forall b b' sr, (b <= b')%nat -> sr_vars_lt b sr = true -> sr_vars_lt b' sr = true.
Proof.
  intros b b' sr Hb. induction sr as [|e t IH]; cbn [sr_vars_lt]; intros H; [reflexivity|].
  apply andb_prop in H as [He Ht]. rewrite (IH Ht), (expr_vars_lt_weaken b b' e Hb He). reflexivity.
Qed.

Lemma sr_vars_lt_upd : forall b sr i e,
  sr_vars_lt b sr = true -> expr_vars_lt b e = true -> sr_vars_lt b (sr_upd sr i e) = true.
Proof.
  intros b sr i e. revert sr. induction i as [|i IH]; intros sr Hsr He; destruct sr as [|x t]; cbn [sr_upd sr_vars_lt] in *.
  - rewrite He. reflexivity.
  - apply andb_prop in Hsr as [_ Ht]. rewrite He, Ht. reflexivity.
  - cbn [expr_vars_lt]. rewrite (IH [] eq_refl He). reflexivity.
  - apply andb_prop in Hsr as [Hx Ht]. rewrite Hx, (IH t Ht He). reflexivity.
Qed.

Lemma regs_after_clob : forall clob vals ebs sr R R',
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall r : reg, ~ In r clob -> getr R' r = getr R r) ->
  ~ In (0%bv : reg) clob -> List.NoDup clob ->
  regs_ok (Env (vals_ev (vals ++ junk_c R' clob)) ebs) (sr_after_call_c sr clob (length vals)) R'.
Proof.
  induction clob as [|r cl IH]; intros vals ebs sr R R' Hlt HR Hkeep H0 Hnd; cbn [sr_after_call_c junk_c map].
  - rewrite app_nil_r. intros x. rewrite (Hkeep x ltac:(intros [])). apply HR.
  - inversion Hnd as [|r' cl' Hr Hnd']; subst.
    change (getr R' r :: map (fun r0 : reg => getr R' r0) cl) with ([getr R' r] ++ junk_c R' cl).
    rewrite app_assoc.
    assert (Hlen : length (vals ++ [getr R' r]) = S (length vals)) by (rewrite length_app; cbn; lia).
    rewrite <- Hlen.
    apply (IH (vals ++ [getr R' r]) ebs (sr_upd sr (ridx r) (EVar (length vals))) (regupd R r (getr R' r)) R').
    + rewrite Hlen. apply sr_vars_lt_upd; [| cbn [expr_vars_lt]; apply Nat.ltb_lt; lia].
      eapply sr_vars_lt_weaken; [| exact Hlt]. lia.
    + apply regs_ok_set.
      * eapply regs_ok_agree; [apply vals_app_agree | exact Hlt | exact HR].
      * intros Heq. apply H0. left. exact Heq.
      * cbn [edenot ev]. unfold vals_ev. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    + intros x Hx. destruct (bv_eq_dec _ x r) as [->|Hne].
      * rewrite getr_same; [reflexivity|]. intros Heq. apply H0. left. exact Heq.
      * rewrite getr_other by exact Hne. apply Hkeep. intros [Heq|Hin]; [apply Hne; symmetry; exact Heq | exact (Hx Hin)].
    + intros Hin. apply H0. right. exact Hin.
    + exact Hnd'.
Qed.

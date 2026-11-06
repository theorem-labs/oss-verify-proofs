From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_calls_copy_c rec_calls_free_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint argbytes (xs : list (list byte)) : Z :=
  match xs with [] => 0 | x :: xs' => Z.of_nat (length x) + 1 + argbytes xs' end.

Lemma argbytes_app : forall l1 l2, argbytes (l1 ++ l2) = argbytes l1 + argbytes l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn [app argbytes]; [lia|]. rewrite IH. lia. Qed.

Lemma argbytes_bound_list : forall l, Forall (fun s => Z.of_nat (length s) <= LMAX) l ->
  argbytes l <= Z.of_nat (length l) * (LMAX + 1).
Proof.
  induction l as [|x l IH]; intros H; cbn [argbytes length]; [lia|].
  inversion H as [|y l' Hx Hl]; subst. pose proof (IH Hl). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma rcc_b_fields : forall xs b,
  sb_live (rcc_b b xs) = sb_live b + Z.of_nat (length xs) /\
  sb_bytes (rcc_b b xs) = sb_bytes b + argbytes xs /\ sb_cap (rcc_b b xs) = sb_cap b.
Proof.
  induction xs as [|x xs IH]; intros b; [cbn; lia|].
  change (rcc_b b (x :: xs)) with (rcc_b (sb_malloc b (Z.of_nat (length x) + 1)) xs).
  destruct (IH (sb_malloc b (Z.of_nat (length x) + 1))) as (A1 & A2 & A3).
  rewrite A1, A2, A3. unfold sb_malloc. cbn [sb_live sb_bytes sb_cap length argbytes]. rewrite Nat2Z.inj_succ.
  split; [ring|]. split; [ring | reflexivity].
Qed.

Lemma rfree_b_cap : forall F b, sb_cap (RecKindB.rfree_b b F) = sb_cap b.
Proof.
  induction F as [|x F IH]; intros b; [reflexivity|].
  change (RecKindB.rfree_b b (x :: F)) with (RecKindB.rfree_b (sb_free b (snd x)) F). rewrite IH. reflexivity.
Qed.

Lemma rcc_args_bound : forall cs : list rcall, (length cs <= 16)%nat ->
  (forall c, In c cs -> (length (snd c) <= 6)%nat /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) ->
  (length (rcc_args cs) <= 96)%nat /\ argbytes (rcc_args cs) <= 96 * (LMAX + 1).
Proof.
  intros cs. unfold rcc_args.
  assert (G : forall l : list rcall,
            (forall c, In c l -> (length (snd c) <= 6)%nat /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) ->
            (length (concat (map snd l)) <= 6 * length l)%nat /\
            argbytes (concat (map snd l)) <= 6 * (LMAX + 1) * Z.of_nat (length l)).
  { induction l as [|c l IH]; intros H; [cbn; split; [lia | unfold LMAX; lia]|].
    cbn [map concat]. rewrite length_app, argbytes_app.
    destruct (H c (or_introl eq_refl)) as [Hc Hf].
    destruct (IH (fun c' Hc' => H c' (or_intror Hc'))) as [I1 I2].
    pose proof (argbytes_bound_list _ Hf) as Hb.
    cbn [length]. rewrite Nat2Z.inj_succ. unfold LMAX in *. split; [lia | nia]. }
  intros H1 H2. destruct (G cs H2) as [G1 G2]. unfold LMAX in *. split; [lia | nia].
Qed.

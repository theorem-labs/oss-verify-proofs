(* G4.ExHead.HeadModel: the scan head's model facts (pure), used by the head walk (FMW_ex_head*.v):
   ManifestModel's head / ci_eqb / zl_eqb / scan / prefix_lc, FMH_Rt's strn_eq,
   FMW_ex_base's ex_scan / cx_res. Reuses lib/Prog/expected_m.v (scan_step, scan_end, firstn_noz, nth_skipn0). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base FMW_ex_head_d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- list helpers ---- *)
Lemma hm_ci_len : forall a b, ManifestModel.ci_eqb a b = true -> length a = length b.
Proof.
  induction a as [|x a IH]; intros b H; destruct b as [|y b]; cbn in H |- *; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [_ H]. f_equal. apply IH. exact H.
Qed.

Lemma hm_ci_nth : forall a b j, ManifestModel.ci_eqb a b = true -> (j < length a)%nat ->
  ((nth j a 0 =? nth j b 0) || (nth j a 0 =? nth j b 0 - 32)) = true.
Proof.
  induction a as [|x a IH]; intros b j H Hj; destruct b as [|y b]; cbn in H; try discriminate.
  - cbn in Hj. lia.
  - apply andb_true_iff in H as [H1 H2]. destruct j as [|j]; [exact H1|].
    cbn [nth]. apply IH; [exact H2|cbn in Hj; lia].
Qed.

Lemma hm_ci_app : forall a b c d, length a = length b ->
  ManifestModel.ci_eqb (a ++ c) (b ++ d) = ManifestModel.ci_eqb a b && ManifestModel.ci_eqb c d.
Proof.
  induction a as [|x a IH]; intros b c d H; destruct b as [|y b]; cbn in H |- *; try discriminate; [reflexivity|].
  rewrite IH by lia. apply andb_assoc.
Qed.

Lemma hm_firstn_S : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|].
  change (firstn (S (S k)) (x :: l)) with (x :: firstn (S k) l).
  rewrite IH by lia. reflexivity.
Qed.

Lemma hm_nth_firstn : forall (l : list Z) n j, (j < n)%nat -> nth j (firstn n l) 0 = nth j l 0.
Proof.
  induction l as [|x l IH]; intros n j Hj; (destruct n as [|n]; [lia|]); [reflexivity|].
  destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

(* ---- the 13 model facts ---- *)
Lemma hd_m_byte : forall (t : list Z) i, (i <= length t)%nat -> Forall (fun c => c <> 0) t ->
  (nth i (t ++ [0]) 0 = 0 <-> i = length t) /\
  ((i < length t)%nat -> nth i (t ++ [0]) 0 = ManifestModel.byte_at t i).
Proof.
  intros t i Hi Hz. destruct (Nat.eq_dec i (length t)) as [E|E].
  - subst i. rewrite app_nth2, Nat.sub_diag by lia. cbn [nth]. split; [tauto|intro; lia].
  - rewrite app_nth1 by lia. split; [|intros _; reflexivity].
    split; [|intro; lia]. intro H0. exfalso. rewrite Forall_forall in Hz.
    apply (Hz (nth i t 0)); [apply nth_In; lia|exact H0].
Qed.

Lemma hd_m_strn : forall (t : list Z) i,
  strn_eq 6 (skipn (S i) t) ManifestModel.prefix_lc <->
  ManifestModel.zl_eqb (firstn 6 (skipn (S i) t)) ManifestModel.prefix_lc = true.
Proof.
  intros t i. unfold strn_eq. rewrite ManifestModel.zl_eqb_eq.
  change (firstn 6 (ManifestModel.prefix_lc ++ [0])) with ManifestModel.prefix_lc.
  change 6%nat with (length ManifestModel.prefix_lc).
  apply expected_m.firstn_noz. apply Forall_forall. intros x Hx. cbn in Hx. lia.
Qed.

Lemma hd_m_head7 : forall t i, hd_arm1 t i = true -> ManifestModel.head t i = Some (i + 7)%nat.
Proof. intros t i H. unfold hd_arm1 in H. unfold ManifestModel.head. rewrite H. reflexivity. Qed.

Lemma hd_m_ci_step : forall (t : list Z) i k, (i + k < length t)%nat -> (k < 6)%nat ->
  ManifestModel.ci_eqb (firstn k (skipn i t)) (firstn k ManifestModel.prefix_lc) = true ->
  ((nth (i + k) t 0 =? nth k ManifestModel.prefix_lc 0) ||
   (nth (i + k) t 0 =? nth k ManifestModel.prefix_lc 0 - 32)) = true ->
  ManifestModel.ci_eqb (firstn (S k) (skipn i t)) (firstn (S k) ManifestModel.prefix_lc) = true.
Proof.
  intros t i k Hik Hk Hci Hc.
  assert (Hl : (k < length (skipn i t))%nat) by (rewrite length_skipn; lia).
  assert (Hp : (k < length ManifestModel.prefix_lc)%nat) by (cbn; lia).
  rewrite (hm_firstn_S _ _ Hl), (hm_firstn_S _ _ Hp), hm_ci_app.
  - rewrite Hci. cbn [ManifestModel.ci_eqb andb]. rewrite expected_m.nth_skipn0, andb_true_r. exact Hc.
  - rewrite !length_firstn. lia.
Qed.

Lemma hd_m_ci6_len : forall (t : list Z) i,
  ManifestModel.ci_eqb (firstn 6 (skipn i t)) ManifestModel.prefix_lc = true -> (i + 6 <= length t)%nat.
Proof.
  intros t i H. apply hm_ci_len in H. rewrite length_firstn, length_skipn in H.
  change (length ManifestModel.prefix_lc) with 6%nat in H. lia.
Qed.

Lemma hd_m_ci_fail : forall (t : list Z) i k, (i + k <= length t)%nat -> (k < 6)%nat ->
  (nth (i + k) (t ++ [0]) 0 =? nth k ManifestModel.prefix_lc 0) = false ->
  (nth (i + k) (t ++ [0]) 0 =? nth k ManifestModel.prefix_lc 0 - 32) = false ->
  ManifestModel.ci_eqb (firstn 6 (skipn i t)) ManifestModel.prefix_lc = false.
Proof.
  intros t i k Hik Hk H1 H2.
  destruct (ManifestModel.ci_eqb (firstn 6 (skipn i t)) ManifestModel.prefix_lc) eqn:E; [|reflexivity].
  exfalso. pose proof (hd_m_ci6_len t i E) as L.
  pose proof (hm_ci_nth _ _ k E) as N.
  rewrite length_firstn, length_skipn in N. specialize (N ltac:(lia)).
  rewrite hm_nth_firstn, expected_m.nth_skipn0 in N by lia.
  rewrite app_nth1 in H1, H2 by lia. rewrite H1, H2 in N. discriminate N.
Qed.

Lemma hd_m_match_lt : forall (t : list Z) i k, (i + k <= length t)%nat -> (k < 6)%nat ->
  ((nth (i + k) (t ++ [0]) 0 =? nth k ManifestModel.prefix_lc 0) ||
   (nth (i + k) (t ++ [0]) 0 =? nth k ManifestModel.prefix_lc 0 - 32)) = true ->
  (i + k < length t)%nat /\ nth (i + k) (t ++ [0]) 0 = nth (i + k) t 0.
Proof.
  intros t i k Hik Hk H.
  destruct (Nat.eq_dec (i + k) (length t)) as [E|E].
  - exfalso. rewrite E, app_nth2, Nat.sub_diag in H by lia. cbn [nth] in H.
    destruct k as [|[|[|[|[|[|k]]]]]]; try lia; vm_compute in H; discriminate H.
  - split; [lia|]. apply app_nth1. lia.
Qed.

Lemma hd_m_none_ci : forall t i, hd_arm1 t i = false ->
  ManifestModel.ci_eqb (firstn 6 (skipn i t)) ManifestModel.prefix_lc = false -> ManifestModel.head t i = None.
Proof. intros t i H1 H2. unfold hd_arm1 in H1. unfold ManifestModel.head. rewrite H1, H2. reflexivity. Qed.

Lemma hd_m_none_sp : forall t i, hd_arm1 t i = false -> (i <> 0)%nat ->
  ManifestModel.is_space (ManifestModel.byte_at t (pred i)) = false -> ManifestModel.head t i = None.
Proof.
  intros t i H1 Hi H2. unfold hd_arm1 in H1. unfold ManifestModel.head. rewrite H1.
  destruct i as [|i]; [contradiction|]. cbn [pred] in H2. cbv beta iota. rewrite H2, andb_false_r. reflexivity.
Qed.

Lemma hd_m_some6 : forall t i, hd_arm1 t i = false ->
  ManifestModel.ci_eqb (firstn 6 (skipn i t)) ManifestModel.prefix_lc = true ->
  (i = 0%nat \/ ManifestModel.is_space (ManifestModel.byte_at t (pred i)) = true) ->
  ManifestModel.head t i = Some (i + 6)%nat.
Proof.
  intros t i H1 H2 H3. unfold hd_arm1 in H1. unfold ManifestModel.head. rewrite H1, H2.
  destruct i as [|i]; [reflexivity|].
  destruct H3 as [H3|H3]; [discriminate|]. cbn [pred] in H3. cbv beta iota. rewrite H3. reflexivity.
Qed.

(* by enumeration of the 256 byte values, as FMW_plain.v's pl_cls_all *)
Lemma hd_m_space : forall c, 0 <= c < 256 ->
  ManifestModel.is_space c = (((c - 9) mod 2 ^ 64 <? 5) || (c =? 32)).
Proof.
  intros c Hc.
  assert (H : forallb (fun c => Bool.eqb (ManifestModel.is_space c) (((c - 9) mod 2 ^ 64 <? 5) || (c =? 32)))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Bool.eqb_prop. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Lemma hd_m_scan_step : forall cx i d f, ex_scan cx i d f -> (i < length (cx_tb cx))%nat ->
  ManifestModel.head (cx_tb cx) i = None -> ex_scan cx (S i) d (pred f).
Proof.
  intros cx i d f Hs Hi Hh. unfold ex_scan in Hs |- *. destruct Hs as (H1 & H2 & H3 & H4 & H5).
  destruct f as [|f]; [lia|]. cbn [pred].
  split; [lia|]. split; [exact H2|]. split; [lia|]. split; [exact H4|].
  assert (Hd : ManifestModel.decl (cx_tb cx) i = ManifestModel.DNone).
  { unfold ManifestModel.decl. rewrite Hh. reflexivity. }
  rewrite H5, expected_m.scan_step by exact Hi. unfold expected_m.sstep. rewrite Hd. reflexivity.
Qed.

Lemma hd_m_res_end : forall cx i d f, ex_scan cx i d f -> i = length (cx_tb cx) -> cx_res cx = 0.
Proof.
  intros cx i d f Hs Hi. unfold ex_scan in Hs. destruct Hs as (H1 & H2 & H3 & H4 & H5). subst i.
  destruct f as [|f]; [lia|]. rewrite H5. apply expected_m.scan_end. lia.
Qed.

Print Assumptions hd_m_byte.
Print Assumptions hd_m_strn.
Print Assumptions hd_m_head7.
Print Assumptions hd_m_ci_step.
Print Assumptions hd_m_ci_fail.
Print Assumptions hd_m_match_lt.
Print Assumptions hd_m_ci6_len.
Print Assumptions hd_m_none_ci.
Print Assumptions hd_m_none_sp.
Print Assumptions hd_m_some6.
Print Assumptions hd_m_space.
Print Assumptions hd_m_scan_step.
Print Assumptions hd_m_res_end.

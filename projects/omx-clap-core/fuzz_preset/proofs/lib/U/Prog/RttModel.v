From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterSpecFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PjWriteHyp.
Import ListNotations.
Local Open Scope Z_scope.

Lemma wdoc_split : forall t p, wdoc t p = concat (wvpieces t p 0) ++ (if p then [10] else []).
Proof. intros t p. unfold wdoc, wdpieces. rewrite concat_app. destruct p; reflexivity. Qed.

Lemma rm_wvpieces_cons : forall t p d, exists b P, wvpieces t p d = b :: P.
Proof. intros t p d. destruct t; cbn [wvpieces]; try unfold spieces; eexists; eexists; reflexivity. Qed.

Lemma rm_lens_ne : forall t p, piece_lens (wdpieces t p) <> [].
Proof.
  intros t p. unfold wdpieces, piece_lens. destruct (rm_wvpieces_cons t p 0) as (b & P & ->).
  cbn [app map]. discriminate.
Qed.

Lemma rm_sum_lens : forall P, fold_right Z.add 0 (piece_lens P) = Z.of_nat (length (concat P)).
Proof.
  induction P as [|b P IH]; [reflexivity|]. unfold piece_lens in *. cbn [map fold_right concat].
  rewrite IH, length_app, Nat2Z.inj_add. reflexivity.
Qed.

Lemma rm_lens_nonneg : forall P, Forall (fun l => 0 <= l) (piece_lens P).
Proof.
  intros P. unfold piece_lens. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _). lia.
Qed.

Lemma rm_newcap : forall c need, (c = 0 \/ exists j, 0 <= j /\ c = 4096 * 2 ^ j) -> c < need -> need <= 2 ^ 63 ->
  (exists j, 0 <= j /\ newcap c need = 4096 * 2 ^ j) /\ need <= newcap c need /\
  newcap c need <= Z.max 4096 (2 * need).
Proof.
  intros c need Hc Hlt Hn.
  assert (H0 : exists j0, 0 <= j0 /\ (if c =? 0 then 4096 else c) = 4096 * 2 ^ j0 /\
    (j0 = 0 \/ 4096 * 2 ^ j0 < need)).
  { destruct Hc as [-> | (j0 & Hj0 & ->)].
    - exists 0. rewrite Z.eqb_refl. split; [lia|]. split; [reflexivity | left; reflexivity].
    - assert (0 < 2 ^ j0) by (apply Z.pow_pos_nonneg; lia).
      destruct (Z.eqb_spec (4096 * 2 ^ j0) 0); [lia|].
      exists j0. split; [exact Hj0|]. split; [reflexivity | right; exact Hlt]. }
  destruct H0 as (j0 & Hj0 & Hc0 & Hcase).
  unfold newcap. rewrite Hc0.
  assert (Hp : 0 < 2 ^ j0) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpre : need <= 4096 * 2 ^ j0 * 2 ^ Z.of_nat 64).
  { change (Z.of_nat 64) with 64. assert (E : 2 ^ 64 = 2 * 2 ^ 63) by reflexivity. rewrite E.
    pose proof (Z.pow_pos_nonneg 2 63 ltac:(lia) ltac:(lia)). nia. }
  destruct (dbl_spec 64 (4096 * 2 ^ j0) need ltac:(lia) Hpre) as (j & Hj & Hd & Hnd & Hmin).
  rewrite Hd in Hnd |- *.
  split; [exists (j0 + Z.of_nat j); split; [lia | rewrite Z.pow_add_r by lia; ring] |].
  split; [exact Hnd|].
  destruct j as [|j'].
  - change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.mul_1_r.
    destruct Hcase as [-> | Hcase]; [change (4096 * 2 ^ 0) with 4096; lia | lia].
  - destruct Hmin as [Hm | Hm]; [discriminate|].
    replace (Z.of_nat (S j') - 1) with (Z.of_nat j') in Hm by lia.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    replace (4096 * 2 ^ j0 * (2 * 2 ^ Z.of_nat j')) with (2 * (4096 * 2 ^ j0 * 2 ^ Z.of_nat j')) by ring.
    lia.
Qed.

Lemma rm_gcap : forall ls x c, 0 <= x -> Forall (fun l => 0 <= l) ls -> x + fold_right Z.add 0 ls + 1 <= 2 ^ 63 ->
  (c = 0 /\ ls <> [] \/ (exists j, 0 <= j /\ c = 4096 * 2 ^ j) /\ x + 1 <= c /\ c <= Z.max 4096 (2 * (x + 1))) ->
  (exists j, 0 <= j /\ grow_cap x c ls = 4096 * 2 ^ j) /\ x + fold_right Z.add 0 ls + 1 <= grow_cap x c ls /\
  grow_cap x c ls <= Z.max 4096 (2 * (x + fold_right Z.add 0 ls + 1)).
Proof.
  induction ls as [|l ls IH]; intros x c Hx Hf Hs Hc; cbn [grow_cap fold_right] in *.
  - destruct Hc as [[_ Hne] | (Hp & H1 & H2)]; [exfalso; apply Hne; reflexivity|].
    split; [exact Hp | lia].
  - apply Forall_cons_iff in Hf as [Hl Hf]. cbv beta in Hl.
    assert (Hn : 0 <= fold_right Z.add 0 ls) by (clear -Hf; induction Hf; cbv beta in *; cbn [fold_right]; lia).
    destruct (Z.ltb_spec c (x + l + 1)) as [Hlt | Hge].
    + assert (Hc' : c = 0 \/ exists j, 0 <= j /\ c = 4096 * 2 ^ j)
        by (destruct Hc as [[H _] | (H & _)]; [left | right]; exact H).
      destruct (rm_newcap c (x + l + 1) Hc' Hlt ltac:(lia)) as (P1 & P2 & P3).
      assert (Hc2 : newcap c (x + l + 1) = 0 /\ ls <> [] \/
        (exists j, 0 <= j /\ newcap c (x + l + 1) = 4096 * 2 ^ j) /\ x + l + 1 <= newcap c (x + l + 1) /\
        newcap c (x + l + 1) <= Z.max 4096 (2 * (x + l + 1))) by (right; split; [exact P1 | lia]).
      destruct (IH (x + l) (newcap c (x + l + 1)) ltac:(lia) Hf ltac:(lia) Hc2) as (Q1 & Q2 & Q3).
      split; [exact Q1|]. split; lia.
    + destruct Hc as [[H0 _] | (Hp & H1 & H2)]; [lia|].
      assert (Hc2 : c = 0 /\ ls <> [] \/
        (exists j, 0 <= j /\ c = 4096 * 2 ^ j) /\ x + l + 1 <= c /\ c <= Z.max 4096 (2 * (x + l + 1)))
        by (right; split; [exact Hp | lia]).
      destruct (IH (x + l) c ltac:(lia) Hf ltac:(lia) Hc2) as (Q1 & Q2 & Q3).
      split; [exact Q1|]. split; lia.
Qed.

Lemma rm_wcap : forall t p, wlen t p + 1 <= 2 ^ 63 ->
  (exists j, 0 <= j /\ wcap t p = 4096 * 2 ^ j) /\ wlen t p + 1 <= wcap t p /\
  wcap t p <= Z.max 4096 (2 * (wlen t p + 1)).
Proof.
  intros t p H. unfold wcap, wlen, wdoc in *. rewrite <- (rm_sum_lens (wdpieces t p)) in *.
  destruct (rm_gcap (piece_lens (wdpieces t p)) 0 0 ltac:(lia) (rm_lens_nonneg _) ltac:(lia)
    (or_introl (conj eq_refl (rm_lens_ne t p)))) as (A1 & A2 & A3).
  split; [exact A1|]. split; lia.
Qed.

Lemma wcap_ge : forall t p, wlen t p + 1 <= 2 ^ 62 -> wlen t p + 1 <= wcap t p.
Proof.
  intros t p H. assert (E : 2 ^ 62 <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  destruct (rm_wcap t p ltac:(lia)) as (_ & A & _). exact A.
Qed.

Lemma wcap_pow : forall t p, wlen t p + 1 <= 2 ^ 62 -> exists j, 0 <= j /\ wcap t p = 4096 * 2 ^ j.
Proof.
  intros t p H. assert (E : 2 ^ 62 <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  destruct (rm_wcap t p ltac:(lia)) as (A & _ & _). exact A.
Qed.

Lemma wcap_le : forall t p, wlen t p + 1 <= 2 ^ 62 -> wcap t p <= Z.max 4096 (2 * (wlen t p + 1)).
Proof.
  intros t p H. assert (E : 2 ^ 62 <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  destruct (rm_wcap t p ltac:(lia)) as (_ & _ & A). exact A.
Qed.

Lemma wcalls_pos : forall t p, 1 <= wcalls t p.
Proof.
  intros t p. unfold wcalls, wdpieces, piece_lens. destruct (rm_wvpieces_cons t p 0) as (b & P & ->).
  cbn [app map grow_calls]. destruct (Z.ltb_spec 0 (0 + Z.of_nat (length b) + 1)); [cbn [length]; lia | lia].
Qed.

Lemma bytes_zb : forall W, Forall (fun c => 0 < c < 256) W -> zb (map (Z_to_bv 8) W) = W.
Proof.
  intros W H. induction H as [|c W Hc HW IH]; [reflexivity|]. cbv beta in Hc.
  unfold zb in *. cbn [map]. rewrite IH. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma bytes_nz : forall W, Forall (fun c => 0 < c < 256) W -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) W).
Proof.
  intros W H Hin. apply in_map_iff in Hin as (c & Ec & Hc). rewrite Forall_forall in H. specialize (H c Hc).
  cbv beta in H. apply (f_equal bv_unsigned) in Ec. rewrite !Z_to_bv_unsigned in Ec. unfold bv_wrap, bv_modulus in Ec.
  change (2 ^ Z.of_N 8) with 256 in Ec. rewrite !Z.mod_small in Ec by lia. lia.
Qed.

Lemma rtt_G9 : forall t p, PjRoundTrip.pj_wf jr_strtod t ->
  json_read jr_strtod (wdoc t p) = Some t /\ snd (jr_run jr_strtod (wdoc t p) []) = PjRoundTrip.ttrace t /\
  ncalls jr_strtod (wdoc t p) = PjRoundTrip.tcalls t.
Proof.
  intros t p H. split; [apply PjRoundTrip.G9; exact H|].
  split; [apply PjRoundTrip.G9_trace; exact H | apply PjRoundTrip.G9_calls; exact H].
Qed.

Lemma rtt_maxrun : forall t p, wlen t p + 1 <= 2 ^ 28 -> Z.of_nat (PjRoundTrip.maxrun (wdoc t p)) < 2 ^ 30.
Proof.
  intros t p H. assert (G : (PjRoundTrip.maxrun (wdoc t p) <= length (wdoc t p))%nat) by apply PjRoundTrip.G12_1.
  assert (E : 2 ^ 28 < 2 ^ 30) by (apply Z.pow_lt_mono_r; lia). unfold wlen in H. lia.
Qed.

Lemma rm_ro_addr_eq : forall s a,
  Mem.ro_addr s a = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.ro_addr s a.
Proof. reflexivity. Qed.

Lemma img_empty : forall segs mem, segs = rsegs -> ro_agree segs mem ->
  Mem.ro_addr segs (Z_to_bv 64 0x102e8) = true /\ YP09.mbyte segs mem 0x102e8 = Some (Z_to_bv 8 0).
Proof.
  intros segs mem -> RA.
  assert (R : Mem.ro_addr rsegs (Z_to_bv 64 0x102e8) = true) by (vm_compute; reflexivity).
  split; [exact R|]. rewrite rm_ro_addr_eq in R.
  etransitivity; [exact (RA _ R) | vm_compute; reflexivity].
Qed.

Lemma img_nl : forall segs mem, segs = rsegs -> ro_agree segs mem ->
  Mem.ro_addr segs (Z_to_bv 64 0x10392) = true /\ YP09.mbyte segs mem 0x10392 = Some (Z_to_bv 8 10).
Proof.
  intros segs mem -> RA.
  assert (R : Mem.ro_addr rsegs (Z_to_bv 64 0x10392) = true) by (vm_compute; reflexivity).
  split; [exact R|]. rewrite rm_ro_addr_eq in R.
  etransitivity; [exact (RA _ R) | vm_compute; reflexivity].
Qed.

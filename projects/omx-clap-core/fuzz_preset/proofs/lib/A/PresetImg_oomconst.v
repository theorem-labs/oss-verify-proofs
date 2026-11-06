(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_oomconst.v (commit 67deba317dfb, blob 0ddc93f7175e) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 9 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
Import ListNotations.
Open Scope Z_scope.

Definition cell_bytes_ok (P : Z -> bool) (c : acell) : bool :=
  match c_at c with
  | ANum a => forallb (fun i => P (a + Z.of_nat i)) (seq 0 (Nat.max 1 (c_w c)))
  | _ => false
  end.

Lemma cell_bytes_ok_sound : forall P c, cell_bytes_ok P c = true ->
  exists a, c_at c = ANum a /\ forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> P (a + k) = true.
Proof.
intros P c H. unfold cell_bytes_ok in H. destruct (c_at c); try discriminate. cbv beta iota in H.
exists z. split; [reflexivity|]. intros k Hk.
rewrite forallb_forall in H.
assert (Hin : In (Z.to_nat k) (seq 0 (Nat.max 1 (c_w c)))) by (apply in_seq; lia).
pose proof (H _ Hin) as Hb. cbv beta in Hb. rewrite Z2Nat.id in Hb by lia. exact Hb.
Qed.

Lemma forallb_In : forall (f : acell -> bool) l c, forallb f l = true -> In c l -> f c = true.
Proof. intros f l c H Hc. rewrite forallb_forall in H. exact (H c Hc). Qed.

Definition not_oom_b (x : Z) : bool := negb (x =? TFIB_OOM).

Lemma tfib_abs_shadow_off_oom : forallb (cell_bytes_ok not_oom_b) (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma abs_shadow_off_oom : forall c, In c (Tfib_const_abs ++ Tfib_const_shadow) ->
  exists a, c_at c = ANum a /\ forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> a + k <> TFIB_OOM.
Proof.
intros c Hc. destruct (cell_bytes_ok_sound _ _ (forallb_In _ _ _ tfib_abs_shadow_off_oom Hc)) as (a & E & H).
exists a. split; [exact E|]. intros k Hk. specialize (H k Hk). unfold not_oom_b in H.
apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Definition in_zr_b (l : list (Z * Z)) (x : Z) : bool := existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) l.

Lemma in_zr_b_sound : forall l x, in_zr_b l x = true -> Exists (in_zr x) l.
Proof.
intros l x H. apply existsb_exists in H as (r & Hr & Hb). apply Exists_exists. exists r. split; [exact Hr|].
apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold in_zr. lia.
Qed.

Lemma tfib_abs_owned : forallb (cell_bytes_ok (in_zr_b Tfib_owned_static)) Tfib_const_abs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma abs_owned : forall c, In c Tfib_const_abs ->
  exists a, c_at c = ANum a /\ forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> Exists (in_zr (a + k)) Tfib_owned_static.
Proof.
intros c Hc. destruct (cell_bytes_ok_sound _ _ (forallb_In _ _ _ tfib_abs_owned Hc)) as (a & E & H).
exists a. split; [exact E|]. intros k Hk. exact (in_zr_b_sound _ _ (H k Hk)).
Qed.

Lemma own_entry : forall lo len x, In (lo, len) Tfib_owned_static -> lo <= x < lo + len -> Exists (in_zr x) Tfib_owned_static.
Proof. intros lo len x Hi Hx. apply Exists_exists. exists (lo, len). split; [exact Hi | exact Hx]. Qed.

Lemma own_inst : forall x, TFIB_INST <= x < TFIB_INST + 3632 -> Exists (in_zr x) Tfib_owned_static.
Proof.
intros x Hx. apply (own_entry 0xa7858 (0xaa708 - 0xa7858)); [apply (nth_error_In _ 2); reflexivity | unfold TFIB_INST in Hx; lia].
Qed.

Lemma own_tp : forall x, TFIB_TP - 88 <= x < TFIB_TP - 80 \/ TFIB_TP - 8 <= x < TFIB_TP + 16 ->
  Exists (in_zr x) Tfib_owned_static.
Proof.
intros x Hx. unfold TFIB_TP in Hx. destruct Hx as [Hx|Hx].
- apply (own_entry 0x5dde98 8); [unfold Tfib_owned_static; cbn [In]; repeat (first [left; reflexivity | right]) | lia].
- destruct (Z.lt_ge_cases x 0x5ddef0) as [Hl|Hg].
  + apply (own_entry 0x5ddee8 8); [unfold Tfib_owned_static; cbn [In]; repeat (first [left; reflexivity | right]) | lia].
  + apply (own_entry 0x5ddef0 0x3c); [unfold Tfib_owned_static; cbn [In]; repeat (first [left; reflexivity | right]) | lia].
Qed.

Lemma own_tsd : forall x, TFIB_TSD <= x < TFIB_TSD + 8 -> Exists (in_zr x) Tfib_owned_static.
Proof.
intros x Hx. unfold TFIB_TSD in Hx.
apply (own_entry 0x5ff298 8); [unfold Tfib_owned_static; cbn [In]; repeat (first [left; reflexivity | right]) | lia].
Qed.

Lemma pairwise_app_cross : forall {X} (R : X -> X -> Prop) l m, pairwise R (l ++ m) ->
  forall a b, In a l -> In b m -> R a b.
Proof.
intros X R l. induction l as [|h t IH]; intros m P a b Ha Hb; [destruct Ha|].
cbn [app pairwise] in P. destruct P as [F P]. destruct Ha as [<- | Ha].
- rewrite Forall_forall in F. apply F. apply in_or_app. right. exact Hb.
- exact (IH m P a b Ha Hb).
Qed.

Lemma owned_in_img : forall B ly x,
  Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B) ->
  Exists (in_zr x) (as_owned_static B) -> in_zr x (ly_img ly).
Proof.
intros B ly x F Ex. apply Exists_exists in Ex as (r & Hr & Hx). rewrite Forall_forall in F.
pose proof (F r ltac:(apply in_or_app; left; exact Hr)) as S. unfold zr_sub, in_zr in *. lia.
Qed.

Lemma sym_where : forall B ly c k, In c Tfib_const_sym -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  (ly_T ly <= aeval B ly (c_at c) + k < ly_T ly + 80) \/ (ly_C ly <= aeval B ly (c_at c) + k < ly_C ly + 160) \/
  (ly_D ly <= aeval B ly (c_at c) + k < ly_D ly + 32) \/ (as_inst B <= aeval B ly (c_at c) + k < as_inst B + 88) \/
  (as_tp B - 88 <= aeval B ly (c_at c) + k < as_tp B - 80) \/ (as_tp B - 8 <= aeval B ly (c_at c) + k < as_tp B + 16) \/
  (ly_tsd ly <= aeval B ly (c_at c) + k < ly_tsd ly + 8).
Proof.
intros B ly c k Hc Hk. unfold Tfib_const_sym in Hc. cbn [In] in Hc.
repeat (destruct Hc as [E | Hc]; [subst c; cbn in Hk |- *; unfold o_space, o_rinfo, o_sec_chunks in *; lia |]).
destruct Hc.
Qed.

Section g. Context {rc : YM05.RunCeil}.

Lemma img_off_owned_extents : forall ly x, layout_ok ly -> in_zr x (ly_img ly) ->
  forall e, In e (owned_extents ly) -> ~ in_zr x e.
Proof.
intros ly x L Hx e He Hxe. pose proof (@lo_disj _ ly L) as P. unfold static_extents in P.
pose proof (pairwise_app_cross _ _ _ P e (ly_img ly) He ltac:(right; left; reflexivity)) as D.
unfold zdisjoint, in_zr in *. lia.
Qed.

Lemma own_off : forall B ly x, TfibSyms B -> layout_ok ly ->
  Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B) ->
  Exists (in_zr x) Tfib_owned_static ->
  ~ (ly_T ly <= x < ly_T ly + kThreadObjSize) /\ ~ (ly_C ly <= x < ly_C ly + 256) /\ ~ (ly_D ly <= x < ly_D ly + 4096).
Proof.
intros B ly x TS L HS Ex. rewrite <- (ts_owned B TS) in Ex. pose proof (owned_in_img B ly x HS Ex) as Hi.
pose proof (img_off_owned_extents ly x L Hi) as N. unfold owned_extents in N. unfold in_zr in N.
split; [|split]; intros H;
  [apply (N (ly_T ly, kThreadObjSize)) | apply (N (ly_C ly, 256)) | apply (N (ly_D ly, 4096))];
  first [exact H | cbn [In]; repeat (first [left; reflexivity | right])].
Qed.

Lemma oom_const_core : forall B ly c k, TfibSyms B -> layout_ok ly -> ly_tsd ly = as_tsd B ->
  Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B) ->
  In c (Tfib_const ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  Exists (in_zr (aeval B ly (c_at c) + k)) (as_owned_static B) -> aeval B ly (c_at c) + k <> as_oom_byte B.
Proof.
intros B ly c k TS L HT HS Hc Hk Ex. rewrite (ts_oom B TS). rewrite (ts_owned B TS) in Ex. unfold Tfib_const in Hc.
apply in_app_or in Hc as [Hc|Hc].
- pose proof (own_off B ly _ TS L HS Ex) as (N1 & N2 & N3). unfold kThreadObjSize in N1.
  pose proof (ts_inst B TS) as I. pose proof (ts_tp B TS) as P. pose proof (ts_tsd B TS) as D.
  destruct (sym_where B ly c k Hc Hk) as [W|[W|[W|[W|[W|[W|W]]]]]]; unfold TFIB_OOM, TFIB_INST, TFIB_TP, TFIB_TSD in *; lia.
- destruct (abs_shadow_off_oom c Hc) as (a & E & K). rewrite E. cbn [aeval]. exact (K k Hk).
Qed.

Lemma oom_const_img_A : forall B, @im_syms AImg_A B ->
  forall ly c k,
  (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) ->
  In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  Exists (in_zr (aeval B ly (c_at c) + k)) (as_owned_static B) -> aeval B ly (c_at c) + k <> as_oom_byte B.
Proof.
intros B TS ly c k (L & HT & HS) Hc Hk Ex. change (TfibSyms B) in TS. rewrite (ts_const B TS ly) in Hc.
exact (oom_const_core B ly c k TS L HT HS Hc Hk Ex).
Qed.

End g.

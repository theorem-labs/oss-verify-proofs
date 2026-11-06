(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU3.v (commit 67deba317dfb, blob ae200ab11166) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainK DMdrainQ DMdrainG1 DMdrainT7.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMdeq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma lcn_from_parts : forall ly iw (m : word -> option byte) (l : list batch) (z : Z),
(forall i b, nth_error l i = Some b -> val_mem tfibsegs m (addrb ly b) 8 (fa ly (skipn (S i) l) z)) ->
(forall b, In b l ->
   val_mem tfibsegs m (addrb ly b + 8) 8 (b_bytes b) /\
   val_mem tfibsegs m (addrb ly b + 16) 8 (zl (b_items b)) /\
   (forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k))) ->
lcn ly iw m l z.
Proof.
intros ly iw m l. induction l as [|b t IH]; intros z HN HC; [exact I|].
split.
- destruct (HC b (or_introl eq_refl)) as (C8 & C16 & CS).
  split; [|split; [exact C8 | split; [exact C16 | exact CS]]].
  exact (HN 0%nat b eq_refl).
- apply IH.
  + intros i b2 Hi. exact (HN (S i) b2 Hi).
  + intros b2 Hb2. exact (HC b2 (or_intror Hb2)).
Qed.

Section g.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs1 : bvmap 5 word) (mem1 mem' : word -> option byte).
Variables (P R : list batch).
Let m1 := mrestrict (w_H W) mem1.
Let m' := mrestrict (w_H W) mem'.
Let sp1 : Z := bv_unsigned (getr regs1 2).
Local Notation iw := (DMdrainK.iwB B ly).

Hypothesis LY : layout_ok ly.
Hypothesis HSP : ly_stk_lo ly + AFeu.DRSTACK <= sp1 /\ sp1 + AFeu.LFRAME <= ly_stk_hi ly.
Hypothesis BADDR : forall b, In b (P ++ R) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL.
Hypothesis HSLOT : forall b, In b (P ++ R) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.

Hypothesis HFR : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp1 <= a < sp1 + 32) -> ~ (A_QUAR + 152 <= a < A_QUAR + 192) ->
  (forall b, In b P -> ~ (addrb ly b <= a < addrb ly b + 8)) ->
  mem' (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a).

Hypothesis HLL : lcn ly iw m1 (P ++ R) 0.

Hypothesis HPN : forall i b, nth_error P i = Some b ->
  val_mem tfibsegs m' (addrb ly b) 8 (next_addr ly P i).
Hypothesis HRN : forall i b, nth_error R i = Some b ->
  val_mem tfibsegs m' (addrb ly b) 8 (next_addr ly R i).

Hypothesis HCL : forall b, In b (P ++ R) ->
  val_mem tfibsegs m1 (addrb ly b + 8) 8 (b_bytes b) /\
  val_mem tfibsegs m1 (addrb ly b + 16) 8 (zl (b_items b)) /\
  (forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m1 (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k)).

Lemma cells_off_dw : forall b a, In b (P ++ R) ->
addrb ly b + 8 <= a < addrb ly b + 24 + 8 * zl (b_items b) ->
0 <= a < 2 ^ 64 /\ ~ (sp1 <= a < sp1 + 32) /\ ~ (A_QUAR + 152 <= a < A_QUAR + 192) /\
(forall b2, In b2 P -> ~ (addrb ly b2 <= a < addrb ly b2 + 8)).
Proof.
intros b a Hb Ha.
destruct (BADDR b Hb) as (A1 & A2 & A3 & A4).
pose proof (HSLOT b Hb) as HS.
assert (HCB : 24 + 8 * zl (b_items b) <= kBatchBytes).
{ unfold zl, kBatchBytes. unfold kBatchSlots in HS. lia. }
pose proof (DMdrainG1.LYB2 ly LY) as (L1 & L2 & L3 & L4 & _).
pose proof (DMdrainT7.prim_apart ly LY) as [_ PS].
destruct HSP as [S1 S2]. ceil.
unfold A_QUAR, A_ALLOCATOR, o_quar, kSpaceSize, kPrimResvSize, kBatchBytes, kHighMemBeg, AFeu.DRSTACK, AFeu.LFRAME in *.
splits.
- lia.
- lia.
- intros HQ. lia.
- lia.
- intros b2 Hb2 HR2.
  assert (Hin2 : In b2 (P ++ R)) by (apply in_app_iff; left; exact Hb2).
  destruct (BADDR b2 Hin2) as (B1 & B2 & B3 & B4).
  destruct (Z.eq_dec (addrb ly b2) (addrb ly b)) as [E|NE]; [lia|].
  destruct (DMdeq.apart8192 (addrb ly b) (addrb ly b2) A3 B3 ltac:(lia)); lia.
Qed.

Lemma cells_keep : forall b, In b (P ++ R) ->
val_mem tfibsegs m' (addrb ly b + 8) 8 (b_bytes b) /\
val_mem tfibsegs m' (addrb ly b + 16) 8 (zl (b_items b)) /\
(forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m' (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k)).
Proof.
intros b Hb.
destruct (In_nth_error _ _ Hb) as [i Hi].
pose proof (DMdrainQ.lcn_nth ly iw m1 (P ++ R) 0 i b HLL Hi) as (N0 & C8 & C16 & CS).
pose proof (HSLOT b Hb) as HS.
assert (FRM : forall off (n : nat), 8 <= off -> off + Z.of_nat n <= 24 + 8 * zl (b_items b) ->
  forall v, val_mem tfibsegs m1 (addrb ly b + off) n v -> val_mem tfibsegs m' (addrb ly b + off) n v).
{ intros off n Hlo Hhi v HV. unfold m1, m' in *.
  apply (AF0x.val_mem_frame (w_H W) mem1 mem'); [|exact HV].
  intros k Hk. apply HFR.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (H1 & _). exact H1.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & H2 & _). exact H2.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & _ & H3 & _). exact H3.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & _ & _ & H4). exact H4. }
splits.
- exact (FRM 8 8%nat ltac:(lia) ltac:(unfold zl; lia) _ C8).
- exact (FRM 16 8%nat ltac:(lia) ltac:(unfold zl; lia) _ C16).
- intros j k Hj.
  assert (HJ : (j < length (b_items b))%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  replace (addrb ly b + 24 + 8 * Z.of_nat j) with (addrb ly b + (24 + 8 * Z.of_nat j)) by lia.
  apply (FRM (24 + 8 * Z.of_nat j) 8%nat ltac:(lia) ltac:(unfold zl; lia)).
  replace (addrb ly b + (24 + 8 * Z.of_nat j)) with (addrb ly b + 24 + 8 * Z.of_nat j) by lia.
  exact (CS j k Hj).
Qed.

Lemma plist_lcn : lcn ly iw m' P 0.
Proof.
apply lcn_from_parts.
- intros i b Hi. rewrite DMdrainQ.fa_skipn. exact (HPN i b Hi).
- intros b Hb. apply cells_keep. apply in_app_iff. left. exact Hb.
Qed.

Lemma kept_lcn : lcn ly iw m' R 0.
Proof.
apply lcn_from_parts.
- intros i b Hi. rewrite DMdrainQ.fa_skipn. exact (HRN i b Hi).
- intros b Hb. apply cells_keep. apply in_app_iff. right. exact Hb.
Qed.

Lemma cells_keep_c : forall b, In b (P ++ R) ->
val_mem tfibsegs m' (addrb ly b + 8) 8 (b_bytes b) /\
val_mem tfibsegs m' (addrb ly b + 16) 8 (zl (b_items b)) /\
(forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m' (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k)).
Proof.
intros b Hb.
destruct (HCL b Hb) as (C8 & C16 & CS).
pose proof (HSLOT b Hb) as HS.
assert (FRM : forall off (n : nat), 8 <= off -> off + Z.of_nat n <= 24 + 8 * zl (b_items b) ->
  forall v, val_mem tfibsegs m1 (addrb ly b + off) n v -> val_mem tfibsegs m' (addrb ly b + off) n v).
{ intros off n Hlo Hhi v HV. unfold m1, m' in *.
  apply (AF0x.val_mem_frame (w_H W) mem1 mem'); [|exact HV].
  intros k Hk. apply HFR.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (H1 & _). exact H1.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & H2 & _). exact H2.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & _ & H3 & _). exact H3.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & _ & _ & H4). exact H4. }
splits.
- exact (FRM 8 8%nat ltac:(lia) ltac:(unfold zl; lia) _ C8).
- exact (FRM 16 8%nat ltac:(lia) ltac:(unfold zl; lia) _ C16).
- intros j k Hj.
  assert (HJ : (j < length (b_items b))%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  replace (addrb ly b + 24 + 8 * Z.of_nat j) with (addrb ly b + (24 + 8 * Z.of_nat j)) by lia.
  apply (FRM (24 + 8 * Z.of_nat j) 8%nat ltac:(lia) ltac:(unfold zl; lia)).
  replace (addrb ly b + (24 + 8 * Z.of_nat j)) with (addrb ly b + 24 + 8 * Z.of_nat j) by lia.
  exact (CS j k Hj).
Qed.

Lemma plist_lcn_c : lcn ly iw m' P 0.
Proof.
apply lcn_from_parts.
- intros i b Hi. rewrite DMdrainQ.fa_skipn. exact (HPN i b Hi).
- intros b Hb. apply cells_keep_c. apply in_app_iff. left. exact Hb.
Qed.

Lemma kept_lcn_c : lcn ly iw m' R 0.
Proof.
apply lcn_from_parts.
- intros i b Hi. rewrite DMdrainQ.fa_skipn. exact (HRN i b Hi).
- intros b Hb. apply cells_keep_c. apply in_app_iff. right. exact Hb.
Qed.
End g.
End f.

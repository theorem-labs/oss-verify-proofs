(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only Require PropExec CatSim StoreOk Frame.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import PImg RMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation same_on := (magree psegs).

Lemma same_on_munch : forall W m m', munch W m m' -> wmono psegs m m' -> same_on (fun a => outside W a) m m'.
Proof. intros W m m' MU WM. exact (magree_of_munch psegs W m m' MU WM). Qed.

Section CANSEC1. Context {rc : runConstT}.
Lemma same_on_rheap_pres : forall LB SP m m', rheap_pres LB SP m m' -> same_on (rclient_addr LB SP) m m'.
Proof. intros LB SP m m' H. exact H. Qed.
Lemma rheap_pres_same_on : forall LB SP m m', same_on (rclient_addr LB SP) m m' -> rheap_pres LB SP m m'.
Proof. intros LB SP m m' H. exact H. Qed.
End CANSEC1.

Lemma rdn_same_on : forall (P : Z -> Prop) M M' a n,
  same_on P M M' -> (forall x, a <= x < a + Z.of_nat n -> P x) -> 0 <= a < 2^64 -> a + Z.of_nat n <= 2^64 ->
  OP.rdn psegs M' (Z_to_bv 64 a) n = OP.rdn psegs M (Z_to_bv 64 a) n.
Proof.
  intros P M M' a n SO HP Ha Hn. apply OP.rdn_ext.
  - rewrite wa_unsigned by lia. lia.
  - intros x Hx. rewrite wa_unsigned in Hx by lia.
    destruct (SO (bv_unsigned x) ltac:(lia) ltac:(apply HP; lia)) as [E _].
    unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

Definition fm_ivs (rs : list (word * Z)) : list (Z * Z) :=
  map (fun r => (bv_unsigned (fst r), bv_unsigned (fst r) + snd r)) rs.

Lemma outside_fm_ivs : forall rs (x : word), outside (fm_ivs rs) (bv_unsigned x) -> OF.outside x rs.
Proof.
  induction rs as [|[b n] rs IH]; intros x H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [unfold OF.in_rng; exact H1 | apply IH; exact H2].
Qed.

Lemma munch_of_frame_mod : forall m m' rs, OF.frame_mod m m' rs -> munch (fm_ivs rs) m m' /\ wmono psegs m m'.
Proof.
  intros m m' rs [H G]. split; [| apply mem_grows_wmono; exact G].
  intros x Hx. apply H. apply outside_fm_ivs. exact Hx.
Qed.

Lemma same_on_frame_mod : forall m m' rs, OF.frame_mod m m' rs -> same_on (fun a => outside (fm_ivs rs) a) m m'.
Proof. intros m m' rs FM. destruct (munch_of_frame_mod _ _ _ FM) as [MU WM]. exact (same_on_munch _ _ _ MU WM). Qed.

Lemma mem_inv_munch : forall W m m', mem_inv psegs m -> munch W m m' ->
  (forall a, 0x10000 <= a < 0x21000 -> outside W a) -> mem_inv psegs m'.
Proof.
  intros W m m' MI MU HW a b Hab. rewrite p_ro_addr.
  destruct ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0x21000))%bool eqn:E; [|reflexivity].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (MU a (HW (bv_unsigned a) ltac:(lia))) in Hab. pose proof (MI a b Hab) as X. rewrite p_ro_addr in X.
  rewrite <- X. symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma pristine_of_mem_inv : forall (M : word -> option byte), mem_inv psegs M ->
  forall i, 0x10000 <= i < 0x21000 -> M (Z_to_bv 64 i) = None.
Proof.
  intros M MI i Hi. destruct (M (Z_to_bv 64 i)) as [b|] eqn:E; [|reflexivity].
  pose proof (MI _ _ E) as X. rewrite p_ro_addr, unsigned_lit in X by lia.
  exfalso. apply andb_false_iff in X. destruct X as [X|X]; [apply Z.leb_gt in X | apply Z.ltb_ge in X]; lia.
Qed.

Lemma wview_above : forall (m : word -> option byte) a, 0x94000 <= a < 2^64 -> wview psegs m (wa a) = m (wa a).
Proof.
  intros m a Ha. apply ref_wview_overlay. right. rewrite wa_unsigned by lia. lia.
Qed.

Lemma stk_wmono : forall (M M' : word -> option byte) lo hi,
  stk psegs M lo hi -> 0x94000 <= lo -> wmono psegs M M' -> stk psegs M' lo hi.
Proof.
  intros M M' lo hi (H0 & H1 & H) Hlo WM. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W _]. pose proof (WM _ W) as W'. split; [exact W'|].
  rewrite wview_above in W' by lia. unfold mrd. destruct (M' (wa a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma store_ok_of_stk : forall (M : word -> option byte) lo hi a (n : nat),
  stk psegs M lo hi -> lo <= a -> a + Z.of_nat n <= hi -> store_ok psegs M (wa a) n = true.
Proof.
  intros M lo hi a n (H0 & H1 & H) Ha Hn.
  assert (W : wr_at psegs M a (Z.of_nat n)).
  { split; [lia|]. split; [lia|]. intros i Hi. apply (H (a + i)). lia. }
  pose proof (wr_at_store_ok psegs M a (Z.of_nat n) 0 n W ltac:(lia) ltac:(lia)) as X.
  rewrite Z.add_0_r in X. exact X.
Qed.

Lemma store_ok_of_block : forall (M : word -> option byte) A (n : Z) junk,
  rw_cells psegs M A [CB (Z.to_nat n) junk] -> 0 <= n -> store_ok psegs M (wa A) (Z.to_nat n) = true.
Proof.
  intros M A n junk BLK Hn.
  pose proof (wr_at_store_ok psegs M A n 0 (Z.to_nat n) (rw_cells_wr_at _ _ _ _ n BLK ltac:(cbn [cells_size csize]; lia)) ltac:(lia) ltac:(lia)) as X.
  rewrite Z.add_0_r in X. exact X.
Qed.

Lemma payload_rdn : forall (M : word -> option byte) D (bs : list byte),
  bytes_at psegs M D bs ->
  forall i, 0 <= i < Z.of_nat (length bs) -> exists b, OP.rdn psegs M (Z_to_bv 64 (D + i)) 1 = Some [b].
Proof.
  intros M D bs BY i Hi. rewrite rdn_conv.
  pose proof (bytes_at_rdn psegs M D bs (Z.to_nat i) 1 BY) as RD.
  rewrite Z2Nat.id in RD by lia. unfold wa in RD. rewrite RD by lia.
  destruct (skipn (Z.to_nat i) bs) as [|b rest] eqn:E.
  - exfalso. apply (f_equal (@length _)) in E. rewrite length_skipn in E. cbn in E. lia.
  - exists b. reflexivity.
Qed.

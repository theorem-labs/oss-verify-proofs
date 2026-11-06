(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec SeqExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs DitherLib DitherTab DitherTabLoop KernelW.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache.

Section KW2.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout} {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma blk_apart_g : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> 0 <= n -> 0 <= k -> u p + n <= u q \/ u q + k <= u p.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Hn Hk.
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X];
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.

(* [comment removed for export] *)
Definition blk_regs (A : AS) (bl : list (Z * Z)) : Prop :=
  Forall (fun r => live A (Z_to_bv 64 (fst r)) = Some (snd r) /\ 0 <= fst r < 2 ^ 64 /\ 0 < snd r) bl.

Lemma pairwise_live : forall C A m md (bl : list (Z * Z)), Cok C -> W C A m md -> blk_regs A bl ->
  List.NoDup (map (fun r => Z_to_bv 64 (fst r)) bl) -> pairwise bl.
Proof.
  intros C A m md bl CK HW. induction bl as [|r tl IH]; intros BR ND; [exact I|].
  inversion BR as [|r0 tl0 (Lr & Rr & Nr) BRt]; subst. inversion ND as [|x l NI NDt]; subst. split; [|exact (IH BRt NDt)].
  intros r' Hr'. rewrite Forall_forall in BRt. destruct (BRt r' Hr') as (Lr' & Rr' & Nr').
  assert (NE : Z_to_bv 64 (fst r) <> Z_to_bv 64 (fst r')) by (intros EE; apply NI; rewrite EE; exact (in_map (fun r0 : Z * Z => Z_to_bv 64 (fst r0)) tl r' Hr')).
  pose proof (blk_apart_g C A m md _ _ _ _ CK HW Lr Lr' NE ltac:(lia) ltac:(lia)) as AP. rewrite !u_Z2bv in AP by lia. exact AP.
Qed.

Lemma pairwise_blocks : forall C A m md (F : Z * Z) (bl : list (Z * Z)), Cok C -> W C A m md ->
  c_top C - LSTK <= fst F -> blk_regs A bl -> List.NoDup (map (fun r => Z_to_bv 64 (fst r)) bl) -> pairwise (F :: bl).
Proof.
  intros C A m md F bl CK HW HF BR ND. split; [|exact (pairwise_live C A m md bl CK HW BR ND)].
  intros r' Hr'. unfold blk_regs in BR. rewrite Forall_forall in BR. destruct (BR r' Hr') as (Lr' & Rr' & Nr').
  destruct (blk_range C A m md _ _ CK HW Lr' Nr') as [_ TOP]. rewrite u_Z2bv in TOP by lia.
  pose proof CK as [T1 _ _ _ _]. right. lia.
Qed.

(* [comment removed for export] *)
Definition all_regs : list reg := map (fun k => Z_to_bv 5 (Z.of_nat k)) (seq 0 32).
Lemma all_regs_in : forall r : reg, In r all_regs.
Proof.
  intros r. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  assert (E : r = Z_to_bv 5 (Z.of_nat (Z.to_nat (u r)))) by (apply bv_eq; rewrite Z2Nat.id by lia; symmetry; apply Z_to_bv_small; exact Hr).
  rewrite E. unfold all_regs. apply in_map with (f := fun k => Z_to_bv 5 (Z.of_nat k)). apply in_seq. lia.
Qed.
Definition reg_mem (r : reg) (l : list reg) : bool := existsb (fun x => bv_eqb x r) l.
Lemma reg_mem_In : forall r l, reg_mem r l = true -> In r l.
Proof.
  intros r l H. unfold reg_mem in H. apply existsb_exists in H. destruct H as (x & Hx & E). unfold bv_eqb in E. apply Z.eqb_eq in E.
  apply bv_eq in E. subst x. exact Hx.
Qed.
(* [comment removed for export] *)
Lemma regs_agree_kept : forall (regs regs' : bvmap 5 word) (K CLOB : list reg),
  (forall r, In r K -> getr regs' r = getr regs r) ->
  forallb (fun r => reg_mem r CLOB || reg_mem r K || bv_eqb r 0) all_regs = true ->
  regs_agree (fun r => In r CLOB) regs regs'.
Proof.
  intros regs regs' K CLOB HK HB r NC. rewrite forallb_forall in HB. specialize (HB r (all_regs_in r)).
  apply orb_true_iff in HB. destruct HB as [HB|HB]; [apply orb_true_iff in HB; destruct HB as [HB|HB]|].
  - exfalso. exact (NC (reg_mem_In _ _ HB)).
  - exact (HK r (reg_mem_In _ _ HB)).
  - unfold getr. rewrite HB. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zero_tab_ok : forall segs (sx : bool) (P : Z -> Prop) (m : word -> option byte) (tab : Z), 0 <= tab -> tab + 1024 <= 2 ^ 64 -> P 0 ->
  (forall i, 0 <= i < 1024 -> m (Z_to_bv 64 (tab + i)) = Some (Z_to_bv 8 0)) -> tab_ok segs sx P m tab.
Proof.
  intros segs sx P m tab H0 H1 HP Z. split; [exact H0|]. split; [exact H1|]. intros k Hk.
  exists (repeat (Z_to_bv 8 0) 4). split.
  - rewrite (rdn_ext segs 4 m (wbytes m (Z_to_bv 64 (tab + 4 * k)) (repeat (Z_to_bv 8 0) 4))).
    + exact (rdn_wbytes_hit segs (repeat (Z_to_bv 8 0) 4) m (Z_to_bv 64 (tab + 4 * k)) ltac:(rewrite u_Z2bv by lia; cbn; lia)).
    + rewrite u_Z2bv by lia. cbn. lia.
    + intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
      assert (Ex : x = Z_to_bv 64 (tab + (u x - tab))) by (apply bv_eq; rewrite u_Z2bv by (pose proof (bv_unsigned_in_range 64 x); lia); lia).
      rewrite Ex at 1. rewrite (Z (u x - tab)) by lia.
      rewrite (MemSplit.wbytes_inside (repeat (Z_to_bv 8 0) 4) m (Z_to_bv 64 (tab + 4 * k)) x) by (rewrite ?u_Z2bv by lia; cbn; lia).
      f_equal. rewrite u_Z2bv by lia.
      assert (C : u x - (tab + 4 * k) = 0 \/ u x - (tab + 4 * k) = 1 \/ u x - (tab + 4 * k) = 2 \/ u x - (tab + 4 * k) = 3) by lia.
      destruct C as [-> | [-> | [-> | ->]]]; reflexivity.
  - replace (rdv sx 4 (repeat (Z_to_bv 8 0) 4)) with 0; [exact HP|]. destruct sx; reflexivity.
Qed.
End KW2.

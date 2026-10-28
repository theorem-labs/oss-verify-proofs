(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocRep.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Fixpoint inb (W : list ivl) (a : Z) : bool :=
  match W with
  | [] => false
  | (lo, hi) :: W' => ((lo <=? a) && (a <? hi)) || inb W' a
  end.

Lemma inb_false_outside : forall W a, inb W a = false <-> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a; cbn; [tauto|].
  rewrite Bool.orb_false_iff, Bool.andb_false_iff, Z.leb_gt, Z.ltb_ge, IH. split.
  - intros [[H|H] H2]; (split; [lia| exact H2]).
  - intros [H1 H2]. split; [| exact H2]. lia.
Qed.
Lemma inb_true_not_outside : forall W a, inb W a = true <-> ~ outside W a.
Proof.
  intros W a. rewrite <- inb_false_outside. destruct (inb W a); split; congruence || (intros H; exfalso; apply H; reflexivity) || auto.
Qed.

Definition chim (W : list ivl) (m m2 : mem) : mem := fun x => if inb W (bv_unsigned x) then m x else m2 x.

Lemma wview_pt : forall ma mb x, ma x = mb x -> wview asegs ma x = wview asegs mb x.
Proof. intros ma mb x E. unfold wview. rewrite E. reflexivity. Qed.
Lemma mrd_pt : forall ma mb x, ma x = mb x -> mrd asegs ma x = mrd asegs mb x.
Proof. intros ma mb x E. unfold mrd. rewrite E. reflexivity. Qed.

Section Chim.
  Variables (W : list ivl) (m m2 : mem).

  Lemma chim_in : forall x, inb W (bv_unsigned x) = true -> chim W m m2 x = m x.
  Proof. intros x E. unfold chim. rewrite E. reflexivity. Qed.
  Lemma chim_out : forall x, inb W (bv_unsigned x) = false -> chim W m m2 x = m2 x.
  Proof. intros x E. unfold chim. rewrite E. reflexivity. Qed.

  Lemma chim_mem_inv : mem_inv asegs m -> mem_inv asegs m2 -> mem_inv asegs (chim W m m2).
  Proof. intros M1 M2 a b E. unfold chim in E. destruct (inb W (bv_unsigned a)); [exact (M1 a b E)| exact (M2 a b E)]. Qed.

  Lemma chim_wmono_in : wmono asegs m m2 -> wmono asegs m (chim W m m2).
  Proof.
    intros WM x Hx. destruct (inb W (bv_unsigned x)) eqn:E.
    - rewrite (wview_pt (chim W m m2) m x (chim_in x E)). exact Hx.
    - rewrite (wview_pt (chim W m m2) m2 x (chim_out x E)). exact (WM x Hx).
  Qed.
  Lemma chim_wmono_out : forall m3, wmono asegs m m3 -> wmono asegs m2 m3 -> wmono asegs (chim W m m2) m3.
  Proof.
    intros m3 W1 W2 x Hx. destruct (inb W (bv_unsigned x)) eqn:E.
    - rewrite (wview_pt (chim W m m2) m x (chim_in x E)) in Hx. exact (W1 x Hx).
    - rewrite (wview_pt (chim W m m2) m2 x (chim_out x E)) in Hx. exact (W2 x Hx).
  Qed.

  Lemma chim_agree_out : agree_on (outside W) m2 (chim W m m2).
  Proof. intros a Ha Hr. apply chim_out. rewrite wa_unsigned by exact Hr. apply inb_false_outside. exact Ha. Qed.

End Chim.

Section PtEq.
  Context {HCEIL : HeapCeil}.
  Variables (P : Z -> Prop) (m m' : mem).
  Hypothesis AG : agree_on P m m'.

  Lemma bytes_at_pteq : forall A bs, bytes_at asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at asegs m' A bs.
  Proof.
    intros A bs (H0 & H1 & H) HP. split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite (mrd_pt m' m); [apply H; exact Hi|]. apply AG; [apply HP; lia| lia].
  Qed.
  Lemma wr_at_pteq : forall A n, wr_at asegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at asegs m' A n.
  Proof.
    intros A n (H0 & H1 & H) HP. split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite (wview_pt m' m); [apply H; exact Hi|]. apply AG; [apply HP; lia| lia].
  Qed.
  Lemma rw_cells_pteq : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells asegs m' A cs.
  Proof.
    intros A cs [[Hwf Hb] Hw] HP. split; [split; [exact Hwf|]|].
    - apply bytes_at_pteq; [exact Hb|]. rewrite cells_bytes_length by exact Hwf. exact HP.
    - apply wr_at_pteq; [exact Hw| exact HP].
  Qed.
  Lemma stk_pteq : forall lo hi, stk asegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk asegs m' lo hi.
  Proof.
    intros lo hi (H0 & H1 & H) HP. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [Hw [b Hb]].
    assert (E : m' (wa a) = m (wa a)) by (apply AG; [apply HP; exact Ha| lia]).
    split; [rewrite (wview_pt m' m _ E); exact Hw| exists b; rewrite (mrd_pt m' m _ E); exact Hb].
  Qed.
  Lemma u8arr_pteq : forall A bs, u8arr asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr asegs m' A bs.
  Proof. intros A bs [Hb Hw] HP. split; [apply bytes_at_pteq; [exact Hb| exact HP]| apply wr_at_pteq; [exact Hw| exact HP]]. Qed.
  Lemma u32arr_pteq : forall A ws, u32arr asegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) -> u32arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] HP. split; [| apply wr_at_pteq; [exact Hw| exact HP]].
    apply bytes_at_pteq; [exact Hb|]. rewrite u32s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HP. lia.
  Qed.

  Lemma poisoned_pteq : forall A k v, poisoned m A k v -> (forall a, sh A <= a < sh A + Z.of_nat k -> P a) -> poisoned m' A k v.
  Proof.
    intros A k v (H0 & H8 & U8) HP. split; [exact H0|]. split; [exact H8|]. apply u8arr_pteq; [exact U8|].
    unfold poison_bytes. rewrite repeat_length. exact HP.
  Qed.

End PtEq.

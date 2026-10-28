(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import RT_iface D_defs D_kit D_auxv X_aexdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record xenv_laws (XENV : mem -> Prop) (XENV_FP : list (Z * Z)) : Type := {
  xl_loc      : fp_local XENV_FP XENV;
  xl_core     : mem -> Prop;
  xl_core_fp  : list (Z * Z);
  xl_split    : forall m, XENV m <-> (xl_core m /\ aexA m);
  xl_core_loc : fp_local xl_core_fp xl_core;
  xl_core_sep : forall x, in_ranges AEX_FPA x -> ~ in_ranges xl_core_fp x;
  xl_aex_in   : forall x, in_ranges AEX_FPA x -> in_ranges XENV_FP x;
  xl_core_in  : forall x, in_ranges xl_core_fp x -> in_ranges XENV_FP x;
  xl_libc     : forall m, xl_core m -> exists (cdt thr sec : byte) (tm1 : word),
                  rw_cells bsegs m 0x6cb5f8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1];
  xl_xdata    : forall m, xl_core m -> el_xdataA m
}.

Arguments xl_loc {XENV XENV_FP} _.
Arguments xl_core {XENV XENV_FP} _.
Arguments xl_core_fp {XENV XENV_FP} _.
Arguments xl_split {XENV XENV_FP} _.
Arguments xl_core_loc {XENV XENV_FP} _.
Arguments xl_core_sep {XENV XENV_FP} _.
Arguments xl_aex_in {XENV XENV_FP} _.
Arguments xl_core_in {XENV XENV_FP} _.
Arguments xl_libc {XENV XENV_FP} _.
Arguments xl_xdata {XENV XENV_FP} _.

Lemma aexA_flag0 : forall m, aexA m -> rw_cells bsegs m AEF_INCB [C1 (Z_to_bv 8 0)].
Proof. intros m [(_ & _ & _ & F)|(_ & _ & _ & F)]; exact F. Qed.

Definition AEX_FP3 : list (Z * Z) := [(AEX, AEX + 48); (AEX_A0, AEX_A0 + 16); (TR_LATCH, TR_LATCH + 1)].

Lemma aexA_reflag : forall m m', aexA m ->
  (forall a : word, in_ranges AEX_FP3 (bv_unsigned a) -> m' a = m a) ->
  rw_cells bsegs m' AEF_INCB [C1 (Z_to_bv 8 0)] -> aexA m'.
Proof.
  intros m m' H AG F'.
  assert (C1' : forall lo hi cs A, In (lo, hi) AEX_FP3 -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 HC. apply (rw_cells_agree_nw bsegs m m' _ _ HC). intros a Ha. apply AG. exists lo, hi. split; [exact Hin| lia]. }
  destruct H as [((p1 & p2 & f1 & T) & (a1 & A) & L & _)|((p1 & p2 & T) & A & L & _)].
  - left. split; [exists p1, p2, f1; apply (C1' AEX (AEX + 48)); [cbn; tauto| lia| cbn; unfold AEX; lia| exact T]|].
    split; [exists a1; apply (C1' AEX_A0 (AEX_A0 + 16)); [cbn; tauto| lia| cbn; unfold AEX_A0; lia| exact A]|].
    split; [apply (C1' TR_LATCH (TR_LATCH + 1)); [cbn; tauto| lia| cbn; unfold TR_LATCH; lia| exact L]| exact F'].
  - right. split; [exists p1, p2; apply (C1' AEX (AEX + 48)); [cbn; tauto| lia| cbn; unfold AEX; lia| exact T]|].
    split; [apply (C1' AEX_A0 (AEX_A0 + 16)); [cbn; tauto| lia| cbn; unfold AEX_A0; lia| exact A]|].
    split; [apply (C1' TR_LATCH (TR_LATCH + 1)); [cbn; tauto| lia| cbn; unfold TR_LATCH; lia| exact L]| exact F'].
Qed.

Lemma in_AEX_FP3 : forall x, in_ranges AEX_FP3 x -> in_ranges AEX_FPA x /\ x <> AEF_INCB.
Proof.
  intros x (lo & hi & Hin & Hx). unfold AEX_FP3 in Hin. unfold AEX, AEX_A0, TR_LATCH, AEF_INCB in *.
  split.
  - rewrite in_AEX_FPA_iff. unfold AEX, AEX_A0, TR_LATCH, AEF_INCB. cbn in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - cbn in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Section Laws.
Variables (XENV : mem -> Prop) (XENV_FP : list (Z * Z)).
Variable XL : xenv_laws XENV XENV_FP.

Lemma xenv_open : forall m, XENV m -> xl_core XL m /\ aexA m.
Proof. intros m H. exact (proj1 (xl_split XL m) H). Qed.
Lemma xenv_close : forall m, xl_core XL m -> aexA m -> XENV m.
Proof. intros m H1 H2. exact (proj2 (xl_split XL m) (conj H1 H2)). Qed.
Lemma xenv_close_reg : forall m, xl_core XL m -> aex_reg m -> XENV m.
Proof. intros m H1 H2. apply xenv_close; [exact H1| right; exact H2]. Qed.

Lemma core_keep : forall m m', xl_core XL m ->
  (forall a : word, in_ranges (xl_core_fp XL) (bv_unsigned a) -> m' a = m a) -> xl_core XL m'.
Proof. intros m m' H AG. exact (xl_core_loc XL m m' H AG). Qed.

Lemma core_keep_agree : forall (P : Z -> Prop) m m', xl_core XL m -> agree_on P m m' ->
  (forall x, in_ranges (xl_core_fp XL) x -> P x) -> xl_core XL m'.
Proof. intros P m m' H AG HP. apply (core_keep m m' H). intros a Ha. apply AG. apply HP. exact Ha. Qed.
End Laws.

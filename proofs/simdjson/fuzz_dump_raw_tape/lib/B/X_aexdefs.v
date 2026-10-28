(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import RT_iface D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AEX : Z := 0x6cbe38.
Definition AEX_BUILTIN : Z := 0x6cbe50.
Definition AEX_A0 : Z := 0x6cbf58.
Definition X_CALL : Z := 0x14fd34.
Definition X_COVDUMP : Z := 0x9e22c.
Definition X_AEXGUARD : Z := 0xaebf4.
Definition X_ATEXIT : Z := 0x14fc70.
Definition X_FUNCS_ON_EXIT : Z := 0x14fadc.
Definition TR_LATCH : Z := 0x6aa210.
Definition AEF_INCB : Z := 0x6aa214.

Definition aex_tbl (slot : Z) (p1 p2 : list byte) (f1 : word) : list cell :=
  [C1 (Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 p2;
   C8 (Z_to_bv 64 AEX_BUILTIN); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 X_CALL); C8 f1].

Ltac aex_lits := unfold aex_tbl, AEX, AEX_BUILTIN, AEX_A0, X_CALL, X_COVDUMP, X_AEXGUARD, X_ATEXIT, X_FUNCS_ON_EXIT, TR_LATCH, AEF_INCB in *.

Definition aex_main (m : mem) : Prop :=
  (exists (p1 p2 : list byte) (f1 : word), rw_cells bsegs m AEX (aex_tbl 1 p1 p2 f1))
  /\ (exists a1 : word, rw_cells bsegs m AEX_A0 [C8 (Z_to_bv 64 X_COVDUMP); C8 a1])
  /\ rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m AEF_INCB [C1 (Z_to_bv 8 0)].

Definition aex_reg (m : mem) : Prop :=
  (exists (p1 p2 : list byte), rw_cells bsegs m AEX (aex_tbl 2 p1 p2 (Z_to_bv 64 X_CALL)))
  /\ rw_cells bsegs m AEX_A0 [C8 (Z_to_bv 64 X_COVDUMP); C8 (Z_to_bv 64 X_AEXGUARD)]
  /\ rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m AEF_INCB [C1 (Z_to_bv 8 0)].

Definition aexA (m : mem) : Prop := aex_main m \/ aex_reg m.

Definition AEX_FPA : list (Z * Z) :=
  [(AEX, AEX + 48); (AEX_A0, AEX_A0 + 16); (TR_LATCH, TR_LATCH + 1); (AEF_INCB, AEF_INCB + 1)].

Lemma in_AEX_FPA : forall lo hi x, In (lo, hi) AEX_FPA -> lo <= x < hi -> in_ranges AEX_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Section Loc.
Variables (m m' : mem).
Hypothesis AG : forall a : word, in_ranges AEX_FPA (bv_unsigned a) -> m' a = m a.

Local Lemma carry : forall lo hi cs A, In (lo, hi) AEX_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
  rw_cells bsegs m A cs -> rw_cells bsegs m' A cs.
Proof.
  intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
  intros a Ha. apply AG. apply (in_AEX_FPA lo hi); [exact Hin| lia].
Qed.

Lemma aex_main_agree : aex_main m -> aex_main m'.
Proof.
  intros ((p1 & p2 & f1 & T) & (a1 & A) & L & F).
  split; [exists p1, p2, f1; apply (carry AEX (AEX + 48)); [cbn; tauto| lia| cbn; unfold AEX; lia| exact T]|].
  split; [exists a1; apply (carry AEX_A0 (AEX_A0 + 16)); [cbn; tauto| lia| cbn; unfold AEX_A0; lia| exact A]|].
  split; [apply (carry TR_LATCH (TR_LATCH + 1)); [cbn; tauto| lia| cbn; unfold TR_LATCH; lia| exact L]|].
  apply (carry AEF_INCB (AEF_INCB + 1)); [cbn; tauto| lia| cbn; unfold AEF_INCB; lia| exact F].
Qed.

Lemma aex_reg_agree : aex_reg m -> aex_reg m'.
Proof.
  intros ((p1 & p2 & T) & A & L & F).
  split; [exists p1, p2; apply (carry AEX (AEX + 48)); [cbn; tauto| lia| cbn; unfold AEX; lia| exact T]|].
  split; [apply (carry AEX_A0 (AEX_A0 + 16)); [cbn; tauto| lia| cbn; unfold AEX_A0; lia| exact A]|].
  split; [apply (carry TR_LATCH (TR_LATCH + 1)); [cbn; tauto| lia| cbn; unfold TR_LATCH; lia| exact L]|].
  apply (carry AEF_INCB (AEF_INCB + 1)); [cbn; tauto| lia| cbn; unfold AEF_INCB; lia| exact F].
Qed.

Lemma aexA_agree : aexA m -> aexA m'.
Proof. intros [H|H]; [left; exact (aex_main_agree H)| right; exact (aex_reg_agree H)]. Qed.
End Loc.

Lemma aexA_agree_on : forall m m', aexA m -> agree_on (in_ranges AEX_FPA) m m' -> aexA m'.
Proof. intros m m' H AG. exact (aexA_agree m m' AG H). Qed.

Lemma in_AEX_FPA_iff : forall x, in_ranges AEX_FPA x <->
  (AEX <= x < AEX + 48 \/ AEX_A0 <= x < AEX_A0 + 16 \/ x = TR_LATCH \/ x = AEF_INCB).
Proof.
  intros x. unfold in_ranges, AEX_FPA, AEX, AEX_A0, TR_LATCH, AEF_INCB. split.
  - intros (lo & hi & Hin & Hx). cbn in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - intros [H|[H|[H|H]]];
      [exists 0x6cbe38, (0x6cbe38 + 48)| exists 0x6cbf58, (0x6cbf58 + 16)| exists 0x6aa210, (0x6aa210 + 1)| exists 0x6aa214, (0x6aa214 + 1)];
      (split; [cbn; tauto| lia]).
Qed.

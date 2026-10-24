(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition ctable := tree Z.
Definition ckey (pc : Z) : positive := Z.to_pos (pc + 1).
Definition clookup (t : ctable) (pc : Z) : option Z :=
if 0 <=? pc then tget (ckey pc) t else None.
Section c.
Variable segs : list Segment.
Fixpoint build_table (pc : Z) (n : nat) (t : ctable) : ctable :=
match n with
| O => t
| S n' => build_table (pc + 4) n'
(match fetch_word segs (Z_to_bv 64 pc) with
| Some w => tset (ckey pc) (bv_unsigned w) t
| None => t
end)
end.
Definition table_ok (t : ctable) : Prop :=
forall pc w, clookup t pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Lemma ckey_inj : forall a b, 0 <= a -> 0 <= b -> ckey a = ckey b -> a = b.
Proof. intros a b Ha Hb H. unfold ckey in H. lia. Qed.
Lemma build_table_ok : forall n pc t,
0 <= pc -> table_ok t -> table_ok (build_table pc n t).
Proof.
induction n as [|n IH]; intros pc t Hpc Ht; cbn; [exact Ht|].
apply IH; [lia|].
destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:He; [|exact Ht].
intros pc' w' Hl. unfold clookup in Hl.
destruct (0 <=? pc') eqn:Hpc'; [|discriminate]. apply Z.leb_le in Hpc'.
destruct (Pos.eq_dec (ckey pc) (ckey pc')) as [Heq|Hne].
- rewrite <- Heq, tget_tset_same in Hl. injection Hl as <-.
apply ckey_inj in Heq; [|lia|lia]. rewrite <- Heq, He. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
- rewrite tget_tset_other in Hl by exact Hne. apply Ht. unfold clookup.
replace (0 <=? pc') with true by (symmetry; apply Z.leb_le; lia). exact Hl.
Qed.
Lemma table_ok_empty : table_ok TEmpty.
Proof.
intros pc e H. unfold clookup in H. destruct (0 <=? pc); [|discriminate].
destruct (ckey pc); cbn in H; discriminate.
Qed.
Lemma build_table_ok0 : forall n pc, 0 <= pc -> table_ok (build_table pc n TEmpty).
Proof. intros. apply build_table_ok; [assumption| apply table_ok_empty]. Qed.
End c.

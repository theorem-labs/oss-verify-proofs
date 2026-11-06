(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them; the two code ranges that held cgif-only code (a Theorem Labs lane release 718254b3f4dd README, "Porter does" item 7: the range-content gate) are split into the fuzz_ctrl twins of the donor code they cover, by the release's own function pairing (a Theorem Labs lane's rec3/splitranges.py): __stdio_write's range keeps its first 125 and last 258 instructions' twins and leaves out the 52 donor instructions with no fuzz_ctrl twin; the first interceptor range keeps 24 + 1 + 11 of its 38. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table tfibsegs lo n t) end.
Lemma build_ranges_ok : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok tfibsegs t -> table_ok tfibsegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition musl_sel_ranges : list (Z * nat) :=
[ (0x8e668, 71%nat); (0x93a94, 25%nat); (0x93af8, 87%nat); (0x93904, 125%nat); (0x93af8, 258%nat); (0x94448, 1146%nat); (0x97558, 47%nat);
(0x987d8, 10%nat); (0x9d230, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x4295c, 24%nat); (0x429bc, 1%nat); (0x429c0, 11%nat);  (0x42c80, 165%nat); (0x4372c, 549%nat); (0x43fc0, 94%nat); (0x44138, 180%nat);
(0x44680, 156%nat); (0x448f0, 157%nat); (0x45248, 729%nat); (0x45dac, 45%nat); (0x46178, 54%nat);
(0x484a8, 102%nat); (0x52020, 1009%nat); (0x54718, 79%nat); (0x54ba4, 209%nat); (0x59128, 6%nat);
(0x5a038, 40%nat);  (0x64468, 13%nat);  (0x64508, 7%nat);   (0x6476c, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x529f4 = Some 0x81010113 /\ clookup tbl_icpt 0x97c0c = None /\ clookup tbl_icpt 0x648e4 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

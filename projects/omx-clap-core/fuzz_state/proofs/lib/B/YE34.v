(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE34.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
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
[ (0x8d1e0, 71%nat); (0x928b0, 25%nat); (0x92914, 87%nat); (0x92720, 383%nat); (0x93264, 1146%nat); (0x987e4, 47%nat);
(0x99b08, 10%nat); (0x9e560, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x426c4, 36%nat);  (0x429e8, 165%nat); (0x43494, 549%nat); (0x43d28, 94%nat); (0x43ea0, 180%nat);
(0x443e8, 156%nat); (0x44658, 157%nat); (0x44fb0, 729%nat); (0x45b14, 45%nat); (0x45ee0, 54%nat);
(0x48210, 102%nat); (0x51d88, 1009%nat); (0x547c8, 79%nat); (0x54c54, 209%nat); (0x591d8, 6%nat);
(0x5a0e8, 40%nat);  (0x64518, 13%nat);  (0x645b8, 7%nat);   (0x6481c, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x5275c = Some 0x81010113 /\ clookup tbl_icpt 0x98f3c = None /\ clookup tbl_icpt 0x64994 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

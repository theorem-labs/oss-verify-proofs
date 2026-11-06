(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
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
[ (0x90ffc, 71%nat); (0x96428, 25%nat); (0x9648c, 87%nat); (0x96298, 435%nat); (0x973e0, 1146%nat); (0x9a4f0, 47%nat);
(0x9b7d0, 10%nat); (0xa0228, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x43044, 40%nat); (* pcap's own __wrap_* trampoline run, __wrap_strlen .. __wrap_sigaction (cgif's run lacks __wrap_fread, __wrap_fmemopen) *)  (0x43374, 165%nat); (0x443fc, 549%nat); (0x44c90, 94%nat); (0x44e08, 180%nat);
(0x45350, 156%nat); (0x455c0, 157%nat); (0x45f18, 729%nat); (0x46a7c, 45%nat); (0x46e48, 54%nat);
(0x491f8, 102%nat); (0x52d70, 441%nat); (0x53454, 568%nat); (0x556a4, 79%nat); (0x55b30, 209%nat); (0x5a304, 6%nat);
(0x5b214, 40%nat);  (0x65758, 13%nat);  (0x657f8, 7%nat);   (0x65a5c, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x53744 = Some 0x81010113 /\ clookup tbl_icpt 0x9aba4 = None /\ clookup tbl_icpt 0x65bd4 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

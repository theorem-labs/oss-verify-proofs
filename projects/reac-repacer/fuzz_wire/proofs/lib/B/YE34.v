(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE34.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/B/YE34.v at 4f87de75d67 (donor image sha256 fde52226dc48), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan+UBSan build; icpt_ranges takes __asan_memset, which fuzz_wire.asan-ubsan does not link, out of fuzz_grant's 1009-word range at 0x51b80, now (0x50c0c, 297) and (0x51420, 568), and adds __asan_memmove (0x510b0, 220 words), which lies between them. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP02. From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
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
[ (0x88604, 71%nat); (0x8da30, 25%nat); (0x8da94, 87%nat); (0x8d8a0, 125%nat); (0x8da94, 258%nat); (0x8e3e4, 1146%nat); (0x914f4, 47%nat);
(0x92774, 10%nat); (0x971cc, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x41548, 24%nat); (0x415a8, 1%nat); (0x415ac, 11%nat);  (0x4186c, 165%nat); (0x42318, 549%nat); (0x42bac, 94%nat); (0x42d24, 180%nat);
(0x4326c, 156%nat); (0x434dc, 157%nat); (0x43e34, 729%nat); (0x44998, 45%nat); (0x44d64, 54%nat);
(0x47094, 102%nat); (0x50c0c, 297%nat); (0x510b0, 220%nat); (0x51420, 568%nat); (0x53434, 79%nat); (0x538c0, 209%nat); (0x57e44, 6%nat);
(0x58d54, 40%nat);  (0x63184, 13%nat);  (0x63224, 7%nat);   (0x63488, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x51710 = Some 0x81010113 /\ clookup tbl_icpt 0x91ba8 = None /\ clookup tbl_icpt 0x63600 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

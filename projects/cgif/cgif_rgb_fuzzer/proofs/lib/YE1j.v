(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Fixpoint build_ranges {imgk : img} (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table tfxsegs lo n t) end.
Lemma build_ranges_ok {imgk : img} : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok tfxsegs t -> table_ok tfxsegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [img_try (img_exact Ht)|].
inversion Hrs; (subst; cbv beta). img_apply IH; [img_try (assumption)|]. img_apply build_table_ok; [img_try (cbn in *; assumption) | img_try (img_exact Ht)].
Qed.
Definition musl_sel_ranges {imgk : img} : list (Z * nat) :=
[ ((0x91a74 + D_104c), 71%nat); ((0x97078 + D_10ec), 25%nat); ((0x971ac + D_10ec), 87%nat); ((0x96ee8 + D_10ec), 435%nat); ((0x97ccc + D_10ec), 1146%nat); ((0x9addc + D_10ec), 47%nat);
((0x9c05c + D_10ec), 10%nat); ((0xa0ab4 + D_10ec), 69%nat) ].
Definition icpt_ranges {imgk : img} : list (Z * nat) :=
musl_sel_ranges ++
[ ((0x420c4 + D_2c4), 38%nat);  ((0x423f0 + D_2c4), 165%nat); ((0x42e9c + D_2c4), 549%nat); ((0x43730 + D_2c4), 94%nat); ((0x438a8 + D_2c4), 180%nat);
((0x43df0 + D_2c4), 156%nat); ((0x44060 + D_2c4), 157%nat); ((0x449b8 + D_2c4), 729%nat); ((0x4551c + D_2c4), 45%nat); ((0x458e8 + D_2c4), 54%nat);
((0x48230 + D_2c4), 102%nat); ((0x51da8 + D_2c4), 1009%nat); ((0x547e8 + D_2c4), 79%nat); ((0x54c74 + D_2c4), 209%nat); ((0x591f8 + D_2c4), 6%nat);
((0x5a108 + D_2c4), 40%nat);  ((0x64538 + D_2c4), 13%nat);  ((0x645d8 + D_2c4), 7%nat);   ((0x6483c + D_2c4), 12%nat) ].
Definition tbl_icpt {imgk : img} : ctable := ltac:(img_eval_sel (fun imgk : img => (build_ranges icpt_ranges TEmpty))).
Lemma tbl_icpt_eq {imgk : img} : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. img_case; lazymatch goal with |- ?l_ = _ => vm_cast_no_check (@eq_refl ctable l_) end. Qed.
Lemma tbl_icpt_ok {imgk : img} : table_ok tfxsegs tbl_icpt.
Proof. img_destruct imgk.
all: rewrite tbl_icpt_eq. all: img_apply build_ranges_ok; [| img_try (img_apply table_ok_empty)].
all: unfold icpt_ranges, musl_sel_ranges. all: cbn [app]. all: repeat constructor; cbn; discriminate.
Qed.


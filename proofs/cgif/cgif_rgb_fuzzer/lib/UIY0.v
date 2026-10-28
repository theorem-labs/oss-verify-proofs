(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition CBL_STK_U : Z := 80.
Definition UOFF_A : Z := 0x7c.
Definition UOFF_B : Z := 0x9c.
Definition UOFF_C : Z := 0x108.
Definition UOFF_X : Z := 0x1f0.
Definition NOTBL : afact := mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0.
Definition sr_cblu : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 17%bv (SLit 1)) 6%bv (SLit 11)) 7%bv (SLit 8))
28%bv (SLit 15)) 31%bv (SLit 16)) 30%bv (SLit 1).
Lemma regs_ok_cblu : forall regs extra,
getr regs 17 = Z_to_bv 64 1 -> getr regs 6 = Z_to_bv 64 11 -> getr regs 7 = Z_to_bv 64 8 ->
getr regs 28 = Z_to_bv 64 15 -> getr regs 31 = Z_to_bv 64 16 -> getr regs 30 = Z_to_bv 64 1 ->
regs_ok (Ereg regs extra) sr_cblu regs.
Proof using.
intros regs extra H17 H6 H7 H28 H31 H30. unfold sr_cblu.
repeat (apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; assumption]).
apply regs_ok_Ereg.
Qed.
Definition cblu_facts_core : list (nat * afact) :=
[ (10%nat, mkAF 4096 CEIL_MAX 4); (12%nat, mkAF 4096 CEIL_MAX 0); (5%nat, NOTBL);
(8%nat, mkAF 4096 CEIL_MAX 0); (9%nat, mkAF 4096 CEIL_MAX 0); (29%nat, mkAF 1 (2 ^ 28) 0);
(13%nat, mkAF 0 65535 0); (14%nat, mkAF 0 12 0); (16%nat, mkAF 0 131070 0);
(15%nat, mkAF 0 (2 ^ 29) 0); (18%nat, mkAF 0 12 0) ].
Definition cblu_facts_A : list (nat * afact) := cblu_facts_core ++ [ (20%nat, mkAF 0 7 0) ].
Definition cblu_facts_B : list (nat * afact) :=
cblu_facts_core ++ [ (20%nat, mkAF 0 7 0); (32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 0 65535 0);
(34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0) ].
Definition cblu_facts_C : list (nat * afact) := cblu_facts_core ++ [ (21%nat, mkAF 0 31 0); (33%nat, mkAF 0 65535 0) ].
Definition R9 : YQ0b.region := YQ0b.mkRegion (Some 9%nat) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff 33%nat 0))].
Definition cblu_cond : list acond := [ mkAC BC_GEU (SOff 8%nat 0) (SOff 12%nat 0) ].
Definition cbl_regs_fix_u (regs : bvmap 5 word) (bl lz D C0 : Z) : Prop :=
getr regs 10 = Z_to_bv 64 bl /\ getr regs 12 = Z_to_bv 64 lz /\
getr regs 13 = Z_to_bv 64 D /\ getr regs 14 = Z_to_bv 64 C0 /\ getr regs 16 = Z_to_bv 64 (2 * D) /\
getr regs 5 = Z_to_bv 64 (2 ^ 64 - 1 - bl) /\
getr regs 17 = Z_to_bv 64 1 /\ getr regs 6 = Z_to_bv 64 11 /\ getr regs 7 = Z_to_bv 64 8 /\
getr regs 28 = Z_to_bv 64 15 /\ getr regs 31 = Z_to_bv 64 16 /\ getr regs 30 = Z_to_bv 64 1.
Definition KEPTU : list reg := [1; 2; 3; 4; 25; 26; 27]%bv.
End c.
Ltac cnormu H HE18 HE20 :=
first [ rewrite branch_ltu_U in H | rewrite branch_geu_U in H | rewrite branch_eq_U in H | rewrite branch_ne_U in H ];
rewrite ?(U_t6 _ 18 _ _ 20 _ HE18 HE20) in H by lia;
rewrite ?(U_and255 _ 18 _ _ HE18) in H by lia;
rewrite ?U_lit in H by lia0;
first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H
| apply (proj1 (Bool.negb_true_iff _)) in H; first [apply Z.ltb_ge in H | apply Z.eqb_neq in H]
| apply (proj1 (Bool.negb_false_iff _)) in H; first [apply Z.ltb_lt in H | apply Z.eqb_eq in H] ].

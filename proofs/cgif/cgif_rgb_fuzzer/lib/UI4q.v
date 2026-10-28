(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YN06 YQ0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c YP0d.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02
UI1i UI11 YP14 YI08 YI0c UI3d UI3h UI4v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
UI4r UI4s UI3w UI41 UI4n UI3o UI3u UI4i UI42 UI3z UI4m UI47 UI4k UI4p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UIZ8 YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis NTN : forall fx', ntn_spec (fx:=fx') API.
Hypothesis GETPAL : forall fx', getpal_spec (fx:=fx') API.
Hypothesis FCHT : forall fx', free_cht_spec (fx:=fx') API.
Hypothesis FTREE : forall fx', free_tree_spec (fx:=fx') API.
Hypothesis ADDF : forall fx', addframe_specG (fx:=fx') API.
Hypothesis COLHASH : forall fx', col_hash_spec (fx:=fx') API.
Hypothesis REALLOC : realloc_realizes ubs2_msyms MR.
Local Ltac seg L := first
[ apply (L API IMG FCHT FTREE) | apply (L API IMG FCHT) | apply (L API IMG FTREE) | apply (L API IMG) ].
Lemma ubs2_all_segments :
forall L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest,
all_segments API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros. unfold all_segments.
split; [apply (ubs2_rgbadd_E1 API IMG)|].
split; [apply (ubs2_rgbadd_E2 API IMG)|].
split; [intro i; first [apply (ubs2_rgbadd_HB API IMG) | apply ubs2_rgbadd_HB]|].
split; [intro i; first [apply (ubs2_rgbadd_HR API IMG REALLOC FCHT COLHASH) | apply (ubs2_rgbadd_HR API IMG REALLOC COLHASH FCHT)]|].
split; [apply (ubs2_rgbadd_Q0 API IMG (COLHASH _))|].
split; [apply (ubs2_rgbadd_CR API IMG NTN)|].
split; [apply (ubs2_rgbadd_QT API IMG GETPAL)|].
split; [apply (ubs2_rgbadd_DI API IMG (fun fx' => ubs2_get_leave_node_index (fx:=fx') API))|].
split; [apply (ubs2_rgbadd_ND API IMG (fun fx' => ubs2_get_leave_node_index (fx:=fx') API))|].
split; [seg ubs2_rgbadd_QE|].
split; [first [apply (ubs2_rgbadd_SM API IMG (COLHASH _) FCHT) | apply (ubs2_rgbadd_SM API IMG (COLHASH _))]|].
split; [apply (ubs2_rgbadd_FIN API IMG ADDF)|].
split; [seg ubs2_rgbadd_X38|].
split; [apply (ubs2_rgbadd_XB API IMG)|].
split; [apply (ubs2_rgbadd_XF API IMG)|].
split; [apply (ubs2_rgbadd_XS API IMG)|].
split; [seg ubs2_rgbadd_XC|].
split; [seg ubs2_rgbadd_XD|].
split; [seg ubs2_rgbadd_XT|].
seg ubs2_rgbadd_XT2.
Qed.
Theorem ubs2_rgb_addframe : rgb_addframe_spec API.
Proof. exact (rgb_addframe_of_segments API ubs2_all_segments). Qed.
End b.
End a.

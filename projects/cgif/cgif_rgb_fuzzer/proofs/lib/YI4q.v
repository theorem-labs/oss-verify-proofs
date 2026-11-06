(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YN06 YQ0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c YP0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02
YI1i YI11 YP14 YI08 YI0c YI3d YI3h YI4v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YI4r YI4s YI3w YI41 YI4n YI3o YI3u YI4i YI42 YI3z YI4m YI47 YI4k YI4p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Hypothesis IMG : img_laws src2_msyms MR.
Hypothesis NTN : forall fx', ntn_spec (fx:=fx') API.
Hypothesis GETPAL : forall fx', getpal_spec (fx:=fx') API.
Hypothesis FCHT : forall fx', free_cht_spec (fx:=fx') API.
Hypothesis FTREE : forall fx', free_tree_spec (fx:=fx') API.
Hypothesis ADDF : forall fx', addframe_specG (fx:=fx') API.
Hypothesis COLHASH : forall fx', col_hash_spec (fx:=fx') API.
Hypothesis REALLOC : realloc_realizes src2_msyms MR.
Local Ltac seg L := first
[ apply (L API IMG FCHT FTREE) | apply (L API IMG FCHT) | apply (L API IMG FTREE) | apply (L API IMG) ].
Lemma src2_all_segments :
forall L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest,
all_segments API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros. unfold all_segments.
split; [apply (src2_rgbadd_E1 API IMG)|].
split; [apply (src2_rgbadd_E2 API IMG)|].
split; [intro i; first [apply (src2_rgbadd_HB API IMG) | apply src2_rgbadd_HB]|].
split; [intro i; first [apply (src2_rgbadd_HR API IMG REALLOC FCHT COLHASH) | apply (src2_rgbadd_HR API IMG REALLOC COLHASH FCHT)]|].
split; [apply (src2_rgbadd_Q0 API IMG (COLHASH _))|].
split; [apply (src2_rgbadd_CR API IMG NTN)|].
split; [apply (src2_rgbadd_QT API IMG GETPAL)|].
split; [first [apply (src2_rgbadd_DI API IMG) | apply src2_rgbadd_DI]|].
split; [first [apply (src2_rgbadd_ND API IMG) | apply src2_rgbadd_ND]|].
split; [seg src2_rgbadd_QE|].
split; [first [apply (src2_rgbadd_SM API IMG (COLHASH _) FCHT) | apply (src2_rgbadd_SM API IMG (COLHASH _))]|].
split; [apply (src2_rgbadd_FIN API IMG ADDF)|].
split; [seg src2_rgbadd_X38|].
split; [apply (src2_rgbadd_XB API IMG)|].
split; [apply (src2_rgbadd_XF API IMG)|].
split; [apply (src2_rgbadd_XS API IMG)|].
split; [seg src2_rgbadd_XC|].
split; [seg src2_rgbadd_XD|].
split; [seg src2_rgbadd_XT|].
seg src2_rgbadd_XT2.
Qed.
Theorem src2_rgb_addframe : rgb_addframe_spec API.
Proof. exact (rgb_addframe_of_segments API src2_all_segments). Qed.
End b.
End a.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0g.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YG0g.v (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_role. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YG0g.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YP09 YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK08 YK0v YK13.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.BudgetWit.AW Require Import YA05_w YA06_w YG0b_w.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YP0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0g.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG0f YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.BudgetWit.AW Require Import YG0n_w YG0s_w YG0q_w.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section c.
Local Open Scope Z_scope.
Definition shna (md : Model) : Prop :=
region_free (vm_noaccess (m_vmmaps md)) (w64 kLowShadowBeg) (w64 (kLowShadowEnd - kLowShadowBeg)) = true /\
region_free (vm_noaccess (m_vmmaps md)) (w64 kHighShadowBeg) (w64 (kHighShadowEnd - kHighShadowBeg)) = true.
Lemma shna_of_uncovered : forall md,
(forall q, In q (vm_noaccess (m_vmmaps md)) -> 0 < bv_unsigned (snd q)) ->
(forall x, kLowShadowBeg <= x < kLowShadowEnd \/ kHighShadowBeg <= x < kHighShadowEnd -> YK0g.covered (vm_noaccess (m_vmmaps md)) x = false) ->
shna md.
Proof.
intros md Hpos Hcov. split; apply region_free_of_uncovered; try exact Hpos.
- unfold w64. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
- intros x Hx. apply Hcov. left. unfold w64, kLowShadowBeg, kLowShadowEnd in *. rewrite !Z_to_bv_unsigned in Hx.
rewrite !bv_wrap_small in Hx by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
- unfold w64. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
- intros x Hx. apply Hcov. right. unfold w64, kHighShadowBeg, kHighShadowEnd in *. rewrite !Z_to_bv_unsigned in Hx.
rewrite !bv_wrap_small in Hx by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
End c.

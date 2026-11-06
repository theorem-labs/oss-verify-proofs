(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import ImgZero AsanHexScan3 AsanPlanImages AsanDepotMem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)
Open Scope Z_scope.

Lemma asan_tab_img_zero_chk : img_zero3_chk ASEGS DEPOT 4194304 = true.   (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.

Lemma asan_tab_img_zero : forall x : word,
  DEPOT <= bv_unsigned x < DEPOT + 4194304 -> seg_rom ASEGS x = Some (Z_to_bv 8 0).
Proof. apply (img_zero3_chk_sound ASEGS DEPOT 4194304 asan_tab_img_zero_chk); lia. Qed.

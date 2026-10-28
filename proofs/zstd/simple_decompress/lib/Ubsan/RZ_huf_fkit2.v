(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma div10_magic : forall x, 0 <= x < 2^64 -> x * 14757395258967641293 / 2^64 / 8 = x / 10.
Proof. intros x Hx. Z.div_mod_to_equations; lia. Qed.

Definition HUF_CTZ_TBL2 : Z := 0x11078.
Lemma huf_ctz_tbl2 : forall m, mem_inv usegs m -> tbl_in usegs m HUF_CTZ_TBL2 64 1 0 0 63.
Proof.
  intros m MI. unfold HUF_CTZ_TBL2.
  destruct (image_bytes usegs 0x11078 64) as [bs|] eqn:EB; [|vm_compute in EB; discriminate EB].
  assert (LB : length bs = 64%nat) by exact (image_bytes_length usegs 64 _ _ EB).
  assert (HB : bytes_at usegs m 0x11078 bs).
  { apply ro_bytes_at; [exact MI | lia | rewrite LB; lia |]. apply ro_bytes_b_sound.
    vm_compute in EB. injection EB as <-. vm_compute. reflexivity. }
  pose proof (tbl_in_bytes_at usegs m 0x11078 bs 1 0 0 63 HB ltac:(lia) ltac:(lia)) as T. rewrite LB in T. apply T.
  intros i Hi Hs. vm_compute in EB. injection EB as <-.
  assert (Hn : (Z.to_nat (1 * i + 0) < 64)%nat) by lia.
  remember (Z.to_nat (1 * i + 0)) as k eqn:Ek. clear - Hn.
  do 64 (destruct k as [|k]; [eexists; split; [reflexivity | vm_compute; split; discriminate]|]). lia.
Qed.

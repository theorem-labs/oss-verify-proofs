(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_su_tool.v (commit eb934de95d13, blob 73c74ab517b3) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YK1b YK07 YK0c YK0e YK09 YA01 YA0c YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB13 AB01 AB03.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import APG.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Definition RA_TOOL_NAME_CELL : Z := 671448.
Definition RA_TOOL_NAME_STR : Z := 132163.
Definition asan_tool_name : list Z := [65; 100; 100; 114; 101; 115; 115; 83; 97; 110; 105; 116; 105; 122; 101; 114; 0].

Definition su_tool_ok (ch : acs) : bool :=
  match kn_read tfibsegs ch (ELit 0) RA_TOOL_NAME_CELL 8 with
  | Some e => expr_eqb e (ELit RA_TOOL_NAME_STR)
  | None => false
  end.

Lemma su_tool_ok_sound : forall ch, su_tool_ok ch = true ->
  kn_read tfibsegs ch (ELit 0) RA_TOOL_NAME_CELL 8 = Some (ELit RA_TOOL_NAME_STR).
Proof.
intros ch H. unfold su_tool_ok in H.
destruct (kn_read tfibsegs ch (ELit 0) RA_TOOL_NAME_CELL 8) as [e|]; [|discriminate H].
apply expr_eqb_eq in H. subst e. reflexivity.
Qed.

Lemma su_tool_hs_all : forallb su_tool_ok HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma su_tool_cell_A : forall h ch, HS_tfib h = Some ch ->
  kn_read tfibsegs ch (ELit 0) RA_TOOL_NAME_CELL 8 = Some (ELit RA_TOOL_NAME_STR).
Proof.
intros h ch H. apply su_tool_ok_sound.
exact (proj1 (forallb_forall su_tool_ok HS_tfib_list) su_tool_hs_all ch (HS_tfib_In h ch H)).
Qed.

Lemma su_tool_band_A :
  kn_read tfibsegs JS_tfib_band (ELit 0) RA_TOOL_NAME_CELL 8 = Some (ELit RA_TOOL_NAME_STR).
Proof. apply su_tool_ok_sound. vm_compute. reflexivity. Qed.

Definition su_tool_byte_ok (k : nat) : bool :=
  match hex_byte_at Asan_seg_bytes_000 (Z.to_N (RA_TOOL_NAME_STR - 0x10000) + N.of_nat k) with
  | Some b => Z.eqb (bv_unsigned b) (nth k asan_tool_name 0)
  | None => false
  end.

Lemma su_tool_bytes_ok : forallb su_tool_byte_ok (seq 0 17) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma su_tool_str_A : forall k, (k < 17)%nat ->
  seg_rom tfibsegs (Z_to_bv 64 (RA_TOOL_NAME_STR + Z.of_nat k)) = Some (Z_to_bv 8 (nth k asan_tool_name 0)).
Proof.
intros k Hk. rewrite tfib_rom0 by (unfold RA_TOOL_NAME_STR; lia).
assert (B : su_tool_byte_ok k = true).
{ apply (proj1 (forallb_forall su_tool_byte_ok (seq 0 17)) su_tool_bytes_ok). apply in_seq. lia. }
unfold su_tool_byte_ok in B.
replace (Z.to_N (RA_TOOL_NAME_STR + Z.of_nat k - 0x10000))
  with (Z.to_N (RA_TOOL_NAME_STR - 0x10000) + N.of_nat k)%N by (unfold RA_TOOL_NAME_STR; lia).
destruct (hex_byte_at Asan_seg_bytes_000 (Z.to_N (RA_TOOL_NAME_STR - 0x10000) + N.of_nat k)) as [b|];
  [|discriminate B].
apply Z.eqb_eq in B. f_equal. apply bv_eq. rewrite B.
do 17 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Theorem su_tool_A :
  (forall h ch, HS_tfib h = Some ch ->
     kn_read tfibsegs ch (ELit 0) RA_TOOL_NAME_CELL 8 = Some (ELit RA_TOOL_NAME_STR)) /\
  kn_read tfibsegs JS_tfib_band (ELit 0) RA_TOOL_NAME_CELL 8 = Some (ELit RA_TOOL_NAME_STR) /\
  (forall k, (k < 17)%nat ->
     seg_rom tfibsegs (Z_to_bv 64 (RA_TOOL_NAME_STR + Z.of_nat k)) = Some (Z_to_bv 8 (nth k asan_tool_name 0))).
Proof. exact (conj su_tool_cell_A (conj su_tool_band_A su_tool_str_A)). Qed.

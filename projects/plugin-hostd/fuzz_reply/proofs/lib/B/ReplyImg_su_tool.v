(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Row img-su-tool-B of REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record) (CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) line 153, class A11): "the cell holds
   \"AddressSanitizer\0\"".  The B twin of a Theorem Labs lane's lib/A/ReplyImg_su_tool.v
   (a working branch 6302064e89f7), same structure and the same consumer stem su_tool, so lane W's
   A -> B relocation maps by name.  That row carries no cf-layer accessor (unlike HOOM's as_oom_byte), so per the
   pool brief the text below is the UNFOLDED one, over the unit's own tfibsegs.

   The two image numerals are reply image B's OWN, measured here from fuzz_reply.asan-ubsan (unstripped twin sha256
   3389287e1d610784..., the twin lib/B/YF0m.v and lib/B/CfImgB.v cite), never carried over from reply A or from cgif:
   - RB_TOOL_NAME_CELL 654904 = 0x9fe38, the 8-byte _ZN11__sanitizer17SanitizerToolNameE (reply A: 653496 = 0x9f8b8);
   - RB_TOOL_NAME_STR 131951 = 0x2036f, "AddressSanitizer\0", its ONLY occurrence in the loaded image (A: 131946);
   - the image's own copy of the cell still holds 0x19b47 = "SanitizerTool\0", so 131951 is the value the start-up
     run writes, which is why the statement is about the start-up states and not about the image bytes of the cell.
   No table is read by a literal (address, byte) pair: the cell goes through kn_read over the unit's own start-up
   states, and the 17 string bytes through this image's own lemma YB13.tfib_rom0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YK1b YK07 YK0c YK0e YK09 YA01 YA0c YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB13 YB01 YB03.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import APG.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Definition RB_TOOL_NAME_CELL : Z := 654904.
Definition RB_TOOL_NAME_STR : Z := 131951.
Definition asan_tool_name : list Z := [65; 100; 100; 114; 101; 115; 115; 83; 97; 110; 105; 116; 105; 122; 101; 114; 0].

Definition su_tool_ok (ch : acs) : bool :=
  match kn_read tfibsegs ch (ELit 0) RB_TOOL_NAME_CELL 8 with
  | Some e => expr_eqb e (ELit RB_TOOL_NAME_STR)
  | None => false
  end.

Lemma su_tool_ok_sound : forall ch, su_tool_ok ch = true ->
  kn_read tfibsegs ch (ELit 0) RB_TOOL_NAME_CELL 8 = Some (ELit RB_TOOL_NAME_STR).
Proof.
intros ch H. unfold su_tool_ok in H.
destruct (kn_read tfibsegs ch (ELit 0) RB_TOOL_NAME_CELL 8) as [e|]; [|discriminate H].
apply expr_eqb_eq in H. subst e. reflexivity.
Qed.

Lemma su_tool_hs_all : forallb su_tool_ok HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma su_tool_cell_B : forall h ch, HS_tfib h = Some ch ->
  kn_read tfibsegs ch (ELit 0) RB_TOOL_NAME_CELL 8 = Some (ELit RB_TOOL_NAME_STR).
Proof.
intros h ch H. apply su_tool_ok_sound.
exact (proj1 (forallb_forall su_tool_ok HS_tfib_list) su_tool_hs_all ch (HS_tfib_In h ch H)).
Qed.

Lemma su_tool_band_B :
  kn_read tfibsegs JS_tfib_band (ELit 0) RB_TOOL_NAME_CELL 8 = Some (ELit RB_TOOL_NAME_STR).
Proof. apply su_tool_ok_sound. vm_compute. reflexivity. Qed.

Definition su_tool_byte_ok (k : nat) : bool :=
  match hex_byte_at AsanUbsan_seg_bytes_000 (Z.to_N (RB_TOOL_NAME_STR - 0x10000) + N.of_nat k) with
  | Some b => Z.eqb (bv_unsigned b) (nth k asan_tool_name 0)
  | None => false
  end.

Lemma su_tool_bytes_ok : forallb su_tool_byte_ok (seq 0 17) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma su_tool_str_B : forall k, (k < 17)%nat ->
  seg_rom tfibsegs (Z_to_bv 64 (RB_TOOL_NAME_STR + Z.of_nat k)) = Some (Z_to_bv 8 (nth k asan_tool_name 0)).
Proof.
intros k Hk. rewrite tfib_rom0 by (unfold RB_TOOL_NAME_STR; lia).
assert (B : su_tool_byte_ok k = true).
{ apply (proj1 (forallb_forall su_tool_byte_ok (seq 0 17)) su_tool_bytes_ok). apply in_seq. lia. }
unfold su_tool_byte_ok in B.
replace (Z.to_N (RB_TOOL_NAME_STR + Z.of_nat k - 0x10000))
  with (Z.to_N (RB_TOOL_NAME_STR - 0x10000) + N.of_nat k)%N by (unfold RB_TOOL_NAME_STR; lia).
destruct (hex_byte_at AsanUbsan_seg_bytes_000 (Z.to_N (RB_TOOL_NAME_STR - 0x10000) + N.of_nat k)) as [b|];
  [|discriminate B].
apply Z.eqb_eq in B. f_equal. apply bv_eq. rewrite B.
do 17 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Theorem su_tool_B :
  (forall h ch, HS_tfib h = Some ch ->
     kn_read tfibsegs ch (ELit 0) RB_TOOL_NAME_CELL 8 = Some (ELit RB_TOOL_NAME_STR)) /\
  kn_read tfibsegs JS_tfib_band (ELit 0) RB_TOOL_NAME_CELL 8 = Some (ELit RB_TOOL_NAME_STR) /\
  (forall k, (k < 17)%nat ->
     seg_rom tfibsegs (Z_to_bv 64 (RB_TOOL_NAME_STR + Z.of_nat k)) = Some (Z_to_bv 8 (nth k asan_tool_name 0))).
Proof. exact (conj su_tool_cell_B (conj su_tool_band_B su_tool_str_B)). Qed.

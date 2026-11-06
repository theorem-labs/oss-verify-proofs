(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_su_tool.v (commit 4d286b2e618d, file sha256 43815026aa8e) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 2 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 0 list indices re-picked, and 2 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Row img-su-tool-B of the internal file REPLY-IMG-ROWS.md (the internal file CF-UNIT-HYPS.md line 153, class A11): "the cell holds
   \"AddressSanitizer\0\"".  The B twin of a Theorem Labs lane's lib/A/PresetImg_su_tool.v
   (6302064e89f7), same structure and the same consumer stem su_tool, so lane W's
   A -> B relocation maps by name.  That row carries no cf-layer accessor (unlike HOOM's as_oom_byte), so per the
   pool brief the text below is the UNFOLDED one, over the unit's own tfibsegs.

   The two image numerals are reply image B's OWN, measured here from fuzz_reply.asan-ubsan (unstripped twin sha256
   3389287e1d610784..., the twin lib/B/YF0m.v and lib/B/CfImgB.v cite), never carried over from reply A or from cgif:
   - RB_TOOL_NAME_CELL 654904 = 0xa4718, the 8-byte _ZN11__sanitizer17SanitizerToolNameE (reply A: 653496 = 0x9f8b8);
   - RB_TOOL_NAME_STR 131951 = 0x20449, "AddressSanitizer\0", its ONLY occurrence in the loaded image (A: 131946);
   - the image's own copy of the cell still holds 0x19b47 = "SanitizerTool\0", so 131951 is the value the start-up
     run writes, which is why the statement is about the start-up states and not about the image bytes of the cell.
   No table is read by a literal (address, byte) pair: the cell goes through kn_read over the unit's own start-up
   states, and the 17 string bytes through this image's own lemma YB13.tfib_rom0. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YK1b YK07 YK0c YK0e YK09 YA01 YA0c YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB13 YB01 YB03.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import APG.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Definition RB_TOOL_NAME_CELL : Z := 673560.
Definition RB_TOOL_NAME_STR : Z := 132169.
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

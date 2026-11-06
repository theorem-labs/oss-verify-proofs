(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, the image-B (asan-ubsan) allocator-instance facts PALib at TfibB, which
   lib/B/W_asm.v takes as its hypothesis TL.  TfibB_libS is relocated from proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v
   TfibB_libS (released): same record (lib/B/YCeg.v TfibLib), B's own errno address and image segments; B's
   lib_const_addr is empty, so its clause is vacuous.  pb_palib_tfib then proves the seven PALib fields of
   lib/B/W_kit.v at the image instance PB_fr: the GOT-shadow / shadow-cell equalities and their separation by
   computing the placement (A_OBJ 0 = 0x9df50, A_OBJ 30 = 0xa6638), the api_env field from YCeg.tl_env, and the
   malloc / free wrapper and return-address fields by computing over Tfib_code and PB_fr's symbol table. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0l YF0m YCej YCe5 YCeg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_tbl W_img W_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ACfi.v:25 TfibB_libS on image B.  The errno word sits in the data segment; the segment is found by a decided
   search over the image's loaded segments rather than by its index. *)
Theorem TfibB_libS : TfibLib YD2l.TfibB.
Proof.
constructor; try reflexivity.
-   cbn [as_errno YD2l.TfibB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
-
intros a Ha. cbn [as_errno YD2l.TfibB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
assert (Hchk : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x5d994c)
  && (0x5d994c + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool tfibsegs = true)
by (vm_compute; reflexivity).
apply existsb_exists in Hchk as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin | lia].
-   intros a Ha. unfold lib_const_addr in Ha. destruct Ha.
-   cbn [as_gp YD2l.TfibB]. unfold TFIB_GP. lia.
Qed.

Ltac pal_num := lazymatch goal with
| |- ?x <= ?y => let a := eval vm_compute in x in let b := eval vm_compute in y in change (a <= b); lia
| |- ?x < ?y => let a := eval vm_compute in x in let b := eval vm_compute in y in change (a < b); lia
end.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Theorem pb_palib_tfib : PALib (PI := PB_fr) YD2l.TfibB.
Proof.
constructor.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- left. pal_num.
- pose proof (tl_env YD2l.TfibB TfibB_libS) as H. exact H.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- split; pal_num.
Qed.
End p.

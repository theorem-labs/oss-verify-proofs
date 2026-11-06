(* The two image rows of reply B that the relocated cf refill cites in place of cgif's YGcfImgcgif.cf_errbuf_obj_cgif /
   relro_seg_cgif (the third, cf_exh_off, is ReplyImgRowsB.exh_off_B): the errbuf object of CfImg_B (B/CfImgB.v:34,
   __asan::error_message_buffer at 0xa5ea8 in image B), and the RELRO row [cf_relro_lo, cf_relro_hi) = [0x9d9b8, 0x9f000)
   of CfImg_B (image B's PT_GNU_RELRO) inside one segment of reply B's tfibsegs. Image B's twin of lib/A/ReplyImgRefillA.v.
   EVENT-FREE.  rule 24: no function proved (kind: image facts, proved by computation on reply B's segment table). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyRelroGeoB.
Import ListNotations.
Open Scope Z_scope.

Lemma cf_errbuf_obj_B : @cf_errbuf_obj CfImg_B = 0xa5ea8.
Proof. reflexivity. Qed.

(* Part 3c: relro_seg_t also covers cf_ro_reads (Reusable/YG0ncf.v:647-650); ReplyRelroGeoB's row proves that form. *)
Lemma relro_seg_B : YG0ncf.relro_seg_t (ci := CfImg_B) tfibsegs.
Proof. exact ReplyRelroGeoB.relro_seg_reply_B. Qed.

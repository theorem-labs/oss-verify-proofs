(* The two image rows of reply A that the relocated cf refill cites in place of cgif's YGcfImgcgif.cf_errbuf_obj_cgif /
   relro_seg_cgif (the third, cf_exh_off, is ReplyImgRowsA.exh_off_A): the errbuf object of CfImg_A (A/CfImgA.v), and
   the RELRO row [cf_relro_lo, cf_relro_hi) = [0x9d438, 0x9f000) of CfImg_A inside one segment of reply's tfibsegs.
   EVENT-FREE.  rule 24: no function proved (kind: image facts, proved by computation on reply's segment table). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyRelroGeoA.
Import ListNotations.
Open Scope Z_scope.

Lemma cf_errbuf_obj_A : @cf_errbuf_obj CfImg_A = 0xa5928.
Proof. reflexivity. Qed.

(* Part 3c: relro_seg_t also covers cf_ro_reads (Reusable/YG0ncf.v:647-650); a Theorem Labs lane's row proves that form. *)
Lemma relro_seg_A : YG0ncf.relro_seg_t (ci := CfImg_A) tfibsegs.
Proof. exact ReplyRelroGeoA.relro_seg_reply_A. Qed.

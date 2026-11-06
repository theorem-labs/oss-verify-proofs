(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/omx-clap-core/fuzz_state/lib/A/FSRealloc_S1_tbl.v (hub ddc081c1a03, blob f434810b61d6) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025), every image numeral moved by symbol + offset; it compiles on image A; record, the internal file A5.md. *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/FSRealloc_S1_tbl.v (hub 96e1d2182ec6, blob 11abb9e52a4f), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rr_build : ctable := build_table tfibsegs 0x53c24 118%nat (build_table tfibsegs 0x3302c 131%nat tfibtbl_rtA).
Definition tfibtbl_rr : ctable := Eval vm_compute in tfibtbl_rr_build.
Lemma tfibtbl_rr_eq : tfibtbl_rr = tfibtbl_rr_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rr). Qed.
Lemma tfibtbl_rr_ok : table_ok tfibsegs tfibtbl_rr.
Proof. rewrite tfibtbl_rr_eq. unfold tfibtbl_rr_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.

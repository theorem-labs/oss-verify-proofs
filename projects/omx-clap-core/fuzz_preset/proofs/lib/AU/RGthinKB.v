(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinK.v (hub 66a127cb11e, blob b4a97a8df297) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025), module paths and every image numeral moved by symbol + offset; record, the internal file A5.md. *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGthinK.v (hub 96e1d2182ec6, blob e967ffbc7fba), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
Open Scope Z_scope.

Definition RT_PCR : Z := 0x53828.
Definition RT_ICPT : Z := 0x53c24.
Definition RT_PC0 : Z := 0x53d60.
Definition RT_AREALLOC : Z := 0x3302c.
Definition RT_REALLOCATE : Z := 0x330d8.
Definition RT_PCA : Z := 0x326a4.
Definition RT_PCD : Z := 0x32390.
Definition RT_PCM : Z := 0x9bb04.
Definition RT_RA_A : Z := 0x33144.
Definition RT_RA_M : Z := 0x331bc.
Definition RT_RA_D : Z := 0x331d8.
Definition RT_RA_R : Z := 0x330c8.
Definition RT_RA_NA : Z := 0x330a4.
Definition RT_RA_I : Z := 0x53dd0.
Definition RT_GOT_M : Z := 0xa2878.
Definition RT_REAL_M : Z := 0xa46c8.
Definition RT_INST : Z := 0xa8098.
Definition RT_OOM : Z := 0x12d960.
Definition RT_TP : Z := 0x5de730.
Definition RT_ERRNO : Z := 0x5de68c.

Definition RT_SO : Z := -2136.
Definition RT_SPR : Z := -2208.
Definition RT_SPN : Z := -2160.

Definition rt_tbl_build : ctable :=
build_table tfibsegs 0x3302c 131%nat (build_table tfibsegs 0x53c24 118%nat
(build_table tfibsegs 0x6d484 8%nat (build_table tfibsegs 0x8f828 3%nat TEmpty))).
Definition rt_tbl : ctable := Eval vm_compute in rt_tbl_build.
Lemma rt_tbl_eq : rt_tbl = rt_tbl_build.
Proof. vm_cast_no_check (@eq_refl ctable rt_tbl). Qed.
Lemma rt_tbl_ok : table_ok tfibsegs rt_tbl.
Proof.
rewrite rt_tbl_eq. unfold rt_tbl_build.
do 3 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate.
Qed.

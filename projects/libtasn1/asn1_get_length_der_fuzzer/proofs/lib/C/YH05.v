(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: image regions and their lengths for libtasn1/asn1_get_length_der_fuzzer's plain binary, and module names. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK11 YQ0j YQ0b YQ0i YQ0a YQ03.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YH04.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition src2_img : smem :=
[ mkRegion None 0x10000 0x12000 0 0 [mkChunk 0x10000 (CImg 0x2000)]    ;
mkRegion None 0x12000 0x1b000 0 0 [mkChunk 0x12000 (CImg 0x9000)]    ;
mkRegion None 0x1b000 0x1c000 0x1b000 0x1c000 [mkChunk 0x1b000 (CImg 0x1000)]    ;
mkRegion None 0x1c000 0x4e000 0x1c000 0x4e000 [mkChunk 0x1c000 (CImg 0x32000)]     ].
Lemma src2_img_ok : img_check src2segs src2_img = true.
Proof. vm_compute. reflexivity. Qed.
Definition src2_pc0 : Z := 0x12468.
Definition src2_W : Z := 65536.
Definition src2_ss0 (two : bool) : sstate := ss0 src2_pc0 Plain_phdrs src2_W two src2_img.
Lemma src2_init_pc_eq : Z.of_N Plain_init_pc = src2_pc0.
Proof. reflexivity. Qed.
Theorem src2_init_st_ok :
forall (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw)
(xw : nat -> word) (xd : nat -> list byte) (two : bool),
valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
xd UID_DATOM = uid_bytes uid ->
xd HWCAP_DATOM = hwcap_bytes hw ->
xd RAND_DATOM = rand_bytes rnd ->
(if two then 2 <= length argv else True)%nat ->
st_ok src2segs (E0 sp argv envp xw xd) (src2_ss0 two)
(init_machine_state src2segs Plain_init_pc Plain_phdrs sp rnd argv envp uid hw).
Proof.
intros sp argv envp uid hw rnd xw xd two Hsp Hva Hve Hfits Hxd Hxh Hxr Htwo.
unfold src2_ss0. rewrite <- src2_init_pc_eq.
apply (init_st_ok src2segs Plain_phdrs sp argv envp Hsp Hva Hve Hfits uid hw rnd src2_W ltac:(unfold src2_W; lia)
xw xd Hxd Hxh Hxr Plain_init_pc two src2_img Htwo src2_img_ok).
Qed.



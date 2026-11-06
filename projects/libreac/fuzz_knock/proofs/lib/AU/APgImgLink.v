(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACed.v at c8557374ad2e to libreac/fuzz_knock's asan-ubsan image (fuzz_knock.asan-ubsan, sha256 f834165f5002...), as the twin of lib/A/APgImgLink.v, with its module paths changed: lines 30-31 (tfibX_segs0), 35 (tfibX_base0, here the three entry addresses tfibX_init0 / tfibX_heard0 / tfibX_step0), 40-55 (tfibX_lib), 70-71, 73 and 76-87 (tfibX_LAWS, tfibX_env, tfibX_PALib0) and 145-149 (tfibX_AMEMSET) are taken; lines 27-29 (XN0), 32-34 (the second listing and the RELRO remarks), 56-69 (the ro_below_ofl instances), 72 and 74-75 (HD, tfibX_ML), 88-144 and 150-166 (the second listing's PALib and the PALibF, malloc, free, memcpy, memcmp and bcmp facts) are left out. Renames: PB_tfib -> PI_knock_asanubsan (lib/AU/APgImg.v), the abbreviations B -> TfibB and HB -> TfibB_syms (lib/AU/YD2l.v), AS_asan_memset -> AS___asan_memset (lib/Reusable/YI0w.v); asan_memset_realizes is lib/AU/YE2r.v's. Constants: tfibX_base0's 0x81404 -> the entry addresses of reac_knock_init 0x7f480, reac_knock_heard 0x7f520 and reac_knock_step 0x7f5b0 (knock symbol table; text base 0x7eed0 + AF_asanubsan_reac_knock_<F> of lib/Reusable/YI0y.v); tfibX_lib's errno segment, cgif's fourth image segment -> knock's (0x98000, 0x55b000), the fourth segment of the image module AsanUbsan.M.loaded_segments (its (base, size) list read by vm_compute: (0x10000, 0x1f000), (0x2f000, 0x67000), (0x96000, 0x2000), (0x98000, 0x55b000); the page-rounded range of the fourth PT_LOAD 0x98310 + 0x55aae0 of the ELF program headers), which holds TFIB_ERRNO 0x5d146c .. 0x5d1470 (lib/AU/YF0m.v); tfibX_lib_consts_chk and its use are dropped and the lib_consts field closes by contradiction, because knock's lib_const_addr is False (lib/AU/YCeh.v). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YP0b YK04 YG00 YG0a YG01 YG0f YG0n YG0q YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YF0m YF0l YCej YD2l YCeh.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YI0w YI0y YC4a.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import APgImg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YC1f.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YE2r.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Remark tfibX_segs0 : @pa_segs _ _ PI_knock_asanubsan = tfibsegs.   Proof. reflexivity. Qed.
Remark tfibX_init0 : @pa_val _ _ PI_knock_asanubsan A_TEXT + AF_asanubsan_reac_knock_init = 0x7f480.   Proof. reflexivity. Qed.
Remark tfibX_heard0 : @pa_val _ _ PI_knock_asanubsan A_TEXT + AF_asanubsan_reac_knock_heard = 0x7f520.   Proof. reflexivity. Qed.
Remark tfibX_step0 : @pa_val _ _ PI_knock_asanubsan A_TEXT + AF_asanubsan_reac_knock_step = 0x7f5b0.   Proof. reflexivity. Qed.
Theorem tfibX_lib : TfibLib TfibB.
Proof.
constructor; try reflexivity.
- cbn [as_errno TfibB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno TfibB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs) 3 = Some (0x98000, 0x55b000))
by (vm_compute; reflexivity).
rewrite nth_error_map in Hb. destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate Hb]. cbn in Hb. injection Hb as H1 H2.
exists sg. split; [exact (nth_error_In _ 3 E) | rewrite H1, H2; lia].
- intros a Ha. unfold lib_const_addr in Ha. contradiction.
- cbn [as_gp TfibB]. unfold TFIB_GP. lia.
Qed.
Definition tfibX_LAWS : AR_laws tfibsegs TfibB := AR_laws_ok tfibsegs TfibB.
Definition tfibX_env : api_env tfibsegs TfibB := tl_env TfibB tfibX_lib.
Lemma tfibX_PALib0 : PALib (PI := PI_knock_asanubsan) TfibB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- left. vm_compute. discriminate.
- exact tfibX_env.
- reflexivity.
- reflexivity.
- vm_compute. split; reflexivity.
Qed.
Lemma tfibX_AMEMSET : aintrin_realizes tfibsegs TfibB OSet (@pa_sigma _ _ PI_knock_asanubsan AS___asan_memset).
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (asan_memset_realizes TfibB tfibX_LAWS TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
End b.

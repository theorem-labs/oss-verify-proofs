(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI5c.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN03.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YI06 YI14 YI5b.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* v1.9 port note (a Theorem Labs lane, 2026-10-28), corrected 2026-10-29 and 2026-10-31: src0_sink has sk_file := None,
   so it fills none of the file-sink fields sk_read, sk_write, sk_seek, sk_close, sk_path_addr, sk_mode_addr,
   sk_trailer_addr and sk_rwa_addr (YI14.v's file_sink_syms, :36-42). With no file sink, YI14.v's sink_at is
   False, stdio_env asks nothing of a file and env_addr holds no file address; a statement taking sink_at over
   src0_sink as a premise has an UNSATISFIABLE premise and would be vacuously true. YH03.v still defines the
   measured v1.9 src0_A_stdio_read (__stdio_read) and src0_A_stdio_seek (__stdio_seek); 261ff111ca53 removed
   src0_D_str_rwa as unread, and src0_D_str_tmp_out_gif / _wb / _3 are not defined in this unit: pcap's image
   has no "/tmp/out.gif", "wb" or ";" string. pcap never opens that sink and the released chain uses
   sink_none.
   See yh03-check.md (sha256 f82c7576099d; internal record). *)
#[global] Instance src0_sink : sink_syms := {|
sk_ofl_lock := src0_D_ofl_lock;
sk_threaded := src0_D_libc + 1;
sk_file := None;
sk_highs_addr := src0_D_const_HIGHS_0x8080808080808080;
sk_ones_addr := src0_D_const_ONES_0x0101010101010100
|}.
Lemma src0_env_addr_range : forall a, env_addr a -> 0x10000 <= a < (symaddr ImgPages.Plain.top).
Proof.
intros a Ha. unfold env_addr in Ha.
cbv [sk_ofl_head sk_threaded sk_ofl_lock sk_file sk_highs_addr sk_ones_addr src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc
src0_D_const_HIGHS_0x8080808080808080 src0_D_const_ONES_0x0101010101010100] in Ha. lia.
Qed.
Section b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma src0_sink_in_img : forall a, (symaddr ImgPages.Plain.rw_lo) <= a < (symaddr ImgPages.Plain.top) -> in_img src0_msyms a.
Proof. intros a Ha. apply (covered_sound src0_msyms (symaddr ImgPages.Plain.rw_lo) (symaddr (ImgPages.Plain.top - ImgPages.Plain.rw_lo)%Z)); [vm_compute; reflexivity | lia]. Qed.
Lemma src0_sink_ro_img : forall a, 0x10000 <= a < (symaddr ImgPages.Plain.text_lo) -> in_img src0_msyms a.
Proof. intros a Ha. apply (covered_sound src0_msyms 0x10000 (symaddr (ImgPages.Plain.text_lo - ImgPages.Plain.ro_lo)%Z)); [vm_compute; reflexivity | lia]. Qed.
Ltac src0_static_tac :=
unfold static_owned, errno_addr; cbn;
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes,
src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_malloc_context, CTX_SIZE, src0_tp; repeat split; intros H; lia.
#[global] Instance src0_sink_laws : sink_laws src0_msyms.
Proof.
constructor.
- intros a Ha. unfold env_addr in Ha.
cbv [sk_ofl_head sk_threaded sk_ofl_lock sk_file sk_highs_addr sk_ones_addr src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc
src0_D_const_HIGHS_0x8080808080808080 src0_D_const_ONES_0x0101010101010100] in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]].
+ split; [apply src0_sink_in_img; lia | src0_static_tac].
+ split; [apply src0_sink_in_img; lia | src0_static_tac].
+ split; [apply src0_sink_in_img; lia | src0_static_tac].
+ destruct Ha.
+ split; [apply src0_sink_ro_img; lia | src0_static_tac].
+ split; [apply src0_sink_ro_img; lia | src0_static_tac].
- intros a Ha. unfold errno_addr in Ha. cbn in Ha. unfold src0_tp in Ha.
split; [apply src0_sink_in_img; lia | src0_static_tac].
Qed.
End b.

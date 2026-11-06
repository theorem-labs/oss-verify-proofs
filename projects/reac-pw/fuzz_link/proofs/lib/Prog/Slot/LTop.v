(* reac-pw/fuzz_link, plain image: Statements.plain_halts from LLVMFuzzerTestOneInput.plain_halts_of_callees
   (lib/Prog/LLVMFuzzerTestOneInput.v), with each callee contract it takes discharged by that callee's walk on this
   branch, and the three allocating callees (text_buf, text_of, mark_quietly) at the frame's instance
   (src0_msyms, zlib_API) by their walks with the frame's allocator facts (FrameProof.zlib_frame_allocator,
   ZAllocator.zlib_allocator_extra, FrameProof.errno_below_ceiling, AllocCut.libc_no_locks_ok).
   plain_halts_of_lib keeps the netlink alias reader and writer as premises; plain_halts_holds discharges them
   with the netlink library lane's walks (reac_link_alias_read / _write over nl_talk, copy_attr and the fake
   kernel's socket calls). *)
From OSSVerify.reac_pw.fuzz_link Require Statements.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YH02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract FrameAPI AllocCut ZAllocator FrameProof
  SlotTopG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import reac_link_alias_read_c
  reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require LLVMFuzzerTestOneInput kernel index_of model_talk
  model_decide bcmp memset strcmp strlen snprintf snprintf_img check_socket check_refused check_bounds check_read
  check_write check_requests check_marks check_verdict reac_served_unmark_all mwrite mseek fseeko rewind fmemopen
  text_buf text_of mark_quietly remember fprintf vfprintf reac_code_emit reac_served_mark
  reac_link_alias_read reac_link_alias_write nl_talk copy_attr strnlen memchr memcpy fuzz_socket fuzz_send
  fuzz_recv fuzz_close __errno_location.
Local Open Scope Z_scope.

(* malloc's contract at the frame's instance: the first part of the frame's allocator facts *)
Lemma src0_malloc (fx : YK11.FPState) (rc : YM05.RunCeil) :
  malloc_contract (fx := fx) (rc := rc) src0_msyms (@zlib_API rc).
Proof. exact (proj1 (@zlib_frame_allocator rc fx)). Qed.

Lemma text_buf_src0 (fx : YK11.FPState) (rc : YM05.RunCeil) :
  @text_buf_c.text_buf_contract fx rc src0_msyms (@zlib_API rc).
Proof. exact (text_buf.text_buf_holds_src0 (@zlib_API rc) (src0_malloc fx rc)). Qed.

Lemma text_of_src0 (fx : YK11.FPState) (rc : YM05.RunCeil) :
  @text_of_c.text_of_contract fx rc src0_msyms (@zlib_API rc).
Proof.
  exact (text_of.text_of_closed src0_msyms (@zlib_API rc) ms_segs_rsegs eq_refl (errno_below_ceiling rc)
    (src0_malloc fx rc)).
Qed.

(* the frame's pins of the allocator's symbols, by computation on src0_msyms *)
Lemma mq_pins_src0 : mark_quietly.mq_pins src0_msyms.
Proof. unfold mark_quietly.mq_pins. repeat split. Qed.

(* rewind over __fseeko_unlocked over mwrite and mseek *)
Lemma rewind_closed : rewind_c.rewind_contract.
Proof. exact (rewind.rewind_proof (fseeko.fseeko0_proof mwrite.mwrite_proof mseek.mseek_set_proof)). Qed.

(* reac_served_mark over remember, reac_code_emit (over fprintf and vfprintf) and fprintf; the alias reader and
   writer stay *)
Lemma reac_served_mark_lib :
  reac_link_alias_read_contract -> reac_link_alias_write_contract -> reac_served_mark_c.reac_served_mark_contract.
Proof.
  intros HAR HAW.
  exact (reac_served_mark.reac_served_mark_closed HAR HAW remember.remember_closed
    (reac_code_emit.reac_code_emit_holds fprintf.fprintf_proof_closed vfprintf.vfprintf_proof)
    fprintf.fprintf_proof_closed).
Qed.

(* mark_quietly over fmemopen (with malloc, libc_no_locks and AllocExtra at the frame's instance), rewind and
   reac_served_mark *)
Lemma mark_quietly_src0 :
  reac_link_alias_read_contract -> reac_link_alias_write_contract ->
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
    @mark_quietly_c.mark_quietly_contract fx rc src0_msyms (@zlib_API rc).
Proof.
  intros HAR HAW fx rc.
  exact (mark_quietly.mark_quietly_closed src0_msyms (@zlib_API rc) mq_pins_src0 (@zlib_allocator_extra rc)
    (fmemopen.fmemopen_w_holds src0_msyms (@zlib_API rc) ms_segs_rsegs
       eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
       (src0_malloc fx rc) (libc_no_locks_ok src0_msyms (@zlib_API rc) (@zlib_allocator_extra rc))
       (@zlib_allocator_extra rc))
    rewind_closed (reac_served_mark_lib HAR HAW)).
Qed.

About LLVMFuzzerTestOneInput.plain_halts_of_callees.

Theorem plain_halts_of_lib :
  reac_link_alias_read_contract -> reac_link_alias_write_contract -> Statements.plain_halts.
Proof.
  intros HAR HAW.
  exact (LLVMFuzzerTestOneInput.plain_halts_of_callees
    kernel.kernel_holds
    (model_talk.model_read_holds_talk index_of.index_of_holds)
    (model_talk.model_write_holds_talk index_of.index_of_holds)
    model_decide.model_decide_closed
    bcmp.bcmp_holds memset.memset_holds strcmp.strcmp_holds strlen.strlen_holds
    snprintf.snprintf_holds snprintf_img.snprintf_img_holds index_of.index_of_holds
    HAR HAW (reac_served_unmark_all.reac_served_unmark_all_closed HAR HAW)
    model_decide.reac_served_decide_closed
    check_socket.check_socket_holds check_refused.check_refused_holds check_bounds.check_bounds_holds
    check_read.check_read_holds check_write.check_write_holds check_requests.check_requests_holds
    check_marks.check_marks_holds check_write.check_mark_holds check_verdict.check_verdict_holds
    text_buf_src0 text_of_src0 (mark_quietly_src0 HAR HAW) mwrite.mwrite_proof).
Qed.

About plain_halts_of_lib.
Print Assumptions plain_halts_of_lib.

(* the netlink library's talk over the fake kernel's socket calls *)
Lemma nl_talk_closed : nl_talk_c.nl_talk_contract.
Proof.
  exact (nl_talk.nl_talk_holds (copy_attr.copy_attr_holds (strnlen.strnlen_holds memchr.memchr_holds)
                                   memcpy.memcpy_holds)
           fuzz_socket.fuzz_socket_holds fuzz_send.fuzz_send_holds fuzz_recv.fuzz_recv_holds
           fuzz_close.fuzz_close_holds __errno_location.__errno_location_holds).
Qed.

(* PLAIN_HALTS *)
Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  exact (plain_halts_of_lib
    (reac_link_alias_read.reac_link_alias_read_holds index_of.fuzz_if_nametoindex_holds memset.memset_holds
       nl_talk_closed)
    (reac_link_alias_write.reac_link_alias_write_holds index_of.fuzz_if_nametoindex_holds strlen.strlen_holds
       memset.memset_holds memcpy.memcpy_holds nl_talk_closed)).
Qed.

About plain_halts_holds.
Print Assumptions plain_halts_holds.

(* The one fact of the frame's symbols the SR glue of LLVMFuzzerTestOneInput (U/Prog/T/LLVMFuzzerTestOneInput_glue.v,
   hypothesis SINK) asks: the sink words of src0_sink (ofl_head, libc.threaded, ofl_lock; U/Reusable/YI5c.v) lie in
   the image, apart from the allocator's statics, its context, errno and the world. By the symbol values of
   U/Reusable/YH03.v (0x63ae0, 0x636b1, 0x63ad8), as src0_sink_laws (U/Reusable/YI5c.v) proves the first two. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YN03.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YI16 YI06 YI14 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import receive_c LLVMFuzzerTestOneInput_glue.
Local Open Scope Z_scope.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma src0_lg_sink : forall a, lg_sink_addr (SH:=src0_sink_head) (SK:=src0_sink) a ->
  in_img src0_msyms a /\ ~ static_owned src0_msyms a /\
  ~ (ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE) /\
  ~ (errno_addr src0_msyms <= a < errno_addr src0_msyms + 4) /\ ~ h_world a.
Proof.
  intros a Ha. unfold lg_sink_addr in Ha.
  cbv [sk_ofl_head sk_threaded sk_ofl_lock src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc] in Ha.
  split; [apply src0_sink_in_img; lia|].
  unfold static_owned, errno_addr, h_world, W_BASE_UBSAN, W_LEN; cbn;
  unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32,
    src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_malloc_context, CTX_SIZE, src0_tp;
  repeat split; intros H; lia.
Qed.

End S.

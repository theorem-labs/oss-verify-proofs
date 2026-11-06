(* Theorem Labs, 2026-10: the frame-area contracts of omx-clap-core/fuzz_preset's ASan image A for classes 0 and 1
   WITH the memnorm keep: YGcallMxmn.astack_malloc_realizes_xm (= FCiface.astack_malloc_realizes_x plus the last post
   conjunct `MN.memnorm segs mem -> MN.memnorm segs mem'`, MN = YAkMemnorm) at any ARx with FCiface.fs_iface.
   Each is the image walk generalised over a memory predicate (FCm0s.tfib_stack_malloc0_at_P,
   FCm1s.tfib_stack_malloc_at_x_P) at Pm := YAkMemnorm.memnorm tfibsegs. The walks' frame-step hypothesis is paid by
   YGcallMxmn.memnorm_frame_of at each of the four runner phases (fs_phase_to r_A, fs_phase C1 / C2 / C3); the probe
   loop and the return keep the memory. The walks themselves do not Require YGcallMxmn (h-hpreset-7, 2026-10-29):
   only this leaf loads its closure, and this leaf calls no lia.
   Arms (FrameMemnormPay's reading for h-hpreset-7, 2026-10-29 ~10:55Z): like FCiface's text, these contracts cover
   only the fake-frame arm, under the premise apath (stack_malloc cid S) [] (PFake cid pos, S'). A caller learns that
   a0 is the frame address (so non-zero) only through YGcallSx.aj_stack_malloc_at_x or YGcallMxmn.aj_stack_malloc_at_xm,
   which discharge that premise from count_cid cid (frames S) < fs_frames cid at the caller's own entry state
   (YGcallScf.stack_malloc_progress_any) and post getr regs2 10 = w64 (frame_addr lyc cid pos).
   No image numeral appears in this file. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 FCiface YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FCm0s FCm1s.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Corollary stack_malloc0_contract_xm : forall B ARx, fs_iface tfibsegs B ARx -> TfibSyms B ->
  astack_malloc_realizes_xm tfibsegs B ARx 0.
Proof.
  intros B ARx I TB ly S Hp W regs mem md pos S' HPRE Hcnt Hpath. rewrite (ts_code B TB).
  exact (FCm0s.tfib_stack_malloc0_at_P B ARx I TB (YAkMemnorm.memnorm tfibsegs) (memnorm_frame_of tfibsegs)
    ly S Hp W regs mem md pos S' HPRE Hcnt Hpath).
Qed.

Corollary stack_malloc1_contract_xm : forall B ARx, fs_iface tfibsegs B ARx -> TfibSyms B ->
  astack_malloc_realizes_xm tfibsegs B ARx 1.
Proof.
  intros B ARx I TB ly S Hp W regs mem md pos S' HPRE Hcnt Hpath. rewrite (ts_code B TB).
  exact (FCm1s.tfib_stack_malloc_at_x_P B ARx I TB (YAkMemnorm.memnorm tfibsegs) (memnorm_frame_of tfibsegs)
    ly S Hp W regs mem md pos S' HPRE Hcnt Hpath).
Qed.

End a.

(* Theorem Labs, 2026-10: the frame-area contract of omx-clap-core/fuzz_preset's ASan image A for class 3
   WITH the memnorm keep: YGcallMxmn.astack_malloc_realizes_xm (= FCiface.astack_malloc_realizes_x plus the last post
   conjunct `MN.memnorm segs mem -> MN.memnorm segs mem'`, MN = YAkMemnorm) at any ARx with FCiface.fs_iface.
   It is the image walk generalised over a memory predicate (FCm3s.tfib_stack_malloc3_at_x_P) at
   Pm := YAkMemnorm.memnorm tfibsegs, as FCm01xm.v does for classes 0 and 1 (h-hpreset-7's route, 2026-10-29). The walk's
   frame-step hypothesis is paid by YGcallMxmn.memnorm_frame_of at each of the four runner phases (fs_phase_to r_A,
   fs_phase C1 / C2 / C3); the probe loop and the return keep the memory. The walk does not Require YGcallMxmn: only
   this leaf loads its closure, and this leaf calls no lia.
   Arms: like FCiface's text, this contract covers only the fake-frame arm, under the premise
   apath (stack_malloc cid S) [] (PFake cid pos, S') (FCm01xm.v's header has the reading).
   No image numeral appears in this file. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 FCiface YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FCm3s.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Corollary stack_malloc3_contract_xm : forall B ARx, fs_iface tfibsegs B ARx -> TfibSyms B ->
  astack_malloc_realizes_xm tfibsegs B ARx 3.
Proof.
  intros B ARx I TB ly S Hp W regs mem md pos S' HPRE Hcnt Hpath. rewrite (ts_code B TB).
  exact (FCm3s.tfib_stack_malloc3_at_x_P B ARx I TB (YAkMemnorm.memnorm tfibsegs) (memnorm_frame_of tfibsegs)
    ly S Hp W regs mem md pos S' HPRE Hcnt Hpath).
Qed.

End a.

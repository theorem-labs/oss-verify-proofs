(* Theorem Labs, 2026-10: __asan_set_shadow_f5 of omx-clap-core/fuzz_preset's ASan image A WITH the memnorm keep:
   YGcallMxmn.aset_shadow_realizes_xm (= FCiface.aset_shadow_realizes_x plus the last post conjunct
   `MN.memnorm segs mem -> MN.memnorm segs mem'`, MN = YAkMemnorm) at any ARx with FCiface.fs_iface, with the premises
   of FCf5.set_shadow_f5_contract_x. It is the walk generalised over a memory predicate (FCf5.set_shadow_gen_x_P) at
   Pm := YAkMemnorm.memnorm tfibsegs, h-hpreset-7's route for FCm0s / FCm1s (2026-10-29). The walk changes memory in two
   ways only, and each has its own hypothesis:
   - the stub's runner phase (FCf5.f5_phase, SRr_run_gen): the frame-step hypothesis, paid by
     YGcallMxmn.memnorm_frame_of (as the stack_malloc walks pay theirs);
   - musl memset (AE3d.tfib_memset), one msteps run over the visible part mrestrict H mem1, merged back by munrestrict:
     the run-step hypothesis, paid by YAkMemnorm.memnorm_mrestrict, memnorm_msteps (its store case is memnorm_write,
     under store_ok) and memnorm_munrestrict.
   The walk makes no kernel step (SRr_msteps and the runner phase only; its post has same_but_materialized md md').
   The walk does not Require YGcallMxmn or YAkMemnorm: only this leaf loads their closure, and this leaf calls no lia.
   No image numeral appears in this file: the pc is FCimg's SET_SHADOW_F5, the value FCf5's 0xf5. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 FCiface YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m FCimg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FCf5.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Corollary set_shadow_f5_contract_xm : forall B ARx, fs_iface tfibsegs B ARx -> TfibSyms B ->
  aset_shadow_realizes_xm tfibsegs B ARx SET_SHADOW_F5 0xf5.
Proof.
  intros B ARx FI TB.
  refine (FCf5.set_shadow_gen_x_P B ARx FI TB SET_SHADOW_F5 0xf5 FCf5.e_f5 FCf5.r_f5 FCf5.shape_f5 _
    (YAkMemnorm.memnorm tfibsegs) (memnorm_frame_of tfibsegs) _).
  - split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity.
  - intros H m ms ms' Hm Hrun Heq. apply YAkMemnorm.memnorm_munrestrict; [exact Hm|].
    apply (YAkMemnorm.memnorm_msteps tfibsegs ms ms' Hrun). rewrite Heq.
    apply YAkMemnorm.memnorm_mrestrict. exact Hm.
Qed.

End a.

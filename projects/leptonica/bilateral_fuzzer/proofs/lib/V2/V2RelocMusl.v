(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg RelocSpan CanonSpans.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocImg.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2RelocMusl () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common4Musl7RelocRW?dwin_bounds_chkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib2V27V2Reloc8v2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2RelocImg7v2_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5PFLib7segs_loC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5PFLib7segs_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl7RelocPF=pf_bounds_chkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common4Musl7RelocPF<pf_prefix_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03".
Local Open Scope Z_scope.

Lemma v2_dwin_bounds : @dwin_bounds_chk v2_reloc v2_data = true.
Proof. lazy. reflexivity. Qed.
Definition v2_rw : RelocRW v2_reloc v2_data :=
  {| rl_rw_spans := v2_spans_ok; rl_rw_hull := v2_hull_ok;
     rl_rw_orders := v2_orders_ok; rl_dwin_bounds := v2_dwin_bounds |}.

Lemma v2_segs_lo : segs_lo (@rl_segs v2_reloc) = @rl_img_lo v2_reloc.
Proof. vm_compute. trivial. Qed.
Lemma v2_segs_hi : segs_hi (@rl_segs v2_reloc) = @rl_img_hi v2_reloc.
Proof. apply Z.eqb_eq. vm_compute. constructor. Qed.
Lemma v2_pf_bounds : @pf_bounds_chk v2_reloc = true.
Proof. change (@pf_bounds_chk v2_reloc) with true. exact (eq_refl true). Qed.
Lemma v2_pf_prefix : pf_prefix_ok (@rl_segs v2_reloc) (0x102e7 + @rl_delta v2_reloc B_S_102e7) = true.
Proof. vm_compute. easy. Qed.
Definition v2_pf : RelocPF v2_reloc :=
  Build_RelocPF v2_reloc v2_segs_lo v2_segs_hi v2_pf_bounds v2_pf_prefix.

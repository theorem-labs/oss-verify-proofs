(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from cgif's ACed.v / ACfi.v top-link facts to fuzz_ctrl's CtrlB *)
(* Image A. The donor is proofs/cgif/cgif_file_fuzzer/lib/A/ACed.v of c8557374ad2e:
     actl_ro_segs_chk / actl_ro_below / actl_RO   <- tfibX_ro_segs_chk :56, tfibX_ro_below :59, tfibX_RO0 :66
                                                     (ACfi.v:42-51 tfib_ro_segs_chk / tfib_ROB is the same check);
     actl_env                                     <- tfibX_env :76;
     actl_PALib                                   <- tfibX_PALib0 :77;
     actl_PALibF                                  <- tfibX_PALibF0 :105.
   The RO instance is stated in the form CM_SPEC takes it: APostBase.ro_below_ofl over A.AB1v.tfibsegs at the read-only
   span [0x9e380, 0xa07c8) (PI_ctrl's pa_relro_lo / pa_relro_hi, A/Prog/CtrlImg.v) and the sink head
   A.AE2k.tfib_sink_head (sk_ofl_head = A_ofl_head). PALib and PALibF are the Records of A/Prog/CtrlPaLib.v and
   A/Prog/CtrlFrame.v at PI := PI_ctrl and B := A.AD2l.CtrlB. Every field is closed by computation, except pal_env,
   which is A.ACeh.tl_env applied to the core's A.ACtlBCode.actlb_libS. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify Require Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05
  Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16 Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq
  Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
From OSSVerify Require Proofs.libreac.fuzz_ctrl.lib.A.AB1v Proofs.libreac.fuzz_ctrl.lib.A.AE2k
  Proofs.libreac.fuzz_ctrl.lib.A.AD2l Proofs.libreac.fuzz_ctrl.lib.A.ACeh Proofs.libreac.fuzz_ctrl.lib.A.ACtlBCode.
From OSSVerify Require Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlImg Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlPaLib
  Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlFrame.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.



Lemma actl_ro_segs_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? lib.A.AE2k.A_ofl_head))%bool
    lib.A.AB1v.tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma actl_ro_below : forall a, lib.Reusable.APostBase.in_roP lib.A.AB1v.tfibsegs 0x9e380 0xa07c8 a -> a < lib.A.AE2k.A_ofl_head.
Proof.
intros a [(s & Hin & Hw & Hr) | Hr].
- pose proof (proj1 (forallb_forall _ _) actl_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb. cbn [orb] in Hb.
  apply Z.leb_le in Hb. lia.
- unfold lib.A.AE2k.A_ofl_head. lia.
Qed.
#[export] Instance actl_RO : @lib.Reusable.APostBase.ro_below_ofl lib.A.AB1v.tfibsegs 0x9e380 0xa07c8 lib.A.AE2k.tfib_sink_head.
Proof. intros a Ha. exact (actl_ro_below a Ha). Qed.


Definition actl_env : lib.Reusable.YCbq.api_env lib.A.AB1v.tfibsegs lib.A.AD2l.CtrlB :=
  lib.A.ACeh.tl_env lib.A.AD2l.CtrlB lib.A.ACtlBCode.actlb_libS.
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.


Lemma actl_PALib : lib.A.Prog.CtrlPaLib.PALib (PI := lib.A.Prog.CtrlImg.PI_ctrl) lib.A.AD2l.CtrlB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- left. vm_compute. discriminate.
- exact actl_env.
- reflexivity.
- reflexivity.
- vm_compute. split; reflexivity.
Qed.


Lemma actl_PALibF : lib.A.Prog.CtrlFrame.PALibF (PI := lib.A.Prog.CtrlImg.PI_ctrl) lib.A.AD2l.CtrlB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- vm_compute. repeat split; first [ left; discriminate | right; discriminate ].
Qed.
End b.

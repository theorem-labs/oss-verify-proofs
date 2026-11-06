(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from cgif's ACed.v / ACfi.v top-link facts to fuzz_ctrl's CtrlB *)
(* Image B, the twin of lib/A/ACtlTopLink.v. The donor is proofs/cgif/cgif_file_fuzzer/lib/YCed.v of c8557374ad2e
   (root-level twin of A/ACed.v):
     ctrlb_ro_segs_chk / ctrlb_ro_below / ctrlb_RO <- tfibX_ro_segs_chk :49, tfibX_ro_below :52, tfibX_RO0 :59
                                                      (YCfi.v:40-49 tfib_ro_segs_chk / tfib_ROB is the same check);
     ctrlb_env                                     <- tfibX_env :69;
     ctrlb_PALib                                   <- tfibX_PALib0 :70.
   The RO instance is stated in the form image B's walk takes it (lib/B/ACtlW*.v `Context {RO_OFL :
   Reusable.APostBase.ro_below_ofl segs RLO RHI}`): over Reusable.YB1v.tfibsegs at the B top's read-only span
   [0x9f1a0, 0xa15e8) (lib/B/ACtl.v ctl_lib_x arguments) and the sink head Reusable.YE2k.tfib_sink_head
   (sk_ofl_head = A_ofl_head = 0x5fcd48). PALib is the Record of lib/B/Prog/CtrlPaLib.v at PI := PI_ctrl_B and
   B := Reusable.YD2l.CtrlB; every field is closed by computation, except pal_env, which is Reusable.YCeg.tl_env
   applied to the core's Reusable.CtrlBCode.ctrlb_libS. Image B has no PALibF Record (no lib/B/Prog/CtrlFrame.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify Require Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05
  Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16 Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq
  Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
From OSSVerify Require Proofs.libreac.fuzz_ctrl.lib.Reusable.YB1v Proofs.libreac.fuzz_ctrl.lib.Reusable.YE2k
  Proofs.libreac.fuzz_ctrl.lib.Reusable.YD2l Proofs.libreac.fuzz_ctrl.lib.Reusable.YCeg
  Proofs.libreac.fuzz_ctrl.lib.Reusable.CtrlBCode.
From OSSVerify Require Proofs.libreac.fuzz_ctrl.lib.B.Prog.CtrlImg Proofs.libreac.fuzz_ctrl.lib.B.Prog.CtrlPaLib.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.



Lemma ctrlb_ro_segs_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? lib.Reusable.YE2k.A_ofl_head))%bool
    lib.Reusable.YB1v.tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ctrlb_ro_below : forall a,
  lib.Reusable.APostBase.in_roP lib.Reusable.YB1v.tfibsegs 0x9f1a0 0xa15e8 a -> a < lib.Reusable.YE2k.A_ofl_head.
Proof.
intros a [(s & Hin & Hw & Hr) | Hr].
- pose proof (proj1 (forallb_forall _ _) ctrlb_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb. cbn [orb] in Hb.
  apply Z.leb_le in Hb. lia.
- unfold lib.Reusable.YE2k.A_ofl_head. lia.
Qed.
#[export] Instance ctrlb_RO :
  @lib.Reusable.APostBase.ro_below_ofl lib.Reusable.YB1v.tfibsegs 0x9f1a0 0xa15e8 lib.Reusable.YE2k.tfib_sink_head.
Proof. intros a Ha. exact (ctrlb_ro_below a Ha). Qed.


Definition ctrlb_env : lib.Reusable.YCbq.api_env lib.Reusable.YB1v.tfibsegs lib.Reusable.YD2l.CtrlB :=
  lib.Reusable.YCeg.tl_env lib.Reusable.YD2l.CtrlB lib.Reusable.CtrlBCode.ctrlb_libS.
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.



Lemma ctrlb_PALib : lib.B.Prog.CtrlPaLib.PALib (PI := lib.B.Prog.CtrlImg.PI_ctrl_B) lib.Reusable.YD2l.CtrlB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- left. vm_compute. discriminate.
- exact ctrlb_env.
- reflexivity.
- reflexivity.
- vm_compute. split; reflexivity.
Qed.
End b.

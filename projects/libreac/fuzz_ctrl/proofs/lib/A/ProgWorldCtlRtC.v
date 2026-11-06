(* lib/A/ProgWorldCtlRtC.v -- fuzz_ctrl image A (libreac v1.9.0): ctl_rt_C from the core's AR at a cut, for route (C)
   (a Theorem Labs lane 09:20Z, wave lead a Theorem Labs lane).  Written by a Theorem Labs lane.  ANNOUNCED ADDITION.

   ctl_rt_C (A.ACtlRtC, a Theorem Labs lane's cform; one writer of that file: a Theorem Labs lane) replaces ACtlCut.ctl_rt's UNIVERSAL
   shadow_rw by the shadow of the cut's own state (F frames / L live blocks / Z zero_shadow ranges) and of the image
   hull (I).  ACtlCutC proves the two shadow conjuncts from AR (cut_shadow_of_AR; img_shadow_of_AR, via its own proved
   img_shadow_cover).  This file adds the other two, asan_cells and ro_agree, exactly as A.ProgWorldCtlRt.ctlrt_of_AR
   does (asan_cells_of_AR / ro_agree_of_AR, factored out of that proof), and discharges ro_agree's owned read-only
   bytes by A.ProgWorldOwnedRo.AR_states_owned_ro_of_AR (proved from AR on the record const rows), so the whole
   ctl_rt_C follows from AR WITHOUT A.ProgWorld.AR_states_vis0_shadow and WITHOUT A.ProgWorld.AR_states_owned_ro.
   ANNOUNCED STATEMENT CHANGE (10:1xZ): the AR_states_owned_ro premise is removed.  A thin wrapper: one conj.
   It lives in its own file because ACtlCutC Requires A.ProgWorldCtlRt (which Requires A.ProgWorld): stating it in
   ProgWorld.v would be a Require cycle.  rule 24: no function proved (a program-world fact over the core's AR). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.ACtlK A.AF0m A.Prog.CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorldCtlRt A.ProgWorldOwnedRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlRtC A.ACtlCutC.
Local Open Scope Z_scope.
Local Notation segs := A.AB1v.tfibsegs (only parsing).

Section CtlRtC.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* The premises are ctlrt_of_AR_stmt's (ProgWorld.v:234-239) with AR_states_vis0_shadow and AR_states_owned_ro
   REMOVED. *)
Definition ctl_rt_C_of_AR_stmt : Prop :=
  A.AF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall (RLO RHI : Z) ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    A.Prog.CtrlBase.arodata_okP segs RLO RHI B (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) ->
    A.ACtlRtC.ctl_rt_C B ly S m.

Lemma ctl_rt_C_of_AR : ctl_rt_C_of_AR_stmt.
Proof.
  unfold ctl_rt_C_of_AR_stmt.
  intros HTS HL RLO RHI ly S W m md HAR Hro.
  exact (conj (A.ProgWorldCtlRt.asan_cells_of_AR B HTS ly S W m md HAR)
        (conj (A.ACtlCutC.cut_shadow_of_AR B HL ly S W m md HAR)
        (conj (A.ACtlCutC.img_shadow_of_AR B HTS HL ly S W m md HAR)
              (A.ProgWorldCtlRt.ro_agree_of_AR B HTS (A.ProgWorldOwnedRo.AR_states_owned_ro_of_AR B HTS)
                 RLO RHI ly S W m md HAR Hro)))).
Qed.
End CtlRtC.

Print Assumptions ctl_rt_C_of_AR.

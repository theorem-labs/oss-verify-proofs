(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldCtlRtC.v 9bde20fbe52 (the blob this tree had at release c5e779efe8c) (a working branch 0e97fddfcea, read by git show, not merged): the same Section, statement and proof over image B, including A's ANNOUNCED STATEMENT CHANGE (10:1xZ): ctl_rt_C_of_AR takes neither AR_states_vis0_shadow nor AR_states_owned_ro; the owned read-only bytes come from B.ProgWorldOwnedRo.AR_states_owned_ro_of_AR.  Differences from A: (1) module paths: A.ACtlK / A.Prog.CtrlBase / A.ProgWorld / A.ProgWorldCtlRt / A.ProgWorldOwnedRo / A.ACtlRtC / A.ACtlCutC -> B.*, A.AB1v / A.AF0m -> lib.Reusable.YB1v / YF0m; (2) every Require names the full directory of the one copy a clean checkout binds, where A writes `From ...fuzz_ctrl.lib Require Reusable.X` / `A.X`; (3) comments: the first lines name image B and the twin, and ProgWorld.v:234-239 is B's ProgWorld.v:259-264.  No statement differs. *)
(* lib/B/ProgWorldCtlRtC.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): ctl_rt_C from the core's AR at a cut, for
   route (C) (a Theorem Labs lane 09:20Z, wave lead a Theorem Labs lane).  Image-B twin of a Theorem Labs lane's lib/A/ProgWorldCtlRtC.v.

   ctl_rt_C (B.ACtlRtC, the B twin of a Theorem Labs lane's cform; one writer: a Theorem Labs lane) replaces ACtlCut.ctl_rt's UNIVERSAL
   shadow_rw by the shadow of the cut's own state (F frames / L live blocks / Z zero_shadow ranges) and of the image
   hull (I).  ACtlCutC proves the two shadow conjuncts from AR (cut_shadow_of_AR; img_shadow_of_AR, via its own proved
   img_shadow_cover).  This file adds the other two, asan_cells and ro_agree, exactly as B.ProgWorldCtlRt.ctlrt_of_AR
   does (asan_cells_of_AR / ro_agree_of_AR, factored out of that proof), and discharges ro_agree's owned read-only
   bytes by B.ProgWorldOwnedRo.AR_states_owned_ro_of_AR (proved from AR on the record const rows), so the whole
   ctl_rt_C follows from AR WITHOUT B.ProgWorld.AR_states_vis0_shadow and WITHOUT B.ProgWorld.AR_states_owned_ro.
   ANNOUNCED STATEMENT CHANGE (10:1xZ): the AR_states_owned_ro premise is removed.  A thin wrapper: one conj.
   It lives in its own file because ACtlCutC Requires B.ProgWorldCtlRt (which Requires B.ProgWorld): stating it in
   ProgWorld.v would be a Require cycle.  rule 24: no function proved (a program-world fact over the core's AR). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorld ProgWorldCtlRt ProgWorldOwnedRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlRtC ACtlCutC.
Local Open Scope Z_scope.
Local Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).

Section CtlRtC.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* The premises are ctlrt_of_AR_stmt's (ProgWorld.v:259-264) with AR_states_vis0_shadow and AR_states_owned_ro
   REMOVED. *)
Definition ctl_rt_C_of_AR_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall (RLO RHI : Z) ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    B.Prog.CtrlBase.arodata_okP segs RLO RHI B (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) ->
    B.ACtlRtC.ctl_rt_C B ly S m.

Lemma ctl_rt_C_of_AR : ctl_rt_C_of_AR_stmt.
Proof.
  unfold ctl_rt_C_of_AR_stmt.
  intros HTS HL RLO RHI ly S W m md HAR Hro.
  exact (conj (B.ProgWorldCtlRt.asan_cells_of_AR B HTS ly S W m md HAR)
        (conj (B.ACtlCutC.cut_shadow_of_AR B HL ly S W m md HAR)
        (conj (B.ACtlCutC.img_shadow_of_AR B HTS HL ly S W m md HAR)
              (B.ProgWorldCtlRt.ro_agree_of_AR B HTS (B.ProgWorldOwnedRo.AR_states_owned_ro_of_AR B HTS)
                 RLO RHI ly S W m md HAR Hro)))).
Qed.
End CtlRtC.

Print Assumptions ctl_rt_C_of_AR.

(* lib/A/ProgWorldRtRo.v -- fuzz_ctrl image A (libreac v1.9.0): ro_agree from the core's AR, for callee glue that takes
   the read-only half separately (a Theorem Labs lane's classify glue: RT_AR stays split, a Theorem Labs lane 05:04Z; the RT_used half is
   a Theorem Labs lane's ProgWorldRt.RT_used_of_AR).  Written by a Theorem Labs lane.  A separate file because it uses
   ProgWorldCtlRt's helpers, which ProgWorld.v cannot Require.

   ITERATION-ONLY: type-check with local stand-ins (AE2k / AF0l / AF0m port_core_refused_X -> 0xX donor literals),
   provisional.  rule 24: no function of the image is proved here (a program-world fact about the core's state).

   Premises: AR (for the owned read-only bytes through the named hypothesis AR_states_owned_ro), CtrlTSyms (the errno
   word, excluded by arodata_okP, lies in a writable segment: ts_errno), and the read-only view of the non-owned
   read-only bytes over the core's APostBase.arodata_okP (of record; A.Prog.CtrlBase.arodata_okP is a parsing alias of
   it, CtrlBase.v:29): at a cut it is ctl_base's arodata_okS (ACfn.v:41) via ProgWorld.arodata_okP_of_S, kept along the
   journal by APostBase.arodata_ok_journalP. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n YG0f YG0n APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AF0m A.ACtlK A.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorldCtlRt.
Local Open Scope Z_scope.

Local Notation segs := A.AB1v.tfibsegs (only parsing).

Section RoOfAR.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma ro_agree_of_AR : A.AF0m.CtrlTSyms B -> A.ProgWorld.AR_states_owned_ro B ->
  forall (RLO RHI : Z) ly S (W : lib.Reusable.YA0n.world segs) (mem : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W mem md ->
    lib.Reusable.APostBase.arodata_okP segs RLO RHI B (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem) ->
    A.ACtlK.ro_agree_at mem.
Proof.
  intros HTS Howned RLO RHI ly S W m md HAR Hro.
  apply (A.ProgWorld.ro_agree_of_view W m).
  intros a Ha.
  destruct (A.ProgWorldCtlRt.exists_zr_dec (bv_unsigned a) (lib.Reusable.YG0f.as_owned_static B)) as [Ho|Ho].
  - exact (Howned ly S W m md HAR a Ha Ho).
  - assert (Hin : lib.Reusable.APostBase.in_roP segs RLO RHI (bv_unsigned a)).
    { left. unfold Lib.Mem.ro_addr in Ha.
      destruct (find_segment A.Img0.rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate Ha].
      destruct (A.ProgWorldCtlRt.find_segment_some_spec _ _ _ _ E) as (Hins & Hb1 & Hb2).
      exists s. split; [exact Hins|].
      destruct (seg_writable s) eqn:Ew; [cbn in Ha; discriminate Ha|].
      split; [reflexivity | lia]. }
    assert (Herr : ~ (lib.Reusable.YG0f.as_errno B <= bv_unsigned a < lib.Reusable.YG0f.as_errno B + 4)).
    { rewrite (A.AF0m.ts_errno B HTS). unfold A.AF0m.TFIB_ERRNO. exact (A.ProgWorldCtlRt.ro_not_errno a Ha). }
    pose proof (Hro (bv_unsigned a) Hin Ho Herr) as Hg.
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hg. exact Hg.
Qed.
End RoOfAR.

(* lib/A/ProgWorldRtC.v -- fuzz_ctrl image A (libreac v1.9.0): RT_used_of_AR_C and rt_of_core_C, route (C)'s forms of
   A.ProgWorldRt.RT_used_of_AR / rt_of_core (two Theorem Labs lanes 10:17Z).  Written by a Theorem Labs lane in its OWN
   file, as a Theorem Labs lane asked: ProgWorldRt.v and ProgWorldRtShadow.v (a Theorem Labs lane's text of record) are untouched and are only
   Required; nothing of them is copied.  ANNOUNCED ADDITION.

   RT_used_C is RT_used (ProgWorld.v:157-161) with its universal `A.AsanRT.shadow_rw m` replaced by the two shadow
   regions of route (C): the cut's own state, `shadow_rw_on (cut_shadow B ly S)`, and the image hull, `shadow_rw_on
   img_shadow` (A.ACtlRtC / A.ShadowRwOn, a Theorem Labs lane's form of record).  Neither statement takes
   A.ProgWorld.AR_states_vis0_shadow: the shadow parts come from AR through A.ACtlCutC.cut_shadow_of_AR /
   img_shadow_of_AR (RT_used_of_AR_C) or from ctl_rt_C (rt_of_core_C); the other conjuncts come from
   A.ProgWorldRt.RT_rest_of_AR exactly as RT_used_of_AR / rt_of_core take them.  The old RT_used_of_AR / rt_of_core /
   shadow_rw_of_AR stay until they have no user.  rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n YO09 YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0m A.AsanRT A.Img0 A.ACtlCut.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorldRt A.ShadowRwOn A.ACtlRtC A.ACtlCutC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Local Open Scope Z_scope.
Local Notation segs := A.AB1v.tfibsegs (only parsing).
(* the sink_head ProgWorld.v's statements (rt_of_core_stmt's ajournal) are elaborated at (ProgWorld.v:76) *)
#[local] Existing Instance A.AE2k.tfib_sink_head.

Section RtUsedC.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Definition RT_used_C ly (S : lib.Reusable.YG00.astate) (m : word -> option byte) : Prop :=
  A.AsanRT.asan_cells m /\
  A.ShadowRwOn.shadow_rw_on (A.ACtlRtC.cut_shadow B ly S) m /\ A.ShadowRwOn.shadow_rw_on A.ACtlRtC.img_shadow m /\
  A.AsanRT.asan_opt_cells m /\ A.AsanRT.asan_cf_cells m /\
  A.AsanRT.asan_uw_cells m /\ A.AsanRT.asan_fs_cells m /\
  Forall (fun p => In (fst p) A.ProgWorld.REAL_USED ->
                   Lib.Mem.bytes_at A.Img0.rsegs m (fst p) (Lib.Mem.le8 (Lib.Mem.wa (snd p)))) A.AsanRT.RT_REALS.

(* RT_used_of_AR_stmt (ProgWorld.v:885-888) with AR_states_vis0_shadow REMOVED and RT_used -> RT_used_C. *)
Definition RT_used_of_AR_C_stmt : Prop :=
  A.AF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md -> RT_used_C ly S m.

Lemma RT_used_of_AR_C : RT_used_of_AR_C_stmt.
Proof.
  unfold RT_used_of_AR_C_stmt, RT_used_C.
  intros HTS HL ly S W m md HAR.
  destruct (A.ProgWorldRt.RT_rest_of_AR B HTS HL ly S W m md HAR)
    as (Hcells & Hopt & Hcf & Huw & Hfs & Hreals).
  exact (conj Hcells
        (conj (A.ACtlCutC.cut_shadow_of_AR B HL ly S W m md HAR)
        (conj (A.ACtlCutC.img_shadow_of_AR B HTS HL ly S W m md HAR)
        (conj Hopt (conj Hcf (conj Huw (conj Hfs Hreals))))))).
Qed.
End RtUsedC.

Section RtOfCoreC.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

(* rt_of_core_stmt (ProgWorld.v:175-183) with its ctl_rt premise -> ctl_rt_C at the cut's own state (ly3, S3) and its
   conclusion ctl_RT -> RT_used_C at that state; the shadow parts are taken from ctl_rt_C. *)
Definition rt_of_core_C_stmt : Prop :=
  A.AF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall (cx : A.ACtlCut.ctlcx) (own : list (Z * Z)) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
    A.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
    lib.Reusable.YCbq.ajournal segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) FP
      (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
      own ly3 S3 W3 (ms_mem ms3) md3 k ->
    A.ACtlRtC.ctl_rt_C B ly3 S3 (ms_mem ms3) ->
    RT_used_C B ly3 S3 (ms_mem ms3).

Lemma rt_of_core_C : rt_of_core_C_stmt.
Proof.
  unfold rt_of_core_C_stmt, RT_used_C.
  intros HTS HL cx own k ly3 S3 W3 ms3 md3 Hbase Hj Hrt.
  destruct Hj as (HAR & _).
  destruct Hrt as (_ & Hcut & Himg & _).
  destruct (A.ProgWorldRt.RT_rest_of_AR B HTS HL ly3 S3 W3 (ms_mem ms3) md3 HAR)
    as (Hcells & Hopt & Hcf & Huw & Hfs & Hreals).
  exact (conj Hcells (conj Hcut (conj Himg (conj Hopt (conj Hcf (conj Huw (conj Hfs Hreals))))))).
Qed.
End RtOfCoreC.

Print Assumptions RT_used_of_AR_C.
Print Assumptions rt_of_core_C.

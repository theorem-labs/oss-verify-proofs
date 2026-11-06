(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldRtC.v (a working branch eb6fb525b71, read by git show, not merged): the same Sections, definitions, statements and proofs over image B.  Differences from A: (1) module paths: A.AsanRT / A.Img0 / A.ACtlCut / A.ProgWorld / A.ProgWorldRt / A.ShadowRwOn / A.ACtlRtC / A.ACtlCutC -> B.*, A.AB1v / A.AE2k / A.ACfn / A.AF0m -> lib.Reusable.YB1v / YE2k / YCfn / YF0m; (2) A's `Lib.Mem.bytes_at / le8 / wa` (RT_used_C's last conjunct) are written lib.Lib.Mem.X, the same constants, as lib/B/ProgWorld.v's RT_used writes them (lib/Lib/Mem.v also exists as lib/B/Bz/Lib/Mem.v); (3) every Require names the full directory of the one copy a clean checkout binds; (4) comments: the first lines name image B and the twin, and A's ProgWorld.v:157-161 / 885-888 / 175-183 / 77 are B's ProgWorld.v:181-185 / 910-913 / 199-207 / 97.  No number is taken from A. *)
(* lib/B/ProgWorldRtC.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): RT_used_of_AR_C and rt_of_core_C, route (C)'s
   forms of B.ProgWorldRt.RT_used_of_AR / rt_of_core (two Theorem Labs lanes 10:17Z).  Image-B twin of a Theorem Labs lane's
   lib/A/ProgWorldRtC.v, in its OWN file, as a Theorem Labs lane asked for A: ProgWorldRt.v and ProgWorldRtShadow.v are
   untouched and are only Required; nothing of them is copied.  ANNOUNCED ADDITION.

   RT_used_C is RT_used (ProgWorld.v:181-185) with its universal `B.AsanRT.shadow_rw m` replaced by the two shadow
   regions of route (C): the cut's own state, `shadow_rw_on (cut_shadow B ly S)`, and the image hull, `shadow_rw_on
   img_shadow` (B.ACtlRtC / B.ShadowRwOn, the B twins of a Theorem Labs lane's form of record).  Neither statement takes
   B.ProgWorld.AR_states_vis0_shadow: the shadow parts come from AR through B.ACtlCutC.cut_shadow_of_AR /
   img_shadow_of_AR (RT_used_of_AR_C) or from ctl_rt_C (rt_of_core_C); the other conjuncts come from
   B.ProgWorldRt.RT_rest_of_AR exactly as RT_used_of_AR / rt_of_core take them.  The old RT_used_of_AR / rt_of_core /
   shadow_rw_of_AR stay until they have no user.  rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n YO09 YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YE2k YCfn YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require AsanRT Img0 ACtlCut.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorld ProgWorldRt ShadowRwOn ACtlRtC ACtlCutC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Local Open Scope Z_scope.
Local Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).
(* the sink_head ProgWorld.v's statements (rt_of_core_stmt's ajournal) are elaborated at (ProgWorld.v:97) *)
#[local] Existing Instance lib.Reusable.YE2k.tfib_sink_head.

Section RtUsedC.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Definition RT_used_C ly (S : lib.Reusable.YG00.astate) (m : word -> option byte) : Prop :=
  B.AsanRT.asan_cells m /\
  B.ShadowRwOn.shadow_rw_on (B.ACtlRtC.cut_shadow B ly S) m /\ B.ShadowRwOn.shadow_rw_on B.ACtlRtC.img_shadow m /\
  B.AsanRT.asan_opt_cells m /\ B.AsanRT.asan_cf_cells m /\
  B.AsanRT.asan_uw_cells m /\ B.AsanRT.asan_fs_cells m /\
  Forall (fun p => In (fst p) B.ProgWorld.REAL_USED ->
                   lib.Lib.Mem.bytes_at B.Img0.rsegs m (fst p) (lib.Lib.Mem.le8 (lib.Lib.Mem.wa (snd p)))) B.AsanRT.RT_REALS.

(* RT_used_of_AR_stmt (ProgWorld.v:910-913) with AR_states_vis0_shadow REMOVED and RT_used -> RT_used_C. *)
Definition RT_used_of_AR_C_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md -> RT_used_C ly S m.

Lemma RT_used_of_AR_C : RT_used_of_AR_C_stmt.
Proof.
  unfold RT_used_of_AR_C_stmt, RT_used_C.
  intros HTS HL ly S W m md HAR.
  destruct (B.ProgWorldRt.RT_rest_of_AR B HTS HL ly S W m md HAR)
    as (Hcells & Hopt & Hcf & Huw & Hfs & Hreals).
  exact (conj Hcells
        (conj (B.ACtlCutC.cut_shadow_of_AR B HL ly S W m md HAR)
        (conj (B.ACtlCutC.img_shadow_of_AR B HTS HL ly S W m md HAR)
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

(* rt_of_core_stmt (ProgWorld.v:199-207) with its ctl_rt premise -> ctl_rt_C at the cut's own state (ly3, S3) and its
   conclusion ctl_RT -> RT_used_C at that state; the shadow parts are taken from ctl_rt_C. *)
Definition rt_of_core_C_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall (cx : B.ACtlCut.ctlcx) (own : list (Z * Z)) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
    B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
    lib.Reusable.YCbq.ajournal segs B lib.Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
      (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
      own ly3 S3 W3 (ms_mem ms3) md3 k ->
    B.ACtlRtC.ctl_rt_C B ly3 S3 (ms_mem ms3) ->
    RT_used_C B ly3 S3 (ms_mem ms3).

Lemma rt_of_core_C : rt_of_core_C_stmt.
Proof.
  unfold rt_of_core_C_stmt, RT_used_C.
  intros HTS HL cx own k ly3 S3 W3 ms3 md3 Hbase Hj Hrt.
  destruct Hj as (HAR & _).
  destruct Hrt as (_ & Hcut & Himg & _).
  destruct (B.ProgWorldRt.RT_rest_of_AR B HTS HL ly3 S3 W3 (ms_mem ms3) md3 HAR)
    as (Hcells & Hopt & Hcf & Huw & Hfs & Hreals).
  exact (conj Hcells (conj Hcut (conj Himg (conj Hopt (conj Hcf (conj Huw (conj Hfs Hreals))))))).
Qed.
End RtOfCoreC.

Print Assumptions RT_used_of_AR_C.
Print Assumptions rt_of_core_C.

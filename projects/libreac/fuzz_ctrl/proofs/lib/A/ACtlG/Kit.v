(* lib/A/ACtlG/Kit.v -- the shared helpers of the GLUE lemmas of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v's stage hypotheses, one glue file per stage in lib/A/ACtlG/).  Written by a Theorem Labs lane,
   moved out of the pilot lib/A/ACtlG/A5.v unchanged (statements and proofs; renamed from the a5_
   prefix to the kit_ prefix); single writer: the lead of the glue lanes.  Every glue file Requires this file QUALIFIED
   (`From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.`) and never copies a helper; the
   pattern is glue-pattern.md (a working note, not in this delivery).  rule 24: no function proved.

   THE REGISTER-MAP MOVE IS NOT HERE.  ctrl's runs start at a canonical register map (Regs6ss.mkR_of regs, or an
   explicit mkR r1 .. r31); the cut's configuration is Reusable.YG0d.cfg_at = mkCfg of lib/Lib's MS over the
   actual map (A/ProgBridge.v cfg_at_MS), and the two maps are only Regs6ss.xregs_eqv.  a Theorem Labs lane's kit now
   moves a WALK along that equivalence: Reusable.YA0nR.SRr_xregs_eqv (with SRr_xregs_iff and SRr_cfg_eqv), PROVED
   at a working branch 5f2500c036a (lemmas in 6517e7b00a9, build 20261029T001125Z
   rc=0).  It replaces the four run-level helpers this file held before (kit_mstepsF_eqv, kit_evtF_eqv,
   kit_MS_of_eqv, kit_getr_eqv), which are deleted.

   WHICH HELPER SERVES WHICH GLUE STEP (glue-pattern.md section 3)
     kit_wx           G4  the kit's once-per-unit premise of Reusable.YA0nR.SRr_fevt / SRr_fevt_hid:
                          wx_segs_nowrap segs.  Proof: the planning core's Hwx_tfa (A/ACeg.v:61-62); the same proof
                          type-checks as a Theorem Labs lane's ctrl_wx (lib/A/Prog/CtrlImg.v (at head lib/A/Prog/CtrlImg.v:42-43;
                          from a working branch 94d4995b31f)).
     kit_segs_low     G5  the image placement premise of Reusable.YCbq.ajournal_exec (and of every YCbq Section a0 /
                          d0 lemma: aj_intrin_at, aj_bcmp_at, ajournal_after_write).  Proof: the planning core's
                          tfib_segs_low (A/ACeg.v:63-72, = CtrlImg.v:44-52 ctrl_segs_low), with a last line that
                          does not fix the number of segments.
     kit_frac_move    G5  ACtlCutP.FRAC (ACtlCutP.v:982-997) moves along a register map that keeps registers 2 3 4 8 9
                          19 26 (the only ones FRAC reads; 2 also through spZ; the fake-frame trailer word, FRAC's last
                          conjunct, reads memory only).  SRr_xregs_eqv does not replace it:
                          it moves the cut body's FRAC from the entry map to the run's end map, two maps that
                          differ on the registers the run writes.
     kit_RNG0         G4  the empty footprint: a register-only run makes no data access (an instruction fetch is not
                          an access, ExecF.v:98-101), so it is lifted with fp_avoids vacuous.
     kit_ajournal_fp_nil    the FP lift of the journal at the exit (a Theorem Labs lane's request, 03:56Z): ACtl.v's
                          ajournal_fp_nil (the donor's A/ACfh.v:29-43 over the core's helpers), whose Section ACtl.v
                          declares above Section Ctl, so a glue file that ACtl.v Requires cannot cite it there.
                          Statement and proof: a Theorem Labs lane's y3_ajournal_fp_nil (lib/A/ACtlG/Y3.v (a version not in this delivery; written on a working branch d1e2e4be924)),
                          same Section shape (fx rc, SK, B).
     kit_ev_llvmf_le        the walk's event bound meets the core's: A.ACtlK.EV_LLVMF <= A.ACfn.EV_LIB (526 <= 2000;
                          a Theorem Labs lane's request, 03:56Z), for the k <= EV_LIB conjunct of tfib_lib_post_x.

   CLOSURE (the glue closure rule, a Theorem Labs lane 23:32Z, FINAL with the porter 23:38Z / 23:40Z): every Require below is
   qualified (no Import / Export of a project module); no statement names a frame-route identifier.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are Reusable.YK11 / Reusable.YG0d-qualified everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/Kit.v   -- hits only inside comments.

   BUILD STATE (honest): TYPECHECKS on the image-A PLANNING core 5a85b67a5d8 (TYPE-CHECK ONLY, values do not count):
   cb build on the packed fuzz_ctrl base 362baf478bf5 (FACTS ed6b6b7b0ab), with the core's undefined
   port_core_refused_<hex> names replaced by the hex literal in the build workspace only (core errors, reported
   to the porter a Theorem Labs lane).  No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YG0f YG0d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v ACfn ACtlK ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:155 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueKit.

(* The glue files' Section shape (ACtl.v:162-166); End GlueKit keeps only what each helper uses (B for
   kit_frac_move). *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* The planning core's Hwx_tfa (A/ACeg.v:61-62), the kit's once-per-unit premise. *)
Lemma kit_wx : Reusable.YK04.wx_segs_nowrap segs.
Proof. apply Reusable.YK04.wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* The planning core's tfib_segs_low (A/ACeg.v:63-72); the last line runs through however many segments the
   image has instead of naming four. *)
Lemma kit_segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr). unfold Reusable.YG0f.kLowMemEnd.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                 (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs)).
  { exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs sg Hin). }
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H.
  repeat (destruct H as [H | H]; [injection H as <- <-; lia |]).
  destruct H.
Qed.

(* FRAC (ACtlCutP.v:982-997) reads registers 2 (also through spZ), 3, 4, 8, 9, 19 and 26 only. *)
Lemma kit_frac_move : forall cx fr sel (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCutP.FRAC B cx fr sel regs m ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 3 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 4 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 8 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 8 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 19 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 19 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 26 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 26 ->
  ACtlCutP.FRAC B cx fr sel regs' m.
Proof.
  intros cx fr sel regs regs' m H E2 E3 E4 E8 E9 E19 E26.
  unfold ACtlCutP.FRAC, ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite E2, E3, E4, E8, E9, E19, E26. exact H.
Qed.

(* The empty footprint: a register-only run makes no data access, so it is lifted with no visibility fact. *)
Definition kit_RNG0 : Lib.ExecF.footprint := fun _ _ => False.

End GlueKit.

(* ajournal_fp_nil over the core's helpers (ACtl.v's, the donor's A/ACfh.v:29-43), for a glue file that cannot
   cite ACtl.v.  a Theorem Labs lane's y3_ajournal_fp_nil, statement and proof unchanged (header). *)
Section KitFpNil.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Lemma kit_ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply Reusable.YCbq.aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (Reusable.YCbq.sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply (Reusable.YCbq.fp_spares_closed (SK := SK)); intros Ho; exact (Reusable.YCbq.sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
End KitFpNil.

(* The walk's event bound (ACtlK.v:43, 526) meets the core's (A.ACfn.EV_LIB, 2000). *)
Lemma kit_ev_llvmf_le : A.ACtlK.EV_LLVMF <= A.ACfn.EV_LIB.
Proof. unfold A.ACtlK.EV_LLVMF, A.ACfn.EV_LIB. lia. Qed.

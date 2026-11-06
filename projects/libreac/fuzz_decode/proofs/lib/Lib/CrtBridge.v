(* CrtBridge: the image-neutral half of the step that carries a footprint run (lib/Lib/ExecF.v) into cgif's SRr
   walk.  Nothing here mentions an image: the segment list is a Variable, as in ExecF.v, and the register map is
   arbitrary.  Image A uses it in lib/A/Prog/crtA_bridge.v, image B in its twin.

   Why it is needed: cgif's configuration (lib/Reusable/YG0d.v:213 cfg_at, over lib/Reusable/YK11.v:17 mkst) carries
   the caller's own register map, while decode's footprint runs start from a state whose register map is `mkR` of
   the 31 register values (lib/Lib/Regs6ss.v:456 mkR_of).  The two maps are not equal, only xregs_eqv
   (Regs6ss.v:20), so a run has to be transported along ms_eqv (Regs6ss.v:144) first.  The transport is proved from
   Regs6ss.v:227 step_accesses_eqv; it adds no assumption. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Regs6ss ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
Import ListNotations.
Open Scope Z_scope.

Section Transport.
Variable segs : list Segment.
Variable RNG : ExecF.footprint.

(* One step of a footprint run is invariant under xregs_eqv: the semantics reads registers only through ms_reg. *)
Lemma mstepF_eqv : forall ms1 ms2 ms1',
  ms_eqv ms1 ms2 -> ExecF.mstepF segs RNG ms1 ms1' ->
  exists ms2', ExecF.mstepF segs RNG ms2 ms2' /\ ms_eqv ms1' ms2'.
Proof.
  intros ms1 ms2 ms1' Heqv [Hsvc (accs & Hstep & Hacc)].
  pose proof (step_accesses_eqv segs ms1 ms2 Heqv) as Hr.
  rewrite Hstep in Hr. unfold rep_eqv in Hr.
  destruct (RiscvSemantics.step_accesses segs ms2) as [rep2| |] eqn:Hstep2; [|destruct Hr|destruct Hr].
  destruct rep2 as [ms2' accs2]. cbn [access_value accessed_ranges] in Hr.
  destruct Hr as [Hms Haccs].
  exists ms2'. split; [|exact Hms].
  split.
  - pose proof Heqv as (_ & _ & _ & Hsv & _). rewrite <- Hsv. exact Hsvc.
  - exists accs2. split; [exact Hstep2|]. rewrite <- Haccs. exact Hacc.
Qed.

Lemma mstepsF_eqv : forall ms1 ms1',
  ExecF.mstepsF segs RNG ms1 ms1' ->
  forall ms2, ms_eqv ms1 ms2 -> exists ms2', ExecF.mstepsF segs RNG ms2 ms2' /\ ms_eqv ms1' ms2'.
Proof.
  intros ms1 ms1' H. induction H as [ms | ms msa msb Hstep Hrest IH]; intros ms2 Heqv.
  - exists ms2. split; [apply ExecF.mstepsF_refl | exact Heqv].
  - destruct (mstepF_eqv ms ms2 msa Heqv Hstep) as (ms2a & Hstep2 & Heqva).
    destruct (IH ms2a Heqva) as (ms2' & Hrest2 & Heqv').
    exists ms2'. split; [eapply ExecF.mstepsF_cons; eassumption | exact Heqv'].
Qed.

(* A run from an xregs_eqv state reaches an xregs_eqv final state. *)
Lemma evtF_eqv : forall (P : machine_state -> Prop) ms1 ms2,
  ms_eqv ms1 ms2 -> ExecF.evtF segs RNG P ms1 ->
  ExecF.evtF segs RNG (fun ms => exists ms0, P ms0 /\ ms_eqv ms0 ms) ms2.
Proof.
  intros P ms1 ms2 Heqv (ms1' & Hrun & HP).
  destruct (mstepsF_eqv ms1 ms1' Hrun ms2 Heqv) as (ms2' & Hrun2 & Heqv').
  exists ms2'. split; [exact Hrun2|]. exists ms1'. split; [exact HP | exact Heqv'].
Qed.
End Transport.

Section Shape.
Context {fx : YK11.FPState}.

Lemma getr_nonzero : forall (regs : bvmap 5 word) (r : reg), is_x0 r = false -> YK11.getr regs r = reg_get regs r.
Proof.
  intros regs r Hr. unfold YK11.getr, is_x0 in *. destruct (bv_eqb r 0) eqn:E; [|reflexivity].
  exfalso. apply bv_eqb_eq in E. subst r. cbn in Hr. discriminate Hr.
Qed.

(* cgif's machine state at a pc and decode's `mkR` state agree up to xregs_eqv, for any ROM. *)
Lemma mkst_eqv_mkR_of : forall (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte),
  ms_eqv (@YK11.mkst fx regs pc mem rom)
         (MS (mkR_of regs) (@fp_regs fx) pc (@fp_csr fx) None mem rom).
Proof.
  intros regs pc mem rom. unfold ms_eqv, YK11.mkst.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  repeat split; try reflexivity. apply mkR_of_eqv.
Qed.
End Shape.

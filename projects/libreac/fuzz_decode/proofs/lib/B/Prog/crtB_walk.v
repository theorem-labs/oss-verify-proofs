(* crtB_walk: the toolkit of the cgif-form walk of check_round_trip (image B of libreac/fuzz_decode): one footprint
   run carried into cgif's SRr, landing in a cgif-shaped configuration.  Twin of lib/A/Prog/crtA_walk.v
   (a working branch 7a7510b6213), at image B; the pieces of the walk and the close onto
   lib/B/Prog/check_round_trip_cg.v use it.

   FORM (the porter's ruling, 2026-10-29 01:54Z): the function's own code runs as decode's footprint runs
   (lib/B/Prog/crtB_segs.v and the loop lane's file, ported from a working branch dc455613c81), each
   carried into SRr after the state transport of lib/Lib/CrtBridge.v; the journal is re-established across each
   run by lib/Reusable/YCbq.v:636 ajournal_exec; each call is cut by its callee contract.
   Difference from the crtA twin: the bridge LeafCgKit.v:101 bridge_evtF_stmt is NOT a Section hypothesis here; it
   is proved (crtB_bridge_evtF below) from lib/B/Prog/crtB_fevt.v crtB_SRr_evtF, the port of cgif's SRr_fevt, so
   the walk's final theorem carries no kit assumption.

   Exits: the only exit is the tail jump to free at CRT_AT 0x2e8.  Every __asan_report_* entry of these images
   RETURNS (a Theorem Labs lane, 2026-10-29 02:13Z), so no block is closed by treating a report call as terminal: the abort
   block, the UBSan traps and the five report calls are excluded by refuting the guard of the branch into them,
   inside the segment runs. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Regs6ss ExecF CrtBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_iface crtB_bridge crtB_fevt.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.

Section CrtWalk.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Notation segs := decodesegsB0.

(* The bridge from a footprint run to cgif's walk: LeafCgKit.v:101 at cgif's world and SRr, proved in
   lib/B/Prog/crtB_fevt.v from the image-neutral lib/Lib/CrtFevt.v. *)
Lemma crtB_bridge_evtF : LCK.bridge_evtF_stmt (world segs) (@w_H segs) (SRr segs) same_but_materialized.
Proof. exact crtB_bridge_holds. Qed.

(* The footprint the walk gives every run: all visible bytes; it avoids the world's hidden bytes by construction. *)
Lemma crtB_fp_avoids_W : forall (W : world segs), LCK.fp_avoids (@w_H segs W) (LCK.RNG_W (world segs) (@w_H segs) W).
Proof.
  intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* A footprint run from cgif's configuration at pc: the run is the one of decode's state ms_of_regs; the walk
   continues from every state the transported run can reach. *)
Lemma crtB_run : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (pc : Z)
    (P : machine_state -> Prop) (Q : world segs -> config -> Prop),
  ExecF.evtF rsegs (LCK.RNG_W (world segs) (@w_H segs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr segs W (mkCfg ms' md') Q) ->
  SRr segs W (@cfg_at fx segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K.
  unfold cfg_at.
  apply (crtB_bridge_evtF W (@YKK.mkst fx regs (w64 pc) mem (YKK.seg_rom segs)) md
           (LCK.RNG_W (world segs) (@w_H segs) W) (fun ms => exists ms0, P ms0 /\ ms_eqv ms0 ms) Q).
  - apply (evtF_eqv rsegs _ P (@LCK.ms_of_regs fx pc regs mem)).
    + apply ms_eqv_sym. exact (@mkst_eqv_ms_of_regs fx pc regs mem).
    + exact Hrun.
  - apply crtB_fp_avoids_W.
  - exact K.
Qed.

(* A state xregs_eqv to decode's MS form with cgif's float state is cgif's mkst state of its own register map. *)
Lemma crtB_ms_shape : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte) (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YKK.seg_rom segs)) ms' ->
  ms' = @YKK.mkst fx (ms_regs ms') pc m (YKK.seg_rom segs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

(* ... and its registers are R's (x1 .. x31). *)
Lemma crtB_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> is_x0 r = false ->
  YKK.getr (ms_regs ms') r = YKK.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _) Hr. cbn [MS ms_regs] in HR.
  rewrite !getr_nonzero by exact Hr. symmetry. apply HR. exact Hr.
Qed.
End CrtWalk.

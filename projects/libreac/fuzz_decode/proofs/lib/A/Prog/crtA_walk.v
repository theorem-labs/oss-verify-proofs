(* crtA_walk: the toolkit of the cgif-form walk of check_round_trip (image A of libreac/fuzz_decode): one footprint
   run carried into cgif's SRr, landing in a cgif-shaped configuration.  The four pieces of the walk
   (lib/A/Prog/crtA_w_*.v) and the close onto lib/A/Prog/check_round_trip_cg.v use it.

   FORM (the porter's ruling, 2026-10-29 01:54Z): the function's own code runs as decode's footprint runs
   (lib/A/Prog/crtA_segs.v and crtA_loop.v, ported from a working branch dc455613c81), each carried
   into SRr by LeafCgKit.v:101 bridge_evtF_stmt after the state transport of lib/Lib/CrtBridge.v; the journal is
   re-established across each run by lib/Reusable/YCbq.v:636 ajournal_exec; each call is cut by its callee
   contract.  The Pa engine cannot walk this function: its convert loop is float code and lib/Reusable/YP0l.v:265
   answers SR_unsupported on every float instruction.

   Exits: the only exit is the tail jump to free at CRT_AT 0x264.  Every __asan_report_* entry of these images
   RETURNS (a Theorem Labs lane, 2026-10-29 02:13Z), so no block is closed by treating a report call as terminal: the abort
   block and the five report calls are excluded by refuting the guard of the branch into them, inside the
   segment runs. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Regs6ss ExecF CrtBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_iface crtA_bridge crtA_fevt.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LeafCgKit.

Section CrtWalk.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Notation segs := decodesegs0.

(* The bridge from a footprint run to cgif's walk: LeafCgKit.v:101 at cgif's world and SRr.  It is PROVED, in
   lib/A/Prog/crtA_fevt.v crtA_bridge_holds (image A's instance of lib/Lib/CrtFevt.v, itself the port of
   a working branch eea54967566 lib/Reusable/YK04R.v / YA0nR.v at ExecF.mstepsF, following image B's
   lib/B/Prog/crtB_fevt.v on a working branch at 82cbfac97a3), so the walk carries no bridge
   hypothesis. *)
Local Notation BRIDGE := crtA_bridge_holds.

(* The footprint the walk gives every run: all visible bytes; it avoids the world's hidden bytes by construction. *)
Lemma crtA_fp_avoids : forall (W : world segs), LCK.fp_avoids (@w_H segs W) (LCK.RNG_W (world segs) (@w_H segs) W).
Proof.
  intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* A footprint run from cgif's configuration at pc: the run is the one of decode's state ms_of_regs; the walk
   continues from every state the transported run can reach. *)
Lemma crtA_run : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (pc : Z)
    (P : machine_state -> Prop) (Q : world segs -> config -> Prop),
  ExecF.evtF rsegs (LCK.RNG_W (world segs) (@w_H segs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr segs W (mkCfg ms' md') Q) ->
  SRr segs W (@cfg_at fx segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K.
  unfold cfg_at.
  apply (BRIDGE W (@YKK.mkst fx regs (w64 pc) mem (YKK.seg_rom segs)) md (LCK.RNG_W (world segs) (@w_H segs) W)
           (fun ms => exists ms0, P ms0 /\ ms_eqv ms0 ms) Q).
  - apply (evtF_eqv rsegs _ P (@LCK.ms_of_regs fx pc regs mem)).
    + apply ms_eqv_sym. exact (@mkst_eqv_ms_of_regs fx pc regs mem).
    + exact Hrun.
  - apply crtA_fp_avoids.
  - exact K.
Qed.

(* A state xregs_eqv to decode's MS form with cgif's float state is cgif's mkst state of its own register map. *)
Lemma crtA_ms_shape : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte) (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YKK.seg_rom segs)) ms' ->
  ms' = @YKK.mkst fx (ms_regs ms') pc m (YKK.seg_rom segs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

(* ... and its registers are R's (x1 .. x31). *)
Lemma crtA_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> is_x0 r = false ->
  YKK.getr (ms_regs ms') r = YKK.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _) Hr. cbn [MS ms_regs] in HR.
  rewrite !getr_nonzero by exact Hr. symmetry. apply HR. exact Hr.
Qed.
End CrtWalk.

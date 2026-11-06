(* fuzz_ctrl image A, ctrl_emit_as (0x849d8): the one instruction at the cut of a Theorem Labs lane's cgif-form glue, as a
   footprint run of its own.

   The first lifted stretch (A/Prog/ctrl_emit_asF2.v ctrl_emit_as_pre_lay_F) ends at pc 0x84cec, BEFORE the
   instruction there; the callee contract the glue applies next (A/Prog/C_ctrl_lay_block.v, TLAY) is stated at
   ctrl_lay_block's entry 0x855f4 with the return address 0x84cf0 in x1. The instruction between them is
   0x84cec jal ra,0x855f4 (read from the image by a Theorem Labs lane, A/Prog/ctrl_emit_asF2.v:31-32), and this file runs it:
     - ge_jal_lay: the run 0x84cec -> 0x855f4 as ExecF.mstepsF (one step), for ProgBridge.fsteps_of_mstepsF;
     - ge_jal_evt: the same as an ExecF.evtF goal, for any property P of the state at 0x855f4, for
       ProgBridge.fevt_of_evtF.

   Footprint: none. A jal makes no memory access: the step's access list is empty (the instruction fetch is not an
   access), so both lemmas hold for EVERY footprint RNG and take no rng, addressable or memory premise. The memory
   mc, the FP registers F, fcsr fc, the reservation (None) and the rom (seg_rom rsegs) are unchanged.

   Register form. StepF's `step` leaves the register map as
     bvmap_set (BV 5 1 (Z_to_bv_obligation_1 5 _)) (Z_to_bv 64 0x84cf0) R
   that is, a bvmap_set of x1 whose key carries the decoder's own well-formedness proof. No source text can write
   that key, and it is NOT convertible to the literal 1%bv (= BV 5 1 I) nor to Z_to_bv 5 1 (the obligation is
   opaque). The lemmas state the map as
     lib.Reusable.YK11.regupd R 1 (Z_to_bv 64 0x84cf0)          (= bvmap_set 1 (Z_to_bv 64 0x84cf0) R by delta of regupd)
   which is the step's map with only the key rewritten to the literal 1%bv (by bv_eq: both keys have
   bv_unsigned 1). It is the core's own register update, written QUALIFIED because lib.Lib's PropExec.regupd
   (the same body) shadows it in this import mix; so lib.Reusable.YK11.getr_same and lib.Reusable.YK11.getr_other read the lib.Reusable.YK11.getr
   premises of C_ctrl_lay_block.v straight off it: getr regs' 1 = Z_to_bv 64 0x84cf0 and getr regs' r =
   getr R r (r <> 1). The value is the
   Z literal 0x84cf0 (= 543984) and the pc is Z_to_bv 64 0x855f4, both as the step produces them.

   Glue closure rule (two Theorem Labs lanes, 2026-10-28 23:38Z): no _F file is Required here at all. The import
   block is A/Prog/GEbase.v's, with StepF (lib.Lib, the evtF step engine) last, as A/Prog/ctrl_emit_asF2.v
   orders it. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Tac StepF.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

(* 0x84cec jal ra,0x855f4: x1 := 0x84cf0, pc := 0x855f4, nothing else changes. *)
Lemma ge_jal_lay : forall (RNG : ExecF.footprint) (R F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte),
  ExecF.mstepsF rsegs RNG
    (MS R F (Z_to_bv 64 0x84cec) fc None mc (seg_rom rsegs))
    (MS (lib.Reusable.YK11.regupd R 1 (Z_to_bv 64 0x84cf0)) F (Z_to_bv 64 0x855f4) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG R F fc mc.
  assert (H : ExecF.evtF rsegs RNG
                (eq (MS (lib.Reusable.YK11.regupd R 1 (Z_to_bv 64 0x84cf0)) F (Z_to_bv 64 0x855f4) fc None mc (seg_rom rsegs)))
                (MS R F (Z_to_bv 64 0x84cec) fc None mc (seg_rom rsegs))).
  { step.
    (* the step's x1 key carries the decoder's proof; rewrite it to the literal 1 *)
    match goal with
    | |- context [bvmap_set ?k (Z_to_bv 64 0x84cf0) R] =>
        replace k with (1%bv : bv 5) by (apply bv_eq; reflexivity)
    end.
    apply ExecF.evtF_done. reflexivity. }
  destruct H as (ms' & Hrun & <-). exact Hrun.
Qed.

(* The same step as the evtF goal the glue lifts with ProgBridge.fevt_of_evtF. *)
Lemma ge_jal_evt : forall (RNG : ExecF.footprint) (R F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte)
    (P : machine_state -> Prop),
  P (MS (lib.Reusable.YK11.regupd R 1 (Z_to_bv 64 0x84cf0)) F (Z_to_bv 64 0x855f4) fc None mc (seg_rom rsegs)) ->
  ExecF.evtF rsegs RNG P (MS R F (Z_to_bv 64 0x84cec) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG R F fc mc P HP.
  exists (MS (lib.Reusable.YK11.regupd R 1 (Z_to_bv 64 0x84cf0)) F (Z_to_bv 64 0x855f4) fc None mc (seg_rom rsegs)).
  split; [exact (ge_jal_lay RNG R F fc mc) | exact HP].
Qed.

(* Both rest on nothing but the semantics' own axioms (the build log shows the list). *)
Print Assumptions ge_jal_lay.
Print Assumptions ge_jal_evt.

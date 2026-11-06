(* lib/A/Prog/Seg/RNIngFon.v -- route (C) form of Seg/RNIngF.v's run rn_ing_evt_F (fuzz_ctrl image A, the shared
   ingest tail 0x81714 .. 0x81730 of segments R11 / R12 and the call of reac_identity_ingest).  ADDITIVE beside-file:
   this file edits no line of Seg/RNIngF.v (owner a Theorem Labs lane; not in this delivery), whose later versions differ from the BASE below only in the module qualification of Frame.outside / munch / wmono in rn_ing_evt_of_F_bounded; the rule of the L3 brief (a working note, not in this delivery) (a Theorem Labs lane 12:52Z,
   agreed) puts this twin in this lane.  Written by a Theorem Labs lane.  rule 24: no function proved (a
   footprint run of a segment).

   WHAT IT IS.  rn_ing_evt_F_on is RNIngF.rn_ing_evt_F (RNIngF.v (not in this delivery) at a Theorem Labs lane's fold a working branch
   4bae33fdf54, blob 19d0d469524) with exactly two changes:
     - the premise `shadow_rw m ->` is removed: the run's own eight instructions read no shadow byte, and its only
       use was to be forwarded to the callee contract;
     - the callee hypothesis INGF is reac_identity_ingest_contract_F_on (a Theorem Labs lane 28e24b8fe6c,
       lib/A/Prog/reac_identity_ingest_c.v 9f4749b6486 (the blob this tree had at release c5e779efe8c)), the footprint contract with that premise DROPPED,
       proved by reac_identity_ingestF.reac_identity_ingest_F_holds_on (a Theorem Labs lane 330e60af39d, blob f2407e89a16).
   Every other binder, premise and the post are RNIngF.rn_ing_evt_F's, term for term (the core copies that statement
   names: lib/Lib's Frame / MState / Mem / Cells / Step, ctrl's A.Reusable.YK11.seg_rom and A.Img0.rsegs).  The
   proof is RNIngF.v's script with the `exact HSW` bullet removed.  No pin to the old lemma: the old one is
   quantified over the OLD contract (reac_identity_ingest_contract_F), which does not give the narrowed one, so it is
   not a one-line corollary of this one; it stays byte-identical (a Theorem Labs lane's condition).

   BASE.  The fold's blob 19d0d469524 differs from a working branch's dcc49379a66 (a working branch 8ce82d7e310)
   only in spelling: `Frame.outside / munch / wmono` -> `LFr.*` (LFr := lib.Lib.Frame) and `MState.unsigned_lit` ->
   the full path of A.Tk.UL.MState's, which is what the short names resolved to.  This file starts from the fold's
   text and writes every twin-library name by a path that picks one copy (the gate's rule), Requires without Import,
   and sets nothing globally. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_ingest_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.RNIng.
Import ListNotations.
Local Open Scope Z_scope.

Section RNIngFon.
(* The callee's narrowed footprint contract (premise shadow_rw dropped), in the place of RNIngF's INGF. *)
Hypothesis INGF : A.Prog.reac_identity_ingest_c.reac_identity_ingest_contract_F_on.

Lemma rn_ing_evt_F_on :
  forall (RNG : lib.Lib.ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A id pa pp pn ad p len lo : Z) (idb pb : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s5 = Z_to_bv 64 id ->
    0 <= spv < 2 ^ 64 -> spv mod 16 = 0 ->
    0 < id < 2 ^ 64 -> id mod 2 = 0 -> 0 <= ad < 65536 -> 0 < p < 2 ^ 64 -> 0 < len < 2 ^ 64 ->
    ov_read_bytes A.Img0.rsegs m (lib.Lib.Mem.wa (A + 88)) 8 = Some (lib.Lib.Mem.le8 (Z_to_bv 64 pa)) ->
    ov_read_bytes A.Img0.rsegs m (lib.Lib.Mem.wa (A + 80)) 8 = Some (lib.Lib.Mem.le8 (Z_to_bv 64 pp)) ->
    ov_read_bytes A.Img0.rsegs m (lib.Lib.Mem.wa (A + 72)) 8 = Some (lib.Lib.Mem.le8 (Z_to_bv 64 pn)) ->
    ov_read_bytes A.Img0.rsegs m (lib.Lib.Mem.wa pa) 2 = Some (lib.Lib.Mem.le2 (Z_to_bv 64 ad)) ->
    ov_read_bytes A.Img0.rsegs m (lib.Lib.Mem.wa pp) 8 = Some (lib.Lib.Mem.le8 (Z_to_bv 64 p)) ->
    ov_read_bytes A.Img0.rsegs m (lib.Lib.Mem.wa pn) 8 = Some (lib.Lib.Mem.le8 (Z_to_bv 64 len)) ->
    lib.Lib.Step.rw_cells A.Img0.rsegs m id [lib.Lib.Cells.CB 38 idb] ->
    length pb = Z.to_nat len -> lib.Lib.Mem.bytes_at A.Img0.rsegs m p pb ->
    p + len <= id \/ id + 38 <= p ->
    lib.Lib.Frame.stk A.Img0.rsegs m lo spv -> lo + 32 <= spv ->
    (id + 38 <= spv - 32 \/ spv <= id) -> (p + len <= spv - 32 \/ spv <= p) ->
    A.AsanRT.asan_cells m -> A.AsanRT.addressable m id 38 -> A.AsanRT.addressable m p len ->
    (forall x, A.AsanRT.GOT_CELL_K <= x < A.AsanRT.GOT_CELL_K + 8 \/ A.AsanRT.CELL_K <= x < A.AsanRT.CELL_K + 8 \/
               A.AsanRT.in_shadow x ->
       lib.Lib.Frame.outside [(spv - 32, spv); (id, id + 38)] x) ->
    (* the run's own six loads *)
    lib.Lib.ExecF.rng RNG (A + 88) 8 -> lib.Lib.ExecF.rng RNG (A + 80) 8 -> lib.Lib.ExecF.rng RNG (A + 72) 8 ->
    lib.Lib.ExecF.rng RNG pa 2 -> lib.Lib.ExecF.rng RNG pp 8 -> lib.Lib.ExecF.rng RNG pn 8 ->
    (* the callee's regions (reac_identity_ingest_contract_F_on's rng premises, at this call's values) *)
    lib.Lib.ExecF.rng RNG (spv - 32) 32 ->
    lib.Lib.ExecF.rng RNG A.AsanRT.GOT_CELL_K 8 -> lib.Lib.ExecF.rng RNG A.AsanRT.CELL_K 8 ->
    lib.Lib.ExecF.rng RNG id 38 -> lib.Lib.ExecF.rng RNG (id / 8 + A.AsanRT.ASAN_K) ((id + 37) / 8 - id / 8 + 1) ->
    lib.Lib.ExecF.rng RNG p len ->
    lib.Lib.ExecF.rng RNG (p / 8 + A.AsanRT.ASAN_K) ((p + len - 1) / 8 - p / 8 + 1) ->
    lib.Lib.ExecF.evtF A.Img0.rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = lib.Lib.MState.MS
                 (lib.Lib.Frame.mkR (Z_to_bv 64 0x81734) sp gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (fst (lib.Prog.RcIdentModel.ING idb ad pb)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x81734) fc None m' (A.Reusable.YK11.seg_rom A.Img0.rsegs) /\
         lib.Lib.Frame.munch [(spv - 32, spv); (id, id + 38)] m m' /\ lib.Lib.Frame.wmono A.Img0.rsegs m m' /\
         lib.Lib.Frame.stk A.Img0.rsegs m' lo spv /\
         lib.Lib.Step.rw_cells A.Img0.rsegs m' id [lib.Lib.Cells.CB 38 (snd (lib.Prog.RcIdentModel.ING idb ad pb))])
      (lib.Lib.MState.MS
         (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
            t5 t6)
         F (Z_to_bv 64 0x81714) fc None m (A.Reusable.YK11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A id pa pp pn ad p len lo idb pb -> -> -> Hspv H16 Hid Hidm Had Hp Hlen
    R88 R80 R72 RPA RPP RPN HI Hpblen HPB HD ST Hlo32 Hidsp Hpsp HAC HAid HAp HOut
    Ra88 Ra80 Ra72 Rpa Rpp Rpn RFR RGOT RCELL RIDr RIDS RPr RPS.
  assert (NR : A.Prog.reac_identity_ingest_c.ingest_refused id p len = false).
  { unfold A.Prog.reac_identity_ingest_c.ingest_refused.
    replace (id =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite andb_false_r. reflexivity. }
  lib.Lib.StepF.step. lib.Lib.StepF.step. lib.Lib.StepF.step. lib.Lib.StepF.step.
  lib.Lib.StepF.step. lib.Lib.StepF.step. lib.Lib.StepF.step. lib.Lib.StepF.step.
  eapply lib.Lib.ExecF.evtF_cut.
  { eapply INGF with (id := id) (ad := ad) (p := p) (len := len) (idb := idb) (pb := pb) (lo := lo).
    - reflexivity.
    - apply A.Prog.Seg.RNIng.rn_zx16. lia.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - intros _. split; [exact Hidm | exact HI].
    - exact Hpblen.
    - intros _ _. exact HPB.
    - intros _ _ _. exact HD.
    - rewrite lib.Lib.MState.unsigned_lit by lia. exact ST.
    - rewrite lib.Lib.MState.unsigned_lit by lia.
      unfold A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME. lia.
    - intros _. rewrite lib.Lib.MState.unsigned_lit by lia.
      unfold A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME. exact Hidsp.
    - intros _ _. rewrite lib.Lib.MState.unsigned_lit by lia.
      unfold A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME. exact Hpsp.
    - exact HAC.
    - intros _. exact HAid.
    - intros _ _. exact HAp.
    - unfold A.Prog.reac_identity_ingest_c.reac_identity_ingest_W,
        A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME.
      rewrite lib.Lib.MState.unsigned_lit by lia. exact HOut.
    - rewrite lib.Lib.MState.unsigned_lit by lia.
      unfold A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME. exact RFR.
    - exact RGOT.
    - exact RCELL.
    - intros _. split; [exact RIDr | exact RIDS].
    - intros _ _. split; [exact RPr | exact RPS]. }
  intros ms' PO. unfold A.Prog.reac_identity_ingest_c.reac_identity_ingest_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI & STc & _ & HZ).
  subst ms'. specialize (HZ NR).
  unfold A.Prog.reac_identity_ingest_c.ingest_ret. rewrite NR.
  unfold A.Prog.reac_identity_ingest_c.reac_identity_ingest_W,
    A.Prog.reac_identity_ingest_c.REAC_IDENTITY_INGEST_FRAME in MU.
  rewrite lib.Lib.MState.unsigned_lit in MU, STc by lia.
  lazymatch goal with
  | |- lib.Lib.ExecF.evtF _ _ _ (lib.Lib.MState.MS _ _ (lib.Lib.MState.ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (lib.Lib.MState.ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k)
        by (symmetry; apply lib.Lib.MState.ret_pc_even; [ lia | reflexivity ])
  end.
  apply lib.Lib.ExecF.evtF_done. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact STc | exact HZ].
Qed.

End RNIngFon.

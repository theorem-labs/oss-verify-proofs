(* lib/A/ACtlG/R12.v -- GLUE for stage seg_R12 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:688) (an earlier version, blob c4edf0be7fe, not in this delivery)).  Written by a Theorem Labs lane (tree (internal path)).  rule 24: no function
   proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_R12 : forall POST (b : nat), CF POST (ix_cut C_A81734_at [Z.of_nat b]) ->
                                           CF POST (ix_cut C_A81708_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R12.  Segment R12 (Seg/R12.v seg_R12 :57): 0x81708 is the return of `jal reac_ctrl_identity_fragment` on
   the b = 6 arm; `li a1,1 ; beq a0,a1,81714` takes the branch (a0 = 1), then the shared ingest tail 0x81714 ..
   0x81730 calls reac_identity_ingest and returns to 0x81734.  Runs: R12F.r12_evt_F (the two instructions, the _F
   twin of r12_evt :33) and RNIngFon.rn_ing_evt_F_on (the tail and the call, the route (C) footprint twin of
   RNIng.rn_ing_evt :248; this lane's beside-file of Seg/RNIngF.v).

   THE PROOF
   G1  unfold the entry cut: ix_cut's index equation, C_A81708_at's body (ACtlCutP.v:1419-1437) at ixn 0 [b] = b;
       X81708 pins b = 6.
   G2' the turn-6 model facts, as Seg/R12.v:68-93 derives them: the fragment CLOSED the record
       (B3Rtm.a_rtm_close: fg_rf = 1), its outputs are address 0x1000 and length 17 (B3Rtm.a_rtm_close_vals), the
       ingest returns 1 (B3Rtm.a_rtm_ing6) and writes RID 7 (B3Rtm.a_RS_56 with fg_rf = 1); the payload is the 17
       bytes at fr + 2256 + 19 inside the closed fragment record RFG 7 (RNIng.rn_bsl_at), i.e. inside the frame,
       above the identity record, and RXS makes that record addressable.
   G3-G5 the shared part, lib/A/ACtlG/RNIng.v glue_rn_ing, at pc0 = 0x81708 with the pre-run R12F.r12_evt_F; its
       header says how the run is lifted (route (C): the _F_on carries reac_identity_ingest_contract_F_on as a
       premise, supplied by reac_identity_ingestF.reac_identity_ingest_F_holds_on, one SRr_fevt_hid over the whole
       run) and where every bound comes from.

   NO LIFT IS CITED: reac_identity_ingest_SRr_at is not used, because rn_ing_evt_F_on carries the callee's contract
   as its own premise; the caller obligations are that contract's premises, which rn_ing_evt_F_on restates and RNIng.v
   discharges.

   SECTION HYPOTHESES (exact text below)
   - LAWS : the core's AR laws (YCbq Section a0's hypothesis), as A5.v and ACtl.v:237.
   - none other: the kit's helpers (A.ACtlG.Kit.kit_wx, kit_segs_low) are cited inside RNIng.v's glue_rn_ing.
     (On the glue base eb89fed7fac, where Kit.v did not compile, they were placeholders with the kit's text:
     commits aa8ed9670fb / 18025d163cd.)

   CLOSURE: every project Require is qualified; no statement names a frame-route identifier.  SHADOWED NAMES:
   getr / FPState / RunCeil are the core's lib.Reusable.YK11 / lib.Reusable.YM05 (RNIng.v's header says why).

   BUILD STATE: on a working branch 1502cba0417 (no port_core_refused name in lib/A or lib/Reusable); the Require closure
   reaches no stand-in.  No Axiom, no Parameter, no unproved step. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* Every project module by its full path (ctrlgate rule (b), as RNIng.v). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R12F OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.RNIng.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.B3Rtm.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.RNIng.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:203 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* R12's pre-run is R12F.r12_evt_F, of the shape RNIng.rn_pre_run at 0x81708. *)
Lemma r12_pre : A.ACtlG.RNIng.rn_pre_run 0x81708.
Proof. exact A.Prog.Seg.R12F.r12_evt_F. Qed.

Section GlueR12.

(* ACtl.v's Section shape (ACtl.v:210-214), restricted to what this stage uses; the contexts are the core's. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:373, :377-378, :399, :400), verbatim. *)
Local Notation ix_cut := A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81708_at := (A.ACtlCutP.C_A81708_at B).
Local Notation C_A81734_at := (A.ACtlCutP.C_A81734_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:237). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* The kit's helpers are cited by name inside RNIng.v's glue_rn_ing. *)

Lemma glue_seg_R12 : forall POST (b : nat), CF POST (ix_cut C_A81734_at [Z.of_nat b]) -> CF POST (ix_cut C_A81708_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [b] (ix_cut, ACtlCut.v:232-234; C_A81708_at, ACtlCutP.v:1419-1437) *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A81708_at A.ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HPerm & HFRAC & HCOM & HX708).
  destruct HX708 as (Hbeq & Ha0 & HRFb & HRXS & HBa & HBp & HBn).
  subst b.
  destruct HRFb as ((_ & _ & _ & _ & HIDB & HFGB) & Hnz & Hr24 & _).
  (* G2': the model facts of turn 6 (Seg/R12.v:68-93) *)
  pose proof (A.Prog.Seg.B3Rtm.a_rtm_close (A.ACtlCut.c_in cx) Hnz) as Hcls.
  destruct (A.Prog.Seg.B3Rtm.a_rtm_close_vals (A.ACtlCut.c_in cx) Hnz) as (Hfa & Hpll).
  pose proof (A.Prog.Seg.B3Rtm.a_rtm_ing6 (A.ACtlCut.c_in cx) Hnz) as HING1.
  destruct (A.Prog.Seg.B3Rtm.a_RS_56 (A.ACtlCut.c_in cx) 6%nat (or_intror eq_refl) Hnz) as (EID & EFG).
  change (Z.of_nat 6) with 6 in EID, EFG, HBa, HBn.
  assert (Hrf : A.Prog.SlotModel.fg_rf (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) 6)
                  (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6) (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 6) = 1).
  { unfold A.Prog.SlotModel.fg_rf. rewrite Hcls. reflexivity. }
  pose proof (A.Prog.Seg.RNIng.rn_RS_len (A.ACtlCut.c_in cx) 7%nat) as (_ & LFG7).
  set (pb := A.Prog.SlotModel.f_pl (A.Prog.SlotModel.rt_n (A.ACtlCut.c_in cx) 6)
               (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6) (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 6)) in *.
  assert (EPB : pb = lib.Prog.RcFrag.bsl (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 7%nat) 19 17).
  { unfold pb, A.Prog.SlotModel.f_pl. rewrite <- EFG. rewrite Hpll. reflexivity. }
  (* the payload: 17 bytes at fr + 2256 + 19 inside the closed fragment record *)
  assert (HPB : lib.Lib.Mem.bytes_at segs mem3 (fr + 2256 + 19) pb).
  { rewrite EPB. apply A.Prog.Seg.RNIng.rn_bsl_at; [exact HFGB | lia | lia | rewrite LFG7; lia]. }
  assert (Hpblen : length pb = Z.to_nat 17).
  { rewrite EPB. apply A.Prog.Seg.RNIng.rn_bsl_len; [lia | lia | rewrite LFG7; lia]. }
  (* the payload is inside the fragment record, which RXS makes addressable *)
  pose proof HRXS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HA72).
  assert (HAp : A.AsanRT.addressable mem3 (fr + 2256 + 19) 17).
  { apply (A.AsanRTFacts.addressable_sub mem3 (fr + 2256) 72 19 17 HA72); lia. }
  (* the payload-length cell holds 17 *)
  assert (HBn' : lib.Lib.Mem.bytes_at segs mem3 (fr + 2496) (lib.Lib.Mem.le8 (Z_to_bv 64 17))).
  { unfold A.Prog.SlotModel.f_pll in Hpll. rewrite <- Hpll. exact HBn. }
  assert (HINGs : snd (lib.Prog.RcIdentModel.ING (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) 6%nat)
                         (lib.Prog.RcFrag.fg_addr (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6%nat)
                            (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 6)) pb) =
                  A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) (S 6%nat)).
  { rewrite EID. unfold A.Prog.SlotModel.fg_id. rewrite Hrf. reflexivity. }
  assert (Had : 0 <= lib.Prog.RcFrag.fg_addr (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6%nat)
                       (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 6) < 65536) by (rewrite Hfa; lia).
  assert (Hploc : (phi <= fr + 2256 + 19 /\ fr + 2256 + 19 + 17 <= phi + A.ACtlCutP.rnb cx 6%nat) \/
                  (fr + 2214 <= fr + 2256 + 19 /\ fr + 2256 + 19 + 17 <= fr + A.ACtlCutP.FRAME_BYTES)).
  { right. split; [lia | unfold A.ACtlCutP.FRAME_BYTES; lia]. }
  (* G3-G5: the shared part (RNIng.v), from 0x81708 *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x81708 regs3 mem3 md3) (POST cx)).
  exact (A.ACtlG.RNIng.glue_rn_ing B MT XM_LIB RLO RHI LAWS 0x81708 r12_pre
           POST 6%nat cx fr k ly3 S3 W3 regs3 mem3 md3 phi
           (lib.Prog.RcFrag.fg_addr (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) 6%nat)
              (A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) 6))
           (fr + 2256 + 19) 17 pb
           HX HB HJ HF HL Hk HPerm HFRAC HCOM Ha0 HRXS Hr24 HIDB HFGB HBa HBp HBn'
           Had ltac:(lia) Hpblen HPB HAp Hploc
           HING1 HINGs Hrt).
Qed.

End GlueR12.

Print Assumptions glue_seg_R12.

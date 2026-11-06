(* lib/A/ACtlG/R11.v -- GLUE for stage seg_R11 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v (at head lib/A/ACtl.v:686) (an earlier version, blob c4edf0be7fe, not in this delivery)).  Written by a Theorem Labs lane (tree (internal path)).  rule 24: no function
   proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_R11 : forall POST (b : nat), CF POST (ix_cut C_A81734_at [Z.of_nat b]) ->
                                           CF POST (ix_cut C_A816c4_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R11.  Segment R11 (Seg/R11.v seg_R11 :67): 0x816c4 is the return of `jal reac_ctrl_identity_reply` on the
   b = 3 / 4 arm; `li a1,1 ; beq a0,a1,81714` takes the branch (a0 = 1), then the shared ingest tail 0x81714 ..
   0x81730 calls reac_identity_ingest and returns to 0x81734.  Runs: R11F.r11_evt_F (the two instructions, the _F
   twin of r11_evt :34) and RNIngFon.rn_ing_evt_F_on (the tail and the call, the route (C) footprint twin of
   RNIng.rn_ing_evt :248; this lane's beside-file of Seg/RNIngF.v).

   THE PROOF
   G1  unfold the entry cut: ix_cut's index equation, C_A816c4_at's body (ACtlCutP.v:1397-1415) at ixn 0 [b] = b.
   G2' the turn-b model facts, as Seg/R11.v:80-117 derives them: ir is true for b = 3, 4 (B3Rtm.a_rtm_ir), the
       ingest returns 1 (B3Rtm.a_rtm_ing34) and writes RID (S b) (B3Rtm.a_RS_34 with ir), RFG (S b) = RFG b; the
       payload is the slice [38, 38 + r_pll g) of the 50 model bytes of the heap block phi (RNIng.rn_fr50_at /
       rn_bsl_at), so it lies in phi's block; the three argument cells are X816c4's (the reply address, phi + 38,
       ir_s - 13).
   G3-G5 the shared part, lib/A/ACtlG/RNIng.v glue_rn_ing, at pc0 = 0x816c4 with the pre-run R11F.r11_evt_F; its
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
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R11F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.RNIng OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.B3Rtm.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.Tac_rt2_b2.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.RNIng.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:203 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* R11's pre-run is R11F.r11_evt_F, of the shape RNIng.rn_pre_run at 0x816c4. *)
Lemma r11_pre : A.ACtlG.RNIng.rn_pre_run 0x816c4.
Proof. exact A.Prog.Seg.R11F.r11_evt_F. Qed.

Section GlueR11.

(* ACtl.v's Section shape (ACtl.v:210-214), restricted to what this stage uses; the contexts are the core's. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:373, :377-378, :398, :400), verbatim. *)
Local Notation ix_cut := A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A816c4_at := (A.ACtlCutP.C_A816c4_at B).
Local Notation C_A81734_at := (A.ACtlCutP.C_A81734_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:237). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* The kit's helpers are cited by name inside RNIng.v's glue_rn_ing. *)

Lemma glue_seg_R11 : forall POST (b : nat), CF POST (ix_cut C_A81734_at [Z.of_nat b]) -> CF POST (ix_cut C_A816c4_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [b] (ix_cut, ACtlCut.v:232-234; C_A816c4_at, ACtlCutP.v:1397-1415) *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A816c4_at A.ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HPerm & HFRAC & HCOM & HX816).
  destruct HX816 as (Hb34 & Ha0 & HRF & HRXS & Hc1 & Hc2 & Hc3).
  destruct HRF as (((_ & _ & _ & _ & HIDB & HFGB) & Hnz & Hr24 & HF50) & _).
  (* G2': the model facts of turn b = 3, 4 (Seg/R11.v:80-117) *)
  assert (HZb : Z.of_nat b = 3 \/ Z.of_nat b = 4) by (destruct Hb34 as [-> | ->]; [left | right]; reflexivity).
  pose proof (A.Prog.Seg.B3Rtm.a_rtm_ir (A.ACtlCut.c_in cx) (Z.of_nat b) HZb) as Hir.
  destruct (A.Prog.Seg.B3Rtm.a_RS_34 (A.ACtlCut.c_in cx) b Hb34 Hnz) as (EID & EFG).
  pose proof (A.Prog.Seg.B3Rtm.a_rtm_ing34 (A.ACtlCut.c_in cx) b Hb34) as HING1.
  destruct (A.Prog.Seg.Tac_rt2_b2.a_rtn (A.ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hnbrng & HLF).
  pose proof (lib.Prog.RcReply.ir_true _ _ Hir) as (_ & _ & _ & _ & Hs & _).
  set (g := A.Prog.SlotModel.rt_g (A.ACtlCut.c_in cx) (Z.of_nat b)) in *.
  assert (Hlen50 : (50 <= length (A.Prog.SlotModel.rt_F (A.ACtlCut.c_in cx) (Z.of_nat b)))%nat)
    by (rewrite HLF; lia).
  assert (HGlen : Z.of_nat (length g) = 50)
    by (unfold g, A.Prog.SlotModel.rt_g; rewrite A.Prog.SlotModel.fr50_length; reflexivity).
  assert (Hpll : 1 <= A.Prog.SlotModel.r_pll g <= 10) by (unfold A.Prog.SlotModel.r_pll; lia).
  assert (HG : lib.Lib.Mem.bytes_at A.Img0.rsegs mem3 phi g).
  { unfold g, A.Prog.SlotModel.rt_g. apply A.Prog.Seg.RNIng.rn_fr50_at; [exact HF50 | exact Hlen50]. }
  assert (HPB : lib.Lib.Mem.bytes_at segs mem3 (phi + 38) (A.Prog.SlotModel.r_pl g)).
  { unfold A.Prog.SlotModel.r_pl. apply A.Prog.Seg.RNIng.rn_bsl_at; [exact HG | lia | lia | rewrite HGlen; lia]. }
  assert (Hpblen : length (A.Prog.SlotModel.r_pl g) = Z.to_nat (A.Prog.SlotModel.r_pll g)).
  { unfold A.Prog.SlotModel.r_pl. apply A.Prog.Seg.RNIng.rn_bsl_len; [lia | lia | rewrite HGlen; lia]. }
  (* the three argument cells (X816c4) as bytes *)
  assert (HBa : lib.Lib.Mem.bytes_at segs mem3 (fr + 2448)
                  (lib.Lib.Mem.le2 (Z_to_bv 64 (A.Prog.SlotModel.r_addr g)))).
  { destruct Hc1 as ((_ & Hb1) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb1.
    rewrite app_nil_r in Hb1. rewrite A.Prog.Seg.R11.r11_reply_addr in Hb1. exact Hb1. }
  assert (HBp : lib.Lib.Mem.bytes_at segs mem3 (fr + 2464) (lib.Lib.Mem.le8 (Z_to_bv 64 (phi + 38)))).
  { destruct Hc2 as ((_ & Hb2) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb2.
    rewrite app_nil_r in Hb2. exact Hb2. }
  assert (HBn : lib.Lib.Mem.bytes_at segs mem3 (fr + 2496)
                  (lib.Lib.Mem.le8 (Z_to_bv 64 (A.Prog.SlotModel.r_pll g)))).
  { destruct Hc3 as ((_ & Hb3) & _). cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Hb3.
    rewrite app_nil_r in Hb3. unfold A.Prog.SlotModel.r_pll. exact Hb3. }
  (* the payload lies in phi's block, which the body makes addressable *)
  pose proof HCOM as (_ & _ & HHB & _).
  destruct HHB as (_ & HAphi).
  assert (Hsz : A.ACtlK.a_size (A.ACtlCutP.rnb cx b) = A.ACtlCutP.rnb cx b)
    by (unfold A.ACtlK.a_size, A.ACtlCutP.rnb in *; lia).
  rewrite Hsz in HAphi.
  assert (HAp : A.AsanRT.addressable mem3 (phi + 38) (A.Prog.SlotModel.r_pll g)).
  { apply (A.AsanRTFacts.addressable_sub mem3 phi (A.ACtlCutP.rnb cx b) 38 _ HAphi);
      unfold A.ACtlCutP.rnb; lia. }
  assert (HFGB' : A.ACtlCutP.FGBr cx fr (A.Prog.SlotModel.RFG (A.ACtlCut.c_in cx) (S b)) mem3)
    by (rewrite EFG; exact HFGB).
  assert (HINGs : snd (lib.Prog.RcIdentModel.ING (A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) b)
                         (A.Prog.SlotModel.r_addr g) (A.Prog.SlotModel.r_pl g)) =
                  A.Prog.SlotModel.RID (A.ACtlCut.c_in cx) (S b)).
  { rewrite EID. unfold A.Prog.SlotModel.rp_id. rewrite Hir. reflexivity. }
  assert (Hploc : (phi <= phi + 38 /\ phi + 38 + A.Prog.SlotModel.r_pll g <= phi + A.ACtlCutP.rnb cx b) \/
                  (fr + 2214 <= phi + 38 /\ phi + 38 + A.Prog.SlotModel.r_pll g <= fr + A.ACtlCutP.FRAME_BYTES)).
  { left. split; [lia | unfold A.ACtlCutP.rnb; lia]. }
  (* G3-G5: the shared part (RNIng.v), from 0x816c4 *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x816c4 regs3 mem3 md3) (POST cx)).
  exact (A.ACtlG.RNIng.glue_rn_ing B MT XM_LIB RLO RHI LAWS 0x816c4 r11_pre
           POST b cx fr k ly3 S3 W3 regs3 mem3 md3 phi (A.Prog.SlotModel.r_addr g) (phi + 38)
           (A.Prog.SlotModel.r_pll g) (A.Prog.SlotModel.r_pl g)
           HX HB HJ HF HL Hk HPerm HFRAC HCOM Ha0 HRXS Hr24 HIDB HFGB' HBa HBp HBn
           (A.Prog.Seg.R11.r11_addr_rng g) ltac:(lia) Hpblen HPB HAp Hploc
           HING1 HINGs Hrt).
Qed.

End GlueR11.

Print Assumptions glue_seg_R11.

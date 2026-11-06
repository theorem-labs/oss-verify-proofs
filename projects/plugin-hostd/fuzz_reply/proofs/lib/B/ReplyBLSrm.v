(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v, with its module paths and module names changed; 170 of its 243 lines of code are new or changed and 1154 lines of the source are left out. *)
(* The image-B relocation of
   lib/A/ReplyLSI.v's remove-arm plugs lsi_LS_rm_step :526 and lsi_LS_rm_cnl_pre :621
   (a working branch 1318828167d3), for B-TOPX-OWNERS rows 88 and 82 of
   the B top's fr_contract_top_x (e43cf0c7bef), at the B instance a Theorem Labs lane ruled (06:02Z, 06:5xZ):
     LSI B OM fr_CAP := fr_LS3cp B CR /\ fr_OUT OM /\ fr_ENT B /\ fr_CAP   (lib/B/ReplyLS3B_inst.v, row G-BLS3-port).
   proves no function (kind: invariant lemma).
   The Require header is lib/B/ReplyLS3B_inst.v's (row G-BLS3-port) plus ReplyB3LS3oGn, ReplyLS3B_inst, ReplyB3LS3Arms,
   ReplyKfMeterB and ReplyLSBSec.
   - Row 88 at B top_x's LS_rm_step text (lib/B/W_LLVMFuzzerTestOneInput_top_x.v, a Theorem Labs lane's restate), at any meter
     MT (KF-COUNT): the four conjuncts by lib/B/ReplyB3LS3p.v fr_LS3cp_rm_step_p, lib/B/ReplyB3LS3o.v
     fr_OUT_rm_step_p, lib/B/ReplyB3LS3e.v fr_ENT_rm_step_p and the fr_CAP slot's fr_CAP_rm_step; fr_OUT's and
     fr_CAP's twins take `0 <= cap2`, derived as A's plug does (lib/B/ReplyB3LS3oGn.v ou_sends_ge,
     lib/B/ReplyLS3B_inst.v lsi_drain_fin_ocap).  The text's mo_le premise goes to fr_LS3cp_rm_step_p, generic in the
     meter since a Theorem Labs lane's b3-kf.
   - Row 82 at B top_x's LS_rm_cnl_pre text (the TIED text), in two parts: lsi_LS_rm_cnl_pre_m, the text WITHOUT its
     final `mo_ok MT S ..` conjunct, at any meter MT, by lib/B/ReplyB3LS3Arms.v fr_LS3_rm_cnl_pre_p; and
     lsi_LS_rm_cnl_pre, the whole text at MT := ameter_triv, from it and `exact I`.  The whole text at a real meter
     needs the instance's count clause (B's fr_SEC).
   - F9 (KF-COUNT, the facts the counts need, as premises): lsi_LS_rm_step_f9 and lsi_LS_rm_cnl_pre_m_f9 are the same
     rows at F9's texts (a Theorem Labs lane's btlsi_LS_rm_step_f9 order; ReplyLSBSec.sec_LS_rm_cnl_pre's order), and
     lsi_LS_rm_cnl_pre_sec is row 82's whole F9 text at the KF meter MT_sec (lib/B/ReplyLSBSec.v), with the count clause
     fr_SEC as a premise until LSI carries it.  The names without _f9 stay at the window's texts, which have no F9.
   - Rows 84 and 86 (LS_rm_cshe_pre / LS_rm_sr_pre) are not here: their conclusion is a meter fact `mo_ok MT S ..` only,
     which the LS instance proves from its count clause.
   - Why the published LS_rm_cnl_pre text (mo_le only) cannot be proved at any LS, and so takes the TIED form: at
     MT := ameter_triv its mo_le is True (rm_cnl_mo_le_free), so its S is free, and cnl_room on a non-empty expected
     list fails once blocks_bytes S >= LIVE_MAX (cnl_room_cons_refute; lib/B/W_contract.v cnl_room :1925-1936).
   fr_CAP and fr_CAP_rm_step are the
   fr_CAP SLOT, as in A's lsi Section (A has no fr_CAP file either). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT drain_b_c send_line_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c
  RelayCap SlotReads SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBArms ReplyLSBTrPeak ReplyRINVB.
(* the arm files after ReplyLSBArms: the wr_* names are B's _write.v's (lib/B/ReplyB3Base.v's ruling) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBo ReplyLSBoRf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3Base ReplyB3LS3 ReplyB3LSCntL ReplyB3LS3c ReplyB3LS3Arms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_bx_defs W_LLVMFuzzerTestOneInput_gone_base.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cArms ReplyB3LS3o ReplyB3LS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3LS3p ReplyB3LS3c ReplyB3LS3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  ReplyB3LS3oGn ReplyLS3B_inst ReplyB3LS3Arms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB ReplyLSBSec.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the published LS_rm_cnl_pre text *)
Lemma rm_cnl_mo_le_free : forall (S0 S : astate) (c : Z), mo_le ameter_triv S0 S c.
Proof. intros. exact I. Qed.
Lemma cnl_room_cons_refute : forall MMAX bb T cap r rs, LIVE_MAX <= bb -> ~ cnl_room MMAX bb T cap (r :: rs).
Proof.
  intros MMAX bb T cap r rs Hb (_ & H & _).
  destruct (Z.eqb_spec (Z.of_nat (length T)) cap) as [E|E]; [|lia].
  unfold ListRep.grow_cap in H. rewrite <- E, Z.eqb_refl in H.
  destruct (Z.eqb_spec (Z.of_nat (length T)) 0); unfold AREC in H; lia.
Qed.

Section lsi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the meter (KF-COUNT, implicit): top_x's LS_rm_step text reads it *)
Context {MT : ameter_ops}.
Variable OM : Z.
Hypothesis HOM : ReplyLSBo.OUT_MAX4 <= OM.
Local Notation RINV := ReplyRINVB.fr_RINV.
(* the fr_CAP SLOT (A lib/A/ReplyLSI.v lsi Section): fr_CAP and its remove twin, with the premises of the rule's fr_OUT
   twin (lib/B/ReplyB3LS3o.v fr_OUT_rm_step_p), then fr_CAP at the rule's start *)
Variable fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Hypothesis fr_CAP_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  ReplyB3LS3.fr_LS3 B YCfn_cf.CALL_ROOM_B cx t m ly0 S0 -> ReplyLSBo.fr_OUT OM cx t m ly0 S0 -> fr_CAP cx t m ly0 S0 ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (CheckRep.set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= cap2 -> 0 <= t < OPS_MAX ->
  fr_CAP cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Local Notation LSx := (ReplyLS3B_inst.LSI B OM fr_CAP).

(* the parts of LSI the plugs read: lib/B/ReplyLS3B_inst.v lsi_parts (A lib/A/ReplyLSI.v :358-366) *)
Ltac lsi_open H :=
  destruct (ReplyLS3B_inst.lsi_parts _ _ _ _ _ _ _ _ H) as (?HP & ?H3c & ?H3 & ?HO & ?HE & ?HC); clear H.
Ltac lsi_goal := unfold ReplyLS3B_inst.LSI; refine (conj _ (conj _ (conj _ _))).

(* row 88: B top_x's LS_rm_step text (lib/B/W_LLVMFuzzerTestOneInput_top_x.v :781, a Theorem Labs lane's restate) at
   TfibB := B, LSx := LSI B OM fr_CAP, RINV := fr_RINV, any meter MT (A lsi_LS_rm_step, lib/A/ReplyLSI.v :526) *)
Lemma lsi_LS_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx cx t m ly0 S0 ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HL Hmo HRI Hat Hrr Hcnl Hcshe
    HF Hpos Hkeys Hpend Ht.
  lsi_open HL.
  assert (Hc0 : 0 <= lm_cap m) by exact (proj1 HO).
  assert (Hc2 : 0 <= cap2).
  { pose proof Hrr as Hrr'. unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_ok in Hrr'. cbv zeta in Hrr'. destruct Hrr' as (_ & Hs).
    match type of Hs with sl_sends ?mx ?c1 ?O1 ?cap1 ?Bs = _ =>
      assert (H1 : 0 <= cap1);
      [| pose proof (ReplyB3LS3oGn.ou_sends_ge mx Bs c1 O1 cap1 H1) as H2; rewrite Hs in H2; cbn [snd] in H2; lia] end.
    match goal with |- 0 <= (if ?b then _ else _) => destruct b; [|exact Hc0] end.
    unfold dr_fin. pose proof (ReplyLS3B_inst.lsi_drain_fin_ocap (dr_live (lm_c m) h) (lm_mx m)
      (Z.of_nat (length (lm_O m))) (lm_cap m) (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) h Hc0). lia. }
  lsi_goal.
  - exact (ReplyB3LS3p.fr_LS3cp_rm_step_p B YCfn_cf.CALL_ROOM_B cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds
      cc ev5 HP Hmo HRI Hat Hrr Hcnl Hcshe HF Hpos Hkeys Hpend).
  - eapply ReplyB3LS3o.fr_OUT_rm_step_p; eassumption.
  - eapply ReplyB3LS3e.fr_ENT_rm_step_p; eassumption.
  - eapply fr_CAP_rm_step; eassumption.
Qed.

(* row 88 at F9's text (KF-COUNT; a Theorem Labs lane's btlsi_LS_rm_step_f9 order): lsi_LS_rm_step's text plus
   `|re_U (rm_ent m j0)| <= APARTIAL` right after LSx, which it does not read *)
Lemma lsi_LS_rm_step_f9 : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx cx t m ly0 S0 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HL _.
  exact (lsi_LS_rm_step cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HL).
Qed.


(* row 82, the meter-free part: B top_x's LS_rm_cnl_pre text (lib/B/W_LLVMFuzzerTestOneInput_top_x.v :737) at
   TfibB := B, LSx := LSI B OM fr_CAP, RINV := fr_RINV, any meter MT, WITHOUT its final `/\ mo_ok MT S ..` conjunct
   (as a Theorem Labs lane's tx_LS_rm_cnl_pre_plug_m splits it); by lib/B/ReplyB3LS3Arms.v fr_LS3_rm_cnl_pre_p *)
Lemma lsi_LS_rm_cnl_pre_m : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)).
Proof.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 H HRI Hat Hrr Hmo Hpos Hfr. lsi_open H.
  exact (ReplyB3LS3Arms.fr_LS3_rm_cnl_pre_p B YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2
    cap2 out2 H3 HRI Hat Hrr Hmo Hpos Hfr).
Qed.

(* row 82, the meter-free part, at F9's text (KF-COUNT; ReplyLSBSec.sec_LS_rm_cnl_pre's order): lsi_LS_rm_cnl_pre_m's
   text plus `0 <= t < OPS_MAX` and `|re_U (rm_ent m j0)| <= APARTIAL` right after rm_rr_ok, which it does not read *)
Lemma lsi_LS_rm_cnl_pre_m_f9 : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)).
Proof.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 H HRI Hat Hrr _ _ Hmo Hpos Hfr.
  exact (lsi_LS_rm_cnl_pre_m cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 H HRI Hat Hrr Hmo Hpos Hfr).
Qed.

End lsi.

Section lsi_triv.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable OM : Z.
Local Notation RINV := ReplyRINVB.fr_RINV.
Variable fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Local Notation LSx := (ReplyLS3B_inst.LSI B OM fr_CAP).

(* row 82, the whole text: B top_x's LS_rm_cnl_pre text (:703) at the same names and MT := ameter_triv (A
   lsi_LS_rm_cnl_pre, lib/A/ReplyLSI.v :621): lsi_LS_rm_cnl_pre_m at ameter_triv, and the mo_ok half, True at
   ameter_triv.  At a real meter the mo_ok half comes from the instance's count clause (B's fr_SEC). *)
Lemma lsi_LS_rm_cnl_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le ameter_triv S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost ameter_triv) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok ameter_triv S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost ameter_triv) (hs_expected h1) (hs_held h1)).
Proof.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 H HRI Hat Hrr Hmo Hpos Hfr.
  split; [|exact I].
  exact (@lsi_LS_rm_cnl_pre_m rc B ameter_triv OM fr_CAP cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 H HRI Hat
    Hrr Hmo Hpos Hfr).
Qed.
End lsi_triv.

(* ================================================================== row 82 at the KF meter *)
Section lsi_sec.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable OM : Z.
Local Notation RINV := ReplyRINVB.fr_RINV.
Variable fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Local Notation LSx := (ReplyLS3B_inst.LSI B OM fr_CAP).
(* the KF meter of lib/B/ReplyLSBSec.v Section slots (s5-r1d): MT := MT_sec nsec KMAX, its count clause fr_SEC *)
Variable nsec : astate -> Z.
Variables KMAX KC : Z.
Hypothesis HKC : 240 <= KC.
Local Notation MT := (ReplyKfMeterB.MT_sec nsec KMAX).

(* row 82, the whole text at F9 and the KF meter: B top_x's LS_rm_cnl_pre text with F9's two premises after rm_rr_ok,
   at MT := MT_sec nsec KMAX.  LSI has no fr_SEC conjunct yet (a Theorem Labs lane adds it last), so the count clause at
   the pre-state is a premise, right after LSx; it becomes an LSI projection when LSI carries it.  The cnl_room half
   is lsi_LS_rm_cnl_pre_m_f9, the mo_ok half lib/B/ReplyLSBSec.v sec_LS_rm_cnl_pre. *)
Lemma lsi_LS_rm_cnl_pre_sec : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSx cx t m ly0 S0 -> ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)).
Proof.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 H HS HRI Hat Hrr Ht HU Hmo Hpos Hfr.
  split.
  - exact (@lsi_LS_rm_cnl_pre_m_f9 rc B MT OM fr_CAP cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 H HRI Hat Hrr
      Ht HU Hmo Hpos Hfr).
  - exact (ReplyLSBSec.sec_LS_rm_cnl_pre B nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 HS HRI
      Hat Hrr Ht HU Hmo).
Qed.
(* the same, with the count clause in the slot, as the B instance will carry it (s5-r1d / k3 14:44Z: LSI B OM
   (fr_CAP /\ fr_SEC), MT := MT_sec nsec KMAX): fr_SEC is LSI's last projection *)
Local Notation LSxS := (ReplyLS3B_inst.LSI B OM
  (fun cx t m ly S => fr_CAP cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S)).
Lemma lsi_LS_rm_cnl_pre_sec_slot : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSxS cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)).
Proof. intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 (HP & HO & HE & HC & HS); exact (lsi_LS_rm_cnl_pre_sec cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 (conj HP (conj HO (conj HE HC))) HS). Qed.
End lsi_sec.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core L5LazyA
  PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibSpecsXA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A CutBridgeA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import XKitXA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module WDXA.
Section W.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma astk_mono : forall (M : mem) sp scr scr', 0 <= scr' <= scr -> CHA.astk ar M sp scr -> CHA.astk ar M sp scr'.
Proof.
  intros M sp scr scr' Hs (K1 & K2 & K3 & K4 & K5 & K6). split; [exact K1|]. split; [lia|]. split; [exact K3|]. split; [exact K4|]. split; [|exact K6].
  intros i Hi. replace (sp - scr' + i) with (sp - scr + (scr - scr' + i)) by lia. apply K5. lia.
Qed.
Lemma ahpres_widen : forall LB FF (M M' : mem) sp scr scr' W, 0 <= scr' <= scr -> CHA.astk ar M sp scr ->
  CHA.ahpres L ar LB FF sp scr' W M M' -> CHA.ahpres L ar LB FF sp scr W M M'.
Proof.
  intros LB FF M M' sp scr scr' W Hs (K1 & K2 & K3 & K4 & K5 & K6) HP.
  assert (HP0 : CHA.ahpres L ar LB FF sp scr W M M) by (split; [intros a _; reflexivity | split; [exact K5 | intros a _ _ Hd; exact Hd]]).
  apply (CRB.ahpres_trans L ar LB LB LB FF sp scr scr' W W W M M M' HP0 HP); [apply incl_refl | apply incl_refl | exact Hs | clear - K3 K4; lia | clear - K4; lia | clear - K2; lia | |];
    intros w a Hw Hin; exists w; split; assumption.
Qed.
(* [comment removed for export] *)
Lemma cps_asan_widen : forall pc r sp scr scr' LB FF LK cr A dd (Pre Pre' : bvmap 5 word -> mem -> Prop) Post, 0 <= scr' <= scr ->
  (forall R M, Pre R M -> Pre' R M) ->
  PMSA.cps_asan L ar HI pc r sp scr' LB FF LK cr A dd Pre' Post -> PMSA.cps_asan L ar HI pc r sp scr LB FF LK cr A dd Pre Post.
Proof.
  intros pc r sp scr scr' LB FF LK cr A dd Pre Pre' Post Hs HPP H fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp Hstk Hroom Hffrs HPre Hcont.
  apply (H fx R M model K HH Hmo HK HFP Hra Hraok Hsp Htp (astk_mono M sp scr scr' Hs Hstk) Hroom Hffrs (HPP R M HPre)).
  intros fx' R' M' model' LB' cr' LBk W LK' A' HFP' HPost HRP HP. apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP' HPost HRP). exact (ahpres_widen LBk FF M M' sp scr scr' W Hs Hstk HP).
Qed.
(* [comment removed for export] *)
Section Vis.
Variable IC : PMLA.consts.
Variable enc_invA : PMSA.mem -> Z -> Z -> PMES.eghost -> Prop.
Variables scr scr' VIS_D : Z.
Variable benc : PMES.eghost -> Z.
Variable eroomA : PMES.eghost -> PMES.eev -> Prop.
Hypothesis SCR : 0 <= scr' <= scr.
Hypothesis SCR8 : scr mod 8 = 0 /\ scr' mod 8 = 0.
Lemma stksh_dn : forall (M : mem) sp, sp mod 32 = 0 -> PMSA.stksh ar M sp scr -> PMSA.stksh ar M sp scr'.
Proof.
  intros M sp Hsp H. unfold PMSA.stksh in *.
  assert (A : forall k, k mod 8 = 0 -> (sp - k) mod 8 = 0).
  { intros k Hk. apply Z.mod_divide in Hsp; [|lia]. destruct Hsp as [q Hq]. apply Z.mod_divide in Hk; [|lia]. destruct Hk as [t Ht]. rewrite Hq, Ht.
    replace (q * 32 - t * 8) with ((q * 4 - t) * 8) by lia. apply Z_mod_mult. }
  exact (PTA.stksh_mono ar M sp scr sp scr' H (A scr (proj1 SCR8)) (A scr' (proj2 SCR8)) ltac:(lia)).
Qed.
Lemma vtransA_widen : forall pc ev Args,
  PMXA.vtransA L ar HI IC enc_invA scr' VIS_D benc eroomA pc ev Args -> PMXA.vtransA L ar HI IC enc_invA scr VIS_D benc eroomA pc ev Args.
Proof.
  intros pc ev Args H LBo FF LK cr A sp r V S2 kx bx g. pose proof (H LBo FF LK cr A sp r V S2 kx bx g) as H1. cbv beta in H1.
  eapply (cps_asan_widen _ _ _ scr scr' _ _ _ _ _ _ _ _ _ SCR); [|exact H1].
  cbv beta. intros R M (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact (stksh_dn M sp P3 P4) | exact P5].
Qed.
Lemma vtranseA_widen : forall pc ev Args,
  PMXA.vtranseA L ar HI IC enc_invA scr' VIS_D benc eroomA pc ev Args -> PMXA.vtranseA L ar HI IC enc_invA scr VIS_D benc eroomA pc ev Args.
Proof.
  intros pc ev Args H LBo FF LK cr A sp r V S2 kx bx g. pose proof (H LBo FF LK cr A sp r V S2 kx bx g) as H1. cbv beta in H1.
  eapply (cps_asan_widen _ _ _ scr scr' _ _ _ _ _ _ _ _ _ SCR); [|exact H1].
  cbv beta. intros R M (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact (stksh_dn M sp P3 P4) | exact P5].
Qed.
End Vis.

(* [comment removed for export] *)
Section Bridges.
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.
Variables WD CL : Z.
Hypothesis WDLE : 0 <= PMESA.VIS_SCRA WD <= XKA.VIS.
Hypothesis WD8 : PMESA.VIS_SCRA WD mod 8 = 0.
Abbreviation EI := (PMESA.enc_invA L IC EC).
Abbreviation BE := (PMESA.benc L CL).
Abbreviation ER := (PMESA.eroomA CL).
Lemma vis8 : XKA.VIS mod 8 = 0 /\ PMESA.VIS_SCRA WD mod 8 = 0.
Proof. split; [reflexivity | exact WD8]. Qed.
Lemma visit_null_bridge : forall pc, PMESA.visit_null_specA L ar HI IC EC WD CL pc -> PMXA.visit_null_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ H). Qed.
Lemma visit_bool_bridge : forall pc, PMESA.visit_bool_specA L ar HI IC EC WD CL pc -> PMXA.visit_bool_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H b. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ (H b)). Qed.
Lemma visit_uint64_bridge : forall pc, PMESA.visit_uint64_specA L ar HI IC EC WD CL pc -> PMXA.visit_uint64_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H v. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ (H v)). Qed.
Lemma visit_int64_bridge : forall pc, PMESA.visit_int64_specA L ar HI IC EC WD CL pc -> PMXA.visit_int64_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H v. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ (H v)). Qed.
Lemma visit_double_bridge : forall pc, PMESA.visit_double_specA L ar HI IC EC WD CL pc -> PMXA.visit_double_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H. exact (vtranseA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ H). Qed.
Lemma visit_key_bridge : forall pc, PMESA.visit_key_specA L ar HI IC EC WD CL pc -> PMXA.visit_key_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H bs sv. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ (H bs sv)). Qed.
Lemma visit_string_bridge : forall pc, PMESA.visit_string_specA L ar HI IC EC WD CL pc -> PMXA.visit_string_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H tag bs sv Htag. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ (H tag bs sv Htag)). Qed.
Lemma visit_begin_object_bridge : forall pc, PMESA.visit_begin_object_specA L ar HI IC EC WD CL pc -> PMXA.visit_begin_object_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ H). Qed.
Lemma visit_begin_array_bridge : forall pc, PMESA.visit_begin_array_specA L ar HI IC EC WD CL pc -> PMXA.visit_begin_array_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ H). Qed.
Lemma visit_end_object_bridge : forall pc, PMESA.visit_end_object_specA L ar HI IC EC WD CL pc -> PMXA.visit_end_object_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ H). Qed.
Lemma visit_end_array_bridge : forall pc, PMESA.visit_end_array_specA L ar HI IC EC WD CL pc -> PMXA.visit_end_array_specXA L ar HI IC EI XKA.VIS XKA.VISD BE ER pc.
Proof. intros pc H. exact (vtransA_widen IC EI _ _ XKA.VISD BE ER WDLE vis8 pc _ _ H). Qed.
End Bridges.
(* [comment removed for export] *)
Lemma wdle_12800 : 0 <= PMESA.VIS_SCRA 12800 <= XKA.VIS.
Proof. vm_compute. split; discriminate. Qed.
Lemma wd8_12800 : PMESA.VIS_SCRA 12800 mod 8 = 0.
Proof. vm_compute. reflexivity. Qed.
End W.
End WDXA.

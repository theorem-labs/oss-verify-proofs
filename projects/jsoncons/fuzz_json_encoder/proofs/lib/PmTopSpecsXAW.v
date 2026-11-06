(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface L5Defs L5Core L5LazyA Pm4L5DefsA
  PmHeapIfaceA IcptIfaceA PmIcptIfaceA PmLibIfaceA PmLibIfaceAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibSpecsXA PmEncSpecsA PmLibSpecsW PmRef PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopSpecsXA HnKitXA PmTopSpecsXA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module TPSXAW.
Section SpecsXAW.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.            (* [comment removed for export] *)
(* [comment removed for export] *)
Variable enc_invA : PMSA.mem -> Z -> Z -> PMES.eghost -> Prop.
Variable VIS_SCRA : Z.
Variable VIS_D : Z.
Variable benc : PMES.eghost -> Z.
(* [comment removed for export] *)
Variable CL : Z.

Abbreviation cps_asan := (PMSA.cps_asan L ar HI).
Abbreviation mem := PMSA.mem.   Abbreviation pstate := PML.pstate.
Abbreviation a0 := PMSA.a0.   Abbreviation a1 := PMSA.a1.
Abbreviation fobj := PMSA.fobj.   Abbreviation stksh := (PMSA.stksh ar).   Abbreviation apart := PMLA.apart.
Abbreviation segs := (hl_segs L).
Abbreviation ENC_SIZE := PMES.ENC_SIZE.
Abbreviation kenc := (PMXA.kenc L).
Abbreviation lits_ok := (PMXA.lits_ok L IC).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition read_specXAW (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r Rr IS V E S2 ch gp sb bptr kx bx : Z) (rep : PML.srep) (g : PML.ls_state) (eg : PMES.eghost),
    let ps := PMSA.ps_init sb bptr in
    cps_asan pc r sp (PMXA.READXA_SCR VIS_SCRA) (PML.ps_blocks ps ++ LBo ++ PMES.g_lbv eg) FF LK cr A (PMXA.DPSOMEXA VIS_D)                            (* [comment removed for export] *)
      (fun R M => a0 R Rr /\ a1 R E /\ stksh M sp (PMXA.READXA_SCR VIS_SCRA) /\
                  PMSA.reader_preA L IC M LBo FF Rr IS V E ch rep gp 0 true ps /\ gp = PML.srep_data (IS + 80) rep /\
                  (forall b, In b (PML.srep_blocks rep) -> fst b <> ch) /\
                  Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\ PMLA.ls_ok segs IC g M /\ g <> PML.LS0 /\
                  enc_invA M V S2 eg /\ lits_ok M /\ PMXA.enc_sync ps eg /\                                                                         (* [comment removed for export] *)
                  0 <= kx /\ 0 <= bx /\ PMLA.pcredit_xA L cr ps (kx + kenc eg) (bx + benc eg) /\                                                  (* [comment removed for export] *)
                  sp mod 32 = 0 /\
                  fobj M FF V ENC_SIZE /\ fobj M FF S2 24 /\ apart V ENC_SIZE S2 24 /\                                                              (* [comment removed for export] *)
                  apart Rr 592 V ENC_SIZE /\ apart Rr 592 S2 24 /\ apart IS 272 V ENC_SIZE /\ apart IS 272 S2 24 /\ apart V ENC_SIZE E 16 /\ apart S2 24 E 16 /\
                  Forall (fun b => 0 <= b <= 255) (PML.srep_chars rep) /\                                                                          (* [comment removed for export] *)
                  PMXAW.wroom CL eg (PMR.K (PML.srep_chars rep)) (PMR.ALLOW (PML.srep_chars rep)))                                                 (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
          PMLA.source_at segs IC M' Rr ch /\ PMLA.parser_at segs IC M' (Rr + 320) ps' /\ PMLA.parser_sh M' ps' /\ PMLA.isrc_at segs IC M' IS rep gp' rdst' /\
          PMLA.ec_at segs IC M' E code /\ PMLA.ls_ok segs IC g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          enc_invA M' V S2 eg' /\ lits_ok M' /\                                                                                                  (* [comment removed for export] *)
          LB' = PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = lb_remove ch LBo /\                                                          (* [comment removed for export] *)
          PMLA.pcredit_xA L cr' ps' (kx + kenc eg') (bx + benc eg') /\ PML.wf_ps ps' /\                                                          (* [comment removed for export] *)
          W = TPSXA.WRDX L IC Rr IS E V S2).                                                                                                    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read_specXA_w_pre : forall pc, TPSXA.read_specXA L ar HI IC enc_invA VIS_SCRA VIS_D benc pc -> read_specXAW pc.
Proof.
  intros pc H LBo FF LK cr A sp r Rr IS V E S2 ch gp sb bptr kx bx rep g eg. cbv zeta.
  intros fx R M model K HRI HAM HK HFP H1 H2 H3 H4 H5 H6 H7 PRE CONT.
  apply (H LBo FF LK cr A sp r Rr IS V E S2 ch gp sb bptr kx bx rep g eg fx R M model K HRI HAM HK HFP H1 H2 H3 H4 H5 H6 H7); [ | exact CONT].
  cbv beta in PRE |- *. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition harness_chainXAW (pc aln : Z) (lng : bool) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r ptr : Z) (txt : list Z) (g : PML.ls_state),
    sp mod 32 = aln -> HNK.len_class lng txt ->
    Forall (fun b => 0 <= b <= 255) txt -> PMR.IND txt < 2 ^ 31 ->                                                                                   (* [comment removed for export] *)
    cps_asan pc r sp TPSXA.HARN_SCRXA LB FF LK cr A TPSXA.LIB_FRAMESXA
             (TPSXA.harness_preX L ar IC benc LB cr sp ptr txt g) (TPSXA.harness_postX L IC benc LB cr txt).
Definition harness_specXAW (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r ptr : Z) (txt : list Z) (g : PML.ls_state),
    Forall (fun b => 0 <= b <= 255) txt -> PMR.IND txt < 2 ^ 31 ->
    cps_asan pc r sp TPSXA.HARN_SCRXA LB FF LK cr A TPSXA.LIB_FRAMESXA
             (TPSXA.harness_preX L ar IC benc LB cr sp ptr txt g) (TPSXA.harness_postX L IC benc LB cr txt).
(* [comment removed for export] *)
Definition clokP : Prop :=
  forall txt : list Z, Z.of_nat (length txt) < 2 ^ 26 -> Forall (fun b => 0 <= b <= 255) txt -> PMR.IND txt < 2 ^ 31 -> PMR.IND txt + PMR.ALLOW txt <= CL.
(* [comment removed for export] *)
Lemma harness_chainXA_of_w : forall pc aln lng, TPSXA.harness_chainXA L ar HI IC benc pc aln lng ->
  harness_chainXAW pc aln lng.
Proof. intros pc aln lng H LB FF LK cr A sp r ptr txt g HA HL _ _. exact (H LB FF LK cr A sp r ptr txt g HA HL). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lib_specxAW (PHI : list byte -> Prop) (Lay : lib_layoutA) : Prop :=
  TPSXA.pm_layout_okxA L IC VIS_SCRA benc Lay -> PmLibIfaceAW.lib_call_okAW Lay ar SCFG HI (TPSXA.pm_staticsxA L IC) PHI.
Definition phiwP (PHI : list byte -> Prop) : Prop := forall payload : list byte, PHI payload -> PMR.IND (map bv_unsigned payload) < 2 ^ 31.

End SpecsXAW.
(* [comment removed for export] *)
Lemma txt_range_of_bytes : forall payload : list byte, Forall (fun b => 0 <= b <= 255) (map bv_unsigned payload).
Proof.   (* [comment removed for export] *)
  intros p. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256%Z in R. lia.
Qed.
End TPSXAW.

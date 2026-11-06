(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmLibSpecsA PmRef.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSWS.
Section SpecsXAW.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Abbreviation cps_asan := (PMSA.cps_asan L ar HI).
Abbreviation a0 := PMSA.a0.   Abbreviation a1 := PMSA.a1.   Abbreviation a2 := PMSA.a2.   Abbreviation a3 := PMSA.a3.
Abbreviation u8 := (PMSA.u8 L).   Abbreviation u32 := (PMSA.u32 L).   Abbreviation u64 := (PMSA.u64 L).
Abbreviation stksh := (PMSA.stksh ar).   Abbreviation fobj := PMSA.fobj.   Abbreviation ec_at := (PMSA.ec_at L IC).   Abbreviation ls_ok := (PMSA.ls_ok L IC).
Abbreviation str_at := (PMSA.str_at L).   Abbreviation ainfr := PMSA.ainfr.   Abbreviation bufcredA := (PMSA.bufcredA L).

(* [comment removed for export] *)
Definition sx32 (z : Z) : Z := let u := z mod 2 ^ 32 in if u <? 2 ^ 31 then u else u + 2 ^ 64 - 2 ^ 32.
(* [comment removed for export] *)
Definition atc_specXAW (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (P E cp c sp r : Z) (g : PML.ls_state),
    cps_asan pc r sp PMSA.ATC_SCR LB FF LK cr A 2
      (fun R M => a0 R P /\ a1 R cp /\ a2 R c /\ a3 R E /\ 0 <= cp < 2 ^ 64 /\ 0 <= c <= 255 /\ sp mod 32 = 0 /\ stksh M sp PMSA.ATC_SCR /\
                  u64 M (P + 96) (PMLA.VT_FUNC IC) /\ u64 M (P + 128) (P + 96) /\ u8 M (P + 211) 1 /\ fobj M FF P 272 /\ fobj M FF E 16 /\ PMLA.apart P 272 E 16 /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0)
      (fun R M R' M' LB' cr' LBk W => (exists v, a0 R' v) /\
                                      ((PMSA.is_hex c /\ ec_at M' E 0 /\ u8 M' (P + 211) 1 /\ ls_ok g M') \/ (~ PMSA.is_hex c /\ ec_at M' E 17 /\ u8 M' (P + 211) 0 /\ ls_ok PML.LS2 M')) /\
                                      LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(P + 211, 1); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES)] /\
                                      (forall d, PMR.hexval c = Some d -> exists v, a0 R' v /\ v = sx32 ((cp * 16 + d) mod 2 ^ 32))).      (* [comment removed for export] *)
Lemma atc_x_of_w : forall pc, atc_specXAW pc -> PMSA.append_to_codepoint_specA L ar HI IC pc.
Proof.
  intros pc H LB FF LK cr A P E cp c sp r g. intros fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  apply (H LB FF LK cr A P E cp c sp r g fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE).
  intros fx' R' M' model' LB' cr' LBk W LK' A' Hfp' (X1 & X2 & X3 & X4 & X5 & X6 & _). exact (Hcont fx' R' M' model' LB' cr' LBk W LK' A' Hfp' (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 X6)))))).
Qed.

(* [comment removed for export] *)
Definition convert_specXAW (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o cap p cpa cp sp r kx bx : Z) (s : list Z),
    cps_asan pc r sp PMSA.CONVERT_SCR LB FF LK cr A 0
      (fun R M => a0 R cpa /\ a1 R 1 /\ a2 R o /\ a3 R 0 /\
                  u32 M cpa cp /\ 0 <= cp < 2 ^ 32 /\ ainfr FF cpa 4 /\ ((cpa mod 8 = 0 /\ byte_at M (S cpa) 4) \/ byte_at M (S cpa) 0) /\
                  str_at M o (PML.SLong cap p s) /\ 24 <= cap /\ In (p, cap) LB /\ shadow_blk M p cap /\ fobj M FF o 24 /\
                  stksh M sp PMSA.CONVERT_SCR /\ Z.of_nat (length s) + 4 < 2 ^ 26 /\ bufcredA cr cap kx bx)
      (fun R M R' M' LB' cr' LBk W => exists cap' p' s',
          str_at M' o (PML.SLong cap' p' s') /\ shadow_blk M' p' cap' /\ cap <= cap' /\
          Z.of_nat (length s) <= Z.of_nat (length s') <= Z.of_nat (length s) + 4 /\
          LB' = (p', cap') :: lb_remove p LB /\ LBk = lb_remove p LB /\ W = [(o, 24)] /\ bufcredA cr' cap' kx bx /\
          s' = s ++ PMR.utf8_of cp).      (* [comment removed for export] *)
Lemma convert_x_of_w : forall pc, convert_specXAW pc -> PMSA.convert_specA L ar HI pc.
Proof.
  intros pc H LB FF LK cr A o cap p cpa cp sp r kx bx s. intros fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  apply (H LB FF LK cr A o cap p cpa cp sp r kx bx s fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE).
  intros fx' R' M' model' LB' cr' LBk W LK' A' Hfp' (cap' & p' & s' & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _).
  apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' Hfp'). exists cap', p', s'. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 X8))))))).
Qed.
End SpecsXAW.
End PSWS.

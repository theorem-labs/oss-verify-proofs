(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_018.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq ej DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_iface2.

(* [comment removed for export] *)
Module Fps_facts.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "eval"; "holds"; "SAlu"; "SLit"; "SVar"; "SPNot"; "sprop"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "modulo"; "sub"; "@Corelib.Init.Logic"; "and"; "eq"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "GEU65"; "sX"; "ENDA"; "big_facts"; "@Corelib.Lists.ListDef"; "Forall"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundV SymSoundI SymSoundM SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform StrBytes MuslWL ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFw DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Icpt_strnlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Section ClassFacts2.
Variable r : valuation.
Hypothesis HFs : Forall (holds r) str_facts.
Hypothesis H140 : ltac2:(tb__ "0|0|
S10S1Q40A1S2Vr;P8cA2S2Vr;P10A2A3").
Let z := bv_unsigned (rw r 16).
Lemma str_factsZ : ltac2:(tb__ "0|5|
SfSbSaS0Q40M0S2Vr;P10A2A2Z10A2S0G0S2Vr;P11A2A2M1A2SfSbG1ScZ2M2Z3eA2M3A2SfSbSaS0G0S2Vr;P14A2A2G1A2S0G0S2Vr;P13A2A2M4A2SfSbG4ScG2Z28A2A2SfSbSaS0G0S2Vr;P12A2A2G4A2ScG2Z2fA2A2SfSbS0G0S3Vr;S15A2A2G3A2S11A2A2A2A2A2A2").
Proof.
  pose proof HFs as HF. unfold str_facts in HF.
  apply Forall_cons_iff in HF as [F2 HF]. apply Forall_cons_iff in HF as [F3 HF]. apply Forall_cons_iff in HF as [F4 HF].
  apply Forall_cons_iff in HF as [F6 HF]. apply Forall_cons_iff in HF as [F7 HF].
  apply Forall_cons_iff in HF as [F11 HF]. apply Forall_cons_iff in HF as [F12 HF]. apply Forall_cons_iff in HF as [F13 HF]. apply Forall_cons_iff in HF as [F14 HF].
  apply Forall_cons_iff in HF as [F15 HF]. apply Forall_cons_iff in HF as [F16 HF]. apply Forall_cons_iff in HF as [F17 HF].
  apply Forall_cons_iff in HF as [F18 HF]. apply Forall_cons_iff in HF as [F19 HF]. apply Forall_cons_iff in HF as [F21 HF]. apply Forall_cons_iff in HF as [F22 HF].
  apply Forall_cons_iff in HF as [F23 HF]. apply Forall_cons_iff in HF as [F24 HF].
  pose proof (urange (rw r 16)). pose proof (urange (rw r 17)). pose proof (urange (rw r 18)). pose proof (urange (rw r 19)). pose proof (urange (rw r 20)).
  unfold vXB, vXL, vXO in *.
  cbn [holds branch_taken eval] in F2, F3, F4, F11, F12, F13, F14, F15, F16, F17, F22, F24. rewrite lit_unsigned in F22. change (131071 mod 2 ^ 64) with 131071 in F22.
  cbn [holds] in F7. rewrite two62_eq in F7. change (bv_unsigned (eval r (SLit (2 ^ 62)))) with ((2 ^ 62) mod 2 ^ 64) in F7. change ((2 ^ 62) mod 2 ^ 64) with (2 ^ 62) in F7.
  rewrite lit_unsigned in F15. rewrite lit_unsigned in F17. change ((2 ^ 47 - 64) mod 2 ^ 64) with (2 ^ 47 - 64) in F17.
  rewrite add_lit_val in F2. change (snorm 8) with 8 in F2.
  rewrite add_lit_val in F24. change (snorm 16) with 16 in F24.
  rewrite lit_unsigned in F3. change (8 mod 2 ^ 64) with 8 in F3.
  rewrite two62_eq, lit_unsigned in F4. change ((2 ^ 62) mod 2 ^ 64) with (2 ^ 62) in F4.
  rewrite add_val in F11. rewrite lit_unsigned in F14. change ((2 ^ 40) mod 2 ^ 64) with (2 ^ 40) in F14.
  rewrite add_val, lit_unsigned in F16. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47) in F16.
  assert (Ea : (bv_unsigned (rw r 16) + 8) mod 2 ^ 64 = bv_unsigned (rw r 16) + 8).
  { destruct (Z_lt_le_dec (bv_unsigned (rw r 16) + 8) (2 ^ 64)); [apply Z.mod_small; lia |].
    exfalso. replace (bv_unsigned (rw r 16) + 8) with ((bv_unsigned (rw r 16) + 8 - 2 ^ 64) + 1 * 2 ^ 64) in F2 by lia.
    rewrite Z_mod_plus_full, Z.mod_small in F2 by lia. lia. }
  rewrite Ea in F2.
  assert (Ex : (bv_unsigned (rw r 16) + 16) mod 2 ^ 64 = bv_unsigned (rw r 16) + 16).
  { destruct (Z_lt_le_dec (bv_unsigned (rw r 16) + 16) (2 ^ 64)); [apply Z.mod_small; lia |].
    exfalso. replace (bv_unsigned (rw r 16) + 16) with ((bv_unsigned (rw r 16) + 16 - 2 ^ 64) + 1 * 2 ^ 64) in F24 by lia.
    rewrite Z_mod_plus_full, Z.mod_small in F24 by lia. lia. }
  rewrite Ex in F24.
  assert (Eb : (bv_unsigned (rw r 20) + bv_unsigned (rw r 17)) mod 2 ^ 64 = bv_unsigned (rw r 20) + bv_unsigned (rw r 17)) by (apply Z.mod_small; lia).
  rewrite Eb in F11.
  assert (Ec : (bv_unsigned (rw r 18) + bv_unsigned (rw r 19)) mod 2 ^ 64 = bv_unsigned (rw r 18) + bv_unsigned (rw r 19)) by (apply Z.mod_small; lia).
  rewrite Ec in F16.
  repeat split; lia.
Qed.
Lemma U_sX' : ltac2:(tb__ "0|1|
S10S12S0Q40M0S3Vr;S15A2A2SaS0G0S2Vr;P12A2A2S0G0S2Vr;P14A2A2A2A3").
Proof.
  destruct str_factsZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 17)).
  unfold sX, vXB, vXO. apply (U_add2 r (SVar 18) (SVar 20)); [reflexivity | reflexivity | lia].
Qed.
Lemma U_z1' : ltac2:(tb__ "0|1|
S10S12S0Q40S3Vr;S5S13S7P8cA1S6Z1M0A1A3A2A2SaVz;G0A2A3").
Proof. pose proof (urange (rw r 16)). destruct str_factsZ as (Z1 & Z2 & _). apply (U_addc r (SVar 140) 1 z); [cbn [eval]; rewrite H140; reflexivity | lia | lia]. Qed.
Lemma U_ENDA' : ltac2:(tb__ "0|1|
S10S12S0Q40M0S3Vr;S16A2A2SaSaS0G0S2Vr;P12A2A2S0G0S2Vr;P14A2A2A2Vz;A2A3").
Proof.
  destruct str_factsZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 17)). pose proof (urange (rw r 16)).
  assert (A2 : bv_unsigned (eval r (SAlu ALU_ADD sX (SAlu ALU_ADD (SVar 140) (SLit 1)))) = bv_unsigned (rw r 18) + bv_unsigned (rw r 20) + (z + 1)).
  { apply (U_add2 r _ _ _ _ U_sX' U_z1'). lia. }
  unfold ENDA. rewrite (U_addc r _ (-1) _ A2); lia.
Qed.
Lemma post_facts_hold' : Forall (holds r) post_facts.
Proof.
  destruct str_factsZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 16)).
  unfold post_facts. constructor; [|constructor; [|constructor]]; cbn [holds].
  - change (eval r vXB) with (rw r 18). rewrite U_ENDA'. lia.
  - rewrite (U_addc r ENDA 1 _ U_ENDA') by lia. unfold vXB, vXL. pose proof (urange (rw r 19)).
    rewrite (U_add2 r (SVar 18) (SVar 19) (bv_unsigned (rw r 18)) (bv_unsigned (rw r 19)) eq_refl eq_refl) by lia. lia.
Qed.
Lemma U_m64' : ltac2:(tb__ "0|1|
S10S12S0Q40S3Vr;S5S13S7P8cA1S6N40A1A3A2A2SdSeVz;Z40M0A2ScZ2G0A2A2A3").
Proof. cbn [eval]. rewrite add_lit_val, H140. change (snorm (-64)) with (-64). reflexivity. Qed.
Lemma GEU65_S' : ltac2:(tb__ "0|0|
SbSaVz;Z1A2Z40A2S4Vr;S8S14A1A2F_;").
Proof.
  intros Hz. pose proof (urange (rw r 16)). unfold GEU65. cbn [holds branch_taken]. unfold bv_ltu. rewrite U_m64', (U_lit64 r 18446744073709551551) by lia.
  replace ((z - 64) mod 2 ^ 64) with (z - 64 + 2 ^ 64) by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small; lia).
  destruct (Z.ltb_spec 18446744073709551551 (z - 64 + 2 ^ 64)); [cbn; congruence | lia].
Qed.
Lemma GEU65_B' : ltac2:(tb__ "0|0|
SbZ41SaVz;Z1A2A2S4Vr;S14A2F_;").
Proof.
  intros Hz. destruct str_factsZ as (Z1 & Z2 & _). pose proof (urange (rw r 16)). unfold GEU65. cbn [holds branch_taken]. unfold bv_ltu. rewrite U_m64', (U_lit64 r 18446744073709551551) by lia.
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec 18446744073709551551 (z - 64)); [lia | reflexivity].
Qed.
Lemma big_facts_hold' : ltac2:(tb__ "0|0|
SbZ41SaVz;Z1A2A2S18S9S4Vr;A1S17A3F_;").
Proof.
  intros Hz. destruct str_factsZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 16)). pose proof (urange (rw r 20)).
  pose proof U_z1' as U141. change (SAlu ALU_ADD (SVar 140) (SLit 1)) with N1 in U141.
  unfold big_facts. apply Forall_app. split.
  2:{ apply (rip8_facts_hold r N1 (z + 1) U141); lia. }
  constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds]; unfold vXO, vXL.
  - pose proof (urange (rw r 19)). rewrite (U_add2 r (SVar 20) _ (bv_unsigned (rw r 20)) (z + 1) eq_refl U141) by lia. change (eval r (SVar 19)) with (rw r 19). lia.
  - rewrite U141. change (eval r (SVar 19)) with (rw r 19). lia.
  - rewrite U141, (U_lit64 r 1) by lia. lia.
Qed.
End ClassFacts2.
End Fps_facts.

(* [comment removed for export] *)
Module Start6Aux.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6Aux"; "pack16"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "Some"; "list"; "nil"; "option"; "app"; "length"; "nat"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "sprop_below"; "ss_next"; "ss_objs"; "SLit"; "ss_facts"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_X"; "axst"; "ax_S"; "ax_setS"; "mkLeafA"; "sym_runA"; "ax_base"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "move_obj_last"; "withX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "In"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "ECALL_MMAP"; "MEMSET"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates"; "F17_of"; "IP16_of"; "IPm_of"; "IPr_of"; "M16_of"; "R16_of"; "s16_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run0"; "F17_0"; "IP16_0"; "IPm_0"; "IPr_0"; "M16_0"; "R16_0"; "s16_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run1"; "F17_1"; "IP16_1"; "IPm_1"; "IPr_1"; "M16_1"; "R16_1"; "s16_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run2"; "F17_2"; "IP16_2"; "IPm_2"; "IPr_2"; "M16_2"; "R16_2"; "s16_2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run3"; "F17_3"; "IP16_3"; "IPm_3"; "IPr_3"; "M16_3"; "R16_3"; "s16_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run4"; "F17_4"; "IP16_4"; "IPm_4"; "IPr_4"; "M16_4"; "R16_4"; "s16_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run5"; "F17_5"; "IP16_5"; "IPm_5"; "IPr_5"; "M16_5"; "R16_5"; "s16_5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run6"; "F17_6"; "IP16_6"; "IPm_6"; "IPr_6"; "M16_6"; "R16_6"; "s16_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run7"; "F17_7"; "IP16_7"; "IPm_7"; "IPr_7"; "M16_7"; "R16_7"; "s16_7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "O_ss"; "R16c"; "classes16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pack16 (t : Z) (M : axst) (s : wsub) (R : list sobj) (IP : axst) (IPm : sstate) (IPr F : axst) : Prop := ltac2:(tb__ "0|b|
S1S0S9S7S19A1M0A1M1S1fS2bS30S31S23S22S22S22S24A1A1A1A1A1A1S4SeS34S8SeA1M2A3S27S75Vt;A1A1S3A5S6G0S4S19S1eVM;S2cA2S8S19A1M3A3A2A3S1S0S9S7S10A1M4A1S7cVM;S28Vs;A3S6G4VR;A2A3S1S0S5S7bVM;S28Vs;VR;S32S19S1bS21S2aA4A5S3A3S1S0S1bS7dVs;S28S78S29A1VM;VR;A5VIP;A3S1S0SfS14S1cVM;A1M5A1P51M6A3S1S0S7SdS11S11A2A1M7S1aVM;A1S25A3S1S0S18S26S1cVIP;A1M8U0A2VIPm;A3S1S0S5S79G8VIPm;A2S3A3S1S0G4S15VIPm;A1SaS10VR;S4S10S74Vt;A1S8S10A1A3A3A3S1S0ScSbS10S15G8A1A2U1aA3S1S0S1bS7aS1dS1dVIP;VIPm;A2S2dVIPm;VR;A2A2S17G5A1M9A2VIPr;A3S1S0S5S2eS12S13S14G8A1MaA1G9A3S3A3S1S0S5S2eS12S13G6A1G9A3S3A3S1S0G1S1fS2bUfa0S4SeS33G2A3VIPr;S3A5S6G0S4S19S1eVF;S2cA2G3A3A2A3S1S0SfGaP79A3S1S0G7S1aVIP;A1S25A3S1S0G7S1aVF;A1S25A3S0S11S20VF;A1S16S77A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Lemma pack16_0 : ltac2:(tb__ "0|0|
S2Z0S40S42S41S3dS3eS3fS3cA8").
Proof.
  unfold pack16. split; [exact run16_0|]. split; [exact fr16_0|]. split; [exact cc16_0|]. split; [exact IP16_0_eq|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [exact run17x_0|]. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma pack16_1 : ltac2:(tb__ "0|0|
S2Z1S47S49S48S44S45S46S43A8").
Proof.
  unfold pack16. split; [exact run16_1|]. split; [exact fr16_1|]. split; [exact cc16_1|]. split; [exact IP16_1_eq|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [exact run17x_1|]. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma pack16_2 : ltac2:(tb__ "0|0|
S2Z2S4eS50S4fS4bS4cS4dS4aA8").
Proof.
  unfold pack16. split; [exact run16_2|]. split; [exact fr16_2|]. split; [exact cc16_2|]. split; [exact IP16_2_eq|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [exact run17x_2|]. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma pack16_3 : ltac2:(tb__ "0|0|
S2Z3S55S57S56S52S53S54S51A8").
Proof.
  unfold pack16. split; [exact run16_3|]. split; [exact fr16_3|]. split; [exact cc16_3|]. split; [exact IP16_3_eq|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [exact run17x_3|]. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma pack16_4 : ltac2:(tb__ "0|0|
S2Z4S5cS5eS5dS59S5aS5bS58A8").
Proof.
  unfold pack16. split; [exact run16_4|]. split; [exact fr16_4|]. split; [exact cc16_4|]. split; [exact IP16_4_eq|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [exact run17x_4|]. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma pack16_5 : ltac2:(tb__ "0|0|
S2Z5S63S65S64S60S61S62S5fA8").
Proof.
  unfold pack16. split; [exact run16_5|]. split; [exact fr16_5|]. split; [exact cc16_5|]. split; [exact IP16_5_eq|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [exact run17x_5|]. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma pack16_6 : ltac2:(tb__ "0|0|
S2Z6S6aS6cS6bS67S68S69S66A8").
Proof.
  unfold pack16. split; [exact run16_6|]. split; [exact fr16_6|]. split; [exact cc16_6|]. split; [exact IP16_6_eq|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [exact run17x_6|]. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma pack16_7 : ltac2:(tb__ "0|0|
S2Z7S71S73S72S6eS6fS70S6dA8").
Proof.
  unfold pack16. split; [exact run16_7|]. split; [exact fr16_7|]. split; [exact cc16_7|]. split; [exact IP16_7_eq|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [exact run17x_7|]. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma cls16 : ltac2:(tb__ "0|0|
SeS2fSeR1S76A3S2R2S39R2A1S3bR2A1S3aR2A1S36R2A1S37R2A1S38R2A1S35R2A1A8F_;Ft;").
Proof.
  intros t Ht. destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
    [exact pack16_0 | exact pack16_1 | exact pack16_2 | exact pack16_3 | exact pack16_4 | exact pack16_5 | exact pack16_6 | exact pack16_7].
Qed.
End Start6Aux.

(* [comment removed for export] *)
Module Start6bStates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "app"; "length"; "nat"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "mkLeafA"; "ax_S"; "ax_X"; "ax_base"; "@Corelib.Init.Decimal"; "D0"; "D8"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sobj"; "sprop"; "SPUle"; "SVar"; "ss_objs"; "SPAlign"; "ss_next"; "ss_pc"; "ss_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates"; "E18"; "MALLOC_ENTRY"; "SPIN17"; "S_s17ok"; "F17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "SPIN_MMAPORDIE"; "fail_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates"; "E_s17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@Stdlib.ZArith.BinInt.Z"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition MALLOC_ENTRY : Z := 0xd5b00.

Definition F17 : list sprop := ltac2:(tb__ "0|2|
S0S1bS1fP53M0ZcA2S0S1bS1cS18Z646000A1S1dG0A1M1A2S0S1bS1cG1S18S34Z7fffff800000Zb09000A2A1A2S1S1bA1A3A3A3").
Definition S_s17ok : axst := ltac2:(tb__ "0|2|
S30S31S27S32S11S2aA1M0S1dP53M1A1S6S1aS1eG0A1S0S1aS33G1Zb09000A2S1S1aA1A3A3P54A4A2A1").
Definition run17b__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS17S2cS2dS15S14S14S14S16A1A1A1A1A1A1S0SaS24S1SaA1A3S26S2A5").
Local Strategy expand [run17b__R].
Definition E18 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => (leaf1 S_s17ok (ro1__))) run17b__R).
Lemma run17b : ltac2:(tb__ "0|1|
ScS5S3SeA1M0A1SfS17S2cS2dS15S14S14S14S16A1A1A1A1A1A1S0SaS24S1SaA1A3S26S2A5S4G0S0SeS10S23S2bA2S1SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17b__R <: run17b__R = Some [mkLeafA E18 RsCut]). Qed.
Definition run17_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS17U12cS0SaS28S1SaA1A3S29S2aA1S2A5").
Local Strategy expand [run17_fail__R].
Definition SPIN17 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => (leaf1 (fail_state E_s17) (ro2__))) run17_fail__R).
Lemma run17_fail : ltac2:(tb__ "0|1|
ScS5S3SeA1M0A1SfS17U12cS0SaS28S1SaA1A3S29S2aA1S2A5S4G0S0SeS10S25S2bA2S1SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17_fail__R <: run17_fail__R = Some [mkLeafA SPIN17 RsCut]). Qed.
Lemma spin17 : ltac2:(tb__ "0|1|
ScS5S3SeA1M0A1SfS17U2S0SaS28S1SaA1A3S25S2A5S4G0S0SeS10S25S2bA2S1SeA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E18_at : ltac2:(tb__ "0|2|
SdScSaS21S11S23A1M0A1S24A3SdScSbS20G0A1P54A3SdScS3S9S19S19A2M1A1S12S23A1S1G1A1A3SdScS19S13S23A1S18S2fA1A3SdScS8S7S1aS1eG0A1A2U1aA3ScS19S2eS19UaS22G0A1S18Z0A1A4S18Z28A1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6bStates.

(* [comment removed for export] *)
Module DrvR_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "true"; "option"; "nil"; "bool"; "Some"; "pair"; "list"; "prod"; "andb"; "false"; "app"; "None"; "length"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SVar"; "cell"; "sstate"; "SPUle"; "ss_objs"; "DUnknown"; "mkObj"; "ss_next"; "ss_pc"; "swf"; "ss_facts"; "SPAlign"; "reg_sv"; "ss_regs"; "SPBranch"; "mkSS"; "sprop_eqb"; "FcsrFrm0"; "SAlu"; "mkCell"; "sv_eqb"; "SExt"; "SPEq"; "SPNot"; "odefault"; "SAluW"; "SLBytes"; "SMd"; "SMdW"; "c_off"; "c_val"; "c_width"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_resv"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "sym_runA"; "leafA"; "ax_setS"; "la_state"; "entailsA"; "sobj_eqb"; "ax_X"; "axwf"; "mkLeafA"; "la_reason"; "mkAX"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states"; "CUTS_R"; "RS"; "ibS"; "pcs_of"; "vWant"; "X_R"; "T_after"; "O_rdsC"; "obind"; "vRes1"; "vResH"; "R1c"; "ob_shape0b"; "G_cut"; "R0c"; "hcZ"; "irds"; "PreC"; "two_cap"; "C_s0"; "RD0"; "RD1"; "nthA"; "objs_R"; "optS"; "E_rd0"; "E_rd1"; "E_s0"; "O_rdsL"; "R_s0"; "S0f"; "errV"; "hdr_cell"; "rd_w1"; "rd_w2"; "s_s0"; "vRes0"; "C_cp1"; "C_czh"; "C_czk"; "C_mc"; "C_rd0"; "C_rd1"; "FUEL_R"; "G_mok"; "Hc1"; "LV_R0"; "LV_R1"; "LV_S0"; "PreM"; "Q1"; "R_mG"; "cp_s1"; "cz_rsd"; "cz_splits"; "errL"; "errL_okb"; "hcD"; "objs37"; "rds_cellsL"; "s_mG"; "vN'"; "B1u"; "Bg"; "C_f"; "E_cl0"; "E_cl1"; "E_clZ"; "E_mcf"; "G_mnull"; "Hc0"; "HcZ"; "Lref"; "LtrR"; "PreCH"; "PreMC"; "R_cp1"; "R_czh"; "R_czk"; "R_f"; "R_mc"; "R_rd0"; "R_rd1"; "T_cp1"; "T_czh"; "T_czk"; "T_f"; "T_mc"; "T_rd0k"; "T_rd0k'"; "T_rd1k"; "T_rd1k'"; "T_s0h"; "T_s0h'"; "T_s0k"; "T_s0k'"; "bk_okb"; "bkpipe"; "bkz_okb"; "bkzpipe"; "cp_cv"; "errV_okb"; "lenG"; "mc_rtc"; "q_okb"; "qpipe"; "qz_okb"; "qzpipe"; "rd_rs"; "rd_rtc"; "rd_s1"; "s_cp1"; "s_czh"; "s_czk"; "s_f"; "s_mc"; "s_rd0"; "s_rd1"; "BZhu"; "BZku"; "E_m"; "E_mG"; "E_mZ"; "E_mZG"; "F1"; "F2"; "LV_C1"; "LV_Gnull"; "LV_Gok"; "LV_S0h"; "LV_S0k"; "LV_T0k"; "LV_T1k"; "LV_Zh"; "LV_Zk"; "LV_c0"; "LV_c1"; "LV_cZ"; "LV_f"; "LV_h0"; "LV_h1"; "LV_hZ"; "LV_mc"; "LV_oom"; "LV_ov1"; "LV_ref"; "LV_sh0"; "LV_sh1"; "LV_shZ"; "Lb1"; "LbZh"; "LbZk"; "Lc0k"; "Lcl0"; "Lcl1"; "Lcp1"; "Lg1"; "LgZh"; "Loom"; "Lov1"; "Lr1"; "Ls0h"; "Ls0k"; "Lsh0"; "Lsh1"; "LshZ"; "Ltr"; "PostsC"; "QZh"; "QZhf"; "QZk"; "QZkf"; "XF_bka"; "XF_bkb"; "XF_bkza"; "XF_bkzb"; "XF_q"; "XF_qz"; "ax_of"; "bk2"; "bkz2"; "cp_rsd"; "cp_rss"; "cp_splits"; "cp_w1"; "cp_w2"; "czh_h1"; "czh_h2"; "czh_h3"; "errL0"; "facts_R"; "facts_R1"; "facts_Rb"; "has_tpfact"; "ierrL"; "ierrV"; "inew"; "len1'"; "mc_b1"; "mc_w1"; "mc_w2"; "mch_rtc"; "q2"; "qz2"; "rd_cv"; "rd_rsZ"; "rd_site"; "rdsb"; "s_RDa"; "s_RDb"; "vJ7"; "E_f"; "E_mc"; "F_bk1"; "Lg"; "O_bufR"; "O_dstC";
"O_dstL"; "O_dstZ"; "O_errnoV"; "PostsCH"; "PostsM"; "PostsMC"; "RD_cut"; "R_cut"; "XF_f"; "X_G"; "clen_x"; "cp_b0"; "cp_b1"; "cp_b2"; "cp_okb"; "cp_site"; "cz_b1"; "cz_okb"; "cz_site"; "czh_okb"; "czh_site"; "errL0_okb"; "errV0"; "errV0_okb"; "facts_G"; "facts_RD"; "mc_cv"; "mc_kfacts"; "mc_site"; "objs38"; "q1"; "q3"; "q4"; "rd_siteZ"; "regs_G"; "regs_R"; "regs_RD"; "s_G"; "s_GZ"; "s_R0"; "s_T"; "s_bk1"; "s_bkG"; "s_bkZh"; "s_bkZk"; "selb"; "selbZ"; "self"; "selq"; "selqZ"; "setregA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXRebase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "set_objs"; "RsFuel"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vB"; "vCap"; "vLen"; "vTP"; "locate"; "DEEP"; "sp0"; "vTOPv"; "PreF"; "fregs_T"; "spM"; "vA1"; "ATOPHI"; "IMGHI"; "PostF"; "X_rds"; "vTID"; "O_errno"; "O_rds"; "S_T"; "arg1_facts"; "top_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "add"; "O_rtc2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "combine"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@Corelib.Lists.ListDef"; "map"; "skipn"; "seq"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read"; "Pre_rd"; "Posts_rd"; "P_rd"; "hc"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "X_R0"; "CAP0"; "R_head"; "objs_R0"; "S_R0"; "argsX_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "malloc_stub"; "free_stub"; "tr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_malloc_null"; "L_malloc_ok"; "Pre_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "fw_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states.RAddr"; "rd_cut"; "close_entry"; "t_oom2"; "t_overrun"; "t_ref"; "t_short"; "t_rderr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.MCAddr"; "mc_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.RDAddr"; "rd_entry"; "rd_ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "aluop"; "mulop"; "ALU_SLL"; "ALU_SUB"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "FERR"; "exit_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface"; "fp_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "P_icpt"; "O_real";
"O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "X_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvErrno"; "errC"; "errC_okb"; "errR_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr"; "O_real"; "O_rtc3"; "P_icpt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs"; "P_icpt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform DrvGlueA SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysStepA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFpIface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvErrno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module RAddr.
  Definition grow_head : Z := 0x8c424.
  Definition malloc_site : Z := 0x8c434.
  Definition memcpy_site : Z := 0x8c40c.
  Definition memcpy_grow : Z := 0x8c450.
  Definition free_site : Z := 0x8c458.
  Definition read_prep : Z := 0x8c45c.
  Definition rd_cut : Z := 0x8c46c.
  Definition read_site : Z := 0x8c474.
  Definition read_ret : Z := 0x8c478.
  Definition close_ret : Z := 0x8c48c.
  Definition t_ref : Z := 0x8c5d8.
  Definition t_oom2 : Z := 0x8c5f8.
  Definition t_rderr : Z := 0x8c5bc.
  Definition t_short : Z := 0x8c548.
  Definition t_overrun : Z := 0x8c564.
  Definition close_entry : Z := 0xe3598.
End RAddr.
Import RAddr.

Definition CUTS_R : list Z := ltac2:(tb__ "0|0|
S0S4fS1a6S0S4fS1a7S0S4fS1b8S0S4fS1b9S0S4fS1b2S0S4fS1baS0S4fS1c4S0S4fS1c6S0S4fS1b0S0S4fS19bS0S4fS1b1S0S4fS1a8S0S4fS1b5S0S4fS1b3S0S4fS1b7S0S4fS1b6S0S4fS1b4S4S4fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition runR (fuel : nat) (A : axst) : list leafA := ltac2:(tb__ "0|1|
S3S8S45A1M0A1G0Lx;S44S52Vfuel;S54VA;S2A5G0R1Ll;S4S45A1X3x2").
Definition nthA (d : axst) (l : list leafA) (i : nat) : axst := ltac2:(tb__ "0|0|
S47S18fS45Vi;Vl;S4cVd;S168A2A4A1").
Definition optS (d : axst) (x : option sstate) : axst := ltac2:(tb__ "0|0|
S3S17A1S42Lx;Vx;S17S46Vd;R1A2LS';Vd;X3x2").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition ax_of (o : option axst) (d : axst) : axst := match o with Some a => a | None => d end.
Definition pcs_of (l : list leafA) : list (Z * stop_reason) := ltac2:(tb__ "0|0|
S18bS45S9S4fS165A2S45S7S4fS165S1dS43S47R1A1A1A1S4dR1A1A4LL;Vl;A4").

Definition O_errnoV : sobj := ltac2:(tb__ "0|0|
S1bS16dS12Na4A1S12Na0A1S4S16A1S1aA5").
Definition ob_shape0b (o : sobj) (b lo hi : sv) : bool := ltac2:(tb__ "0|2|
SaSaSaSaS29S35Vo;A1Vb;A2S29S39Vo;A1Vlo;A2A2S29S38Vo;A1Vhi;A2A2S8S16A1M0S5Lx;S36Vo;A1S2S16G0SbLl;Lc;X8x2A2S2dS5Lx;S37Vo;A1S2SbSbS50SbLl;M1G1S4fS11S8S9S4fS4fA2A1S8S3fA1SbLtmpl;Lflds;Lcnt;Lesz;X2dx6A2").

Definition ierrL (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S12Z0A1S12S1a2S1a5Za4A2A1A3").
Definition ierrV (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S16dS12Na4A1A3").

Definition errV0 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1S116VE;A1S12fA3A2").
Definition errL0 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1S117VE;A1S17bA3A2").
Definition errV (E : axst) : axst := errV0 (errC E).
Definition errL (E : axst) : axst := errR (errL0 E).
Definition has_tpfact (E : axst) : bool := ltac2:(tb__ "0|0|
S188S14S25S2bS16dS12S1a5A1A2A1S1fS43VE;A1A1A3").
Definition errV0_okb (E : axst) : bool := ltac2:(tb__ "0|1|
SaSaS3S13A1S5Lx;S185S13S19S43VE;A1M0A1S116VE;A1A3S13S60R1S12Z0A1S12S1a2S1a5Za4A2A1S12S1a2S1a5Za0A2A1A4Lo;SbX3x2S189G0S43S143VE;A1A1A2A2S115VE;A1A2").
Definition errV_okb (E : axst) : bool := ltac2:(tb__ "0|0|
SaS1ccVE;A1S144S1cbVE;A1A1A2").
Definition errL0_okb (E : axst) : bool := ltac2:(tb__ "0|1|
SaSaS3S13A1S5Lx;S185S13S19S43VE;A1M0A1S117VE;A1A3S13S60R1S16dS12Na4A1S12Na0A1A4Lo;SbX3x2S189G0S43S111VE;A1A1A2A2S115VE;A1A2").
Definition errL_okb (E : axst) : bool := ltac2:(tb__ "0|0|
SaS142VE;A1S1cdS111VE;A1A1A2").

Definition RS : Z := RD_STAGE.
Definition rdsb : sv := add (SLit RS) (SLit 0).
Definition O_rdsC (n : sv) (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS123S12Z0A1Vn;Vcs;S1aA5").
Definition O_rdsR (n : sv) : sobj := ltac2:(tb__ "0|0|
S1bS12Z0A1S180S12S55A1Vn;A2S12S1a0S55Z10000A2A1S4S16A1S1aA5").
Definition O_rdsL (n : sv) (cs : list cell) : sobj := ltac2:(tb__ "0|1|
S1bS12Z0A1S12S55A1M0S180G0Vn;A2Vcs;S1aA5").

Definition O_rdsP (n : sv) (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS12S55A1S12Z0A1Vn;Vcs;S1aA5").
Definition irds (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S12Z0A1S12S55A1A3").
Definition irdsC (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S123S12Z0A1A3").

Definition O_bufR (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS16aS12Z0A1S16bVcs;S1aA5").
Definition hdr_cell : cell := mkCell (SLit 0) 4 vH.
Definition objs_R (cs : list cell) : list sobj := Eval vm_compute in (firstn 9 objs_R0 ++ [O_bufR cs] ++ skipn 10 objs_R0).
Lemma objs_R_shape : ltac2:(tb__ "0|0|
S8S16A1S40S8S13A1S6bR1A1ScS13S18eS13U9S19cA3ScS13S0S13S12bR1A1S4S13A1A3S18cS13UaS19cA3A3A3A3Fcs;"). Proof. reflexivity. Qed.
Definition X_R : list (sv * sv) := ltac2:(tb__ "0|2|
ScS9S11S11A2M0S0G0S7S11S11S12Z14d40A1S12Z80M1A1A4S0G0S7S11S11S180S170S12S1a3S1a0S16fG1A2A1A1A2S12S16fA1A4S0G0S7S11S11S16aS16bA4S0G0S179S4G0A1A3A3A3A3S1caA3").

Definition facts_Rb : list sprop := ltac2:(tb__ "0|6|
ScS14S0S14S20P1Z4M0A2S0S14S18S12Z7fff80000000A1S170A2S0S14S18S170S12S1a2S1a1Z2M1Z2fA2Ze0A2A1A2S0S14S2bS16dS12S1a5A1A2S0S14S20P18Z3M2A2S0S14S20P28M3G0A2S0S14S20G3G2A2S0S14S18S12Z1000A1S16aA2S0S14S18S180S16aS16bA2M4S12S176A1M5A2S0S14S18S16aG5A2S0S14S18S12S177A1S16aA2S0S14S18G4S171A2S0S14S18S16aS171A2S0S14S2cS23S1bdS16aS12Z0A1A3A1S0S14S18S12Z10000A1S16bA2S0S14S18S16bS12S1a1G1Z1aA2A1A2S0S14S20P29ZcA2S0S14S18S12Z1A1S17aA2S0S14S18S17aS12Z3fffffA1A2S4S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS14S17fScS14S17eS19eA3A3A3").
Definition facts_R : list sprop := ltac2:(tb__ "0|0|
ScS14S0S14S18S180S16cS12Z1A1A2S16bA2S0S14S18S16cS16bA2S4S14A1A3A3S114A3").

Definition facts_R0f : list sprop := ltac2:(tb__ "0|0|
S0S14S18S16cS12Z3A1A2S112A3").
Definition facts_R1 : list sprop := ltac2:(tb__ "0|0|
S0S14S18S12Z4A1S16cA2S112A3").

Definition vJ7 : sv := SVar 66.
Definition regs_R : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11S15P3cA1S0S11S174S0S11S12Z10800A1S0S11S16dS0S11S15P3dA1S0S11S15P3eA1S0S11S15P3fA1S0S11S12Z2A1S0S11S16aS0S11S15P64A1S0S11S15P33A1S0S11S15P34A1S0S11S15P35A1S0S11S15P36A1S0S11S15P37A1S0S11S15P38A1S0S11S15P39A1S0S11S175S0S11S16cS0S11S12Z3A1S0S11S16bS0S11S12S55A1S0S11S126S0S11G0S0S11G0S0S11G0S0S11G0S0S11S15P3aA1S0S11S15P3bA1S0S11S15P40A1S0S11S15P41A1S4S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition R_cut (cs : list cell) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S4eS24S19bS150S173S26SdS11A1S6bVcs;A1VF;P65SbA9S59S12S53A1A3").
Definition R0c : axst := R_cut [] facts_R0f.
Definition R1c : axst := ltac2:(tb__ "0|0|
S134S0S16S74S4S16A1A3S113A2").

Lemma R_wf : ltac2:(tb__ "0|0|
S41S40S5S4bS62A1S2A3S41S40S5S1eS43S62A1A1S2A3S41S40S5S4bS5fA1S2A3S40S5S1eS43S5fA1A1S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S0f : axst := ltac2:(tb__ "0|0|
S19fS0S14S20P18Z3A2S4S14A1A3S19dA2").
Definition s_R0 : wsub := ltac2:(tb__ "0|1|
S0S9S50S11A2M0S7S50S11P2aS12Z0A1A4S0G0S7S50S11P29S12S19aA1A4S0G0S7S50S11P64S15P32A1A4S0G0S7S50S11P42S16aA4S4G0A1A3A3A3A3").
Lemma ent_R0 : ltac2:(tb__ "0|0|
S40S5S48S72S62S154A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition FUEL_R : nat := 200%nat.
Definition run_R0__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52S7fS54S62S2A5").
Local Strategy expand [run_R0__R].
Definition LV_R0 : list leafA := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) run_R0__R).
Definition run_R1__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52S7fS54S5fS2A5").
Local Strategy expand [run_R1__R].
Definition LV_R1 : list leafA := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) run_R1__R).
Lemma run_R0 : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52S7fS54S62S2A5S6G0S82A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_R0__R <: run_R0__R = Some LV_R0). Qed.
Lemma run_R1 : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52S7fS54S5fS2A5S6G0S83A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_R1__R <: run_R1__R = Some LV_R1). Qed.
Lemma LV_R_pcs : ltac2:(tb__ "0|4|
S41S40S8S9S4fS165A2M0A1M1S57S82A1S0G0S7S4fS165S1b1S166A4M2S0G0G2S4G0A1A3A3M3A3S40G1S57S83A1G3A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vWant : sv := SVar 49.
Definition facts_RD (F : list sprop) : list sprop := ltac2:(tb__ "0|0|
ScS14S0S14S18S12Z1A1S58A2S0S14S18S58S12Z10000A1A2S0S14S18S180S16cS58A2S16bA2S4S14A1A3A3A3VF;A3").
Definition regs_RD : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11S15P3cA1S0S11S174S0S11S12Z10800A1S0S11S16dS0S11S15P3dA1S0S11S15P3eA1S0S11S15P3fA1S0S11S12Z2A1S0S11S16aS0S11S12Z10000A1S0S11S15P33A1S0S11S58S0S11S15P35A1S0S11S15P36A1S0S11S15P37A1S0S11S15P38A1S0S11S15P39A1S0S11S175S0S11S16cS0S11S12Z3A1S0S11S16bS0S11S12S55A1S0S11S126S0S11G0S0S11G0S0S11G0S0S11G0S0S11S15P3aA1S0S11S15P3bA1S0S11S15P40A1S0S11S15P41A1S4S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition RD_cut (cs : list cell) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S4eS24S1b1S151S173S26SdS11A1S6bVcs;A1S146VF;A1P65SbA9S59S12S53A1A3").
Definition RD0 : axst := RD_cut [] facts_R0f.
Definition RD1 : axst := ltac2:(tb__ "0|0|
S133S0S16S74S4S16A1A3S113A2").
Lemma RD_wf : ltac2:(tb__ "0|0|
S41S40S5S4bS68A1S2A3S41S40S5S1eS43S68A1A1S2A3S41S40S5S4bS69A1S2A3S40S5S1eS43S69A1A1S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_RDa : wsub := ltac2:(tb__ "0|1|
S0S9S50S11A2M0S7S50S11P31S27S1c1S16bS16cA3A4S4G0A1A3").
Definition s_RDb : wsub := ltac2:(tb__ "0|1|
S0S9S50S11A2M0S7S50S11P31S12Z10000A1A4S4G0A1A3").
Lemma ent_RD : ltac2:(tb__ "0|2|
S41S40S5S48S6aS62S82U0M0A3S68S124A3S2A3S41S40S5S48S6aS62S82U1M1A3S68S125A3S2A3S41S40S5S48S6aS5fS83G0A3S69S124A3S2A3S40S5S48S6aS5fS83G1A3S69S125A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_RD__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S68S2A5").
Local Strategy expand [run_RD__R1].
Definition LV_RD0 : list leafA := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) run_RD__R1).
Definition run_RD__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S69S2A5").
Local Strategy expand [run_RD__R2].
Definition LV_RD1 : list leafA := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) run_RD__R2).
Definition E_rd0 : axst := Eval vm_compute in nthA RD0 LV_RD0 0.
Definition E_rd1 : axst := Eval vm_compute in nthA RD1 LV_RD1 0.
Lemma run_RD : ltac2:(tb__ "0|4|
S41S40S3S8S45A1M0A1M1S44S52U14M2S54S68S2A5S6G0S0S45S4cS6dS166A2S4S45A1M3A3A2A3S40G1S44S52G2S54S69S2A5S6G0S0S45S4cS6eS166A2G3A3A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_RD__R1 <: run_RD__R1 = Some [mkLeafA E_rd0 RsCut]) (@eq_refl (option (list leafA)) run_RD__R2 <: run_RD__R2 = Some [mkLeafA E_rd1 RsCut])). Qed.
Lemma E_rd_pcs : ltac2:(tb__ "0|0|
S41S40S4fS1dS43S6dA1A1S1b9A3S40S4fS1dS43S6eA1A1S1b9A3A2"). Proof. split; reflexivity. Qed.

Definition rd_rtc : list sobj := ltac2:(tb__ "0|0|
S0S13S194S0S13S181S4S13A1A3A3").
Definition rd_w1 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1U0S12N8d0A1A3A2").
Definition rd_w2 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1U0S12N920A1A3A2").
Definition rd_s1 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1S64VE;A1S180S12S55A1S58A2A3A2").
Definition rd_rs (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1S64VE;A1S5bS58S4S16A1A2A3A2").
Definition rd_cv (E : axst) : axst := ltac2:(tb__ "0|1|
S46VE;S167S43VE;A1M0ScS13S19G0A1Sc1A3A2A2").
Definition rd_site (E : axst) : axst := ltac2:(tb__ "0|0|
S120Sc0Sc2S76S75S73VE;A1A1A1A1A1A1").
Definition C_rd0 : axst := Eval vm_compute in rd_site E_rd0.
Definition C_rd1 : axst := Eval vm_compute in rd_site E_rd1.
Lemma rd_pipe0 : ltac2:(tb__ "0|8|
S73S6dA1S42S75R1A1S42S76R1A1S42Sc2R1A1S42S41S40S5Sb9S6dA1S2A3S41S40S3S17A1M0S182S43R4A1U0M1S12N8d0A1A3S6S17S43R3A1M2A2A3S41S40G0S182G2G1S12N920A1A3S6S17S43R2A1M3A2A3S41S40G0S182G3S64R2A1S180S12S55A1S58A2A3S6S17S43R1A1M4A2A3S41S40S3S13A1S185S13S19G4A1S64R1A1M5A3S6S13S70S58S4S16A1M6A2A2A3S41S40S17S184G4G5S5bS58G6A2A3S43Sc0R1A1A1M7A3S41S40S5S189G4G7A2S2A3S40S42S122S6dA1S7dA3A2A2A2A2A2A2A2TA3;TA2;TA1;TA0;").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma rd_pipe1 : ltac2:(tb__ "0|8|
S73S6eA1S42S75R1A1S42S76R1A1S42Sc2R1A1S42S41S40S5Sb9S6eA1S2A3S41S40S3S17A1M0S182S43R4A1U0M1S12N8d0A1A3S6S17S43R3A1M2A2A3S41S40G0S182G2G1S12N920A1A3S6S17S43R2A1M3A2A3S41S40G0S182G3S64R2A1S180S12S55A1S58A2A3S6S17S43R1A1M4A2A3S41S40S3S13A1S185S13S19G4A1S64R1A1M5A3S6S13S70S58S4S16A1M6A2A2A3S41S40S17S184G4G5S5bS58G6A2A3S43Sc0R1A1A1M7A3S41S40S5S189G4G7A2S2A3S40S42S122S6eA1S7eA3A2A2A2A2A2A2A2TA3;TA2;TA1;TA0;").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s_rd (C : axst) : wsub := ltac2:(tb__ "0|1|
ScS9S50S11A2M0S0G0S7S50S11PfS12S55A1A4S0G0S7S50S11P10S12Z10000A1A4S0G0S7S50S11P11S12Z0A1A4S0G0S7S50S11P13S58A4S4G0A1A3A3A3A3S1c5P1S43VC;A1S43S190A1A3A3").
Definition s_rd0 : wsub := Eval vm_compute in s_rd C_rd0.
Definition s_rd1 : wsub := Eval vm_compute in s_rd C_rd1.
Definition R_rd0 : list sobj := Eval vm_compute in optR (entails_frA C_rd0 Pre_rd s_rd0).
Definition R_rd1 : list sobj := Eval vm_compute in optR (entails_frA C_rd1 Pre_rd s_rd1).
Lemma fr_rd0 : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7dS190Sc8A3S6G0Sa5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_rd1 : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7eS190Sc9A3S6G0Sa6A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_rd0k : ltac2:(tb__ "0|0|
S40S5S196S7dS190Sc8Sa5S18bS45S42S47S191S4S16A1P64A2A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_rd1k : ltac2:(tb__ "0|0|
S40S5S196S7eS190Sc9Sa6S18bS45S42S47S191S4S16A1P64A2A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T_after (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S19fS1fS43VCl;A1A1S198Vs;VPre;VL;VCl;VR;A5A2").

Definition T_rd0k' : axst := Eval vm_compute in T_after Pre_rd C_rd0 s_rd0 R_rd0 (P_rd [] 100).
Definition T_rd1k' : axst := Eval vm_compute in T_after Pre_rd C_rd1 s_rd1 R_rd1 (P_rd [] 100).
Definition T_rd0k : axst := Eval vm_compute in errL T_rd0k'.
Definition T_rd1k : axst := Eval vm_compute in errL T_rd1k'.
Lemma T_rd_eqs : ltac2:(tb__ "0|1|
S41S40S42S5aS190S7dSc8Sa5S192S4S16A1P64A2M0A5SadA3S41S40S42S5aS190S7eSc9Sa6G0A5SafA3S41S40S42S8bSadA1SacA3S41S40S42S8bSafA1SaeA3S41S40S5S8cSadA1S2A3S40S5S8cSafA1S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_T__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54SacS2A5").
Local Strategy expand [run_T__R1].
Definition LV_T0k : list leafA := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) run_T__R1).
Definition run_T__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54SaeS2A5").
Local Strategy expand [run_T__R2].
Definition LV_T1k : list leafA := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) run_T__R2).
Lemma run_T : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U3cM2S54SacS2A5S6G0Sd7A2A3S40G1S44S52G2S54SaeS2A5S6G0Sd8A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_T__R1 <: run_T__R1 = Some LV_T0k) (@eq_refl (option (list leafA)) run_T__R2 <: run_T__R2 = Some LV_T1k)). Qed.
Lemma LV_T_pcs : ltac2:(tb__ "0|3|
S41S40S8S9S4fS165A2M0A1M1S57Sd7A1S0G0S7S4fS165S1b8S166A4S0G0S7S4fS165S1b2S166A4S4G0A1A3A3M2A3S40G1S57Sd8A1G2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_S0__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U28S54S72S2A5").
Local Strategy expand [run_S0__R].
Definition LV_S0 : list leafA := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) run_S0__R).
Lemma run_S0 : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U28S54S72S2A5S6G0S84A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_S0__R <: run_S0__R = Some LV_S0). Qed.
Lemma LV_S0_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57S84A1S0G0S7S4fS165S1b1S166A4S4G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_S0b__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S6aS72S84U0A3S2A5").
Local Strategy expand [run_S0b__R].
Definition E_s0 : axst := Eval vm_compute in ((fun ro8__ : option (list leafA) => nthA S0f ((match ro8__ with Some l => l | None => [] end)) 0) run_S0b__R).
Lemma run_S0b : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U14S54S6aS72S84U0A3S2A5S6G0S0S45S4cS6fS166A2S4S45A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_S0b__R <: run_S0b__R = Some [mkLeafA E_s0 RsCut]). Qed.
Lemma E_s0_pc : ltac2:(tb__ "0|0|
S40S4fS1dS43S6fA1A1S1b9A3"). Proof. reflexivity. Qed.

Definition rd_rsZ (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1S64VE;A1S5bS12S19aA1S4S16A1A2A3A2").
Definition rd_siteZ (E : axst) : axst := ltac2:(tb__ "0|0|
S120S121S76S75S73VE;A1A1A1A1A1").
Definition C_s0 : axst := Eval vm_compute in rd_siteZ E_s0.
Lemma s0_pipe : ltac2:(tb__ "0|6|
S73S6fA1S42S75R1A1S42S76R1A1S42S41S40S5Sb9S6fA1S2A3S41S40S3S17A1M0S182S43R3A1U0M1S12N8d0A1A3S6S17S43R2A1M2A2A3S41S40G0S182G2G1S12N920A1A3S6S17S43R1A1M3A2A3S41S40S3S13A1S185S13S19G3A1S64R1A1M4A3S6S13S17cA2A3S41S40S17S184G3G4S5bS12S19aA1S4S16A1A2A3S43S121R1A1A1M5A3S41S40S5S189G3G5A2S2A3S40S42S14eS6fA1S67A3A2A2A2A2A2A2TA2;TA1;TA0;").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_s0 : wsub := Eval vm_compute in ([(15%positive, SLit RS); (16%positive, SLit CAP0); (17%positive, SLit 0); (19%positive, SLit CAP0)] ++ infer_sub 1 (ax_S C_s0) (ax_S Pre_rd)).
Definition R_s0 : list sobj := Eval vm_compute in optR (entails_frA C_s0 Pre_rd s_s0).
Lemma fr_s0 : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S67S190S77A3S6G0S71A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_s0k : ltac2:(tb__ "0|0|
S40S5S196S67S190S77S71S18bS45S42S47S191S4S16A1P64A2A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_s0h : ltac2:(tb__ "0|0|
S40S5S196S67S190S77S71S18bS45S42S47S191S193P65A2A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T_s0k' : axst := Eval vm_compute in T_after Pre_rd C_s0 s_s0 R_s0 (P_rd [] 100).
Definition T_s0h' : axst := Eval vm_compute in T_after Pre_rd C_s0 s_s0 R_s0 (P_rd hc 101).
Definition T_s0k : axst := Eval vm_compute in errL T_s0k'.
Definition T_s0h : axst := Eval vm_compute in errL T_s0h'.
Lemma T_s0_eqs : ltac2:(tb__ "0|0|
S41S40S42S5aS190S67S77S71S192S4S16A1P64A2A5Sb3A3S41S40S42S5aS190S67S77S71S192S193P65A2A5Sb1A3S41S40S42S8bSb3A1Sb2A3S41S40S42S8bSb1A1Sb0A3S41S40S5S8cSb3A1S2A3S40S5S8cSb1A1S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition run_S0T__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sb2S2A5").
Local Strategy expand [run_S0T__R1].
Definition LV_S0k : list leafA := Eval vm_compute in ((fun ro9__ : option (list leafA) => (match ro9__ with Some l => l | None => [] end)) run_S0T__R1).
Definition run_S0T__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sb0S2A5").
Local Strategy expand [run_S0T__R2].
Definition LV_S0h : list leafA := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) run_S0T__R2).
Lemma run_S0T : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U3cM2S54Sb2S2A5S6G0Sd6A2A3S40G1S44S52G2S54Sb0S2A5S6G0Sd5A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_S0T__R1 <: run_S0T__R1 = Some LV_S0k) (@eq_refl (option (list leafA)) run_S0T__R2 <: run_S0T__R2 = Some LV_S0h)). Qed.
Lemma LV_S0T_pcs : ltac2:(tb__ "0|3|
S41S40S8S9S4fS165A2M0A1M1S57Sd6A1S0G0S7S4fS165S1b8S166A4S0G0S7S4fS165S1b2S166A4S4G0A1A3A3M2A3S40G1S57Sd5A1G2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition selq : list nat := ltac2:(tb__ "0|2|
ScS1S0S1U9S0S1U1S0S1U0S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1U3S0S1UfS0S1U10M0S0S1U11S0S1U12S0S1U13S0S1U14S0S1U15S0S1U6S0S1U16S0S1U17S0S1U18S0S1U19S0S1U1aS0S1U1bS0S1U1cS4S1A1M1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU1dG0A2S0S1U2S0S1U2dS0S1U7S0S1U8S0S1U4S0S1U5G1A3A3A3A3A3A3A3A3").
Definition XF_q : list axform := ltac2:(tb__ "0|1|
S0S160S164S15dA1S0S160S163U1A1S0S160S163U2A1S0S160S162U0A1M0S0S160G0S4S160A1A3A3A3A3A3").
Definition q1 (E : axst) : axst := ltac2:(tb__ "0|0|
S106S161VE;S104A2VE;A2").

Definition q2 (w : sv) (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1U26S70Vw;S4S16A1A2A3A2").
Definition q3 (E : axst) : axst := ltac2:(tb__ "0|0|
S106S161VE;S0S160S162U26A1S4S160A1A3A2VE;A2").

Definition objs37 (A : axst) : list sobj := firstn 41 (ss_objs (ax_S A)).
Definition q4 (X : list (sv * sv)) (E : axst) : axst := ltac2:(tb__ "0|0|
S1bbS46VE;S167S43VE;A1S8eVE;A1A2A2VX;A2").
Definition qpipe (w : sv) (X : list (sv * sv)) (E : axst) : axst := ltac2:(tb__ "0|0|
S14dVX;S14cS11eVw;S14bVE;A1A2A1A2").
Definition q_okb (w : sv) (X : list (sv * sv)) (E : axst) : bool := ltac2:(tb__ "0|5|
S3S42A1S5Lx;M0S161VE;S104A2S42S3S13A1S5Lx;S185S13S19S43R1A1A1M1U26M2A3S13SaSaS60R1S12S55A1S12Z0A1Vw;A4S189S43R2A1S43S11eVw;R2A2M3A1A2A2G0S161G3S0S160S162G2A1S4S160A1A3A2S42SaSaS186S9S13S13A2M4G4S49SfS13S13R1A3S10S13S13R1A3A2Lp;S187S13S13S18cS13U29G1A3Sc1A4A3S1bcSeS13G1A2U2bA2A2S1a9VX;S4aR1A1A2A2LA3;SbX3x2A2Lo;SbX3x2LA1;SbX3x2").

Definition Lcp1 : axst := Eval vm_compute in nthA R1c LV_T1k 0.
Definition Lcl1 : axst := Eval vm_compute in nthA R1c LV_T1k 1.
Definition Q1 : axst := Eval vm_compute in qpipe vWant X_R Lcp1.
Definition Hc1 : axst := Eval vm_compute in qpipe vWant X_R Lcl1.
Lemma q1_ok : ltac2:(tb__ "0|0|
S41S40S5SbcS58S59SefA3S2A3S41S40S42SbdS58S59SefA3S86A3S41S40S5SbcS58S59SeeA3S2A3S40S42SbdS58S59SeeA3S81A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma Q1_objs : ltac2:(tb__ "0|2|
S41S40S8S13A1M0S19S43S86A1A1S6bS0S16S74S4S16A1A3A1M1A3S40G0S19S43S81A1A1G1A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition mc_rtc : list sobj := ltac2:(tb__ "0|0|
S0S13S1c9S0S13S181S0S13S1c8S4S13A1A3A3A3").
Definition ibS (St : sstate) (b lo : sv) : nat := ltac2:(tb__ "0|0|
S16eS19VSt;A1Vb;Vlo;A3").
Definition obind (x : option sstate) (f : sstate -> option sstate) : option sstate := ltac2:(tb__ "0|1|
S3S17A1M0G0Lx;Vx;S17Vf;R1A1LSt;SdS17A1X3x2").
Definition cp_w1 (St : sstate) : option sstate := split_obj_at St 0 (SLit (-2288)).
Definition cp_w2 (St : sstate) : option sstate := split_obj_at St 0 (SLit (-2368)).
Definition cp_b0 (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S16aS12Z0A1A3S12Z4A1A3").
Definition cp_b1 (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S16aS12Z4A1A3S16cA3").
Definition cp_b2 (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S16aS16cA3S180S16cVr;A2A3").
Definition cp_splits (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S5cS5cS5cS5cS10cVSt;A1S10dA2S138A2S139A2S13aVr;A1A2").
Definition O_dstC (r : sv) : sobj := ltac2:(tb__ "0|0|
S1bS180S16aS16cA2S12Z0A1Vr;S4S16A1S1aA5").
Definition O_dstL (r : sv) : sobj := ltac2:(tb__ "0|0|
S1bS16aS16cS180S16cVr;A2S4S16A1S1aA5").
Definition cp_rsd (r : sv) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184VSt;S56VSt;S16aS16cA3S12cVr;A1A3").
Definition cp_s1 (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|1|
S182VSt;S56VSt;S12Z0A1S12S55A1M0A3S180G0Vr;A2A3").
Definition cp_rss (r : sv) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184VSt;S56VSt;S12Z0A1S12S55A1A3S5bVr;S4S16A1A2A3").
Definition cp_cv (St : sstate) : sstate := ltac2:(tb__ "0|0|
S167VSt;ScS13S19VSt;A1SbbA3A2").
Definition cp_site (r : sv) (E : axst) : option axst := ltac2:(tb__ "0|2|
S3S17A1S3S42A1Lx;M0S10bVr;S43VE;A1A2S17G0S88Vr;S109Vr;R1A2A2S17S6S42S46VE;Sb8S10aVr;R1A2A1A2A2LS7;SdS42A1M1X3x2LS5;G1X3x2").

Definition cp_okb (r : sv) (E : axst) : bool := ltac2:(tb__ "0|6|
S3S17A1S5Lx;M0S10bVr;S43VE;A1A2S17S3S13A1S5Lx;M1S185S13S19R1A1M2S56R1S16aS16cA3A3S13SaSaS60R1S16aS16cS180S16cVr;A2A4S189R2S109Vr;R2A2M3A2A2G0S88Vr;G3A2S17G1S185S13G2S56R1S12Z0A1M4S12S55A1M5A3A3S13SaS60R1G4G5S180G5Vr;A2A4S189R2S10aVr;R2A2A2A2Lo';SbX3x2LS7;SbX3x2A2Lo;SbX3x2LS5;SbX3x2").
Definition PreC : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.Pre_mc0.
Definition PostsC : list leafA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.Posts_mc.
Definition s_cp (r : sv) (C : axst) : wsub := ltac2:(tb__ "0|1|
ScS9S50S11A2M0S0G0S7S50S11PfS16aA4S0G0S7S50S11P10S16bA4S0G0S7S50S11P11S16cA4S0G0S7S50S11P13S12S55A1A4S0G0S7S50S11P34S12Z10000A1A4S0G0S7S50S11P35S12Z0A1A4S0G0S7S50S11P12Vr;A4S4G0A1A3A3A3A3A3A3A3S1c5P1S43VC;A1S43S65A1A3A3").

Definition vRes1 : sv := SVar 101.
Definition C_cp1 : axst := Eval vm_compute in ax_of (cp_site vRes1 Q1) Q1.
Lemma cp1_ok : ltac2:(tb__ "0|0|
S41S40S5S13bS5dS86A2S2A3S40S3S42A1S13cS5dS86A2S6S42S79A2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_cp1 : wsub := Eval vm_compute in s_cp vRes1 C_cp1.
Definition R_cp1 : list sobj := Eval vm_compute in optR (entails_frA C_cp1 PreC s_cp1).
Lemma fr_cp1 : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S79S65Sc3A3S6G0Sa0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_cp1 : ltac2:(tb__ "0|0|
S40S5S196S79S65Sc3Sa0S18bS45S42S47SfbA4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T_cp1 : axst := Eval vm_compute in T_after PreC C_cp1 s_cp1 R_cp1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.P_icpt.
Lemma T_cp1_eq : ltac2:(tb__ "0|0|
S40S42S5aS65S79Sc3Sa0S1c7A5Sa7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_C1__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sa7S2A5").
Local Strategy expand [run_C1__R].
Definition LV_C1 : list leafA := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) run_C1__R).
Lemma run_C1 : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U3cS54Sa7S2A5S6G0Sd2A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_C1__R <: run_C1__R = Some LV_C1). Qed.
Lemma LV_C1_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57Sd2A1S0G0S7S4fS165S1b5S166A4S0G0S7S4fS165S1a6S166A4S0G0S7S4fS165S19bS166A4S4G0A1A3A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition selb : list nat := ltac2:(tb__ "0|1|
ScS1S0S1U9S0S1U1S0S1U0S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U2S0S1U14S4S1A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU15U1cA2S0S1U3S0S1U31S0S1U7S0S1U8S0S1U4S0S1U5S0S1U6G0A3A3A3A3A3A3A3A3A3").
Definition XF_bka : list axform := ltac2:(tb__ "0|1|
S0S160S164S15aA1S0S160S163U1A1S0S160S163U2A1S0S160S162U0A1M0S0S160G0S4S160A1A3A3A3A3A3").

Definition bk2 (r : sv) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184S184VSt;UbS12dVr;A1A3U29S70Vr;S4S16A1A2A3").
Definition XF_bkb : list axform := ltac2:(tb__ "0|1|
S0S160S162U9A1M0S0S160G0S0S160G0S0S160S162U26A1S4S160A1A3A3A3A3").
Definition bkpipe (r : sv) (X : list (sv * sv)) (E : axst) : option axst := ltac2:(tb__ "0|4|
S3S42A1M0G0Lx;M1S161VE;S100A2S42G1S161S46R1S107Vr;S43R1A1M2A2A2S101A2S42S6S42S1bbS46R1S167G2S8eR1A1A2A2VX;A2A2LA3;SdS42A1M3X3x2LA1;G3X3x2").
Definition bk_okb (r : sv) (X : list (sv * sv)) (E : axst) : bool := ltac2:(tb__ "0|8|
S3S42A1S5Lx;M0S161VE;S100A2S42S3S13A1S5Lx;M1S185S13S19S43R1A1A1M2UbA3S13G1S185S13S19S43R2A1A1U29M3A3S13SaSaSaS60R2S180S16aS16cA2S12Z0A1M4Vr;A4S60R1S12S55A1G4Vr;A4A2S189S43R3A1M5S107Vr;G5A2M6A2A2G0S161S46R3G6A2S101A2S42SaSaS186S9S13S13A2M7G7S49SfS13S13R1A3S10S13S13R1A3A2Lp;S187S13S13S18cS13G3G2A3SbbA4A3S1bcSeS13G2A2U2cA2A2S1a9VX;S4aR1A1A2A2LA3;SbX3x2A2Lo';SbX3x2Lo;SbX3x2LA1;SbX3x2").

Definition Lb1 : axst := Eval vm_compute in nthA R1c LV_C1 2.
Definition B1u : axst := Eval vm_compute in ax_of (bkpipe vRes1 X_R Lb1) Lb1.
Lemma bk1_ok : ltac2:(tb__ "0|0|
S41S40S5Sb4S5dS59Se9A3S2A3S40S3S42A1Sb5S5dS59Se9A3S6S42S92A2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma B1u_objs : ltac2:(tb__ "0|0|
S40S8S13A1S19S43S92A1A1S6bS0S16S74S4S16A1A3A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition s_bk1 : wsub := Eval vm_compute in infer_sub 1 (ax_S B1u) (ax_S R1c).
Definition len1' : sv := Eval vm_compute in wsub_get s_bk1 42%positive.
Definition F_bk1 : list sprop := ltac2:(tb__ "0|0|
S0S14S18S180S119S12Z1A1A2S16bA2S0S14S18S119S16bA2S4S14A1A3A3").
Lemma ent_bk1 : ltac2:(tb__ "0|0|
S40S5S48S19fS129S92A2S5fS156A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition PreM : axst := ltac2:(tb__ "0|0|
S1afS1aaS4S1acA1S1abA3").
Definition PostsM : list axst := ltac2:(tb__ "0|1|
S0S42S1adS1aaS4S1acA1M0S1abA3S0S42S1aeS1aaG0S1abA3S4S42A1A3A3").

Definition Lg1 : axst := Eval vm_compute in nthA R1c LV_C1 1.
Definition Lr1 : axst := Eval vm_compute in nthA R1c LV_C1 0.
Definition E_m : axst := Eval vm_compute in ax_of (bkpipe vRes1 X_R Lg1) Lg1.
Definition Lref : axst := Eval vm_compute in ax_of (bkpipe vRes1 X_R Lr1) Lr1.
Lemma bkg_ok : ltac2:(tb__ "0|1|
S41S40S5Sb4S5dS59Sf0A3S2A3S41S40S3S42A1M0Sb5S5dS59Sf0A3S6S42SccA2A3S41S40S5Sb4S5dS59Sf4A3S2A3S40G0Sb5S5dS59Sf4A3S6S42S9cA2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition two_cap : sv := SAlu ALU_SLL vCap (SLit 1).
Definition regs_G : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11S12Z8c438A1S0S11S174S0S11S12Z10800A1S0S11S16dS0S11S15P3dA1S0S11S15P3eA1S0S11S15P3fA1S0S11S12Z2A1S0S11S16aS0S11S66S0S11S15P33A1S0S11S15P34A1S0S11S15P35A1S0S11S15P36A1S0S11S15P37A1S0S11S15P38A1S0S11S15P39A1S0S11S175S0S11S16bS0S11S12Z3A1S0S11S66S0S11S12S55A1S0S11S16aS0S11G0S0S11G0S0S11G0S0S11G0S0S11S15P3aA1S0S11S15P3bA1S0S11S15P40A1S0S11S15P41A1S4S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition facts_G : list sprop := ltac2:(tb__ "0|0|
S0S14S18S16bS12S1a1Z2Z19A2A1A2S114A3").
Definition G_cut : axst := ltac2:(tb__ "0|0|
S4eS24S1a6S14fS173S26SdS11A1S6bS0S16S74S4S16A1A3A1S145P65SbA9S59S12S53A1A3").
Lemma G_wf : ltac2:(tb__ "0|0|
S41S40S5S4bS61A1S2A3S40S5S1eS43S61A1A1S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition lenG : sv := add vRes1 vLen.
Definition E_mG : axst := Eval vm_compute in
  ax_setS E_m (mkSS (ss_pc (ax_S E_m)) (list_set (list_set (list_set (ss_regs (ax_S E_m)) 10 two_cap) 19 vCap) 21 two_cap)
                    (ss_fregs (ax_S E_m)) (ss_fcsr (ax_S E_m)) (ss_resv (ax_S E_m)) (ss_objs (ax_S E_m)) (ss_facts (ax_S E_m)) (ss_next (ax_S E_m)) (ss_lenient (ax_S E_m))).
Lemma E_mG_diff : ltac2:(tb__ "0|7|
S41S40S3S9S8S9S11S11A2M0A1M1S8S14A1M2A2M3A1S18aS43SccA1M4S43ScdA1M5A2S6G3S7G1G2S0G0S7S11S11S27S1c0SbaS12Z1A1A3S66A4M6S0G0S7S11S11SbaS16bA4S0G0G6S4G0A1A3A3A3S4S14A1A4A2A3S41S40S5S1eG5A1S2A3S41S40S50S1cG5A1S1cG4A1A3S40S5S188S14S25S23S1bdSbaS16bA3A1S1fG4A1A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_G : wsub := Eval vm_compute in infer_sub 1 (ax_S E_mG) (ax_S G_cut).

Lemma ent_G : ltac2:(tb__ "0|0|
S40S5S48S19fS0S14S18S16bS12S1a1Z2Z19A2A1A2S4S14A1A3ScdA2S61S152A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition s_mG : wsub := Eval vm_compute in ((15%positive, SLit (- DEEP)) :: infer_sub 1 (ax_S G_cut) (ax_S PreM)).
Definition R_mG : list sobj := Eval vm_compute in optR (entails_frA G_cut PreM s_mG).
Lemma fr_mG : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S61S85S90A3S6G0S87A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_mG : ltac2:(tb__ "0|0|
S40S5S197S61S85S90S87S131A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G_mnull : axst := Eval vm_compute in T_after PreM G_cut s_mG R_mG (L_malloc_null AE_A [] UStopLe).
Definition G_mok : axst := Eval vm_compute in T_after PreM G_cut s_mG R_mG (L_malloc_ok AE_A [] UStopLe).
Lemma G_m_eqs : ltac2:(tb__ "0|1|
S41S40S42S5aS85S61S90S87S1adS1aaS4S1acA1M0S1abA3A5S99A3S40S42S5aS85S61S90S87S1aeS1aaG0S1abA3A5S80A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition vN' : positive := Eval vm_compute in match nth 10 (ss_regs (ax_S G_mok)) (SLit 0) with SVar v => v | _ => 1%positive end.
Lemma vN'_eq : ltac2:(tb__ "0|0|
S40S11S18fS11UaS22S43S80A1A1S12Z0A1A4S15S91A1A3"). Proof. reflexivity. Qed.
Definition run_G__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S99S2A5").
Local Strategy expand [run_G__R1].
Definition LV_Gnull : list leafA := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) run_G__R1).
Definition run_G__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S80S2A5").
Local Strategy expand [run_G__R2].
Definition LV_Gok : list leafA := Eval vm_compute in ((fun ro13__ : option (list leafA) => (match ro13__ with Some l => l | None => [] end)) run_G__R2).
Lemma run_G : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U14M2S54S99S2A5S6G0Sd3A2A3S40G1S44S52G2S54S80S2A5S6G0Sd4A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_G__R1 <: run_G__R1 = Some LV_Gnull) (@eq_refl (option (list leafA)) run_G__R2 <: run_G__R2 = Some LV_Gok)). Qed.
Lemma LV_G_pcs : ltac2:(tb__ "0|3|
S41S40S8S9S4fS165A2M0A1M1S57Sd3A1S0G0S7S4fS165S1b3S166A4S4G0A1M2A3A3S40G1S57Sd4A1S0G0S7S4fS165S1b8S166A4G2A3A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_mc : axst := Eval vm_compute in nthA G_mok LV_Gok 0.

Definition mch_rtc : list sobj := ltac2:(tb__ "0|0|
S0S13S1cfS0S13S181S0S13S1ceS4S13A1A3A3A3").
Definition mc_kfacts : list sprop := ltac2:(tb__ "0|3|
S0S14S18S16bS66A2S0S14S18S180S16bS12Z1A1A2S66A2S0S14S18S15S91A1M0S12S176A1M1A2S0S14S18S180G0S66A2M2G1A2S0S14S18S12S177A1G0A2S0S14S18G2S171A2S0S14S18G0S171A2S4S14A1A3A3A3A3A3A3A3").
Definition E_mcf : axst := ax_add_facts mc_kfacts E_mc.
Definition mc_w1 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1U0S12N870A1A3A2").
Definition mc_w2 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1U0S12N8c0A1A3A2").
Definition inew (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S15S91A1S12Z0A1A3").
Definition mc_b1 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1S118VE;A1S16bA3A2").
Definition mc_cv (E : axst) : axst := ltac2:(tb__ "0|1|
S46VE;S167S43VE;A1M0ScS13S19G0A1S11dA3A2A2").
Definition mc_site (E : axst) : axst := ltac2:(tb__ "0|0|
S147S11aS11cS11bVE;A1A1A1A1").
Definition C_mc : axst := Eval vm_compute in mc_site E_mcf.
Lemma mc_pipe : ltac2:(tb__ "0|5|
S11bS98A1S42S11cR1A1S42S11aR1A1S42S41S40S5S186S14S3aS1cS43S128A1M0A1A1ScS14S148S1fG0A1A3A3S2A3S41S40S3S17A1M1S182S43S98A1U0M2S12N870A1A3S6S17S43R3A1M3A2A3S41S40G1S182G3G2S12N8c0A1A3S6S17S43R2A1M4A2A3S41S40G1S182G4S118R2A1S16bA3S6S17S43R1A1A2A3S40S42S149S98A1S7cA3A2A2A2A2TA3;TA2;TA1;").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition PreMC : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr.Pre_mc0.
Definition PostsMC : list leafA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr.Posts_mc.
Definition s_mc : wsub := Eval vm_compute in
  ([(15%positive, SVar vN'); (16%positive, two_cap); (19%positive, vB); (52%positive, vCap); (18%positive, vCap); (54%positive, vH)]
   ++ infer_sub 1 (ax_S C_mc) (ax_S PreMC)).
Definition R_mc : list sobj := Eval vm_compute in optR (entails_frA C_mc PreMC s_mc).
Lemma fr_mc : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7cS9fSc7A3S6G0Sa4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_mc : ltac2:(tb__ "0|0|
S40S5S196S7cS9fSc7Sa4S18bS45S42S47S132A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T_mc : axst := Eval vm_compute in T_after PreMC C_mc s_mc R_mc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr.P_icpt.
Lemma T_mc_eq : ltac2:(tb__ "0|0|
S40S42S5aS9fS7cSc7Sa4S1d0A5SabA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_mc__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U1eS54SabS2A5").
Local Strategy expand [run_mc__R].
Definition LV_mc : list leafA := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) run_mc__R).
Lemma run_mc : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U1eS54SabS2A5S6G0Se2A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_mc__R <: run_mc__R = Some LV_mc). Qed.
Lemma LV_mc_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57Se2A1S0G0S7S4fS165S1a7S166A4S4G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_f : axst := Eval vm_compute in nthA T_mc LV_mc 0.

Definition self : list nat := ltac2:(tb__ "0|1|
ScS1S0S1U9S0S1U1S0S1U0S0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U2S0S1UaS0S1U3S4S1A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU13U1cA2S0S1U2fS0S1U7S0S1U8S0S1U4S0S1U5S0S1U6G0A3A3A3A3A3A3A3A3").
Definition XF_f : list axform := ltac2:(tb__ "0|2|
S0S160S164S15cA1S0S160S163U0M0A1S0S160S163U1A1S0S160S163U2A1S0S160S162G0A1M1S0S160G1S0S160S162U9A1S4S160A1A3A3A3A3A3A3A3").
Definition X_G : list (sv * sv) := ltac2:(tb__ "0|2|
ScS9S11S11A2M0S0G0S7S11S11S12Z14d40A1S12Z80M1A1A4S0G0S7S11S11S180S170S12S1a3S1a0S16fG1A2A1A1A2S12S16fA1A4S0G0S7S11S11S15S91A1S66A4S0G0S179S4G0A1A3A3A3A3S1caA3").
Definition F1 : axst := Eval vm_compute in ax_of (apply_axforms E_f XF_f) E_f.
Lemma F1_eq : ltac2:(tb__ "0|0|
S40S3S42A1S161S127S135A2S6S42Sd0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F2 : axst := Eval vm_compute in ax_setX F1 X_G.

Definition objs38 (A : axst) : list sobj := firstn 42 (ss_objs (ax_S A)).
Lemma F2_objs : ltac2:(tb__ "0|0|
S41S40S8S13A1S19S43Sd1A1A1ScS13S14aSd1A1S11dA3A3S40S5S1a9S136S4aSd0A1A2S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_f : axst := Eval vm_compute in ax_setS F2 (set_objs (ax_S F2) (objs38 F2)).
Definition s_f : wsub := Eval vm_compute in ([(15%positive, SLit (- DEEP)); (12%positive, vB); (13%positive, vCap)] ++ infer_sub 1 (ax_S C_f) (ax_S PreF)).
Definition R_f : list sobj := Eval vm_compute in optR (entails_frA C_f PreF s_f).
Lemma fr_f : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S94S172Sc6A3S6G0Sa3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_f : ltac2:(tb__ "0|0|
S40S5S197S94S172Sc6Sa3S0S42S178S4S42A1A3A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_f : axst := Eval vm_compute in T_after PreF C_f s_f R_f PostF.
Lemma T_f_eq : ltac2:(tb__ "0|0|
S40S42S5aS172S94Sc6Sa3S178A5SaaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U1eS54SaaS2A5").
Local Strategy expand [run_f__R].
Definition LV_f : list leafA := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) run_f__R).
Lemma run_f : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U1eS54SaaS2A5S6G0SdeA2A3"). Proof. exact (@eq_refl (option (list leafA)) run_f__R <: run_f__R = Some LV_f). Qed.
Lemma LV_f_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57SdeA1S0G0S7S4fS165S19bS166A4S4G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Lg : axst := Eval vm_compute in nthA T_f LV_f 0.
Definition Bg : axst := Eval vm_compute in ax_of (apply_axforms Lg [AXRebase 0]) Lg.
Lemma Bg_eq : ltac2:(tb__ "0|0|
S40S3S42A1S161S12aS0S160S163U0A1S4S160A1A3A2S6S42S93A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Bg_objs : ltac2:(tb__ "0|0|
S40S1SeS13S19S43S93A1A1A2U29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s_bkG : wsub := Eval vm_compute in
  ([(40%positive, SVar vN'); (41%positive, two_cap); (42%positive, vCap); (45%positive, SExt true 32 vH)] ++ infer_sub 1 (ax_S Bg) (ax_S R1c)).
Lemma ent_bkG : ltac2:(tb__ "0|0|
S40S5S48S93S5fS157A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Ls0k : axst := Eval vm_compute in nthA S0f LV_S0k 0.
Definition Lc0k : axst := Eval vm_compute in nthA S0f LV_S0k 1.
Definition Ls0h : axst := Eval vm_compute in nthA S0f LV_S0h 0.
Definition selqZ : list nat := ltac2:(tb__ "0|2|
ScS1S0S1U9S0S1U1S0S1U0S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1U3S0S1UfS0S1U10M0S0S1U11S0S1U12S0S1U13S0S1U14S0S1U15S0S1U6S0S1U16S0S1U17S0S1U18S0S1U19S0S1U1aS0S1U1bS0S1U1cS4S1A1M1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU1dG0A2S0S1U2S0S1U7S0S1U8S0S1U4S0S1U5G1A3A3A3A3A3A3A3").
Definition XF_qz : list axform := ltac2:(tb__ "0|1|
S0S160S164S15eA1S0S160S163U1A1S0S160S163U2A1S0S160S162U0A1M0S0S160G0S4S160A1A3A3A3A3A3").

Definition rds_cellsL (cs : list cell) : list cell := ltac2:(tb__ "0|1|
S18bS16S16S16S28S11S11Lx;S32R1A1S4fS12S1a0S55R1A2A1Lz;S50S180S12S55A1M0S15R1A1A2Li;S1beS11S11S180G0S27R3R2R1A3A2Lb;La;Lop;S1beS11S11S180G0S2eR3R2R1A3A2Lb;La;Lop;S1bfS11S11S180G0S30R3R2R1A3A2Lb;La;Lop;S1bfS11S11S180G0S31R3R2R1A3A2Lb;La;Lop;S5S51S11S180G0S2aR3R2R1A3A2La;Lw;Lsgn;S50S11S4fS180G0S2fR3R2R1A3A2Lk;Li;Ll;X11x8S34R1A1S33R1A1A3Lc;Vcs;A4").
Definition qz2 (cs : list cell) (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1U26S1bS12Z0A1S12S55A1S12S1a0S55Z10000A2A1S8fVcs;A1S1aA5A3A2").
Definition qzpipe (cs : list cell) (E : axst) : option axst := ltac2:(tb__ "0|1|
S3S42A1M0G0Lx;S161VE;S105A2S42S11fVcs;R1A2S42S6S42S1bbS46R1S167S43R1A1S8eR1A1A2A2S199A2A2TA2;LA1;SdS42A1X3x2").
Definition qz_okb (cs : list cell) (E : axst) : bool := ltac2:(tb__ "0|3|
S3S42A1S5Lx;S161VE;S105A2S42S3S13A1S5Lx;S185S13S19S43R1A1A1U26A3S13SaSaSaSaS49R1S1bS12S55A1S12Z0A1S12Z10000A1Vcs;S1aA5A2S189S43R2A1M0S43S11fVcs;R2A2A1A2A2S186S9S13S13A2M1G1S49SfS13S13R1A3S10S13S13R1A3A2Lp;S187S13S13S18cS13U29S19G0A1M2A3Sc1A4A3A2S1bcSeS13G2A2U2bA2A2S1a9S199S4aR2A1A2A2Lo;SbX3x2LA1;SbX3x2").
Definition hcZ : list cell := ltac2:(tb__ "0|0|
S0S16S28S12Z0A1Z4S15P64A1A3S4S16A1A3").
Definition QZk : axst := Eval vm_compute in ax_of (qzpipe [] Ls0k) Ls0k.
Definition QZh : axst := Eval vm_compute in ax_of (qzpipe hcZ Ls0h) Ls0h.
Definition HcZ : axst := Eval vm_compute in ax_of (qzpipe [] Lc0k) Lc0k.
Lemma qz_ok : ltac2:(tb__ "0|2|
S41S40S5SbeS4S16A1M0Sf6A2S2A3S41S40S3S42A1M1SbfG0Sf6A2S6S42SfeA2A3S41S40S5SbeS63Sf5A2S2A3S41S40G1SbfS63Sf5A2S6S42SfcA2A3S41S40S5SbeG0SecA2S2A3S40G1SbfG0SecA2S6S42S9bA2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cz_b1 (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S16aS12Z0A1A3Vr;A3").
Definition cz_splits (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S5cS5cS10cVSt;A1S10dA2S13dVr;A1A2").
Definition O_dstZ (r : sv) : sobj := ltac2:(tb__ "0|1|
S1bS180S16aS12Z0A1M0A2G0Vr;S4S16A1S1aA5").
Definition cz_rsd (r : sv) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184VSt;S56VSt;S16aS12Z0A1A3S12eVr;A1A3").
Definition cz_site (r : sv) (cs : list cell) (E : axst) : option axst := ltac2:(tb__ "0|2|
S3S17A1S3S42A1Lx;M0S8aVr;S43VE;A1A2S17G0S88Vr;S89Vr;R1A2A2S17S6S42S46VE;Sb8S184R1S56R1S12Z0A1S12S55A1A3S5bVr;Vcs;A2A3A1A2A2LS5;SdS42A1M1X3x2LS3;G1X3x2").
Definition cz_okb (r : sv) (cs : list cell) (E : axst) : bool := ltac2:(tb__ "0|6|
S3S17A1S5Lx;M0S8aVr;S43VE;A1A2S17S3S13A1S5Lx;M1S185S13S19R1A1M2S56R1S16aS12Z0A1M3A3A3S13SaSaS60R1S16aG3Vr;A4S189R2S89Vr;R2A2M4A2A2G0S88Vr;G4A2S17G1S185S13G2S56R1G3S12S55A1M5A3A3S13SaS49R1S1bG3G5S180G5Vr;A2S8fVcs;A1S1aA5A2S189R2S184R2S56R2G3G5A3S5bVr;Vcs;A2A3A2A2Lo';SbX3x2LS5;SbX3x2A2Lo;SbX3x2LS3;SbX3x2").
Definition s_cz (r : sv) (C Pre : axst) : wsub := ltac2:(tb__ "0|2|
ScS9S50S11A2M0S0G0S7S50S11PfS16aA4S0G0S7S50S11P10S12S19aA1A4S0G0S7S50S11P11S12Z0A1M1A4S0G0S7S50S11P13S12S55A1A4S0G0S7S50S11P34S12Z10000A1A4S0G0S7S50S11P35G1A4S0G0S7S50S11P12Vr;A4S4G0A1A3A3A3A3A3A3A3S1c5P1S43VC;A1S43VPre;A1A3A3").

Definition vRes0 : sv := SVar 100.
Definition QZkf : axst := ltac2:(tb__ "0|0|
S19fS0S14S18S78S12Z3A1A2S4S14A1A3SfeA2").
Definition C_czk : axst := Eval vm_compute in ax_of (cz_site vRes0 [] QZkf) QZkf.
Lemma czk_ok : ltac2:(tb__ "0|1|
S41S40S5S13eS78S4S16A1M0SffA3S2A3S40S3S42A1S13fS78G0SffA3S6S42S7bA2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_czk : wsub := Eval vm_compute in s_cz vRes0 C_czk PreC.
Definition R_czk : list sobj := Eval vm_compute in optR (entails_frA C_czk PreC s_czk).
Lemma fr_czk : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7bS65Sc5A3S6G0Sa2A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_czk : ltac2:(tb__ "0|0|
S40S5S196S7bS65Sc5Sa2S18bS45S42S47SfbA4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_czk : axst := Eval vm_compute in T_after PreC C_czk s_czk R_czk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.P_icpt.
Lemma T_czk_eq : ltac2:(tb__ "0|0|
S40S42S5aS65S7bSc5Sa2S1c7A5Sa9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_Zk__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sa9S2A5").
Local Strategy expand [run_Zk__R].
Definition LV_Zk : list leafA := Eval vm_compute in ((fun ro16__ : option (list leafA) => (match ro16__ with Some l => l | None => [] end)) run_Zk__R).
Lemma run_Zk : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U3cS54Sa9S2A5S6G0SdaA2A3"). Proof. exact (@eq_refl (option (list leafA)) run_Zk__R <: run_Zk__R = Some LV_Zk). Qed.
Lemma LV_Zk_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57SdaA1S0G0S7S4fS165S19bS166A4S4G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition vResH : sv := SVar 101.
Definition PreCH : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs.Pre_mc0.
Definition PostsCH : list leafA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs.Posts_mc.
Definition QZhf : axst := ltac2:(tb__ "0|0|
S19fS0S14S18S12Z4A1S5eA2S4S14A1A3SfcA2").
Definition czh_h1 (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S12Z0A1S12S55A1A3S12S1a0S55Z4A2A1A3").
Definition czh_h2 (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S12Z0A1S12S1a0S55Z4A2A1A3S180S12S55A1Vr;A2A3").
Definition czh_h3 (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S183VSt;S56VSt;S12Z0A1S12S55A1A3A2").
Definition czh_site (r : sv) (cs : list cell) (E : axst) : option axst := ltac2:(tb__ "0|2|
S3S17A1S3S42A1Lx;M0S8aVr;S43VE;A1A2S17G0S5cS5cS10eS89Vr;R1A2A1S10fVr;A1A2S110A2S17S6S42S46VE;Sb8S184R1S56R1S12Z0A1S12S55A1A3S5bVr;Vcs;A2A3A1A2A2LS6;SdS42A1M1X3x2LS3;G1X3x2").
Definition czh_okb (r : sv) (cs : list cell) (E : axst) : bool := ltac2:(tb__ "0|6|
S3S17A1S5Lx;M0S8aVr;S43VE;A1A2S17S3S13A1S5Lx;M1S185S13S19R1A1M2S56R1S16aS12Z0A1M3A3A3S13SaSaS60R1S16aG3Vr;A4S189R2S89Vr;R2A2M4A2A2G0S5cS5cS10eG4A1S10fVr;A1A2S110A2S17G1S185S13G2S56R1G3S12S55A1M5A3A3S13SaS49R1S1bG3G5S180G5Vr;A2S8fVcs;A1S1aA5A2S189R2S184R2S56R2G3G5A3S5bVr;Vcs;A2A3A2A2Lo';SbX3x2LS6;SbX3x2A2Lo;SbX3x2LS3;SbX3x2").
Definition C_czh : axst := Eval vm_compute in ax_of (czh_site vResH hcZ QZhf) QZhf.
Lemma czh_ok : ltac2:(tb__ "0|0|
S41S40S5S140S5eS63SfdA3S2A3S40S3S42A1S141S5eS63SfdA3S6S42S7aA2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_czh : wsub := Eval vm_compute in ((54%positive, SVar 100) :: s_cz vResH C_czh PreCH).
Definition R_czh : list sobj := Eval vm_compute in optR (entails_frA C_czh PreCH s_czh).
Lemma fr_czh : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7aS9eSc4A3S6G0Sa1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_czh : ltac2:(tb__ "0|0|
S40S5S196S7aS9eSc4Sa1S18bS45S42S47S130A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_czh : axst := Eval vm_compute in T_after PreCH C_czh s_czh R_czh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs.P_icpt.
Lemma T_czh_eq : ltac2:(tb__ "0|0|
S40S42S5aS9eS7aSc4Sa1S1d1A5Sa8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_Zh__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sa8S2A5").
Local Strategy expand [run_Zh__R].
Definition LV_Zh : list leafA := Eval vm_compute in ((fun ro17__ : option (list leafA) => (match ro17__ with Some l => l | None => [] end)) run_Zh__R).
Lemma run_Zh : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U3cS54Sa8S2A5S6G0Sd9A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_Zh__R <: run_Zh__R = Some LV_Zh). Qed.
Lemma LV_Zh_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57Sd9A1S0G0S7S4fS165S1a6S166A4S0G0S7S4fS165S19bS166A4S4G0A1A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition selbZ : list nat := ltac2:(tb__ "0|1|
ScS1S0S1U9S0S1U1S0S1U0S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U2S0S1U12S4S1A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU13U1cA2S0S1U3S0S1U2fS0S1U7S0S1U8S0S1U4S0S1U5S0S1U6G0A3A3A3A3A3A3A3A3A3").
Definition XF_bkza : list axform := ltac2:(tb__ "0|1|
S0S160S164S15bA1S0S160S163U1A1S0S160S163U2A1S0S160S162U0A1M0S0S160G0S4S160A1A3A3A3A3A3").

Definition bkz2 (r : sv) (cd cs : list cell) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184VSt;U27S70Vr;S8fVcs;A1A2A3").
Definition XF_bkzb : list axform := ltac2:(tb__ "0|0|
S0S160S162U9A1S0S160S162U26A1S4S160A1A3A3").
Definition bkzpipe (r : sv) (cd cs : list cell) (X : list (sv * sv)) (E : axst) : option axst := ltac2:(tb__ "0|4|
S3S42A1M0G0Lx;M1S161VE;S102A2S42G1S161S46R1S108Vr;Vcd;Vcs;S43R1A1M2A4A2S103A2S42S6S42S1bbS46R1S167G2S8eR1A1A2A2VX;A2A2LA3;SdS42A1M3X3x2LA1;G3X3x2").
Definition bkz_okb (r : sv) (cd cs : list cell) (X : list (sv * sv)) (E : axst) : bool := ltac2:(tb__ "0|7|
S3S42A1S5Lx;M0S161VE;S102A2S42S3S13A1S5Lx;M1S185S13S19S43R1A1A1M2U9A3S13G1S185S13S19S43R2A1A1U27A3S13SaSaSaS49R2S1bS16aS12Z0A1M3Vr;Vcd;S1aA5A2S49R1S1bS12S55A1G3Vr;Vcs;S1aA5A2A2S189S43R3A1M4S108Vr;Vcd;Vcs;G4A4M5A2A2G0S161S46R3G5A2S103A2S42SaSaS186S9S13S13A2M6G6S49SfS13S13R1A3S10S13S13R1A3A2Lp;S187S13S13S18cS13U29G2A3SbbA4A3S1bcSeS13G2A2U2cA2A2S1a9VX;S4aR1A1A2A2LA3;SbX3x2A2Lo';SbX3x2Lo;SbX3x2LA1;SbX3x2").

Definition LbZk : axst := Eval vm_compute in nthA S0f LV_Zk 0.
Definition BZku : axst := Eval vm_compute in ax_of (bkzpipe vRes0 [] [] X_R0 LbZk) LbZk.
Lemma bkzk_ok : ltac2:(tb__ "0|1|
S41S40S5Sb6S78S4S16A1M0G0S199SebA5S2A3S40S3S42A1Sb7S78G0G0S199SebA5S6S42ScbA2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_bkZk : wsub := Eval vm_compute in ([(42%positive, vRes0); (41%positive, SLit CAP0)] ++ infer_sub 1 (ax_S BZku) (ax_S R0c)).
Lemma ent_bkZk : ltac2:(tb__ "0|0|
S40S5S48ScbS62S159A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition hcD : list cell := ltac2:(tb__ "0|0|
S0S16S28S12Z0A1Z4S2aS2Q20S15P64A1A3A3S4S16A1A3").
Definition LbZh : axst := Eval vm_compute in nthA S0f LV_Zh 1.
Definition LgZh : axst := Eval vm_compute in nthA S0f LV_Zh 0.
Definition BZhu : axst := Eval vm_compute in ax_of (bkzpipe vResH hcD hcZ X_R0 LbZh) LbZh.
Definition E_mZ : axst := Eval vm_compute in ax_of (bkzpipe vResH hcD hcZ X_R0 LgZh) LgZh.
Lemma bkzh_ok : ltac2:(tb__ "0|1|
S41S40S5Sb6S5eS8dS63S199SeaA5S2A3S41S40S3S42A1M0Sb7S5eS8dS63S199SeaA5S6S42ScaA2A3S41S40S5Sb6S5eS8dS63S199Sf1A5S2A3S40G0Sb7S5eS8dS63S199Sf1A5S6S42SceA2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_bkZh : wsub := Eval vm_compute in ([(42%positive, vResH); (41%positive, SLit CAP0); (45%positive, SExt true 32 (SVar 100))] ++ infer_sub 1 (ax_S BZhu) (ax_S R1c)).
Lemma ent_bkZh : ltac2:(tb__ "0|0|
S40S5S48S19fS0S14S18S180S5eS12Z1A1A2S12S19aA1A2S4S14A1A3ScaA2S5fS158A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_mZG : axst := Eval vm_compute in
  ax_setS E_mZ (mkSS (ss_pc (ax_S E_mZ)) (list_set (ss_regs (ax_S E_mZ)) 19 (SLit CAP0))
                     (ss_fregs (ax_S E_mZ)) (ss_fcsr (ax_S E_mZ)) (ss_resv (ax_S E_mZ)) (ss_objs (ax_S E_mZ)) (ss_facts (ax_S E_mZ)) (ss_next (ax_S E_mZ)) (ss_lenient (ax_S E_mZ))).
Lemma E_mZG_diff : ltac2:(tb__ "0|7|
S41S40S3S9S8S9S11S11A2M0A1M1S8S14A1M2A2M3A1S18aS43SceA1M4S43ScfA1M5A2S6G3S7G1G2S0G0S7S11S11S5eS12S19aA1M6A4S4G0A1A3S4S14A1A4A2A3S41S40S5S1eG5A1S2A3S41S40S50S1cG5A1S1cG4A1A3S40S5S188S14S25S23S1bdS5eG6A3A1S1fG4A1A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_GZ : wsub := Eval vm_compute in ([(41%positive, SLit CAP0); (45%positive, SExt true 32 (SVar 100))] ++ infer_sub 1 (ax_S E_mZG) (ax_S G_cut)).
Lemma ent_GZ : ltac2:(tb__ "0|0|
S40S5S48ScfS61S153A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Lcl0 : axst := Eval vm_compute in nthA R0c LV_T0k 1.
Definition Hc0 : axst := Eval vm_compute in qpipe vWant X_R Lcl0.
Lemma q0_ok : ltac2:(tb__ "0|0|
S41S40S5SbcS58S59SedA3S2A3S40S42SbdS58S59SedA3S9aA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_c__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U28S54S81S2A5").
Local Strategy expand [run_c__R1].
Definition LV_c1 : list leafA := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) run_c__R1).
Definition run_c__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U28S54S9aS2A5").
Local Strategy expand [run_c__R2].
Definition LV_c0 : list leafA := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) run_c__R2).
Definition run_c__R3 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U28S54S9bS2A5").
Local Strategy expand [run_c__R3].
Definition LV_cZ : list leafA := Eval vm_compute in ((fun ro20__ : option (list leafA) => (match ro20__ with Some l => l | None => [] end)) run_c__R3).
Lemma run_c : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U28M2S54S81S2A5S6G0SdcA2A3S41S40G1S44S52G2S54S9aS2A5S6G0SdbA2A3S40G1S44S52G2S54S9bS2A5S6G0SddA2A3A2A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_c__R1 <: run_c__R1 = Some LV_c1) (conj (@eq_refl (option (list leafA)) run_c__R2 <: run_c__R2 = Some LV_c0) (@eq_refl (option (list leafA)) run_c__R3 <: run_c__R3 = Some LV_cZ))). Qed.
Lemma LV_c_pcs : ltac2:(tb__ "0|3|
S41S40S8S9S4fS165A2M0A1M1S57SdcA1S0G0S7S4fS165S1baS166A4S4G0A1A3M2A3S41S40G1S57SdbA1G2A3S40G1S57SddA1G2A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_cl1 : axst := Eval vm_compute in nthA R1c LV_c1 0.
Definition E_cl0 : axst := Eval vm_compute in nthA R0c LV_c0 0.
Definition E_clZ : axst := Eval vm_compute in nthA S0f LV_cZ 0.
Lemma E_cl_regs : ltac2:(tb__ "0|7|
S41S40S9S11S11A2M0S7S11S11S21S43S96A1M1Z11M2A2S21G1ZaM3A2A4S7S11S11S12Z39A1S12Z3A1A4M4A3S41S40G0S7S11S11S21S43S95A1M5G2A2S21G5G3A2A4G4A3S40G0S7S11S11S21S43S97A1M6G2A2S21G6G3A2A4G4A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_h__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U78S54S1a4S96S12Z0A1A2S2A5").
Local Strategy expand [run_h__R1].
Definition LV_h1 : list leafA := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) run_h__R1).
Definition run_h__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U78S54S1a4S95S12Z0A1A2S2A5").
Local Strategy expand [run_h__R2].
Definition LV_h0 : list leafA := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) run_h__R2).
Definition run_h__R3 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U78S54S1a4S97S12Z0A1A2S2A5").
Local Strategy expand [run_h__R3].
Definition LV_hZ : list leafA := Eval vm_compute in ((fun ro23__ : option (list leafA) => (match ro23__ with Some l => l | None => [] end)) run_h__R3).
Lemma run_h : ltac2:(tb__ "0|4|
S41S40S3S8S45A1M0A1M1S44S52U78M2S54S1a4S96S12Z0A1M3A2S2A5S6G0Se0A2A3S41S40G1S44S52G2S54S1a4S95G3A2S2A5S6G0SdfA2A3S40G1S44S52G2S54S1a4S97G3A2S2A5S6G0Se1A2A3A2A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_h__R1 <: run_h__R1 = Some LV_h1) (conj (@eq_refl (option (list leafA)) run_h__R2 <: run_h__R2 = Some LV_h0) (@eq_refl (option (list leafA)) run_h__R3 <: run_h__R3 = Some LV_hZ))). Qed.
Lemma LV_h_pcs : ltac2:(tb__ "0|5|
S41S40S8S9S4fS165A2M0A1M1S57Se0A1S0G0S7S4fS165S1b6S166A4M2S0G0S7S4fS165S1b4S166A4S0G0S7S4fS165S1a8S166A4S4G0A1M3A3A3A3A3S41S40G1S57SdfA1S0G0G2G3A3M4A3S40G1S57Se1A1G4A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Ltr : axst := Eval vm_compute in nthA R1c LV_h1 2.
Definition clen_x : sv := Eval vm_compute in nth 11 (ss_regs (ax_S Ltr)) (SLit 0).
Definition plen_x : sv := Eval vm_compute in nth 13 (ss_regs (ax_S Ltr)) (SLit 0).
Definition flg_x : sv := Eval vm_compute in nth 21 (ss_regs (ax_S Ltr)) (SLit 0).

Definition setregA (A : axst) (k : nat) (v : sv) : axst := ltac2:(tb__ "0|1|
S46VA;S24S1dS43VA;A1M0A1S169S11S22G0A1Vk;Vv;A4S3cG0A1S3bG0A1S3eG0A1S19G0A1S1fG0A1S1cG0A1S3dG0A1A9A2").
Definition LtrR : axst := Eval vm_compute in setregA Ltr 23 (SLit 0).
Lemma LtrR_diff : ltac2:(tb__ "0|7|
S41S40S3S9S8S9S11S11A2M0A1M1S8S14A1M2A2M3A1S18aS43SfaA1M4S43S9dA1M5A2S6G3S7G1G2S0G0S7S11S11S5dS12Z0A1M6A4S4G0A1A3S4S14A1A4A2A3S41S40S5S1eG5A1S2A3S41S40S50S1cG5A1S1cG4A1A3S41S40S5S188S14S25S2cS23S1c2S5dG6A3A1A1S1fG4A1A3S2A3S40S42S15fSfaU17G6A3S9dA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_T : wsub := Eval vm_compute in
  ([(43%positive, clen_x); (44%positive, plen_x); (46%positive, flg_x)] ++ infer_sub 1 (ax_S LtrR) (ax_S S_T)).

Lemma ent_T : ltac2:(tb__ "0|0|
S40S5S48S19fS0S14S18S137S12Z7fffA1A2S4S14A1A3S9dA2S17dS155A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Loom : axst := Eval vm_compute in nthA G_cut LV_Gnull 0.
Definition run_oom__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf2S2A5").
Local Strategy expand [run_oom__R].
Definition LV_oom : list leafA := Eval vm_compute in ((fun ro24__ : option (list leafA) => (match ro24__ with Some l => l | None => [] end)) run_oom__R).
Lemma run_oom : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U14S54Sf2S2A5S6G0Se3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_oom__R <: run_oom__R = Some LV_oom). Qed.
Lemma LV_oom_pcs : ltac2:(tb__ "0|4|
S40S8S9S9S4fS165A2M0S8S11A1M1A2M2A1S18bS45G2S45S7G0G1S7S4fS165S1dS43S47R1A1A1M3A1S4dR1A1A4S18eS11U4S18cS11UaS22G3A1A3A3A4LL;Se3A4S0G2S7G0G1S7S4fS165S1b0S166A4S0S11S12Z14d77A1S0S11S12Z13A1S0S11S12Z1A1S0S11S12S1c3A1S4S11A1A3A3A3A3A4S4G2A1A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run_ref__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S9cS2A5").
Local Strategy expand [run_ref__R].
Definition LV_ref : list leafA := Eval vm_compute in ((fun ro25__ : option (list leafA) => (match ro25__ with Some l => l | None => [] end)) run_ref__R).
Lemma run_ref : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U14S54S9cS2A5S6G0Se5A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_ref__R <: run_ref__R = Some LV_ref). Qed.
Lemma LV_ref_pcs : ltac2:(tb__ "0|4|
S40S8S9S9S4fS165A2M0S8S11A1M1A2M2A1S18bS45G2S45S7G0G1S7S4fS165S1dS43S47R1A1A1M3A1S4dR1A1A4S18eS11U3S18cS11UaS22G3A1A3A3A4LL;Se5A4S0G2S7G0G1S7S4fS165S1c6S166A4S0S11S12S1c3A1S0S11S12Z1a7edA1S0S11S12Z4000000A1S4S11A1A3A3A3A4S4G2A1A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Lsh1 : axst := Eval vm_compute in nthA R1c LV_h1 0.
Definition Lov1 : axst := Eval vm_compute in nthA R1c LV_h1 1.
Definition Lsh0 : axst := Eval vm_compute in nthA R0c LV_h0 0.
Definition LshZ : axst := Eval vm_compute in nthA S0f LV_hZ 0.
Definition run_sh__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf8S2A5").
Local Strategy expand [run_sh__R1].
Definition LV_sh1 : list leafA := Eval vm_compute in ((fun ro26__ : option (list leafA) => (match ro26__ with Some l => l | None => [] end)) run_sh__R1).
Definition run_sh__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf3S2A5").
Local Strategy expand [run_sh__R2].
Definition LV_ov1 : list leafA := Eval vm_compute in ((fun ro27__ : option (list leafA) => (match ro27__ with Some l => l | None => [] end)) run_sh__R2).
Definition run_sh__R3 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf7S2A5").
Local Strategy expand [run_sh__R3].
Definition LV_sh0 : list leafA := Eval vm_compute in ((fun ro28__ : option (list leafA) => (match ro28__ with Some l => l | None => [] end)) run_sh__R3).
Definition run_sh__R4 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf9S2A5").
Local Strategy expand [run_sh__R4].
Definition LV_shZ : list leafA := Eval vm_compute in ((fun ro29__ : option (list leafA) => (match ro29__ with Some l => l | None => [] end)) run_sh__R4).
Lemma run_sh : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U14M2S54Sf8S2A5S6G0Se7A2A3S41S40G1S44S52G2S54Sf3S2A5S6G0Se4A2A3S41S40G1S44S52G2S54Sf7S2A5S6G0Se6A2A3S40G1S44S52G2S54Sf9S2A5S6G0Se8A2A3A2A2A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_sh__R1 <: run_sh__R1 = Some LV_sh1) (conj (@eq_refl (option (list leafA)) run_sh__R2 <: run_sh__R2 = Some LV_ov1) (conj (@eq_refl (option (list leafA)) run_sh__R3 <: run_sh__R3 = Some LV_sh0) (@eq_refl (option (list leafA)) run_sh__R4 <: run_sh__R4 = Some LV_shZ)))). Qed.
Lemma LV_sh_pcs : ltac2:(tb__ "0|5|
S40S8S9S4fS8S11A1M0A2M1A1S18bS45G1S45S7S4fG0S1dS43S47R1A1A1M2A1S18eS11U4S18cS11UaS22G2A1A3A3A4LL;ScS45Se7ScS45Se4ScS45Se6Se8A3A3A3A4S0G1S7S4fG0S1b0S0S11S12Z21441A1S0S11S12Z1fA1S0S11S12Z1A1S0S11S12S1c3A1S4S11A1A3A3A3M3A3A4M4S0G1S7S4fG0S1b0S0S11S12Z1609eA1G3A3A4S0G1G4S0G1G4S4G1A1A3A3A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

End DrvR_states.

(* [comment removed for export] *)
Module DrvSiteEx.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "True"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_facts"; "sobj"; "ss_next"; "sstate"; "SLit"; "ss_objs"; "sprop"; "holds"; "ss_lenient"; "sprop_eqb"; "DUnknown"; "SPUle"; "cell"; "mkObj"; "SPEq"; "agree_below"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "nil"; "option"; "Some"; "cons"; "pair"; "app"; "nat"; "false"; "length"; "fst"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_base"; "sym_runA"; "mkAX"; "mkLeafA"; "ax_setS"; "la_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "ExitEv"; "FdChannel"; "WriteEv"; "fd_lookup"; "m_fds"; "m_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "w_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit"; "ch1"; "supported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "FERR"; "PEND"; "Pre_exit"; "Pre_exitP"; "supportedP"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "le"; "lt"; "opp"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_tv"; "ANone"; "NDA"; "nd_below"; "ndesc"; "tvinA"; "JA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vB"; "vCap"; "PreF"; "s_fb"; "PostF"; "vTP"; "CUTS_X"; "DEEP"; "FUEL_X"; "N_ex"; "O_deepM"; "O_deepS"; "dropX"; "s_ex"; "spM"; "spT"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "cls_kept_freeA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "sp0_factsb"; "drv_xrb"; "robjs_checkD"; "xrs_checkD"; "ex_pipe"; "fb_pipe"; "HKP_K"; "HKV_K"; "site_ok_drv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "BX0"; "KP_T"; "KV_T"; "CST_drv"; "HKVrng_T"; "SH0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "JAK"; "carve_okb"; "lcarve"; "JA_carve"; "lc_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep";
"RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "tnz"; "tvd"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "KU"; "bd_below"; "bitem"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "alloc_contractsA_ex"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section SITE.
Variable AInv : ltac2:(tb__ "0|0|
S71S7S21S46Q40A1A1S3bOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S2dS8fVCST;R1A2S1S55Z0R2A2S56R2SabA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2dS8fVXGL;R1A2S1S55Z0R2A2S56R2SabA2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S2dS8fS88R1A2S8fVCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sb3S2fSb1VAInv;VCST;VXGL;A5").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Hypothesis HP0SH : ltac2:(tb__ "0|0|
S7VP0f;R1A1S8aR2A1F_;Fr;").
Variable PA : AA -> Prop.
Hypothesis HPAf : ltac2:(tb__ "0|0|
S71S71VPA;R2A1S72R3R2A2VPA;R3A1F_;F_;FA';FA;").

Let JK (nd : ndesc) : jpredA := ltac2:(tb__ "0|1|
S5fVAInv;VCST;VXGL;S48VKc;Vrho0;VP0f;S23S22S2dS2dA2M0A1S23S22G0S2dA2A1S85VPA;Vnd;Ac").
Let carveK : ltac2:(tb__ "0|3|
Sb2S5dS31S7S21S46Q40A1A1S4aS21S94A1S2eS43S2fS92VAInv;VCST;VXGL;S48Vrho0;VP0f;S23S22S2dS2dA2M0A1M1S23S22G0S2dA2A1M2S85VPA;R8R7AcR6R5R4R3A6S30R7A1SbS18S1bR1A1S1cR1A1S1aR1A1S19R1A1S1dR1A1S28S9SdR1A1S73S94S9S96R4A4A3S8R1A1R3S10R1A1A9SbS0S1fS1eR1A1S20A3S0S1fS70SaR3A1R5A2S20A3S0S6S34RbA1ScSacA1A3S0S1fS93S8R5A1SdR5A1S33RcA1S87S86S59RdA1R8A7S20A3S43S2fS92VAInv;VCST;VXGL;S48Vrho0;VP0f;G1G2S85VPA;RfReAcS38RdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
S95VAInv;VCST;VXGL;VALA;S48Vrho0;VP0f;S23S22S2dS2dA2M0A1S23S22G0S2dA2A1S85VPA;S87S7cVAInv;VCST;VXGL;VALA;VHCSTdrv;VHLPP;VKc;Vrho0;VP0f;VHP0SH;VPA;VPA;AcS89S86S7bVAInv;VCST;VXGL;VHCSTdrv;VKc;Vrho0;VP0f;VHP0SH;VPA;VPA;AaA10").
Let site_ok_drv := site_ok_drv AInv CST XGL ALA HCSTdrv rho0 P0f.

Lemma JK_erun : ltac2:(tb__ "0|1|
S5dS29S21S2dA1S31S21S32A1M0S7S21S46Q40A1A1S4aOF_;S0S24G0A1S35S2fR7R6R5S20A5S25G0R4A2A3S0S1fS10S30R6A1A1S2aA3S0S1fS70S48SaS30R7A1A1A2S20A3S0S1fS5cSaS30R8A1A1RbA2S20A3S32S7S82S32R2RaA3S17SaS30RcA1A1RaR2A3S49S2fS43S2fVJK;R10A1S39R4A1R3RaA5R9A3F_;F_;Frho';FL;S49S2fS43S2fVJK;RdA1RaR8R7A5R6A3F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;Fnd;").
Proof.
  intros nd fuel cuts A leaves rho tp Q Hrun Hlen Hnf Hnb H. apply Pos.leb_le in Hnf.
  exact (erunA_tr segs fuel cuts A leaves (JK nd) rho tp Q Hrun Hlen (JK_stable AInv CST XGL ALA Kc HKc rho0 P0f PA nd _ Hnf Hnb) H).
Qed.

Lemma final_callJ_ex : ltac2:(tb__ "0|4|
S5dS31S31S8cS21S9A1M0S7S21S46Q40A1A1M1S44S7G1S4aOF_;M2F_;F_;G2S7G1S49S2fS43S2fR5RaR2R1A5R4R2R1A2A3Ftp1;Frho1;S0S24G0A1S7eRaR9R8A3S25G0R7A2A3S21S3aA1M3S90S3bS45S2fRaR9ReS27G3SadR3SaeR2R1A2A4A5VJK;R10RbRaR4R2A5RaS8eS8dRcRdSb0R3RbR4A3A3ReA2RbR5R3A4F_;F_;Fmd;Fms;Ftr;S7S4aR7R2R9R1A3R7R2A1F_;Fw;Frho1;S49S2fS43S2fVJK;ReA1RdR9R8A5R5A3F_;F_;F_;F_;FQ;FQc;FJp;Ftp;Frho;FR;Fs;FPre;FCl;Fnd;").
Proof.
  intros nd Cl Pre s R rho tp Jp Qc Q Hsum He HIN HQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (HIN tr ms md Hsm Hk))) as (w' & Hsteps & HQc).
  exists w'. split; [exact Hsteps | exact (HQ _ _ HQc)].
Qed.

Section ExitCallEx.
Variable ph : bool.
Variable ndX : ndesc.
Variables n c : Z.
Variable CX : axst.
Variable s : wsub.
Variable R : list sobj.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1fS70S48SaS30VCX;A1A1A2S20A3").
Hypothesis Hnb : ltac2:(tb__ "0|0|
S0S1fS5cSaS30VCX;A1A1VndX;A2S20A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S24S21S9A1M0A1S7eVCX;S51Vph;Vn;Vc;A3Vs;A3S25G0VR;A2A3").
Hypothesis Hsupp : ltac2:(tb__ "0|0|
S82S22S2dS2dA2S27S2dS2dVn;Vc;A4S52Vph;A1A3").
Hypothesis HKfd1 : ltac2:(tb__ "0|0|
S21S3aA1S3bVKc;R2R1A2S0S24S3cA1S40S41R2A1S4cA2S25S3cS3eS4cA1A2A3F_;Fmd;Ftr;").

Variable Q : world -> Prop.
Hypothesis HQ : ltac2:(tb__ "0|1|
S4aS21S3aA1M0S3bVKc;R2R1A2S0G0S4bR4A1S28S3aR3S28S3aS73S46Q8A1S3aS3fS4cA1S4fVn;A1A4S26S3aS3dS47Q40Vc;A2S42R2A1A2S23S3aA1A3A3A3A3VQ;R5A1F_;F_;Fmd;Ftr;Fw;").

Lemma X_exit_call_ex : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndX;A1VCX;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. pose proof Hnx as Hnx'. apply Pos.leb_le in Hnx'.
  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JK ndX rho t tr md).
  assert (JpK : forall r t tr md, Jp r t tr md -> Kc tr md) by (intros r t tr md HJ; exact (JK_Kc AInv CST XGL Kc rho0 P0f PA ndX _ _ _ _ HJ)).
  apply (final_callJ_ex ndX CX (Pre_exitP ph n c) s R rho tp Jp
           (fun rho1 tp1 w' => exists tr md, Jp rho1 tp1 tr md /\ w_tr w' = tr ++ map (WriteEv ch1) (PEND n) ++ [ExitEv (Z_to_bv 64 c) (m_fs md)])).
  - intros rho1 tp1. apply (exit_sumP_ex Jp n c) with (ph := ph); [| | exact Hsupp].
    + intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *.
      destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF Kc rho0 P0f [] [] BX0 PA HKc ALA (ss_next (ax_S CX)) ndX Ai kc rho rho t tr md md');
        [exact Hnx' | exact Hnb | apply agree_below_refl | exact Hme | exact HJi].
    + intros r t tr md HJ. apply (HKfd1 tr md). exact (JpK _ _ _ _ HJ).
  - exact Hfr.
  - intros tr ms md Hsm HJ. exact HJ.
  - intros rho1 w (tr & md & HJ & Hw). exact (HQ w tr md (JpK _ _ _ _ HJ) Hw).
Qed.
End ExitCallEx.

Section ExitHandoffEx.
Variable ndX : ndesc.
Variables n c : Z.
Variable E : axst.
Variables S1 S4 S5 S6 : sstate.
Variable idxs : list nat.
Variable R : list sobj.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1fS70S48SaS30VE;A1A1A2S20A3").
Hypothesis Hnb : ltac2:(tb__ "0|0|
S0S1fS5cSaS30VE;A1A1VndX;A2S20A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S6S34VE;A1ScSacA1A3").
Variable iw : nat.
Hypothesis H1n : ltac2:(tb__ "0|0|
S0S24S9A1S84S9SdS30VE;A1A1Viw;A3S25S9S15S6eScS57S67A1A1ScZ0A1S23S14A1S12A5A2A3").
Variable S0 : sstate.
Hypothesis H1e : ltac2:(tb__ "0|0|
S0SbSa7S30VE;A1Viw;S6bA3VS0;A3").
Hypothesis H1s : ltac2:(tb__ "0|0|
S0S1fS97S30VE;A1VS0;A2S20A3").
Variable ie : nat.
Let S0a : ltac2:(tb__ "0|0|
Sb") := ltac2:(tb__ "0|0|
S80VS0;Vie;S53S4eZ8cA2Z4S54S58Z2Z20A2Z1A2A5").
Let S0b : ltac2:(tb__ "0|0|
Sb") := ltac2:(tb__ "0|0|
S80VS0a;Vie;S53S4eZ10A2Z8Z0A5").
Let S0c : ltac2:(tb__ "0|0|
Sb") := ltac2:(tb__ "0|1|
S80VS0b;Vie;S53S4eZ8M0A2G0Z0A5").
Let S0d : ltac2:(tb__ "0|0|
Sb") := ltac2:(tb__ "0|0|
S80VS0c;Vie;S53S4eZ38A2Z8Z0A5").
Hypothesis H1i : ltac2:(tb__ "0|2|
S1S0S1fS81S2fVS0;Vie;S53S4eZ8cA2Z4S54S58Z2Z20A2Z1A2A6S20A3S1S0S1fS81S2fVS0a;Vie;S53S4eZ10A2Z8M0Z0M1A6S20A3S1S0S1fS81S2fVS0b;Vie;S53S4eG0A2G0G1A6S20A3S1S0S1fS81S2fVS0c;Vie;S53S4eZ38A2G0G1A6S20A3S0S1fS81S2fVS0d;Vie;S53S4eZ28A2G0G1A6S20A3A2A2A2A2").
Hypothesis H1j : ltac2:(tb__ "0|0|
S0SbS80VS0d;Vie;S53S4eZ28A2Z8Z0A5VS1;A3").
Hypothesis H2 : ltac2:(tb__ "0|0|
S0S1fS9eS2bS9SdVS1;A1A2Vidxs;A2S20A3").
Hypothesis H3 : ltac2:(tb__ "0|0|
S0S24SbA1S9aS9dVS1;S99SdVS1;A1Vidxs;A2A2U0A2S25SbVS4;A2A3").
Hypothesis H4 : ltac2:(tb__ "0|0|
S0S24SbA1S9bVS4;U0ScN430A1A3S25SbVS5;A2A3").
Let S5c := ex_S5c E S5.
Hypothesis H5n : ltac2:(tb__ "0|0|
S0S2eSaVS5;A1SaS30VE;A1A1A3").
Hypothesis H5w : swf S5c = true.
Hypothesis H5c : ltac2:(tb__ "0|0|
S0S1fS93S8VS5;A1SdVS5;A1S23S22S6S6A2A1S87S86S59VndX;A1S69A7S20A3").
Hypothesis H6e : ex_S6 S5c = S6.
Hypothesis H6w : swf S6 = true.
Variable d6 : list (sv * sv).
Hypothesis H6d : ltac2:(tb__ "0|3|
S0S24S22S21S22S6S6A2A1M0S21SeA1M1A2M2A1S98VS5c;VS6;A2S25G2S27G0G1Vd6;S23SeA1A4A2A3").
Hypothesis H6v : ltac2:(tb__ "0|4|
S5S0S21S22S6S6A2M0A1M1Vd6;S26G0S27S6S6S65ScS91A1M2A4S23G0A1M3A3A3S0G1Vd6;S26G0S27S6S6G2S65A4G3A3A3A2").
Hypothesis H6f : ltac2:(tb__ "0|0|
S0S1fS83SeS11S16S65ScS91A1A2A1S8S30VE;A1A1A3S20A3").
Let CX : axst := ltac2:(tb__ "0|0|
S36VS6;S23S22S6S6A2A1S34VE;A1A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S24S21S9A1M0A1S7eVCX;S50Vn;Vc;A2S6dVCX;Vn;Vc;A3A3S25G0VR;A2A3").
Hypothesis Hsupp : ltac2:(tb__ "0|0|
S82S22S2dS2dA2S27S2dS2dVn;Vc;A4S4dA3").
Hypothesis HKfd1 : ltac2:(tb__ "0|0|
S21S3aA1S3bVKc;R2R1A2S0S24S3cA1S40S41R2A1S4cA2S25S3cS3eS4cA1A2A3F_;Fmd;Ftr;").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S1fS75S8S30VE;A1A1A1S20A3").
Variable Q : world -> Prop.
Hypothesis HQ : ltac2:(tb__ "0|1|
S4aS21S3aA1M0S3bVKc;R2R1A2S0G0S4bR4A1S28S3aR3S28S3aS73S46Q8A1S3aS3fS4cA1S4fVn;A1A4S26S3aS3dS47Q40Vc;A2S42R2A1A2S23S3aA1A3A3A3A3VQ;R5A1F_;F_;Fmd;Ftr;Fw;").

Lemma exit_reshape : ltac2:(tb__ "0|1|
S7S21S46Q40A1A1S4aS74SeSfR3A1S8S30VE;A1A1A3S43S2fVJK;VndX;A1M0VE;R4R3R2A6S43S2fG0VCX;R5R4R3A6F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HF HS.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }
  assert (Htp : eval rho vTP = eval rho (SLit TP)).
  { pose proof (holds_mem _ _ _ HF H6f) as X. cbn [holds] in X. exact X. }
  assert (HS0 : SPA segs (JK ndX) (ax_setS E S0) rho tp w).
  { rewrite <- H1e. apply (SPA_reslice segs (JK ndX) rho E iw _ O_deepS tp w H1n); try reflexivity.
    - rewrite H1e. exact H1s.
    - unfold O_deepS, spM. rewrite !obj_range_lits by (unfold DEEP; lia). rewrite U_add_lit by lia. unfold DEEP. f_equal; lia.
    - unfold O_deepS, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia.
    - exact HS. }
  destruct H1i as (I1 & I2 & I3 & I4 & I5).
  assert (HS1 : SPA segs (JK ndX) (mkAX S1 (ax_X E) (ax_base E)) rho tp w).
  { rewrite <- H1j.
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0d (ax_X E) (ax_base E)) ie _ 8 0 tp w I5).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0c (ax_X E) (ax_base E)) ie _ 8 0 tp w I4).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0b (ax_X E) (ax_base E)) ie _ 8 0 tp w I3).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0a (ax_X E) (ax_base E)) ie _ 8 0 tp w I2).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0 (ax_X E) (ax_base E)) ie _ 4 _ tp w I1). exact HS0. }
  pose proof (AxXform.SPA_select segs (JK ndX) rho (mkAX S1 (ax_X E) (ax_base E)) idxs tp w H2 HS1) as HS2.
  pose proof (SPA_merge segs (JK ndX) rho (mkAX (set_objs S1 (select (ss_objs S1) idxs)) (ax_X E) (ax_base E)) 0 S4 tp w H3 HS2) as HS3.
  pose proof (SPA_split segs (JK ndX) rho (mkAX S4 (ax_X E) (ax_base E)) 0 (SLit (-1072)) S5 tp w H4 HS3) as HS4.
  apply (SPA_x_sub segs (JK ndX) rho (mkAX S5 (ax_X E) (ax_base E)) [] tp w ltac:(intros rr Hrr; destruct Hrr)) in HS4.
  change (ax_setX (mkAX S5 (ax_X E) (ax_base E)) []) with (mkAX S5 [] (ax_base E)) in HS4.
  assert (HS5 : SPA segs (JK ndX) (mkAX S5c [] (ax_base E)) rho tp w).
  { pose proof (carveK Kc ndX (mkAX S5 [] (ax_base E)) rho tp w N_ex (ss_next S5) HS4) as X.
    cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X.
    - exact H5w.
    - apply Pos.leb_refl.
    - exact HbE.
    - exact H5c. }
  assert (HS6 : SPA segs (JK ndX) (mkAX S6 [] (ax_base E)) rho tp w).
  { change (mkAX S6 [] (ax_base E)) with (ax_setS (mkAX S5c [] (ax_base E)) S6).
    apply (SPA_restate segs (JK ndX) rho (mkAX S5c [] (ax_base E)) S6 tp w d6 [] H6w H6d).
    - rewrite <- H6e. reflexivity.
    - unfold diffs_ok. destruct H6v as [-> | ->]; (constructor; [cbn [fst snd] | constructor]); [exact Htp | symmetry; exact Htp].
    - constructor.
    - exact HS5. }
  unfold CX. exact HS6.
Qed.

Lemma X_exit_ex : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndX;A1VE;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. apply etriple_factsA. intros HF.
  assert (HnxC : ss_next (ax_S CX) = ss_next (ax_S E)).
  { unfold CX. cbn [ax_S]. rewrite <- H6e. cbn [ss_next ex_S6]. exact H5n. }
  eapply (etriple_conseq (P := SPA segs (JK ndX) CX rho tp)); [intros w HS; exact (exit_reshape rho tp w HF HS) | intros w' Hw'; exact Hw' |].
  apply (X_exit_call_ex true ndX n c CX (s_ex CX n c) R); [rewrite HnxC; exact Hnx | rewrite HnxC; exact Hnb | exact Hfr | exact Hsupp | exact HKfd1 | exact HQ].
Qed.
End ExitHandoffEx.

Lemma X_exit_pipe_ex : ltac2:(tb__ "0|4|
S5dS2dS2dS31S21S9A1M0S4aOF_;S0S24G0A1S79R6R3R5R4A4S25G0R2A2A3S82S22S2dS2dA2S27S2dS2dR6R5A4S4dA3S21S3aA1M1S3bVKc;R2R1A2M2S0S24S3cA1S40S41R2A1S4cA2S25S3cS3eS4cA1A2A3F_;Fmd;Ftr;S4aG1S3bG2S0G1S4bR4A1S28S3aR3S28S3aS73S46Q8A1S3aS3fS4cA1S4fRcA1A4S26S3aS3dS47Q40M3RbA2S42R2A1A2S23S3aA1A3A3A3A3R9R5A1F_;F_;Fmd;Ftr;Fw;S7S21S46G3A1A1S49S2fS43S2fVJK;RcA1R9R2R1A5R7A3Ftp;Frho;F_;F_;F_;F_;FQ;FR;FE;Fc;Fn;FndX;").
Proof.
  intros ndX n c E R Q Hp Hsupp HKfd1 HQ rho tp. unfold ex_pipe in Hp. cbv zeta in Hp.
  destruct (nth_error (ss_objs (ax_S E)) (locate (ss_objs (ax_S E)) spM (SLit (- DEEP)))) as [o|] eqn:E1; [|discriminate].
  destruct (ob_shapeb o spM (SLit (- DEEP)) (SLit 0)) eqn:E2; [|discriminate]. apply ob_shapeb_sound in E2. subst o.
  destruct (same_but_objs _ _) eqn:E3; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:EI; [|discriminate] end.
  apply andb_prop in EI as [EI I5]. apply andb_prop in EI as [EI I4]. apply andb_prop in EI as [EI I3]. apply andb_prop in EI as [I1 I2].
  destruct (select_ok _ _) eqn:E4; [|discriminate].
  destruct (merge_objs_at _ 0) as [S4|] eqn:E5; [|discriminate].
  destruct (split_obj_at S4 0 (SLit (-1072))) as [S5|] eqn:E6; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E7; [|discriminate] end.
  destruct (entails_frA _ _ _) as [R'|] eqn:E8; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E9; [|discriminate] end. injection Hp as HR. subst R'.
  apply andb_prop in E9 as [E9 E10].
  apply andb_prop in E7 as [E7 E7j]. apply andb_prop in E7 as [E7 E7i]. apply andb_prop in E7 as [E7 E7h]. apply andb_prop in E7 as [E7 E7g].
  apply andb_prop in E7 as [E7 E7f]. apply andb_prop in E7 as [E7 E7e]. apply andb_prop in E7 as [E7 E7d]. apply andb_prop in E7 as [E7 E7c].
  apply andb_prop in E7 as [E7a E7b].
  destruct (state_diff (ex_S5c E S5) (ex_S6 (ex_S5c E S5))) as [[d6 [|]]|] eqn:E11; try discriminate.
  apply Pos.eqb_eq in E7a. apply sv_eqb_sound in E7j.
  eapply (X_exit_ex ndX n c E _ S4 S5 (ex_S6 (ex_S5c E S5)) _ R E7h E7i E7j _ E1 _ eq_refl E3 _ (conj I1 (conj I2 (conj I3 (conj I4 I5)))) eq_refl
            E4 E5 E6 E7a E7b E7c eq_refl E7d d6 E11 (d6_okb_sound d6 E7e) E7f E8 Hsupp HKfd1 E7g Q HQ).
Qed.

Section FreeCallEx.
Variables tb tl : sv.
Let t : sv * sv := ltac2:(tb__ "0|0|
S27S6S6Vtb;Vtl;A4").
Variable kept : list (sv * sv).
Variables bdJ bdX : list bitem.
Let ndJ : ndesc := ltac2:(tb__ "0|0|
S5bS26S22S6S6A2Vt;Vkept;A3S23S22S22S6S2dA2S6A2A1VbdJ;S5aA4").
Let ndX : ndesc := ltac2:(tb__ "0|0|
S5bVkept;S23S22S22S6S2dA2S6A2A1VbdX;S5aA4").
Variables (CF : axst) (s : wsub) (R : list sobj) (T : axst).
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S24S21S9A1M0A1S7eVCF;S62Vs;A3S25G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S1fS7fVCF;S62Vs;VR;S26S31S64S23S31A1A3A5S20A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S1fSa9S48Vs;A2S20A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1fS70S48SaS30VCF;A1A1A2S20A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S1fS5cSaS30VCF;A1A1M0VndJ;A2S20A3S0S1fSa4G0VbdX;A2S20A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|0|
S1S0S6S8bVs;PcA2Vtb;A3S0S6S8bVs;PdA2Vtl;A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S0S1fSa6S8S30VCF;A1A1ScZ0A1Sa3VbdJ;VbdX;A5S20A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S1fS75S8S30VCF;A1A1A1S20A3").
Hypothesis Hro : ltac2:(tb__ "0|0|
S0S1fS77S8S30VCF;A1A1S26S22S6S6A2Vt;Vkept;A3S25S29U0A2VR;A4S20A3").
Hypothesis Hxr : ltac2:(tb__ "0|1|
S0S1fS78S8S30VCF;A1M0A1S26S22S6S6A2Vt;Vkept;A3S25S29U0A2SdG0A1S76S33VCF;A1A6S20A3").
Hypothesis Hnz : ltac2:(tb__ "0|0|
S0S1fS83SeS11S13ScZ1000A1Vtb;A2A1S8S30VCF;A1A1A3S20A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S31Sa8S62VCF;Vs;VR;S64A5VT;A3").
Variable Q : world -> Prop.
Hypothesis HT' : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndX;A1VT;R2R1A5VQ;A3Ftp';Frho';").

Lemma X_free_call_ex : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndJ;A1VCF;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct Hs12 as [Hs12a Hs13].
  apply etriple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact Hspf]. }
  assert (Htnz : tnz rho t).
  { unfold tnz, t. cbn [fst]. pose proof (holds_mem _ _ _ HF Hnz) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
    rewrite Z.mod_small in X by lia. unfold uval in X |- *. lia. }
  apply (free_callA_ex segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0f [] [] BX0 PA HKc [] UStopLe CF s R rho tp
           ndJ 0%nat t bdX Q free_shape_nil ACX Hfr Hcc HcT Hnx Hnb1 Hnb2 eq_refl).
  - apply payA_of_bud_pay. exact Hpay.
  - exact HPAf.
  - apply (site_ok_drv ndJ CF s R rho (Some 0%nat) (Some (uval rho (wsub_get s 12%positive)))); try assumption.
    + intros Ai HF' HN HZ. exists t. split; [reflexivity|]. rewrite Hs12a. split; [exact Htnz | reflexivity].
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. split; [|split; [| exact I]].
      * exact Htnz.
      * rewrite Hs12a, Hs13. reflexivity.
  - intros rho' tp'. unfold PreF, PostF in HT. rewrite HT. cbn [nd_tv nd_fr nd_am ndJ remove_nth]. fold ndX. apply HT'.
Qed.
End FreeCallEx.

Section FbChainEx.
Variable A0 : axst.
Variable bdJ bdX : list bitem.
Let ndJ' : ndesc := ltac2:(tb__ "0|1|
S5bS26S22S6S6A2M0S27S6S6S60S61A4S23G0A1A3S23S22S22S6S2dA2S6A2A1VbdJ;S5aA4").
Let ndX' : ndesc := ltac2:(tb__ "0|0|
S5bS23S22S6S6A2A1S23S22S22S6S2dA2S6A2A1VbdX;S5aA4").
Variables (E : axst) (S2 S4 : sstate) (idxs : list nat) (R : list sobj) (T Ex : axst).
Variable iw : nat.
Hypothesis HJwf : ltac2:(tb__ "0|2|
S1S0S1fS70S48SaS30VA0;A1M0A1M1A2S20A3S1S0S1fS10G0A1S2aA3S0S1fS5cG1VndJ';A2S20A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0S24S21S32A1M0A1S35S2fS68S66VA0;S20A5S25G0S26S32S37VE;S9cA2S23S32A1A3A2A3").
Hypothesis H1n : ltac2:(tb__ "0|0|
S0S24S9A1S84S9SdS30VE;A1A1Viw;A3S25S9S15S6fScS57S54S67Z50A2A1A1ScZ0A1S23S14A1S12A5A2A3").
Hypothesis H1e : ltac2:(tb__ "0|0|
S0SbSa7S30VE;A1Viw;S6aA3VS2;A3").
Hypothesis H1s : ltac2:(tb__ "0|0|
S0S1fS97S30VE;A1VS2;A2S20A3").
Hypothesis H2 : ltac2:(tb__ "0|0|
S0S1fS9eS2bS9SdVS2;A1A2Vidxs;A2S20A3").
Hypothesis H3 : ltac2:(tb__ "0|0|
S0S24SbA1S9aS9dVS2;S99SdVS2;A1Vidxs;A2A2U0A2S25SbVS4;A2A3").
Let CF : axst := ltac2:(tb__ "0|0|
S6cS27S6S6S60S61A4S36VS4;S33VE;A1S34VE;A1A3A2").
Hypothesis H4n : ltac2:(tb__ "0|0|
S0S2eSaVS4;A1SaS30VE;A1A1A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S24S21S9A1M0A1S7eVCF;S62S63VCF;A1A3S25G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S1fS7fVCF;S62S63VCF;A1VR;S26S31S64S23S31A1A3A5S20A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S1fSa9S48S63VCF;A1A2S20A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1fS70S48SaS30VE;A1A1A2S20A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S1fS5cSaS30VE;A1A1M0VndJ';A2S20A3S0S1fSa4G0VbdX;A2S20A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|1|
S1S0S6S8bS63VCF;A1M0PcA2S60A3S0S6S8bG0PdA2S61A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S0S1fSa6S8S30VCF;A1A1ScZ0A1Sa3VbdJ;VbdX;A5S20A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S1fS75S8S30VE;A1A1A1S20A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S1fS75S8S30VCF;A1A1A1S20A3").
Hypothesis Hro : ltac2:(tb__ "0|1|
S0S1fS77S8S30VCF;A1A1S26S22S6S6A2M0S27S6S6S60S61A4S23G0A1A3S25S29U0A2VR;A4S20A3").
Hypothesis Hxr : ltac2:(tb__ "0|2|
S0S1fS78S8S30VCF;A1M0A1S26S22S6S6A2M1S27S6S6S60S61A4S23G1A1A3S25S29U0A2SdG0A1S76S33VCF;A1A6S20A3").
Hypothesis HvB : ltac2:(tb__ "0|0|
S0S1fS83SeS11S13ScZ1000A1S60A2A1S8S30VCF;A1A1A3S20A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S31Sa8S62VCF;S63VCF;A1VR;S64A5VT;A3").
Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S1fS70S48SaS30VT;A1M0A1M1A2S20A3S1S0S1fS10G0A1S2aA3S0S1fS5cG1VndX';A2S20A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0S24S21S32A1M0A1S35S2fS68S66VT;S20A5S25G0S26S32S37VEx;S9cA2S23S32A1A3A2A3").
Variable Q : world -> Prop.
Hypothesis HX : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndX';A1VEx;R2R1A5VQ;A3Ftp;Frho;").

Lemma fb_reshape : ltac2:(tb__ "0|1|
S7S21S46Q40A1A1S4aS74SeSfR3A1S8S30VE;A1A1A3S43S2fVJK;VndJ';A1M0VE;R4R3R2A6S43S2fG0VCF;R5R4R3A6F_;F_;Fw;Ftp;Frho1;").
Proof.
  intros rho1 tp w HF HS.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }
  assert (HS1 : SPA segs (JK ndJ') (ax_setS E S2) rho1 tp w).
  { rewrite <- H1e. apply (SPA_reslice segs (JK ndJ') rho1 E iw _ O_deepM tp w H1n); try reflexivity.
    - rewrite H1e. exact H1s.
    - unfold O_deepM, spT. rewrite !obj_range_lits by (unfold DEEP; lia). rewrite U_add_lit by lia. unfold DEEP. f_equal; lia.
    - unfold O_deepM, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia.
    - exact HS. }
  pose proof (AxXform.SPA_select segs (JK ndJ') rho1 (mkAX S2 (ax_X E) (ax_base E)) idxs tp w H2 HS1) as HS2.
  pose proof (SPA_merge segs (JK ndJ') rho1 (mkAX (set_objs S2 (select (ss_objs S2) idxs)) (ax_X E) (ax_base E)) 0 S4 tp w H3 HS2) as HS3.
  unfold CF, dropX. apply SPA_x_sub; [|exact HS3]. cbn [ax_X]. apply In_dropX.
Qed.

Lemma X_fb_ex : ltac2:(tb__ "0|0|
S7S21S46Q40A1A1S49S2fS43S2fVJK;VndJ';A1VA0;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct HJwf as (W1 & W2 & W3). destruct Hnb as [Hnb1 Hnb2]. destruct HTwf as (V1 & V2 & V3).
  eapply JK_erun; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply etriple_factsA. intros HF.
  eapply (etriple_conseq (P := SPA segs (JK ndJ') CF rho1 tp)); [intros w HS; exact (fb_reshape rho1 tp w HF HS) | intros w' Hw'; exact Hw' |].
  assert (HnxC : ss_next (ax_S CF) = ss_next (ax_S E)) by (unfold CF, dropX; cbn [ax_S ax_setX]; exact H4n).
  apply (X_free_call_ex vB vCap [] bdJ bdX CF (s_fb CF) R T Hfr Hcc HcT); try assumption.
  - rewrite HnxC. exact Hnx.
  - rewrite HnxC. split; [exact Hnb1 | exact Hnb2].
  - intros rho' tp'. eapply JK_erun; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros L rho3 [<-|[]] Hag3. cbn [la_state]. apply HX.
Qed.
End FbChainEx.

Lemma X_fb_pipe_ex : ltac2:(tb__ "0|5|
S21Sa5A1M0G0S31S31S4aOF_;S0S24S31A1S7aR5R4R3A3S25S31R2A2A3S7S21S46Q40A1A1M1S49S2fS43S2fVJK;S5bS23S22S6S6A2M2A1M3S23S22S22S6S2dA2S6A2A1M4R7S5aA4A1R5R2R1A5R4A3Ftp;Frho;S7G1S49S2fS43S2fVJK;S5bS26G2S27S6S6S60S61A4G3A3G4R9S5aA4A1R7R2R1A5R5A3Ftp;Frho;F_;F_;FQ;FEx;FA0;FbdX;FbdJ;").
Proof.
  intros bdJ bdX A0 Ex Q Hp HX rho tp. unfold fb_pipe in Hp. cbv zeta in Hp.
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E0; [|discriminate] end.
  apply andb_prop in E0 as [E0 E0c]. apply andb_prop in E0 as [E0a E0b]. apply negb_true in E0b.
  destruct (one_leaf (sym_runA segs FUEL_X CUTS_X A0 true)) as [E|] eqn:E1; [|discriminate]. apply one_leaf_sound in E1.
  destruct (nth_error (ss_objs (ax_S E)) _) as [o|] eqn:E2; [|discriminate].
  destruct (ob_shapeb o _ _ _) eqn:E3; [|discriminate]. apply ob_shapeb_sound in E3. subst o.
  destruct (same_but_objs _ _) eqn:E4; [|discriminate].
  destruct (select_ok _ _) eqn:E5; [|discriminate].
  destruct (merge_objs_at _ 0) as [S4|] eqn:E6; [|discriminate].
  destruct (entails_frA _ PreF _) as [R|] eqn:E7; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E8; [|discriminate] end.
  apply one_leaf_sound in Hp.
  apply andb_prop in E8 as [E8 Q3]. apply andb_prop in E8 as [E8 Q2]. apply andb_prop in E8 as [E8 Q1]. apply negb_true in Q2.
  apply andb_prop in E8 as [E8 P14]. apply andb_prop in E8 as [E8 P13]. apply andb_prop in E8 as [E8 P12].
  apply andb_prop in E8 as [E8 P11]. apply andb_prop in E8 as [E8 P10]. apply andb_prop in E8 as [E8 P9].
  apply andb_prop in E8 as [E8 P8]. apply andb_prop in E8 as [E8 P7]. apply andb_prop in E8 as [E8 P6].
  apply andb_prop in E8 as [E8 P5]. apply andb_prop in E8 as [E8 P4]. apply andb_prop in E8 as [E8 P3]. apply andb_prop in E8 as [P1 P2].
  apply Pos.eqb_eq in P1. apply sv_eqb_sound in P7. apply sv_eqb_sound in P8.
  eapply (X_fb_ex A0 bdJ bdX E _ S4 _ R _ Ex _ (conj E0a (conj E0b E0c)) E1 E2 eq_refl E4 E5 E6 P1 E7 P2 P3 P4 (conj P5 P6) (conj P7 P8)
            P9 P10 P11 P12 P13 P14 eq_refl (conj Q1 (conj Q2 Q3)) Hp Q HX).
Qed.

Lemma X_join_ex : ltac2:(tb__ "0|8|
S21Sa5A1M0G0S31S2dS2dS31S21S9A1M1S4aOF_;S0S24S31A1S7aR8R7R6A3S25S31R3A2A3S0S24G1A1S79S5bS23S22S6S6A2M2A1M3S23S22S22S6S2dA2S6A2A1M4R8S5aA4R4R6R5A4S25G1R3A2A3S82S22S2dS2dA2S27S2dS2dR7R6A4S4dA3S21S3aA1M5S3bVKc;R2R1A2M6S0S24S3cA1S40S41R2A1S4cA2S25S3cS3eS4cA1A2A3F_;Fmd;Ftr;S4aG5S3bG6S0G5S4bR4A1S28S3aR3S28S3aS73S46Q8A1S3aS3fS4cA1S4fRdA1A4S26S3aS3dS47Q40M7RcA2S42R2A1A2S23S3aA1A3A3A3A3RaR5A1F_;F_;Fmd;Ftr;Fw;S7S21S46G7A1A1S49S2fS43S2fVJK;S5bS26G2S27S6S6S60S61A4G3A3G4RfS5aA4A1RdR2R1A5R8A3Ftp;Frho;F_;F_;F_;F_;F_;FQ;FR;FEx;Fc;Fn;FA0;FbdX;FbdJ;").
Proof.
  intros bdJ bdX A0 n c Ex R Q Hfb Hex Hsupp HKfd1 HQ.
  apply (X_fb_pipe_ex bdJ bdX A0 Ex Q Hfb). apply (X_exit_pipe_ex (NDA [] [] bdX ANone) n c Ex R Q Hex Hsupp HKfd1 HQ).
Qed.

End SITE.
End DrvSiteEx.

(* [comment removed for export] *)
Module DrvTLX.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "or"; "True"; "not"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nat"; "prod"; "nil"; "cons"; "false"; "pair"; "option"; "Some"; "app"; "length"; "andb"; "None"; "orb"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_next"; "sprop"; "ss_facts"; "valuation"; "sstate"; "SLit"; "ss_objs"; "ss_lenient"; "holds"; "sprop_eqb"; "SPUle"; "SPBranch"; "SVar"; "sprop_below"; "SPNot"; "cell"; "mkObj"; "DUnknown"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "SAlu"; "agree_below"; "obj_hi_of"; "obj_lo_of"; "obj_range"; "rm"; "rw"; "eval"; "obj_wf"; "sv_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "ax_X"; "ax_base"; "la_state"; "sym_runA"; "mkAX"; "entailsA"; "mkLeafA"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "ExitEv"; "FdEntry"; "WriteEv"; "m_fs"; "FdChannel"; "fd_lookup"; "m_fds"; "VmState"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "LQA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ANone"; "NDA"; "ndesc"; "PTrue"; "nd_tv"; "nd_am"; "ok_frameKA"; "JAi"; "nd_bd"; "nd_fr"; "tvinA"; "JA"; "am_eqb"; "am_subst"; "amode"; "apot"; "bxa"; "fr_sub_eqb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "tcons"; "assn"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "pow"; "lt"; "sub"; "opp"; "div"; "land"; "modulo"; "of_nat"; "ltb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.TLX.LoopE"; "CfzE"; "CpfE"; "keptE"; "ndE1"; "Cpf0E"; "P1cE"; "ndE0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.TLX.LoopP"; "Cfz"; "Cpf"; "kept"; "ndL1"; "Cpf0"; "P1c"; "ndL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "wsub_get"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "s_fz"; "vP"; "CUTS_L"; "FUEL_L"; "J_E"; "PreP"; "pf_hints"; "s_m"; "s_pf"; "O_srcT"; "s_fp"; "O_WloT"; "PreM"; "pf_u1"; "s_fn"; "CUTS_T"; "PreFN"; "s_mc"; "O_WfzT"; "O_payE"; "PostFN"; "WDP"; "X_payE"; "cnt_reg"; "AND3"; "FUEL_T0"; "FUEL_T1"; "FUEL_T2"; "O_cstkB"; "PostsM"; "mc_hints"; "mc_rtc"; "pf_rtc"; "sel_buf"; "sel_rtc_last"; "sel_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vPlen"; "vB"; "vCap"; "nd_T"; "vClen"; "vLen"; "S_T"; "bd_T"; "tv_T"; "PreF"; "sp0"; "CUTS_X"; "FUEL_X"; "PostF"; "calls_of"; "dropX"; "flags_of"; "vFlg"; "ATOPHI"; "facts_T"; "hdr_word"; "locate"; "@Stdlib.Lists.List"; "forallb"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.TLX.ExitFreeP"; "CP"; "keptX"; "ndJX"; "ndLX";
"@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "lcarve"; "lc_obj"; "JAK"; "carve_okb"; "uncarve_okb"; "JA_carve"; "JA_uncarve"; "pure_callJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "sp0_factsb"; "drv_xrb"; "kept_nzb"; "robjs_checkD"; "xrs_checkD"; "drv_objb"; "ex_pipe"; "fb_pipe"; "site_ok_drv"; "xrs_okF_drv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "KV_T"; "BX0"; "KP_T"; "HKVrng_T"; "JT"; "P0T"; "CST_drv"; "HCSTKV_T"; "HKP_T"; "HKV_T"; "JT_tv_band_free"; "JTi"; "SH0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "bitem"; "bud_le"; "bsumV"; "bd_below"; "bud_pay"; "BIc"; "KU"; "LARGE_MIN"; "SECCAP"; "uval"; "BUD"; "bx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.TLX.SegMC"; "B3h"; "Cmc"; "ndM"; "B3c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "robj_tracked"; "tnz"; "tvz"; "T0"; "tvd"; "tvv"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "BC_EQ"; "branch_cond"; "mulop"; "BC_LT"; "BC_NE"; "ALU_AND"; "ALU_OR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.TLX"; "N_pf"; "EVk"; "N_mc"; "O_srcM"; "edge_okb"; "kept"; "ms16_shape"; "mc_needb"; "plen_factsb"; "ndE0"; "backedge_okb"; "cntg_b"; "cntl_b"; "exit1_b"; "exitc_b"; "ms16_shapeb"; "ndM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "Pre_fz"; "bd_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "xr_tracked"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit"; "ch1"; "supported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "AE_A"; "Kc_ok"; "L_malloc_ok"; "UStopLe"; "ulink"; "V_RES"; "alloc_contractsA"; "band_free"; "with_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "bd_E"; "bd_M"; "CKM"; "CVM"; "bd_L"; "cnt_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "acell"; "cells_ok"; "mkACell"; "view"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "PEND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2"; "P_fz"; "PD_fz"; "fuzz_one_sumT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config";
"mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.TLX.ExitFreeE"; "ndJE"; "ndEX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "Pre_mc0"; "P_icpt"; "Posts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TR_INIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.PFAddr"; "PW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "P_pf"; "Posts_pf"; "kok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.FZAddr"; "fz_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "MAX_INPUT"; "CK0"; "CK_DIV"; "CV"; "CV0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC"; "add_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "alloc_roomA"; "malloc_contractA_strong"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvBox.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CVM : Z := ltac2:(tb__ "0|0|
S7bS7cS181S17eA2S182A2").
Definition CKM : Z := ltac2:(tb__ "0|0|
S7bS81S17eS180A2S17fA2").
Definition bd_L (k : Z) : list bitem := ltac2:(tb__ "0|3|
SdS103S108Z1M0Z0M1S7cS7fZ4Vk;A2M2S15bA2A3SdS103S108G1G0S7cS109S7bS7cG2S15aA2Z2A2A2A3ScS103A1A3A3").
Definition bd_E (k : Z) : list bitem := ltac2:(tb__ "0|3|
SdS103S108Z1M0Z0M1S7cS7fZ4Vk;A2M2S15bA2A3SdS103S108G1G0S7cS109S7bS7cG2S15aA2G0A2A2A3ScS103A1A3A3").
Definition bd_J : list bitem := [BIc 0 1 KU].
Definition bd_M : list bitem := bd_L 0.

Lemma bd_L_cap : ltac2:(tb__ "0|0|
S19S21S7aS7bS7cS10aZ2A2S7fS105S15cR2A1R1A2S105S15cS7bR2Z1A2A1R1A2A2A2S10bA2Frho;Fk;").
Proof. intros k rho. unfold bd_L, bsumV, bival, BIc. cbn [lfval bi_f bi_c bi_v bi_k]. unfold SECCAP, LARGE_MIN, Model.SEC_SLACK, CVM, CV, MAX_INPUT, CV0. lia. Qed.
Lemma bd_E_cap : ltac2:(tb__ "0|0|
S19S21S7aS7bS7cS10aZ2A2S7fS105S158R2A1R1A2S105S158S7bR2Z1A2A1R1A2A2A2S10bA2Frho;Fk;").
Proof. intros k rho. unfold bd_E, bsumV, bival, BIc. cbn [lfval bi_f bi_c bi_v bi_k]. unfold SECCAP, LARGE_MIN, Model.SEC_SLACK, CVM, CV, MAX_INPUT, CV0. lia. Qed.

Definition cnt_word (u : Z) : Z := ltac2:(tb__ "0|1|
S82S83S81Vu;S7dZ2M0Z10A2A2S7dG0Z8A2A2Z3A2").

Lemma eval_AND3 : ltac2:(tb__ "0|1|
S21S0S19S50Q40M0S3dR1Sb6A2A2S15dS50G0S3cR1P2dA2A2A1A3Frho;").
Proof.
  intros rho. unfold AND3, vH. cbn [eval]. rewrite and_val, lit_unsigned. change (3 mod 2 ^ 64) with 3.
  rewrite (U_zext_w 8) by (cbv; discriminate). rewrite srl_val. change (16 mod 64) with 16.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma cnt_word_hdr : ltac2:(tb__ "0|2|
S9S4eQ8M0A1M1A1S19S0S19S83R1S7dZ2Z20A2A2Sd6R2A1A3S0S19S15dR2A1S82S50G0S8aG1U2R3S4fG0Z0A2A4A2Z3A2A3F_;Fu;FF;").
Proof.
  intros F u Hu. unfold cnt_word, hdr_word in *.
  pose proof (bv_unsigned_in_range 8 (nth 0 F (Z_to_bv 8 0))) as R0. pose proof (bv_unsigned_in_range 8 (nth 1 F (Z_to_bv 8 0))) as R1.
  pose proof (bv_unsigned_in_range 8 (nth 2 F (Z_to_bv 8 0))) as R2. pose proof (bv_unsigned_in_range 8 (nth 3 F (Z_to_bv 8 0))) as R3.
  change (bv_modulus 8) with 256 in *.
  set (b0 := bv_unsigned (nth 0 F (Z_to_bv 8 0))) in *. set (b1 := bv_unsigned (nth 1 F (Z_to_bv 8 0))) in *.
  set (b2 := bv_unsigned (nth 2 F (Z_to_bv 8 0))) in *. set (b3 := bv_unsigned (nth 3 F (Z_to_bv 8 0))) in *.
  change (2 ^ 8) with 256 in *. f_equal.
  pose proof (Z.div_mod u (2 ^ 32) ltac:(lia)) as Hd. rewrite Hu in Hd.
  pose proof (Z.mod_pos_bound u (2 ^ 32) ltac:(lia)) as Hm.
  change (2 ^ 32) with 4294967296 in *. change (2 ^ 16) with 65536 in *.
  assert (E : u / 65536 = (65536 * (u / 4294967296) + 256 * b3 + b2) + (b0 + 256 * b1) / 65536).
  { rewrite Hd at 1. rewrite <- (Z.div_add_l _ 65536) by lia. f_equal. lia. }
  assert (S : (b0 + 256 * b1) / 65536 = 0) by (apply Z.div_small; lia).
  rewrite E, S, Z.add_0_r.
  replace (65536 * (u / 4294967296) + 256 * b3 + b2) with (b2 + (256 * (u / 4294967296) + b3) * 256) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section TLX.
Variable AInv : ltac2:(tb__ "0|0|
S145S21S9S4eQ40A1A1S52OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S19S15eVCST;R1A2S1S7aZ0R2A2S7eR2S169A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S19S15eVXGL;R1A2S1S7aZ0R2A2S7eR2S169A2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S19S15eSfbR1A2S15eVCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Variable ok : world -> Prop.
Variable Spec : list event -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S5cS21S9S4eQ40A1A1S9S51A1S52R5R4R3R2R1A4S78VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S5dS4cVok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S5cS21S9S4eQ40A1A1S9S51A1S52R5R4R3R2R1A4S78VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S183S4cVok;R2A3F_;FJ;").
Hypothesis Hokh : ok_halted ok Spec.
Hypothesis AC : ltac2:(tb__ "0|0|
S155S4cS14fVAInv;VCST;VXGL;A5").

Hypothesis MS : ltac2:(tb__ "0|0|
S188S4cS14fVAInv;VCST;VXGL;A5").

Variable rhoT : valuation.
Variable F : list byte.
Variable T0 : list event.
Variable MD : Model -> Prop.
Hypothesis HMDvm : ltac2:(tb__ "0|0|
S52S5aVMD;R2A1VMD;S157R2R3A2A1F_;Fv;Fmd;").
Hypothesis HMDfd1 : ltac2:(tb__ "0|0|
S52VMD;R1A1S0S10S54A1S58S59R2A1S149A2S11S54S57S149A1A2A3F_;Fmd;").

Let KcT := KcT T0 MD.
Let P0T := P0T F.
Let JT (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Sf9VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S65Vk;Vnd;Aa").
Let JTi (k : nat) (nd : ndesc) (Ai : AA) (kc : Z) : jpredA := ltac2:(tb__ "0|0|
S100VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S65Vk;Vnd;VAi;Vkc;Ac").

Let HKV : ltac2:(tb__ "0|1|
S14eS64S145S19S21S9S4eQ40A1A1S9S51A1S52S69VAInv;VCST;VXGL;S4dR8VrhoT;SfaVF;A1ScSbS19S19A2M0A1ScSbG0S19A2A1Sf6S65R7R6R5R4R3R2R1A12S160S162S4cS3bR5A1A2Sf5A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;") := ltac2:(tb__ "0|0|
SfeVAInv;VCST;VXGL;VALA;VHCSTdrv;VHLPP;VrhoT;VF;S65A9").
Let HKP := HKP_T AInv CST XGL HCSTdrv rhoT F PTrue.
Let HCK := HCSTKV_T AInv CST HCSTok HLPP.
Let carveT : ltac2:(tb__ "0|3|
S14eS64S43S21S9S4eQ40A1A1S77S9Se1A1S1aS5bS4cSe3VAInv;VCST;VXGL;S4dVrhoT;VP0T;ScSbS19S19A2M0A1M1ScSbG0S19A2A1M2Sf6S65R8R7AcR6R5R4R3A6S41R7A1S22S30S33R1A1S34R1A1S32R1A1S31R1A1S35R1A1S12S1dS24R1A1S86Se1S1dSe2R4A4A3S20R1A1R3S25R1A1A9S22S0S7S40R1A1S8A3S0S7S74S1eR3A1R5A2S8A3S0S1cS45RbA1S23S168A1A3S0S7Se4S20R5A1S24R5A1S44RcA1Sf5Sf7S66RdA1R8A7S8A3S5bS4cSe3VAInv;VCST;VXGL;S4dVrhoT;VP0T;G1G2Sf6S65RfReAcS4bRdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
Se6VAInv;VCST;VXGL;VALA;S4dVrhoT;VP0T;ScSbS19S19A2M0A1ScSbG0S19A2A1Sf6S65Sf5VHKV;Sf8Sf7VHKP;A10").
Let uncarveT : ltac2:(tb__ "0|5|
S14eS64S43S21S9S4eQ40A1A1S9S51A1M0S163S52S9S1dA1M1S9Se1A1S150RaA1S0G1S24S41R9A1A1S12S1dR3S86Se1S1dSe2R2A4A3A3S0S7Se5Sf5R3A2S8A3S0S70S67RcA1S62A3S0S7S61S1eS41RcA1A1RdA2S8A3S5bS4cSe3VAInv;VCST;VXGL;S4dVrhoT;VP0T;ScSbS19S19A2M2A1M3ScSbG2S19A2A1M4Sf6S65RfReAcRdRcRbSfG0S16aRaS16bR9R8A2A4A6S5bS4cSe3VAInv;VCST;VXGL;S4dVrhoT;VP0T;G3G4Sf6S65R10RfAcS4bReSe9S41ReA1R8A2A2S9cRdS86Se1S1dSe2R7A4S179R9RcRaA3A3RcSfG0S16aRbS16bRaR9A2A4A6F_;F_;F_;F_;F_;F_;FN;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
Se7VAInv;VCST;VXGL;VALA;VHLV;S4dVrhoT;VP0T;ScSbS19S19A2M0A1ScSbG0S19A2A1Sf6S65Sf5VHKV;Sf8VHCK;A10").
Let pcallT := pure_callJ AInv CST XGL ALA NF rhoT P0T [] [] BX0 PTrue ok.

Let site_ok_drv := site_ok_drv AInv CST XGL ALA HCSTdrv rhoT P0T.
Let robjs_okF_drv := robjs_okF_drv CST HCSTdrv rhoT.
Let xrs_okF_drv := xrs_okF_drv CST XGL HCSTdrv rhoT.
Let kept_in_FBx := kept_in_FBx CST.
Let JT_tv_band_free : ltac2:(tb__ "0|1|
S145OF_;SaS64S21S9S4eQ40A1A1S9S51A1S52SbS1cS1cA2M0Sf9VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;R8R7R6R5R4R3R2AeSd9G0R2S66R7A1A3S117R7R3A2S156S10cR8S17S1cS1cR4A3A2S10cR8S18S1cS1cR4A3A2A2F_;F_;F_;Ft;Fmd;Ftr;Ftp;Frho;Fnd;Fk;FPA;") := ltac2:(tb__ "0|0|
SffVAInv;VCST;VXGL;VALA;VrhoT;VF;VT0;VMD;A8").

Definition EVk (k : nat) : list event := match k with O => [] | _ => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.EVS 2 end.

Lemma JT_Kc : ltac2:(tb__ "0|1|
SaS64S21S9S4eQ40A1A1S9S51A1M0S52VJT;R6R5R4R3R2R1A6S1VMD;R2A1S0G0R3S12S51VT0;S125R7A1A3A3A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;").
Proof. intros k nd rho tp tr md (Ai & kc & _ & [H1 H2] & _). split; [exact H1 | exact H2]. Qed.

Lemma JT_stable : ltac2:(tb__ "0|0|
SaS64S1aS75S4dR1A2S0S7S61R2R3A2S8A3S60S4cR3VJT;R5R4A2A3F_;F_;Fn;Fnd;Fk;").
Proof. intros k nd n Hn Hb. apply (stableA_JA segs AInv CST XGL NF _ rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm k) ALA n nd Hn Hb). Qed.

Variable Htc : ltac2:(tb__ "0|0|
SaS78VSpec;S12S51VT0;S125R1A1A3A2Fk;").

Lemma JT_tcons : ltac2:(tb__ "0|0|
SaS64S21S9S4eQ40A1A1S9S51A1S52VJT;R6R5R4R3R2R1A6S78VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;").
Proof. intros k nd rho tp tr md H. destruct (JT_Kc _ _ _ _ _ _ H) as [_ ->]. apply Htc. Qed.

Lemma okKT : ltac2:(tb__ "0|0|
SaS68S4cVKcT;R1A1Vok;A3Fk;").
Proof. intros k. split; [apply HOKJ | apply HOKP]; intros rho tp tr md [_ ->]; apply Htc. Qed.

Lemma JT_okframe : ltac2:(tb__ "0|0|
SaS64S5dS4cVok;VJT;R2R1A2A3Fnd;Fk;").
Proof. intros k nd. apply HOKJ. apply JT_tcons. Qed.

Lemma JT_run : ltac2:(tb__ "0|1|
SaS64SaS9S19A1S43S9S42A1M0S21S9S4eQ40A1A1S79S0S10G0A1S47S4cR7R6R5S8A5S11G0R4A2A3S0S7S25S41R6A1A1SeA3S0S7S74S4dS1eS41R7A1A1A2S8A3S0S7S61S1eS41R8A1A1RbA2S8A3S42S21Sd9S42R2RaA3S37S1eS41RcA1A1RaR2A3S76S4cVok;S5bS4cVJT;R11R10A2S46R4A1R3RaA5R9A4F_;F_;Frho';FL;S76S4cVok;S5bS4cVJT;ReRdA2RaR8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;Fnd;Fk;").
Proof.
  intros k nd fuel cuts A leaves rho tp Q Hrun Hlen Hnf Hnb H. apply Pos.leb_le in Hnf.
  eapply (runA_tr segs ok fuel cuts A leaves (JT k nd) rho tp Q Hrun Hlen (JT_okframe k nd) (JT_stable k nd _ Hnf Hnb) H).
Qed.

Lemma JT_entails : ltac2:(tb__ "0|0|
SaS43S43S99S64S64S21S9S4eQ40A1A1S77S0S7S49R8R7R6A3S8A3S0S7S9aR7S4dA2S8A3S0S7S74S4dS1eS41RaA1A1A2S8A3S0S7S61S1eS41RbA1A1R8A2S8A3S0S7S115RaS66R9A1S66R8A1A3S8A3S0S7S73RbS6bRaA1S6bR9A1A3S8A3S0S7S104S20S41ReA1A1S102RcS6aRaA1A2S6aRbA1A3S8A3S0S7S6eS6fRdS67RbA1A2S67RcA1A2S8A3S5bS4cVJT;R11RdA2R10RbRaR9A6S5bS4cVJT;R12RdA2R10S9dRcRfA2RbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;Fk;").
Proof.
  intros k L T s ndi ndj rho tp w. apply (SPA_entails_JA segs AInv CST XGL ALA NF (KcT k) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm k)).
Qed.

Lemma JT_factsT : ltac2:(tb__ "0|0|
SaS64S21S9S4eQ40A1A1S9S51A1S52VJT;R6R5R4R3R2R1A6S87S1fS26R5A1Sd5A3S5F_;F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;").
Proof. intros; exact I. Qed.

Lemma triple_JT_pre : ltac2:(tb__ "0|0|
SaS64S43S21S9S4eQ40A1A1S79VP0T;VrhoT;A1S13eS4dVrhoT;R4A3S76S4cVok;S5bS4cVJT;R8R7A2R6R5R4A5R3A4F_;F_;S76S4cVok;S5bS4cVJT;R7R6A2R5R4R3A5R2A4F_;FQ;Ftp;Frho;FA;Fnd;Fk;").
Proof.
  intros k nd A rho tp Q H n Hg w [Hsm HJ]. pose proof HJ as (Ai & kc & Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _).
  exact (H HP0 Hav n Hg w (conj Hsm HJ)).
Qed.

Definition exitc_b (k : Z) (facts : list sprop) : bool := ltac2:(tb__ "0|5|
S14SdaS1fS27S2cS29S11dSc6S23Z0A1M0A3A1A1Vfacts;A3S7S7L_;S85Vk;Z3M1A2SdaS1fS27S2cS29S121Sb5S8S7bVk;Z1M2A2A2G0A3A1A1Vfacts;A3S14SdaS1fS27S28S23G2A1M3Sb5S8G1A2M4A2A1Vfacts;A3SdaS1fS27S28G4G3A2A1Vfacts;A3A2X7x2A2").
Lemma exitc_sound : ltac2:(tb__ "0|0|
S19S21S9S1fA1S1S7aZ0R3A2S7aR3Z3A2A2S87S1fS26R3A1R2A3S0S7S132R5R3A2S8A3VP0T;VrhoT;A1S13eS4dVrhoT;R6A3S0S19Sd0VF;A1S7bR8Z1A2A3F_;F_;F_;F_;F_;Ffacts;Frho;Fk;").
Proof.
  intros k rho facts Hk HF H ((_ & _ & HC & _ & HH & _) & _) [Hav _].
  unfold exitc_b in H. apply andb_prop in H as [H1 H2].
  apply (holds_mem rho facts) in H1; [|exact HF]. apply holds_nbeq in H1. unfold vClen in H1. cbn [eval] in H1.
  rewrite lit_unsigned in H1. change (0 mod 2 ^ 64) with 0 in H1.
  rewrite <- (Hav 43%positive) in H1 by (unfold NF; lia). rewrite HC in H1.
  unfold calls_of. rewrite (proj2 (Z.eqb_neq _ _) H1).
  rewrite <- (cnt_word_hdr F (bv_unsigned (rw rhoT 45%positive)) HH). rewrite (Hav 45%positive) by (unfold NF; lia).
  rewrite <- eval_AND3. pose proof (eval_AND3 rho) as EA.
  assert (RA : 0 <= bv_unsigned (eval rho AND3) <= 3).
  { rewrite EA. unfold cnt_word. split; [apply Z.land_nonneg; right; lia|].
    change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (Z.ones 2) with 3. pose proof (Z.mod_pos_bound ((bv_unsigned (rw rho 35) / 2 ^ 16) mod 2 ^ 8) (2 ^ 2) ltac:(lia)). lia. }
  destruct (k <? 3) eqn:K3.
  - apply Z.ltb_lt in K3. apply (holds_mem rho facts) in H2; [|exact HF]. apply holds_nbne in H2.
    unfold cnt_reg in H2. cbn [eval] in H2. rewrite lit_unsigned in H2. change (0 mod 2 ^ 64) with 0 in H2.
    destruct (k + 1 =? 1) eqn:K1.
    + apply Z.eqb_eq in K1. cbn [eval] in H2. lia.
    + apply Z.eqb_neq in K1. cbn [eval] in H2. rewrite U_add, U_lit, <- M64v_eq in H2.
      replace (1 - (k + 1)) with (- k) in H2 by lia.
      rewrite <- (Z.mod_add (- k) 1 (2 ^ 64)) in H2 by lia. rewrite (Z.mod_small (- k + 1 * 2 ^ 64)) in H2 by lia.
      destruct (Z_le_gt_dec k (bv_unsigned (eval rho AND3))) as [LE|GT].
      * replace (bv_unsigned (eval rho AND3) + (- k + 1 * 2 ^ 64)) with ((bv_unsigned (eval rho AND3) - k) + 1 * 2 ^ 64) in H2 by lia.
        rewrite Z.mod_add in H2 by lia. rewrite Z.mod_small in H2 by lia. lia.
      * rewrite Z.mod_small in H2 by lia. lia.
  - apply Z.ltb_ge in K3. assert (k = 3) by lia. subst k.
    apply andb_prop in H2 as [H2 H3]. apply (holds_mem rho facts) in H2; [|exact HF]. apply (holds_mem rho facts) in H3; [|exact HF].
    apply (proj1 (holds_ule _ _ _)) in H2. apply (proj1 (holds_ule _ _ _)) in H3. unfold cnt_reg, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.add in H2, H3. cbn [Z.eqb Pos.eqb eval] in H2, H3.
    rewrite add_val, !lit_unsigned in H2, H3. change (1 mod 2 ^ 64) with 1 in H2, H3. change ((1 - 3) mod 2 ^ 64) with (2 ^ 64 - 2) in H2, H3.
    destruct (Z_le_gt_dec 2 (bv_unsigned (eval rho AND3))) as [LE|GT].
    + replace (bv_unsigned (eval rho AND3) + (2 ^ 64 - 2)) with ((bv_unsigned (eval rho AND3) - 2) + 1 * 2 ^ 64) in H2, H3 by lia.
      rewrite Z.mod_add in H2, H3 by lia. rewrite Z.mod_small in H2, H3 by lia. lia.
    + rewrite Z.mod_small in H2, H3 by lia. lia.
Qed.

Definition exit1_b (facts : list sprop) : bool := ltac2:(tb__ "0|0|
SdaS1fS27S29S11dSc6S23Z0A1A3A1Vfacts;A3").
Lemma exit1_sound : ltac2:(tb__ "0|0|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S131R2A1S8A3VP0T;VrhoT;A1S13eS4dVrhoT;R5A3S0S19Sd0VF;A1S7bZ0Z1A2A3F_;F_;F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H ((_ & _ & HC & _) & _) [Hav _].
  apply (holds_mem rho facts) in H; [|exact HF]. apply (proj1 (holds_beq _ _ _)) in H. unfold vClen in H. cbn [eval] in H.
  rewrite lit_unsigned in H. change (0 mod 2 ^ 64) with 0 in H.
  rewrite <- (Hav 43%positive) in H by (unfold NF; lia). rewrite HC in H.
  unfold calls_of. rewrite H. reflexivity.
Qed.

Definition cntg_b (facts : list sprop) : bool := ltac2:(tb__ "0|0|
SdaS1fS27S29S120Sd3S23Z0A1A3A1Vfacts;A3").
Definition cntl_b (facts : list sprop) : bool := ltac2:(tb__ "0|0|
SdaS1fS27S2cS29S120Sd3S23Z0A1A3A1A1Vfacts;A3").
Lemma flags_range : 0 <= flags_of F < 256.
Proof. unfold flags_of. pose proof (bv_unsigned_in_range 8 (nth 1 F (Z_to_bv 8 0))). change (bv_modulus 8) with 256 in *. lia. Qed.
Lemma cntg_sound : ltac2:(tb__ "0|0|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S12fR2A1S8A3VP0T;VrhoT;A1S13eS4dVrhoT;R5A3S7aZ80Sd2VF;A1A2F_;F_;F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H ((_ & _ & _ & _ & _ & HS) & _) [Hav _]. pose proof flags_range as FR.
  apply (holds_mem rho facts) in H; [|exact HF]. apply (proj1 (holds_blt _ _ _)) in H. unfold vFlg in H. cbn [eval] in H.
  rewrite lit_unsigned, (Z.mod_small 0) in H by lia. rewrite <- (Hav 46%positive) in H by (unfold NF; lia). rewrite HS in H.
  pose proof (Zsigned_spec 0) as Z0.
  destruct (flags_of F <? 128) eqn:E; [|apply Z.ltb_ge in E; exact E].
  apply Z.ltb_lt in E. exfalso. pose proof (Zsigned_spec (flags_of F)) as ZS. lia.
Qed.
Lemma cntl_sound : ltac2:(tb__ "0|0|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S130R2A1S8A3VP0T;VrhoT;A1S13eS4dVrhoT;R5A3S7eSd2VF;A1Z80A2F_;F_;F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H ((_ & _ & _ & _ & _ & HS) & _) [Hav _]. pose proof flags_range as FR.
  apply (holds_mem rho facts) in H; [|exact HF]. apply (proj1 (holds_nblt _ _ _)) in H. unfold vFlg in H. cbn [eval] in H.
  rewrite lit_unsigned, (Z.mod_small 0) in H by lia. rewrite <- (Hav 46%positive) in H by (unfold NF; lia). rewrite HS in H.
  pose proof (Zsigned_spec 0) as Z0.
  destruct (flags_of F <? 128) eqn:E; [apply Z.ltb_lt in E; exact E|].
  apply Z.ltb_ge in E. exfalso. pose proof (Zsigned_spec (flags_of F + 2 ^ 64 - 256)) as ZS. lia.
Qed.

Lemma P0T_SH : ltac2:(tb__ "0|0|
S21VP0T;R1A1S101R2A1F_;Fr;").
Proof. intros r [_ H]. exact H. Qed.
Lemma KtcT : ltac2:(tb__ "0|0|
SaS9S51A1S52VKcT;R3R2R1A3S78VSpec;R3A2F_;Fmd;Ftr;Fk;").
Proof. intros k tr md [_ ->]. apply (Htc k). Qed.
Lemma HKfd1_T : ltac2:(tb__ "0|0|
SaS9S51A1S52VKcT;R3R2R1A3S0S10S54A1S58S59R2A1S149A2S11S54S57S149A1A2A3F_;Fmd;Ftr;Fk;").
Proof. intros k tr md [H _]. apply HMDfd1. exact H. Qed.
Lemma HSPEC_T : ltac2:(tb__ "0|5|
SaS19S19S52VMD;R1A1VSpec;S12S51S12S51VT0;S125R5A1A3S12S51S86S4eQ8A1M0S51S55S149A1M1S164R4A1A4SdS51S53S4fQ40M2R3A2S56R2A1M3A2ScS51A1M4A3A3A3A1F_;Fmd;S9S51A1S52VKcT;R6R2R1A3VSpec;S12S51R3S12S51S86G0S51G1S164R6A1A4SdS51S53S4fG2R5A2G3A2G4A3A3A3A1F_;Fmd;Ftr;F_;Fc;Fn;Fk;").
Proof. intros k n c H tr md [Hmd ->]. exact (H md Hmd). Qed.

Lemma X_exit_pipe : ltac2:(tb__ "0|2|
SaS64S19S19S43S9S1dA1M0S0S10G0A1Sf1R5R2R4R3A4S11G0R1A2A3Sd9SbS19S19A2SfS19S19R5R4A4S14aA3S52VMD;R1A1VSpec;S12S51S12S51VT0;S125RaA1A3S12S51S86S4eQ8A1S51S55S149A1S164R8A1A4SdS51S53S4fQ40M1R7A2S56R2A1A2ScS51A1A3A3A3A1F_;Fmd;S21S9S4eG1A1A1S76S4cVok;S5bS4cVJT;RbRaA2R7R2R1A5S77S2L_;A4Ftp;Frho;F_;F_;F_;FR;FE;Fc;Fn;FndX;Fkx;").
Proof.
  intros kx ndX n c E R Hp Hs HS.
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite.X_exit_pipe AInv CST XGL ALA HCSTdrv HLPP ok Spec HOKJ HOKP Hokh (KcT kx) (Kc_okT T0 MD HMDvm kx) rhoT P0T P0T_SH PTrue
           ndX n c E R Hp Hs (HSPEC_T kx n c HS) (HKfd1_T kx)).
Qed.

Lemma X_join : ltac2:(tb__ "0|6|
SaS9S103A1M0G0S19S1cS19S43S9S1dA1M1S0S10S43A1Sf2R7R6Sa2R5R4A2A3S11S43R2A2A3S0S10G1A1Sf1S63ScSbS1cS1cA2M2A1M3ScSbSbS1cS19A2S1cA2A1M4R7S62A4R3R6R4A4S11G1R2A2A3Sd9SbS19S19A2SfS19S19R7R5A4S14aA3S52VMD;R1A1VSpec;S12S51S12S51VT0;S125RdA1A3S12S51S86S4eQ8A1S51S55S149A1S164RaA1A4SdS51S53S4fQ40M5R8A2S56R2A1A2ScS51A1A3A3A3A1F_;Fmd;S21S9S4eG5A1A1S76S4cVok;S5bS4cVJT;ReS63SdG2SfS1cS1cSc3Sc4A4G3A3G4RdS62A4A2Sa2RbRaA2R2R1A5S77S2L_;A4Ftp;Frho;F_;F_;F_;F_;FR;FEx;Fc;Fst;Fn;FbdX;FbdJ;Fkx;").
Proof.
  intros kx bdJ bdX n st c Ex R Hfb Hex Hs HS.
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite.X_join AInv CST XGL ALA HCST HXGL HCSTdrv HLPP ok Spec HOKJ HOKP Hokh AC (KcT kx) (Kc_okT T0 MD HMDvm kx) rhoT P0T P0T_SH (KtcT kx) PTrue (fun _ _ _ _ => I)
           bdJ bdX (J_E n st) n c Ex R Hfb Hex Hs (HSPEC_T kx n c HS) (HKfd1_T kx)).
Qed.

Definition N_pf : list lcarve := ltac2:(tb__ "0|e|
SdSbSbS19S19A2M0S9SbSbS19SaA2M1S19A2M2A1M3A2M4SfG0G3SfS19S19Z800c0998M5Z800c09a8A4SdG2SfG1S19SfS19SaG5U8M6A4Z0M7A4SdG2SfG1S19SfS19SaZ800c09a0G6A4G7A4ScG2A1M8A3A3A4SdG4SfG0G3SfS19S19Zf20d8M9Zf20daA4SdG2SfG1S19SfS19SaG9U1MaA4Z1MbA4SdG2SfG1S19SfS19SaZf20d9GaA4GbA4G8A3A3A4SdG4SfG0G3SfS19S19Zf20e0McZf20f8A4SdG2SfG1S19SfS19SaGcG6A4Z7fffffffffffA4SdG2SfG1S19SfS19SaZf20e8G6A4G7A4SdG2SfG1S19SfS19SaZf20f0G6A4G7A4G8A3A3A3A4SdG4SfG0G3SfS19S19Ze9ae8MdZe9af8A4SdG2SfG1S19SfS19SaGdG6A4Zddf74A4SdG2SfG1S19SfS19SaZe9af0G6A4Zde378A4G8A3A3A4ScG4A1A3A3A3A3").
Lemma N_pf_eq : ltac2:(tb__ "0|0|
S0S9S1dA1S86Se1S1dSe2S124A4SbeA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition ms16_shape (x : sv) : sprop := ltac2:(tb__ "0|0|
S2cS29S11dS36S122S36S123S23Z28A1Vx;A3S23ZfA1A3S23Z0A1A3A1").
Lemma ms16_holds : ltac2:(tb__ "0|0|
S21S1cS26R2S12aR1A1A2Fx;Frho;").
Proof.
  intros rho x. unfold ms16_shape. cbn [holds eval branch_taken]. intros HB.
  unfold bv_eqb in HB. apply Z.eqb_eq in HB.
  assert (U0 : bv_unsigned (alu64 ALU_AND (alu64 ALU_OR (Z_to_bv 64 40) (eval rho x)) (Z_to_bv 64 15)) = 0).
  { rewrite HB. rewrite lit_unsigned. reflexivity. }
  rewrite and_val, or_val_A, !lit_unsigned in U0. change (40 mod 2 ^ 64) with 40 in U0. change (15 mod 2 ^ 64) with 15 in U0.
  assert (T : Z.testbit (Z.land (Z.lor 40 (bv_unsigned (eval rho x))) 15) 3 = true).
  { rewrite Z.land_spec, Z.lor_spec. reflexivity. }
  rewrite U0 in T. cbn in T. discriminate.
Qed.

Section LoopP.
Variable k : Z.
Variables kx kx' : nat.
Variables bd0 bd1 : list bitem.
Hypothesis Hcapbd : ltac2:(tb__ "0|0|
S21S7aS7bS7cS10aZ2A2S7fS105Vbd0;R1A2S105Vbd1;R1A2A2A2S10bA2Frho;").
Definition kept : list (sv * sv) := ltac2:(tb__ "0|1|
SdSbS1cS1cA2M0SfS1cS1cS2aS9fA1Sc2A4SdG0SfS1cS1cSc3Sc4A4ScG0A1A3A3").
Definition ndL0 : ndesc := ltac2:(tb__ "0|0|
S63S94ScSbSbS1cS19A2S1cA2A1Vbd0;S62A4").
Definition ndL1 : ndesc := ltac2:(tb__ "0|0|
S63S94ScSbSbS1cS19A2S1cA2A1Vbd1;S62A4").
Variable L : axst.
Variable Lnext : axst.
Variables (Efz : axst) (S1 S2 : sstate) (Rfz : list sobj) (TT : axst) (U1 U3 : sstate) (Tfz : axst).
Variables (Epf : axst) (P1 : sstate) (Rpf : list sobj) (TP : axst) (Q1 Q2 Q4 : sstate) (Upf : axst).
Variable leaves : list leafA.
Variable iw : nat.

Hypothesis HLwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VL;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S98A2S8A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VL;S8A5S11G0SdS42S4aVEfz;SeaA2ScS42A1A3A2A3").

Hypothesis F1 : ltac2:(tb__ "0|0|
S0S10S22A1S113S41VEfz;A1Viw;S23S80S177A1A1A3S11S22VS1;A2A3").
Hypothesis F2n : ltac2:(tb__ "0|0|
S0S10S1dA1SdbS1dS24VS1;A1Viw;A3S11S1dSa9A2A3").
Hypothesis F2e : ltac2:(tb__ "0|0|
S0S22S14dVS1;Viw;Sb0A3VS2;A3").
Hypothesis F2s : ltac2:(tb__ "0|0|
S0S7S14cVS1;VS2;A2S8A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S7SebS20S41VEfz;A1A1A1S8A3").
Definition Cfz : axst := ltac2:(tb__ "0|0|
S48VS2;S44VEfz;A1S45VEfz;A1A3").
Hypothesis F3n : ltac2:(tb__ "0|1|
S1S0S1aS1eVS2;A1S1eS41VEfz;A1M0A1A3S0S9S1fA1S20VS2;A1S20G0A1A3A2").

Hypothesis HFZ : ltac2:(tb__ "0|1|
S77OF_;S68S4cVKcT;Vkx;A1M0R1A3S167VAInv;VCST;VXGL;G0R2A5F_;Fok';").
Hypothesis Fxk : ltac2:(tb__ "0|1|
S0S7S17cS44S92A1M0G0A2S8A3").
Hypothesis Ffr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S136S92S13cS9eS92A1A3S11G0VRfz;A2A3").
Hypothesis Fcc : ltac2:(tb__ "0|0|
S0S7S137S92S13cS9eS92A1VRfz;SdS43S165ScS43A1A3A5S8A3").
Hypothesis Ftp : ltac2:(tb__ "0|0|
S0S7S142S4dS9eS92A1A2S8A3").
Hypothesis Fdom : ltac2:(tb__ "0|0|
S0S7S13fS9eS92A1S4dA2S8A3").
Hypothesis Fnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VEfz;A1A1A2S8A3").
Hypothesis Fnb : ltac2:(tb__ "0|2|
S1S0S7S61S1eS41VEfz;A1A1M0S63S12SbS1cS1cA2M1S94ScG1A1A3ScSbSbS1cS19A2S1cA2A1Vbd0;S62A4A2S8A3S0S7S106G0Vbd1;A2S8A3A2").
Hypothesis Fpay : ltac2:(tb__ "0|1|
S0S7S107S20S41S92A1A1S23Z0M0A1G0Vbd0;S12S103S102S9eS92A1S13dA2Vbd1;A3A5S8A3").
Hypothesis Fpd : ltac2:(tb__ "0|0|
S0S7Sd8S17bS17aS13cS4dS9eS92A1S1eS41S92A1A1A4S166A3S8A3").
Hypothesis FspfC : ltac2:(tb__ "0|0|
S0S7SebS20S41S92A1A1A1S8A3").
Hypothesis Fknz : ltac2:(tb__ "0|0|
S0S7SedS20S41S92A1A1S94A2S8A3").
Hypothesis Fro : ltac2:(tb__ "0|0|
S0S7Sd8S1dS1dS16Sf0S20S41S92A1A1R1A2S116S94S15SaA1R1A3A2Lo;VRfz;A3S8A3").
Hypothesis Fxr : ltac2:(tb__ "0|1|
S0S7Sd8SbS1cS1cA2M0G0S16SecR1A1S143S94S15SaA1R1A3A2Lr;S44S92A1A3S8A3").
Hypothesis Fa0 : ltac2:(tb__ "0|1|
S1S0S1cS9bS9eS92A1M0PcA2S2aS9fA1A3S0S1cS9bG0PdA2Sc2A3A2").
Hypothesis FTT : ltac2:(tb__ "0|0|
S0S43S141S13cS92S9eS92A1VRfz;S165A5VTT;A3").

Hypothesis U1n : ltac2:(tb__ "0|0|
S0S10S1dA1SdbS1dS24S41VTT;A1A1U1A3S11S1dS2eS14bSccS23N250A1A2S23S80Sb3A1A1S23Z0A1ScS2dA1S2fA5A2A3").
Hypothesis U1e : ltac2:(tb__ "0|0|
S0S22S14dS41VTT;A1U1Sa9A3VU1;A3").
Hypothesis U1s : ltac2:(tb__ "0|0|
S0S7S14cS41VTT;A1VU1;A2S8A3").
Hypothesis U1f : ltac2:(tb__ "0|0|
S0S7SebS20S41VTT;A1A1A1S8A3").
Hypothesis U2 : ltac2:(tb__ "0|2|
S0S7S13bS13S1dS24VU1;A1A2M0S12SaSdSaU1SdSaU0ScSaA1A3A3S88U2M1Se0G0G1A2A2A3A2S8A3").
Hypothesis U3e : ltac2:(tb__ "0|3|
S0S10S22A1S114Se9VU1;S135S24VU1;A1M0S12SaSdSaU1SdSaU0M1ScSaA1A3A3S88U2M2Se0S13S1dG0A2G2A2A2A3A2A2G1A2S11S22VU3;A2A3").
Hypothesis UT : ltac2:(tb__ "0|0|
S0S43S48VU3;S44VTT;A1S45VTT;A1A3VTfz;A3").

Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VTfz;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S95A2S8A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VTfz;S8A5S11G0SdS42S4aVEpf;SeaA2ScS42A1A3A2A3").

Hypothesis P1e : ltac2:(tb__ "0|0|
S0S10S22A1S113S41VEpf;A1U0S23S80S173A1A1A3S11S22VP1;A2A3").
Definition P1c : sstate := ltac2:(tb__ "0|0|
S30S33VP1;A1S34VP1;A1S32VP1;A1S31VP1;A1S35VP1;A1S12S1dS24VP1;A1S86Se1S1dSe2S124A4A3S20VP1;A1S1eVP1;A1S25VP1;A1A9").
Hypothesis P2w : swf P1c = true.
Hypothesis P2c : ltac2:(tb__ "0|0|
S0S7Se4S20VP1;A1S24VP1;A1S44VEpf;A1Sf5Sf7S66S95A1S124A7S8A3").
Hypothesis P2n : ltac2:(tb__ "0|0|
S0S1aS1eVP1;A1S1eS41VEpf;A1A1A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S1cS45VEpf;A1S23S168A1A3").
Definition Cpf0 : axst := ltac2:(tb__ "0|0|
S48S97S44VEpf;A1S45VEpf;A1A3").
Definition Cpf : axst := ltac2:(tb__ "0|0|
S171Sa4S96Vk;A2S96A2").
Hypothesis P3b : ltac2:(tb__ "0|0|
S0S7Sd8S1fS2bS1eS97A1A1S12S1fSa4S96Vk;A2S20S97A1A3A3S8A3").
Hypothesis P3h : ltac2:(tb__ "0|0|
S1fSd9S1fR1Sa4S96Vk;A2A3S3S1cS1cS0S1fR3S12aR1A1A3Lx;A2F_;Fq;").

Hypothesis Pfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S136S93Sa3Vk;A1Sa6S93Vk;A2A3S11G0VRpf;A2A3").
Hypothesis Pcc : ltac2:(tb__ "0|0|
S0S7S138S93Sa3Vk;A1Sa6S93Vk;A2VRpf;S86S42S43S46S175Vk;A1A4A5S8A3").
Hypothesis Pnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41S93A1A1A2S8A3").
Hypothesis Pnb : ltac2:(tb__ "0|0|
S0S7S61S1eS41S93A1A1S95A2S8A3").
Hypothesis Pfb : ltac2:(tb__ "0|1|
S0S7Sd8S1fS2bS1eS41S93A1M0A1A1S20G0A1A3S8A3").
Hypothesis Pk : ltac2:(tb__ "0|2|
S4S1S0S19Vk;Z0A3S1S0SaVkx;U0A3S0SaVkx';U1M0A3M1A2A2S1S176Vk;A1S1S0SaVkx;G0A3G1A2A2A2").
Hypothesis PTP : ltac2:(tb__ "0|0|
S0S43S141Sa3Vk;A1S93Sa6S93Vk;A2VRpf;S174Vk;A1A5VTP;A3").

Hypothesis Q1e : ltac2:(tb__ "0|1|
S0S7S13bS13S1dS24S41VTP;A1A1A2M0SabG0A1A2S8A3").
Hypothesis Q1o : ltac2:(tb__ "0|1|
S0S9S1dA1S135S24S41VTP;A1A1M0SabS13S1dG0A2A1A2S24VQ1;A1A3").
Hypothesis Q1d : ltac2:(tb__ "0|0|
S0S22Se9S41VTP;A1S24VQ1;A1A2VQ1;A3").
Hypothesis Q1s : ltac2:(tb__ "0|1|
S0S9S1dA1S24VQ1;A1M0S12S1dS89S1dSe0S13S1dG0A2U4A2G0A3S86Se1S1dSe2S124A4A3A3").
Hypothesis Q2e : ltac2:(tb__ "0|1|
S0S22Se9VQ1;S89S1dSe0S13S1dS24VQ1;A1M0A2U4A2G0A3A2VQ2;A3").
Hypothesis Q2u : ltac2:(tb__ "0|0|
S0S7Se5Sf5S124A2S8A3").
Hypothesis Q2n : ltac2:(tb__ "0|0|
S0S7S61S1eVQ1;A1S95A2S8A3").
Hypothesis Q3e : ltac2:(tb__ "0|2|
S0S7S13bS13S1dS24VQ2;A1A2M0S12SaSdSaU8SdSaU0ScSaA1A3A3S12SaS88U1U7A2S88U9M1Se0G0G1A2A2A3A3A2S8A3").
Hypothesis Q4e : ltac2:(tb__ "0|3|
S0S10S22A1S114Se9VQ2;S135S24VQ2;A1M0S12SaSdSaU8SdSaU0M1ScSaA1A3A3S12SaS88U1U7A2S88U9M2Se0S13S1dG0A2G2A2A2A3A3A2A2G1A2S11S22VQ4;A2A3").
Hypothesis QU : ltac2:(tb__ "0|0|
S0S43S48VQ4;S44VTP;A1S45VTP;A1A3VUpf;A3").

Hypothesis HUwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VUpf;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S95A2S8A3A2A2").
Hypothesis Hrun3 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VUpf;S8A5S11G0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|3|
S42Sd9S42R1Vleaves;A3S4S3S99S99S1S0S7S49S46R3A1M0VLnext;R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41G0A1M1A1M2A2S8A3S1S0S7S61G2S95A2S8A3S1S0S7S115R1S94S94A3S8A3S0S7S104S20G1A1S102R1Vbd1;A2Vbd1;A3S8A3A2A2A2A2A2Ls;A2S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx';S95A2S46R4A1R2R1A5S77S2L_;A4Ftp;Frho;A2F_;FLf;").
Hypothesis Hnext : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx';S95A2VLnext;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_loopP : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;S98A2VL;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct HLwf as (W1 & W2 & W3). destruct Fnb as [Fnb1 Fnb2]. destruct Fa0 as [Fa12 Fa13]. destruct F3n as [F3nx F3f].
  destruct HTwf as (V1 & V2 & V3). destruct HUwf as (Y1 & Y2 & Y3).

  eapply JT_run; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }

  eapply (triple_conseq (P := SPA segs (JT kx ndL0) Cfz rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs (JT kx ndL0) rho1 Efz iw (SLit (- fz_frame)) S1 tp w F1 HS) as HS1.
    unfold Cfz. rewrite <- F2e. change (mkAX (set_obj_at S1 iw O_WfzT) (ax_X Efz) (ax_base Efz)) with (ax_setS (mkAX S1 (ax_X Efz) (ax_base Efz)) (set_obj_at S1 iw O_WfzT)).
    apply (SPA_reslice segs (JT kx ndL0) rho1 (mkAX S1 (ax_X Efz) (ax_base Efz)) iw O_WloT O_WfzT tp w F2n); try reflexivity.
    - cbn [ax_S]. rewrite F2e. exact F2s.
    - unfold O_WloT, O_WfzT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
      rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
    - unfold O_WfzT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold WDP, DEEP, fz_frame; lia). unfold WDP, DEEP, fz_frame; lia.
    - exact HS1. }

  assert (HnxC : ss_next (ax_S Cfz) = ss_next (ax_S Efz)) by (unfold Cfz; cbn [ax_S]; exact F3nx).
  unfold ndL0, kept.

  assert (Fnbc : bd_below (ss_next (ax_S Efz)) (bd_subst (s_fz Cfz) bd_fz) = true).
  { pose proof (proj1 (Pos.leb_le _ _) Fnx) as Hnf. unfold NF in Hnf. unfold bd_fz, bd_subst, bi_subst, lf_subst, bd_below, vLEN. cbn [map forallb bi_f fst snd atom_subst asv sv_subst].
    rewrite Fa13. unfold vPlen. cbn [sv_below]. try (assert (E : (44 <? ss_next (ax_S Efz))%positive = true) by (apply Pos.ltb_lt; lia); rewrite E). reflexivity. }
  apply (box_open_T segs AInv CST XGL ALA NF (KcT kx) rhoT P0T [] [] PTrue ok BX0 [(SVar vP, vPlen); (vB, vCap)] [] bd0 (bd_subst (s_fz Cfz) bd_fz) bd1 Cfz rho1 tp _ (BXnn_mk00 0) Fpay).
  { intros _. pose proof (Hcapbd rho1) as HC. assert (LMP : 0 <= LARGE_MIN) by (unfold LARGE_MIN; lia). cbn [length]. lia. }
  intros BXc HBXc Hback.
  rewrite <- (app_nil_r [(SVar vP, vPlen); (vB, vCap)]).
  apply (client_callA segs AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BXc PTrue (Kc_okT T0 MD HMDvm kx) HBXc
           (P0_fz CST) PTrue (fun _ H => H) (fun _ _ _ H => H) Pre_fz nd_fz0 PD_fz NF eq_refl eq_refl eq_refl
           (fun ok' FBc FFc BXc rho2 tp2 Hok HB => HFZ ok' Hok FBc FFc BXc rho2 tp2 HB) eq_refl
           ok Cfz (s_fz Cfz) Rfz (ax_X Cfz) rho1 tp [(SVar vP, vPlen); (vB, vCap)] [] [] (bd_subst (s_fz Cfz) bd_fz) [] ANone (fun _ => False)
           (okKT kx) Fxk Ffr Fcc Ftp Fdom).
  - rewrite HnxC. exact Fnx.
  - rewrite HnxC. pose proof (nd_below_split _ _ Fnb1) as (N1 & N2 & _ & N4). pose proof (nd_below_len _ _ Fnb1) as N5. cbn [nd_tv nd_fr nd_bd nd_am] in N1, N2, N4, N5. apply nd_below_intro; cbn [nd_tv nd_fr nd_bd nd_am]; [exact N1 | exact N2 | exact Fnbc | exact N4 | exact N5].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply payA_self. reflexivity.
  - rewrite HnxC. unfold Cfz in Fpd. cbn [ax_S] in Fpd. rewrite F3nx in Fpd. exact Fpd.
  -
    intros Ai ms HF' HP0 Hav HB HFF HN HD HZ HFR HM HTPA HTok. rewrite app_nil_r in HN, HD, HZ.
    split; [eapply robjs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fro]|].
    split; [eapply xrs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fxr]|].
    unfold P0_fz. split; [|intros c; reflexivity].
    intros a Ha. unfold uval, vDAT, vLEN in Ha. cbn [eval] in Ha. rewrite !rw_call' in Ha. rewrite Fa12, Fa13 in Ha.
    eapply (kept_in_FBx _ rho1 (ss_facts (ax_S Cfz)) [(SVar vP, vPlen); (vB, vCap)] (SVar vP, vPlen) a HF' Fknz); [left; reflexivity|].
    unfold tvv. cbn [fst snd]. exact Ha.
  -
    intros d rho' tp' [<-|[]] Hag'. cbn [fst snd nd_tv nd_bd nd_am nd_fz1 import_tv bd_subst am_subst map app].
    unfold T_afterA3. rewrite import_postA3_full. fold (T_afterA Pre_fz Cfz (s_fz Cfz) Rfz P_fz). rewrite FTT.
    fold kept. fold ndL1.

    eapply (triple_conseq (P := SPA segs (JT kx ndL1) TT rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { exact (box_close segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] PTrue BX0 BXc bd1 kept [] [] ANone (ss_next (ax_S Cfz)) TT rho1 rho' tp' w (BXnn_mk00 0) Hback Hag' ltac:(rewrite HnxC; exact Fnb2) HS). }

    apply triple_factsA. intros HF2.
    assert (Hsp' : 0x7fff80000000 <= bv_unsigned (eval rho' sp0) <= 2 ^ 47 - 224).
    { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF2 | exact U1f]. }
    eapply (triple_conseq (P := SPA segs (JT kx ndL1) Tfz rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { assert (HS1 : SPA segs (JT kx ndL1) (ax_setS TT U1) rho' tp' w).
      { rewrite <- U1e. apply (SPA_reslice segs (JT kx ndL1) rho' TT 1 _ O_WloT tp' w U1n); try reflexivity.
        - rewrite U1e. exact U1s.
        - unfold O_WloT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
          rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
        - unfold O_WloT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP, fz_frame; lia). unfold DEEP, fz_frame; lia.
        - exact HS. }
      pose proof (AxXform.SPA_select segs (JT kx ndL1) rho' (mkAX U1 (ax_X TT) (ax_base TT)) _ tp' w U2 HS1) as HS2.
      pose proof (SPA_merge segs (JT kx ndL1) rho' (mkAX (set_objs U1 (select (ss_objs U1) ([1; 0] ++ seq 2 (length (ss_objs U1) - 2))%nat)) (ax_X TT) (ax_base TT)) 0 U3 tp' w U3e HS2) as HS3.
      rewrite <- UT. exact HS3. }

    eapply JT_run; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 [<-|[]] Hag2. cbn [la_state].
    apply triple_factsA. intros HF3.

    eapply (triple_conseq (P := SPA segs (JT kx ndL1) Cpf rho2 tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { pose proof (SPA_split segs (JT kx ndL1) rho2 Epf 0 (SLit (- PW)) P1 tp' w P1e HS) as HS1.
      assert (HS2 : SPA segs (JT kx ndL1) Cpf0 rho2 tp' w).
      { pose proof (carveT (KcT kx) ndL1 (mkAX P1 (ax_X Epf) (ax_base Epf)) rho2 tp' w N_pf (ss_next P1) HS1) as X.
        cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X; [exact P2w | apply Pos.leb_refl | exact HbE | exact P2c]. }
      unfold Cpf, ax_add_facts.
      change (ax_setS Cpf0 (add_facts (pf_hints Cpf0 k) (ax_S Cpf0))) with (ax_with_facts Cpf0 (pf_hints Cpf0 k ++ ss_facts (ax_S Cpf0))).
      apply (SPA_refacts_JA segs); [exact HS2 | exact P3b |].
      intros tr md HJ HFc. apply Forall_app. split; [|exact HFc]. apply Forall_forall. intros q Hq.
      destruct (P3h q Hq) as [x ->]. apply ms16_holds. }

    assert (HnxP : ss_next (ax_S Cpf) = ss_next (ax_S Epf)).
    { unfold Cpf, Cpf0, ax_add_facts. cbn [ax_S ss_next add_facts P1c]. exact P2n. }
    set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JT kx ndL1 rho2 t tr md).
    assert (JpK : forall r t tr md, Jp r t tr md -> MD md /\ tr = T0 ++ EVk kx) by (intros r t tr md HJ; exact (JT_Kc _ _ _ _ _ _ HJ)).
    assert (HstJp : stableA segs NF Jp).
    { intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *. destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ALA (ss_next (ax_S Cpf)) ndL1 Ai kc rho2 rho2 t tr md md');
        [apply Pos.leb_le; exact Pnx | exact Pnb | apply agree_below_refl | exact Hme | exact HJi]. }
    assert (HokJp : ok_frameA segs ok Jp).
    { apply HOKJ. intros r t tr md HJ. destruct (JpK _ _ _ _ HJ) as [_ ->]. apply Htc. }
    assert (CONT : forall Lf rho3, In Lf (Posts_pf k) -> agree_below (ss_next (ax_S Cpf)) rho2 rho3 ->
              triple segs ok (SPA segs (JT kx' ndL1) (ax_add_facts (ss_facts (ax_S Cpf)) (import_postA (s_pf Cpf k) (PreP k) (la_state Lf) Cpf Rpf)) rho3 tp') (fun _ => False)).
    { intros Lf rho3 HinL Hag3. unfold Posts_pf in HinL. destruct HinL as [<-|[]]. cbn [la_state].
      fold (T_afterA (PreP k) Cpf (s_pf Cpf k) Rpf (P_pf k)). rewrite PTP.

      eapply (triple_conseq (P := fun w => exists rho4, SPA segs (JT kx' ndL1) Upf rho4 tp' w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct w as [tr [ms md]].
        pose proof (AxXform.SPA_select segs (JT kx' ndL1) rho3 TP _ tp' _ Q1e HS) as HS1. rewrite Q1o, Q1d in HS1.
        pose proof (uncarveT (KcT kx') ndL1 (mkAX Q1 (ax_X TP) (ax_base TP)) rho3 tp' tr ms md _ N_pf (Kc_okT T0 MD HMDvm kx') Q1s Q2u eq_refl Q2n HS1) as HS2.
        cbn [ax_S ax_setS ax_X ax_base] in HS2. rewrite Q2e in HS2.
        set (rho4 := rho_absorb rho3 (map lc_obj N_pf) (vms md tp' ms)) in HS2. exists rho4.
        pose proof (AxXform.SPA_select segs (JT kx' ndL1) rho4 (mkAX Q2 (ax_X TP) (ax_base TP)) _ tp' _ Q3e HS2) as HS3.
        pose proof (SPA_merge segs (JT kx' ndL1) rho4 (mkAX (set_objs Q2 (select (ss_objs Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs Q2) - 9))%nat)) (ax_X TP) (ax_base TP)) 0 Q4 tp' _ Q4e HS3) as HS4.
        rewrite <- QU. exact HS4. }
      apply triple_ex. intros rho4.

      eapply JT_run; [exact Hrun3 | exact Y2 | exact Y1 | exact Y3 |].
      intros Lf rho5 HinLf Hag5.
      destruct (Hleaves Lf HinLf) as [(s5 & E1 & E2 & E3 & E4 & E5 & E6)|HX]; [|apply HX].
      eapply (triple_conseq (P := SPA segs (JT kx' ndL1) Lnext (rho_sub rho5 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
      apply (JT_entails kx' (la_state Lf) Lnext s5 ndL1 ndL1 rho5 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS). }
    destruct Pk as [(Ek & Ekx & Ekx')|(Hkok & Ekx & Ekx')].
    +
      subst kx kx'. unfold PreP in *. rewrite Ek in *. cbn [Z.eqb] in *.
      apply (pcallT (KcT 0) (KcT 1) Cpf Pre_pf0 (s_pf Cpf 0) Rpf (Posts_pf 0) rho2 tp' ndL1 Jp (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.Kw Jp 2) (fun _ => False) (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf0_sum ok Jp HstJp).
        -- intros r t tr md HJ. apply HMDfd1. exact (proj1 (JpK _ _ _ _ HJ)).
        -- intros n'. apply HOKJ. intros r t tr md (tr0 & HJ & ->). destruct (JpK _ _ _ _ HJ) as [_ ->].
           destruct (Htc 1%nat) as (tf & Htf & Hpre). exists tf. split; [exact Htf|]. eapply is_prefix_trans; [|exact Hpre].
           cbn [EVk]. rewrite app_nil_r. apply is_prefix_app_mono.
           unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.EVS. change (firstn 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0) with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0. clear. generalize OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0 as l. intros l.
           induction n' as [|n' IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH].
        -- intros n'. apply HOKP. intros r t tr md (tr0 & HJ & ->). destruct (JpK _ _ _ _ HJ) as [_ ->].
           destruct (Htc 1%nat) as (tf & Htf & Hpre). exists tf. split; [exact Htf|]. eapply is_prefix_trans; [|exact Hpre].
           cbn [EVk]. rewrite app_nil_r. apply is_prefix_app_mono.
           unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.EVS. change (firstn 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0) with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0. clear. generalize OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0 as l. intros l.
           induction n' as [|n' IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH].
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' (tr0 & HJ & ->). unfold Jp in HJ. destruct HJ as (Ai & kc & Hav & [Hmd Htr] & REST).
        exists Ai, kc. split; [exact Hav|]. split; [|exact REST]. split; [exact Hmd|]. rewrite Htr. cbn [EVk]. rewrite app_nil_r. reflexivity.
      * exact CONT.
    +
      subst kx kx'.
      assert (EP : PreP k = Pre_pf k).
      { unfold PreP. destruct Hkok as [->|[->| ->]]; reflexivity. }
      rewrite EP in *.
      apply (pcallT (KcT 1) (KcT 1) Cpf (Pre_pf k) (s_pf Cpf k) Rpf (Posts_pf k) rho2 tp' ndL1 Jp Jp (fun _ => False) (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf_sum ok Jp HokJp HstJp k rho6 tp6 Hkok).
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' HJ. exact HJ.
      * exact CONT.
Qed.
End LoopP.

Section LoopE.
Variable k : Z.
Variables kx kx' : nat.
Variables bd0 bd1 : list bitem.
Hypothesis Hcapbd : ltac2:(tb__ "0|0|
S21S7aS7bS7cS10aZ2A2S7fS105Vbd0;R1A2S105Vbd1;R1A2A2A2S10bA2Frho;").
Definition keptE : list (sv * sv) := ltac2:(tb__ "0|1|
SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3").
Definition ndE0 : ndesc := ltac2:(tb__ "0|0|
S63S8dScSbSbS1cS19A2S1cA2A1Vbd0;S62A4").
Definition ndE1 : ndesc := ltac2:(tb__ "0|0|
S63S8dScSbSbS1cS19A2S1cA2A1Vbd1;S62A4").
Variable L : axst.
Variable Lnext : axst.
Variables (Efz : axst) (S1 S2 S3 : sstate) (Rfz : list sobj) (TT : axst) (U1 U3 U4 : sstate) (Tfz : axst).
Variables (bE : sv) (dE : odefault).
Variables (Epf : axst) (P1 : sstate) (Rpf : list sobj) (TP : axst) (Q1 Q2 Q4 : sstate) (Upf : axst).
Variable leaves : list leafA.
Variable iw : nat.

Hypothesis HLwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VL;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S91A2S8A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VL;S8A5S11G0SdS42S4aVEfz;SeaA2ScS42A1A3A2A3").

Hypothesis F1 : ltac2:(tb__ "0|0|
S0S10S22A1S113S41VEfz;A1Viw;S23S80S177A1A1A3S11S22VS1;A2A3").
Hypothesis F2n : ltac2:(tb__ "0|0|
S0S10S1dA1SdbS1dS24VS1;A1Viw;A3S11S1dSa9A2A3").
Hypothesis F2e : ltac2:(tb__ "0|0|
S0S22S14dVS1;Viw;Sb0A3VS2;A3").
Hypothesis F2s : ltac2:(tb__ "0|0|
S0S7S14cVS1;VS2;A2S8A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S7SebS20S41VEfz;A1A1A1S8A3").

Hypothesis F2a : ltac2:(tb__ "0|0|
S0S22S186VS2;Sb1A2VS3;A3").
Hypothesis F2w : swf S3 = true.
Hypothesis F2o : ltac2:(tb__ "0|0|
S0S7S3eS1eVS2;A1Sb1A2S8A3").
Definition CfzE : axst := ltac2:(tb__ "0|1|
S48VS3;S12SbS1cS1cA2M0S44VEfz;A1SdG0Sb4ScG0A1A3A3S45VEfz;A1A3").
Hypothesis F3n : ltac2:(tb__ "0|1|
S1S0S1aS1eVS3;A1S1eS41VEfz;A1M0A1A3S0S9S1fA1S20VS3;A1S20G0A1A3A2").

Hypothesis HFZ : ltac2:(tb__ "0|1|
S77OF_;S68S4cVKcT;Vkx;A1M0R1A3S167VAInv;VCST;VXGL;G0R2A5F_;Fok';").
Hypothesis Fxk : ltac2:(tb__ "0|1|
S0S7S17cS44S8bA1M0G0A2S8A3").
Hypothesis Ffr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S136S8bS13cS9eS8bA1A3S11G0VRfz;A2A3").
Hypothesis Fcc : ltac2:(tb__ "0|0|
S0S7S137S8bS13cS9eS8bA1VRfz;SdS43S165ScS43A1A3A5S8A3").
Hypothesis Ftp : ltac2:(tb__ "0|0|
S0S7S142S4dS9eS8bA1A2S8A3").
Hypothesis Fdom : ltac2:(tb__ "0|0|
S0S7S13fS9eS8bA1S4dA2S8A3").
Hypothesis Fnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VEfz;A1A1A2S8A3").
Hypothesis Fnb : ltac2:(tb__ "0|2|
S1S0S7S61S1eS41VEfz;A1A1M0S63S12SbS1cS1cA2M1S8dScG1A1A3ScSbSbS1cS19A2S1cA2A1Vbd0;S62A4A2S8A3S0S7S106G0Vbd1;A2S8A3A2").
Hypothesis Fpay : ltac2:(tb__ "0|1|
S0S7S107S20S41S8bA1A1S23Z0M0A1G0Vbd0;S12S103S102S9eS8bA1S13dA2Vbd1;A3A5S8A3").
Hypothesis Fpd : ltac2:(tb__ "0|0|
S0S7Sd8S17bS17aS13cS4dS9eS8bA1S1eS41S8bA1A1A4S166A3S8A3").
Hypothesis FspfC : ltac2:(tb__ "0|0|
S0S7SebS20S41S8bA1A1A1S8A3").
Hypothesis Fknz : ltac2:(tb__ "0|0|
S0S7SedS20S41S8bA1A1S8dA2S8A3").
Hypothesis Fro : ltac2:(tb__ "0|0|
S0S7Sd8S1dS1dS16Sf0S20S41S8bA1A1R1A2S116S8dS15SaA1R1A3A2Lo;VRfz;A3S8A3").
Hypothesis Fxr : ltac2:(tb__ "0|1|
S0S7Sd8SbS1cS1cA2M0G0S16SecR1A1S143S8dS15SaA1R1A3A2Lr;S44S8bA1A3S8A3").
Hypothesis Fa0 : ltac2:(tb__ "0|0|
S0S1cS9bS9eS8bA1PdA2S23Z0A1A3").
Hypothesis FTT : ltac2:(tb__ "0|0|
S0S43S141S13cS8bS9eS8bA1VRfz;S165A5VTT;A3").

Hypothesis U1n : ltac2:(tb__ "0|0|
S0S10S1dA1SdbS1dS24S41VTT;A1A1U1A3S11S1dS2eS14bSccS23N250A1A2S23S80Sb3A1A1S23Z0A1ScS2dA1S2fA5A2A3").
Hypothesis U1e : ltac2:(tb__ "0|0|
S0S22S14dS41VTT;A1U1Sa9A3VU1;A3").
Hypothesis U1s : ltac2:(tb__ "0|0|
S0S7S14cS41VTT;A1VU1;A2S8A3").
Hypothesis U1f : ltac2:(tb__ "0|0|
S0S7SebS20S41VTT;A1A1A1S8A3").
Hypothesis U2 : ltac2:(tb__ "0|2|
S0S7S13bS13S1dS24VU1;A1A2M0S12SaSdSaU1SdSaU0ScSaA1A3A3S88U2M1Se0G0G1A2A2A3A2S8A3").
Hypothesis U3e : ltac2:(tb__ "0|3|
S0S10S22A1S114Se9VU1;S135S24VU1;A1M0S12SaSdSaU1SdSaU0M1ScSaA1A3A3S88U2M2Se0S13S1dG0A2G2A2A2A3A2A2G1A2S11S22VU3;A2A3").

Hypothesis U4n : ltac2:(tb__ "0|1|
S0S10S1dA1SdbS1dS24VU3;A1U1A3S11S1dS2eVbE;S23Z0A1M0G0ScS2dA1VdE;A5A2A3").
Hypothesis U4e : drop_obj_at U3 1 = U4.
Hypothesis UT : ltac2:(tb__ "0|0|
S0S43Sd1Sb4S48VU4;S44VTT;A1S45VTT;A1A3A2VTfz;A3").

Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VTfz;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S8eA2S8A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VTfz;S8A5S11G0SdS42S4aVEpf;SeaA2ScS42A1A3A2A3").

Hypothesis P1e : ltac2:(tb__ "0|0|
S0S10S22A1S113S41VEpf;A1U0S23S80S173A1A1A3S11S22VP1;A2A3").
Definition P1cE : sstate := ltac2:(tb__ "0|0|
S30S33VP1;A1S34VP1;A1S32VP1;A1S31VP1;A1S35VP1;A1S12S1dS24VP1;A1S86Se1S1dSe2S124A4A3S20VP1;A1S1eVP1;A1S25VP1;A1A9").
Hypothesis P2w : swf P1cE = true.
Hypothesis P2c : ltac2:(tb__ "0|0|
S0S7Se4S20VP1;A1S24VP1;A1S44VEpf;A1Sf5Sf7S66S8eA1S124A7S8A3").
Hypothesis P2n : ltac2:(tb__ "0|0|
S0S1aS1eVP1;A1S1eS41VEpf;A1A1A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S1cS45VEpf;A1S23S168A1A3").
Definition Cpf0E : axst := ltac2:(tb__ "0|0|
S48S90S44VEpf;A1S45VEpf;A1A3").
Definition CpfE : axst := ltac2:(tb__ "0|0|
S171Sa4S8fVk;A2S8fA2").
Hypothesis P3b : ltac2:(tb__ "0|0|
S0S7Sd8S1fS2bS1eS90A1A1S12S1fSa4S8fVk;A2S20S90A1A3A3S8A3").
Hypothesis P3h : ltac2:(tb__ "0|0|
S1fSd9S1fR1Sa4S8fVk;A2A3S3S1cS1cS0S1fR3S12aR1A1A3Lx;A2F_;Fq;").

Hypothesis Pfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S136S8cSa3Vk;A1Sa6S8cVk;A2A3S11G0VRpf;A2A3").
Hypothesis Pcc : ltac2:(tb__ "0|0|
S0S7S138S8cSa3Vk;A1Sa6S8cVk;A2VRpf;S86S42S43S46S175Vk;A1A4A5S8A3").
Hypothesis Pnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41S8cA1A1A2S8A3").
Hypothesis Pnb : ltac2:(tb__ "0|0|
S0S7S61S1eS41S8cA1A1S8eA2S8A3").
Hypothesis Pfb : ltac2:(tb__ "0|1|
S0S7Sd8S1fS2bS1eS41S8cA1M0A1A1S20G0A1A3S8A3").
Hypothesis Pk : ltac2:(tb__ "0|2|
S4S1S0S19Vk;Z0A3S1S0SaVkx;U0A3S0SaVkx';U1M0A3M1A2A2S1S176Vk;A1S1S0SaVkx;G0A3G1A2A2A2").
Hypothesis PTP : ltac2:(tb__ "0|0|
S0S43S141Sa3Vk;A1S8cSa6S8cVk;A2VRpf;S174Vk;A1A5VTP;A3").

Hypothesis Q1e : ltac2:(tb__ "0|1|
S0S7S13bS13S1dS24S41VTP;A1A1A2M0SabG0A1A2S8A3").
Hypothesis Q1o : ltac2:(tb__ "0|1|
S0S9S1dA1S135S24S41VTP;A1A1M0SabS13S1dG0A2A1A2S24VQ1;A1A3").
Hypothesis Q1d : ltac2:(tb__ "0|0|
S0S22Se9S41VTP;A1S24VQ1;A1A2VQ1;A3").
Hypothesis Q1s : ltac2:(tb__ "0|1|
S0S9S1dA1S24VQ1;A1M0S12S1dS89S1dSe0S13S1dG0A2U4A2G0A3S86Se1S1dSe2S124A4A3A3").
Hypothesis Q2e : ltac2:(tb__ "0|1|
S0S22Se9VQ1;S89S1dSe0S13S1dS24VQ1;A1M0A2U4A2G0A3A2VQ2;A3").
Hypothesis Q2u : ltac2:(tb__ "0|0|
S0S7Se5Sf5S124A2S8A3").
Hypothesis Q2n : ltac2:(tb__ "0|0|
S0S7S61S1eVQ1;A1S8eA2S8A3").
Hypothesis Q3e : ltac2:(tb__ "0|2|
S0S7S13bS13S1dS24VQ2;A1A2M0S12SaSdSaU8SdSaU0ScSaA1A3A3S12SaS88U1U7A2S88U9M1Se0G0G1A2A2A3A3A2S8A3").
Hypothesis Q4e : ltac2:(tb__ "0|3|
S0S10S22A1S114Se9VQ2;S135S24VQ2;A1M0S12SaSdSaU8SdSaU0M1ScSaA1A3A3S12SaS88U1U7A2S88U9M2Se0S13S1dG0A2G2A2A2A3A3A2A2G1A2S11S22VQ4;A2A3").
Hypothesis QU : ltac2:(tb__ "0|0|
S0S43S48VQ4;S44VTP;A1S45VTP;A1A3VUpf;A3").

Hypothesis HUwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VUpf;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S8eA2S8A3A2A2").
Hypothesis Hrun3 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSa1Sa0VUpf;S8A5S11G0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|3|
S42Sd9S42R1Vleaves;A3S4S3S99S99S1S0S7S49S46R3A1M0VLnext;R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41G0A1M1A1M2A2S8A3S1S0S7S61G2S8eA2S8A3S1S0S7S115R1S8dS8dA3S8A3S0S7S104S20G1A1S102R1Vbd1;A2Vbd1;A3S8A3A2A2A2A2A2Ls;A2S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx';S8eA2S46R4A1R2R1A5S77S2L_;A4Ftp;Frho;A2F_;FLf;").
Hypothesis Hnext : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx';S8eA2VLnext;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_loopE : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;S91A2VL;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct HLwf as (W1 & W2 & W3). destruct Fnb as [Fnb1 Fnb2]. pose proof Fa0 as Fa13. destruct F3n as [F3nx F3f].
  destruct HTwf as (V1 & V2 & V3). destruct HUwf as (Y1 & Y2 & Y3).

  eapply JT_run; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }

  eapply (triple_conseq (P := SPA segs (JT kx ndE0) CfzE rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs (JT kx ndE0) rho1 Efz iw (SLit (- fz_frame)) S1 tp w F1 HS) as HS1.
    assert (HS2 : SPA segs (JT kx ndE0) (mkAX S2 (ax_X Efz) (ax_base Efz)) rho1 tp w).
    { rewrite <- F2e. change (mkAX (set_obj_at S1 iw O_WfzT) (ax_X Efz) (ax_base Efz)) with (ax_setS (mkAX S1 (ax_X Efz) (ax_base Efz)) (set_obj_at S1 iw O_WfzT)).
      apply (SPA_reslice segs (JT kx ndE0) rho1 (mkAX S1 (ax_X Efz) (ax_base Efz)) iw O_WloT O_WfzT tp w F2n); try reflexivity.
      - cbn [ax_S]. rewrite F2e. exact F2s.
      - unfold O_WloT, O_WfzT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
        rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
      - unfold O_WfzT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold WDP, DEEP, fz_frame; lia). unfold WDP, DEEP, fz_frame; lia.
      - exact HS1. }
    assert (HS3 : SPA segs (JT kx ndE0) (mkAX S3 (ax_X Efz) (ax_base Efz)) rho1 tp w).
    { rewrite <- F2a. change (mkAX (add_obj S2 O_payE) (ax_X Efz) (ax_base Efz)) with (ax_setS (mkAX S2 (ax_X Efz) (ax_base Efz)) (add_obj (ax_S (mkAX S2 (ax_X Efz) (ax_base Efz))) O_payE)).
      apply (SPA_add_empty segs (JT kx ndE0) rho1 (mkAX S2 (ax_X Efz) (ax_base Efz)) O_payE tp w); [cbn [ax_S]; rewrite F2a; exact F2w | reflexivity | reflexivity | cbn [ax_S]; exact F2o | | exact HS2].
      intros _. unfold O_payE, obj_hi_of, obj_lo_of. cbn [ob_hi ob_lo ob_base eval]. rewrite !soff_lit_small by lia. rewrite lit_unsigned. unfold EMPTY. cbn. lia. }
    pose proof (SPA_x_publish_empty segs (JT kx ndE0) rho1 (mkAX S3 (ax_X Efz) (ax_base Efz)) EMPTY tp w ltac:(unfold EMPTY; lia) eq_refl HS3) as HS4.
    unfold CfzE. change (mkAX S3 (ax_X Efz ++ [X_payE]) (ax_base Efz)) with (ax_setX (ax_setX (mkAX S3 (ax_X Efz) (ax_base Efz)) ((SLit EMPTY, SLit 0) :: ax_X (mkAX S3 (ax_X Efz) (ax_base Efz)))) (ax_X Efz ++ [X_payE])).
    apply SPA_x_sub; [| exact HS4]. cbn [ax_X ax_setX]. intros r Hr. apply in_app_or in Hr as [Hr|[<-|[]]]; [right; exact Hr | left; reflexivity]. }

  assert (HnxC : ss_next (ax_S CfzE) = ss_next (ax_S Efz)) by (unfold CfzE; cbn [ax_S]; exact F3nx).
  unfold ndE0, keptE.

  assert (Fnbc : bd_below (ss_next (ax_S Efz)) (bd_subst (s_fz CfzE) bd_fz) = true).
  { pose proof (proj1 (Pos.leb_le _ _) Fnx) as Hnf. unfold NF in Hnf. unfold bd_fz, bd_subst, bi_subst, lf_subst, bd_below, vLEN. cbn [map forallb bi_f fst snd atom_subst asv sv_subst].
    rewrite Fa13. unfold vPlen. cbn [sv_below]. try (assert (E : (44 <? ss_next (ax_S Efz))%positive = true) by (apply Pos.ltb_lt; lia); rewrite E). reflexivity. }
  apply (box_open_T segs AInv CST XGL ALA NF (KcT kx) rhoT P0T [] [] PTrue ok BX0 [(vB, vCap)] [] bd0 (bd_subst (s_fz CfzE) bd_fz) bd1 CfzE rho1 tp _ (BXnn_mk00 0) Fpay).
  { intros _. pose proof (Hcapbd rho1) as HC. assert (LMP : 0 <= LARGE_MIN) by (unfold LARGE_MIN; lia). cbn [length]. lia. }
  intros BXc HBXc Hback.
  rewrite <- (app_nil_r [(vB, vCap)]).
  apply (client_callA segs AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BXc PTrue (Kc_okT T0 MD HMDvm kx) HBXc
           (P0_fz CST) PTrue (fun _ H => H) (fun _ _ _ H => H) Pre_fz nd_fz0 PD_fz NF eq_refl eq_refl eq_refl
           (fun ok' FBc FFc BXc rho2 tp2 Hok HB => HFZ ok' Hok FBc FFc BXc rho2 tp2 HB) eq_refl
           ok CfzE (s_fz CfzE) Rfz (ax_X CfzE) rho1 tp [(vB, vCap)] [] [] (bd_subst (s_fz CfzE) bd_fz) [] ANone (fun _ => False)
           (okKT kx) Fxk Ffr Fcc Ftp Fdom).
  - rewrite HnxC. exact Fnx.
  - rewrite HnxC. pose proof (nd_below_split _ _ Fnb1) as (N1 & N2 & _ & N4). pose proof (nd_below_len _ _ Fnb1) as N5. cbn [nd_tv nd_fr nd_bd nd_am] in N1, N2, N4, N5. apply nd_below_intro; cbn [nd_tv nd_fr nd_bd nd_am]; [exact N1 | exact N2 | exact Fnbc | exact N4 | exact N5].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply payA_self. reflexivity.
  - rewrite HnxC. unfold CfzE in Fpd. cbn [ax_S] in Fpd. rewrite F3nx in Fpd. exact Fpd.
  -
    intros Ai ms HF' HP0 Hav HB HFF HN HD HZ HFR HM HTPA HTok. rewrite app_nil_r in HN, HD, HZ.
    split; [eapply robjs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fro]|].
    split; [eapply xrs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fxr]|].
    unfold P0_fz. split; [|intros c; reflexivity].
    intros a Ha. exfalso. unfold uval, vDAT, vLEN in Ha. cbn [eval] in Ha. rewrite !rw_call' in Ha. rewrite Fa13 in Ha.
    cbn [eval] in Ha. rewrite lit_unsigned in Ha. change (0 mod 2 ^ 64) with 0 in Ha. lia.
  -
    intros d rho' tp' [<-|[]] Hag'. cbn [fst snd nd_tv nd_bd nd_am nd_fz1 import_tv bd_subst am_subst map app].
    unfold T_afterA3. rewrite import_postA3_full. fold (T_afterA Pre_fz CfzE (s_fz CfzE) Rfz P_fz). rewrite FTT.
    fold keptE. fold ndE1.

    eapply (triple_conseq (P := SPA segs (JT kx ndE1) TT rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { exact (box_close segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] PTrue BX0 BXc bd1 keptE [] [] ANone (ss_next (ax_S CfzE)) TT rho1 rho' tp' w (BXnn_mk00 0) Hback Hag' ltac:(rewrite HnxC; exact Fnb2) HS). }

    apply triple_factsA. intros HF2.
    assert (Hsp' : 0x7fff80000000 <= bv_unsigned (eval rho' sp0) <= 2 ^ 47 - 224).
    { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF2 | exact U1f]. }
    eapply (triple_conseq (P := SPA segs (JT kx ndE1) Tfz rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { assert (HS1 : SPA segs (JT kx ndE1) (ax_setS TT U1) rho' tp' w).
      { rewrite <- U1e. apply (SPA_reslice segs (JT kx ndE1) rho' TT 1 _ O_WloT tp' w U1n); try reflexivity.
        - rewrite U1e. exact U1s.
        - unfold O_WloT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
          rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
        - unfold O_WloT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP, fz_frame; lia). unfold DEEP, fz_frame; lia.
        - exact HS. }
      pose proof (AxXform.SPA_select segs (JT kx ndE1) rho' (mkAX U1 (ax_X TT) (ax_base TT)) _ tp' w U2 HS1) as HS2.
      pose proof (SPA_merge segs (JT kx ndE1) rho' (mkAX (set_objs U1 (select (ss_objs U1) ([1; 0] ++ seq 2 (length (ss_objs U1) - 2))%nat)) (ax_X TT) (ax_base TT)) 0 U3 tp' w U3e HS2) as HS3.
      pose proof (SPA_drop_empty segs (JT kx ndE1) rho' (mkAX U3 (ax_X TT) (ax_base TT)) 1 _ tp' w U4n
                    ltac:(intros _; unfold obj_hi_of, obj_lo_of; cbn [ob_hi ob_lo]; apply Z.le_refl) HS3) as HS4.
      cbn [ax_S ax_setS ax_X ax_base] in HS4. rewrite U4e in HS4.
      rewrite <- UT. unfold dropX. apply SPA_x_sub; [cbn [ax_X]; apply In_dropX | exact HS4]. }

    eapply JT_run; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 [<-|[]] Hag2. cbn [la_state].
    apply triple_factsA. intros HF3.

    eapply (triple_conseq (P := SPA segs (JT kx ndE1) CpfE rho2 tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { pose proof (SPA_split segs (JT kx ndE1) rho2 Epf 0 (SLit (- PW)) P1 tp' w P1e HS) as HS1.
      assert (HS2 : SPA segs (JT kx ndE1) Cpf0E rho2 tp' w).
      { pose proof (carveT (KcT kx) ndE1 (mkAX P1 (ax_X Epf) (ax_base Epf)) rho2 tp' w N_pf (ss_next P1) HS1) as X.
        cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X; [exact P2w | apply Pos.leb_refl | exact HbE | exact P2c]. }
      unfold CpfE, ax_add_facts.
      change (ax_setS Cpf0E (add_facts (pf_hints Cpf0E k) (ax_S Cpf0E))) with (ax_with_facts Cpf0E (pf_hints Cpf0E k ++ ss_facts (ax_S Cpf0E))).
      apply (SPA_refacts_JA segs); [exact HS2 | exact P3b |].
      intros tr md HJ HFc. apply Forall_app. split; [|exact HFc]. apply Forall_forall. intros q Hq.
      destruct (P3h q Hq) as [x ->]. apply ms16_holds. }

    assert (HnxP : ss_next (ax_S CpfE) = ss_next (ax_S Epf)).
    { unfold CpfE, Cpf0E, ax_add_facts. cbn [ax_S ss_next add_facts P1cE]. exact P2n. }
    set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JT kx ndE1 rho2 t tr md).
    assert (JpK : forall r t tr md, Jp r t tr md -> MD md /\ tr = T0 ++ EVk kx) by (intros r t tr md HJ; exact (JT_Kc _ _ _ _ _ _ HJ)).
    assert (HstJp : stableA segs NF Jp).
    { intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *. destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ALA (ss_next (ax_S CpfE)) ndE1 Ai kc rho2 rho2 t tr md md');
        [apply Pos.leb_le; exact Pnx | exact Pnb | apply agree_below_refl | exact Hme | exact HJi]. }
    assert (HokJp : ok_frameA segs ok Jp).
    { apply HOKJ. intros r t tr md HJ. destruct (JpK _ _ _ _ HJ) as [_ ->]. apply Htc. }
    assert (CONT : forall Lf rho3, In Lf (Posts_pf k) -> agree_below (ss_next (ax_S CpfE)) rho2 rho3 ->
              triple segs ok (SPA segs (JT kx' ndE1) (ax_add_facts (ss_facts (ax_S CpfE)) (import_postA (s_pf CpfE k) (PreP k) (la_state Lf) CpfE Rpf)) rho3 tp') (fun _ => False)).
    { intros Lf rho3 HinL Hag3. unfold Posts_pf in HinL. destruct HinL as [<-|[]]. cbn [la_state].
      fold (T_afterA (PreP k) CpfE (s_pf CpfE k) Rpf (P_pf k)). rewrite PTP.

      eapply (triple_conseq (P := fun w => exists rho4, SPA segs (JT kx' ndE1) Upf rho4 tp' w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct w as [tr [ms md]].
        pose proof (AxXform.SPA_select segs (JT kx' ndE1) rho3 TP _ tp' _ Q1e HS) as HS1. rewrite Q1o, Q1d in HS1.
        pose proof (uncarveT (KcT kx') ndE1 (mkAX Q1 (ax_X TP) (ax_base TP)) rho3 tp' tr ms md _ N_pf (Kc_okT T0 MD HMDvm kx') Q1s Q2u eq_refl Q2n HS1) as HS2.
        cbn [ax_S ax_setS ax_X ax_base] in HS2. rewrite Q2e in HS2.
        set (rho4 := rho_absorb rho3 (map lc_obj N_pf) (vms md tp' ms)) in HS2. exists rho4.
        pose proof (AxXform.SPA_select segs (JT kx' ndE1) rho4 (mkAX Q2 (ax_X TP) (ax_base TP)) _ tp' _ Q3e HS2) as HS3.
        pose proof (SPA_merge segs (JT kx' ndE1) rho4 (mkAX (set_objs Q2 (select (ss_objs Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs Q2) - 9))%nat)) (ax_X TP) (ax_base TP)) 0 Q4 tp' _ Q4e HS3) as HS4.
        rewrite <- QU. exact HS4. }
      apply triple_ex. intros rho4.

      eapply JT_run; [exact Hrun3 | exact Y2 | exact Y1 | exact Y3 |].
      intros Lf rho5 HinLf Hag5.
      destruct (Hleaves Lf HinLf) as [(s5 & E1 & E2 & E3 & E4 & E5 & E6)|HX]; [|apply HX].
      eapply (triple_conseq (P := SPA segs (JT kx' ndE1) Lnext (rho_sub rho5 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
      apply (JT_entails kx' (la_state Lf) Lnext s5 ndE1 ndE1 rho5 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS). }
    destruct Pk as [(Ek & Ekx & Ekx')|(Hkok & Ekx & Ekx')].
    +
      subst kx kx'. unfold PreP in *. rewrite Ek in *. cbn [Z.eqb] in *.
      apply (pcallT (KcT 0) (KcT 1) CpfE Pre_pf0 (s_pf CpfE 0) Rpf (Posts_pf 0) rho2 tp' ndE1 Jp (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.Kw Jp 2) (fun _ => False) (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf0_sum ok Jp HstJp).
        -- intros r t tr md HJ. apply HMDfd1. exact (proj1 (JpK _ _ _ _ HJ)).
        -- intros n'. apply HOKJ. intros r t tr md (tr0 & HJ & ->). destruct (JpK _ _ _ _ HJ) as [_ ->].
           destruct (Htc 1%nat) as (tf & Htf & Hpre). exists tf. split; [exact Htf|]. eapply is_prefix_trans; [|exact Hpre].
           cbn [EVk]. rewrite app_nil_r. apply is_prefix_app_mono.
           unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.EVS. change (firstn 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0) with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0. clear. generalize OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0 as l. intros l.
           induction n' as [|n' IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH].
        -- intros n'. apply HOKP. intros r t tr md (tr0 & HJ & ->). destruct (JpK _ _ _ _ HJ) as [_ ->].
           destruct (Htc 1%nat) as (tf & Htf & Hpre). exists tf. split; [exact Htf|]. eapply is_prefix_trans; [|exact Hpre].
           cbn [EVk]. rewrite app_nil_r. apply is_prefix_app_mono.
           unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.EVS. change (firstn 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0) with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0. clear. generalize OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.MSG0 as l. intros l.
           induction n' as [|n' IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH].
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' (tr0 & HJ & ->). unfold Jp in HJ. destruct HJ as (Ai & kc & Hav & [Hmd Htr] & REST).
        exists Ai, kc. split; [exact Hav|]. split; [|exact REST]. split; [exact Hmd|]. rewrite Htr. cbn [EVk]. rewrite app_nil_r. reflexivity.
      * exact CONT.
    +
      subst kx kx'.
      assert (EP : PreP k = Pre_pf k).
      { unfold PreP. destruct Hkok as [->|[->| ->]]; reflexivity. }
      rewrite EP in *.
      apply (pcallT (KcT 1) (KcT 1) CpfE (Pre_pf k) (s_pf CpfE k) Rpf (Posts_pf k) rho2 tp' ndE1 Jp Jp (fun _ => False) (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf_sum ok Jp HokJp HstJp k rho6 tp6 Hkok).
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' HJ. exact HJ.
      * exact CONT.
Qed.
End LoopE.

Section ExitFreeP.
Variable kx : nat.
Variable n : Z.
Variables bd1 bdJ : list bitem.
Definition keptX : list (sv * sv) := ltac2:(tb__ "0|1|
SdSbS1cS1cA2M0SfS1cS1cS2aS9fA1Sc2A4SdG0SfS1cS1cSc3Sc4A4ScG0A1A3A3").
Definition ndLX : ndesc := ltac2:(tb__ "0|0|
S63SddScSbSbS1cS19A2S1cA2A1Vbd1;S62A4").
Definition ndJX : ndesc := ltac2:(tb__ "0|1|
S63SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3ScSbSbS1cS19A2S1cA2A1VbdJ;S62A4").
Variables (LX : axst) (R : list sobj) (T : axst) (leaves : list leafA).
Definition CP : axst := ltac2:(tb__ "0|0|
Sd1SfS1cS1cS2aS9fA1Sc2A4VLX;A2").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S136SdcScbSa8SdcA1A3S11G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S7S137SdcScbSa8SdcA1VR;SdS43ScfScS43A1A3A5S8A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S7S142S4dSa8SdcA1A2S8A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VLX;A1A1A2S8A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S7S61S1eS41VLX;A1A1M0SdfA2S8A3S0S7S106G0VbdJ;A2S8A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|1|
S1S0S1cS9bSa8SdcA1M0PcA2S2aS9fA1A3S0S1cS9bG0PdA2Sc2A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S0S7S107S20S41SdcA1A1S23Z0A1S109Vbd1;VbdJ;A5S8A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S7SebS20S41SdcA1A1A1S8A3").
Hypothesis Hro : ltac2:(tb__ "0|0|
S0S7SeeS20S41SdcA1A1SddS11SaU0A2VR;A4S8A3").
Hypothesis Hxr : ltac2:(tb__ "0|1|
S0S7SefS20S41SdcA1M0A1SddS11SaU0A2S24G0A1SecS44SdcA1A6S8A3").
Hypothesis HvP : ltac2:(tb__ "0|0|
S0S7SdaS1fS27S28S23Z1000A1S2aS9fA1A2A1S20S41SdcA1A1A3S8A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S43S141ScbSdcSa8SdcA1VR;ScfA5VT;A3").
Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VT;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1SdeA2S8A3A2A2").
Hypothesis Hrun : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSceScdVT;S8A5S11G0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|5|
S42Sd9S42R1Vleaves;A3S3S99S99S1S0S7S49S46R3A1M0Sa2Vn;S23Z0A1A2R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41G0A1M1A1M2A2S8A3S1S0S7S61G2SdeA2S8A3S1S0S7S115R1SdSbS1cS1cA2M3SfS1cS1cSc3Sc4A4ScG3A1A3M4G4A3S8A3S0S7S104S20G1A1S102R1VbdJ;A2VbdJ;A3S8A3A2A2A2A2A2Ls;A2F_;FLf;").

Variable CondJ : Prop.
Hypothesis Hcond : ltac2:(tb__ "0|0|
S21S87S1fS26R1A1S20S41VLX;A1A1A3VP0T;VrhoT;A1S13eS4dVrhoT;R3A3VCondJ;F_;F_;F_;Frho;").
Hypothesis HJ : ltac2:(tb__ "0|0|
VCondJ;S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;SdeA2Sa2Vn;S23Z0A1A2R2R1A5S77S2L_;A4Ftp;Frho;F_;").

Lemma X_freeP : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;SdfA2VLX;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct Hs12 as [Hs12a Hs13]. destruct HTwf as (V1 & V2 & V3).
  apply triple_factsA. intros HF. apply triple_JT_pre. intros HP0' Hav'. pose proof (Hcond rho HF HP0' Hav') as HC.
  eapply (triple_conseq (P := SPA segs (JT kx ndLX) CP rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { unfold CP, dropX. apply SPA_x_sub; [|exact HS]. apply In_dropX. }
  assert (HnxC : ss_next (ax_S CP) = ss_next (ax_S LX)) by reflexivity.
  unfold ndLX, keptX.
  apply (free_callA segs AE_A AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ok [] UStopLe CP (s_fp CP) R rho tp
           (NDA [(SVar vP, vPlen); (vB, vCap)] [] bd1 ANone) 0%nat (SVar vP, vPlen) bdJ (fun _ => False) free_shape_nil (okKT kx) AC Hfr Hcc HcT).
  - rewrite HnxC. exact Hnx.
  - rewrite HnxC. exact Hnb1.
  - rewrite HnxC. exact Hnb2.
  - reflexivity.
  - apply payA_of_bud_pay. exact Hpay.
  - intros A A' _ _. exact I.
  - apply (site_ok_drv (NDA [(SVar vP, vPlen); (vB, vCap)] [] bd1 ANone) CP (s_fp CP) R rho (Some 0%nat) (Some (uval rho (wsub_get (s_fp CP) 12%positive)))); try assumption.
    + intros Ai HF' HN HZ. exists (SVar vP, vPlen). split; [reflexivity|]. rewrite Hs12a.
      assert (Hnz : tnz rho (SVar vP, vPlen)).
      { unfold tnz. cbn [fst]. pose proof (holds_mem _ _ _ HF' HvP) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
        rewrite Z.mod_small in X by lia. unfold uval in *. lia. }
      split; [exact Hnz | reflexivity].
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. split; [|split; [| exact I]].
      * unfold tnz. cbn [fst]. pose proof (holds_mem _ _ _ HF' HvP) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
        rewrite Z.mod_small in X by lia. lia.
      * rewrite Hs12a, Hs13. reflexivity.
  - intros rho' tp'. unfold PreF, PostF in HT. rewrite HT. cbn [nd_tv nd_fr nd_am remove_nth]. fold ndJX.
    eapply JT_run; [exact Hrun | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 HinLf Hag2. destruct (Hleaves Lf HinLf) as (s5 & E1 & E2 & E3 & E4 & E5 & E6).
    eapply (triple_conseq (P := SPA segs (JT kx ndJX) (J_E n (SLit 0)) (rho_sub rho2 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply (HJ HC)].
    apply (JT_entails kx (la_state Lf) (J_E n (SLit 0)) s5 ndJX ndJX rho2 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.
End ExitFreeP.

Section ExitFreeE.
Variable kx : nat.
Variable n : Z.
Variables bd1 bdJ : list bitem.
Definition ndEX : ndesc := ltac2:(tb__ "0|1|
S63SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3ScSbSbS1cS19A2S1cA2A1Vbd1;S62A4").
Definition ndJE : ndesc := ltac2:(tb__ "0|1|
S63SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3ScSbSbS1cS19A2S1cA2A1VbdJ;S62A4").
Variables (LX : axst) (R : list sobj) (T : axst) (leaves : list leafA).
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S136VLX;SaeSacVLX;A1A3S11G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S7S137VLX;SaeSacVLX;A1VR;SdS43Sb2ScS43A1A3A5S8A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S7S142S4dSacVLX;A1A2S8A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VLX;A1A1A2S8A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S7S61S1eS41VLX;A1A1M0S16dA2S8A3S0S7S106G0VbdJ;A2S8A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|1|
S0S7S107S20S41VLX;A1A1S23Z0M0A1G0Vbd1;VbdJ;A5S8A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S7SebS20S41VLX;A1A1A1S8A3").
Hypothesis Hro : ltac2:(tb__ "0|1|
S0S7SeeS20S41VLX;A1A1SdSbS1cS1cA2M0SfS1cS1cSc3Sc4A4ScG0A1A3S15SaA1VR;A4S8A3").
Hypothesis Hxr : ltac2:(tb__ "0|2|
S0S7SefS20S41VLX;A1M0A1SdSbS1cS1cA2M1SfS1cS1cSc3Sc4A4ScG1A1A3S15SaA1S24G0A1SecS44VLX;A1A6S8A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S43S141SaeVLX;SacVLX;A1VR;Sb2A5VT;A3").
Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VT;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S16cA2S8A3A2A2").
Hypothesis Hrun : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSceScdVT;S8A5S11G0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|5|
S42Sd9S42R1Vleaves;A3S3S99S99S1S0S7S49S46R3A1M0Sa2Vn;S23Z0A1A2R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41G0A1M1A1M2A2S8A3S1S0S7S61G2S16cA2S8A3S1S0S7S115R1SdSbS1cS1cA2M3SfS1cS1cSc3Sc4A4ScG3A1A3M4G4A3S8A3S0S7S104S20G1A1S102R1VbdJ;A2VbdJ;A3S8A3A2A2A2A2A2Ls;A2F_;FLf;").
Variable CondJ : Prop.
Hypothesis Hcond : ltac2:(tb__ "0|0|
S21S87S1fS26R1A1S20S41VLX;A1A1A3VP0T;VrhoT;A1S13eS4dVrhoT;R3A3VCondJ;F_;F_;F_;Frho;").
Hypothesis HJ : ltac2:(tb__ "0|0|
VCondJ;S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;S16cA2Sa2Vn;S23Z0A1A2R2R1A5S77S2L_;A4Ftp;Frho;F_;").

Lemma X_freeE : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;Vkx;S16dA2VLX;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct HTwf as (V1 & V2 & V3).
  apply triple_factsA. intros HF. apply triple_JT_pre. intros HP0' Hav'. pose proof (Hcond rho HF HP0' Hav') as HC.
  unfold ndEX.
  apply (free_null_callA segs AE_A AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ok [] UStopLe LX (s_fn LX) R rho tp
           (NDA [(vB, vCap)] [] bd1 ANone) bdJ (fun _ => False) eq_refl (okKT kx) AC Hfr Hcc HcT Hnx Hnb1 Hnb2).
  - apply payA_of_bud_pay. exact Hpay.
  - intros A A' _. exact I.
  - apply (site_ok_drv (NDA [(vB, vCap)] [] bd1 ANone) LX (s_fn LX) R rho None None); try assumption.
    + intros Ai HF' HN HZ. exact I.
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. exact I.
  - intros rho' tp'. unfold PreFN, PostFN in HT. rewrite HT. cbn [nd_tv nd_fr nd_am]. fold ndJE.
    eapply JT_run; [exact Hrun | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 HinLf Hag2. destruct (Hleaves Lf HinLf) as (s5 & E1 & E2 & E3 & E4 & E5 & E6).
    eapply (triple_conseq (P := SPA segs (JT kx ndJE) (J_E n (SLit 0)) (rho_sub rho2 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply (HJ HC)].
    apply (JT_entails kx (la_state Lf) (J_E n (SLit 0)) s5 ndJE ndJE rho2 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.
End ExitFreeE.

Definition N_mc : list lcarve := ltac2:(tb__ "0|d|
SdSbSbS19S19A2M0S9SbSbS19SaA2M1S19A2M2A1M3A2M4SfG0G3SfS19S19Zf20d8M5Zf20daA4SdG2SfG1S19SfS19SaG5U1M6A4Z1M7A4SdG2SfG1S19SfS19SaZf20d9G6A4G7A4ScG2A1M8A3A3A4SdG4SfG0G3SfS19S19Zf20e0M9Zf20f8A4SdG2SfG1S19SfS19SaG9U8MaA4Z7fffffffffffA4SdG2SfG1S19SfS19SaZf20e8GaA4Z0MbA4SdG2SfG1S19SfS19SaZf20f0GaA4GbA4G8A3A3A3A4SdG4SfG0G3SfS19S19Ze9ae8McZe9af0A4SdG2SfG1S19SfS19SaGcGaA4Zddf74A4G8A3A4ScG4A1A3A3A3").
Lemma N_mc_eq : ltac2:(tb__ "0|0|
S0S9S1dA1S86Se1S1dSe2S126A4SbdA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition mc_needb (facts : list sprop) : bool := ltac2:(tb__ "0|2|
Sd8S1fS1fSdaS1fS27R1A1Vfacts;A3Lf;SdS1fS28S14bS14bSc6Sc2A2S23Z6A1A2M0Sc7A2SdS1fS28Sc7G0A2SdS1fS28Sc6S23Z7fffA1A2SdS1fS28Sc2S23S7dZ2Z1aA2A1M1A2SdS1fS28Sc7Sc4A2SdS1fS28Sc4G1A2SdS1fS28Sc3S23Sd4A1A2ScS1fA1A3A3A3A3A3A3A3A3").
Definition O_srcM : sobj := ltac2:(tb__ "0|0|
S2eSc3S14bSc6S23Z6A1A2Sc7ScS2dA1S2fA5").

Lemma mc_src_range : ltac2:(tb__ "0|5|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S12bR2A1S8A3S1S0SbS19S19A2S3aR4Sa7A2S3aR4S127A2A3S1S1S7aZ0S39R4Sa7A2M0A2S7aG0S38R4Sa7A2M1A2A2S1S7eS7fG1G0A2S7dZ2Z3fA2M2A2S1S7aS39R4S127A2M3S38R4S127A2M4A2S7eS7fG4G3A2G2A2A2A2A2A2F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF Hn. unfold mc_needb in Hn. cbn [forallb] in Hn.
  repeat (apply andb_prop in Hn as [?X Hn]).
  repeat match goal with H : existsb (sprop_eqb _) facts = true |- _ => apply (holds_mem rho facts) in H; [|exact HF] end.
  unfold vB, vClen, vPlen, vLen, vCap in *. cbn [holds eval] in *. rewrite ?U_add, ?U_lit, <- ?M64v_eq in *.
  pose proof (urange (rw rho 40%positive)) as R30. pose proof (urange (rw rho 41%positive)) as R31. pose proof (urange (rw rho 42%positive)) as R32.
  pose proof (urange (rw rho 43%positive)) as R33. pose proof (urange (rw rho 44%positive)) as R34.
  unfold ACEIL, ATOPHI in *.
  rewrite ?(Z.mod_small 6), ?(Z.mod_small 32767), ?(Z.mod_small (2 ^ 26)), ?(Z.mod_small 140737479966720) in * by lia.
  repeat match goal with H : context [((?a + ?b) mod 2 ^ 64)] |- _ => rewrite (Z.mod_small (a + b) (2 ^ 64)) in H by lia end.
  unfold obj_range, obj_lo_of, obj_hi_of, O_srcT, O_srcM. cbn [ob_base ob_lo ob_hi].
  rewrite !soff_snorm. unfold U. unfold vB, vClen, vPlen, vLen. cbn [eval]. rewrite ?U_add, ?U_lit, <- ?M64v_eq. cbn [eval].
  cbn [eval] in *. rewrite ?lit_unsigned in *.
  change (32767 mod 2 ^ 64) with 32767 in *. change (2 ^ 26 mod 2 ^ 64) with (2 ^ 26) in *.
  change (140737479966720 mod 2 ^ 64) with 140737479966720 in *. change (6 mod 2 ^ 64) with 6 in *. change (0 mod 2 ^ 64) with 0 in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho 43%positive) + bv_unsigned (rw rho 44%positive))) in * by lia.
  rewrite (Z.mod_small (bv_unsigned (rw rho 43%positive) + bv_unsigned (rw rho 44%positive) + 6)) in * by lia.
  rewrite (Z.mod_small (bv_unsigned (rw rho 43%positive) + 6)) in * by lia.
  rewrite (Z.mod_small (bv_unsigned (rw rho 40%positive) + (bv_unsigned (rw rho 43%positive) + 6))) in * by lia.
  rewrite !snorm_small by lia. split; [f_equal; lia|]. repeat split; lia.
Qed.

Section SegMC.
Variable bd0 : list bitem.
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S63S129ScSbSbS1cS19A2S1cA2A1Vbd0;S62A4").
Variables (TM Emc : axst) (W1 W2 B1 B2 B3 RS : sstate) (i0 i1 i2 : nat) (Rmc : list sobj) (TMC : axst).
Variables (V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 : sstate) (Umc Lp : axst) (sLP : wsub) (LP0 : axst)  .

Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VTM;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S111A2S8A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSb8SadVTM;S8A5S11G0SdS42S4aVEmc;SeaA2ScS42A1A3A2A3").

Hypothesis M1 : ltac2:(tb__ "0|0|
S0S10S22A1S113S41VEmc;A1U0S23N870A1A3S11S22VW1;A2A3").
Hypothesis M2 : ltac2:(tb__ "0|0|
S0S10S22A1S113VW1;U0S23N8c0A1A3S11S22VW2;A2A3").
Hypothesis M3 : ltac2:(tb__ "0|0|
S0S10S22A1S113VW2;Vi0;S23Z6A1A3S11S22VB1;A2A3").
Hypothesis M4 : ltac2:(tb__ "0|0|
S0S10S22A1S113VB1;Vi1;S14bSc6S23Z6A1A2A3S11S22VB2;A2A3").
Hypothesis M5 : ltac2:(tb__ "0|0|
S0S10S22A1S113VB2;Vi2;Sc7A3S11S22VB3;A2A3").

Hypothesis M6b : ltac2:(tb__ "0|0|
S0S7Sd8S1fS2bS1eVB3;A1A1S12S1fSbcS20VB3;A1A3A3S8A3").
Hypothesis M6z : ltac2:(tb__ "0|0|
S0S7SedS20VB3;A1S129A2S8A3").
Definition B3h : sstate := add_facts mc_hints B3.
Definition B3c : sstate := ltac2:(tb__ "0|0|
S30S33S10fA1S34S10fA1S32S10fA1S31S10fA1S35S10fA1S12S1dS24S10fA1S86Se1S1dSe2S126A4A3S20S10fA1S1eS10fA1S25S10fA1A9").
Hypothesis M6w : swf B3c = true.
Hypothesis M6c : ltac2:(tb__ "0|0|
S0S7Se4S20S10fA1S24S10fA1S44VEmc;A1Sf5Sf7S66S111A1S126A7S8A3").
Hypothesis M6x : ltac2:(tb__ "0|1|
S1S0S1aS1eVB3;A1S1eS41VEmc;A1M0A1A3S0S9S1fA1S20VB3;A1S20G0A1A3A2").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S1cS45VEmc;A1S23S168A1A3").
Hypothesis M7n : ltac2:(tb__ "0|0|
S0S10S1dA1SdbS1dS24S112A1Vi2;A3S11S1dS127A2A3").
Hypothesis M7e : ltac2:(tb__ "0|0|
S0S22S14dS112Vi2;Sa7A3VRS;A3").
Hypothesis M7s : ltac2:(tb__ "0|0|
S0S7S14cS112VRS;A2S8A3").
Hypothesis M7f : ltac2:(tb__ "0|1|
S1S0S7S12bS20S41VEmc;A1M0A1A1S8A3S0S1aS1eVRS;A1S1eG0A1A3A2").
Definition Cmc : axst := ltac2:(tb__ "0|0|
S48VRS;S44VEmc;A1S45VEmc;A1A3").

Hypothesis Cfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S136S110S16eSafS110A1A3S11G0VRmc;A2A3").
Hypothesis Ccc : ltac2:(tb__ "0|0|
S0S7S138S110S16eSafS110A1VRmc;S86S42S43S46S170A4A5S8A3").
Hypothesis Cnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41S110A1A1A2S8A3").
Hypothesis Cnb : ltac2:(tb__ "0|0|
S0S7S61S1eS41S110A1A1S111A2S8A3").
Hypothesis Cfb : ltac2:(tb__ "0|1|
S0S7Sd8S1fS2bS1eS41S110A1M0A1A1S20G0A1A3S8A3").
Hypothesis ChB : ltac2:(tb__ "0|0|
S0S7SdaS1fS27S28S23Z1000A1Sc3A2A1S20S41S110A1A1A3S8A3").
Hypothesis CT : ltac2:(tb__ "0|0|
S0S43S141S16eS110SafS110A1VRmc;S16fA5VTMC;A3").

Hypothesis V1e : ltac2:(tb__ "0|4|
S1S0S7S13bS13S1dS24S41VTMC;A1M0A1M1A2M2Sc0G2A1M3A2S8A3S0S22Se9G0S135G1G3A2A2VV1;A3A2").
Hypothesis V2e : ltac2:(tb__ "0|2|
S1S0S9S1dA1S24VV1;A1M0S12S1dS89S1dSe0S13S1dG0A2U3A2G0A3M1S86Se1S1dSe2S126A4A3A3S1S0S22Se9VV1;G1A2VV2;A3S1S0S7Se5Sf5S126A2S8A3S0S7S61S1eVV1;A1S111A2S8A3A2A2A2").
Hypothesis V3e : ltac2:(tb__ "0|1|
S1S0S10S1dA1SdbS1dS24VV2;A1U3M0A3S11S1dSa7A2A3S1S0S22S14dVV2;G0S127A3VV3;A3S1S0S7S14cVV2;VV3;A2S8A3S0S7S12bS20VV2;A1A1S8A3A2A2A2").
Hypothesis V4e : ltac2:(tb__ "0|1|
S1S0S10S1dA1SdbS1dS24VV3;A1U1M0A3S11S1dS2eS14bSccS23N940A1A2S23N50A1S23Z0A1ScS2dA1S2fA5A2A3S1S0S22S14dVV3;G0SbaA3VV4;A3S1S0S7S14cVV3;VV4;A2S8A3S0S7SebS20VV3;A1A1S8A3A2A2A2").
Hypothesis V5e : ltac2:(tb__ "0|3|
S1S0S7S13bS13S1dS24VV4;A1M0A2M1Sc1G1A1M2A2S8A3S0S22Se9VV4;S135G0G2A2A2VV5;A3A2").
Hypothesis V6e : ltac2:(tb__ "0|0|
S0S10S22A1S114VV5;U0A2S11S22VV6;A2A3").
Hypothesis V7e : ltac2:(tb__ "0|0|
S0S10S22A1S114VV6;U0A2S11S22VV7;A2A3").
Hypothesis V8e : ltac2:(tb__ "0|2|
S1S0S7S13bS13S1dS24VV7;A1M0A2SbfG0A1M1A2S8A3S0S22Se9VV7;S135G0G1A2A2VV8;A3A2").
Hypothesis V9e : ltac2:(tb__ "0|2|
S1S0S10S22A1M0S114VV8;U0M1A2S11S22VV9;A2A3S1S0G0S114VV9;G1A2S11S22VV10;A2A3S0G0S114VV10;G1A2S11S22VV11;A2A3A2A2").
Hypothesis VU : ltac2:(tb__ "0|0|
S0S43S48VV11;S44VTMC;A1S45VTMC;A1A3VUmc;A3").

Hypothesis HUwf : ltac2:(tb__ "0|2|
S1S0S7S74S4dS1eS41VUmc;A1M0A1M1A2S8A3S1S0S7S25G0A1SeA3S0S7S61G1S111A2S8A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSb9SadVUmc;S8A5S11G0SdS42S4aVLp;SeaA2ScS42A1A3A2A3").
Hypothesis HLp : ltac2:(tb__ "0|2|
S1S0S7S49VLp;VLP0;VsLP;A3S8A3S1S0S7S9aVsLP;S4dA2S8A3S1S0S7S74S4dS1eS41VLp;A1M0A1M1A2S8A3S1S0S7S61G1S111A2S8A3S1S0S7S115VsLP;S129S129A3S8A3S0S7S104S20G0A1S102VsLP;Vbd0;A2Vbd0;A3S8A3A2A2A2A2A2").
Hypothesis Hnext : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S111A2VLP0;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_mc : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S111A2VTM;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct HTwf as (W1' & W2' & W3'). destruct M6x as [M6nx M6fx]. destruct M7f as [M6f1 M7nx]. destruct HUwf as (Y1 & Y2 & Y3).
  destruct V1e as [V1a V1b]. destruct V2e as (V2a & V2b & V2c & V2d). destruct V3e as (V3a & V3b & V3c & V3d). destruct V4e as (V4a & V4b & V4c & V4d).
  destruct V5e as [V5a V5b]. destruct V8e as [V8a V8b]. destruct V9e as (V9a & V9b & V9c). destruct HLp as (E1 & E2 & E3 & E4 & E5 & E6).

  eapply JT_run; [exact Hrun1 | exact W2' | exact W1' | exact W3' |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. intros HF.
  destruct (mc_src_range rho1 _ HF M6f1) as (RG & (L1 & L2) & L3 & L4 & L5).

  eapply (triple_conseq (P := SPA segs (JT 0 ndM) Cmc rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs (JT 0 ndM) rho1 Emc 0 (SLit (-2160)) W1 tp w M1 HS) as HS1.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX W1 (ax_X Emc) (ax_base Emc)) 0 (SLit (-2240)) W2 tp w M2 HS1) as HS2.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX W2 (ax_X Emc) (ax_base Emc)) i0 (SLit 6) B1 tp w M3 HS2) as HS3.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX B1 (ax_X Emc) (ax_base Emc)) i1 (add vClen (SLit 6)) B2 tp w M4 HS3) as HS4.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX B2 (ax_X Emc) (ax_base Emc)) i2 vLen B3 tp w M5 HS4) as HS5.
    assert (HS5h : SPA segs (JT 0 ndM) (mkAX B3h (ax_X Emc) (ax_base Emc)) rho1 tp w).
    { unfold B3h. change (mkAX (add_facts mc_hints B3) (ax_X Emc) (ax_base Emc)) with (ax_with_facts (mkAX B3 (ax_X Emc) (ax_base Emc)) (mc_hints ++ ss_facts B3)).
    apply (SPA_refacts_JA segs); [exact HS5 | exact M6b |].
    intros tr md HJ HFc. apply Forall_app. split; [|exact HFc].

    assert (Hnz : tnz rho1 (SVar vP, vPlen)).
    { unfold tnz. cbn [fst]. unfold kept_nzb in M6z. cbn [forallb fst] in M6z. apply andb_prop in M6z as [Z1 _].
      pose proof (holds_mem _ _ _ HFc Z1) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X. rewrite Z.mod_small in X by lia.
      unfold uval, vP in *. cbn [fst eval] in X |- *. lia. }
    pose proof (JA_tv_facts segs AInv CST XGL NF (KcT 0) rhoT P0T [] [] BX0 PTrue ALA ndM rho1 tp tr md (SVar vP, vPlen) eq_refl HJ ltac:(left; reflexivity) Hnz) as TF.
    unfold tv_factsA in TF. cbn [fst snd] in TF.
    inversion TF as [| ? ? T1 TF2]; subst. inversion TF2 as [| ? ? _ TF3]; subst. inversion TF3 as [| ? ? T3 TF4]; subst.
    inversion TF4 as [| ? ? _ TF5]; subst. inversion TF5 as [| ? ? _ TF6]; subst. inversion TF6 as [| ? ? T6 TF7]; subst.
    inversion TF7 as [| ? ? T7 TF8]; subst. inversion TF8 as [| ? ? T8 _]; subst.
    unfold mc_hints. constructor; [exact T1 | constructor; [exact T3 | constructor; [exact T6 | constructor; [exact T8 | constructor; [exact T7 | constructor]]]]]. }
    assert (HS6 : SPA segs (JT 0 ndM) (mkAX B3c (ax_X Emc) (ax_base Emc)) rho1 tp w).
    { pose proof (carveT (KcT 0) ndM (mkAX B3h (ax_X Emc) (ax_base Emc)) rho1 tp w N_mc (ss_next B3h) HS5h) as X.
      cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X; [exact M6w | apply Pos.leb_refl | exact HbE | exact M6c]. }
    unfold Cmc. rewrite <- M7e. change (mkAX (set_obj_at B3c i2 O_srcT) (ax_X Emc) (ax_base Emc)) with (ax_setS (mkAX B3c (ax_X Emc) (ax_base Emc)) (set_obj_at B3c i2 O_srcT)).
    apply (SPA_reslice segs (JT 0 ndM) rho1 (mkAX B3c (ax_X Emc) (ax_base Emc)) i2 O_srcM O_srcT tp w M7n); try reflexivity.
    - cbn [ax_S]. rewrite M7e. exact M7s.
    - exact RG.
    - exact L2.
    - exact L3.
    - exact HS6. }

  assert (HnxC : ss_next (ax_S Cmc) = ss_next (ax_S Emc)) by exact M7nx.
  apply triple_factsA. intros HFC.
  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JT 0 ndM rho1 t tr md /\ clsZ r 15 16 /\ clsZ r 19 52).
  assert (JpK : forall r t tr md, Jp r t tr md -> MD md /\ tr = T0 ++ EVk 0) by (intros r t tr md (HJ & _); exact (JT_Kc _ _ _ _ _ _ HJ)).
  assert (HstJp : stableA segs NF Jp).
  { intros r r' t tr md md' Hag Hme (HJ & C1 & C2). unfold Jp. split; [|split].
    - destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF (KcT 0) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm 0) ALA (ss_next (ax_S Cmc)) ndM Ai kc rho1 rho1 t tr md md');
        [apply Pos.leb_le; exact Cnx | exact Cnb | apply agree_below_refl | exact Hme | exact HJi].
    - unfold clsZ in C1 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C1.
    - unfold clsZ in C2 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C2. }
  assert (HokJp : ok_frameA segs ok Jp).
  { apply HOKJ. intros r t tr md HJ. destruct (JpK _ _ _ _ HJ) as [_ ->]. apply Htc. }
  apply (pcallT (KcT 0) (KcT 0) Cmc Pre_mc0 (s_mc Cmc) Rmc Posts_mc rho1 tp ndM Jp Jp (fun _ => False) (Kc_okT T0 MD HMDvm 0)).
  - intros rho6 tp6. apply (memcpy_icpt_sum ok Jp rho6 tp6 HokJp HstJp).
    + intros r t tr md (_ & C1 & _). exact C1.
    + intros r t tr md (_ & _ & C2). exact C2.
  - exact Cfr.
  - exact Ccc.
  - exact Cnx.
  - exact Cnb.
  - exact Cfb.
  -
    intros tr ms md Hsm HJ. unfold Jp. split; [exact HJ|].
    assert (Hnz : tnz rho1 (SVar vP, vPlen)).
    { unfold tnz. cbn [fst]. unfold kept_nzb in M6z. cbn [forallb fst] in M6z. apply andb_prop in M6z as [Z1 _]. rewrite M6fx in Z1.
      pose proof (holds_mem _ _ _ HF Z1) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X. rewrite Z.mod_small in X by lia.
      unfold uval, vP in X |- *. cbn [fst eval] in X |- *. lia. }
    assert (HnzB : tnz rho1 (vB, vCap)).
    { unfold tnz, vB. cbn [fst eval]. pose proof (holds_mem _ _ _ HFC ChB) as X. unfold vB in X. cbn [holds eval] in X.
      rewrite lit_unsigned, Z.mod_small in X by lia. lia. }
    split; apply band_free_clsZ; rewrite !rw_call'.
    + change (wsub_get (s_mc Cmc) 15%positive) with (SVar vP). change (wsub_get (s_mc Cmc) 16%positive) with vPlen.
      exact (JT_tv_band_free _ 0 ndM rho1 tp tr md (SVar vP, vPlen) HJ ltac:(left; reflexivity) Hnz).
    + change (wsub_get (s_mc Cmc) 19%positive) with vB. change (wsub_get (s_mc Cmc) 52%positive) with vCap.
      exact (JT_tv_band_free _ 0 ndM rho1 tp tr md (vB, vCap) HJ ltac:(right; left; reflexivity) HnzB).
  - intros rhoL tr' md' (HJ & _). exact HJ.
  -
    intros Lf rho3 HinL Hag3. unfold Posts_mc in HinL. destruct HinL as [<-|[]]. cbn [la_state].
    fold (T_afterA Pre_mc0 Cmc (s_mc Cmc) Rmc P_icpt). rewrite CT.
    eapply (triple_conseq (P := fun w => exists rho4, SPA segs (JT 0 ndM) Umc rho4 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
    { destruct w as [tr [ms md]].
      pose proof (AxXform.SPA_select segs (JT 0 ndM) rho3 TMC _ tp _ V1a HS) as HS1. rewrite V1b in HS1.
      pose proof (uncarveT (KcT 0) ndM (mkAX V1 (ax_X TMC) (ax_base TMC)) rho3 tp tr ms md _ N_mc (Kc_okT T0 MD HMDvm 0) V2a V2c eq_refl V2d HS1) as HS2.
      cbn [ax_S ax_setS ax_X ax_base] in HS2. rewrite V2b in HS2.
      set (rho4 := rho_absorb rho3 (map lc_obj N_mc) (vms md tp ms)) in HS2. exists rho4.
      destruct HS2 as [HS2a HS2b]. pose proof (conj HS2a HS2b : SPA segs (JT 0 ndM) (mkAX V2 (ax_X TMC) (ax_base TMC)) rho4 tp (tr, mkCfg ms md)) as HS2. clear HS2a HS2b.
      assert (HF4 : Forall (holds rho4) (ss_facts V2)) by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 HS2))))))))))))).
      destruct (mc_src_range rho4 _ HF4 V3d) as (RG' & _ & _ & L4' & L5').
      assert (HS3 : SPA segs (JT 0 ndM) (mkAX V3 (ax_X TMC) (ax_base TMC)) rho4 tp (tr, mkCfg ms md)).
      { rewrite <- V3b. change (mkAX (set_obj_at V2 3 O_srcM) (ax_X TMC) (ax_base TMC)) with (ax_setS (mkAX V2 (ax_X TMC) (ax_base TMC)) (set_obj_at V2 3 O_srcM)).
        apply (SPA_reslice segs (JT 0 ndM) rho4 (mkAX V2 (ax_X TMC) (ax_base TMC)) 3 O_srcT O_srcM tp _ V3a); try reflexivity.
        - cbn [ax_S]. rewrite V3b. exact V3c.
        - symmetry. exact RG'.
        - exact L4'.
        - exact L5'.
        - exact HS2. }
      assert (HF5 : Forall (holds rho4) (ss_facts V3)) by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 HS3))))))))))))).
      assert (Hsp4 : 0x7fff80000000 <= bv_unsigned (eval rho4 sp0) <= 2 ^ 47 - 224).
      { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF5 | exact V4d]. }
      assert (HS4 : SPA segs (JT 0 ndM) (mkAX V4 (ax_X TMC) (ax_base TMC)) rho4 tp (tr, mkCfg ms md)).
      { rewrite <- V4b. change (mkAX (set_obj_at V3 1 O_cstkB) (ax_X TMC) (ax_base TMC)) with (ax_setS (mkAX V3 (ax_X TMC) (ax_base TMC)) (set_obj_at V3 1 O_cstkB)).
        apply (SPA_reslice segs (JT 0 ndM) rho4 (mkAX V3 (ax_X TMC) (ax_base TMC)) 1 _ O_cstkB tp _ V4a); try reflexivity.
        - cbn [ax_S]. rewrite V4b. exact V4c.
        - unfold O_cstkB, spT. rewrite !obj_range_lits by lia. rewrite !U_add_lit by (try lia; rewrite U_add_lit by lia; lia). f_equal; lia.
        - unfold O_cstkB, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by lia. lia.
        - exact HS3. }
      pose proof (AxXform.SPA_select segs (JT 0 ndM) rho4 (mkAX V4 (ax_X TMC) (ax_base TMC)) _ tp _ V5a HS4) as HS5. cbn [ax_S ax_X ax_base] in HS5. rewrite V5b in HS5.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V5 (ax_X TMC) (ax_base TMC)) 0 V6 tp _ V6e HS5) as HS6.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V6 (ax_X TMC) (ax_base TMC)) 0 V7 tp _ V7e HS6) as HS7.
      pose proof (AxXform.SPA_select segs (JT 0 ndM) rho4 (mkAX V7 (ax_X TMC) (ax_base TMC)) _ tp _ V8a HS7) as HS8. cbn [ax_S ax_X ax_base] in HS8. rewrite V8b in HS8.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V8 (ax_X TMC) (ax_base TMC)) 0 V9 tp _ V9a HS8) as HS9.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V9 (ax_X TMC) (ax_base TMC)) 0 V10 tp _ V9b HS9) as HS10.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V10 (ax_X TMC) (ax_base TMC)) 0 V11 tp _ V9c HS10) as HS11.
      rewrite <- VU. exact HS11. }
    apply triple_ex. intros rho4.

    eapply JT_run; [exact Hrun2 | exact Y2 | exact Y1 | exact Y3 |].
    intros Lf rho5 [<-|[]] Hag5. cbn [la_state].
    eapply (triple_conseq (P := SPA segs (JT 0 ndM) LP0 (rho_sub rho5 sLP) tp)); [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
    apply (JT_entails 0%nat Lp LP0 sLP ndM ndM rho5 tp w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.
End SegMC.

Definition edge_okb (Lnext : axst) (tv : list (sv * sv)) (bdi bdj : list bitem) (Lf : axst) : bool := ltac2:(tb__ "0|2|
S178S4dS41VLf;A1M0S41VLnext;A1A3S99S14S14S14S14S14S49VLf;VLnext;R1A3S9aR1S4dA2A2S74S4dS1eG0A1M1A2A2S61G1S63Vtv;ScSbSbS1cS19A2S1cA2A1Vbdi;S62A4A2A2S115R1Vtv;Vtv;A3A2S104S20G0A1S102R1Vbdj;A2Vbdi;A3A2Ts;").
Lemma edge_okb_sound : ltac2:(tb__ "0|3|
S43S9SbS1cS1cA2A1S9S103A1M0G0S43S0S7S128R5R4R3R2R1A5S8A3S3S99S99S1S0S7S49R3R7R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41R3A1M1A1M2A2S8A3S1S0S7S61G2S63R6ScSbSbS1cS19A2S1cA2A1R5S62A4A2S8A3S1S0S7S115R1R6R6A3S8A3S0S7S104S20G1A1S102R1R4A2R5A3S8A3A2A2A2A2A2Ls;A2F_;FLf;Fbdj;Fbdi;Ftv;FLnext;").
Proof.
  intros Lnext tv bdi bdj Lf H. unfold edge_okb in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  eexists. repeat split; eassumption.
Qed.
Lemma JT_edge : ltac2:(tb__ "0|4|
SaS43S9SbS1cS1cA2A1S9S103A1M0G0S43S21S9S4eQ40A1A1M1S0S7S128R7R6R5R4R3A5S8A3S21G1S76S4cVok;S5bS4cVJT;RbS63R9ScSbSbS1cS19A2S1cA2A1M2R7S62A4A2RaR2R1A5S77S2L_;M3A4Ftp';Frho';S76S4cVok;S5bS4cVJT;RaS63R8G2R7S62A4A2R5R4R3A5G3A4F_;F_;Ftp;Frho;FLf;Fbdj;Fbdi;Ftv;FLnext;Fk;").
Proof.
  intros k Lnext tv bdi bdj Lf rho tp H Hn. destruct (edge_okb_sound _ _ _ _ _ H) as (s5 & E1 & E2 & E3 & E4 & E5 & E6).
  eapply (triple_conseq (P := SPA segs (JT k (NDA tv [] bdj ANone)) Lnext (rho_sub rho s5) tp)); [intros w HS | intros w' Hw'; exact Hw' | apply Hn].
  apply (JT_entails k Lf Lnext s5 (NDA tv [] bdi ANone) (NDA tv [] bdj ANone) rho tp w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.

Definition plen_factsb (facts : list sprop) : bool := ltac2:(tb__ "0|1|
S14SdaS1fS27S28Sc2S23S7dZ2Z1aA2A1A2A1Vfacts;A3S16SdaS1fS27S29S121Sc2S23Z0A1M0A3A1Vfacts;A3SdaS1fS27S2cS29S11dSc2G0A3A1A1Vfacts;A3A2A2").
Lemma plen_facts_sound26 : ltac2:(tb__ "0|1|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S12cR2A1S8A3S1S7aZ1S10cR4Sc2A2M0A2S7aG0S7dZ2Z1aA2A2A2F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H. unfold plen_factsb in H. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as A1. cbn [holds] in A1. unfold vPlen in A1. cbn [eval] in A1. rewrite lit_unsigned in A1.
  change ((2 ^ 26) mod 2 ^ 64) with (2 ^ 26) in A1.
  assert (NZ : bv_unsigned (rw rho 44%positive) <> 0).
  { apply orb_prop in H2 as [H2|H2]; pose proof (holds_mem _ _ _ HF H2) as A2; cbn [holds] in A2; unfold vPlen in A2; cbn [eval] in A2;
      unfold branch_taken, bv_eqb in A2; rewrite lit_unsigned in A2; change (0 mod 2 ^ 64) with 0 in A2.
    - intros E. rewrite E in A2. cbn in A2. discriminate.
    - intros E. apply A2. rewrite E. reflexivity. }
  unfold uval, vPlen. cbn [eval]. pose proof (urange (rw rho 44%positive)). lia.
Qed.
Lemma plen_facts_sound : ltac2:(tb__ "0|1|
S21S9S1fA1S87S1fS26R2A1R1A3S0S7S12cR2A1S8A3S1S7aZ1S10cR4Sc2A2M0A2S7eG0S7dZ2Z27A2A2A2F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H. unfold plen_factsb in H. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as A1. cbn [holds] in A1. unfold vPlen in A1. cbn [eval] in A1. rewrite lit_unsigned in A1.
  change ((2 ^ 26) mod 2 ^ 64) with (2 ^ 26) in A1.
  assert (NZ : bv_unsigned (rw rho 44%positive) <> 0).
  { apply orb_prop in H2 as [H2|H2]; pose proof (holds_mem _ _ _ HF H2) as A2; cbn [holds] in A2; unfold vPlen in A2; cbn [eval] in A2;
      unfold branch_taken, bv_eqb in A2; rewrite lit_unsigned in A2; change (0 mod 2 ^ 64) with 0 in A2.
    - intros E. rewrite E in A2. cbn in A2. discriminate.
    - intros E. apply A2. rewrite E. reflexivity. }
  unfold uval, vPlen. cbn [eval]. pose proof (urange (rw rho 44%positive)). lia.
Qed.

Lemma room_T : ltac2:(tb__ "0|0|
S145S19S21S19S1S7aZ1R1A2S7aR1S7dZ2Z1aA2A2A2S10dSc9S72S10eSf6A1S71S62R3A2R4A3S148R5A1S147R5A1S146R5A1R3A6S187R6R3A2F_;F_;Fn;Frho;Fkc;FA;").
Proof.
  intros A kc rho n Hn HB. apply BUD_room in HB as (B0 & B1 & BV & BK). pose proof (apot_range ANone rho) as AR.
  unfold bxa, BX0 in B0, B1, BV, BK. cbn [fst snd bx2] in B0, B1, BV, BK.
  assert (EV : bsumV bd_T rho = V_T) by (unfold bd_T; cbn [bsumV]; unfold bival, BIc; cbn [lfval bi_f bi_c bi_v bi_k]; lia).
  assert (EK : bsumK bd_T rho = KU * K_T) by (unfold bd_T; cbn [bsumK]; unfold bival, BIc; cbn [lfval bi_f bi_c bi_v bi_k]; lia).
  rewrite EV in BV. rewrite EK in BK.
  unfold alloc_roomA. unfold V_T, K_T, VMAX, KMAX, V_DRV, K_DRV, NCALLS, CV, CV0, CK_DIV, CK0, MAX_INPUT, KU in BV, BK |- *. lia.
Qed.

Section MallocSite.

Variables (Em : axst) (R : list sobj) (Tk : axst).
Hypothesis Mfr : ltac2:(tb__ "0|1|
S0S10S9S1dA1M0A1S136VEm;SaaSa5VEm;A1A3S11G0VR;A2A3").
Hypothesis Mcc : ltac2:(tb__ "0|0|
S0S7S137VEm;SaaSa5VEm;A1VR;SbbA5S8A3").
Hypothesis McT : ltac2:(tb__ "0|0|
S0S7S142S4dSa5VEm;A1A2S8A3").
Hypothesis Mnx : ltac2:(tb__ "0|0|
S0S7S74S4dS1eS41VEm;A1A1A2S8A3").
Hypothesis Mnb : ltac2:(tb__ "0|1|
S1S0S7S61S1eS41VEm;A1A1M0Sc5A2S8A3S0S7S106G0S159A2S8A3A2").
Hypothesis Ms12 : ltac2:(tb__ "0|0|
S0S1cS9bSa5VEm;A1PcA2Sc2A3").
Hypothesis Msv : ltac2:(tb__ "0|0|
S0S7S3fS1eS41VEm;A1A1Sc2A2S8A3").
Hypothesis Mres : ltac2:(tb__ "0|1|
S1S0S1cS9bS13aSa5VEm;A1SaaS151S14fScS153A1S152A3VEm;A4S154A2S2aS140S1eS41VEm;A1A1UaA2M0A1A3S0S1aG0S9fA3A2").
Hypothesis Mpay : ltac2:(tb__ "0|0|
S0S7S107S20S41VEm;A1A1Sc2S109Sc9S159A5S8A3").
Hypothesis Mspf : ltac2:(tb__ "0|0|
S0S7SebS20S41VEm;A1A1A1S8A3").
Hypothesis Mro : ltac2:(tb__ "0|0|
S0S7SeeS20S41VEm;A1A1ScaS15SaA1VR;A4S8A3").
Hypothesis Mxr : ltac2:(tb__ "0|1|
S0S7SefS20S41VEm;A1M0A1ScaS15SaA1S24G0A1SecS44VEm;A1A6S8A3").
Hypothesis Msz : ltac2:(tb__ "0|0|
S0S7S12cS20S41VEm;A1A1A1S8A3").
Hypothesis MTk : ltac2:(tb__ "0|0|
S0S43S141SaaVEm;Sa5VEm;A1VR;S151S14fScS153A1S152A3A5VTk;A3").

Hypothesis HMC : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S134S159A1A2VTk;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_msite : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0Sc5A2VEm;R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct Mnb as [Mnb1 Mnb2]. destruct Mres as [Mres1 Mres2].
  apply triple_factsA. intros HF.
  pose proof (plen_facts_sound rho _ HF Msz) as HSZ. pose proof (plen_facts_sound26 rho _ HF Msz) as HSZ26.
  unfold nd_T. unfold PostsM in Mcc.
  apply (malloc_callA_S segs AE_A AInv CST XGL ALA HCST HXGL NF (KcT 0) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm 0) PTrue ok [] UStopLe Em (s_m Em) R rho tp
           (NDA tv_T [] bd_T ANone) bd_M (fun _ => False) malloc_shape_nil (okKT 0) MS Mfr (call_checkPA_drop1 _ _ _ _ _ _ Mcc) McT Mnx Mnb1 Mnb2).
  - rewrite Ms12. exact Msv.
  - exact Mres1.
  - rewrite Ms12. apply payA_of_bud_pay. exact Mpay.
  - intros A A' _ _. exact I.
  - intros A kc _ _ HB. rewrite Ms12. cbn [nd_bd nd_am] in HB. exact (room_T A kc rho _ HSZ26 HB).
  - reflexivity.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - apply (site_ok_drv (NDA tv_T [] bd_T ANone) Em (s_m Em) R rho None None); try assumption.
    + intros Ai HF' HN HZ. exact I.
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. rewrite Ms12. split; [exact HSZ | exact I].
  -
    intros rho' tp'. unfold PreM in MTk. rewrite MTk, Mres2, Ms12. cbn [nd_tv nd_fr nd_am]. fold kept. fold (ndM bd_M). apply HMC.
Qed.
End MallocSite.

Section SegT0.
Variables (S1 S2 : sstate) (EmA LeA LeB EmB : axst).
Hypothesis T1 : ltac2:(tb__ "0|0|
S0S10S22A1S113S41Sc8A1U0S23Nd0A1A3S11S22VS1;A2A3").

Hypothesis T2 : ltac2:(tb__ "0|4|
S1S0S7S185S4cVS1;Sd7S24VS1;A1S23Z0M0A1S23S172A1A3M1S7bS172Z4A2M2Z1M3G0A6S8A3S0S22S184VS1;G1G2G3G0A5VS2;A3A2").
Hypothesis T1w : ltac2:(tb__ "0|1|
S1S0S7S74S4dS1eVS2;A1M0A2S8A3S1S0S7S25VS2;A1SeA3S0S7S61G0Sc5A2S8A3A2A2").
Hypothesis Trun : ltac2:(tb__ "0|1|
S0S10S9S42A1M0A1S47S4cSb7SadS48VS2;S44Sc8A1S45Sc8A1A3S8A5S11G0SdS42S4aVEmA;SeaA2SdS42S4aVLeA;SeaA2SdS42S4aVLeB;SeaA2SdS42S4aVEmB;SeaA2ScS42A1A3A3A3A3A2A3").
Hypothesis HmA : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0Sc5A2VEmA;R2R1A5S77S2L_;A4Ftp;Frho;").
Hypothesis HmB : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0Sc5A2VEmB;R2R1A5S77S2L_;A4Ftp;Frho;").
Variables LEA LEB : axst.
Hypothesis HeA : ltac2:(tb__ "0|0|
S0S7S128VLEA;ScaSc9S158Z0A1VLeA;A5S8A3").
Hypothesis HeB : ltac2:(tb__ "0|0|
S0S7S128VLEB;ScaSc9S158Z0A1VLeB;A5S8A3").
Hypothesis HLEA : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S12dS158Z0A1A1A2VLEA;R2R1A5S77S2L_;A4Ftp;Frho;").
Hypothesis HLEB : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0S12dS158Z0A1A1A2VLEB;R2R1A5S77S2L_;A4Ftp;Frho;").

Lemma X_T0 : ltac2:(tb__ "0|0|
S21S9S4eQ40A1A1S76S4cVok;S5bS4cVJT;U0Sc5A2Sc8R2R1A5S77S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct T1w as (W1' & W2' & W3').
  eapply (triple_conseq (P := SPA segs (JT 0 nd_T) (mkAX S1 (ax_X S_T) (ax_base S_T)) rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { exact (SPA_split segs (JT 0 nd_T) rho S_T 0 (SLit (-208)) S1 tp w T1 HS). }
  eapply (triple_conseq (P := SPA segs (JT 0 nd_T) (mkAX S2 (ax_X S_T) (ax_base S_T)) rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { destruct T2 as [T2a T2b]. rewrite <- T2b. exact (SPA_img_cell segs (JT 0 nd_T) rho (mkAX S1 (ax_X S_T) (ax_base S_T)) _ _ 1 0 tp w T2a HS). }
  eapply JT_run; [exact Trun | exact W2' | exact W1' | exact W3' |].
  intros Lf rho1 Hin Hag1. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [la_state].
  - apply HmA.
  - unfold nd_T. exact (JT_edge 0%nat LEA tv_T bd_T (bd_E 0) LeA rho1 tp HeA HLEA).
  - unfold nd_T. exact (JT_edge 0%nat LEB tv_T bd_T (bd_E 0) LeB rho1 tp HeB HLEB).
  - apply HmB.
Qed.
End SegT0.

Definition ms16_shapeb (q : sprop) : bool :=
  match q with
  | SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 40) x) (SLit 15)) (SLit 0)) => true
  | _ => false
  end.
Lemma ms16_shapeb_sound : ltac2:(tb__ "0|0|
S1fS0S7S133R1A1S8A3S3S1cS1cS0S1fR3S12aR1A1A3Lx;A2F_;Fq;").
Proof.
  intros q H. unfold ms16_shapeb in H.
  repeat match type of H with
         | (match ?e with _ => _ end) = true => destruct e eqn:?; try discriminate
         end.
  subst. eexists. reflexivity.
Qed.

Definition backedge_okb (Lnext : axst) (tv : list (sv * sv)) (bd1 : list bitem) (Lf : axst) : bool := ltac2:(tb__ "0|2|
S178S4dS41VLf;A1M0S41VLnext;A1A3S99S14S14S14S14S14S49VLf;VLnext;R1A3S9aR1S4dA2A2S74S4dS1eG0A1M1A2A2S61G1S63Vtv;ScSbSbS1cS19A2S1cA2A1Vbd1;S62A4A2A2S115R1Vtv;Vtv;A3A2S104S20G0A1S102R1Vbd1;A2Vbd1;A3A2Ts;").
Lemma backedge_okb_sound : ltac2:(tb__ "0|2|
S43S9SbS1cS1cA2A1S9S103A1S43S0S7S12eR4R3R2R1A4S8A3S3S99S99S1S0S7S49R3R6R1A3S8A3S1S0S7S9aR1S4dA2S8A3S1S0S7S74S4dS1eS41R3A1M0A1M1A2S8A3S1S0S7S61G1S63R5ScSbSbS1cS19A2S1cA2A1R4S62A4A2S8A3S1S0S7S115R1R5R5A3S8A3S0S7S104S20G0A1S102R1R4A2R4A3S8A3A2A2A2A2A2Ls;A2F_;FLf;Fbd1;Ftv;FLnext;").
Proof.
  intros Lnext tv bd1 Lf H. unfold backedge_okb in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  eexists. repeat split; eassumption.
Qed.
End TLX.
End DrvTLX.


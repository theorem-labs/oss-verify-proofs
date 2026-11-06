(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs PmCurSpecsA PmFloatCSpecsA PmFloatCWD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import GetSpecCA PmCurSpecsBLocal GetContCB GetLitCB GetIntCB GetStrSCB GetDblCB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section GetStrOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL : icpt_layout.
Abbreviation IC := PMLA.C_cboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps Pm9PlanKit.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Pm9PlanKit.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom Pm9PlanKit.RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis CONV_OK : PMCSA.conv_ec_specA L ar HI IC 729476.
Hypothesis CSTR_OK : PMCSB.cstr_ctor_specB L ar HI IC 863168.
Hypothesis STRINIT_OK : PMSA.strinit_specA L ar HI 849628.
Hypothesis FROMI_OK : PMFCA.from_integer_i64_specA L ar HI IC 844828.
Hypothesis FROMU_OK : PMFCA.from_integer_u64_specA L ar HI IC 843204.
Hypothesis WD_OK : PMFCW.write_double_specW L ar HI IC 846852.
Hypothesis RTG : rt_globals IL HI.
Hypothesis ILG : forall ch, (ch <= 2)%nat -> In (GLC.LIT ch, Z.of_nat (length (GLC.TXT ch)) + 1) (icl_globals IL).
Hypothesis ISH : rt_img_shadow L IL HI.
Hypothesis POI : Forall (fun r : Z * Z => 1393560 + 8 <= fst r \/ snd r <= 1393560) (icl_poison IL) /\
                 Forall (fun r : Z * Z => 84664 + 8 <= fst r \/ snd r <= 84664) (icl_poison IL).
Hypothesis TPV : hl_tp L - 164 = 6888684.
Hypothesis ERRC : forall a, 6888684 <= a < 6888688 -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.

Theorem get_string_ok : PMCSA.get_string_specA L ar HI IC 841728.
Proof.
  apply GSP.get_string_of.
  - exact (get_cont_ok L ar C HI HIok LAY FPM FOOTC2 CONV_OK).
  - exact (get_lit_ok L ar C HI IL HIok LAY FPM FOOTC2 CSTR_OK RTG ILG).
  - exact (get_int_ok L ar C HI HIok LAY FPM FOOTC2 FROMI_OK FROMU_OK).
  - exact (get_txt_ok L ar C HI HIok LAY FPM FOOTC2 STRINIT_OK).
  - eapply get_dbl_ok; eassumption.
Qed.
End GetStrOk.


From Stdlib Require Import ZArith List.
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require AgreeSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require SegEnd memset memchr reac_segconf_init.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require SegWalkMainA E01 L01 L03 X01 M01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require memset memchr reac_segconf_init.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require SegWalkMainA M01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegCF Require SlotTopCF E01 L01 L03 X01.

(* reac-pw/fuzz_segconf's ubsan_agrees at the cut records the walks are proved at (CPseg: the cut predicates,
   Prog/Seg/SegWalkMainA.v and U/Prog/Seg/SegWalkMainA.v), with the segments whose
   walks have landed discharged: AgreeSeg.ubsan_agrees_of_callees at CPseg with
   - plain: Prog/Seg/E01.seg_E01_holds, Prog/Seg/M01.seg_M01_holds (K_M01 = reac_segconf_init_contract, by
     reac_segconf_init_holds from memset_holds), Prog/Seg/L01.seg_L01_holds (K_L01 = memchr_contract, by
     memchr_holds), Prog/Seg/L03.seg_L03_holds, Prog/Seg/X01.seg_X01_holds;
   - UBSan: the evt statement U/Prog/Seg/M01.evt_M01_holds (K_M01 likewise), and the cut-free copies of the U walks
     U/Prog/Seg/E01.v, L01.v, L03.v, X01.v: U/Prog/SegCF/E01.seg_E01_cf_holds (its calloc premise is
     AgreeSeg.calloc_cf_concrete_holds), U/Prog/SegCF/L01.seg_L01_cf_holds (K_L01 likewise),
     U/Prog/SegCF/L03.seg_L03_cf_holds, U/Prog/SegCF/X01.seg_X01_cf_holds.
   The premises left are the other segments' statements and their evt-callee contracts (each discharged here when
   its walk lands). Proves no function (kind: agreement composition of LLVMFuzzerTestOneInput's two slots). *)

Local Abbreviation CPp := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg.SegWalkMainA.CPseg.
Local Abbreviation CPu := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg.SegWalkMainA.CPseg.

Lemma plain_init_holds :
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.reac_segconf_init_c.reac_segconf_init_contract.
Proof. exact (lib.Prog.reac_segconf_init.reac_segconf_init_holds lib.Prog.memset.memset_holds). Qed.

Lemma ubsan_init_holds :
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.reac_segconf_init_c.reac_segconf_init_contract.
Proof. exact (U.Prog.reac_segconf_init.reac_segconf_init_holds U.Prog.memset.memset_holds). Qed.

Theorem ubsan_agrees_of_walks :
  forall (KpL02 KpM02 KpV01 : Prop) (KuL02 KuM02 KuV01 : Prop),
  lib.Prog.SegEnd.seg_L02_stmt CPp KpL02 ->
  lib.Prog.SegEnd.seg_M02_stmt CPp KpM02 -> lib.Prog.SegEnd.seg_V01_stmt CPp KpV01 ->
  KpL02 -> KpM02 -> KpV01 ->
  SlotTopCF.evt_L02_stmt CPu KuL02 ->
  SlotTopCF.seg_M02_cf_stmt CPu KuM02 -> SlotTopCF.evt_V01_stmt CPu KuV01 ->
  KuL02 -> KuM02 -> KuV01 ->
  Statements.ubsan_agrees.
Proof.
  intros KpL02 KpM02 KpV01 KuL02 KuM02 KuV01 PL02 PM02 PV01 KPL02 KPM02 KPV01
    UL02 UM02 UV01 KUL02 KUM02 KUV01.
  exact (AgreeSeg.ubsan_agrees_of_callees CPp _ _ KpL02 KpM02 KpV01 CPu _ _ KuL02 KuM02 KuV01
           lib.Prog.Seg.E01.seg_E01_holds lib.Prog.Seg.M01.seg_M01_holds lib.Prog.Seg.L01.seg_L01_holds PL02 lib.Prog.Seg.L03.seg_L03_holds
           PM02 PV01 lib.Prog.Seg.X01.seg_X01_holds
           plain_init_holds lib.Prog.memchr.memchr_holds KPL02 KPM02 KPV01
           U.Prog.SegCF.E01.seg_E01_cf_holds U.Prog.Seg.M01.evt_M01_holds U.Prog.SegCF.L01.seg_L01_cf_holds UL02 U.Prog.SegCF.L03.seg_L03_cf_holds
           UM02 UV01 U.Prog.SegCF.X01.seg_X01_cf_holds
           ubsan_init_holds U.Prog.memchr.memchr_holds KUL02 KUM02 KUV01).
Qed.

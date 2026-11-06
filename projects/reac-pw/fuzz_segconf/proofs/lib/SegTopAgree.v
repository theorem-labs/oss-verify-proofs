(* ubsan_agrees of reac-pw/fuzz_segconf: AgreeSegTop.ubsan_agrees_of_walks (AgreeSeg.ubsan_agrees_of_callees
   at the cut records CPseg of both builds; E01, M01, L01, L03, X01 of both builds and K_M01, K_L01 discharged there),
   its remaining premises discharged by the walks of the other segments and by the callee bundles of Prog/SegTop.v
   (plain K_L02, K_M02, K_V01) and U/Prog/SegTop.v (UBSan K_L02, K_M02, K_V01), as reac-pw/fuzz_pin's
   AgreePin.ubsan_agrees_holds (commit aa56e9780de) is pin's.
   - plain: seg_L02_stmt by Prog/Seg/L02T.seg_L02, seg_M02_stmt by Prog/Seg/M02.seg_M02, seg_V01_stmt by
     Prog/Seg/V01.seg_V01; K_L02, K_M02, K_V01 by Prog/SegTop.K_L02_holds, K_M02_holds, K_V01_holds;
   - UBSan: SlotTopCF.evt_L02_stmt by U_evt_L02_holds below (U/Prog/Seg/L02.evt_L02_of_inner over
     U/Prog/Seg/L02W.L02_inner_holds: the U walk of L02 in its evt form, as U/Prog/Seg/L02T.seg_L02_of_inner uses it),
     SlotTopCF.seg_M02_cf_stmt by U/Prog/SegCF/M02.seg_M02_cf_holds (the cut-free copy of the U walk of
     M02), SlotTopCF.evt_V01_stmt by U/Prog/Seg/V01.evt_V01_holds; K_L02, K_M02, K_V01 by U/Prog/SegTop.K_L02_holds,
     K_M02_holds, K_V01_holds.
   No premise is left.
   Proves no function (kind: agreement composition of LLVMFuzzerTestOneInput's two slots). *)
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require AgreeSegTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require SegTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require L02T M02 V01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require SegTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require SegWalkMainA L02D L02 L02W V01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegCF Require SlotTopCF M02.

Local Abbreviation CPu := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg.SegWalkMainA.CPseg.

(* The U walk of L02 in the evt form the cut-free UBSan slot takes. *)
Lemma U_evt_L02_holds : lib.U.Prog.SegCF.SlotTopCF.evt_L02_stmt CPu lib.U.Prog.Seg.L02D.K_L02.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF K.
  exact (lib.U.Prog.Seg.L02.evt_L02_of_inner (fx:=fx) (rc:=rc) B APIf ra empty FF
           (lib.U.Prog.Seg.L02W.L02_inner_holds K)).
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  exact (lib.AgreeSegTop.ubsan_agrees_of_walks _ _ _ _ _ _
           lib.Prog.Seg.L02T.seg_L02 lib.Prog.Seg.M02.seg_M02 lib.Prog.Seg.V01.seg_V01
           lib.Prog.SegTop.K_L02_holds
           lib.Prog.SegTop.K_M02_holds
           lib.Prog.SegTop.K_V01_holds
           U_evt_L02_holds lib.U.Prog.SegCF.M02.seg_M02_cf_holds lib.U.Prog.Seg.V01.evt_V01_holds
           lib.U.Prog.SegTop.K_L02_holds
           lib.U.Prog.SegTop.K_M02_holds
           lib.U.Prog.SegTop.K_V01_holds).
Qed.

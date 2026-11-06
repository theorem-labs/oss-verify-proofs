(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Lib Require NoCache.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_SpecConsts () := "K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08c59OSSVerify5KrLib6Common:SpecConstsArw_bytes_max_ge17C1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SpecConsts ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;4p;7p;3g0000j1ATg000Pj1@Tg0010j14Tg001Nj13Tg001lj1?Tg002Wj11Tg003<j15Tg003Zj26Tg004=j47Tg004hj78Tg005Lj29Tg005nj2:Tg006Hj2>Tg0074j3=Tg007Nj3<Tg007mj4;Tg008_j22Tf0R0#1#1p=0g009;R1#A%@1g009gR1#4%31%?1R2g00:Eg00:dR3P3g00;DR3P1g00;d#1#0#0#0#0#0#0#0#0#5R4,61R5g00<IP5C7g00=0F81923P0f2R3g00=PR2g00>0R5':1>03==25dg00>Pf15<1C;b1b2b31244P0b0g00>n,24eo"). Qed.

Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SpecConsts ()) [] "h04__x1h11Hh27__arithh34__ffh48__varmaph55__witp;1p;2p;4p;8p;3p;7g002Wj12Tg003<j19Tg008_j21Tg0000j1ETg000Pj1;Tg00?oj2:Tg001Nj18Tg001lj17Tg003Zj23Tg00@Mj26Tg004=j44Tg00A0j1DTg00ARj8CTg005Lj2BTg005nj2<Tg006Hj2=Tg0074j3>Tg007Nj3?Tg007mj4@Tg004hj7ATf0R0#2#2p=0f1R1g00:ER2g00:dR3P3g00;DR4P0g00=0FAp=5g00B6g00;dR5#2#0#0#0#0#0#0#0#0#9R6g00>nR7'1g009gR8g009;R9#E%;91:81%88%78R9P2P3P3P4P81386g00<IR21685R5C4,59%D3P8g00>PR3,38P2P5C4,59GC1B94P0f2R9g00=PR4g00>0R5'<1=09=>45dA?831C@b3b4b5W011601131[^08P0P7P1O2b2b1o"). Qed.

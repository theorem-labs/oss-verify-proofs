(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib RefMainEntry RefMainEntryN SymDriveH4 LibStdioCall LibDiagKn.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil03nat04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~l17scriptsl19sym_statel18sidecond04true79OSSVerify6Proofsaboost_jsonafuzz_parse3libdMainWalk_defs4FPX1~~~~~~r75FUELMr76STOPSMl18sym_exec69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hh8floaded_segmentsl16kentry04bool03fstl15carryl15s_logl13SCRl14expr3h5LinuxProcessSemantics5Riscv5Instrhp27ALU_ADDl14EAlul14ELitl14EVarr74MSTKl13KWrl12SAl16KAlignl14KImgl16KRange46Stdlib6ZArith6BinInt1Zig13sub05falseig13powr73knAr73spxr73knLl15KWord" s.
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPSM : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+tsnlc@3$1$0+tsmhc@3$1$0+uqtq8@3$1$0+knmq0@3$1$0+knklc@3$1$0+knkm4@3$1$0+knlm8@3$1$0+knlo8@3$1$0+knlq4@3$1$0+knlvc@3$1$0+knmh8@3$1$0+knmm0@1$2$0").
Definition FUELM : nat := 3000.
Definition runM : ltac2:(zQ "50!kb!p0!pa!h8!q6>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k1!r1!vc!hg4!p0!q6!hgd!pa!hke\3scr$4\2ss$7@7$6$8$2$1$3^2^1@1$0$5").
Definition carryM : ltac2:(zQ "70!h8!kb!hm1!q6!hma!p0!pa>1r@2$1@2$1$6@1$0$3$5>2kn@1$0$2@2$1@2$1@1$0$2@1$0$3@1$0$4") := ltac2:(zQ "b0!h8!kb!q6!pa!hn0!p0!hma!k1!hn5!hm1!hnd\1r@2$1@2$1$3@1$0$2$5\2kn@1$0$9@3$8@1$a@3$4$3@1$0$2@3$4@2$1$3@1$0$2$5^2^1@1$7$6").
Definition noscr : ltac2:(zQ "10!p0$0") := ltac2:(zQ "40!k1!hma!ho5!hob@3$2@1$0$1@1$0$3@1$0$1").
Definition spx : ltac2:(zQ "20!j7!hob>1k$0$1") := ltac2:(zQ "50!j7!hr6!hs1!hs8!hsf\1k$0@3$2$1@1$4N0@1$3^1").

(* [comment removed for export] *)
Definition MSTK : Z := 1024.
Definition knL : ltac2:(zQ "20!h8!hm1@1$0$1") := ltac2:(zQ "c0!hm1!jb!hsf!ht6!htd!hu3!k1!hs8!hu8!hv1!hv8!ih9@3$1$0@2$8@1$2N0+h0@3$1$0@3$a@1$2N0+nvvvogggggg0+ogggggggggg0@3$1$0@2$4@2$5@1$2N0@2$b-o0$3$3@3$1$0@2$4@2$5@1$7Z+vpgg0+jkgg0@3$1$0@2$9+hggg0+vhgg0@1$6$0").

(* [comment removed for export] *)
Definition scrU : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!r1!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").       (* [comment removed for export] *)
Definition rU := Eval vm_compute in runM scrU (SS 0x473d0 sr_mainN [] kn_mainN 40).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
Definition knU : list kentry := Eval vm_compute in fst (fst (carryM rU kn_mainN)).

(* [comment removed for export] *)
Definition scrA : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!ii0!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rA := Eval vm_compute in runM scrA (SS 0x473d0 sr_main [] kn_main 40).
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in fst (fst (carryM rA kn_main)).

(* [comment removed for export] *)
Definition srC0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (ELit 3).
Definition rC := Eval vm_compute in runM noscr (SS 0xebe8c srC0 [] knA 40).
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).

(* [comment removed for export] *)
Definition srF0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (EVar 40).
Definition knF0 : ltac2:(zQ "20!h8!hm1@1$0$1") := ltac2:(zQ "70!ii7!ih9!jb!iie!hsf!hv8!hm1@3$2$6@3$5@1$4Ni8@2$1@2$0+2+k0+vvf@2$1@2$0+2+k0+1$3").
Definition scrF : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!ii0!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rF := Eval vm_compute in runM scrF (SS 0xebe8c srF0 [] knF0 41).
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).

(* [comment removed for export] *)
Definition srE0 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2Nh7@3$1$0@1$2N3@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2Ni1@3$1$0@1$3+3@3$1$0@1$3+hggg0@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrE : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!ii0!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rE := Eval vm_compute in runM scrE (SS 0x47424 srE0 [] knL 46).
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
(* [comment removed for export] *)
Definition srN0 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vprv9@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrN : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!r1!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").      (* [comment removed for export] *)
Definition scrN' : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!ii0!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rN := Eval vm_compute in runM scrN (SS 0x4745c srN0 [] knL 46).
Definition rN' := Eval vm_compute in runM scrN' (SS 0x4745c srN0 [] knL 46).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN)).
Definition srN' : list expr := Eval vm_compute in s_regs (fst (fst rN')).
(* [comment removed for export] *)
Definition srR0 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vprv9@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrR : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!r1!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition scrR' : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!ii0!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rR := Eval vm_compute in runM scrR (SS 0x4749c srR0 [] knL 46).
Definition rR' := Eval vm_compute in runM scrR' (SS 0x4749c srR0 [] knL 46).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition srR' : list expr := Eval vm_compute in s_regs (fst (fst rR')).
(* [comment removed for export] *)
Definition srL50 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$3+vggs4@3$1$0@1$5-p0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2N7@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vprv9@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition knL5 : ltac2:(zQ "20!h8!hm1@1$0$1") := ltac2:(zQ "70!jb!ija!hs8!hsf!ik0!hu3!hm1@3$0$6@3$4@2$5@1$3N0-o8N8@1$2+knkr8$1").
(* [comment removed for export] *)
Definition scrL5a : ltac2:(zQ "10!p0$0") := ltac2:(zQ "70!hma!jb!k1!r1!ii0!ho5!hob@3$5@3$1$0$3@3$1$0$4@3$1$0$3@1$2$0@1$2$6@1$2$0").
Definition rL5a := Eval vm_compute in runM scrL5a (SS 0xebe8c srL50 [] knL5 46).
Definition srL5a : list expr := Eval vm_compute in s_regs (fst (fst rL5a)).
(* [comment removed for export] *)
Definition srL50z : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit 0).
Definition rL5b := Eval vm_compute in runM noscr (SS 0xebe8c srL50z [] knL5 46).
Definition srL5b : list expr := Eval vm_compute in s_regs (fst (fst rL5b)).
(* [comment removed for export] *)
Definition srL50e : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit (2^64 - 21)).
Definition rL5c := Eval vm_compute in runM noscr (SS 0xebe8c srL50e [] knL5 46).
Definition srL5c : list expr := Eval vm_compute in s_regs (fst (fst rL5c)).
(* [comment removed for export] *)
Definition srM0 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vprv9@3$1$0@1$2N7@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrMa : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!ii0!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").    (* [comment removed for export] *)
Definition scrMb : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!r1!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rMa := Eval vm_compute in runM scrMa (SS 0x47450 srM0 [] knL 46).
Definition rMb := Eval vm_compute in runM scrMb (SS 0x47450 srM0 [] knL 46).
Definition srMa : list expr := Eval vm_compute in s_regs (fst (fst rMa)).
Definition srMb : list expr := Eval vm_compute in s_regs (fst (fst rMb)).
(* [comment removed for export] *)
Definition srG0 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N4@3$1$0@1$3+vprv9@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrGb : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!ii0!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").    (* [comment removed for export] *)
Definition scrGr : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!r1!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rGb := Eval vm_compute in runM scrGb (SS 0x47464 srG0 [] knL 46).
Definition rGr := Eval vm_compute in runM scrGr (SS 0x47464 srG0 [] knL 46).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
Definition srGr : list expr := Eval vm_compute in s_regs (fst (fst rGr)).
(* [comment removed for export] *)
Definition srL20 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2N6@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vprv9@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrL2 : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!ii0!ho5!hob@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rL2 := Eval vm_compute in runM scrL2 (SS 0x47478 srL20 [] knL 46).
Definition srL2 : list expr := Eval vm_compute in s_regs (fst (fst rL2)).
(* [comment removed for export] *)
Definition srL30 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N6@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vprv9@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rL3 := Eval vm_compute in runM noscr (SS 0x47494 srL30 [] knL 46).
Definition srL3 : list expr := Eval vm_compute in s_regs (fst (fst rL3)).
(* [comment removed for export] *)
Definition srH0 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$3+vggm8@3$1$0@1$5-p0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$3Z@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition knH : ltac2:(zQ "20!h8!hm1@1$0$1") := ltac2:(zQ "70!jb!ija!hs8!hsf!ik0!hu3!hm1@3$0$6@3$4@2$5@1$3N0-o8N8@1$2+knksc$1").
(* [comment removed for export] *)
Definition scrHs : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hma!k1!jb!r1!ho5!hob@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rHs := Eval vm_compute in runM scrHs (SS 0xebe8c srH0 [] knH 46).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
(* [comment removed for export] *)
Definition scrHo : ltac2:(zQ "10!p0$0") := ltac2:(zQ "80!hma!jb!k1!hob!hsf!ii0!r1!ho5@3$7@3$1$0$5@3$1$0$6@1$2$0@3$1$3@1$4Nd@3$1$3@1$4Nc@1$2$3@1$2$0").
Definition rHo := Eval vm_compute in runM scrHo (SS 0xebe8c srH0 [] knH 46).
Definition srHo : list expr := Eval vm_compute in s_regs (fst (fst rHo)).
(* [comment removed for export] *)
Definition scrHk : ltac2:(zQ "10!p0$0") := ltac2:(zQ "70!jb!hob!hsf!hma!k1!ii0!ho5@3$6@3$0$3$5@3$0$3$5@1$4$3@3$0$1@1$2Nd@3$0$1@1$2Nc@3$0$1@1$2N9@3$0$1@1$2N8@3$0$1@1$2Na@3$0$1@1$2Nb@1$4$1@1$4$3").
Definition rHk := Eval vm_compute in runM scrHk (SS 0xebe8c srH0 [] knH 46).
Definition srHk : list expr := Eval vm_compute in s_regs (fst (fst rHk)).
(* [comment removed for export] *)
Definition srI0 : ltac2:(zQ "20!h8!hob@1$0$1") := ltac2:(zQ "60!hob!jb!hsf!hs8!k1!ij4@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgrmr8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rI := Eval vm_compute in runM noscr (SS 0x475c4 srI0 [] knL 46).
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).

(* [comment removed for export] *)
End FPX1.
(* [comment removed for export] *)

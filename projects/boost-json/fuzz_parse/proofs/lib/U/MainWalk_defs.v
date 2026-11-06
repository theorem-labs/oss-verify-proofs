(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefMainEntry RefMainEntryN LibStdioCall LibDiagKn.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil03nat04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~l17scriptsl19sym_statel18sidecond04truel18sym_exec89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UdMainWalk_defs4FPX1~~~~~~s25FUELMs26STOPSM69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hhafloaded_segmentsl16kentry04bool03fstl15carryl15s_logl13SCRl14expr3h5LinuxProcessSemantics5Riscv5Instrhp47ALU_ADDl14EAlul14ELitl14EVarl13KWrl12SAs24MSTKl16KAlignl14KImgl16KRange46Stdlib6ZArith6BinInt1Zig33sub05falseig33pows23knAs23spxl15KWords23knL" s.
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPSM : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+tvsg4@3$1$0+tvqs4@3$1$0+uuil0@3$1$0+knir4@3$1$0+kngn0@3$1$0+kngn8@3$1$0+knhnc@3$1$0+knhpc@3$1$0+knhr8@3$1$0+knih0@3$1$0+kniic@3$1$0+knin4@1$2$0").
Definition FUELM : nat := 3000.
Definition runM : ltac2:(zQ "50!kb!p0!pa!h8!q6>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k1!r1!p0!q6!r7!pa!hg9!hh1!hl0\3scr$2\2ss$5@7$4$8$6$1$7^2^1@1$0$3").
Definition carryM : ltac2:(zQ "70!h8!kb!hm3!q6!hmc!p0!pa>1r@2$1@2$1$6@1$0$3$5>2kn@1$0$2@2$1@2$1@1$0$2@1$0$3@1$0$4") := ltac2:(zQ "b0!h8!kb!q6!pa!hn2!p0!hmc!k1!hn7!hm3!hnf\1r@2$1@2$1$3@1$0$2$5\2kn@1$0$9@3$8@1$a@3$4$3@1$0$2@3$4@2$1$3@1$0$2$5^2^1@1$7$6").
Definition noscr : ltac2:(zQ "10!p0$0") := ltac2:(zQ "40!k1!hmc!ho7!hod@3$2@1$0$1@1$0$3@1$0$1").
Definition spx : ltac2:(zQ "20!j7!hod>1k$0$1") := ltac2:(zQ "50!j7!hr8!hs3!hsa!ht1\1k$0@3$2$1@1$4N0@1$3^1").

(* [comment removed for export] *)
Definition MSTK : Z := 1024.
Definition knL : ltac2:(zQ "20!h8!hm3@1$0$1") := ltac2:(zQ "c0!hm3!jb!ht1!ht8!hte!hu3!k1!hsa!hua!hv3!hva!ihb@3$1$0@2$8@1$2N0+h0@3$1$0@3$a@1$2N0+nvvvogggggg0+ogggggggggg0@3$1$0@2$3@2$4@1$2N0@2$b-o0$5$5@3$1$0@2$3@2$4@1$7Z+vsgg0+jlgg0@3$1$0@2$9+hggg0+vkgg0@1$6$0").

(* [comment removed for export] *)
Definition scrU : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!r1!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").       (* [comment removed for export] *)
Definition rU := Eval vm_compute in runM scrU (SS 0x46fe4 sr_mainN [] kn_mainN 40).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
Definition knU : list kentry := Eval vm_compute in fst (fst (carryM rU kn_mainN)).

(* [comment removed for export] *)
Definition scrA : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!ii2!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rA := Eval vm_compute in runM scrA (SS 0x46fe4 sr_main [] kn_main 40).
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in fst (fst (carryM rA kn_main)).

(* [comment removed for export] *)
Definition srC0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (ELit 3).
Definition rC := Eval vm_compute in runM noscr (SS 0xef334 srC0 [] knA 40).
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).

(* [comment removed for export] *)
Definition srF0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (EVar 40).
Definition knF0 : ltac2:(zQ "20!h8!hm3@1$0$1") := ltac2:(zQ "70!ii9!ihb!jb!ht1!hva!hm3!ij0@3$2$5@3$4@1$3Ni8@2$1@2$0+2+k0+vvf@2$1@2$0+2+k0+1$6").
Definition scrF : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!ii2!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rF := Eval vm_compute in runM scrF (SS 0xef334 srF0 [] knF0 41).
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).

(* [comment removed for export] *)
Definition srE0 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2Nh7@3$1$0@1$2N3@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2Ni1@3$1$0@1$3+3@3$1$0@1$3+hggg0@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrE : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!ii2!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rE := Eval vm_compute in runM scrE (SS 0x47038 srE0 [] knL 46).
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
(* [comment removed for export] *)
Definition srN0 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vthj9@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrN : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!r1!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").      (* [comment removed for export] *)
Definition scrN' : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!ii2!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rN := Eval vm_compute in runM scrN (SS 0x47070 srN0 [] knL 46).
Definition rN' := Eval vm_compute in runM scrN' (SS 0x47070 srN0 [] knL 46).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN)).
Definition srN' : list expr := Eval vm_compute in s_regs (fst (fst rN')).
(* [comment removed for export] *)
Definition srR0 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vthj9@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrR : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!r1!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition scrR' : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!ii2!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rR := Eval vm_compute in runM scrR (SS 0x470b0 srR0 [] knL 46).
Definition rR' := Eval vm_compute in runM scrR' (SS 0x470b0 srR0 [] knL 46).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition srR' : list expr := Eval vm_compute in s_regs (fst (fst rR')).
(* [comment removed for export] *)
Definition srL50 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$3+vjlmc@3$1$0@1$5-p0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2N7@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vthj9@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition knL5 : ltac2:(zQ "20!h8!hm3@1$0$1") := ltac2:(zQ "70!jb!hsa!ht1!ijc!hte!hm3!ik4@3$0$5@3$3@2$4@1$2N0-o8N8@1$1+kngsc$6").
(* [comment removed for export] *)
Definition scrL5a : ltac2:(zQ "10!p0$0") := ltac2:(zQ "70!hmc!jb!k1!r1!ii2!ho7!hod@3$5@3$1$0$3@3$1$0$4@3$1$0$3@1$2$0@1$2$6@1$2$0").
Definition rL5a := Eval vm_compute in runM scrL5a (SS 0xef334 srL50 [] knL5 46).
Definition srL5a : list expr := Eval vm_compute in s_regs (fst (fst rL5a)).
(* [comment removed for export] *)
Definition srL50z : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit 0).
Definition rL5b := Eval vm_compute in runM noscr (SS 0xef334 srL50z [] knL5 46).
Definition srL5b : list expr := Eval vm_compute in s_regs (fst (fst rL5b)).
(* [comment removed for export] *)
Definition srL50e : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit (2^64 - 21)).
Definition rL5c := Eval vm_compute in runM noscr (SS 0xef334 srL50e [] knL5 46).
Definition srL5c : list expr := Eval vm_compute in s_regs (fst (fst rL5c)).
(* [comment removed for export] *)
Definition srM0 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vthj9@3$1$0@1$2N7@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrMa : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!ii2!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").    (* [comment removed for export] *)
Definition scrMb : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!r1!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rMa := Eval vm_compute in runM scrMa (SS 0x47064 srM0 [] knL 46).
Definition rMb := Eval vm_compute in runM scrMb (SS 0x47064 srM0 [] knL 46).
Definition srMa : list expr := Eval vm_compute in s_regs (fst (fst rMa)).
Definition srMb : list expr := Eval vm_compute in s_regs (fst (fst rMb)).
(* [comment removed for export] *)
Definition srG0 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N4@3$1$0@1$3+vthj9@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrGb : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!ii2!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").    (* [comment removed for export] *)
Definition scrGr : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!r1!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rGb := Eval vm_compute in runM scrGb (SS 0x47078 srG0 [] knL 46).
Definition rGr := Eval vm_compute in runM scrGr (SS 0x47078 srG0 [] knL 46).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
Definition srGr : list expr := Eval vm_compute in s_regs (fst (fst rGr)).
(* [comment removed for export] *)
Definition srL20 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2N6@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vthj9@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrL2 : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!ii2!ho7!hod@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rL2 := Eval vm_compute in runM scrL2 (SS 0x4708c srL20 [] knL 46).
Definition srL2 : list expr := Eval vm_compute in s_regs (fst (fst rL2)).
(* [comment removed for export] *)
Definition srL30 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N6@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+vthj9@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rL3 := Eval vm_compute in runM noscr (SS 0x470a8 srL30 [] knL 46).
Definition srL3 : list expr := Eval vm_compute in s_regs (fst (fst rL3)).
(* [comment removed for export] *)
Definition srH0 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$3+vjlh0@3$1$0@1$5-p0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$3Z@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition knH : ltac2:(zQ "20!h8!hm3@1$0$1") := ltac2:(zQ "70!jb!hsa!ht1!ijc!hte!hm3!ik4@3$0$5@3$3@2$4@1$2N0-o8N8@1$1+kngu0$6").
(* [comment removed for export] *)
Definition scrHs : ltac2:(zQ "10!p0$0") := ltac2:(zQ "60!hmc!k1!jb!r1!ho7!hod@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rHs := Eval vm_compute in runM scrHs (SS 0xef334 srH0 [] knH 46).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
(* [comment removed for export] *)
Definition scrHo : ltac2:(zQ "10!p0$0") := ltac2:(zQ "80!hmc!jb!k1!hod!ht1!ii2!r1!ho7@3$7@3$1$0$5@3$1$0$6@1$2$0@3$1$3@1$4Nd@3$1$3@1$4Nc@1$2$3@1$2$0").
Definition rHo := Eval vm_compute in runM scrHo (SS 0xef334 srH0 [] knH 46).
Definition srHo : list expr := Eval vm_compute in s_regs (fst (fst rHo)).
(* [comment removed for export] *)
Definition scrHk : ltac2:(zQ "10!p0$0") := ltac2:(zQ "70!jb!hod!ht1!hmc!k1!ii2!ho7@3$6@3$0$3$5@3$0$3$5@1$4$3@3$0$1@1$2Nd@3$0$1@1$2Nc@3$0$1@1$2N9@3$0$1@1$2N8@3$0$1@1$2Na@3$0$1@1$2Nb@1$4$1@1$4$3").
Definition rHk := Eval vm_compute in runM scrHk (SS 0xef334 srH0 [] knH 46).
Definition srHk : list expr := Eval vm_compute in s_regs (fst (fst rHk)).
(* [comment removed for export] *)
Definition srI0 : ltac2:(zQ "20!h8!hod@1$0$1") := ltac2:(zQ "60!hod!jb!ht1!hsa!k1!ij6@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+hgurv8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rI := Eval vm_compute in runM noscr (SS 0x471d8 srI0 [] knL 46).
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).

(* [comment removed for export] *)
End FPX1.
(* [comment removed for export] *)

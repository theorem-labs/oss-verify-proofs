(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MainWalk_defs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kc7scriptskc9sym_statekc8sidecond04true89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAsMainWalk_defs4FPX1~~~~~~r27STOPSAM69OSSVerify6Proofsaboost_jsonafuzz_parse3libdMainWalk_defs~~~~~~hg65FUELMkc8sym_exec69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~hlafloaded_segmentskc6kentrykc4EVarhg64MSTKkc4KImgkc6KAlignkc6KRangekc3KWrkc2SA46Stdlib6ZArith6BinInt1Zhte3subkc5KWordr24ESTKkc4ELithte3oppkc4exprhg63spx04boolkc3SCRhte3powr23knA05falser24aknL03app" s.
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPSAM : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+pgrlc@3$1$0+pgrl8@3$1$0+ouvt4@3$1$0+nqhq0@3$1$0+rurv0@3$1$0+rupqc@3$1$0+rupr4@3$1$0+rurh4@3$1$0+ruqr8@3$1$0+ruqt8@3$1$0+ruqv4@3$1$0+rurkc@3$1$0+rurm8@3$1$0+rurr0@3$1$0+hpkkvc@1$2$0").
Definition runAM : ltac2:(zQ "50!k6!ob!p5!h8!q1>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k1!qc!vc!hk6!ob!q1!hkf!p5!hof\3scr$4\2ss$7@7$6$8$3$1$2^2^1@1$0$5").

(* [comment removed for export] *)
Definition aknL : ltac2:(zQ "20!h8!hq2@1$0$1") := ltac2:(zQ "b0!hq2!jb!hqb!hr2!hra!k1!hs1!hsa!ht3!ht9!hv6@3$1$0@2$6@1$2N0+h0@3$1$0@3$7@1$2N0+nvvvogggggg0+ogggggggggg0@3$1$0@2$8@2$9@1$2N0@2$a-o0$3$3@3$1$0@2$4+hggg0+mngg0@3$1$0@2$4+hqtgg0+hrngg0@1$5$0").

(* [comment removed for export] *)
Definition ESTK : Z := 2048.
Definition kn_amain : ltac2:(zQ "20!h8!hq2@1$0$1") := ltac2:(zQ "d0!hq2!jb!hqb!ht9!hvd!ig5!igc!hra!ht3!k1!hs1!hsa!ih3@3$1$0@2$a@1$2N0+h0@3$1$0@3$b@1$2N0+nvvvogggggg0+ogggggggggg0@3$1$0@2$8@2$3@1$2N0@1$c$5$5@3$1$0@3$4@2$3@1$2N0+8N8@1$2N1@3$1$0@3$4@2$3@1$2N0+h0N8@1$2N2@3$1$0@3$4@2$3@1$6Z+nhkkh8N8@1$2Ni7@3$1$0@2$8@2$3@1$6Z+mvkjj4+4@3$1$0@2$7+hggg0+mngg0@3$1$0@2$7+hqtgg0+hrngg0@1$9$0").
(* [comment removed for export] *)
Definition kn_amainU : ltac2:(zQ "20!h8!hq2@1$0$1") := ltac2:(zQ "b0!hq2!jb!hqb!ig5!hra!k1!hs1!hsa!ht3!ht9!ih3@3$1$0@2$6@1$2N0+h0@3$1$0@3$7@1$2N0+nvvvogggggg0+ogggggggggg0@3$1$0@2$8@2$9@1$2N0@1$a$3$3@3$1$0@2$4+hggg0+mngg0@3$1$0@2$4+hqtgg0+hrngg0@1$5$0").

(* [comment removed for export] *)
Definition sr_amain : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!ii1!k1@3$1$0@1$3Z@3$1$0@1$3+hpjti4@3$1$0@1$4-j0@3$1$0@1$2N9@3$1$0@1$3+mvkjt8@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$2Nf@3$1$0@1$3+2@3$1$0@1$4+8@3$1$0@1$2Nh2@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@1$5$0").
Definition sr_amainN : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!ii1!k1@3$1$0@1$3Z@3$1$0@1$3+hpjti4@3$1$0@1$4-j0@3$1$0@1$2N9@3$1$0@1$3+mvkjt8@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$4+8@3$1$0@1$2Nh2@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@1$5$0").

(* [comment removed for export] *)
Definition scrU : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!qc!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").       (* [comment removed for export] *)
Definition rU := Eval vm_compute in runAM scrU (SS 0xbe920 sr_amainN [] kn_amainU 40).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
Definition knU : list kentry := Eval vm_compute in fst (fst (carryM rU kn_amainU)).

(* [comment removed for export] *)
Definition scrA : ltac2:(zQ "10!ob$0") := ltac2:(zQ "40!k1!ii8!iie!iha@3$2@1$0$1@1$0$3@1$0$1").
Definition rA := Eval vm_compute in runAM scrA (SS 0xbe920 sr_amain [] kn_amain 40).
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in fst (fst (carryM rA kn_amain)).

(* [comment removed for export] *)
Definition srC0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (ELit 3).
Definition rC := Eval vm_compute in runAM noscr (SS 0x1a6628 srC0 [] knA 40).
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).

(* [comment removed for export] *)
Definition srF0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (EVar 40).
Definition knF0 : ltac2:(zQ "20!h8!hq2@1$0$1") := ltac2:(zQ "70!ij4!hv6!jb!ijb!hqb!hsa!hq2@3$2$6@3$5@1$4Ni8@2$1@2$0+2+k0+vvf@2$1@2$0+2+k0+1$3").
Definition scrF : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!ik1!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rF := Eval vm_compute in runAM scrF (SS 0x1a6628 srF0 [] knF0 41).
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).

(* [comment removed for export] *)
Definition srE0 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2Nh7@3$1$0@1$2N3@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2Ni1@3$1$0@1$3+3@3$1$0@1$3+hggg0@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrE : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!ik1!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rE := Eval vm_compute in runAM scrE (SS 0xbe974 srE0 [] aknL 46).
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
(* [comment removed for export] *)
Definition srN0 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+muiop0@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrN : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!qc!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").      (* [comment removed for export] *)
Definition scrN' : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!ik1!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rN := Eval vm_compute in runAM scrN (SS 0xbe9ac srN0 [] aknL 46).
Definition rN' := Eval vm_compute in runAM scrN' (SS 0xbe9ac srN0 [] aknL 46).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN)).
Definition srN' : list expr := Eval vm_compute in s_regs (fst (fst rN')).
(* [comment removed for export] *)
Definition srR0 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+muiop0@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrR : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!qc!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition scrR' : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!ik1!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rR := Eval vm_compute in runAM scrR (SS 0xbe9ec srR0 [] aknL 46).
Definition rR' := Eval vm_compute in runAM scrR' (SS 0xbe9ec srR0 [] aknL 46).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition srR' : list expr := Eval vm_compute in s_regs (fst (fst rR')).
(* [comment removed for export] *)
Definition srL50 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2N7@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+muiop0@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
(* [comment removed for export] *)
Definition scrL5a : ltac2:(zQ "10!ob$0") := ltac2:(zQ "70!ii8!k1!jb!ik1!qc!iie!iha@3$5@3$2$0$3@3$2$0$4@1$1$0@1$1$6@1$1$0").
Definition rL5a := Eval vm_compute in runAM scrL5a (SS 0xbea08 srL50 [] aknL 46).
Definition srL5a : list expr := Eval vm_compute in s_regs (fst (fst rL5a)).
(* [comment removed for export] *)
Definition srL50z : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit 0).
Definition rL5b := Eval vm_compute in runAM noscr (SS 0xbea08 srL50z [] aknL 46).
Definition srL5b : list expr := Eval vm_compute in s_regs (fst (fst rL5b)).
(* [comment removed for export] *)
Definition srL50e : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit (2^64 - 1)).
Definition rL5c := Eval vm_compute in runAM noscr (SS 0xbea08 srL50e [] aknL 46).
Definition srL5c : list expr := Eval vm_compute in s_regs (fst (fst rL5c)).
(* [comment removed for export] *)
Definition srM0 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+muiop0@3$1$0@1$2N7@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrMa : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!ik1!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").    (* [comment removed for export] *)
Definition scrMb : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!qc!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rMa := Eval vm_compute in runAM scrMa (SS 0xbe9a0 srM0 [] aknL 46).
Definition rMb := Eval vm_compute in runAM scrMb (SS 0xbe9a0 srM0 [] aknL 46).
Definition srMa : list expr := Eval vm_compute in s_regs (fst (fst rMa)).
Definition srMb : list expr := Eval vm_compute in s_regs (fst (fst rMb)).
(* [comment removed for export] *)
Definition srG0 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N4@3$1$0@1$3+muiop0@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrGb : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!ik1!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").    (* [comment removed for export] *)
Definition scrGr : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!qc!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").     (* [comment removed for export] *)
Definition rGb := Eval vm_compute in runAM scrGb (SS 0xbe9b4 srG0 [] aknL 46).
Definition rGr := Eval vm_compute in runAM scrGr (SS 0xbe9b4 srG0 [] aknL 46).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
Definition srGr : list expr := Eval vm_compute in s_regs (fst (fst rGr)).
(* [comment removed for export] *)
Definition srL20 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$2N6@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+muiop0@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrL2 : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!ik1!iie!iha@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rL2 := Eval vm_compute in runAM scrL2 (SS 0xbe9c8 srL20 [] aknL 46).
Definition srL2 : list expr := Eval vm_compute in s_regs (fst (fst rL2)).
(* [comment removed for export] *)
Definition srL30 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N6@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$3+muiop0@3$1$0@1$2N3@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rL3 := Eval vm_compute in runAM noscr (SS 0xbe9e4 srL30 [] aknL 46).
Definition srL3 : list expr := Eval vm_compute in s_regs (fst (fst rL3)).
(* [comment removed for export] *)
Definition srH0 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$3+hqshsc@3$1$0@1$5-p0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$3+2@3$1$0@1$2N3@3$1$0@1$3Z@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N4@3$1$0@1$3+3@3$1$0@1$2N5@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition knH : ltac2:(zQ "20!h8!hq2@1$0$1") := ltac2:(zQ "70!jb!ik8!igc!hqb!hvd!ht9!hq2@3$0$6@3$4@2$5@1$3N0-o8N8@1$2+ruqhc$1").
(* [comment removed for export] *)
Definition scrHs : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!ii8!k1!jb!qc!iie!iha@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").
Definition rHs := Eval vm_compute in runAM scrHs (SS 0x1a6628 srH0 [] knH 46).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
(* [comment removed for export] *)
Definition scrHo : ltac2:(zQ "10!ob$0") := ltac2:(zQ "80!ii8!jb!k1!iha!hqb!ik1!qc!iie@3$7@3$1$0$5@3$1$0$6@1$2$0@3$1$3@1$4Nd@3$1$3@1$4Nc@1$2$3@1$2$0").
Definition rHo := Eval vm_compute in runAM scrHo (SS 0x1a6628 srH0 [] knH 46).
Definition srHo : list expr := Eval vm_compute in s_regs (fst (fst rHo)).
(* [comment removed for export] *)
Definition scrHk : ltac2:(zQ "10!ob$0") := ltac2:(zQ "70!jb!iha!hqb!ii8!k1!ik1!iie@3$6@3$0$3$5@3$0$3$5@1$4$3@3$0$1@1$2Nd@3$0$1@1$2Nc@3$0$1@1$2N9@3$0$1@1$2N8@3$0$1@1$2Na@3$0$1@1$2Nb@1$4$1@1$4$3").
Definition rHk := Eval vm_compute in runAM scrHk (SS 0x1a6628 srH0 [] knH 46).
Definition srHk : list expr := Eval vm_compute in s_regs (fst (fst rHk)).
(* [comment removed for export] *)
Definition srI0 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2N3@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rI := Eval vm_compute in runAM noscr (SS 0xbeb14 srI0 [] aknL 46).
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
(* [comment removed for export] *)
Definition srX0 : ltac2:(zQ "20!h8!iha@1$0$1") := ltac2:(zQ "60!iha!jb!hqb!igc!k1!ii1@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-o0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition knX : ltac2:(zQ "20!h8!hq2@1$0$1") := ltac2:(zQ "90!hqb!hq2!jb!hvd!ht9!ikf!k1!ik8!igc@3$5$1@3$2$1@3$3@2$4@1$0N0-j8N8@1$8+hpjti4@3$2$1@3$3@2$4@1$0N0-n8N8@1$0N6@3$2$1@3$3@2$4@1$0N0-n0N8@1$0N7@3$2$1@3$3@2$4@1$0N0-m8N8@1$0N8@3$2$1@3$3@2$4@1$0N0-m0N8@1$0N9@3$2$1@3$3@2$4@1$0N0-l8N8@1$0Na@3$2$1@3$3@2$4@1$0N0-l0N8@1$0Nb@3$2$1@3$3@2$4@1$0N0-k8N8@1$0Nc@3$2$1@3$3@2$4@1$0N0-k0N8@1$0Nd@1$6$1$7").
Definition rX := Eval vm_compute in runAM noscr (SS 0xbeb1c srX0 [] knX 46).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).

(* [comment removed for export] *)
End FPX1.
(* [comment removed for export] *)

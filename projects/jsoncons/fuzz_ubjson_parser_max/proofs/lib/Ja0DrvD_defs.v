(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvRead Ja0DrvG_defs Ja0DrvC_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvD_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvD_defs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "stdpp.bitvector.definitions."], [["1bool"; "1cons"; "1fst"; "1list"; "1nil"; "1pair"; "1prod"; "1snd"; "1true"; "2I"; "2and"; "2eq"; "3nth"; "4Z"; "5ksubl_b"; "6knLH1A"]; ["6knTcA"; "6knTeA"; "6knU0A"; "6knV0A"; "6rLB1A"; "6rT00"; "6rT01"; "6rT10"; "6rT11"; "6rUA"; "6rVA"; "6relay_ok_bA"; "6spxA"; "6sr00"; "6sr01"; "6sr10"]; ["6srLBA"; "6srTm0A"; "6srVA"; "7kn_after"; "8ELit"; "8EVar"; "8SA"; "8SE"; "8expr"; "8kentry"; "8ridx"; "8s_log"; "8s_pc"; "8scripts"; "8sentry"; "8sidecond"]; ["8sr_upd"; "8sym_state"; "9kn_vars_lt"; "9sr_vars_lt"; ":BV"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition STOPS_TA : list Z := 0xa7534 :: 0xa7320 :: STOPSA.
Definition runTA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPS_TA scr ss [].
Definition knTcA (clo chi plo phi : Z) : list kentry :=
KRange (EVar 73) clo chi :: KRange (EVar 79) plo phi :: KWr (SA (ELit 0) 0x66d350) 16 :: KWr (SA (ELit 0) 0x68edd0) 544 :: knT0A.
Definition rT00 := Eval vm_compute in runTA scr0 (SS 0xa747c srT0A [] (knTcA 0 0 0 0) 81).
Definition rT01 := Eval vm_compute in runTA scr0 (SS 0xa747c srT0A [] (knTcA 0 0 1 67108857) 81).
Definition rT10 := Eval vm_compute in runTA scr0 (SS 0xa747c srT0A [] (knTcA 1 32767 0 0) 81).
Definition rT11 := Eval vm_compute in runTA scr0 (SS 0xa747c srT0A [] (knTcA 1 32767 1 67108857) 81).
Definition sr00 : list expr := Eval vm_compute in s_regs (fst (fst rT00)).
Definition sr01 : list expr := Eval vm_compute in s_regs (fst (fst rT01)).
Definition sr10 : list expr := Eval vm_compute in s_regs (fst (fst rT10)).
Definition sr11 : list expr := Eval vm_compute in s_regs (fst (fst rT11)).
Definition calls_xA : expr := Eval vm_compute in nth 21 sr11 (ELit 0).
Definition is_case_entryA (K : kentry) : bool :=
existsb (kentry_eqb K) [KRange (EVar 73) 0 0; KRange (EVar 73) 1 32767; KRange (EVar 79) 0 0; KRange (EVar 79) 1 67108857].
Definition uncaseA (kn : list kentry) : list kentry := List.filter (fun K => negb (is_case_entryA K)) kn.
Definition knTeA : list kentry := Eval vm_compute in uncaseA (kn_after rT11 (knTcA 1 32767 1 67108857)).
Definition TSO : Z := -208.
Definition knTkA : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knTeA.
Definition srTm0A : list expr := Eval vm_compute in sr_upd sr11 (ridx 21) (EVar 81).
Definition srU0A : list expr := Eval vm_compute in sr_after_call_j srTm0A (map ridx c_kept) 82.
Definition knU0A : list kentry := Eval vm_compute in kn_blk2A 92 ++ knTkA.
Definition rUA := Eval vm_compute in runTA scr0 (SS 0xa74e0 srU0A [] knU0A 114).
Definition srUA : list expr := Eval vm_compute in s_regs (fst (fst rUA)).
Definition srV0A : list expr := Eval vm_compute in sr_after_call_j srUA (map ridx c_kept) 114.
Definition knV0A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knU0A.
Definition rVA := Eval vm_compute in runTA scr0 (SS 0xa74f4 srV0A [] knV0A 146).
Definition srVA : list expr := Eval vm_compute in s_regs (fst (fst rVA)).
Definition spxA (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition knLH1A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knTkA.
Definition srLHA : list expr :=
[ELit 0; EVar 85; spxA (-208); ELit 67584; ELit 6745472; EVar 86; EVar 87; EVar 88;
EVar 79; EVar 82; EVar 89; EVar 90; EVar 91; EVar 92; EVar 93; EVar 94; EVar 95; EVar 96;
EVar 83; EVar 84; ELit 6738768; EVar 81; ELit 0; ELit 18446744073709551614; EVar 30; EVar 31; EVar 32; EVar 33;
EVar 97; EVar 98; EVar 99; EVar 100].
Definition shared_posA : list nat := [2; 3; 4; 8; 20; 21; 22; 23]%nat.
Definition relay_ok_bA (sr : list expr) : bool :=
forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLHA (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_posA.
Definition rLB1A := Eval vm_compute in runTA scr0 (SS 0xa7534 srLHA [] knLH1A 102).
Definition srLBA : list expr := Eval vm_compute in s_regs (fst (fst rLB1A)).
Definition knLB1A : list kentry := Eval vm_compute in kn_after rLB1A knLH1A.
Definition LIBSTK : Z := 1048576.
Definition srLr0A : list expr := Eval vm_compute in sr_upd (sr_after_call_j srLBA (map ridx c_kept) 102) (ridx 10) (ELit 0).
Lemma tgt_itinerary_okA : ltac2:(TCodec.tc2 tcn__Ja0DrvD_defs "VH':';'6'=%2211%3212%4213(5&Q<&2'QA'3'Q?%211%<241'Q=&E%83321%93851%;11&G%<3761%=3<91%?11%A4EE51&F%A3<;1%B3A>1%D11%F4IJ51&H%F3A@1%G3FC1%I11%K4MO51+dmYD%M4Q1Q111+_Sf0%O4Q2Q321%Q04Q2Q412%Q73Q261'0&>&Q3&@z%241111%42O1&A%7221(8%QB3:21+1+QooooI%:49921%<2N1%>218%QH3@17+ooO%?471>>%A2Q81%C21=%QM3E1<%C4;5;:%E2Q21%G21A%R13I1@'Q8%QI11&Q@&N&Q:(QDy5+E(9%43321%611(Q5uRA%211%<3;41&Q1%RB3?21&?%Q;2Q51%RE3Q=1Q4&C%Q>214%RH3Q@1Q7'Q9%R@11&J%QB216%RM3317&I&B%QF221%S13712&K&M%Q031HE%311%S63QN1QE&O%Q431LI%711%S:3R21QI&Q2%:11%S=3R51QL&QBuRB%221M%SA3R91R0&QC%124Q2%SD3R<1R3%SD2SCS9'Q>%S=11%SG231%SA3S<S;K%SB3SAS>1%SD11&7%13SDSA4%SH4SLSB31&Q;%116%SK4<:31+^liH(4%11SI%SO4T3SI31%31@%T14B@21%T83@71%T13SLSKQ>%T23T1SN1%T411%@3T3T03%T74T;T121%?14%T94JH21%T:4T>T4S><%T;4LJ1;%TB3J31&D%T<3T7T61%T=3T<T91%T?11%K3T>T;3%TB4TFT<21%J14%TD4Q5Q321+dmb<%TF4TJT@1H(1(Q7(Q6(Q4%11SE+V]djD%4221u1%51SB%83321%:3QA1Q1%U24QCQA<1%U93QA?1%U92S8S8%U:21S9%U;21S:&<u:&Q0%34S>21?u;%54S@13A%U=4SASA31%74SB@5C%U?4;SC21u2%:4SE18F%UB4=SF31%S<1R:uR?%S>11%UF4SJSJ31+dmZ8%N11%UI4ESM31&L-V@%211%UM4HT141%V43H<1%V62L1%V72QD1%V82QO1%V92RD1%V:2RH1%V;2RM1%V<2S11%V=2S61%V>2S<1%V?2SA1%V@2SG1%VA2SK1%VB2SO1%VC2TA1%VD2TF1%VE2TL1%VF2U31%VG2U?1").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX_1.

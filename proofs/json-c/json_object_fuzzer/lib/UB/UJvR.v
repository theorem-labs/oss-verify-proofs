(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QsRG Q7m0 QSpR QuJV QCPB QH7x QBxa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWQV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QBxa.Mq3.
Import UWQV.Mq0.
Import QqES.Mq0.
Import U1oC.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition STOPS : list Z := [0x5f438; 0x5f9b8; 0x5fe24; 0x5f33c; 0x21024; 0x53a78; 0x50e6c; 0x551dc]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
match stdio_call nv sr kn with
| Some r => r
| None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
end.

Definition KEPT_MC : list nat := map ridx callee_kept.
Definition KEPT_CS : list nat := map ridx callee_saved.

Definition IHI : Z := 0x99000.

Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

Definition ssA0 : sym_state := SS 0x20b84 sr_main [] kn_main 39.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 39).
Definition knB0 : list kentry :=
KRange (EVar 2) 0x7fff80000000 0x800000400000
:: KRange (EVar 39) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0x6086c srB0 [] knB0 40.
Definition scrB : scripts := SCR [false] [] [].
Definition rB := Eval vm_compute in run scrB ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.

Definition logM1 : list sentry :=
[SE (SA (EVar 0) (-544)) 1 (ELit 32);
SE (SA (EVar 0) (-552)) 8 (ELit 7954887939408031598);
SE (SA (EVar 0) (-560)) 8 (ELit 7953747406983097443)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 40.

Definition ssC0 : sym_state := SS 0x55024 srC0 [] knC0 72.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 72.

Definition ssD0 : sym_state := SS 0x55024 srD0 [] knC 104.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.

Definition PX : expr := EVar 114.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 104.

Definition ssE0 : sym_state := SS 0x55c3c srE0 [] knE0 136.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 136.

Definition ssF0 : sym_state := SS 0x55024 srF0 [] knE 168.
Definition scrF : scripts := SCR [true; true] [] [].
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 168.

Definition ssG0 : sym_state := SS 0x55024 srG0 [] knG0 200.
Definition scrG : scripts := SCR [true] [] [].
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 200.

Definition ssH0 : sym_state := SS 0x55024 srH0 [] knH0 232.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Definition scOF : stdio_res := Eval vm_compute in sc_of 232 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

Definition ssI0 : sym_state := SS 0x5559c srI0 [] knI0 264.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Definition scrG3 : scripts := SCR [false] [] [].
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 200 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.

Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 232.
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 232 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.

Definition ssI30 : sym_state := SS 0x5559c srI30 [] knI30 264.
Definition rI3 := Eval vm_compute in run scr0 ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_after rI3 knI30.

Definition scrF4 : scripts := SCR [true; false] [] [].
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 168 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.

Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 200.
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.

Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 200.

Definition ssH40 : sym_state := SS 0x55024 srH40 [] knH40 232.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 232 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.

Definition ssI40 : sym_state := SS 0x5559c srI40 [] knI40 264.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

#[using="Type"] Lemma itinerary_63_64 :
(s_pc (fst (fst rG3)), snd (fst rG3))
= (0x551dc%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
/\ stdio_call 200 srG3 knG3 = Some scG3
/\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0x5576c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x12981, ELit 1)
/\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0x551dc%Z, [])
/\ stdio_call 232 srH3 knH3 = Some scH3
/\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0x5559c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
/\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0x50e6c%Z, [])
/\ (s_pc (fst (fst rF4)), snd (fst rF4))
= (0x551dc%Z, [SCBr false BC_GEU (ELit 63) PX;
SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
/\ stdio_call 168 srF4 knF4 = Some scF4
/\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0x5618c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
/\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0x551dc%Z, [])
/\ stdio_call 232 srH4 knH4 = Some scH4
/\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0x5559c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
/\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0x50e6c%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.

#[using="Type"] Lemma itinerary_le62 :
(s_pc (fst (fst rA)), snd (fst rA)) = (0x60868%Z, [])
/\ (s_pc (fst (fst rB)), snd (fst rB))
= (0x5f438%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 39) (ELit 0)) (ELit 18446744073709547521)])
/\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x5fe24%Z, [])
/\ (s_pc (fst (fst rE)), snd (fst rE))
= (0x5f438%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
/\ (s_pc (fst (fst rF)), snd (fst rF))
= (0x5f438%Z, [SCBr true BC_GEU (ELit 63) PX;
SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
/\ (s_pc (fst (fst rG)), snd (fst rG))
= (0x5f438%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
/\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x551dc%Z, [])
/\ stdio_call 232 srH knH = Some scOF
/\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0x5559c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
= (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
/\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x50e6c%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPGEN1.

End Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QBxa.Mq3.
Import UWQV.Mq0.
Import QqES.Mq0.
Import U1oC Um90.Mq0.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition STOPS : list Z := [0x5f438; 0x5f9b8; 0x5fe24; 0x5f33c; 0x21024; 0x53a78; 0x50e6c; 0x551dc]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.
Definition KEPT_CS : list nat := map ridx callee_saved.
Definition IHI : Z := 0x99000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition srRE_base : list expr :=
[ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x77c00; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

Definition knRE0 : list kentry :=
[KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
KWr (SA (EVar 0) (-8388608)) 8388608;
KRange (EVar 2) 0x7fff80000000 0x800000400000;
KWr (SA (ELit 0) 0x66000) 0x33000;
KImg 0x10000 0x66f30; KImg 0x66f31 0x66f79;  KImg 0x76f79 0x77b30; KImg 0x97c08 0x97c18;
KWord (SA (ELit 0) 0x77b38) 8 (ELit 0x77b38);
KWord (SA (ELit 0) 0x77b58) 4 (EVar 5);
KImg 0x77b64 0x77bb0; KImg 0x77bb8 0x77bd0; KImg 0x77bd8 0x77bf0;
KImg 0x77c00 0x77c10; KImg 0x77c20 0x97c08; KImg 0x97c40 0x97e70;
KWord (SA (ELit 0) 0x97e70) 8 (EVar 38);
KImg 0x97e78 0x97e80; KImg 0x97e91 0x97e98;
KWord (SA (ELit 0) 0x97ec0) 8 (ELit 4096);
KImg 0x97ec8 0x97ef8;
KImg 0x97f00 0x97f78; KImg 0x98320 0x99000;
KRange (EVar 5) 1 4194303].

Definition ssB0 : sym_state := SS 0x20db0 srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.

Definition logM1 : list sentry :=
[SE (SA (EVar 0) (-542)) 1 (ELit 32);
SE (SA (EVar 0) (-544)) 2 (ELit 28271);
SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

Definition ssC0 : sym_state := SS 0x55024 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

Definition ssD0 : sym_state := SS 0x55024 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

Definition ssE0 : sym_state := SS 0x55c3c srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

Definition ssF0 : sym_state := SS 0x55024 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

Definition ssG0 : sym_state := SS 0x55024 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

Definition ssH0 : sym_state := SS 0x55024 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Definition scRE : stdio_res := Eval vm_compute in
match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

#[using="Type"] Lemma itinerary_re :
(s_pc (fst (fst rB)), snd (fst rB)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x5f438%Z, [])
/\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x5fe24%Z, [])
/\ (s_pc (fst (fst rE)), snd (fst rE))
= (0x5f438%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
/\ (s_pc (fst (fst rF)), snd (fst rF))
= (0x5f438%Z, [SCBr true BC_GEU (ELit 61) PX;
SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
/\ (s_pc (fst (fst rG)), snd (fst rG))
= (0x5f438%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
/\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x551dc%Z, [])
/\ stdio_call 231 srH knH = Some scRE
/\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0x5559c%Z, 0x66d38%Z, 2%Z)
/\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
/\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x50e6c%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPGEN1.

End Mq1.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEVk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require USPu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import USPu. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UU2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UU2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8LG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8LG.
Import ListNotations.
Open Scope bv_scope.

Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma exit_pre_regs : forall regs regs' mem model code pending,
getr regs' 2 = getr regs 2 -> getr regs' 4 = getr regs 4 -> getr regs' 10 = getr regs 10 ->
exit_pre regs mem model code pending -> exit_pre regs' mem model code pending.
Proof.
intros regs regs' mem model code pending H2 H4 H10 (sp & tp & tid & wp2 & rp2 & EC & REST).
exists sp, tp, tid, wp2, rp2. split; [|exact REST].
destruct EC; split; try assumption; congruence.
Qed.

#[using="Type"] Theorem ref_main_ret : forall regs mem model code pending,
exit_pre regs mem model code pending ->
realizes RSEGS (mkCfg (mkst regs (0x508ac : word) mem (seg_rom RSEGS)) model)
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
intros regs mem model code pending PRE.
assert (Hh : m_halted model = None) by (destruct PRE as (? & ? & ? & ? & ? & _ & Hh & _); exact Hh).
assert (Hlazy : m_vm_lazy model = []) by (destruct PRE as (? & ? & ? & ? & ? & _ & _ & Hl & _); exact Hl).
eapply rz_msteps; [exact Hh | exact Hlazy | |].
{ stepn F_4eac4 D_4eac4. apply mst_refl. }
apply ref_exit. eapply exit_pre_regs; [ | | | exact PRE]; gres; reflexivity.
Qed.

End FPGEN1.

Theorem ref_main_ret_MS : forall (R F : bvmap 5 word) (fc : bv 32) m model code pending,
exit_pre R m model code pending ->
realizes RSEGS (mkCfg (MS R F (Z_to_bv 64 0x508ac) fc None m (seg_rom RSEGS)) model)
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
intros R F fc m model code pending PRE.
replace (Z_to_bv 64 0x508ac) with (0x508ac : word) by (apply bv_eq; reflexivity).
change (MS R F (0x508ac : word) fc None m (seg_rom RSEGS))
with (@mkst F fc R (0x508ac : word) m (seg_rom RSEGS)).
apply ref_main_ret. exact PRE.
Qed.

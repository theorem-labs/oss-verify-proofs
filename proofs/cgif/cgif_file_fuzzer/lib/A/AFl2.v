(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition lit8 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition lit4 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 4) 0 0 [YP09.mkChunk a (CVal 4 (SLit v))].
Definition lit1 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 1) 0 0 [YP09.mkChunk a (CVal 1 (SLit v))].
Definition atom8 (a : Z) (n : nat) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SOff n 0))].
Definition aT : nat := 32.
Definition aC : nat := 33.
Definition aTOP : nat := 34.
Definition aNFP : nat := 35.
Definition aRA : nat := 36.
Definition aB : nat := 37.
Definition aZ : nat := 38.
Definition aQ : nat := 39.
Definition aHAV : nat := 40.
Definition UF_fixed : list (nat * afact) :=
[ (2%nat, mkAF (kHighMemBeg + UNW_STK) kHighMemEnd 4);
(10%nat, mkAF kHighMemBeg kHighMemEnd 3);
(11%nat, mkAF 0 (2 ^ 64 - 1) 0);
(12%nat, mkAF kHighMemBeg kHighMemEnd 3);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)         ;
(aTOP, mkAF (kHighMemBeg + kStackSpan) kHighMemEnd 12) ].
Definition UF_atoms : list (nat * afact) := UF_fixed ++ [ (aNFP, mkAF 0 (2 ^ 64 - 1) 0); (aRA, mkAF 4096 (2 ^ 64 - 1) 0) ].
Definition UF_conds : list acond := [ mkAC BC_LTU (SOff aTOP (- kStackSpan)) (SOff 12%nat 0) ].
Definition UF0 : facts := mkFacts UF_atoms UF_conds [].
Definition UREGS0 : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 13%bv (SLit 0)) 14%bv (SLit 1)) 15%bv (SLit 30).
Definition R_S : YP09.region := YP09.mkRegion (Some 2%nat) (- UNW_STK) 0 (- UNW_STK) 0 [].
Definition R_C : YP09.region := YP09.mkRegion (Some aC) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff aT 0))].
Definition R_T1 : YP09.region := YP09.mkRegion (Some aT) 8 41 0 0
[YP09.mkChunk 8 (CVal 8 (SOff aTOP 0)); YP09.mkChunk 16 (CVal 8 (SOff aTOP (- kStackSpan))); YP09.mkChunk 40 (CVal 1 (SLit 0))].
Definition R_T2 : YP09.region := YP09.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1)
[YP09.mkChunk t_unwinding (CVal 1 (SLit 0))].
Definition R_O1a0 : YP09.region := YP09.mkRegion (Some 10%nat) 8 12 8 12 [].
Definition R_O1b0 : YP09.region := YP09.mkRegion (Some 10%nat) 16 24 16 24 [].
Definition R_O2 : YP09.region := YP09.mkRegion (Some 10%nat) 2056 2064 2056 2064 [].
Definition R_F (b : nat) : YP09.region := YP09.mkRegion (Some b) (- 16) 0 0 0
[YP09.mkChunk (- 16) (CVal 8 (SOff aNFP 0)); YP09.mkChunk (- 8) (CVal 8 (SOff aRA 0))].
Definition UCONST : smem :=
[ lit1 0xa6cd8 1; lit1 0xa5860 1; lit4 0xa5864 0; lit8 (TFIB_TP - 88) TFIB_TSD; atom8 TFIB_TSD aC;
lit8 0x9df78 0x135aa0; lit8 0x135aa0 4096 ].
Definition UMEM0 : smem := [R_S; R_O1a0; R_O1b0; R_O2; R_F 12%nat] ++ UCONST ++ [R_C; R_T1; R_T2].
Definition SS_U0 : sstate := mkSS A_UnwindImpl UREGS0 UMEM0 None UF0.
Definition run_rt (ss : sstate) : sstate := fst (sym_runN tfibsegs tfibtbl_rtA FUEL ss).
Definition runto_rt (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN tfibsegs tfibtbl_rtA FUEL pc ss).
Definition S1 : sstate := Eval vm_compute in run_rt SS_U0.
Definition c_f0_bad : acond := mkAC Instr.BC_GEU (SOff 12%nat 0) (SOff aTOP (-16)).
Definition c_f0_ok : acond := mkAC Instr.BC_LTU (SOff 12%nat 0) (SOff aTOP (-16)).
Definition R_S' : YP09.region := YP09.mkRegion (Some 2%nat) (- UNW_STK) 0 (- UNW_STK) 0
[YP09.mkChunk (-144) (CVal 8 (SOff aTOP 0)); YP09.mkChunk (-136) (CVal 8 (SLit 1)); YP09.mkChunk (-128) (CVal 8 (SLit 0));
YP09.mkChunk (-120) (CVal 8 (SOff 10%nat 0)); YP09.mkChunk (-112) (CVal 8 (SOff 11%nat 0)); YP09.mkChunk (-104) (CVal 8 (SLit 30));
YP09.mkChunk (-96) (CVal 8 (SOff 12%nat 0)); YP09.mkChunk (-88) (CVal 8 (SLit 0x5a4a0)); YP09.mkChunk (-80) (CVal 8 (SOff 24%nat 0));
YP09.mkChunk (-72) (CVal 8 (SOff 23%nat 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22%nat 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21%nat 0));
YP09.mkChunk (-48) (CVal 8 (SOff 20%nat 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19%nat 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18%nat 0));
YP09.mkChunk (-24) (CVal 8 (SOff 9%nat 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8%nat 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1%nat 0))].
Definition R_O1a (z : sv) : YP09.region := YP09.mkRegion (Some 10%nat) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 z)].
Definition R_O1b : YP09.region := YP09.mkRegion (Some 10%nat) 16 24 16 24 [YP09.mkChunk 16 (CVal 8 (SOff 11%nat 0))].
Definition R_O2' : YP09.region := YP09.mkRegion (Some 10%nat) 2056 2064 2056 2064 [YP09.mkChunk 2056 (CVal 8 (SOff 12%nat 0))].
Definition R_T2' : YP09.region := YP09.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1)
[YP09.mkChunk t_unwinding (CVal 1 (SLit 1))].
Definition LFIX : smem := [R_S'; R_O1b; R_O2'] ++ UCONST ++ [R_C; R_T1; R_T2'].
Definition S_LH0 : sstate := Eval vm_compute in runto_rt 0x72efc (YP06.add_cond S1 c_f0_ok).
Lemma S_LH0_mem : ss_mem S_LH0 = [R_S'; R_O1a (SLit 1); R_O1b; R_O2'; R_F 12%nat] ++ UCONST ++ [R_C; R_T1; R_T2'].
Proof. vm_compute. reflexivity. Qed.
Definition R_Q : YP09.region := YP09.mkRegion (Some aQ) 0 8 0 8 [].
Definition LREGS : list sv :=
[SLit 0; SLit 0x5a4a0; SOff 2 (-144); SOff 3 0; SLit TFIB_TP; SOff 10 2047; SOff 12 0; SOff 7 0; SLit 30; SOff aTOP (-16); SOff 10 0; SOff 11 0; SOff aB 0; SLit 4096;
SOff 10 16; SOff aZ 0; SOff aHAV 0; SOff (S aHAV) 0; SLit 0x135aa0; SOff 10 0; SLit 0; SLit 1; SOff aTOP 0; SOff aT 0; SOff aT 2047; SOff 25 0; SOff 26 0;
SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]%nat.
Definition LATOMS : list (nat * afact) :=
UF_atoms ++ [(aB, mkAF kHighMemBeg kHighMemEnd 3); (aZ, mkAF 1 30 0); (aQ, mkAF kHighMemBeg kHighMemEnd 3);
(aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S aHAV, mkAF 0 (2 ^ 64 - 1) 0)].
Definition LCONDS : list acond := [c_f0_ok] ++ UF_conds.
Definition LALIAS : sv * sv := (SAlu Instr.ALU_ADD (SOff 10%nat 16) (SAlu Instr.ALU_SLL (SOff aZ 0) (SLit 3)), SOff aQ 0).
Definition LF0 : facts := mkFacts LATOMS LCONDS [].
Definition LF : facts := mkFacts LATOMS LCONDS [LALIAS].
Definition LMEM : smem := R_F aB :: R_O1a (SOff aZ 0) :: LFIX.
Definition A_LOOP : Z := 0x72efc.
Definition S_L : sstate := mkSS A_LOOP LREGS LMEM None LF.
Definition R_Fb (b : nat) : YP09.region := YP09.mkRegion (Some b) (- 8) 0 0 0 [YP09.mkChunk (- 8) (CVal 8 (SOff aRA 0))].
Definition LATOMSB : list (nat * afact) :=
UF_fixed ++ [(aRA, mkAF 0 4095 0); (aB, mkAF kHighMemBeg kHighMemEnd 3); (aZ, mkAF 1 30 0); (aQ, mkAF kHighMemBeg kHighMemEnd 3);
(aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S aHAV, mkAF 0 (2 ^ 64 - 1) 0)].
Definition LFB : facts := mkFacts LATOMSB LCONDS [].
Definition LMEMB : smem := R_Fb aB :: R_O1a (SOff aZ 0) :: LFIX.
Definition S_LB : sstate := mkSS A_LOOP LREGS LMEMB None LFB.
Definition XREGS : list sv :=
[SLit 0; SLit 0x5a4a0; SOff 2 (-144); SOff 3 0; SLit TFIB_TP; SOff 10 2047; SOff 12 0; SOff 7 0; SLit 30; SOff aTOP (-16); SOff 10 0; SOff 11 0; SOff aHAV 0; SLit 4096;
SOff 44 0; SOff (S aHAV) 0; SOff (S (S aHAV)) 0; SOff (S (S (S aHAV))) 0; SLit 0x135aa0; SOff 10 0; SLit 0; SLit 1; SOff aTOP 0; SOff aT 0; SOff aT 2047;
SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]%nat.
Definition XATOMS : list (nat * afact) :=
UF_fixed ++ [(aZ, mkAF 1 30 0); (aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S (S aHAV), mkAF 0 (2 ^ 64 - 1) 0);
(S (S (S aHAV)), mkAF 0 (2 ^ 64 - 1) 0); (44%nat, mkAF 0 (2 ^ 64 - 1) 0)].
Definition XF : facts := mkFacts XATOMS UF_conds [].
Definition XMEM : smem := R_O1a (SOff aZ 0) :: LFIX.
Definition A_EXIT : Z := 0x72f38.
Definition S_X : sstate := mkSS A_EXIT XREGS XMEM None XF.
